"""
Knights Contract (PS3) Save Editor
==================================
Standard-library-only Tkinter editor for decrypted/extracted SAVEDATA.DAT files.

Verified fields:
- Upgrade Points / Souls: big-endian uint32 at offset 0x808
- Game clear count: big-endian uint32 at offset 0x80
- Per-difficulty episode-clear counts: five big-endian uint32 values at 0xC4..0xD4
- 20 cleared episodes is the game's completion threshold for a difficulty slot
- Episode result records: 20 episode blocks x 5 difficulty slots
- Episode Select result mapping: category 0=C-..4=S; overall 0=D..5=S+
- Collectible item table: Lost Pages 401..450, equipment 201..209, extra Witchcraft 332..337
- Trophy/stat counters: Finishers 0xBC, Knight's Fury kills 0xA4, Witch's Embrace kills 0xA8

This tool deliberately does not guess labels for unknown offsets.
"""

from __future__ import annotations

import hashlib
import os
import shutil
import struct
import tempfile
import tkinter as tk
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from typing import Iterable


APP_TITLE = "Knights Contract PS3 Save Editor"
APP_VERSION = "1.0"

EXPECTED_SIZE = 0xA000
MAGIC_OFFSET = 0x04
MAGIC = b"fs_save\x00"
DECLARED_SIZE_OFFSET = 0x10

UPGRADE_POINTS_OFFSET = 0x808
UPGRADE_POINTS_MAX = 9_999_999

GAME_CLEAR_COUNT_OFFSET = 0x80
GAME_FINISH_COUNT_OFFSET = 0xBC
KNIGHTS_FURY_KILL_COUNT_OFFSET = 0xA4
WITCHS_EMBRACE_KILL_COUNT_OFFSET = 0xA8
COMBAT_COUNTER_MAX = 0xFFFFFFFF
KNIGHTS_FURY_TROPHY_TARGET = 200
WITCHS_EMBRACE_TROPHY_TARGET = 200
FINISHER_TROPHY_TARGET = 1000

EPISODE_CLEAR_COUNTS_OFFSET = 0xC4
EPISODE_CLEAR_COUNT_SLOTS = 5
EPISODES_PER_DIFFICULTY = 20
DIFFICULTY_UNLOCK_PREREQUISITE_SLOTS = (1, 2, 3)
DIFFICULTY_INTERNAL_NAMES = ("PAGE (Easy)", "SQUIRE (Normal)", "KNIGHT (Hard)", "HEXEN KNIGHT (Very Hard)", "WITCHSLAYER (Hell)")

EPISODE_RESULT_BASE_OFFSET = 0x1A00
EPISODE_RESULT_STRIDE = 0x500
EPISODE_RESULT_DIFFICULTY_STRIDE = 0x100
EPISODE_RESULT_COUNT = 20
RESULT_COMPONENT_SCORE_OFFSETS = (0x04, 0x0C, 0x20, 0x2C, 0x38)
RESULT_COMPONENT_RANK_OFFSETS = (0x08, 0x10, 0x24, 0x30, 0x3C)
RESULT_S_PLUS_SCORE_VALUES = (500000, 500000, 500000, 500000, 50000)
RESULT_S_PLUS_TOTAL_SCORE = sum(RESULT_S_PLUS_SCORE_VALUES)
RESULT_TOTAL_SCORE_OFFSET = 0x40
RESULT_TOTAL_RANK_OFFSET = 0x44
RESULT_COMPONENT_S_RANK = 4
RESULT_TOTAL_S_PLUS_RANK = 5
RESULT_MAX_SCORE = 0x7FFFFFFF
RESULT_COMPONENT_RANK_LABELS = ("C-", "C", "B", "A", "S")
RESULT_TOTAL_RANK_LABELS = ("D", "C", "B", "A", "S", "S+")

ITEM_TABLE_SCAN_START = 0x0A00
ITEM_TABLE_SCAN_END = 0x1500
ITEM_TABLE_RECORD_STRIDE = 8

LOST_PAGE_ITEMS = tuple((401 + i, f"Lost Page {i + 1:02d}") for i in range(50))
EQUIPMENT_COLLECTIBLE_ITEMS = (
    (201, "Seal of Vitality"),
    (202, "Seal of the Bond"),
    (203, "Seal of Magic"),
    (204, "Seal of Life"),
    (205, "Seal of the Hunter"),
    (206, "Seal of Wisdom"),
    (207, "Seal of Rage"),
    (208, "Book of Unification"),
    (209, "Seal of Souls"),
)
EXTRA_WITCHCRAFT_COLLECTIBLE_ITEMS = (
    (332, "Tannhauser's Illusion"),
    (333, "Hildebrand's Sword"),
    (334, "Elizabeth's Fangs"),
    (335, "Fafrotskies Rain"),
    (336, "Kaspar's Rifle"),
    (337, "Spirit Cannon"),
)
MAX_HEALTH_EQUIPMENT_ITEMS = (
    (201, "Seal of Vitality"),
    (204, "Seal of Life"),
)
ALL_COLLECTIBLE_ITEMS = (
    *(('Lost Page', item_id, name) for item_id, name in LOST_PAGE_ITEMS),
    *(('Equipment', item_id, name) for item_id, name in EQUIPMENT_COLLECTIBLE_ITEMS),
    *(('Extra Witchcraft', item_id, name) for item_id, name in EXTRA_WITCHCRAFT_COLLECTIBLE_ITEMS),
)
ALL_COLLECTIBLE_ITEM_IDS = tuple(item_id for _category, item_id, _name in ALL_COLLECTIBLE_ITEMS)

PS3_SECURE_FILE_ID = "AA451A251190F0078D555BFEF799C10D"
SUPPORTED_TITLE_IDS = ("BLUS30582", "BLES01001", "BLAS50303", "BLJS10088")

APP_ICON_PNG_BASE64 = """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"""


@dataclass(frozen=True)
class ValidationResult:
    ok: bool
    messages: tuple[str, ...]


@dataclass(frozen=True)
class DiffSpan:
    start: int
    old: bytes
    new: bytes

    @property
    def end(self) -> int:
        return self.start + len(self.old) - 1


def sha256_hex(data: bytes | bytearray) -> str:
    return hashlib.sha256(data).hexdigest()


def be_u32(data: bytes | bytearray, offset: int) -> int:
    if offset < 0 or offset + 4 > len(data):
        raise ValueError(f"Offset 0x{offset:X} is outside the save.")
    return struct.unpack_from(">I", data, offset)[0]


def write_be_u32(data: bytearray, offset: int, value: int) -> None:
    if not 0 <= value <= 0xFFFFFFFF:
        raise ValueError("32-bit value must be between 0 and 4,294,967,295.")
    if offset < 0 or offset + 4 > len(data):
        raise ValueError(f"Offset 0x{offset:X} is outside the save.")
    struct.pack_into(">I", data, offset, value)


def validate_save(data: bytes | bytearray) -> ValidationResult:
    messages: list[str] = []

    if len(data) != EXPECTED_SIZE:
        messages.append(
            f"Unexpected file size: 0x{len(data):X} ({len(data):,} bytes); "
            f"expected 0x{EXPECTED_SIZE:X} ({EXPECTED_SIZE:,} bytes)."
        )

    if len(data) < MAGIC_OFFSET + len(MAGIC) or data[MAGIC_OFFSET:MAGIC_OFFSET + len(MAGIC)] != MAGIC:
        messages.append("Header marker 'fs_save' was not found at offset 0x04.")

    if len(data) >= DECLARED_SIZE_OFFSET + 4:
        declared_size = be_u32(data, DECLARED_SIZE_OFFSET)
        if declared_size != EXPECTED_SIZE:
            messages.append(
                f"Header declares size 0x{declared_size:X}; expected 0x{EXPECTED_SIZE:X}."
            )
    else:
        messages.append("File is too short to contain the declared-size field.")

    return ValidationResult(ok=not messages, messages=tuple(messages))


def group_differences(a: bytes | bytearray, b: bytes | bytearray) -> list[DiffSpan]:
    """Group adjacent changed bytes into spans."""
    limit = min(len(a), len(b))
    spans: list[DiffSpan] = []
    start = None

    for i in range(limit):
        different = a[i] != b[i]
        if different and start is None:
            start = i
        elif not different and start is not None:
            spans.append(DiffSpan(start, bytes(a[start:i]), bytes(b[start:i])))
            start = None

    if start is not None:
        spans.append(DiffSpan(start, bytes(a[start:limit]), bytes(b[start:limit])))

    if len(a) != len(b):
        longer_a = bytes(a[limit:])
        longer_b = bytes(b[limit:])
        spans.append(DiffSpan(limit, longer_a, longer_b))

    return spans


def parse_int(text: str, *, allow_hex: bool = True) -> int:
    s = text.strip().replace("_", "")
    if not s:
        raise ValueError("Enter a value.")
    if allow_hex and s.lower().startswith("0x"):
        return int(s, 16)
    return int(s, 10)


def parse_hex_bytes(text: str) -> bytes:
    s = text.strip().replace(" ", "").replace("-", "").replace(":", "")
    if s.lower().startswith("0x"):
        s = s[2:]
    if not s:
        raise ValueError("Enter one or more hex bytes.")
    if len(s) % 2:
        raise ValueError("Hex byte input must contain an even number of digits.")
    try:
        return bytes.fromhex(s)
    except ValueError as exc:
        raise ValueError("Invalid hex byte input.") from exc


class KnightsContractSave:
    def __init__(self, data: bytes, path: Path | None = None):
        result = validate_save(data)
        if not result.ok:
            raise ValueError("\n".join(result.messages))
        self.path = path
        self.original = bytes(data)
        self.data = bytearray(data)
        self.edit_log: list[str] = []

    @classmethod
    def load(cls, path: str | os.PathLike[str]) -> "KnightsContractSave":
        p = Path(path)
        return cls(p.read_bytes(), p)

    @property
    def upgrade_points(self) -> int:
        return be_u32(self.data, UPGRADE_POINTS_OFFSET)

    def set_upgrade_points(self, value: int) -> None:
        if not 0 <= value <= UPGRADE_POINTS_MAX:
            raise ValueError(
                f"Upgrade Points must be between 0 and {UPGRADE_POINTS_MAX:,}."
            )
        old = self.upgrade_points
        write_be_u32(self.data, UPGRADE_POINTS_OFFSET, value)
        if old != value:
            self.edit_log.append(
                f"Upgrade Points: {old:,} -> {value:,} "
                f"(0x{UPGRADE_POINTS_OFFSET:08X}, big-endian u32)"
            )

    def combat_counter(self, offset: int) -> int:
        if offset not in (GAME_FINISH_COUNT_OFFSET, KNIGHTS_FURY_KILL_COUNT_OFFSET, WITCHS_EMBRACE_KILL_COUNT_OFFSET):
            raise ValueError(f"Unsupported combat counter offset 0x{offset:X}.")
        return be_u32(self.data, offset)

    def set_combat_counter(self, offset: int, value: int, label: str) -> None:
        if not 0 <= value <= COMBAT_COUNTER_MAX:
            raise ValueError(f"{label} must be between 0 and {COMBAT_COUNTER_MAX:,}.")
        old = self.combat_counter(offset)
        write_be_u32(self.data, offset, value)
        if old != value:
            self.edit_log.append(
                f"{label}: {old:,} -> {value:,} "
                f"(0x{offset:08X}, big-endian u32)"
            )

    @property
    def finisher_count(self) -> int:
        return self.combat_counter(GAME_FINISH_COUNT_OFFSET)

    @property
    def knights_fury_kill_count(self) -> int:
        return self.combat_counter(KNIGHTS_FURY_KILL_COUNT_OFFSET)

    @property
    def witchs_embrace_kill_count(self) -> int:
        return self.combat_counter(WITCHS_EMBRACE_KILL_COUNT_OFFSET)

    def set_finisher_count(self, value: int) -> None:
        self.set_combat_counter(GAME_FINISH_COUNT_OFFSET, value, "Finishers")

    def set_knights_fury_kill_count(self, value: int) -> None:
        self.set_combat_counter(KNIGHTS_FURY_KILL_COUNT_OFFSET, value, "Knight's Fury kills")

    def set_witchs_embrace_kill_count(self, value: int) -> None:
        self.set_combat_counter(WITCHS_EMBRACE_KILL_COUNT_OFFSET, value, "Witch's Embrace kills")

    def _find_item_record_offset(self, item_id: int) -> int:
        if not 0 <= item_id <= 0xFFFF:
            raise ValueError("Item ID must fit an unsigned 16-bit value.")
        for offset in range(ITEM_TABLE_SCAN_START, ITEM_TABLE_SCAN_END, ITEM_TABLE_RECORD_STRIDE):
            word = be_u32(self.data, offset)
            if (word >> 16) == item_id:
                return offset
        raise ValueError(f"Item ID {item_id} (0x{item_id:04X}) was not found in this save's item table.")

    def item_state(self, item_id: int) -> int:
        offset = self._find_item_record_offset(item_id)
        return be_u32(self.data, offset) & 0xFFFF

    def set_item_state(self, item_id: int, state: int) -> None:
        if not 0 <= state <= 0xFFFF:
            raise ValueError("Item state must fit an unsigned 16-bit value.")
        offset = self._find_item_record_offset(item_id)
        word = be_u32(self.data, offset)
        old_state = word & 0xFFFF
        new_word = (word & 0xFFFF0000) | state
        write_be_u32(self.data, offset, new_word)
        if old_state != state:
            self.edit_log.append(
                f"Item {item_id} (0x{item_id:04X}): state {old_state} -> {state} "
                f"(0x{offset:08X})"
            )

    def set_items_collected(self, item_ids: Iterable[int], collected: bool = True) -> None:
        state = 1 if collected else 0
        for item_id in item_ids:
            self.set_item_state(item_id, state)

    def set_all_collectibles(self) -> None:
        self.set_items_collected(ALL_COLLECTIBLE_ITEM_IDS, True)

    def set_max_health_equipment_acquired(self) -> None:
        self.set_items_collected((item_id for item_id, _name in MAX_HEALTH_EQUIPMENT_ITEMS), True)

    def collectible_counts(self) -> dict[str, tuple[int, int]]:
        groups = {
            "Lost Pages": tuple(item_id for item_id, _name in LOST_PAGE_ITEMS),
            "Equipment": tuple(item_id for item_id, _name in EQUIPMENT_COLLECTIBLE_ITEMS),
            "Extra Witchcraft": tuple(item_id for item_id, _name in EXTRA_WITCHCRAFT_COLLECTIBLE_ITEMS),
        }
        result: dict[str, tuple[int, int]] = {}
        for name, item_ids in groups.items():
            owned = sum(1 for item_id in item_ids if self.item_state(item_id) != 0)
            result[name] = (owned, len(item_ids))
        return result

    @property
    def game_clear_count(self) -> int:
        return be_u32(self.data, GAME_CLEAR_COUNT_OFFSET)

    @property
    def episode_clear_counts(self) -> tuple[int, ...]:
        return tuple(
            be_u32(self.data, EPISODE_CLEAR_COUNTS_OFFSET + index * 4)
            for index in range(EPISODE_CLEAR_COUNT_SLOTS)
        )

    def set_game_clear_count_minimum(self, minimum: int = 1) -> None:
        old = self.game_clear_count
        if old < minimum:
            write_be_u32(self.data, GAME_CLEAR_COUNT_OFFSET, minimum)
            self.edit_log.append(
                f"Game clear count: {old} -> {minimum} "
                f"(0x{GAME_CLEAR_COUNT_OFFSET:08X}, big-endian u32)"
            )

    def set_game_clear_count(self, value: int) -> None:
        if not 0 <= value <= 0xFFFFFFFF:
            raise ValueError("Game clear count must fit an unsigned 32-bit value.")
        old = self.game_clear_count
        write_be_u32(self.data, GAME_CLEAR_COUNT_OFFSET, value)
        if old != value:
            self.edit_log.append(
                f"Game clear count: {old} -> {value} "
                f"(0x{GAME_CLEAR_COUNT_OFFSET:08X}, big-endian u32)"
            )

    def set_episode_clear_count(self, index: int, value: int) -> None:
        if not 0 <= index < EPISODE_CLEAR_COUNT_SLOTS:
            raise ValueError("Difficulty slot index is outside 0..4.")
        if not 0 <= value <= EPISODES_PER_DIFFICULTY:
            raise ValueError(
                f"Episode clear count must be between 0 and {EPISODES_PER_DIFFICULTY}."
            )
        offset = EPISODE_CLEAR_COUNTS_OFFSET + index * 4
        old = be_u32(self.data, offset)
        write_be_u32(self.data, offset, value)
        if old != value:
            self.edit_log.append(
                f"Episode clear count {DIFFICULTY_INTERNAL_NAMES[index]}: "
                f"{old} -> {value} (0x{offset:08X}, big-endian u32)"
            )

    def unlock_all_difficulties(self) -> None:
        self.set_game_clear_count_minimum(1)
        for index in DIFFICULTY_UNLOCK_PREREQUISITE_SLOTS:
            self.set_episode_clear_count(index, EPISODES_PER_DIFFICULTY)

    def unlock_episode_select_all(self) -> None:
        self.set_game_clear_count_minimum(1)
        for index in range(EPISODE_CLEAR_COUNT_SLOTS):
            self.set_episode_clear_count(index, EPISODES_PER_DIFFICULTY)

    def unlock_all_progression(self) -> None:
        self.unlock_episode_select_all()

    @staticmethod
    def episode_result_offset(episode_index: int, difficulty_index: int) -> int:
        if not 0 <= episode_index < EPISODE_RESULT_COUNT:
            raise ValueError("Episode index is outside 0..19.")
        if not 0 <= difficulty_index < EPISODE_CLEAR_COUNT_SLOTS:
            raise ValueError("Difficulty slot index is outside 0..4.")
        return (
            EPISODE_RESULT_BASE_OFFSET
            + episode_index * EPISODE_RESULT_STRIDE
            + difficulty_index * EPISODE_RESULT_DIFFICULTY_STRIDE
        )

    def episode_total_rank(self, episode_index: int, difficulty_index: int) -> int:
        base = self.episode_result_offset(episode_index, difficulty_index)
        return be_u32(self.data, base + RESULT_TOTAL_RANK_OFFSET)

    def episode_component_ranks(self, episode_index: int, difficulty_index: int) -> tuple[int, ...]:
        base = self.episode_result_offset(episode_index, difficulty_index)
        return tuple(be_u32(self.data, base + rel) for rel in RESULT_COMPONENT_RANK_OFFSETS)

    def episode_total_score(self, episode_index: int, difficulty_index: int) -> int:
        base = self.episode_result_offset(episode_index, difficulty_index)
        return be_u32(self.data, base + RESULT_TOTAL_SCORE_OFFSET)

    def set_episode_result_fields(
        self,
        episode_index: int,
        difficulty_index: int,
        *,
        component_scores: dict[int, int] | None = None,
        component_ranks: dict[int, int] | None = None,
        total_score: int | None = None,
        total_rank: int | None = None,
    ) -> None:
        base = self.episode_result_offset(episode_index, difficulty_index)
        changed_parts: list[str] = []

        if component_scores:
            for component_index, value in sorted(component_scores.items()):
                if not 0 <= component_index < len(RESULT_COMPONENT_SCORE_OFFSETS):
                    raise ValueError("Component-score index is outside 0..4.")
                if not 0 <= value <= RESULT_MAX_SCORE:
                    raise ValueError("Component score is outside the supported uint31 range.")
                offset = base + RESULT_COMPONENT_SCORE_OFFSETS[component_index]
                old = be_u32(self.data, offset)
                write_be_u32(self.data, offset, value)
                if old != value:
                    changed_parts.append(f"P{component_index + 1} {old}->{value}")

        if component_ranks:
            for component_index, value in sorted(component_ranks.items()):
                if not 0 <= component_index < len(RESULT_COMPONENT_RANK_OFFSETS):
                    raise ValueError("Component-rank index is outside 0..4.")
                if not 0 <= value < len(RESULT_COMPONENT_RANK_LABELS):
                    raise ValueError("Component rank must be between 0 (C-) and 4 (S).")
                rel = RESULT_COMPONENT_RANK_OFFSETS[component_index]
                offset = base + rel
                old = be_u32(self.data, offset)
                write_be_u32(self.data, offset, value)
                if old != value:
                    changed_parts.append(
                        f"C{component_index + 1} {old}->{value}"
                    )

        if total_score is not None:
            if not 0 <= total_score <= RESULT_MAX_SCORE:
                raise ValueError(
                    f"Total score must be between 0 and {RESULT_MAX_SCORE:,} (0x7FFFFFFF)."
                )
            offset = base + RESULT_TOTAL_SCORE_OFFSET
            old = be_u32(self.data, offset)
            write_be_u32(self.data, offset, total_score)
            if old != total_score:
                changed_parts.append(f"score {old}->{total_score}")

        if total_rank is not None:
            if not 0 <= total_rank < len(RESULT_TOTAL_RANK_LABELS):
                raise ValueError("Overall rank must be between 0 (D) and 5 (S+).")
            offset = base + RESULT_TOTAL_RANK_OFFSET
            old = be_u32(self.data, offset)
            write_be_u32(self.data, offset, total_rank)
            if old != total_rank:
                changed_parts.append(f"overall {old}->{total_rank}")

        if changed_parts:
            self.edit_log.append(
                f"Episode {episode_index + 1:02d} {DIFFICULTY_INTERNAL_NAMES[difficulty_index]}: "
                + ", ".join(changed_parts)
            )

    def s_plus_count(self, difficulty_index: int) -> int:
        return sum(
            self.episode_total_rank(episode, difficulty_index) == RESULT_TOTAL_S_PLUS_RANK
            for episode in range(EPISODE_RESULT_COUNT)
        )

    def _set_episode_s_plus_record(self, episode_index: int, difficulty_index: int) -> None:
        self.set_episode_result_fields(
            episode_index,
            difficulty_index,
            component_scores={i: RESULT_S_PLUS_SCORE_VALUES[i] for i in range(5)},
            component_ranks={i: RESULT_COMPONENT_S_RANK for i in range(5)},
            total_score=RESULT_S_PLUS_TOTAL_SCORE,
            total_rank=RESULT_TOTAL_S_PLUS_RANK,
        )

    def set_difficulty_all_s_plus(self, difficulty_index: int) -> None:
        if not 0 <= difficulty_index < EPISODE_CLEAR_COUNT_SLOTS:
            raise ValueError("Difficulty slot index is outside 0..4.")

        self.set_game_clear_count_minimum(1)
        self.set_episode_clear_count(difficulty_index, EPISODES_PER_DIFFICULTY)
        before = self.s_plus_count(difficulty_index)
        for episode_index in range(EPISODE_RESULT_COUNT):
            self._set_episode_s_plus_record(episode_index, difficulty_index)
        after = self.s_plus_count(difficulty_index)
        self.edit_log.append(
            f"S+ ranks {DIFFICULTY_INTERNAL_NAMES[difficulty_index]}: "
            f"{before}/{EPISODE_RESULT_COUNT} -> {after}/{EPISODE_RESULT_COUNT}"
        )

    def set_all_difficulties_all_s_plus(self) -> None:
        self.unlock_episode_select_all()
        before = tuple(self.s_plus_count(i) for i in range(EPISODE_CLEAR_COUNT_SLOTS))
        for difficulty_index in range(EPISODE_CLEAR_COUNT_SLOTS):
            for episode_index in range(EPISODE_RESULT_COUNT):
                self._set_episode_s_plus_record(episode_index, difficulty_index)
        after = tuple(self.s_plus_count(i) for i in range(EPISODE_CLEAR_COUNT_SLOTS))
        self.edit_log.append(
            f"S+ ranks all difficulties: {before} -> {after}"
        )

    def raw_patch(self, offset: int, payload: bytes, description: str = "Raw patch") -> None:
        if offset < 0:
            raise ValueError("Offset cannot be negative.")
        end = offset + len(payload)
        if end > len(self.data):
            raise ValueError(
                f"Patch would end at 0x{end:X}, beyond file size 0x{len(self.data):X}."
            )
        old = bytes(self.data[offset:end])
        self.data[offset:end] = payload
        self.edit_log.append(
            f"{description}: 0x{offset:08X}-0x{end - 1:08X} "
            f"{old.hex(' ').upper()} -> {payload.hex(' ').upper()}"
        )

    def revert_all(self) -> None:
        self.data[:] = self.original
        self.edit_log.clear()

    def changed_spans(self) -> list[DiffSpan]:
        return group_differences(self.original, self.data)

    def save_atomic(self, destination: str | os.PathLike[str], backup: bool = True) -> Path:
        dest = Path(destination)
        dest.parent.mkdir(parents=True, exist_ok=True)

        if backup and dest.exists():
            backup_path = dest.with_name(dest.name + ".bak")
            shutil.copy2(dest, backup_path)

        fd, tmp_name = tempfile.mkstemp(
            prefix=dest.name + ".",
            suffix=".tmp",
            dir=str(dest.parent),
        )
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(self.data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp_name, dest)
        except Exception:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
            raise

        return dest


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        try:
            self._app_icon = tk.PhotoImage(data=APP_ICON_PNG_BASE64)
            self.iconphoto(True, self._app_icon)
        except tk.TclError:
            self._app_icon = None
        self.title(f"{APP_TITLE} v{APP_VERSION}")
        self.geometry("1040x900")
        self.minsize(860, 720)

        self.save: KnightsContractSave | None = None
        self.compare_data: bytes | None = None
        self.compare_path: Path | None = None

        self._configure_style()
        self._build_ui()
        self._set_loaded_state(False)

    def _configure_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("vista")
        except tk.TclError:
            pass
        style.configure("Title.TLabel", font=("Segoe UI", 16, "bold"))
        style.configure("Section.TLabel", font=("Segoe UI", 10, "bold"))

    def _build_ui(self):
        top = ttk.Frame(self, padding=(14, 12))
        top.pack(fill="x")

        ttk.Label(top, text="Knights Contract — PS3 Save Editor", style="Title.TLabel").pack(side="left")

        filebar = ttk.Frame(self, padding=(14, 0, 14, 10))
        filebar.pack(fill="x")

        ttk.Button(filebar, text="Open SAVEDATA.DAT", command=self.open_save).pack(side="left")
        self.save_as_btn = ttk.Button(filebar, text="Save As…", command=self.save_as)
        self.save_as_btn.pack(side="left", padx=(8, 0))
        self.overwrite_btn = ttk.Button(filebar, text="Save / Overwrite", command=self.save_overwrite)
        self.overwrite_btn.pack(side="left", padx=(8, 0))
        self.revert_btn = ttk.Button(filebar, text="Revert All", command=self.revert_all)
        self.revert_btn.pack(side="left", padx=(8, 0))

        self.path_var = tk.StringVar(value="No save loaded")
        ttk.Label(filebar, textvariable=self.path_var).pack(side="left", padx=(16, 0), fill="x", expand=True)

        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill="both", expand=True, padx=14, pady=(0, 12))

        self.editor_tab = ttk.Frame(self.notebook, padding=14)
        self.manual_tab = ttk.Frame(self.notebook, padding=14)
        self.collectibles_tab = ttk.Frame(self.notebook, padding=14)
        self.combat_tab = ttk.Frame(self.notebook, padding=14)
        self.compare_tab = ttk.Frame(self.notebook, padding=14)
        self.advanced_tab = ttk.Frame(self.notebook, padding=14)
        self.info_tab = ttk.Frame(self.notebook, padding=14)

        self.notebook.add(self.editor_tab, text="Quick Editor")
        self.notebook.add(self.manual_tab, text="Manual Edit")
        self.notebook.add(self.collectibles_tab, text="Collectibles / Health")
        self.notebook.add(self.combat_tab, text="Trophy Counters")
        self.notebook.add(self.compare_tab, text="Compare Saves")
        self.notebook.add(self.advanced_tab, text="Advanced Patch")
        self.notebook.add(self.info_tab, text="PS3 / Info")

        self._build_editor_tab()
        self._build_manual_tab()
        self._build_collectibles_tab()
        self._build_combat_tab()
        self._build_compare_tab()
        self._build_advanced_tab()
        self._build_info_tab()

        self.status_var = tk.StringVar(value="Ready.")
        status = ttk.Label(self, textvariable=self.status_var, anchor="w", padding=(14, 6))
        status.pack(fill="x", side="bottom")

    def _build_editor_tab(self):
        self.editor_tab.columnconfigure(0, weight=1)

        info = ttk.LabelFrame(self.editor_tab, text="Loaded save", padding=12)
        info.grid(row=0, column=0, sticky="ew")
        info.columnconfigure(1, weight=1)

        self.file_size_var = tk.StringVar(value="—")
        self.hash_var = tk.StringVar(value="—")
        self.original_hash_var = tk.StringVar(value="—")
        self.change_count_var = tk.StringVar(value="0")

        labels = [
            ("Format", "Knights Contract / fs_save"),
            ("Expected size", f"0x{EXPECTED_SIZE:X} ({EXPECTED_SIZE:,} bytes)"),
        ]
        row = 0
        for label, value in labels:
            ttk.Label(info, text=label + ":", style="Section.TLabel").grid(row=row, column=0, sticky="w", pady=2)
            ttk.Label(info, text=value).grid(row=row, column=1, sticky="w", padx=(12, 0), pady=2)
            row += 1

        for label, var in [
            ("Loaded size", self.file_size_var),
            ("Original SHA-256", self.original_hash_var),
            ("Working SHA-256", self.hash_var),
            ("Changed spans", self.change_count_var),
        ]:
            ttk.Label(info, text=label + ":", style="Section.TLabel").grid(row=row, column=0, sticky="nw", pady=2)
            ttk.Label(info, textvariable=var, wraplength=650).grid(row=row, column=1, sticky="w", padx=(12, 0), pady=2)
            row += 1

        field = ttk.LabelFrame(self.editor_tab, text="Verified game field", padding=12)
        field.grid(row=1, column=0, sticky="ew", pady=(14, 0))
        field.columnconfigure(1, weight=1)

        ttk.Label(field, text="Upgrade Points / Souls:", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.points_var = tk.StringVar()
        self.points_entry = ttk.Entry(field, textvariable=self.points_var, width=24)
        self.points_entry.grid(row=0, column=1, sticky="w", padx=(12, 8))

        self.max_btn = ttk.Button(field, text="Max 9,999,999", command=self.max_points)
        self.max_btn.grid(row=0, column=2, padx=(0, 8))
        self.apply_points_btn = ttk.Button(field, text="Apply", command=self.apply_points)
        self.apply_points_btn.grid(row=0, column=3)

        ttk.Label(
            field,
            text=(
                "Verified: big-endian uint32 at offset 0x00000808. "
                "This editor caps the named control at 9,999,999."
            ),
            wraplength=800,
        ).grid(row=1, column=0, columnspan=4, sticky="w", pady=(8, 0))

        progression = ttk.LabelFrame(
            self.editor_tab,
            text="Episode Select / Difficulty Unlocks (EBOOT verified)",
            padding=12,
        )
        progression.grid(row=2, column=0, sticky="ew", pady=(14, 0))
        progression.columnconfigure(0, weight=1)

        self.game_clear_var = tk.StringVar(value="—")
        ttk.Label(
            progression,
            text="Game clear count:",
            style="Section.TLabel",
        ).grid(row=0, column=0, sticky="w")
        ttk.Label(progression, textvariable=self.game_clear_var).grid(
            row=0, column=1, sticky="w", padx=(8, 0)
        )

        self.progress_tree = ttk.Treeview(
            progression,
            columns=("slot", "internal", "cleared", "state"),
            show="headings",
            height=5,
        )
        for key, title in (
            ("slot", "Slot"),
            ("internal", "Internal difficulty"),
            ("cleared", "Episodes cleared"),
            ("state", "Episode Select"),
        ):
            self.progress_tree.heading(key, text=title)
        self.progress_tree.column("slot", width=60, anchor="center")
        self.progress_tree.column("internal", width=180, anchor="w")
        self.progress_tree.column("cleared", width=140, anchor="center")
        self.progress_tree.column("state", width=220, anchor="w")
        self.progress_tree.grid(row=1, column=0, columnspan=4, sticky="ew", pady=(10, 8))

        self.unlock_difficulty_btn = ttk.Button(
            progression,
            text="Unlock All Difficulties",
            command=self.unlock_all_difficulties,
        )
        self.unlock_difficulty_btn.grid(row=2, column=0, sticky="w")

        self.unlock_episode_btn = ttk.Button(
            progression,
            text="Episode Select — Unlock All 20",
            command=self.unlock_all_episodes,
        )
        self.unlock_episode_btn.grid(row=2, column=1, sticky="w", padx=(8, 0))

        self.unlock_everything_btn = ttk.Button(
            progression,
            text="Unlock Episodes + Difficulties",
            command=self.unlock_all_progression,
        )
        self.unlock_everything_btn.grid(row=2, column=2, sticky="w", padx=(8, 0))

        ttk.Label(
            progression,
            text=(
                "The executable stores five per-difficulty episode-clear counters at "
                "0xC4–0xD4. Episode Select uses the selected counter, and the title menu "
                "uses 20 cleared episodes as the progression threshold for later tiers."
            ),
            wraplength=900,
        ).grid(row=3, column=0, columnspan=4, sticky="w", pady=(10, 0))

        ranking = ttk.LabelFrame(
            self.editor_tab,
            text="Episode Rankings — S+ Highest Rank",
            padding=12,
        )
        ranking.grid(row=3, column=0, sticky="ew", pady=(14, 0))
        ranking.columnconfigure(0, weight=1)

        self.rank_tree = ttk.Treeview(
            ranking,
            columns=("slot", "internal", "splus"),
            show="headings",
            height=5,
        )
        for key, title in (
            ("slot", "Slot"),
            ("internal", "Internal difficulty"),
            ("splus", "S+ episode ranks"),
        ):
            self.rank_tree.heading(key, text=title)
        self.rank_tree.column("slot", width=60, anchor="center")
        self.rank_tree.column("internal", width=180, anchor="w")
        self.rank_tree.column("splus", width=180, anchor="center")
        self.rank_tree.grid(row=0, column=0, columnspan=4, sticky="ew", pady=(0, 10))

        ttk.Label(ranking, text="Difficulty:", style="Section.TLabel").grid(
            row=1, column=0, sticky="w"
        )
        self.rank_difficulty_var = tk.StringVar(value=DIFFICULTY_INTERNAL_NAMES[2])
        self.rank_difficulty_combo = ttk.Combobox(
            ranking,
            textvariable=self.rank_difficulty_var,
            values=DIFFICULTY_INTERNAL_NAMES,
            state="readonly",
            width=18,
        )
        self.rank_difficulty_combo.grid(row=1, column=1, sticky="w", padx=(8, 12))

        self.splus_selected_btn = ttk.Button(
            ranking,
            text="Set Selected Difficulty — All 20 S+",
            command=self.set_selected_difficulty_s_plus,
        )
        self.splus_selected_btn.grid(row=1, column=2, sticky="w")

        self.splus_all_btn = ttk.Button(
            ranking,
            text="S+ Highest Rank — All Episodes / Difficulties",
            command=self.set_all_s_plus,
        )
        self.splus_all_btn.grid(row=1, column=3, sticky="w", padx=(8, 0))

        ttk.Label(
            ranking,
            text=(
                "Uses the in-game difficulty names. Force S+ writes the five displayed result "
                "scores plus their grades, then writes a matching total score and S+ overall grade. "
                "This fixes the old rank-only write that could leave Episode Select unchanged."
            ),
            wraplength=900,
        ).grid(row=2, column=0, columnspan=4, sticky="w", pady=(10, 0))

        log_frame = ttk.LabelFrame(self.editor_tab, text="Working changes", padding=8)
        log_frame.grid(row=4, column=0, sticky="nsew", pady=(14, 0))
        self.editor_tab.rowconfigure(4, weight=1)

        self.change_tree = ttk.Treeview(
            log_frame,
            columns=("range", "old", "new"),
            show="headings",
            height=10,
        )
        self.change_tree.heading("range", text="Offset / range")
        self.change_tree.heading("old", text="Original bytes")
        self.change_tree.heading("new", text="Working bytes")
        self.change_tree.column("range", width=180, anchor="w")
        self.change_tree.column("old", width=260, anchor="w")
        self.change_tree.column("new", width=260, anchor="w")
        self.change_tree.pack(fill="both", expand=True)

    def _build_manual_tab(self):
        self.manual_tab.columnconfigure(0, weight=1)
        self.manual_tab.rowconfigure(2, weight=1)

        ttk.Label(
            self.manual_tab,
            text=(
                "Edit only the fields you choose. Unticked result fields are left unchanged. "
                "Episode rows support Ctrl/Shift multi-selection."
            ),
            wraplength=1080,
        ).grid(row=0, column=0, sticky="ew", pady=(0, 10))

        progression = ttk.LabelFrame(self.manual_tab, text="Exact progression values", padding=10)
        progression.grid(row=1, column=0, sticky="ew")
        for c in range(8):
            progression.columnconfigure(c, weight=1 if c in (1, 4) else 0)

        ttk.Label(progression, text="Game clear count:", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.manual_game_clear_var = tk.StringVar(value="0")
        self.manual_game_clear_entry = ttk.Entry(progression, textvariable=self.manual_game_clear_var, width=12)
        self.manual_game_clear_entry.grid(row=0, column=1, sticky="w", padx=(8, 8))
        self.manual_game_clear_btn = ttk.Button(progression, text="Apply exact", command=self.apply_manual_game_clear)
        self.manual_game_clear_btn.grid(row=0, column=2, sticky="w", padx=(0, 18))

        ttk.Separator(progression, orient="vertical").grid(row=0, column=3, sticky="ns", padx=8)

        ttk.Label(progression, text="Difficulty:", style="Section.TLabel").grid(row=0, column=4, sticky="e")
        self.manual_progress_difficulty_var = tk.StringVar(value=DIFFICULTY_INTERNAL_NAMES[2])
        self.manual_progress_difficulty_combo = ttk.Combobox(
            progression,
            textvariable=self.manual_progress_difficulty_var,
            values=DIFFICULTY_INTERNAL_NAMES,
            state="readonly",
            width=13,
        )
        self.manual_progress_difficulty_combo.grid(row=0, column=5, sticky="w", padx=(8, 8))
        self.manual_progress_difficulty_combo.bind("<<ComboboxSelected>>", self._manual_progress_difficulty_changed)

        ttk.Label(progression, text="Episodes unlocked 0–20:").grid(row=0, column=6, sticky="e")
        self.manual_episode_clear_var = tk.StringVar(value="0")
        self.manual_episode_clear_spin = ttk.Spinbox(
            progression,
            from_=0,
            to=EPISODES_PER_DIFFICULTY,
            textvariable=self.manual_episode_clear_var,
            width=7,
        )
        self.manual_episode_clear_spin.grid(row=0, column=7, sticky="w", padx=(8, 8))
        self.manual_episode_clear_btn = ttk.Button(progression, text="Apply exact", command=self.apply_manual_episode_clear)
        self.manual_episode_clear_btn.grid(row=0, column=8, sticky="w")

        results = ttk.LabelFrame(self.manual_tab, text="Individual episode result records", padding=10)
        results.grid(row=2, column=0, sticky="nsew", pady=(12, 0))
        results.columnconfigure(0, weight=1)
        results.rowconfigure(2, weight=1)

        toolbar = ttk.Frame(results)
        toolbar.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        ttk.Label(toolbar, text="Difficulty:", style="Section.TLabel").pack(side="left")
        self.manual_rank_difficulty_var = tk.StringVar(value=DIFFICULTY_INTERNAL_NAMES[2])
        self.manual_rank_difficulty_combo = ttk.Combobox(
            toolbar,
            textvariable=self.manual_rank_difficulty_var,
            values=DIFFICULTY_INTERNAL_NAMES,
            state="readonly",
            width=13,
        )
        self.manual_rank_difficulty_combo.pack(side="left", padx=(8, 12))
        self.manual_rank_difficulty_combo.bind("<<ComboboxSelected>>", self._manual_rank_difficulty_changed)
        self.manual_select_all_btn = ttk.Button(toolbar, text="Select all 20", command=self.manual_select_all_episodes)
        self.manual_select_all_btn.pack(side="left")
        self.manual_clear_selection_btn = ttk.Button(toolbar, text="Clear selection", command=self.manual_clear_episode_selection)
        self.manual_clear_selection_btn.pack(side="left", padx=(8, 0))
        self.manual_selection_var = tk.StringVar(value="0 selected")
        ttk.Label(toolbar, textvariable=self.manual_selection_var).pack(side="right")

        self.manual_result_tree = ttk.Treeview(
            results,
            columns=("episode", "overall", "score", "c1", "c2", "c3", "c4", "c5"),
            show="headings",
            selectmode="extended",
            height=13,
        )
        headings = (
            ("episode", "Episode"), ("overall", "Overall"), ("score", "Total score"),
            ("c1", "Cat 1"), ("c2", "Cat 2"), ("c3", "Cat 3"), ("c4", "Cat 4"), ("c5", "Cat 5"),
        )
        for key, title in headings:
            self.manual_result_tree.heading(key, text=title)
        self.manual_result_tree.column("episode", width=75, anchor="center")
        self.manual_result_tree.column("overall", width=100, anchor="center")
        self.manual_result_tree.column("score", width=125, anchor="e")
        for key in ("c1", "c2", "c3", "c4", "c5"):
            self.manual_result_tree.column(key, width=82, anchor="center")
        self.manual_result_tree.grid(row=2, column=0, sticky="nsew")
        self.manual_result_tree.bind("<<TreeviewSelect>>", self._manual_tree_selection_changed)

        edit = ttk.LabelFrame(results, text="Fields to change on selected episode(s)", padding=8)
        edit.grid(row=3, column=0, sticky="ew", pady=(10, 0))

        self.manual_component_enabled_vars = []
        self.manual_component_rank_vars = []
        component_values = tuple(f"{i} - {name}" for i, name in enumerate(RESULT_COMPONENT_RANK_LABELS))
        for i in range(5):
            enabled = tk.BooleanVar(value=False)
            rank_var = tk.StringVar(value="4 - S")
            self.manual_component_enabled_vars.append(enabled)
            self.manual_component_rank_vars.append(rank_var)
            cb = ttk.Checkbutton(edit, text=f"Category {i + 1}", variable=enabled)
            cb.grid(row=0, column=i * 2, sticky="w", padx=(0 if i == 0 else 10, 4))
            combo = ttk.Combobox(edit, textvariable=rank_var, values=component_values, state="readonly", width=8)
            combo.grid(row=0, column=i * 2 + 1, sticky="w")
            setattr(self, f"manual_component_combo_{i}", combo)
            setattr(self, f"manual_component_check_{i}", cb)

        self.manual_total_rank_enabled_var = tk.BooleanVar(value=False)
        self.manual_total_rank_check = ttk.Checkbutton(edit, text="Overall rank", variable=self.manual_total_rank_enabled_var)
        self.manual_total_rank_check.grid(row=1, column=0, sticky="w", pady=(10, 0))
        total_values = tuple(f"{i} - {name}" for i, name in enumerate(RESULT_TOTAL_RANK_LABELS))
        self.manual_total_rank_var = tk.StringVar(value="5 - S+")
        self.manual_total_rank_combo = ttk.Combobox(edit, textvariable=self.manual_total_rank_var, values=total_values, state="readonly", width=10)
        self.manual_total_rank_combo.grid(row=1, column=1, sticky="w", pady=(10, 0))

        self.manual_score_enabled_var = tk.BooleanVar(value=False)
        self.manual_score_check = ttk.Checkbutton(edit, text="Total score", variable=self.manual_score_enabled_var)
        self.manual_score_check.grid(row=1, column=2, sticky="w", padx=(12, 4), pady=(10, 0))
        self.manual_score_var = tk.StringVar(value=str(RESULT_MAX_SCORE))
        self.manual_score_entry = ttk.Entry(edit, textvariable=self.manual_score_var, width=16)
        self.manual_score_entry.grid(row=1, column=3, sticky="w", pady=(10, 0))

        self.manual_unlock_selected_var = tk.BooleanVar(value=False)
        self.manual_unlock_selected_check = ttk.Checkbutton(
            edit,
            text="Unlock Episode Select through highest selected episode",
            variable=self.manual_unlock_selected_var,
        )
        self.manual_unlock_selected_check.grid(row=1, column=4, columnspan=3, sticky="w", padx=(12, 0), pady=(10, 0))

        self.manual_apply_results_btn = ttk.Button(
            edit,
            text="Apply only checked fields to selected episodes",
            command=self.apply_manual_result_edits,
        )
        self.manual_apply_results_btn.grid(row=1, column=8, columnspan=2, sticky="e", padx=(18, 0), pady=(10, 0))

        ttk.Label(
            edit,
            text=(
                "Displayed category grades are C-=0, C=1, B=2, A=3, S=4. "
                "Overall grades are D=0, C=1, B=2, A=3, S=4, S+=5."
            ),
            wraplength=1060,
        ).grid(row=2, column=0, columnspan=10, sticky="w", pady=(8, 0))

    def _build_collectibles_tab(self):
        self.collectibles_tab.columnconfigure(0, weight=1)
        self.collectibles_tab.rowconfigure(2, weight=1)

        summary = ttk.LabelFrame(self.collectibles_tab, text="Collectible summary", padding=10)
        summary.grid(row=0, column=0, sticky="ew")
        for col in range(6):
            summary.columnconfigure(col, weight=1 if col in (1, 3, 5) else 0)

        self.collect_lost_var = tk.StringVar(value="—")
        self.collect_equipment_var = tk.StringVar(value="—")
        self.collect_witch_var = tk.StringVar(value="—")
        self.collect_total_var = tk.StringVar(value="—")

        ttk.Label(summary, text="Lost Pages:", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(summary, textvariable=self.collect_lost_var).grid(row=0, column=1, sticky="w", padx=(6, 18))
        ttk.Label(summary, text="Equipment:", style="Section.TLabel").grid(row=0, column=2, sticky="w")
        ttk.Label(summary, textvariable=self.collect_equipment_var).grid(row=0, column=3, sticky="w", padx=(6, 18))
        ttk.Label(summary, text="Extra Witchcraft:", style="Section.TLabel").grid(row=0, column=4, sticky="w")
        ttk.Label(summary, textvariable=self.collect_witch_var).grid(row=0, column=5, sticky="w", padx=(6, 0))
        ttk.Label(summary, text="Total:", style="Section.TLabel").grid(row=1, column=0, sticky="w", pady=(8, 0))
        ttk.Label(summary, textvariable=self.collect_total_var).grid(row=1, column=1, sticky="w", padx=(6, 18), pady=(8, 0))

        buttons = ttk.Frame(summary)
        buttons.grid(row=1, column=2, columnspan=4, sticky="e", pady=(8, 0))
        self.collect_all_btn = ttk.Button(buttons, text="Collect All 65", command=self.collect_all_items)
        self.collect_all_btn.pack(side="left")
        self.health_equipment_btn = ttk.Button(
            buttons,
            text="Acquire Max-Health Equipment",
            command=self.acquire_max_health_equipment,
        )
        self.health_equipment_btn.pack(side="left", padx=(8, 0))

        health = ttk.LabelFrame(self.collectibles_tab, text="Maximum health", padding=10)
        health.grid(row=1, column=0, sticky="ew", pady=(12, 0))
        self.health_status_var = tk.StringVar(value="—")
        ttk.Label(health, textvariable=self.health_status_var, wraplength=950).pack(anchor="w")
        ttk.Label(
            health,
            text=(
                "The save does not contain a verified standalone permanent max-HP number. "
                "Seal of Vitality and Seal of Life are the two permanent equipment items documented "
                "to raise Gretchen's maximum health. This editor can acquire them safely; it does not "
                "guess an equipped-slot or temporary in-battle HP field."
            ),
            wraplength=950,
        ).pack(anchor="w", pady=(6, 0))

        manual = ttk.LabelFrame(self.collectibles_tab, text="Choose exactly what to edit", padding=8)
        manual.grid(row=2, column=0, sticky="nsew", pady=(12, 0))
        manual.columnconfigure(0, weight=1)
        manual.rowconfigure(1, weight=1)

        toolbar = ttk.Frame(manual)
        toolbar.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        self.collect_select_all_btn = ttk.Button(toolbar, text="Select all", command=self.select_all_collectibles)
        self.collect_select_all_btn.pack(side="left")
        self.collect_clear_selection_btn = ttk.Button(toolbar, text="Clear selection", command=self.clear_collectible_selection)
        self.collect_clear_selection_btn.pack(side="left", padx=(8, 0))
        self.collect_mark_btn = ttk.Button(toolbar, text="Set selected: Collected", command=lambda: self.set_selected_collectibles(True))
        self.collect_mark_btn.pack(side="left", padx=(18, 0))
        self.collect_unmark_btn = ttk.Button(toolbar, text="Set selected: Not collected", command=lambda: self.set_selected_collectibles(False))
        self.collect_unmark_btn.pack(side="left", padx=(8, 0))

        self.collectible_tree = ttk.Treeview(
            manual,
            columns=("category", "name", "id", "offset", "state"),
            show="headings",
            selectmode="extended",
            height=22,
        )
        for key, title in (
            ("category", "Category"),
            ("name", "Item"),
            ("id", "Item ID"),
            ("offset", "Save offset"),
            ("state", "State"),
        ):
            self.collectible_tree.heading(key, text=title)
        self.collectible_tree.column("category", width=130, anchor="w")
        self.collectible_tree.column("name", width=310, anchor="w")
        self.collectible_tree.column("id", width=90, anchor="center")
        self.collectible_tree.column("offset", width=120, anchor="center")
        self.collectible_tree.column("state", width=130, anchor="center")
        yscroll = ttk.Scrollbar(manual, orient="vertical", command=self.collectible_tree.yview)
        self.collectible_tree.configure(yscrollcommand=yscroll.set)
        self.collectible_tree.grid(row=1, column=0, sticky="nsew")
        yscroll.grid(row=1, column=1, sticky="ns")

        ttk.Label(
            manual,
            text=(
                "Manual changes write only the selected item's 16-bit state inside its existing item-table record. "
                "Nothing else is bulk-filled."
            ),
            wraplength=950,
        ).grid(row=2, column=0, sticky="w", pady=(8, 0))

    def _build_combat_tab(self):
        self.combat_tab.columnconfigure(0, weight=1)

        intro = ttk.LabelFrame(self.combat_tab, text="Editable persistent counters", padding=12)
        intro.grid(row=0, column=0, sticky="ew")
        intro.columnconfigure(1, weight=1)
        ttk.Label(
            intro,
            text=(
                "Enter any exact count and click Apply exact. For trophies, Prepare writes one below "
                "the target; then perform one matching action in-game."
            ),
            wraplength=940,
        ).grid(row=0, column=0, columnspan=5, sticky="w", pady=(0, 10))

        self.knights_fury_var = tk.StringVar(value="0")
        self.witchs_embrace_var = tk.StringVar(value="0")
        self.finisher_var = tk.StringVar(value="0")

        rows = (
            ("Knight's Fury kills", self.knights_fury_var, KNIGHTS_FURY_TROPHY_TARGET,
             KNIGHTS_FURY_KILL_COUNT_OFFSET, self.apply_knights_fury_count),
            ("Witch's Embrace kills", self.witchs_embrace_var, WITCHS_EMBRACE_TROPHY_TARGET,
             WITCHS_EMBRACE_KILL_COUNT_OFFSET, self.apply_witchs_embrace_count),
            ("Finishers", self.finisher_var, FINISHER_TROPHY_TARGET,
             GAME_FINISH_COUNT_OFFSET, self.apply_finisher_count),
        )
        self.combat_entries = []
        self.combat_apply_buttons = []
        self.combat_target_buttons = []
        for row, (label, var, target, offset, command) in enumerate(rows, start=1):
            ttk.Label(intro, text=label + ":", style="Section.TLabel").grid(
                row=row, column=0, sticky="w", pady=6
            )
            entry = ttk.Entry(intro, textvariable=var, width=18)
            entry.grid(row=row, column=1, sticky="w", padx=(10, 10), pady=6)
            target_btn = ttk.Button(
                intro,
                text=f"Prepare {target - 1:,}",
                command=lambda v=var, t=target - 1, c=command: (v.set(str(t)), c()),
            )
            target_btn.grid(row=row, column=2, sticky="w", padx=(0, 8), pady=6)
            apply_btn = ttk.Button(intro, text="Apply exact", command=command)
            apply_btn.grid(row=row, column=3, sticky="w", pady=6)
            ttk.Label(intro, text=f"offset 0x{offset:08X}").grid(
                row=row, column=4, sticky="w", padx=(14, 0), pady=6
            )
            self.combat_entries.append(entry)
            self.combat_target_buttons.append(target_btn)
            self.combat_apply_buttons.append(apply_btn)

        buttons = ttk.Frame(self.combat_tab)
        buttons.grid(row=1, column=0, sticky="w", pady=(12, 0))
        self.combat_apply_all_btn = ttk.Button(
            buttons, text="Apply all three exact values", command=self.apply_all_combat_counts
        )
        self.combat_apply_all_btn.pack(side="left")
        self.combat_set_targets_btn = ttk.Button(
            buttons, text="Prepare + apply (199 / 199 / 999)", command=self.fill_combat_trophy_targets
        )
        self.combat_set_targets_btn.pack(side="left", padx=(8, 0))

        note = ttk.LabelFrame(self.combat_tab, text="Verified EBOOT mapping", padding=12)
        note.grid(row=2, column=0, sticky="ew", pady=(14, 0))
        ttk.Label(
            note,
            text=(
                "Verified: Fury 0xA4, Embrace 0xA8. The 1,000-Finisher trophy reads 0xBC and compares "
                "exactly with 1,000; a one-Finisher save changed 21 to 22. v0.7's 0x90 mapping was wrong."
            ),
            wraplength=940,
        ).pack(anchor="w")

    def _build_compare_tab(self):
        actions = ttk.Frame(self.compare_tab)
        actions.pack(fill="x")
        self.compare_btn = ttk.Button(actions, text="Load comparison save…", command=self.open_compare)
        self.compare_btn.pack(side="left")
        self.compare_label_var = tk.StringVar(value="No comparison save loaded")
        ttk.Label(actions, textvariable=self.compare_label_var).pack(side="left", padx=(12, 0))

        ttk.Label(
            self.compare_tab,
            text=(
                "Use this after making ONE controlled change in-game. "
                "Adjacent changed bytes are grouped into spans; unknown spans are not assigned guessed labels."
            ),
            wraplength=840,
        ).pack(fill="x", pady=(10, 8))

        self.diff_tree = ttk.Treeview(
            self.compare_tab,
            columns=("range", "length", "current", "other"),
            show="headings",
            height=18,
        )
        for key, title in [
            ("range", "Offset / range"),
            ("length", "Bytes"),
            ("current", "Current save"),
            ("other", "Comparison save"),
        ]:
            self.diff_tree.heading(key, text=title)
        self.diff_tree.column("range", width=170)
        self.diff_tree.column("length", width=70, anchor="center")
        self.diff_tree.column("current", width=300)
        self.diff_tree.column("other", width=300)
        self.diff_tree.pack(fill="both", expand=True)

        self.diff_summary_var = tk.StringVar(value="")
        ttk.Label(self.compare_tab, textvariable=self.diff_summary_var).pack(anchor="w", pady=(8, 0))

    def _build_advanced_tab(self):
        ttk.Label(
            self.advanced_tab,
            text="Raw patching — for researched offsets only",
            style="Section.TLabel",
        ).pack(anchor="w")
        ttk.Label(
            self.advanced_tab,
            text=(
                "This tab intentionally does not assign names to unknown save fields. "
                "Use it only when you know an offset and representation."
            ),
            wraplength=840,
        ).pack(anchor="w", pady=(4, 12))

        form = ttk.Frame(self.advanced_tab)
        form.pack(fill="x")
        for i in range(2):
            form.columnconfigure(i * 2 + 1, weight=1)

        ttk.Label(form, text="Offset:").grid(row=0, column=0, sticky="w")
        self.raw_offset_var = tk.StringVar(value="0x808")
        self.raw_offset_entry = ttk.Entry(form, textvariable=self.raw_offset_var)
        self.raw_offset_entry.grid(row=0, column=1, sticky="ew", padx=(8, 18))

        ttk.Label(form, text="Type:").grid(row=0, column=2, sticky="w")
        self.raw_type_var = tk.StringVar(value="u32")
        self.raw_type = ttk.Combobox(
            form,
            textvariable=self.raw_type_var,
            values=("u8", "u16", "u32", "hex bytes"),
            state="readonly",
        )
        self.raw_type.grid(row=0, column=3, sticky="ew", padx=(8, 0))

        ttk.Label(form, text="Value:").grid(row=1, column=0, sticky="w", pady=(10, 0))
        self.raw_value_var = tk.StringVar()
        self.raw_value_entry = ttk.Entry(form, textvariable=self.raw_value_var)
        self.raw_value_entry.grid(row=1, column=1, sticky="ew", padx=(8, 18), pady=(10, 0))

        ttk.Label(form, text="Endian:").grid(row=1, column=2, sticky="w", pady=(10, 0))
        self.raw_endian_var = tk.StringVar(value="Big")
        self.raw_endian = ttk.Combobox(
            form,
            textvariable=self.raw_endian_var,
            values=("Big", "Little"),
            state="readonly",
        )
        self.raw_endian.grid(row=1, column=3, sticky="ew", padx=(8, 0), pady=(10, 0))

        self.raw_apply_btn = ttk.Button(
            self.advanced_tab,
            text="Apply raw patch to working copy",
            command=self.apply_raw_patch,
        )
        self.raw_apply_btn.pack(anchor="w", pady=(14, 0))

        self.raw_preview_var = tk.StringVar(value="")
        ttk.Label(
            self.advanced_tab,
            textvariable=self.raw_preview_var,
            wraplength=840,
        ).pack(anchor="w", pady=(12, 0))

    def _build_info_tab(self):
        text = (
            "PS3 save notes\n\n"
            f"Supported title IDs seen for Knights Contract:\n  {', '.join(SUPPORTED_TITLE_IDS)}\n\n"
            f"Known secure_file_id:\n  {PS3_SECURE_FILE_ID}\n\n"
            "This program edits the decrypted/extracted SAVEDATA.DAT payload only. "
            "A normal PS3 savedata folder may still need to be resigned/rebuilt for your account "
            "with a compatible PS3 savedata tool after editing.\n\n"
            "Verified fields in v0.5:\n"
            f"  Upgrade Points / Souls — offset 0x{UPGRADE_POINTS_OFFSET:08X}, "
            "big-endian uint32, max control 9,999,999.\n"
            f"  Game clear count — offset 0x{GAME_CLEAR_COUNT_OFFSET:08X}.\n"
            f"  Episode-clear counters — offsets 0x{EPISODE_CLEAR_COUNTS_OFFSET:08X}–"
            f"0x{EPISODE_CLEAR_COUNTS_OFFSET + 16:08X}, five big-endian uint32 values.\n"
            "  Completion threshold — 20 episodes per difficulty slot.\n"
            f"  Episode result table — starts at 0x{EPISODE_RESULT_BASE_OFFSET:08X}; "
            f"0x{EPISODE_RESULT_STRIDE:X} bytes per episode and "
            f"0x{EPISODE_RESULT_DIFFICULTY_STRIDE:X} bytes per difficulty.\n"
            f"  Category S rank value — {RESULT_COMPONENT_S_RANK}; overall S+ rank value — "
            f"{RESULT_TOTAL_S_PLUS_RANK}.\n"
            "  Collectible table — 50 Lost Pages (IDs 401–450), nine collectible equipment "
            "(IDs 201–209), six extra Witchcraft collectibles (IDs 332–337).\n"
            "  Permanent max-health support — acquire Seal of Vitality (201) and Seal of Life (204); "
            "no unverified standalone HP integer is written.\n\n"
            "Research workflow for more fields:\n"
            "  1. Keep a baseline save.\n"
            "  2. Change exactly one thing in-game (for example one upgrade, difficulty, or mission score).\n"
            "  3. Save again.\n"
            "  4. Load the baseline here, then use Compare Saves with the second file.\n"
            "  5. Repeat with a second controlled value before naming an offset."
        )
        box = tk.Text(self.info_tab, wrap="word", height=22)
        box.insert("1.0", text)
        box.configure(state="disabled")
        box.pack(fill="both", expand=True)

    def _set_loaded_state(self, loaded: bool):
        state = "normal" if loaded else "disabled"
        for widget in (
            self.save_as_btn,
            self.overwrite_btn,
            self.revert_btn,
            self.max_btn,
            self.apply_points_btn,
            self.unlock_difficulty_btn,
            self.unlock_episode_btn,
            self.unlock_everything_btn,
            self.splus_selected_btn,
            self.splus_all_btn,
            self.manual_game_clear_btn,
            self.manual_episode_clear_btn,
            self.manual_select_all_btn,
            self.manual_clear_selection_btn,
            self.manual_apply_results_btn,
            self.collect_all_btn,
            self.health_equipment_btn,
            self.combat_apply_all_btn,
            self.combat_set_targets_btn,
            *self.combat_apply_buttons,
            *self.combat_target_buttons,
            self.collect_select_all_btn,
            self.collect_clear_selection_btn,
            self.collect_mark_btn,
            self.collect_unmark_btn,
            self.compare_btn,
            self.raw_apply_btn,
        ):
            widget.configure(state=state)

        self.points_entry.configure(state=state)
        for entry in self.combat_entries:
            entry.configure(state=state)
        self.raw_offset_entry.configure(state=state)
        self.raw_value_entry.configure(state=state)
        self.raw_type.configure(state="readonly" if loaded else "disabled")
        self.raw_endian.configure(state="readonly" if loaded else "disabled")
        self.rank_difficulty_combo.configure(state="readonly" if loaded else "disabled")
        self.manual_game_clear_entry.configure(state=state)
        self.manual_episode_clear_spin.configure(state=state)
        self.manual_score_entry.configure(state=state)
        self.manual_progress_difficulty_combo.configure(state="readonly" if loaded else "disabled")
        self.manual_rank_difficulty_combo.configure(state="readonly" if loaded else "disabled")
        self.manual_total_rank_combo.configure(state="readonly" if loaded else "disabled")
        for i in range(5):
            getattr(self, f"manual_component_combo_{i}").configure(state="readonly" if loaded else "disabled")
            getattr(self, f"manual_component_check_{i}").configure(state=state)
        self.manual_total_rank_check.configure(state=state)
        self.manual_score_check.configure(state=state)
        self.manual_unlock_selected_check.configure(state=state)

    def open_save(self):
        path = filedialog.askopenfilename(
            title="Open Knights Contract SAVEDATA.DAT",
            filetypes=[("Knights Contract save", "SAVEDATA.DAT"), ("DAT files", "*.DAT"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            self.save = KnightsContractSave.load(path)
        except Exception as exc:
            messagebox.showerror("Invalid save", str(exc), parent=self)
            return

        self.compare_data = None
        self.compare_path = None
        self.compare_label_var.set("No comparison save loaded")
        self.diff_summary_var.set("")
        self._clear_tree(self.diff_tree)

        self.path_var.set(str(Path(path)))
        self._set_loaded_state(True)
        self.refresh()
        self.status_var.set("Save loaded and validated.")

    def max_points(self):
        self.points_var.set(f"{UPGRADE_POINTS_MAX}")
        self.apply_points()

    def apply_points(self):
        if not self.save:
            return
        try:
            value = parse_int(self.points_var.get())
            self.save.set_upgrade_points(value)
        except Exception as exc:
            messagebox.showerror("Invalid Upgrade Points", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(f"Upgrade Points set to {value:,} in the working copy.")

    def fill_combat_trophy_targets(self):
        self.knights_fury_var.set(str(KNIGHTS_FURY_TROPHY_TARGET - 1))
        self.witchs_embrace_var.set(str(WITCHS_EMBRACE_TROPHY_TARGET - 1))
        self.finisher_var.set(str(FINISHER_TROPHY_TARGET - 1))
        self.apply_all_combat_counts()
        if self.save:
            self.status_var.set("Prepared 199 / 199 / 999. Save, then perform one matching action for each trophy.")

    def _apply_single_combat_counter(self, var: tk.StringVar, setter, label: str):
        if not self.save:
            return
        try:
            value = parse_int(var.get())
            setter(value)
        except Exception as exc:
            messagebox.showerror(label, str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(f"{label} set exactly to {value:,} in the working copy.")

    def apply_knights_fury_count(self):
        if self.save:
            self._apply_single_combat_counter(
                self.knights_fury_var, self.save.set_knights_fury_kill_count, "Knight's Fury kills"
            )

    def apply_witchs_embrace_count(self):
        if self.save:
            self._apply_single_combat_counter(
                self.witchs_embrace_var, self.save.set_witchs_embrace_kill_count, "Witch's Embrace kills"
            )

    def apply_finisher_count(self):
        if self.save:
            self._apply_single_combat_counter(
                self.finisher_var, self.save.set_finisher_count, "Finishers"
            )

    def apply_all_combat_counts(self):
        if not self.save:
            return
        try:
            fury = parse_int(self.knights_fury_var.get())
            embrace = parse_int(self.witchs_embrace_var.get())
            finishers = parse_int(self.finisher_var.get())
            for label, value in (
                ("Knight's Fury kills", fury),
                ("Witch's Embrace kills", embrace),
                ("Finishers", finishers),
            ):
                if not 0 <= value <= COMBAT_COUNTER_MAX:
                    raise ValueError(f"{label} must be between 0 and {COMBAT_COUNTER_MAX:,}.")
            self.save.set_knights_fury_kill_count(fury)
            self.save.set_witchs_embrace_kill_count(embrace)
            self.save.set_finisher_count(finishers)
        except Exception as exc:
            messagebox.showerror("Trophy counters", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(
            f"Combat counters set: Fury {fury:,}, Embrace {embrace:,}, Finishers {finishers:,}."
        )

    def _manual_progress_difficulty_changed(self, _event=None):
        self.refresh_manual_progression_fields()

    def _manual_rank_difficulty_changed(self, _event=None):
        self.refresh_manual_results()

    def _manual_tree_selection_changed(self, _event=None):
        if hasattr(self, "manual_selection_var"):
            self.manual_selection_var.set(f"{len(self.manual_result_tree.selection())} selected")

    def manual_select_all_episodes(self):
        if not self.save:
            return
        self.manual_result_tree.selection_set(self.manual_result_tree.get_children())
        self._manual_tree_selection_changed()

    def manual_clear_episode_selection(self):
        self.manual_result_tree.selection_remove(self.manual_result_tree.selection())
        self._manual_tree_selection_changed()

    def apply_manual_game_clear(self):
        if not self.save:
            return
        try:
            value = parse_int(self.manual_game_clear_var.get())
            self.save.set_game_clear_count(value)
        except Exception as exc:
            messagebox.showerror("Game clear count", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(f"Game clear count set exactly to {value}.")

    def apply_manual_episode_clear(self):
        if not self.save:
            return
        try:
            difficulty_index = DIFFICULTY_INTERNAL_NAMES.index(self.manual_progress_difficulty_var.get())
            value = parse_int(self.manual_episode_clear_var.get())
            self.save.set_episode_clear_count(difficulty_index, value)
        except Exception as exc:
            messagebox.showerror("Episode unlock count", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(
            f"{DIFFICULTY_INTERNAL_NAMES[difficulty_index]} Episode Select count set exactly to {value}."
        )

    @staticmethod
    def _rank_value_from_combo(text: str) -> int:
        return int(text.split("-", 1)[0].strip())

    def apply_manual_result_edits(self):
        if not self.save:
            return
        selected = self.manual_result_tree.selection()
        if not selected:
            messagebox.showerror("Manual result edit", "Select at least one episode row.", parent=self)
            return

        try:
            difficulty_index = DIFFICULTY_INTERNAL_NAMES.index(self.manual_rank_difficulty_var.get())
            episodes = sorted(int(item[2:]) for item in selected if item.startswith("ep"))
            if not episodes:
                raise ValueError("No valid episode rows are selected.")

            component_scores = {}
            component_ranks = {}
            for i, enabled in enumerate(self.manual_component_enabled_vars):
                if enabled.get():
                    component_ranks[i] = self._rank_value_from_combo(self.manual_component_rank_vars[i].get())

            total_rank = None
            if self.manual_total_rank_enabled_var.get():
                total_rank = self._rank_value_from_combo(self.manual_total_rank_var.get())
                if total_rank == RESULT_TOTAL_S_PLUS_RANK:
                    component_ranks = {i: RESULT_COMPONENT_S_RANK for i in range(5)}
                    component_scores = {i: RESULT_S_PLUS_SCORE_VALUES[i] for i in range(5)}

            total_score = None
            if self.manual_score_enabled_var.get():
                total_score = parse_int(self.manual_score_var.get())
            elif total_rank == RESULT_TOTAL_S_PLUS_RANK:
                total_score = RESULT_S_PLUS_TOTAL_SCORE

            unlock = self.manual_unlock_selected_var.get()
            if not component_scores and not component_ranks and total_rank is None and total_score is None and not unlock:
                raise ValueError("Tick at least one field to edit, or tick the Episode Select unlock option.")

            for episode_index in episodes:
                self.save.set_episode_result_fields(
                    episode_index,
                    difficulty_index,
                    component_scores=component_scores or None,
                    component_ranks=component_ranks or None,
                    total_score=total_score,
                    total_rank=total_rank,
                )

            if unlock:
                self.save.set_game_clear_count_minimum(1)
                required = max(episodes) + 1
                current = self.save.episode_clear_counts[difficulty_index]
                if current < required:
                    self.save.set_episode_clear_count(difficulty_index, required)

        except Exception as exc:
            messagebox.showerror("Manual result edit", str(exc), parent=self)
            return

        self.refresh()
        for episode_index in episodes:
            iid = f"ep{episode_index}"
            if self.manual_result_tree.exists(iid):
                self.manual_result_tree.selection_add(iid)
        self._manual_tree_selection_changed()
        fields = []
        if component_scores:
            fields.append("result points")
        if component_ranks:
            fields.append("selected categories")
        if total_rank is not None:
            fields.append("overall rank")
        if total_score is not None:
            fields.append("score")
        if unlock:
            fields.append("Episode Select progress")
        self.status_var.set(
            f"Edited {len(episodes)} episode record(s) on {DIFFICULTY_INTERNAL_NAMES[difficulty_index]}: "
            + ", ".join(fields)
        )

    def unlock_all_difficulties(self):
        if not self.save:
            return
        before = self.save.episode_clear_counts
        self.save.unlock_all_difficulties()
        self.refresh()
        after = self.save.episode_clear_counts
        self.status_var.set(
            f"All difficulties unlocked. Episode counts: {before} -> {after}"
        )

    def unlock_all_episodes(self):
        if not self.save:
            return
        before = self.save.episode_clear_counts
        self.save.unlock_episode_select_all()
        self.refresh()
        after = self.save.episode_clear_counts
        self.status_var.set(
            f"Episode Select unlocked for all 20 episodes on all slots: {before} -> {after}"
        )

    def unlock_all_progression(self):
        if not self.save:
            return
        self.save.unlock_all_progression()
        self.refresh()
        self.status_var.set(
            "Episode Select and all difficulty progression unlocked in the working copy."
        )

    def set_selected_difficulty_s_plus(self):
        if not self.save:
            return
        try:
            difficulty_index = DIFFICULTY_INTERNAL_NAMES.index(self.rank_difficulty_var.get())
            before = self.save.s_plus_count(difficulty_index)
            self.save.set_difficulty_all_s_plus(difficulty_index)
            after = self.save.s_plus_count(difficulty_index)
        except Exception as exc:
            messagebox.showerror("S+ rank error", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set(
            f"{DIFFICULTY_INTERNAL_NAMES[difficulty_index]}: S+ episode ranks "
            f"{before}/{EPISODE_RESULT_COUNT} -> {after}/{EPISODE_RESULT_COUNT}."
        )

    def set_all_s_plus(self):
        if not self.save:
            return
        before = tuple(self.save.s_plus_count(i) for i in range(EPISODE_CLEAR_COUNT_SLOTS))
        self.save.set_all_difficulties_all_s_plus()
        after = tuple(self.save.s_plus_count(i) for i in range(EPISODE_CLEAR_COUNT_SLOTS))
        self.refresh()
        self.status_var.set(
            f"All 100 episode/difficulty result records set to S+. {before} -> {after}"
        )

    def collect_all_items(self):
        if not self.save:
            return
        before = self.save.collectible_counts()
        try:
            self.save.set_all_collectibles()
        except Exception as exc:
            messagebox.showerror("Collectibles error", str(exc), parent=self)
            return
        self.refresh()
        after = self.save.collectible_counts()
        self.status_var.set(f"All collectible groups set to collected: {before} -> {after}")

    def acquire_max_health_equipment(self):
        if not self.save:
            return
        try:
            self.save.set_max_health_equipment_acquired()
        except Exception as exc:
            messagebox.showerror("Health equipment error", str(exc), parent=self)
            return
        self.refresh()
        self.status_var.set("Seal of Vitality and Seal of Life set to acquired.")

    def select_all_collectibles(self):
        if not self.save:
            return
        self.collectible_tree.selection_set(self.collectible_tree.get_children())

    def clear_collectible_selection(self):
        self.collectible_tree.selection_remove(self.collectible_tree.selection())

    def set_selected_collectibles(self, collected: bool):
        if not self.save:
            return
        selected = self.collectible_tree.selection()
        if not selected:
            messagebox.showinfo("No collectibles selected", "Select one or more collectible rows first.", parent=self)
            return
        item_ids = []
        for iid in selected:
            try:
                item_ids.append(int(iid.split("_", 1)[1]))
            except Exception:
                continue
        if not item_ids:
            return
        try:
            self.save.set_items_collected(item_ids, collected)
        except Exception as exc:
            messagebox.showerror("Collectibles error", str(exc), parent=self)
            return
        self.refresh()
        state_text = "collected" if collected else "not collected"
        self.status_var.set(f"Set {len(item_ids)} selected collectible(s) to {state_text}.")

    def apply_raw_patch(self):
        if not self.save:
            return
        try:
            offset = parse_int(self.raw_offset_var.get())
            kind = self.raw_type_var.get()
            endian = ">" if self.raw_endian_var.get() == "Big" else "<"
            value_text = self.raw_value_var.get()

            if kind == "hex bytes":
                payload = parse_hex_bytes(value_text)
            else:
                value = parse_int(value_text)
                fmts = {"u8": "B", "u16": "H", "u32": "I"}
                limits = {"u8": 0xFF, "u16": 0xFFFF, "u32": 0xFFFFFFFF}
                if not 0 <= value <= limits[kind]:
                    raise ValueError(f"{kind} must be between 0 and {limits[kind]:,}.")
                payload = struct.pack(endian + fmts[kind], value)

            end = offset + len(payload)
            if end > len(self.save.data):
                raise ValueError(
                    f"Patch ends at 0x{end:X}, beyond save size 0x{len(self.save.data):X}."
                )

            before = bytes(self.save.data[offset:end])
            if not messagebox.askyesno(
                "Confirm raw patch",
                (
                    f"Offset: 0x{offset:08X}\n"
                    f"Before: {before.hex(' ').upper() or '(empty)'}\n"
                    f"After:  {payload.hex(' ').upper()}\n\n"
                    "Apply this patch to the working copy?"
                ),
                parent=self,
            ):
                return

            self.save.raw_patch(offset, payload)
            self.raw_preview_var.set(
                f"Applied at 0x{offset:08X}: "
                f"{before.hex(' ').upper()} -> {payload.hex(' ').upper()}"
            )
            self.refresh()
            self.status_var.set("Raw patch applied to working copy.")
        except Exception as exc:
            messagebox.showerror("Raw patch error", str(exc), parent=self)

    def revert_all(self):
        if not self.save:
            return
        if self.save.changed_spans() and not messagebox.askyesno(
            "Revert all changes",
            "Discard every unsaved edit and restore the originally loaded bytes?",
            parent=self,
        ):
            return
        self.save.revert_all()
        self.refresh()
        self.status_var.set("Working copy restored to the originally loaded save.")

    def open_compare(self):
        if not self.save:
            return
        path = filedialog.askopenfilename(
            title="Open comparison SAVEDATA.DAT",
            filetypes=[("Knights Contract save", "SAVEDATA.DAT"), ("DAT files", "*.DAT"), ("All files", "*.*")],
        )
        if not path:
            return

        try:
            data = Path(path).read_bytes()
            result = validate_save(data)
            if not result.ok:
                raise ValueError("\n".join(result.messages))
        except Exception as exc:
            messagebox.showerror("Invalid comparison save", str(exc), parent=self)
            return

        self.compare_data = data
        self.compare_path = Path(path)
        self.compare_label_var.set(str(self.compare_path))
        self.refresh_compare()

    def save_as(self):
        if not self.save:
            return
        initial = "SAVEDATA.DAT"
        path = filedialog.asksaveasfilename(
            title="Save edited Knights Contract data",
            initialfile=initial,
            defaultextension=".DAT",
            filetypes=[("DAT files", "*.DAT"), ("All files", "*.*")],
        )
        if not path:
            return
        self._perform_save(Path(path))

    def save_overwrite(self):
        if not self.save:
            return
        if self.save.path is None:
            self.save_as()
            return

        if not messagebox.askyesno(
            "Overwrite save",
            (
                f"Overwrite:\n{self.save.path}\n\n"
                "A .bak copy of the current file will be created first."
            ),
            parent=self,
        ):
            return
        self._perform_save(self.save.path)

    def _perform_save(self, path: Path):
        if not self.save:
            return
        try:
            result = validate_save(self.save.data)
            if not result.ok:
                raise ValueError("\n".join(result.messages))
            written = self.save.save_atomic(path, backup=True)
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc), parent=self)
            return

        self.status_var.set(f"Saved edited data: {written}")
        messagebox.showinfo(
            "Saved",
            (
                f"Edited SAVEDATA.DAT written to:\n{written}\n\n"
                "If this is going back to a PS3 savedata folder, resign/rebuild the "
                "savedata container for the target account as required."
            ),
            parent=self,
        )

    def refresh_manual_progression_fields(self):
        if not self.save:
            return
        self.manual_game_clear_var.set(str(self.save.game_clear_count))
        try:
            difficulty_index = DIFFICULTY_INTERNAL_NAMES.index(self.manual_progress_difficulty_var.get())
        except ValueError:
            difficulty_index = 0
            self.manual_progress_difficulty_var.set(DIFFICULTY_INTERNAL_NAMES[0])
        self.manual_episode_clear_var.set(str(self.save.episode_clear_counts[difficulty_index]))

    @staticmethod
    def _format_component_rank(value: int) -> str:
        if 0 <= value < len(RESULT_COMPONENT_RANK_LABELS):
            return f"{RESULT_COMPONENT_RANK_LABELS[value]} ({value})"
        return f"raw {value}"

    @staticmethod
    def _format_total_rank(value: int) -> str:
        if 0 <= value < len(RESULT_TOTAL_RANK_LABELS):
            return f"{RESULT_TOTAL_RANK_LABELS[value]} ({value})"
        return f"raw {value}"

    def refresh_manual_results(self):
        if not self.save:
            return
        try:
            difficulty_index = DIFFICULTY_INTERNAL_NAMES.index(self.manual_rank_difficulty_var.get())
        except ValueError:
            difficulty_index = 0
            self.manual_rank_difficulty_var.set(DIFFICULTY_INTERNAL_NAMES[0])

        old_selection = set(self.manual_result_tree.selection())
        self._clear_tree(self.manual_result_tree)
        for episode_index in range(EPISODE_RESULT_COUNT):
            components = self.save.episode_component_ranks(episode_index, difficulty_index)
            total_rank = self.save.episode_total_rank(episode_index, difficulty_index)
            total_score = self.save.episode_total_score(episode_index, difficulty_index)
            iid = f"ep{episode_index}"
            self.manual_result_tree.insert(
                "",
                "end",
                iid=iid,
                values=(
                    episode_index + 1,
                    self._format_total_rank(total_rank),
                    f"{total_score:,}",
                    *(self._format_component_rank(value) for value in components),
                ),
            )
        for iid in old_selection:
            if self.manual_result_tree.exists(iid):
                self.manual_result_tree.selection_add(iid)
        self._manual_tree_selection_changed()

    def refresh_collectibles(self):
        if not self.save:
            return
        counts = self.save.collectible_counts()
        lost_owned, lost_total = counts["Lost Pages"]
        equip_owned, equip_total = counts["Equipment"]
        witch_owned, witch_total = counts["Extra Witchcraft"]
        total_owned = lost_owned + equip_owned + witch_owned
        total = lost_total + equip_total + witch_total
        self.collect_lost_var.set(f"{lost_owned} / {lost_total}")
        self.collect_equipment_var.set(f"{equip_owned} / {equip_total}")
        self.collect_witch_var.set(f"{witch_owned} / {witch_total}")
        self.collect_total_var.set(f"{total_owned} / {total}")

        health_parts = []
        for item_id, name in MAX_HEALTH_EQUIPMENT_ITEMS:
            owned = self.save.item_state(item_id) != 0
            health_parts.append(f"{name}: {'acquired' if owned else 'missing'}")
        self.health_status_var.set(" | ".join(health_parts))

        old_selection = set(self.collectible_tree.selection())
        self._clear_tree(self.collectible_tree)
        for category, item_id, name in ALL_COLLECTIBLE_ITEMS:
            offset = self.save._find_item_record_offset(item_id)
            state = self.save.item_state(item_id)
            iid = f"item_{item_id}"
            self.collectible_tree.insert(
                "",
                "end",
                iid=iid,
                values=(
                    category,
                    name,
                    f"{item_id} / 0x{item_id:04X}",
                    f"0x{offset:08X}",
                    "Collected" if state != 0 else "Not collected",
                ),
            )
        for iid in old_selection:
            if self.collectible_tree.exists(iid):
                self.collectible_tree.selection_add(iid)

    def refresh(self):
        if not self.save:
            return

        self.points_var.set(str(self.save.upgrade_points))
        self.knights_fury_var.set(str(self.save.knights_fury_kill_count))
        self.witchs_embrace_var.set(str(self.save.witchs_embrace_kill_count))
        self.finisher_var.set(str(self.save.finisher_count))
        self.game_clear_var.set(str(self.save.game_clear_count))
        self.refresh_manual_progression_fields()
        self.refresh_manual_results()
        self.refresh_collectibles()
        self._clear_tree(self.progress_tree)
        for index, count in enumerate(self.save.episode_clear_counts):
            state = "All 20 episodes" if count >= EPISODES_PER_DIFFICULTY else f"Through episode {count}"
            self.progress_tree.insert(
                "",
                "end",
                values=(index, DIFFICULTY_INTERNAL_NAMES[index], f"{count} / {EPISODES_PER_DIFFICULTY}", state),
            )

        self._clear_tree(self.rank_tree)
        for index, name in enumerate(DIFFICULTY_INTERNAL_NAMES):
            self.rank_tree.insert(
                "",
                "end",
                values=(index, name, f"{self.save.s_plus_count(index)} / {EPISODE_RESULT_COUNT}"),
            )

        self.file_size_var.set(f"0x{len(self.save.data):X} ({len(self.save.data):,} bytes)")
        self.original_hash_var.set(sha256_hex(self.save.original))
        self.hash_var.set(sha256_hex(self.save.data))

        spans = self.save.changed_spans()
        self.change_count_var.set(str(len(spans)))
        self._clear_tree(self.change_tree)

        for span in spans:
            self.change_tree.insert(
                "",
                "end",
                values=(
                    self._format_range(span),
                    span.old.hex(" ").upper(),
                    span.new.hex(" ").upper(),
                ),
            )

        if self.compare_data is not None:
            self.refresh_compare()

    def refresh_compare(self):
        if not self.save or self.compare_data is None:
            return
        spans = group_differences(self.save.data, self.compare_data)
        self._clear_tree(self.diff_tree)

        total_bytes = 0
        for span in spans:
            total_bytes += max(len(span.old), len(span.new))
            self.diff_tree.insert(
                "",
                "end",
                values=(
                    self._format_range(span),
                    max(len(span.old), len(span.new)),
                    span.old.hex(" ").upper(),
                    span.new.hex(" ").upper(),
                ),
            )

        self.diff_summary_var.set(
            f"{len(spans)} changed span(s), {total_bytes} changed byte position(s)."
        )
        self.status_var.set(
            f"Compared saves: {len(spans)} changed span(s), {total_bytes} byte position(s)."
        )

    @staticmethod
    def _format_range(span: DiffSpan) -> str:
        if span.end <= span.start:
            return f"0x{span.start:08X}"
        return f"0x{span.start:08X}–0x{span.end:08X}"

    @staticmethod
    def _clear_tree(tree: ttk.Treeview):
        for item in tree.get_children():
            tree.delete(item)


def main():
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
