# Knights Contract PS3 Save Editor

Windows save editor for **Knights Contract** on PlayStation 3.

## Download

Use [`KnightsContract_SaveEditor_v1.0_RankFix.exe`](./KnightsContract_SaveEditor_v1.0_RankFix.exe), or download the complete [`v1.0 RankFix ZIP`](./KnightsContract_SaveEditor_v1.0_RankFix.zip).

Always keep a backup of your original save before editing it.

## v1.0 Rank Fix

This version fixes the S+ episode-rank edit by updating both the grade fields and the five displayed result-point fields. It uses the game's difficulty names:

| Game difficulty | Internal slot |
| --- | --- |
| Page | Easy |
| Squire | Normal |
| Knight | Hard |
| Hexen Knight | Very Hard |
| Witchslayer | Hell |

The **Force S+** operation writes consistent component grades, point values, total points, and overall grade.

## Files

- `KnightsContract_SaveEditor_v1.0_RankFix.exe` — 64-bit Windows GUI application (no console window)
- `KnightsContract_SaveEditor_v1.0_NoConsole.pyw` — Python source
- `KnightsContract_SaveEditor_v1.0_RankFix.zip` — complete packaged release
- `KnightsContract_SaveEditor_v1.0_RankFix_README.txt` — detailed technical notes and verified values

## Integrity

SHA-256 for the Windows executable:

```text
422ae0f25b271f3627ee8982fd099b305a715c0b48e68ea5f4ec7bb6f60cf395
```

## Running from source

Python 3 with Tkinter is required:

```text
py KnightsContract_SaveEditor_v1.0_NoConsole.pyw
```

## Important

This is an unofficial fan-made tool. Back up your save before making changes.
