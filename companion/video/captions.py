"""Turn the caption logs of the rendered scenes into a subtitle file and a narration script.

Usage: python3 captions.py SCENE_LIST DURATIONS_FILE
SCENE_LIST is the order of the scenes, DURATIONS_FILE holds one duration in seconds per line.
"""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
scenes = sys.argv[1].split(",")
durations = [float(x) for x in Path(sys.argv[2]).read_text().split()]


def stamp(t, srt=True):
    h, rem = divmod(t, 3600)
    m, s = divmod(rem, 60)
    if srt:
        return f"{int(h):02d}:{int(m):02d}:{int(s):02d},{int(round((s - int(s)) * 1000)):03d}"
    return f"{int(m)}:{int(s):02d}"


cues = []
offset = 0.0
for name, dur in zip(scenes, durations):
    log = json.loads((HERE / "captions" / f"{name}.json").read_text())
    for cur, nxt in zip(log, log[1:]):
        if cur["text"]:
            cues.append((offset + cur["t"], offset + min(nxt["t"], dur), cur["text"], name))
    offset += dur

srt = []
for i, (a, b, text, _) in enumerate(cues, 1):
    srt.append(f"{i}\n{stamp(a)} --> {stamp(b)}\n{text}\n")
(HERE / "real_power_cauchy_schwarz.srt").write_text("\n".join(srt))

md = [
    "# Narration script",
    "",
    "These are the captions of the video with their start times. They are written to be read aloud, so the same text can be recorded as a voice-over. Each line should take no longer than the gap to the next start time.",
    "",
    "| Start | Scene | Text |",
    "| --- | --- | --- |",
]
for a, b, text, name in cues:
    md.append(f"| {stamp(a, srt=False)} | {name[3:]} | {text} |")
md.append("")
md.append(f"Total length: {stamp(offset, srt=False)}.")
(HERE / "narration.md").write_text("\n".join(md) + "\n")
print(f"{len(cues)} captions, {offset:.1f} s")
