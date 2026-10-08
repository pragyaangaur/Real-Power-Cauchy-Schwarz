"""Write a quiet ambient pad of a given length to a WAV file.

Usage: python3 music.py SECONDS OUT.wav
"""

import sys
import wave

import numpy as np
from scipy.signal import lfilter

RATE = 44100
seconds = float(sys.argv[1])
out = sys.argv[2]

# A slow progression in A minor: Am(add9), Fmaj7, C(add9), G6. Each chord lasts 8 seconds.
CHORDS = [
    [57, 64, 67, 71, 72],
    [53, 60, 64, 69, 72],
    [48, 55, 62, 64, 67],
    [55, 59, 62, 64, 71],
]
CHORD_LEN = 8.0


def freq(midi):
    return 440.0 * 2 ** ((midi - 69) / 12)


n = int(seconds * RATE)
t = np.arange(n) / RATE
signal = np.zeros(n)
rng = np.random.default_rng(7)
k = 0
start = 0.0
while start < seconds:
    chord = CHORDS[k % len(CHORDS)]
    # Each chord fades in over 2.5 s and out over 3 s, overlapping the next one.
    a, b = int(start * RATE), min(n, int((start + CHORD_LEN + 3.0) * RATE))
    tt = t[a:b] - start
    env = np.minimum(1.0, tt / 2.5) * np.clip((CHORD_LEN + 3.0 - tt) / 3.0, 0, 1)
    for note in chord:
        f = freq(note)
        for detune, amp in ((0.0, 1.0), (0.12, 0.6), (-0.1, 0.6)):
            phase = rng.uniform(0, 2 * np.pi)
            tone = np.sin(2 * np.pi * (f + detune) * tt + phase)
            tone += 0.18 * np.sin(2 * np.pi * 2 * (f + detune) * tt + phase)
            signal[a:b] += amp * env * tone / (1 + (note - 48) / 24)
    start += CHORD_LEN
    k += 1

# Slow tremolo and a gentle one-pole low-pass filter soften the sound.
signal *= 0.85 + 0.15 * np.sin(2 * np.pi * 0.07 * t)
alpha = 0.08
filtered = lfilter([alpha], [1, alpha - 1], signal)
# Fade in and out of the whole track.
fade = np.minimum(1.0, t / 4.0) * np.clip((seconds - t) / 5.0, 0, 1)
filtered *= fade
filtered /= np.abs(filtered).max()
filtered *= 0.5

stereo = np.stack([filtered, np.roll(filtered, int(0.012 * RATE))], axis=1)
pcm = (stereo * 32767).astype(np.int16)
with wave.open(out, "wb") as w:
    w.setnchannels(2)
    w.setsampwidth(2)
    w.setframerate(RATE)
    w.writeframes(pcm.tobytes())
