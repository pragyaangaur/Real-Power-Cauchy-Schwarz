#!/bin/sh
# Render every scene at 1080p and 30 frames per second, join them, add the music bed and
# write the subtitle file and the narration script.
#
# Usage: MANIM=/path/to/manim ./build.sh
set -e
cd "$(dirname "$0")"
MANIM="${MANIM:-manim}"
MEDIA="${MEDIA:-media}"
SCENES="S01Title S02CauchySchwarz S03Powers S04History S05Tensor S06Matrices S07Cone S08Phi S09NewResults S10Lean S11Applications S12Outro"

"$MANIM" -r 1920,1080 --fps 30 --media_dir "$MEDIA" scenes.py $SCENES

DIR="$MEDIA/videos/scenes/1080p30"
: > list.txt
: > durations.txt
for s in $SCENES; do
  echo "file '$DIR/$s.mp4'" >> list.txt
  ffprobe -v error -show_entries format=duration -of csv=p=0 "$DIR/$s.mp4" >> durations.txt
done
ffmpeg -y -v error -f concat -safe 0 -i list.txt -c copy silent.mp4
TOTAL=$(ffprobe -v error -show_entries format=duration -of csv=p=0 silent.mp4)
python3 music.py "$TOTAL" music.wav
ffmpeg -y -v error -i silent.mp4 -i music.wav -map 0:v -map 1:a -c:v libx264 -preset slow -crf 18 -pix_fmt yuv420p -c:a aac -b:a 160k -af "volume=0.55" -shortest -movflags +faststart real_power_cauchy_schwarz.mp4
python3 captions.py "$(echo $SCENES | tr ' ' ',')" durations.txt
"$MANIM" -s -r 1920,1080 --media_dir "$MEDIA" -o thumbnail scenes.py Thumbnail
cp "$MEDIA/images/scenes/thumbnail.png" thumbnail.png
rm -f list.txt durations.txt silent.mp4 music.wav
echo "done: real_power_cauchy_schwarz.mp4 ($TOTAL s)"
