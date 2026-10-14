# Bryan Music Manager

![Bryan Music Manager logo](bryan_logo_full.png)

A free desktop app for organizing your music library. Built with Python.

<img width="1920" height="1080" alt="Screenshot (7)" src="https://github.com/user-attachments/assets/a6a34a0c-c4d8-42dd-b072-d51f1fccfc92" />


## Features
- Keep your songs in numerical order (reorder, or sort by title, artist, BPM, key or colour)
- Edit metadata and add cover art (MP3, M4A, MP4, FLAC)
- Automatic **BPM** and **musical key** detection, saved into the file tags
- **Colour-code** songs manually or automatically by key
- Convert between MP3, M4A, MP4, WAV and FLAC

## Install (Windows)
1. Install [Python](https://www.python.org/downloads/) (tick **Add Python to PATH**).
2. Install [FFmpeg](https://www.gyan.dev/ffmpeg/builds/) and put `ffmpeg.exe` in the same folder as the app, or add it to your PATH.
3. Download this project and open a terminal in its folder.
4. Run: `pip install -r requirements.txt`
5. Start the app: `python music_manager.py`

## Notes
- BPM detection can occasionally come out at half or double speed on unusual tracks.
- Your library list is stored locally in `library.json`.
- This project does not include any music or FFmpeg.

## License
GPL-3.0. See the `LICENSE` file.
