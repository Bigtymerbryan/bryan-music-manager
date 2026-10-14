"""
Music Manager - a desktop music library tool for Windows/Mac/Linux.

Features
  * Library in numerical order (reorder with Up/Down or sort by BPM/Key/Title/Artist)
  * Metadata editing + cover image input (MP3, M4A, MP4, FLAC)
  * BPM and musical key detection (stored in the library and written to file tags)
  * Colour coding per song (manual or automatic by key)
  * Format conversion (MP3, M4A, MP4, WAV, FLAC) via FFmpeg

Setup:  pip install -r requirements.txt   and install FFmpeg (see README steps).
Run:    python music_manager.py
"""
import base64
import colorsys
import io
import json
import os
import shutil
import subprocess
import tempfile
import threading
import tkinter as tk
from pathlib import Path
from tkinter import colorchooser, filedialog, messagebox, ttk

import mutagen
import numpy as np
from mutagen.flac import FLAC, Picture
from mutagen.id3 import APIC, ID3, TBPM, TKEY, TRCK, ID3NoHeaderError
from mutagen.mp4 import MP4, MP4Cover, MP4FreeForm
from PIL import Image, ImageTk

AUDIO_EXTS = {".mp3", ".m4a", ".mp4", ".wav", ".flac", ".ogg", ".aac", ".wma"}
LIB_FILE = Path(__file__).with_name("library.json")
LOGO_FILE = Path(__file__).with_name("bryan_logo.png")  # optional: replace the built-in logo with your own
LOGO_B64 = "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"  # built-in logo, so no extra file is needed

# ---- CHANGE THESE LINES TO CUSTOMISE THE APP ----
APP_NAME = "Bryan Music Manager"   # shown in the title bar and header
COLOR_LEFT = "#2f7bf5"              # blue side of the two-tone look
COLOR_RIGHT = "#8e44e8"             # purple side of the two-tone look
# --------------------------------------------------


def _hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def _blend(c1, c2, t):
    a, b = _hex_to_rgb(c1), _hex_to_rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


THEME_COLOR = _blend(COLOR_LEFT, COLOR_RIGHT, 0.5)  # used for selected rows
NOTES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
MAJOR = np.array([6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88])
MINOR = np.array([6.33, 2.68, 3.52, 5.38, 2.60, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17])
CONVERT_FORMATS = ["mp3", "m4a", "mp4", "wav", "flac"]
PRESET_COLORS = {
    "Red": "#f4a6a6", "Orange": "#f8c99a", "Yellow": "#f6ec9e", "Green": "#a9e3a9",
    "Teal": "#9adfd6", "Blue": "#a5c8f4", "Purple": "#cdb0ee", "Pink": "#f3b3da",
    "Grey": "#d0d0d0", "None": "",
}


# ----------------------------------------------------------------------------
# Tag helpers
# ----------------------------------------------------------------------------
def read_tags(path):
    t = {"path": path, "title": Path(path).stem, "artist": "", "album": "", "genre": "",
         "year": "", "bpm": None, "key": "", "color": ""}
    try:
        f = mutagen.File(path, easy=True)
        if f is not None and f.tags:
            def g(k):
                v = f.tags.get(k)
                return str(v[0]) if v else ""
            t["title"] = g("title") or t["title"]
            t["artist"], t["album"], t["genre"] = g("artist"), g("album"), g("genre")
            t["year"] = g("date")[:4]
            bpm = g("bpm")
            if bpm:
                t["bpm"] = float(bpm)
            t["key"] = g("initialkey")
    except Exception:
        pass
    return t


def write_basic_tags(t):
    f = mutagen.File(t["path"], easy=True)
    if f is None:
        return
    if f.tags is None:
        f.add_tags()
    for k, v in (("title", t["title"]), ("artist", t["artist"]), ("album", t["album"]),
                 ("genre", t["genre"]), ("date", t["year"])):
        if v:
            f[k] = v
        elif k in f:
            del f[k]
    f.save()


def write_extra_tags(t, track_no=None):
    """BPM / key / track number in each format's native tag."""
    p, ext = t["path"], Path(t["path"]).suffix.lower()
    bpm = int(round(t["bpm"])) if t.get("bpm") else None
    key = t.get("key") or ""
    if ext == ".mp3":
        try:
            tags = ID3(p)
        except ID3NoHeaderError:
            tags = ID3()
        if bpm:
            tags.setall("TBPM", [TBPM(encoding=3, text=str(bpm))])
        if key:
            tags.setall("TKEY", [TKEY(encoding=3, text=key)])
        if track_no:
            tags.setall("TRCK", [TRCK(encoding=3, text=str(track_no))])
        tags.save(p)
    elif ext in (".m4a", ".mp4"):
        mp = MP4(p)
        if bpm:
            mp["tmpo"] = [bpm]
        if key:
            mp["----:com.apple.iTunes:initialkey"] = [MP4FreeForm(key.encode())]
        if track_no:
            mp["trkn"] = [(track_no, 0)]
        mp.save()
    elif ext == ".flac":
        fl = FLAC(p)
        if bpm:
            fl["bpm"] = str(bpm)
        if key:
            fl["initialkey"] = key
        if track_no:
            fl["tracknumber"] = str(track_no)
        fl.save()


def get_cover(path):
    ext = Path(path).suffix.lower()
    try:
        if ext == ".mp3":
            pics = ID3(path).getall("APIC")
            return pics[0].data if pics else None
        if ext in (".m4a", ".mp4"):
            c = MP4(path).get("covr")
            return bytes(c[0]) if c else None
        if ext == ".flac":
            pics = FLAC(path).pictures
            return pics[0].data if pics else None
    except Exception:
        pass
    return None


def set_cover(path, image_path):
    data = Path(image_path).read_bytes()
    is_png = image_path.lower().endswith(".png")
    mime = "image/png" if is_png else "image/jpeg"
    ext = Path(path).suffix.lower()
    if ext == ".mp3":
        try:
            tags = ID3(path)
        except ID3NoHeaderError:
            tags = ID3()
        tags.delall("APIC")
        tags.add(APIC(encoding=3, mime=mime, type=3, desc="Cover", data=data))
        tags.save(path)
    elif ext in (".m4a", ".mp4"):
        mp = MP4(path)
        fmt = MP4Cover.FORMAT_PNG if is_png else MP4Cover.FORMAT_JPEG
        mp["covr"] = [MP4Cover(data, imageformat=fmt)]
        mp.save()
    elif ext == ".flac":
        fl = FLAC(path)
        pic = Picture()
        pic.type, pic.mime, pic.data = 3, mime, data
        fl.clear_pictures()
        fl.add_picture(pic)
        fl.save()
    else:
        raise ValueError("Cover art isn't supported for this file type.")


# ----------------------------------------------------------------------------
# Analysis (BPM + key)
# ----------------------------------------------------------------------------
def analyze(path):
    import librosa  # imported lazily: slow to load

    tmp = None
    try:
        try:
            y, sr = librosa.load(path, sr=22050, mono=True, duration=150)
        except Exception:
            # Fallback: let FFmpeg decode to a temporary WAV first
            tmp = os.path.join(tempfile.gettempdir(), "mm_analysis.wav")
            subprocess.run(["ffmpeg", "-y", "-i", path, "-vn", "-t", "150", tmp],
                           check=True, capture_output=True)
            y, sr = librosa.load(tmp, sr=22050, mono=True)
    finally:
        if tmp and os.path.exists(tmp):
            os.remove(tmp)

    tempo, _ = librosa.beat.beat_track(y=y, sr=sr)
    bpm = float(np.atleast_1d(tempo)[0])

    chroma = librosa.feature.chroma_cens(y=librosa.effects.harmonic(y), sr=sr).mean(axis=1)
    best, best_score = ("C", "major"), -2
    for i in range(12):
        for profile, mode in ((MAJOR, "major"), (MINOR, "minor")):
            score = np.corrcoef(chroma, np.roll(profile, i))[0, 1]
            if score > best_score:
                best, best_score = (NOTES[i], mode), score
    note, mode = best
    return round(bpm, 1), f"{note}{'m' if mode == 'minor' else ''}"


def key_color(key):
    """Automatic colour: hue from the note, lighter for major, deeper for minor."""
    if not key:
        return ""
    minor = key.endswith("m")
    note = key[:-1] if minor else key
    if note not in NOTES:
        return ""
    r, g, b = colorsys.hsv_to_rgb(NOTES.index(note) / 12, 0.35 if not minor else 0.55, 0.97 if not minor else 0.88)
    return "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))


class GradientBar(tk.Canvas):
    """Blue-to-purple gradient canvas. Text and widgets sit on it with a see-through look."""

    def __init__(self, parent, height=40, text="", textvariable=None, font=("Segoe UI", 11), **kw):
        super().__init__(parent, height=height, highlightthickness=0, bd=0, **kw)
        self.bar_h = height
        self.var = textvariable
        self.text_id = self.create_text(12, height // 2, text=text, anchor="w", fill="white", font=font)
        self._x = 10
        if textvariable is not None:
            self.itemconfig(self.text_id, text=textvariable.get())
            textvariable.trace_add("write", lambda *a: self.itemconfig(self.text_id, text=self.var.get()))
        self.bind("<Configure>", self.redraw)

    def redraw(self, event=None):
        self.delete("grad")
        w, h = max(self.winfo_width(), 2), max(self.winfo_height(), 2)
        for x in range(0, w, 2):
            self.create_rectangle(x, 0, x + 2, h, outline="", fill=_blend(COLOR_LEFT, COLOR_RIGHT, x / w), tags="grad")
        self.tag_lower("grad")

    def add_label(self, text):
        item = self.create_text(self._x, self.bar_h // 2, text=text, anchor="w", fill="white",
                                font=("Segoe UI", 10, "bold"))
        self._x = self.bbox(item)[2] + 6

    def add_widget(self, widget, pad=4):
        self.create_window(self._x, self.bar_h // 2, window=widget, anchor="w")
        self.update_idletasks()
        self._x += widget.winfo_reqwidth() + pad

    def add_gap(self, px=14):
        self._x += px


# ----------------------------------------------------------------------------
# Metadata editor window
# ----------------------------------------------------------------------------
class EditDialog(tk.Toplevel):
    def __init__(self, parent, track, on_save):
        super().__init__(parent)
        self.title("Edit Metadata")
        self.track, self.on_save, self.new_cover = track, on_save, None
        self.resizable(False, False)
        self.transient(parent)

        cv = GradientBar(self, height=270, width=580)
        cv.pack(fill="both", expand=True)
        self.vars = {}
        for n, (label, key) in enumerate([("Title", "title"), ("Artist", "artist"), ("Album", "album"),
                                          ("Genre", "genre"), ("Year", "year")]):
            y = 30 + n * 38
            cv.create_text(20, y, text=label, anchor="w", fill="white", font=("Segoe UI", 10, "bold"))
            self.vars[key] = tk.StringVar(value=track[key])
            cv.create_window(95, y, window=ttk.Entry(cv, textvariable=self.vars[key], width=34), anchor="w")

        self.cover_label = tk.Label(cv, text="No cover", width=22, height=9, bg="white", relief="groove")
        cv.create_window(400, 14, window=self.cover_label, anchor="nw")
        self._show_cover(get_cover(track["path"]))
        cv.create_window(400, 215, window=ttk.Button(cv, text="Choose cover image...", command=self.pick_cover),
                         anchor="nw")
        cv.create_window(95, 235, window=ttk.Button(cv, text="Save", command=self.save), anchor="w")

    def _show_cover(self, data=None, path=None):
        try:
            img = Image.open(io.BytesIO(data)) if data else Image.open(path) if path else None
            if img is None:
                return
            img.thumbnail((150, 150))
            self._photo = ImageTk.PhotoImage(img)
            self.cover_label.config(image=self._photo, text="", width=150, height=150)
        except Exception:
            pass

    def pick_cover(self):
        p = filedialog.askopenfilename(parent=self, filetypes=[("Images", "*.jpg *.jpeg *.png")])
        if p:
            self.new_cover = p
            self._show_cover(path=p)

    def save(self):
        for k, v in self.vars.items():
            self.track[k] = v.get().strip()
        try:
            write_basic_tags(self.track)
            if self.new_cover:
                set_cover(self.track["path"], self.new_cover)
        except Exception as e:
            messagebox.showerror("Couldn't write tags", str(e), parent=self)
        self.on_save()
        self.destroy()


# ----------------------------------------------------------------------------
# Main app
# ----------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1180x640")
        self.tracks = []
        self.known_tags = set()

        style = ttk.Style(self)
        style.map("Treeview", background=[("selected", THEME_COLOR)], foreground=[("selected", "white")])
        # full-window gradient sitting behind everything, so no grey/white shows through
        self.bg = GradientBar(self, height=10)
        self.bg.place(x=0, y=0, relwidth=1, relheight=1)
        tk.Misc.lower(self.bg)
        header = GradientBar(self, height=52, text=APP_NAME, font=("Segoe UI", 18, "bold"))
        header.pack(fill="x")
        try:
            src = LOGO_FILE if LOGO_FILE.exists() else io.BytesIO(base64.b64decode(LOGO_B64))
            logo = Image.open(src).convert("RGBA")
            self.iconphoto(True, ImageTk.PhotoImage(logo.resize((64, 64), Image.LANCZOS)))  # window/taskbar icon
            self.logo_small = ImageTk.PhotoImage(logo.resize((40, 40), Image.LANCZOS))  # logo in the header
            header.create_image(12, 26, image=self.logo_small, anchor="w")
            header.coords(header.text_id, 62, 26)
        except Exception as e:
            print("Logo could not be loaded:", e)

        bar = GradientBar(self, height=42)
        bar.pack(fill="x")
        for text, cmd in [("Add Files", self.add_files), ("Add Folder", self.add_folder),
                          ("Remove", self.remove), ("▲ Up", lambda: self.move(-1)), ("▼ Down", lambda: self.move(1)),
                          ("Edit Metadata", self.edit), ("Analyze BPM/Key", self.analyze_selected)]:
            bar.add_widget(ttk.Button(bar, text=text, command=cmd), pad=4)

        bar2 = GradientBar(self, height=38)
        bar2.pack(fill="x")
        bar2.add_label("Colour:")
        self.color_choice = ttk.Combobox(bar2, values=list(PRESET_COLORS) + ["Custom..."], width=10, state="readonly")
        self.color_choice.set("Blue")
        bar2.add_widget(self.color_choice)
        bar2.add_widget(ttk.Button(bar2, text="Apply to selected", command=self.apply_color))
        bar2.add_widget(ttk.Button(bar2, text="Auto-colour by key", command=self.auto_color))
        bar2.add_gap()
        bar2.add_label("Sort by:")
        self.sort_choice = ttk.Combobox(bar2, values=["Title", "Artist", "BPM", "Key", "Colour"], width=8, state="readonly")
        self.sort_choice.set("Title")
        bar2.add_widget(self.sort_choice)
        bar2.add_widget(ttk.Button(bar2, text="Sort", command=self.sort))
        bar2.add_gap()
        bar2.add_widget(ttk.Button(bar2, text="Write order to file tags", command=self.write_numbers))
        bar2.add_gap()
        bar2.add_label("Convert to:")
        self.fmt_choice = ttk.Combobox(bar2, values=CONVERT_FORMATS, width=6, state="readonly")
        self.fmt_choice.set("mp3")
        bar2.add_widget(self.fmt_choice)
        bar2.add_widget(ttk.Button(bar2, text="Convert selected", command=self.convert))

        self.status = tk.StringVar(value="Add some music to get started.")
        GradientBar(self, height=26, textvariable=self.status, font=("Segoe UI", 9)).pack(side="bottom", fill="x")

        cols = ("num", "title", "artist", "album", "bpm", "key", "fmt")
        heads = ("#", "Title", "Artist", "Album", "BPM", "Key", "Format")
        widths = (50, 300, 180, 200, 70, 60, 70)
        self.tree = ttk.Treeview(self, columns=cols, show="headings", selectmode="extended")
        for c, h, w in zip(cols, heads, widths):
            self.tree.heading(c, text=h)
            self.tree.column(c, width=w, anchor="center" if c in ("num", "bpm", "key", "fmt") else "w")
        sb = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=10)
        sb.pack(side="right", fill="y", pady=10, padx=(0, 10))

        self.load_library()
        self.refresh()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    # --- persistence ---
    def load_library(self):
        if LIB_FILE.exists():
            try:
                data = json.loads(LIB_FILE.read_text(encoding="utf-8"))
                self.tracks = [t for t in data if os.path.exists(t["path"])]
            except Exception:
                pass

    def save_library(self):
        LIB_FILE.write_text(json.dumps(self.tracks, indent=1), encoding="utf-8")

    def on_close(self):
        self.save_library()
        self.destroy()

    # --- view ---
    def refresh(self, keep=None):
        self.tree.delete(*self.tree.get_children())
        for i, t in enumerate(self.tracks):
            tag = ()
            if t.get("color"):
                tag = ("c" + t["color"],)
                if tag[0] not in self.known_tags:
                    self.tree.tag_configure(tag[0], background=t["color"], foreground="black")
                    self.known_tags.add(tag[0])
            self.tree.insert("", "end", iid=str(i), tags=tag, values=(
                i + 1, t["title"], t["artist"], t["album"],
                f"{t['bpm']:.1f}" if t.get("bpm") else "", t.get("key", ""),
                Path(t["path"]).suffix.lstrip(".").upper()))
        if keep:
            self.tree.selection_set([str(i) for i in keep if i < len(self.tracks)])
        self.save_library()

    def selected(self):
        return sorted(int(i) for i in self.tree.selection())

    # --- library actions ---
    def add_paths(self, paths):
        have = {t["path"] for t in self.tracks}
        new = [p for p in paths if p not in have and Path(p).suffix.lower() in AUDIO_EXTS]
        for p in new:
            self.tracks.append(read_tags(p))
        self.refresh()
        self.status.set(f"Added {len(new)} file(s). {len(self.tracks)} in library.")

    def add_files(self):
        exts = " ".join(f"*{e}" for e in sorted(AUDIO_EXTS))
        self.add_paths(filedialog.askopenfilenames(filetypes=[("Audio/Video", exts)]))

    def add_folder(self):
        d = filedialog.askdirectory()
        if d:
            self.add_paths([str(p) for p in sorted(Path(d).rglob("*"))])

    def remove(self):
        sel = set(self.selected())
        self.tracks = [t for i, t in enumerate(self.tracks) if i not in sel]
        self.refresh()

    def move(self, d):
        sel = self.selected()
        if not sel:
            return
        order = sel if d < 0 else sel[::-1]
        for i in order:
            j = i + d
            if 0 <= j < len(self.tracks) and j not in sel:
                self.tracks[i], self.tracks[j] = self.tracks[j], self.tracks[i]
                sel[sel.index(i)] = j
        self.refresh(keep=sel)

    def sort(self):
        k = self.sort_choice.get()
        keyfn = {
            "Title": lambda t: t["title"].lower(),
            "Artist": lambda t: (t["artist"].lower(), t["title"].lower()),
            "BPM": lambda t: (t.get("bpm") is None, t.get("bpm") or 0),
            "Key": lambda t: (not t.get("key"), t.get("key", "")),
            "Colour": lambda t: t.get("color", ""),
        }[k]
        self.tracks.sort(key=keyfn)
        self.refresh()

    def edit(self):
        sel = self.selected()
        if sel:
            EditDialog(self, self.tracks[sel[0]], self.refresh)

    # --- colours ---
    def apply_color(self):
        name = self.color_choice.get()
        if name == "Custom...":
            c = colorchooser.askcolor()[1]
            if not c:
                return
        else:
            c = PRESET_COLORS[name]
        for i in self.selected():
            self.tracks[i]["color"] = c
        self.refresh(keep=self.selected())

    def auto_color(self):
        targets = self.selected() or range(len(self.tracks))
        for i in targets:
            c = key_color(self.tracks[i].get("key", ""))
            if c:
                self.tracks[i]["color"] = c
        self.refresh(keep=self.selected())
        self.status.set("Coloured by key (analyze songs first to get keys).")

    # --- analysis ---
    def analyze_selected(self):
        idx = self.selected() or list(range(len(self.tracks)))
        if not idx:
            return
        threading.Thread(target=self._analyze_worker, args=(idx,), daemon=True).start()

    def _analyze_worker(self, idx):
        for n, i in enumerate(idx, 1):
            t = self.tracks[i]
            self.after(0, self.status.set, f"Analyzing {n}/{len(idx)}: {t['title']} ...")
            try:
                t["bpm"], t["key"] = analyze(t["path"])
                try:
                    write_extra_tags(t)
                except Exception:
                    pass
            except Exception as e:
                self.after(0, self.status.set, f"Failed on {t['title']}: {e}")
            self.after(0, self.refresh)
        self.after(0, self.status.set, f"Analysis done ({len(idx)} song(s)).")

    # --- tags / conversion ---
    def write_numbers(self):
        if not messagebox.askyesno("Write order", "Write the current list position as the track number in every file?"):
            return
        for i, t in enumerate(self.tracks, 1):
            try:
                write_extra_tags(t, track_no=i)
            except Exception:
                pass
        self.status.set("Track numbers written to file tags.")

    def convert(self):
        if not shutil.which("ffmpeg"):
            messagebox.showerror("FFmpeg missing", "Install FFmpeg and make sure it's on your PATH.")
            return
        idx = self.selected()
        if not idx:
            messagebox.showinfo("Convert", "Select one or more songs first.")
            return
        out = filedialog.askdirectory(title="Choose output folder")
        if not out:
            return
        threading.Thread(target=self._convert_worker, args=(idx, out, self.fmt_choice.get()), daemon=True).start()

    def _convert_worker(self, idx, out, fmt):
        codec = {"mp3": ["-vn", "-c:a", "libmp3lame", "-q:a", "2"],
                 "m4a": ["-vn", "-c:a", "aac", "-b:a", "256k"],
                 "mp4": ["-c:a", "aac", "-b:a", "256k"],
                 "wav": ["-vn"], "flac": ["-vn"]}[fmt]
        for n, i in enumerate(idx, 1):
            t = self.tracks[i]
            dest = os.path.join(out, f"{i + 1:03d} - {Path(t['path']).stem}.{fmt}")
            self.after(0, self.status.set, f"Converting {n}/{len(idx)}: {t['title']} ...")
            cmd = ["ffmpeg", "-y", "-i", t["path"], "-map_metadata", "0", *codec, dest]
            r = subprocess.run(cmd, capture_output=True, text=True)
            if r.returncode != 0:
                self.after(0, self.status.set, f"Convert failed: {t['title']}")
        self.after(0, self.status.set, f"Conversion finished -> {out}")


if __name__ == "__main__":
    App().mainloop()
