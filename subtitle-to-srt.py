#!/usr/bin/env python3
# subtitle-to-srt.py: convert the VobSub or PGS subtitle track of an MKV
# to an SRT file.
# Copyright (C) 2026 sophom@users.noreply.github.com
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, version 3 of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

"""Convert a VobSub or PGS subtitle track of an MKV to an SRT file.

Supports the two bitmap subtitle formats found on HD DVD and Blu-ray
rips: dvd_subtitle (VobSub) and hdmv_pgs_subtitle (PGS). Pipeline:
mkvextract (tracks) -> fix the .idx size line (VobSub) -> ffmpeg renders
the subtitle stream to full-frame PNGs -> crop to text bbox -> tesseract
-> SRT.
"""

import csv
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import NamedTuple, NoReturn

from PIL import Image

USAGE = """\
Usage: subtitle-to-srt.py <file.mkv> [stream-index | -1] [-l lang] [-o out.srt] [--tesseract-language lang] [-f] [--workdir DIR] [--debug]
       subtitle-to-srt.py <dir> [stream-index | -1] [-l lang] [--type criteria] [-y] [-o OUTDIR] [--tesseract-language lang] [-f] [--workdir DIR] [--debug]
       subtitle-to-srt.py <file.mkv> --learn LANG1,LANG2 [-o out.srt] [-f] [--workdir DIR] [--debug]
       subtitle-to-srt.py --learn LANG1,LANG2 <file1.srt> <file2.srt> [-o out.srt] [-f]

Converts a VobSub or PGS subtitle track of an MKV to an SRT file.

Pass a directory instead of a file to recursively find .mkv files, list them
with the codec of their primary (first) video stream, and process every file
after a yes/no prompt (-y skips the prompt). In directory mode: -o selects
the directory that receives each SRT file; a stream index is applied to every
file (a file without that subtitle track is reported and skipped); --type
limits the file list by comma-separated criteria, all of which must match
(AND): a primary video codec prefix (e.g. vc1, mpeg2, h264), a subtitle
codec (dvd_subtitle or dvd, hdmv_pgs_subtitle or pgs), and/or a video
resolution (480, 576p, 1080, 2160p).

Pick the track with a stream index and/or -l lang (a stream index wins if both):

  stream-index  global stream index as shown by -L/--list (#4, #5, ...).
                If neither this nor -l is given, uses the track marked default,
                else the first English (eng/en) subtitle track, else the first
                subtitle track.
  -l lang       extract the first subtitle stream whose language matches LANG
                (2- or 3-letter ISO code, e.g. es or spa).
  -1            extract the first subtitle stream for each language to a
                separate SRT file. Tagged English is preferred; if no tagged
                English exists, the first untagged stream is assumed English.
                Cannot be combined with stream-index, -l, or
                --tesseract-language; -o (output directory) is only allowed
                in directory mode.
  --tesseract-language lang
                 force the language tesseract OCRs with (default: the selected
                 track's language tag).
  --learn L1,L2  produce a bilingual learning SRT. L1 is the top text, L2 is
                 the bottom text and provides timing for matched entries.
                 Either give one MKV (one track per language is extracted) or
                 two existing SRT files in L1,L2 order.
                 Default output: <name>.L1-L2.srt.
  -o out.srt    output path (default: <mkv file name>.<lang>.srt, where <lang>
                 is the 2-letter ISO code of the extracted track); in
                 directory mode: the directory that receives each SRT file
  -f            overwrite existing .srt output files (default: skip them)
  -j N          tesseract parallelism (default: physical cores - 1, min 1)
  -y            directory mode only: skip the yes/no prompt and process all
                 the listed files
  --type criteria
              directory mode only: only process files matching ALL
              comma-separated criteria (AND, case-insensitive): a primary
              video codec prefix (e.g. vc1, mpeg2, h264), a subtitle codec
              (dvd_subtitle/dvd or hdmv_pgs_subtitle/pgs: the file needs
              at least one such subtitle stream), and/or a video
              resolution (e.g. 480, 576p, 1080, 2160p; the "p" is
              optional and ignored, so 480 matches both 480i and 480p)
  -L, --list    list subtitle tracks (index, language, codec, duration) and exit
  --workdir DIR   base directory for temporary workdirs; must already exist
                  (default: system temp dir, usually /tmp)
  --debug         keep the temporary workdir(s) after the script exits

Pipeline: mkvextract (tracks) -> fix .idx size line -> ffmpeg renders the
subtitle stream to full-frame PNGs -> crop to text bbox -> tesseract -> SRT.
Timing: start = the DirectVobSub .idx timestamp; end = start + the track's
per-entry display duration (read from the VobSub packets via ffprobe), so
each entry ends when its subtitle disappears instead of when the next starts.
tesseract runs at nice 19 so the OCR phase yields CPU to other processes.
"""

# Quirks included (afk=af, both ton/tsn=tn): changing it changes CLI
# behavior (validation and the default output file name).
ISO639_1 = {
    "aar": "aa", "abk": "ab", "afk": "af", "aka": "ak", "amh": "am",
    "ara": "ar", "arg": "an", "asm": "as", "ava": "av", "aym": "ay",
    "aze": "az", "bel": "be", "ben": "bn", "bod": "bo", "bos": "bs",
    "bul": "bg", "cat": "ca", "ces": "cs", "chi": "zh", "cor": "kw",
    "cre": "cr", "cym": "cy", "dan": "da", "deu": "de", "ell": "el",
    "eng": "en", "epo": "eo", "est": "et", "eus": "eu", "fao": "fo",
    "fas": "fa", "fil": "tl", "fin": "fi", "fra": "fr", "fry": "fy",
    "glg": "gl", "grn": "gn", "guj": "gu", "hau": "ha", "heb": "he",
    "hin": "hi", "hrv": "hr", "hun": "hu", "hye": "hy", "ido": "io",
    "ind": "id", "isl": "is", "ita": "it", "jav": "jv", "jpn": "ja",
    "kan": "kn", "kat": "ka", "kaz": "kk", "khm": "km", "kir": "ky",
    "kor": "ko", "lao": "lo", "lat": "la", "lav": "lv", "lim": "li",
    "lin": "ln", "lit": "lt", "ltz": "lb", "mac": "mk", "mal": "ml",
    "mar": "mr", "mri": "mi", "mlt": "mt", "mya": "my", "nep": "ne",
    "nld": "nl", "nor": "no", "oci": "oc", "ori": "or", "orm": "om",
    "pan": "pa", "pol": "pl", "por": "pt", "que": "qu", "ron": "ro",
    "rum": "ro", "rus": "ru", "san": "sa", "sin": "si", "slo": "sk",
    "slv": "sl", "som": "so", "spo": "es", "spa": "es", "sqi": "sq",
    "srp": "sr", "swa": "sw", "swe": "sv", "tam": "ta", "tat": "tt",
    "tel": "te", "tgk": "tg", "tha": "th", "tir": "ti", "ton": "tn",
    "tsn": "tn", "tur": "tr", "twi": "tw", "ukr": "uk", "urd": "ur",
    "uzb": "uz", "ven": "ve", "vie": "vi", "xho": "xh", "yid": "yi",
    "yor": "yo", "zha": "za", "zho": "zh", "zul": "zu",
}


LANGUAGE_ALIASES = {
    "fre": "fra",
}


def normalize_lang(code: str) -> str:
    """Map legacy language aliases to their canonical ISO 639-2/T codes.

    Args:
        code: Language code to normalize, e.g. "fre".

    Returns:
        The normalized code, e.g. "fra"; unchanged if no alias is known.
    """
    return LANGUAGE_ALIASES.get(code, code)


def tag_to_2(tag: str) -> str:
    """Convert a language tag to its 2-letter ISO 639-1 code.

    Args:
        tag: ISO 639-1 or 639-2/T language tag, e.g. "eng".

    Returns:
        The 2-letter code, e.g. "en"; the tag itself if it is unknown.
    """
    return ISO639_1.get(normalize_lang(tag), tag)


TESSERACT_LANG_ALIASES = {
    "fre": "fra",
    "fr": "fra",
}


def tesseract_lang(code: str) -> str:
    """Map a language code to its tesseract traineddata name.

    Args:
        code: Language code, e.g. "fr".

    Returns:
        The tesseract language, e.g. "fra"; unchanged if no alias is known.
    """
    return TESSERACT_LANG_ALIASES.get(code, code)


def die(msg: str) -> NoReturn:
    """Print an error to stderr and exit with status 1.

    Args:
        msg: Error message to print.
    """
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


class TrackError(Exception):
    """Raised for a track failure in batch (-1) mode so the run continues."""


def fail(msg: str, batch: bool) -> NoReturn:
    """Report a track failure.

    Args:
        msg: Error message.
        batch: If True, raise TrackError instead of exiting (batch mode).
    """
    if batch:
        raise TrackError(msg)
    die(msg)


class Args(NamedTuple):
    """Parsed command-line options, mirroring the bash script's variables."""

    file: str
    stream: str
    out: str
    sel_lang: str
    ocr_lang: str
    par: str
    listing: bool
    first_each: bool
    force: bool
    learn: str
    workdir: str
    debug: bool
    assume_yes: bool
    vtype: str


def physical_core_count() -> int:
    """Count the physical CPU cores, ignoring hyperthreading.

    Each online CPU's thread_siblings_list topology file under
    /sys/devices/system/cpu names the logical CPUs that share one physical
    core, so the number of unique lists is the physical core count. Falls
    back to the logical CPU count when the topology is unreadable.

    Returns:
        The physical core count, at least 1.
    """
    seen: set[str] = set()
    for entry in sorted(Path("/sys/devices/system/cpu").glob("cpu[0-9]*")):
        try:
            with (entry / "topology" / "thread_siblings_list").open() as f:
                seen.add(f.read().strip())
        except OSError:
            return max(os.cpu_count() or 1, 1)
    if not seen:
        return max(os.cpu_count() or 1, 1)
    return len(seen)


def parse_args(argv: list[str]) -> Args:
    """Parse command-line arguments, mirroring the bash option loop.

    Also handles the Python-only --workdir and --debug options.

    Args:
        argv: Arguments after the program name.

    Returns:
        An Args with every option filled in.
    """
    file = stream = out = sel_lang = ocr_lang = ""
    par = str(max(physical_core_count() - 1, 1))
    listing = False
    first_each = False
    force = False
    learn = ""
    workdir = ""
    debug = False
    assume_yes = False
    vtype = ""
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "-o":
            if i + 1 >= len(argv):
                die("-o needs an argument")
            out = argv[i + 1]
            i += 2
        elif a == "-l":
            if i + 1 >= len(argv):
                die("-l needs an argument")
            sel_lang = argv[i + 1]
            i += 2
        elif a == "-j":
            if i + 1 >= len(argv):
                die("-j needs an argument")
            par = argv[i + 1]
            i += 2
        elif a in ("-L", "--list"):
            listing = True
            i += 1
        elif a == "--tesseract-language":
            if i + 1 >= len(argv):
                die("--tesseract-language needs an argument")
            ocr_lang = argv[i + 1]
            i += 2
        elif a == "--learn":
            if i + 1 >= len(argv):
                die("--learn needs an argument")
            learn = argv[i + 1]
            i += 2
        elif a == "-1":
            first_each = True
            i += 1
        elif a == "-f":
            force = True
            i += 1
        elif a == "--workdir":
            if i + 1 >= len(argv):
                die("--workdir needs an argument")
            workdir = argv[i + 1]
            i += 2
        elif a == "--debug":
            debug = True
            i += 1
        elif a == "-y":
            assume_yes = True
            i += 1
        elif a == "--type":
            if i + 1 >= len(argv):
                die("--type needs an argument")
            vtype = argv[i + 1]
            if not vtype:
                die("--type needs a non-empty argument")
            i += 2
        elif a in ("-h", "--help"):
            sys.stdout.write(USAGE)
            sys.exit(0)
        elif a.startswith("-"):
            die(f"unknown option: {a} (see --help)")
        else:
            if not file:
                file = a
            elif not stream:
                stream = a
            else:
                die(f"unexpected argument: {a}")
            i += 1
    if not file:
        sys.stderr.write(USAGE)
        sys.exit(1)
    if workdir and not os.path.isdir(workdir):
        die(f"--workdir is not a directory: {workdir}")
    return Args(file, stream, out, sel_lang, ocr_lang, par, listing,
                first_each, force, learn, workdir, debug, assume_yes, vtype)


def lang_to_2(code: str) -> str:
    """Validate a 2- or 3-letter language code; return its 2-letter form.

    Args:
        code: 2- or 3-letter ISO language code.

    Returns:
        The 2-letter ISO 639-1 code.

    Raises:
        SystemExit: If the code is unknown or not 2 or 3 letters.
    """
    code = normalize_lang(code)
    if len(code) == 3:
        if code not in ISO639_1:
            die(f"unknown 3-letter language code: {code}")
        return ISO639_1[code]
    if len(code) == 2:
        if code in ISO639_1.values():
            return code
        die(f"unknown 2-letter language code: {code}")
    die(f"language code must be 2 or 3 letters, got: {code}")


def _fmt_hms(seconds: str | float) -> str:
    """Format seconds as HH:MM:SS, like the awk in the shell script."""
    # awk: s+=0; h=int(s/3600); m=int((s%3600)/60); sec=int(s%60)
    s = float(seconds)
    h = int(s // 3600)
    m = int((s % 3600) // 60)
    sec = int(s % 60)
    return f"{h:02d}:{m:02d}:{sec:02d}"


def list_tracks(path: str) -> None:
    """Print a table of subtitle streams: index, language, codec, duration.

    One row per subtitle stream, using the per-track DURATION tag when
    present and the stream duration otherwise.

    Args:
        path: Path to the MKV file.
    """
    # One row per subtitle stream: index,codec_name,duration,language,DURATION
    out = run_captured([
        "ffprobe", "-v", "error", "-select_streams", "s",
        "-show_entries",
        "stream=index,codec_name,duration:stream_tags=language,DURATION",
        "-of", "csv=p=0", path,
    ])
    rows = []
    for row in csv.reader(io.StringIO(out)):
        if not row or not row[0].strip():
            continue
        while len(row) < 5:
            row.append("")
        idx, codec, dur_stream, lang, dur_tag = row[:5]
        lang = lang if lang != "" else "und"
        if dur_tag != "":
            # Strip decimals, like awk sub(/\..*$/, "")
            dur = dur_tag.split(".", 1)[0]
        else:
            try:
                dur = _fmt_hms(float(dur_stream))
            except ValueError:
                dur = _fmt_hms(0.0)  # awk s+=0 turns non-numerics into 0
        rows.append(f"#{idx:<4} {lang:<8} {codec:<13} {dur}")
    if not rows:
        print("(no subtitle streams)", file=sys.stderr)
        sys.exit(1)
    print("stream  language  codec          duration")
    print("\n".join(rows))


def run_captured(cmd: list[str], batch: bool = False) -> str:
    """Run a command and return its stdout; stderr goes to the terminal.

    A non-zero exit ends the script with the same code, like bash `set -e`.
    In batch mode it raises TrackError instead of exiting.

    Args:
        cmd: Command and arguments to run.
        batch: Raise TrackError on failure instead of exiting.

    Returns:
        The command's stdout.
    """
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, text=True)
    except FileNotFoundError:
        print(f"{cmd[0]}: command not found", file=sys.stderr)
        sys.exit(127)
    if p.returncode != 0:
        if batch:
            raise TrackError(f"{cmd[0]} failed with exit code {p.returncode}")
        sys.exit(p.returncode)
    return p.stdout


def run_quiet_ok(cmd: list[str]) -> str:
    """Like run_captured, but a failure or missing binary yields "".

    Args:
        cmd: Command and arguments to run.

    Returns:
        The command's stdout, or "" if it failed or was not found.
    """
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL, text=True)
    except FileNotFoundError:
        return ""
    return p.stdout if p.returncode == 0 else ""


def make_workdir(workdir: str = "") -> str:
    """Create a fresh temporary working directory.

    Args:
        workdir: Base directory to create it in; system temp dir if empty.

    Returns:
        The path of the new directory.
    """
    if workdir:
        return tempfile.mkdtemp(dir=workdir)
    return tempfile.mkdtemp()


def main() -> None:
    """Entry point: parse the arguments and dispatch to the right pipeline."""
    (file, stream, out, sel_lang, ocr_lang, par, listing, first_each,
     force, learn, workdir, debug, assume_yes, vtype) = parse_args(
        sys.argv[1:])

    if learn:
        if listing:
            die("--learn cannot be combined with -L/--list")
        if first_each:
            die("--learn cannot be combined with -1")
        if sel_lang:
            die(f"--learn cannot be combined with -l: {sel_lang}")
        if ocr_lang:
            die("--learn cannot be combined with --tesseract-language")
        if not (par.isdigit() and int(par) >= 1):
            die(f"-j must be a positive number, got: {par}")
        par = int(par)
        lang1, lang2 = parse_learn_langs(learn)

        if file.lower().endswith(".srt"):
            if not stream or not stream.lower().endswith(".srt"):
                die("--learn with SRT input needs two .srt files: "
                    "<top.srt> <base.srt>")
            if not os.path.isfile(file):
                die(f"file not found: {file}")
            if not os.path.isfile(stream):
                die(f"file not found: {stream}")
            if not out:
                out = learn_default_out_srt(file, lang1, lang2)
            if not force and os.path.isfile(out):
                print(f"skipping {out}: file already exists "
                      f"(use -f to overwrite)")
                sys.exit(0)
            top_entries = parse_srt_file(file)
            base_entries = parse_srt_file(stream)
            merged = merge_learn(top_entries, base_entries, lang1, lang2)
            write_learn_srt(out, merged)
            sys.exit(0)

        if file.lower().endswith(".mkv"):
            if stream:
                die("--learn with MKV input cannot be combined "
                    "with a stream index")
            if not os.path.isfile(file):
                die(f"file not found: {file}")
            if not out:
                out = learn_default_out_mkv(file, lang1, lang2)
            if not force and os.path.isfile(out):
                print(f"skipping {out}: file already exists "
                      f"(use -f to overwrite)")
                sys.exit(0)
            t0 = time.time()
            probe = json.loads(run_captured(
                ["ffprobe", "-v", "error", "-show_streams",
                 "-show_entries", "format=duration", "-of", "json", file]))
            streams = probe.get("streams", [])
            top_idx = select_learn_track(file, streams, lang1)
            base_idx = select_learn_track(file, streams, lang2)
            w, h = video_size(file)
            work = make_workdir(workdir)
            try:
                top_srt = f"{work}/top.{lang1}.srt"
                base_srt = f"{work}/base.{lang2}.srt"
                process_track(file, str(top_idx), top_idx, streams, "",
                              top_srt, par, w, h, batch=False,
                              workdir=workdir, debug=debug)
                process_track(file, str(base_idx), base_idx, streams, "",
                              base_srt, par, w, h, batch=False,
                              workdir=workdir, debug=debug)
                top_entries = parse_srt_file(top_srt)
                base_entries = parse_srt_file(base_srt)
                merged = merge_learn(top_entries, base_entries, lang1, lang2)
                entries = write_learn_srt(out, merged)
            finally:
                if not debug:
                    shutil.rmtree(work, ignore_errors=True)
            print(file_done_line(file, t0, entries,
                                 video_duration_hms(probe), 2, learn=True))
            sys.exit(0)

        die("with --learn the first positional argument must be a .mkv file, "
            "or give two .srt files")

    if os.path.isdir(file):
        process_directory(file, stream, out, sel_lang, ocr_lang, par,
                          listing, first_each, force, workdir, debug,
                          assume_yes, vtype)

    if not os.path.isfile(file):
        die(f"file not found: {file}")

    if listing:
        list_tracks(file)
        sys.exit(0)

    if not (par.isdigit() and int(par) >= 1):
        die(f"-j must be a positive number, got: {par}")
    par = int(par)

    if first_each:
        if stream:
            die(f"-1 cannot be combined with a stream index: {stream}")
        if sel_lang:
            die(f"-1 cannot be combined with -l: {sel_lang}")
        if out:
            die(f"-1 cannot be combined with -o: {out}")
        if ocr_lang:
            die(f"-1 cannot be combined with --tesseract-language: {ocr_lang}")

    t0 = time.time()
    probe = json.loads(run_captured(
        ["ffprobe", "-v", "error", "-show_streams", "-show_entries",
         "format=duration", "-of", "json", file]))
    streams = probe.get("streams", [])

    if out and not force and os.path.isfile(out):
        print(f"skipping {out}: file already exists (use -f to overwrite)")
        sys.exit(0)

    if first_each:
        _failed, entries, n_done = process_first_each(
            file, streams, par, force, "", workdir, debug, batch=False)
        print(file_done_line(file, t0, entries,
                             video_duration_hms(probe), n_done))
        sys.exit(0)

    stream, stream_i = select_stream(streams, sel_lang, stream, file,
                                     batch=False)

    if not out:
        out = output_for_track(file, streams, stream_i, ocr_lang, batch=False)
        if not force and os.path.isfile(out):
            print(f"skipping {out}: file already exists (use -f to overwrite)")
            sys.exit(0)

    w, h = video_size(file)
    entries = process_track(file, stream, stream_i, streams, ocr_lang, out,
                            par, w, h, batch=False, workdir=workdir,
                            debug=debug)
    print(file_done_line(file, t0, entries, video_duration_hms(probe), 1))


def idx_starts(work: str) -> list[int] | None:
    """Read the event start times (ms) from sub.idx's timestamp lines.

    Args:
        work: Working directory containing sub.idx.

    Returns:
        One start time in ms per event, or None if the file is missing or
        holds no timestamp lines.
    """
    try:
        text = Path(f"{work}/sub.idx").read_text(errors="replace")
    except OSError:
        return None
    starts = []
    for line in text.splitlines():
        m = re.fullmatch(
            r"timestamp: (\d+):(\d+):(\d+):(\d+), "
            r"filepos: [0-9a-fA-F]+",
            line.strip())
        if m:
            h, mi, s, ms = (int(g) for g in m.groups())
            starts.append(h * 3600000 + mi * 60000 + s * 1000 + ms)
    return starts or None


def probe_durations(work: str, n: int) -> list[int] | None:
    """Read per-event display durations from the .idx via ffprobe.

    Frames are matched to events by pts; an event whose packet failed to
    decode has no frame and gets a 0 duration (the SRT writer then ends it
    at the next event's start).

    Args:
        work: Working directory containing sub.idx.
        n: Expected number of subtitle events.

    Returns:
        One end_display_time in ms per event, or None if the ffprobe
        output is missing or no frame has a usable pts.
    """
    out = run_quiet_ok(
        ["ffprobe", "-hide_banner", "-show_frames", "-of", "json",
         f"{work}/sub.idx"])
    try:
        data = json.loads(out)
    except ValueError:
        return None
    frames = data.get("frames")
    if not isinstance(frames, list) or not frames:
        return None
    by_pts: dict[int, int] = {}
    try:
        for f in frames:
            pts = int(round(float(f["pts_time"]) * 1000))
            by_pts[pts] = int(f.get("end_display_time", 0))
    except (KeyError, TypeError, ValueError):
        return None
    starts = idx_starts(work)
    if starts is None or len(starts) != n:
        return None
    return [by_pts.get(s, 0) for s in starts]


def _parse_durations(durations: list[int] | None,
                     n: int) -> list[int] | None:
    """Coerce durations to ints; None if missing or the wrong length."""
    if durations is None or len(durations) != n:
        return None
    try:
        return [int(x) for x in durations]
    except (TypeError, ValueError):
        return None


def probe_pgs_starts(work: str) -> tuple[list[int], int, int] | None:
    """Read per-event start times (ms) and the page size from a PGS .sup.

    Args:
        work: Working directory containing sub.sup.

    Returns:
        A (starts, width, height) tuple where starts holds one start time
        in ms per event (the frame pts), or None if the ffprobe output is
        missing, any frame lacks a pts_time, or the stream has no size.
    """
    out = run_quiet_ok(
        ["ffprobe", "-hide_banner", "-show_streams", "-show_frames",
         "-of", "json", f"{work}/sub.sup"])
    try:
        data = json.loads(out)
    except ValueError:
        return None
    frames = data.get("frames")
    if not isinstance(frames, list) or not frames:
        return None
    try:
        starts = [int(round(float(f["pts_time"]) * 1000)) for f in frames]
        stream = data["streams"][0]
        return starts, int(stream["width"]), int(stream["height"])
    except (KeyError, IndexError, TypeError, ValueError):
        return None


def probe_rendered_pts(work: str) -> list[int] | None:
    """Read the rendered frames' pts (ms) from render.nut, in file order.

    Args:
        work: Working directory containing render.nut.

    Returns:
        One pts in ms per rendered frame, or None if the ffprobe output is
        missing or a frame lacks a pts.
    """
    out = run_quiet_ok(
        ["ffprobe", "-hide_banner", "-show_frames", "-of", "json",
         f"{work}/render.nut"])
    try:
        data = json.loads(out)
    except ValueError:
        return None
    frames = data.get("frames")
    if not isinstance(frames, list) or not frames:
        return None
    try:
        return [int(round(float(f["pts_time"]) * 1000)) for f in frames]
    except (KeyError, TypeError, ValueError):
        return None


def crop_frames(work: str, n: int, durations: list[int] | None,
                width: int = 0, height: int = 0, batch: bool = False,
                pgs: bool = False) -> None:
    """Crop the rendered frames to their text bounding boxes for OCR.

    VobSub: normally pairs each on-bitmap with its (blank) off-bitmap by
    position. When the rendered frame count deviates from the prediction
    (an event whose SPU fails to decode renders fewer frames), re-renders
    through a lossless NUT and matches frames to events by pts instead:
    each event owns the frames between its start and the next event's
    start, and its text comes from the first of those with content. PGS:
    the demuxer emits a display and an identical end frame per event plus
    one initial blank frame; only each event's display frame is used.
    Skips empty events and composites each crop over a black background so
    white font outlines do not hurt OCR.

    Args:
        work: Working directory containing the frame_*.png renders.
        n: Number of subtitle events.
        durations: Per-event display durations in ms, or None.
        width: Video width in pixels; 0 if unknown.
        height: Video height in pixels; 0 if unknown.
        batch: Raise TrackError on failure instead of exiting.
        pgs: True for PGS tracks (two frames per event plus one initial
             blank frame; no off-bitmaps).
    """
    frames = sorted(
        (f for f in os.listdir(work) if re.fullmatch(r"frame_\d+\.png", f)),
        key=lambda f: int(re.search(r"\d+", f).group()))
    durs = _parse_durations(durations, n)

    width = int(width) if str(width).isdigit() else 0
    height = int(height) if str(height).isdigit() else 0
    low_res = width > 0 and height > 0 and width <= 720 and height <= 576
    crops = os.path.join(work, "crops")
    os.makedirs(crops, exist_ok=True)

    on_idx: list[int | None] = []
    if pgs:
        if len(frames) != 2 * n + 1:
            fail(f"got {len(frames)} frames, expected {2 * n + 1} "
                 f"(PGS frame/event mismatch)", batch)
        for k in range(n):
            on_num = int(re.search(r"\d+", frames[2 * k + 1]).group())
            if on_num != 2 * k + 2:
                fail(f"frame numbering not sequential at event {k + 1} "
                     f"({on_num})", batch)
            on_idx.append(2 * k + 1)
    elif len(frames) == (sum(2 if d > 0 else 1 for d in durs)
                         if durs is not None else 2 * n):
        ptr = 0
        for k in range(n):
            on_num = int(re.search(r"\d+", frames[ptr]).group())
            if on_num != ptr + 1:
                fail(f"frame numbering not sequential at event {k + 1} "
                     f"({on_num})", batch)
            on_idx.append(ptr)
            if durs is None or durs[k] > 0:
                if ptr + 1 >= len(frames):
                    fail(f"missing off-bitmap for event {k + 1}", batch)
                off_num = int(re.search(r"\d+", frames[ptr + 1]).group())
                if off_num != ptr + 2:
                    fail(f"frame numbering not sequential at event "
                         f"{k + 1} ({off_num})", batch)
                off = Image.open(
                    os.path.join(work, frames[ptr + 1])).convert("RGBA")
                if off.getchannel("A").getbbox() is not None:
                    fail(f"off-bitmap of event {k + 1} has content "
                         f"(pairing anomaly)", batch)
                ptr += 2
            else:
                ptr += 1
    else:
        expected = (sum(2 if d > 0 else 1 for d in durs)
                    if durs is not None else 2 * n)
        print(f"warning: rendered {len(frames)} frames, expected "
              f"{expected}; re-rendering with per-frame pts to match "
              f"frames to events")
        _vobsub_render_nut(work, width, height, batch)
        os.makedirs(crops, exist_ok=True)
        frames = sorted(
            (f for f in os.listdir(work)
             if re.fullmatch(r"frame_\d+\.png", f)),
            key=lambda f: int(re.search(r"\d+", f).group()))
        starts = idx_starts(work)
        if starts is None or len(starts) != n:
            fail("could not read event start times from sub.idx", batch)
        pts = probe_rendered_pts(work)
        if pts is None or len(pts) != len(frames):
            got = 0 if pts is None else len(pts)
            fail(f"render.nut has {got} pts entries but "
                 f"{len(frames)} frames", batch)
        fi = 0
        for k in range(n):
            lo = starts[k]
            hi = starts[k + 1] if k + 1 < n else None
            window = []
            while fi < len(frames) and (hi is None or pts[fi] < hi):
                if pts[fi] >= lo:
                    window.append(fi)
                fi += 1
            chosen = None
            for idx in window:
                img = Image.open(
                    os.path.join(work, frames[idx])).convert("RGBA")
                if img.getchannel("A").getbbox() is not None:
                    chosen = idx
                    break
            if chosen is None and not window:
                print(f"warning: event {k + 1} rendered no frames "
                      f"(its subtitle packet failed to decode)")
            on_idx.append(chosen)

    empty = 0
    for k in range(n):
        if on_idx[k] is None:
            empty += 1
            continue
        on = Image.open(os.path.join(work, frames[on_idx[k]])).convert("RGBA")
        bbox = on.getchannel("A").getbbox()
        if (bbox is None
                or (bbox[2] - bbox[0]) < 16
                or (bbox[3] - bbox[1]) < 16):
            empty += 1
            continue
        pad = 10 if low_res else 30
        x0, y0 = max(0, bbox[0] - pad), max(0, bbox[1] - pad)
        x1, y1 = min(on.width, bbox[2] + pad), min(on.height, bbox[3] + pad)
        # Make the background black so that the black outline of white
        # fonts disappears for better OCR. This makes a significant
        # difference for both high-res and low-res fonts
        crop_rgba = on.crop((x0, y0, x1, y1))
        bg = Image.new("RGBA", crop_rgba.size, (0, 0, 0, 255))
        crop = Image.alpha_composite(bg, crop_rgba).convert("L")
        crop = crop.point(lambda p: 0 if p < 128 else 255)
        crop.save(os.path.join(crops, f"{k + 1:04d}.png"))
    print(f"events: {n}  with text: {n - empty}  empty: {empty}")


def _fmt_dur(s: int) -> str:
    """Format a duration in seconds as M:SS or H:MM:SS."""
    if s >= 3600:
        return f"{s // 3600}:{s % 3600 // 60:02d}:{s % 60:02d}"
    return f"{s // 60}:{s % 60:02d}"


def run_tesseract(crops_dir: str, n_crops: int, ocr_lang: str, par: int,
                  batch: bool = False) -> None:
    """OCR the cropped PNGs with tesseract, chunked over parallel jobs.

    Runs tesseract at nice 19 (psm 6) on per-chunk file lists, prints
    progress with an ETA, and writes one .txt per crop beside its PNG.

    Args:
        crops_dir: Directory of crop PNGs to OCR.
        n_crops: Number of crop PNGs.
        ocr_lang: tesseract language to OCR with.
        par: Number of parallel tesseract processes.
        batch: Raise TrackError on failure instead of exiting.
    """
    print(f"running tesseract ({ocr_lang}, psm 6) on {n_crops} crops ...")
    pngs = sorted(p for p in os.listdir(crops_dir) if p.endswith(".png"))
    start_s = time.time()
    ocr_dir = os.path.join(os.path.dirname(crops_dir), "ocr")
    os.makedirs(ocr_dir, exist_ok=True)
    chunks = min(par, n_crops)
    chunk_size = (n_crops + chunks - 1) // chunks
    specs = []
    for c in range(chunks):
        names = pngs[c * chunk_size:(c + 1) * chunk_size]
        if not names:
            continue
        list_path = os.path.join(ocr_dir, f"list_{c:03d}.txt")
        outbase = os.path.join(ocr_dir, f"chunk_{c:03d}")
        tsv_path = outbase + ".tsv"
        with open(list_path, "w") as f:
            for name in names:
                f.write(os.path.join(crops_dir, name) + "\n")
        specs.append((list_path, outbase, tsv_path, names))

    procs = []
    for list_path, outbase, tsv_path, names in specs:
        try:
            p = subprocess.Popen(
                ["nice", "-n", "19", "tesseract", list_path, outbase,
                 "--psm", "6", "-l", ocr_lang, "tsv"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except OSError:
            p = None
        procs.append(p)

    def count_pages():
        done = 0
        for _, _, tsv_path, _ in specs:
            if not os.path.exists(tsv_path):
                continue
            with open(tsv_path, "r", encoding="utf-8", errors="replace") as f:
                for line in f:
                    if line.endswith("\n") and line.startswith("1\t"):
                        done += 1
        return min(done, n_crops)

    done_n = 0
    while True:
        for p in procs:
            if p is not None:
                p.poll()
        done_n = count_pages()
        if all(p is None or p.returncode is not None for p in procs):
            break
        el = int(time.time() - start_s)
        pct = 100 * done_n // n_crops
        if done_n == 0 or el < 4:
            line = "\rOCR: %d/%d (%d%%)  ETA --:--" % (done_n, n_crops, pct)
        else:
            eta = (n_crops - done_n) * el // done_n
            line = "\rOCR: %d/%d (%d%%)  ETA %s" % (
                done_n, n_crops, pct, _fmt_dur(eta))
        sys.stdout.write(line)
        sys.stdout.flush()
        time.sleep(2)

    failed = (any(p is None or p.returncode != 0 for p in procs)
              or done_n < n_crops)
    if failed:
        fail("tesseract failed on one or more crops (exit code 123)", batch)

    for _, _, tsv_path, names in specs:
        if not os.path.exists(tsv_path):
            fail("tesseract failed on one or more crops "
                 "(exit code 123)", batch)
        by_page = {}
        with open(tsv_path, "r", encoding="utf-8", errors="replace") as f:
            first = True
            for line in f:
                if first:
                    first = False
                    continue
                if not line.endswith("\n"):
                    continue
                parts = line.rstrip("\n").split("\t")
                if len(parts) < 12 or parts[0] != "5":
                    continue
                page_num = parts[1]
                key = (page_num, parts[2], parts[3], parts[4])
                by_page.setdefault(page_num, {}).setdefault(key, []).append(
                    (parts[5], parts[11]))
        for page_num, lines in by_page.items():
            idx = int(page_num) - 1
            if idx < 0 or idx >= len(names):
                fail("tesseract failed on one or more crops "
                     "(exit code 123)", batch)
            text_lines = []
            for key in sorted(lines, key=lambda k: tuple(int(x) for x in k)):
                words = sorted(lines[key], key=lambda r: int(r[0]))
                text_lines.append(" ".join(text for _, text in words))
            target = os.path.join(crops_dir, names[idx][:-4] + ".txt")
            with open(target, "w", encoding="utf-8") as f:
                f.write("\n".join(text_lines))
        for name in names:
            target = os.path.join(crops_dir, name[:-4] + ".txt")
            if not os.path.exists(target):
                with open(target, "w", encoding="utf-8") as f:
                    f.write("")

    sys.stdout.write("\rOCR: %d/%d (100%%)  done in %s\n"
                     % (n_crops, n_crops,
                        _fmt_dur(int(time.time() - start_s))))
    sys.stdout.flush()


def write_srt(work: str, n: int, out: str, batch: bool = False,
              english: bool = False) -> int:
    """Assemble the SRT from start times, durations, and OCR text.

    Start = the DirectVobSub .idx timestamp (VobSub) or the PGS frame pts
    (from starts.json); end = start + the event's display duration
    (VobSub), falling back to the next start (or +5s for the last event).
    Blank PGS events (no OCR text) are omitted from the output.

    Args:
        work: Working directory with sub.idx or starts.json,
            durations.json, and crops/.
        n: Number of subtitle events.
        out: Output SRT path.
        batch: Raise TrackError on failure instead of exiting.
        english: When True (English output), normalize tesseract's "lam"
            misread of "I am" back to "I am" (word-boundary).

    Returns:
        Number of entries written to the SRT.
    """
    starts_path = f"{work}/starts.json"
    pgs = os.path.exists(starts_path)
    if pgs:
        ts = None
        try:
            cand = json.loads(Path(starts_path).read_text())
            if (isinstance(cand, list)
                    and all(type(x) in (int, float) for x in cand)):
                ts = [int(x) for x in cand]
        except (OSError, ValueError):
            ts = None
        if ts is None or len(ts) != n:
            fail(f"no valid start times in starts.json, expected {n}",
                 batch)
    else:
        offset_ms = 0
        ts = []
        for line in (Path(f"{work}/sub.idx").read_text(
                errors="replace").splitlines()):
            line = line.strip()
            m = re.fullmatch(r"time offset: (-?\d+)", line)
            if m:
                offset_ms = int(m.group(1))
                continue
            m = re.fullmatch(
                r"timestamp: (\d+):(\d+):(\d+):(\d+), "
                r"filepos: [0-9a-fA-F]+",
                line)
            if m:
                h, mi, s, ms = (int(g) for g in m.groups())
                ts.append((h * 3600000 + mi * 60000 + s * 1000 + ms)
                          + offset_ms)
        if len(ts) != n:
            fail(f"{len(ts)} timestamp lines in sub.idx, expected {n}",
                 batch)

    dur = None
    try:
        cand = json.loads(Path(f"{work}/durations.json").read_text())
        if (isinstance(cand, list) and len(cand) == n
                and all(type(x) in (int, float) for x in cand)):
            dur = [int(x) for x in cand]
    except Exception:
        dur = None

    def fmt(v: int) -> str:
        return (f"{v // 3600000:02d}:{v % 3600000 // 60000:02d}:"
                f"{v % 60000 // 1000:02d},{v % 1000:03d}")

    entries = []
    for i, start in enumerate(ts):
        tf = f"{work}/crops/{i + 1:04d}.txt"
        text = ""
        if os.path.exists(tf):
            text = Path(tf).read_text(
                errors="replace").strip().replace("|", "I")
            if english:
                text = re.sub(r"\blam\b", "I am", text)
        if pgs and not text:
            continue
        if dur is not None and dur[i] > 0:
            end = start + dur[i]
        else:
            end = ts[i + 1] if i + 1 < n else start + 5000
        entries.append((len(entries) + 1, fmt(start), fmt(end), text))

    if not any(t for *_, t in entries):
        fail(f"no subtitle text: all {n} events blank", batch)

    with open(out, "w") as f:
        for num, s, e, text in entries:
            f.write(f"{num}\n{s} --> {e}\n{text}\n\n")
    if pgs:
        print(f"{len(entries)} entries written to {out} "
              f"({n - len(entries)} blank events skipped)")
    else:
        n_empty = sum(1 for *_, t in entries if not t)
        print(f"{len(entries)} entries written to {out} ({n_empty} empty)")
    return len(entries)


def video_size(file: str) -> tuple[str, str]:
    """Get the first video stream's dimensions.

    Args:
        file: Path to the MKV file.

    Returns:
        (width, height) as strings; ("1920", "1080") if undetectable.
    """
    vlines = run_quiet_ok([
        "ffprobe", "-v", "error", "-select_streams", "v:0",
        "-show_entries", "stream=width,height", "-of", "csv=p=0", file,
    ]).splitlines()
    parts = (vlines[0] if vlines else "").split(",")
    w = parts[0] if parts and parts[0] else ""
    h = parts[1] if len(parts) > 1 and parts[1] else ""
    if not w or not h:
        w, h = "1920", "1080"
    return w, h


def video_duration_hms(probe: dict) -> str:
    """Format-level duration from a probe dict, as HH:MM:SS.

    The per-stream duration of the video stream is often absent, so the
    container (format) duration is used; it equals the video's.

    Args:
        probe: Parsed ffprobe JSON with format=duration requested.

    Returns:
        The duration as HH:MM:SS, or "00:00:00" if not available.
    """
    d = (probe.get("format") or {}).get("duration", "")
    try:
        return _fmt_hms(float(d))
    except (TypeError, ValueError):
        return "00:00:00"


def file_done_line(path: str, t0: float, entries: int, video_dur: str,
                   n_streams: int, learn: bool = False) -> str:
    """Build the one-line per-file stats message printed when done.

    Args:
        path: MKV path.
        t0: time.time() when this file's processing started.
        entries: Number of subtitle entries written.
        video_dur: Video duration as HH:MM:SS.
        n_streams: Number of subtitle streams extracted from the MKV.
        learn: --learn mode; the streams are merged into one SRT file.

    Returns:
        The message, e.g. "File movie.mkv finished in 1:32. Wrote 150
        subtitles in 1 stream for a video with a duration of 00:58:34"
        and adds a newline.
    """
    streams = f"in {n_streams} stream{'s' if n_streams != 1 else ''}"
    if learn:
        streams += " in one .srt file"
    return (f"File {os.path.basename(path)} finished in "
            f"{_fmt_dur(int(time.time() - t0))}. Wrote {entries} subtitles "
            f"{streams} for a video with a duration of {video_dur}")


def stream_lang(streams: list[dict], index: int) -> str:
    """Get a stream's language tag, "und" if missing or untagged.

    Args:
        streams: ffprobe stream dicts.
        index: Stream index to look up.

    Returns:
        The language tag, or "und".
    """
    for s in streams:
        if s.get("index") == index:
            return (s.get("tags") or {}).get("language") or "und"
    return "und"


def first_per_language(streams: list[dict]) -> tuple[list[int], int | None]:
    """Pick the first subtitle stream per language, preferring English.

    Args:
        streams: ffprobe stream dicts.

    Returns:
        (selected indices, warning index): the warning marks the untagged
        stream assumed to be English when no tagged English exists.
    """
    subs = sorted((s for s in streams
                   if s.get("codec_type") == "subtitle"),
                  key=lambda s: s["index"])
    selected = set()
    seen = set()
    english = None
    untagged = None
    for s in subs:
        idx = s["index"]
        tag = (s.get("tags") or {}).get("language") or ""
        if tag in ("", "und", "unknown"):
            if untagged is None:
                untagged = idx
            continue
        norm = tag_to_2(tag)
        if norm == "en":
            if english is None:
                english = idx
            continue
        if norm not in seen:
            seen.add(norm)
            selected.add(idx)
    if english is not None:
        selected.add(english)
    warning = None
    if english is None and untagged is not None:
        selected.add(untagged)
        warning = untagged
    return sorted(selected), warning


def default_out(file: str, s_lang: str, ocr_lang: str) -> str:
    """Build the default output path <name>.<lang>.srt.

    Args:
        file: Source MKV path.
        s_lang: Stream language tag, or ""/"unknown" if untagged.
        ocr_lang: Language to fall back to when the stream is untagged.

    Returns:
        The default output SRT path.
    """
    fname_lang = s_lang
    if not fname_lang or fname_lang == "unknown":
        fname_lang = ocr_lang
    base = file[:-4] if file.endswith(".mkv") else file
    return f"{base}.{tag_to_2(fname_lang)}.srt"


def output_for_track(file: str, streams: list[dict], stream_i: int,
                     ocr_lang: str, batch: bool = False,
                     assume_english: bool = False) -> str:
    """Validate a subtitle stream and compute its default output path.

    Args:
        file: Source MKV path.
        streams: ffprobe stream dicts.
        stream_i: Stream index to validate.
        ocr_lang: Forced tesseract language; "" to use the track's tag.
        batch: Raise TrackError on failure instead of exiting.
        assume_english: Treat an untagged stream as English.

    Returns:
        The output SRT path.
    """
    chosen = next((s for s in streams if s.get("index") == stream_i), None)
    if chosen is None:
        fail(f"no stream with index {stream_i} in {file}", batch)
    s_type = chosen.get("codec_type") or ""
    s_codec = chosen.get("codec_name") or ""
    s_lang = (chosen.get("tags") or {}).get("language") or "unknown"
    if s_type != "subtitle":
        fail(f"stream {stream_i} is a {s_type} stream, not a subtitle", batch)
    if s_codec not in ("dvd_subtitle", "hdmv_pgs_subtitle"):
        fail(f"unsupported subtitle codec: {s_codec} "
             "(need dvd_subtitle/VobSub)", batch)
    if not ocr_lang:
        if assume_english and s_lang in ("", "unknown", "und"):
            ocr_lang = "eng"
        elif not s_lang or s_lang == "unknown":
            fail(f"stream {stream_i} has no language tag; "
                 f"pass --tesseract-language LANG", batch)
        else:
            ocr_lang = s_lang
    return default_out(file, s_lang, tesseract_lang(ocr_lang))


_SRT_TS_RE = re.compile(r"(\d{1,2}):(\d{1,2}):(\d{1,2})[,.](\d{1,3})")


def parse_srt_ts(value: str) -> int | None:
    """Parse an SRT timestamp (HH:MM:SS,mmm) into milliseconds.

    Args:
        value: Timestamp string, e.g. "01:02:03,045".

    Returns:
        Milliseconds since 00:00:00, or None if the value does not match.
    """
    m = _SRT_TS_RE.match(value.strip())
    if not m:
        return None
    h, mi, s = int(m.group(1)), int(m.group(2)), int(m.group(3))
    ms = int(m.group(4).ljust(3, "0")[:3])
    return ((h * 60 + mi) * 60 + s) * 1000 + ms


def fmt_srt_ms(value: int) -> str:
    """Format milliseconds as an SRT timestamp (HH:MM:SS,mmm)."""
    return (f"{value // 3600000:02d}:{value % 3600000 // 60000:02d}:"
            f"{value % 60000 // 1000:02d},{value % 1000:03d}")


def parse_srt_file(path: str) -> list[tuple[int, int, str]]:
    """Parse an SRT file into (start_ms, end_ms, text) entries.

    Tolerates missing index lines, CRLF, a BOM, and end < start (which is
    clamped to start).

    Args:
        path: Path to the SRT file.

    Returns:
        The entries, sorted by (start, end).
    """
    text = Path(path).read_text(errors="replace")
    text = text.replace("\r\n", "\n").replace("\r", "\n").lstrip("\ufeff")
    entries = []
    for block in re.split(r"\n\s*\n", text.strip()):
        lines = block.splitlines()
        while lines and not lines[0].strip():
            lines.pop(0)
        if not lines:
            continue
        ts_idx = 0
        if not re.search(r"-->", lines[0]):
            ts_idx = 1
        if ts_idx >= len(lines):
            continue
        m = re.match(r"(\S+)\s*-->\s*(\S+)", lines[ts_idx])
        if not m:
            continue
        start = parse_srt_ts(m.group(1))
        end = parse_srt_ts(m.group(2))
        if start is None or end is None:
            continue
        if end < start:
            end = start
        body = [line.rstrip() for line in lines[ts_idx + 1:]]
        while body and not body[0].strip():
            body.pop(0)
        while body and not body[-1].strip():
            body.pop()
        entries.append((start, end, "\n".join(body)))
    entries.sort(key=lambda e: (e[0], e[1]))
    return entries


def write_learn_srt(out: str, entries: list[tuple[int, int, str]]) -> int:
    """Write bilingual learning entries as an SRT file.

    Args:
        out: Output SRT path.
        entries: (start_ms, end_ms, combined text) tuples.

    Returns:
        Number of entries written to the SRT.
    """
    with open(out, "w") as f:
        for i, (start, end, text) in enumerate(entries, 1):
            text = text.replace("|", "I")
            f.write(f"{i}\n{fmt_srt_ms(start)} --> {fmt_srt_ms(end)}\n"
                    f"{text}\n\n")
    print(f"{len(entries)} entries written to {out}")
    return len(entries)


def learn_clean(text: str) -> str:
    """Strip leading and trailing blank lines from a subtitle text block."""
    lines = [line.rstrip() for line in text.splitlines()]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines)


def learn_combine(top_text: str, base_text: str) -> str:
    """Join top and base texts with a "---" separator line.

    Args:
        top_text: L1 (top) text; may be empty.
        base_text: L2 (bottom) text; may be empty.

    Returns:
        The combined text, e.g. "top\n---\nbase"; "" if both are empty.
    """
    top = learn_clean(top_text)
    base = learn_clean(base_text)
    if top and base:
        return f"{top}\n---\n{base}"
    if base:
        return f"---\n{base}"
    if top:
        return f"{top}\n---"
    return ""


LEARN_SLACK_MS = 600


def learn_overlap(entry_a: tuple[int, int, str],
                  entry_b: tuple[int, int, str]) -> int:
    """Score how much two entries overlap, in ms (0 = no match).

    Only overlaps of at least 200 ms and 20% of the shorter entry count.

    Args:
        entry_a: (start_ms, end_ms, text) entry.
        entry_b: (start_ms, end_ms, text) entry.

    Returns:
        The overlap in ms, or 0 if below the match threshold.
    """
    overlap = min(entry_a[1], entry_b[1]) - max(entry_a[0], entry_b[0])
    if overlap <= 0:
        return 0
    short = min(entry_a[1] - entry_a[0], entry_b[1] - entry_b[0])
    threshold = max(200, int(short * 0.20))
    if overlap < threshold:
        return 0
    return overlap


def merge_learn(top_entries: list[tuple[int, int, str]],
                base_entries: list[tuple[int, int, str]],
                top_lang: str, base_lang: str) -> list[tuple[int, int, str]]:
    """Merge top and base SRT entries into bilingual learning entries.

    Base entries provide the timing; matching top entries are merged in,
    and unmatched top entries that do not overlap a match are appended.

    Args:
        top_entries: (start, end, text) entries for L1 (top text).
        base_entries: (start, end, text) entries for L2 (timing source).
        top_lang: L1 language code, for the warning message.
        base_lang: L2 language code, for the warning message.

    Returns:
        The merged entries, sorted by (start, end).
    """
    top = [e for e in top_entries if learn_clean(e[2])]
    base = [e for e in base_entries if learn_clean(e[2])]
    used = [False] * len(top)
    matched_base = []
    out = []
    prev_top = -1
    for base_entry in base:
        best_k = None
        best_score = 0
        best_dist = None
        k = prev_top + 1
        while k < len(top) and top[k][0] <= base_entry[1] + LEARN_SLACK_MS:
            if not used[k] and top[k][1] >= base_entry[0] - LEARN_SLACK_MS:
                score = learn_overlap(top[k], base_entry)
                if score > best_score:
                    top_mid = (top[k][0] + top[k][1]) // 2
                    base_mid = (base_entry[0] + base_entry[1]) // 2
                    best_k = k
                    best_score = score
                    best_dist = abs(top_mid - base_mid)
            k += 1
        if best_k is not None:
            used[best_k] = True
            prev_top = best_k
            matched_base.append(base_entry)
            out.append((base_entry[0], base_entry[1],
                        learn_combine(top[best_k][2], base_entry[2])))
        else:
            out.append((base_entry[0], base_entry[1],
                        learn_combine("", base_entry[2])))
    suppressed = 0
    for i, top_entry in enumerate(top):
        if used[i]:
            continue
        if any(learn_overlap(top_entry, base_entry) > 0
               for base_entry in matched_base):
            suppressed += 1
        else:
            out.append((top_entry[0], top_entry[1],
                        learn_combine(top_entry[2], "")))
    if suppressed:
        print(f"warning: suppressed {suppressed} unmatched {top_lang} entries "
              f"that overlap matched {base_lang} entries", file=sys.stderr)
    out.sort(key=lambda e: (e[0], e[1]))
    return out


def parse_learn_langs(value: str) -> tuple[str, str]:
    """Parse the --learn value into two distinct 2-letter language codes.

    Args:
        value: Comma-separated codes, e.g. "es,en".

    Returns:
        The (lang1, lang2) 2-letter codes.

    Raises:
        SystemExit: If the value is malformed or both codes match.
    """
    parts = [p.strip() for p in value.split(",")]
    if len(parts) != 2 or not all(parts):
        die("--learn expects two comma-separated language codes, e.g. es,en")
    lang1 = lang_to_2(parts[0])
    lang2 = lang_to_2(parts[1])
    if lang1 == lang2:
        die("--learn languages must be different")
    return lang1, lang2


def learn_default_out_srt(top_path: str, lang1: str, lang2: str) -> str:
    """Default --learn output path for two SRT inputs.

    Replaces the top file's trailing ".<lang1>" with ".<lang1>-<lang2>".

    Args:
        top_path: Path of the L1 (top) input SRT.
        lang1: L1 2-letter code.
        lang2: L2 2-letter code.

    Returns:
        The output SRT path, next to the top input.
    """
    p = Path(top_path)
    stem = p.stem
    suffix = f".{lang1}"
    if stem.lower().endswith(suffix):
        stem = stem[:-len(suffix)]
    return str(p.with_name(f"{stem}.{lang1}-{lang2}.srt"))


def learn_default_out_mkv(file: str, lang1: str, lang2: str) -> str:
    """Default --learn output path for an MKV input.

    Args:
        file: Path of the source MKV.
        lang1: L1 2-letter code.
        lang2: L2 2-letter code.

    Returns:
        "<mkv name>.<lang1>-<lang2>.srt".
    """
    base = file[:-4] if file.endswith(".mkv") else file
    return f"{base}.{lang1}-{lang2}.srt"


def _parse_hms_duration(value: str) -> float:
    """Parse a DURATION tag like "01:51:34.5" into seconds; 0.0 on error."""
    try:
        hms, _, frac = value.partition(".")
        h, mi, s = (int(x) for x in hms.split(":"))
        frac_val = float(frac) if frac else 0.0
        return (h * 3600 + mi * 60 + s) + frac_val
    except Exception:
        return 0.0


def select_learn_track(file: str, streams: list[dict],
                       code: str) -> int:
    """Pick the best subtitle track for a language for --learn.

    Prefers default-flagged tracks, then the longest per-track DURATION
    (feature vs. extras), then the lowest index.

    Args:
        file: Source MKV path, for the error message.
        streams: ffprobe stream dicts.
        code: 2-letter language code to match.

    Returns:
        The chosen stream index.
    """
    cands = []
    for s in streams:
        if s.get("codec_type") != "subtitle":
            continue
        if s.get("codec_name") not in ("dvd_subtitle", "hdmv_pgs_subtitle"):
            continue
        tag = (s.get("tags") or {}).get("language") or ""
        if tag_to_2(tag) != code:
            continue
        tags = s.get("tags") or {}
        dur = _parse_hms_duration(tags.get("DURATION", ""))
        if not dur:
            try:
                dur = float(s.get("duration") or 0)
            except ValueError:
                dur = 0.0
        default = 1 if (s.get("disposition") or {}).get("default") == 1 else 0
        cands.append((-default, -dur, s["index"]))
    if not cands:
        die(f"no subtitle track with language {code} in {file} "
            f"(see -L/--list)")
    cands.sort()
    return cands[0][2]


# Common VobSub SPU canvases, tried (after the video size) when the video
# size yields mostly blank subtitles. The .idx size line names the subtitle
# canvas, which can differ from the video resolution (e.g. a subtitle
# authored at 1080p on a 480p video renders blank at the video size).
_VOBSUB_CANVAS_CANDIDATES: tuple[tuple[int, int], ...] = (
    (1920, 1080), (1280, 720), (1440, 1080), (3840, 2160),
    (720, 576), (1280, 960),
)


def _set_idx_size(idx_path: str, width: int, height: int) -> None:
    """Rewrite the DirectVobSub .idx ``size:`` line to ``width x height``.

    The ``index:`` line is left untouched: the demuxer only accepts packets
    whose stream id equals the index, and the extracted stream uses 0.

    Args:
        idx_path: Path to the .idx file.
        width: Canvas width in pixels.
        height: Canvas height in pixels.
    """
    lines = Path(idx_path).read_text(errors="replace").splitlines(
        keepends=True)
    for k, line in enumerate(lines):
        if line.startswith("size: "):
            lines[k] = f"size: {width}x{height}\n"
            break
    Path(idx_path).write_text("".join(lines))


def _clear_render(work: str) -> None:
    """Remove a previous render's frames, ``render.nut``, and ``crops/``.

    Args:
        work: Temporary work directory.
    """
    for name in os.listdir(work):
        if re.fullmatch(r"frame_\d+\.png", name) or name == "render.nut":
            os.remove(os.path.join(work, name))
    crops = os.path.join(work, "crops")
    if os.path.isdir(crops):
        shutil.rmtree(crops)


def _vobsub_render_nut(work: str, width: int, height: int,
                       batch: bool) -> None:
    """Re-render the events through a lossless NUT, keeping per-frame pts.

    The direct PNG render loses the frame timestamps the pts-based frame/
    event matching needs; the NUT keeps them (ffv1, lossless).

    Args:
        work: Temporary work directory holding sub.idx/sub.sub with the
            .idx canvas already set to width x height.
        width: Canvas width in pixels.
        height: Canvas height in pixels.
        batch: Raise TrackError on failure instead of exiting.
    """
    _clear_render(work)
    run_captured([
        "ffmpeg", "-hide_banner", "-v", "error",
        "-i", f"{work}/sub.idx",
        "-filter_complex", f"[0:s:0]scale={width}:{height}[v]",
        "-map", "[v]", "-c:v", "ffv1", "-vsync", "vfr",
        f"{work}/render.nut",
    ], batch=batch)
    run_captured([
        "ffmpeg", "-hide_banner", "-v", "error",
        "-i", f"{work}/render.nut",
        "-fps_mode", "passthrough", "-c:v", "png",
        f"{work}/frame_%04d.png",
    ], batch=batch)


def _count_crops(work: str) -> int:
    """Count cropped subtitle images in the work dir's ``crops/`` dir.

    Args:
        work: Temporary work directory.

    Returns:
        Number of ``.png`` crops, or 0 if the dir is absent.
    """
    crops = os.path.join(work, "crops")
    if not os.path.isdir(crops):
        return 0
    return len([p for p in os.listdir(crops) if p.endswith(".png")])


def _render_vobsub_at(work: str, n: int, durations: list[int] | None,
                      width: int, height: int, batch: bool) -> None:
    """Render VobSub events at a given canvas size, then crop them.

    Sets the .idx canvas, clears any prior render, renders every event to
    PNG at ``width x height``, and crops the non-blank events.

    Args:
        work: Temporary work directory holding sub.idx/sub.sub.
        n: Number of subtitle events.
        durations: Per-event on-screen durations in ms (length n).
        width: Canvas width in pixels.
        height: Canvas height in pixels.
        batch: Raise TrackError on failure instead of exiting.
    """
    _set_idx_size(f"{work}/sub.idx", width, height)
    _clear_render(work)
    print(f"rendering {n} subtitle events to {width}x{height} frames ...")
    run_captured([
        "ffmpeg", "-hide_banner", "-v", "error",
        "-i", f"{work}/sub.idx",
        "-filter_complex", f"[0:s:0]scale={width}:{height}[v]",
        "-map", "[v]", "-c:v", "png", "-vsync", "vfr",
        f"{work}/frame_%04d.png",
    ], batch=batch)
    crop_frames(work, n, durations, width=width, height=height,
                batch=batch)


def _vobsub_render_candidates(work: str, n: int, durations: list[int] | None,
                              w: str, h: str, batch: bool) -> tuple[int, int]:
    """Render VobSub events, retrying across candidate canvas sizes.

    The .idx size line sets the subtitle canvas and normally equals the
    video size, but a subtitle authored at a different resolution renders
    blank at the video size. Try the video size first (to keep the common
    case's output identical), then common authoring canvases, and pick the
    first that leaves at most a quarter of the events blank; if none does,
    use the canvas with the fewest blanks and warn.

    Args:
        work: Temporary work directory holding sub.idx/sub.sub.
        n: Number of subtitle events.
        durations: Per-event on-screen durations in ms (length n).
        w: Video width, as a string from ffprobe.
        h: Video height, as a string from ffprobe.
        batch: Raise TrackError on failure instead of exiting.

    Returns:
        The chosen ``(canvas_width, canvas_height)``; the work dir is left
        holding that canvas' ``frame_*.png`` renders and ``crops/``.
    """
    try:
        vw, vh = int(w), int(h)
    except (TypeError, ValueError):
        vw, vh = 0, 0
    candidates: list[tuple[int, int]] = []
    if vw > 0 and vh > 0:
        candidates.append((vw, vh))
    for cw, ch in _VOBSUB_CANVAS_CANDIDATES:
        if (cw, ch) not in candidates:
            candidates.append((cw, ch))

    best: tuple[int, int, int] | None = None  # (empty, cw, ch)
    last: tuple[int, int] = (0, 0)
    for cw, ch in candidates:
        last = (cw, ch)
        _render_vobsub_at(work, n, durations, cw, ch, batch)
        empty = n - _count_crops(work)
        if best is None or empty < best[0]:
            best = (empty, cw, ch)
        if empty * 4 <= n:
            if vw > 0 and vh > 0 and (vw, vh) != (cw, ch):
                print(f"subtitle canvas is {cw}x{ch} "
                      f"(video is {vw}x{vh})")
            return cw, ch
    assert best is not None
    empty, cw, ch = best
    print(f"warning: subtitles were mostly blank at every canvas size; "
          f"using {cw}x{ch} ({empty}/{n} events blank)")
    if last != (cw, ch):
        _render_vobsub_at(work, n, durations, cw, ch, batch)
    return cw, ch


def process_track(file: str, stream: str, stream_i: int,
                  streams: list[dict], ocr_lang: str, out: str, par: int,
                  w: str, h: str, batch: bool = False,
                   assume_english: bool = False, workdir: str = "",
                   debug: bool = False) -> int:
    """Extract one subtitle track and OCR it to an SRT file.

    Pipeline: mkvextract -> fix the .idx size line (VobSub) -> ffmpeg PNG
    renders -> crop -> tesseract -> SRT. PGS tracks render at native page
    size and time from the frame pts. The workdir is removed unless debug
    is set.

    Args:
        file: Source MKV path.
        stream: Stream index as a string, for messages.
        stream_i: Stream index as an int.
        streams: ffprobe stream dicts.
        ocr_lang: Forced tesseract language; "" to use the track's tag.
        out: Output SRT path; "" to use the default.
        par: tesseract parallelism.
        w: Video width; for VobSub the .idx size line is fixed to w x h.
        h: Video height.
        batch: Raise TrackError on failure instead of exiting.
        assume_english: Treat an untagged stream as English.
        workdir: Base directory for the temp workdir.
        debug: Keep the workdir after the run.

    Returns:
        Number of entries written to the SRT.
    """
    chosen = next((s for s in streams if s.get("index") == stream_i), None)
    if chosen is None:
        fail(f"no stream with index {stream} in {file}", batch)
    s_type = chosen.get("codec_type") or ""
    s_codec = chosen.get("codec_name") or ""
    s_lang = (chosen.get("tags") or {}).get("language") or "unknown"
    if s_type != "subtitle":
        fail(f"stream {stream} is a {s_type} stream, not a subtitle", batch)
    if s_codec not in ("dvd_subtitle", "hdmv_pgs_subtitle"):
        fail(f"unsupported subtitle codec: {s_codec} "
             "(need dvd_subtitle/VobSub)", batch)

    if not ocr_lang:
        if assume_english and s_lang in ("", "unknown", "und"):
            ocr_lang = "eng"
        elif not s_lang or s_lang == "unknown":
            fail(f"stream {stream} has no language tag; "
                 f"pass --tesseract-language LANG", batch)
        else:
            ocr_lang = s_lang
    ocr_lang = tesseract_lang(ocr_lang)
    if ocr_lang not in (
            run_quiet_ok(["tesseract", "--list-langs"]).splitlines()):
        fail(f"tesseract has no language traineddata for: {ocr_lang}", batch)

    work = make_workdir(workdir)
    try:
        print(f"extracting track {stream} ({s_codec}, {s_lang}) "
              f"from {file} ...")
        pgs = s_codec == "hdmv_pgs_subtitle"
        ext = "sup" if pgs else "sub"
        run_captured([
            "mkvextract", file, "tracks", f"{stream}:{work}/sub.{ext}",
        ], batch=batch)
        durations = None
        if pgs:
            if not os.path.isfile(f"{work}/sub.sup"):
                fail("mkvextract produced no sub.sup", batch)
            # PGS pages carry no display duration; each entry starts at
            # the frame pts and ends when the next page starts.
            probed = probe_pgs_starts(work)
            if probed is None:
                fail("no frame timestamps or size in sub.sup", batch)
            starts, pgs_w, pgs_h = probed
            n = len(starts)
            Path(f"{work}/starts.json").write_text(json.dumps(starts))
            Path(f"{work}/durations.json").write_text(json.dumps(None))
        else:
            if not (os.path.isfile(f"{work}/sub.sub")
                    and os.path.isfile(f"{work}/sub.idx")):
                fail("mkvextract produced no sub.sub/sub.idx", batch)

            n = sum(1 for line in Path(f"{work}/sub.idx").read_text(
                errors="replace").splitlines()
                if line.startswith("timestamp:"))
            if n == 0:
                fail("no timestamp lines in sub.idx", batch)

            # Per-entry on-screen durations (ms) from the VobSub packets;
            # each entry ends when its own subtitle disappears rather than
            # when the next starts.
            durations = probe_durations(work, n)
            Path(f"{work}/durations.json").write_text(
                json.dumps(durations))

        if pgs:
            render_w, render_h = pgs_w, pgs_h
            print(f"rendering {n} subtitle events to {render_w}x{render_h} "
                  f"frames ...")
            # Render at the native page size: scaling to the video size
            # would distort the text when the two differ. The demuxer
            # emits a display and an identical end frame per page plus
            # one initial blank frame; keep every frame and let
            # crop_frames pick each page's display frame.
            run_captured([
                "ffmpeg", "-hide_banner", "-v", "error",
                "-i", f"{work}/sub.sup",
                "-filter_complex", "[0:s:0]format=rgba[v]",
                "-map", "[v]", "-c:v", "png", "-fps_mode", "passthrough",
                f"{work}/frame_%04d.png",
            ], batch=batch)
            crop_frames(work, n, durations, width=render_w,
                        height=render_h, batch=batch, pgs=pgs)
        else:
            # VobSub: the .idx size line names the subtitle canvas, which
            # can differ from the video resolution (a subtitle authored at
            # 1080p on a 480p video renders blank at the video size). Try
            # the video size first, then common authoring canvases, and use
            # the first that yields mostly non-blank events.
            render_w, render_h = _vobsub_render_candidates(
                work, n, durations, w, h, batch)

        crops_dir = f"{work}/crops"
        n_crops = (
            len([p for p in os.listdir(crops_dir) if p.endswith(".png")])
            if os.path.isdir(crops_dir) else 0
        )
        if n_crops > 0:
            run_tesseract(crops_dir, n_crops, ocr_lang, par, batch=batch)

        if not out:
            out = default_out(file, s_lang, ocr_lang)

        return write_srt(work, n, out, batch=batch,
                         english=(tag_to_2(ocr_lang) == "en"))
    finally:
        if not debug:
            shutil.rmtree(work, ignore_errors=True)


def find_mkvs(dirpath: str) -> list[str]:
    """Recursively find .mkv files under a directory.

    Hidden directories (starting with a dot) are not entered.

    Args:
        dirpath: Directory to scan.

    Returns:
        Sorted list of .mkv paths (extension matched case-insensitively).
    """
    found = []
    for root, dirs, names in os.walk(dirpath):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        for name in names:
            if name.lower().endswith(".mkv"):
                found.append(os.path.join(root, name))
    return sorted(found)


def codec_matches(wanted: str, codec: str) -> bool:
    """Check whether a codec name matches a --type value.

    Matching is case-insensitive, ignores non-alphanumerics, and is
    prefix-based, so "VC-1" matches "vc1" and "mpeg2" matches
    "mpeg2video".

    Args:
        wanted: Value of --type.
        codec: ffprobe codec_name of the primary video stream.

    Returns:
        True if the codec matches.
    """
    w = re.sub(r"[^a-z0-9]", "", wanted.lower())
    c = re.sub(r"[^a-z0-9]", "", codec.lower())
    return bool(w) and c.startswith(w)


def type_matches(vtype: str, streams: list[dict]) -> bool:
    """Check a file's streams against comma-separated --type criteria.

    All criteria must match (AND). Each criterion is one of:
    a resolution such as 480 or 1080p (compared against the primary
    video stream's height; the "p" is optional and ignored, so 480
    matches both 480i and 480p), a subtitle codec name (dvd_subtitle
    or hdmv_pgs_subtitle, aliases dvd and pgs; the file needs at least
    one such subtitle stream), or anything else, which is treated as a
    primary video codec prefix (see codec_matches).

    Args:
        vtype: Value of --type (comma-separated criteria).
        streams: ffprobe stream list of the file.

    Returns:
        True if every criterion matches.
    """
    video = next((s for s in streams
                  if s.get("codec_type") == "video"), {})
    sub_codecs = [s.get("codec_name", "").lower() for s in streams
                  if s.get("codec_type") == "subtitle"]
    for crit in (c.strip() for c in vtype.split(",")):
        if not crit:
            continue
        m = re.fullmatch(r"(\d+)p?", crit, re.IGNORECASE)
        if m:
            if video.get("height") != int(m.group(1)):
                return False
        elif crit.lower() in ("dvd", "dvd_subtitle", "pgs",
                              "hdmv_pgs_subtitle"):
            code = ("dvd_subtitle" if crit.lower().startswith("dvd")
                    else "hdmv_pgs_subtitle")
            if code not in sub_codecs:
                return False
        elif not codec_matches(crit, video.get("codec_name", "")):
            return False
    return True


def select_stream(streams: list[dict], sel_lang: str, stream: str,
                  file: str, batch: bool) -> tuple[str, int]:
    """Pick a subtitle stream index.

    A positional stream index wins over -l lang. Without either, uses the
    track marked default, else the first English (eng/en) subtitle track,
    else the first subtitle track.

    Args:
        streams: ffprobe stream dicts.
        sel_lang: Value of -l, or "".
        stream: Positional stream index, or "".
        file: MKV path, used in messages.
        batch: Raise TrackError instead of exiting when nothing matches.

    Returns:
        (stream index as given, stream index as int).
    """
    if not stream and sel_lang:
        sel2 = lang_to_2(sel_lang)
        matched = ""
        for s in sorted((s for s in streams
                         if s.get("codec_type") == "subtitle"),
                        key=lambda s: s["index"]):
            tag = (s.get("tags") or {}).get("language") or ""
            tag2 = tag_to_2(tag)
            if tag2 == sel2:
                matched = str(s["index"])
                break
        if not matched:
            fail(f"no subtitle track with language {sel_lang} in {file} "
                 f"(see -L/--list)", batch)
        stream = matched
        print(f"no stream index given; using first {sel_lang} "
              f"subtitle track {stream}")
    elif not stream:
        subs = sorted((s for s in streams
                       if s.get("codec_type") == "subtitle"),
                      key=lambda s: s["index"])
        d = next((s for s in subs
                  if (s.get("disposition") or {}).get("default") == 1), None)
        e = next((s for s in subs
                  if ((s.get("tags") or {}).get("language")
                      or "") in ("eng", "en")), None)
        if d is not None:
            chosen_s, reason = d, "default subtitle track"
        elif e is not None:
            chosen_s, reason = e, "first English subtitle track"
        elif subs:
            chosen_s, reason = subs[0], "first subtitle track"
        else:
            fail(f"no subtitle streams in {file} (see -L/--list)", batch)
        stream = str(chosen_s["index"])
        pick_lang = (chosen_s.get("tags") or {}).get("language") or ""
        print(f"no stream index given; using {reason} {stream} ({pick_lang})")

    if not stream.isdigit():
        die(f"stream index must be a number, got: {stream}")
    return stream, int(stream)


def process_first_each(file: str, streams: list[dict], par: int,
                       force: bool, out_dir: str, workdir: str, debug: bool,
                        batch: bool) -> tuple[list[str], int, int]:
    """Process the first subtitle stream per language of one file.

    Args:
        file: MKV path.
        streams: ffprobe stream dicts.
        par: tesseract parallelism.
        force: Overwrite existing SRT outputs.
        out_dir: If set, redirect each default output here (directory mode).
        workdir: Base directory for temporary workdirs.
        debug: Keep the temporary workdirs.
        batch: Raise TrackError instead of exiting on a fatal failure.

    Returns:
        (list of per-track failure messages, number of entries written,
        number of streams extracted); an empty list means all ok or skipped.
    """
    selected, warning = first_per_language(streams)
    if not selected:
        fail(f"no subtitle streams in {file} (see -L/--list)", batch)
    pending = []
    failures: list[str] = []
    entries = 0
    n_done = 0
    for idx in selected:
        assume_english = idx == warning
        try:
            track_out = output_for_track(file, streams, idx, "",
                                         batch=True,
                                         assume_english=assume_english)
        except Exception as e:
            print(f"error: track {idx} ({stream_lang(streams, idx)}): {e}",
                  file=sys.stderr)
            failures.append(f"track {idx} ({stream_lang(streams, idx)}): {e}")
            continue
        if out_dir:
            track_out = os.path.join(out_dir, os.path.basename(track_out))
        if not force and os.path.isfile(track_out):
            print(f"skipping {track_out}: file already exists "
                  f"(use -f to overwrite)")
        else:
            pending.append((idx, track_out, assume_english))
    if pending:
        w, h = video_size(file)
        for idx, track_out, assume_english in pending:
            if idx == warning:
                print(f"warning: stream {idx} has no language tag; "
                      f"assuming English",
                      file=sys.stderr)
            try:
                entries += process_track(file, str(idx), idx, streams, "",
                                         track_out, par, w, h,
                                         batch=True,
                                         assume_english=assume_english,
                                         workdir=workdir, debug=debug)
                n_done += 1
            except Exception as e:
                print(f"error: track {idx} ({stream_lang(streams, idx)}): {e}",
                      file=sys.stderr)
                failures.append(
                    f"track {idx} ({stream_lang(streams, idx)}): {e}")
    return failures, entries, n_done


def process_file(path: str, streams: list[dict], video_dur: str,
                 stream: str, sel_lang: str, first_each: bool, out_dir: str,
                 ocr_lang: str, par: int, force: bool, workdir: str,
                  debug: bool) -> list[str]:
    """Process the subtitle tracks of one MKV file in directory mode.

    Args:
        path: MKV path.
        streams: ffprobe stream dicts (already probed).
        video_dur: Video duration as HH:MM:SS, from the probe.
        stream: Positional stream index to apply, or "".
        sel_lang: Value of -l, or "".
        first_each: Use -1 (first stream per language) mode.
        out_dir: Output directory for SRT files, or "".
        ocr_lang: Value of --tesseract-language, or "".
        par: tesseract parallelism.
        force: Overwrite existing SRT outputs.
        workdir: Base directory for temporary workdirs.
        debug: Keep the temporary workdirs.

    Returns:
        List of failure messages (empty means ok or skipped).
    """
    t0 = time.time()
    try:
        if first_each:
            failures, entries, n_done = process_first_each(
                path, streams, par, force, out_dir, workdir, debug,
                batch=True)
            if not failures:
                print(file_done_line(path, t0, entries, video_dur, n_done))
            return failures
        stream, stream_i = select_stream(streams, sel_lang, stream, path,
                                         batch=True)
        out = output_for_track(path, streams, stream_i, ocr_lang, batch=True)
    except Exception as e:
        print(f"error: {e}", file=sys.stderr)
        return [str(e)]
    if out_dir:
        out = os.path.join(out_dir, os.path.basename(out))
    if not force and os.path.isfile(out):
        print(f"skipping {out}: file already exists (use -f to overwrite)")
        return []
    w, h = video_size(path)
    try:
        entries = process_track(path, stream, stream_i, streams, ocr_lang,
                                out, par, w, h, batch=True, workdir=workdir,
                                debug=debug)
    except Exception as e:
        print(f"error: track {stream_i} ({stream_lang(streams, stream_i)}): "
              f"{e}", file=sys.stderr)
        return [f"track {stream_i} ({stream_lang(streams, stream_i)}): {e}"]
    print(file_done_line(path, t0, entries, video_dur, 1))
    return []


def process_directory(dirpath: str, stream: str, out: str, sel_lang: str,
                      ocr_lang: str, par: str, listing: bool,
                      first_each: bool, force: bool, workdir: str,
                      debug: bool, assume_yes: bool, vtype: str) -> None:
    """Scan a directory for .mkv files and process their subtitle tracks.

    Recursively finds .mkv files, lists them with the codec of their
    primary (first) video stream, asks for confirmation (unless -y), then
    processes every file with the same track selection and options as
    single-file mode.

    Args:
        dirpath: Directory to scan recursively.
        stream: Positional stream index applied to every file, or "".
        out: Directory that receives each SRT file, or "".
        sel_lang: Value of -l, or "".
        ocr_lang: Value of --tesseract-language, or "".
        par: tesseract parallelism.
        listing: True if -L/--list was given (rejected for directories).
        first_each: True if -1 was given.
        force: Overwrite existing SRT outputs.
        workdir: Base directory for temporary workdirs.
        debug: Keep the temporary workdirs.
        assume_yes: Skip the confirmation prompt.
        vtype: Value of --type, or "".
    """
    if listing:
        die("-L/--list cannot be combined with a directory")
    if not (par.isdigit() and int(par) >= 1):
        die(f"-j must be a positive number, got: {par}")
    par = int(par)
    if first_each:
        if stream:
            die(f"-1 cannot be combined with a stream index: {stream}")
        if sel_lang:
            die(f"-1 cannot be combined with -l: {sel_lang}")
        if ocr_lang:
            die(f"-1 cannot be combined with --tesseract-language: {ocr_lang}")

    entries = []
    for path in find_mkvs(dirpath):
        try:
            raw = run_captured(
                ["ffprobe", "-v", "error", "-show_streams", "-show_entries",
                 "format=duration", "-of", "json", path], batch=True)
        except TrackError as e:
            print(f"skipping {path}: {e}", file=sys.stderr)
            continue
        probe = json.loads(raw)
        streams = probe.get("streams", [])
        video = next((s for s in streams
                      if s.get("codec_type") == "video"), None)
        codec = (video or {}).get("codec_name", "")
        entries.append((path, codec, streams, video_duration_hms(probe)))

    if vtype:
        entries = [(p, c, s, d) for p, c, s, d in entries
                   if type_matches(vtype, s)]

    if not entries:
        if vtype:
            print(f"no mkv files in {dirpath} match --type {vtype}")
        else:
            print(f"no mkv files found in {dirpath}")
        sys.exit(0)

    print(f"found {len(entries)} mkv file(s):")
    for path, codec, _streams, _dur in entries:
        print(f"  {codec or 'unknown'}  {path}")

    if not assume_yes:
        try:
            ans = input(f"Process all {len(entries)} file(s)? [y/N] ")
        except EOFError:
            ans = ""
        if ans.strip().lower() not in ("y", "yes"):
            print("cancelled")
            sys.exit(0)

    if out:
        if os.path.exists(out) and not os.path.isdir(out):
            die(f"-o is not a directory: {out}")
        os.makedirs(out, exist_ok=True)

    m = len(entries)
    n_err = 0
    errors: list[tuple[str, list[str]]] = []
    t0 = time.time()
    for i, (path, _codec, streams, video_dur) in enumerate(entries, 1):
        print(f"\nProcessing file {i}/{m} : {path}")
        errs = process_file(path, streams, video_dur, stream, sel_lang,
                            first_each, out, ocr_lang, par, force, workdir,
                            debug)
        if errs:
            n_err += 1
            errors.append((path, errs))

    print(f"\ndone: {m - n_err} ok, {n_err} error(s) of {m} file(s)")
    for path, errs in errors:
        print(f"  {os.path.abspath(path)}: error: {'; '.join(errs)}")
    print(f"\nprocessed {m} file(s) in {_fmt_dur(int(time.time() - t0))}")
    sys.exit(1 if n_err else 0)


if __name__ == "__main__":
    main()
