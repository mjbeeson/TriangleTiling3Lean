#!/usr/bin/env python3
# Copied from M. Bonfioli, github.com/ElVec1o/erdos634_primes_and_N200, code/lakeserial.py
# (commit 61b0412), MIT license. The newer repository formalizing-triangle-tiling-in-lean does not ship it.
"""Serial, memory-guarded lake runner.

`lake build` runs about one `lean` process per CPU core, and a single `lean` process of this library needs up to about
13.5 GB.  This script builds the requested targets ONE MODULE AT A TIME in dependency order, so that at most one `lean`
process exists, and a watchdog kills the build if the total resident memory of `lean`/`lake` exceeds LAKE_RSS_LIMIT_GB
(default 14).

usage: python3 code/lakeserial.py <lean_dir> build <Module> [<Module> ...]      (serial build in dependency order)
       python3 code/lakeserial.py <lean_dir> <anything else...>                  (passthrough `lake ...` under the watchdog)
"""
import os, re, subprocess, sys, threading, time, signal

LIMIT_GB = float(os.environ.get("LAKE_RSS_LIMIT_GB", "14"))
leandir = os.path.abspath(sys.argv[1]); args = sys.argv[2:]
proc_holder = {"p": None}
killed = {"v": False}

def _descendants():
    """PIDs of all descendants of THIS process (our lake/lean tree only; other projects' lean processes are never counted or killed)."""
    try:
        out = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,comm="], capture_output=True, text=True).stdout
    except Exception:
        return []
    rows = []
    for ln in out.splitlines():
        parts = ln.split(None, 3)
        if len(parts) == 4:
            try: rows.append((int(parts[0]), int(parts[1]), int(parts[2]), parts[3]))
            except ValueError: pass
    kids = {}
    for pid, ppid, rss, comm in rows:
        kids.setdefault(ppid, []).append((pid, rss, comm))
    stack, res = [os.getpid()], []
    while stack:
        cur = stack.pop()
        for pid, rss, comm in kids.get(cur, []):
            res.append((pid, rss, comm)); stack.append(pid)
    return res

def total_lean_rss_gb():
    tot = 0
    for pid, rss, comm in _descendants():
        if comm.rsplit("/", 1)[-1] in ("lean", "lake"):
            tot += rss
    return tot / 1048576.0

def watchdog():
    while True:
        time.sleep(2)
        g = total_lean_rss_gb()
        if g > LIMIT_GB:
            killed["v"] = True
            sys.stderr.write(f"\n[lakeserial] WATCHDOG: lean/lake RSS {g:.1f} GB > {LIMIT_GB} GB: killing all lean/lake\n")
            for _pid, _r, _c in _descendants():
                try: os.kill(_pid, 9)
                except Exception: pass
            os._exit(137)
threading.Thread(target=watchdog, daemon=True).start()

def run(cmd):
    p = subprocess.Popen(cmd, cwd=leandir)
    proc_holder["p"] = p
    return p.wait()

if not args or args[0] != "build":
    sys.exit(run(["lake"] + args))

mods = [a for a in args[1:] if not a.startswith("-")]
flags = [a for a in args[1:] if a.startswith("-")]
# Strategy: `lake build --no-build <targets>` lists (under "Some required targets logged failures:") exactly the modules whose
# own inputs are stale and whose dependencies are up to date (blocked dependents are not listed). Build those ONE AT A TIME
# (each `lake build <module>` then compiles only that module: ONE lean process), repeat until nothing is stale.
built = 0
t0 = time.time()
for it in range(1, 400):
    r = subprocess.run(["lake", "build", "--no-build"] + mods + flags, cwd=leandir, capture_output=True, text=True)
    if r.returncode == 0:
        break
    txt = r.stdout + "\n" + r.stderr
    fails = []
    grab = False
    for ln in txt.splitlines():
        if ln.startswith("Some required targets logged failures"):
            grab = True; continue
        if grab:
            if ln.startswith("- "): fails.append(ln[2:].strip())
            elif ln.strip() == "": continue
            else: grab = False
    fails = [f for f in fails if f]
    if not fails:
        sys.stderr.write("[lakeserial] --no-build failed with no module list; output tail:\n" + txt[-1500:] + "\n")
        sys.exit(r.returncode)
    for m in fails:
        built += 1
        sys.stderr.write(f"[lakeserial] pass {it}: building {m} (#{built}; {time.time()-t0:.0f}s elapsed; lean RSS {total_lean_rss_gb():.1f} GB)\n")
        rc = run(["lake", "build", m] + flags)
        if rc != 0:
            sys.stderr.write(f"[lakeserial] FAILED {m} rc={rc}\n"); sys.exit(rc)
else:
    sys.stderr.write("[lakeserial] too many passes\n"); sys.exit(4)
sys.stderr.write(f"[lakeserial] all up to date after {built} serial module builds, {time.time()-t0:.0f}s\n")
# targets are up to date: replay their logs (axiom prints) without compiling anything
sys.exit(run(["lake", "build"] + mods + flags))
