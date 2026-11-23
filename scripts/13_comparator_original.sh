#!/usr/bin/env bash
# 13_comparator_original.sh: run Comparator's own judge on the ORIGINAL submission, on a real
# build, by the route leanprover-community/riemann-hypothesis described before its Lean 4.36 port
# (README "Checking it", commit f1f6d654). Its verification notes still list Comparator's verdict
# on a real export as not yet recorded.
#
# A  challenge: clean clone of the repository at f1f6d654 (Lean v4.33.1, the published Mathlib
#    pin), lake build Challenge, export it with lean4export v4.33.0
# B  solution: export Main from our finished build of the published archive (src/ tree b41b516b,
#    the archive exactly), with the clean clone's export targets; expect sha256 5ea74b91...
# C  judge: lake comparator with Lean v4.36.0 from an empty directory, the clean clone's
#    comparator.json (Lean's kernel, Lean paranoid, nanoda), in the bubblewrap sandbox if present
#
# Writes only under $OUT/orig and $WORK/orig. Nothing in the project tree changes.
cd "$(dirname "$0")"; . ./common.sh
need_proj; elan_env

REV=f1f6d65420dbbf36d6cfdac1af8d79511a855a5b
SOL_SHA=5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e
R="$OUT/orig"; W="$WORK/orig"; mkdir -p "$R" "$W"
RES="$R/RESULT.txt"
EXPBIN="$WORK/lean4export/.lake/build/bin/lean4export"
note(){ echo "$*" | tee -a "$RES"; }
peak(){ grep -E "Maximum resident|Elapsed" "$1" 2>/dev/null | sed 's/^[[:space:]]*//' | tr '\n' ';'; }
[ -f "$PROJ/.lake/build/lib/lean/Main.olean" ] || die "build not finished"
[ -x "$EXPBIN" ] || die "lean4export missing"
command -v /usr/bin/time >/dev/null || die "need GNU time (sudo apt-get install -y time)"

run_detached orig "$PWD/13_comparator_original.sh"
exec >> "$OUT/orig.log" 2>&1
export LEAN_ABORT_ON_PANIC=1 LAKE_ARTIFACT_CACHE=false
ulimit -n "$(ulimit -Hn)" 2>/dev/null || ulimit -n 65536 2>/dev/null || true
: > "$RES"
note "13_comparator_original.sh started $(date -u +%FT%TZ) on $(nproc) cores, $(ram_gb) GB"
note "repository commit $REV; project $PROJ"

# ---------------------------------------------------------------- A
log "A. challenge export from a clean clone"
C="$W/clean"
if [ -s "$W/challenge.export" ] && [ -f "$C/comparator.json" ]; then
  note "A  reusing challenge.export: $(fsize "$W/challenge.export") bytes, sha256 $(sha "$W/challenge.export")"
else
if [ ! -d "$C/.git" ]; then
  git init --quiet "$C"
  (cd "$C" && git fetch --quiet --depth 1 https://github.com/leanprover-community/riemann-hypothesis "$REV" && git checkout --quiet FETCH_HEAD)
fi
[ "$(cd "$C" && git rev-parse HEAD)" = "$REV" ] || die "clean clone not at $REV"
note "A  clean clone: lean-toolchain $(cat "$C/lean-toolchain"); src/ tree $(cd "$C" && git rev-parse HEAD:src)"
for f in lean-toolchain lake-manifest.json; do
  if cmp -s "$C/$f" "$PROJ/$f"; then note "A  $f identical to the build's"; else note "A  $f DIFFERS from the build's"; fi
done
(cd "$C" && lake exe cache get > "$R/cache.log" 2>&1 && lake build Challenge > "$R/challenge_build.log" 2>&1) \
  || die "challenge build failed (see $R)"
# shellcheck disable=SC2046
(cd "$C" && lake env "$EXPBIN" Challenge -- $(cat export-targets.txt) > "$W/challenge.export") || die "challenge export failed"
note "A  challenge.export: $(fsize "$W/challenge.export") bytes, sha256 $(sha "$W/challenge.export")"
# The clean clone's `lake exe cache get` also fetches the project's own prebuilt cache (about 91 GB);
# only the challenge is needed from it, so drop the build directory once the challenge is exported.
rm -rf "$C/.lake/build"
fi

# ---------------------------------------------------------------- B
log "B. solution export from our build"
if [ ! -s "$W/solution.export" ] || [ "$(sha "$W/solution.export")" != "$SOL_SHA" ]; then
  [ "$(free_gb)" -ge 70 ] || die "need about 70 GB free for the solution export; have $(free_gb) GB"
  # shellcheck disable=SC2046
  (cd "$PROJ" && /usr/bin/time -v -o "$R/export.time" lake env "$EXPBIN" Main -- $(cat "$C/export-targets.txt") > "$W/solution.export") \
    || die "solution export failed"
fi
got=$(sha "$W/solution.export")
note "B  solution.export: $(fsize "$W/solution.export") bytes, sha256 $got  [$(peak "$R/export.time")]"
if [ "$got" = "$SOL_SHA" ]; then note "B  MATCHES the published export and the independent runs"; else note "B  DIFFERS from $SOL_SHA"; fi

# ---------------------------------------------------------------- C
log "C. lake comparator (Lean v4.36.0)"
J="$W/judge"; rm -rf "$J"; mkdir -p "$J"; cd "$J"
echo leanprover/lean4:v4.36.0 > lean-toolchain
PATH="$(lean --print-prefix)/bin:$PATH"
note "C  judge: $(lean --version | head -1)"
note "C  config: $(tr -d '\n ' < "$C/comparator.json")"
SANDBOX=""
if command -v bwrap >/dev/null; then note "C  sandbox: bubblewrap $(bwrap --version 2>&1 | head -1)"
else SANDBOX="--inadvisably-no-sandbox"; note "C  sandbox: none (bwrap not installed); both exports were made here from files we trust"; fi
s=$(date +%s)
set +e
/usr/bin/time -v -o "$R/comparator.time" lake comparator $SANDBOX --config "$C/comparator.json" \
  --challenge-from-export "$W/challenge.export" --solution-from-export "$W/solution.export" > "$R/comparator.log" 2>&1
rc=$?
set -e
note "C  lake comparator: exit $rc ($(( $(date +%s) - s )) s)  [$(peak "$R/comparator.time")]"
tail -15 "$R/comparator.log" | tee -a "$RES"

note "finished $(date -u +%FT%TZ)"
rm -f "$OUT/orig.pid"
