#!/bin/bash
set -euo pipefail

# logZ convergence for the two SMC baseline models on the toy dataset.
#
# For each baseline model (coalescent-toy, stardecomp-toy) this sweeps over a
# range of particle counts, runs the model REPS times per count, extracts the
# SMC log normalizing constant (logZ) -- written as the first line of the
# tree-length output file by postProcessTree -- and reports logZ mean +/- std.
# A convergence plot (logZ vs particles) is produced at the end.
#
# Usage:
#   bash coreppl/models/tree-inference/smc/logz_convergence.bash
#
# Optional env overrides:
#   CPPL=/path/to/cppl   REPS=10   PARTICLES="100 1000 10000"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
export MCORE_LIBS="coreppl=$REPO_ROOT/coreppl/src"
CPPL="${CPPL:-$REPO_ROOT/build/cppl}"

BENCH_DIR="$SCRIPT_DIR/benchmarks"
OUTDIR="$SCRIPT_DIR/logz_results"
TMPDIR="$OUTDIR/tmp"

read -r -a PARTICLES <<< "${PARTICLES:-100 500 1000 2000 5000 10000}"
REPS="${REPS:-5}"
MODELS=(coalescent-toy stardecomp-toy)

rm -rf "$OUTDIR"
mkdir -p "$TMPDIR"

# mean and (sample) std of finite floats, one per line, on stdin
mean_std() {
  python3 -c "
import math, sys
xs = [float(l) for l in sys.stdin if l.strip() and l.strip().lower() != 'nan']
xs = [x for x in xs if math.isfinite(x)]
if not xs:
    print('nan\tnan'); sys.exit()
m = sum(xs)/len(xs)
s = math.sqrt(sum((x-m)**2 for x in xs)/(len(xs)-1)) if len(xs) > 1 else 0.0
print(f'{m:.6f}\t{s:.6f}')
"
}

echo "Repo:      $REPO_ROOT"
echo "cppl:      $CPPL"
echo "particles: ${PARTICLES[*]}"
echo "reps:      $REPS"
echo

for MODEL in "${MODELS[@]}"; do
  echo "============================================================"
  echo " $MODEL"
  echo "============================================================"
  BIN="$TMPDIR/$MODEL"
  ( cd "$BENCH_DIR" && "$CPPL" "$MODEL.mc" --output "$BIN" )

  DAT="$OUTDIR/logz_${MODEL}.dat"
  printf "particles\tmean\tstd\n" > "$DAT"
  printf "%-10s %-14s %-10s\n" "particles" "logZ_mean" "logZ_std"

  for P in "${PARTICLES[@]}"; do
    LOGZS="$TMPDIR/logz_${MODEL}_${P}.tmp"
    : > "$LOGZS"
    for ((r = 1; r <= REPS; r++)); do
      TL="$TMPDIR/tl_${MODEL}_${P}_${r}.txt"
      SP="$TMPDIR/sp_${MODEL}_${P}_${r}.txt"
      echo "${P}:${TL}:${SP}" | "$BIN" > /dev/null 2>&1
      head -1 "$TL" >> "$LOGZS"
    done
    STATS="$(mean_std < "$LOGZS")"
    M="$(echo "$STATS" | cut -f1)"
    S="$(echo "$STATS" | cut -f2)"
    printf "%s\t%s\t%s\n" "$P" "$M" "$S" >> "$DAT"
    printf "%-10s %-14s %-10s\n" "$P" "$M" "$S"
  done
  echo
done

echo "============================================================"
echo " Generating convergence plot"
echo "============================================================"
python3 "$SCRIPT_DIR/plot_logz_convergence.py" \
  --coalescent "$OUTDIR/logz_coalescent-toy.dat" \
  --stardecomp "$OUTDIR/logz_stardecomp-toy.dat" \
  --out "$OUTDIR/logz_convergence.png"

echo
echo "Done. Results in $OUTDIR/"
echo "  logz_coalescent-toy.dat, logz_stardecomp-toy.dat  (particles  mean  std)"
echo "  logz_convergence.png                              (logZ vs particles)"
