#!/bin/zsh
# Sequential, nice'd, timeout-capped driver for the round-reduced attack sweep.
# Each cell: `<attack> <t> <n> <field> [cap_s]` as a single quoted arg.
# Appends one line per cell to the results log:
#   <csvline> | peakMB=<mem> | wall=<s> | <OK|DNF|KILL>
# Usage: ./run_sweep.sh OUTLOG "uni 2 3 kb 600" "uni 2 5 kb 600" ...
set -u
ENGINE="$(cd "$(dirname "$0")" && pwd)/round_reduced_attacks.sage"
OUT="$1"; shift
for spec in "$@"; do
  set -- ${(z)spec}
  attack=$1; t=$2; n=$3; field=$4; cap=${5:-600}
  tmperr=$(mktemp)
  start=$(date +%s.%N)
  # gtimeout sends TERM then KILL; nice -19 keeps the laptop cool; time -l -> peak RSS
  nice -n 19 gtimeout -k 5 ${cap}s /usr/bin/time -l \
      sage "$ENGINE" "$attack" "$t" "$n" "$field" > /tmp/cell_out.txt 2> "$tmperr"
  rc=$?
  end=$(date +%s.%N)
  wall=$(printf "%.1f" $((end - start)))
  # peak RSS (bytes on macOS) -> MB
  rss=$(grep "maximum resident set size" "$tmperr" | awk '{print $1}')
  if [ -n "$rss" ]; then memMB=$(printf "%.0f" $((rss/1048576.0))); else memMB="?"; fi
  csv=$(cat /tmp/cell_out.txt | grep -E "^(uni|gb)," | head -1)
  if [ $rc -eq 124 ] || [ $rc -eq 137 ]; then
    st="DNF>${cap}s"; csv="${attack},${t},${n},${field},,,,,,KILLED"
  elif [ $rc -ne 0 ]; then
    st="ERR(rc=$rc)"
  else
    st="OK"
  fi
  line="${csv} | peakMB=${memMB} | wall=${wall} | ${st}"
  print -- "$line"
  print -- "$line" >> "$OUT"
  rm -f "$tmperr"
done
