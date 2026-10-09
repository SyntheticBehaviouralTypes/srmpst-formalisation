#!/usr/bin/env bash

# Run `agda "$@"` with a memory cap, so a runaway evaluation fails instead
# of exhausting the machine.
#
# The cap is AGDA_MEM_PERCENT (default 40) percent of physical memory:
#
#   * GHC's heap is limited to 90% of the cap (`+RTS -M`), so the usual
#     failure is Agda's own "Heap exhausted" error;
#   * the whole process runs in a transient systemd scope with MemoryMax at
#     the cap and swap disabled, so anything the heap limit misses is killed
#     (exit status 137) rather than pushed into swap.
#
# Without a usable `systemd-run --user`, only the heap limit applies.

set -u

pct=${AGDA_MEM_PERCENT:-40}
total_kb=$(awk '/^MemTotal:/ { print $2 }' /proc/meminfo)
cap_kb=$(( total_kb * pct / 100 ))
heap_mb=$(( cap_kb * 9 / 10 / 1024 ))

if command -v systemd-run > /dev/null \
   && systemd-run --user --scope --quiet true 2> /dev/null; then
    exec systemd-run --user --scope --quiet \
         -p MemoryMax="${cap_kb}K" -p MemorySwapMax=0 \
         agda +RTS -M"${heap_mb}m" -RTS "$@"
else
    echo "agda-guard: systemd-run unavailable; heap limit only" >&2
    exec agda +RTS -M"${heap_mb}m" -RTS "$@"
fi
