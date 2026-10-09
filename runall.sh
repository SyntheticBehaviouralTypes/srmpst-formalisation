#!/usr/bin/env bash

# Parse command line arguments
AGDA_FLAGS=""
CLEAN=0
WITH_TESTS=0

show_help() {
    cat << EOF
Usage: $0 [OPTIONS]

Type-check the project roots.

By default this is an INCREMENTAL build: existing *.agdai interface files are
reused, so only what actually changed is re-checked.  Use --clean for a
from-scratch rebuild — that is the slow, memory-hungry path (see the note on
Tests/SkipBeforeVar.agda below), so keep it for the end of a piece of
work rather than for every iteration.

OPTIONS:
    --tests               Also check TEST_ROOTS (expensive, see NOTES)
    --clean               Delete all *.agdai first (full rebuild)
    --CheckClosedProof    Run Agda with --no-allow-unsolved-metas flag
                         to ensure all proofs are closed
    --help               Show this help message and exit

EXAMPLES:
    $0                              # incremental (default)
    $0 --clean                      # full rebuild, from scratch
    $0 --clean --CheckClosedProof   # full rebuild, no holes tolerated

NOTES:
    No file is expected to have holes.  Any hole is a real failure.

    ROOTS only type-check statements.  TEST_ROOTS additionally FORCE
    decisions (via toWitness / T ⌊_⌋), which is the expensive part, so they
    are opt-in via --tests.  Everything under Examples/ and Tests/ is in
    TEST_ROOTS, so

        $0 --clean --tests

    checks every .agda file in the repository from scratch.  Nothing is
    excluded and there are no special cases.  Measured 2026-10-07:
    478 s, 2.3 GB peak resident.

    Every file is checked through agda-guard.sh, which kills Agda once it
    uses more than AGDA_MEM_PERCENT (default 40) percent of physical memory.

    `wellBehaved?` witnesses must be `opaque`: a transparent one is re-evaluated
    at every use site.
EOF
    exit 0
}

for arg in "$@"; do
    case $arg in
        --tests)
            WITH_TESTS=1
            ;;
        --clean)
            CLEAN=1
            ;;
        --CheckClosedProof)
            AGDA_FLAGS="--no-allow-unsolved-metas"
            ;;
        --help)
            show_help
            ;;
        *)
            echo "Unknown option: $arg"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Explicit list, not `*.agda`: after the 2026-08 restructure the roots are
# no longer all at top level (`Definitions/Graph.agda` is parameterised by
# `N` and lives under `Definitions/`).  `Check.agda` pulls in Check/Wait,
# Check/Alg, Check/Graph and Check/Network -- and through Check/Alg, the
# whole Definitions/Typing/Alg* family, which is therefore covered here.

ROOTS=(
    Definitions.agda
    Definitions/Graph.agda
    Definitions/Typing/AlgNorm.agda
    Definitions/Typing/AlgDeclarative.agda
    Definitions/View/Lemmas.agda
    Safety.agda
    Check.agda
)

# Opt-in only (--tests).  These are separated from ROOTS because they FORCE
# decisions rather than only type-check statements — not because any of them
# is expected to fail.  Globbed, so a new example or test is picked up
# automatically and cannot be silently left unchecked.
TEST_ROOTS=(
    Tests/*.agda
    Examples/*.agda
)

if [ $CLEAN -eq 1 ]; then
    echo "Full rebuild: deleting *.agdai"
    find . -name "*.agdai" -type f -delete
fi

TO_CHECK=("${ROOTS[@]}")
if [ $WITH_TESTS -eq 1 ]; then
    TO_CHECK+=("${TEST_ROOTS[@]}")
fi

GUARD="$(dirname "$0")/agda-guard.sh"
errors=0

for file in "${TO_CHECK[@]}"; do
    # Memory-capped: see agda-guard.sh.
    out=$("$GUARD" $AGDA_FLAGS "$file" 2>&1)
    status=$?
    echo "$out" | grep -v "^ *Checking"

    if [ $status -ne 0 ]; then
        if [ $status -eq 137 ] || echo "$out" | grep -q "Heap exhausted"; then
            echo "Memory cap exceeded: $file"
        fi
        echo "Error processing file: $file"
        errors=$((errors + 1))
    fi
done

# Check if there were any errors
if [ $errors -gt 0 ]; then
    echo "There were $errors errors."
else
	echo -e "\033[1;32mAll files processed successfully!\033[0m"
fi

exit $errors
