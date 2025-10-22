#!/usr/bin/env bash

# Parse command line arguments
AGDA_FLAGS=""

show_help() {
    cat << EOF
Usage: $0 [OPTIONS]

Compile all Agda files in the current directory.

OPTIONS:
    --CheckClosedProof    Run Agda with --no-allow-unsolved-metas flag
                         to ensure all proofs are closed
    --help               Show this help message and exit

EXAMPLES:
    $0                   # Compile all files (allows unsolved metas)
    $0 --CheckClosedProof  # Compile all files with strict checking

EOF
    exit 0
}

for arg in "$@"; do
    case $arg in
        --CheckClosedProof)
            AGDA_FLAGS="--no-allow-unsolved-metas"
            shift
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

# clean the compiled files
find . -name "*.agdai" -type f -delete

# compile

errors=0

for file in *.agda; do
    agda $AGDA_FLAGS "$file"

    # Check the exit status of the command
    if [ $? -ne 0 ]; then
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
