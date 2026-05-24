#!/bin/bash
# Run the library build, collect every redundant-by / redundant-congruenceOf
# warning, and dump each one with file path, line number, and ~5 lines of
# context so we can walk through them by hand.

set -e
cd "$(dirname "$0")"

LOG=/tmp/library_build.log
make -j 16 library > "$LOG" 2>&1 || {
    echo "build failed; see $LOG"
    exit 1
}

WARNINGS=$(grep "^warning:" "$LOG" | grep -E "redundant " | sort -u)

if [ -z "$WARNINGS" ]; then
    echo "no redundant-by warnings"
    exit 0
fi

count=$(echo "$WARNINGS" | wc -l | tr -d ' ')
echo "$count warning(s) to consider:"
echo

echo "$WARNINGS" | while IFS= read -r line; do
    # warning: <Module.Path>:<line>[:col]: redundant ...
    location=$(echo "$line" | sed -E 's/^warning: ([^:]+):([0-9]+).*/\1:\2/')
    module=$(echo "$location" | cut -d: -f1)
    lineno=$(echo "$location" | cut -d: -f2)

    # Module.Foo  →  library/Module/Foo.math
    file="library/$(echo "$module" | tr '.' '/').math"
    if [ ! -f "$file" ]; then
        echo "?? $line"
        continue
    fi

    echo "──── $file:$lineno"
    echo "$line" | sed 's/^warning: /     /'
    # Two lines before, the line itself, two lines after.
    start=$((lineno - 2 < 1 ? 1 : lineno - 2))
    end=$((lineno + 2))
    awk -v lineno="$lineno" -v start="$start" -v end="$end" '
        NR >= start && NR <= end {
            marker = (NR == lineno) ? ">>" : "  "
            printf "%s %4d  %s\n", marker, NR, $0
        }
    ' "$file"
    echo
done
