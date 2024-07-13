#!/bin/bash

usage () {
echo "Usage: month-in-mathlib.sh YYYY M path/to/mathlib4"
echo ""
echo "where YYYY is a 4-digit year, and M is the number of the month."
echo "Example: month-in-mathlib.sh 2021 8 ~/mathlib4"
echo "It is important that M is a natural number between 1 and 12."
echo "The formats '02' and '2' are both allowed."
echo ""
echo "Important: make sure that the mathlib4 clone is clean,"
echo "and points to an up-to-date copy of master."
exit 1
}

[ $# -ne 3 ] && { usage; }

year=$1
month=$2
mathlib=$3

# the number of days in the given month in the given year
daysOfMonth="$(date -d "$year/$month/1 + 1 month - 1 day" "+%d")"
# the 3-letter month first letter capitalized
month_uc="$(date -d "$year/$month/1" "+%b")"
# the 3-letter month lowercase
month_lc="$(date -d "$year/$month/1" "+%b" | tr A-Z a-z)"

echo "---"
echo "author: 'Mathlib community'"
echo "category: 'month-in-mathlib'"
# sadly, the MacOS date command doesn't support the --rfc-3339 option
# echo "date: $(date --rfc-3339=sec)"
echo "date: $(date -u +'%Y-%m-%d %H:%M:%S+00:00')"
echo "description: ''"
echo "has_math: true"
echo "link: ''"
echo "slug: month-in-mathlib-${month_lc}-$year"
echo "tags: ''"
echo "title: This month in Mathlib (${month_uc} $year)"
echo "type: text"
echo "---"

echo ""

pushd $mathlib > /dev/null

git log --date=iso-local --pretty=oneline --abbrev-commit --since "$yy-$mm-01" --until "$yy-$mm-$daysOfMonth" | tac |
sed 's|\([^ ]*\) \(.*\) (#\([0-9]*\))|* [PR #\3](https://github.com/leanprover-community/mathlib4/pull/\3) :: \2|'

popd > /dev/null
