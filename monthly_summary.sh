#!/bin/bash

: <<'BASH_DOC_MODULE'

Running `monthly_summary.sh 2024-07` produces an md-formatted summary of all the PRs that were
merged into mathlib master in the month 2024-07.
A "raw" format can be obtain running `monthly_summary.sh 2024-07 raw`.

There is a slight discrepancy

BASH_DOC_MODULE


repository='leanprover-community/mathlib4'
baseUrl="https://github.com/${repository}/pull/"

# the year and month being processed
yr_mth="${1}" #"$(date +%Y-%m)"
yr_mth_day=${yr_mth}-01

mth="$(date -d "${yr_mth_day}" '+%B')"
title="### ${mth} in Mathlib summary"

printf '%s\n\n' "${title}"

{
# Check if required argument is provided
if [ "$#" -gt 2 ]; then
    printf $'Usages:\n%s <YYYY-MM>\n%s <YYYY-MM> raw\n\nFor instance `%s 2024-07`\n\nThe `raw` input skips .md formatting\n' "${0}" "${0}" "${0}"
    exit 1
fi

rm -rf found_by_gh.txt found_by_git.txt

findInRange () {

# Get the start and end dates
startDate="${1}"
endDate="${2}"

# find how many commits to master there have been in the given range -- note that there is a limit to how many commits `gh` returns
commits_in_range="$(git log --since="${startDate}" --until="${endDate}" --pretty=oneline | wc -l)"

# Retrieve merged (i.e. closed, due to bors) PRs from the given range
prs=$(gh pr list --repo "$repository" --state closed --base master --search "closed:${startDate}..${endDate}" --json number,labels,title,author --limit "$((commits_in_range * 2))")

# Store to file `found_by_gh.txt` the PR numbers, as found by `gh`
echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "(#\(.number))"' | sort >> found_by_gh.txt

# Store to file `found_by_git.txt` the PR numbers, as found by looking at the commits to `master`
git log --pretty=oneline --since="${startDate}" --until="${endDate}" |
  sed -n 's=.*\((#[0-9]*)\)$=\1=p' | sort >> found_by_git.txt

echo "$prs"
}

start_date="${yr_mth_day}T00:00:00"
end_date="$(date -d "${yr_mth_day} + 1 month - 1 day" +%Y-%m-%d)T23:59:59"

mth="$(date -d "${yr_mth_day}" '+%B')"
prev_mth="$(date -d "${yr_mth_day} - 1 day" '+%B')"
next_mth="$(date -d "${yr_mth_day} + 1 month" '+%B')"

commits_in_range="$(git log --since="${start_date}" --until="${end_date}" --pretty=oneline | wc -l)"

printf $'\n\nBetween %s and %s there were\n' "${yr_mth_day}" "${end_date/%T*}"

printf $'* %s commits to `master` and\n' "${commits_in_range}"

(
  findInRange "${start_date}" "${yr_mth}-15T23:59:59" | sed -z 's=]\n*$=,\n='
  findInRange "${yr_mth}-16T00:00:00" "${end_date}"   | sed -z 's=^\[=='
) | jq -S -r '.[] |
  select(.title | startswith("[Merged by Bors]")) |
  "\(.labels | map(.name | select(startswith("t-"))) ) PR #\(.number) \(if .author.name == "" then .author.login else .author.name end): \(.title)"' |
  sort |
  awk 'BEGIN{ labels=""; con=0; total=0 }
    { total++
      if(!($1 in seen)) { con++; order[con]=$1; seen[$1]=0 }
      seen[$1]++
      gsub(/\[Merged by Bors\] - /, "")
      rest=$2; for(i=3; i<=NF; i++){rest=rest" "$i};acc[$1]=acc[$1]"\n"rest }
    END {
      printf("* %s closed PRs\n", total)
      for(i=1; i<=con; i++) {
        tag=order[i]
        gsub(/\[\]/, "Miscellaneous", tag)
        gsub(/["\][]/, "", tag)
        gsub(/,/, " ", tag)
        noPR=seen[order[i]]
        printf("\n%s, %s PR%s%s\n", tag, noPR, noPR == "1" ? "" : "s", acc[order[i]])
      }
    }
  '

only_gh="$( comm -23 <(sort found_by_gh.txt) <(sort found_by_git.txt) | sed 's=^=PR =' | tr -d '()')"
only_git="$(comm -13 <(sort found_by_gh.txt) <(sort found_by_git.txt) | sed 's=^=PR =' | tr -d '()')"

printf $'\n---\nReports\n\n'

if [ -z "${only_gh}" ]
then
  printf $'* All PRs are accounted for!\n'
else
  printf $'* PRs not corresponding to a commit (CI started in %s and ended in %s?)\n%s\n' "${prev_mth}" "${mth}" "${only_gh}"
fi

if [ -z "${only_git}" ]
then
  printf $'\n* All commits are accounted for!\n'
else
  printf $'\n* PRs not found by `gh` (CI started in %s and ended in %s?)\n%s\n' "${mth}" "${next_mth}" "${only_git}"
fi

printf -- $'---\n'

rm -rf found_by_gh.txt found_by_git.txt
} | {
  if (( $2 == "raw" ))
  then
    cat -
  else  # extra .md formatting
    sed '
      / [0-9]* PRs$/{
        s=^=</details><details><summary>\n=
        s=$=\n</summary>\n=
      }
      s=^PR #\([0-9]*\)=* PR [#\1]('"${baseUrl}"'\1)=' |
    sed -z '
      s=</details><details><summary>=<details><summary>=
      s=\n---\nReports\n\n=\n</details>\n\n---\n\n<details><summary>Reports</summary>\n\n=
      s=\n---[\n]*$=\n\n</details>\n&=
    '
  fi
  }
