from github import Github
from datetime import datetime, date, time
from dateutil.relativedelta import *
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("month", help="Month",
                    type=int)
parser.add_argument("year", help="Year",
                    type=int)
args = parser.parse_args()

def extract_folder(title):
    start = title.index('(')
    end = title.index(')', start+1)
    return title[start+1:end]

def extract_pr_number(title):
    words = title.split()
    return words[-1][2:-1]

def extract_msg_title(title):
    start = title.index(')') # this is totally stupid, but some people forget the colon
    words = title.split()
    end = len(words[-1])
    return title[start+2:-end].strip()

class mathlib_commit():
    def __init__(self, commit):
        self.author = commit.commit.author.name
        title = commit.commit.message.splitlines()[0]
        self.pr = extract_pr_number(title)
        self.folder = extract_folder(title)
        self.msg_title = extract_msg_title(title)
        self.feature = title.startswith("feat")

g = Github()
repo = g.get_repo("leanprover-community/mathlib")

date1 = date(args.year, args.month, 1)
date2 = date1 + relativedelta(months=+1)
time = time(0, 0)

now = datetime.now()

monthnames_uc = ["NaM", "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
monthnames_lc = ["NaM", "jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

# Get all commits in the timeframe
commit_list = repo.get_commits(since=datetime.combine(date1,time), until=datetime.combine(date2,time))

mathlib_commits = list(map(lambda commit: mathlib_commit(commit), commit_list))

number_of_commits = len(mathlib_commits)

sorted_commits = sorted(mathlib_commits, key=lambda commit: commit.folder)

this_month_file = open("month-in-mathlib-" + monthnames_lc[args.month] + "_" + str(args.year) + ".md", "a")

print("Number of commits: " + str(number_of_commits))

print("---\nauthor: 'Mathlib community'\ncategory: 'month-in-mathlib'\ndate: " +
        str(now) + "\ndescription: ''\nhas_math: true\nlink: ''\nslug: month-in-mathlib-" +
        monthnames_lc[args.month] + "-" + str(args.year) +
        "\ntags: ''\ntitle: This month in mathlib (" + monthnames_uc[args.month]
        + " " + str(args.year) + ")\ntype: text\n---\nThis month there were " +
        number_of_commits + " PRs merged into mathlib.\n\n<!-- TEASER_END -->", file=this_month_file)

for commit in sorted_commits:
    if commit.feature:
        print("* [PR #" + commit.pr +
                "](https://github.com/leanprover-community/mathlib/pull/" +
                commit.pr + ")" + " " + commit.folder + ": " + commit.msg_title, file=this_month_file)
