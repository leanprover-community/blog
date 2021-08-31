set -e
set -x

# is $DEPLOY_GITHUB_USER: needed?
git clone --branch deploy "https://pat:$DEPLOY_GITHUB_TOKEN@github.com/leanprover-community/blog.git" ./build

nikola build
rm -rf build/docs
mv output build/docs

if [ "$github_repo" = "leanprover-community/blog" -a "$github_ref" = "refs/heads/master" ]; then
  cd build/
  git config user.email "leanprover.community@gmail.com"
  git config user.name "leanprover-community-bot"
  git add -A .
  git diff-index HEAD
  git diff-index --quiet HEAD || { git commit -m "deploy site from $git_hash" && git push; }
fi