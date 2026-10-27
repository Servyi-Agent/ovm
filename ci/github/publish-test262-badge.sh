#!/usr/bin/env bash
# Publish the test262 pass-count badge from a runner log.
#
# Writes a shields.io endpoint JSON (`test262.json`) and pushes it to the
# `badges` branch, so the README badge always reflects the latest
# `test262-become` run.
#
#   ./ci/github/publish-test262-badge.sh [test262.log]
#
# Requires GH_TOKEN with contents:write for the repository. BADGE_REMOTE
# overrides the destination (useful for local testing), BADGE_BRANCH the
# branch name.
set -euo pipefail

log="${1:-test262.log}"
branch="${BADGE_BRANCH:-badges}"

if [[ ! -f "$log" ]]; then
    echo "test262 badge: no log at $log; skipping" >&2
    exit 0
fi

pass="$(awk '/^pass:/{print $2; exit}' "$log")"
total="$(awk '/^total:/{print $2; exit}' "$log")"
if [[ -z "$pass" || -z "$total" || "$total" == "0" ]]; then
    echo "test262 badge: no pass/total summary in $log; skipping" >&2
    exit 0
fi

remote="${BADGE_REMOTE:-}"
if [[ -z "$remote" ]]; then
    repo="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is not set}"
    token="${GH_TOKEN:?GH_TOKEN is not set}"
    remote="https://x-access-token:${token}@github.com/${repo}.git"
fi

percent="$(awk -v pass="$pass" -v total="$total" \
    'BEGIN { printf "%.1f", 100 * pass / total }')"
message="$(printf '%s passing (%s%% of %s)' "$pass" "$percent" "$total")"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
git -C "$tmp" init -q
# Keep any other files on the badge branch; start from it when it exists.
if git -C "$tmp" fetch -q --depth 1 "$remote" "refs/heads/$branch" 2>/dev/null; then
    git -C "$tmp" checkout -q FETCH_HEAD
else
    git -C "$tmp" checkout -q --orphan "$branch"
fi

cat >"$tmp/test262.json" <<EOF
{"schemaVersion":1,"label":"test262","message":"$message","color":"yellow"}
EOF

git -C "$tmp" add test262.json
git -C "$tmp" \
    -c user.name='github-actions[bot]' \
    -c user.email='41898282+github-actions[bot]@users.noreply.github.com' \
    commit -qm "Update test262 badge: $pass/$total"
git -C "$tmp" push -q "$remote" "HEAD:refs/heads/$branch"

echo "test262 badge: $message"
