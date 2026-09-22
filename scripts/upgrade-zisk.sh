#!/usr/bin/env bash
# upgrade-zisk.sh NEW_VERSION
#
# Bumps the pinned ZisK version used by Dockerfile's `ziskup -v ...` install
# step, so the pin lives in exactly one place (Dockerfile's ARG
# ZISK_VERSION) instead of being retyped at each call site.
#
# ZisK 0.16.0 is known NOT to work for succinct proof verification against
# this guest; 0.18.0 is the current minimum known-good version pinned by
# Dockerfile and documented in docs/DOCKER-EEST.md and README.md. Do not
# downgrade below it without re-validating end to end.
#
# This only rewrites the pin. It does not touch the (also pinned)
# STATELESS_PANCAKETH_COMMIT or EEST fixture tag, which are unrelated axes.
set -euo pipefail
cd "$(dirname "$0")/.."

NEW_VERSION="${1:?usage: scripts/upgrade-zisk.sh NEW_VERSION   (e.g. 0.19.0, no leading v)}"
NEW_VERSION="${NEW_VERSION#v}"

if command -v git >/dev/null 2>&1; then
  if ! git ls-remote --tags https://github.com/0xPolygonHermez/zisk "v${NEW_VERSION}" 2>/dev/null | grep -q .; then
    echo "warning: no tag v${NEW_VERSION} found in 0xPolygonHermez/zisk -- double-check the version string" >&2
  fi
fi

if ! grep -q '^ARG ZISK_VERSION=' Dockerfile; then
  echo "Dockerfile has no 'ARG ZISK_VERSION=' line to update" >&2
  exit 1
fi

sed -i.bak -E "s/^ARG ZISK_VERSION=.*/ARG ZISK_VERSION=${NEW_VERSION}/" Dockerfile
rm -f Dockerfile.bak
grep -n '^ARG ZISK_VERSION=' Dockerfile

cat <<EOF

Dockerfile now pins ZisK ${NEW_VERSION}.

Remaining manual steps:
  - update the version mentioned in docs/DOCKER-EEST.md and README.md
  - rebuild the image: docker build -t flapjack-eest .
  - re-run the fixture check and compare pass counts before merging
EOF

if command -v ziskup >/dev/null 2>&1; then
  read -r -p "Also reinstall ziskemu locally via ziskup, to match? [y/N] " reply
  if [[ "$reply" =~ ^[Yy]$ ]]; then
    ziskup -v "$NEW_VERSION" --cpu --nokey -y
    ziskemu --version
  fi
else
  cat <<EOF
ziskup not found locally. To install/upgrade it and ziskemu:
  curl -sSf https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh \\
    | bash -s -- -v ${NEW_VERSION} --cpu --nokey -y
EOF
fi
