# Runs the EEST "zkevm" conformance fixtures against the stateless guest
# compiled by flapjack's own Pancake-to-RISC-V port (`flapjack-compile`),
# under ziskemu. Modeled on evm-asm's Dockerfile/DOCKER-EEST.md, which does
# the same thing for evm-asm's own (independently written) Lean-codegen
# guest; here the guest under test is the pinned `stateless-pancaketh`
# Pancake source built with flapjack's compiler instead. See
# docs/DOCKER-EEST.md for the full picture and known caveats.
FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

# ZisK 0.16.0 is known not to work for succinct proof verification against
# this guest; 0.18.0 is the current minimum known-good version. Bump with
# scripts/upgrade-zisk.sh so the Dockerfile, docs, and README stay in sync.
ARG ZISK_VERSION=0.18.0

# Pins the `pirapira/stateless-pancaketh` commit `Guest/guest.pp.pnk` and
# `guest/runtime/start.S` are fetched from (scripts/build-flapjack-guest.sh).
# This is the same commit already pinned by scripts/check-guest-parity.py
# and .github/workflows/lean_action_ci.yml.
ARG STATELESS_PANCAKETH_COMMIT=84405317d6705de9df563ad2f6cdd30b459198b4

ARG GIT_COMMIT=unknown
ARG GIT_REF=unknown
ARG BUILD_DATE=unknown

RUN apt-get update && apt-get install -y --no-install-recommends \
    git curl ca-certificates python3 xxd cpp \
    gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf \
    && rm -rf /var/lib/apt/lists/*

# ziskemu via ziskup (prebuilt binaries -- no Rust toolchain or zisk source
# build needed). --nokey: this image only runs the RISC-V guest under
# ziskemu, it never generates a zk proof, so the multi-GB proving/verify
# keys are skipped.
RUN curl -sSf https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh \
      | bash -s -- -v "${ZISK_VERSION}" --cpu --nokey -y
ENV PATH="/root/.zisk/bin:${PATH}"
RUN ziskemu --version

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /flapjack

# The evm-asm submodule supplies only its (Lean-independent) EEST harness
# scripts here -- see .dockerignore for what is excluded from the build
# context (its Lean sources, fixtures, tests, etc. are not needed: the
# harness is driven with --guest-elf/--no-build, so evm-asm's own Lean
# project is never built in this image).
COPY . .

RUN elan toolchain install "$(cat lean-toolchain)"
RUN lake build flapjack-compile

RUN scripts/build-flapjack-guest.sh "${STATELESS_PANCAKETH_COMMIT}" gen-out/guest

RUN evm-asm/scripts/eest-fetch-fixtures.sh

LABEL org.opencontainers.image.licenses="MIT"
LABEL org.opencontainers.image.source="https://github.com/pirapira/flapjack"
LABEL org.opencontainers.image.revision="${GIT_COMMIT}"
LABEL org.opencontainers.image.ref.name="${GIT_REF}"
LABEL org.opencontainers.image.created="${BUILD_DATE}"
LABEL zisk.version="${ZISK_VERSION}"
LABEL stateless-pancaketh.commit="${STATELESS_PANCAKETH_COMMIT}"

ENTRYPOINT ["scripts/eest-docker-entrypoint.sh"]
CMD ["--all", "--quiet-passes"]
