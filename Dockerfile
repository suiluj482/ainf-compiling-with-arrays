FROM ubuntu:24.04

ARG LEAN_VERSION

RUN apt-get update \
 && apt-get install -y wget \
 && wget https://github.com/leanprover/elan/releases/download/v3.0.0/elan-x86_64-unknown-linux-gnu.tar.gz \
 && tar -xf elan-x86_64-unknown-linux-gnu.tar.gz \
 && ./elan-init -y --default-toolchain $LEAN_VERSION

WORKDIR /app

ENTRYPOINT ["./run_lean.sh"]
