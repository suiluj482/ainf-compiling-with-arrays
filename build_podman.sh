#! /bin/bash

PROJ=lake

podman build . \
  -t "$PROJ" \
  --network=host \
  --build-arg LEAN_VERSION=$(cat src/lean-toolchain)
#podman run -it --userns=keep-id -v "$PWD":/app "$PROJ"

rm docker-image.tar
podman save "$PROJ" -o docker-image.tar

##podman container prune
#podman image rm -f "$PROJ"
#podman load -i docker-image.tar
#podman run -it --userns=keep-id -v "$PWD":/app "$PROJ"
