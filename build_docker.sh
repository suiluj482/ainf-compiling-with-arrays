#! /bin/bash

PROJ=lake

sudo docker build . \
  -t "$PROJ" \
  --network=host \
  --build-arg LEAN_VERSION=$(cat src/lean-toolchain)
#sudo docker run -it -e HOST_UID=$(id -u) -v "$PWD":/app "$PROJ" "$@"

rm docker-image.tar
sudo docker save "$PROJ" -o docker-image.tar

##sudo docker container prune
#sudo docker image rm -f "$PROJ"
#sudo docker load -i docker-image.tar
#sudo docker run -it -e HOST_UID=$(id -u) -v "$PWD":/app "$PROJ"
