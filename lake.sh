#! /bin/sh

if command -v podman; then
  time podman run -it -v "$PWD"/src:/app lake "$@"
elif command -v docker; then
  time docker run -it -e HOST_UID=$(id -u) -v "$PWD"/src:/app localhost/lake "$@"
else
  echo you need either podman or docker
fi

# Explanation:
#
# -  The argument `-it` will run the container with a text-terminal attached,
#    and in interactive mode. This means you can press CTRL-C to stop it.
#
# -  The argument `-v $PWD/src:/app` gives the docker container
#    read/write access to the folder `src`, which contains the source code.
#    This is also the place where the results will be placed.
#
# -  The argument `-e HOST_UID=(id -u)` will pass an additional environment
#    variable into the docker container that contains your user ID.
#    Docker creates files by default as user `root`, so you can get confusing
#    "permission denied" errors, if you attempt to modify those files later.
#    We use the provided user id to give ownership of created files
#    back to the current user.
#
# -  podman is by default rootless, so no sudo is necessary, and files created do
#    also belong to you by default, avoiding annoying "permission denied" errors.
