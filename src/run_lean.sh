#! /bin/sh

. $HOME/.elan/env

echo "> lake clean"
lake clean

echo ">" lake "$@"
lake "$@"

if [ -z "$HOST_UID" ]; then
  echo done
else
  echo change ownership to $HOST_UID
  chown -R $HOST_UID:$HOST_UID .
fi
