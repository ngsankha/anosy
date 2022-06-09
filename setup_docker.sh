#!/bin/bash

# The following script is modified from the RbSyn artifact
set -e
IMG_NAME="anosy-artifact-img"
CONTAINER_NAME="anosy-artifact"
DIR="/root/anosy"

if [[ "$(docker images -q $IMG_NAME 2> /dev/null)" == "" ]]; then
    docker build -t $IMG_NAME .
fi

echo "[0] starting container with name $CONTAINER_NAME ..."
if [ "$(docker ps -a | grep $CONTAINER_NAME)" ]; then
    echo "docker $CONTAINER_NAME already exist, remove it now"
    docker rm $CONTAINER_NAME
fi
docker run -v "$(pwd)":$DIR -w $DIR --name=$CONTAINER_NAME -it $IMG_NAME bash -l
