#!/bin/bash

#Building docker images
#https://www.linode.com/docs/kubernetes/deploy-container-image-to-kubernetes/
#https://training.play-with-docker.com/beginner-linux/#Task_2

docker image build --tag jonhdotnet/summer_school:1.1 dafny_server/
# docker login
# docker push jonhdotnet/summer_school:1.1
