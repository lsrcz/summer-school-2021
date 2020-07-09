#!/bin/bash

#https://www.linode.com/docs/kubernetes/deploy-container-image-to-kubernetes/
#https://training.play-with-docker.com/beginner-linux/#Task_2

IMAGE_NAME=jonhdotnet/summer_school:1.0
docker image build --tag ${IMAGE_NAME} summer_school/
docker push ${IMAGE_NAME}


