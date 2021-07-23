FROM ubuntu:latest

# https://askubuntu.com/questions/909277/avoiding-user-interaction-with-tzdata-when-installing-certbot-in-a-docker-contai
ARG DEBIAN_FRONTEND=noninteractive

# Load mono keys so we can install PPA to get a recent version (ubuntu ships
# with 4.x; we want 6.x)
RUN apt-get update
RUN apt-get install -y ca-certificates gnupg2
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF
RUN apt-get update
RUN apt-get install -y git apt-utils wget time make unzip graphviz apt-transport-https python3-pip clang libc++-dev
RUN pip3 install toposort
# Derived from https://docs.microsoft.com/en-us/dotnet/core/install/linux-debian
COPY install-dot-net.sh /tmp
WORKDIR /tmp
RUN ./install-dot-net.sh

RUN useradd -ms /bin/bash dafnyserver
RUN apt-get install -y vim emacs
USER dafnyserver
WORKDIR /home/dafnyserver

COPY install-dafny.sh /home/dafnyserver
RUN ./install-dafny.sh
COPY test.dfy /home/dafnyserver
RUN mkdir bin
COPY bin_dafny_sh bin/dafny
COPY bashrc-appendage /tmp
RUN cat /tmp/bashrc-appendage >> /home/dafnyserver/.bashrc
RUN pip3 install termcolor
## COPY tutorial.tgz /home/dafnyserver/tutorial.tgz
## RUN tar -C /home/dafnyserver -xzf /home/dafnyserver/tutorial.tgz
