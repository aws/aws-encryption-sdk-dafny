FROM ubuntu:18.04

USER root

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get upgrade -y \
    && apt-get install -y software-properties-common \
    && apt-get install -y \
                       --no-install-recommends \
                       git \
                       golang \
                       nodejs \
                       npm \
                       python \
                       python-setuptools \
                       python-pip \
                       unzip \
                       wget \
                       zip

RUN apt-get install -y gnupg ca-certificates \
    && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF \
    && echo "deb https://download.mono-project.com/repo/ubuntu stable-bionic main" > /etc/apt/sources.list.d/mono-official-stable.list \
    && apt-get update \
    && apt-get install -y \
                       mono-devel \
                       nuget

RUN apt-get clean

RUN pip install --no-cache-dir lit OutputCheck pyyaml

RUN npm install bignumber.js
