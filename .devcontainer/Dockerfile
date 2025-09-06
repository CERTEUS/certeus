FROM mcr.microsoft.com/devcontainers/python:3.11-bookworm

# Install additional OS packages
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
    git-lfs \
    && apt-get clean -y && rm -rf /var/lib/apt/lists/*

# Set up git-lfs
RUN git lfs install

# [Optional] If your pip requirements rarely change, uncomment this section to add them to the image
# COPY requirements.txt /tmp/pip-tmp/
# RUN pip3 --disable-pip-version-check --no-cache-dir install -r /tmp/pip-tmp/requirements.txt \
#    && rm -rf /tmp/pip-tmp
