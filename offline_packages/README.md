This directory holds Debian package files (.deb) for offline installation.
Place each required package listed below in this directory before running
`./setup.sh --offline`. Obtain packages with `apt-get download <package>=<version>`
on a machine with network access.

Example package versions tested on Ubuntu 24.04:

- build-essential 12.10ubuntu1
- gcc 4:13.2.0-7ubuntu1
- g++ 4:13.2.0-7ubuntu1
- cmake 3.28.3-1build7
- ninja-build 1.11.1-2
- python3 3.12.3-0ubuntu2
- python3-pip 23.0.1+dfsg-3ubuntu2
- qemu-system-x86 1:8.2.0+ds-1
- qemu-user-static 1:8.2.0+ds-1

Add any additional packages required by `setup.sh` with matching versions.
