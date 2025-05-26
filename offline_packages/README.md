This directory holds Debian package files (`.deb`) used when running
`./setup.sh --offline`.  Collect the packages on a machine with network
access and copy them here before invoking the setup script.

Steps to gather the packages:

1. On an Ubuntu 24.04 system run `sudo apt-get update`.
2. For each package listed below run
   `apt-cache policy <package>` to determine the exact version
   that `setup.sh` will install.
3. Download that version with `apt-get download <package>=<version>`.
4. Verify each file with `dpkg-deb -f <package>.deb Version` and ensure the
   version matches what you recorded from step&nbsp;2.
5. Copy all downloaded `.deb` files into this directory.

`setup.sh` uses `apt-cache` to determine package versions when it runs.
If the versions here do not match those it expects, installation will fail
in offline mode, so double-check each file.

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
