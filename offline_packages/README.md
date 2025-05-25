# Offline Packages

This directory can be populated with `.deb` packages required by `setup.sh`.
If the script detects that no network connection is available it will attempt
to install matching packages from this directory using `dpkg -i`. The
package file names should follow the usual `name_version_arch.deb`
convention so the script can locate them.
Place the pre-downloaded Debian packages here before running `setup.sh`
offline.

