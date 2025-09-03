Build Flags
===========

The build system targets ISO C17 with strict POSIX-2024 (SUSv5) conformance and enables several optimization
flags for all C sources. A representative invocation uses ``clang`` with::

   clang -std=c17 -O3 -march=native -ffast-math -fstrict-aliasing \
         -fomit-frame-pointer -funroll-loops -pipe -flto

These options tune for aggressive optimization while still remaining
portable across modern architectures. The ``setup.sh`` script verifies the
compiler understands ``-std=c17`` before any compilation steps occur.
