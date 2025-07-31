Build Flags
===========

The build system targets modern C23 features and enables several optimization
flags for all C sources. A representative invocation uses ``clang`` with::

   clang -std=c2x -O3 -march=native -ffast-math -fstrict-aliasing \
         -fomit-frame-pointer -funroll-loops -pipe -flto

These options tune for aggressive optimization while still remaining
portable across modern architectures. The ``setup.sh`` script verifies the
compiler understands ``-std=c2x`` before any compilation steps occur.
