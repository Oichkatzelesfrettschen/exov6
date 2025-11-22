# Standards Reference Documentation

This directory contains reference materials for the standards compliance in this project.

## POSIX-2024 (SUSv5) - Single UNIX Specification Version 5

- **susv5.zip**: Complete SUSv5 archive
- **susv5-html/**: HTML version of the complete POSIX-2024 specification
- **Standard**: IEEE Std 1003.1-2024 / The Open Group Base Specifications, Issue 8
- **Publication**: June 2024
- **Compliance Level**: ISO C17 with strict POSIX-2024 (SUSv5); use `_POSIX_C_SOURCE=200809L` and `_XOPEN_SOURCE=700` for strict headers

## C17 Standard (ISO/IEC 9899:2018)

- **c17_n2176_draft.pdf**: C17 draft standard (N2176, November 2017)
- **Standard**: ISO/IEC 9899:2018 (formally known as C17/C18)
- **Features**: C17 fixes defects in C11 without introducing new language features

## Project Configuration

All build systems are configured for:
- C17 language standard (`-std=c17`)
- POSIX-2024 compliance (`-D_POSIX_C_SOURCE=200809L -D_XOPEN_SOURCE=700`)
- See meson.build, CMakeLists.txt, and Makefile for implementation details

## Usage

Reference these materials when implementing POSIX-compliant system interfaces in the libos layer and ensuring kernel API compatibility with standard specifications.
