# Games

This directory contains standalone userland examples. The classic
terminal games here can be compiled separately from the exokernel
environment for quick testing.

## wumpus

An implementation of the vintage *Hunt the Wumpus* game. Build with:

```sh
cc -O2 wumpus.c -o wumpus
```

Run `./wumpus` to play.
