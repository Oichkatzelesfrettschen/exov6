#!/usr/bin/env bash
set -e
schema=$1
base=$(basename "$schema" .capnp)
dir=$(dirname "$schema")
hfile="$dir/$base.capnp.h"
cfile="$dir/$base.capnp.c"
struct=$(grep -Eo 'struct [A-Za-z_][A-Za-z0-9_]+' "$schema" | head -n1 | awk '{print $2}')
field=$(grep -Eo '[A-Za-z_][A-Za-z0-9_]* @0' "$schema" | head -n1 | awk '{print $1}')
cat > "$hfile" <<EOFH
#pragma once
#include <stdint.h>
#include "types.h"

typedef struct {
    int32_t $field;
} $struct;

size_t ${struct}_encode(const $struct *msg, unsigned char *buf);
size_t ${struct}_decode($struct *msg, const unsigned char *buf);
#define ${struct}_MESSAGE_SIZE sizeof($struct)
EOFH

cat > "$cfile" <<EOFC
#include "$(basename "$hfile")"
size_t ${struct}_encode(const $struct *msg, unsigned char *buf){
    const unsigned char *src = (const unsigned char *)msg;
    for(size_t i=0;i<sizeof(*msg);i++)
        buf[i] = src[i];
    return sizeof(*msg);
}
size_t ${struct}_decode($struct *msg, const unsigned char *buf){
    unsigned char *dst = (unsigned char *)msg;
    for(size_t i=0;i<sizeof(*msg);i++)
        dst[i] = buf[i];
    return sizeof(*msg);
}
EOFC

exit 0
