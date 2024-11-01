#!/bin/bash

zig build-exe -target riscv64-linux -femit-bin=t.exe t.s riscv_rt/zig-out/lib/libmincaml.a -O Debug -fno-strip -mcpu=baseline_rv64
