#!/bin/bash

rm t.s t.exe
moon run src/bin/main.mbt test/test_src/$1.mbt -- -o t.s
if [ $? -ne 0 ]; then
    exit 1
fi
zig build-exe -target riscv64-linux -femit-bin=t.exe t.s riscv_rt/zig-out/lib/libmincaml.a -O Debug -fno-strip -mcpu=baseline_rv64
echo "Build finish"
libriscv/emulator/rvlinux -n t.exe