rm t.wat
moon run src/bin/main.mbt test/test_src/$1.mbt -- --wasm -o t.wat
wat2wasm t.wat -o t.wasm
if [ $? -ne 0 ]; then
    exit 1
fi
echo "Build finish"
node wasm_rt/runtime.mjs t.wasm