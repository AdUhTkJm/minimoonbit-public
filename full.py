#!/bin/python3
import os;

files = os.listdir("test/test_src");
unpass = [];
passed = [];

for x in files:
    name = x[:-4];
    if x[-4:] == ".ans":
        continue;
    
    status = os.system(f"./test.sh {name} > test.txt");
    if status < 0:
        print(f"compiler failed on {name}, cannot continue");
        exit(1);
    
    result = open("test.txt");
    content = result.read();
    result.close();
    
    truth = open(name + ".ans");
    content2 = truth.read();
    truth.close();
    
    if content != content2:
        unpass.append((name, result, truth));
    else:
        passed.append((name, result, truth));
        
print(f"Passed: {len(passed)}; Failed: {len(unpass)}");

for x in unpass:
    print(f"{name}:");
    print(f"got      {result}");
    print(f"expected {truth}");
    print("\n");
    
os.remove("test.txt");