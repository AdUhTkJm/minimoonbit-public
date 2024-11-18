#!/bin/python3
import os;

files = os.listdir("test/test_src");

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
    
    truth = open("test/test_src/" + name + ".ans");
    content2 = truth.read();
    truth.close();
    
    if content != content2:
        print(f"{name} failed");
    else:
        print(f"{name} passed");

    
os.remove("test.txt");