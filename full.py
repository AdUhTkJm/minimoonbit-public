#!/bin/python3
import os;
import random;

files = os.listdir("test/test_src");
random.shuffle(files);

for x in files:
    name = x[:-4];
    if x[-4:] == ".ans" or name == "t":
        continue;
    
    os.system(f"./test.sh {name} > test.txt 2> /dev/null");

    result = open("test.txt");
    content = result.read().strip();
    result.close();
    
    truth = open("test/test_src/" + name + ".ans");
    content2 = truth.read().strip();
    truth.close();
    
    if content != content2:
        print(f"{name} failed");
        print(f"expected {content2}, got {content}")
    else:
        print(f"{name} passed");

    
os.remove("test.txt");