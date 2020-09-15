import sys

if not len(sys.argv) == 4:
    print("ERROR; Usage: python math_helper.py op number1 number2")
    exit(1)

print(hex(eval(sys.argv[1] + sys.argv[2] + sys.argv[3])))
