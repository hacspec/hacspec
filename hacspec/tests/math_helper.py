import sys

if not len(sys.argv) == 4:
    print("ERROR; Usage: python math_helper.py op number1 number2")
    print("              op can be: add, mul, pow, mod")
    exit(1)

if sys.argv[1] == "add":
    print(hex(int(sys.argv[2], 16) + int(sys.argv[3], 16)))
elif sys.argv[1] == "mul":
    print(hex(int(sys.argv[2], 16) * int(sys.argv[3], 16)))
elif sys.argv[1] == "pow":
    print(hex(int(sys.argv[2], 16) ** int(sys.argv[3], 16)))
elif sys.argv[1] == "mod":
    print(hex(int(sys.argv[2], 16) % int(sys.argv[3], 16)))
