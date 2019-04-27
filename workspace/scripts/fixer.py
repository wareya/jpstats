#!python
import sys

sys.stdout.reconfigure(encoding="utf-8", newline="\n")

mode = 0
text = ""

for line in open(sys.argv[1], encoding="utf-8"):
    line = line.rstrip("\n")
    if line == "":
        if text != "":
            print(text)
        text = ""
        print("")
        mode = 0
        continue
    if mode == 0:
        if line.startswith("「"):
            mode = 1
            text = "" + line
        else:
            mode = 2
            print(line)
    elif mode == 1:
        text = text + line.lstrip("　")
    elif mode == 2:
        print(line)