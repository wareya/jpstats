#!python
import sys

sys.stdout.reconfigure(encoding="utf-8", newline="\n")

mode = 0
text = ""

sentence_enders = "」。.！？⁉!?…―"

strip_left_next = False

for line in open(sys.argv[1], encoding="utf-8"):
    line = line.rstrip("\n")
    line = line.rstrip("　")
    if line == "":
        if text != "":
            print(text)
        text = ""
        print("")
        mode = 0
        if strip_left_next:
            strip_left_next = False
            print("")
        continue
    if strip_left_next:
        line = line.lstrip("　")
    if mode == 0:
        if line.startswith("「") and strip_left_next:
            strip_left_next = False
            print("")
        if line.startswith("「") and line[-1] not in sentence_enders and line.count("「") != line.count("」"):
            mode = 1
            text = "" + line
        else:
            if line.endswith("、"):
                print(line, end="")
                strip_left_next = True
                continue
            else:
                print(line)
    elif mode == 1:
        text = text + line.strip("　")
        if text[-1] in sentence_enders:
            print(text)
            text = ""
            mode = 0
    strip_left_next = False
