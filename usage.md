# Setting up a workspace

1) install rust and cargo with rustup: https://rustup.rs/
2) clone or download the jpstats repository to a folder called "jpstats", so that the path "jpstats/src" exists, and NOT so that the path "jpstats/jpstats/src" exists

# Setting up unidic

3) download a copy of unidic: https://unidic.ninjal.ac.jp/
 * if your version of unidic is not ***EXACTLY*** unidic-csj-2.3.0.zip, you ***MUST*** delete the "jpstats/workspace/common_edges_right.txt" and "jpstats/workspace/common_edges_left.txt" files. ***PERIOD.***
4) there are two versions of unidic: written language and spoken language. I feel like spoken language tends to give slightly better results, even on literature
5) extract "matrix.bin", "sys.dic", "char.bin", "unk.dic", "rewrite.def", "right-id.def", and "left-id.def" to "jpstats/data"

# Setting up your texts

6) dump text files into "jpstats/workspace/scripts"
7) edit "jpstast/workspace/config/allowed_test_failures.txt" so that it contains the single line "all" (unless you're working with VN scripts, in which case don't touch it)

# Running it

8) navigate to the jpstats directory with a terminal emulator like cmd.exe or msys2
7) run "cargo run --release update_everything". this may take a while, because the entire application and all of its dependencies have to get compiled from scratch.

This produces a few different useful files in "jpstats/workspace", including a frequency list and a table of stats.
