# Natural Number Game Solutions in Coq

Reimplementation of the [Natural Number Game](https://github.com/ImperialCollegeLondon/natural_number_game),
written in [Lean](https://leanprover.github.io/) by Imperial College London,
in [Coq](https://coq.inria.fr/).
It turns out that Lean and Coq are very similar and many proofs can be translated 1:1.
There seem to be differences when writing complex proofs, but we will not encounter those here :)

The files were translated into Coq more or less 1:1.
All the credit goes to Imperial College London for creating such an amazing game.
Play their game [here](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

## Dependencies

- coq 8.12 or higher
- coqide (optional)

```
apt update
apt install coq coqide
```

## Building

```
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakeFile
```

## Running

- Open CoqIDE
- File/Open
- Select any file in `Game/World/`
- Use arrows in top left to move through file
- Delete proofs and write your own
