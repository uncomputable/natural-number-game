# Natural Number Game Solutions in Coq

Reimplementation of the [Natural Number Game](https://github.com/ImperialCollegeLondon/natural_number_game),
written in [Lean](https://leanprover.github.io/) by Imperial College London,
in [Coq](https://coq.inria.fr/).
It turns out that Lean and Coq are very similar and many proofs can be translated 1-by-1.
There seem to be differences when writing complex proofs, but we will not encounter those here :)

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
