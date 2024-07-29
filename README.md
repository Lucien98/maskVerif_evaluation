# Evaluations for maskVerif
This repository includes the source code for maskVerif, along with its benchmarks and verification results.

We have adjusted the maskVerif source code to output only leakage lines, omitting the reduced expressions.

Benchmarks can be found in the `mv` folder, while verification results are stored in the `experiments` folder. These results are referenced in the following paper.

## Publication
F. Zhou, H. Chen, L. Fan (2024): [Prover - Toward More Efficient Formal Verification of Masking in Probing Model](https://eprint.iacr.org/2024/1202.pdf)


Here down below is the original README of maskVerif

---

To compile the tool, the best way is to use nix

Start doing

> nix-shell
> make 

Then you can start using it iteractively by doing 
./maskverif 
or by passing a .mv file
./maskverif < tutorial.mv

A small tutorial is provide in tutorial.mv

