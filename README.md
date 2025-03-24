# The crypto implementation verification survey

This project originated at HACS 2025 -- our goal is to compare and contrast different verification
tools, using a curated selection of sample verification problems.

We are strictly concerned with the question of implementation correctness, that is, showing that an
implementation behaves according to its specification.

The sample problems aim to cover a wide range of areas, ranging from mathematics, to formats and
long-lived state and complex APIs.

We are happy to take pull requests!

## Audience

This repository is for vefification-curious folks who want to understand the differences between
tools in concrete terms, rather than from a theoretical perspective.

Tool developers can use this sample set to showcase their approaches, and are welcome to contribute
more solutions and/or problems.

## Tools covered

The tools we showcase in this repository are:
- Low\*, a subset of F\* that compiles down to C. Programs written in Low\* "look" like C, and
  reason about stack and heap-allocated objects.
  [Tutorial](https://fstarlang.github.io/lowstar/html/index.html)
- Bedrock2 is a low-level C-like language formalized in Rocq. Programs written in Bedrock2 compile
  directly to machine code, or more commonly, to actual C. Bedrock2 represents the perspective of C
  as a portable assembly language, meaning memory contains bytes and functions take machine words as
  arguments. Representation of data is modeled using a separation logic.
  [Website](https://github.com/mit-plv/bedrock2),
  [Reference](http://adam.chlipala.net/theses/andreser.pdf)
- Hax is a tool that can verify a subset of Rust by extraction to a proof assistant. Rust programs
  are annotated with refinements, pre- and post-conditions, loop invariants, and more. The output of
  the translation is a pure program that does not mention memory at all. The main backend is F\*.
  [Website](https://hax.cryspen.com)
- Aeneas verifies a subset of Rust by extraction to a proof assistant. Rust programs are exactly as
  written the programmer, and devoid of any annotations or extra syntax. The output of the
  translation is a pure program that does not mention memory at all. The main backend is Lean.
  [Website](https://aeneasverif.github.io).

# TODO

- Having a template to add a new problem
- Table of problems here in the README along with difficulty level, scope, limitations
- Determine evaluation matrix for each problem
- Have each problem come with commentary
- Say something about PRs and what we want to see to accept a new problem or solution
- Email Charlie to cross-reference repositories
