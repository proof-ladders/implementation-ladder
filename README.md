# Intro

This repository contains a set of examples that allow comparing different crypto implementation
verification tools. The goal is to be able to show, by example, the styles and tradeoffs adopted by
many tools. We aim to cover a wide range of areas, ranging from mathematics to formats and long-lived
state and complex APIs.

This repository is concerned with the question of implementation correctness, that is, showing that
an implementation behaves according to its specification. Other repositories under the same
organization tackle the question of protocol security, or cryptographic security of primitives and
constructions.

This project originated at HACS 2025.

We are happy to take pull requests!

# Audience

If you are verification-curious, this repository will help you understand the differences between
tools in concrete terms, rather than from a theoretical perspective, and doing so, pick a tool that
best suits your needs.

If you are a tool developer, you can contribute to this sample set by either adding more examples,
or providing reference solutions in your tool of choice for existing problems. If you add a new
problem, please follow the template (e.g. the first problem). If you add a new solution, make sure
you update this README.

# Tools covered

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
- Gobra is an automated, modular verifier for Go programs, based on the Viper verification
  infrastructure. [Website](https://www.pm.inf.ethz.ch/research/gobra.html)

Without looking at examples, the tools above can already be differentiated along a few axes.
- consuming or producing code:
  - code-producing tools *generate* executable output: Low\* and Bedrock2 both *produce* C code from
    F\* and Coq, respectively
  - code-consuming tools *take actual code* as an input: Hax and Aeneas both consume Rust code, while
    Gobra consumes Go code
- interactive vs automated:
  - some tools emphasize automation: Hax and Low\* with F\* (and Z3 under the hood), Gobra with Viper
  - some tools emphasize interactivity: Aeneas with Lean, Bedrock2 with Coq
- among the code-consuming tools:
  - intrinsic tools like Hax or Gobra favor an annotated source where the programmer conducts the
    proof by adding pre- and post-conditions, intermediary assertions, and calls to lemmas
  - extrinsic tools like Aeneas advocate for a clean separation between the pristine,
    developer-authored source, and the proof, which lives separately

Finally, an imperfect way to contrast the tools is to look at the projects that have been conducted
with these tools. This ought to be taken with a grain of salt: a large-scale project
attests to the expressive power of the underlying tool, but also reflects the size of the underlying
team.
- Low\* was used to author HACL\*, a verified cryptographic library that combines 80,000 lines of C
  code with 10,000 lines of assembly, used in Python, Firefox, Linux
- Hax was used to author a verified implementation of ML-KEM soon to be integrated in BoringSSL
- Bedrock2 was used to author a library of verified elliptic curves that have been integrated in
  BoringSSL

# Arithmetic problems

## Problem 1: Long Subtraction

subfolder: [01-long-subtraction](01-long-subtraction/)

| Tool      | Proof Status      | Limitations        | Difficulty Rating |
| --------- | ----------------- | -----------------  | ----------------- |
| Bedrock2  | ✅                |                    |                   |
| Low\*     | spec only         |                    |                   |
| Hax       | impl only         | no aliasing (Rust) |                   |

Commentary: Rust does not permit the equal-or-disjoint aliasing pattern.
