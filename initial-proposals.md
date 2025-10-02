---
title: "Sample Problems for Cryptographic Implementation Verification"
author: Collected by Andres Erbsen
date: Discussed at HACS 2025
geometry: "left=3cm,right=3cm,top=2cm,bottom=2cm"
---

## Premise and Suggestions

This document provides a sampling of small sub-problems relevant to formally verified cryptographic implementations.
The idea is that solving these would be nice way to explore how different methodologies and tools apply to each problem, and to understand how experts use certain techniques at a manageable scale.
Each problem is presented in an isolated form, with integration considerations intentionally removed.
These idealizations are inevitably opinionated, and highlight one aspect of the problem while eliding the rest.

It is understood that isolated verification is only one step towards integrated verification, and some tools are quite reasonably designed to work between different boundaries than the ones presented here.
Thus one attempting these problems is invited to cast each one in the framework of the tool being exercised, while preserving the central challenges.
In particular, while each problem is presented in a maximally abstracted form to hide unnecessary detail, filling in that detail when it simplifies reasoning is welcome.
However, it would also be helpful to explain which specializations are load-bearing for successful verification with the given approach.

The hope is that solutions would focus on giving a taste of the developer experience in various approaches and tools, and helping potential users understand key considerations.
The intent is *not* to run a competition, even in jest -- we seek a to gather shared understanding, not a ranking.
Solving the same problem with the same tool and libraries but with a different problem-solving approach is encouraged.

Illustrative solutions are preferred to clever and beautiful ones.
It'd be great to see each verification task in the shape it was right after getting it to work, without further polishing or code golf.
Automation is encouraged, but magical solutions are not.
Please consider a non-expert reader's ability to generalize when picking the level of detail to show.

Successful solutions are encouraged to be accompanied with curated stuck attempts based on a similar approach.
As the vast majority of verification-engineering time is spent troubleshooting unsuccessful verification queries, it seems good to highlight the error feedback and debubugging facilities of each tool and approach.
Even if a solution goes through at the first try, it may be helpful to come up with implementation, specification, and proof flaws that a new user might encounter, illustrate how they appear, and describe how to interpret the feedback or debugging information.
If a specific technique works well for troubleshooting, describing it along with the solution is very welcome.

## Status

This set of problems is preliminary, somewhere between a shortlist ideas and a "beta" request for solutions.
Input on scope, approach, and presentation is very welcome.

\pagebreak

# Sequence 1: Representations and Arithmetic 

This sequence of problems is intended to exercise reasoning involving machine words, memory, and representation relations.
The conceptual content of the problems is intentionally straightforward (just subtraction!) to emphasize the technical aspects.

## Exercise 1: Long Subtraction

**a)** Specify, implement, and prove and full subtraction of 256-bit numbers using four 64-bit machine words as the underlying representation.
The implementation should accept a borrow bit as input, and produce one as output.
The implementation must have well-defined (and proven) behavior on all 4-word inputs, even in case of underflow of the represented value.

This problem is posed with the presumption that a specification designed around a central polynomial equation between the inputs and outputs is desirable.
Alternative specifications are welcome, but please comment on the choice if you create one.

**b)** Prove that the output is uniquely determined by the input (this may be implicit already or easily derived; make it explicit).

## Exercise 2: Cryptographic Constant Time

**a)** Prove that inherently execution-time-influencing intermediates (memory-accesses addresses, branch conditions, etc) are independent of the value of the inputs.

**b)** Construct a 512-bit carry-select subtracter and prove that its leakage is similarly innocuous. Specifically, perform 3 calls to the 256-bit adder: once at position 0 to determine a borrow bit at the 256th position, and twice at position 256 with guesses 0 and 1 for that borrow bit; then use the position-256 borrow bit to select between the outputs of the high half.
Prove that it subtracts correctly, using a specification in the same style as for the original adder.

**c)** Prove that the carry-select subtracter does not leak the value of the inputs through timing.
If you haven't already, implement constant-time conditional select for 256-bit numbers.

See the rightmost figure at <https://en.wikipedia.org/wiki/Carry-select_adder#Uniform-sized_adder>.

## Exercise 3: Read-Before-Write Aliasing

**a)** Extend your implementation and proof to support the following additional use cases:

	x, c := sub256(x, y, c) 	y, c := sub256(x, y, c)
	x, c := sub256(x, x, c) 	y, c := sub256(x, x, c)

The intent of this subproblem is to exercise reasoning about multiple references to the same memory, illustrating techniques that would scale to inputs larger than a few words.
In particular, solutions that copy the entire input upon function call merely sidestep the challenge.
(They can be demonstrated anyway)

**b)** Juggling eggs: \hfill `	(x, _), (y, _) := sub256(x, y, 0), sub256(y, x, 0)` \hfill\null\hfill\null

The is expected require a copy, but that's besides the point.
The intent is to exercise tooling support for the same specification variable having a different value during different points throughout execution, and relating them to each other.
Demonstrate how to troubleshoot proof attempts for a broken implementation that overwrites one input prematurely.

## Exercise 4: Scalar Clamping (a la Curve25519)

Specify a function that takes 256 bits as input, and produces a number of the form $8x$ for $2^{251} \le x < 2^{252}$ based on the input.
Implement this function using bitwise operations (potentially in place), and prove that it satisfies the specification.
It will likely be straightforward to give (but factor out) a specific definition for x.

\pagebreak

# Sequence 2: Remainder Arithmetic

This sequence of problems is intended to exercise use of number-theoretic lemmas in program verification.

## Exercise 1: RSA-CRT Basic Operation

The specification is simple: exponentiation modulo a semiprime N=pq.
It's fine to work with toy-sized moduli for this problem (e.g., 32 bits).
Feel free to axiomatize an implementation of modular exponentiation, as well as appropriate theory about modular arithmetic.
However, it would defeat the purpose to choose the formulation of this theory to suit this problem in particular; instead consider the standard math library for the proof tool at hand or one for another proof tool for inspiration.
It is also fine to require a CRT-related precomputed values as a part of the input, again specified in separately defensible ways, such as how they could be computed or validated, not in terms of a hypothetical CRT instance.

The implementation should (separately) perform exponentiation modulo the two factors, with appropriately reduced exponents.
The results modulo p and modulo q should then be combined to a single result, matching the specification stated without referencing the individual factors.

Implementation inspiration: [go/crypto/internal/fips140/rsa/rsa.go:DecryptWithoutCheck](https://cs.opensource.google/go/go/+/master:src/crypto/internal/fips140/rsa/rsa.go;drc=c7ea87132f4e6f3c81e525c396a64471c9af0091;l=416?q=DecryptWithoutCheck&ss=go%2Fgo)

## Exercise 2: "Redundant" Checks

**a)** Implement unpadded RSA decryption using the previous function.
Have the implementation encrypt the decrypted value and check that it matches the input.
Prove that this check is redundant given a valid secret key.

**b)** And then find a way to enforce this check in the function specification anyway.
(One option is to axiomatize an external call, and pass the decrypted plaintext through it. Treating that external call as unspecified, the check is not redundant, but in case the external call behaves like an identity function, original behavior should be restored.)

## Exercise 3: Simple Recursive NTT

**a)** Specify, implement, and prove a function that takes as argument a polynomial in $F_q[x]/(x^{2^n}-1)$ and returns its values at powers of the $2^n$-th root of unity (in some specified order).
Specifically, the function should operate recursively by reducing the input polynomial modulo two polynomials of the form $x^{2^n/2}-b$ for some coefficient $b$, and then multi-evaluate those polynomials recursively.
The specification of the function should explain how to find the evaluation of the input polynomial on the i-th power of the root of unity in the output list, and the proof should justify that the value is correct.

It is explicitly *not* a requirement for this exercise to connect the final list of valuations to the bit-reverse ordering, or to the slow Fourier transform; while solutions that do so are absolutely valid, they may be challenging to construct.
It is permissible to elide or axiomatize general theory of polynomials, including properties, and to automatize the existence of a root of unity and existence and uniqueness for the polynomial CRT. Again, consider referencing the mathematics library of any formal-verification tool.

**b)** Prove that the body of the recursive function can be implemented using one or two loops of simple operations (the NTT butterflies), only referencing polynomials in the specification but not the implementation.

**c)** Specify polynomial multiplication, and prove against that specification an implementation that uses NTT, pointwise multipication, and inverse NTT (axiomatized in a style closely mirroring NTT).

## Exercise 4: Partial Recursive NTT

This is a challenge version of the previous exercise. **a)** Instead of assuming a $2^n$-th root of unity, assume a $2^{n-r}$-th root of unity, and have the function return a list of residues modulo polynomials $x^{2^r}-b$. **b)** Butterflies as recursive-function body **c)** NTT-based polynomial multiplication

\pagebreak

# Sequence 3: Constructed Objects (Elliptic-Curve Operations)

These exercises consider construction and implementation of elliptic curves based on arithmetic on coordinates in the underlying field.
Following [Montgomery curves and their arithmetic (ia.cr/2017/212)](https://eprint.iacr.org/2017/212.pdf) section 4 for exercises 1-3.

## Exercise 1: Montgomery-Ladder Step

Prove that the Montgomery-ladder step produces the sum and doubling of the inputs under appropriate assumptions about the difference of the input points.
The implementation should use x/z coordinates (x-only format with deferred division) while the specification should use affine (x, y) coordinates and appropriate representation relations.
It is fine to use or not use structured data representation in the implementation (passing just 5 field elements in and 4 out is expected to work OK).
This exercise is intended to demonstrate basic computer-algebra reasoning combined with basic casework.
Note that while the interpretation of the ladder step can be extended to x=0 as input, the x/z=0/0 does not represent any point.
TODO: can an invalid combination of input values may produce invalid output representation?

## Exercise 2: Montgomery Ladder

Prove that a loop that repeatedly applies the ladder step and conditionally swaps the two points of state implements scalar multiplication.
Scalar multiplication should be specified as unary repetition of point addition in affine coordinates; basic properties of it should be easy to prove but can also be axiomatized.

## Exercise 3: y-Coordinate Reconstruction

Given an affine point and the two x/z pairs produced by the Montgomery ladder, implement and prove reconstruction of the affine representation of the scalar-multiplication result.
A good solution would include a self-contained specification of the reconstruction function, taking care to appropriately reference elliptic-curve points or field elements in their construction.

---

The following additional exercises consider relationship between group structure of the elliptic curve and equations on its coordinates.

## Exercise 4: Exceptional Points for Unified Weierstrass Addition

The paper "[Complete addition formulas for prime order elliptic curves" (ia.cr/2015/1060)](https://eprint.iacr.org/2015/1060.pdf)
presents an optimized addition law for points $P$ and $Q$ whose difference $P-Q$ has a nonzero $y$ coordinate.
Prove that all points on an odd-order curve satisfy this condition.
(Verifying that the formula itself matches affine addition would be a different exercise, also welcome.)

## Exercise 5: Order of Curve25519

Prove the number of points on Curve25519.
Starting from a characterization of the points as solutions to a quadratic equation, and concrete examples of points of order 2, 4, 8, and $l$, use group-theory lemmas to argue that the order of the curve must be exactly $8l$.
Use this fact to prove that adding a multiple of $8l$ to a scalar before scalar multiplication does not affect the result.

\pagebreak

# Sequence 4: Nonlinear Integer Arithmetic

# Exercise 1: Saturated Pseudo-Mersenne Reduction

Consider a saturated representation of numbers modulo a value close to a power of two.
Call the power of two $s$ and the difference between the modulus and the power of two $c$ (so $s$ is congruent to $c$).
A common step for moduler reduction is to replace $a+sb$ with $a+cb$, but even $a,b<s$ does not guarantee $a+cb<s$, so additional reduction is required.

Given an appropriately small $b$, repeating the same reduction for a second time converges without even needing to propagate the carry through the entire $s$-bit number.
(From now on $a$ and $b$ refer to the inputs of the second reduction.)
Specifically, for a power of two $W$, we can show that only the low part (mod $W$) is affected by carry propagation under rather flexible conditions about $c$, $W$, and $|b|$.

The following formalization is excerpted from a proven development; it is general and concise but not all that elegant.
The key idea is that for computing the numerator of the final RHS, after computing the mod-$W$ part, the $/W$ part can be reused from the intermediate expression that is the LHS.

### Candidate Formalization

```
forall s c W a b,
(b < 0 -> s / W * W = s) ->
0 <= c < W ->
W <= s ->
0 <= a < s ->
0 <= c*Z.abs b <= W-c ->
((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W.
```

<!-- Based on this formula, and fast implementations of A+=c*B for bignums A, B, fast implementations of modular reduction can be proven. -->

## Exercise 2: Expedited Barrett Reduction

Depending on the modulus, Barrett reduction after multiplication may require one or two conditional subtractions to preduce a canonical result.
Barrett reduction computes an approximation of $a/m$ and subtracts that many times $m$ from $a$ to approximate $a \bmod m$.
Using $(k+1)$-limb approximations of $1/m$ and $a$ gives an intermediate result within $[0, 3m)$.
Further assuming that the former approximation $\mu \le W * (W^k - (W^{2k} \bmod m))$ and that $\lfloor a/m \rfloor$ fits in $k$ limbs, the intermediate result is within $[0, 2m)$.

### Candidate Formalization


```
Context 
  (a m : Z) (m_pos : 0 < m) (* computing a mod m *)
  (W : Z) (W_pos : 0 < W) (* e.g. W = 2^64, k smallest s.t. *)
  (k : Z) (k_sufficient : m < W ^ k) (k_ge_1 : 1 <= k).
Let mu := W^(2*k) / m. (* approximate reciprocal *)
Let q := (mu * (a / W^(k-1))) / W^(k+1). (* approximate division *)
Let r := a - q * m. (* approximate modulo *)
Theorem barrett_reduction_mod : r mod m = a mod m.
Theorem barrett_reduction_2red : a < W^(2*k) ->
  a mod m = let r := if r <? m then r else r-m in
            let r := if r <? m then r else r-m in r.
Theorem barrett_reduction_1red : a < m * W ^ k ->
  W * (W^(2*k) mod m) <= W^(k+1) - mu ->
  a mod m = if r <? m then r else r-m.
```

### More Background

<https://en.wikipedia.org/wiki/Barrett_reduction>

[Handbook of Applied Cryptography, section 14.3.3](https://theswissbay.ch/pdf/Gentoomen%20Library/Cryptography/Handbook%20of%20Applied%20Cryptography%20-%20Alfred%20J.%20Menezes.pdf)

\pagebreak

# Sequence 5: Scaling Up

These problems focus on scenarios where the size of the program is a challenge in itself, independently from the conceptual complexity of the optimizations it uses.

# Exercise 1: Inlined ChaCha20

Take an implementation of chacha20, and inline (or use syntactic macros for) the 4-word quarter-round mixing function.
Show that the 10-iteration loop that applies 8 calls to the quarter round is equivalent to a specification without such inlining (which may be expressed directly as a pure function).

# Exercise 2: Repeated Modular Addition

Given an expression containing addition, modulo, and sharing, remove redundant modulo operations while preserving sharing (and prove equivalence).

Example input:

```
let y := x + x mod m in
let y := (y + y) mod m in
let y := (y + y) mod m in
...
y
```

The qualitative result of the experiment should be an asymptotic complexity: how does the time taken by this verification task scale as a function of the number of operations and shared intermediates. Answers observed so far for different techniques include quasi-linear, quadratic, cubic, exponential, and doubly exponential time.

# Exercise 3: Pragmatically Unified Addition for Weierstrass Curves with a=0

The libsecp256k1 implementation of mixed addition for elliptic-curve points in Jacobian representation includes a casework-heavy constant-time addition formula.
Proving that this formula produces a result that represents the affine sum of the Jacobian interpretations of the input points is "just" a task of computer algebra and casework, but naive approaches can easily make the verification impractically slow.

Reference: [secp256k1 src/group_impl.h:secp256k1_gej_add_ge](https://github.com/bitcoin-core/secp256k1/blob/master/src/group_impl.h#L724)

# Exercise 4: 4x/8x SHA3 for ML-KEM

Optimized ML-KEM implementations include parallel calls to SHA3-family hash functions. 
Prove that optimized, parallel computation is equivalent to combining the results of 4 independent calls to a reference implementation of the hash function.
It is acceptable (and probably desirable) to include a fragment of the code using the hash-function outputs in the verification, but for that the same code may be used both in the specification and the implementation.

# Exercise 5: Decoding and Decompressing ML-KEM Ciphertexts

Specify the wire format of ML-KEM ciphertexts as well as a suitable in-memory representation.
Implement and prove decoding of the former to the latter.
The specification, implementation, and proof should cover all error handling.
See [FIPS-203](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.203.pdf) Algorithm 15, steps before any NTT.
