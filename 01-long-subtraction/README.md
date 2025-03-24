# Long subtraction

## Description

As part of an unspecified cryptographic algorithm, you are representing long integers using four
machine words. These are are passed by address. We set out to implement a subtraction operation for
these long integers. This requires consuming and returning a *borrow* bit, which is analogous to the
carry bit for addition.

The subtraction operation thus takes two input long integers and one input borrow bit, and produces
ont output long integer, and one output borrow bit. Both the input and output long integers are
passed by address; borrow bits are passed directly and the output borrow bit is the return value of
the function.

## Verification Goals

- Specify how the data structures in memory map to mathematical integers.
- Capture the behavior of the subtraction function, relating its three inputs to its two outputs
  using operations over mathematical integers.
- The intended use-case, if possible, is to support in-place subtraction where the one input long
  integers and the result may alias each other.
