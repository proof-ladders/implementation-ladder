/*
   The subtraction of 256-bit integers, each represented by four 64-bit words.

   The operation takes two input 256-bit integers and one input borrow bit, and
   produces one output 256-bit integer, and one output borrow bit.

   In-place subtraction is supported, where the result overwrites the left
   operand.

   Command: frama-c-gui -wp -wp-rte -wp-prover z3 borrowing_sub.c

   Author: Nicky Mouha
*/

#include <stdint.h>

// Frama-C annotations are written in ACSL, where integers have an arbitrary
// precision.
/*@
  logic integer to_int(uint64_t *a) =
    a[3] * (1 << 192) +
    a[2] * (1 << 128) +
    a[1] * (1 <<  64) +
    a[0];
*/

// A subtraction defined on 64-bit words, with borrow input and output.
/*@
  requires \valid(sub); // Must be valid pointer.
  requires borrow == 0 || borrow == 1;
  assigns *sub;
  ensures *sub == \result * (1 << 64) + lhs - rhs - borrow;
  ensures \result == 0 || \result == 1;
*/
int borrowing_sub_u64(uint64_t *sub, uint64_t lhs, uint64_t rhs, int borrow) {
  *sub = (uint64_t)(lhs - rhs - borrow);
  return (lhs < rhs) || ((lhs == rhs) && borrow);
}

// A subtraction defined on 256-bit words, with borrow input and output.
/*@
  // Inputs and outputs must be valid pointers.
  requires \valid(&sub[0..3]) && \valid(&lhs[0..3]) && \valid(&rhs[0..3]);
  // Support for either no overlap, or in-place subtraction.
  requires \separated(&sub[0..3], &lhs[0..3], &rhs[0..3])
    || ((sub == lhs) && \separated(&sub[0..3], &rhs[0..3]));
  requires borrow0 == 0 || borrow0 == 1;
  assigns sub[0..3];
  // The "Pre" label refers to the values before the function starts.
  ensures to_int(sub) ==
    \result * (1 << 256) + to_int{Pre}(lhs) - to_int{Pre}(rhs) - borrow0;
  ensures \result == 0 || \result == 1;
*/
int borrowing_sub(uint64_t *sub, uint64_t *lhs, uint64_t *rhs, int borrow0) {
  int borrow1 = borrowing_sub_u64(&sub[0], lhs[0], rhs[0], borrow0);
  int borrow2 = borrowing_sub_u64(&sub[1], lhs[1], rhs[1], borrow1);
  int borrow3 = borrowing_sub_u64(&sub[2], lhs[2], rhs[2], borrow2);
  int borrow4 = borrowing_sub_u64(&sub[3], lhs[3], rhs[3], borrow3);
  return borrow4;
}
