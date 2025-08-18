# Long Subtraction with Borrow with Jasmin & EasyCrypt

This directory features a verified implementation for x86_64 of subtraction with
borrow of 256-bit unsigned integers, represented as four 64-bit *limbs*. The
borrow is encoded in the least significant bit of an 8-bit machine word. It is structured as follows:

  - **main.jazz** Jasmin implementations; one operates in place, the other one
    writes into a fresh array
  - **LongSubEquiv.ec** EasyCrypt equivalence proof of the two implementations
  - **proof.ec** correctness proofs of both implementations; the out-of-place
    is proved directly, the correctness of the in-place version is showed by
    equivalence to the other version.
  - **README.md** this file
  - **easycrypt.config** configuration file for EasyCrypt
  - **justfile** utility file gathering the main commands to run for using these files

This is known to work with the latest released versions of Jasmin and EasyCrypt
at the time of writing, namely Jasmin 2025.06.1 and EasyCrypt 2025.08.
