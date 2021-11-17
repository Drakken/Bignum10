This is a toy module for arbitrary-precision integers, written entirely in OCaml.  
Its purpose is educational. The Zarith library is recommended for production code.

In this module, integer values are implemented as tuples containing a sign flag and a list of positive ints.  
Each int contains two smaller integers that are limited by a power of ten (10^4 for 32-bit ints).  
This format speeds up conversion to and from base-10 string representations but makes arithmetic slow.
