This is a simple OCaml module for arbitrary-precision integers.  
Integer values are implemented as tuples containing a sign flag and a list of positive ints.  
Each int contains two smaller integers that are limited by a power of 10 (10^4 for 32-bit ints).  
This format speeds up conversion to and from base-10 string representations.
