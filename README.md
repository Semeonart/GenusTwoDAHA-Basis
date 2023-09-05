# GenusTwoDAHA-Basis
This project contains supplementary materials for paper ArXiv:

-----------Scripts for SINGULAR, ".singular" files-----------

The following scripts must be executed in Computer Algebra software SINGULAR https://www.singular.uni-kl.de/

1. RadicalT2-v4.singular
   This scripts performs the computation of a radical of defining ideal of A_{q=t=1} which is used in
   a) Lemma 22 of Section 4.3
   Versions of Singular 4.1.2 and 4.1.3 are recomended to run this code, but without the cache files this program should work on
   almost any version of Singular.

----------- Mathematica Notebooks, ".nb" files ---------------------

1. IsomorphismABL.nb
   This notebook contains commutative algebra verifications required for Section 4 of the text. In particular, for
   a) Proposition 19 of Section 4.2
   b) Lemma 21 of Section 4.3
   c) Lemma 45 of Appendix B
   d) Lemma 46 of Appendix B
   e) Lemma 47 of Appendix B

2. Ideal-MCG-Action.nb
   This notebook contains noncommutative algebra verifications required for Appendices A & C. In particular, for
   a) Proposition 48 of Appendix C
   b) Remark 49 of Appendix C
   c) Appendix A
   d) Lemma 4 of Section 2
   

----------- Mathematica Packages, ".m"/".wl" files------------------

We include the following Mathematica Packages which contain most of the procedures:

1. AbstractAlgebra.

-----------Precomputed data, "cache" subdirectory------------

Some of the computations used in this project are rather resourse heavy. For this reason we include precomputed files with an output
of these calculations along with our source code, so that the programs would not require long initialization. Cache is not required
for the code to run, if you clear the cache the programs will recalculate required parts of the cache as they go. Here is the list
of precomputed data included:

1. Radical_T2_Rad1.ssi
   Generating set for the radical of an intermediate zero-dimensional ideal used in the script RadicalT2-v4.singular. Because ".ssi"
   files are version-specific in Singular, they should only be used with Singular 4.1.2 (and a few other compatible versions).
   For other versions delete this cache file and the program will recalculate the generating set using about 1.5G of memeory and
   6-12 hours on average 2023 computer.
   
