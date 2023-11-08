# GenusTwoDAHA-Basis
This project contains supplementary materials for paper ArXiv:2309.01011 http://arxiv.org/abs/2309.01011

-----------Scripts for SINGULAR, ".singular" files-----------

The following scripts must be executed in Computer Algebra software SINGULAR https://www.singular.uni-kl.de/

1. RadicalT2-v4.singular
   This scripts performs the computation of the radical of defining ideal of A_{q=t=1} which is used in
   
   a) Lemma 22 of Section 4.3
   
   Versions of Singular 4.1.2 and 4.1.3 are recomended to run this code, but without the cache files this program should work on
   almost any version of Singular.

----------- Mathematica Notebooks, ".nb" files ---------------------

1. CommutativeIsomorphism.nb
   This notebook contains commutative algebra verifications required for Section 4 of the text. In particular, for
   
   a) Proposition 19 of Section 4.2
   
   b) Lemma 21 of Section 4.3
   
   c) Lemma 45 of Appendix B
   
   d) Lemma 46 of Appendix B
   
   e) Lemma 47 of Appendix B

3. Ideal-MCG-Action.nb
   This notebook contains noncommutative algebra verifications required for Appendices A & C. In particular, for
   
   a) Proposition 48 of Appendix C
   
   b) Remark 49 of Appendix C
   
   c) Appendix A
   
   d) Lemma 4 of Section 2
   

----------- Mathematica Packages and Data, ".m"/".wl" files------------------

1. AbstractAlgebra.m
   General package to work with associative algebra over a field.

2. CommutativeAlgebra.wl
   Basic functionality for commutative algebra.

3. PoissonGeometry.wl
   Basic functionality for Poisson brackets on commutative algebras.

4. Deformation6j.wl
   Package written with paper arXiv:1504.02620. We use just a few notations from there for consistency.

5. HigherRuijsenaars.wl
   Package written with paper arXiv:1704.02947. We use it to define homomorphism to q-difference operators.

6. OxxAlgebra.wl
   Main package for the current text.

7. RepresentationAlgebras.wl
   This package is used to define coordinate ring of the representation variety.

8. ABL18-g2b0sl2.m
   Generators and Relations of the set thoretic cut-off for genus two character variety obtained via program math.gmu.edu/%7eslawton3/trace-identities.nb
   using the following input: FromSnapPyList["Generators: a,b,c,d Relators: abABcdCD"];
   We use this list of relations in CommutativeIsomorphism.nb


-----------Precomputed data, "cache" subdirectory------------

Some of the computations used in this project are resource heavy. For this reason we include precomputed files with an output
of these calculations along with our source code, so that the programs would not require long initialization. Cache is not required
for the code to run, if you clear the cache the programs will recalculate required parts of the cache as they go. Here is the list
of precomputed data included:

1. Radical_T2_Rad1.ssi
   Generating set for the radical of an intermediate zero-dimensional ideal used in the script RadicalT2-v4.singular. Because ".ssi"
   files are version-specific in Singular, they should only be used with Singular 4.1.2 (and a few other compatible versions).
   For other versions delete this cache file and the program will recalculate the generating set using about 1.5G of memeory and
   6-12 hours on average 2023 computer.
   
2. Quot1_h1_T2.singular
   Generators of the first quotient ideal used for calculation of a saturated ideal in RadicalT2-v4.singular.
   Can be recalculated in just a few hours if Radical_T2_Rad1.ssi is already computed.

4. Quot1_h2_T2.singular
   Generators of the second quotient ideal used for calculation of a saturated ideal in RadicalT2-v4.singular.
   Also can be recalculated in just a few hours if Radical_T2_Rad1.ssi is already computed.

6. NCGroebner/XX.m
   Expression for the q-Groebner element with number 1<=XX<=61. This cache is needed to bring expressions to canonical form in the main algebra.
   If cached files are not found by the program, parts of it will be automatically recomputed only as neccessary, i.e.
   when simplification of your expression actually utilizes the given q-Groebner element. The full collection of q-Groebner elements can be recomputed in a few hours.

8. NCGroebner/Coeff-Ideal19-XX.m
   Decomposition of q-Groebner elements as linear combintaion of relators \rho and \eta with two-sided coefficients regular at Q=1.
   Essentially formulas for the proof of Proposition 48 of Appendix C.
   This cache on its own can be recomputed in a few hours provided that computationally-heavy auxiliarry cache "Ideal19/regular-basis-XX.m" is already computed.

10. Ideal19/regular-basis-XX.m
    Auxilliary cache, primarily used as an intermediate step for computation of "NCGroebner/Coeff-Ideal19-XX.m".
    It contains small spanning set of linear combinations of relators up to the total degree XX using the \rho and \eta generators with coefficients regular at Q=1.
    For 1<=XX<=9 this can be recomputed in secods; for XX=10 in a few minutes; for XX=11 in a few hours; for XX=12 in a couple of days.
    Without parallelization XX=13 computes in a couple of weeks. This cache is needed if you want to compute decomposition of q-Groebner elements via original relators with regular coefficients, see Ideal-MCG-Action.nb.
