# Computable algebraic numbers

This project aims to make the algebraic closure of the rationals, in short algebraic numbers, computable.
This consists of computable equality, addition, additive inverses, multiplication and multiplicative inverses.
The real and complex parts are stored separately both as an real algebraic number.
We store a real algebraic number by storing a square free polynomial, a rational lower and upper bound forming a closed interval containing exactly the root we want to store where the derivative is none zero everywhere,
and the proofs about all the previously mentioned properties. (Currently we only have the real algebraic numbers.)

Since Mathlib doesn't have computable polynomials, including the needed operations on them and linear systems, most of our work consists of building that.


## Operations

Let $a := (p_a,l_a,u_a)$ and $b := (p_b,l_b,u_b)$ with $p_a(x) = \sum_{n=0}^{deg(p_a)} a_n x^n$ and $p_b(x) = \sum_{n=0}^{deg(p_b)} b_n x^n$ be two real algebraic numbers.

### Equality
We can check whether $\gcd(p_a,p_b)$ contains a root in $[\max(l_a,l_b),\min(u_a,u_b)]$

Note: If the interval has negative length so $\max(l_a,l_b)>\min(u_a,u_b)$ there is no root in it.

In pratise, we compare the difference to zero which is easier albiet less efficient.

### Addition
Take a non trivial, finite support solution $c_n$ of $\sum_{n \in \mathbb{N}} c_n (\alpha+\beta)^n \equiv 0 \mod (p_a(\alpha),p_b(\beta))$

$(c_n)_{n \in \mathbb{N}}$ is now a polynomial with $a+b$ as root.
We now refine the bounds and make our polynomial squarefree.

### Additive inverse
Take the additive inverse of all odd coefficients $c_n = a_n \cdot (-1)^n$
The bounds change their sign and place.

### Multiplication
Take a non trivial, finite support solution $c_n$ of $\sum_{n \in \mathbb{N}} c_n (\alpha\cdot\beta)^n \equiv 0 \mod (p_a(\alpha),p_b(\beta))$

$(c_n)_{n \in \mathbb{N}}$ is now a polynomial with $a \cdot b$ as root.
We now refine the bounds and make our polynomial squarefree.

### Multiplicative inverse
$c_n := a_{deg(p_a)-n}$ $%p_c(\alpha) := p_a(\frac{1}{\alpha})\cdot\alpha^{degree(p_a)}$

We did not get around to implement this.

## Project structure

### [ApproximationType.lean](ComputableAlgebraicNumbers/ApproximationType.lean)

To implement brefining bounds, we introduced the notion of an `ApproximationType`, which is a Type with an `improve` endofunction. In our case, we take the bisect our interval and check which half the root lies in. If we have a decidable predicate that is eventually true if we improve often enough and that is stable under further improve operations, we say it `isExact`. Then we can, from each element improve until the predicate is true. That is how we refine bounds sufficiently whereever we need to.

### [CPoly.lean](ComputableAlgebraicNumbers/CPoly.lean)

We implement our own Polynomial ring `CPoly R` in a way that is computable, i. e. a polynomial consists of a list of coeficients and a proof that there are no tailing zeros. We construct an isomorphism to the Mathlib definition, which is not computable, which we extensively rely on for proofs. We intrduced a simp set `toPolynomialSimp` to translate simple goals about `CPoly` to Mathlib Polynomials, which can often be easily proved with lemmas from the library.

### [PolyOperations.lean](ComputableAlgebraicNumbers/PolyOperations.lean)

Here we define functions to find a polynomial that has the sums/products of pairs of root of given polynomials as roots, as described above, this requires solving a linear system. We can always phrase this as finding a non-zero vector in the kernel of a matrix with more columns then rows, which is always possible. We wrote our own solver for this problem, but for time reasons we did not manage to prove its correctness, hence we sorryed the corresponding proves.

### [AlgebraicNumber.lean](ComputableAlgebraicNumbers/AlgebraicNumber.lean)

A `PreRealAlgebraicNumber` consists of a minimal polynomial (which is actually not required to be minimal, just a squarefree polynomial with the number as a root), an upper and lower bound, and some proofs:
- A prove that the polynomial has different sings (or is zero) on the bounds
- A prove that the derivative is non-zero on the entire interval

From these it is easy to conclude that there is exactly one root in the (closed) interval. We have some lemmas to work with them.
We also have the notion of a `PolyLevelFun` which consist of data and proves required to implement a function on real numbers to a function on real algebraic numbers. Here we sorryed some proves that this data actually suffices. This `PolyLevelFun` can now `lift` to a function on real algebraic numbers. Real algebraic numbers are a quotient of Pre-real-algebraic-numbers by them having the same root (This equivalence relation is not decidable, this is not an issue).

### [Tests.lean](ComputableAlgebraicNumbers/Tests.lean)
A few Tests for our real algebraic numbers.

### [Array2d.lean](ComputableAlgebraicNumbers/Array2d.lean) [Array2d_WIP_refactor.lean](ComputableAlgebraicNumbers/Array2d_WIP_refactor.lean)
An efficient WIP linear equations solver.

### [PolyFactor.lean](ComputableAlgebraicNumbers/PolyFactor.lean)
WIP polynom factorization
