# Computable algebraic numbers

This project aims to make the algebraic closure of the rationals, short algebraic numbers or 𝔸, computable.
This consists of computable equality, addition, additive inverses, multiplication and multiplicative inverses.
The real and complex part are stored seperately both as an algebraic real number.
We store an real algebraic number by storing a square free polynomial, a rational lower and upper bound forming a closed interval containing exactly the root we want to store where the polynomial is monotone,
and the proves about all the previosly mentioned properties.

Since mathlib doesn't have computable polynomials, including the needed operations on them and linear systems, most of our work consists of building that.




let $a := (p_a,l_a,u_a)$ and $b := (p_b,l_b,u_b)$ with $p_a(x) = \sum_{n=0}^{deg(p_a)} a_n x^n$ and $p_b(x) = \sum_{n=0}^{deg(p_b)} b_n x^n$ be two real algebraic numbers

## Equality
We check whether $\gcd(p_a,p_b)$ contains a root in $[\max(l_a,l_b),\min(u_a,u_b)]$

Note: If the interval has negative length so $\max(l_a,l_b)>\min(u_a,u_b)$ there is no root in it.

## Addition
For every $n \in \mathbb{N}$ we define $z_n:=((\alpha+\beta)^n \mod p(\alpha)) \mod q(\beta)$ and
take a non trivial non almost everywhere zero solution $c_n$ of $\sum_{n \in \mathbb{N}} c_n z_n = 0$

$(c_n)_{n \in \mathbb{N}}$ is now a polynomial with $a+b$ as root.
We now refine the bounds and make our polynomial squarefree.

## Additive inverse
Take the additive inverse of all odd coefficients $c_n = a_n \cdot (-1)^n$
The bounds change their sign and place.

## Multiplication
For every $n \in \mathbb{N}$ we define $z_n:=((\alpha \cdot \beta)^n \mod p(\alpha)) \mod q(\beta)$ and
take a non trivial non almost everywhere zero solution $c_n$ of $\sum_{n \in \mathbb{N}} c_n z_n = 0$

$(c_n)_{n \in \mathbb{N}}$ is now a polynomial with $a \cdot b$ as root.
We now refine the bounds and make our polynomial squarefree.

## Multiplicative inverse
$c_n := a_{deg(p_a)-n}$ $%p_c(\alpha) := p_a(\frac{1}{\alpha})\cdot\alpha^{degree(p_a)}$
