# 1. selberg-sieve

The aim of this project is to formally verify the fundamental theorem of the Selberg sieve and prove some of its direct consequences. It was ported from [this repo](https://github.com/FLDutchmann/selberg-sieve).

# 2. Build Instructions 
TODO

# 3. Goals
I try to state the most important results and goals in `MainResults.lean` as I work on them.


We prove the following version of the Fundamental Theorem of the Selberg sieve as adapted from [Heath-Brown](https://arxiv.org/abs/math/0209360).

## Fundamental Theorem 
Let $\mathcal{A} = (a_n)$ be a finitely supported sequence of nonnegative real numbers, $\mathcal{P}$ a squarefree number repersenting a finite set of primes, and $y\ge 1$ a real number. 

Suppose we can write $\sum_{d \mid i} a_i = X \nu(d) + R_d$ where $\nu$ is multiplicative and $0 < \nu(p) < 1$ for every prime $p \in \mathcal{P}$.

Then 
$$\sum_{(i,\mathcal{P})=1}a_i\le \frac{X}{S} + \sum_{d \\mid \mathcal{P}, d\le y} 3^{\omega(d)}\left|R_d\right|$$
where 
$$\omega(d) := \sum_{p\mid d} 1, ~~~~ S := \sum_{l\mid \mathcal{P}, l \le \sqrt{y}} g(l)$$
with
$$g(d) = \nu(d)\prod_{p\mid d}(1-\nu(p))^{-1}.$$
And to get a better handle on $S$ we also show that if $\nu$ is completely multiplicative and all primes less than $y$ divide $\mathcal{P}$ then 
$$S \ge \sum_{1 \le m \le \sqrt{y}} \nu(m)$$


## Prime counting function
To test this result, we prove that 
$$ \pi(x) \ll \frac{x}{\log x} $$
And in fact, with little addition effort we are able to prove the Brun-Titchmarsh type bound 
$$ \pi(x+y) - \pi(x) \le 2\frac{y}{\log{z}} + 6z(1+\log{z})^3$$


We hope to later use this result to prove

## Brun's Theorem
Let $\pi_2(x)$ denote the number of twin primes at most $x$. Then 
$$\pi_2(x) \ll \frac{x}{\log(x)^2}$$
and as a corollary
$$\sum_{\text{twin prime} p} \frac{1}{p} < \infty.$$
