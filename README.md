# A filtration bound for the erasure entropies of Boolean functions

Yitzchak Shmalo

This repository contains a paper on the Fourier entropy-influence (FEI) conjecture of Friedgut and Kalai, together
with the script behind every numerical value in it.

Paper: [main.pdf](main.pdf) (source [main.tex](main.tex)).

## Summary

For a Boolean function f and a coordinate i, let g and h be the even and odd parts of f in x_i, and let U be drawn
from the spectral distribution. FEI is equivalent to every non-constant f having a coordinate with
E_i(f) = H(1[i in U] | U minus i) <= c Inf_i(f). The paper bounds E_i by conditioning on less.

* Reveal the other coordinates in an order pi and keep only the position of the last revealed coordinate that U
  contains. The resulting witness L^pi_i satisfies E_i <= L^pi_i <= h(Inf_i), equals a sum, over the steps, of a
  two-variable entropy of the squared increments of the Doob martingales of g and h, and its minimum over all orders
  is a shortest path over subsets.
* A two-sequence lemma: if, along the order, the probability that i is pivotal both before and after the unrevealed
  coordinates are resampled, times the influence of those coordinates on g, is at most M Inf_i^2, then
  L^pi_i <= (1/ln 2 + 4 + 2 log2(1 + 2M)) Inf_i.
* An exact formula for E_i and Inf_i under block composition F(g(x_B), z).
* A coordinate that enters only through one AND of k + 1 variables has
  2(1 - 2^-k) <= E_i/Inf_i <= L^pi_i/Inf_i <= 2(1 - 2^-k) + 2^-k log2(e 2^k / Inf_i).
* Conditioning on the last r revealed coordinates gives a decreasing family of bounds that reaches E_i at r = n - 1.

## Code

The script needs Python 3 and NumPy. Its saved output is next to it.

* `code/check_witness.py` (output `check_witness_out.txt`): every identity and inequality of the paper, computed with
  exact Walsh-Hadamard transforms on 58 random functions of 3 to 7 variables (all orders up to 6 variables), 60 random
  compositions and 80 random private ANDs, and the table of Section 7 (AND, majority and tribes).
* `code/bent_point.py` (output `bent_point_out.txt`): the bent point replacement of Section 7, every coordinate.

## Related papers

* [The one-coordinate step in the Fourier entropy-influence conjecture](https://github.com/yspennstate/fourier-entropy-influence-one-coordinate)
* [Good coordinates in the Fourier entropy-influence conjecture](https://github.com/yspennstate/fei-good-coordinates)
* [A variance form of Han's bound on the Fourier entropy](https://github.com/yspennstate/fei-variance-han-bound)
* [Four equivalent forms of the Fourier entropy-influence conjecture](https://github.com/yspennstate/fei-equivalent-forms)
* [Erasure entropies of sparse linear DNFs](https://github.com/yspennstate/fei-sparse-linear-dnf)
* [The Fourier entropy of linear monotone DNFs on few variables](https://github.com/yspennstate/fei-linear-dnf-census)

## License

MIT, see [LICENSE](LICENSE).
