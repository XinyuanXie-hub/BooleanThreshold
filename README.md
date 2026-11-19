# BooleanThreshold

This project uses Lean to verify Theorem 1 (Counting Boolean threshold functions) and Theorem 7 (Linear dependence) from the following paper.

> Xinyuan Xie, *Boolean threshold functions, neuron capacity, and memory retrieval*, [arXiv:2609.29756v1](https://arxiv.org/abs/2609.29756v1).

## Mathematical statements

A Boolean threshold function is a map $`f:\{-1,1\}^{n}\to\{-1,1\}`$ of the form

```math
f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)
```

for real coefficients $a_0,\ldots,a_n$.

<a name="theorem-1"></a>

**Theorem 1 (Counting Boolean threshold functions).** Write $T_n$ for the number of Boolean threshold functions on $`\{-1,1\}^{n}`$. For every integer $n\ge 1$,

```math
T_n=2\binom{2^n-1}{n}\bigl(1+O(n^{-99})\bigr)
```

with an absolute implicit constant.

<a name="theorem-7"></a>

**Theorem 7 (Linear dependence).** For $1\le r\le n-1$, draw $v_1,\ldots,v_r$ independently and uniformly from $`\{-1,1\}^n`$. Then

```math
\mathbb P\{v_1,\ldots,v_r\text{ are linearly dependent}\}
=2\binom{r}{2}\,2^{-n}+O(2^{-n}e^{-cn})
```

for an absolute $c>0$ and an absolute implicit constant.

## Verification

Check that the statements and definitions in [Challenge.lean](Challenge.lean) match the mathematical statements above and the cited sources. Then run:

```sh
bash scripts/verify-comparator.sh
```

This runs the full Comparator with Lean, NanoDa, and con-ron.

To inspect verification on GitHub:

1. Open this repository’s **Actions** tab and select the run for the commit being reviewed.
2. Open “Verify the Challenge against Solution”, then “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log reports acceptance by Lean, NanoDa, and con-ron, followed by `Your solution is okay!`.

Successful verification checks the recorded Lean statements and proofs; fidelity to the paper requires reviewing Challenge.lean.

See Lean's documentation on [validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) and [Comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator).
