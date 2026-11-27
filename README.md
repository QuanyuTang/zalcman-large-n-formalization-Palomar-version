# The Zalcman inequality for sufficiently large indices

**Authors:** Yuyam Cheung, Tao Hu, Quanyu Tang

Codex formalized the authors' original informal proof in Lean 4 with Mathlib.

There is an absolute integer $N \ge 3$ such that every normalized univalent
function $f(z) = z + \sum_{j \ge 2} a_j z^j$ on the unit disk satisfies

$$
\left|a_n^2-a_{2n-1}\right| \le (n-1)^2
\qquad(n\ge N).
$$

Equality holds exactly for $f(z)=\overline{\lambda} k(\lambda z)$ on the
disk, where $|\lambda|=1$ and $k(z)=z/(1-z)^2$.

[`Challenge.lean`](Challenge.lean) states the theorem with its normalization
conditions and equality characterization spelled out. [`Solution.lean`](Solution.lean)
applies the proof of [`Zalcman.zalcman_large_n`](Zalcman/LargeIndex.lean).
The development formalizes the unit-driver Löwner approximation, the positive
Milin representation, and the coefficient and radial estimates that yield
the uniform threshold and rigidity.

Run `lake build` with the pinned Lean toolchain. GitHub Actions builds the
project and runs the Palomar Comparator with the toolchain's bundled kernels.
[Palomar submission instructions](https://palomar-registry.org/how-to-submit).

## Reused Lean sources

The area and distortion proofs reuse Apache-2.0 material from the
[`openai/math` Brennan formalization](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/IntegralMeans).
The Riemann mapping and normal-family proofs reuse material from the
[`openai/math` Crouzeix formalization](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Crouzeix).
