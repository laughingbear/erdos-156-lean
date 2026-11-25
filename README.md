# erdos-156-lean

A Lean 4 proof of `Erdos156.erdos_156.variants.greedy_lower_bound` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/156.lean`): the greedy Sidon set in $\{1, \ldots, N\}$ has size
$\gg N^{1/3}$.

The proof is in [`Erdos156.lean`](Erdos156.lean). It proves an invariant of formal-conjectures'
`Finset.greedySidon.aux` (every skipped number is incompatible with the smaller chosen elements),
shows that such a number is $a + b - c$ or $(a + b)/2$ with $a, b, c$ chosen, and concludes
$N \le 3|G|^3$.

The greedy definitions, the supporting lemmas they use, the `≫` notation and the theorem statement
are copied verbatim from formal-conjectures. Mathlib is pinned to the same commit as
formal-conjectures (`0df444a`, Lean v4.33.1).

```
lake exe cache get
lake build
```

`#print axioms Erdos156.erdos_156.variants.greedy_lower_bound` gives
`[propext, Classical.choice, Quot.sound]`.

The proof was written with AI assistance (Claude).
