# e is irrational

A formal proof in [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
that Euler's number `e = ∑ 1/n!` is irrational, via the classic argument. Namely, if `e = r/s`
were rational, then `s! · (e − ∑_{n≤s} 1/n!)` would be an integer strictly between `0` and `1`,
which is impossible.

This was my first Lean project, done to get hands-on experience with AI-assisted formalization
workflows. I wrote the proof skeleton and lemma breakdown below myself, then used Claude Opus to
translate it into Lean syntax, debugging and verifying the resulting code line by line.

The whole development is in [`test.lean`](test.lean). The key result is:

```lean
theorem e_irrational : Irrational e
```

## Proof outline

| Lemma | Statement |
| --- | --- |
| `is_summable` | `∑ 1/n!` converges |
| `split_sum` | `∑ 1/n! = (∑_{n<s} 1/n!) + ∑_{n≥s} 1/n!` |
| `A_times_s_factorial_integer` | `s! · (r/s − ∑_{n≤s} 1/n!)` is an integer |
| `tail_pos` | `s! · ∑_{n≥s+1} 1/n! > 0` |
| `tail_lt_one` | `s! · ∑_{n≥s+1} 1/n! < 1` (geometric bound) |
| `e_irrational` | combine the above: no integer lies in `(0, 1)` |

## Building

This file depends on Mathlib, so it must be compiled inside a Lean project that provides it.

```bash
lake update
lake build
```
