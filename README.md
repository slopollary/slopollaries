# Slopollaries

Small, original theorems proved off the back of big results, by [@slopollary](https://x.com/slopollary).

Every slopollary ships with:

- a Lean 4 file that compiles against Mathlib with no `sorry` and only the standard axioms,
- a short paper (PDF and LaTeX source),
- a thread on X.

The Lean theorems take the big result as a hypothesis in Mathlib's own form (for example `RiemannHypothesis`). They are "verified in Lean, given RH"; they do not re-prove RH. The Riemann hypothesis itself was proved by Levent Alpöge (released 20 November 2026, certified by the Lean and Mathlib communities on 21 November 2026).

On novelty: we search for each statement before posting and publish only when we cannot find it. If you know a prior source, open an issue and we will credit it.

## Index

| # | Date | Statement | Files |
|---|------|-----------|-------|
| 1 | 25 Nov 2026 | For every nontrivial zero ρ of ζ, the square ρ² lies on the parabola with focus 0 and directrix Re = ½, and Im(ρ²) = Im(ρ). | [paper](01-parabola/slopollary1.pdf) · [Lean](01-parabola/Slopollary1.lean) · [TeX](01-parabola/slopollary1.tex) · [post brief](01-parabola/POST.md) |

## Checking a proof yourself

Paste any `.lean` file into [live.lean-lang.org](https://live.lean-lang.org) and add `#print axioms <theorem name>` at the end. No errors, and an axioms line listing only `propext`, `Classical.choice` and `Quot.sound`, means it checks.

## Licence

Free to use, share and build on, with credit to **@slopollary**.

- Lean code (`.lean`): [Apache License 2.0](LICENSE-APACHE), the same licence as Mathlib.
- Papers, figures, post briefs and everything else: [CC BY 4.0](LICENSE-CC-BY).

Suggested credit: "Slopollary N, @slopollary, github.com/slopollary/slopollaries".
