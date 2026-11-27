# Slopollaries

Small, original theorems proved off the back of big results, by Maths Slop.

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
| 2 | 25 Nov 2026 | For every nontrivial zero ρ of ζ, the point c = (1 − 1/ρ²)/4 lies on the boundary of the Mandelbrot set's main cardioid; equivalently z² + c has a neutral fixed point. Superseded by Slopollary 3. | [paper](02-mandelbrot/slopollary2.pdf) · [Lean](02-mandelbrot/Slopollary2.lean) · [TeX](02-mandelbrot/slopollary2.tex) · [post brief](02-mandelbrot/POST.md) |
| 3 | 26 Nov 2026 | The map c(s) = ¼ − 1/(4s²) sends Re s > ½ onto the main cardioid of the Mandelbrot set and the critical line onto its boundary; RH ⇔ no nontrivial zero lands inside the cardioid. Plus a finite Li criterion: RH ⇔ every finite partial Li sum over zeros is ≥ 0. Supersedes Slopollary 2. | [paper](03-dictionary/slopollary3.pdf) · [Lean: dictionary](03-dictionary/Slopollary3.lean) · [Lean: finite Li](03-dictionary/FiniteLi.lean) · [TeX](03-dictionary/slopollary3.tex) · [post brief](03-dictionary/POST.md) |
| 4 | 27 Nov 2026 | Which exponents does Li's criterion need? For finite families of points, the test Σ Re(1 − μⁿ) ≥ 0 over n ∈ S forces all \|μ\| ≤ 1 if and only if S is a set of Bohr recurrence. Multiples of any m are enough; the primes are not (2i passes every prime test). For recurrent S, RH ⇔ all finite partial Li sums over zeros with exponent in S are ≥ 0. | [paper](04-recurrence/slopollary4.pdf) · [Lean](04-recurrence/Slopollary4.lean) · [TeX](04-recurrence/slopollary4.tex) · [post brief](04-recurrence/POST.md) |

## Checking a proof yourself

Paste any `.lean` file into [live.lean-lang.org](https://live.lean-lang.org) and add `#print axioms <theorem name>` at the end. No errors, and an axioms line listing only `propext`, `Classical.choice` and `Quot.sound`, means it checks.

## Licence

Free to use, share and build on, with credit to **Maths Slop**.

- Lean code (`.lean`): [Apache License 2.0](LICENSE-APACHE), the same licence as Mathlib.
- Papers, figures, post briefs and everything else: [CC BY 4.0](LICENSE-CC-BY).

Suggested credit: "Slopollary N, Maths Slop, github.com/slopollary/slopollaries".
