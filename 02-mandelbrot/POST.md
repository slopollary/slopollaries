# Slopollary 2: post brief

This file is the single source of truth for posting about Slopollary 2 on X. Use only the facts here. Do not add claims.

## Facts

- **Number and date:** Slopollary 2, 25 November 2026
- **Statement:** For every nontrivial zero ρ of the Riemann zeta function, put μ = 1 − 1/ρ and c = (1 − 1/ρ²)/4. Then |μ| = 1 and c = μ/2 − μ²/4, so c lies on the boundary of the main cardioid of the Mandelbrot set. Equivalently, the map z ↦ z² + c has a neutral fixed point at z₀ = μ/2 (it is fixed, and the derivative 2z₀ has modulus 1).
- **Why it is true:** c = μ/2 − μ²/4 is plain algebra for any ρ ≠ 0. RH puts ρ on the line Re = 1/2, which is equidistant from 0 and 1, so |μ| = |ρ − 1|/|ρ| = 1.
- **Example:** the first zero (γ ≈ 14.1347) gives c ≈ 0.25125 + 0.00009i, just off the cusp at 1/4. The rotation number is about 0.01126.
- **Where the zeros go:** as the zeros climb the critical line, their c values approach the cusp 1/4. The angle of μ is 2·arctan(1/(2γ)).
- **Depends on:** the Riemann hypothesis (Alpöge, released 20 Nov 2026, Lean-certified 21 Nov 2026).
- **Lean status:** compiles on live.lean-lang.org (Lean 4.37.0-rc1, current Mathlib, 25 Nov 2026) with no errors or warnings, no `sorry`, axioms: `propext`, `Classical.choice`, `Quot.sound`. RH is taken as a hypothesis (`RiemannHypothesis`); we did not re-prove RH.
- **Main theorem names:** `mandelbrot_cardioid_slopollary`, `neutral_fixed_point_slopollary`
- **Novelty:** we searched (about 14 queries across two passes) and could not find zeta zeros linked to the Mandelbrot cardioid. The ingredients are classical: |1 − 1/ρ| = 1 under RH is the fact behind Li's criterion, and the cardioid parametrisation is standard.
- **Closest prior work:** Kawahira, "The Riemann hypothesis and holomorphic index in complex dynamics" (arXiv:1602.06843). It shows RH plus simple zeros is equivalent to every nontrivial zero being an indifferent fixed point of a map built from ζ. Same multiplier 1 − 1/ρ, but no quadratic maps and no Mandelbrot set.
- **Depth:** mild. It is two classical facts composed. The packaging is the contribution. Say so if asked.
- **Converse:** if ρ ≠ 0, Re ρ ≠ −1/2 and c is on the cardioid, then Re ρ = 1/2 (formalised as `re_half_of_on_cardioid`). So the statement is equivalent to RH, but that last step uses the critical strip 0 < Re ρ < 1 and is not formalised.
- **Relation to Slopollary 1:** 1/ρ² lies on a cardioid that is the inversion of Slopollary 1's parabola.
- **Links:** https://github.com/slopollary/slopollaries/tree/main/02-mandelbrot

## Must say / must not say

- Say "verified in Lean, given RH". Never "we proved RH" or "verified" without "given RH".
- Say "we couldn't find it stated". Never "this is new" or "first ever".
- Say the zeros land on the boundary of the main cardioid. Never say the zeros "are in" or "generate" the Mandelbrot set, and never imply a deep link between ζ and complex dynamics.
- Never call it deep, a breakthrough, or important.

## Thread

Images: `page-1.png` on post 1, `page-3.png` (Lean source with the main theorems) on post 4.

1/ Slopollary 2. RH is a theorem now, so: every nontrivial zeta zero ρ picks a point on the Mandelbrot set. Take c = (1 − 1/ρ²)/4. It lands exactly on the boundary of the main cardioid. Every single zero.

2/ Why: put μ = 1 − 1/ρ. Then c = μ/2 − μ²/4 (algebra), and RH gives |μ| = 1. That's the textbook formula for the cardioid. So z² + c has a neutral fixed point, one for each zero.

3/ As the zeros climb the critical line, the points slide into the cusp at ¼. First zero: c ≈ 0.25125 + 0.00009i. Is this deep? No. It's Li's |1 − 1/ρ| = 1 plus the cardioid formula. We couldn't find the two put together anywhere.

4/ Lean 4 + Mathlib: compiles, no sorry, standard axioms, RH taken as a hypothesis. Related work: Kawahira, arXiv:1602.06843. Code and paper: github.com/slopollary/slopollaries

## Reply notes

- "Isn't this trivial?" Mild, not deep. Two classical facts composed. That's the genre.
- "Did you prove RH?" No. Alpöge did. We assume it, in Mathlib's own form.
- "So zeta zeros are in the Mandelbrot set?" The points c built from the zeros lie on the boundary of the main cardioid, which is part of the set. The zeros themselves are not.
- "Is it equivalent to RH?" Yes on paper, using the critical strip. The Lean file proves the pointwise converse with two side conditions.
- "Someone already showed this." Thank them, ask for the source, and we will credit it in the repo.
