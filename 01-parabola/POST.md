# Slopollary 1: post brief

This file is the single source of truth for posting about Slopollary 1 on X. Use only the facts here. Do not add claims.

## Facts

- **Number and date:** Slopollary 1, 25 November 2026
- **Statement:** For every nontrivial zero ρ of the Riemann zeta function, ρ² lies on the parabola with focus 0 and directrix Re = 1/2 (equivalently |ρ²| = 1/2 − Re(ρ²)), and Im(ρ²) = Im(ρ).
- **Why it is true:** RH gives ρ = 1/2 + iγ, so ρ² = (1/4 − γ²) + iγ, which is the parabola x = 1/4 − y².
- **Example:** the first zero has γ ≈ 14.1347, so ρ² ≈ −199.54 + 14.13i.
- **Depends on:** the Riemann hypothesis (Alpöge, released 20 Nov 2026, Lean-certified 21 Nov 2026).
- **Lean status:** compiles against Mathlib on live.lean-lang.org (25 Nov 2026), no `sorry`, axioms: `propext`, `Classical.choice`, `Quot.sound`. RH is taken as a hypothesis (`RiemannHypothesis`); we did not re-prove RH.
- **Main theorem name:** `parabola_slopollary`
- **Novelty:** we searched and could not find this stated about zeta zeros. The underlying geometry (squaring a vertical line gives a parabola with focus at the origin) is classical.
- **Depth:** shallow. Three lines of algebra once RH is known. Say so if asked.
- **Converse:** true (the statement is equivalent to RH) but not formalised.
- **Links:** https://github.com/slopollary/slopollaries/tree/main/01-parabola

## Must say / must not say

- Say "verified in Lean, given RH". Never "we proved RH" or "verified" without "given RH".
- Say "we couldn't find it stated". Never "this is new" or "first ever".
- Never call it deep, a breakthrough, or important.

## Thread

Images: paper page 1 on post 1, paper page 2 (Lean source) on post 4.

1/ Slopollary 1. RH is a theorem now, so: square every nontrivial zero of the zeta function and they all land on ONE parabola. Focus: the origin. Directrix: the critical line.

2/ Why: RH says ρ = ½ + iγ. So ρ² = (¼ − γ²) + iγ. That's the parabola x = ¼ − y². Bonus: squaring a zero doesn't change its height.

3/ Is this deep? No. Squaring a vertical line gives a parabola; that's classical. What's new is saying it about zeta zeros without the word "conjecturally". We couldn't find it stated anywhere.

4/ Lean 4 + Mathlib: compiles, no sorry, standard axioms, RH taken as a hypothesis. Code and paper: github.com/slopollary/slopollaries

## Reply notes

- "Isn't this trivial?" Yes, given RH. That's the genre.
- "Did you prove RH?" No. Alpöge did. We assume it, in Mathlib's own form.
- "Someone already showed this." Thank them, ask for the source, and we will credit it in the repo.
