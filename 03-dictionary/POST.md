# Slopollary 3: post brief

This file is the single source of truth for posting about Slopollary 3. Use only the facts here. Do not add claims.

## Facts

- **Number and date:** Slopollary 3, 26 November 2026.
- **The map:** c(s) = 1/4 − 1/(4s²) sends zeta's plane to the Mandelbrot parameter plane. The quadratic map z² + c(s) has a fixed point with multiplier μ = 1 − 1/s, and the holomorphic index of that fixed point, 1/(1 − μ), equals s.
- **Dictionary (for Re s > 0):** c(s) is inside the main cardioid exactly when Re s > 1/2, and on its boundary exactly when Re s = 1/2. The pole s = 1 goes to the centre c = 0. The trivial zeros go to 1/4 − 1/(16n²) on the real axis. The line Re s = t/2 goes to the cardioid scaled about its cusp by 1/t².
- **RH, three equivalent forms (all proved in Lean as "if and only if" with Mathlib's RiemannHypothesis):**
  1. No nontrivial zero lands inside the main cardioid.
  2. Every nontrivial zero lands on the boundary of the main cardioid.
  3. ζ(1/(1 − μ)) ≠ 0 for every μ in the open unit disc.
- **Unconditional:** the classical zero-free region Re s ≥ 1 is the quarter-size cardioid. Nontrivial zeros are confined to the crescent between it and the main cardioid.
- **Finite Li criterion:** for finitely many complex numbers μ_j, the sums Σ Re(1 − μ_j^n) are ≥ 0 for all n ≥ 1 exactly when every |μ_j| ≤ 1. This is the finite case of a 1999 theorem of Bombieri and Lagarias.
- **RH via finite Li sums:** RH holds if and only if, for every finite set Z of nontrivial zeros and every n ≥ 1, Σ over Z of Re(1 − (1 − 1/ρ)^n) ≥ 0.
- **Depends on:** nothing unproved. The equivalences are with RH as a statement; RH itself (Alpöge, 20 Nov 2026) is not imported.
- **Lean status:** compiled on live.lean-lang.org (Lean 4.37.0-rc1, current Mathlib), no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`. Both published files, `Slopollary3.lean` and `FiniteLi.lean`, were checked exactly as published (26 Nov 2026). `FiniteLi.lean` gives one deprecation warning.
- **Main theorem names:** `dictionary`, `riemannHypothesis_iff_no_zero_inside_cardioid`, `riemannHypothesis_iff_neutral`, `riemannHypothesis_iff_zero_free_at_attracting_index`, `no_zero_in_quarter_cardioid`, `finite_li_criterion`, `riemannHypothesis_iff_finite_li_sums_nonneg`.
- **Novelty:** we could not find the Mandelbrot forms, the quarter-cardioid picture, or the finite-sum form of RH stated anywhere, and we could not find a Lean formalisation of the finite Bombieri–Lagarias theorem. The searches were short.
- **Prior work to credit:** Kawahira (arXiv:1602.06843) for RH and the holomorphic index; Li (1997) and Bombieri–Lagarias (1999) for Li's criterion; Milnor's book for the cardioid and index facts.
- **Supersedes:** Slopollary 2, whose statement is the boundary form above.
- **Links:** https://github.com/slopollary/slopollaries/tree/main/03-dictionary
- **Depth:** the dictionary is a change of variables. The finite Li theorem is known mathematics with a real proof (a compactness argument). The finite-sum form of RH is an easy consequence. Say so if asked.

## Must say / must not say

- Say "proved equivalent to RH in Lean". Never "we proved RH".
- Say "we couldn't find it stated". Never "this is new" or "first ever".
- Say the finite Li theorem is the finite case of Bombieri–Lagarias. Never present it as our theorem.
- Never say zeta zeros "are in" the Mandelbrot set; the points c(ρ) are on the boundary of the main cardioid.
- Never call it deep, a breakthrough, or important.

## Thread

Images: `page-1.png` on post 1, `page-2.png` (the figure) on post 2.

1/ Slopollary 3. One formula, c = ¼ − 1/(4s²), turns the Riemann zeta plane into the Mandelbrot set. Right of the critical line ↦ inside the main cardioid. Critical line ↦ its boundary. The pole ↦ the centre.

2/ So: the Riemann hypothesis holds if and only if no zeta zero lands inside the cardioid. The classical zero-free region is a quarter-size copy of the cardioid, so the zeros live in a crescent, and RH says they sit on the outer rim.

3/ Why it works: z² + c has a fixed point whose "holomorphic index" is s itself, and index with real part ½ means neutral. Kawahira linked RH to this index in 2016; the Mandelbrot picture is the part we couldn't find anywhere.

4/ Bonus, with a real proof: we formalised the finite case of Bombieri–Lagarias (1999). Consequence: RH ⇔ every finite partial Li sum over zeros is ≥ 0. No infinite sums needed.

5/ All of it is Lean 4 + Mathlib, no sorry, standard axioms, proved as equivalences with Mathlib's own statement of RH. Is it deep? No. It is a change of variables and a known theorem. It is a nice picture. Code and paper: github.com/slopollary/slopollaries

## Reply notes

- "Isn't this just a Möbius map and a square?" Yes. That is the proof.
- "Did you prove RH?" No. Alpöge did. These are statements proved equivalent to it.
- "Is the finite Li result new?" The theorem is Bombieri–Lagarias, 1999. The Lean proof and the finite-sum form of RH are what we add.
- "Someone already showed this." Thank them, ask for the source, credit it in the repo.
