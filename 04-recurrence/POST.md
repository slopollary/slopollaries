# Slopollary 4: post brief

This file is the single source of truth for posting about Slopollary 4. Use only the facts here. Do not add claims.

## Facts

- **Number and date:** Slopollary 4, 27 November 2026.
- **Setting:** for finitely many complex numbers μ_1, …, μ_k, the "Li test at exponent n" is the sum L_n = Σ Re(1 − μ_j^n). If every |μ_j| ≤ 1, every test passes (L_n ≥ 0). The finite Bombieri–Lagarias theorem (1999) is the converse when all n ≥ 1 are tested. With μ = 1 − 1/ρ over zeros of ζ this is the mechanism behind Li's criterion for the Riemann hypothesis.
- **Question:** if you only test the exponents n in a set S, does passing every test still force every |μ_j| ≤ 1? If yes for every finite family, "Li's criterion works along S".
- **Statement (Slopollary 4):** Li's criterion works along S if and only if S is a set of Bohr recurrence. A set of Bohr recurrence is a set S such that, for any finitely many points u on the unit circle and any ε > 0, some n > 0 in S has every u^n within ε of 1.
- **Why it is true:** if S is recurrent, pick n in S where all the phases line up; the biggest modulus then dominates and the sum goes negative. If S is not recurrent, a de la Vallée-Poussin kernel with its constant term removed gives finitely many points of modulus 2 whose tests are all ≥ 0 on S.
- **Enough:** all n ≥ 1; the multiples of any fixed m ≥ 1 (so the multiples of a million are enough).
- **Not enough:** the primes. Concrete example: the single point 2i. Its test is 5 at p = 2 and exactly 1 at every odd prime, yet |2i| = 2.
- **Also true but not in the Lean file:** the odd numbers are not enough (the pair 2, −2 gives L_n = 2 for every odd n). Lacunary sets such as powers of 2 and factorials are not sets of Bohr recurrence (known, see arXiv:2406.01353), so they are not enough. The squares are a set of recurrence (Furstenberg, Sárközy), so they are enough.
- **Riemann hypothesis form:** if S is a set of Bohr recurrence, RH holds if and only if for every finite set Z of nontrivial zeros and every n in S, Σ over Z of Re(1 − (1 − 1/ρ)^n) ≥ 0.
- **Depends on:** nothing unproved. The RH form is an equivalence of statements with Mathlib's `RiemannHypothesis`; RH itself (Alpöge, 20 Nov 2026) is not imported.
- **Lean status:** `Slopollary4.lean` (741 lines) compiled on live.lean-lang.org (Lean 4.37.0-rc1, latest Mathlib) on 27 November 2026, exactly as published: no errors, no warnings, no `sorry`; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for each main theorem.
- **Main theorem names:** `liAlong_iff_bohrRecurrent`, `liAlong_multiples`, `not_liAlong_primes`, `two_I_passes_prime_tests`, `riemannHypothesis_iff_finite_li_sums_along`.
- **Novelty:** we could not find the equivalence, or the failure along the primes, stated anywhere, and could not find a Lean formalisation. Searched: Li's criterion along subsequences / arithmetic progressions; Bombieri–Lagarias with Bohr recurrence; one-sided power sum problems (Turán) with Bohr recurrence. The searches were short.
- **Prior work to credit:** Li (1997); Bombieri–Lagarias (1999); Turán's power sum method (power sums over prescribed sets of exponents); Bohr recurrence is a standard notion; the kernel is de la Vallée-Poussin's.
- **Limits:** the theorem is about arbitrary finite families of points. It does NOT say the real Li coefficients λ_n of ζ (infinite sums over all zeros) fail to characterise RH along the primes. We do not know that.
- **Depth:** a real two-sided proof (compactness one way, a positive kernel the other), at the level of a first course in harmonic analysis. Not deep. A specialist in power sums may well know it.
- **Link:** https://github.com/slopollary/slopollaries/tree/main/04-recurrence

## Must say / must not say

- Say "verified in Lean" for the theorem and "proved equivalent to RH in Lean" for the RH form. Never "we proved RH".
- Say "we couldn't find it stated". Never "this is new" or "first ever".
- Say "for finite families of points". Never "Li's criterion for the Riemann hypothesis fails along the primes".
- Never call it deep, a breakthrough, or important.

## Thread

Images: `page-1.png` on post 1, `page-2.png` (the proof) on post 3, `page-3.png` (the figure) on post 4.

1/ Slopollary 4. Li's criterion checks a sum for every exponent n = 1, 2, 3, … Do you need all of them? For finite sets of points we found the exact answer: you need a "set of Bohr recurrence", no more and no less.

2/ So: multiples of 1,000,000 are enough. Primes are not. The single point 2i passes the test at every prime (5 at p = 2, exactly 1 at every odd prime) while sitting at distance 2 from the origin.

3/ Why: if your exponents make every finite set of rotations come home, the phases line up and the biggest point blows the sum negative. If they don't, a classical positive kernel builds points of modulus 2 that the test can't see.

4/ Back to Riemann: for any such set S, RH ⇔ every finite partial Li sum over zeros with exponent in S is ≥ 0. Caveat: this is about finite families. It doesn't say the real Li coefficients fail along the primes.

5/ Lean 4 + Mathlib, 741 lines, no sorry, standard axioms. Li, Bombieri–Lagarias, Turán and de la Vallée-Poussin did the classical parts; the equivalence is the bit we couldn't find stated. Not deep, but a real proof. github.com/slopollary/slopollaries

## Reply notes

- "Isn't this trivial?" It is elementary, not trivial: one direction needs a kernel construction. It is first-course harmonic analysis and we say so.
- "Did you prove RH?" No. Alpöge did. The RH form is an equivalence of statements.
- "So Li's criterion fails on the primes?" Only for arbitrary finite families of points, e.g. the point 2i. Nothing is claimed about the actual Li coefficients of ζ.
- "What is Bohr recurrence?" S is a set of Bohr recurrence if any finite set of circle rotations returns arbitrarily close to the start at some time in S.
- "This is already known." Thank them, ask for the source, credit it in the repo.
