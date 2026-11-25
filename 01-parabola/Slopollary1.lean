import Mathlib

/-!
# Slopollary 1 — the parabola of squared zeta zeros

Under the Riemann hypothesis, the square of every nontrivial zero of ζ lies on
the parabola with focus `0` and directrix `Re w = 1/2`, and squaring leaves the
imaginary part of the zero unchanged.
-/

open Complex

/-- On the critical line, squaring does not change the imaginary part. -/
theorem sq_im_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) : (ρ ^ 2).im = ρ.im := by
  rw [sq, Complex.mul_im, h]; ring

/-- On the critical line, `Re (ρ²) = 1/4 - (Im ρ)²`. -/
theorem sq_re_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) :
    (ρ ^ 2).re = 1 / 4 - ρ.im ^ 2 := by
  rw [sq, Complex.mul_re, h]; ring

/-- Focus–directrix form: distance from `ρ²` to `0` equals its distance to the
line `Re w = 1/2`. -/
theorem norm_sq_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) :
    ‖ρ ^ 2‖ = 1 / 2 - (ρ ^ 2).re := by
  rw [sq_re_of_re_half ρ h, norm_pow, Complex.sq_norm, Complex.normSq_apply, h]
  ring

/-- **Slopollary 1.** Assume the Riemann hypothesis. If `ρ` is a nontrivial zero
of the Riemann zeta function, then `ρ²` lies on the parabola with focus `0` and
directrix `Re w = 1/2`, and `Im (ρ²) = Im ρ`. -/
theorem parabola_slopollary (RH : RiemannHypothesis) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1) :
    ‖ρ ^ 2‖ = 1 / 2 - (ρ ^ 2).re ∧ (ρ ^ 2).im = ρ.im :=
  have h : ρ.re = 1 / 2 := RH ρ hζ htriv h1
  ⟨norm_sq_of_re_half ρ h, sq_im_of_re_half ρ h⟩

/-- A nontrivial zero of ζ has positive real part (from Mathlib's description of the
zeros in the closed left half-plane). -/
theorem nontrivial_zero_re_pos {s : ℂ} (hζ : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra h
  exact htriv ((riemannZeta_eq_zero_iff_of_re_nonpos (not_lt.mp h)).mp hζ)

/-- Converse on the right half-plane: a point with positive real part whose square lies
on the parabola has real part `1/2`. -/
theorem re_half_of_on_parabola (ρ : ℂ) (hpos : 0 < ρ.re)
    (h : ‖ρ ^ 2‖ = 1 / 2 - (ρ ^ 2).re) : ρ.re = 1 / 2 := by
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re] at h
  have h2 : (ρ.re - 1 / 2) * (ρ.re + 1 / 2) = 0 := by
    linear_combination h / 2
  rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith

/-- **Equivalence.** The Riemann hypothesis holds if and only if the square of every
nontrivial zero lies on the parabola with focus `0` and directrix `Re w = 1/2`. -/
theorem parabola_iff :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
        ‖ρ ^ 2‖ = 1 / 2 - (ρ ^ 2).re := by
  constructor
  · intro RH ρ hζ ht h1
    exact (parabola_slopollary RH ρ hζ ht h1).1
  · intro H ρ hζ ht h1
    exact re_half_of_on_parabola ρ (nontrivial_zero_re_pos hζ ht) (H ρ hζ ht h1)

#print axioms parabola_slopollary
#print axioms parabola_iff
