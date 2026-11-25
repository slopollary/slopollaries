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
