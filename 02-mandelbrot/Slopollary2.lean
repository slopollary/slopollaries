import Mathlib

/-!
# Slopollary 2: zeta zeros on the main cardioid of the Mandelbrot set

For a nontrivial zero ρ of the Riemann zeta function put c = (1 - 1/ρ^2)/4 and
μ = 1 - 1/ρ. Under the Riemann hypothesis, ‖μ‖ = 1 and c = μ/2 - μ^2/4, which
is the standard parametrisation of the boundary of the main cardioid of the
Mandelbrot set. Equivalently, z ↦ z^2 + c has a neutral fixed point at μ/2.
-/

namespace Slopollary

/-- A complex number with real part 1/2 is nonzero. -/
theorem ne_zero_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) : ρ ≠ 0 := by
  intro h0
  rw [h0] at h
  norm_num at h

/-- On the critical line, ρ is equidistant from 0 and 1. -/
theorem norm_sub_one_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) : ‖ρ - 1‖ = ‖ρ‖ := by
  have h2 : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, h]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- The multiplier μ = 1 - 1/ρ has modulus one on the critical line. -/
theorem norm_multiplier_of_re_half (ρ : ℂ) (h : ρ.re = 1 / 2) : ‖1 - 1 / ρ‖ = 1 := by
  have hρ : ρ ≠ 0 := ne_zero_of_re_half ρ h
  have e : 1 - 1 / ρ = (ρ - 1) / ρ := by
    rw [sub_div, div_self hρ]
  rw [e, norm_div, norm_sub_one_of_re_half ρ h]
  exact div_self (norm_ne_zero_iff.mpr hρ)

/-- The cardioid parametrisation identity (pure algebra, valid for every ρ). -/
theorem cardioid_param (ρ : ℂ) :
    (1 - 1 / ρ ^ 2) / 4 = (1 - 1 / ρ) / 2 - (1 - 1 / ρ) ^ 2 / 4 := by
  ring

/-- The fixed point equation z₀^2 + c = z₀ (pure algebra). -/
theorem fixed_point_eq (ρ : ℂ) :
    ((1 - 1 / ρ) / 2) ^ 2 + (1 - 1 / ρ ^ 2) / 4 = (1 - 1 / ρ) / 2 := by
  ring

/-- **Slopollary 2 (cardioid form).** Assume the Riemann hypothesis. For every
nontrivial zero ρ, the parameter c = (1 - 1/ρ^2)/4 lies on the boundary of the
main cardioid of the Mandelbrot set: c = μ/2 - μ^2/4 with ‖μ‖ = 1. -/
theorem mandelbrot_cardioid_slopollary (RH : RiemannHypothesis) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ (1 - 1 / ρ ^ 2) / 4 = μ / 2 - μ ^ 2 / 4 := by
  have h : ρ.re = 1 / 2 := RH ρ hζ htriv h1
  exact ⟨1 - 1 / ρ, norm_multiplier_of_re_half ρ h, cardioid_param ρ⟩

/-- **Slopollary 2 (dynamical form).** Assume the Riemann hypothesis. For every
nontrivial zero ρ, the map z ↦ z^2 + c with c = (1 - 1/ρ^2)/4 has the neutral
fixed point z₀ = (1 - 1/ρ)/2: it is fixed, and the derivative 2 z₀ has modulus one. -/
theorem neutral_fixed_point_slopollary (RH : RiemannHypothesis) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1) :
    ((1 - 1 / ρ) / 2) ^ 2 + (1 - 1 / ρ ^ 2) / 4 = (1 - 1 / ρ) / 2 ∧
      ‖2 * ((1 - 1 / ρ) / 2)‖ = 1 := by
  have h : ρ.re = 1 / 2 := RH ρ hζ htriv h1
  refine ⟨fixed_point_eq ρ, ?_⟩
  have e : 2 * ((1 - 1 / ρ) / 2) = 1 - 1 / ρ := by ring
  rw [e]
  exact norm_multiplier_of_re_half ρ h

/-- **Converse (pointwise).** If c = (1 - 1/ρ^2)/4 lies on the main cardioid,
ρ ≠ 0 and Re ρ ≠ -1/2, then Re ρ = 1/2. -/
theorem re_half_of_on_cardioid (ρ : ℂ) (hρ : ρ ≠ 0) (hneg : ρ.re ≠ -1 / 2)
    (μ : ℂ) (hμ : ‖μ‖ = 1) (hc : (1 - 1 / ρ ^ 2) / 4 = μ / 2 - μ ^ 2 / 4) :
    ρ.re = 1 / 2 := by
  have hinv : ρ ^ 2 * (1 / ρ ^ 2) = 1 := mul_one_div_cancel (pow_ne_zero 2 hρ)
  have hsq : (ρ * (1 - μ)) ^ 2 = 1 := by
    linear_combination 4 * ρ ^ 2 * hc + hinv
  have hfac : (ρ * (1 - μ) - 1) * (ρ * (1 - μ) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · have e : ρ - 1 = ρ * μ := by linear_combination hcase
    have hn : ‖ρ - 1‖ = ‖ρ‖ := by rw [e, norm_mul, hμ, mul_one]
    have hs : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [hn]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hs
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hs
    nlinarith [hs]
  · have e : ρ + 1 = ρ * μ := by linear_combination hcase
    have hn : ‖ρ + 1‖ = ‖ρ‖ := by rw [e, norm_mul, hμ, mul_one]
    have hs : ‖ρ + 1‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [hn]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hs
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at hs
    exact absurd (by nlinarith [hs]) hneg

/-- A nontrivial zero of ζ has positive real part (from Mathlib's description of the
zeros in the closed left half-plane). -/
theorem nontrivial_zero_re_pos {s : ℂ} (hζ : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra h
  exact htriv ((riemannZeta_eq_zero_iff_of_re_nonpos (not_lt.mp h)).mp hζ)

/-- **Equivalence.** The Riemann hypothesis holds if and only if, for every nontrivial
zero ρ, the parameter c = (1 - 1/ρ^2)/4 lies on the main cardioid. -/
theorem mandelbrot_iff :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
        ∃ μ : ℂ, ‖μ‖ = 1 ∧ (1 - 1 / ρ ^ 2) / 4 = μ / 2 - μ ^ 2 / 4 := by
  constructor
  · intro RH ρ hζ ht h1
    exact mandelbrot_cardioid_slopollary RH ρ hζ ht h1
  · intro H ρ hζ ht h1
    obtain ⟨μ, hμ, hc⟩ := H ρ hζ ht h1
    have hpos : 0 < ρ.re := nontrivial_zero_re_pos hζ ht
    have hρ : ρ ≠ 0 := by
      intro h0
      rw [h0] at hpos
      simp at hpos
    have hneg : ρ.re ≠ -1 / 2 := by
      intro h
      linarith
    exact re_half_of_on_cardioid ρ hρ hneg μ hμ hc

end Slopollary

#print axioms Slopollary.mandelbrot_iff
#print axioms Slopollary.mandelbrot_cardioid_slopollary
#print axioms Slopollary.neutral_fixed_point_slopollary
#print axioms Slopollary.re_half_of_on_cardioid
