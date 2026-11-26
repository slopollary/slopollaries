import Mathlib

/-!
# Slopollary 3: the Mandelbrot dictionary for the Riemann hypothesis

For s ≠ 0 put c(s) = (1 - 1/s^2)/4. The quadratic map z ↦ z^2 + c(s) has a fixed point
with multiplier μ = 1 - 1/s, whose holomorphic index 1/(1 - μ) is s itself. So:

* the half-plane Re s > 1/2 is sent onto the open main cardioid of the Mandelbrot set
  (the parameters with an attracting fixed point), the critical line onto its boundary,
  and the pole s = 1 to the centre c = 0;
* the Riemann hypothesis holds if and only if no nontrivial zero of ζ lands inside the
  main cardioid, and if and only if every nontrivial zero lands on its boundary;
* vertical lines Re s = t/2 go to copies of the cardioid scaled about its cusp by 1/t^2, so
  the classical zero-free region Re s ≥ 1 is the quarter-size cardioid;
* the Riemann hypothesis holds if and only if ζ(1/(1 - μ)) ≠ 0 for every μ in the open
  unit disc, that is, ζ never vanishes at the holomorphic index of an attracting fixed point.

Everything is proved against Mathlib's `RiemannHypothesis`.
-/

open Complex

namespace Slopollary

/-- The quadratic map z ↦ z^2 + c has an attracting fixed point: a fixed point at which
the derivative has modulus less than one. The set of such c is the open main cardioid. -/
def HasAttractingFixedPoint (c : ℂ) : Prop :=
  ∃ z : ℂ, z ^ 2 + c = z ∧ ‖deriv (fun w : ℂ => w ^ 2 + c) z‖ < 1

/-- The parameter attached to a point s of the zeta plane. -/
noncomputable def cardioidParam (s : ℂ) : ℂ := (1 - 1 / s ^ 2) / 4

theorem deriv_quadratic (c z : ℂ) : deriv (fun w : ℂ => w ^ 2 + c) z = 2 * z := by
  have h : HasDerivAt (fun w : ℂ => w ^ 2 + c) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).add_const c
  exact h.deriv

/-- The open main cardioid is the image of the open unit disc under μ ↦ μ/2 - μ^2/4. -/
theorem hasAttractingFixedPoint_iff (c : ℂ) :
    HasAttractingFixedPoint c ↔ ∃ μ : ℂ, ‖μ‖ < 1 ∧ c = μ / 2 - μ ^ 2 / 4 := by
  constructor
  · rintro ⟨z, hz, hd⟩
    rw [deriv_quadratic] at hd
    exact ⟨2 * z, hd, by linear_combination hz⟩
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ / 2, by ring, ?_⟩
    rw [deriv_quadratic]
    have e : 2 * (μ / 2) = μ := by ring
    rw [e]
    exact hμ

theorem norm_sub_one_lt_iff (s : ℂ) : ‖s - 1‖ < ‖s‖ ↔ 1 / 2 < s.re := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

theorem norm_add_one_lt_iff (s : ℂ) : ‖s + 1‖ < ‖s‖ ↔ s.re < -1 / 2 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

/-- The multiplier μ = 1 - 1/s lies in the open unit disc exactly when Re s > 1/2. -/
theorem norm_one_sub_inv_lt_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖1 - 1 / s‖ < 1 ↔ 1 / 2 < s.re := by
  have e : 1 - 1 / s = (s - 1) / s := by rw [sub_div, div_self hs]
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hs)]
  exact norm_sub_one_lt_iff s

theorem norm_one_add_inv_lt_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖1 + 1 / s‖ < 1 ↔ s.re < -1 / 2 := by
  have e : 1 + 1 / s = (s + 1) / s := by rw [add_div, div_self hs]
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hs)]
  exact norm_add_one_lt_iff s

/-- **Dictionary.** c(s) lies in the open main cardioid exactly when Re s > 1/2 or
Re s < -1/2 (the second case because c(s) = c(-s)). -/
theorem attracting_cardioidParam_iff {s : ℂ} (hs : s ≠ 0) :
    HasAttractingFixedPoint (cardioidParam s) ↔ 1 / 2 < s.re ∨ s.re < -1 / 2 := by
  rw [hasAttractingFixedPoint_iff]
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  constructor
  · rintro ⟨μ, hμ, hc⟩
    unfold cardioidParam at hc
    have hinv : s ^ 2 * (1 / s ^ 2) = 1 := mul_one_div_cancel (pow_ne_zero 2 hs)
    have hsq : (s * (1 - μ)) ^ 2 = 1 := by
      linear_combination 4 * s ^ 2 * hc + hinv
    have hfac : (s * (1 - μ) - 1) * (s * (1 - μ) + 1) = 0 := by
      linear_combination hsq
    have hmul : ‖s‖ * ‖μ‖ < ‖s‖ * 1 := mul_lt_mul_of_pos_left hμ hpos
    rcases mul_eq_zero.mp hfac with hcase | hcase
    · left
      have e : s - 1 = s * μ := by linear_combination hcase
      have hn : ‖s - 1‖ < ‖s‖ := by
        rw [e, norm_mul]
        linarith
      exact (norm_sub_one_lt_iff s).mp hn
    · right
      have e : s + 1 = s * μ := by linear_combination hcase
      have hn : ‖s + 1‖ < ‖s‖ := by
        rw [e, norm_mul]
        linarith
      exact (norm_add_one_lt_iff s).mp hn
  · rintro (h | h)
    · exact ⟨1 - 1 / s, (norm_one_sub_inv_lt_one_iff hs).mpr h, by unfold cardioidParam; ring⟩
    · exact ⟨1 + 1 / s, (norm_one_add_inv_lt_one_iff hs).mpr h, by unfold cardioidParam; ring⟩

/-- The pole of ζ goes to the centre of the Mandelbrot set. -/
theorem cardioidParam_one : cardioidParam 1 = 0 := by
  unfold cardioidParam
  norm_num

theorem trivial_zero_re (n : ℕ) : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
  simp

theorem one_sub_re (s : ℂ) : (1 - s).re = 1 - s.re := by
  simp

theorem nontrivial_zero_re_pos {s : ℂ} (hζ : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra h
  exact htriv ((riemannZeta_eq_zero_iff_of_re_nonpos (not_lt.mp h)).mp hζ)

theorem zero_re_lt_one {s : ℂ} (hζ : riemannZeta s = 0) : s.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ

theorem ne_zero_of_re_pos {s : ℂ} (h : 0 < s.re) : s ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h

/-- Zeros in the critical strip come in pairs s, 1 - s (functional equation). -/
theorem zeta_one_sub_eq_zero {s : ℂ} (hζ : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) : riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    apply ne_zero_of_re_pos
    rw [one_sub_re]
    linarith
  have hΛ : completedRiemannZeta s = 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [hζ] at h
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
    exact (div_eq_zero_iff.mp h.symm).resolve_right hΓ
  rw [riemannZeta_def_of_ne_zero hs1, completedRiemannZeta_one_sub, hΛ, zero_div]

/-- If ζ has no zeros with Re s > 1/2, every nontrivial zero has Re = 1/2. -/
theorem re_eq_half_of_forall
    (hP : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re ≤ 1 / 2)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (ht : ¬∃ n : ℕ, ρ = -2 * (n + 1)) :
    ρ.re = 1 / 2 := by
  have hpos := nontrivial_zero_re_pos hζ ht
  have hlt := zero_re_lt_one hζ
  have h1 := hP ρ hζ hpos
  have h2 := hP (1 - ρ) (zeta_one_sub_eq_zero hζ hpos hlt) (by rw [one_sub_re]; linarith)
  rw [one_sub_re] at h2
  linarith

/-- **Index form.** The Riemann hypothesis holds if and only if ζ(1/(1 - μ)) ≠ 0 for every
μ in the open unit disc: ζ never vanishes at the holomorphic index of an attracting
fixed point. -/
theorem riemannHypothesis_iff_zero_free_at_attracting_index :
    RiemannHypothesis ↔ ∀ μ : ℂ, ‖μ‖ < 1 → riemannZeta (1 / (1 - μ)) ≠ 0 := by
  constructor
  · intro RH μ hμ hζ
    have hμ1 : (1 : ℂ) - μ ≠ 0 := by
      intro h
      have hμe : μ = 1 := by linear_combination -h
      rw [hμe] at hμ
      simp at hμ
    have hs0 : (1 / (1 - μ) : ℂ) ≠ 0 := one_div_ne_zero hμ1
    have e : 1 - 1 / (1 / (1 - μ)) = μ := by
      rw [one_div_one_div]
      ring
    have hre : 1 / 2 < (1 / (1 - μ)).re := by
      apply (norm_one_sub_inv_lt_one_iff hs0).mp
      rw [e]
      exact hμ
    have ht : ¬∃ n : ℕ, 1 / (1 - μ) = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      rw [hn, trivial_zero_re] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h1 : 1 / (1 - μ) ≠ 1 := by
      intro h
      rw [h] at hζ
      exact riemannZeta_one_ne_zero hζ
    have hhalf := RH _ hζ ht h1
    linarith
  · intro H ρ hζ ht _
    refine re_eq_half_of_forall ?_ hζ ht
    intro s hs hsp
    by_contra hcon
    have hs0 : s ≠ 0 := ne_zero_of_re_pos hsp
    have hμ : ‖1 - 1 / s‖ < 1 := (norm_one_sub_inv_lt_one_iff hs0).mpr (not_le.mp hcon)
    have e : 1 / (1 - (1 - 1 / s)) = s := by
      rw [sub_sub_cancel, one_div_one_div]
    exact H (1 - 1 / s) hμ (by rw [e]; exact hs)

/-- **Mandelbrot form.** The Riemann hypothesis holds if and only if no nontrivial zero of ζ
is sent inside the main cardioid of the Mandelbrot set. -/
theorem riemannHypothesis_iff_no_zero_inside_cardioid :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
        ¬HasAttractingFixedPoint (cardioidParam ρ) := by
  constructor
  · intro RH ρ hζ ht h1 hatt
    have h : ρ.re = 1 / 2 := RH ρ hζ ht h1
    have hρ : ρ ≠ 0 := ne_zero_of_re_pos (by rw [h]; norm_num)
    rcases (attracting_cardioidParam_iff hρ).mp hatt with h' | h' <;> linarith
  · intro H
    have key : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re ≤ 1 / 2 := by
      intro s hs hsp
      by_contra hcon
      have hs0 : s ≠ 0 := ne_zero_of_re_pos hsp
      have hst : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        rw [hn, trivial_zero_re] at hsp
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at hs
        exact riemannZeta_one_ne_zero hs
      exact H s hs hst hs1
        ((attracting_cardioidParam_iff hs0).mpr (Or.inl (not_le.mp hcon)))
    intro ρ hζ ht _
    exact re_eq_half_of_forall key hζ ht

/-- The quadratic map z ↦ z^2 + c has a neutral fixed point: a fixed point at which the
derivative has modulus exactly one. The set of such c is the boundary of the main cardioid. -/
def HasNeutralFixedPoint (c : ℂ) : Prop :=
  ∃ z : ℂ, z ^ 2 + c = z ∧ ‖deriv (fun w : ℂ => w ^ 2 + c) z‖ = 1

theorem hasNeutralFixedPoint_iff (c : ℂ) :
    HasNeutralFixedPoint c ↔ ∃ μ : ℂ, ‖μ‖ = 1 ∧ c = μ / 2 - μ ^ 2 / 4 := by
  constructor
  · rintro ⟨z, hz, hd⟩
    rw [deriv_quadratic] at hd
    exact ⟨2 * z, hd, by linear_combination hz⟩
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ / 2, by ring, ?_⟩
    rw [deriv_quadratic]
    have e : 2 * (μ / 2) = μ := by ring
    rw [e]
    exact hμ

theorem norm_sub_one_eq_iff (s : ℂ) : ‖s - 1‖ = ‖s‖ ↔ s.re = 1 / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

theorem norm_add_one_eq_iff (s : ℂ) : ‖s + 1‖ = ‖s‖ ↔ s.re = -1 / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

/-- c(s) lies on the boundary of the main cardioid exactly when Re s = 1/2 or Re s = -1/2. -/
theorem neutral_cardioidParam_iff {s : ℂ} (hs : s ≠ 0) :
    HasNeutralFixedPoint (cardioidParam s) ↔ s.re = 1 / 2 ∨ s.re = -1 / 2 := by
  rw [hasNeutralFixedPoint_iff]
  constructor
  · rintro ⟨μ, hμ, hc⟩
    unfold cardioidParam at hc
    have hinv : s ^ 2 * (1 / s ^ 2) = 1 := mul_one_div_cancel (pow_ne_zero 2 hs)
    have hsq : (s * (1 - μ)) ^ 2 = 1 := by
      linear_combination 4 * s ^ 2 * hc + hinv
    have hfac : (s * (1 - μ) - 1) * (s * (1 - μ) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with hcase | hcase
    · left
      have e : s - 1 = s * μ := by linear_combination hcase
      have hn : ‖s - 1‖ = ‖s‖ := by rw [e, norm_mul, hμ, mul_one]
      exact (norm_sub_one_eq_iff s).mp hn
    · right
      have e : s + 1 = s * μ := by linear_combination hcase
      have hn : ‖s + 1‖ = ‖s‖ := by rw [e, norm_mul, hμ, mul_one]
      exact (norm_add_one_eq_iff s).mp hn
  · rintro (h | h)
    · refine ⟨1 - 1 / s, ?_, by unfold cardioidParam; ring⟩
      have e : 1 - 1 / s = (s - 1) / s := by rw [sub_div, div_self hs]
      rw [e, norm_div, (norm_sub_one_eq_iff s).mpr h]
      exact div_self (norm_ne_zero_iff.mpr hs)
    · refine ⟨1 + 1 / s, ?_, by unfold cardioidParam; ring⟩
      have e : 1 + 1 / s = (s + 1) / s := by rw [add_div, div_self hs]
      rw [e, norm_div, (norm_add_one_eq_iff s).mpr h]
      exact div_self (norm_ne_zero_iff.mpr hs)

/-- **The dictionary.** On the right half-plane Re s > 0: c(s) is inside the main cardioid
exactly when s is right of the critical line, and on its boundary exactly when s is on the
critical line. -/
theorem dictionary {s : ℂ} (hs : 0 < s.re) :
    (HasAttractingFixedPoint (cardioidParam s) ↔ 1 / 2 < s.re) ∧
    (HasNeutralFixedPoint (cardioidParam s) ↔ s.re = 1 / 2) := by
  have hs0 := ne_zero_of_re_pos hs
  constructor
  · rw [attracting_cardioidParam_iff hs0]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · intro h
      exact Or.inl h
  · rw [neutral_cardioidParam_iff hs0]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · intro h
      exact Or.inl h

/-- **Boundary form.** The Riemann hypothesis holds if and only if every nontrivial zero of ζ
is sent to the boundary of the main cardioid. -/
theorem riemannHypothesis_iff_neutral :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
        HasNeutralFixedPoint (cardioidParam ρ) := by
  constructor
  · intro RH ρ hζ ht h1
    have h : ρ.re = 1 / 2 := RH ρ hζ ht h1
    have hpos : 0 < ρ.re := by rw [h]; norm_num
    exact (dictionary hpos).2.mpr h
  · intro H ρ hζ ht h1
    exact (dictionary (nontrivial_zero_re_pos hζ ht)).2.mp (H ρ hζ ht h1)

/-- Scaling the zeta variable by a real t scales the cardioid about its cusp 1/4 by t^2. -/
theorem cardioidParam_div_ofReal {s : ℂ} {t : ℝ} :
    cardioidParam (s / (t : ℂ)) = 1 / 4 + (t : ℂ) ^ 2 * (cardioidParam s - 1 / 4) := by
  unfold cardioidParam
  have h1 : 1 / (s / (t : ℂ)) ^ 2 = (t : ℂ) ^ 2 / s ^ 2 := by rw [div_pow, one_div_div]
  rw [h1]
  ring

/-- **Vertical lines are scaled cardioids.** For t > 0, the half-plane Re s > t/2 corresponds
to the main cardioid shrunk about its cusp by the factor 1/t^2: the point c(s) lies in that
smaller cardioid exactly when its t^2-fold enlargement about the cusp lies in the main one. -/
theorem attracting_scaled_iff {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasAttractingFixedPoint (1 / 4 + (t : ℂ) ^ 2 * (cardioidParam s - 1 / 4)) ↔
      t / 2 < s.re ∨ s.re < -t / 2 := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hst : s / (t : ℂ) ≠ 0 := div_ne_zero hs ht'
  rw [← cardioidParam_div_ofReal, attracting_cardioidParam_iff hst, Complex.div_ofReal_re,
    lt_div_iff₀ ht, div_lt_iff₀ ht]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- **The classical zero-free region is the quarter-size cardioid.** Unconditionally, no zero
of ζ with positive real part is sent into the copy of the main cardioid shrunk about its cusp
by the factor 1/4 (this is the non-vanishing of ζ on Re s ≥ 1). -/
theorem no_zero_in_quarter_cardioid {s : ℂ} (hζ : riemannZeta s = 0) (hs : 0 < s.re) :
    ¬HasAttractingFixedPoint (1 / 4 + ((2 : ℝ) : ℂ) ^ 2 * (cardioidParam s - 1 / 4)) := by
  intro h
  rcases (attracting_scaled_iff (ne_zero_of_re_pos hs) (by norm_num : (0 : ℝ) < 2)).mp h
    with h' | h'
  · have h1 : 1 ≤ s.re := by linarith
    exact riemannZeta_ne_zero_of_one_le_re h1 hζ
  · linarith

/-- The trivial zeros are sent to the points 1/4 - 1/(16 (n+1)^2) on the real axis, inside
the main cardioid, marching into the cusp. -/
theorem cardioidParam_trivial_zero (n : ℕ) :
    cardioidParam (-2 * ((n : ℂ) + 1)) = 1 / 4 - 1 / (16 * ((n : ℂ) + 1) ^ 2) := by
  have h : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  unfold cardioidParam
  field_simp
  ring

end Slopollary

#print axioms Slopollary.riemannHypothesis_iff_zero_free_at_attracting_index
#print axioms Slopollary.riemannHypothesis_iff_no_zero_inside_cardioid
#print axioms Slopollary.attracting_cardioidParam_iff
#print axioms Slopollary.dictionary
#print axioms Slopollary.riemannHypothesis_iff_neutral
#print axioms Slopollary.attracting_scaled_iff
#print axioms Slopollary.no_zero_in_quarter_cardioid
#print axioms Slopollary.cardioidParam_trivial_zero
