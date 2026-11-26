import Mathlib

open Filter Topology

namespace Slopollary

def powSeq {ι : Type*} (u : ι → ℂ) (n : ℕ) : ι → ℂ := fun j => u j ^ n

theorem exists_pow_near_one {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ 0 < n ∧ ∀ j, ‖u j ^ n - 1‖ < ε := by
  have hx : ∀ n, powSeq u n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simp [powSeq, hu j]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hx
  have hc : CauchySeq (powSeq u ∘ φ) := hlim.cauchySeq
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.mp hc ε hε
  obtain ⟨i, hi_def⟩ : ∃ i, i = φ M + N + 1 := ⟨_, rfl⟩
  have h1 : M ≤ φ M := hφ.id_le M
  have h2 : i ≤ φ i := hφ.id_le i
  have hi : M ≤ i := by omega
  refine ⟨φ i - φ M, by omega, by omega, fun j => ?_⟩
  have hd := hM i hi
  have hj : dist ((powSeq u ∘ φ) i j) ((powSeq u ∘ φ) M j) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ j) hd
  have hsplit : u j ^ (φ i) = u j ^ (φ M) * u j ^ (φ i - φ M) := by
    rw [← pow_add]
    congr 1
    omega
  have key : (powSeq u ∘ φ) i j - (powSeq u ∘ φ) M j
      = u j ^ (φ M) * (u j ^ (φ i - φ M) - 1) := by
    simp only [Function.comp_apply, powSeq]
    rw [hsplit]
    ring
  rw [dist_eq_norm, key, norm_mul, norm_pow, hu j, one_pow, one_mul] at hj
  exact hj

theorem re_le_norm' (z : ℂ) : z.re ≤ ‖z‖ := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z, mul_self_nonneg z.im]

theorem neg_half_lt_re_of_norm_lt (z : ℂ) (hz : ‖z‖ < 1 / 2) : -1 / 2 < z.re := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z, mul_self_nonneg z.im,
    mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz.le)]

theorem exists_neg_li_sum {ι : Type*} [Fintype ι] (μ : ι → ℂ) (j₀ : ι) (h₀ : 1 < ‖μ j₀‖) :
    ∃ n : ℕ, 0 < n ∧ ∑ j, (1 - μ j ^ n).re < 0 := by
  obtain ⟨w, hw_def⟩ : ∃ w : ι → ℂ, w = fun j => if μ j = 0 then 1 else μ j / (‖μ j‖ : ℂ) :=
    ⟨_, rfl⟩
  have hw : ∀ j, ‖w j‖ = 1 := by
    intro j
    by_cases h : μ j = 0
    · simp [hw_def, h]
    · have hn : ‖μ j‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp [hw_def, h, hn]
  have hμw : ∀ j, μ j = (‖μ j‖ : ℂ) * w j := by
    intro j
    by_cases h : μ j = 0
    · simp [hw_def, h]
    · have hn : (‖μ j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      simp only [hw_def, if_neg h]
      field_simp
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * (Fintype.card ι : ℝ)) h₀
  obtain ⟨n, hNn, hn0, hn⟩ := exists_pow_near_one w hw (by norm_num : (0 : ℝ) < 1 / 2) N
  refine ⟨n, hn0, ?_⟩
  have hre : ∀ j, ‖μ j‖ ^ n / 2 ≤ (μ j ^ n).re := by
    intro j
    have h3 : (w j ^ n - 1).re = (w j ^ n).re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    have h1 : 1 / 2 ≤ (w j ^ n).re := by
      have := neg_half_lt_re_of_norm_lt _ (hn j)
      linarith
    have h4 : μ j ^ n = ((‖μ j‖ ^ n : ℝ) : ℂ) * w j ^ n := by
      rw [Complex.ofReal_pow, ← mul_pow, ← hμw j]
    rw [h4, Complex.re_ofReal_mul]
    have hp : 0 ≤ ‖μ j‖ ^ n := by positivity
    have := mul_le_mul_of_nonneg_left h1 hp
    linarith
  have hterm : ∀ j, (1 - μ j ^ n).re ≤ 1 - ‖μ j‖ ^ n / 2 := by
    intro j
    rw [Complex.sub_re, Complex.one_re]
    linarith [hre j]
  have hsum : ‖μ j₀‖ ^ n ≤ ∑ j, ‖μ j‖ ^ n :=
    Finset.single_le_sum (f := fun j => ‖μ j‖ ^ n) (fun j _ => by positivity)
      (Finset.mem_univ j₀)
  have hpow : ‖μ j₀‖ ^ N ≤ ‖μ j₀‖ ^ n := pow_le_pow_right₀ h₀.le hNn
  have hcalc : ∑ j, (1 - μ j ^ n).re ≤ (Fintype.card ι : ℝ) - (∑ j, ‖μ j‖ ^ n) / 2 := by
    calc ∑ j, (1 - μ j ^ n).re ≤ ∑ j, (1 - ‖μ j‖ ^ n / 2) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (Fintype.card ι : ℝ) - (∑ j, ‖μ j‖ ^ n) / 2 := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div]
          simp
  linarith

theorem finite_li_criterion {ι : Type*} [Fintype ι] (μ : ι → ℂ) :
    (∀ n : ℕ, 0 < n → 0 ≤ ∑ j, (1 - μ j ^ n).re) ↔ ∀ j, ‖μ j‖ ≤ 1 := by
  constructor
  · intro h j
    by_contra hj
    obtain ⟨n, hn, hneg⟩ := exists_neg_li_sum μ j (not_le.mp hj)
    exact absurd (h n hn) (not_le.mpr hneg)
  · intro h n _
    apply Finset.sum_nonneg
    intro j _
    rw [Complex.sub_re, Complex.one_re]
    have h1 : (μ j ^ n).re ≤ ‖μ j ^ n‖ := re_le_norm' _
    have h2 : ‖μ j ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (h j)
    linarith

theorem norm_sub_one_le_iff (s : ℂ) : ‖s - 1‖ ≤ ‖s‖ ↔ 1 / 2 ≤ s.re := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

theorem norm_one_sub_inv_le_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖1 - 1 / s‖ ≤ 1 ↔ 1 / 2 ≤ s.re := by
  have e : 1 - 1 / s = (s - 1) / s := by rw [sub_div, div_self hs]
  rw [e, norm_div, div_le_one (norm_pos_iff.mpr hs)]
  exact norm_sub_one_le_iff s

theorem finite_li_criterion_half_plane {ι : Type*} [Fintype ι] (s : ι → ℂ)
    (hs : ∀ j, s j ≠ 0) :
    (∀ n : ℕ, 0 < n → 0 ≤ ∑ j, (1 - (1 - 1 / s j) ^ n).re) ↔ ∀ j, 1 / 2 ≤ (s j).re :=
  (finite_li_criterion (fun j => 1 - 1 / s j)).trans
    (forall_congr' (fun j => norm_one_sub_inv_le_one_iff (hs j)))

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
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
    exact (div_eq_zero_iff.mp h.symm).resolve_right hΓ
  rw [riemannZeta_def_of_ne_zero hs1, completedRiemannZeta_one_sub, hΛ, zero_div]

def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

theorem isNontrivialZero_one_sub {ρ : ℂ} (h : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - ρ) := by
  obtain ⟨hζ, ht, -⟩ := h
  have hpos := nontrivial_zero_re_pos hζ ht
  have hlt := zero_re_lt_one hζ
  refine ⟨zeta_one_sub_eq_zero hζ hpos hlt, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := one_sub_re ρ
    rw [hn, trivial_zero_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h1
    have hre := one_sub_re ρ
    rw [h1, Complex.one_re] at hre
    linarith

theorem li_term_nonneg_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    (∀ n : ℕ, 0 < n → 0 ≤ (1 - (1 - 1 / ρ) ^ n).re) ↔ 1 / 2 ≤ ρ.re := by
  have h := finite_li_criterion_half_plane (ι := Unit) (fun _ => ρ) (fun _ => hρ)
  simpa using h

theorem riemannHypothesis_iff_finite_li_sums_nonneg :
    RiemannHypothesis ↔
      ∀ Z : Finset ℂ, (∀ ρ ∈ Z, IsNontrivialZero ρ) →
        ∀ n : ℕ, 0 < n → 0 ≤ ∑ ρ ∈ Z, (1 - (1 - 1 / ρ) ^ n).re := by
  constructor
  · intro RH Z hZ n hn
    apply Finset.sum_nonneg
    intro ρ hρ
    obtain ⟨hζ, ht, h1⟩ := hZ ρ hρ
    have hre : ρ.re = 1 / 2 := RH ρ hζ ht h1
    have hρ0 : ρ ≠ 0 := ne_zero_of_re_pos (by rw [hre]; norm_num)
    exact (li_term_nonneg_iff hρ0).mpr hre.ge n hn
  · intro H
    have key : ∀ ρ : ℂ, IsNontrivialZero ρ → 1 / 2 ≤ ρ.re := by
      intro ρ hρ
      have hρ0 : ρ ≠ 0 := ne_zero_of_re_pos (nontrivial_zero_re_pos hρ.1 hρ.2.1)
      apply (li_term_nonneg_iff hρ0).mp
      intro n hn
      have hH := H {ρ} (by
        intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact hρ) n hn
      rwa [Finset.sum_singleton] at hH
    intro ρ hζ ht h1
    have hρ : IsNontrivialZero ρ := ⟨hζ, ht, h1⟩
    have h1' := key ρ hρ
    have h2' := key (1 - ρ) (isNontrivialZero_one_sub hρ)
    rw [one_sub_re] at h2'
    linarith

end Slopollary

#print axioms Slopollary.finite_li_criterion
#print axioms Slopollary.finite_li_criterion_half_plane
#print axioms Slopollary.riemannHypothesis_iff_finite_li_sums_nonneg
