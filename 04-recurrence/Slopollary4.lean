import Mathlib

/-!
# Slopollary 4: which exponents does Li's criterion need?

Li's criterion (in the Bombieri-Lagarias form) says: a family of complex numbers μ lies in
the closed unit disc if and only if the sums Σ Re(1 - μ^n) are nonnegative for every n ≥ 1.
For the points μ = 1 - 1/ρ attached to the zeros of ζ this is the Riemann hypothesis.

Here we ask which sets S of exponents are enough. For finite families the answer is exact:

  the criterion works along S  ⟺  S is a set of Bohr recurrence,

where S is a set of Bohr recurrence if for any finitely many points u on the unit circle
and any ε > 0 some n > 0 in S has every u^n within ε of 1.

* `liAlong_of_bohrRecurrent`: recurrence makes all the phases line up while the largest
  modulus blows up, so a point outside the disc is detected.
* `not_liAlong_of_not_recurrent`: if S avoids a Bohr neighbourhood of 0, a
  de la Vallée-Poussin kernel with its constant term removed gives finitely many points of
  modulus 2 that the criterion along S cannot see.

Consequences: the multiples of any m ≥ 1 are enough; the primes are not (the single point
2i passes every prime test); and for a set of Bohr recurrence S the Riemann hypothesis is
equivalent to nonnegativity of all finite partial Li sums over zeros with exponents in S.
-/

open Filter Topology ComplexConjugate

namespace Slopollary

/-- `S` is a set of Bohr recurrence: every finite family of rotations of the circle returns
simultaneously close to the identity at some positive time in `S`. -/
def BohrRecurrent (S : Set ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (u : κ → ℂ), (∀ j, ‖u j‖ = 1) → ∀ ε : ℝ, 0 < ε →
    ∃ n ∈ S, 0 < n ∧ ∀ j, ‖u j ^ n - 1‖ < ε

/-- The finite Li criterion works along `S`: nonnegativity of the Li sums for the exponents
in `S` forces every point of every finite family into the closed unit disc. (The converse
implication holds for every `S`; see `li_sum_nonneg`.) -/
def LiAlong (S : Set ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : ι → ℂ),
    (∀ n ∈ S, 0 ≤ ∑ j, (1 - μ j ^ n).re) → ∀ j, ‖μ j‖ ≤ 1

/-! ## Elementary facts about complex numbers -/

theorem re_le_norm' (z : ℂ) : z.re ≤ ‖z‖ := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z, mul_self_nonneg z.im]

theorem neg_half_lt_re_of_norm_lt (z : ℂ) (hz : ‖z‖ < 1 / 2) : -1 / 2 < z.re := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z, mul_self_nonneg z.im,
    mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz.le)]

theorem norm_two' : ‖(2 : ℂ)‖ = 2 := by
  have h : ((2 : ℝ) : ℂ) = 2 := by norm_num
  rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos two_pos]

theorem two_pow_mul_re (n : ℕ) (z : ℂ) : ((2 : ℂ) ^ n * z).re = 2 ^ n * z.re := by
  have h : ((2 : ℂ) ^ n) = (((2 : ℝ) ^ n : ℝ) : ℂ) := by norm_num
  rw [h, Complex.re_ofReal_mul]

theorem unit_mul_conj {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  have hns : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  rw [Complex.mul_conj, hns]
  norm_num

theorem norm_conj_of_unit {z : ℂ} (hz : ‖z‖ = 1) : ‖conj z‖ = 1 := by
  have h := congrArg norm (unit_mul_conj hz)
  rw [norm_mul, hz, one_mul, norm_one] at h
  exact h

theorem two_add_two_re {z : ℂ} (hz : ‖z‖ = 1) : 2 + 2 * z.re = 4 - ‖z - 1‖ ^ 2 := by
  have h1 := Complex.sq_norm z
  rw [Complex.normSq_apply, hz] at h1
  have h2 := Complex.sq_norm (z - 1)
  rw [Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith

theorem two_add_two_re_nonneg {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 2 + 2 * z.re := by
  have h1 := Complex.sq_norm z
  rw [Complex.normSq_apply, hz] at h1
  nlinarith [sq_nonneg (z.re + 1), mul_self_nonneg z.im]

theorem two_add_two_re_le {z : ℂ} (hz : ‖z‖ = 1) : 2 + 2 * z.re ≤ 4 := by
  rw [two_add_two_re hz]
  nlinarith [sq_nonneg ‖z - 1‖]

/-! ## Recurrence implies the criterion -/

def powSeq {ι : Type*} (u : ι → ℂ) (n : ℕ) : ι → ℂ := fun j => u j ^ n

/-- Compactness: finitely many rotations return simultaneously, at arbitrarily late times. -/
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

theorem norm_exp_I : ‖Complex.exp Complex.I‖ = 1 := by
  simpa using Complex.norm_exp_ofReal_mul_I 1

/-- The rotation by one radian never returns exactly: π is irrational. -/
theorem exp_I_pow_ne_one {n : ℕ} (hn : 0 < n) : Complex.exp Complex.I ^ n ≠ 1 := by
  intro h
  rw [← Complex.exp_natCast_mul, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have him : (n : ℝ) = (k : ℝ) * (2 * Real.pi) := by
    have h' := congrArg Complex.im hk
    simpa using h'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at him
    linarith
  have h2k : (2 * (k : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hk0
  have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by
    rw [eq_div_iff h2k, him]
    ring
  have hq : (((n : ℚ) / (2 * (k : ℚ)) : ℚ) : ℝ) = (n : ℝ) / (2 * (k : ℝ)) := by
    push_cast
    ring
  exact irrational_pi.ne_rat ((n : ℚ) / (2 * (k : ℚ))) (hpi.trans hq.symm)

theorem exists_gap (N : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 0 < n → n ≤ N →
    δ ≤ ‖Complex.exp Complex.I ^ n - 1‖ := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n h0 hn => absurd hn (by omega)⟩
  | succ N ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    have hpos : 0 < ‖Complex.exp Complex.I ^ (N + 1) - 1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (exp_I_pow_ne_one (Nat.succ_pos N)))
    refine ⟨min δ ‖Complex.exp Complex.I ^ (N + 1) - 1‖, lt_min hδ hpos, fun n h0 hn => ?_⟩
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · exact le_trans (min_le_left _ _) (h n h0 (by omega))
    · have hn' : n = N + 1 := by omega
      rw [hn']
      exact min_le_right _ _

/-- Along a set of Bohr recurrence, a point outside the unit disc makes some Li sum negative. -/
theorem exists_neg_li_sum_along {S : Set ℕ} (hS : BohrRecurrent S) {ι : Type} [Fintype ι]
    (μ : ι → ℂ) (j₀ : ι) (h₀ : 1 < ‖μ j₀‖) : ∃ n ∈ S, ∑ j, (1 - μ j ^ n).re < 0 := by
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
      simp only [hw_def, ite_eq_right h]
      field_simp
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * (Fintype.card ι : ℝ)) h₀
  obtain ⟨δ, hδ, hgap⟩ := exists_gap N
  obtain ⟨v, hv_def⟩ : ∃ v : Option ι → ℂ,
      v = fun o => Option.elim o (Complex.exp Complex.I) w := ⟨_, rfl⟩
  have hv : ∀ o, ‖v o‖ = 1 := by
    intro o
    cases o with
    | none => rw [hv_def]; exact norm_exp_I
    | some j => rw [hv_def]; exact hw j
  obtain ⟨n, hnS, hn0, hn⟩ := hS (Option ι) v hv (min δ (1 / 2)) (lt_min hδ (by norm_num))
  have hnone : ‖Complex.exp Complex.I ^ n - 1‖ < min δ (1 / 2) := by
    have h := hn none
    rw [hv_def] at h
    exact h
  have hclose : ∀ j, ‖w j ^ n - 1‖ < 1 / 2 := by
    intro j
    have h := hn (some j)
    rw [hv_def] at h
    exact lt_of_lt_of_le h (min_le_right _ _)
  have hNn : N ≤ n := by
    by_contra hlt
    have h1 := hgap n hn0 (by omega)
    have h3 := lt_of_lt_of_le hnone (min_le_left _ _)
    linarith
  refine ⟨n, hnS, ?_⟩
  have hre : ∀ j, ‖μ j‖ ^ n / 2 ≤ (μ j ^ n).re := by
    intro j
    have h3 : (w j ^ n - 1).re = (w j ^ n).re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    have h1 : 1 / 2 ≤ (w j ^ n).re := by
      have := neg_half_lt_re_of_norm_lt _ (hclose j)
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

theorem liAlong_of_bohrRecurrent {S : Set ℕ} (hS : BohrRecurrent S) : LiAlong S := by
  intro ι _ μ h j
  by_contra hj
  obtain ⟨n, hn, hneg⟩ := exists_neg_li_sum_along hS μ j (not_le.mp hj)
  exact absurd (h n hn) (not_le.mpr hneg)

/-- The easy half of the criterion, valid for every exponent. -/
theorem li_sum_nonneg {ι : Type} [Fintype ι] (μ : ι → ℂ) (h : ∀ j, ‖μ j‖ ≤ 1) (n : ℕ) :
    0 ≤ ∑ j, (1 - μ j ^ n).re := by
  apply Finset.sum_nonneg
  intro j _
  rw [Complex.sub_re, Complex.one_re]
  have h1 : (μ j ^ n).re ≤ ‖μ j ^ n‖ := re_le_norm' _
  have h2 : ‖μ j ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (h j)
  linarith

/-! ## The kernel -/

/-- Multiplicity of the frequency vector `e`: a product of binomial coefficients. -/
def mult (κ : Type) [Fintype κ] (M : ℕ) (e : κ → Fin (2 * M + 1)) : ℕ :=
  ∏ j, (2 * M).choose (e j)

/-- The frequency vector that gives the constant term. -/
def centre (κ : Type) (M : ℕ) : κ → Fin (2 * M + 1) := fun _ => ⟨M, by omega⟩

/-- The character with frequency vector `e - (M, …, M)`, evaluated at `u`. -/
noncomputable def phase {κ : Type} [Fintype κ] (M : ℕ) (u : κ → ℂ)
    (e : κ → Fin (2 * M + 1)) : ℂ :=
  ∏ j, (u j ^ (e j : ℕ) * conj (u j) ^ M)

theorem kernel_factor {z : ℂ} (hz : ‖z‖ = 1) (M : ℕ) :
    (1 + z) ^ (2 * M) * conj z ^ M = (((2 + 2 * z.re) ^ M : ℝ) : ℂ) := by
  have h1 := unit_mul_conj hz
  have h2 : z + conj z = ((2 * z.re : ℝ) : ℂ) := Complex.add_conj z
  have h3 : (1 + z) ^ 2 * conj z = ((2 + 2 * z.re : ℝ) : ℂ) := by
    push_cast
    push_cast at h2
    linear_combination (2 + z) * h1 + h2
  rw [pow_mul, ← mul_pow, h3, Complex.ofReal_pow]

theorem kernel_expand (z : ℂ) (M : ℕ) :
    ∑ e : Fin (2 * M + 1), (((2 * M).choose (e : ℕ) : ℕ) : ℂ) * (z ^ (e : ℕ) * conj z ^ M)
      = (1 + z) ^ (2 * M) * conj z ^ M := by
  rw [add_comm 1 z, add_pow, Finset.sum_mul, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro e _
  rw [one_pow]
  ring

theorem phase_pow {κ : Type} [Fintype κ] (M : ℕ) (u : κ → ℂ) (e : κ → Fin (2 * M + 1))
    (n : ℕ) : phase M u e ^ n = phase M (fun j => u j ^ n) e := by
  simp only [phase]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_pow]
  ring

theorem phase_centre {κ : Type} [Fintype κ] (M : ℕ) (u : κ → ℂ) (hu : ∀ j, ‖u j‖ = 1) :
    phase M u (centre κ M) = 1 := by
  simp only [phase]
  apply Finset.prod_eq_one
  intro j _
  have h := unit_mul_conj (hu j)
  calc u j ^ M * conj (u j) ^ M = (u j * conj (u j)) ^ M := by rw [mul_pow]
    _ = 1 := by rw [h, one_pow]

theorem norm_phase {κ : Type} [Fintype κ] (M : ℕ) (u : κ → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    (e : κ → Fin (2 * M + 1)) : ‖phase M u e‖ = 1 := by
  simp only [phase]
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro j _
  rw [norm_mul, norm_pow, norm_pow, hu j, norm_conj_of_unit (hu j), one_pow, one_pow, mul_one]

theorem mult_centre (κ : Type) [Fintype κ] (M : ℕ) :
    (mult κ M (centre κ M) : ℝ) = (Nat.centralBinom M : ℝ) ^ Fintype.card κ := by
  have h : mult κ M (centre κ M) = Nat.centralBinom M ^ Fintype.card κ := by
    show (∏ _j : κ, (2 * M).choose M) = _
    rw [Finset.prod_const, Finset.card_univ, Nat.centralBinom_eq_two_mul_choose]
  rw [h, Nat.cast_pow]

/-- The kernel identity: summing the characters with their multiplicities gives
`∏ (2 + 2 Re z_j)^M = ∏ |1 + z_j|^(2M)`. -/
theorem sum_mult_phase {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℕ) (z : κ → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ∑ e : κ → Fin (2 * M + 1), (mult κ M e : ℂ) * phase M z e
      = ((∏ j, (2 + 2 * (z j).re) ^ M : ℝ) : ℂ) := by
  calc ∑ e : κ → Fin (2 * M + 1), (mult κ M e : ℂ) * phase M z e
      = ∑ e : κ → Fin (2 * M + 1), ∏ j,
          ((((2 * M).choose (e j : ℕ) : ℕ) : ℂ) * (z j ^ (e j : ℕ) * conj (z j) ^ M)) := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [mult, phase]
        rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    _ = ∏ j, ∑ e : Fin (2 * M + 1),
          ((((2 * M).choose (e : ℕ) : ℕ) : ℂ) * (z j ^ (e : ℕ) * conj (z j) ^ M)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ((∏ j, (2 + 2 * (z j).re) ^ M : ℝ) : ℂ) := by
        rw [Complex.ofReal_prod]
        apply Finset.prod_congr rfl
        intro j _
        rw [kernel_expand, kernel_factor (hz j)]

theorem sum_mult_phase_re {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℕ) (z : κ → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ∑ e : κ → Fin (2 * M + 1), (mult κ M e : ℝ) * (phase M z e).re
      = ∏ j, (2 + 2 * (z j).re) ^ M := by
  have h := congrArg Complex.re (sum_mult_phase M z hz)
  rw [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

/-- The Li sum of the kernel family: the points `2 · phase e`, each taken `mult e` times,
with the constant term `e = centre` left out. -/
theorem family_sum {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℕ) (u : κ → ℂ)
    (hu : ∀ j, ‖u j‖ = 1) (n : ℕ) :
    ∑ x : (Σ e : κ → Fin (2 * M + 1), Fin (if e = centre κ M then 0 else mult κ M e)),
        (1 - (2 * phase M u x.1) ^ n).re
      = ((∑ e : κ → Fin (2 * M + 1), (mult κ M e : ℝ)) - (mult κ M (centre κ M) : ℝ))
        - 2 ^ n * (∏ j, (2 + 2 * (u j ^ n).re) ^ M - (mult κ M (centre κ M) : ℝ)) := by
  have hz : ∀ j, ‖u j ^ n‖ = 1 := fun j => by rw [norm_pow, hu j, one_pow]
  have hterm : ∀ e : κ → Fin (2 * M + 1),
      (1 - (2 * phase M u e) ^ n).re = 1 - 2 ^ n * (phase M (fun j => u j ^ n) e).re := by
    intro e
    rw [mul_pow, phase_pow, Complex.sub_re, Complex.one_re, two_pow_mul_re]
  have hsig : ∑ x : (Σ e : κ → Fin (2 * M + 1),
        Fin (if e = centre κ M then 0 else mult κ M e)), (1 - (2 * phase M u x.1) ^ n).re
      = ∑ e : κ → Fin (2 * M + 1), ((if e = centre κ M then 0 else mult κ M e : ℕ) : ℝ)
          * (1 - 2 ^ n * (phase M (fun j => u j ^ n) e).re) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hterm]
  have hsplit : ∀ e : κ → Fin (2 * M + 1),
      ((if e = centre κ M then 0 else mult κ M e : ℕ) : ℝ)
          * (1 - 2 ^ n * (phase M (fun j => u j ^ n) e).re)
        = ((mult κ M e : ℝ) - 2 ^ n * ((mult κ M e : ℝ) * (phase M (fun j => u j ^ n) e).re))
          - (if e = centre κ M then (mult κ M (centre κ M) : ℝ) * (1 - 2 ^ n) else 0) := by
    intro e
    by_cases h : e = centre κ M
    · rw [ite_eq_left h, ite_eq_left h, h, phase_centre M _ hz]
      simp only [Nat.cast_zero, Complex.one_re]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring
  rw [hsig, Finset.sum_congr rfl (fun e _ => hsplit e), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ← Finset.mul_sum,
    sum_mult_phase_re M _ hz]
  ring

/-- A tall enough kernel: polynomial growth loses to geometric decay. -/
theorem exists_M (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ M : ℕ, 1 ≤ M ∧ (2 * (M : ℝ) + 1) ^ d * q ^ M ≤ 1 := by
  have hq : |q| < 1 := by
    rw [abs_of_nonneg hq0]
    exact hq1
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one d hq
  have hpos : (0 : ℝ) < 1 / 3 ^ d := by positivity
  have hev := (ht.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop 1)
  obtain ⟨M, hM, hM1⟩ := hev.exists
  refine ⟨M, hM1, ?_⟩
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have h3 : (2 * (M : ℝ) + 1) ^ d ≤ (3 * (M : ℝ)) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hqM : 0 ≤ q ^ M := pow_nonneg hq0 M
  have h3d : (0 : ℝ) < 3 ^ d := by positivity
  calc (2 * (M : ℝ) + 1) ^ d * q ^ M ≤ (3 * (M : ℝ)) ^ d * q ^ M :=
        mul_le_mul_of_nonneg_right h3 hqM
    _ = 3 ^ d * ((M : ℝ) ^ d * q ^ M) := by
        rw [mul_pow]
        ring
    _ ≤ 3 ^ d * (1 / 3 ^ d) := mul_le_mul_of_nonneg_left hM.le h3d.le
    _ = 1 := by
        field_simp

theorem prod_le_prod_nonneg {κ : Type} (s : Finset κ) (f g : κ → ℝ) :
    (∀ j ∈ s, 0 ≤ f j) → (∀ j ∈ s, f j ≤ g j) → ∏ j ∈ s, f j ≤ ∏ j ∈ s, g j := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a t ha ih h0 h1
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hf : 0 ≤ ∏ j ∈ t, f j :=
      Finset.prod_nonneg (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
    have h0a := h0 a (Finset.mem_insert_self a t)
    have h1a := h1 a (Finset.mem_insert_self a t)
    have ih' := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    exact mul_le_mul h1a ih' hf (le_trans h0a h1a)

/-- Off the Bohr neighbourhood the kernel is below its own constant term. -/
theorem kernel_le {κ : Type} [Fintype κ] [DecidableEq κ] {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (hM : (2 * (M : ℝ) + 1) ^ Fintype.card κ * q ^ M ≤ 1)
    (a : κ → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha4 : ∀ j, a j ≤ 4) (j₀ : κ) (hj₀ : a j₀ ≤ 4 * q) :
    ∏ j, a j ^ M ≤ (mult κ M (centre κ M) : ℝ) := by
  have h1 : ∏ j, a j ^ M ≤ ∏ j, ((4 : ℝ) ^ M * (if j = j₀ then q ^ M else 1)) := by
    apply prod_le_prod_nonneg
    · intro j _
      exact pow_nonneg (ha0 j) M
    · intro j _
      by_cases h : j = j₀
      · rw [ite_eq_left h, h, ← mul_pow]
        exact pow_le_pow_left₀ (ha0 j₀) hj₀ M
      · rw [ite_eq_right h, mul_one]
        exact pow_le_pow_left₀ (ha0 j) (ha4 j) M
  have h2 : ∏ j : κ, ((4 : ℝ) ^ M * (if j = j₀ then q ^ M else 1))
      = ((4 : ℝ) ^ M) ^ Fintype.card κ * q ^ M := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite_eq',
      ite_eq_left (Finset.mem_univ _)]
  have hC : (4 : ℝ) ^ M ≤ (2 * (M : ℝ) + 1) * (Nat.centralBinom M : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom M
  have h3 : ((4 : ℝ) ^ M) ^ Fintype.card κ
      ≤ ((2 * (M : ℝ) + 1) * (Nat.centralBinom M : ℝ)) ^ Fintype.card κ :=
    pow_le_pow_left₀ (by positivity) hC _
  have hqM : 0 ≤ q ^ M := pow_nonneg hq0 M
  have hCd : (0 : ℝ) ≤ (Nat.centralBinom M : ℝ) ^ Fintype.card κ := by positivity
  rw [mult_centre κ M]
  calc ∏ j, a j ^ M ≤ ((4 : ℝ) ^ M) ^ Fintype.card κ * q ^ M := h1.trans_eq h2
    _ ≤ ((2 * (M : ℝ) + 1) * (Nat.centralBinom M : ℝ)) ^ Fintype.card κ * q ^ M :=
        mul_le_mul_of_nonneg_right h3 hqM
    _ = (Nat.centralBinom M : ℝ) ^ Fintype.card κ
          * ((2 * (M : ℝ) + 1) ^ Fintype.card κ * q ^ M) := by
        rw [mul_pow]
        ring
    _ ≤ (Nat.centralBinom M : ℝ) ^ Fintype.card κ * 1 := mul_le_mul_of_nonneg_left hM hCd
    _ = (Nat.centralBinom M : ℝ) ^ Fintype.card κ := mul_one _

/-! ## The criterion implies recurrence -/

theorem not_liAlong_aux {S : Set ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (j₁ : κ)
    (u : κ → ℂ) (hu : ∀ j, ‖u j‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ n ∈ S, 0 < n → ∃ j, ε ≤ ‖u j ^ n - 1‖) : ¬LiAlong S := by
  intro hLi
  obtain ⟨ε', hε', hε'1, hε'le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ 1 ∧ ε' ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  have hsq1 : ε' ^ 2 ≤ 1 := pow_le_one₀ hε'.le hε'1
  have hsq0 : 0 < ε' ^ 2 := pow_pos hε' 2
  have hq0 : 0 ≤ 1 - ε' ^ 2 / 4 := by linarith
  have hq1 : 1 - ε' ^ 2 / 4 < 1 := by linarith
  obtain ⟨M, hM1, hM⟩ := exists_M (Fintype.card κ) hq0 hq1
  have key : ∀ n ∈ S, 0 ≤ ∑ x : (Σ e : κ → Fin (2 * M + 1),
      Fin (if e = centre κ M then 0 else mult κ M e)), (1 - (2 * phase M u x.1) ^ n).re := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · rw [family_sum M u hu n]
      obtain ⟨j₀, hj₀⟩ := hbad n hn hpos
      have hz : ∀ j, ‖u j ^ n‖ = 1 := fun j => by rw [norm_pow, hu j, one_pow]
      have hk : ∏ j, (2 + 2 * (u j ^ n).re) ^ M ≤ (mult κ M (centre κ M) : ℝ) := by
        refine kernel_le hq0 hM (fun j => 2 + 2 * (u j ^ n).re)
          (fun j => two_add_two_re_nonneg (hz j)) (fun j => two_add_two_re_le (hz j)) j₀ ?_
        show 2 + 2 * (u j₀ ^ n).re ≤ 4 * (1 - ε' ^ 2 / 4)
        rw [two_add_two_re (hz j₀)]
        have hsq := pow_le_pow_left₀ hε'.le (le_trans hε'le hj₀) 2
        linarith
      have hs : (mult κ M (centre κ M) : ℝ) ≤ ∑ e : κ → Fin (2 * M + 1), (mult κ M e : ℝ) :=
        Finset.single_le_sum (f := fun e : κ → Fin (2 * M + 1) => (mult κ M e : ℝ))
          (fun e _ => Nat.cast_nonneg _) (Finset.mem_univ (centre κ M))
      have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
      have hprod := mul_nonneg h2n (sub_nonneg.mpr hk)
      linarith
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : κ → Fin (2 * M + 1), ∀ j, (e₁ j : ℕ) = 0 :=
    ⟨fun _ => ⟨0, by omega⟩, fun _ => rfl⟩
  have hne : e₁ ≠ centre κ M := by
    intro h
    have h0 := he₁ j₁
    rw [h] at h0
    have hc : ((centre κ M j₁ : Fin (2 * M + 1)) : ℕ) = M := rfl
    omega
  have hpos : 0 < (if e₁ = centre κ M then 0 else mult κ M e₁) := by
    rw [ite_eq_right hne]
    unfold mult
    exact Finset.prod_pos (fun j _ => Nat.choose_pos (by have := he₁ j; omega))
  have hfinal : ‖2 * phase M u e₁‖ ≤ 1 :=
    hLi _ (fun x : (Σ e : κ → Fin (2 * M + 1),
      Fin (if e = centre κ M then 0 else mult κ M e)) => 2 * phase M u x.1) key
      ⟨e₁, ⟨0, hpos⟩⟩
  rw [norm_mul, norm_two', norm_phase M u hu, mul_one] at hfinal
  linarith

/-- If `S` misses a Bohr neighbourhood of 0, the Li criterion fails along `S`. -/
theorem not_liAlong_of_not_recurrent {S : Set ℕ} {κ : Type} [Fintype κ] (u : κ → ℂ)
    (hu : ∀ j, ‖u j‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ n ∈ S, 0 < n → ∃ j, ε ≤ ‖u j ^ n - 1‖) : ¬LiAlong S := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · intro hLi
    have h : ‖(2 : ℂ)‖ ≤ 1 := hLi Unit (fun _ => (2 : ℂ)) (by
      intro n hn
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp
      · obtain ⟨j, -⟩ := hbad n hn hpos
        exact (hκ.false j).elim) ()
    rw [norm_two'] at h
    linarith
  · obtain ⟨j₁⟩ := hκ
    exact not_liAlong_aux j₁ u hu hε hbad

/-- **Slopollary 4.** The finite Li criterion works along a set `S` of exponents if and only
if `S` is a set of Bohr recurrence. -/
theorem liAlong_iff_bohrRecurrent (S : Set ℕ) : LiAlong S ↔ BohrRecurrent S := by
  constructor
  · intro hLi κ _ u hu ε hε
    by_contra hcon
    refine not_liAlong_of_not_recurrent u hu hε (fun n hn hpos => ?_) hLi
    by_contra hj
    apply hcon
    refine ⟨n, hn, hpos, fun j => ?_⟩
    by_contra hlt
    exact hj ⟨j, not_lt.mp hlt⟩
  · exact liAlong_of_bohrRecurrent

/-! ## Examples -/

/-- All positive integers: the classical finite Li criterion (Bombieri-Lagarias). -/
theorem bohrRecurrent_univ : BohrRecurrent Set.univ := by
  intro κ _ u hu ε hε
  obtain ⟨n, -, hn0, hn⟩ := exists_pow_near_one u hu hε 0
  exact ⟨n, Set.mem_univ n, hn0, hn⟩

/-- The multiples of any fixed m ≥ 1 are enough. -/
theorem bohrRecurrent_multiples {m : ℕ} (hm : 0 < m) : BohrRecurrent {n : ℕ | m ∣ n} := by
  intro κ _ u hu ε hε
  obtain ⟨k, -, hk0, hk⟩ := exists_pow_near_one (fun j => u j ^ m)
    (fun j => by rw [norm_pow, hu j, one_pow]) hε 0
  refine ⟨m * k, Dvd.intro k rfl, Nat.mul_pos hm hk0, fun j => ?_⟩
  rw [pow_mul]
  exact hk j

theorem liAlong_multiples {m : ℕ} (hm : 0 < m) : LiAlong {n : ℕ | m ∣ n} :=
  liAlong_of_bohrRecurrent (bohrRecurrent_multiples hm)

theorem I_pow_prime_re_nonpos {p : ℕ} (hp : p.Prime) : (Complex.I ^ p).re ≤ 0 := by
  have h4 : p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by
    have hne : p % 4 ≠ 0 := by
      intro h
      have h2 : 2 ∣ p := by omega
      have hp2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
      omega
    omega
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  rw [Complex.I_pow_eq_pow_mod]
  rcases h4 with h | h | h
  · rw [h, pow_one, Complex.I_re]
  · rw [h, Complex.I_sq]
    simp
  · rw [h, hI3]
    simp

/-- The primes are not a set of Bohr recurrence: a quarter turn never comes home at a prime. -/
theorem not_bohrRecurrent_primes : ¬BohrRecurrent {p : ℕ | p.Prime} := by
  intro h
  obtain ⟨p, hp, -, hclose⟩ := h Unit (fun _ => Complex.I) (fun _ => Complex.norm_I) 1 one_pos
  have h1 := hclose ()
  have h2 : (1 - Complex.I ^ p).re ≤ ‖1 - Complex.I ^ p‖ := re_le_norm' _
  rw [norm_sub_rev] at h2
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := I_pow_prime_re_nonpos hp
  linarith

/-- Li's criterion along the primes fails for finite families. -/
theorem not_liAlong_primes : ¬LiAlong {p : ℕ | p.Prime} := fun h =>
  not_bohrRecurrent_primes ((liAlong_iff_bohrRecurrent _).mp h)

/-- An explicit witness: the single point 2i passes the Li test at every prime. -/
theorem two_I_passes_prime_tests {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - (2 * Complex.I) ^ p).re := by
  rw [mul_pow, Complex.sub_re, Complex.one_re, two_pow_mul_re]
  have h3 := I_pow_prime_re_nonpos hp
  have h2 : (0 : ℝ) ≤ 2 ^ p := by positivity
  nlinarith

/-! ## Back to the Riemann hypothesis -/

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

/-- **The Riemann hypothesis along a set of Bohr recurrence.** If `S` is a set of Bohr
recurrence (for instance the multiples of a fixed m), then the Riemann hypothesis holds if
and only if every finite partial Li sum over nontrivial zeros, with exponent in `S`, is
nonnegative. -/
theorem riemannHypothesis_iff_finite_li_sums_along {S : Set ℕ} (hS : BohrRecurrent S) :
    RiemannHypothesis ↔
      ∀ Z : Finset ℂ, (∀ ρ ∈ Z, IsNontrivialZero ρ) →
        ∀ n ∈ S, 0 ≤ ∑ ρ ∈ Z, (1 - (1 - 1 / ρ) ^ n).re := by
  have hLi := liAlong_of_bohrRecurrent hS
  constructor
  · intro RH Z hZ n _
    apply Finset.sum_nonneg
    intro ρ hρ
    obtain ⟨hζ, ht, h1⟩ := hZ ρ hρ
    have hre : ρ.re = 1 / 2 := RH ρ hζ ht h1
    have hρ0 : ρ ≠ 0 := ne_zero_of_re_pos (by rw [hre]; norm_num)
    have hnorm : ‖1 - 1 / ρ‖ ≤ 1 := (norm_one_sub_inv_le_one_iff hρ0).mpr hre.ge
    rw [Complex.sub_re, Complex.one_re]
    have h2 : ((1 - 1 / ρ) ^ n).re ≤ ‖(1 - 1 / ρ) ^ n‖ := re_le_norm' _
    have h3 : ‖(1 - 1 / ρ) ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hnorm
    linarith
  · intro H
    have key : ∀ ρ : ℂ, IsNontrivialZero ρ → 1 / 2 ≤ ρ.re := by
      intro ρ hρ
      have hρ0 : ρ ≠ 0 := ne_zero_of_re_pos (nontrivial_zero_re_pos hρ.1 hρ.2.1)
      apply (norm_one_sub_inv_le_one_iff hρ0).mp
      refine hLi Unit (fun _ => 1 - 1 / ρ) (fun n hn => ?_) ()
      have hH := H {ρ} (by
        intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact hρ) n hn
      rw [Finset.sum_singleton] at hH
      simpa using hH
    intro ρ hζ ht h1
    have hρ : IsNontrivialZero ρ := ⟨hζ, ht, h1⟩
    have h1' := key ρ hρ
    have h2' := key (1 - ρ) (isNontrivialZero_one_sub hρ)
    rw [one_sub_re] at h2'
    linarith

end Slopollary

#print axioms Slopollary.liAlong_iff_bohrRecurrent
#print axioms Slopollary.liAlong_multiples
#print axioms Slopollary.not_liAlong_primes
#print axioms Slopollary.two_I_passes_prime_tests
#print axioms Slopollary.riemannHypothesis_iff_finite_li_sums_along
