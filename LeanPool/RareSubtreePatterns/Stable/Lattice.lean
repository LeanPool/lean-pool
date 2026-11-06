/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.WalkCF
public import LeanPool.RareSubtreePatterns.Bienayme.Normalization
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The span of the offspring law and lattice Fourier inversion

Source lines 855–883 ("Periodicity"). The span of `μ` is
`d = gcd {i - j : μ_i μ_j > 0}` (`PoissonDeclumping.Stable.latticeSpan`, defined literally as
the greatest common divisor of the differences). For critical `μ` with `μ_1 ≠ 1` we have
`μ_0 > 0`, so every support point is a multiple of `d`, and `X = K - 1 ∈ -1 + dℤ`; hence
`S_n ∈ -n + dℤ` (this is the paper's lattice `nb + dℤ` with the support point `b = -1`).

* `PoissonDeclumping.Stable.stepCF_add_period`: `φ(θ + 2π/d) = e^{-2πi/d} φ(θ)`;
* `PoissonDeclumping.Stable.norm_stepCF_lt_one`: `|φ(θ)| < 1` for `0 < |θ| ≤ π/d` (via Bezout:
  `d` is an integer combination of support differences);
* `PoissonDeclumping.Stable.walkLaw_real_singleton_eq_zero`: `P(S_n = k) = 0` unless
  `d ∣ k + n`;
* `PoissonDeclumping.Stable.walkLaw_real_singleton_lattice`: for `d ∣ k + n`,
  `P(S_n = k) = (d/2π) ∫_{-π/d}^{π/d} φ(θ)^n e^{-ikθ} dθ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable (μ : PMF ℕ)

/-- The differences `i - j` of points of the support of `μ`. -/
def supportDiffs : Set ℤ := {m | ∃ i j : ℕ, μ i ≠ 0 ∧ μ j ≠ 0 ∧ m = (i : ℤ) - j}

/-- The span `d = gcd {i - j : μ_i μ_j > 0}` of the support of `μ` (source lines 855–858):
the greatest natural number dividing every difference of two support points. -/
noncomputable def latticeSpan : ℕ :=
  sSup {D : ℕ | ∀ i j : ℕ, μ i ≠ 0 → μ j ≠ 0 → (D : ℤ) ∣ (i : ℤ) - j}

lemma latticeSpan_eq_natAbs_generator :
    latticeSpan μ = (Submodule.IsPrincipal.generator (Ideal.span (supportDiffs μ))).natAbs := by
  set g := Submodule.IsPrincipal.generator (Ideal.span (supportDiffs μ))
  have hcd : ∀ D : ℕ, (∀ i j : ℕ, μ i ≠ 0 → μ j ≠ 0 → (D : ℤ) ∣ (i : ℤ) - j) ↔ (D : ℤ) ∣ g := by
    intro D
    constructor
    · intro h
      have hle : Ideal.span (supportDiffs μ) ≤ Ideal.span {(D : ℤ)} := by
        rw [Ideal.span_le]
        rintro m ⟨i, j, hi, hj, rfl⟩
        exact Ideal.mem_span_singleton.2 (h i j hi hj)
      exact Ideal.mem_span_singleton.1
        (hle (Submodule.IsPrincipal.generator_mem (Ideal.span (supportDiffs μ))))
    · intro h i j hi hj
      have hm : (i : ℤ) - j ∈ Ideal.span (supportDiffs μ) :=
        Ideal.subset_span ⟨i, j, hi, hj, rfl⟩
      rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hm
      obtain ⟨c, hc⟩ := hm
      rw [hc, smul_eq_mul]
      exact Dvd.dvd.mul_left h c
  unfold latticeSpan
  rcases eq_or_ne g 0 with hg | hg
  · rw [hg]
    simp only [Int.natAbs_zero]
    apply Nat.sSup_of_not_bddAbove
    rintro ⟨B, hB⟩
    have : B + 1 ∈ {D : ℕ | ∀ i j : ℕ, μ i ≠ 0 → μ j ≠ 0 → (D : ℤ) ∣ (i : ℤ) - j} := by
      rw [mem_ofPred_eq, hcd, hg]; exact dvd_zero _
    have := hB this
    omega
  · apply IsGreatest.csSup_eq
    refine ⟨?_, ?_⟩
    · rw [mem_ofPred_eq, hcd]; exact Int.natAbs_dvd.2 dvd_rfl
    · intro D hD
      rw [mem_ofPred_eq, hcd] at hD
      exact Nat.le_of_dvd (Int.natAbs_pos.2 hg) (Int.natCast_dvd.1 hD)

/-- `d` divides every difference of support points. -/
theorem latticeSpan_dvd {i j : ℕ} (hi : μ i ≠ 0) (hj : μ j ≠ 0) :
    (latticeSpan μ : ℤ) ∣ (i : ℤ) - j := by
  rw [latticeSpan_eq_natAbs_generator, Int.natCast_natAbs, abs_dvd]
  have hm : (i : ℤ) - j ∈ Ideal.span (supportDiffs μ) := Ideal.subset_span ⟨i, j, hi, hj, rfl⟩
  rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hm
  obtain ⟨c, hc⟩ := hm
  rw [hc, smul_eq_mul]
  exact Dvd.intro_left c rfl

/-- Bezout: `d` is an integer combination of differences of support points. -/
theorem latticeSpan_mem_span : (latticeSpan μ : ℤ) ∈ Ideal.span (supportDiffs μ) := by
  rw [latticeSpan_eq_natAbs_generator, Int.natCast_natAbs]
  rcases abs_choice (Submodule.IsPrincipal.generator (Ideal.span (supportDiffs μ))) with h | h
  · rw [h]; exact Submodule.IsPrincipal.generator_mem _
  · rw [h]; exact (Ideal.neg_mem_iff _).2 (Submodule.IsPrincipal.generator_mem _)

variable {μ}

theorem latticeSpan_pos (hc : IsCritical μ) (hne : μ 1 ≠ 1) : 0 < latticeSpan μ := by
  obtain ⟨j, hj2, hj⟩ := hc.exists_two_le_ne_zero hne
  have h0 := hc.apply_zero_ne_zero hne
  have hd := latticeSpan_dvd μ hj h0
  rcases Nat.eq_zero_or_pos (latticeSpan μ) with h | h
  · rw [h] at hd
    simp at hd
    omega
  · exact h

/-- Every support point of `μ` is a multiple of `d` (since `μ_0 > 0`). -/
theorem latticeSpan_dvd_of_ne_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) {i : ℕ} (hi : μ i ≠ 0) :
    (latticeSpan μ : ℤ) ∣ i := by
  simpa using latticeSpan_dvd μ hi (hc.apply_zero_ne_zero hne)


lemma stepCF_eq_integral (θ : ℝ) :
    stepCF μ θ = ∫ k : ℕ, cexp (θ * (((k : ℤ) - 1 : ℤ) : ℂ) * I) ∂μ.toMeasure := by
  rw [stepCF, stepLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]

lemma ae_toMeasure_ne_zero : ∀ᵐ k ∂μ.toMeasure, μ k ≠ 0 := by
  rw [ae_iff_of_countable]
  intro k hk
  rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)] at hk

/-- Twisted periodicity of `φ`: `φ(θ + 2π/d) = e^{-2πi/d} φ(θ)`. -/
theorem stepCF_add_period (hc : IsCritical μ) (hne : μ 1 ≠ 1) (θ : ℝ) :
    stepCF μ (θ + 2 * Real.pi / latticeSpan μ) =
      cexp (-((2 * Real.pi / latticeSpan μ : ℝ) * I)) * stepCF μ θ := by
  rw [stepCF_eq_integral, stepCF_eq_integral, ← integral_const_mul]
  refine integral_congr_ae ((ae_toMeasure_ne_zero (μ := μ)).mono fun k hk => ?_)
  obtain ⟨m, hm⟩ := latticeSpan_dvd_of_ne_zero hc hne hk
  have hd : (latticeSpan μ : ℂ) ≠ 0 := by exact_mod_cast (latticeSpan_pos hc hne).ne'
  simp only
  rw [← Complex.exp_add]
  have hk' : (k : ℂ) = (latticeSpan μ : ℂ) * m := by exact_mod_cast hm
  rw [show (((θ + 2 * Real.pi / latticeSpan μ : ℝ) : ℂ) * (((k : ℤ) - 1 : ℤ) : ℂ) * I) =
      (-((2 * Real.pi / latticeSpan μ : ℝ) * I) + θ * (((k : ℤ) - 1 : ℤ) : ℂ) * I) +
        (m : ℂ) * (2 * Real.pi * I) by
    push_cast
    rw [hk']
    field_simp
    ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]


lemma eq_one_of_norm_eq_one_of_re_eq_one {w : ℂ} (hn : ‖w‖ = 1) (hr : w.re = 1) : w = 1 := by
  have h := Complex.normSq_eq_norm_sq w
  rw [hn, Complex.normSq_apply, hr] at h
  have him : w.im = 0 := by nlinarith
  exact Complex.ext hr (by simpa using him)

/-- If `|φ(θ)| = 1` then `θ d ∈ 2πℤ`. -/
theorem exists_int_of_norm_stepCF_eq_one {θ : ℝ} (h : ‖stepCF μ θ‖ = 1) :
    ∃ n : ℤ, θ * latticeSpan μ = n * (2 * Real.pi) := by
  set e : ℕ → ℂ := fun k => cexp (θ * (((k : ℤ) - 1 : ℤ) : ℂ) * I) with he
  have hen : ∀ k, ‖e k‖ = 1 := fun k => by
    simp only [he]
    rw [show ((θ : ℂ) * (((k : ℤ) - 1 : ℤ) : ℂ) * I) = ((θ * (((k : ℤ) - 1 : ℤ) : ℝ) : ℝ) : ℂ) * I
      by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hφ : stepCF μ θ = ∫ k, e k ∂μ.toMeasure := stepCF_eq_integral θ
  set u : ℂ := (starRingEnd ℂ) (stepCF μ θ) with hu
  have hun : ‖u‖ = 1 := by rw [hu, Complex.norm_conj, h]
  have huφ : u * stepCF μ θ = 1 := by
    rw [hu, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  have hint : Integrable e μ.toMeasure :=
    Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun k => (hen k).le)
  set g : ℕ → ℝ := fun k => 1 - (u * e k).re with hg
  have hg0 : 0 ≤ g := by
    intro k
    change 0 ≤ 1 - (u * e k).re
    rw [sub_nonneg]
    calc (u * e k).re ≤ ‖u * e k‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hun, hen, one_mul]
  have hgi : Integrable g μ.toMeasure :=
    (integrable_const 1).sub ((hint.const_mul u).re)
  have hre : ∫ k, (u * e k).re ∂μ.toMeasure = (∫ k, u * e k ∂μ.toMeasure).re :=
    integral_re (hint.const_mul u)
  have hgint : ∫ k, g k ∂μ.toMeasure = 0 := by
    change ∫ k, (1 - (u * e k).re) ∂μ.toMeasure = 0
    rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun k => (u * e k).re) (integrable_const 1)
      (by exact (hint.const_mul u).re), integral_const, probReal_univ,
      one_smul, hre, integral_const_mul, ← hφ, huφ, Complex.one_re, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hgint
  rw [Filter.EventuallyEq, ae_iff_of_countable] at hae
  have hk1 : ∀ k, μ k ≠ 0 → u * e k = 1 := by
    intro k hk
    have hk' : μ.toMeasure {k} ≠ 0 := by
      rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]
    have := hae k hk'
    simp only [hg, Pi.zero_apply, sub_eq_zero] at this
    exact eq_one_of_norm_eq_one_of_re_eq_one (by rw [norm_mul, hun, hen, one_mul]) this.symm
  -- the subgroup of `m` with `e^{iθm} = 1` contains all support differences
  have hmem : ∀ m ∈ Ideal.span (supportDiffs μ), cexp (θ * (m : ℂ) * I) = 1 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hx
      have h1 := hk1 i hi
      have h2 := hk1 j hj
      have hu0 : u ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
      have hij : e i = e j := mul_left_cancel₀ hu0 (h1.trans h2.symm)
      have : cexp (θ * (((i : ℤ) - j : ℤ) : ℂ) * I) = e i / e j := by
        simp only [he]
        rw [← Complex.exp_sub]; congr 1; push_cast; ring
      have hej : e j ≠ 0 := by
        intro h0
        have := hen j
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      rw [this, hij, div_self hej]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [show (θ : ℂ) * ((x + y : ℤ) : ℂ) * I = θ * (x : ℂ) * I + θ * (y : ℂ) * I by
        push_cast; ring, Complex.exp_add, hx, hy, one_mul]
    | smul c x _ hx =>
      rw [smul_eq_mul, show (θ : ℂ) * ((c * x : ℤ) : ℂ) * I = (c : ℂ) * (θ * (x : ℂ) * I) by
        push_cast; ring, Complex.exp_int_mul, hx, one_zpow]
  have := hmem _ (latticeSpan_mem_span μ)
  rw [Complex.exp_eq_one_iff] at this
  obtain ⟨n, hn⟩ := this
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa using this

/-- **Aperiodicity modulo the span**: `|φ(θ)| < 1` for `0 < |θ| ≤ π/d`. -/
theorem norm_stepCF_lt_one (hc : IsCritical μ) (hne : μ 1 ≠ 1) {θ : ℝ} (h0 : θ ≠ 0)
    (hθ : |θ| ≤ Real.pi / latticeSpan μ) : ‖stepCF μ θ‖ < 1 := by
  rcases (norm_stepCF_le μ θ).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := exists_int_of_norm_stepCF_eq_one h
    have hd : (0 : ℝ) < latticeSpan μ := by exact_mod_cast latticeSpan_pos hc hne
    have h1 : |θ| * latticeSpan μ ≤ Real.pi := by rwa [le_div_iff₀ hd] at hθ
    have h2 : |θ| * latticeSpan μ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [← abs_of_pos hd, ← abs_mul, hn, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h3 : 0 < |θ| * latticeSpan μ := mul_pos (abs_pos.2 h0) hd
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : |θ| * latticeSpan μ = 0 := by rw [h2]; simp
      linarith
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    nlinarith [Real.pi_pos]


variable (μ) in
/-- The Fourier integrand `F(θ) = φ(θ)^n e^{-ikθ}` of `P(S_n = k)`. -/
noncomputable def fourierIntegrand (n : ℕ) (k : ℤ) (θ : ℝ) : ℂ :=
  stepCF μ θ ^ n * cexp (-(θ * k * I))

lemma continuous_fourierIntegrand (n : ℕ) (k : ℤ) : Continuous (fourierIntegrand μ n k) := by
  unfold fourierIntegrand
  have := continuous_stepCF μ
  fun_prop

lemma fourierIntegrand_add_period (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) (k : ℤ) (θ : ℝ) :
    fourierIntegrand μ n k (θ + 2 * Real.pi / latticeSpan μ) =
      cexp (-((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) * I)) * fourierIntegrand μ n k θ := by
  unfold fourierIntegrand
  rw [stepCF_add_period hc hne, mul_pow, ← Complex.exp_nat_mul]
  have : cexp (n * -(((2 * Real.pi / latticeSpan μ : ℝ) : ℂ) * I)) *
      cexp (-(((θ + 2 * Real.pi / latticeSpan μ : ℝ) : ℂ) * k * I)) =
      cexp (-((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) * I)) * cexp (-(θ * k * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (stepCF μ θ ^ n) * this

lemma fourierIntegrand_add_nat_mul_period (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) (k : ℤ)
    (θ : ℝ) (j : ℕ) :
    fourierIntegrand μ n k (θ + j * (2 * Real.pi / latticeSpan μ)) =
      cexp (-((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) * I)) ^ j * fourierIntegrand μ n k θ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show θ + ((j + 1 : ℕ) : ℝ) * (2 * Real.pi / latticeSpan μ) =
        (θ + j * (2 * Real.pi / latticeSpan μ)) + 2 * Real.pi / latticeSpan μ by push_cast; ring,
      fourierIntegrand_add_period hc hne, ih, pow_succ]
    ring

lemma fourierIntegrand_periodic (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) (k : ℤ) :
    Function.Periodic (fourierIntegrand μ n k) (2 * Real.pi) := by
  intro θ
  have hd : (latticeSpan μ : ℝ) ≠ 0 := by exact_mod_cast (latticeSpan_pos hc hne).ne'
  have h := fourierIntegrand_add_nat_mul_period hc hne n k θ (latticeSpan μ)
  rw [show ((latticeSpan μ : ℕ) : ℝ) * (2 * Real.pi / latticeSpan μ) = 2 * Real.pi by
    field_simp] at h
  rw [h, ← Complex.exp_nat_mul]
  have : (latticeSpan μ : ℂ) * -(((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) : ℂ) * I) =
      ((-(n + k) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    have hdC : (latticeSpan μ : ℂ) ≠ 0 := by exact_mod_cast hd
    push_cast; field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I, one_mul]

lemma intervalIntegrable_fourierIntegrand (n : ℕ) (k : ℤ) (a b : ℝ) :
    IntervalIntegrable (fourierIntegrand μ n k) volume a b :=
  (continuous_fourierIntegrand n k).intervalIntegrable a b

/-- `P(S_n = k) = 0` off the lattice `-n + dℤ`. -/
theorem walkLaw_real_singleton_eq_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n : ℕ} {k : ℤ}
    (h : ¬ (latticeSpan μ : ℤ) ∣ k + n) : (walkLaw μ n).real {k} = 0 := by
  set T : ℝ := 2 * Real.pi / latticeSpan μ with hT
  set ω : ℂ := cexp (-((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) * I)) with hω
  have hd : (latticeSpan μ : ℝ) ≠ 0 := by exact_mod_cast (latticeSpan_pos hc hne).ne'
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [hω, Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have := congrArg Complex.im hm
    simp only [ofReal_mul, ofReal_div, ofReal_ofNat, ofReal_natCast, ofReal_add,
      ofReal_intCast, neg_im, mul_im, mul_re, div_natCast_re, re_ofNat, ofReal_re,
      im_ofNat, ofReal_im, mul_zero, sub_zero, add_re, natCast_re, intCast_re,
      div_natCast_im, zero_mul, add_zero, zero_div, add_im, natCast_im, intCast_im,
      I_im, mul_one, I_re, sub_self] at this
    apply h
    refine ⟨-m, ?_⟩
    have h5 : -(2 * Real.pi * ((n : ℝ) + k)) = (latticeSpan μ : ℝ) * m * (2 * Real.pi) := by
      have h6 := congrArg (· * (latticeSpan μ : ℝ)) this
      rw [show -(2 * Real.pi / (latticeSpan μ : ℝ) * ((n : ℝ) + k)) * (latticeSpan μ : ℝ) =
        -(2 * Real.pi * ((n : ℝ) + k)) by field_simp] at h6
      linarith
    have h3 : (2 * Real.pi) * (((k : ℝ) + n) - (latticeSpan μ : ℝ) * (-m)) = 0 := by
      linear_combination -h5
    have h4 := (mul_eq_zero.1 h3).resolve_left (by positivity)
    have h2 : ((k + n : ℤ) : ℝ) = ((latticeSpan μ * -m : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  set Iπ := ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand μ n k θ with hI
  have hshift : ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand μ n k (θ + T) = ω * Iπ := by
    simp_rw [hT, fourierIntegrand_add_period hc hne]
    rw [intervalIntegral.integral_const_mul]
  have hshift' : ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand μ n k (θ + T) = Iπ := by
    have h6 := (fourierIntegrand_periodic hc hne n k).intervalIntegral_add_eq (-Real.pi + T)
      (-Real.pi)
    rw [intervalIntegral.integral_comp_add_right, hI,
      show Real.pi + T = -Real.pi + T + 2 * Real.pi by ring, h6,
      show -Real.pi + 2 * Real.pi = Real.pi by ring]
  have hI0 : Iπ = 0 := by
    have h3 : (ω - 1) * Iπ = 0 := by rw [sub_mul, ← hshift, hshift', one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hω1
    · exact h4
  have h5 := walkLaw_real_singleton μ n k
  rw [show (∫ θ in (-Real.pi)..Real.pi, stepCF μ θ ^ n * cexp (-(θ * k * I))) = Iπ from rfl,
    hI0, mul_zero] at h5
  exact_mod_cast h5

/-- **Lattice Fourier inversion**: for `k ≡ -n (mod d)`,
`P(S_n = k) = (d/2π) ∫_{-π/d}^{π/d} φ(θ)^n e^{-ikθ} dθ`. -/
theorem walkLaw_real_singleton_lattice (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) (k : ℤ)
    (h : (latticeSpan μ : ℤ) ∣ k + n) :
    (((walkLaw μ n).real {k} : ℝ) : ℂ) = (latticeSpan μ / (2 * Real.pi)) *
      ∫ θ in (-(Real.pi / latticeSpan μ))..(Real.pi / latticeSpan μ), fourierIntegrand μ n k θ := by
  set T : ℝ := 2 * Real.pi / latticeSpan μ with hT
  have hd : (latticeSpan μ : ℝ) ≠ 0 := by exact_mod_cast (latticeSpan_pos hc hne).ne'
  obtain ⟨m, hm⟩ := h
  have hω : cexp (-((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) * I)) = 1 := by
    have : -(((2 * Real.pi / latticeSpan μ * (n + k) : ℝ) : ℂ) * I) =
        ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
      have hmC : ((k : ℂ) + n) = (latticeSpan μ : ℂ) * m := by exact_mod_cast hm
      have hdC : (latticeSpan μ : ℂ) ≠ 0 := by exact_mod_cast hd
      push_cast
      rw [add_comm (n : ℂ), hmC]
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hper : Function.Periodic (fourierIntegrand μ n k) T := by
    intro θ
    rw [hT, fourierIntegrand_add_period hc hne, hω, one_mul]
  have h1 := hper.intervalIntegral_add_zsmul_eq (latticeSpan μ : ℤ) (-Real.pi)
    (intervalIntegrable_fourierIntegrand n k)
  rw [show -Real.pi + (latticeSpan μ : ℤ) • T = Real.pi by
    rw [hT, zsmul_eq_mul]; push_cast; field_simp; ring] at h1
  have h2 := hper.intervalIntegral_add_eq (-Real.pi) (-(Real.pi / latticeSpan μ))
  rw [show -(Real.pi / latticeSpan μ) + T = Real.pi / latticeSpan μ by
    rw [hT]; field_simp; ring] at h2
  rw [walkLaw_real_singleton]
  change _ * ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand μ n k θ = _
  rw [h1, h2, zsmul_eq_mul]
  push_cast
  ring

end PoissonDeclumping.Stable
