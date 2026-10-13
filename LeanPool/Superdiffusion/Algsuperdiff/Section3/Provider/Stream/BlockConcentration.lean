/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Concentration
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Int.Interval

/-!
# BlockConcentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for independent sums with geometrically growing scales

ABK26's stream estimate `e.k.ell.upscales` applies the concentration proposition
`p.concentration` to the family `{j_k(0)}_{k ∈ (n, m]}`, whose scales `3^{γk}`
are *not* uniform, and reads off the `ℓ²`-aggregated amplitude

`(∑_{k ∈ (n, m]} 3^{2γk})^{1/2} ≤ C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm}`.

The concentration proposition available in CoarseGraining,
`Homogenization.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero`,
is stated at a *uniform* scale `K` with amplitude `C √N K`.  Used with `K =
3^{γm}` it produces `C (m-n)^{1/2} 3^{γm}`, which is the correct answer exactly
when `m - n ≤ γ^{-1}` and is lossy beyond that.

This module supplies the missing regime by the standard blocking argument,
using only proved tools: split `(n, m]` into consecutive blocks of width `r =
⌈γ^{-1}⌉`, apply the uniform concentration on each block at its own largest
scale, and recombine with the generalized triangle inequality
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`.  Since
`γ r ≥ 1`, the block amplitudes `C √r 3^{γ(m - jr)}` decay at least
geometrically with ratio `1/3`, so their sum is at most `(3/2) C √r 3^{γm}`,
and `√r ≤ √2 γ^{-1/2}`.

Nothing here refers to the ABK model: the statements are about an arbitrary
independent centered family with `Γ₂` tails at the scales `3^{γk}`.

## Main definitions

* `Algsuperdiff.Section3.Provider.Stream.geometricBlockWidth`
* `Algsuperdiff.Section3.Provider.Stream.geometricBlockEnd`
* `Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst`

## Main results

* `isBigO_gammaSigma_two_sum_Ioc_of_card`: the uniform-scale branch, with
  amplitude `C (m-n)^{1/2} 3^{γm}`.
* `isBigO_gammaSigma_two_sum_Ioc_of_inv_gamma`: the blocked branch, with
  amplitude `C γ^{-1/2} 3^{γm}`.
* `isBigO_gammaSigma_two_sum_Ioc_geometric`: the combined estimate with the
  source's `min{γ^{-1/2}, (m-n)^{1/2}}` amplitude.

## References

* ABK26, `e.k.ell.upscales`.
* ABK26, Proposition `p.concentration`.
* ABK26, Lemma `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Elementary preliminaries -/

/-- Consecutive half-open integer intervals split a sum.  This is the integer
analogue of `Finset.sum_Ioc_consecutive`, which Mathlib states only for `ℕ`. -/
theorem sum_Ioc_consecutive_int {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((∑ i ∈ Finset.Ioc a b, f i) + ∑ i ∈ Finset.Ioc b c, f i) =
      ∑ i ∈ Finset.Ioc a c, f i := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.sum_union]
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  exact absurd ((Finset.mem_Ioc.1 hx').1.trans_le (Finset.mem_Ioc.1 hx).2) (lt_irrefl _)

/-- The truncated geometric series with ratio `1/3`. -/
theorem sum_range_geom_third_le (J : ℕ) :
    ∑ j ∈ Finset.range J, ((1 : ℝ) / 3) ^ j ≤ 3 / 2 := by
  have key : ∀ K : ℕ,
      ∑ j ∈ Finset.range K, ((1 : ℝ) / 3) ^ j = 3 / 2 * (1 - ((1 : ℝ) / 3) ^ K) := by
    intro K
    induction K with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [key J]
  have hpos : (0 : ℝ) < ((1 : ℝ) / 3) ^ J := by positivity
  nlinarith

/-- The identically zero random variable satisfies every nonnegative
weak-Orlicz bound. -/
theorem isBigO_gammaSigma_zero_fun {A sigma : ℝ} (hA : 0 ≤ A) :
    IsBigO μ (gammaSigma sigma) (fun _ : Ω => (0 : ℝ)) A := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hAt : 0 ≤ A * t := mul_nonneg hA (le_trans zero_le_one ht)
  have hempty : absTailEvent (fun _ : Ω => (0 : ℝ)) (A * t) = (∅ : Set Ω) := by
    ext omega
    simp only [mem_absTailEvent, abs_zero, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hAt
  rw [hempty, measureReal_empty]
  exact (Real.exp_pos _).le

/-- The `σ = 2` instance of CoarseGraining's concentration constant is positive. -/
theorem gammaSigmaIndependentSumConst_two_pos :
    0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 := by
  have hmom : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hexp : (0 : ℝ) < gammaSigmaExpRegimeConst 2 := by
    have hpos : (0 : ℝ) < 8 * Real.exp 1 * gammaMomentConst 2 := by positivity
    exact lt_of_lt_of_le hpos (le_max_left _ _)
  have hEq : HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 =
      2 * gammaSigmaExpRegimeConst 2 := by
    unfold HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst
    norm_num [HCPolySupport.Book.Ch04.gammaSigmaExpRegimeEndpointConst,
      gammaSigmaExpRegimeEndpointConst]
  rw [hEq]
  linarith

/-! ## Blocks -/

/-- The block width `⌈γ⁻¹⌉` used to split `(n, m]` into consecutive blocks on
which the geometric amplitudes `3^{γk}` are comparable.  Since
`γ ⌈γ⁻¹⌉ ≥ 1`, consecutive block amplitudes decay by at least a factor `3`. -/
def geometricBlockWidth (gamma : ℝ) : ℕ := ⌈gamma⁻¹⌉₊

/-- The right endpoint of the `j`-th block of `(n, m]`, counted downwards from
`m`.  The truncation at `n` makes all sufficiently late blocks empty. -/
def geometricBlockEnd (gamma : ℝ) (n m : ℤ) (j : ℕ) : ℤ :=
  max n (m - (j : ℤ) * (geometricBlockWidth gamma : ℤ))

theorem geometricBlockEnd_eq (gamma : ℝ) (n m : ℤ) (j : ℕ) :
    geometricBlockEnd gamma n m j =
      max n (m - (j : ℤ) * (geometricBlockWidth gamma : ℤ)) :=
  rfl

theorem geometricBlockWidth_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < geometricBlockWidth gamma :=
  Nat.ceil_pos.2 (inv_pos.2 hgamma)

theorem one_le_gamma_mul_geometricBlockWidth {gamma : ℝ} (hgamma : 0 < gamma) :
    1 ≤ gamma * (geometricBlockWidth gamma : ℝ) := by
  have hle : gamma⁻¹ ≤ (geometricBlockWidth gamma : ℝ) := Nat.le_ceil _
  have h := mul_le_mul_of_nonneg_left hle hgamma.le
  rwa [mul_inv_cancel₀ hgamma.ne'] at h

theorem geometricBlockWidth_le_two_mul_inv {gamma : ℝ} (hgamma : 0 < gamma)
    (hquarter : gamma ≤ 1 / 4) :
    (geometricBlockWidth gamma : ℝ) ≤ 2 * gamma⁻¹ := by
  have hlt : (geometricBlockWidth gamma : ℝ) < gamma⁻¹ + 1 :=
    Nat.ceil_lt_add_one (inv_nonneg.2 hgamma.le)
  have hgi : gamma⁻¹ * gamma = 1 := inv_mul_cancel₀ hgamma.ne'
  have hginv : 0 < gamma⁻¹ := inv_pos.2 hgamma
  have h4 : (4 : ℝ) ≤ gamma⁻¹ := by nlinarith [hgi, hginv, hgamma, hquarter]
  linarith

theorem geometricBlockEnd_antitone (gamma : ℝ) (n m : ℤ) :
    Antitone (geometricBlockEnd gamma n m) := by
  intro i j hij
  rw [geometricBlockEnd_eq, geometricBlockEnd_eq]
  refine max_le_max (le_refl n) ?_
  have hcast : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
  have hwidth : (0 : ℤ) ≤ (geometricBlockWidth gamma : ℤ) := Int.natCast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hcast hwidth
  linarith

theorem geometricBlockEnd_zero {gamma : ℝ} {n m : ℤ} (hnm : n ≤ m) :
    geometricBlockEnd gamma n m 0 = m := by
  rw [geometricBlockEnd_eq]
  simp only [Nat.cast_zero, zero_mul, sub_zero]
  exact max_eq_right hnm

theorem geometricBlockEnd_toNat {gamma : ℝ} (hgamma : 0 < gamma) {n m : ℤ}
    (hnm : n ≤ m) :
    geometricBlockEnd gamma n m (m - n).toNat = n := by
  have hwidth : (1 : ℤ) ≤ (geometricBlockWidth gamma : ℤ) := by
    exact_mod_cast geometricBlockWidth_pos hgamma
  have htoNat : (((m - n).toNat : ℤ)) = m - n := Int.toNat_of_nonneg (by omega)
  have hnn : (0 : ℤ) ≤ m - n := by omega
  have hmul : m - n ≤ (((m - n).toNat : ℤ)) * (geometricBlockWidth gamma : ℤ) := by
    rw [htoNat]
    nlinarith [hwidth, hnn]
  rw [geometricBlockEnd_eq]
  exact max_eq_left (by linarith)

/-! ## The per-block estimate -/

/-- Each block of `(n, m]` obeys the uniform-scale concentration estimate at
its own largest amplitude `3^{γ(m - jr)}`, with at most `r` summands. -/
theorem isBigO_gammaSigma_two_geometricBlock [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} {gamma : ℝ} {n m : ℤ} (j : ℕ)
    (hgamma : 0 < gamma)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ k : ℤ, Measurable (X k))
    (hX : ∀ k : ℤ, IsBigO μ (gammaSigma 2) (X k) ((3 : ℝ) ^ (gamma * (k : ℝ))))
    (h_mean : ∀ k : ℤ, ∫ omega, X k omega ∂μ = 0) :
    IsBigO μ (gammaSigma 2)
      (fun omega => ∑ k ∈ Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
          (geometricBlockEnd gamma n m j), X k omega)
      (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) *
        (3 : ℝ) ^ (gamma * ((m : ℝ) -
          (j : ℝ) * (geometricBlockWidth gamma : ℝ)))) := by
  have hC : 0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hK : (0 : ℝ) < (3 : ℝ) ^ (gamma * ((m : ℝ) -
      (j : ℝ) * (geometricBlockWidth gamma : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hamp : 0 ≤ HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt (geometricBlockWidth gamma : ℝ) *
      (3 : ℝ) ^ (gamma * ((m : ℝ) -
        (j : ℝ) * (geometricBlockWidth gamma : ℝ))) :=
    mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg _)) hK.le
  by_cases hempty : geometricBlockEnd gamma n m j ≤ geometricBlockEnd gamma n m (j + 1)
  · have hnil : Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j) = ∅ :=
      Finset.Ioc_eq_empty (not_lt.2 hempty)
    simp only [hnil, Finset.sum_empty]
    exact isBigO_gammaSigma_zero_fun hamp
  · push Not at hempty
    have hn_le : n ≤ geometricBlockEnd gamma n m (j + 1) := by
      rw [geometricBlockEnd_eq]
      exact le_max_left _ _
    have hn_lt : n < geometricBlockEnd gamma n m j := lt_of_le_of_lt hn_le hempty
    have hBj : geometricBlockEnd gamma n m j =
        m - (j : ℤ) * (geometricBlockWidth gamma : ℤ) := by
      rw [geometricBlockEnd_eq] at hn_lt ⊢
      rcases max_choice n (m - (j : ℤ) * (geometricBlockWidth gamma : ℤ)) with h | h
      · rw [h] at hn_lt
        exact absurd hn_lt (lt_irrefl n)
      · exact h
    have hAj : m - ((j : ℤ) + 1) * (geometricBlockWidth gamma : ℤ) ≤
        geometricBlockEnd gamma n m (j + 1) := by
      have hcast : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
      rw [geometricBlockEnd_eq, hcast]
      exact le_max_right _ _
    have hs : (Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j)).Nonempty := by
      refine ⟨geometricBlockEnd gamma n m j, ?_⟩
      simp only [Finset.mem_Ioc]
      exact ⟨hempty, le_refl _⟩
    have hcard : ((Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j)).card : ℝ) ≤
        (geometricBlockWidth gamma : ℝ) := by
      have hexpand : ((j : ℤ) + 1) * (geometricBlockWidth gamma : ℤ) =
          (j : ℤ) * (geometricBlockWidth gamma : ℤ) +
            (geometricBlockWidth gamma : ℤ) := by ring
      have hbnd : geometricBlockEnd gamma n m j -
          geometricBlockEnd gamma n m (j + 1) ≤ (geometricBlockWidth gamma : ℤ) := by
        rw [hBj]
        rw [hexpand] at hAj
        linarith
      have hcardZ := Int.card_Ioc_of_le (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j) hempty.le
      have hcardnat : (Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
          (geometricBlockEnd gamma n m j)).card ≤ geometricBlockWidth gamma := by
        have hZ : ((Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
            (geometricBlockEnd gamma n m j)).card : ℤ) ≤
            (geometricBlockWidth gamma : ℤ) := by
          rw [hcardZ]
          exact hbnd
        exact_mod_cast hZ
      exact_mod_cast hcardnat
    have hscale : ∀ k ∈ Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j),
        IsBigO μ (gammaSigma 2) (X k)
          ((3 : ℝ) ^ (gamma * ((m : ℝ) -
            (j : ℝ) * (geometricBlockWidth gamma : ℝ)))) := by
      intro k hk
      refine (hX k).mono_scale ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine mul_le_mul_of_nonneg_left ?_ hgamma.le
      have hkle : k ≤ m - (j : ℤ) * (geometricBlockWidth gamma : ℤ) := by
        rw [← hBj]
        exact (Finset.mem_Ioc.1 hk).2
      have hkreal : ((k : ℤ) : ℝ) ≤
          ((m - (j : ℤ) * (geometricBlockWidth gamma : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hkle
      push_cast at hkreal
      linarith
    have hmain :=
      HCPolySupport.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := μ) (X := X)
        (s := Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
          (geometricBlockEnd gamma n m j))
        (σ := 2)
        (K := (3 : ℝ) ^ (gamma * ((m : ℝ) -
          (j : ℝ) * (geometricBlockWidth gamma : ℝ))))
        h_indep h_meas hs (by norm_num) (le_refl 2) hK hscale
        (fun k _ => h_mean k)
    refine hmain.mono_scale ?_
    refine mul_le_mul_of_nonneg_right ?_ hK.le
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) hC.le

/-! ## Telescoping the blocks -/

omit [MeasurableSpace Ω] in
/-- The blocks of `(n, m]` exhaust the interval. -/
theorem sum_geometricBlocks (gamma : ℝ) (n m : ℤ) (X : ℤ → Ω → ℝ) (omega : Ω)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, (∑ k ∈ Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j), X k omega) =
      ∑ k ∈ Finset.Ioc (geometricBlockEnd gamma n m J)
        (geometricBlockEnd gamma n m 0), X k omega := by
  induction J with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, ih, add_comm]
      exact sum_Ioc_consecutive_int (fun k => X k omega)
        (geometricBlockEnd_antitone gamma n m (Nat.le_succ p))
        (geometricBlockEnd_antitone gamma n m (Nat.zero_le p))

/-! ## The two branches -/

/-- The uniform-scale branch of ABK26's `e.k.ell.upscales`: applying the
concentration proposition at the single largest scale `3^{γm}` gives the
amplitude `C (m-n)^{1/2} 3^{γm}`. -/
theorem isBigO_gammaSigma_two_sum_Ioc_of_card [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} {gamma : ℝ} {n m : ℤ}
    (hgamma : 0 < gamma) (hnm : n < m)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ k : ℤ, Measurable (X k))
    (hX : ∀ k : ℤ, IsBigO μ (gammaSigma 2) (X k) ((3 : ℝ) ^ (gamma * (k : ℝ))))
    (h_mean : ∀ k : ℤ, ∫ omega, X k omega ∂μ = 0) :
    IsBigO μ (gammaSigma 2) (fun omega => ∑ k ∈ Finset.Ioc n m, X k omega)
      (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (gamma * (m : ℝ))) := by
  have hK : (0 : ℝ) < (3 : ℝ) ^ (gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hs : (Finset.Ioc n m).Nonempty := by
    refine ⟨m, ?_⟩
    simp only [Finset.mem_Ioc]
    exact ⟨hnm, le_refl m⟩
  have hscale : ∀ k ∈ Finset.Ioc n m,
      IsBigO μ (gammaSigma 2) (X k) ((3 : ℝ) ^ (gamma * (m : ℝ))) := by
    intro k hk
    refine (hX k).mono_scale (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    refine mul_le_mul_of_nonneg_left ?_ hgamma.le
    exact_mod_cast (Finset.mem_Ioc.1 hk).2
  have hmain :=
    HCPolySupport.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := μ) (X := X) (s := Finset.Ioc n m) (σ := 2)
      (K := (3 : ℝ) ^ (gamma * (m : ℝ)))
      h_indep h_meas hs (by norm_num) (le_refl 2) hK hscale (fun k _ => h_mean k)
  have hcard : (((Finset.Ioc n m).card : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) (Int.card_Ioc_of_le n m hnm.le)
    push_cast at hz
    exact hz
  rwa [hcard] at hmain

/-- The blocked branch of ABK26's `e.k.ell.upscales`: splitting `(n, m]` into
blocks of width `⌈γ^{-1}⌉` and summing the block estimates with the
generalized triangle inequality gives the amplitude `C γ^{-1/2} 3^{γm}`, with
no dependence on `m - n`. -/
theorem isBigO_gammaSigma_two_sum_Ioc_of_inv_gamma [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} {gamma : ℝ} {n m : ℤ}
    (hgamma : 0 < gamma) (hquarter : gamma ≤ 1 / 4) (hnm : n < m)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ k : ℤ, Measurable (X k))
    (hX : ∀ k : ℤ, IsBigO μ (gammaSigma 2) (X k) ((3 : ℝ) ^ (gamma * (k : ℝ))))
    (h_mean : ∀ k : ℤ, ∫ omega, X k omega ∂μ = 0) :
    IsBigO μ (gammaSigma 2) (fun omega => ∑ k ∈ Finset.Ioc n m, X k omega)
      (3 * gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt gamma⁻¹ * (3 : ℝ) ^ (gamma * (m : ℝ))) := by
  have hC₀ : 0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hC₁ : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hKpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrpos : (0 : ℝ) < (geometricBlockWidth gamma : ℝ) := by
    exact_mod_cast geometricBlockWidth_pos hgamma
  have hrange : (Finset.range (m - n).toNat).Nonempty := by
    refine Finset.nonempty_range_iff.2 ?_
    have : 0 < m - n := by omega
    omega
  have hb_pos : ∀ j : ℕ, 0 <
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) *
        (3 : ℝ) ^ (gamma * ((m : ℝ) -
          (j : ℝ) * (geometricBlockWidth gamma : ℝ))) := fun j =>
    mul_pos (mul_pos hC₀ (Real.sqrt_pos.2 hrpos))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have htriangle := isBigO_finset_sum_of_isBigO_gammaSigma (μ := μ)
    (Finset.range (m - n).toNat)
    (X := fun j omega => ∑ k ∈ Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
      (geometricBlockEnd gamma n m j), X k omega)
    (a := fun j : ℕ =>
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) *
        (3 : ℝ) ^ (gamma * ((m : ℝ) -
          (j : ℝ) * (geometricBlockWidth gamma : ℝ))))
    (σ := 2) (by norm_num) hrange (fun j _ => hb_pos j)
    (fun j _ => isBigO_gammaSigma_two_geometricBlock j hgamma h_indep h_meas hX h_mean)
    (fun j _ => Finset.measurable_sum _ fun k _ => h_meas k)
  have hsum : (fun omega => ∑ j ∈ Finset.range (m - n).toNat,
      ∑ k ∈ Finset.Ioc (geometricBlockEnd gamma n m (j + 1))
        (geometricBlockEnd gamma n m j), X k omega) =
      fun omega => ∑ k ∈ Finset.Ioc n m, X k omega := by
    funext omega
    rw [sum_geometricBlocks gamma n m X omega (m - n).toNat,
      geometricBlockEnd_toNat hgamma hnm.le, geometricBlockEnd_zero hnm.le]
  rw [hsum] at htriangle
  refine htriangle.mono_scale ?_
  -- bound the sum of block amplitudes by a geometric series
  have hthird : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
    rw [show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hratio : (3 : ℝ) ^ (-(gamma * (geometricBlockWidth gamma : ℝ))) ≤ 1 / 3 := by
    have hle : -(gamma * (geometricBlockWidth gamma : ℝ)) ≤ -(1 : ℝ) := by
      linarith [one_le_gamma_mul_geometricBlockWidth (gamma := gamma) hgamma]
    calc (3 : ℝ) ^ (-(gamma * (geometricBlockWidth gamma : ℝ)))
        ≤ (3 : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 1 / 3 := hthird
  have hratio_nonneg : (0 : ℝ) ≤
      (3 : ℝ) ^ (-(gamma * (geometricBlockWidth gamma : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hterm : ∀ j : ℕ,
      (3 : ℝ) ^ (gamma * ((m : ℝ) - (j : ℝ) * (geometricBlockWidth gamma : ℝ))) ≤
        (3 : ℝ) ^ (gamma * (m : ℝ)) * ((1 : ℝ) / 3) ^ j := by
    intro j
    have hsplit :
        (3 : ℝ) ^ (gamma * ((m : ℝ) - (j : ℝ) * (geometricBlockWidth gamma : ℝ))) =
          (3 : ℝ) ^ (gamma * (m : ℝ)) *
            ((3 : ℝ) ^ (-(gamma * (geometricBlockWidth gamma : ℝ)))) ^ j := by
      rw [← Real.rpow_natCast
          ((3 : ℝ) ^ (-(gamma * (geometricBlockWidth gamma : ℝ)))) j,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hratio_nonneg hratio j) hKpos.le
  have hsum_b : ∑ j ∈ Finset.range (m - n).toNat,
      (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) *
        (3 : ℝ) ^ (gamma * ((m : ℝ) -
          (j : ℝ) * (geometricBlockWidth gamma : ℝ)))) ≤
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) *
        ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 / 2)) := by
    have hpref : (0 : ℝ) ≤ HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt (geometricBlockWidth gamma : ℝ) :=
      mul_nonneg hC₀.le (Real.sqrt_nonneg _)
    calc ∑ j ∈ Finset.range (m - n).toNat,
          (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt (geometricBlockWidth gamma : ℝ) *
            (3 : ℝ) ^ (gamma * ((m : ℝ) -
              (j : ℝ) * (geometricBlockWidth gamma : ℝ))))
        ≤ ∑ j ∈ Finset.range (m - n).toNat,
            (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt (geometricBlockWidth gamma : ℝ) *
              ((3 : ℝ) ^ (gamma * (m : ℝ)) * ((1 : ℝ) / 3) ^ j)) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hterm j) hpref
      _ = HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt (geometricBlockWidth gamma : ℝ) *
            (3 : ℝ) ^ (gamma * (m : ℝ)) *
            ∑ j ∈ Finset.range (m - n).toNat, ((1 : ℝ) / 3) ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt (geometricBlockWidth gamma : ℝ) *
            (3 : ℝ) ^ (gamma * (m : ℝ)) * (3 / 2) :=
          mul_le_mul_of_nonneg_left (sum_range_geom_third_le _)
            (mul_nonneg hpref hKpos.le)
      _ = HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt (geometricBlockWidth gamma : ℝ) *
            ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 / 2)) := by ring
  have hsqrt_r : Real.sqrt (geometricBlockWidth gamma : ℝ) ≤
      Real.sqrt 2 * Real.sqrt gamma⁻¹ := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (geometricBlockWidth_le_two_mul_inv hgamma hquarter)
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2 : Real.sqrt 2 ≤ 2 :=
    le_trans (Real.sqrt_le_sqrt (by norm_num)) (le_of_eq hsqrt4)
  have hP : (0 : ℝ) ≤ gammaTriangleConst 2 *
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt gamma⁻¹ * (3 : ℝ) ^ (gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hC₀.le) (Real.sqrt_nonneg _)) hKpos.le
  calc gammaTriangleConst 2 * ∑ j ∈ Finset.range (m - n).toNat,
        (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt (geometricBlockWidth gamma : ℝ) *
          (3 : ℝ) ^ (gamma * ((m : ℝ) -
            (j : ℝ) * (geometricBlockWidth gamma : ℝ))))
      ≤ gammaTriangleConst 2 *
          (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt (geometricBlockWidth gamma : ℝ) *
            ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 / 2))) :=
        mul_le_mul_of_nonneg_left hsum_b hC₁.le
    _ ≤ gammaTriangleConst 2 *
          (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            (Real.sqrt 2 * Real.sqrt gamma⁻¹) *
            ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁.le
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrt_r hC₀.le
    _ = 3 / 2 * Real.sqrt 2 * (gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt gamma⁻¹ * (3 : ℝ) ^ (gamma * (m : ℝ))) := by ring
    _ ≤ 3 * (gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt gamma⁻¹ * (3 : ℝ) ^ (gamma * (m : ℝ))) := by
        nlinarith [hsqrt2, hP]
    _ = 3 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt gamma⁻¹ * (3 : ℝ) ^ (gamma * (m : ℝ)) := by ring

/-! ## The combined estimate -/

/-- The explicit universal constant of ABK26's `e.k.ell.upscales`. -/
def geometricConcentrationConst : ℝ :=
  HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    (1 + 3 * gammaTriangleConst 2)

theorem geometricConcentrationConst_eq :
    geometricConcentrationConst =
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (1 + 3 * gammaTriangleConst 2) :=
  rfl

theorem geometricConcentrationConst_pos : 0 < geometricConcentrationConst := by
  have hC₀ : 0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hC₁ : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  rw [geometricConcentrationConst_eq]
  exact mul_pos hC₀ (by linarith)

/-- ABK26's `e.k.ell.upscales` in abstract form: for an independent centered
family with `Γ₂` tails at the geometric scales `3^{γk}`,

`∑_{k ∈ (n, m]} X_k = O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`.

The source obtains this amplitude by evaluating the `ℓ²` aggregate
`(∑_{k ∈ (n,m]} 3^{2γk})^{1/2}` through `e.geo.part.sum`; the proof here
instead splits `(n, m]` into `⌈γ^{-1}⌉`-wide blocks, so that only the
uniform-scale concentration proposition and the generalized triangle
inequality are used.  The constant is explicit and universal. -/
theorem isBigO_gammaSigma_two_sum_Ioc_geometric [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} {gamma : ℝ} {n m : ℤ}
    (hgamma : 0 < gamma) (hquarter : gamma ≤ 1 / 4) (hnm : n < m)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ k : ℤ, Measurable (X k))
    (hX : ∀ k : ℤ, IsBigO μ (gammaSigma 2) (X k) ((3 : ℝ) ^ (gamma * (k : ℝ))))
    (h_mean : ∀ k : ℤ, ∫ omega, X k omega ∂μ = 0) :
    IsBigO μ (gammaSigma 2) (fun omega => ∑ k ∈ Finset.Ioc n m, X k omega)
      (geometricConcentrationConst *
        min (Real.sqrt gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (gamma * (m : ℝ))) := by
  have hC₀ : 0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hC₁ : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hKpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hprod : (0 : ℝ) ≤
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        gammaTriangleConst 2 := mul_nonneg hC₀.le hC₁.le
  rcases le_total (Real.sqrt gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) with hmin | hmin
  · rw [min_eq_left hmin]
    refine (isBigO_gammaSigma_two_sum_Ioc_of_inv_gamma hgamma hquarter hnm
      h_indep h_meas hX h_mean).mono_scale ?_
    refine mul_le_mul_of_nonneg_right ?_ hKpos.le
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [geometricConcentrationConst_eq]
    nlinarith [hC₀.le, hprod]
  · rw [min_eq_right hmin]
    refine (isBigO_gammaSigma_two_sum_Ioc_of_card hgamma hnm
      h_indep h_meas hX h_mean).mono_scale ?_
    refine mul_le_mul_of_nonneg_right ?_ hKpos.le
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [geometricConcentrationConst_eq]
    nlinarith [hC₀.le, hprod]

end

end Algsuperdiff.Section3.Provider.Stream
