/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GammaSigmaFiniteTriangle
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# CesaroWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Cesàro window average, its arithmetic, and `Γ_σ` centering

ABK26, §4.2 writes `avsum_{k=n}^m f k` for the window average `(m − n +
1)⁻¹ ∑_{k ∈ [n,m]} f k`. This module supplies

* the average itself (`cesaroAvg`) and the elementary window arithmetic
  (`natCast_card_Icc_int`, `one_le_window`, `window_pos`) used to normalise the
  `√N / N = N^{-1/2}` bookkeeping;
* the `rpow` identities `sqrt_div_self_eq_rpow_neg_half` and
  `inv_le_rpow_neg_half` that convert those prefactors into the paper's
  `(m − n + 1)^{-1/2}` envelope;
* the moment and centering layer for the stretched-exponential class: a `Γ_σ`
  tail gives integrability and a first-moment bound (`e.moments.OGamma2`), and
  recentring a `Γ_σ` variable costs only the explicit constant
  `cesaroCenterConst σ = (1 + log 2)^{1/σ}(1 + gammaMomentConst σ)`; and
* the deterministic split `cesaroAvg_le_add_cesaroAvg_sub`, which peels a
  uniform mean bound off a window average.

Everything here is generic over the sample space: no carrier, no coefficient
field, no scale index enters. The centering step deliberately routes through the
**measurability-free** two-term triangle inequality of
`Algsuperdiff/Probability/GammaSigmaFiniteTriangle.lean`, because the objects
recentred downstream are existential witnesses with no available measurability.

## Main results

* `Algsuperdiff.Probability.cesaroAvg`
* `Algsuperdiff.Probability.integrable_of_isBigO_gammaSigma`
* `Algsuperdiff.Probability.centered_isBigO_gammaSigma_moment`
* `Algsuperdiff.Probability.cesaroAvg_le_add_cesaroAvg_sub`

## References

* ABK26, `l.minimal.scale.sep` for the window average.
* ABK26, `e.moments.OGamma2` for the moment bound.
* ABK26, `l.Gamma.sigma.triangle` for the centering cost.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-! ## The window average -/

/-- The Cesàro (window) average `avsum_{k=n}^m f k = (m − n + 1)⁻¹ ∑_{k=n}^m f k`. -/
def cesaroAvg (f : ℤ → ℝ) (n m : ℤ) : ℝ :=
  (1 / (((m - n + 1 : ℤ) : ℝ))) * ∑ k ∈ Finset.Icc n m, f k

/-! ## Window arithmetic -/

/-- The window cardinality, as a real number. -/
theorem natCast_card_Icc_int {n m : ℤ} (hnm : n ≤ m) :
    (((Finset.Icc n m).card : ℕ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) := by
  have h : (((Finset.Icc n m).card : ℕ) : ℤ) = m + 1 - n := Int.card_Icc_of_le n m (by omega)
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2 ⊢
  linarith only [h2]

theorem one_le_window {n m : ℤ} (hnm : n ≤ m) : (1 : ℝ) ≤ ((m - n + 1 : ℤ) : ℝ) := by
  have h : (1 : ℤ) ≤ m - n + 1 := by omega
  exact_mod_cast h

theorem window_pos {n m : ℤ} (hnm : n ≤ m) : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) :=
  lt_of_lt_of_le zero_lt_one (one_le_window hnm)

/-! ## `rpow` bookkeeping -/

/-- `√c / c = c^{-1/2}` for `c > 0`. -/
theorem sqrt_div_self_eq_rpow_neg_half {c : ℝ} (hc : 0 < c) :
    Real.sqrt c / c = c ^ (-(1 : ℝ) / 2) := by
  have h1 : Real.sqrt c = c ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow c
  have h2 : c ^ (-(1 : ℝ) / 2) * c ^ (1 : ℝ) = c ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hc]
    norm_num
  have h3 : c ^ (1 : ℝ) = c := Real.rpow_one c
  rw [h1, ← h2, h3]
  field_simp

/-- `c⁻¹ ≤ c^{-1/2}` for `c ≥ 1`. -/
theorem inv_le_rpow_neg_half {c : ℝ} (hc : 1 ≤ c) :
    1 / c ≤ c ^ (-(1 : ℝ) / 2) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hinv : c ^ (-(1 : ℝ)) = 1 / c := by
    rw [Real.rpow_neg hc0.le, Real.rpow_one, one_div]
  have hmono : c ^ (-(1 : ℝ)) ≤ c ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hc (by norm_num)
  rw [← hinv]
  exact hmono

/-! ## The centering constant -/

theorem one_add_log_two_pos : (0 : ℝ) < 1 + Real.log 2 := by
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith only [h]

/-- The centering cost for a `Γ_σ` variable: `X − ≤ O_{Γ_σ}(cesaroCenterConst σ ·
K)` whenever `X ≤ O_{Γ_σ}(K)`.  Built from the measurability-free two-term
triangle constant `(1 + log 2)^{1/σ}` and the first-moment constant
`gammaMomentConst σ` (`e.moments.OGamma2`). -/
def cesaroCenterConst (σ : ℝ) : ℝ :=
  (1 + Real.log 2) ^ σ⁻¹ * (1 + gammaMomentConst σ)

theorem cesaroCenterConst_pos {σ : ℝ} (hσ : 0 < σ) : 0 < cesaroCenterConst σ := by
  have h2 : (0 : ℝ) < (1 + Real.log 2) ^ σ⁻¹ :=
    Real.rpow_pos_of_pos one_add_log_two_pos _
  have h3 : 0 < gammaMomentConst σ := gammaMomentConst_pos hσ
  simp only [cesaroCenterConst]
  exact mul_pos h2 (by linarith only [h3])

/-! ## Moments from `Γ_σ` tails (`e.moments.OGamma2`) -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `e.moments.OGamma2` (`p = 1`): a `Γ_σ` tail gives `∫ |X| ≤ C_mom(σ) K`. -/
theorem integral_abs_le_of_isBigO_gammaSigma [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X P) (hX : IsBigO P (gammaSigma σ) X K) :
    ∫ ω, |X ω| ∂P ≤ gammaMomentConst σ * K := by
  have h := integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := P) (X := X) (K := K) (σ := σ) (p := 1) hσ hK le_rfl hXm hX
  simpa using h

/-- A `Γ_σ` tail bound makes `X` integrable. -/
theorem integrable_of_isBigO_gammaSigma [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X P) (hX : IsBigO P (gammaSigma σ) X K) :
    Integrable X P := by
  have h := integrable_rpow_of_isBigOWith_gammaSigma
    (μ := P) (Y := fun ω => |X ω|) (K := K) (σ := σ) (p := 1) hσ hK le_rfl
    (fun ω => abs_nonneg _) (continuous_abs.measurable.comp_aemeasurable hXm) hX
  have h' : Integrable (fun ω => |X ω|) P := by simpa using h
  rw [← MeasureTheory.integrable_norm_iff hXm.aestronglyMeasurable]
  simpa [Real.norm_eq_abs] using h'

/-- `|| ≤ C_mom(σ) K` under a `Γ_σ` tail bound. -/
theorem abs_integral_le_of_isBigO_gammaSigma [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X P) (hX : IsBigO P (gammaSigma σ) X K) :
    |∫ ω, X ω ∂P| ≤ gammaMomentConst σ * K := by
  have h1 : |∫ ω, X ω ∂P| ≤ ∫ ω, |X ω| ∂P := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := P) (f := X)
  exact h1.trans (integral_abs_le_of_isBigO_gammaSigma hσ hK hXm hX)

end Moments

/-! ## Centering -/

section Centering

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Centering a `Γ_σ` variable.** If `X ≤ O_{Γ_σ}(K)` and `|| ≤ c` then `X − ≤
O_{Γ_σ}((1 + log 2)^{1/σ}(K + c))`.  Measurability-free: it uses the two-term
triangle inequality of `GammaSigmaFiniteTriangle.lean`. -/
theorem centered_isBigO_gammaSigma [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K c : ℝ} (hσ : 0 < σ) (hK : 0 ≤ K) (hc0 : 0 ≤ c)
    (hc : |∫ ω, X ω ∂P| ≤ c) (hX : IsBigO P (gammaSigma σ) X K) :
    IsBigO P (gammaSigma σ) (fun ω => X ω - ∫ ω', X ω' ∂P)
      ((1 + Real.log 2) ^ σ⁻¹ * (K + c)) := by
  have hconst : IsBigO P (gammaSigma σ) (fun _ : Ω => -(∫ ω', X ω' ∂P)) c :=
    HCPolySupport.Book.Ch04.isBigO_gammaSigma_const_of_abs_le hc0
      (by simpa [abs_neg] using hc)
  have h := isBigO_gammaSigma_add2' (μ := P) hσ hK hc0 hX hconst
  simpa [sub_eq_add_neg] using h

/-- Centering with the moment bound already inserted: the scale is
`cesaroCenterConst σ · K`. -/
theorem centered_isBigO_gammaSigma_moment [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X P) (hX : IsBigO P (gammaSigma σ) X K) :
    IsBigO P (gammaSigma σ) (fun ω => X ω - ∫ ω', X ω' ∂P) (cesaroCenterConst σ * K) := by
  have hc0 : 0 ≤ gammaMomentConst σ * K :=
    mul_nonneg (gammaMomentConst_pos hσ).le hK.le
  have hc := abs_integral_le_of_isBigO_gammaSigma hσ hK hXm hX
  have h := centered_isBigO_gammaSigma hσ hK.le hc0 hc hX
  have hcst : (1 + Real.log 2) ^ σ⁻¹ * (K + gammaMomentConst σ * K)
      = cesaroCenterConst σ * K := by
    simp only [cesaroCenterConst]; ring
  rwa [hcst] at h

end Centering

/-! ## The deterministic Cesàro rearrangement -/

/-- Splitting a Cesàro average into a mean part and a centered part: if
`g j ≤ μ₀` for all `j` then `avsum f ≤ μ₀ + avsum (f − g)`. -/
theorem cesaroAvg_le_add_cesaroAvg_sub {f g : ℤ → ℝ} {mu0 : ℝ} {n m : ℤ}
    (hnm : n ≤ m) (hg : ∀ j, g j ≤ mu0) :
    cesaroAvg f n m ≤ mu0 + cesaroAvg (fun j => f j - g j) n m := by
  have hcard : (((Finset.Icc n m).card : ℕ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) :=
    natCast_card_Icc_int hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  have hsum : ∑ j ∈ Finset.Icc n m, f j
      = (∑ j ∈ Finset.Icc n m, (f j - g j)) + ∑ j ∈ Finset.Icc n m, g j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgsum : ∑ j ∈ Finset.Icc n m, g j ≤ ((m - n + 1 : ℤ) : ℝ) * mu0 := by
    rw [← hcard]
    calc ∑ j ∈ Finset.Icc n m, g j ≤ ∑ _j ∈ Finset.Icc n m, mu0 :=
          Finset.sum_le_sum (fun j _ => hg j)
      _ = (((Finset.Icc n m).card : ℕ) : ℝ) * mu0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hinv : (0 : ℝ) < 1 / ((m - n + 1 : ℤ) : ℝ) := div_pos zero_lt_one hcpos
  have hstep : (1 / ((m - n + 1 : ℤ) : ℝ)) * (∑ j ∈ Finset.Icc n m, g j) ≤ mu0 := by
    have hmul := mul_le_mul_of_nonneg_left hgsum hinv.le
    have heq : (1 / ((m - n + 1 : ℤ) : ℝ)) * (((m - n + 1 : ℤ) : ℝ) * mu0) = mu0 := by
      field_simp
    linarith only [hmul, heq.le, heq.ge]
  have hdist : (1 / ((m - n + 1 : ℤ) : ℝ)) *
        ((∑ j ∈ Finset.Icc n m, (f j - g j)) + ∑ j ∈ Finset.Icc n m, g j)
      = (1 / ((m - n + 1 : ℤ) : ℝ)) * (∑ j ∈ Finset.Icc n m, (f j - g j))
        + (1 / ((m - n + 1 : ℤ) : ℝ)) * (∑ j ∈ Finset.Icc n m, g j) := by ring
  simp only [cesaroAvg]
  rw [hsum]
  linarith only [hstep, hdist.le, hdist.ge]

end

end Algsuperdiff.Probability
