/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierPotential

/-!
# JSpace Fourier Converse

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform SchwartzMap Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

@[expose]
def regularizedPositiveDerivativeSymbol (δ : ℝ) (k j : Fin 3) :
    L2Vec3 → ℂ :=
  fun ξ => Complex.ofReal
    (regularizedFrequencyCoord δ k ξ * regularizedFrequencyCoord δ j ξ *
      regularizedFrequencyWeight δ ξ)

private theorem regularizedPositiveDerivativeSymbol_hasTemperateGrowth
    (δ : ℝ) (k j : Fin 3) :
    (regularizedPositiveDerivativeSymbol δ k j).HasTemperateGrowth := by
  change (fun ξ : L2Vec3 => Complex.ofReal
    (regularizedFrequencyCoord δ k ξ * regularizedFrequencyCoord δ j ξ *
      regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  fun_prop

private theorem regularizedPositiveDerivativeSymbol_eq_neg_derivativeEntry
    (δ : ℝ) (k j : Fin 3) :
    regularizedPositiveDerivativeSymbol δ k j = -regularizedDerivativeEntry δ k j := by
  funext ξ
  simp [regularizedPositiveDerivativeSymbol, regularizedDerivativeEntry]

private theorem regularizedPositiveDerivativeSymbol_symmetric
    (δ : ℝ) (k j : Fin 3) :
    regularizedPositiveDerivativeSymbol δ k j = regularizedPositiveDerivativeSymbol δ j k := by
  funext ξ
  simp [regularizedPositiveDerivativeSymbol, mul_comm]

private theorem fin3_sum_eq {G : Type*} [AddCommMonoid G] (f : Fin 3 → G) :
    (∑ j : Fin 3, f j) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem fourierMultiplierCLM_sub_apply {g h : L2Vec3 → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (f : 𝓢'(L2Vec3, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (g - h) f =
      TemperedDistribution.fourierMultiplierCLM ℂ g f -
        TemperedDistribution.fourierMultiplierCLM ℂ h f := by
  rw [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.fourierMultiplierCLM_apply]
  have h := congrArg (fun T : 𝓢'(L2Vec3, ℂ) →L[ℂ] 𝓢'(L2Vec3, ℂ) => T (𝓕 f))
    (TemperedDistribution.smulLeftCLM_sub hg hh)
  exact congrArg (fun d : 𝓢'(L2Vec3, ℂ) => 𝓕⁻ d) h

private theorem fourierMultiplierCLM_add_apply {g h : L2Vec3 → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (f : 𝓢'(L2Vec3, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (g + h) f =
      TemperedDistribution.fourierMultiplierCLM ℂ g f +
        TemperedDistribution.fourierMultiplierCLM ℂ h f := by
  rw [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.fourierMultiplierCLM_apply]
  have h := congrArg (fun T : 𝓢'(L2Vec3, ℂ) →L[ℂ] 𝓢'(L2Vec3, ℂ) => T (𝓕 f))
    (TemperedDistribution.smulLeftCLM_add hg hh)
  exact congrArg (fun d : 𝓢'(L2Vec3, ℂ) => 𝓕⁻ d) h

private theorem fourierMultiplierCLM_neg_apply {g : L2Vec3 → ℂ}
    (hg : g.HasTemperateGrowth) (f : 𝓢'(L2Vec3, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (-g) f =
      -TemperedDistribution.fourierMultiplierCLM ℂ g f := by
  rw [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.fourierMultiplierCLM_apply]
  have h := congrArg (fun T : 𝓢'(L2Vec3, ℂ) →L[ℂ] 𝓢'(L2Vec3, ℂ) => T (𝓕 f))
    (TemperedDistribution.smulLeftCLM_neg hg)
  exact congrArg (fun d : 𝓢'(L2Vec3, ℂ) => 𝓕⁻ d) h

private theorem regularizedPositiveDiagonalSymbol_sum (δ : ℝ) (ξ : L2Vec3) :
    (∑ j : Fin 3, regularizedPositiveDerivativeSymbol δ j j ξ) =
      Complex.ofReal (1 - regularizedFrequencyWeight δ ξ) := by
  have hsum : ∑ j : Fin 3,
      (regularizedFrequencyCoord δ j ξ) ^ 2 * regularizedFrequencyWeight δ ξ =
        1 - regularizedFrequencyWeight δ ξ := by
    have h := regularizedFrequencyWeight_mul_one_add_sum_sq δ ξ
    calc
      _ = regularizedFrequencyWeight δ ξ *
          (∑ j : Fin 3, (regularizedFrequencyCoord δ j ξ) ^ 2) := by
            calc
              _ = (∑ j : Fin 3, (regularizedFrequencyCoord δ j ξ) ^ 2) *
                  regularizedFrequencyWeight δ ξ := by
                    rw [Finset.sum_mul]
              _ = _ := mul_comm _ _
      _ = regularizedFrequencyWeight δ ξ *
          (1 + ∑ j : Fin 3, (regularizedFrequencyCoord δ j ξ) ^ 2) -
          regularizedFrequencyWeight δ ξ := by ring
      _ = 1 - regularizedFrequencyWeight δ ξ := by rw [h]
  have hsum' : ∑ j : Fin 3,
      regularizedFrequencyCoord δ j ξ * regularizedFrequencyCoord δ j ξ *
        regularizedFrequencyWeight δ ξ = 1 - regularizedFrequencyWeight δ ξ := by
    simpa [pow_two] using hsum
  simp only [regularizedPositiveDerivativeSymbol]
  rw [← Complex.ofReal_sum, hsum']

private theorem regularizedDerivativeEntry_fourierMultiplier_apply
    (δ : ℝ) (k j : Fin 3) (f : 𝓢'(L2Vec3, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k j) f =
      -TemperedDistribution.fourierMultiplierCLM ℂ
        (regularizedPositiveDerivativeSymbol δ k j) f := by
  have hsymbol : regularizedDerivativeEntry δ k j =
      -regularizedPositiveDerivativeSymbol δ k j := by
    funext ξ
    simp [regularizedDerivativeEntry, regularizedPositiveDerivativeSymbol]
  rw [hsymbol]
  exact fourierMultiplierCLM_neg_apply
    (regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ k j) f

private theorem regularizedPositiveDiagonal_fourierMultiplier_sum
    (δ : ℝ) (f : 𝓢'(L2Vec3, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ
        (regularizedPositiveDerivativeSymbol δ 0 0) f +
      TemperedDistribution.fourierMultiplierCLM ℂ
        (regularizedPositiveDerivativeSymbol δ 1 1) f +
      TemperedDistribution.fourierMultiplierCLM ℂ
        (regularizedPositiveDerivativeSymbol δ 2 2) f =
    TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) f := by
  have hsymbol : regularizedPositiveDerivativeSymbol δ 0 0 +
      regularizedPositiveDerivativeSymbol δ 1 1 +
      regularizedPositiveDerivativeSymbol δ 2 2 =
      (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) := by
    funext ξ
    have hξ := regularizedPositiveDiagonalSymbol_sum δ ξ
    simpa [fin3_sum_eq] using hξ
  calc
    _ = TemperedDistribution.fourierMultiplierCLM ℂ
        (regularizedPositiveDerivativeSymbol δ 0 0 +
          regularizedPositiveDerivativeSymbol δ 1 1 +
          regularizedPositiveDerivativeSymbol δ 2 2) f := by
      rw [← fourierMultiplierCLM_add_apply
        (regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ 0 0)
        (regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ 1 1) f,
        ← fourierMultiplierCLM_add_apply
          ((regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ 0 0).add
            (regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ 1 1))
          (regularizedPositiveDerivativeSymbol_hasTemperateGrowth δ 2 2) f]
    _ = _ := congrArg (fun g : L2Vec3 → ℂ =>
      TemperedDistribution.fourierMultiplierCLM ℂ g f) hsymbol

private theorem regularizedPotentialCurlComponentLp_distribution_identity_zero
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialCurlComponentLp ha.1 δ hδ 0 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ))
        (weakFieldFourierComponent ha.1 0 : 𝓢'(L2Vec3, ℂ)) := by
  let f0 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 0
  let f1 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 1
  let f2 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 2
  let P := regularizedPositiveDerivativeSymbol δ
  have hdiv := weakDivFreeL2_regularizedFrequencyDivergence_zero ha δ 0
  rw [fin3_sum_eq] at hdiv
  change TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f1 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f2 = 0 at hdiv
  have hcross : TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f1 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f2 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f1 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f2) -
          TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 := by abel
      _ = 0 - TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 := by rw [hdiv]
      _ = _ := by simp
  have hcurl : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 0 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 0) f1 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 1) f0) -
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 2) f0 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 0) f2) := by
    simpa [regularizedPotentialCurlComponentLp, f0, f1, f2] using
      regularizedPotentialCurlComponentLp_toDist ha.1 δ hδ 0
  have hcurl' : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 0 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      -(TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f1) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f0 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f0 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f2 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 1 0) f1 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 1 1) f0) -
          (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 2 2) f0 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 2 0) f2) := hcurl
      _ = _ := by
        rw [regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply]
        abel
  have hcross' : TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f1 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f2 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 := by
    rw [show P 1 0 = P 0 1 by exact regularizedPositiveDerivativeSymbol_symmetric δ 1 0,
      show P 2 0 = P 0 2 by exact regularizedPositiveDerivativeSymbol_symmetric δ 2 0]
    exact hcross
  have hsum := regularizedPositiveDiagonal_fourierMultiplier_sum δ f0
  calc
    _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f1) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f0 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f0 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f2 := hcurl'
    _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f0 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f0 := by
      calc
        _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f1 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f2) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f0 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f0 := by abel
        _ = -(-TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f0) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f0 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f0 := by rw [hcross']
        _ = _ := by abel
    _ = TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) f0 := hsum
    _ = _ := by rfl

private theorem regularizedPotentialCurlComponentLp_distribution_identity_one
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialCurlComponentLp ha.1 δ hδ 1 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ))
        (weakFieldFourierComponent ha.1 1 : 𝓢'(L2Vec3, ℂ)) := by
  let f0 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 0
  let f1 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 1
  let f2 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 2
  let P := regularizedPositiveDerivativeSymbol δ
  have hdiv := weakDivFreeL2_regularizedFrequencyDivergence_zero ha δ 1
  rw [fin3_sum_eq] at hdiv
  change TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f2 = 0 at hdiv
  have hcross : TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f2 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ (P 1 0) f0 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f2) -
          TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 := by abel
      _ = 0 - TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 := by rw [hdiv]
      _ = _ := by simp
  have hcurl : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 1 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 1) f2 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 2) f1) -
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 0) f1 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 1) f0) := by
    simpa [regularizedPotentialCurlComponentLp, f0, f1, f2] using
      regularizedPotentialCurlComponentLp_toDist ha.1 δ hδ 1
  have hcurl' : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 1 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      -(TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 2 1) f2 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 2 2) f1) -
          (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 0 0) f1 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 0 1) f0) := hcurl
      _ = _ := by
        rw [regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply]
        abel
  have hcross' : TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 := by
    rw [show P 0 1 = P 1 0 by exact regularizedPositiveDerivativeSymbol_symmetric δ 0 1,
      show P 2 1 = P 1 2 by exact regularizedPositiveDerivativeSymbol_symmetric δ 2 1]
    exact hcross
  have hcross'' : TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 := by
    calc
      _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2 := by abel
      _ = _ := hcross'
  calc
    _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0 := hcurl'
    _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 := by
      calc
        _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f2 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 0 1) f0) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 := by abel
        _ = -(-TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 := by rw [hcross'']
        _ = _ := by abel
    _ = TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) f1 := by
      have hsum := regularizedPositiveDiagonal_fourierMultiplier_sum δ f1
      calc
        _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f1 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f1 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f1 := by abel
        _ = _ := hsum
    _ = _ := by rfl

private theorem regularizedPotentialCurlComponentLp_distribution_identity_two
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialCurlComponentLp ha.1 δ hδ 2 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ))
        (weakFieldFourierComponent ha.1 2 : 𝓢'(L2Vec3, ℂ)) := by
  let f0 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 0
  let f1 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 1
  let f2 : 𝓢'(L2Vec3, ℂ) := weakFieldFourierComponent ha.1 2
  let P := regularizedPositiveDerivativeSymbol δ
  have hdiv := weakDivFreeL2_regularizedFrequencyDivergence_zero ha δ 2
  rw [fin3_sum_eq] at hdiv
  change TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f1 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 = 0 at hdiv
  have hcross : TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f1 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ (P 2 0) f0 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 2 1) f1 +
          TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2) -
          TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 := by abel
      _ = 0 - TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 := by rw [hdiv]
      _ = _ := by simp
  have hcurl : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 2 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 2) f0 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 0) f2) -
      (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 1) f2 -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 2) f1) := by
    simpa [regularizedPotentialCurlComponentLp, f0, f1, f2] using
      regularizedPotentialCurlComponentLp_toDist ha.1 δ hδ 2
  have hcurl' : ((regularizedPotentialCurlComponentLp ha.1 δ hδ 2 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      -(TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f0) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f1 := by
    calc
      _ = (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 0 2) f0 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 0 0) f2) -
          (TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 1 1) f2 -
          TemperedDistribution.fourierMultiplierCLM ℂ
            (regularizedDerivativeEntry δ 1 2) f1) := hcurl
      _ = _ := by
        rw [regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply,
          regularizedDerivativeEntry_fourierMultiplier_apply]
        abel
  have hcross' : TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f0 +
      TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f1 =
      -TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 := by
    rw [show P 0 2 = P 2 0 by exact regularizedPositiveDerivativeSymbol_symmetric δ 0 2,
      show P 1 2 = P 2 1 by exact regularizedPositiveDerivativeSymbol_symmetric δ 1 2]
    exact hcross
  calc
    _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f0) +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 -
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f1 := hcurl'
    _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
        TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 := by
      calc
        _ = -(TemperedDistribution.fourierMultiplierCLM ℂ (P 0 2) f0 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 2) f1) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 := by abel
        _ = -(-TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2) +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 := by rw [hcross']
        _ = _ := by abel
    _ = TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) f2 := by
      have hsum := regularizedPositiveDiagonal_fourierMultiplier_sum δ f2
      calc
        _ = TemperedDistribution.fourierMultiplierCLM ℂ (P 0 0) f2 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 1 1) f2 +
            TemperedDistribution.fourierMultiplierCLM ℂ (P 2 2) f2 := by abel
        _ = _ := hsum
    _ = _ := by rfl

private theorem regularizedPotentialCurlComponentLp_distribution_identity
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ)
    (i : Fin 3) :
    ((regularizedPotentialCurlComponentLp ha.1 δ hδ i :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ))
        (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) := by
  fin_cases i
  · exact regularizedPotentialCurlComponentLp_distribution_identity_zero ha δ hδ
  · exact regularizedPotentialCurlComponentLp_distribution_identity_one ha δ hδ
  · exact regularizedPotentialCurlComponentLp_distribution_identity_two ha δ hδ

/-- The positive scale sequence used to remove the Fourier regularization. -/
@[expose]
def regularizationScale (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)

@[expose]
def regularizedWeightMultiplier (δ : ℝ) : L2Vec3 → ℂ :=
  fun ξ => Complex.ofReal (regularizedFrequencyWeight δ ξ)

@[expose]
def regularizedCurlMultiplier (δ : ℝ) : L2Vec3 → ℂ :=
  fun ξ => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)

private theorem regularizedWeightMultiplier_hasTemperateGrowth (δ : ℝ) :
    (regularizedWeightMultiplier δ).HasTemperateGrowth := by
  change (fun ξ : L2Vec3 => Complex.ofReal (regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  exact Complex.hasTemperateGrowth_ofReal.comp (regularizedFrequencyWeight_hasTemperateGrowth δ)

private theorem regularizedCurlMultiplier_hasTemperateGrowth (δ : ℝ) :
    (regularizedCurlMultiplier δ).HasTemperateGrowth := by
  change (fun ξ : L2Vec3 => Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  fun_prop

private theorem regularizedFrequencyWeight_bounds (δ : ℝ) (ξ : L2Vec3) :
    0 ≤ regularizedFrequencyWeight δ ξ ∧ regularizedFrequencyWeight δ ξ ≤ 1 := by
  let η : L2Vec3 := (δ⁻¹ : ℝ) • ξ
  have hweight : regularizedFrequencyWeight δ ξ = 1 / (1 + ‖η‖ ^ 2) := by
    rw [regularizedFrequencyWeight, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖η‖ ^ 2)]
    simp [η, Real.rpow_one]
  have hden : 1 ≤ 1 + ‖η‖ ^ 2 := by
    exact le_add_of_nonneg_right (sq_nonneg ‖η‖)
  rw [hweight]
  constructor
  · positivity
  · exact (div_le_one (by positivity)).2 hden

private theorem regularizedWeightMultiplier_norm_le_one (δ : ℝ) (ξ : L2Vec3) :
    ‖regularizedWeightMultiplier δ ξ‖ ≤ 1 := by
  rw [regularizedWeightMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (regularizedFrequencyWeight_bounds δ ξ).1]
  exact (regularizedFrequencyWeight_bounds δ ξ).2

private theorem regularizedCurlMultiplier_norm_le_one (δ : ℝ) (ξ : L2Vec3) :
    ‖regularizedCurlMultiplier δ ξ‖ ≤ 1 := by
  have hw := regularizedFrequencyWeight_bounds δ ξ
  rw [regularizedCurlMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith only [hw.1, hw.2])]
  exact sub_le_self 1 hw.1

/-- Every term of `regularizationScale` is positive. -/
theorem regularizationScale_pos (n : ℕ) : 0 < regularizationScale n := by
  dsimp [regularizationScale]
  positivity

private theorem regularizedWeightMultiplier_tendsto_zero_ae :
    ∀ᵐ ξ : L2Vec3 ∂(volume : Measure L2Vec3),
      Tendsto (fun n => regularizedWeightMultiplier (regularizationScale n) ξ)
        atTop (𝓝 0) := by
  filter_upwards [(volume : Measure L2Vec3).ae_ne (0 : L2Vec3)] with ξ hξ
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto
      (fun n : ℕ => ‖(regularizationScale n)⁻¹ • ξ‖) atTop atTop := by
    have hmul := hnat.atTop_mul_const (norm_pos_iff.mpr hξ)
    convert hmul using 1
    ext n
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (regularizationScale_pos n))]
    have hinv : (regularizationScale n)⁻¹ = ((n + 1 : ℕ) : ℝ) := by
      dsimp [regularizationScale]
      field_simp
    rw [hinv]
  have hdenom : Tendsto
      (fun n : ℕ => 1 + ‖(regularizationScale n)⁻¹ • ξ‖ ^ 2) atTop atTop := by
    have hpow := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hscale
    simpa [add_comm] using tendsto_atTop_add_const_right atTop 1 hpow
  have hweight (n : ℕ) : regularizedFrequencyWeight (regularizationScale n) ξ =
      (1 + ‖(regularizationScale n)⁻¹ • ξ‖ ^ 2)⁻¹ := by
    rw [regularizedFrequencyWeight, Real.rpow_neg (by positivity)]
    simp [Real.rpow_one]
  have hreal : Tendsto
      (fun n : ℕ => regularizedFrequencyWeight (regularizationScale n) ξ)
      atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hdenom) using 1
    ext n
    exact hweight n
  change Tendsto (fun n => Complex.ofReal
    (regularizedFrequencyWeight (regularizationScale n) ξ)) atTop (𝓝 0)
  simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hreal

private theorem regularizedWeightMultiplier_memLp (δ : ℝ) :
    MemLp (regularizedWeightMultiplier δ) (⊤ : ℝ≥0∞)
      (volume : Measure L2Vec3) :=
  boundedComplexMultiplier_memLp (regularizedWeightMultiplier δ)
    (regularizedWeightMultiplier_hasTemperateGrowth δ) (C := 1)
    (regularizedWeightMultiplier_norm_le_one δ)

private theorem regularizedCurlMultiplier_memLp (δ : ℝ) :
    MemLp (regularizedCurlMultiplier δ) (⊤ : ℝ≥0∞)
      (volume : Measure L2Vec3) :=
  boundedComplexMultiplier_memLp (regularizedCurlMultiplier δ)
    (regularizedCurlMultiplier_hasTemperateGrowth δ) (C := 1)
    (regularizedCurlMultiplier_norm_le_one δ)

private theorem l2Lp_toTemperedDistribution_injective :
    Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM (E := L2Vec3) ℂ volume 2) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let T : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3) →L[ℂ]
      𝓢'(L2Vec3, ℂ) := MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2
  have hker : T.ker = ⊥ := by
    simpa [T] using
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (E := L2Vec3) (F := ℂ) (μ := volume) (p := 2))
  intro u v huv
  have hsub : T (u - v) = 0 := by
    have hmap := T.map_sub u v
    rw [huv] at hmap
    simpa [T] using hmap
  have hmem : u - v ∈ T.ker := by
    change T (u - v) = 0
    exact hsub
  rw [hker] at hmem
  have hzero : u - v = 0 := by simpa using hmem
  exact sub_eq_zero.mp hzero

private theorem toTemperedDistribution_neg_l2
    (u : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
    ((-u : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      -(u : 𝓢'(L2Vec3, ℂ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let T : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3) →L[ℂ]
      𝓢'(L2Vec3, ℂ) := MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2
  change T (-u) = -T u
  exact T.map_neg u

private theorem regularizedCurlComponentLp_error_eq_negative_weightedInverseFourier
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ)
    (i : Fin 3) :
    regularizedPotentialCurlComponentLp ha.1 δ hδ i - weakFieldFourierComponent ha.1 i =
      -(𝓕⁻ (fourierMultiplyScalarL2 (regularizedWeightMultiplier δ)
        (regularizedWeightMultiplier_memLp δ)
        (𝓕 (weakFieldFourierComponent ha.1 i)))) := by
  let f : Lp (α := L2Vec3) ℂ 2 := weakFieldFourierComponent ha.1 i
  let q := regularizedCurlMultiplier δ
  let w := regularizedWeightMultiplier δ
  have hcurlDist := regularizedPotentialCurlComponentLp_distribution_identity ha δ hδ i
  have hqfun' : q = (fun ξ : L2Vec3 =>
      Complex.ofReal (1 - regularizedFrequencyWeight δ ξ)) := by rfl
  have hqDist :
      ((regularizedPotentialCurlComponentLp ha.1 δ hδ i :
        Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
        TemperedDistribution.fourierMultiplierCLM ℂ q (f : 𝓢'(L2Vec3, ℂ)) := by
    rw [hqfun']
    simpa only [f] using hcurlDist
  have hfilteredDist := inverseFourier_fourierMultiplyScalarL2_eq_fourierMultiplierCLM
    q (regularizedCurlMultiplier_hasTemperateGrowth δ)
    (regularizedCurlMultiplier_memLp δ) f
  have hDistEq :
      ((regularizedPotentialCurlComponentLp ha.1 δ hδ i :
        Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ((𝓕⁻ (fourierMultiplyScalarL2 q (regularizedCurlMultiplier_memLp δ)
        (𝓕 f)) : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) :=
    hqDist.trans hfilteredDist.symm
  have hcurlEq : regularizedPotentialCurlComponentLp ha.1 δ hδ i =
      𝓕⁻ (fourierMultiplyScalarL2 q (regularizedCurlMultiplier_memLp δ) (𝓕 f)) :=
    l2Lp_toTemperedDistribution_injective hDistEq
  have hqfun : q = (fun _ : L2Vec3 => (1 : ℂ)) - w := by
    funext ξ
    simp [q, w, regularizedCurlMultiplier, regularizedWeightMultiplier,
      Complex.ofReal_sub]
  have hfourierError :
      TemperedDistribution.fourierMultiplierCLM ℂ q (f : 𝓢'(L2Vec3, ℂ)) -
        (f : 𝓢'(L2Vec3, ℂ)) =
      -TemperedDistribution.fourierMultiplierCLM ℂ w (f : 𝓢'(L2Vec3, ℂ)) := by
    rw [hqfun, fourierMultiplierCLM_sub_apply
      (by fun_prop : (fun _ : L2Vec3 => (1 : ℂ)).HasTemperateGrowth)
      (regularizedWeightMultiplier_hasTemperateGrowth δ)]
    have hone : TemperedDistribution.fourierMultiplierCLM ℂ
        (fun _ : L2Vec3 => (1 : ℂ)) (f : 𝓢'(L2Vec3, ℂ)) = f := by simp
    rw [hone]
    abel
  have herrorDist :
      ((regularizedPotentialCurlComponentLp ha.1 δ hδ i - f :
        Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ((-(𝓕⁻ (fourierMultiplyScalarL2 w (regularizedWeightMultiplier_memLp δ)
        (𝓕 f))) : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) := by
    calc
      _ = (regularizedPotentialCurlComponentLp ha.1 δ hδ i :
          Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) - (f : 𝓢'(L2Vec3, ℂ)) :=
        toTemperedDistribution_sub_l2 _ _
      _ = -TemperedDistribution.fourierMultiplierCLM ℂ w
          (f : 𝓢'(L2Vec3, ℂ)) := by rw [hqDist, hfourierError]
      _ = _ := by
        rw [toTemperedDistribution_neg_l2,
          inverseFourier_fourierMultiplyScalarL2_eq_fourierMultiplierCLM
            w (regularizedWeightMultiplier_hasTemperateGrowth δ)
            (regularizedWeightMultiplier_memLp δ) f]
  exact l2Lp_toTemperedDistribution_injective herrorDist

/-- The Fourier multiplier error of the regularized curl tends to zero in
`L²` on each complex coordinate. -/
theorem regularizedPotentialCurlComponentLp_error_tendsto
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (i : Fin 3) :
    Tendsto (fun n : ℕ => eLpNorm
      (regularizedPotentialCurlComponentLp ha.1 (regularizationScale n)
        (regularizationScale_pos n) i - weakFieldFourierComponent ha.1 i)
      (2 : ℝ≥0∞) (volume : Measure L2Vec3)) atTop (𝓝 0) := by
  have hmul := fourierMultiplyScalarL2_tendsto_zero_of_tendsto_ae
    (fun n => regularizedWeightMultiplier_memLp (regularizationScale n))
    (fun n ξ => regularizedWeightMultiplier_norm_le_one (regularizationScale n) ξ)
    regularizedWeightMultiplier_tendsto_zero_ae
    (𝓕 (weakFieldFourierComponent ha.1 i))
  have hnorm (n : ℕ) : eLpNorm
      (regularizedPotentialCurlComponentLp ha.1 (regularizationScale n)
        (regularizationScale_pos n) i - weakFieldFourierComponent ha.1 i)
      (2 : ℝ≥0∞) (volume : Measure L2Vec3) =
      eLpNorm (fourierMultiplyScalarL2 (regularizedWeightMultiplier (regularizationScale n))
        (regularizedWeightMultiplier_memLp (regularizationScale n))
        (𝓕 (weakFieldFourierComponent ha.1 i)))
        (2 : ℝ≥0∞) (volume : Measure L2Vec3) := by
    rw [← Lp.enorm_def,
      regularizedCurlComponentLp_error_eq_negative_weightedInverseFourier ha
        (regularizationScale n) (regularizationScale_pos n) i,
      enorm_neg, ← Lp.enorm_def]
    exact (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ℂ).symm.enorm_map _
  exact hmul.congr' (Filter.Eventually.of_forall fun n => (hnorm n).symm)


end CKN

end
