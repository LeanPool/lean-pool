/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedInteriorEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSplitMass

/-!
# LocalizedInteriorMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localized Agmon mass estimate for bounded H¹ solutions

The compactly supported multiplier lies strictly inside the domain.  Thus the
weighted argument applies to an arbitrary `H1Function`; no trace condition on
the solution is used.  The rough size and smooth divergence are read only on
the topological support of the localization.
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ}

/-- The split-skew Agmon mass estimate for an `H¹` solution, using an
interior compactly supported multiplier. -/
theorem agmonMass_split_interior_le {Om : Set (Vec d)}
    (hOm : IsOpenBoundedConvexDomain Om) {a : CoeffField d}
    {ks kl : Vec d → Mat d} {u : H1Function Om} {g eta psi : Vec d → ℝ}
    {L : Set (Vec d)} {nu LamS Ks Kl mass kappa M : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hmass : 0 < mass) (hM : 0 ≤ M)
    (hEllS : IsEllipticFieldOn nu LamS Om
      (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaOm : tsupport eta ⊆ Om) (hetaL : tsupport eta ⊆ L)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hg : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y ≠ 0 → g y * u.toFun y ≤ -(mass * u.toFun y ^ 2))
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hadmiss : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 ≤
      3 * mass / 8) :
    mass / 2 * ∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) *
        ∫ y in Om, u.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume := by
  classical
  have hchiSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => Real.exp (kappa * psi y)) :=
    contDiff_exponentialWeight hpsi kappa
  have hzetaSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => eta y * Real.exp (kappa * psi y)) := heta.mul hchiSmooth
  have hzetaCompact : HasCompactSupport
      (fun y => eta y * Real.exp (kappa * psi y)) := hetaCompact.mul_right
  have hzetaOm : tsupport (fun y => eta y * Real.exp (kappa * psi y)) ⊆ Om :=
    tsupport_mul_subset hetaOm
  have hzetaL : tsupport (fun y => eta y * Real.exp (kappa * psi y)) ⊆ L :=
    tsupport_mul_subset hetaL
  have hadm := isAdmissibleMultiplier_localized_of_tsupport_subset hOm u
    heta hetaCompact hetaOm hchiSmooth
  have hgzeta : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y * Real.exp (kappa * psi y) ≠ 0 →
        g y * u.toFun y ≤ -(mass * u.toFun y ^ 2) := by
    filter_upwards [hg] with y hy hzy
    exact hy fun hzero => hzy (by rw [hzero, zero_mul])
  have hchiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i =>
          (fderiv ℝ (fun w => Real.exp (kappa * psi w)) y) (basisVec i)) ≤
        kappa ^ 2 * Real.exp (kappa * psi y) ^ 2 := by
    filter_upwards [hpsiGrad] with y hy
    exact exponentialWeight_gradient_le hpsi hy kappa
  have hsplitEnergy := weightedEnergy_split_interior_le hOm hnu hKs hM hEllS
    hsplit hksSkew hklSkew hklC1 hsol hMbound hzetaSmooth hzetaCompact
    hzetaOm hzetaL hksSize
  have hZle := integral_sq_mul_gradSq_product_le (u := u)
    (kappa := kappa) heta hetaCompact hchiSmooth hchiGrad
  have hDle := integral_sq_mul_vecDot_skewFieldDiv_le (u := u)
    (kl := kl) (L := L) (mass := mass) hmass hzetaSmooth hzetaCompact hzetaL
    hklC1 hklDiv
  set A := ∫ y in Om, u.toFun y ^ 2 *
    (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume with hA_def
  set B := ∫ y in Om, u.toFun y ^ 2 *
    (Real.exp (kappa * psi y) ^ 2 *
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume with hB_def
  set Zg := ∫ y in Om, u.toFun y ^ 2 *
    vecNormSq (fun i =>
      (fderiv ℝ (fun w => eta w * Real.exp (kappa * psi w)) y)
        (basisVec i)) ∂volume with hZ_def
  set D := ∫ y in Om, u.toFun y ^ 2 * vecDot (skewFieldDiv kl y)
      (fun i => (fderiv ℝ
        (fun w => (eta w * Real.exp (kappa * psi w)) ^ 2) y) (basisVec i))
    ∂volume with hD_def
  have henergy : nu / 2 * (∫ x in Om,
      (eta x * Real.exp (kappa * psi x)) ^ 2 * vecNormSq (u.grad x) ∂volume) ≤
      (∫ x in Om, g x * ((eta x * Real.exp (kappa * psi x)) ^ 2 *
        u.toFun x) ∂volume) + (2 * (nu + Ks) ^ 2 / nu * Zg - 1 / 2 * D) := by
    linarith only [hsplitEnergy]
  have hmassRaw := weightedMass_le_of_energy hnu hsol hadm hgzeta henergy
  have hArw : (∫ x in Om, (eta x * Real.exp (kappa * psi x)) ^ 2 *
      u.toFun x ^ 2 ∂volume) = A := by
    rw [hA_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hDArw : (∫ y in Om, u.toFun y ^ 2 *
      (eta y * Real.exp (kappa * psi y)) ^ 2 ∂volume) = A := by
    rw [hA_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hArw] at hmassRaw
  rw [hDArw] at hDle
  have hA0 : 0 ≤ A := by
    rw [hA_def]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by positivity)
  have hCnn : (0 : ℝ) ≤ 2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass := by
    positivity
  set C : ℝ := 2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass with hC_def
  have hcombine : mass * A ≤ C * Zg + mass / 8 * A := by
    rw [hC_def]
    linarith only [hmassRaw, hDle]
  have hZmul : C * Zg ≤ C * (2 * B + 2 * kappa ^ 2 * A) :=
    mul_le_mul_of_nonneg_left hZle hCnn
  have hadmiss' : 2 * C * kappa ^ 2 ≤ 3 * mass / 8 := by
    rw [hC_def]
    calc
      2 * (2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass) * kappa ^ 2 =
          (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 := by ring
      _ ≤ 3 * mass / 8 := hadmiss
  have hadmA : 2 * C * kappa ^ 2 * A ≤ 3 * mass / 8 * A :=
    mul_le_mul_of_nonneg_right hadmiss' hA0
  have hgoal : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) = 2 * C := by
    rw [hC_def]
    ring
  rw [hgoal]
  nlinarith only [hcombine, hZmul, hadmA]

/-- The `H¹` interior mass estimate at the effective localized upper
constant. -/
theorem agmonMass_localizedSplit_interior_le {Om : Set (Vec d)}
    (hOm : IsOpenBoundedConvexDomain Om) {a : CoeffField d}
    {ks kl : Vec d → Mat d} {u : H1Function Om} {g eta psi : Vec d → ℝ}
    {L : Set (Vec d)} {nu LamS Ks Kl mass kappa M : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmass : 0 < mass)
    (hM : 0 ≤ M)
    (hEllS : IsEllipticFieldOn nu LamS Om
      (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaOm : tsupport eta ⊆ Om) (hetaL : tsupport eta ⊆ L)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hg : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y ≠ 0 → g y * u.toFun y ≤ -(mass * u.toFun y ^ 2))
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hkappa : 8 * localizedAgmonUpper nu mass Ks Kl ^ 2 * kappa ^ 2 ≤
      nu * mass) :
    mass / 2 * ∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      4 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu *
        ∫ y in Om, u.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume := by
  have hL1 := two_mul_sq_le_localizedAgmonUpper_sq (mass := mass) hnu hKs hKl
  have hL2 := eight_mul_div_le_localizedAgmonUpper_sq hnu hmass hKs hKl
  have hcoef : 4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass ≤
      3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu := by
    rw [le_div_iff₀ hnu]
    have hexp : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * nu =
        4 * (nu + Ks) ^ 2 + 4 * nu * Kl ^ 2 / mass := by field_simp
    rw [hexp]
    have hLsq0 : (0 : ℝ) ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := sq_nonneg _
    have hL2' : 4 * nu * Kl ^ 2 / mass ≤
        localizedAgmonUpper nu mass Ks Kl ^ 2 := by
      refine le_trans ?_ hL2
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hfour : 4 * nu * Kl ^ 2 ≤ 8 * nu * Kl ^ 2 := by
        have h := mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 8)
          (mul_nonneg hnu.le (sq_nonneg Kl))
        linarith only [h]
      exact mul_le_mul_of_nonneg_right hfour (inv_pos.2 hmass).le
    linarith only [hL1, hL2', hLsq0]
  have hLsqk : localizedAgmonUpper nu mass Ks Kl ^ 2 * kappa ^ 2 ≤
      nu * mass / 8 := by linarith only [hkappa]
  have hadmiss : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 ≤
      3 * mass / 8 := by
    have hstep := mul_le_mul_of_nonneg_right hcoef (sq_nonneg kappa)
    have hval : 3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu * kappa ^ 2 ≤
        3 * mass / 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hnu]
      nlinarith only [hLsqk, hnu]
    linarith only [hstep, hval]
  have hbase := agmonMass_split_interior_le hOm hnu hKs hmass hM hEllS
    hsplit hksSkew hklSkew hklC1 hsol hMbound heta hetaCompact hetaOm hetaL
    hpsi hpsiGrad hg hksSize hklDiv hadmiss
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have hLsq : (0 : ℝ) ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := sq_nonneg _
    have hquarter : 3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu ≤
        4 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith only [hLsq]) (inv_pos.2 hnu).le
    linarith only [hcoef, hquarter]
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)))

/-! ### The sharp zero-divergence branch -/

/-- Effective upper constant for the interior estimate.  When the smooth
part has zero divergence bound, its transferred contribution vanishes and
the sharp rough-only constant `nu + Ks` is retained. -/
def localizedInteriorUpper (nu mass Ks Kl : ℝ) : ℝ :=
  if Kl = 0 then nu + Ks else localizedAgmonUpper nu mass Ks Kl

theorem localizedInteriorUpper_pos {nu mass Ks Kl : ℝ} (hnu : 0 < nu)
    (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) :
    0 < localizedInteriorUpper nu mass Ks Kl := by
  unfold localizedInteriorUpper
  split_ifs
  · linarith only [hnu, hKs]
  · exact localizedAgmonUpper_pos hnu hKs hKl

/-- The interior mass estimate at the sharp branched upper constant. -/
theorem agmonMass_localizedInterior_le {Om : Set (Vec d)}
    (hOm : IsOpenBoundedConvexDomain Om) {a : CoeffField d}
    {ks kl : Vec d → Mat d} {u : H1Function Om} {g eta psi : Vec d → ℝ}
    {L : Set (Vec d)} {nu LamS Ks Kl mass kappa M : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmass : 0 < mass)
    (hM : 0 ≤ M)
    (hEllS : IsEllipticFieldOn nu LamS Om
      (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaOm : tsupport eta ⊆ Om) (hetaL : tsupport eta ⊆ L)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hg : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y ≠ 0 → g y * u.toFun y ≤ -(mass * u.toFun y ^ 2))
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hkappa : 8 * localizedInteriorUpper nu mass Ks Kl ^ 2 * kappa ^ 2 ≤
      nu * mass) :
    mass / 2 * ∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      4 * localizedInteriorUpper nu mass Ks Kl ^ 2 / nu *
        ∫ y in Om, u.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume := by
  by_cases hzero : Kl = 0
  · subst Kl
    rw [localizedInteriorUpper, ite_eq_left rfl] at hkappa ⊢
    let chi : Vec d → ℝ := fun y => Real.exp (kappa * psi y)
    let zeta : Vec d → ℝ := fun y => eta y * chi y
    have hchi : ContDiff ℝ (⊤ : ℕ∞) chi := contDiff_exponentialWeight hpsi kappa
    have hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta := heta.mul hchi
    have hzetaCompact : HasCompactSupport zeta := hetaCompact.mul_right
    have hzetaOm : tsupport zeta ⊆ Om := tsupport_mul_subset hetaOm
    have hzetaL : tsupport zeta ⊆ L := tsupport_mul_subset hetaL
    have hadm := isAdmissibleMultiplier_localized_of_tsupport_subset hOm u
      heta hetaCompact hetaOm hchi
    have hgzeta : ∀ᵐ y ∂volumeMeasureOn Om, zeta y ≠ 0 →
        g y * u.toFun y ≤ -(mass * u.toFun y ^ 2) := by
      filter_upwards [hg] with y hy hzy
      exact hy fun heta0 => hzy (by simp only [zeta, heta0, zero_mul])
    have hDzero : (∫ y in Om, u.toFun y ^ 2 *
        vecDot (skewFieldDiv kl y)
          (fun i => (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i)) ∂volume) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with y
      change u.toFun y ^ 2 * vecDot (skewFieldDiv kl y)
        (fun i => (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i)) = (0 : ℝ)
      by_cases hyL : y ∈ L
      · have hle := hklDiv y hyL
        norm_num at hle
        have hnorm : vecNormSq (skewFieldDiv kl y) = 0 :=
          le_antisymm hle (vecNormSq_nonneg _)
        rw [vecNormSq_eq_zero hnorm]
        simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]
      · have hynSq : y ∉ tsupport (fun w => zeta w ^ 2) :=
          fun hy => hyL (tsupport_sq_weight_subset hzetaL hy)
        rw [fderiv_of_notMem_tsupport ℝ hynSq]
        simp only [zero_apply, vecDot, mul_zero,
          Finset.sum_const_zero]
    have hsplitEnergy := weightedEnergy_split_interior_le hOm hnu hKs hM hEllS
      hsplit hksSkew hklSkew hklC1 hsol hMbound hzeta hzetaCompact hzetaOm
      hzetaL hksSize
    have henergy : nu / 2 * ∫ y in Om, zeta y ^ 2 * vecNormSq (u.grad y) ∂volume ≤
        (∫ y in Om, g y * (zeta y ^ 2 * u.toFun y) ∂volume) +
          2 * (nu + Ks) ^ 2 / nu *
            ∫ y in Om, u.toFun y ^ 2 *
              vecNormSq (fun i => (fderiv ℝ zeta y) (basisVec i)) ∂volume := by
      rw [hDzero] at hsplitEnergy
      linarith only [hsplitEnergy]
    have hmassBound := weightedMass_le_of_energy hnu hsol hadm hgzeta henergy
    have hchiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
        vecNormSq (fun i => (fderiv ℝ chi y) (basisVec i)) ≤
          kappa ^ 2 * chi y ^ 2 := by
      filter_upwards [hpsiGrad] with y hy
      exact exponentialWeight_gradient_le hpsi hy kappa
    have hCbase : (0 : ℝ) ≤ 2 * (nu + Ks) ^ 2 / nu := by positivity
    have habs : 2 * (2 * (nu + Ks) ^ 2 / nu) * kappa ^ 2 ≤ mass / 2 := by
      rw [show 2 * (2 * (nu + Ks) ^ 2 / nu) * kappa ^ 2 =
        4 * (nu + Ks) ^ 2 * kappa ^ 2 / nu by ring, div_le_iff₀ hnu]
      linarith only [hkappa]
    have hfinal := localizedMass_absorb heta hetaCompact hchi hCbase hchiGrad
      habs hmassBound
    simp only [chi] at hfinal
    convert hfinal using 1
    all_goals ring
  · rw [localizedInteriorUpper, ite_eq_right hzero] at hkappa ⊢
    exact agmonMass_localizedSplit_interior_le hOm hnu hKs hKl hmass hM hEllS
      hsplit hksSkew hklSkew hklC1 hsol hMbound heta hetaCompact hetaOm hetaL
      hpsi hpsiGrad hg hksSize hklDiv hkappa

end DivergenceFormProcess.Decay
