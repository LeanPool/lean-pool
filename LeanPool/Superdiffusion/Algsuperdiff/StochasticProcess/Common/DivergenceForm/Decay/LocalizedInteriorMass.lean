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
  have hDle := integral_sq_mul_vecDot_skewFieldDiv_le (u := u)
    (kl := kl) (L := L) (mass := mass) hmass hzetaSmooth hzetaCompact hzetaL
    hklC1 hklDiv
  exact agmonMass_split_of_energy_le hnu hmass heta hetaCompact hchiSmooth hchiGrad
    hsol hadm hgzeta hsplitEnergy hDle hadmiss

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
  refine agmonMass_normalize_effective_constant hnu hmass hKs hKl hkappa
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)))) ?_
  intro hadmiss
  exact agmonMass_split_interior_le hOm hnu hKs hmass hM hEllS hsplit hksSkew
    hklSkew hklC1 hsol hMbound heta hetaCompact hetaOm hetaL hpsi hpsiGrad hg
    hksSize hklDiv hadmiss

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
