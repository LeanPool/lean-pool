/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedLocalL2
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSkewDivergence

/-!
# LocalizedSplitSkew

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weighted energy inequality with a split antisymmetric part

The antisymmetric part of the coefficient is split as `k = ks + kl`, with `ks`
merely bounded and `kl` continuously differentiable.  The two parts are paid
for differently.

* The rough part `ks` enters the flux cross term and is bounded there by its
  size on the transition layer, exactly as in the unsplit estimate.
* The smooth part `kl` is a divergence-free drift: for every zero-trace test
  the flux `kl grad z` pairs as `-(test) ⟨div kl, grad z⟩`, so the solution of
  the equation with coefficient `a` also solves the equation with coefficient
  `nu • I + ks` and the extra forcing `⟨div kl, grad z⟩`.  The cross term this
  produces is then integrated by parts and carries `‖div kl‖` rather than
  `‖kl‖`.

The resulting energy inequality keeps the drift term as an exact quantity on
the left, so no absolute value is committed to before the weight is chosen.

## Main results

- `DivergenceFormProcess.Decay.isScalarForcedWeakSolution_of_splitSkew`
- `DivergenceFormProcess.Decay.weightedEnergy_split_le`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ}

/-! ### The smooth antisymmetric part as a drift -/

/-- **The smooth antisymmetric part is a drift.**  A zero-trace solution of the
equation with coefficient `a = nu • I + ks + kl`, with `kl` a `C¹`
antisymmetric field, is a solution of the equation with coefficient
`nu • I + ks` and the extra forcing `⟨div kl, grad z⟩`. -/
theorem isScalarForcedWeakSolution_of_splitSkew {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {a : CoeffField d} {ks kl : Vec d → Mat d} {nu LamS : ℝ}
    {z : H10Function Om} {g : Vec d → ℝ}
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g z.toH1Function) :
    IsScalarForcedWeakSolution (fun y => nu • (1 : Mat d) + ks y) Om
      (fun y => g y + vecDot (skewFieldDiv kl y) (z.toH1Function.grad y))
      z.toH1Function := by
  classical
  have hUm : MeasurableSet Om := hOmOpen.measurableSet
  have hbG : MemScalarL2 Om
      (fun y => vecDot (skewFieldDiv kl y) (z.toH1Function.grad y)) :=
    memScalarL2_vecDot_skewFieldDiv hUm hOmBdd hklC1
      z.toH1Function.gradMemL2
  have hfluxS : MemVectorL2 Om
      (fun y => matVecMul (nu • (1 : Mat d) + ks y) (z.toH1Function.grad y)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllS
      z.toH1Function.grad_memVectorL2
  have hfluxL : MemVectorL2 Om
      (fun y => matVecMul (kl y) (z.toH1Function.grad y)) :=
    MemLp.of_eval fun i =>
      memScalarL2_matVecMul_coord hUm hOmBdd hklC1
        z.toH1Function.gradMemL2 i
  refine ⟨hsol.1.add hbG, fun phi => ?_⟩
  have hgradPhi := phi.toH1Function.grad_memVectorL2
  have hintS : Integrable (fun y =>
      vecDot (matVecMul (nu • (1 : Mat d) + ks y) (z.toH1Function.grad y))
        (phi.toH1Function.grad y)) (volumeMeasureOn Om) :=
    integrableOn_vecDot_of_memVectorL2 hfluxS hgradPhi
  have hintL : Integrable (fun y =>
      vecDot (matVecMul (kl y) (z.toH1Function.grad y))
        (phi.toH1Function.grad y)) (volumeMeasureOn Om) :=
    integrableOn_vecDot_of_memVectorL2 hfluxL hgradPhi
  have hgInt : Integrable
      (fun y => g y * phi.toH1Function.toFun y) (volumeMeasureOn Om) :=
    hsol.1.integrable_mul phi.toH1Function.memL2
  have hbInt : Integrable
      (fun y => vecDot (skewFieldDiv kl y) (z.toH1Function.grad y) *
        phi.toH1Function.toFun y) (volumeMeasureOn Om) :=
    hbG.integrable_mul phi.toH1Function.memL2
  have hsum : (∫ y in Om, vecDot (matVecMul (a y) (z.toH1Function.grad y))
        (phi.toH1Function.grad y) ∂volume) =
      (∫ y in Om,
        vecDot (matVecMul (nu • (1 : Mat d) + ks y) (z.toH1Function.grad y))
          (phi.toH1Function.grad y) ∂volume) +
        ∫ y in Om, vecDot (matVecMul (kl y) (z.toH1Function.grad y))
          (phi.toH1Function.grad y) ∂volume := by
    rw [← integral_add hintS hintL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hsplit y]
    have hmv : matVecMul (nu • (1 : Mat d) + ks y + kl y)
          (z.toH1Function.grad y) =
        fun i => matVecMul (nu • (1 : Mat d) + ks y) (z.toH1Function.grad y) i +
          matVecMul (kl y) (z.toH1Function.grad y) i := by
      funext i
      simp only [matVecMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hmv]
    simp only [vecDot, add_mul, Finset.sum_add_distrib]
  have htransfer := integral_vecDot_matVecMul_grad_eq_neg hUm hOmBdd hklC1
    hklSkew z phi
  have hforcing : (∫ y in Om,
      (g y + vecDot (skewFieldDiv kl y) (z.toH1Function.grad y)) *
        phi.toH1Function.toFun y ∂volume) =
      (∫ y in Om, g y * phi.toH1Function.toFun y ∂volume) +
        ∫ y in Om, vecDot (skewFieldDiv kl y) (z.toH1Function.grad y) *
          phi.toH1Function.toFun y ∂volume := by
    rw [← integral_add hgInt hbInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hcomm : (∫ y in Om,
      phi.toH1Function.toFun y *
        vecDot (skewFieldDiv kl y) (z.toH1Function.grad y) ∂volume) =
      ∫ y in Om, vecDot (skewFieldDiv kl y) (z.toH1Function.grad y) *
        phi.toH1Function.toFun y ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [hforcing]
  have hweak := hsol.2 phi
  rw [hsum] at hweak
  rw [hcomm] at htransfer
  linarith only [hweak, htransfer]

/-! ### The energy inequality with a split antisymmetric part -/

/-- **The weighted energy inequality with a split antisymmetric part.**  The
rough part is charged to its size on the layer through the Young inequality;
the smooth part appears as the exact drift term on the left, carrying only the
divergence of the smooth part and no gradient of the solution. -/
theorem weightedEnergy_split_le {Om : Set (Vec d)} (hOmOpen : IsOpen Om)
    (hOmBdd : IsBoundedDomain Om) {a : CoeffField d} {ks kl : Vec d → Mat d}
    {z : H10Function Om} {g zeta : Vec d → ℝ} {L : Set (Vec d)}
    {nu LamS Ks : ℝ} (hnu : 0 < nu) (hKs : 0 ≤ Ks)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g z.toH1Function)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta)
    (hzetaL : tsupport zeta ⊆ L)
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v) :
    nu / 2 * (∫ x in Om, zeta x ^ 2 * vecNormSq (z.toH1Function.grad x) ∂volume) +
        1 / 2 * ∫ x in Om, z.toH1Function.toFun x ^ 2 *
          vecDot (skewFieldDiv kl x)
            (fun i => (fderiv ℝ (fun y => zeta y ^ 2) x) (basisVec i)) ∂volume ≤
      (∫ x in Om, g x * (zeta x ^ 2 * z.toH1Function.toFun x) ∂volume) +
        2 * (nu + Ks) ^ 2 / nu *
          ∫ x in Om, z.toH1Function.toFun x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i)) ∂volume := by
  classical
  have hUm : MeasurableSet Om := hOmOpen.measurableSet
  have hsolS := isScalarForcedWeakSolution_of_splitSkew hOmOpen hOmBdd hEllS
    hsplit hklSkew hklC1 hsol
  have hadm := isAdmissibleMultiplier_sq_of_zeroTrace z hzeta hzetaCompact
  have hCpos : (0 : ℝ) < nu + Ks := by linarith only [hnu, hKs]
  have hlayer : ∀ y ∈ Om, fderiv ℝ zeta y ≠ 0 → ∀ v : Vec d,
      vecNormSq (matVecMul (nu • (1 : Mat d) + ks y) v) ≤
        (nu + Ks) ^ 2 * vecNormSq v := by
    intro y _ hne v
    have hyL : y ∈ L := by
      refine hzetaL ?_
      by_contra hcon
      exact hne (fderiv_of_notMem_tsupport ℝ hcon)
    exact vecNormSq_matVecMul_le_add_of_scalar_add_skew hnu.le hKs rfl
      (hksSkew y) (hksSize y hyL v)
  have henergy := weightedEnergy_localized_le hnu hCpos hEllS
    (fun y => rfl) hksSkew hsolS hzeta hzetaCompact hadm hlayer
  have hsqSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => zeta y ^ 2) :=
    (sq_weight_smooth hzeta hzetaCompact).1
  have hsqCompact : HasCompactSupport (fun y => zeta y ^ 2) :=
    (sq_weight_smooth hzeta hzetaCompact).2
  have hdrift := integral_mul_mul_vecDot_skewFieldDiv_eq hUm hOmBdd hklC1
    hklSkew z hsqSmooth hsqCompact
  have hforcing : (∫ x in Om,
      (g x + vecDot (skewFieldDiv kl x) (z.toH1Function.grad x)) *
        (zeta x ^ 2 * z.toH1Function.toFun x) ∂volume) =
      (∫ x in Om, g x * (zeta x ^ 2 * z.toH1Function.toFun x) ∂volume) +
        ∫ x in Om, zeta x ^ 2 * z.toH1Function.toFun x *
          vecDot (skewFieldDiv kl x) (z.toH1Function.grad x) ∂volume := by
    have hprodL2 : MemScalarL2 Om
        (fun x => zeta x ^ 2 * z.toH1Function.toFun x) := by
      obtain ⟨w, hwval, -⟩ := hadm
      have hw := w.toH1Function.memL2
      rwa [hwval] at hw
    have hbG : MemScalarL2 Om
        (fun y => vecDot (skewFieldDiv kl y) (z.toH1Function.grad y)) :=
      memScalarL2_vecDot_skewFieldDiv hUm hOmBdd hklC1
        z.toH1Function.gradMemL2
    have h1 : Integrable
        (fun x => g x * (zeta x ^ 2 * z.toH1Function.toFun x))
        (volumeMeasureOn Om) := hsol.1.integrable_mul hprodL2
    have h2 : Integrable
        (fun x => zeta x ^ 2 * z.toH1Function.toFun x *
          vecDot (skewFieldDiv kl x) (z.toH1Function.grad x))
        (volumeMeasureOn Om) := hprodL2.integrable_mul hbG
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hforcing, hdrift] at henergy
  linarith only [henergy]


end DivergenceFormProcess.Decay
