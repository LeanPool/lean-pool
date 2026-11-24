/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoComplexProducts

/-!
# Genuine covector product calculus in arbitrary degree

The existing actual covector exterior product is a continuous bilinear map.
Its associativity and anticommutation give the actual one-form exterior
Leibniz rule via the existing coordinate sum formula for the exterior derivative.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoCovectorProducts

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ConstantFormProducts
  ClosedProductCurrents CoordinateWedgeAssoc LocalBedfordTaylorProducts ProductTestForms

noncomputable section

variable {n k : ℕ}

/-- The existing actual covector-to-one-form construction as a continuous linear map. -/
def oneFormCLM (n : ℕ) : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] RealForm n 1 :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexModel n)
    (F := ℝ) (ι := Fin 1) (0 : Fin 1)).toContinuousLinearMap

@[simp] theorem oneFormCLM_apply (L : ComplexModel n →L[ℝ] ℝ) :
    oneFormCLM n L = oneForm n L := rfl

/-- Wedge multiplication by an actual covector is a continuous bilinear map. -/
def covectorWedgeCLM (n k : ℕ) :
    (ComplexModel n →L[ℝ] ℝ) →L[ℝ] RealForm n k →L[ℝ] RealForm n (k + 1) :=
  haveI := realForm_finiteDimensional (n := n) k
  let W := (wedgeToBilin n (Nat.add_comm 1 k)).comp (oneFormCLM n).toLinearMap
  LinearMap.toContinuousLinearMap
    { toFun := fun L => LinearMap.toContinuousLinearMap (W L)
      map_add' := fun L L' => by
        ext A : 1
        simp only [map_add]
      map_smul' := fun c L => by
        ext A : 1
        simp only [map_smul, RingHom.id_apply] }

@[simp] theorem covectorWedgeCLM_apply (L : ComplexModel n →L[ℝ] ℝ) (A : RealForm n k) :
    covectorWedgeCLM n k L A = oneWedge L A :=
  wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 k) L A

/-- Associativity of actual covector multiplication with every degree form. -/
theorem oneWedge_oneWedge_eq_wedgeTo (L K : ComplexModel n →L[ℝ] ℝ) (A : RealForm n k) :
    oneWedge L (oneWedge K A) = wedgeTo (by omega : 2 + k = k + 1 + 1)
      (coordinateWedge (oneForm n L) (oneForm n K)) A := by
  rw [← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 (k + 1)),
    ← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 k)]
  exact (wedgeTo_assoc rfl (by omega) (Nat.add_comm 1 k)
    (Nat.add_comm 1 (k + 1)) (oneForm n L) (oneForm n K) A).symm

/-- Actual covector multiplication anticommutes in every degree. -/
theorem oneWedge_anticommute (L K : ComplexModel n →L[ℝ] ℝ) (A : RealForm n k) :
    oneWedge L (oneWedge K A) = -oneWedge K (oneWedge L A) := by
  rw [oneWedge_oneWedge_eq_wedgeTo, coordinateWedge_comm_one, wedgeTo_neg_left,
    ← oneWedge_oneWedge_eq_wedgeTo]

private theorem oneWedge_add_right (L : ComplexModel n →L[ℝ] ℝ) (A B : RealForm n k) :
    oneWedge L (A + B) = oneWedge L A + oneWedge L B := by
  simpa only [covectorWedgeCLM_apply] using (covectorWedgeCLM n k L).map_add A B

private theorem oneWedge_sum_right {ι : Type*} (s : Finset ι)
    (L : ComplexModel n →L[ℝ] ℝ) (A : ι → RealForm n k) :
    oneWedge L (∑ i ∈ s, A i) = ∑ i ∈ s, oneWedge L (A i) := by
  simpa only [covectorWedgeCLM_apply] using map_sum (covectorWedgeCLM n k L) A s

/-- The genuine exterior product rule for a differentiable actual covector field. -/
theorem extDeriv_oneWedge_eq {L : ComplexModel n → (ComplexModel n →L[ℝ] ℝ)}
    {A : ComplexModel n → RealForm n k} {x : ComplexModel n}
    (hL : DifferentiableAt ℝ L x) (hA : DifferentiableAt ℝ A x) :
    extDeriv (fun y => oneWedge (L y) (A y)) x =
      wedgeTo (by omega : 2 + k = k + 1 + 1)
        (extDeriv (fun y => oneForm n (L y)) x) (A x) -
          oneWedge (L x) (extDeriv A x) := by
  let W := covectorWedgeCLM n k
  have hWL : HasFDerivAt (fun y => W (L y)) (W.comp (fderiv ℝ L x)) x := by
    apply HasFDerivAt.of_isLittleOTVS
    have hsmall := hL.hasFDerivAt.isLittleOTVS
    have hh := (ContinuousLinearMap.isBigOTVS_fun_comp
      (E := ComplexModel n →L[ℝ] ℝ) (F := RealForm n k →L[ℝ] RealForm n (k + 1)) W
      (f := fun y => L y - L x - fderiv ℝ L x (y - x))
      (l := 𝓝 x)).trans_isLittleOTVS hsmall
    simpa only [map_sub, ContinuousLinearMap.comp_apply] using hh
  have hprod := hWL.clm_apply hA.hasFDerivAt
  have hD (v : ComplexModel n) :
      fderiv ℝ (fun y => oneWedge (L y) (A y)) x v =
        oneWedge (fderiv ℝ L x v) (A x) + oneWedge (L x) (fderiv ℝ A x v) := by
    have hfun : (fun y => oneWedge (L y) (A y)) = fun y => W (L y) (A y) :=
      funext fun y => (covectorWedgeCLM_apply (L y) (A y)).symm
    rw [hfun, hprod.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    dsimp only [W]
    simp only [covectorWedgeCLM_apply]
    exact add_comm _ _
  have hDb (v : ComplexModel n) :
      fderiv ℝ (fun y => oneForm n (L y)) x v = oneForm n (fderiv ℝ L x v) := by
    change fderiv ℝ (fun y => oneFormCLM n (L y)) x v = _
    have hd : HasFDerivAt (fun y => oneFormCLM n (L y))
        ((oneFormCLM n).comp (fderiv ℝ L x)) x :=
      (oneFormCLM n).hasFDerivAt.comp x hL.hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [extDeriv_eq_sum_oneWedge]
  simp_rw [hD, oneWedge_add_right]
  rw [Finset.sum_add_distrib]
  have hfirst : ∑ a, oneWedge (coordCLM n a) (oneWedge (fderiv ℝ L x (realBasis n a)) (A x)) =
      wedgeTo (by omega : 2 + k = k + 1 + 1)
        (extDeriv (fun y => oneForm n (L y)) x) (A x) := by
    simp_rw [oneWedge_oneWedge_eq_wedgeTo]
    rw [← wedgeTo_sum_left, extDeriv_eq_sum_oneWedge]
    simp only [hDb, ← wedgeTo_oneForm_eq_oneWedge (rfl : 1 + 1 = 1 + 1), wedgeTo_rfl]
  have hsecond : ∑ a, oneWedge (coordCLM n a) (oneWedge (L x) (fderiv ℝ A x (realBasis n a))) =
      -oneWedge (L x) (extDeriv A x) := by
    conv_lhs => arg 2; intro a; rw [oneWedge_anticommute]
    rw [Finset.sum_neg_distrib, ← oneWedge_sum_right, ← extDeriv_eq_sum_oneWedge]
  rw [hfirst, hsecond, sub_eq_add_neg]

end

end SGPT.Foundations.Analysis.Pending.XiaoCovectorProducts
