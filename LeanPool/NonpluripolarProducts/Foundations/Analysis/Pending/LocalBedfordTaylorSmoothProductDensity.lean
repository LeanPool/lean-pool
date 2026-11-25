/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Densities for smooth local Bedford–Taylor products

Identifies products of smooth potentials with wedge densities in complex coordinates.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts TopDegreeDensity ProductTestForms
  LocalBedfordTaylorCollar LocalBedfordTaylorDecreasing
  LocalBedfordTaylorWedgeAssociation LocalBedfordTaylorSmoothDensity

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Smoothness of the actual finite exterior product of smooth two-form maps. -/
theorem contDiffOn_wedgeProd : ∀ (q : ℕ) (β : Fin q → ComplexModel n → RealForm n 2),
    (∀ i, ContDiffOn ℝ ∞ (β i) U) →
    ContDiffOn ℝ ∞ (fun x => wedgeProd q (fun i => β i x)) U
  | 0, _, _ => contDiffOn_const
  | q + 1, β, hβ => by
    exact contDiffOn_coordinateWedge
      (contDiffOn_wedgeProd q (fun i => β i.castSucc) (fun i => hβ i.castSucc))
      (hβ (Fin.last q))

/-- Every finite product of full one-one span forms lies in the full prescribed span. -/
theorem wedgeProd_mem_formSpan : ∀ (q : ℕ) (β : Fin q → RealForm n 2),
    (∀ i, β i ∈ formSpan n 1) → wedgeProd q β ∈ formSpan n q
  | 0, _, _ => (kahlerPower n 0).2
  | q + 1, β, hβ =>
    wedgeTo_mem_formSpan (wedgeProd_mem_formSpan q (fun i => β i.castSucc)
      (fun i => hβ i.castSucc)) (hβ (Fin.last q)) rfl

private theorem wedgeForm_unit {r : ℕ} (T : LocalProductCurrent n U r) :
    wedgeForm (r := r) (k := 0) rfl T
      (contDiffOn_const (c := (coordinateWedgeUnit : RealForm n 0))) = T := by
  classical
  ext γ φ
  rw [wedgeForm_apply_eq (r := r) (k := 0) rfl T
    (α := fun _ : ComplexModel n => (coordinateWedgeUnit : RealForm n 0))
    contDiffOn_const (fun _ _ => (kahlerPower n 0).2)
    (fun _ : Unit => fun _ : ComplexModel n => (1 : ℝ))
    (fun _ => contDiffOn_const) (fun _ => kahlerPower n 0)
    (fun _ _ => by
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl)]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have eγ : wedgeSpan n rfl γ (kahlerPower n 0) = γ := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply rfl _ _ (by omega)]
    change wedgeTo (by omega : 2 * r + 0 = 2 * r) (γ : RealForm n (2 * r))
      (coordinateWedgeUnit : RealForm n 0) = γ
    rw [wedgeTo_unit_right (by omega) rfl]
    rfl
  have eφ : mulSmoothOnCLM (contDiffOn_const (c := (1 : ℝ))) φ = φ := by
    ext x
    simp only [mulSmoothOnCLM_apply, mul_one]
  rw [eγ, eφ]

private theorem wedgeForm_castLPC {a b r k : ℕ} (hab : a = b) (h : r + k = a)
    (T : LocalProductCurrent n U a) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab T) hα = wedgeForm h T hα := by
  subst hab
  rfl

/-- The genuine recursive current for smooth PSH potentials is its finite smooth wedge. -/
theorem btProduct_eq_wedgeForm : ∀ (q r : ℕ) (u : Fin q → ComplexModel n → ℝ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (u i) U),
    (∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) U) →
    ∀ (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
      btProduct q r u T = wedgeForm rfl T
        (contDiffOn_wedgeProd q (fun i => ddcForm (u i))
          (fun i => contDiffOn_ddcForm (hg i)))
  | 0, r, u, hg, hp, T, hT, hTc => (wedgeForm_unit T).symm
  | q + 1, r, u, hg, hp, T, hT, hTc => by
    have hdeg : r + (q + 1) = r + 1 + q := by omega
    let T' := castLPC hdeg T
    have hT' : IsPositive T' := isPositive_castLPC hdeg hT
    have hTc' : IsClosedAny (r + 1 + q) T' := isClosedAny_castLPC hdeg hTc
    have hlevi (i : Fin (q + 1)) : ∀ z ∈ U, ∀ v, 0 ≤ leviForm (u i) z v :=
      fun _ hz v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (hg i) (hp i) hz v
    have hub (i : Fin (q + 1)) : IsLocallyBoundedPshOn U (u i) :=
      isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh (hg i) (hp i))
    have e := btProduct_wedgeForm_ddcForm (hg (Fin.last q)) (hlevi (Fin.last q))
      q r (Fin.init u) T' (by omega) hT' hTc' (fun i => hub i.castSucc)
    have ew : wedgeForm (r := r + q) (k := 1)
        (by omega : r + q + 1 = r + 1 + q) T'
        (contDiffOn_ddcForm (hg (Fin.last q))) =
        wedgeForm (r := r + q) (k := 1) rfl T
          (contDiffOn_ddcForm (hg (Fin.last q))) :=
      wedgeForm_castLPC (r := r + q) (k := 1) hdeg rfl T
        (contDiffOn_ddcForm (hg (Fin.last q)))
    rw [ew] at e
    rw [btProduct_succ, ddcMul_eq_ddcWedge hT hTc (hg (Fin.last q)),
      ddcWedge_eq_wedgeForm, e,
      btProduct_eq_wedgeForm q (r + 1) (Fin.init u) (fun i => hg i.castSucc)
        (fun i => hp i.castSucc) T' hT' hTc', ddcWedge_eq_wedgeForm]
    rw [wedgeForm_wedge_two rfl T'
      (contDiffOn_wedgeProd q (fun i => ddcForm (Fin.init u i))
        (fun i => contDiffOn_ddcForm (hg i.castSucc)))
      (contDiffOn_ddcForm (hg (Fin.last q)))
      (fun x hx => wedgeProd_mem_formSpan q _
        (fun i => ddcForm_mem_formSpan (hg i.castSucc) (hlevi i.castSucc) x hx))
      (ddcForm_mem_formSpan (hg (Fin.last q)) (hlevi (Fin.last q)))]
    exact wedgeForm_castLPC (r := r) (k := q + 1) hdeg rfl T
      (contDiffOn_wedgeProd (q + 1) (fun i => ddcForm (u i))
        (fun i => contDiffOn_ddcForm (hg i)))

private theorem wedgeForm_oneCurrentOf {r q : ℕ} (h : r + q = n)
    {α : ComplexModel n → RealForm n (2 * q)} (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (r := r) (k := q) rfl (oneCurrentOf (U := U) h) hα =
      wedgeForm h (oneCurrent U) hα := by
  cases h
  rfl

/-- The actual top-degree smooth BT current evaluates by the genuine mixed Hessian density. -/
theorem btProduct_oneCurrent_apply {u : Fin n → ComplexModel n → ℝ}
    (hg : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hp : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) U) (φ : 𝓓(U, ℝ)) :
    btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n)) (kahlerPower n 0) φ =
      ∫ z, φ z * MixedMongeAmpere.mixedDensity u z := by
  rw [btProduct_eq_wedgeForm n 0 u hg hp _ (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _), wedgeForm_oneCurrentOf]
  rw [wedgeForm_oneCurrent_apply (Nat.zero_add n)
    (contDiffOn_wedgeProd n (fun i => ddcForm (u i))
      (fun i => contDiffOn_ddcForm (hg i)))
    (fun x hx => wedgeProd_mem_formSpan n _
      (fun i => ddcForm_mem_formSpan (hg i)
        (fun _ hz v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (hg i) (hp i) hz v)
        x hx))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ U
  · change φ z * topDensity (wedgeTo (by omega : 0 + 2 * n = 2 * n)
      (coordinateWedgeUnit : RealForm n 0)
      (wedgeProd n (fun i => ddcForm (u i) z))) = _
    rw [wedgeTo_unit_left (by omega) rfl]
    change φ z * topDensity (wedgeProd n (fun i => smoothDDC (u i) z)) = _
    rw [topDensity_wedgeProd, actualMixedTopDensity_smoothDDC
      (fun i => ((hg i).contDiffAt (U.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  · simp only [LocalBedfordTaylorLocality.testFunction_eq_zero_of_notMem _ hz, zero_mul]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
