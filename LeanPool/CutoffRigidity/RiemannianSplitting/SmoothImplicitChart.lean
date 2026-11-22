/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RegularLevelLocalChart
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Smoothness of the constructed implicit-function chart and inverse -/

@[expose] public section
open Set
open scoped ContDiff Topology

namespace CutoffRigidity
variable {n : ℕ}
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The actual implicit-function chart is `C¹` at its original point whenever
the original equation and the chosen complementary coordinate are `C¹`. -/
theorem contDiffAt_implicitChart (φ : ImplicitFunctionData ℝ E F G)
    (hl : ContDiffAt ℝ n φ.leftFun φ.pt) (hr : ContDiffAt ℝ n φ.rightFun φ.pt) :
    ContDiffAt ℝ n φ.toOpenPartialHomeomorph φ.pt := by
  rw [φ.toOpenPartialHomeomorph_coe]
  have heq : φ.prodFun = fun x ↦ (φ.leftFun x, φ.rightFun x) := funext φ.prodFun_apply
  rw [heq]
  exact hl.prodMk hr

/-- The actual inverse of the constructed chart is `C¹` at the corresponding
point. Its differentiability is obtained from the actual inverse theorem. -/
theorem contDiffAt_implicitChart_symm (φ : ImplicitFunctionData ℝ E F G)
    (hl : ContDiffAt ℝ n φ.leftFun φ.pt) (hr : ContDiffAt ℝ n φ.rightFun φ.pt) :
    ContDiffAt ℝ n φ.toOpenPartialHomeomorph.symm (φ.prodFun φ.pt) := by
  have hc := contDiffAt_implicitChart φ hl hr
  let L := φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
    φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hD : HasFDerivAt φ.toOpenPartialHomeomorph (L : E →L[ℝ] F × G) φ.pt := by
    rw [φ.toOpenPartialHomeomorph_coe]
    exact φ.hasStrictFDerivAt.hasFDerivAt
  have htarget : φ.prodFun φ.pt ∈ φ.toOpenPartialHomeomorph.target := by
    simpa only [φ.prodFun_apply] using φ.map_pt_mem_toOpenPartialHomeomorph_target
  have hpoint : φ.toOpenPartialHomeomorph.symm (φ.prodFun φ.pt) = φ.pt := by
    rw [← φ.toOpenPartialHomeomorph_coe]
    exact φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
  apply φ.toOpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ) (n := n) (f₀' := L) htarget
  · rw [hpoint]
    exact hD
  · rw [hpoint]
    exact hc

omit [CompleteSpace E] [CompleteSpace F] in
/-- Restrict actual locally smooth inverse coordinates to domains where both
coordinate directions are smooth everywhere. -/
theorem exists_contDiff_restriction (e : OpenPartialHomeomorph E F) {a : E}
    (ha : a ∈ e.source) (he : ContDiffAt ℝ n e a)
    (hi : ContDiffAt ℝ n e.symm (e a)) :
    ∃ c : OpenPartialHomeomorph E F,
      a ∈ c.source ∧ c.source ⊆ e.source ∧
      (∀ x, c x = e x) ∧ (∀ y, c.symm y = e.symm y) ∧
      ContDiffOn ℝ n c c.source ∧ ContDiffOn ℝ n c.symm c.target := by
  obtain ⟨u, hu, hcu⟩ := he.contDiffOn (le_refl (n : ℕ∞ω)) (by simp)
  obtain ⟨v, hv, hcv⟩ := hi.contDiffOn (le_refl (n : ℕ∞ω)) (by simp)
  obtain ⟨uo, huou, huo, hau⟩ := mem_nhds_iff.mp hu
  obtain ⟨vo, hvov, hvo, hav⟩ := mem_nhds_iff.mp hv
  let s := uo ∩ (e.source ∩ e ⁻¹' vo)
  have hs : IsOpen s := huo.inter (e.isOpen_inter_preimage hvo)
  let c := e.restrOpen s hs
  have hsrc : c.source = e.source ∩ s := e.restrOpen_source s hs
  have hraw : (c : E → F) = e := e.coe_restrOpen hs
  have hinv : (c.symm : F → E) = e.symm := e.coe_restrOpen_symm hs
  refine ⟨c, ?_, ?_, fun x ↦ congrFun hraw x, fun y ↦ congrFun hinv y, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨ha, hau, ha, hav⟩
  · rw [hsrc]
    exact inter_subset_left
  · rw [hraw]
    apply hcu.mono
    intro x hx
    rw [hsrc] at hx
    exact huou hx.2.1
  · rw [hinv]
    apply hcv.mono
    intro y hy
    have hxy := c.map_target hy
    rw [hsrc] at hxy
    have hyy : e (c.symm y) = y := by rw [← hraw]; exact c.right_inv hy
    have hv' := hxy.2.2.2
    change e (c.symm y) ∈ vo at hv'
    rw [hyy] at hv'
    exact hvov hv'

section Scalar
variable [FiniteDimensional ℝ E]

/-- The scalar implicit theorem supplies actual `C¹` coordinates in both
directions on open neighborhoods, with the exact original scalar coordinate. -/
theorem exists_contDiff_regularScalar_coordinates {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ n f a) (hn : n ≠ 0) (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ∃ e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ f a).ker),
      a ∈ e.source ∧ e a = (f a, 0) ∧ (∀ x, (e x).1 = f x) ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  let D := fderiv ℝ f a
  have hnonzero : (↑n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hn
  have hd : HasStrictFDerivAt f D a :=
    hf.hasStrictFDerivAt (hf.differentiableAt hnonzero).hasFDerivAt hnonzero
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hker := D.ker_closedComplemented_of_finiteDimensional_range
  let φ : ImplicitFunctionData ℝ E ℝ D.ker :=
    { leftFun := f
      leftDeriv := D
      rightFun := fun x ↦ Classical.choose hker (x - a)
      rightDeriv := Classical.choose hker
      pt := a
      hasStrictFDerivAt_leftFun := hd
      hasStrictFDerivAt_rightFun := (Classical.choose hker).hasStrictFDerivAt.comp a
        ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hrange
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  have hl : ContDiffAt ℝ n φ.leftFun φ.pt := by
    exact hf
  have hr : ContDiffAt ℝ n φ.rightFun φ.pt := by
    change ContDiffAt ℝ n (fun x ↦ Classical.choose hker (x - a)) a
    exact ((Classical.choose hker).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hc := contDiffAt_implicitChart φ hl hr
  have hi := contDiffAt_implicitChart_symm φ hl hr
  have hcoe (x : E) : φ.toOpenPartialHomeomorph x = (f x, Classical.choose hker (x - a)) := by
    exact φ.toOpenPartialHomeomorph_apply x
  have hcenter : φ.toOpenPartialHomeomorph a = (f a, 0) := by
    rw [hcoe, sub_self, map_zero]
  have ha : a ∈ φ.toOpenPartialHomeomorph.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hi' : ContDiffAt ℝ n φ.toOpenPartialHomeomorph.symm (φ.toOpenPartialHomeomorph a) := by
    convert! hi using 1
    exact (φ.toOpenPartialHomeomorph_coe ▸ rfl)
  obtain ⟨e, he, _, hraw, _, hforward, hbackward⟩ :=
    exists_contDiff_restriction φ.toOpenPartialHomeomorph ha hc hi'
  refine ⟨e, he, ?_, ?_, hforward, hbackward⟩
  · rw [hraw, hcenter]
  · intro x
    rw [hraw, hcoe]

end Scalar

end CutoffRigidity
