/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # `C^∞` adapted coordinates for a vector-valued submersion (Euclidean level)

For `Ψ : E → G` of class `C^∞` on an open set `T` with surjective differential at `a ∈ T`, there
  is an
open partial homeomorphism `e : E → G × ker DΨ(a)` with `e = (Ψ, P(· - a))`, both `e` and `e.symm`
being `C^∞` on their domains.  This is the implicit function theorem, with the chart shrunk so that
smoothness holds on the whole domain (Mathlib only gives smoothness of the inverse at one point).
-/

@[expose] public section
open Set
open scoped ContDiff Topology

namespace CutoffRigidity.Riemann

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_contDiff_regular_coordinates (Ψ : E → G) {T : Set E} (hT : IsOpen T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) {a : E} (ha : a ∈ T)
    (hsurj : Function.Surjective (fderiv ℝ Ψ a)) :
    ∃ e : OpenPartialHomeomorph E (G × (fderiv ℝ Ψ a).ker),
      a ∈ e.source ∧ e.source ⊆ T ∧ e a = (Ψ a, 0) ∧ (∀ x, (e x).1 = Ψ x) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := fderiv ℝ Ψ a
  have hΨa : ContDiffAt ℝ ∞ Ψ a := hΨ.contDiffAt (hT.mem_nhds ha)
  have hd : HasStrictFDerivAt Ψ D a := hΨa.hasStrictFDerivAt (hΨa.differentiableAt (by
    simp)).hasFDerivAt (by simp)
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hker := D.ker_closedComplemented_of_finiteDimensional_range
  let P : E →L[ℝ] D.ker := Classical.choose hker
  have hP := Classical.choose_spec hker
  let φ : ImplicitFunctionData ℝ E G D.ker :=
    { leftFun := Ψ
      leftDeriv := D
      rightFun := fun x ↦ P (x - a)
      rightDeriv := P
      pt := a
      hasStrictFDerivAt_leftFun := hd
      hasStrictFDerivAt_rightFun := P.hasStrictFDerivAt.comp a
        ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hrange
      range_rightDeriv := LinearMap.range_eq_of_proj hP
      isCompl_ker := LinearMap.isCompl_of_proj hP }
  let e₀ := φ.toOpenPartialHomeomorph
  have he₀ : ∀ x, e₀ x = (Ψ x, P (x - a)) := fun x => φ.toOpenPartialHomeomorph_apply x
  have ha₀ : a ∈ e₀.source := φ.pt_mem_toOpenPartialHomeomorph_source
  -- derivative of the formula on `T`
  let L : E → E →L[ℝ] (G × D.ker) := fun x =>
    (ContinuousLinearMap.inl ℝ G D.ker).comp (fderiv ℝ Ψ x) +
      (ContinuousLinearMap.inr ℝ G D.ker).comp P
  have hderiv : ∀ x ∈ T, HasFDerivAt e₀ (L x) x := by
    intro x hx
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ x) x :=
      ((hΨ.contDiffAt (hT.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (fun y => P (y - a)) P x :=
      P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
    have h3 := h1.prodMk h2
    have hfun : (e₀ : E → G × D.ker) = fun y => (Ψ y, P (y - a)) := funext he₀
    rw [hfun]
    convert h3 using 1
    ext v <;> simp [L]
  have hLcont : ContinuousOn L T := by
    have : ContinuousOn (fun x => fderiv ℝ Ψ x) T :=
      hΨ.continuousOn_fderiv_of_isOpen hT (by simp)
    exact (continuousOn_const.clm_comp this).add continuousOn_const
  -- invertibility locus
  have hLa : L a = ((D.equivProdOfSurjectiveOfIsCompl P hrange
      (LinearMap.range_eq_of_proj hP) (LinearMap.isCompl_of_proj hP) :
      E ≃L[ℝ] (G × D.ker)) : E →L[ℝ] (G × D.ker)) := by
    have h1 := hderiv a ha
    have h2 : HasFDerivAt e₀ ((D.equivProdOfSurjectiveOfIsCompl P hrange
      (LinearMap.range_eq_of_proj hP) (LinearMap.isCompl_of_proj hP) :
      E ≃L[ℝ] (G × D.ker)) : E →L[ℝ] (G × D.ker)) a := by
      have := φ.hasStrictFDerivAt.hasFDerivAt
      rw [φ.toOpenPartialHomeomorph_coe]
      exact this
    exact h1.unique h2
  let S : Set (E →L[ℝ] (G × D.ker)) := range ((↑) : (E ≃L[ℝ] (G × D.ker)) → _)
  have hS : IsOpen S := ContinuousLinearEquiv.isOpen
  let s : Set E := T ∩ L ⁻¹' S
  have hs : IsOpen s := hLcont.isOpen_inter_preimage hT hS
  have has : a ∈ s := ⟨ha, by rw [Set.mem_preimage, hLa]; exact ⟨_, rfl⟩⟩
  let e := e₀.restrOpen s hs
  have hraw : (e : E → G × D.ker) = e₀ := e₀.coe_restrOpen hs
  have hsrc : e.source = e₀.source ∩ s := e₀.restrOpen_source s hs
  have he₀C : ContDiffOn ℝ ∞ e₀ T := by
    have hfun : (e₀ : E → G × D.ker) = fun y => (Ψ y, P (y - a)) := funext he₀
    rw [hfun]
    exact hΨ.prodMk ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  refine ⟨e, by rw [hsrc]; exact ⟨ha₀, has⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]; exact inter_subset_right.trans inter_subset_left
  · rw [hraw, he₀]; simp
  · intro x; rw [hraw, he₀]
  · rw [hraw]
    exact he₀C.mono (by rw [hsrc]; exact inter_subset_right.trans inter_subset_left)
  · intro b hb
    have hx : e.symm b ∈ e.source := e.map_target hb
    rw [hsrc] at hx
    obtain ⟨eq, heq⟩ := hx.2.2
    have hxT : e.symm b ∈ T := hx.2.1
    have hd1 : HasFDerivAt e (eq : E →L[ℝ] (G × D.ker)) (e.symm b) := by
      rw [hraw]
      have := hderiv _ hxT
      rw [heq]
      exact this
    have hc1 : ContDiffAt ℝ ∞ e (e.symm b) := by
      rw [hraw]
      exact (he₀C.contDiffAt (hT.mem_nhds hxT))
    exact (e.contDiffAt_symm hb hd1 hc1).contDiffWithinAt

end CutoffRigidity.Riemann
