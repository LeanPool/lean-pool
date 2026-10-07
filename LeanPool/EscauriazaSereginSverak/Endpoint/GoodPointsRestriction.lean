/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Restricting suitable solutions

Open restrictions of suitable solutions retain the same test identities, as in
`lem:sws-restrict` of the CKN manuscript.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A scalar product-spacetime test viewed on parabolic spacetime. -/
@[expose] def parabolicScalarTest (g : Vec3 × ℝ → ℝ) : ParabolicPoint → ℝ :=
  fun z => g (parabolicHomeomorph z)

/-- A vector product-spacetime test viewed on parabolic spacetime. -/
@[expose] def parabolicVectorTest (g : Vec3 × ℝ → Vec3) : ParabolicPoint → Vec3 :=
  fun z => g (parabolicHomeomorph z)

private theorem scalarTest_tsupport_subset
    (Ω : Set Vec3) (I : Set ℝ) (g : Vec3 × ℝ → ℝ)
    (hsupp : tsupport g ⊆ Ω ×ˢ I) :
    tsupport (parabolicScalarTest g) ⊆ spaceTimeSet Ω I := by
  change tsupport (g ∘ parabolicHomeomorph) ⊆
    parabolicHomeomorph ⁻¹' (Ω ×ˢ I)
  rw [tsupport_comp_eq_preimage]
  exact preimage_mono hsupp

private theorem vectorTest_tsupport_subset
    (Ω : Set Vec3) (I : Set ℝ) (g : Vec3 × ℝ → Vec3)
    (hsupp : tsupport g ⊆ Ω ×ˢ I) :
    tsupport (parabolicVectorTest g) ⊆ spaceTimeSet Ω I := by
  change tsupport (g ∘ parabolicHomeomorph) ⊆
    parabolicHomeomorph ⁻¹' (Ω ×ˢ I)
  rw [tsupport_comp_eq_preimage]
  exact preimage_mono hsupp

private theorem spatialPartial_zero_of_not_mem_tsupport
    (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint)
    (hz : z ∉ tsupport g) : spatialPartial g i z = 0 := by
  let e : Vec3 → ParabolicPoint := fun x => parabolicHomeomorph.symm (x, z.2)
  have he : Continuous e := by fun_prop
  have hnot : z.1 ∉ tsupport (g ∘ e) := by
    intro hx
    have hmem := tsupport_comp_subset_preimage
      (f := e) g he hx
    have heq : e z.1 = z := by
      cases z
      rfl
    exact hz (heq ▸ (Set.mem_preimage.mp hmem))
  have hslice : (fun x : Vec3 => g (x, z.2)) = g ∘ e := by
    funext x
    rfl
  have hnot' : z.1 ∉ tsupport (fun x : Vec3 => g (x, z.2)) := by
    rw [hslice]
    exact hnot
  have hderiv : fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1 = 0 :=
    fderiv_of_notMem_tsupport ℝ hnot'
  simp [spatialPartial, hderiv]

private theorem timePartial_zero_of_not_mem_tsupport
    (g : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (hz : z ∉ tsupport g) : timePartial g z = 0 := by
  let e : ℝ → ParabolicPoint := fun t => parabolicHomeomorph.symm (z.1, t)
  have he : Continuous e := by fun_prop
  have hnot : z.2 ∉ tsupport (g ∘ e) := by
    intro ht
    have hmem := tsupport_comp_subset_preimage
      (f := e) g he ht
    have heq : e z.2 = z := by
      cases z
      rfl
    exact hz (heq ▸ (Set.mem_preimage.mp hmem))
  have hslice : (fun t : ℝ => g (z.1, t)) = g ∘ e := by
    funext t
    rfl
  have hnot' : z.2 ∉ tsupport (fun t : ℝ => g (z.1, t)) := by
    rw [hslice]
    exact hnot
  have hderiv : fderiv ℝ (fun t : ℝ => g (z.1, t)) z.2 = 0 :=
    fderiv_of_notMem_tsupport ℝ hnot'
  simp [timePartial, hderiv]

private theorem tsupport_spatialPartial_subset
    (g : ParabolicPoint → ℝ) (i : Fin 3) :
    tsupport (fun z => spatialPartial g i z) ⊆ tsupport g := by
  apply closure_minimal
  · intro z hz
    by_contra hnot
    have hzero := spatialPartial_zero_of_not_mem_tsupport g i z hnot
    exact (Function.mem_support.mp hz) hzero
  · exact isClosed_tsupport g

private theorem tsupport_timePartial_subset
    (g : ParabolicPoint → ℝ) :
    tsupport (fun z => timePartial g z) ⊆ tsupport g := by
  apply closure_minimal
  · intro z hz
    by_contra hnot
    have hzero := timePartial_zero_of_not_mem_tsupport g z hnot
    exact (Function.mem_support.mp hz) hzero
  · exact isClosed_tsupport g

private theorem tsupport_spatialSecondPartial_subset
    (g : ParabolicPoint → ℝ) (i j : Fin 3) :
    tsupport (fun z => spatialSecondPartial g i j z) ⊆ tsupport g := by
  exact (tsupport_spatialPartial_subset (fun z => spatialPartial g i z) j).trans
    (tsupport_spatialPartial_subset g i)

private theorem tsupport_component_subset
    (g : ParabolicPoint → Vec3) (i : Fin 3) :
    tsupport (fun z => g z i) ⊆ tsupport g := by
  exact tsupport_comp_subset (g := fun v : Vec3 => v i) (by simp) g

/-- Suitable weak solutions restrict to open subdomains and open time intervals. -/
theorem isSuitableWeakSolution_restrict
    {Ω Ω₁ : Set Vec3} {I I₁ : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hSuitable : IsSuitableWeakSolution Ω I q u Du p f)
    (hΩ₁open : IsOpen Ω₁) (hI₁open : IsOpen I₁) (hI₁ord : OrdConnected I₁)
    (hΩ₁ : Ω₁ ⊆ Ω) (hI₁ : I₁ ⊆ I) :
    IsSuitableWeakSolution Ω₁ I₁ q u Du p f := by
  rcases hSuitable with ⟨hΩopen, hIopen, hIord, hq, hforce, hlocal,
    hdiv, hmomentum, henergy⟩
  have hspaceTimeSub : spaceTimeSet Ω₁ I₁ ⊆ spaceTimeSet Ω I := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hΩ₁ hx, hI₁ ht⟩
  have hΩI_meas : MeasurableSet (spaceTimeSet Ω I) :=
    hΩopen.measurableSet.prod hIopen.measurableSet
  refine ⟨hΩ₁open, hI₁open, hI₁ord, hq, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω' J hbox
    rcases hbox with ⟨hΩ'op, hΩ'compact, hΩ'closure, hJord, hJcompact, hJclosure⟩
    exact hforce Ω' J ⟨hΩ'op, hΩ'compact, hΩ'closure.trans hΩ₁,
      hJord, hJcompact, hJclosure.trans hI₁⟩
  · intro Ω' J hbox
    rcases hbox with ⟨hΩ'op, hΩ'compact, hΩ'closure, hJord, hJcompact, hJclosure⟩
    exact hlocal Ω' J ⟨hΩ'op, hΩ'compact, hΩ'closure.trans hΩ₁,
      hJord, hJcompact, hJclosure.trans hI₁⟩
  · intro ψ hψ
    rcases hψ with ⟨hcont, hcompact, hsupp⟩
    change tsupport ψ ⊆ Ω₁ ×ˢ I₁ at hsupp
    have hψ' : ψ ∈ spaceTimeTestFunction Ω I := by
      exact ⟨hcont, hcompact, hsupp.trans (by
        rintro ⟨x, t⟩ ⟨hx, ht⟩
        exact ⟨hΩ₁ hx, hI₁ ht⟩)⟩
    have hψsupport : tsupport (parabolicScalarTest ψ) ⊆
        spaceTimeSet Ω₁ I₁ :=
      scalarTest_tsupport_subset Ω₁ I₁ ψ hsupp
    have hsource := hdiv ψ hψ'
    have heq : (∫ z in spaceTimeSet Ω I,
        ∑ i, u z i * spatialPartial ψ i z) =
        ∫ z in spaceTimeSet Ω₁ I₁,
          ∑ i, u z i * spatialPartial ψ i z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hΩI_meas hspaceTimeSub
      intro z hz
      have hznot : z ∉ tsupport (parabolicScalarTest ψ) :=
        fun hs => hz.2 (hψsupport hs)
      apply Finset.sum_eq_zero
      intro i hi
      have hzero := spatialPartial_zero_of_not_mem_tsupport
        (parabolicScalarTest ψ) i z hznot
      have hzero' : spatialPartial ψ i z = 0 := by
        convert hzero using 1; rfl
      rw [hzero']
      ring
    rw [heq] at hsource
    exact hsource
  · intro φ hφ
    rcases hφ with ⟨hcont, hcompact, hsupp⟩
    change tsupport φ ⊆ Ω₁ ×ˢ I₁ at hsupp
    have hφ' : φ ∈ spaceTimeTestFunction Ω I := by
      exact ⟨hcont, hcompact, hsupp.trans (by
        rintro ⟨x, t⟩ ⟨hx, ht⟩
        exact ⟨hΩ₁ hx, hI₁ ht⟩)⟩
    have hφsupport : tsupport (parabolicVectorTest φ) ⊆
        spaceTimeSet Ω₁ I₁ :=
      vectorTest_tsupport_subset Ω₁ I₁ φ hsupp
    have hsource := hmomentum φ hφ'
    have heq : (∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i) =
        ∫ z in spaceTimeSet Ω₁ I₁,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hΩI_meas hspaceTimeSub
      intro z hz
      have hznot : z ∉ tsupport (parabolicVectorTest φ) :=
        fun hs => hz.2 (hφsupport hs)
      have hφzero : parabolicVectorTest φ z = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hznot (subset_tsupport _ hmem)
      have hcomponent : ∀ i, φ z i = 0 := by
        intro i
        have hzero : parabolicVectorTest φ z i = 0 := by
          rw [hφzero]
          simp
        convert hzero using 1; rfl
      have hcomponentSupport : ∀ i,
          tsupport (fun q => parabolicVectorTest φ q i) ⊆
            tsupport (parabolicVectorTest φ) := fun i =>
          tsupport_component_subset (parabolicVectorTest φ) i
      have htime : ∀ i, timePartial (fun w => φ w i) z = 0 := by
        intro i
        have hnot : z ∉ tsupport (fun q => parabolicVectorTest φ q i) := by
          intro hs
          exact hznot (hcomponentSupport i hs)
        have hcomponentFun : parabolicScalarTest (fun w => φ w i) =
            (fun q => parabolicVectorTest φ q i) := by
          funext q
          rfl
        have hnot' : z ∉ tsupport (parabolicScalarTest (fun w => φ w i)) := by
          rw [hcomponentFun]
          exact hnot
        have hzero := timePartial_zero_of_not_mem_tsupport
          (parabolicScalarTest (fun w => φ w i)) z hnot'
        convert hzero using 1; rfl
      have hpartial : ∀ i j, spatialPartial (fun w => φ w i) j z = 0 := by
        intro i j
        have hnot : z ∉ tsupport (fun q => parabolicVectorTest φ q i) := by
          intro hs
          exact hznot (hcomponentSupport i hs)
        have hcomponentFun : parabolicScalarTest (fun w => φ w i) =
            (fun q => parabolicVectorTest φ q i) := by
          funext q
          rfl
        have hnot' : z ∉ tsupport (parabolicScalarTest (fun w => φ w i)) := by
          rw [hcomponentFun]
          exact hnot
        have hzero := spatialPartial_zero_of_not_mem_tsupport
          (parabolicScalarTest (fun w => φ w i)) j z hnot'
        convert hzero using 1; rfl
      simp [htime, hpartial, hcomponent]
    rw [heq] at hsource
    exact hsource
  · intro ψ hψ hnonneg
    rcases hψ with ⟨hcont, hcompact, hsupp⟩
    change tsupport ψ ⊆ Ω₁ ×ˢ I₁ at hsupp
    have hψ' : ψ ∈ spaceTimeTestFunction Ω I := by
      exact ⟨hcont, hcompact, hsupp.trans (by
        rintro ⟨x, t⟩ ⟨hx, ht⟩
        exact ⟨hΩ₁ hx, hI₁ ht⟩)⟩
    have hψsupport : tsupport (parabolicScalarTest ψ) ⊆
        spaceTimeSet Ω₁ I₁ :=
      scalarTest_tsupport_subset Ω₁ I₁ ψ hsupp
    have hsource := henergy ψ hψ' hnonneg
    have hleftEq : (∫ z in spaceTimeSet Ω I,
        spatialGradientSq u Du z * ψ z) =
        ∫ z in spaceTimeSet Ω₁ I₁,
          spatialGradientSq u Du z * ψ z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hΩI_meas hspaceTimeSub
      intro z hz
      have hznot : z ∉ tsupport (parabolicScalarTest ψ) :=
        fun hs => hz.2 (hψsupport hs)
      have hzero : parabolicScalarTest ψ z = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hznot (subset_tsupport _ hmem)
      have hψzero : ψ z = 0 := by
        convert hzero using 1; rfl
      rw [hψzero]
      ring
    have heq : (∫ z in spaceTimeSet Ω I,
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψ i z
          + 2 * (∑ i, f z i * u z i) * ψ z) =
        ∫ z in spaceTimeSet Ω₁ I₁,
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψ i z
          + 2 * (∑ i, f z i * u z i) * ψ z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hΩI_meas hspaceTimeSub
      intro z hz
      have hznot : z ∉ tsupport (parabolicScalarTest ψ) :=
        fun hs => hz.2 (hψsupport hs)
      have htimeLift : timePartial (parabolicScalarTest ψ) z = 0 :=
        timePartial_zero_of_not_mem_tsupport (parabolicScalarTest ψ) z hznot
      have htime : timePartial ψ z = 0 := by
        convert htimeLift using 1; rfl
      have hpartial : ∀ i, spatialPartial ψ i z = 0 := by
        intro i
        have hzero := spatialPartial_zero_of_not_mem_tsupport
          (parabolicScalarTest ψ) i z hznot
        convert hzero using 1; rfl
      have hsecond : ∀ i j, spatialSecondPartial ψ i j z = 0 := by
        intro i j
        have hnot : z ∉ tsupport
            (fun q => spatialPartial (parabolicScalarTest ψ) i q) := by
          intro hs
          exact hznot ((tsupport_spatialPartial_subset (parabolicScalarTest ψ) i) hs)
        have hzero : spatialSecondPartial (parabolicScalarTest ψ) i j z = 0 := by
          apply spatialPartial_zero_of_not_mem_tsupport
            (fun q => spatialPartial (parabolicScalarTest ψ) i q) j z hnot
        convert hzero using 1; rfl
      have hψzeroLift : parabolicScalarTest ψ z = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hznot (subset_tsupport _ hmem)
      have hψzero : ψ z = 0 := by
        convert hψzeroLift using 1; rfl
      simp [htime, hpartial, hsecond, hψzero]
    rw [hleftEq] at hsource
    rw [heq] at hsource
    exact hsource

end ESS
