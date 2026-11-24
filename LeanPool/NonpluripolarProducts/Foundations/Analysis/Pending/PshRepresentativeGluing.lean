/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularizationData
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local-to-global PSH representatives

Local representatives are restricted to overlaps and identified by uniqueness.
Their glued function represents the original distribution because smooth
partitions of unity reduce each compactly supported test function to finitely
many local tests. Almost-everywhere finiteness is transferred through a
countable open subcover.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending

private theorem distribution_eq_of_restrict_eq_on_openCover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} {T S : 𝓓'(Ω, ℝ)} {ι : Type*}
    (U : ι → Opens E) (hUΩ : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hlocal : ∀ i,
      restrictDistribution T (hUΩ i) = restrictDistribution S (hUΩ i)) :
    T = S := by
  classical
  ext φ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_closure (fun i ↦ (U i : Set E))
    (fun i ↦ (U i).isOpen) (by
      intro x hx
      obtain ⟨i, hi⟩ := hcover x (φ.tsupport_subset hx)
      exact mem_iUnion.mpr ⟨i, hi⟩)
  let active : Set ι := {i | (Function.support (ρ i) ∩ tsupport φ).Nonempty}
  have hactive : active.Finite :=
    by simpa only [active] using
      ρ.locallyFinite.finite_nonempty_inter_compact φ.hasCompactSupport
  let ψ (i : ι) : 𝓓(U i, ℝ) :=
    ⟨fun x ↦ ρ i x * φ x,
      (ρ i).contMDiff.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_left
        (f := fun x ↦ ρ i x) (g := fun x ↦ φ x)).trans (hρ i)⟩
  let Ψ (i : ι) : 𝓓(Ω, ℝ) := TestFunction.monoCLM ℝ (ψ i)
  have hφsum : φ = ∑ i ∈ hactive.toFinset, Ψ i := by
    apply TestFunction.ext
    intro x
    have hsum_apply :
        (∑ i ∈ hactive.toFinset, Ψ i) x =
          ∑ i ∈ hactive.toFinset, ρ i x * φ x := by
      have hsum_apply' : ∀ s : Finset ι,
          (∑ i ∈ s, Ψ i) x = ∑ i ∈ s, ρ i x * φ x := by
        intro s
        induction s using Finset.induction_on with
        | empty => rfl
        | @insert i s hi hs =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi]
            change (Ψ i) x + (∑ j ∈ s, Ψ j) x =
              ρ i x * φ x + ∑ j ∈ s, ρ j x * φ x
            rw [hs]
            exact congrArg₂ (· + ·)
              (congrFun (testFunction_inclusion_coe (hUΩ i) (ψ i)) x) rfl
      exact hsum_apply' hactive.toFinset
    by_cases hx : x ∈ tsupport φ
    · have hsupp : Function.support (fun i ↦ ρ i x) ⊆ active := by
        intro i hi
        exact ⟨x, hi, hx⟩
      rw [hsum_apply]
      rw [← Finset.sum_mul]
      rw [← finsum_eq_finsetSum_of_support_subset (fun i ↦ ρ i x)
        (by simpa only [Set.Finite.coe_toFinset] using hsupp)]
      rw [ρ.sum_eq_one hx, one_mul]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hsum_apply, hφx]
      simp
  calc
    T φ = T (∑ i ∈ hactive.toFinset, Ψ i) :=
      congrArg T hφsum
    _ = ∑ i ∈ hactive.toFinset, T (Ψ i) := by
      simp only [map_sum]
    _ = ∑ i ∈ hactive.toFinset, S (Ψ i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun R : 𝓓'(U i, ℝ) ↦ R (ψ i)) (hlocal i)
    _ = S (∑ i ∈ hactive.toFinset, Ψ i) := by
      simp only [map_sum]
    _ = S φ := congrArg S hφsum.symm

private theorem regularDistribution_eq_of_eqOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {U : Opens E} {f g : E → ℝ}
    (hf : LocallyIntegrableOn f U μ) (hg : LocallyIntegrableOn g U μ)
    (hfg : EqOn f g U) :
    regularDistribution μ f hf = regularDistribution μ g hg := by
  ext φ
  rw [regularDistribution_apply, regularDistribution_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · change φ x * f x = φ x * g x
      rw [hfg hx]
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
      simp only [hφx, zero_mul]

/-- Local PSH representatives of restrictions glue to a genuine representative
of the original distribution. No compatibility is assumed as extra data: it
must follow from the already checked uniqueness theorem. -/
theorem exists_pshRepresentative_of_locally
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {T : 𝓓'(Ω, ℝ)}
    (hlocal : ∀ x ∈ Ω, ∃ (U : Opens E) (hUΩ : U ≤ Ω) (u : E → EReal),
      x ∈ U ∧ IsPshRepresentative μ (restrictDistribution T hUΩ) u) :
    ∃ u : E → EReal, IsPshRepresentative μ T u := by
  classical
  choose U hUΩ u hxU hu using fun x : Ω => hlocal x x.2
  have hcompat (x y : Ω) : EqOn (u x) (u y) (U x ⊓ U y) := by
    have hux := SGPT.Foundations.Analysis.IsPshRepresentative.restrict
      (U := U x ⊓ U y) μ (hu x) inf_le_left
    have huy := SGPT.Foundations.Analysis.IsPshRepresentative.restrict
      (U := U x ⊓ U y) μ (hu y) inf_le_right
    rw [restrictDistribution_trans] at hux huy
    exact hux.unique huy
  let g : E → EReal := fun y => if hy : y ∈ Ω then u ⟨y, hy⟩ y else 0
  have hg_eq (x : Ω) : EqOn g (u x) (U x) := by
    intro y hy
    have hyΩ : y ∈ Ω := hUΩ x hy
    simp only [g, dite_eq_left hyΩ]
    exact hcompat ⟨y, hyΩ⟩ x ⟨hxU ⟨y, hyΩ⟩, hy⟩
  have hgPsh : PlurisubharmonicOn g Ω := by
    intro y hyΩ
    let x : Ω := ⟨y, hyΩ⟩
    have hyU : y ∈ U x := hxU x
    apply ((hu x).1 y hyU).congr
    filter_upwards [(U x).isOpen.mem_nhds hyU] with z hz
    exact (hg_eq x hz).symm
  have hgLocal : LocallyIntegrableOn (fun y => (g y).toReal) Ω μ := by
    intro y hyΩ
    let x : Ω := ⟨y, hyΩ⟩
    have hyU : y ∈ U x := hxU x
    obtain ⟨_, _, huLocal, _⟩ := hu x
    have hae : (fun z => (u x z).toReal) =ᵐ[μ.restrict (U x)]
        fun z => (g z).toReal := by
      filter_upwards [ae_restrict_mem (U x).isOpen.measurableSet] with z hz
      exact congrArg EReal.toReal (hg_eq x hz).symm
    have hgLocalU := huLocal.congr hae
    have hgAt := hgLocalU y hyU
    rw [(U x).isOpen.nhdsWithin_eq hyU] at hgAt
    rw [Ω.isOpen.nhdsWithin_eq hyΩ]
    exact hgAt
  have hUunion : (⋃ x : Ω, (U x : Set E)) = (Ω : Set E) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hyx⟩ := mem_iUnion.mp hy
      exact hUΩ x hyx
    · intro y hy
      exact mem_iUnion_of_mem ⟨y, hy⟩ (hxU ⟨y, hy⟩)
  obtain ⟨A, hAcount, hAunion⟩ :=
    isOpen_iUnion_countable (fun x : Ω => (U x : Set E)) (fun x => (U x).isOpen)
  have hgFinite : ∀ᵐ y ∂μ.restrict Ω, g y ≠ ⊤ ∧ g y ≠ ⊥ := by
    rw [← hUunion, ← hAunion]
    rw [ae_restrict_biUnion_iff (fun x : Ω => (U x : Set E)) hAcount]
    intro x _
    filter_upwards [(hu x).2.1, ae_restrict_mem (U x).isOpen.measurableSet] with y hy hyU
    simpa only [hg_eq x hyU] using hy
  have hrestrict (x : Ω) :
      restrictDistribution T (hUΩ x) =
        restrictDistribution
          (regularDistribution μ (fun y => (g y).toReal) hgLocal) (hUΩ x) := by
    obtain ⟨_, _, huLocal, huT⟩ := hu x
    calc
      restrictDistribution T (hUΩ x) =
          regularDistribution μ (fun y => (u x y).toReal) huLocal := huT
      _ = regularDistribution μ (fun y => (g y).toReal)
          (hgLocal.mono_set (hUΩ x)) := by
        apply regularDistribution_eq_of_eqOn μ
        intro y hy
        exact congrArg EReal.toReal (hg_eq x hy).symm
      _ = restrictDistribution
          (regularDistribution μ (fun y => (g y).toReal) hgLocal) (hUΩ x) :=
        (SGPT.Foundations.Analysis.restrictDistribution_regularDistribution
          μ hgLocal (hUΩ x)).symm
  have hT : T = regularDistribution μ (fun y => (g y).toReal) hgLocal := by
    apply distribution_eq_of_restrict_eq_on_openCover U hUΩ
    · intro y hyΩ
      exact ⟨⟨y, hyΩ⟩, hxU ⟨y, hyΩ⟩⟩
    · exact hrestrict
  exact ⟨g, hgPsh, hgFinite, hgLocal, hT⟩

end SGPT.Foundations.Analysis.Pending
