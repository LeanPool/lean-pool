/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientExtract
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessExhaustion
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSupport
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Compactness Gradient Glue

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Weak spatial derivatives on every open inner member of a compact
exhaustion give the weak derivative on the whole open domain. -/
theorem hasWeakPartialDerivOn_of_inner_exhaustion
    {U : Set Vec3} (hU : IsOpen U)
    (K : ℕ → Set Vec3)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hKinner : ∀ j, K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (f d : Vec3 → ℝ) (i : Fin 3)
    (hlocal : ∀ j, CKN.HasWeakPartialDerivOn (interior (K j)) i f d) :
    CKN.HasWeakPartialDerivOn U i f d := by
  intro φ hφ hφc hφU
  obtain ⟨j, hj⟩ := compact_subset_eventually_in_exhaustion
    hφc.isCompact hφU K hKmono hKinner hKcover
  let Ω := interior (K (j + 1))
  have hφΩ : tsupport φ ⊆ Ω := hj.trans (hKinner j)
  have hΩU : Ω ⊆ U := by
    intro x hx
    rw [← hKcover]
    exact Set.mem_iUnion.mpr ⟨j + 1, interior_subset hx⟩
  have hleft : (∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
      ∫ x in Ω, f x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet hΩU
    intro x hx
    have hxnot : x ∉ tsupport φ := fun h => hx.2 (hφΩ h)
    simp [fderiv_of_notMem_tsupport ℝ hxnot]
  have hright : (∫ x in U, d x * φ x ∂volume) =
      ∫ x in Ω, d x * φ x ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet hΩU
    intro x hx
    have hxnot : x ∉ tsupport φ := fun h => hx.2 (hφΩ h)
    simp [image_eq_zero_of_notMem_tsupport hxnot]
  rw [hleft, hright]
  exact hlocal (j + 1) φ hφ hφc hφΩ

/-- A measurable field assembled on disjointed nested sets agrees almost
everywhere with each compatible local representative on its full set. -/
theorem ae_eq_on_nested_sets_of_disjointed_representative
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    (R : ℕ → Set α) (hRmeas : ∀ j, MeasurableSet (R j))
    (g : ℕ → α → E) (F : α → E)
    (hF : ∀ j, EqOn F (g j) (disjointed R j))
    (hcompat : ∀ i j, i ≤ j → g i =ᵐ[μ.restrict (R i)] g j)
    (j : ℕ) :
    F =ᵐ[μ.restrict (R j)] g j := by
  classical
  let A : ℕ → Set α := disjointed R
  have hcover : (⋃ i, A i ∩ R j) = R j := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi.2
    · intro hx
      have hxUnion : x ∈ ⋃ i, R i :=
        Set.mem_iUnion.mpr ⟨j, hx⟩
      rw [← iUnion_disjointed] at hxUnion
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxUnion
      exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hx⟩⟩
  rw [← hcover, ae_eq_restrict_iUnion_iff]
  intro i
  by_cases hij : i ≤ j
  · have hAmeas : MeasurableSet (A i) :=
      MeasurableSet.disjointed hRmeas i
    have hSmeas : MeasurableSet (A i ∩ R j) :=
      hAmeas.inter (hRmeas j)
    have hSi : A i ∩ R j ⊆ R i :=
      Set.inter_subset_left.trans (disjointed_subset R i)
    have hcompat' := ae_restrict_of_ae_restrict_of_subset
      hSi (hcompat i j hij)
    filter_upwards [hcompat', ae_restrict_mem hSmeas] with x hx hmem
    exact (hF i hmem.1).trans hx
  · have hji : j < i := Nat.lt_of_not_ge hij
    have hempty : A i ∩ R j = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hAi : x ∈ R i ∩ ⋂ k < i, (R k)ᶜ := by
        rw [← disjointed_eq_inter_compl R i]
        exact hx.1
      have hnot := Set.mem_iInter₂.mp hAi.2 j hji
      exact hnot hx.2
    rw [hempty]
    rw [Measure.restrict_empty, ae_zero]
    change ∀ᶠ x : α in (⊥ : Filter α), F x = g j x
    exact Filter.eventually_bot

/-- Local `L²` gradient classes on a countable rectangle family admit a
jointly measurable selection on the disjointed rectangle family. -/
theorem exists_measurable_disjointed_gradient_representative
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hJ : ∀ j, IsCompact (J j))
    (gLocal : ℕ → Vec3 × ℝ → CompactnessGradientFiber)
    (hgMeas : ∀ j, Measurable (gLocal j)) :
    ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable g ∧ ∀ j,
        EqOn g (gLocal j)
          (disjointed (fun k => interior (K k) ×ˢ J k) j) := by
  classical
  let R : ℕ → Set (Vec3 × ℝ) := fun j => interior (K j) ×ˢ J j
  let A : ℕ → Set (Vec3 × ℝ) := disjointed R
  have hRmeas (j : ℕ) : MeasurableSet (R j) :=
    isOpen_interior.measurableSet.prod (hJ j).measurableSet
  have hAmeas (j : ℕ) : MeasurableSet (A j) :=
    MeasurableSet.disjointed hRmeas j
  have hdisj : Pairwise (Function.onFun Disjoint A) :=
    disjoint_disjointed R
  obtain ⟨F, hFmeas, hF⟩ := exists_measurable_piecewise A hAmeas
    gLocal hgMeas (by
      intro i j hij z hz
      exact False.elim (Set.disjoint_left.mp (hdisj hij) hz.1 hz.2))
  exact ⟨F, hFmeas, hF⟩

end CKN.Leray
