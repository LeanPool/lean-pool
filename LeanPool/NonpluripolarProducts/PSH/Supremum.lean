/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshSupremumRegularization

/-!
# Actual source PSH upper envelopes

The raw supremum and its neighborhood regularization retain both infinities.
The main branch's genuine moving-disc proof supplies the submean property;
the source non-bottom witness is produced from a member of the actual family.
This file concerns open complex normed domains. Manifold chart transport is
a separate source obligation.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {I : Type*}

/-- The actual source local uniform upper bound, relative to the domain. -/
def LocallyUniformlyBoundedAbove (u : I → E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, ∃ V : Set E, V ∈ 𝓝[U] x ∧
    ∃ C : ℝ, ∀ i, ∀ y ∈ V ∩ U, u i y ≤ (C : EReal)

/-- The upper semicontinuous regularization of the actual indexed supremum. -/
noncomputable def uscSup {X : Type*} [TopologicalSpace X]
    (u : I → X → EReal) : X → EReal :=
  SGPT.Foundations.Analysis.FirstPass.uscRegularization (fun x ↦ ⨆ i, u i x)

omit [NormedSpace ℂ E] in
/-- Indexed and set-family bounds agree for the actual image family. -/
theorem locallyUniformlyBoundedAbove_range_iff {u : I → E → EReal} {U : Set E} :
    SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove (Set.range u) U ↔
      LocallyUniformlyBoundedAbove u U := by
  constructor
  · intro h x hx
    obtain ⟨V, hV, C, hC⟩ := h x hx
    exact ⟨V, hV, C, fun i ↦ hC (u i) (Set.mem_range_self i)⟩
  · intro h x hx
    obtain ⟨V, hV, C, hC⟩ := h x hx
    refine ⟨V, hV, C, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hC i

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The ambient Pi-lattice supremum is the pointwise indexed supremum. -/
theorem sSup_range_eq (u : I → E → EReal) :
    sSup (Set.range u) = fun x ↦ ⨆ i, u i x := by
  rw [sSup_range]
  funext x
  exact iSup_apply

omit [NormedSpace ℂ E] in
/-- Every original family member lies below its actual regularized supremum. -/
theorem le_uscSup (u : I → E → EReal) (i : I) (x : E) :
    u i x ≤ uscSup u x :=
  (le_iSup (fun j ↦ u j x) i).trans
    (SGPT.Foundations.Analysis.FirstPass.le_uscRegularization (fun y ↦ ⨆ j, u j y) x)

/-- Source upper-envelope stability on an actual open complex domain.
The non-bottom field is obtained from an actual original PSH function. -/
theorem pshOn_uscSup_of_locallyBounded [Nonempty I] {u : I → E → EReal}
    {U : Set E} (hU : IsOpen U) (hu : ∀ i, PSHOn (u i) U)
    (hb : LocallyUniformlyBoundedAbove u U) : PSHOn (uscSup u) U := by
  classical
  have hpsh : ∀ f ∈ Set.range u, SGPT.Foundations.Analysis.PlurisubharmonicOn f U := by
    rintro f ⟨i, rfl⟩
    exact (hu i).disc.plurisubharmonicOn hU
  have hreg := SGPT.Foundations.Analysis.FirstPass.plurisubharmonicOn_uscRegularization_sSup
    hU (Set.range_nonempty u) hpsh (locallyUniformlyBoundedAbove_range_iff.mpr hb)
  rw [sSup_range_eq] at hreg
  refine ⟨hreg.discPshOn, ?_⟩
  obtain ⟨x, hx, hn⟩ := (hu (Classical.arbitrary I)).nontrivial
  refine ⟨x, hx, ?_⟩
  intro hbot
  exact hn (le_bot_iff.mp (by simpa only [hbot] using le_uscSup u (Classical.arbitrary I) x))

/-- The same actual upper envelope has the source complex-line criterion. -/
theorem linePSHOn_uscSup_of_locallyBounded [Nonempty I] {u : I → E → EReal}
    {U : Set E} (hU : IsOpen U) (hu : ∀ i, LinePSHOn (u i) U)
    (hb : LocallyUniformlyBoundedAbove u U) : LinePSHOn (uscSup u) U :=
  linePSHOn_of_pshOn (pshOn_uscSup_of_locallyBounded hU
    (fun i ↦ pshOn_of_linePSHOn (hu i)) hb)

/-- Finite actual suprema preserve relative upper semicontinuity, including
the empty supremum. The proof uses a finite intersection of neighborhoods. -/
theorem upperSemicontinuousOn_iSup_finite {X : Type*} [TopologicalSpace X] [Finite I]
    {u : I → X → EReal}
    {U : Set X} (hu : ∀ i, UpperSemicontinuousOn (u i) U) :
    UpperSemicontinuousOn (fun x ↦ ⨆ i, u i x) U := by
  intro x hx a ha
  obtain ⟨b, hxb, hba⟩ := exists_between ha
  have h : ∀ i, ∀ᶠ y in 𝓝[U] x, u i y < b :=
    fun i ↦ hu i x hx b ((le_iSup (fun j ↦ u j x) i).trans_lt hxb)
  filter_upwards [Filter.eventually_all.mpr h] with y hy
  exact (iSup_le fun i ↦ (hy i).le).trans_lt hba

/-- The source's finite-family observation holds on the actual open domain;
arbitrary ambient extensions outside the domain do not affect the result. -/
theorem uscSup_eq_iSup_finite {X : Type*} [TopologicalSpace X] [Finite I] {u : I → X → EReal} {U :
    Set X}
    (hU : IsOpen U) (hu : ∀ i, UpperSemicontinuousOn (u i) U) :
    EqOn (uscSup u) (fun x ↦ ⨆ i, u i x) U := by
  intro x hx
  apply le_antisymm
  · apply le_of_forall_gt
    intro a ha
    obtain ⟨b, hxb, hba⟩ := exists_between ha
    have hb := upperSemicontinuousOn_iSup_finite hu x hx b hxb
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at hb
    exact (SGPT.Foundations.Analysis.FirstPass.uscRegularization_le_localSup _ hb).trans_lt
      ((iSup_le fun y ↦ iSup_le fun hy ↦ hy.le).trans_lt hba)
  · exact SGPT.Foundations.Analysis.FirstPass.le_uscRegularization (fun y ↦ ⨆ i, u i y) x

end SGPT.PSH
