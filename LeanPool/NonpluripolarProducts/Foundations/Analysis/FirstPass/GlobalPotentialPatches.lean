/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ClosedRealOneOneForms
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Compactness.Compact

/-!
# Common local-potential patches

A patch simultaneously expresses a finite tuple of theta-PSH functions as
ordinary PSH functions after adding genuine smooth local potentials. Its source
is an open subset of the manifold, homeomorphic to the stated coordinate domain.
All assertions stay on chart domains: the arbitrary extensions of charts are
never declared continuous or measurable on the entire ambient space.

The construction includes the chart target in its finite intersection, including
when the tuple is empty. Compactness yields a finite cover by these actual
patches; no measure, finiteness of mass, or overlap equality is assumed here.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Simultaneous smooth corrections on one genuine coordinate neighborhood. -/
structure Patch (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal) where
  /-- The complex chart carrying the local potentials. -/
  chart : ComplexChart n M
  /-- The open coordinate domain of the patch. -/
  domain : TopologicalSpace.Opens (ComplexModel n)
  domain_le_target : (domain : Set (ComplexModel n)) ⊆ chart.val.target
  /-- Smooth local potentials for the background forms. -/
  potential : Fin n → ComplexModel n → ℝ
  localPotential : ∀ i, IsSmoothLocalPotential (θ i).val chart domain (potential i)
  plurisubharmonic : ∀ i,
    PlurisubharmonicOn
      (fun z => chartFunction (u i) chart z + (potential i z : EReal)) domain

variable {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

namespace Patch

/-- The corrected potentials retain their extended-real pole values. -/
def corrected (P : Patch θ u) (i : Fin n) (z : ComplexModel n) : EReal :=
  chartFunction (u i) P.chart z + (P.potential i z : EReal)

/-- The actual manifold neighborhood corresponding to the coordinate domain. -/
def source (P : Patch θ u) : TopologicalSpace.Opens M :=
  ⟨P.chart.val.source ∩ P.chart.val ⁻¹' P.domain,
    P.chart.val.isOpen_inter_preimage P.domain.isOpen⟩

@[simp] theorem mem_source (P : Patch θ u) {x : M} :
    x ∈ P.source ↔ x ∈ P.chart.val.source ∧ P.chart.val x ∈ P.domain := Iff.rfl

theorem source_subset (P : Patch θ u) : (P.source : Set M) ⊆ P.chart.val.source :=
  inter_subset_left

theorem map_source (P : Patch θ u) {x : M} (hx : x ∈ P.source) :
    P.chart.val x ∈ P.domain := hx.2

theorem map_target (P : Patch θ u) {z : ComplexModel n} (hz : z ∈ P.domain) :
    P.chart.val.symm z ∈ P.source := by
  refine ⟨P.chart.val.map_target (P.domain_le_target hz), ?_⟩
  change P.chart.val (P.chart.val.symm z) ∈ P.domain
  rwa [P.chart.val.right_inv (P.domain_le_target hz)]

/-- Restricting chart and inverse chart gives a genuine homeomorphism; no claim
is made about either map outside the relevant source or target. -/
def homeomorph (P : Patch θ u) : P.source ≃ₜ P.domain where
  toFun x := ⟨P.chart.val x, P.map_source x.property⟩
  invFun z := ⟨P.chart.val.symm z, P.map_target z.property⟩
  left_inv x := Subtype.ext (P.chart.val.left_inv (P.source_subset x.property))
  right_inv z := Subtype.ext (P.chart.val.right_inv (P.domain_le_target z.property))
  continuous_toFun := (P.chart.val.continuousOn.mono P.source_subset).mapsToRestrict
    (fun _ hx => P.map_source hx)
  continuous_invFun := (P.chart.val.symm.continuousOn.mono
    P.domain_le_target).mapsToRestrict (fun _ hz => P.map_target hz)

@[simp] theorem homeomorph_apply (P : Patch θ u) (x : P.source) :
    (P.homeomorph x : ComplexModel n) = P.chart.val x := rfl

@[simp] theorem homeomorph_symm_apply (P : Patch θ u) (z : P.domain) :
    (P.homeomorph.symm z : M) = P.chart.val.symm z := rfl

/-- Shrinking the coordinate neighborhood keeps the same chart and corrections. -/
def restrict (P : Patch θ u) (V : TopologicalSpace.Opens (ComplexModel n))
    (hV : V ≤ P.domain) : Patch θ u where
  chart := P.chart
  domain := V
  domain_le_target := fun _ hz => P.domain_le_target (hV hz)
  potential := P.potential
  localPotential i := (P.localPotential i).mono V.isOpen hV
  plurisubharmonic i := (P.plurisubharmonic i).mono hV

theorem mem_source_restrict (P : Patch θ u) (V : TopologicalSpace.Opens (ComplexModel n))
    (hV : V ≤ P.domain) {x : M} :
    x ∈ (P.restrict V hV).source ↔ x ∈ P.source ∧ P.chart.val x ∈ V := by
  constructor
  · intro hx
    exact ⟨⟨hx.1, hV hx.2⟩, hx.2⟩
  · intro hx
    exact ⟨hx.1.1, hx.2⟩

end Patch

/-- A common patch can be taken in any specified atlas chart. The explicit
intersection with its target is necessary even for an empty tuple. -/
theorem exists_patch_in_chart
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ P : Patch θ u, P.chart = e ∧ z ∈ P.domain := by
  classical
  choose W ρ hmem hlocal hpsh using fun i => hu i e z hz
  let V : TopologicalSpace.Opens (ComplexModel n) :=
    ⟨e.val.target ∩ ⋂ i, W i,
      e.val.open_target.inter (isOpen_iInter_of_finite fun i => (hlocal i).1)⟩
  have hVW (i : Fin n) : (V : Set (ComplexModel n)) ⊆ W i :=
    fun _ hy => mem_iInter.mp hy.2 i
  refine ⟨{
    chart := e
    domain := V
    domain_le_target := inter_subset_left
    potential := ρ
    localPotential := fun i => (hlocal i).mono V.isOpen (hVW i)
    plurisubharmonic := fun i => (hpsh i).mono (hVW i) }, rfl, ?_⟩
  exact ⟨hz, mem_iInter.mpr hmem⟩

/-- Genuine local-potential patches cover the manifold, without compactness or
local nondegeneracy hypotheses. -/
theorem exists_patch_containing
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (x : M) :
    ∃ P : Patch θ u, x ∈ P.source := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨P, hP, hz⟩ := exists_patch_in_chart hu e (e.val.map_source hx)
  refine ⟨P, ?_⟩
  rw [Patch.mem_source, hP]
  exact ⟨hx, hz⟩

/-- A finite ordered family of actual potential patches covering the manifold. -/
structure FiniteCover (θ : Fin n → ClosedRealOneOneForm n M)
    (u : Fin n → M → EReal) where
  /-- The number of patches in the finite cover. -/
  count : ℕ
  /-- The patches of the cover indexed by a finite type. -/
  patch : Fin count → Patch θ u
  covers : ∀ x : M, ∃ i, x ∈ (patch i).source

/-- Compactness supplies a finite potential cover. The count is allowed to be
zero when the manifold is empty. -/
theorem nonempty_finiteCover [CompactSpace M]
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    Nonempty (FiniteCover θ u) := by
  classical
  have hcover : (univ : Set M) ⊆ ⋃ P : Patch θ u, (P.source : Set M) := by
    intro x _
    obtain ⟨P, hx⟩ := exists_patch_containing hu x
    exact mem_iUnion.mpr ⟨P, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun P : Patch θ u => (P.source : Set M)) (fun P => P.source.isOpen) hcover
  refine ⟨{
    count := s.card
    patch := fun i => (s.equivFin.symm i).val
    covers := ?_ }⟩
  intro x
  obtain ⟨P, hPx⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hP, hx⟩ := mem_iUnion.mp hPx
  refine ⟨s.equivFin ⟨P, hP⟩, ?_⟩
  change x ∈ (((s.equivFin.symm (s.equivFin ⟨P, hP⟩)).val).source : Set M)
  rw [Equiv.symm_apply_apply]
  exact hx

end

end SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
