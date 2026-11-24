/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifinePshTopology
public import Mathlib.Topology.Bases

/-! # Finite real PSH interval neighborhoods in the initial plurifine topology -/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PlurifineFiniteIntervalNeighborhoods

open FirstPass FirstPass.MongeAmpere PlurifinePshTopology

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private theorem isOpen_finite_intervals (F : Finset (realPshFunctions Ω))
    (a b : realPshFunctions Ω → ℝ) :
    IsOpen[topology Ω] {z : Ω | ∀ f ∈ F, a f < f.val z.val ∧ f.val z.val < b f} := by
  let : TopologicalSpace Ω := topology Ω
  convert isOpen_biInter_finset (fun f (_ : f ∈ F) =>
    (isOpen_Ioo : IsOpen (Ioo (a f) (b f))).preimage
      (continuous_realPsh f.property)) using 1
  ext z
  simp only [mem_iInter, mem_preimage, mem_Ioo, mem_ofPred_eq]

/-- Every plurifine open neighborhood contains an internally chosen finite intersection
of intervals of genuine finite real PSH functions, and that intersection is itself open. -/
theorem exists_finite_intervals_subset_of_mem_open {S : Set Ω}
    (hS : IsOpen[topology Ω] S) {x : Ω} (hx : x ∈ S) :
    ∃ (F : Finset (realPshFunctions Ω)) (a b : realPshFunctions Ω → ℝ),
      (∀ f ∈ F, a f < f.val x.val ∧ f.val x.val < b f) ∧
      IsOpen[topology Ω] {z : Ω | ∀ f ∈ F, a f < f.val z.val ∧ f.val z.val < b f} ∧
      {z : Ω | ∀ f ∈ F, a f < f.val z.val ∧ f.val z.val < b f} ⊆ S := by
  classical
  let : TopologicalSpace Ω := topology Ω
  have hb (f : realPshFunctions Ω) :
      (@nhds Ω (TopologicalSpace.induced (fun z : Ω => f.val z.val) inferInstance) x).HasBasis
        (fun ab : ℝ × ℝ => ab.1 < f.val x.val ∧ f.val x.val < ab.2)
        (fun ab : ℝ × ℝ => {z : Ω | ab.1 < f.val z.val ∧ f.val z.val < ab.2}) := by
    rw [nhds_induced]
    exact (nhds_basis_Ioo (f.val x.val)).comap (fun z : Ω => f.val z.val)
  have hn : S ∈ ⨅ f : realPshFunctions Ω,
      @nhds Ω (TopologicalSpace.induced (fun z : Ω => f.val z.val) inferInstance) x := by
    simpa only [topology, nhds_iInf] using hS.mem_nhds hx
  obtain ⟨⟨F, ab⟩, ⟨hF, hab⟩, hsub⟩ := (HasBasis.iInf' hb).mem_iff.mp hn
  refine ⟨hF.toFinset, fun f => (ab f).1, fun f => (ab f).2, ?_,
    isOpen_finite_intervals _ _ _, ?_⟩
  · intro f hf
    exact hab f (hF.mem_toFinset.mp hf)
  · intro z hz
    apply hsub
    simp only [mem_iInter, mem_ofPred_eq]
    intro f hf
    exact hz f (hF.mem_toFinset.mpr hf)

/-- The actual initial plurifine topology has the pointwise finite real PSH interval
criterion, including zero dimensional and empty domains and empty finite families. -/
theorem isOpen_iff_finite_intervals (S : Set Ω) :
    IsOpen[topology Ω] S ↔ ∀ x ∈ S,
      ∃ (F : Finset (realPshFunctions Ω)) (a b : realPshFunctions Ω → ℝ),
        (∀ f ∈ F, a f < f.val x.val ∧ f.val x.val < b f) ∧
        {z : Ω | ∀ f ∈ F, a f < f.val z.val ∧ f.val z.val < b f} ⊆ S := by
  constructor
  · intro hS x hx
    obtain ⟨F, a, b, hab, _, hsub⟩ := exists_finite_intervals_subset_of_mem_open hS hx
    exact ⟨F, a, b, hab, hsub⟩
  · intro hS
    let : TopologicalSpace Ω := topology Ω
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨F, a, b, hab, hsub⟩ := hS x hx
    exact mem_of_superset ((isOpen_finite_intervals F a b).mem_nhds hab) hsub

end

end SGPT.Foundations.Analysis.Pending.PlurifineFiniteIntervalNeighborhoods
