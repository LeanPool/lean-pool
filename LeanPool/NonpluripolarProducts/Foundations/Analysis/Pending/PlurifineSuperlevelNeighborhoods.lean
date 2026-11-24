/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineFiniteIntervalNeighborhoods

/-! # Ordinary open neighborhoods and finite PSH strict superlevels -/

@[expose] public section

open Set TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PlurifineSuperlevelNeighborhoods

open FirstPass FirstPass.MongeAmpere PlurifinePshTopology

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private theorem isOpen_realPsh_sublevel_ordinary (f : realPshFunctions Ω) (b : ℝ) :
    IsOpen {z : Ω | f.val z.val < b} := by
  have hsc : UpperSemicontinuousOn (fun z : Ω => (f.val z.val : EReal)) univ :=
    f.property.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => z.property)
  have ho := (upperSemicontinuousOn_univ_iff.mp hsc).isOpen_preimage (b : EReal)
  convert ho using 1
  ext z
  simp only [mem_ofPred_eq, mem_preimage, mem_Iio, EReal.coe_lt_coe_iff]

/-- The finite upper endpoint conditions are internally absorbed into an ordinary
open set; the remaining strict PSH superlevels give a genuine plurifine neighborhood. -/
theorem exists_ordinary_open_finite_superlevels {S : Set Ω}
    (hS : IsOpen[topology Ω] S) {x : Ω} (hx : x ∈ S) :
    ∃ (F : Finset (realPshFunctions Ω)) (a : realPshFunctions Ω → ℝ) (O : Set Ω),
      IsOpen O ∧ x ∈ O ∧ (∀ f ∈ F, a f < f.val x.val) ∧
      IsOpen[topology Ω] (O ∩ {z : Ω | ∀ f ∈ F, a f < f.val z.val}) ∧
      O ∩ {z : Ω | ∀ f ∈ F, a f < f.val z.val} ⊆ S := by
  obtain ⟨F, a, b, hab, hBopen, hBsub⟩ :=
    PlurifineFiniteIntervalNeighborhoods.exists_finite_intervals_subset_of_mem_open hS hx
  let O : Set Ω := {z : Ω | ∀ f ∈ F, f.val z.val < b f}
  have ho : IsOpen O := by
    convert isOpen_biInter_finset (fun f (_ : f ∈ F) =>
      isOpen_realPsh_sublevel_ordinary f (b f)) using 1
    ext z
    simp only [O, mem_ofPred_eq, mem_iInter]
  have heq : O ∩ {z : Ω | ∀ f ∈ F, a f < f.val z.val} =
      {z : Ω | ∀ f ∈ F, a f < f.val z.val ∧ f.val z.val < b f} := by
    ext z
    constructor
    · intro hz f hf
      exact ⟨hz.2 f hf, hz.1 f hf⟩
    · intro hz
      exact ⟨fun f hf => (hz f hf).2, fun f hf => (hz f hf).1⟩
  refine ⟨F, a, O, ho, (fun f hf => (hab f hf).2),
    (fun f hf => (hab f hf).1), ?_, ?_⟩
  · rw [heq]
    exact hBopen
  · rw [heq]
    exact hBsub

end

end SGPT.Foundations.Analysis.Pending.PlurifineSuperlevelNeighborhoods
