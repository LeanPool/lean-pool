/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4261T1ExteriorIndices
public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification

-- [TABLET NODE: P4261T1EdgeExterior]

/-!
# P4261T1EdgeExterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T1EdgeExterior
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (T : ProtoTile) (a : PeriodicSubtileIndex)
    (hcells : T.cells =
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells)
    (ha : a.first ≠ 0 ∨ a.second ≠ 0)
    (hedge : (FootprintEdges T ∩ FootprintEdges T₀).Nonempty) :
    a ∈ P4261T1ExteriorIndices := by
-- BODY
  classical
  obtain ⟨edge, heT, he₀⟩ := hedge
  obtain ⟨z, hz, hshape⟩ := he₀
  obtain ⟨j, t, hzj⟩ := (cert.outer_union z).1 hz
  let label : SixSubtileLabel :=
    if j = 0 then (if t then .A else .B)
    else if j = 1 then (if t then .C else .D)
    else (if t then .E else .F)
  let b : PeriodicSubtileIndex := ⟨label, 0, 0⟩
  have hzero : GaussianTranslation 0 = id := by
    funext z
    simp [GaussianTranslation]
  have hbcells : (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells =
      (cert.P j t).cells := by
    fin_cases j <;> cases t <;>
      simp [b, label, SubtileOccurrenceInterpretation, TileTranslation, hzero]
  have heb : edge ∈ FootprintEdges
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) := by
    exact ⟨z, by rw [hbcells]; exact hzj, hshape⟩
  have hea : edge ∈ FootprintEdges
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) := by
    obtain ⟨w, hw, hside⟩ := heT
    exact ⟨w, by rw [← hcells]; exact hw, hside⟩
  have hab : a ≠ b := by
    intro heq
    have hf : a.first = 0 := by simpa [b] using congrArg PeriodicSubtileIndex.first heq
    have hs : a.second = 0 := by simpa [b] using congrArg PeriodicSubtileIndex.second heq
    exact ha.elim (fun h => h hf) (fun h => h hs)
  have hinc := (BandOriginalOccurrenceIntersectionClassification q cfg C₀ T₀ cert a b hab).1
    ⟨edge, hea, heb⟩
  have ledger (a b : PeriodicSubtileIndex) (h : AllowedSubtileIncidence a b) :
      (b.first = 0 → b.second = 0 → (a.first ≠ 0 ∨ a.second ≠ 0) →
        a ∈ P4261T1ExteriorIndices) ∧
      (a.first = 0 → a.second = 0 → (b.first ≠ 0 ∨ b.second ≠ 0) →
        b ∈ P4261T1ExteriorIndices) := by
    induction h with
    | symm _ ih => exact ⟨ih.2, ih.1⟩
    | AB m n | AB01 m n | AB11 m n | AC m n | AC11 m n | AD m n
    | AE01 m n | AF m n | BC m n | BDm1m1 m n | BD m n | BE m n
    | BF0m1 m n | CDm10 m n | CEm10 m n | CF m n | DE m n | DF10 m n =>
      constructor <;> intro hf hs hn <;>
        simp_all [P4261T1ExteriorIndices, PeriodicSubtileIndex.mk.injEq]
      all_goals omega
  exact (ledger a b hinc).1 rfl rfl ha

end ApollonianSuperharmonic

end
