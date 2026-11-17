/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/IndexPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.OrderMatrixRecursive
public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexJoin

/-!
# Index Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndexPresentation
open Encodable TableIndices IndexMatrix OrderNormalForm

abbrev Dom (Y : Oracle) (e : ℕ) := Valid Y (machine e)
def LE (Y : Oracle) (e f : ℕ) : Prop := ∃ d, ∀ q, ∃ r, orderMatrix Y e f d q r
noncomputable def joinIndex (e f : ℕ) : ℕ := encode (IndexJoin.joined (machine e) (machine f))

theorem joinIndex_primrec : Primrec₂ joinIndex :=
  Primrec.encode.comp (IndexJoin.joined_primrec.comp (machine_primrec.comp Primrec.fst)
    (machine_primrec.comp Primrec.snd))

noncomputable def value (Y : Oracle) (e : ℕ) : Degree := by
  classical
  exact if h : Dom Y e then degree (output Y ⟨machine e, h⟩) else ⊥

theorem value_eq {Y A : Oracle} {e : ℕ} (h : Represents Y (machine e) A) :
    value Y e = degree A := by
  have hv : Dom Y e := (valid_iff_represents _ _).mpr ⟨A, h⟩
  simp only [value, dite_eq_left hv]
  rw [represents_unique (output_represents _ _) h]

theorem value_below (Y : Oracle) (e : ℕ) : value Y e ≤ degree Y := by
  classical
  by_cases h : Dom Y e
  · simp only [value, dite_eq_left h]
    exact represents_reduces (output_represents _ _)
  · simp [value, h]

theorem value_surjective (Y : Oracle) (x : Degree) (hx : x ≤ degree Y) :
    ∃ e, Dom Y e ∧ value Y e = x := by
  obtain ⟨A, rfl⟩ := degree_surjective x
  obtain ⟨d, hd⟩ := reduces_represents hx
  have hr : Represents Y (machine (encode d)) A := by simpa using hd
  exact ⟨encode d, (valid_iff_represents _ _).mpr ⟨A, hr⟩, value_eq hr⟩

theorem le_iff {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    LE Y e f ↔ value Y e ≤ value Y f := by
  rw [value_eq (output_represents Y ⟨machine e, he⟩),
    value_eq (output_represents Y ⟨machine f, hf⟩)]
  exact (order_normal_form (output_represents Y ⟨machine e, he⟩) (output_represents Y ⟨machine f,
    hf⟩)).symm

theorem join_dom {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    Dom Y (joinIndex e f) := by
  apply (valid_iff_represents _ _).mpr
  refine ⟨join (output Y ⟨machine e, he⟩) (output Y ⟨machine f, hf⟩), ?_⟩
  simpa only [joinIndex, machine_encode] using
    IndexJoin.joined_represents (output_represents Y ⟨machine e, he⟩)
      (output_represents Y ⟨machine f, hf⟩)

theorem join_value {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    value Y (joinIndex e f) = value Y e ⊔ value Y f := by
  have hr : Represents Y (machine (joinIndex e f))
      (join (output Y ⟨machine e, he⟩) (output Y ⟨machine f, hf⟩)) := by
    simpa only [joinIndex, machine_encode] using
      IndexJoin.joined_represents (output_represents Y ⟨machine e, he⟩)
        (output_represents Y ⟨machine f, hf⟩)
  rw [value_eq hr, value_eq (output_represents Y ⟨machine e, he⟩),
    value_eq (output_represents Y ⟨machine f, hf⟩)]
  rfl

end TuringRigidity.IndexPresentation

end OAI
