/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Adapted from the MacMahon cube formalization for Lean Pool.
module

public import LeanPool.MacMahon.Definitions

import Mathlib.Algebra.Group.Fin.Basic

/-!
# Matching oriented corners by proper rotations

An ordering of the outward faces with positive determinant is preserved up to cyclic shift.
The canonically ordered colour triple identifies the corner in Conway's tableau.
-/

namespace MacMahon

/-- Swap the last two axes when the slot has an odd number of negative directions. -/
private def orientedIndex (k : Slot) (f : Fin 3) : Fin 3 :=
  if (k.val + k.val / 2 + k.val / 4) % 2 = 0 then f else -f

private theorem orientedIndex_involutive (k : Slot) : Function.Involutive (orientedIndex k) := by
  intro f
  by_cases h : (k.val + k.val / 2 + k.val / 4) % 2 = 0 <;> simp [orientedIndex, h]

private def orientedFaces (k : Slot) (f : Fin 3) : Fin 6 :=
  exposedFaces k (orientedIndex k f)

private theorem rotated_faces : ∀ k : Slot, ∀ r : Fin 24, ∃ l : Slot, ∃ shift : Fin 3,
    ∀ f : Fin 3, rotations r (orientedFaces k f) = orientedFaces l (f + shift) := by
  decide +kernel

private theorem realize_rotated_faces : ∀ k l : Slot, ∀ shift : Fin 3, ∃ r : Fin 24,
    ∀ f : Fin 3, rotations r (orientedFaces k f) = orientedFaces l (f + shift) := by
  decide +kernel

private def CyclicMatch (a b : Fin 3 → Fin 7) : Prop :=
  ∃ shift : Fin 3, ∀ f : Fin 3, a (f + shift) = b f

private theorem CyclicMatch.symm {a b : Fin 3 → Fin 7} (h : CyclicMatch a b) :
    CyclicMatch b a := by
  obtain ⟨shift, hshift⟩ := h
  refine ⟨-shift, fun f => ?_⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using (hshift (f + -shift)).symm

private theorem CyclicMatch.trans {a b c : Fin 3 → Fin 7}
    (hab : CyclicMatch a b) (hbc : CyclicMatch b c) : CyclicMatch a c := by
  obtain ⟨r, hr⟩ := hab
  obtain ⟨s, hs⟩ := hbc
  refine ⟨s + r, fun f => ?_⟩
  rw [← add_assoc, hr, hs]

private def orientedColours (p : Pair) (k : Slot) (f : Fin 3) : Fin 7 :=
  faceColours p.1 p.2 (orientedFaces k f)

private theorem faceFits_iff_cyclic_match (t p : Pair) (k : Slot) :
    (∃ r : Fin 24, FaceFits t p k r) ↔
      ∃ l : Slot, CyclicMatch (orientedColours p l) (orientedColours t k) := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨l, shift, h⟩ := rotated_faces k r
    exact ⟨l, shift, fun f =>
      (congrArg (faceColours p.1 p.2) (h f)).symm.trans (hr (orientedIndex k f))⟩
  · rintro ⟨l, shift, h⟩
    obtain ⟨r, hr⟩ := realize_rotated_faces k l shift
    refine ⟨r, fun f => ?_⟩
    obtain ⟨g, rfl⟩ := (orientedIndex_involutive k).surjective f
    exact (congrArg (faceColours p.1 p.2) (hr g)).trans (h g)

/-- Conway corner codes in lexicographic order, with the least colour first. -/
private def cornerSignature : Corner → Fin 3 → Fin 7 :=
  ![![1, 2, 3], ![1, 2, 4], ![1, 2, 5], ![1, 2, 6], ![1, 3, 2],
    ![1, 3, 4], ![1, 3, 5], ![1, 3, 6], ![1, 4, 2], ![1, 4, 3],
    ![1, 4, 5], ![1, 4, 6], ![1, 5, 2], ![1, 5, 3], ![1, 5, 4],
    ![1, 5, 6], ![1, 6, 2], ![1, 6, 3], ![1, 6, 4], ![1, 6, 5],
    ![2, 3, 4], ![2, 3, 5], ![2, 3, 6], ![2, 4, 3], ![2, 4, 5],
    ![2, 4, 6], ![2, 5, 3], ![2, 5, 4], ![2, 5, 6], ![2, 6, 3],
    ![2, 6, 4], ![2, 6, 5], ![3, 4, 5], ![3, 4, 6], ![3, 5, 4],
    ![3, 5, 6], ![3, 6, 4], ![3, 6, 5], ![4, 5, 6], ![4, 6, 5]]

private theorem signature_first_ne_zero : ∀ c : Corner, cornerSignature c 0 ≠ 0 := by
  decide +kernel

private theorem signature_label_eq : ∀ a b : Corner, ∀ shift : Fin 3,
    (∀ f : Fin 3, cornerSignature a (f + shift) = cornerSignature b f) → a = b := by
  decide +kernel

private theorem slot_signature_exists : ∀ i j : Label, i ≠ j → ∀ k : Slot, ∃ shift : Fin 3,
    ∀ f : Fin 3, orientedColours (i, j) k (f + shift) = cornerSignature (cornerAt i j k) f := by
  decide +kernel

private theorem hasCorner_iff_slot : ∀ i j : Label, i ≠ j → ∀ c : Corner,
    HasCorner (i, j) c ↔ ∃ k : Slot, cornerAt i j k = c := by
  decide +kernel

private theorem diagonal_has_no_corner : ∀ i : Label, ∀ c : Corner, ¬ HasCorner (i, i) c := by
  decide +kernel

private theorem diagonal_colours : ∀ i : Label, ∀ k : Slot, ∀ f : Fin 3,
    orientedColours (i, i) k f = 0 := by
  decide +kernel

/-- A valid tableau target matches a proper rotation exactly when its corner code is present. -/
public theorem face_corner_of_ne (i j : Label) (hij : i ≠ j) (p : Pair) (k : Slot) :
    HasCorner p (cornerAt i j k) ↔ ∃ r : Fin 24, FaceFits (i, j) p k r := by
  rcases p with ⟨a, b⟩
  rw [faceFits_iff_cyclic_match]
  have htarget : CyclicMatch (orientedColours (i, j) k) (cornerSignature (cornerAt i j k)) :=
    slot_signature_exists i j hij k
  by_cases hab : a = b
  · subst b
    refine ⟨fun h => (diagonal_has_no_corner a _ h).elim, ?_⟩
    rintro ⟨l, h⟩
    obtain ⟨shift, hshift⟩ := h.trans htarget
    exact (signature_first_ne_zero _ ((hshift 0).symm.trans (diagonal_colours a l _))).elim
  · rw [hasCorner_iff_slot a b hab]
    refine exists_congr fun l => ?_
    have hsource : CyclicMatch (orientedColours (a, b) l) (cornerSignature (cornerAt a b l)) :=
      slot_signature_exists a b hab l
    constructor
    · intro h
      rw [h] at hsource
      exact hsource.trans htarget.symm
    · intro h
      obtain ⟨shift, hshift⟩ := hsource.symm.trans (h.trans htarget)
      exact signature_label_eq _ _ shift hshift

end MacMahon
