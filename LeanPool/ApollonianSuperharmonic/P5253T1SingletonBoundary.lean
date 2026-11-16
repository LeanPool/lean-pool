/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices

-- [TABLET NODE: P5253T1SingletonBoundary]

/-!
# P5253T1SingletonBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5253T1SingletonBoundary (c a : GaussianInt) :
    let U : ProtoTile := ⟨{c}, a⟩
    BoundaryFootprintVertices U = {c, c + 1, c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩} ∧
    BoundaryFootprintEdges U =
      {{c, c + 1}, {c, c + ⟨0, 1⟩},
        {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}, {c + 1, c + 1 + ⟨0, 1⟩}} := by
-- BODY
  classical
  dsimp only
  have edges : BoundaryFootprintEdges (⟨{c}, a⟩ : ProtoTile) =
      {{c, c + 1}, {c, c + ⟨0, 1⟩},
        {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}, {c + 1, c + 1 + ⟨0, 1⟩}} := by
    ext e
    constructor
    · rintro ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
      · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
        · have : z = c := Finset.mem_singleton.mp hz
          subst z
          simp
        · have hz : z = c + ⟨0, 1⟩ :=
            (sub_eq_iff_eq_add).mp (Finset.mem_singleton.mp hz)
          subst z
          simp [add_assoc, add_comm, add_left_comm]
      · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
        · have : z = c := Finset.mem_singleton.mp hz
          subst z
          simp
        · have hz : z = c + 1 :=
            (sub_eq_iff_eq_add).mp (Finset.mem_singleton.mp hz)
          subst z
          simp
    · intro he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨c, Or.inl ⟨rfl, Or.inl ⟨by simp, ?_⟩⟩⟩
        simp [Zsqrtd.ext_iff]
      · refine ⟨c, Or.inr ⟨rfl, Or.inl ⟨by simp, ?_⟩⟩⟩
        simp []
      · refine ⟨c + ⟨0, 1⟩, Or.inl ⟨?_, Or.inr ⟨?_, by simp⟩⟩⟩
        · simp [add_assoc, add_comm, add_left_comm]
        · simp [Zsqrtd.ext_iff]
      · refine ⟨c + 1, Or.inr ⟨rfl, Or.inr ⟨?_, by simp⟩⟩⟩
        simp []
  refine ⟨?_, edges⟩
  rw [BoundaryFootprintVertices, ite_eq_left (Finset.singleton_nonempty c)]
  ext v
  simp only [Set.mem_ofPred_eq, edges, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, Finset.mem_insert, Finset.mem_singleton]
  tauto

end ApollonianSuperharmonic

end
