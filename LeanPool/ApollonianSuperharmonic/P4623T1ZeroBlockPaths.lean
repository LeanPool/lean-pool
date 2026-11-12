/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import Mathlib.Logic.Relation

-- [TABLET NODE: P4623T1ZeroBlockPaths]

/-!
# P4623T1ZeroBlockPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4623T1ZeroBlockPaths :
    let K : Finset PeriodicSubtileIndex :=
      {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
        ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
    ∀ S : Finset PeriodicSubtileIndex,
      (S = K ∨ ∃ d ∈ K, S = K.erase d) →
      ∀ a ∈ S, ∀ b ∈ S,
        Relation.ReflTransGen
          (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) a b := by
-- BODY
  classical
  dsimp only
  let K : Finset PeriodicSubtileIndex :=
    {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
  have reverse {S : Finset PeriodicSubtileIndex} {a b}
      (h : Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) a b) :
      Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) b a := by
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single ⟨e.1.symm, e.2.2, e.2.1⟩).trans ih
  have tree (S : Finset PeriodicSubtileIndex) (root : PeriodicSubtileIndex)
      (hroot : ∀ a ∈ S, Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) a root) :
      ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) a b := by
    intro a ha b hb
    exact (hroot a ha).trans (reverse (hroot b hb))
  have edge (S : Finset PeriodicSubtileIndex) (a b : PeriodicSubtileIndex)
      (e : AllowedSubtileIncidence a b) (ha : a ∈ S) (hb : b ∈ S) :
      Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∈ S ∧ y ∈ S) a b :=
    .single ⟨e, ha, hb⟩
  intro S hS
  rcases hS with rfl | ⟨d, hd, rfl⟩
  · apply tree K ⟨.A, 0, 0⟩
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .refl
    · exact edge _ _ _ (AllowedSubtileIncidence.AB 0 0).symm (by decide) (by decide)
    · exact edge _ _ _ (AllowedSubtileIncidence.AC 0 0).symm (by decide) (by decide)
    · exact edge _ _ _ (AllowedSubtileIncidence.AD 0 0).symm (by decide) (by decide)
    · exact (edge _ _ _ (AllowedSubtileIncidence.BE 0 0).symm (by decide) (by decide)).trans
        (edge _ _ _ (AllowedSubtileIncidence.AB 0 0).symm (by decide) (by decide))
    · exact edge _ _ _ (AllowedSubtileIncidence.AF 0 0).symm (by decide) (by decide)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · apply tree _ ⟨.B, 0, 0⟩
      intro a ha
      simp only [Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha with ⟨hne, rfl | rfl | rfl | rfl | rfl | rfl⟩
      · exact (hne rfl).elim
      · exact .refl
      · exact edge _ _ _ (AllowedSubtileIncidence.BC 0 0).symm (by decide) (by decide)
      · exact edge _ _ _ (AllowedSubtileIncidence.BD 0 0).symm (by decide) (by decide)
      · exact edge _ _ _ (AllowedSubtileIncidence.BE 0 0).symm (by decide) (by decide)
      · exact (edge _ _ _ (AllowedSubtileIncidence.CF 0 0).symm (by decide) (by decide)).trans
          (edge _ _ _ (AllowedSubtileIncidence.BC 0 0).symm (by decide) (by decide))
    · apply tree _ ⟨.A, 0, 0⟩
      intro a ha
      simp only [Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha with ⟨hne, rfl | rfl | rfl | rfl | rfl | rfl⟩
      · exact .refl
      · exact (hne rfl).elim
      · exact edge _ _ _ (AllowedSubtileIncidence.AC 0 0).symm (by decide) (by decide)
      · exact edge _ _ _ (AllowedSubtileIncidence.AD 0 0).symm (by decide) (by decide)
      · exact (edge _ _ _ (AllowedSubtileIncidence.DE 0 0).symm (by decide) (by decide)).trans
          (edge _ _ _ (AllowedSubtileIncidence.AD 0 0).symm (by decide) (by decide))
      · exact edge _ _ _ (AllowedSubtileIncidence.AF 0 0).symm (by decide) (by decide)
    all_goals
      apply tree _ ⟨.A, 0, 0⟩
      intro a ha
      simp only [Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha with ⟨hne, rfl | rfl | rfl | rfl | rfl | rfl⟩
      all_goals first
        | exact (hne rfl).elim
        | exact .refl
        | exact edge _ _ _ (AllowedSubtileIncidence.AB 0 0).symm (by decide) (by decide)
        | exact edge _ _ _ (AllowedSubtileIncidence.AC 0 0).symm (by decide) (by decide)
        | exact edge _ _ _ (AllowedSubtileIncidence.AD 0 0).symm (by decide) (by decide)
        | exact edge _ _ _ (AllowedSubtileIncidence.AF 0 0).symm (by decide) (by decide)
        | exact (edge _ _ _ (AllowedSubtileIncidence.BE 0 0).symm (by decide) (by decide)).trans
            (edge _ _ _ (AllowedSubtileIncidence.AB 0 0).symm (by decide) (by decide))

end ApollonianSuperharmonic

end
