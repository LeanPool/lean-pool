/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Set.Card

-- [TABLET NODE: P3511T1AttachmentIntersection]

/-!
# P3511T1AttachmentIntersection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3511T1AttachmentIntersection {n count : Nat}
    (vertex : Fin (n + 3) → Real × Real)
    (face : Fin count → Fin 3 → Fin (n + 3))
    (hexact : ∀ k l,
      convexHull Real (Set.range (vertex ∘ face k)) ∩
        convexHull Real (Set.range (vertex ∘ face l)) =
        convexHull Real (vertex '' (Set.range (face k) ∩ Set.range (face l))))
    (order : Fin count ≃ Fin count) (k : Fin count)
    (a b c : Fin (n + 3))
    (hface : Set.range (face (order k)) = {a, b, c})
    (hnew : ∀ l : Fin count, l.val < k.val → c ∉ Set.range (face (order l)))
    (hcount : Set.ncard {l : Fin count | l.val < k.val ∧
      a ∈ Set.range (face (order l)) ∧ b ∈ Set.range (face (order l))} = 1) :
    convexHull Real (Set.range (vertex ∘ face (order k))) ∩
      (⋃ l : {l : Fin count // l.val < k.val},
        convexHull Real (Set.range (vertex ∘ face (order l.val)))) =
      segment Real (vertex a) (vertex b) := by
-- BODY
  classical
  have hsub (l : Fin count) (hl : l.val < k.val) :
      Set.range (face (order k)) ∩ Set.range (face (order l)) ⊆ {a, b} := by
    intro i hi
    rw [hface] at hi
    rcases hi with ⟨hi, hil⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    rcases hi with ha | hb | hc
    · exact Or.inl ha
    · exact Or.inr hb
    · subst i
      exact False.elim (hnew l hl hil)
  have hone : ({l : Fin count | l.val < k.val ∧
      a ∈ Set.range (face (order l)) ∧ b ∈ Set.range (face (order l))}).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcount]
    exact one_ne_zero
  obtain ⟨l, hl, ha, hb⟩ := hone
  have hab : {a, b} ⊆ Set.range (face (order k)) ∩ Set.range (face (order l)) := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact ⟨by rw [hface]; simp, ha⟩
    · exact ⟨by rw [hface]; simp, hb⟩
  have hpair : vertex '' ({a, b} : Set (Fin (n + 3))) = {vertex a, vertex b} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨hxk, hxu⟩ := hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxu
    have hxint : x ∈ convexHull Real
        (vertex '' (Set.range (face (order k)) ∩ Set.range (face (order j.val)))) := by
      rw [← hexact]
      exact ⟨hxk, hxj⟩
    have hm := convexHull_mono (𝕜 := Real) (Set.image_mono (hsub j.val j.property)) hxint
    rw [hpair, convexHull_pair] at hm
    exact hm
  · intro x hx
    have hm : x ∈ convexHull Real
        (vertex '' (Set.range (face (order k)) ∩ Set.range (face (order l)))) := by
      apply convexHull_mono (𝕜 := Real) (Set.image_mono hab)
      rw [hpair, convexHull_pair]
      exact hx
    rw [← hexact] at hm
    exact ⟨hm.1, Set.mem_iUnion.mpr ⟨⟨l, hl⟩, hm.2⟩⟩

end ApollonianSuperharmonic

end
