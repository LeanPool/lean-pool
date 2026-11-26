/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5Forest
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-!
# The cluster of far hair ends in XVI (6.3)

Choose a largest family of pairs whose ends are far from the ends of
every other pair. Either it has `μ` members, or every remaining pair
has an end near this family. The pigeonhole principle gives many pairs
near one end. At most one near end of a hair can be in that group, since
all near ends are widely separated. Thus many far ends lie near one point.
-/

public section
namespace GraphMinor.GM16
open Set Function
universe w

/-- The maximal-family and pigeonhole argument producing `Y₄` in XVI
(6.3), page 60. The maximality condition applies to every member of `Y`,
correcting the printed sentence that says only `y ∈ Y₂`. -/
theorem separated_pairs_or_far_end_cluster
    {S : Type w} {U Y : Set S} {far : S → S} {d : S → S → ℕ} {r μ k : ℕ}
    (hY : Y.Finite) (hYU : Y ⊆ U) (hfarU : ∀ y ∈ Y, far y ∈ U)
    (hr : 1 ≤ r)
    (hself : ∀ z ∈ U, d z z = 0)
    (hsymm : ∀ a ∈ U, ∀ b ∈ U, d a b = d b a)
    (htri : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, d a c ≤ d a b + d b c)
    (hsep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 2 * r < d y z)
    (hcount : 2 * (μ - 1) * k < Y.ncard) :
    (∃ f : Fin μ ↪ S, (∀ i, f i ∈ Y) ∧
      ∀ i j, i ≠ j → ∀ a ∈ ({f i, far (f i)} : Set S),
        ∀ b ∈ ({f j, far (f j)} : Set S), r ≤ d a b) ∨
    (∃ w ∈ U, ∃ Y₄ ⊆ Y, k ≤ Y₄.ncard ∧ ∀ y ∈ Y₄, d (far y) w < r) := by
  classical
  let cross : S → S → Prop := fun y z =>
    ∀ a ∈ ({y, far y} : Set S), ∀ b ∈ ({z, far z} : Set S), r ≤ d a b
  let good : Finset S → Prop := fun I =>
    ∀ y ∈ I, ∀ z ∈ I, y ≠ z → cross y z
  let candidates := hY.toFinset.powerset.filter good
  have hempty : (∅ : Finset S) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by intro y hy; exact False.elim (Finset.notMem_empty y hy)⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hIY : (I : Set S) ⊆ Y := by
    intro y hy
    exact hY.mem_toFinset.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1) hy)
  have hIgood : good I := (Finset.mem_filter.mp hI).2
  by_cases hlarge : μ ≤ I.card
  · obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin μ) (s := I) (by simpa using hlarge)
    refine Or.inl ⟨f, fun i => hIY (hf ⟨i, rfl⟩), ?_⟩
    intro i j hij
    exact hIgood (f i) (hf ⟨i, rfl⟩) (f j) (hf ⟨j, rfl⟩) (f.injective.ne hij)
  · let W := (I : Set S) ∪ far '' (I : Set S)
    have hW : W.Finite := I.finite_toSet.union (I.finite_toSet.image far)
    have hWU : W ⊆ U := by
      rintro z (hz | ⟨y, hy, rfl⟩)
      · exact hYU (hIY hz)
      · exact hfarU y (hIY hy)
    have hWcard : W.ncard ≤ 2 * (μ - 1) := by
      have hc := ncard_union_le (I : Set S) (far '' (I : Set S))
      have himg := ncard_image_le (f := far) (s := (I : Set S))
      rw [ncard_coe_finset] at hc himg
      change ((I : Set S) ∪ far '' (I : Set S)).ncard ≤ 2 * (μ - 1)
      omega
    have hnear : ∀ y ∈ Y, ∃ w ∈ W, d y w < r ∨ d (far y) w < r := by
      intro y hy
      by_cases hyI : y ∈ I
      · refine ⟨y, Or.inl hyI, Or.inl ?_⟩
        rw [hself y (hYU hy)]
        exact hr
      · by_contra hnone
        have hfar : ∀ w ∈ W, r ≤ d y w ∧ r ≤ d (far y) w := by
          intro w hw
          exact ⟨Nat.le_of_not_gt (fun h => hnone ⟨w, hw, Or.inl h⟩),
            Nat.le_of_not_gt (fun h => hnone ⟨w, hw, Or.inr h⟩)⟩
        have hcross : ∀ z ∈ I, cross y z := by
          intro z hz a ha b hb
          have hbW : b ∈ W := by
            rcases hb with rfl | hb
            · exact Or.inl hz
            · exact Or.inr ⟨z, hz, (mem_singleton_iff.mp hb).symm⟩
          rcases ha with rfl | ha
          · exact (hfar b hbW).1
          · have hay := mem_singleton_iff.mp ha
            subst a
            exact (hfar b hbW).2
        have hgood : good (insert y I) := by
          intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with hay | haI
          · subst a
            rcases Finset.mem_insert.mp hb with hby | hbI
            · exact False.elim (hab hby.symm)
            · exact hcross b hbI
          · rcases Finset.mem_insert.mp hb with hby | hbI
            · subst b
              intro z hz w hw
              have hzU : z ∈ U := by
                rcases hz with rfl | hz
                · exact hYU (hIY haI)
                · exact (mem_singleton_iff.mp hz) ▸ hfarU a (hIY haI)
              have hwU : w ∈ U := by
                rcases hw with rfl | hw
                · exact hYU hy
                · exact (mem_singleton_iff.mp hw) ▸ hfarU y hy
              rw [hsymm z hzU w hwU]
              exact hcross a haI w hw z hz
            · exact hIgood a haI b hbI hab
        have hinsert : insert y I ∈ candidates := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr ?_, hgood⟩
          exact Finset.insert_subset (hY.mem_toFinset.mpr hy)
            (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1)
        have hc := hmax (insert y I) hinsert
        rw [Finset.card_insert_of_notMem hyI] at hc
        omega
    let witness : S → S := fun y => if hy : y ∈ Y then (hnear y hy).choose else y
    have hwitness : ∀ y ∈ Y, witness y ∈ W ∧
        (d y (witness y) < r ∨ d (far y) (witness y) < r) := by
      intro y hy
      dsimp only [witness]
      rw [dite_eq_left hy]
      exact (hnear y hy).choose_spec
    have hnum : k * W.ncard < Y.ncard := by
      have hc := Nat.mul_le_mul_right k hWcard
      rw [Nat.mul_comm W.ncard k] at hc
      exact hc.trans_lt hcount
    obtain ⟨w, hwW, Y₃, hY₃Y, hY₃card, hY₃w⟩ :=
      exists_many_marked_vertices_at_one_vertex hW hY
        (fun y hy => (hwitness y hy).1) hnum
    have hoptions : ∀ y ∈ Y₃, d y w < r ∨ d (far y) w < r := by
      intro y hy
      have hopt := (hwitness y (hY₃Y hy)).2
      rwa [hY₃w y hy] at hopt
    let bad := {y ∈ Y₃ | d y w < r}
    have hbadfin : bad.Finite := hY.subset (fun _ h => hY₃Y h.1)
    have hbad : bad.ncard ≤ 1 := by
      apply (ncard_le_one hbadfin).mpr
      intro y hy z hz
      by_contra hyz
      have hyY := hY₃Y hy.1
      have hzY := hY₃Y hz.1
      have hc := htri y (hYU hyY) w (hWU hwW) z (hYU hzY)
      rw [hsymm w (hWU hwW) z (hYU hzY)] at hc
      have hd := hsep y hyY z hzY hyz
      have hynear : d y w < r := hy.2
      have hznear : d z w < r := hz.2
      omega
    refine Or.inr ⟨w, hWU hwW, Y₃ \ bad, fun y hy => hY₃Y hy.1, ?_, ?_⟩
    · have hc := ncard_le_ncard_sdiff_add_ncard Y₃ bad hbadfin
      omega
    · intro y hy
      exact (hoptions y hy.1).resolve_left (fun h => hy.2 ⟨hy.1, h⟩)

end GraphMinor.GM16
