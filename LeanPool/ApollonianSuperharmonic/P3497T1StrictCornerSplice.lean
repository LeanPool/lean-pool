/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import Mathlib.Analysis.Convex.Basic
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant

-- [TABLET NODE: P3497T1StrictCornerSplice]

/-!
# P3497T1StrictCornerSplice

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3497T1StrictCornerSplice (a b c : Real × Real)
    (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c)
    (hdet : P3381T1TriangleDeterminant ![a, b, c] = 0)
    (hint : segment Real a b ∩ segment Real b c = {b}) :
    ∃ t : Real, 0 < t ∧ t < 1 ∧
      b = (1 - t) • a + t • c ∧
      segment Real a b ∪ segment Real b c = segment Real a c := by
-- BODY
  have hd : (b.1 - a.1) * (c.2 - a.2) -
      (c.1 - a.1) * (b.2 - a.2) = 0 := by
    simpa [P3381T1TriangleDeterminant] using hdet
  have hp : ∃ t : Real, b = (1 - t) • a + t • c := by
    by_cases hx : c.1 - a.1 = 0
    · have hy : c.2 - a.2 ≠ 0 := by
        intro hy
        apply hac
        ext <;> linarith
      refine ⟨(b.2 - a.2) / (c.2 - a.2), ?_⟩
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      · field_simp
        nlinarith
      · field_simp
        ring
    · refine ⟨(b.1 - a.1) / (c.1 - a.1), ?_⟩
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      · field_simp
        ring
      · field_simp
        nlinarith
  obtain ⟨t, ht⟩ := hp
  have ht0 : 0 < t := by
    by_contra hn
    have hle : t ≤ 0 := le_of_not_gt hn
    have hden : 0 < 1 - t := by linarith
    have ha : a ∈ segment Real b c := by
      rw [segment_eq_image]
      refine ⟨-t / (1 - t), ?_, ?_⟩
      · constructor
        · exact div_nonneg (neg_nonneg.mpr hle) (le_of_lt hden)
        · apply (div_le_one hden).mpr
          linarith
      · rw [ht]
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]
        all_goals field_simp
        all_goals ring
    have ha' : a ∈ segment Real a b ∩ segment Real b c :=
      ⟨left_mem_segment Real a b, ha⟩
    rw [hint, Set.mem_singleton_iff] at ha'
    exact hab ha'
  have ht1 : t < 1 := by
    by_contra hn
    have hle : 1 ≤ t := le_of_not_gt hn
    have hc : c ∈ segment Real a b := by
      rw [segment_eq_image]
      refine ⟨1 / t, ?_, ?_⟩
      · constructor
        · exact div_nonneg (by norm_num) (le_of_lt ht0)
        · exact (div_le_one ht0).mpr hle
      · rw [ht]
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]
        all_goals field_simp
        all_goals ring
    have hc' : c ∈ segment Real a b ∩ segment Real b c :=
      ⟨hc, right_mem_segment Real b c⟩
    rw [hint, Set.mem_singleton_iff] at hc'
    exact hbc hc'.symm
  refine ⟨t, ht0, ht1, ht, ?_⟩
  have hb : b ∈ segment Real a c := by
    rw [segment_eq_image]
    exact ⟨t, ⟨le_of_lt ht0, le_of_lt ht1⟩, ht.symm⟩
  apply Set.Subset.antisymm
  · apply Set.union_subset
    · exact (convex_segment a c).segment_subset (left_mem_segment Real a c) hb
    · exact (convex_segment a c).segment_subset hb (right_mem_segment Real a c)
  · intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    by_cases hut : u ≤ t
    · apply Set.mem_union_left
      rw [segment_eq_image]
      refine ⟨u / t, ⟨div_nonneg hu.1 (le_of_lt ht0), (div_le_one ht0).mpr hut⟩, ?_⟩
      rw [ht]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      all_goals field_simp
      all_goals ring
    · apply Set.mem_union_right
      rw [segment_eq_image]
      have hden : 0 < 1 - t := sub_pos.mpr ht1
      refine ⟨(u - t) / (1 - t), ?_, ?_⟩
      · constructor
        · exact div_nonneg (by linarith) (le_of_lt hden)
        · apply (div_le_one hden).mpr
          linarith [hu.2]
      · rw [ht]
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]
        all_goals field_simp
        all_goals ring

end ApollonianSuperharmonic

end
