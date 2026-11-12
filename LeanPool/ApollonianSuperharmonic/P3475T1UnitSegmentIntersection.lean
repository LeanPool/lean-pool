/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P3475T1UnitSegmentIntersection]

/-!
# P3475T1UnitSegmentIntersection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3475T1UnitSegmentIntersection (a b c d : GaussianInt)
    (hab : FourNeighborAdjacent a b) (hcd : FourNeighborAdjacent c d)
    (hne : ({a, b} : Finset GaussianInt) ≠ {c, d}) :
    segment Real (GaussianRealPoint a) (GaussianRealPoint b) ∩
      segment Real (GaussianRealPoint c) (GaussianRealPoint d) =
      {z | (z = GaussianRealPoint a ∨ z = GaussianRealPoint b) ∧
        (z = GaussianRealPoint c ∨ z = GaussianRealPoint d)} := by
-- BODY
  have horizontal (a : GaussianInt) (z : Real × Real) :
      z ∈ segment Real (GaussianRealPoint a) (GaussianRealPoint (a + 1)) ↔
        z.2 = (a.im : Real) ∧ (a.re : Real) ≤ z.1 ∧ z.1 ≤ (a.re : Real) + 1 := by
    rw [segment_eq_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [Set.mem_Icc] at ht
      simp only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
        Zsqrtd.im_one, Int.cast_add, Int.cast_one, add_zero, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      exact ⟨by ring, by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · rintro ⟨hy, hx0, hx1⟩
      refine ⟨z.1 - (a.re : Real), ⟨by linarith, by linarith⟩, ?_⟩
      apply Prod.ext
      · simp only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add,
          Int.cast_one, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
        ring
      · simp only [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one, add_zero,
          Prod.smul_snd, Prod.snd_add, smul_eq_mul]
        nlinarith
  have vertical (a : GaussianInt) (z : Real × Real) :
      z ∈ segment Real (GaussianRealPoint a) (GaussianRealPoint (a + ⟨0, 1⟩)) ↔
        z.1 = (a.re : Real) ∧ (a.im : Real) ≤ z.2 ∧ z.2 ≤ (a.im : Real) + 1 := by
    rw [segment_eq_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [Set.mem_Icc] at ht
      simp only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
        Int.cast_add, Int.cast_one, add_zero, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      exact ⟨by ring, by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · rintro ⟨hx, hy0, hy1⟩
      refine ⟨z.2 - (a.im : Real), ⟨by linarith, by linarith⟩, ?_⟩
      apply Prod.ext
      · simp only [GaussianRealPoint, Zsqrtd.re_add,
          add_zero, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
        nlinarith
      · simp only [GaussianRealPoint, Zsqrtd.im_add, Int.cast_add, Int.cast_one,
          Prod.smul_snd, Prod.snd_add, smul_eq_mul]
        ring
  have integer_interval (u v : Int) (x : Real) (hu : (u : Real) ≤ x)
      (hu' : x ≤ (u : Real) + 1) (hv : (v : Real) ≤ x)
      (hv' : x ≤ (v : Real) + 1) (hne : u ≠ v) :
      (x = (u : Real) ∨ x = (u : Real) + 1) ∧
        (x = (v : Real) ∨ x = (v : Real) + 1) := by
    by_cases hlt : u < v
    · have hgap : (u : Real) + 1 ≤ (v : Real) := by
        exact_mod_cast (show u + 1 ≤ v by omega)
      exact ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
    · have hgap : (v : Real) + 1 ≤ (u : Real) := by
        exact_mod_cast (show v + 1 ≤ u by omega)
      exact ⟨Or.inl (by linarith), Or.inr (by linarith)⟩
  have cross (a c : GaussianInt) (z : Real × Real)
      (ha : z ∈ segment Real (GaussianRealPoint a) (GaussianRealPoint (a + 1)))
      (hc : z ∈ segment Real (GaussianRealPoint c)
        (GaussianRealPoint (c + ⟨0, 1⟩))) :
      (z = GaussianRealPoint a ∨ z = GaussianRealPoint (a + 1)) ∧
        (z = GaussianRealPoint c ∨ z = GaussianRealPoint (c + ⟨0, 1⟩)) := by
    rcases (horizontal a z).mp ha with ⟨hy, hx0, hx1⟩
    rcases (vertical c z).mp hc with ⟨hx, hy0, hy1⟩
    have hx0' : a.re ≤ c.re := by exact_mod_cast (hx ▸ hx0)
    have hx1' : c.re ≤ a.re + 1 := by exact_mod_cast (hx ▸ hx1)
    have hy0' : c.im ≤ a.im := by exact_mod_cast (hy ▸ hy0)
    have hy1' : a.im ≤ c.im + 1 := by exact_mod_cast (hy ▸ hy1)
    constructor
    · have h : c.re = a.re ∨ c.re = a.re + 1 := by omega
      rcases h with h | h
      · left
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · rw [hx, h]
        · exact hy
      · right
        apply Prod.ext
        · simpa only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
            Int.cast_add, Int.cast_one] using hx.trans (congrArg (fun t : Int => (t : Real)) h)
        · simpa only [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one, add_zero] using hy
    · have h : a.im = c.im ∨ a.im = c.im + 1 := by omega
      rcases h with h | h
      · left
        apply Prod.ext <;> simp only [GaussianRealPoint]
        · exact hx
        · rw [hy, h]
      · right
        apply Prod.ext
        · simpa only [GaussianRealPoint, Zsqrtd.re_add, Int.cast_add, Int.cast_zero,
            add_zero] using hx
        · simpa only [GaussianRealPoint, Zsqrtd.im_add, Int.cast_add, Int.cast_one]
            using hy.trans (congrArg (fun t : Int => (t : Real)) h)
  have canonical (a c u v : GaussianInt) (hu : u = 1 ∨ u = ⟨0, 1⟩)
      (hv : v = 1 ∨ v = ⟨0, 1⟩)
      (hne : ({a, a + u} : Finset GaussianInt) ≠ {c, c + v})
      (z : Real × Real)
      (ha : z ∈ segment Real (GaussianRealPoint a) (GaussianRealPoint (a + u)))
      (hc : z ∈ segment Real (GaussianRealPoint c) (GaussianRealPoint (c + v))) :
      (z = GaussianRealPoint a ∨ z = GaussianRealPoint (a + u)) ∧
        (z = GaussianRealPoint c ∨ z = GaussianRealPoint (c + v)) := by
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rcases (horizontal a z).mp ha with ⟨hyA, hA0, hA1⟩
      rcases (horizontal c z).mp hc with ⟨hyC, hC0, hC1⟩
      have him : a.im = c.im := by exact_mod_cast hyA.symm.trans hyC
      have hre : a.re ≠ c.re := by
        intro h
        have heq : a = c := Zsqrtd.ext h him
        exact hne (by rw [heq])
      rcases integer_interval a.re c.re z.1 hA0 hA1 hC0 hC1 hre with ⟨hA, hC⟩
      constructor
      · rcases hA with h | h
        · left; exact Prod.ext h hyA
        · right
          apply Prod.ext
          · simpa only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
              Int.cast_add, Int.cast_one] using h
          · simpa only [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one, add_zero] using hyA
      · rcases hC with h | h
        · left; exact Prod.ext h hyC
        · right
          apply Prod.ext
          · simpa only [GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.re_one,
              Int.cast_add, Int.cast_one] using h
          · simpa only [GaussianRealPoint, Zsqrtd.im_add, Zsqrtd.im_one, add_zero] using hyC
    · exact cross a c z ha hc
    · exact (cross c a z hc ha).symm
    · rcases (vertical a z).mp ha with ⟨hxA, hA0, hA1⟩
      rcases (vertical c z).mp hc with ⟨hxC, hC0, hC1⟩
      have hre : a.re = c.re := by exact_mod_cast hxA.symm.trans hxC
      have him : a.im ≠ c.im := by
        intro h
        have heq : a = c := Zsqrtd.ext hre h
        exact hne (by rw [heq])
      rcases integer_interval a.im c.im z.2 hA0 hA1 hC0 hC1 him with ⟨hA, hC⟩
      constructor
      · rcases hA with h | h
        · left; exact Prod.ext hxA h
        · right
          apply Prod.ext
          · simpa only [GaussianRealPoint, Zsqrtd.re_add, Int.cast_add,
              Int.cast_zero, add_zero] using hxA
          · simpa only [GaussianRealPoint, Zsqrtd.im_add, Int.cast_add, Int.cast_one] using h
      · rcases hC with h | h
        · left; exact Prod.ext hxC h
        · right
          apply Prod.ext
          · simpa only [GaussianRealPoint, Zsqrtd.re_add, Int.cast_add,
              Int.cast_zero, add_zero] using hxC
          · simpa only [GaussianRealPoint, Zsqrtd.im_add, Int.cast_add, Int.cast_one] using h
  have normalize (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
      ∃ a0 u : GaussianInt, (u = 1 ∨ u = ⟨0, 1⟩) ∧
        ({a, b} : Finset GaussianInt) = {a0, a0 + u} ∧
        segment Real (GaussianRealPoint a) (GaussianRealPoint b) =
          segment Real (GaussianRealPoint a0) (GaussianRealPoint (a0 + u)) := by
    rcases hab with rfl | rfl | rfl | rfl
    · exact ⟨a, 1, Or.inl rfl, rfl, rfl⟩
    · refine ⟨a - 1, 1, Or.inl rfl, ?_, ?_⟩
      · simp [Finset.pair_comm]
      · simpa using segment_symm Real (GaussianRealPoint a) (GaussianRealPoint (a - 1))
    · exact ⟨a, ⟨0, 1⟩, Or.inr rfl, rfl, rfl⟩
    · refine ⟨a - ⟨0, 1⟩, ⟨0, 1⟩, Or.inr rfl, ?_, ?_⟩
      · simp [Finset.pair_comm]
      · simpa using segment_symm Real (GaussianRealPoint a)
          (GaussianRealPoint (a - ⟨0, 1⟩))
  obtain ⟨a0, u, hu, hpairA, hsegA⟩ := normalize a b hab
  obtain ⟨c0, v, hv, hpairC, hsegC⟩ := normalize c d hcd
  ext z
  constructor
  · rintro ⟨ha, hc⟩
    rw [hsegA] at ha
    rw [hsegC] at hc
    have hne' : ({a0, a0 + u} : Finset GaussianInt) ≠ {c0, c0 + v} := by
      rwa [← hpairA, ← hpairC]
    obtain ⟨hA, hC⟩ := canonical a0 c0 u v hu hv hne' z ha hc
    have endpoints (a b a0 u : GaussianInt)
        (hpair : ({a, b} : Finset GaussianInt) = {a0, a0 + u})
        (h : z = GaussianRealPoint a0 ∨ z = GaussianRealPoint (a0 + u)) :
        z = GaussianRealPoint a ∨ z = GaussianRealPoint b := by
      rcases h with h | h
      · have hm : a0 ∈ ({a, b} : Finset GaussianInt) := by rw [hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hm | hm
        · exact Or.inl (h.trans (congrArg GaussianRealPoint hm))
        · exact Or.inr (h.trans (congrArg GaussianRealPoint hm))
      · have hm : a0 + u ∈ ({a, b} : Finset GaussianInt) := by rw [hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hm | hm
        · exact Or.inl (h.trans (congrArg GaussianRealPoint hm))
        · exact Or.inr (h.trans (congrArg GaussianRealPoint hm))
    exact ⟨endpoints a b a0 u hpairA hA, endpoints c d c0 v hpairC hC⟩
  · rintro ⟨ha, hc⟩
    constructor
    · rcases ha with rfl | rfl
      · exact left_mem_segment Real _ _
      · exact right_mem_segment Real _ _
    · rcases hc with rfl | rfl
      · exact left_mem_segment Real _ _
      · exact right_mem_segment Real _ _

end ApollonianSuperharmonic

end
