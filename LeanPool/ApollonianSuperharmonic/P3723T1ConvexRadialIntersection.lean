/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# P3723T1ConvexRadialIntersection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

-- [TABLET NODE: P3723T1ConvexRadialIntersection]
theorem P3723T1ConvexRadialIntersection
    (K : Set (Real × Real)) (hK : Convex Real K) (hclosed : IsClosed K)
    (x y z : Real × Real) (hx : x ∈ interior K)
    (hy : y ∈ frontier K) (hz : z ∈ frontier K) (hne : y ≠ z) :
    segment Real x y ∩ segment Real x z = {x} := by
-- BODY
  have unique (y z : Real × Real) (hy : y ∈ frontier K) (hz : z ∈ frontier K)
      (a b : Real) (ha : 0 < a) (hb : 0 < b)
      (heq : (1 - a) • x + a • y = (1 - b) • x + b • z) : y = z := by
    have boundary_not_interior : ∀ q ∈ frontier K, q ∉ interior K := by
      intro q hq
      exact hq.2
    have no_lt : ∀ (u v : Real × Real) (s t : Real),
        u ∈ frontier K → v ∈ frontier K → 0 < s → 0 < t →
        (1 - s) • x + s • u = (1 - t) • x + t • v → ¬ s < t := by
      intro u v s t hu hv hs ht huv hlt
      have ht0 : t ≠ 0 := ne_of_gt ht
      have hvblend : v = (1 - s / t) • x + (s / t) • u := by
        have he1 := congrArg Prod.fst huv
        have he2 := congrArg Prod.snd huv
        dsimp at he1 he2
        apply Prod.ext <;> dsimp <;> field_simp <;> nlinarith
      have hr0 : 0 ≤ s / t := le_of_lt (div_pos hs ht)
      have hr1 : s / t < 1 := (div_lt_one ht).mpr hlt
      have hvI : v ∈ interior K := by
        rw [hvblend]
        exact hK.combo_interior_self_mem_interior hx
          (hclosed.frontier_subset hu) (sub_pos.mpr hr1) hr0 (by ring)
      exact boundary_not_interior v hv hvI
    have hab : a = b := le_antisymm
      (le_of_not_gt (no_lt z y b a hz hy hb ha heq.symm))
      (le_of_not_gt (no_lt y z a b hy hz ha hb heq))
    subst b
    have he : a • y = a • z := add_left_cancel heq
    exact (smul_right_injective _ (ne_of_gt ha)) he
  ext q
  constructor
  · rintro ⟨hqy, hqz⟩
    rw [segment_eq_image] at hqy hqz
    obtain ⟨a, ha, hqa⟩ := hqy
    obtain ⟨b, hb, hqb⟩ := hqz
    by_cases hqx : q = x
    · exact hqx
    · have ha0 : a ≠ 0 := by
        intro h
        subst a
        simp only [sub_zero, one_smul, zero_smul, add_zero] at hqa
        exact hqx hqa.symm
      have hb0 : b ≠ 0 := by
        intro h
        subst b
        simp only [sub_zero, one_smul, zero_smul, add_zero] at hqb
        exact hqx hqb.symm
      exact False.elim (hne (unique y z hy hz a b (lt_of_le_of_ne ha.1 ha0.symm)
          (lt_of_le_of_ne hb.1 hb0.symm) (hqa.trans hqb.symm)))
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq]
    exact ⟨left_mem_segment Real x y, left_mem_segment Real x z⟩

end ApollonianSuperharmonic

end
