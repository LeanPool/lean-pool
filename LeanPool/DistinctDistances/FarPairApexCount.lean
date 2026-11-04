/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.EntropyCensus
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Apex deficiency of far pairs

Formalizes the apex count of the Lean route in
`docs/results/explicit-constant-gain-2026-10-18.md`. Let `s ≥ 0` be a distance
threshold such that no distance lies in `(s, 2s]` and no four points are
pairwise farther than `s`. Under no three collinear points and the degree cap
three, the number of ordered pairs farther than `s` is at most `3 n Q`, where
`Q = 3D - n + 1`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- Ordered pairs of distinct indices at distance greater than `s`. -/
noncomputable def FarOrderedPairs (p : Config n) (s : ℝ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ s < dist (p ab.1) (p ab.2))

/-- One non-edge `{u, v}` of a symmetric relation removes both of its
orientations from the ordered off-diagonal pairs of `S`. -/
private theorem card_filter_product_add_two_le_of_nonEdge {α : Type*}
    (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) {u v : α} (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) (hR : ¬R u v)
    (hoff : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆ S.offDiag) :
    ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card + 2 ≤ S.offDiag.card := by
  classical
  have hmem1 : (u, v) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩
  have hmem2 : (v, u) ∈ S.offDiag.erase (u, v) := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_offDiag.mpr ⟨hv, hu, huv.symm⟩⟩
    intro h
    exact huv (Prod.mk.inj h).2
  have hsub : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆
      (S.offDiag.erase (u, v)).erase (v, u) := by
    intro ab hab
    have hR' : R ab.1 ab.2 := (Finset.mem_filter.mp hab).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hoff hab⟩⟩
    · rintro rfl
      exact hR (hsymm _ _ hR')
    · rintro rfl
      exact hR hR'
  have h1 := Finset.card_erase_add_one hmem1
  have h2 := Finset.card_erase_add_one hmem2
  have h3 := Finset.card_le_card hsub
  omega

/-- A triangle-free symmetric irreflexive relation on at most three elements
has at most four ordered edges per three elements. -/
theorem three_mul_card_filter_product_le_of_triangleFree {α : Type*}
    (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a) (hS : S.card ≤ 3)
    (htri : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c → False) :
    3 * ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card ≤ 4 * S.card := by
  classical
  have hoff : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆ S.offDiag := by
    intro ab hab
    rw [Finset.mem_filter, Finset.mem_product] at hab
    refine Finset.mem_offDiag.mpr ⟨hab.1.1, hab.1.2, fun h ↦ hirr ab.2 ?_⟩
    have hR := hab.2
    rwa [h] at hR
  have hle := Finset.card_le_card hoff
  rw [Finset.offDiag_card] at hle
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h | h | h | h
  · rw [h] at hle ⊢
    omega
  · rw [h] at hle ⊢
    omega
  · rw [h] at hle ⊢
    omega
  · obtain ⟨a, b, c, hab, hac, hbc, hSabc⟩ := Finset.card_eq_three.mp h
    have ha : a ∈ S := by rw [hSabc]; simp
    have hb : b ∈ S := by rw [hSabc]; simp
    have hc : c ∈ S := by rw [hSabc]; simp
    have hkey : ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card + 2 ≤ S.offDiag.card := by
      by_cases h1 : R a b
      · by_cases h2 : R b c
        · by_cases h3 : R a c
          · exact (htri a ha b hb c hc h1 h2 h3).elim
          · exact card_filter_product_add_two_le_of_nonEdge S R hsymm ha hc hac h3 hoff
        · exact card_filter_product_add_two_le_of_nonEdge S R hsymm hb hc hbc h2 hoff
      · exact card_filter_product_add_two_le_of_nonEdge S R hsymm ha hb hab h1 hoff
    rw [Finset.offDiag_card, h] at hkey
    rw [h]
    omega

/-- The falling product of a natural number dominates the linear bound
`4 d - 6`, because `(d - 2) (d - 3) ≥ 0` on the integers. -/
private theorem four_mul_sub_six_le_falling (d : ℕ) :
    4 * (d : ℝ) - 6 ≤ ((d * (d - 1) : ℕ) : ℝ) := by
  have h : 4 * d ≤ d * (d - 1) + 6 := by
    rcases Nat.lt_or_ge d 3 with hd | hd
    · interval_cases d <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
      have hk : (3 + k) * (3 + k - 1) = k * k + 5 * k + 6 := by
        rw [show 3 + k - 1 = k + 2 by omega]
        ring
      omega
  have h' : ((4 * d : ℕ) : ℝ) ≤ ((d * (d - 1) + 6 : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_add] at h'
  push_cast at h' ⊢
  linarith

/-- The palette size bounds the ordered witness total from below:
`d (d - 1) ≥ 4 d - 6` for every local distance degree `d`. -/
theorem orderedPairWitnessTotal_lower_bound {p : Config n} (hp : Function.Injective p) :
    (n : ℝ) * (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)) ≤
      (OrderedPairWitnessTotal p : ℝ) := by
  rw [← distanceDegreeFallingMass_eq_orderedPairWitnessTotal hp, DistanceDegreeFallingMass,
    Finset.sum_comm]
  have hrow : ∀ x : Fin n, 4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ) ≤
      ((∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1) : ℕ) : ℝ) := by
    intro x
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Fin.pos x).ne'
    have hsum : ((∑ r ∈ OrderedDistanceValues p,
        (DistanceOutNeighborsAtValue p x r).card : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [distanceDegreeProfile_sum_eq_pred p x, Nat.cast_sub hn, Nat.cast_one]
    rw [Nat.cast_sum] at hsum ⊢
    calc 4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)
        = ∑ r ∈ OrderedDistanceValues p,
            (4 * ((DistanceOutNeighborsAtValue p x r).card : ℝ) - 6) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
            NumDistancesOrdered, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun r _ ↦ four_mul_sub_six_le_falling _
  calc (n : ℝ) * (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ))
      = ∑ _x : Fin n, (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ x : Fin n, ((∑ r ∈ OrderedDistanceValues p,
          (DistanceOutNeighborsAtValue p x r).card *
            ((DistanceOutNeighborsAtValue p x r).card - 1) : ℕ) : ℝ) :=
        Finset.sum_le_sum fun x _ ↦ hrow x
    _ = _ := by rw [Nat.cast_sum]

/-- A distance above a nonnegative threshold separates distinct indices. -/
private theorem ne_of_lt_dist {p : Config n} {s : ℝ} (hs : 0 ≤ s) {a b : Fin n}
    (h : s < dist (p a) (p b)) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  linarith

/-- The distance between distinct indices is an ordered distance value. -/
private theorem dist_mem_orderedDistanceValues {p : Config n} {a b : Fin n} (h : a ≠ b) :
    dist (p a) (p b) ∈ OrderedDistanceValues p := by
  rw [OrderedDistanceValues, Finset.mem_image]
  exact ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩

/-- The far ordered pairs are counted row by row. -/
theorem farOrderedPairs_card_eq_sum {p : Config n} {s : ℝ} (hs : 0 ≤ s) :
    (FarOrderedPairs p s).card =
      ∑ a, ((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ s < dist (p a) (p q))).card := by
  have heq : FarOrderedPairs p s = (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ab ↦ s < dist (p ab.1) (p ab.2)) := by
    ext ab
    simp only [FarOrderedPairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_lt_dist hs h, h⟩⟩
  rw [heq, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

/-- Swapping the witness and base-pair coordinates of the far-pair witness
count. -/
private theorem sum_farOrderedPairs_witness_card_eq {p : Config n} {s : ℝ} :
    ∑ ab ∈ FarOrderedPairs p s, (IndexedEquidistantWitnesses p ab.1 ab.2).card =
      ∑ x, ((FarOrderedPairs p s).filter
        (fun ab ↦ dist (p x) (p ab.1) = dist (p x) (p ab.2))).card := by
  simp only [IndexedEquidistantWitnesses, Finset.card_filter]
  exact Finset.sum_comm

/-- At a fixed apex `x`, three times the number of far ordered pairs
equidistant from `x` is at most four times the number of points far from `x`.
The circle of each radius about `x` carries at most three points, and these
contain no far triangle. -/
private theorem three_mul_apexFarPairs_card_le {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {s : ℝ} (hs : 0 ≤ s)
    (hgap : ∀ a b, dist (p a) (p b) ≤ 2 * s → dist (p a) (p b) ≤ s)
    (hfour : ∀ a b c d : Fin n,
      s < dist (p a) (p b) → s < dist (p a) (p c) → s < dist (p a) (p d) →
      s < dist (p b) (p c) → s < dist (p b) (p d) → s < dist (p c) (p d) → False)
    (x : Fin n) :
    3 * ((FarOrderedPairs p s).filter
        (fun ab ↦ dist (p x) (p ab.1) = dist (p x) (p ab.2))).card ≤
      4 * ((Finset.univ : Finset (Fin n)).filter (fun q ↦ s < dist (p x) (p q))).card := by
  set A := (FarOrderedPairs p s).filter
    (fun ab ↦ dist (p x) (p ab.1) = dist (p x) (p ab.2)) with hA
  set T := (Finset.univ : Finset (Fin n)).filter (fun q ↦ s < dist (p x) (p q)) with hT
  have hmemT : ∀ q, q ∈ T ↔ s < dist (p x) (p q) := by
    intro q
    rw [hT, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hmemA : ∀ ab ∈ A, ab.1 ∈ T ∧ ab.2 ∈ T ∧ s < dist (p ab.1) (p ab.2) ∧
      dist (p x) (p ab.1) = dist (p x) (p ab.2) := by
    intro ab hab
    rw [hA, Finset.mem_filter, FarOrderedPairs, Finset.mem_filter] at hab
    obtain ⟨⟨_, hfar⟩, heq⟩ := hab
    have hxa : s < dist (p x) (p ab.1) := by
      by_contra hle
      rw [not_lt] at hle
      have h2 : dist (p ab.1) (p ab.2) ≤ 2 * s := by
        calc dist (p ab.1) (p ab.2) ≤ dist (p ab.1) (p x) + dist (p x) (p ab.2) :=
              dist_triangle _ _ _
          _ = dist (p x) (p ab.1) + dist (p x) (p ab.1) := by rw [dist_comm, heq]
          _ ≤ 2 * s := by linarith
      linarith [hgap _ _ h2]
    exact ⟨(hmemT _).mpr hxa, (hmemT _).mpr (heq ▸ hxa), hfar, heq⟩
  have hmapsA : ∀ ab ∈ A, dist (p x) (p ab.1) ∈ OrderedDistanceValues p := fun ab hab ↦
    dist_mem_orderedDistanceValues (ne_of_lt_dist hs ((hmemT _).mp (hmemA ab hab).1))
  have hmapsT : ∀ q ∈ T, dist (p x) (p q) ∈ OrderedDistanceValues p := fun q hq ↦
    dist_mem_orderedDistanceValues (ne_of_lt_dist hs ((hmemT _).mp hq))
  rw [Finset.card_eq_sum_card_fiberwise hmapsA, Finset.card_eq_sum_card_fiberwise hmapsT,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  set U := T.filter (fun q ↦ dist (p x) (p q) = r) with hU
  have hmemU : ∀ q, q ∈ U ↔ s < dist (p x) (p q) ∧ dist (p x) (p q) = r := by
    intro q
    rw [hU, Finset.mem_filter, hmemT]
  calc 3 * (A.filter (fun ab ↦ dist (p x) (p ab.1) = r)).card
      ≤ 3 * ((U ×ˢ U).filter (fun ab ↦ s < dist (p ab.1) (p ab.2))).card := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro ab hab
        rw [Finset.mem_filter] at hab
        obtain ⟨h1, h2, hfar, heq⟩ := hmemA ab hab.1
        rw [Finset.mem_filter, Finset.mem_product, hmemU, hmemU]
        exact ⟨⟨⟨(hmemT _).mp h1, hab.2⟩, (hmemT _).mp h2, heq ▸ hab.2⟩, hfar⟩
    _ ≤ 4 * U.card := by
        apply three_mul_card_filter_product_le_of_triangleFree U
          (fun a b ↦ s < dist (p a) (p b))
        · intro a
          rw [dist_self]
          exact not_lt.mpr hs
        · intro a b h
          rwa [dist_comm]
        · refine (Finset.card_le_card ?_).trans (hcap x r)
          intro q hq
          rw [hmemU] at hq
          rw [DistanceOutNeighborsAtValue, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ne_of_lt_dist hs hq.1, hq.2⟩
        · intro a ha b hb c hc hab hbc hac
          rw [hmemU] at ha hb hc
          exact hfour x a b c ha.1 hb.1 hc.1 hab hac hbc

/-- Far-pair apex count. A far pair has no apex within distance `s` of its
ends, so the at most three points on a circle about an apex contain no far
triangle; hence each apex sees at most `4/3` far pairs per far point. -/
theorem farOrderedPairs_card_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {s : ℝ} (hs : 0 ≤ s)
    (hgap : ∀ a b, dist (p a) (p b) ≤ 2 * s → dist (p a) (p b) ≤ s)
    (hfour : ∀ a b c d : Fin n,
      s < dist (p a) (p b) → s < dist (p a) (p c) → s < dist (p a) (p d) →
      s < dist (p b) (p c) → s < dist (p b) (p d) → s < dist (p c) (p d) → False) :
    ((FarOrderedPairs p s).card : ℝ) ≤
      3 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  have hsub : FarOrderedPairs p s ⊆ (Finset.univ : Finset (Fin n)).offDiag :=
    Finset.filter_subset _ _
  have hWle : ∀ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤ 2 := by
    intro ab hab
    exact_mod_cast indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3
      (Finset.mem_offDiag.mp hab).2.2
  have hdef : ∑ ab ∈ FarOrderedPairs p s,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ab hab _ ↦ by
      linarith [hWle ab hab]
  have hcard : (((Finset.univ : Finset (Fin n)).offDiag.card : ℕ) : ℝ) =
      (n : ℝ) * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
  have htot : ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) =
        (OrderedPairWitnessTotal p : ℝ) := by
    rw [OrderedPairWitnessTotal, Nat.cast_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, htot, hcard] at hdef
  have hlow := orderedPairWitnessTotal_lower_bound hp
  have hnat : 3 * ∑ ab ∈ FarOrderedPairs p s, (IndexedEquidistantWitnesses p ab.1 ab.2).card ≤
      4 * (FarOrderedPairs p s).card := by
    rw [sum_farOrderedPairs_witness_card_eq, Finset.mul_sum, farOrderedPairs_card_eq_sum hs,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ ↦ three_mul_apexFarPairs_card_le hcap hs hgap hfour x
  have hreal : 3 * ∑ ab ∈ FarOrderedPairs p s,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤
        4 * ((FarOrderedPairs p s).card : ℝ) := by
    exact_mod_cast hnat
  linarith

end Esgk
