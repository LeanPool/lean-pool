/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.FarPairApexCount
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Apex count of ordered pairs with a radius predicate

Formalizes the counting part of Steps Ant and Apex in
`docs/results/refined-constant-gain-2026-10-19.md`. Under no three collinear
points, the ordered witness deficiency `Σ_Φ (2 - α)` of any set `Φ` of ordered
distinct pairs is at most `2 n Q`, where `Q = 3D - n + 1`. Let `R` be a
symmetric irreflexive relation on indices and `G` a radius predicate with
`¬G 0`, such that every apex of an `R`-pair sees it at a radius in `G`, and no
circle of such a radius about an apex carries an `R`-triangle. With the degree
cap three, each apex `z` then sees at most `4/3` ordered `R`-pairs per point
`q` with `G |zq|`. Combining both bounds gives
`6 |Φ_R| ≤ 6 n Q + 4 Σ_z #{q : G |zq|}`. The far-pair case `R a b := s < |ab|`,
`G := (s < ·)` gives `|Φ| ≤ 3 n Q` from the apex and circle hypotheses alone.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- Ordered witness deficiency for any set of ordered distinct pairs. Under no
three collinear points every ordered base pair has at most two equidistant
witnesses, so the deficiency over `Φ` is at most the full off-diagonal
deficiency, and the palette bound on the witness total gives `2 n Q`. -/
theorem sum_two_sub_witnesses_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    {Φ : Finset (Fin n × Fin n)} (hΦ : Φ ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    ∑ ab ∈ Φ, (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  have hWle : ∀ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤ 2 := by
    intro ab hab
    exact_mod_cast indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3
      (Finset.mem_offDiag.mp hab).2.2
  have hdef : ∑ ab ∈ Φ,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hΦ fun ab hab _ ↦ by
      linarith [hWle ab hab]
  have hcard : (((Finset.univ : Finset (Fin n)).offDiag.card : ℕ) : ℝ) =
      (n : ℝ) * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
  have htot : ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) =
        (OrderedPairWitnessTotal p : ℝ) := by
    rw [OrderedPairWitnessTotal, Nat.cast_sum]
  rw [Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin n)).offDiag),
    Finset.sum_const, nsmul_eq_mul, htot, hcard] at hdef
  have hlow := orderedPairWitnessTotal_lower_bound hp
  linarith

/-- A circle about an index that carries a point at radius in `G`, with
`¬G 0`, is not centered at that point. -/
private theorem ne_of_radius_pred {p : Config n} {G : ℝ → Prop} (hG0 : ¬G 0)
    {z q : Fin n} (h : G (dist (p z) (p q))) : z ≠ q := by
  rintro rfl
  rw [dist_self] at h
  exact hG0 h

/-- The distance between distinct indices is an ordered distance value. -/
private theorem dist_mem_orderedDistanceValues_of_ne {p : Config n} {a b : Fin n}
    (h : a ≠ b) : dist (p a) (p b) ∈ OrderedDistanceValues p := by
  rw [OrderedDistanceValues, Finset.mem_image]
  exact ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩

/-- Per-apex count with a radius predicate. Let `R` be a symmetric irreflexive
relation such that every apex `z` of an `R`-pair sees it at a radius in `G`,
and no circle about `z` of such a radius carries an `R`-triangle. With the
degree cap three, three times the number of ordered `R`-pairs equidistant from
`z` is at most four times the number of points `q` with `G |zq|`. -/
theorem three_mul_apexPairs_card_le {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a)
    (G : ℝ → Prop) [DecidablePred G] (hG0 : ¬G 0)
    (hrad : ∀ z a b, R a b → dist (p z) (p a) = dist (p z) (p b) → G (dist (p z) (p a)))
    (htri : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → G (dist (p z) (p a)) →
      R a b → R b c → R a c → False)
    (z : Fin n) :
    3 * ((Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2 ∧ dist (p z) (p ab.1) = dist (p z) (p ab.2))).card ≤
      4 * ((Finset.univ : Finset (Fin n)).filter (fun q ↦ G (dist (p z) (p q)))).card := by
  set A := (Finset.univ : Finset (Fin n)).offDiag.filter
    (fun ab ↦ R ab.1 ab.2 ∧ dist (p z) (p ab.1) = dist (p z) (p ab.2)) with hA
  set T := (Finset.univ : Finset (Fin n)).filter (fun q ↦ G (dist (p z) (p q))) with hT
  have hmemT : ∀ q, q ∈ T ↔ G (dist (p z) (p q)) := by
    intro q
    rw [hT, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hmemA : ∀ ab ∈ A, ab.1 ∈ T ∧ ab.2 ∈ T ∧ R ab.1 ab.2 ∧
      dist (p z) (p ab.1) = dist (p z) (p ab.2) := by
    intro ab hab
    rw [hA, Finset.mem_filter] at hab
    obtain ⟨_, hR, heq⟩ := hab
    have hza : G (dist (p z) (p ab.1)) := hrad z ab.1 ab.2 hR heq
    exact ⟨(hmemT _).mpr hza, (hmemT _).mpr (heq ▸ hza), hR, heq⟩
  have hmapsA : ∀ ab ∈ A, dist (p z) (p ab.1) ∈ OrderedDistanceValues p := fun ab hab ↦
    dist_mem_orderedDistanceValues_of_ne
      (ne_of_radius_pred hG0 ((hmemT _).mp (hmemA ab hab).1))
  have hmapsT : ∀ q ∈ T, dist (p z) (p q) ∈ OrderedDistanceValues p := fun q hq ↦
    dist_mem_orderedDistanceValues_of_ne (ne_of_radius_pred hG0 ((hmemT _).mp hq))
  rw [Finset.card_eq_sum_card_fiberwise hmapsA, Finset.card_eq_sum_card_fiberwise hmapsT,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  set U := T.filter (fun q ↦ dist (p z) (p q) = r) with hU
  have hmemU : ∀ q, q ∈ U ↔ G (dist (p z) (p q)) ∧ dist (p z) (p q) = r := by
    intro q
    rw [hU, Finset.mem_filter, hmemT]
  calc 3 * (A.filter (fun ab ↦ dist (p z) (p ab.1) = r)).card
      ≤ 3 * ((U ×ˢ U).filter (fun ab ↦ R ab.1 ab.2)).card := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro ab hab
        rw [Finset.mem_filter] at hab
        obtain ⟨h1, h2, hR, heq⟩ := hmemA ab hab.1
        rw [Finset.mem_filter, Finset.mem_product, hmemU, hmemU]
        exact ⟨⟨⟨(hmemT _).mp h1, hab.2⟩, (hmemT _).mp h2, heq ▸ hab.2⟩, hR⟩
    _ ≤ 4 * U.card := by
        apply three_mul_card_filter_product_le_of_triangleFree U R hirr hsymm
        · refine (Finset.card_le_card ?_).trans (hcap z r)
          intro q hq
          rw [hmemU] at hq
          rw [DistanceOutNeighborsAtValue, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ne_of_radius_pred hG0 hq.1, hq.2⟩
        · intro a ha b hb c hc hab hbc hac
          rw [hmemU] at ha hb hc
          exact htri z a b c (ha.2.trans hb.2.symm) (ha.2.trans hc.2.symm) ha.1 hab hbc hac

/-- Swapping the witness and base-pair coordinates of the witness count of a
set of ordered pairs. -/
private theorem sum_witness_card_eq_sum_apex_card (p : Config n)
    (Φ : Finset (Fin n × Fin n)) :
    ∑ ab ∈ Φ, (IndexedEquidistantWitnesses p ab.1 ab.2).card =
      ∑ z, (Φ.filter (fun ab ↦ dist (p z) (p ab.1) = dist (p z) (p ab.2))).card := by
  simp only [IndexedEquidistantWitnesses, Finset.card_filter]
  exact Finset.sum_comm

/-- Total apex count with a radius predicate. Under the hypotheses of
`three_mul_apexPairs_card_le`, no three collinear points, and the degree cap
three, the ordered `R`-pairs satisfy
`6 |Φ_R| ≤ 6 n Q + 4 Σ_z #{q : G |zq|}`, where `Q = 3D - n + 1`. -/
theorem six_mul_card_pairs_le_of_apex {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a)
    (G : ℝ → Prop) [DecidablePred G] (hG0 : ¬G 0)
    (hrad : ∀ z a b, R a b → dist (p z) (p a) = dist (p z) (p b) → G (dist (p z) (p a)))
    (htri : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → G (dist (p z) (p a)) →
      R a b → R b c → R a c → False) :
    6 * ((((Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2)).card : ℝ)) ≤
      6 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ G (dist (p z) (p q)))).card : ℝ) := by
  have hsub : (Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2) ⊆
      (Finset.univ : Finset (Fin n)).offDiag :=
    Finset.filter_subset _ _
  have hdef := sum_two_sub_witnesses_le hp hgp3 hsub
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hdef
  have hnat : 3 * ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2), (IndexedEquidistantWitnesses p ab.1 ab.2).card ≤
      4 * ∑ z, ((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ G (dist (p z) (p q)))).card := by
    rw [sum_witness_card_eq_sum_apex_card, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ ↦ ?_
    rw [Finset.filter_filter]
    exact three_mul_apexPairs_card_le hcap R hirr hsymm G hG0 hrad htri z
  have hreal : 3 * ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2), ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤
      4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ G (dist (p z) (p q)))).card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Far-pair apex count from apex and circle hypotheses. If every apex of a
pair farther than `s` is farther than `s` from its ends, and no circle of
radius greater than `s` about an index carries three points pairwise farther
than `s`, then under no three collinear points and the degree cap three the
number of ordered pairs farther than `s` is at most `3 n Q`, where
`Q = 3D - n + 1`. -/
theorem farOrderedPairs_card_le_of_apex {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {s : ℝ} (hs : 0 ≤ s)
    (hapex : ∀ z a b, s < dist (p a) (p b) → dist (p z) (p a) = dist (p z) (p b) →
      s < dist (p z) (p a))
    (hcirc : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → s < dist (p z) (p a) →
      s < dist (p a) (p b) → s < dist (p b) (p c) → s < dist (p a) (p c) → False) :
    ((FarOrderedPairs p s).card : ℝ) ≤
      3 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  have hirr : ∀ a : Fin n, ¬s < dist (p a) (p a) := by
    intro a
    rw [dist_self]
    exact not_lt.mpr hs
  have hsymm : ∀ a b : Fin n, s < dist (p a) (p b) → s < dist (p b) (p a) := by
    intro a b h
    rwa [dist_comm]
  have h : 6 * ((FarOrderedPairs p s).card : ℝ) ≤
      6 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ s < dist (p z) (p q))).card : ℝ) :=
    six_mul_card_pairs_le_of_apex hp hgp3 hcap (fun a b ↦ s < dist (p a) (p b)) hirr hsymm
      (fun r ↦ s < r) (not_lt.mpr hs) hapex hcirc
  have hrow : ∑ z, (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ s < dist (p z) (p q))).card : ℝ) = ((FarOrderedPairs p s).card : ℝ) := by
    rw [farOrderedPairs_card_eq_sum hs, Nat.cast_sum]
  rw [hrow] at h
  linarith

end Esgk
