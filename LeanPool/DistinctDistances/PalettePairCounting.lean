/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ClosePairRowStability
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Close pairs on the circles about each point

Formalizes Lemma P of `docs/results/explicit-constant-gain-1-85-2026-10-20.md`
(§5.2), with the row bounds (B1) that it uses. Thresholds are squared distances
throughout. For a squared threshold `t ≥ 0`, `N_j(t)` counts the points `q` with
`|p_j p_q|² ≤ t`, including `j` itself; `R(u)` counts the palette values `r` with
`r² ≤ u`; and `Q = 3D - n + 1` is the degree deficit at every vertex.

For each apex `i`, count the ordered pairs of distinct points within squared
distance `t` on the circles about `i` over the palette. Under no three collinear
points an ordered pair has at most two apexes, so the total over all apexes is at
most twice the number of ordered close pairs, that is `2 Σ_j (N_j(t) - 1)`.

Let `S` be a set of palette values such that every saturated circle with radius
in `S` carries two distinct points within squared distance `t`, and let `K` be the
size of `S ∪ {r : r² ≤ t/4}`. A circle of squared radius at most `t/4` has all
its pairs close; a saturated circle with radius in `S` has a close pair; and the
deficits at one apex sum to `Q`. Counting per apex gives

* `Σ_j (N_j(t) - 1) ≥ n (K - Q)`, and
* `Σ_j (N_j(t) - 1) ≥ n (K + 2 R(t/4) - 2 Q)`.

The row bounds `3 R(t) - Q ≤ N_j(t) - 1 ≤ 3 R(t)` then give the same two lower
bounds for `3 R(t)`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- The closed ball of squared radius `t ≥ 0` about a point is that point together
with its close-pair row. -/
theorem closedBall_sq_card_eq_closePairRow_card_add_one (p : Config n) {t : ℝ}
    (ht : 0 ≤ t) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card =
      (ClosePairRow p j t).card + 1 := by
  classical
  have h : (Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t) =
      insert j (ClosePairRow p j t) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, ClosePairRow]
    constructor
    · intro hq
      by_cases hqj : q = j
      · exact Or.inl hqj
      · exact Or.inr ⟨Ne.symm hqj, hq⟩
    · rintro (rfl | ⟨_, hq⟩)
      · rw [dist_self]
        simpa using ht
      · exact hq
  rw [h, Finset.card_insert_of_notMem (by simp [ClosePairRow])]

/-- Row bound (B1), upper side. With the degree cap three, the closed ball of
squared radius `t ≥ 0` about a point holds at most `3 R(t)` points other than the
point, where `R(t)` counts the palette values `r` with `r² ≤ t`. -/
theorem closedBall_sq_card_sub_one_le_three_mul_palette {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    (j : Fin n) :
    (((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) -
        1 ≤
      3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) := by
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t) with hRT
  have hrow : ((ClosePairRow p j t).card : ℝ) ≤ 3 * (RT.card : ℝ) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    calc ∑ r ∈ RT, ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤
          ∑ _r ∈ RT, (3 : ℝ) :=
          Finset.sum_le_sum (fun r _ ↦ by exact_mod_cast hcap j r)
      _ = 3 * (RT.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hball : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) = ((ClosePairRow p j t).card : ℝ) + 1 := by
    rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one]
  linarith

/-- Row bound (B1), lower side. With the degree cap three, the closed ball of
squared radius `t ≥ 0` about a point holds at least `3 R(t) - Q` points other than
the point, where `R(t)` counts the palette values `r` with `r² ≤ t` and
`Q = 3D - n + 1`. -/
theorem three_mul_palette_sub_le_closedBall_sq_card_sub_one {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    (j : Fin n) :
    3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      (((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) -
        1 := by
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t) with hRT
  have hdef : ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) ≤
      3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
    rw [← sum_distanceDegreeDeficit p hn j]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r _ _
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    linarith
  have hrow : ((ClosePairRow p j t).card : ℝ) = 3 * (RT.card : ℝ) -
      ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hball : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) = ((ClosePairRow p j t).card : ℝ) + 1 := by
    rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one]
  linarith

/-- For `t ≥ 0`, the ordered close pairs are counted by the closed balls about the
points, each without its center. -/
lemma orderedClosePairs_card_eq_sum_closedBall_sq (p : Config n) {t : ℝ}
    (ht : 0 ≤ t) :
    ((OrderedClosePairs p t).card : ℝ) =
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  rw [orderedClosePairs_card_eq_sum_row, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]

/-- At one apex `i`, the ordered close pairs on the circles about `i` over the
palette are ordered close pairs with `i` as an equidistant witness; the circles
for distinct radii are disjoint. -/
lemma sum_circle_closePairs_le_apex (p : Config n) (t : ℝ) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card ≤
      ((OrderedClosePairs p t).filter
        (fun ab ↦ dist (p i) (p ab.1) = dist (p i) (p ab.2))).card := by
  classical
  set X := (OrderedClosePairs p t).filter
    (fun ab ↦ i ≠ ab.1 ∧ dist (p i) (p ab.1) = dist (p i) (p ab.2)) with hX
  have hmaps : ∀ ab ∈ X, dist (p i) (p ab.1) ∈ OrderedDistanceValues p := by
    intro ab hab
    have h := (Finset.mem_filter.mp hab).2.1
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(i, ab.1), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩
  have hXle : X.card ≤ ((OrderedClosePairs p t).filter
      (fun ab ↦ dist (p i) (p ab.1) = dist (p i) (p ab.2))).card := by
    apply Finset.card_le_card
    intro ab hab
    obtain ⟨h1, -, h2⟩ := Finset.mem_filter.mp hab
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  refine le_trans ?_ hXle
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro r _
  apply Finset.card_le_card
  intro ab hab
  obtain ⟨hab, hclose⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨-, hia, hda⟩ := Finset.mem_filter.mp ha
  obtain ⟨-, -, hdb⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hia, hda.trans hdb.symm⟩, hda⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩, hclose⟩

/-- Upper bound for the circle pair count. Under no three collinear points, every
ordered close pair has at most two equidistant witnesses, so the ordered close
pairs on the circles about all apexes number at most twice the ordered close
pairs. -/
lemma sum_sum_circle_closePairs_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (t : ℝ) :
    ∑ i, ∑ r ∈ OrderedDistanceValues p,
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) ≤
      2 * ((OrderedClosePairs p t).card : ℝ) := by
  classical
  have hswap : ∑ i, ((OrderedClosePairs p t).filter
        (fun ab ↦ dist (p i) (p ab.1) = dist (p i) (p ab.2))).card =
      ∑ ab ∈ OrderedClosePairs p t, (IndexedEquidistantWitnesses p ab.1 ab.2).card := by
    simp only [IndexedEquidistantWitnesses, Finset.card_filter]
    exact Finset.sum_comm
  have hnat : ∑ i, ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card ≤
      2 * (OrderedClosePairs p t).card := by
    calc ∑ i, ∑ r ∈ OrderedDistanceValues p,
          ((DistanceOutNeighborsAtValue p i r).offDiag.filter
            (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card ≤
        ∑ i, ((OrderedClosePairs p t).filter
          (fun ab ↦ dist (p i) (p ab.1) = dist (p i) (p ab.2))).card :=
          Finset.sum_le_sum fun i _ ↦ sum_circle_closePairs_le_apex p t i
      _ = ∑ ab ∈ OrderedClosePairs p t, (IndexedEquidistantWitnesses p ab.1 ab.2).card := hswap
      _ ≤ ∑ _ab ∈ OrderedClosePairs p t, 2 :=
          Finset.sum_le_sum fun ab hab ↦ indexedEquidistantWitnesses_card_le_two_of_nonTrilinear
            hp hgp3 (Finset.mem_offDiag.mp (Finset.mem_filter.mp hab).1).2.2
      _ = 2 * (OrderedClosePairs p t).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  exact_mod_cast hnat

/-- On a circle of squared radius at most `t/4` about a point, every two points are
within squared distance `t`. -/
lemma circle_offDiag_filter_eq_of_sq_le {p : Config n} {t r : ℝ}
    (hr : r ^ 2 ≤ t / 4) (i : Fin n) :
    (DistanceOutNeighborsAtValue p i r).offDiag.filter
        (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t) =
      (DistanceOutNeighborsAtValue p i r).offDiag := by
  apply Finset.filter_true_of_mem
  intro ab hab
  obtain ⟨ha, hb, -⟩ := Finset.mem_offDiag.mp hab
  have hda := (Finset.mem_filter.mp ha).2.2
  have hdb := (Finset.mem_filter.mp hb).2.2
  have htri := dist_triangle (p ab.1) (p i) (p ab.2)
  rw [dist_comm (p ab.1) (p i), hda, hdb] at htri
  have h0 := dist_nonneg (x := p ab.1) (y := p ab.2)
  nlinarith [pow_le_pow_left₀ h0 htri 2]

/-- Lower bounds for the circle pair count at one apex, radius by radius. Let `S`
be a set of palette values whose saturated circles carry two distinct points within
squared distance `t`, and `L` the palette values `r` with `r² ≤ t/4`. Summed over
the palette against the deficit `Q`, the close pairs on the circles about one apex
number at least `2 (K - Q)` and at least `2 (K + 2 |L| - 2 Q)`, `K = |S ∪ L|`. -/
private lemma sum_circle_closePairs_lower_bound {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t : ℝ}
    {S : Finset ℝ} (hSsub : S ⊆ OrderedDistanceValues p)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ∈ S → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t)
    (i : Fin n) :
    2 * (((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) ≤
      ∑ r ∈ OrderedDistanceValues p,
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) ∧
    2 * (((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) +
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        2 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) ≤
      ∑ r ∈ OrderedDistanceValues p,
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) := by
  classical
  set V := OrderedDistanceValues p with hV
  set L := V.filter (fun r ↦ r ^ 2 ≤ t / 4) with hL
  have hLsub : L ⊆ V := Finset.filter_subset _ _
  have hSLsub : S ∪ L ⊆ V := Finset.union_subset hSsub hLsub
  have key : ∀ r ∈ V,
      2 * (if r ∈ S ∪ L then (1 : ℝ) else 0) -
          2 * (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) ≤
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) ∧
      2 * (if r ∈ S ∪ L then (1 : ℝ) else 0) + 4 * (if r ∈ L then (1 : ℝ) else 0) -
          4 * (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) ≤
        (((DistanceOutNeighborsAtValue p i r).offDiag.filter
          (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) := by
    intro r hr
    have hd3 := hcap i r
    have hc0 : (0 : ℝ) ≤ (((DistanceOutNeighborsAtValue p i r).offDiag.filter
        (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) := Nat.cast_nonneg _
    by_cases hrL : r ∈ L
    · rw [ite_eq_left (Finset.mem_union_right _ hrL), ite_eq_left hrL,
        circle_offDiag_filter_eq_of_sq_le (Finset.mem_filter.mp hrL).2 i, Finset.offDiag_card]
      generalize (DistanceOutNeighborsAtValue p i r).card = d at hd3 ⊢
      interval_cases d <;> norm_num
    · rw [ite_eq_right hrL]
      by_cases hrS : r ∈ S
      · rw [ite_eq_left (Finset.mem_union_left _ hrS)]
        by_cases h3 : (DistanceOutNeighborsAtValue p i r).card = 3
        · have hsat : (i, r) ∈ SaturatedDistanceIncidences p :=
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hr⟩, h3⟩
          obtain ⟨a, b, ha, hb, hab, hclose⟩ := hS (i, r) hsat hrS
          have h2 : 1 < ((DistanceOutNeighborsAtValue p i r).offDiag.filter
              (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card := by
            refine Finset.one_lt_card.mpr ⟨(a, b), ?_, (b, a), ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab.ne⟩, hclose⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hb, ha, hab.ne'⟩,
                by simpa [dist_comm] using hclose⟩
            · exact fun h ↦ hab.ne (Prod.ext_iff.mp h).1
          have h2R : (2 : ℝ) ≤ (((DistanceOutNeighborsAtValue p i r).offDiag.filter
              (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)).card : ℝ) := by
            exact_mod_cast h2
          rw [h3]
          push_cast
          constructor <;> linarith
        · have hd2 : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 2 := by
            exact_mod_cast (show (DistanceOutNeighborsAtValue p i r).card ≤ 2 by omega)
          constructor <;> linarith
      · rw [ite_eq_right (by simp [hrL, hrS] : r ∉ S ∪ L)]
        have hd3R : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 := by
          exact_mod_cast hd3
        constructor <;> linarith
  have hind : ∀ X ⊆ V, ∑ r ∈ V, (if r ∈ X then (1 : ℝ) else 0) = (X.card : ℝ) := by
    intro X hX
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hX]
  have hdef := sum_distanceDegreeDeficit p hn i
  rw [← hV] at hdef
  have hSLsum := hind _ hSLsub
  have hLsum := hind _ hLsub
  have h1 := Finset.sum_le_sum fun r hr ↦ (key r hr).1
  have h2 := Finset.sum_le_sum fun r hr ↦ (key r hr).2
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h1 h2 hdef
  constructor <;> linarith

/-- Lemma P, saturated circles. Let `S` be a set of palette values such that every
saturated circle about a point with radius in `S` carries two distinct points within
squared distance `t ≥ 0`, and let `K` be the size of `S ∪ {r : r² ≤ t/4}` in the
palette. Under no three collinear points and the degree cap three,
`Σ_j (N_j(t) - 1) ≥ n (K - Q)`, where `N_j(t)` counts the points within squared
distance `t` of `p_j` (including `j`) and `Q = 3D - n + 1`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_saturated {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) {S : Finset ℝ} (hSsub : S ⊆ OrderedDistanceValues p)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ∈ S → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    (n : ℝ) * (((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  rw [← orderedClosePairs_card_eq_sum_closedBall_sq p ht]
  have hup := sum_sum_circle_closePairs_le hp hgp3 t
  have hlow := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
    (sum_circle_closePairs_lower_bound hn hcap hSsub hS i).1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  linarith

/-- Lemma P, short radii. Let `S` be a set of palette values such that every
saturated circle about a point with radius in `S` carries two distinct points within
squared distance `t ≥ 0`, and let `K` be the size of `S ∪ {r : r² ≤ t/4}` in the
palette. Under no three collinear points and the degree cap three,
`Σ_j (N_j(t) - 1) ≥ n (K + 2 R(t/4) - 2 Q)`, where `N_j(t)` counts the points within
squared distance `t` of `p_j` (including `j`), `R(t/4)` counts the palette values `r`
with `r² ≤ t/4`, and `Q = 3D - n + 1`. -/
theorem sum_closedBall_sq_card_sub_one_lower_bound_short_radii {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) {S : Finset ℝ} (hSsub : S ⊆ OrderedDistanceValues p)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ∈ S → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    (n : ℝ) * (((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) +
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        2 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  rw [← orderedClosePairs_card_eq_sum_closedBall_sq p ht]
  have hup := sum_sum_circle_closePairs_le hp hgp3 t
  have hlow := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
    (sum_circle_closePairs_lower_bound hn hcap hSsub hS i).2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  linarith

/-- The row upper bound, summed over the points: `Σ_j (N_j(t) - 1) ≤ n · 3 R(t)`. -/
private lemma sum_closedBall_sq_card_sub_one_le {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      (n : ℝ) * (3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ)) := by
  have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
    closedBall_sq_card_sub_one_le_three_mul_palette hcap ht j
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

/-- Lemma P for the palette, saturated circles: under the hypotheses of
`sum_closedBall_sq_card_sub_one_lower_bound_saturated`, `3 R(t) ≥ K - Q`. -/
theorem three_mul_palette_lower_bound_saturated {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) {S : Finset ℝ} (hSsub : S ⊆ OrderedDistanceValues p)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ∈ S → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) := by
  have hlow := sum_closedBall_sq_card_sub_one_lower_bound_saturated hp hgp3 hcap hn ht hSsub hS
  have hup := sum_closedBall_sq_card_sub_one_le hcap ht (p := p)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact le_of_mul_le_mul_left (hlow.trans hup) hnR

/-- Lemma P for the palette, short radii: under the hypotheses of
`sum_closedBall_sq_card_sub_one_lower_bound_short_radii`,
`3 R(t) ≥ K + 2 R(t/4) - 2 Q`. -/
theorem three_mul_palette_lower_bound_short_radii {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) {S : Finset ℝ} (hSsub : S ⊆ OrderedDistanceValues p)
    (hS : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ∈ S → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    ((S ∪ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) +
        2 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t / 4)).card : ℝ) -
        2 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) := by
  have hlow :=
    sum_closedBall_sq_card_sub_one_lower_bound_short_radii hp hgp3 hcap hn ht hSsub hS
  have hup := sum_closedBall_sq_card_sub_one_le hcap ht (p := p)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact le_of_mul_le_mul_left (hlow.trans hup) hnR

end Esgk
