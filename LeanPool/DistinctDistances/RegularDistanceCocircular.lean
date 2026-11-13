/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.DistanceDesign
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Constant squared-distance row sums force cocircularity

If every point of a finite Euclidean configuration has the same sum of squared
distances to all points, then every point has the same distance from the
configuration centroid. The entire configuration is therefore cospherical.

This gives a uniform obstruction to the exact saturated corner of the ESGK
distance-design problem. A partition of `K_n` into spanning regular distance
graphs has constant squared-distance row sums, hence cannot be in general
position once `n >= 4`. This is an exact-corner result only: turning an almost
regular partition into a quantitative energy saving remains open.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- Expand one squared-distance row in terms of norms and the vector sum. -/
lemma sum_sqDistance_expand (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * ‖p i‖ ^ 2 + ∑ j, ‖p j‖ ^ 2 -
        2 * @inner ℝ Point _ (p i) (∑ j, p j) := by
  simp_rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left,
    inner_sub_right]
  simp_rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← inner_sum, ← sum_inner, real_inner_comm (∑ j, p j) (p i)]
  ring

/-- The centroid of a nonempty indexed configuration, expressed in the ambient
vector space. The definition is harmless at `n = 0`; its geometric lemmas
assume `0 < n`. -/
noncomputable def configCentroid (p : Config n) : Point :=
  (n : ℝ)⁻¹ • ∑ j, p j

/-- Scaled squared distance to the centroid, in a form directly comparable to
`sum_sqDistance_expand`. -/
lemma natCast_mul_dist_configCentroid_sq (p : Config n) (hn : 0 < n)
    (i : Fin n) :
    (n : ℝ) * dist (p i) (configCentroid p) ^ 2 =
      (n : ℝ) * ‖p i‖ ^ 2 - 2 * @inner ℝ Point _ (p i) (∑ j, p j) +
        (n : ℝ)⁻¹ * ‖∑ j, p j‖ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [configCentroid, dist_eq_norm, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (∑ j, p j) (p i)]
  field_simp
  ring

/-- Equal squared-distance row sums give equal distances from the centroid. -/
lemma dist_configCentroid_eq_of_row_sum_eq (p : Config n) (hn : 0 < n)
    (i k : Fin n)
    (hrow : (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2) :
    dist (p i) (configCentroid p) = dist (p k) (configCentroid p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow' := hrow
  rw [sum_sqDistance_expand, sum_sqDistance_expand] at hrow'
  have hi := natCast_mul_dist_configCentroid_sq p hn i
  have hk := natCast_mul_dist_configCentroid_sq p hn k
  have hsq : dist (p i) (configCentroid p) ^ 2 =
      dist (p k) (configCentroid p) ^ 2 := by
    nlinarith
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hsq

/-- A nonempty finite configuration with constant squared-distance row sums is
cospherical around its centroid. -/
theorem cospherical_range_of_constant_sqDistanceSum (p : Config n) (hn : 0 < n)
    (hrow : ∀ i k, (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2) :
    Cospherical (Set.range p) := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨configCentroid p, dist (p i0) (configCentroid p), ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  exact dist_configCentroid_eq_of_row_sum_eq p hn i i0 (hrow i i0)

/-- Finset-shaped version of
`cospherical_range_of_constant_sqDistanceSum`. -/
theorem cospherical_toFinset_of_constant_sqDistanceSum (p : Config n) (hn : 0 < n)
    (hrow : ∀ i k, (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2) :
    Cospherical (↑(Config.toFinset p) : Set Point) := by
  apply Cospherical.subset _ (cospherical_range_of_constant_sqDistanceSum p hn hrow)
  intro x hx
  rw [Finset.mem_coe, Config.toFinset, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Set.mem_range_self i

/-- A general-position configuration with at least four distinct points cannot
have constant squared-distance row sums. In particular, an exact saturated
distance design whose distance graphs are all spanning regular graphs has no
general-position realization. -/
theorem not_constant_sqDistanceSum_of_generalPosition {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 4 ≤ n) :
    ¬(∀ i k, (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2) := by
  intro hrow
  have hn0 : 0 < n := by omega
  have hcos := cospherical_toFinset_of_constant_sqDistanceSum p hn0 hrow
  have hcard : (Config.toFinset p).card = n := by
    rw [Config.toFinset, Finset.card_image_of_injective Finset.univ hp]
    simp
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (s := Config.toFinset p) (n := 4) (by omega)
  exact hgp.2 T hTsub hTcard (Cospherical.subset (by simpa using hTsub) hcos)

/-- Indices whose squared-distance rows have a prescribed sum. -/
noncomputable def SqDistanceRowSumFiber (p : Config n) (s : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ ∑ j, dist (p i) (p j) ^ 2 = s)

/-- In general position, at most three indexed points have the same
squared-distance row sum. Four such points would lie on one circle centered at
the configuration centroid. -/
theorem sqDistanceRowSumFiber_card_le_three {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (s : ℝ) :
    (SqDistanceRowSumFiber p s).card ≤ 3 := by
  classical
  by_contra hcard
  have hfour : 4 ≤ (SqDistanceRowSumFiber p s).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (s := SqDistanceRowSumFiber p s) (n := 4) hfour
  have hTpos : 0 < T.card := by omega
  obtain ⟨i, hiT⟩ := Finset.card_pos.mp hTpos
  let U : Finset Point := T.image p
  have hUsub : U ⊆ Config.toFinset p := by
    intro x hx
    change x ∈ T.image p at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _hk, rfl⟩ := hx
    rw [Config.toFinset, Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  have hUcard : U.card = 4 := by
    change (T.image p).card = 4
    rw [Finset.card_image_of_injective T hp, hTcard]
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hcos : Cospherical (↑U : Set Point) := by
    refine ⟨configCentroid p, dist (p i) (configCentroid p), ?_⟩
    intro x hx
    rw [Finset.mem_coe] at hx
    change x ∈ T.image p at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hkT, rfl⟩ := hx
    have hiFiber := hTsub hiT
    have hkFiber := hTsub hkT
    rw [SqDistanceRowSumFiber, Finset.mem_filter] at hiFiber hkFiber
    apply dist_configCentroid_eq_of_row_sum_eq p hn k i
    exact hkFiber.2.trans hiFiber.2.symm
  exact hgp.2 U hUsub hUcard hcos

/-- Decompose one squared-distance row by realized distance values. The
coefficient of `r^2` is exactly the out-degree of the distance-`r` graph at the
chosen vertex. -/
lemma sum_sqDistance_eq_sum_outDegree_mul (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ) * r ^ 2 := by
  classical
  have hdiag : (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        dist (p i) (p j) ^ 2 := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => dist (p i) (p j) ^ 2) (a := i) (by simp)
    simpa only [dist_self, pow_two, zero_mul, add_zero] using h.symm
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      dist (p i) (p j) ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [Finset.mem_erase, ne_comm] using hj⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin n)).erase i)
    (t := OrderedDistanceValues p)
    (g := fun j => dist (p i) (p j)) hmaps (fun r : ℝ => r ^ 2)
  rw [hdiag, ← hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  have hcard :
      (((Finset.univ : Finset (Fin n)).erase i).filter
        (fun j => dist (p i) (p j) = r)).card =
      (DistanceOutNeighborsAtValue p i r).card := by
    congr 1
    ext j
    simp [DistanceOutNeighborsAtValue, ne_comm]
  rw [← hcard]
  simp [mul_comm]

/-- Two vertices have the same complete distance-degree profile when every
realized distance graph gives them the same degree. -/
def SameDistanceDegreeProfile (p : Config n) (i k : Fin n) : Prop :=
  ∀ r ∈ OrderedDistanceValues p,
    (DistanceOutNeighborsAtValue p i r).card =
      (DistanceOutNeighborsAtValue p k r).card

/-- A complete distance-degree profile determines the squared-distance row
sum. -/
lemma sum_sqDistance_eq_of_sameDistanceDegreeProfile (p : Config n)
    {i k : Fin n} (hprofile : SameDistanceDegreeProfile p i k) :
    (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2 := by
  rw [sum_sqDistance_eq_sum_outDegree_mul,
    sum_sqDistance_eq_sum_outDegree_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hprofile r hr]

/-- The fiber of the complete distance-degree profile of one vertex. -/
noncomputable def DistanceDegreeProfileFiber (p : Config n) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (SameDistanceDegreeProfile p i)

/-- In general position, no four vertices have the same complete
distance-degree profile. This is the finite combinatorial shadow of the
centroid-circle obstruction. -/
theorem distanceDegreeProfileFiber_card_le_three {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (i : Fin n) :
    (DistanceDegreeProfileFiber p i).card ≤ 3 := by
  classical
  have hsubset : DistanceDegreeProfileFiber p i ⊆
      SqDistanceRowSumFiber p (∑ j, dist (p i) (p j) ^ 2) := by
    intro k hk
    change k ∈ Finset.univ.filter (SameDistanceDegreeProfile p i) at hk
    rw [Finset.mem_filter] at hk
    rw [SqDistanceRowSumFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (sum_sqDistance_eq_of_sameDistanceDegreeProfile p hk.2).symm⟩
  exact (Finset.card_le_card hsubset).trans
    (sqDistanceRowSumFiber_card_le_three hp hgp _)

/-- If every distance graph has the same degree at every vertex, then the
squared-distance row sum is independent of the vertex. -/
theorem constant_sqDistanceSum_of_regular_distance_degrees (p : Config n)
    (hregular : ∀ i k r,
      (DistanceOutNeighborsAtValue p i r).card =
        (DistanceOutNeighborsAtValue p k r).card) :
    ∀ i k, (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j, dist (p k) (p j) ^ 2 := by
  intro i k
  rw [sum_sqDistance_eq_sum_outDegree_mul,
    sum_sqDistance_eq_sum_outDegree_mul]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [hregular i k r]

/-- A nonempty configuration whose distance graphs are all regular is
cospherical. -/
theorem regular_distance_degrees_force_cospherical (p : Config n) (hn : 0 < n)
    (hregular : ∀ i k r,
      (DistanceOutNeighborsAtValue p i r).card =
        (DistanceOutNeighborsAtValue p k r).card) :
    Cospherical (↑(Config.toFinset p) : Set Point) :=
  cospherical_toFinset_of_constant_sqDistanceSum p hn
    (constant_sqDistanceSum_of_regular_distance_degrees p hregular)

/-- A value outside `OrderedDistanceValues` has no out-neighbors at any
vertex. -/
lemma distanceOutNeighborsAtValue_eq_empty_of_not_mem
    (p : Config n) (i : Fin n) {r : ℝ}
    (hr : r ∉ OrderedDistanceValues p) :
    DistanceOutNeighborsAtValue p i r = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hr
  rw [DistanceOutNeighborsAtValue, Finset.mem_filter] at hj
  rw [OrderedDistanceValues, Finset.mem_image]
  exact ⟨(i, j), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hj.2.1⟩,
    hj.2.2⟩

/-- If every realized ordered multiplicity reaches `3*n`, then the local
degree-three cap is saturated at every vertex of every realized distance graph;
unrealized distance values have degree zero. Hence every distance graph is
regular. -/
theorem regular_distance_degrees_of_all_multiplicities_eq_three_mul
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p))
    (hmult : ∀ r ∈ OrderedDistanceValues p,
      OrderedMultiplicity p r = 3 * n) :
    ∀ i k r,
      (DistanceOutNeighborsAtValue p i r).card =
        (DistanceOutNeighborsAtValue p k r).card := by
  intro i k r
  by_cases hr : r ∈ OrderedDistanceValues p
  · have hsum : ∑ x, (DistanceOutNeighborsAtValue p x r).card = 3 * n := by
      rw [← orderedMultiplicity_eq_sum_outNeighbor_card, hmult r hr]
    have hall : ∀ x ∈ (Finset.univ : Finset (Fin n)),
        (DistanceOutNeighborsAtValue p x r).card = 3 := by
      apply all_eq_cap_of_sum_eq_cap_mul_card
        (s := (Finset.univ : Finset (Fin n)))
        (m := fun x => (DistanceOutNeighborsAtValue p x r).card)
        (cap := 3)
      · intro x _hx
        exact distanceOutNeighborsAtValue_card_le_three hp hgp x r
      · simpa using hsum
    rw [hall i (Finset.mem_univ _), hall k (Finset.mem_univ _)]
  · rw [distanceOutNeighborsAtValue_eq_empty_of_not_mem p i hr,
      distanceOutNeighborsAtValue_eq_empty_of_not_mem p k hr]

/-- No general-position configuration of at least four points can have every
distance graph regular. This is the direct geometric terminal for the exact
saturated distance-design core. -/
theorem not_regular_distance_degrees_of_generalPosition {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 4 ≤ n) :
    ¬(∀ i k r,
      (DistanceOutNeighborsAtValue p i r).card =
        (DistanceOutNeighborsAtValue p k r).card) := by
  intro hregular
  exact not_constant_sqDistanceSum_of_generalPosition hp hgp hn
    (constant_sqDistanceSum_of_regular_distance_degrees p hregular)

end Esgk
