/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.RegularDistanceCocircular
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Entropy-census formalization checkpoints

This module packages the finite, data-driven facts that are stable enough to
formalize after the entropy-census experiments.

The results here do not improve the ESGK bound. They formalize reusable
bookkeeping:

* distance energy is exactly multiplicity collision energy;
* cap-only histogram information cannot beat the cubic endpoint;
* high energy under a cap forces a heavy/rich band;
* the exact integer-scaled energy/cherry defect decomposition;
* the strict finite exact cap and thresholded near-cap class, incidence, and
  exceptional-vertex cleanup bounds;
* integer power-energy probes under a cap are controlled by the same cap;
* the mined `K5` twin-opposite atom has an exact algebraic obstruction in its
  one-dimensional normal form.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {α : Type*}

/-! ## Collision-energy and cap-only bookkeeping -/

/-- Distance energy is the generic multiplicity collision energy of the ordered
distance multiplicities. -/
theorem distanceEnergy_eq_multiplicityEnergy {n : ℕ} (p : Config n) :
    DistanceEnergy p =
      MultiplicityEnergy (OrderedDistanceValues p) (OrderedMultiplicity p) := by
  rfl

/-- A pointwise multiplicity cap gives the cap-only second-moment bound
`sum m_i^2 <= B * sum m_i`. This is the formal histogram-only no-go: without
additional geometric co-realizability information, the second moment is
controlled only by the cap times total mass. -/
theorem multiplicityEnergy_le_cap_mul_mass
    (s : Finset α) (m : α → ℕ) (B : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ B) :
    MultiplicityEnergy s m ≤ B * MultiplicityMass s m := by
  classical
  unfold MultiplicityEnergy MultiplicityMass
  calc
    ∑ a ∈ s, (m a) ^ 2
        ≤ ∑ a ∈ s, B * m a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          calc
            (m a) ^ 2 = m a * m a := by ring
            _ ≤ B * m a := Nat.mul_le_mul_right (m a) (hcap a ha)
    _ = B * ∑ a ∈ s, m a := by
          rw [Finset.mul_sum]

/-- Equality case of the cap-only collision bound. If every multiplicity is
positive and at most `cap`, and `sum m^2 = cap * sum m`, then every
multiplicity equals `cap`. -/
theorem all_eq_cap_of_sum_sq_eq_cap_mul_sum
    (s : Finset α) (m : α → ℕ) (cap : ℕ)
    (hpos : ∀ a ∈ s, 0 < m a)
    (hcap : ∀ a ∈ s, m a ≤ cap)
    (heq : ∑ a ∈ s, (m a) ^ 2 = cap * ∑ a ∈ s, m a) :
    ∀ a ∈ s, m a = cap := by
  classical
  intro a ha
  by_contra hne
  have hlt : m a < cap := Nat.lt_of_le_of_ne (hcap a ha) hne
  have hstrict : ∑ x ∈ s, (m x) ^ 2 < ∑ x ∈ s, cap * m x := by
    refine Finset.sum_lt_sum ?_ ⟨a, ha, ?_⟩
    · intro x hx
      calc
        (m x) ^ 2 = m x * m x := by ring
        _ ≤ cap * m x := Nat.mul_le_mul_right (m x) (hcap x hx)
    · calc
        (m a) ^ 2 = m a * m a := by ring
        _ < cap * m a := Nat.mul_lt_mul_of_pos_right hlt (hpos a ha)
  rw [← Finset.mul_sum, heq] at hstrict
  exact (lt_irrefl _) hstrict

/-- Total slack in the cap-only collision inequality, written as the sum of
pointwise weighted deficits `m(a) * (cap - m(a))`. -/
def MultiplicityCapDefect
    (s : Finset α) (m : α → ℕ) (cap : ℕ) : ℕ :=
  ∑ a ∈ s, m a * (cap - m a)

/-- Exact cap-defect identity
`sum m^2 + sum m(cap-m) = cap * sum m`. -/
theorem multiplicityEnergy_add_capDefect_eq_cap_mul_mass
    (s : Finset α) (m : α → ℕ) (cap : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ cap) :
    MultiplicityEnergy s m + MultiplicityCapDefect s m cap =
      cap * MultiplicityMass s m := by
  classical
  unfold MultiplicityEnergy MultiplicityCapDefect MultiplicityMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    m a ^ 2 + m a * (cap - m a) =
        m a * m a + (m a * cap - m a * m a) := by
      rw [pow_two, Nat.mul_sub_left_distrib]
    _ = m a * cap :=
      Nat.add_sub_of_le (Nat.mul_le_mul_left (m a) (hcap a ha))
    _ = cap * m a := Nat.mul_comm _ _

/-- Thresholded mass form of Markov's inequality for cap deficits. Distance
classes whose deficit is at least `threshold` carry at most total cap defect
divided by `threshold` mass, stated without division. -/
theorem threshold_mul_bad_mass_le_capDefect
    (s : Finset α) (m : α → ℕ) (cap threshold : ℕ) :
    threshold * MultiplicityMass
      (s.filter (fun a => threshold ≤ cap - m a)) m ≤
        MultiplicityCapDefect s m cap := by
  classical
  unfold MultiplicityMass MultiplicityCapDefect
  calc
    threshold * ∑ a ∈ s.filter (fun a => threshold ≤ cap - m a), m a =
        ∑ a ∈ s.filter (fun a => threshold ≤ cap - m a),
          threshold * m a := by
      rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ s.filter (fun a => threshold ≤ cap - m a),
        m a * (cap - m a) := by
      refine Finset.sum_le_sum ?_
      intro a ha
      rw [Finset.mem_filter] at ha
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (m a) ha.2
    _ ≤ ∑ a ∈ s, m a * (cap - m a) := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Thresholded count form of Markov's inequality for arbitrary natural-number
deficits. -/
theorem threshold_mul_bad_count_le_sum
    (s : Finset α) (defect : α → ℕ) (threshold : ℕ) :
    threshold * (s.filter (fun a => threshold ≤ defect a)).card ≤
      ∑ a ∈ s, defect a := by
  classical
  calc
    threshold * (s.filter (fun a => threshold ≤ defect a)).card =
        ∑ _a ∈ s.filter (fun a => threshold ≤ defect a), threshold := by
      simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ a ∈ s.filter (fun a => threshold ≤ defect a), defect a := by
      refine Finset.sum_le_sum ?_
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a ∈ s, defect a := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A weighted threshold inequality: on terms whose weight is at least
`threshold`, the total defect is controlled by the global weighted-defect
sum. -/
theorem threshold_mul_filtered_defect_le_weighted_sum
    (s : Finset α) (weight defect : α → ℕ) (threshold : ℕ) :
    threshold * ∑ a ∈ s.filter (fun a => threshold ≤ weight a), defect a ≤
      ∑ a ∈ s, weight a * defect a := by
  classical
  calc
    threshold * ∑ a ∈ s.filter (fun a => threshold ≤ weight a), defect a =
        ∑ a ∈ s.filter (fun a => threshold ≤ weight a),
          threshold * defect a := by
      rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ s.filter (fun a => threshold ≤ weight a),
        weight a * defect a := by
      refine Finset.sum_le_sum ?_
      intro a ha
      exact Nat.mul_le_mul_right (defect a) (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a ∈ s, weight a * defect a := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Cap-only distance-energy bound, before using the GP-specific cap. -/
theorem distanceEnergy_le_cap_mul_orderedDistanceMass {n B : ℕ} {p : Config n}
    (hcap : ∀ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r ≤ B) :
    DistanceEnergy p ≤ B * OrderedDistanceMass p := by
  simpa [distanceEnergy_eq_multiplicityEnergy, OrderedDistanceMass, MultiplicityMass] using
    multiplicityEnergy_le_cap_mul_mass
      (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (B := B) hcap

/-- In general position, the cap-only theorem specializes to the `3*n` bound.
This is the reusable Lean form of "the cap alone reaches only the cubic
endpoint". -/
theorem distanceEnergy_le_three_mul_orderedDistanceMass {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p ≤ (3 * n) * OrderedDistanceMass p := by
  exact distanceEnergy_le_cap_mul_orderedDistanceMass
    (p := p) (B := 3 * n) (fun r _hr => orderedMultiplicity_le_three_mul hp hgp r)

/-- If the distance-energy cap inequality is an equality, every realized
ordered distance multiplicity reaches the cap. -/
theorem all_orderedMultiplicities_eq_cap_of_energy_eq_cap
    {n cap : ℕ} {p : Config n}
    (hcap : ∀ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r ≤ cap)
    (henergy : DistanceEnergy p = cap * OrderedDistanceMass p) :
    ∀ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = cap := by
  apply all_eq_cap_of_sum_sq_eq_cap_mul_sum
    (s := OrderedDistanceValues p) (m := OrderedMultiplicity p)
    (cap := cap)
  · intro r hr
    exact orderedMultiplicity_pos_of_mem hr
  · exact hcap
  · simpa [DistanceEnergy, OrderedDistanceMass] using henergy

/-- Exact ordered-energy form of the elementary cap. Unlike the older
`3*n^3` packaging, this retains the exact off-diagonal mass `n*(n-1)`. -/
theorem distanceEnergy_le_exact_cap {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p ≤ 3 * n ^ 2 * (n - 1) := by
  have hcap := distanceEnergy_le_three_mul_orderedDistanceMass (p := p) hp hgp
  rw [orderedDistanceMass_eq_n_mul_pred] at hcap
  calc
    DistanceEnergy p ≤ (3 * n) * (n * (n - 1)) := hcap
    _ = 3 * n ^ 2 * (n - 1) := by ring

/-- Cap defect for ordered distance multiplicities under the GP cap `3*n`. -/
noncomputable def DistanceMultiplicityCapDefect {n : ℕ} (p : Config n) : ℕ :=
  MultiplicityCapDefect
    (OrderedDistanceValues p) (OrderedMultiplicity p) (3 * n)

/-- Total number of missing local degree incidences from degree three in one
distance graph. Under general position every summand is an honest deficit in
`{0,1,2,3}`. -/
noncomputable def DistanceLocalDegreeDefect {n : ℕ}
    (p : Config n) (r : ℝ) : ℕ :=
  ∑ i : Fin n, (3 - (DistanceOutNeighborsAtValue p i r).card)

/-- The global multiplicity deficit `3*n-M_r` is exactly the sum of the local
degree-three deficits in the distance-`r` graph. -/
theorem orderedMultiplicity_defect_eq_localDegreeDefect
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (r : ℝ) :
    3 * n - OrderedMultiplicity p r = DistanceLocalDegreeDefect p r := by
  have hdegree : ∀ i : Fin n,
      (DistanceOutNeighborsAtValue p i r).card ≤ 3 :=
    fun i => distanceOutNeighborsAtValue_card_le_three hp hgp i r
  have hsum : OrderedMultiplicity p r + DistanceLocalDegreeDefect p r =
      3 * n := by
    rw [orderedMultiplicity_eq_sum_outNeighbor_card]
    unfold DistanceLocalDegreeDefect
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i, ((DistanceOutNeighborsAtValue p i r).card +
          (3 - (DistanceOutNeighborsAtValue p i r).card)) =
          ∑ _i : Fin n, 3 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Nat.add_sub_of_le (hdegree i)
      _ = 3 * n := by simp [Finset.sum_const, mul_comm]
  omega

/-- The multiplicity cap defect is exactly the multiplicity-weighted sum of
the local degree-three deficits. -/
theorem distanceMultiplicityCapDefect_eq_weightedLocalDegreeDefect
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceMultiplicityCapDefect p =
      ∑ r ∈ OrderedDistanceValues p,
        OrderedMultiplicity p r * DistanceLocalDegreeDefect p r := by
  unfold DistanceMultiplicityCapDefect MultiplicityCapDefect
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← orderedMultiplicity_defect_eq_localDegreeDefect hp hgp r]

/-- Exact distance specialization of the cap-defect identity. -/
theorem distanceEnergy_add_capDefect_eq_exactCap {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p + DistanceMultiplicityCapDefect p =
      3 * n ^ 2 * (n - 1) := by
  have h := multiplicityEnergy_add_capDefect_eq_cap_mul_mass
    (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (cap := 3 * n)
    (fun r _hr => orderedMultiplicity_le_three_mul hp hgp r)
  rw [← distanceEnergy_eq_multiplicityEnergy] at h
  change DistanceEnergy p + DistanceMultiplicityCapDefect p =
    (3 * n) * OrderedDistanceMass p at h
  rw [orderedDistanceMass_eq_n_mul_pred] at h
  calc
    DistanceEnergy p + DistanceMultiplicityCapDefect p =
        (3 * n) * (n * (n - 1)) := h
    _ = 3 * n ^ 2 * (n - 1) := by ring

/-- If energy is within additive deficit `delta` of the exact cap, then the
total weighted multiplicity defect is at most `delta`. -/
theorem distanceMultiplicityCapDefect_le_of_near_cap
    {n delta : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    DistanceMultiplicityCapDefect p ≤ delta := by
  have hid := distanceEnergy_add_capDefect_eq_exactCap hp hgp
  omega

/-- Explicit SR1 multiplicity cleanup bound. If energy is within `delta` of
the cap, the total ordered-pair mass in distance classes whose multiplicity is
at least `threshold` below `3*n` is at most `delta / threshold`, stated in
division-free product form. -/
theorem threshold_mul_underfullDistanceMass_le_of_near_cap
    {n delta threshold : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    threshold * MultiplicityMass
      ((OrderedDistanceValues p).filter
        (fun r => threshold ≤ 3 * n - OrderedMultiplicity p r))
      (OrderedMultiplicity p) ≤ delta := by
  exact (threshold_mul_bad_mass_le_capDefect
    (s := OrderedDistanceValues p) (m := OrderedMultiplicity p)
    (cap := 3 * n) (threshold := threshold)).trans
      (distanceMultiplicityCapDefect_le_of_near_cap hp hgp hnear)

/-- Explicit SR1 local-incidence cleanup bound. Among distance classes of
ordered multiplicity at least `threshold`, the total number of incidences
missing from degree three is at most `delta / threshold`, stated without
division. -/
theorem threshold_mul_richDistanceLocalDegreeDefect_le_of_near_cap
    {n delta threshold : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    threshold *
      ∑ r ∈ (OrderedDistanceValues p).filter
        (fun r => threshold ≤ OrderedMultiplicity p r),
        DistanceLocalDegreeDefect p r ≤ delta := by
  have hweighted := threshold_mul_filtered_defect_le_weighted_sum
    (s := OrderedDistanceValues p) (weight := OrderedMultiplicity p)
    (defect := DistanceLocalDegreeDefect p) threshold
  rw [← distanceMultiplicityCapDefect_eq_weightedLocalDegreeDefect hp hgp]
    at hweighted
  exact hweighted.trans
    (distanceMultiplicityCapDefect_le_of_near_cap hp hgp hnear)

/-- At one vertex, total local degree-three defect over the distance classes
whose ordered multiplicity is at least `classThreshold`. -/
noncomputable def RichDistanceVertexDegreeDefect {n : ℕ}
    (p : Config n) (classThreshold : ℕ) (i : Fin n) : ℕ :=
  ∑ r ∈ (OrderedDistanceValues p).filter
    (fun r => classThreshold ≤ OrderedMultiplicity p r),
    (3 - (DistanceOutNeighborsAtValue p i r).card)

/-- Double-count the missing rich-class degree incidences, first by vertices
and then by distance classes. -/
theorem sum_richDistanceVertexDegreeDefect_eq_sum_localDegreeDefect
    {n : ℕ} (p : Config n) (classThreshold : ℕ) :
    ∑ i, RichDistanceVertexDegreeDefect p classThreshold i =
      ∑ r ∈ (OrderedDistanceValues p).filter
        (fun r => classThreshold ≤ OrderedMultiplicity p r),
        DistanceLocalDegreeDefect p r := by
  unfold RichDistanceVertexDegreeDefect DistanceLocalDegreeDefect
  rw [Finset.sum_comm]

/-- Explicit SR1 exceptional-vertex bound. A vertex is exceptional when its
total missing degree over the rich distance classes is at least
`vertexThreshold`. The product form preserves both threshold parameters. -/
theorem richDistance_exceptionalVertex_count_product_le_of_near_cap
    {n delta classThreshold vertexThreshold : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    classThreshold * vertexThreshold *
      ((Finset.univ : Finset (Fin n)).filter
        (fun i => vertexThreshold ≤
          RichDistanceVertexDegreeDefect p classThreshold i)).card ≤ delta := by
  have hvertices := threshold_mul_bad_count_le_sum
    (s := (Finset.univ : Finset (Fin n)))
    (defect := RichDistanceVertexDegreeDefect p classThreshold)
    vertexThreshold
  rw [sum_richDistanceVertexDegreeDefect_eq_sum_localDegreeDefect] at hvertices
  have hclasses :=
    threshold_mul_richDistanceLocalDegreeDefect_le_of_near_cap
      hp hgp hnear (threshold := classThreshold)
  calc
    classThreshold * vertexThreshold *
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => vertexThreshold ≤
            RichDistanceVertexDegreeDefect p classThreshold i)).card =
        classThreshold * (vertexThreshold *
          ((Finset.univ : Finset (Fin n)).filter
            (fun i => vertexThreshold ≤
              RichDistanceVertexDegreeDefect p classThreshold i)).card) := by ring
    _ ≤ classThreshold *
        (∑ r ∈ (OrderedDistanceValues p).filter
          (fun r => classThreshold ≤ OrderedMultiplicity p r),
          DistanceLocalDegreeDefect p r) :=
      Nat.mul_le_mul_left classThreshold hvertices
    _ ≤ delta := hclasses

/-- The exact ordered-energy cap is never attained by a general-position
configuration with at least four points. Equality would force every realized
distance graph to be spanning 3-regular; constant squared-distance row sums
would then force the configuration to be cocircular. This strict finite
inequality is not a uniform-density or asymptotic saving. -/
theorem distanceEnergy_lt_exact_cap {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 4 ≤ n) :
    DistanceEnergy p < 3 * n ^ 2 * (n - 1) := by
  apply Nat.lt_of_le_of_ne (distanceEnergy_le_exact_cap hp hgp)
  intro heq
  have hmass : OrderedDistanceMass p = n * (n - 1) :=
    orderedDistanceMass_eq_n_mul_pred p
  have henergy : DistanceEnergy p = (3 * n) * OrderedDistanceMass p := by
    rw [hmass, heq]
    ring
  have hmult : ∀ r ∈ OrderedDistanceValues p,
      OrderedMultiplicity p r = 3 * n := by
    apply all_orderedMultiplicities_eq_cap_of_energy_eq_cap
      (cap := 3 * n)
    · intro r _hr
      exact orderedMultiplicity_le_three_mul hp hgp r
    · exact henergy
  have hregular :=
    regular_distance_degrees_of_all_multiplicities_eq_three_mul hp hgp hmult
  exact not_regular_distance_degrees_of_generalPosition hp hgp hn hregular

/-- Combining the cap-only theorem with the total ordered-pair mass bound gives
the existing cubic endpoint. -/
theorem distanceEnergy_le_three_mul_cube_via_capOnly {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p ≤ 3 * n ^ 3 := by
  have hcap := distanceEnergy_le_three_mul_orderedDistanceMass (p := p) hp hgp
  have hmass := orderedDistanceMass_le_square (p := p)
  calc
    DistanceEnergy p ≤ (3 * n) * OrderedDistanceMass p := hcap
    _ ≤ (3 * n) * n ^ 2 := Nat.mul_le_mul_left (3 * n) hmass
    _ = 3 * n ^ 3 := by ring

/-! ## Rich-band consequence -/

/-- Product-form rich-band consequence. This restates the existing
`DistanceDesign` theorem in the entropy-census vocabulary: high collision
energy under the GP cap forces many ordered edges to lie in linear-rich distance
classes. -/
theorem collisionEnergy_forces_heavyDistanceValues
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (hn : 0 < n) (K : ℕ) {eta : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (henergy : eta * ((3 * n : ℕ) : ℝ) * (n : ℝ) ^ 2 ≤
      (DistanceEnergy p : ℝ))
    (hK : (K : ℝ) ≤ eta / 2 * ((3 * n : ℕ) : ℝ)) :
    eta / 2 * (OrderedDistanceMass p : ℝ) ≤
      ((3 * n : ℕ) : ℝ) * ((HeavyDistanceValues p K).card : ℝ) := by
  exact heavyDistanceValues_card_product_lower_bound_real_of_energy_ge_square
    (p := p) hp hgp hn K heta_nonneg henergy hK

/-! ## Cherry saturation bookkeeping -/

/-- Summed form of `d^2 = d * (d - 1) + d`. This is the algebraic bridge from
degree squares to doubled cherry counts and total degree mass. -/
theorem sum_sq_eq_sum_falling_add_sum
    (s : Finset α) (degree : α → ℤ) :
    ∑ a ∈ s, (degree a) ^ 2 =
      (∑ a ∈ s, degree a * (degree a - 1)) + ∑ a ∈ s, degree a := by
  calc
    ∑ a ∈ s, (degree a) ^ 2 =
        ∑ a ∈ s, (degree a * (degree a - 1) + degree a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          ring
    _ = (∑ a ∈ s, degree a * (degree a - 1)) + ∑ a ∈ s, degree a := by
          rw [Finset.sum_add_distrib]

/-- If the falling-factorial sum is twice the cherry count and the degree sum
is the total incidence mass, then the degree-square mass is their stated sum. -/
theorem degreeSquareMass_eq_two_mul_cherry_add_mass
    (s : Finset α) (degree : α → ℤ) (cherry mass : ℤ)
    (hcherry : ∑ a ∈ s, degree a * (degree a - 1) = 2 * cherry)
    (hmass : ∑ a ∈ s, degree a = mass) :
    ∑ a ∈ s, (degree a) ^ 2 = 2 * cherry + mass := by
  rw [sum_sq_eq_sum_falling_add_sum, hcherry, hmass]

/-- Integer-scaled form of the exact energy-defect decomposition. The input
`degreeSquareMass = 2 * cherry + n * (n - 1)` is the summed identity
`d^2 = d + 2 * binom(d,2)` for a complete edge coloring. Scaling by four
keeps every term integral. -/
theorem energyDefect_four_mul_decomposition
    (n energy cherry degreeSquareMass : ℤ)
    (hdegree : degreeSquareMass = 2 * cherry + n * (n - 1)) :
    3 * n ^ 2 * (n - 1) - 4 * energy =
      (n * degreeSquareMass - 4 * energy) +
        2 * n * (n * (n - 1) - cherry) := by
  rw [hdegree]
  ring

/-- Nonnegativity consequence of the exact defect decomposition. The two
hypotheses are precisely nonnegativity of the Cauchy slack and of the cherry
defect. -/
theorem energyDefect_four_mul_nonneg
    (n energy cherry degreeSquareMass : ℤ)
    (hn : 0 ≤ n)
    (hdegree : degreeSquareMass = 2 * cherry + n * (n - 1))
    (hcauchy : 4 * energy ≤ n * degreeSquareMass)
    (hcherry : cherry ≤ n * (n - 1)) :
    0 ≤ 3 * n ^ 2 * (n - 1) - 4 * energy := by
  rw [energyDefect_four_mul_decomposition n energy cherry degreeSquareMass hdegree]
  exact add_nonneg (sub_nonneg.mpr hcauchy)
    (mul_nonneg (mul_nonneg (by norm_num) hn) (sub_nonneg.mpr hcherry))

/-- A sum of pointwise integer deficits is the cap times the number of terms
minus the observed total. This is the common finite identity behind both the
pair-witness and local degree-packing forms of the cherry defect. -/
theorem sum_int_defect_eq_card_mul_sub_sum
    (s : Finset α) (w : α → ℕ) (cap : ℕ) :
    ∑ a ∈ s, ((cap : ℤ) - (w a : ℤ)) =
      (cap : ℤ) * s.card - ∑ a ∈ s, (w a : ℤ) := by
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, mul_comm]

/-- The perpendicular bisector of two distinct points in the plane is collinear.
This helper packages the finite-dimensional part of the cherry bound: the
bisector direction is the orthogonal complement of a nonzero one-dimensional
subspace of `ℝ²`, hence has dimension at most one. -/
theorem collinear_subset_perpBisector {a b : Point} {s : Set Point}
    [Finite s] (hab : a ≠ b) (hs : s ⊆ (AffineSubspace.perpBisector a b : Set Point)) :
    Collinear ℝ s := by
  classical
  have : FiniteDimensional ℝ (vectorSpan ℝ s) :=
    finiteDimensional_vectorSpan_of_finite ℝ (Set.toFinite s)
  rw [collinear_iff_finrank_le_one]
  have hspan_le : vectorSpan ℝ s ≤ (AffineSubspace.perpBisector a b).direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.mpr hs)
  have hdir : Module.finrank ℝ (AffineSubspace.perpBisector a b).direction ≤ 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have hv : b -ᵥ a ≠ (0 : Point) := vsub_ne_zero.mpr (Ne.symm hab)
    let : Fact (Module.finrank ℝ Point = 1 + 1) := ⟨by simp [Point]⟩
    have hfin : Module.finrank ℝ (↥(ℝ ∙ (b -ᵥ a))ᗮ) = 1 := by
      simpa using
        (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := Point) (n := 1) hv)
    rw [hfin]
  exact (Submodule.finrank_mono hspan_le).trans hdir

/-- Equal-distance cherry witnesses for a base pair `{a,b}` inside a finite
point set. The witnesses are not required to exclude `a` or `b`; when `a ≠ b`
those two endpoints are not members anyway. -/
noncomputable def EquidistantWitnesses (P : Finset Point) (a b : Point) : Finset Point :=
  P.filter (fun x => dist x a = dist x b)

/-- Cherry bound: in a general-position finite point set, at most two points are
equidistant from a fixed distinct pair `{a,b}`. All witnesses lie on the
perpendicular bisector of `ab`, which is collinear; three witnesses would
contradict the no-three-collinear part of `InGeneralPosition`. -/
theorem equidistantWitnesses_card_le_two_of_nonTrilinear {P : Finset Point} {a b : Point}
    (hgp3 : NonTrilinear (P : Set Point)) (hab : a ≠ b) :
    (EquidistantWitnesses P a b).card ≤ 2 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := EquidistantWitnesses P a b) (n := 3) (by omega)
  have hTP : T ⊆ P := hTsub.trans (Finset.filter_subset _ _)
  rw [Finset.card_eq_three] at hTcard
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hTcard
  have hxT : x ∈ ({x, y, z} : Finset Point) := by simp
  have hyT : y ∈ ({x, y, z} : Finset Point) := by simp
  have hzT : z ∈ ({x, y, z} : Finset Point) := by simp
  have hxP : x ∈ (P : Set Point) := by exact hTP hxT
  have hyP : y ∈ (P : Set Point) := by exact hTP hyT
  have hzP : z ∈ (P : Set Point) := by exact hTP hzT
  have hxw : dist x a = dist x b := by
    have hx := hTsub hxT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hx).2
  have hyw : dist y a = dist y b := by
    have hy := hTsub hyT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hy).2
  have hzw : dist z a = dist z b := by
    have hz := hTsub hzT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hz).2
  have hcol : Collinear ℝ ({x, y, z} : Set Point) := by
    apply collinear_subset_perpBisector (a := a) (b := b) hab
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hxw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hyw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hzw
  exact (hgp3 hxP hyP hzP hxy hyz hxz) hcol

/-- General-position consumer of the GP3-only perpendicular-bisector bound. -/
theorem equidistantWitnesses_card_le_two {P : Finset Point} {a b : Point}
    (hgp : InGeneralPosition P) (hab : a ≠ b) :
    (EquidistantWitnesses P a b).card ≤ 2 :=
  equidistantWitnesses_card_le_two_of_nonTrilinear hgp.1 hab

/-- Indexed-configuration form of the cherry bound. -/
theorem config_equidistantWitnesses_card_le_two {n : ℕ} {p : Config n}
    (hgp : InGeneralPosition (Config.toFinset p)) {i j : Fin n}
    (hij : p i ≠ p j) :
    (EquidistantWitnesses (Config.toFinset p) (p i) (p j)).card ≤ 2 :=
  equidistantWitnesses_card_le_two hgp hij

/-- Index-level equidistant witnesses for an ordered base pair. This is the
shape needed to reindex witness counts against local distance degrees. -/
noncomputable def IndexedEquidistantWitnesses {n : ℕ}
    (p : Config n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => dist (p x) (p i) = dist (p x) (p j))

/-- Injectivity maps index-level witnesses into the point-finset witness set. -/
lemma indexedEquidistantWitnesses_card_le_pointWitnesses
    {n : ℕ} {p : Config n} (hp : Function.Injective p) (i j : Fin n) :
    (IndexedEquidistantWitnesses p i j).card ≤
      (EquidistantWitnesses (Config.toFinset p) (p i) (p j)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun x => p x) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, IndexedEquidistantWitnesses,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, EquidistantWitnesses, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hx⟩
  · intro a _ha b _hb hab
    exact hp hab

/-- Index-level cherry bound for distinct ordered base indices. -/
theorem indexedEquidistantWitnesses_card_le_two_of_nonTrilinear
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) {i j : Fin n}
    (hij : i ≠ j) :
    (IndexedEquidistantWitnesses p i j).card ≤ 2 :=
  (indexedEquidistantWitnesses_card_le_pointWitnesses hp i j).trans
    (equidistantWitnesses_card_le_two_of_nonTrilinear hgp3 (hp.ne hij))

/-- General-position consumer of the GP3-only indexed cherry bound. -/
theorem indexedEquidistantWitnesses_card_le_two
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) {i j : Fin n}
    (hij : i ≠ j) :
    (IndexedEquidistantWitnesses p i j).card ≤ 2 := by
  exact indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp.1 hij

/-- Total witness count over ordered off-diagonal base pairs. -/
noncomputable def OrderedPairWitnessTotal {n : ℕ} (p : Config n) : ℕ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (IndexedEquidistantWitnesses p ij.1 ij.2).card

/-- Ordered equal-distance base pairs seen from one apex, with the apex removed
from the base vertex set. -/
noncomputable def ApexEqualDistancePairs {n : ℕ}
    (p : Config n) (x : Fin n) : Finset (Fin n × Fin n) :=
  ((Finset.univ.erase x).offDiag).filter
    (fun ab => dist (p x) (p ab.1) = dist (p x) (p ab.2))

/-- Local falling-degree mass summed over all distance values and apexes. -/
noncomputable def DistanceDegreeFallingMass {n : ℕ} (p : Config n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p,
    ∑ x, (DistanceOutNeighborsAtValue p x r).card *
      ((DistanceOutNeighborsAtValue p x r).card - 1)

/-- At a fixed apex, the falling-degree mass counts ordered equal-distance
base pairs. -/
theorem fixedApex_fallingMass_eq_apexEqualDistancePairs_card
    {n : ℕ} (p : Config n) (x : Fin n) :
    (∑ r ∈ OrderedDistanceValues p,
      (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1)) =
      (ApexEqualDistancePairs p x).card := by
  classical
  have hmaps : ∀ ab ∈ ApexEqualDistancePairs p x,
      dist (p x) (p ab.1) ∈ OrderedDistanceValues p := by
    intro ab hab
    rw [ApexEqualDistancePairs, Finset.mem_filter, Finset.mem_offDiag] at hab
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(x, ab.1), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_erase.mp hab.1.1).1.symm⟩, rfl⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun ab : Fin n × Fin n => dist (p x) (p ab.1))
    (s := ApexEqualDistancePairs p x)
    (t := OrderedDistanceValues p) hmaps
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  have heq :
      (ApexEqualDistancePairs p x).filter
        (fun ab => dist (p x) (p ab.1) = r) =
      (DistanceOutNeighborsAtValue p x r).offDiag := by
    ext ab
    simp only [ApexEqualDistancePairs, Finset.mem_filter,
      Finset.mem_offDiag, DistanceOutNeighborsAtValue, Finset.mem_erase,
      Finset.mem_univ, true_and]
    aesop
  rw [heq, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Reindex ordered-pair witness total by its witness/apex coordinate. -/
theorem orderedPairWitnessTotal_eq_sum_apexEqualDistancePairs_card
    {n : ℕ} {p : Config n} (hp : Function.Injective p) :
    OrderedPairWitnessTotal p =
      ∑ x, (ApexEqualDistancePairs p x).card := by
  unfold OrderedPairWitnessTotal IndexedEquidistantWitnesses
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  have heq :
      ((Finset.univ : Finset (Fin n)).offDiag).filter
        (fun ab => dist (p x) (p ab.1) = dist (p x) (p ab.2)) =
      ApexEqualDistancePairs p x := by
    ext ab
    rw [ApexEqualDistancePairs, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hoff, hdist⟩
      rw [Finset.mem_offDiag] at hoff
      obtain ⟨ha, hb, hab⟩ := hoff
      have hax : ab.1 ≠ x := by
        intro h
        have hzero : dist (p x) (p ab.2) = 0 := by
          simpa [h] using hdist.symm
        exact hab (h.trans (hp (dist_eq_zero.mp hzero)))
      have hbx : ab.2 ≠ x := by
        intro h
        have hzero : dist (p x) (p ab.1) = 0 := by
          simpa [h] using hdist
        have hxa : x = ab.1 := hp (dist_eq_zero.mp hzero)
        exact hab (hxa.symm.trans h.symm)
      refine ⟨?_, hdist⟩
      rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_erase.mpr ⟨hax, ha⟩,
        Finset.mem_erase.mpr ⟨hbx, hb⟩, hab⟩
    · rintro ⟨hoff, hdist⟩
      refine ⟨?_, hdist⟩
      rw [Finset.mem_offDiag] at hoff ⊢
      exact ⟨(Finset.mem_erase.mp hoff.1).2,
        (Finset.mem_erase.mp hoff.2.1).2, hoff.2.2⟩
  rw [← heq]
  rw [Finset.sum_filter]

/-- The local falling-degree mass and ordered pair-witness total are the same
finite equal-distance triple count. -/
theorem distanceDegreeFallingMass_eq_orderedPairWitnessTotal
    {n : ℕ} {p : Config n} (hp : Function.Injective p) :
    DistanceDegreeFallingMass p = OrderedPairWitnessTotal p := by
  unfold DistanceDegreeFallingMass
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ r ∈ OrderedDistanceValues p,
      (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1)) =
        ∑ x, (ApexEqualDistancePairs p x).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact fixedApex_fallingMass_eq_apexEqualDistancePairs_card p x
    _ = OrderedPairWitnessTotal p :=
      (orderedPairWitnessTotal_eq_sum_apexEqualDistancePairs_card hp).symm

/-- Total ordered-base-pair witness defect from the cap two. -/
noncomputable def OrderedPairWitnessDefect {n : ℕ} (p : Config n) : ℕ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (2 - (IndexedEquidistantWitnesses p ij.1 ij.2).card)

/-- Ordered base pairs whose witness defect is at least `threshold`. -/
noncomputable def ExceptionalOrderedPairsByWitnessDefect {n : ℕ}
    (p : Config n) (threshold : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter
    (fun ij => threshold ≤
      2 - (IndexedEquidistantWitnesses p ij.1 ij.2).card)

/-- Conditional SR1 pair-witness cleanup: exceptional pair count is controlled
by total pair-witness defect. The remaining bridge is to bound
`OrderedPairWitnessDefect` by the energy defect. -/
theorem threshold_mul_exceptionalOrderedPair_count_le_witnessDefect
    {n : ℕ} (p : Config n) (threshold : ℕ) :
    threshold * (ExceptionalOrderedPairsByWitnessDefect p threshold).card ≤
      OrderedPairWitnessDefect p := by
  exact threshold_mul_bad_count_le_sum
    (s := (Finset.univ : Finset (Fin n)).offDiag)
    (defect := fun ij =>
      2 - (IndexedEquidistantWitnesses p ij.1 ij.2).card)
    threshold

/-- Sum of squared local distance degrees. -/
noncomputable def DistanceDegreeSquareMass {n : ℕ} (p : Config n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p,
    ∑ i, (DistanceOutNeighborsAtValue p i r).card ^ 2

/-- Local degree-square mass splits into falling-degree mass plus total ordered
distance mass. -/
theorem distanceDegreeSquareMass_eq_falling_add_mass
    {n : ℕ} (p : Config n) :
    DistanceDegreeSquareMass p =
      DistanceDegreeFallingMass p + OrderedDistanceMass p := by
  unfold DistanceDegreeSquareMass DistanceDegreeFallingMass OrderedDistanceMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [orderedMultiplicity_eq_sum_outNeighbor_card]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let d := (DistanceOutNeighborsAtValue p i r).card
  change d ^ 2 = d * (d - 1) + d
  cases d with
  | zero => simp
  | succ k => simp; ring

/-- Cauchy-Schwarz on the degree sequence of every distance graph, summed over
all realized distances. -/
theorem distanceEnergy_le_n_mul_degreeSquareMass
    {n : ℕ} (p : Config n) :
    DistanceEnergy p ≤ n * DistanceDegreeSquareMass p := by
  unfold DistanceEnergy DistanceDegreeSquareMass
  calc
    ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r ^ 2 ≤
        ∑ r ∈ OrderedDistanceValues p,
          n * ∑ i, (DistanceOutNeighborsAtValue p i r).card ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro r _hr
      have hcs :
          (∑ i, (DistanceOutNeighborsAtValue p i r).card) ^ 2 ≤
            (Finset.univ : Finset (Fin n)).card *
              ∑ i, (DistanceOutNeighborsAtValue p i r).card ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      rw [← orderedMultiplicity_eq_sum_outNeighbor_card,
        Finset.card_univ, Fintype.card_fin] at hcs
      exact hcs
    _ = n * ∑ r ∈ OrderedDistanceValues p,
        ∑ i, (DistanceOutNeighborsAtValue p i r).card ^ 2 := by
      rw [Finset.mul_sum]

/-- Ordered witness total plus ordered witness defect is twice the number of
ordered off-diagonal base pairs. -/
theorem orderedPairWitnessTotal_add_defect_eq_two_mul_pairMass
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) :
    OrderedPairWitnessTotal p + OrderedPairWitnessDefect p =
      2 * (n * (n - 1)) := by
  unfold OrderedPairWitnessTotal OrderedPairWitnessDefect
  rw [← Finset.sum_add_distrib]
  calc
    ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        ((IndexedEquidistantWitnesses p ij.1 ij.2).card +
          (2 - (IndexedEquidistantWitnesses p ij.1 ij.2).card)) =
        ∑ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag, 2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [Finset.mem_offDiag] at hij
      exact Nat.add_sub_of_le
        (indexedEquidistantWitnesses_card_le_two hp hgp hij.2.2)
    _ = 2 * ((Finset.univ : Finset (Fin n)).offDiag).card := by
      simp [Finset.sum_const, mul_comm]
    _ = 2 * (n * (n - 1)) := by
      congr 1
      rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      cases n with
      | zero => simp
      | succ k => simp [Nat.mul_succ]

/-- Concrete ordered normalization of the energy/cherry defect inequality:
energy plus `n` times the pair-witness defect is at most the exact cap. -/
theorem distanceEnergy_add_n_mul_pairWitnessDefect_le_exactCap
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p + n * OrderedPairWitnessDefect p ≤
      3 * n ^ 2 * (n - 1) := by
  have henergy := distanceEnergy_le_n_mul_degreeSquareMass p
  have hsquare := distanceDegreeSquareMass_eq_falling_add_mass p
  have hfalling := distanceDegreeFallingMass_eq_orderedPairWitnessTotal hp
  have hpairs := orderedPairWitnessTotal_add_defect_eq_two_mul_pairMass hp hgp
  calc
    DistanceEnergy p + n * OrderedPairWitnessDefect p ≤
        n * DistanceDegreeSquareMass p +
          n * OrderedPairWitnessDefect p := Nat.add_le_add_right henergy _
    _ = n * (OrderedPairWitnessTotal p + OrderedPairWitnessDefect p +
        OrderedDistanceMass p) := by rw [hsquare, hfalling]; ring
    _ = n * (2 * (n * (n - 1)) + OrderedDistanceMass p) := by rw [hpairs]
    _ = n * (2 * (n * (n - 1)) + n * (n - 1)) := by
      rw [orderedDistanceMass_eq_n_mul_pred]
    _ = 3 * n ^ 2 * (n - 1) := by ring

/-- Near-cap energy bounds total pair-witness defect. -/
theorem n_mul_pairWitnessDefect_le_of_near_cap
    {n delta : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    n * OrderedPairWitnessDefect p ≤ delta := by
  have hupper := distanceEnergy_add_n_mul_pairWitnessDefect_le_exactCap hp hgp
  omega

/-- Explicit SR1 pair-witness cleanup. Ordered base pairs with witness defect
at least `threshold` are bounded in division-free product form. -/
theorem n_mul_threshold_mul_exceptionalPair_count_le_of_near_cap
    {n delta threshold : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    n * threshold * (ExceptionalOrderedPairsByWitnessDefect p threshold).card ≤
      delta := by
  have hcount := threshold_mul_exceptionalOrderedPair_count_le_witnessDefect
    p threshold
  calc
    n * threshold * (ExceptionalOrderedPairsByWitnessDefect p threshold).card =
        n * (threshold *
          (ExceptionalOrderedPairsByWitnessDefect p threshold).card) := by ring
    _ ≤ n * OrderedPairWitnessDefect p := Nat.mul_le_mul_left n hcount
    _ ≤ delta := n_mul_pairWitnessDefect_le_of_near_cap hp hgp hnear

/-- Ordered base pairs that do not have exactly two equidistant witnesses. -/
noncomputable def BadOrderedPairsByWitnessCount {n : ℕ}
    (p : Config n) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag.filter
    (fun ij => (IndexedEquidistantWitnesses p ij.1 ij.2).card ≠ 2)

/-- Under the cherry cap, non-two-regular ordered pairs are exactly the pairs
with witness defect at least one. -/
theorem badOrderedPairsByWitnessCount_eq_exceptional_one
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) :
    BadOrderedPairsByWitnessCount p =
      ExceptionalOrderedPairsByWitnessDefect p 1 := by
  classical
  ext ij
  simp only [BadOrderedPairsByWitnessCount,
    ExceptionalOrderedPairsByWitnessDefect, Finset.mem_filter]
  constructor
  · rintro ⟨hijmem, hne⟩
    refine ⟨hijmem, ?_⟩
    rw [Finset.mem_offDiag] at hijmem
    have hle := indexedEquidistantWitnesses_card_le_two hp hgp hijmem.2.2
    omega
  · rintro ⟨hijmem, hdefect⟩
    refine ⟨hijmem, ?_⟩
    omega

/-- Near the energy cap, all but at most `delta/n` ordered base pairs have
exactly two witnesses, stated without division. -/
theorem n_mul_badOrderedPair_count_le_of_near_cap
    {n delta : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    n * (BadOrderedPairsByWitnessCount p).card ≤ delta := by
  have h := n_mul_threshold_mul_exceptionalPair_count_le_of_near_cap
    hp hgp hnear (threshold := 1)
  rw [← badOrderedPairsByWitnessCount_eq_exceptional_one hp hgp] at h
  simpa using h

/-- Bundled division-free SR1 cleanup theorem. Near-cap energy simultaneously
controls underfull-class pair mass, missing local degree incidences in rich
classes, vertices with large rich-class degree defect, and ordered pairs that
are not cherry-2-regular. The thresholds remain explicit so downstream
asymptotic packaging can choose their scale. -/
theorem nearCap_stability_product_bounds
    {n delta underfullThreshold classThreshold vertexThreshold : ℕ}
    {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hnear : 3 * n ^ 2 * (n - 1) ≤ DistanceEnergy p + delta) :
    underfullThreshold * MultiplicityMass
        ((OrderedDistanceValues p).filter
          (fun r => underfullThreshold ≤ 3 * n - OrderedMultiplicity p r))
        (OrderedMultiplicity p) ≤ delta ∧
      classThreshold *
        (∑ r ∈ (OrderedDistanceValues p).filter
          (fun r => classThreshold ≤ OrderedMultiplicity p r),
          DistanceLocalDegreeDefect p r) ≤ delta ∧
      classThreshold * vertexThreshold *
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => vertexThreshold ≤
            RichDistanceVertexDegreeDefect p classThreshold i)).card ≤ delta ∧
      n * (BadOrderedPairsByWitnessCount p).card ≤ delta := by
  exact ⟨
    threshold_mul_underfullDistanceMass_le_of_near_cap hp hgp hnear,
    threshold_mul_richDistanceLocalDegreeDefect_le_of_near_cap hp hgp hnear,
    richDistance_exceptionalVertex_count_product_le_of_near_cap hp hgp hnear,
    n_mul_badOrderedPair_count_le_of_near_cap hp hgp hnear⟩

/-- If a nonnegative integer witness count is bounded by `2` at every pair, and
its total count saturates the bound `2 * #pairs`, then every pair has exactly
two witnesses. This is the finite counting core behind the cherry-saturation
diagnostic. -/
theorem all_eq_two_of_sum_eq_two_mul_card
    (s : Finset α) (w : α → ℕ)
    (hle : ∀ a ∈ s, w a ≤ 2)
    (hsum : ∑ a ∈ s, w a = 2 * s.card) :
    ∀ a ∈ s, w a = 2 := by
  exact all_eq_cap_of_sum_eq_cap_mul_card s w 2 hle hsum

/-- If the witness map sends each pair to its two-witness set, then
two-regularity plus injectivity makes the witness map a bijection whenever the
source and target finite sets have the same cardinality. This isolates the
finite combinatorial content of the "witness map is a bijection at saturation"
observation; the geometric proof of injectivity belongs to the perpendicular
bisector layer. -/
theorem witnessMap_bijective_of_injective_of_card_eq
    {pairs witnesses : Type*} [Fintype pairs] [Fintype witnesses]
    (f : pairs → witnesses)
    (hinj : Function.Injective f)
    (hcard : Fintype.card pairs = Fintype.card witnesses) :
    Function.Bijective f := by
  exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩

/-! ## Integer power-probe no-go under a cap -/

/-- Integer power energy `sum m_i^k`. This is the exact finite object behind
integer `p`-energy probes; fractional Renyi monotonicity is not needed for this
cap-only obstruction. -/
def MultiplicityPowerEnergy (s : Finset α) (m : α → ℕ) (k : ℕ) : ℕ :=
  ∑ a ∈ s, (m a) ^ k

/-- Pointwise cap control of integer power energies:
for `1 <= k`, `m_i^k <= B^(k-1) m_i`, hence the whole power-energy probe is
bounded by the same cap-only data. -/
theorem multiplicityPowerEnergy_le_cap_pow_mul_mass
    (s : Finset α) (m : α → ℕ) (B k : ℕ)
    (hk : 1 ≤ k) (hcap : ∀ a ∈ s, m a ≤ B) :
    MultiplicityPowerEnergy s m k ≤ B ^ (k - 1) * MultiplicityMass s m := by
  classical
  unfold MultiplicityPowerEnergy MultiplicityMass
  calc
    ∑ a ∈ s, (m a) ^ k
        ≤ ∑ a ∈ s, B ^ (k - 1) * m a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          cases k with
          | zero => cases hk
          | succ k' =>
              have hpow : (m a) ^ k' ≤ B ^ k' :=
                Nat.pow_le_pow_left (hcap a ha) k'
              calc
                (m a) ^ (Nat.succ k') = (m a) ^ k' * m a := by
                  rw [pow_succ']
                  exact Nat.mul_comm _ _
                _ ≤ B ^ k' * m a := Nat.mul_le_mul_right (m a) hpow
    _ = B ^ (k - 1) * ∑ a ∈ s, m a := by
          rw [Finset.mul_sum]

/-- The same cap-only control for ordered distance multiplicities. -/
theorem distanceMultiplicityPowerEnergy_le_cap_pow_mul_orderedDistanceMass
    {n B k : ℕ} {p : Config n}
    (hk : 1 ≤ k)
    (hcap : ∀ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r ≤ B) :
    MultiplicityPowerEnergy (OrderedDistanceValues p) (OrderedMultiplicity p) k ≤
      B ^ (k - 1) * OrderedDistanceMass p := by
  simpa [OrderedDistanceMass, MultiplicityMass] using
    multiplicityPowerEnergy_le_cap_pow_mul_mass
      (s := OrderedDistanceValues p) (m := OrderedMultiplicity p)
      (B := B) (k := k) hk hcap

/-! ## `K5` twin-opposite algebraic obstruction -/

/-- Algebraic normal form of the `K5` twin-opposite triangle atom. In the
normal form, `h` is half the distance between the two twin vertices, and
`X,Y,Z` are signed coordinates of the three opposite vertices on the
perpendicular bisector. The three equal-length constraints are inconsistent
when `h > 0`.

This theorem is the proof-grade core of the finite atom recorded in
`docs/results/forbidden-subdesign-library.md`. -/
theorem k5_twin_opposite_normal_form_unsat {X Y Z h : ℝ}
    (hh : 0 < h)
    (hYZ : (Y - Z) ^ 2 = h ^ 2 + X ^ 2)
    (hXZ : (X - Z) ^ 2 = h ^ 2 + Y ^ 2)
    (hXY : (X - Y) ^ 2 = h ^ 2 + Z ^ 2) :
    False := by
  have hsub1 : (Y - X) * (X + Y - Z) = 0 := by
    nlinarith [hYZ, hXZ]
  have hsub2 : (Z - Y) * (Y + Z - X) = 0 := by
    nlinarith [hXZ, hXY]
  have hsub3 : (X - Z) * (X + Z - Y) = 0 := by
    nlinarith [hXY, hYZ]
  have hXneY : X ≠ Y := by
    intro hxy
    have : 0 = h ^ 2 + Z ^ 2 := by
      simpa [hxy] using hXY
    have hsq_pos : 0 < h ^ 2 + Z ^ 2 := by nlinarith [sq_nonneg Z, sq_pos_of_pos hh]
    nlinarith
  have hYneZ : Y ≠ Z := by
    intro hyz
    have : 0 = h ^ 2 + X ^ 2 := by
      simpa [hyz] using hYZ
    have hsq_pos : 0 < h ^ 2 + X ^ 2 := by nlinarith [sq_nonneg X, sq_pos_of_pos hh]
    nlinarith
  have hXneZ : X ≠ Z := by
    intro hxz
    have : 0 = h ^ 2 + Y ^ 2 := by
      simpa [hxz] using hXZ
    have hsq_pos : 0 < h ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg Y, sq_pos_of_pos hh]
    nlinarith
  have hz_eq : Z = X + Y := by
    have hfirst : Y - X ≠ 0 := by
      intro hzero
      exact hXneY (by nlinarith)
    have hsecond : X + Y - Z = 0 := (mul_eq_zero.mp hsub1).resolve_left hfirst
    nlinarith
  have hx_eq : X = Y + Z := by
    have hfirst : Z - Y ≠ 0 := by
      intro hzero
      exact hYneZ (by nlinarith)
    have hsecond : Y + Z - X = 0 := (mul_eq_zero.mp hsub2).resolve_left hfirst
    nlinarith
  have hy_eq : Y = X + Z := by
    have hfirst : X - Z ≠ 0 := by
      intro hzero
      exact hXneZ (by nlinarith)
    have hsecond : X + Z - Y = 0 := (mul_eq_zero.mp hsub3).resolve_left hfirst
    nlinarith
  have hX0 : X = 0 := by nlinarith
  have hY0 : Y = 0 := by nlinarith
  have hZ0 : Z = 0 := by nlinarith
  have : 0 = h ^ 2 := by
    simpa [hX0, hY0, hZ0] using hYZ
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  nlinarith

end Esgk
