/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.DistanceNormalForm
public import Mathlib.Tactic.NormNum

/-!
# Heavy distance classes as bounded-degree graph designs

This module carries out Step 2 of `docs/plans/d7.2-exact-emptiness-plan.md`: convert
heavy distance values into ordered edge sets on `Fin n` and record the basic
properties supplied by the distance normal form plus general position.

The key output is not a D7.2 proof. It is the precise interface D7.2 must act
on: many equal-distance ordered-edge classes, each with linear ordered edge
count and out-degree at most `3`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ} {α : Type*}

/-- If every term is at most `cap` and their sum reaches
`cap * #terms`, then every term equals `cap`. -/
theorem all_eq_cap_of_sum_eq_cap_mul_card
    (s : Finset α) (m : α → ℕ) (cap : ℕ)
    (hcap : ∀ a ∈ s, m a ≤ cap)
    (heq : ∑ a ∈ s, m a = cap * s.card) :
    ∀ a ∈ s, m a = cap := by
  classical
  intro a ha
  by_contra hne
  have hlt : m a < cap := Nat.lt_of_le_of_ne (hcap a ha) hne
  have hstrict : ∑ x ∈ s, m x < ∑ _x ∈ s, cap := by
    refine Finset.sum_lt_sum hcap ⟨a, ha, hlt⟩
  have hcap_sum : ∑ _x ∈ s, cap = cap * s.card := by
    simp [Finset.sum_const, mul_comm]
  rw [heq, hcap_sum] at hstrict
  exact (lt_irrefl _) hstrict

/-- Ordered edges realizing a fixed distance value `r`. -/
noncomputable def DistanceEdgesAtValue {n : ℕ} (p : Config n) (r : ℝ) :
    Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter
    (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)

/-- Out-neighbors of one vertex at a fixed distance value `r`. -/
noncomputable def DistanceOutNeighborsAtValue {n : ℕ} (p : Config n) (i : Fin n) (r : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => i ≠ j ∧ dist (p i) (p j) = r)

/-- The edge-set cardinality is exactly the ordered distance multiplicity. -/
theorem distanceEdgesAtValue_card (p : Config n) (r : ℝ) :
    (DistanceEdgesAtValue p r).card = OrderedMultiplicity p r := by
  rfl

/-- Ordered multiplicity is the sum of the fixed-distance out-degrees over all
vertices. This is the exact degree-sum bridge for one distance graph. -/
theorem orderedMultiplicity_eq_sum_outNeighbor_card (p : Config n) (r : ℝ) :
    OrderedMultiplicity p r =
      ∑ i, (DistanceOutNeighborsAtValue p i r).card := by
  classical
  unfold OrderedMultiplicity DistanceOutNeighborsAtValue
  simp_rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_filter]

/-- The total ordered distance mass is exactly the number of ordered
off-diagonal pairs. This holds without injectivity: coincident indexed points
contribute to the distance-zero fiber. -/
theorem orderedDistanceMass_eq_n_mul_pred (p : Config n) :
    OrderedDistanceMass p = n * (n - 1) := by
  classical
  set T : Finset (Fin n × Fin n) :=
    (Finset.univ.product Finset.univ).filter
      (fun ij : Fin n × Fin n => ij.1 ≠ ij.2) with hT
  set f : Fin n × Fin n → ℝ :=
    fun ij => dist (p ij.1) (p ij.2) with hf
  have hTcard : T.card = n * (n - 1) := by
    have h1 : T = (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨i, j⟩
      simp [T, Finset.mem_offDiag]
    have h2 : ((Finset.univ : Finset (Fin n)).offDiag).card =
        (Finset.univ : Finset (Fin n)).card *
          (Finset.univ : Finset (Fin n)).card -
          (Finset.univ : Finset (Fin n)).card := by
      exact Finset.offDiag_card _
    rw [h1, h2, Finset.card_univ, Fintype.card_fin]
    cases n with
    | zero => simp
    | succ k => simp [Nat.mul_succ]
  have hMult : ∀ r : ℝ,
      OrderedMultiplicity p r =
        (T.filter (fun ij => f ij = r)).card := by
    intro r
    unfold OrderedMultiplicity
    rw [show T = (Finset.univ.product Finset.univ).filter
      (fun ij : Fin n × Fin n => ij.1 ≠ ij.2) from rfl,
      Finset.filter_filter]
  have hVals : OrderedDistanceValues p = T.image f := rfl
  unfold OrderedDistanceMass
  rw [hVals]
  simp_rw [hMult]
  have hsum : ∑ r ∈ T.image f, (T.filter (fun ij => f ij = r)).card =
      T.card := (Finset.card_eq_sum_card_image f T).symm
  exact hsum.trans hTcard

/-- Every value in `OrderedDistanceValues` has positive ordered
multiplicity. -/
theorem orderedMultiplicity_pos_of_mem {p : Config n} {r : ℝ}
    (hr : r ∈ OrderedDistanceValues p) :
    0 < OrderedMultiplicity p r := by
  classical
  rw [OrderedDistanceValues, Finset.mem_image] at hr
  obtain ⟨ij, hij, hdist⟩ := hr
  rw [Finset.mem_filter] at hij
  unfold OrderedMultiplicity
  apply Finset.card_pos.mpr
  refine ⟨ij, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hij.1, hij.2, hdist⟩

/-- A heavy distance value has at least `K` ordered edges. -/
theorem heavyDistanceValue_card_ge_threshold {p : Config n} {K : ℕ} {r : ℝ}
    (hr : r ∈ HeavyDistanceValues p K) :
    K ≤ (DistanceEdgesAtValue p r).card := by
  rw [distanceEdgesAtValue_card]
  exact (Finset.mem_filter.mp hr).2

/-- General position bounds the out-degree of every fixed-distance graph by
`3`: four out-neighbors of `i` at the same distance would put four points on a
circle centered at `p i`. -/
theorem distanceOutNeighborsAtValue_card_le_three {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (i : Fin n) (r : ℝ) :
    (DistanceOutNeighborsAtValue p i r).card ≤ 3 := by
  classical
  let S : Finset Point := (Config.toFinset p).filter (fun x => dist x (p i) = r)
  have hcard_le : (DistanceOutNeighborsAtValue p i r).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun j => p j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, DistanceOutNeighborsAtValue, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      obtain ⟨_hne, hdist⟩ := hj
      change p j ∈ (Config.toFinset p).filter (fun x => dist x (p i) = r)
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · rw [dist_comm]
        exact hdist
    · intro _a _ha _b _hb hab
      exact hp hab
  exact hcard_le.trans (fixedDistance_card_le_three hgp (p i) r)

/-- The out-degree bound applies in particular to every heavy distance value. -/
theorem heavyDistanceValue_outDegree_le_three {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    {K : ℕ} {r : ℝ} (_hr : r ∈ HeavyDistanceValues p K) (i : Fin n) :
    (DistanceOutNeighborsAtValue p i r).card ≤ 3 :=
  distanceOutNeighborsAtValue_card_le_three hp hgp i r

/-- Heavy distance mass is the sum of ordered edge-set sizes over the heavy
distance values. -/
theorem heavyDistanceMass_eq_sum_distanceEdgesAtValue_card (p : Config n) (K : ℕ) :
    HeavyDistanceMass p K =
      ∑ r ∈ HeavyDistanceValues p K, (DistanceEdgesAtValue p r).card := by
  unfold HeavyDistanceMass HeavyDistanceValues HeavyMultiplicityMass HeavyMultiplicityClasses
  apply Finset.sum_congr rfl
  intro r _hr
  rw [distanceEdgesAtValue_card]

/-- Branch-A-scale energy, after Step 1's heavy-mass lower bound, forces many
heavy distance values in the precise product form
`(eta/2)*OrderedDistanceMass <= (3*n)*#HeavyDistanceValues`.

This is the Lean version of "divide the heavy mass by the `3n` cap." It avoids
division so downstream users can choose their preferred asymptotic packaging. -/
theorem heavyDistanceValues_card_product_lower_bound_real_of_energy_ge_square
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (hn : 0 < n) (K : ℕ) {eta : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (henergy : eta * ((3 * n : ℕ) : ℝ) * (n : ℝ) ^ 2 ≤
      (DistanceEnergy p : ℝ))
    (hK : (K : ℝ) ≤ eta / 2 * ((3 * n : ℕ) : ℝ)) :
    eta / 2 * (OrderedDistanceMass p : ℝ) ≤
      ((3 * n : ℕ) : ℝ) * ((HeavyDistanceValues p K).card : ℝ) := by
  have hmass_low :=
    heavyDistanceMass_lower_bound_real_of_energy_ge_square
      (p := p) hp hgp hn K heta_nonneg henergy hK
  have hmass_card_nat :=
    heavyDistanceMass_le_three_mul_heavyDistanceValues_card (p := p) hp hgp K
  have hmass_card : (HeavyDistanceMass p K : ℝ) ≤
      ((3 * n : ℕ) : ℝ) * ((HeavyDistanceValues p K).card : ℝ) := by
    exact_mod_cast hmass_card_nat
  exact hmass_low.trans hmass_card

/-- Every complete distance-degree profile has coordinate sum `n - 1`. -/
theorem distanceDegreeProfile_sum_eq_pred (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p i r).card = n - 1 := by
  classical
  let s : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let f : Fin n → ℝ := fun j ↦ dist (p i) (p j)
  have hmaps : ∀ j ∈ s, f j ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [s, Finset.mem_erase, ne_comm] using hj⟩
  have hfiber' :
      ∑ r ∈ OrderedDistanceValues p, (s.filter (fun j ↦ f j = r)).card = s.card := by
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcard : s.card = n - 1 := by
    simp [s, Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← hfiber']
  apply Finset.sum_congr rfl
  intro r _hr
  have hfilter : s.filter (fun j ↦ f j = r) = DistanceOutNeighborsAtValue p i r := by
    ext j
    simp [s, f, DistanceOutNeighborsAtValue, ne_comm]
  rw [hfilter]

end Esgk
