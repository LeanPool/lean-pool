/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.GP4OrderedSquaredDistanceLedger
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A centroid annulus from a nearly saturated distance palette

Formalizes §3.1 of `docs/results/nonquantitative-route-assessment-2026-10-06.md`.
The geometric input is injectivity and no four cocircular points. The result
holds at every vertex. The final lower bound includes its vacuous regime.
This is a stability theorem, not a stronger distinct-distance lower bound.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- The total squared distance to the configuration centroid. -/
noncomputable def centroidSquaredMass (p : Config n) : ℝ :=
  ∑ i, dist (p i) (configCentroid p) ^ 2

/-- The squared radius furnished by the common palette capacity. -/
noncomputable def distanceAnnulusRadiusSq (p : Config n) : ℝ :=
  (3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p) / (n : ℝ)

/-- The nonnegative radius furnished by the common palette capacity. -/
noncomputable def distanceAnnulusRadius (p : Config n) : ℝ :=
  Real.sqrt (distanceAnnulusRadiusSq p)

/-- The configuration translated by its centroid has vector sum zero. -/
lemma sum_sub_configCentroid (p : Config n) (hn : 0 < n) :
    ∑ i, (p i - configCentroid p) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, configCentroid, smul_smul,
    mul_inv_cancel₀ hn0, one_smul, sub_self]

/-- The squared-distance row identity with its exact centroid offset. -/
lemma sum_sqDistance_eq_centroid (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * dist (p i) (configCentroid p) ^ 2 + centroidSquaredMass p := by
  have h := sum_sqDistance_expand (fun j ↦ p j - configCentroid p) i
  rw [sum_sub_configCentroid p hn, inner_zero_right, mul_zero, sub_zero] at h
  simpa only [dist_sub_right, ← dist_eq_norm, centroidSquaredMass] using h

/-- The missing degree at every vertex over the global palette is exactly
`3*D - n + 1`, in real arithmetic (including unrealized local distances). -/
lemma sum_distanceDegreeDeficit (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) =
        3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
  have hdeg := distanceDegreeProfile_sum_eq_pred p i
  have hdegR :
      (∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ)) = (n : ℝ) - 1 := by
    rw [← Nat.cast_sum, hdeg, Nat.cast_sub (by omega)]
    norm_num
  rw [Finset.sum_sub_distrib, hdegR]
  simp only [Finset.sum_const, nsmul_eq_mul, NumDistancesOrdered]
  ring

/-- The weighted missing-degree sum is the difference between palette
capacity and the actual squared-distance row. -/
lemma sum_weighted_distanceDegreeDeficit (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 =
        3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) -
          ∑ j, dist (p i) (p j) ^ 2 := by
  rw [sum_sqDistance_eq_sum_outDegree_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Exact weighted missing-degree bound for any upper bound on squared
distances and any bound on the unweighted deficit. -/
lemma weighted_distanceDegreeDeficit_le {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {B q : ℝ} (hB : 0 ≤ B)
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ B)
    (hq : 3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 ≤ q)
    (i : Fin n) :
    (∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2) ≤ q * B := by
  calc
    _ ≤ ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * B := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left (hpal r hr)
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 :=
        by exact_mod_cast hcap i r
      linarith
    _ = (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) * B := by
      rw [← Finset.sum_mul, sum_distanceDegreeDeficit p hn i]
    _ ≤ q * B := mul_le_mul_of_nonneg_right hq hB

/-- Under a degree cap of three, the squared annulus radius is nonnegative
and bounds every centroid radius from above. -/
lemma distanceAnnulusRadiusSq_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadiusSq p ∧
      ∀ i, dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper (i : Fin n) :
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
    have hdef : 0 ≤ ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 := by
      apply Finset.sum_nonneg
      intro r _hr
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 :=
        by exact_mod_cast hcap i r
      exact mul_nonneg (by linarith) (sq_nonneg r)
    rw [sum_weighted_distanceDegreeDeficit, sum_sqDistance_eq_centroid p hn i] at hdef
    unfold distanceAnnulusRadiusSq
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  let i0 : Fin n := ⟨0, hn⟩
  exact ⟨(sq_nonneg _).trans (hupper i0), hupper⟩

/-- The annulus radius is nonnegative and dominates every centroid distance. -/
lemma distanceAnnulusRadius_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadius p ∧
      distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p ∧
        ∀ i, dist (p i) (configCentroid p) ≤ distanceAnnulusRadius p := by
  obtain ⟨hR, hupper⟩ := distanceAnnulusRadiusSq_bounds hn hcap
  have hρ : 0 ≤ distanceAnnulusRadius p := Real.sqrt_nonneg _
  have hsq : distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p :=
    Real.sq_sqrt hR
  refine ⟨hρ, hsq, ?_⟩
  intro i
  have hd := dist_nonneg (x := p i) (y := configCentroid p)
  have hi := hupper i
  nlinarith

/-- All squared palette distances are bounded by four times the squared
annulus radius. This replaces a separate diameter definition. -/
lemma palette_sq_le_four_mul_distanceAnnulusRadiusSq {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {r : ℝ} (hr : r ∈ OrderedDistanceValues p) :
    r ^ 2 ≤ 4 * distanceAnnulusRadiusSq p := by
  obtain ⟨hρ, hsq, hupper⟩ := distanceAnnulusRadius_bounds hn hcap
  rw [OrderedDistanceValues, Finset.mem_image] at hr
  obtain ⟨⟨i, j⟩, _hij, hdist⟩ := hr
  have ht := dist_triangle (p i) (configCentroid p) (p j)
  rw [dist_comm (configCentroid p) (p j)] at ht
  have hi := hupper i
  have hj := hupper j
  have hd := dist_nonneg (x := p i) (y := p j)
  have hle : dist (p i) (p j) ≤ 2 * distanceAnnulusRadius p := by linarith
  have hsqle := mul_self_le_mul_self hd hle
  nlinarith [hdist]

/-- The exact deficit form of the squared annulus estimate. -/
theorem centroid_sq_ge_distanceAnnulusRadiusSq_mul_deficit {p : Config n}
    (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (i : Fin n) :
    distanceAnnulusRadiusSq p *
        (1 - 4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) / (n : ℝ)) ≤
      dist (p i) (configCentroid p) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR := (distanceAnnulusRadiusSq_bounds hn hcap).1
  have hdef := weighted_distanceDegreeDeficit_le hn hcap
    (B := 4 * distanceAnnulusRadiusSq p) (by positivity)
    (fun _ hr ↦ palette_sq_le_four_mul_distanceAnnulusRadiusSq hn hcap hr) le_rfl i
  rw [sum_weighted_distanceDegreeDeficit, sum_sqDistance_eq_centroid p hn i] at hdef
  have hRadius : (n : ℝ) * distanceAnnulusRadiusSq p =
      3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p := by
    unfold distanceAnnulusRadiusSq
    field_simp
  convert (show
      ((n : ℝ) * distanceAnnulusRadiusSq p -
        4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) *
          distanceAnnulusRadiusSq p) / (n : ℝ) ≤
      dist (p i) (configCentroid p) ^ 2 from
        (div_le_iff₀ hnR).mpr (by nlinarith)) using 1
  field_simp

/-- Squared annulus estimate from the actual distinct-distance hypothesis,
with raw no-four-cocircularity and no no-three-collinear assumption. -/
theorem thin_annulus_sq_of_noFourCocircular {p : Config n}
    (hp : Function.Injective p)
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 0 < n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ)) :
    ∀ i, distanceAnnulusRadiusSq p * (1 - 12 * δ - 4 / (n : ℝ)) ≤
        dist (p i) (configCentroid p) ^ 2 ∧
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4
  obtain ⟨hR, hupper⟩ := distanceAnnulusRadiusSq_bounds hn hcap
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD' := hD
  rw [numDistances_eq_numDistancesOrdered_of_injective hp] at hD'
  have hc : 1 - 12 * δ - 4 / (n : ℝ) ≤
      1 - 4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) / (n : ℝ) := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    field_simp
    nlinarith
  intro i
  exact ⟨(mul_le_mul_of_nonneg_left hc hR).trans
    (centroid_sq_ge_distanceAnnulusRadiusSq_mul_deficit hn hcap i), hupper i⟩

/-- The square-comparison step, including the regime where the lower bound
is nonpositive. It never takes a square root of `1-x` for `x>1`. -/
lemma annulus_linear_lower_bound {ρ t x : ℝ}
    (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (hsq : ρ ^ 2 * (1 - x) ≤ t ^ 2) :
    ρ * (1 - x) ≤ t := by
  by_cases hx1 : x ≤ 1
  · have ha : 0 ≤ ρ * (1 - x) := mul_nonneg hρ (by linarith)
    have hxprod : 0 ≤ x * (1 - x) := mul_nonneg hx (by linarith)
    have hsq' : (ρ * (1 - x)) ^ 2 ≤ t ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg ρ) hxprod]
    nlinarith
  · have ha : ρ * (1 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ (by linarith)
    exact ha.trans ht

/-- Every point lies in the stated centroid annulus. This theorem includes
singletons and the vacuous lower-bound regime `12*δ + 4/n > 1`. -/
theorem thin_annulus_of_noFourCocircular {p : Config n}
    (hp : Function.Injective p)
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 0 < n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ)) :
    ∀ i, distanceAnnulusRadius p * (1 - 12 * δ - 4 / (n : ℝ)) ≤
        dist (p i) (configCentroid p) ∧
      dist (p i) (configCentroid p) ≤ distanceAnnulusRadius p := by
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4
  obtain ⟨hρ, hsq, hupper⟩ := distanceAnnulusRadius_bounds hn hcap
  have hs := thin_annulus_sq_of_noFourCocircular hp hgp4 hn hD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 ≤ 3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
    rw [← sum_distanceDegreeDeficit p hn ⟨0, hn⟩]
    apply Finset.sum_nonneg
    intro r _hr
    have hc : ((DistanceOutNeighborsAtValue p ⟨0, hn⟩ r).card : ℝ) ≤ 3 :=
      by exact_mod_cast hcap ⟨0, hn⟩ r
    linarith
  have hD' := hD
  rw [numDistances_eq_numDistancesOrdered_of_injective hp] at hD'
  have hx : 0 ≤ 12 * δ + 4 / (n : ℝ) := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    field_simp
    nlinarith
  intro i
  refine ⟨?_, hupper i⟩
  have hi := (hs i).1
  rw [← hsq] at hi
  have hl := annulus_linear_lower_bound hρ
    (dist_nonneg (x := p i) (y := configCentroid p))
    (x := 12 * δ + 4 / (n : ℝ)) hx (by nlinarith [hi])
  nlinarith

/-- An injective configuration with at least two points has positive annulus
radius under the degree cap. This justifies radius normalization. -/
theorem distanceAnnulusRadius_pos {p : Config n} (hp : Function.Injective p)
    (hn : 2 ≤ n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 < distanceAnnulusRadius p := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  have hdist : 0 < dist (p i0) (p i1) :=
    dist_pos.mpr (fun h ↦ hi (hp h))
  have hb := (distanceAnnulusRadius_bounds (by omega : 0 < n) hcap).2.2
  have ht := dist_triangle (p i0) (configCentroid p) (p i1)
  rw [dist_comm (configCentroid p) (p i1)] at ht
  have h0 := hb i0
  have h1 := hb i1
  linarith

/-- General-position specialization of the raw GP4 annulus theorem. -/
theorem thin_annulus_of_generalPosition {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 0 < n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ)) :
    ∀ i, distanceAnnulusRadius p * (1 - 12 * δ - 4 / (n : ℝ)) ≤
        dist (p i) (configCentroid p) ∧
      dist (p i) (configCentroid p) ≤ distanceAnnulusRadius p :=
  thin_annulus_of_noFourCocircular hp hgp.2 hn hD

end Esgk
