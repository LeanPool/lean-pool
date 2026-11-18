/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module
public import LeanPool.DistinctDistances.Energy
public import LeanPool.DistinctDistances.CauchyEnergy
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The elementary `O(n³)` energy ceiling under no-four-cocircular — (E1)/(E2)

PROVEN, sorry-free, Guth–Katz-free. Under `InGeneralPosition` (in particular its
no-four-cocircular clause), every ordered distance multiplicity is at most `3n`
((E1), `orderedMultiplicity_le_three_mul`), hence the ordered distance energy
`DistanceEnergy p = Σ_r m_r²` is at most `3n³` ((E2),
`distanceEnergy_le_three_mul_cube`).

**Honest framing.** This is the *trivial ceiling*: via Cauchy–Schwarz it yields
only `D = Ω(n)`, with leading constant near `1/3` in ordered normalization.
It does not prove the active `FixedLinearDistanceEnergyGapStatement` for
arbitrary fixed `A`; it only supplies the reference saturation edge. It removes
the Guth–Katz `log` elementarily — the `log` is a cocircularity artifact.

The "hard geometry" is the hypothesis itself: four points at a common distance
`r` from a center `c` are `Cospherical` (witness `⟨c, r⟩`), so the
no-four-cocircular clause forbids a fourth. No imported geometry beyond Mathlib's
`Cospherical`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open Filter

variable {n : ℕ}

open Classical in
/-- (E1), geometric core: at most three points of a general-position configuration
lie at any fixed distance `r` from any center `c`. A fourth would exhibit four
cocircular points (`Cospherical` with center `c`, radius `r`), contradicting the
no-four-cocircular clause of `InGeneralPosition`. -/
theorem fixedDistance_card_le_three {p : Config n}
    (hgp : InGeneralPosition (Config.toFinset p)) (c : Point) (r : ℝ) :
    ((Config.toFinset p).filter (fun x ↦ dist x c = r)).card ≤ 3 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (s := (Config.toFinset p).filter (fun x ↦ dist x c = r)) (n := 4) (by omega)
  have hTX : T ⊆ Config.toFinset p := hTsub.trans (Finset.filter_subset _ _)
  have hcos : Cospherical (SetLike.coe T) := by
    refine ⟨c, r, ?_⟩
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    have hxf := hTsub hxT
    rw [Finset.mem_filter] at hxf
    exact hxf.2
  exact hgp.2 T hTX hTcard hcos

/-- (E1), summed form: each ordered distance multiplicity is at most `3n` in an
injective general-position configuration. The injection `(i,j) ↦ ⟨i, p j⟩` maps
the `(i,j)` pairs at distance `r` into `⨆ i, {x ∈ P : dist x (p i) = r}`, whose
each fiber has `≤ 3` points by `fixedDistance_card_le_three`. -/
theorem orderedMultiplicity_le_three_mul {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) (r : ℝ) :
    OrderedMultiplicity p r ≤ 3 * n := by
  classical
  -- target multiset of (index, point) records, fibered over the first index
  set S : Finset (Σ _ : Fin n, Point) :=
    Finset.univ.sigma (fun i => (Config.toFinset p).filter (fun x => dist x (p i) = r)) with hS
  have hcard_le : OrderedMultiplicity p r ≤ S.card := by
    unfold OrderedMultiplicity
    refine Finset.card_le_card_of_injOn (fun ij => ⟨ij.1, p ij.2⟩) ?_ ?_
    · intro ij hij
      simp only [Finset.mem_coe, Finset.mem_filter] at hij
      obtain ⟨_, hne, hdist⟩ := hij
      simp only [Finset.mem_coe, hS, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        true_and]
      exact ⟨Finset.mem_image.mpr ⟨ij.2, Finset.mem_univ _, rfl⟩, by rw [dist_comm]; exact hdist⟩
    · intro a ha b hb hab
      simp only [Sigma.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      have h2' : p a.2 = p b.2 := eq_of_heq h2
      exact Prod.ext h1 (hp h2')
  have hScard : S.card ≤ 3 * n := by
    rw [hS, Finset.card_sigma]
    calc ∑ i, ((Config.toFinset p).filter (fun x => dist x (p i) = r)).card
        ≤ ∑ _i : Fin n, 3 := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact fixedDistance_card_le_three hgp (p i) r
      _ = 3 * n := by simp [Finset.sum_const, mul_comm]
  exact hcard_le.trans hScard

/-- The total ordered off-diagonal pair count, partitioned by realized distance,
is at most `n²`: `Σ_r m_r = #{(i,j) : i ≠ j} ≤ n²`. -/
theorem sum_orderedMultiplicity_le {p : Config n} :
    ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r ≤ n ^ 2 := by
  classical
  set D : Finset (Fin n × Fin n) :=
    (Finset.univ.product Finset.univ).filter (fun ij => ij.1 ≠ ij.2) with hD
  have hfib : ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = D.card := by
    rw [Finset.card_eq_sum_card_fiberwise
        (f := fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
        (t := OrderedDistanceValues p) ?_]
    · refine Finset.sum_congr rfl ?_
      intro r _
      unfold OrderedMultiplicity
      congr 1
      rw [hD, Finset.filter_filter]
    · intro ij hij
      simp only [Finset.mem_coe, hD, Finset.mem_filter] at hij
      exact Finset.mem_image.mpr ⟨ij, Finset.mem_filter.mpr ⟨hij.1, hij.2⟩, rfl⟩
  rw [hfib]
  calc D.card ≤ (Finset.univ.product Finset.univ : Finset (Fin n × Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n ^ 2 := by
        simp [Finset.product_eq_sprod, Finset.card_univ, Fintype.card_fin, pow_two]

/-- (E2): the ordered distance energy is at most `3n³` for an injective
general-position configuration. Combines (E1) `m_r ≤ 3n` with
`Σ_r m_r² ≤ (max_r m_r)·Σ_r m_r ≤ 3n·n²`. -/
theorem distanceEnergy_le_three_mul_cube {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    DistanceEnergy p ≤ 3 * n ^ 3 := by
  classical
  have hpt : ∀ r ∈ OrderedDistanceValues p,
      (OrderedMultiplicity p r) ^ 2 ≤ 3 * n * OrderedMultiplicity p r := by
    intro r _
    have h1 := orderedMultiplicity_le_three_mul hp hgp r
    calc (OrderedMultiplicity p r) ^ 2
        = OrderedMultiplicity p r * OrderedMultiplicity p r := by ring
      _ ≤ (3 * n) * OrderedMultiplicity p r := Nat.mul_le_mul h1 le_rfl
  calc DistanceEnergy p
      = ∑ r ∈ OrderedDistanceValues p, (OrderedMultiplicity p r) ^ 2 := rfl
    _ ≤ ∑ r ∈ OrderedDistanceValues p, 3 * n * OrderedMultiplicity p r :=
        Finset.sum_le_sum hpt
    _ = 3 * n * ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r := by
        rw [Finset.mul_sum]
    _ ≤ 3 * n * n ^ 2 := Nat.mul_le_mul le_rfl sum_orderedMultiplicity_le
    _ = 3 * n ^ 3 := by ring

/-- Real-valued restatement of (E2): `(E_dist : ℝ) ≤ 3·n³`. This is the explicit
`O(n³)` ceiling. It neither proves the active fixed-`A` energy gap for arbitrary
`A` nor the stronger legacy universal `o(n³)` target. -/
theorem distanceEnergy_le_three_mul_cube_real {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    (DistanceEnergy p : ℝ) ≤ 3 * (n : ℝ) ^ 3 := by
  have h := distanceEnergy_le_three_mul_cube hp hgp
  have := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at this
  linarith

/-- Cauchy–Schwarz capstone: the `O(n³)` energy ceiling forces only `D = Ω(n)`.
Concretely `(n(n-1))² ≤ 3n³ · D` — i.e. `D ≳ (n-1)²/(3n) = Ω(n)`, the **trivial**
distinct-distance bound. This is the entire energy mechanism made formal: an
*upper* bound on `E` yields a *lower* bound on `D` via `energy_lower_bound_of_few_distances`.
It is emphatically **not** superlinear. The active route to `D = ω(n)` is the
counterexample-local `FixedLinearDistanceEnergyGapStatement`; universal
`E = o(n³)` would be sufficient but is no longer required. The ceiling is
reached, not beaten. -/
theorem numDistances_ge_of_ceiling {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) :
    (n * (n - 1)) ^ 2 ≤ 3 * n ^ 3 * NumDistances p := by
  have hCS := energy_lower_bound_of_few_distances p
  have hE := distanceEnergy_le_three_mul_cube hp hgp
  have hbridge := numDistances_eq_numDistancesOrdered_of_injective hp
  calc (n * (n - 1)) ^ 2
      ≤ NumDistancesOrdered p * DistanceEnergy p := hCS
    _ ≤ NumDistancesOrdered p * (3 * n ^ 3) := Nat.mul_le_mul le_rfl hE
    _ = 3 * n ^ 3 * NumDistancesOrdered p := by ring
    _ = 3 * n ^ 3 * NumDistances p := by rw [← hbridge]

/-- The elementary cubic ceiling already settles the fixed-`A` Problem 98
conclusion for every `A < 1/3`: every sufficiently large injective
general-position configuration has more than `A n` distinct distances. The
remaining active problem is to pass the `1/3` edge and then handle arbitrary
fixed `A`. -/
theorem eventually_numDistances_gt_linear_of_lt_one_third
    (A : ℝ) (hA : A < 1 / 3) :
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        InGeneralPosition (Config.toFinset p) →
        A * (n : ℝ) < (NumDistances p : ℝ) := by
  have hcoef : 0 < 1 - 3 * A := by linarith
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 < (1 - 3 * A) * (n : ℝ) := by
    have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hscaled : Filter.Tendsto (fun n : ℕ ↦ (1 - 3 * A) * (n : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_const_mul_atTop_of_pos hcoef).mpr hnat
    exact hscaled.eventually (Filter.eventually_gt_atTop 2)
  filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with n hnLarge hnPos
  intro p hp hgp
  by_contra hnot
  have hD : (NumDistances p : ℝ) ≤ A * (n : ℝ) := le_of_not_gt hnot
  have hceilingNat := numDistances_ge_of_ceiling hp hgp
  have hceiling := (Nat.cast_le (α := ℝ)).mpr hceilingNat
  push_cast at hceiling
  have hnOne : 1 ≤ n := by omega
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hnOne]
    norm_num
  rw [hpred] at hceiling
  have hupper : 3 * (n : ℝ) ^ 3 * (NumDistances p : ℝ) ≤
      3 * (n : ℝ) ^ 3 * (A * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hnRealPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnPos
  have hpoly : 3 * (n : ℝ) ^ 3 * (A * (n : ℝ)) <
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 := by
    apply sub_pos.mp
    calc
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 -
            3 * (n : ℝ) ^ 3 * (A * (n : ℝ)) =
          (n : ℝ) ^ 2 *
            ((n : ℝ) * ((1 - 3 * A) * (n : ℝ) - 2) + 1) := by ring
      _ > 0 := by positivity
  exact (not_lt_of_ge hceiling) (hupper.trans_lt hpoly)

end Esgk
