/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.NormalForm
public import LeanPool.DistinctDistances.EnergyCeiling
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Distance-level multiplicity normal form

This module instantiates `Esgk.NormalForm` to the ordered distance
multiplicities used by `DistanceEnergy`. It is Step 1 of
`docs/plans/d7.2-exact-emptiness-plan.md`.

The proved content is bookkeeping plus the existing geometric cap
`OrderedMultiplicity p r <= 3*n` under injective general position. It does not
prove D7.2 exact-emptiness and does not improve the ESGK bound.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- Total ordered off-diagonal distance mass, written as a named object so the
normal form can refer to it without unfolding the sum. -/
noncomputable def OrderedDistanceMass {n : ℕ} (p : Config n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r

/-- Distance values whose ordered multiplicity is at least `K`. -/
noncomputable def HeavyDistanceValues {n : ℕ} (p : Config n) (K : ℕ) : Finset ℝ :=
  HeavyMultiplicityClasses (OrderedDistanceValues p) (OrderedMultiplicity p) K

/-- Ordered pair mass carried by distance values of multiplicity at least `K`. -/
noncomputable def HeavyDistanceMass {n : ℕ} (p : Config n) (K : ℕ) : ℕ :=
  HeavyMultiplicityMass (OrderedDistanceValues p) (OrderedMultiplicity p) K

/-- The ordered off-diagonal distance mass is at most `n^2`. -/
theorem orderedDistanceMass_le_square {p : Config n} :
    OrderedDistanceMass p ≤ n ^ 2 := by
  simpa [OrderedDistanceMass] using sum_orderedMultiplicity_le (p := p)

/-- Every `K`-heavy distance value contributes at least `K` ordered pairs. -/
theorem threshold_mul_heavyDistanceValues_card_le_heavyDistanceMass
    (p : Config n) (K : ℕ) :
    K * (HeavyDistanceValues p K).card ≤ HeavyDistanceMass p K := by
  simpa [HeavyDistanceValues, HeavyDistanceMass] using
    threshold_mul_heavyMultiplicityCard_le_heavyMultiplicityMass
      (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (K := K)

/-- Under general position, heavy distance mass is at most `3*n` times the
number of heavy distance values. -/
theorem heavyDistanceMass_le_three_mul_heavyDistanceValues_card
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (K : ℕ) :
    HeavyDistanceMass p K ≤ (3 * n) * (HeavyDistanceValues p K).card := by
  simpa [HeavyDistanceValues, HeavyDistanceMass] using
    heavyMultiplicityMass_le_cap_mul_heavyMultiplicityCard
      (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (K := K)
      (B := 3 * n)
      (fun r _hr => orderedMultiplicity_le_three_mul hp hgp r)

/-- Distance-energy normal form before replacing total mass by `n^2`.
Light distance classes contribute at most `K * OrderedDistanceMass`; the rest
is charged to the `K`-heavy distance mass under the `3*n` cap. -/
theorem distanceEnergy_le_threshold_mul_orderedDistanceMass_add_cap_mul_heavyDistanceMass
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (K : ℕ) :
    DistanceEnergy p ≤ K * OrderedDistanceMass p + (3 * n) * HeavyDistanceMass p K := by
  change MultiplicityEnergy (OrderedDistanceValues p) (OrderedMultiplicity p) ≤
    K * MultiplicityMass (OrderedDistanceValues p) (OrderedMultiplicity p) +
      (3 * n) * HeavyMultiplicityMass (OrderedDistanceValues p) (OrderedMultiplicity p) K
  exact multiplicityEnergy_le_threshold_mul_mass_add_cap_mul_heavyMass
    (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (K := K)
    (B := 3 * n)
    (fun r _hr => orderedMultiplicity_le_three_mul hp hgp r)

/-- Distance-energy normal form with the total ordered pair mass bounded by
`n^2`. This is the concrete Step 1 inequality from the D7.2 plan. -/
theorem distanceEnergy_le_threshold_mul_square_add_cap_mul_heavyDistanceMass
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (K : ℕ) :
    DistanceEnergy p ≤ K * n ^ 2 + (3 * n) * HeavyDistanceMass p K := by
  have hmain :=
    distanceEnergy_le_threshold_mul_orderedDistanceMass_add_cap_mul_heavyDistanceMass
      (p := p) hp hgp K
  have hmass := orderedDistanceMass_le_square (p := p)
  exact hmain.trans (Nat.add_le_add_right (Nat.mul_le_mul_left K hmass) _)

/-- Real-valued distance normal form. If the energy is at least
`eta * (3*n) * OrderedDistanceMass`, and `K <= (eta/2)*(3*n)`, then the
`K`-heavy distance values carry at least `(eta/2)` of all ordered distance mass. -/
theorem heavyDistanceMass_lower_bound_real
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (hn : 0 < n) (K : ℕ) {eta : ℝ}
    (henergy : eta * ((3 * n : ℕ) : ℝ) * (OrderedDistanceMass p : ℝ) ≤
      (DistanceEnergy p : ℝ))
    (hK : (K : ℝ) ≤ eta / 2 * ((3 * n : ℕ) : ℝ)) :
    eta / 2 * (OrderedDistanceMass p : ℝ) ≤ (HeavyDistanceMass p K : ℝ) := by
  have hBposNat : 0 < 3 * n := Nat.mul_pos (by norm_num) hn
  have hBpos : 0 < ((3 * n : ℕ) : ℝ) := by exact_mod_cast hBposNat
  simpa [DistanceEnergy, OrderedDistanceMass, HeavyDistanceMass, MultiplicityMass,
    HeavyMultiplicityMass] using
    heavyMultiplicityMass_lower_bound_real
      (s := OrderedDistanceValues p) (m := OrderedMultiplicity p) (K := K)
      (B := 3 * n) (eta := eta)
      (fun r _hr => orderedMultiplicity_le_three_mul hp hgp r)
      hBpos henergy hK

/-- Real-valued distance normal form using the cruder `n^2` total-mass upper
bound in the energy lower-bound hypothesis. The nonnegativity of `eta` is needed
to pass from `OrderedDistanceMass p <= n^2` to the stronger hypothesis required
by `heavyDistanceMass_lower_bound_real`. -/
theorem heavyDistanceMass_lower_bound_real_of_energy_ge_square
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (hn : 0 < n) (K : ℕ) {eta : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (henergy : eta * ((3 * n : ℕ) : ℝ) * (n : ℝ) ^ 2 ≤
      (DistanceEnergy p : ℝ))
    (hK : (K : ℝ) ≤ eta / 2 * ((3 * n : ℕ) : ℝ)) :
    eta / 2 * (OrderedDistanceMass p : ℝ) ≤ (HeavyDistanceMass p K : ℝ) := by
  have hmass_nat := orderedDistanceMass_le_square (p := p)
  have hmass_real : (OrderedDistanceMass p : ℝ) ≤ (n : ℝ) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hmass_nat
    push_cast at this
    simpa using this
  have hcoef_nonneg : 0 ≤ eta * ((3 * n : ℕ) : ℝ) := by
    exact mul_nonneg heta_nonneg (by positivity)
  have henergy_mass : eta * ((3 * n : ℕ) : ℝ) * (OrderedDistanceMass p : ℝ) ≤
      (DistanceEnergy p : ℝ) := by
    have hle : eta * ((3 * n : ℕ) : ℝ) * (OrderedDistanceMass p : ℝ) ≤
        eta * ((3 * n : ℕ) : ℝ) * (n : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hmass_real hcoef_nonneg
    exact hle.trans henergy
  exact heavyDistanceMass_lower_bound_real (p := p) hp hgp hn K henergy_mass hK

end Esgk
