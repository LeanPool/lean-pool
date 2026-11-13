/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.DistanceDeficiencyPositive
public import LeanPool.DistinctDistances.ThinAnnulus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Row facts for the constant gain `1/40`

Formalizes, in count form, the row `A2lo` and the lower end of the box of `𝔡` used by
Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` (the S2 file
`docs/results/explicit-constant-gain-5-239-2026-10-20.md`, F2 and §3). Thresholds are squared
distances. Write `P(t) = Σ_j (N_j(t) - 1)` for the ordered pairs of distinct indices at squared
distance at most `t`, where `N_j(t)` counts the indices `q` with `|p_j p_q|² ≤ t` (including `j`
itself), and `D` for the number of ordered distance values. The normalized quantities are
`𝒜 = P/n²`, `𝔡 = D/n` and `ε = 1/n`.

* Row `A2lo` (`mul_self_sub_le_sum_closedBall_sq_card_sub_one_of_four_le`): with
  `ρ² = distanceAnnulusRadiusSq p` and the degree cap three, every pair is within squared
  distance `4ρ²` (the S2 fact (N3)), so `n² - n ≤ P(τρ²)` for `τ ≥ 4`. At `τ = 4` this is the
  S2 row `-𝒜(2) - ε ≤ -1` times `n²`.
* The box (`numPoints_le_three_mul_numDistancesOrdered_real`): `n ≤ 3D` for an injective
  general-position configuration with `n ≥ 4`, so `𝔡 ≥ 1/3`, which is above the box end
  `1/3 - ε/3` of the certificate.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- Row `A2lo` (the S2 fact `𝒜(2) = 1 - ε`, lower half; the row `-𝒜(2) - ε ≤ -1` times `n²`).
With the degree cap three and `ρ² = distanceAnnulusRadiusSq p`, every pair of indices is within
squared distance `4ρ²`, so for every squared threshold factor `τ ≥ 4` the ordered close-pair
count `P(τρ²) = Σ_j (N_j(τρ²) - 1)` is at least `n² - n`. -/
theorem mul_self_sub_le_sum_closedBall_sq_card_sub_one_of_four_le {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {ρ τ : ℝ}
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) (hτ : 4 ≤ τ) :
    (n : ℝ) * n - n ≤ ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ * ρ ^ 2)).card : ℝ) - 1) := by
  have hτρ : 4 * ρ ^ 2 ≤ τ * ρ ^ 2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg ρ)
  have hpair : ∀ j q : Fin n, dist (p j) (p q) ^ 2 ≤ τ * ρ ^ 2 := by
    intro j q
    by_cases hjq : j = q
    · subst hjq
      rw [dist_self]
      nlinarith [sq_nonneg ρ]
    · have h4 : dist (p j) (p q) ^ 2 ≤ 4 * ρ ^ 2 := by
        rw [hρsq]
        exact palette_sq_le_four_mul_distanceAnnulusRadiusSq j.pos hcap
          (Finset.mem_image.mpr ⟨(j, q), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hjq⟩, rfl⟩)
      exact h4.trans hτρ
  have hfull : ∀ j, (Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ * ρ ^ 2) = Finset.univ := fun j ↦
    Finset.filter_true_of_mem fun q _ ↦ hpair j q
  simp only [hfull, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The box lower end of `𝔡` (real form of `numPoints_le_three_mul_numDistancesOrdered`): an
injective general-position configuration of at least four points satisfies `n ≤ 3D`, where `D`
is the number of ordered distance values. In normalized form `𝔡 ≥ 1/3 ≥ 1/3 - ε/3`. -/
theorem numPoints_le_three_mul_numDistancesOrdered_real {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) (hn : 4 ≤ n) :
    (n : ℝ) ≤ 3 * (NumDistancesOrdered p : ℝ) := by
  exact_mod_cast numPoints_le_three_mul_numDistancesOrdered hp hgp hn

end Esgk
