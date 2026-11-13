/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.MeanInequalities
public import LeanPool.DistinctDistances.Foundation
public import LeanPool.DistinctDistances.Energy
public import LeanPool.DistinctDistances.Asymptotics
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cauchy-Schwarz energy lower bound and fixed-`A` contradiction bridge.

Lifts (Sigma m_r)^2 <= |D| * (Sigma m_r^2) to (n(n-1))^2 <= NumDistancesOrdered * DistanceEnergy,
the geometric content underlying few-distances implies cubic energy. Stated in the ordered-pair
NumDistancesOrdered form so the inequality holds for all p; the image-finset NumDistances view is
recovered at GP-aware call sites via numDistances_eq_numDistancesOrdered_of_injective.

The capstone proves that the active `FixedLinearDistanceEnergyGapStatement`
is equivalent to eventual exclusion of `NumDistances p <= A n` for every fixed
`A > 0`. The reverse implication is vacuous on the eventually empty
counterexample slice, so this target is a reformulation of Problem 98 rather
than a reduction. The module also records that the former universal `o(n³)`
energy target implies the fixed-`A` target.
-/

@[expose] public section

namespace Esgk

open Filter

/-- Cauchy-Schwarz on ordered multiplicities: `(Σ m_r)² ≤ |D| · Σ m_r² = NumDistancesOrdered ·
DistanceEnergy`, with `Σ m_r = n(n-1)` (total ordered pairs with `i ≠ j`). Stated in the
ordered-pair `NumDistancesOrdered` form so the inequality holds for all `p` (no injectivity
hypothesis); under `Function.Injective p` the bridge
`numDistances_eq_numDistancesOrdered_of_injective` recovers the image-finset form. -/
theorem energy_lower_bound_of_few_distances {n : ℕ} (p : Config n) :
    (n * (n - 1))^2 ≤ (NumDistancesOrdered p) * (DistanceEnergy p) := by
  classical
  -- Abbreviate the ordered-pair finset and its distance-valued function.
  set T : Finset (Fin n × Fin n) :=
    (Finset.univ.product Finset.univ).filter (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2)
    with hT_def
  set f : Fin n × Fin n → ℝ := fun ij ↦ dist (p ij.1) (p ij.2) with hf_def
  -- Fact 1: |T| = n * (n - 1).
  have hTcard : T.card = n * (n - 1) := by
    have h1 : T = (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨i, j⟩
      simp [T, Finset.mem_offDiag]
    have h2 : ((Finset.univ : Finset (Fin n)).offDiag).card =
        (Finset.univ : Finset (Fin n)).card * (Finset.univ : Finset (Fin n)).card -
          (Finset.univ : Finset (Fin n)).card := Finset.offDiag_card _
    rw [h1, h2, Finset.card_univ, Fintype.card_fin]
    -- n * n - n = n * (n - 1)
    cases n with
    | zero => simp
    | succ k => simp [Nat.mul_succ]
  -- Fact 2: OrderedMultiplicity p r = #{ij ∈ T | f ij = r}.
  have hMult : ∀ r : ℝ, OrderedMultiplicity p r = (T.filter (fun ij ↦ f ij = r)).card := by
    intro r
    unfold OrderedMultiplicity
    rw [show T = (Finset.univ.product Finset.univ).filter
        (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2) from rfl,
      Finset.filter_filter]
  -- Fact 3: OrderedDistanceValues p = T.image f.
  have hVals : OrderedDistanceValues p = T.image f := rfl
  -- Fact 4: ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = T.card.
  have hSum : ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = T.card := by
    rw [hVals]
    simp_rw [hMult]
    exact (Finset.card_eq_sum_card_image f T).symm
  -- Fact 5: Discrete Cauchy-Schwarz over ℕ.
  have hCS : (∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r) ^ 2 ≤
      (OrderedDistanceValues p).card *
        ∑ r ∈ OrderedDistanceValues p, (OrderedMultiplicity p r) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- Combine: rewrite LHS and unfold RHS.
  unfold NumDistancesOrdered DistanceEnergy
  rw [hSum] at hCS
  rw [hTcard] at hCS
  exact hCS

/-- The active fixed-`A` energy-gap target is sufficient for Problem 98: for
every `A > 0`, every sufficiently large injective general-position
configuration has strictly more than `A n` distinct distances. -/
theorem fixedLinearDistanceEnergyGap_implies_eventually_numDistances_gt_linear
    (hgap : FixedLinearDistanceEnergyGapStatement) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        EuclideanGeometry.InGeneralPosition (Config.toFinset p) →
        A * (n : ℝ) < (NumDistances p : ℝ) := by
  obtain ⟨δ, hδ, hgapA⟩ := hgap A hA
  have hAδ : 0 < A * δ := mul_pos hA hδ
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 < A * δ * (n : ℝ) := by
    have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hscaled : Filter.Tendsto (fun n : ℕ ↦ A * δ * (n : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_const_mul_atTop_of_pos hAδ).mpr hnat
    exact hscaled.eventually (Filter.eventually_gt_atTop 2)
  filter_upwards [hgapA, hlarge, Filter.eventually_gt_atTop 0] with n hnGap hnLarge hnPos
  intro p hp hgp
  by_contra hnot
  have hD : (NumDistances p : ℝ) ≤ A * (n : ℝ) := le_of_not_gt hnot
  have hE := hnGap p hp hgp hD
  have hCSNat := energy_lower_bound_of_few_distances p
  rw [← numDistances_eq_numDistancesOrdered_of_injective hp] at hCSNat
  have hCS := (Nat.cast_le (α := ℝ)).mpr hCSNat
  push_cast at hCS
  have hnOne : 1 ≤ n := by omega
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hnOne]
    norm_num
  rw [hpred] at hCS
  have hprod : (NumDistances p : ℝ) * (DistanceEnergy p : ℝ) ≤
      (A * (n : ℝ)) * ((A⁻¹ - δ) * (n : ℝ) ^ 3) := by
    calc
      (NumDistances p : ℝ) * (DistanceEnergy p : ℝ)
          ≤ (A * (n : ℝ)) * (DistanceEnergy p : ℝ) :=
            mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg _)
      _ ≤ (A * (n : ℝ)) * ((A⁻¹ - δ) * (n : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left hE (mul_nonneg hA.le (Nat.cast_nonneg _))
  have hAne : A ≠ 0 := ne_of_gt hA
  have hnRealPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnPos
  have hAinv : A * A⁻¹ = 1 := mul_inv_cancel₀ hAne
  have hpoly :
      (A * (n : ℝ)) * ((A⁻¹ - δ) * (n : ℝ) ^ 3) <
        ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 := by
    calc
      (A * (n : ℝ)) * ((A⁻¹ - δ) * (n : ℝ) ^ 3) =
          (A * A⁻¹ - A * δ) * (n : ℝ) ^ 4 := by ring
      _ = (1 - A * δ) * (n : ℝ) ^ 4 := by rw [hAinv]
      _ < ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 := by
        apply sub_pos.mp
        calc
          ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 -
                (1 - A * δ) * (n : ℝ) ^ 4 =
              (n : ℝ) ^ 2 *
                ((n : ℝ) * (A * δ * (n : ℝ) - 2) + 1) := by ring
          _ > 0 := by positivity
  exact (not_lt_of_ge hCS) (hprod.trans_lt hpoly)

/-- Bundled target-to-conclusion implication. -/
theorem fixedLinearDistanceEnergyGap_implies_superlinearDistances
    (hgap : FixedLinearDistanceEnergyGapStatement) :
    GeneralPositionDistinctDistancesSuperlinearStatement := by
  intro A hA
  exact fixedLinearDistanceEnergyGap_implies_eventually_numDistances_gt_linear hgap A hA

/-- The fixed-`A` distinct-distance conclusion implies the conditional energy
gap because the counterexample slice is eventually empty. This direction has
no quantitative content; it records that the energy-gap target is a
reformulation of Problem 98, not a reduction. -/
theorem superlinearDistances_implies_fixedLinearDistanceEnergyGap
    (hsuper : GeneralPositionDistinctDistancesSuperlinearStatement) :
    FixedLinearDistanceEnergyGapStatement := by
  intro A hA
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [hsuper A hA] with n hn
  intro p hp hgp hD
  exact ((not_lt_of_ge hD) (hn p hp hgp)).elim

/-- The active conditional energy-gap statement is logically equivalent to the
fixed-`A` general-position distinct-distance conclusion. -/
theorem fixedLinearDistanceEnergyGap_iff_superlinearDistances :
    FixedLinearDistanceEnergyGapStatement ↔
      GeneralPositionDistinctDistancesSuperlinearStatement :=
  ⟨fixedLinearDistanceEnergyGap_implies_superlinearDistances,
    superlinearDistances_implies_fixedLinearDistanceEnergyGap⟩

/-- The former universal `o(n³)` energy target implies the active fixed-`A`
target. No converse is claimed. -/
theorem generalPositionEnergySaving_implies_fixedLinearDistanceEnergyGap
    (hsaving : GeneralPositionEqualDistanceEnergySavingStatement) :
    FixedLinearDistanceEnergyGapStatement := by
  intro A hA
  have hInvPos : 0 < A⁻¹ := inv_pos.mpr hA
  refine ⟨A⁻¹ / 2, div_pos hInvPos (by norm_num), ?_⟩
  have hsavingA := hsaving (A⁻¹ / 2) (div_pos hInvPos (by norm_num))
  filter_upwards [hsavingA] with n hn
  intro p hp hgp _
  calc
    (DistanceEnergy p : ℝ) ≤ (A⁻¹ / 2) * (n : ℝ) ^ 3 := hn p hp hgp
    _ = (A⁻¹ - A⁻¹ / 2) * (n : ℝ) ^ 3 := by ring

end Esgk
