/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Convergence of absolutely bounded Schwartz series

The limit is constructed as the actual pointwise sum. Mathlib's smooth-series
theorem identifies all of its derivatives, and the summable Schwartz
seminorm bounds prove rapid decay and convergence in the actual Schwartz
topology. No completeness instance or normed structure on Schwartz space is
assumed. The convergence assertion below is for natural partial sums.
-/

@[expose] public section

open Filter Topology
open scoped SchwartzMap

namespace VacuumBellSeparation

variable (f : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
  (hf : ∀ k j, Summable (fun n => SchwartzMap.seminorm ℂ k j (f n)))

include hf

theorem summable_schwartzSeries_iteratedFDeriv (j : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun n => iteratedFDeriv ℝ j (f n) x) :=
  (hf 0 j).of_norm_bounded fun n => by
    simpa only [pow_zero, one_mul] using (f n).le_seminorm ℂ 0 j x

theorem schwartzSeries_iteratedFDeriv (j : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℝ j (fun y => ∑' n, f n y) x =
      ∑' n, iteratedFDeriv ℝ j (f n) x := by
  apply iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞))
    (v := fun j n => SchwartzMap.seminorm ℂ 0 j (f n))
    (fun n => (f n).smooth ⊤) (fun j _ => hf 0 j) ?_ le_top x
  intro j n y hj
  simpa only [pow_zero, one_mul] using (f n).le_seminorm ℂ 0 j y

theorem schwartzSeries_weighted_derivative_bound (k j : ℕ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y => ∑' n, f n y) x‖ ≤
      ∑' n, SchwartzMap.seminorm ℂ k j (f n) := by
  rw [schwartzSeries_iteratedFDeriv f hf j x]
  have hs := (summable_schwartzSeries_iteratedFDeriv f hf j x).hasSum.const_smul (‖x‖ ^ k)
  have hb := hs.norm_le_of_bounded (hf k j).hasSum (fun n =>
    show ‖‖x‖ ^ k • iteratedFDeriv ℝ j (f n) x‖ ≤ SchwartzMap.seminorm ℂ k j (f n) from by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)]
        using (f n).le_seminorm ℂ k j x)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)] using hb

/-- The actual pointwise series is a Schwartz function under summable seminorm bounds. -/
noncomputable def schwartzSeries : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ where
  toFun x := ∑' n, f n x
  smooth' := by
    apply contDiff_tsum (N := (⊤ : ℕ∞))
      (v := fun j n => SchwartzMap.seminorm ℂ 0 j (f n))
      (fun n => (f n).smooth ⊤) (fun j _ => hf 0 j)
    intro j n x hj
    simpa only [pow_zero, one_mul] using (f n).le_seminorm ℂ 0 j x
  decay' k j := ⟨∑' n, SchwartzMap.seminorm ℂ k j (f n),
    schwartzSeries_weighted_derivative_bound f hf k j⟩

@[simp] theorem schwartzSeries_apply (x : EuclideanSpace ℝ (Fin 3)) :
    schwartzSeries f hf x = ∑' n, f n x := rfl

theorem seminorm_schwartzSeries_le (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (schwartzSeries f hf) ≤
      ∑' n, SchwartzMap.seminorm ℂ k j (f n) :=
  SchwartzMap.seminorm_le_bound ℂ k j _ (tsum_nonneg fun n => by positivity)
    (schwartzSeries_weighted_derivative_bound f hf k j)

theorem schwartzSeries_tail_summable (N k j : ℕ) :
    Summable (fun n => SchwartzMap.seminorm ℂ k j (f (n + N))) :=
  (summable_nat_add_iff N).mpr (hf k j)

theorem schwartzSeries_split (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) +
      schwartzSeries (fun n => f (n + N)) (schwartzSeries_tail_summable f hf N) =
        schwartzSeries f hf := by
  ext x
  have hs : Summable (fun n => f n x) :=
    (hf 0 0).of_norm_bounded fun n => (f n).norm_le_seminorm ℂ x
  simpa only [add_apply, sum_apply, schwartzSeries_apply] using
    hs.sum_add_tsum_nat_add N

/-- Natural partial sums converge in every Schwartz seminorm to the explicitly constructed sum. -/
theorem tendsto_schwartzSeries_partialSums :
    Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 (schwartzSeries f hf)) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin 3)) ℂ).tendsto_nhds]
  intro kj ε hε
  have ht := (tendsto_sum_nat_add
    (fun n => SchwartzMap.seminorm ℂ kj.1 kj.2 (f n))).eventually (gt_mem_nhds hε)
  filter_upwards [ht] with N hN
  have heq : (∑ n ∈ Finset.range N, f n) - schwartzSeries f hf =
      -schwartzSeries (fun n => f (n + N)) (schwartzSeries_tail_summable f hf N) := by
    rw [← schwartzSeries_split f hf N]
    abel
  rw [heq, map_neg_eq_map]
  exact (seminorm_schwartzSeries_le (fun n => f (n + N))
    (schwartzSeries_tail_summable f hf N) kj.1 kj.2).trans_lt hN

end VacuumBellSeparation
