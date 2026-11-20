/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoVersionExists
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoLinear

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

@[expose] public section

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

/-- The clamp of a real number to `[-j, j]`. -/
noncomputable def clampAt (j x : ℝ) : ℝ := max (-j) (min j x)

theorem clampAt_zero {j : ℝ} (hj : 0 ≤ j) : clampAt j 0 = 0 := by
  unfold clampAt
  rw [min_eq_right hj, max_eq_right (by linarith : -j ≤ (0 : ℝ))]

theorem continuous_clampAt (j : ℝ) : Continuous (clampAt j) := by
  unfold clampAt
  fun_prop

theorem abs_clampAt_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ j := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj]
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le, abs_le]
      exact ⟨hx.le, hx'⟩
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj]

theorem abs_clampAt_le_abs {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj,
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith

theorem abs_clampAt_sub_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x - x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ -j - x), abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
      simp
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j),
        abs_of_nonpos (by linarith : j - x ≤ 0), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith

theorem clampAt_eq_self {j x : ℝ} (hx : |x| ≤ j) : clampAt j x = x := by
  rw [abs_le] at hx
  unfold clampAt
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem tendsto_clampAt (x : ℝ) :
    Filter.Tendsto (fun j : ℕ => clampAt (j : ℝ) x) Filter.atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  refine (clampAt_eq_self ?_).symm
  exact hN.le.trans (by exact_mod_cast hj)

end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem eventually_clampAt_eq (x : ℝ) : ∀ᶠ j : ℕ in Filter.atTop, clampAt (j : ℝ) x = x := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  exact clampAt_eq_self (hN.le.trans (by exact_mod_cast hj))

/-- **Clamping an integrand converges to it in energy on every window.** -/
theorem tendsto_energy_clampAt_sub {G : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry G))
    {T : ℝ} (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hmc : ∀ j : ℕ, Measurable (Function.uncurry fun ω s => clampAt (j : ℝ) (G ω s)) :=
    fun j => (continuous_clampAt (j : ℝ)).measurable.comp hm
  have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity hm T
  have hFmeas : ∀ j : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun j => measurable_energyDensity ((hmc j).sub hm) T
  have hptw : ∀ (j : ℕ) (ω : Ω) (s : ℝ),
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro j ω s
    have habs : |clampAt (j : ℝ) (G ω s) - G ω s| ≤ |G ω s| :=
      abs_clampAt_sub_le (Nat.cast_nonneg j) _
    have hle : (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using habs
    gcongr
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun j : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top hbmeas hq] with ω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (j : ℕ) (s : ℝ) => (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun j => ((((continuous_clampAt ((j : ℕ) : ℝ)).measurable.comp
          (Measurable.of_uncurry_left hm)).sub
        (Measurable.of_uncurry_left hm)).nnNorm.coe_nnreal_ennreal).pow_const 2)
      (fun j => Filter.Eventually.of_forall fun s => hptw j ω s) hfin.ne ?_
    · simpa using hlim
    · filter_upwards with s
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_clampAt_eq (G ω s))
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun j hj => ?_
      rw [hN j hj]
      simp
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (j : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun j => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.lintegral_mono fun s => hptw j ω s) hq hinner
  simpa using hlim


section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

/-- The squared norm of a real vector is at most the sum of its squared coordinates, in `ℝ≥0∞`. -/
theorem sq_enorm_pi_le_sum {m : ℕ} (x : Fin m → ℝ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖x‖₊ ^ 2 ≤ ∑ p, ‖x p‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa [Real.norm_eq_abs, sq_abs] using sq_norm_pi_le_sum_sq x
  calc (‖x‖₊ : ℝ≥0∞) ^ 2 = ((‖x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((∑ p, ‖x p‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring

/-- The squared norm of a finite sum of reals is at most the number of summands times the sum of
their squared norms, in `ℝ≥0∞`. -/
theorem sq_enorm_finsetSum_le {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (∑ k, |x k|) ^ 2 ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun k => |x k|)
    simpa using this
  have habs : |∑ k, x k| ≤ ∑ k, |x k| := Finset.abs_sum_le_sum_abs _ _
  have hnn : ‖∑ k, x k‖₊ ^ 2 ≤ (m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have h1 : |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |∑ k, x k| := abs_nonneg _
      nlinarith [habs, h0]
    calc |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := h1
      _ ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := hreal
      _ = (m : ℝ) * ∑ k, |x k| ^ 2 := rfl
  calc (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 = ((‖∑ k, x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (((m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring

end Difference

end Brownian.Ito

end LevyStochCalc
