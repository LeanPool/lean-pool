/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.HighContrastHomogenization.Support.Sobolev.L2Ambient
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# VectorPairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `L²` pairing bound on the supremum-norm carrier

The ambient carrier `Vec d = Fin d → ℝ` is normed by the supremum norm, so it is
not an inner-product space and the Cauchy-Schwarz inequality is not available on
`VectorL2 U` directly.  What is true, and what the energy estimates need, is the
same bound with the dimensional factor `d`:

```text
  |∫_U ⟨F, G⟩| ≤ d ‖F‖_{L²(U)} ‖G‖_{L²(U)} .
```

The factor enters once, in the pointwise step `|⟨x, y⟩| ≤ d ‖x‖ ‖y‖`, and is the
exact price of measuring a `d`-term sum by the largest of its factors.  No
Hilbert carrier is introduced.

## Main results

* `abs_vecDot_le_dim_mul` — the pointwise bound.
* `abs_setIntegral_vecDot_le` — the integrated bound.
* `vecNormSq_matVecMul_le_of_entry_bound` — a matrix with entries bounded by
  `delta` moves the Euclidean square by at most `(d · delta)²`.

## References

* ABK26, the energy estimates of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped BigOperators

variable {d : ℕ}

/-! ## 1. The pointwise bound -/

/-- **The pairing is bounded by `d` times the product of the supremum norms.** -/
theorem abs_vecDot_le_dim_mul (x y : Vec d) : |vecDot x y| ≤ (d : ℝ) * (‖x‖ * ‖y‖) := by
  calc |vecDot x y| = |∑ i, x i * y i| := rfl
    _ ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * ‖y‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i) (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖x‖ * ‖y‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The integrated bound -/

/-- **The `L²` pairing bound on the supremum-norm carrier.** -/
theorem abs_setIntegral_vecDot_le (U : Set (Vec d)) {F G : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    |∫ x in U, vecDot (F x) (G x) ∂volume| ≤
      (d : ℝ) * (Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume)) := by
  have hFn : MemLp (fun x => ‖F x‖) 2 (volume.restrict U) := hF.norm
  have hGn : MemLp (fun x => ‖G x‖) 2 (volume.restrict U) := hG.norm
  have hint : Integrable (fun x => ‖F x‖ * ‖G x‖) (volume.restrict U) := by
    simpa [Pi.mul_apply] using! hFn.integrable_mul hGn
  have h1 : |∫ x in U, vecDot (F x) (G x) ∂volume| ≤
      ∫ x in U, |vecDot (F x) (G x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict U)
        (f := fun x => vecDot (F x) (G x))
  have h2 : ∫ x in U, |vecDot (F x) (G x)| ∂volume ≤
      ∫ x in U, (d : ℝ) * (‖F x‖ * ‖G x‖) ∂volume :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hint.const_mul (d : ℝ)) (Filter.Eventually.of_forall fun x => abs_vecDot_le_dim_mul _ _)
  have h3 : ∫ x in U, (d : ℝ) * (‖F x‖ * ‖G x‖) ∂volume =
      (d : ℝ) * ∫ x in U, ‖F x‖ * ‖G x‖ ∂volume := integral_const_mul _ _
  have h4 : ∫ x in U, ‖F x‖ * ‖G x‖ ∂volume ≤
      Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume) := by
    have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict U)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => norm_nonneg (F x))
      (Filter.Eventually.of_forall fun x => norm_nonneg (G x))
      (by simpa using hFn) (by simpa using hGn)
    have hrw : ∀ H : Vec d → Vec d,
        ∫ x in U, ‖H x‖ ^ (2 : ℝ) ∂volume = ∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume := by
      intro H
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖H x‖ ^ (2 : ℝ) = ‖H x‖ ^ (2 : ℕ)
      rw [← Real.rpow_natCast (‖H x‖) 2]
      norm_num
    rw [hrw F, hrw G] at hhold
    have hsq : ∀ H : Vec d → Vec d,
        (∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume) ^ (1 / (2 : ℝ)) =
          Real.sqrt (∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume) := by
      intro H
      rw [Real.sqrt_eq_rpow]
    rw [hsq F, hsq G] at hhold
    exact hhold
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by positivity
  calc |∫ x in U, vecDot (F x) (G x) ∂volume|
      ≤ ∫ x in U, |vecDot (F x) (G x)| ∂volume := h1
    _ ≤ ∫ x in U, (d : ℝ) * (‖F x‖ * ‖G x‖) ∂volume := h2
    _ = (d : ℝ) * ∫ x in U, ‖F x‖ * ‖G x‖ ∂volume := h3
    _ ≤ (d : ℝ) * (Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume)) :=
        mul_le_mul_of_nonneg_left h4 hdnn

/-! ## 3. A matrix perturbation moves the Euclidean square by `(d · delta)²` -/

/-- **An entrywise bound on a matrix bounds its action.** -/
theorem norm_matVecMul_le_of_entry_bound {A : Mat d} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ∀ i j, |A i j| ≤ delta) (xi : Vec d) :
    ‖matVecMul A xi‖ ≤ (d : ℝ) * delta * ‖xi‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hentry : matVecMul A xi i = ∑ j, A i j * xi j := rfl
  rw [hentry]
  calc |∑ j, A i j * xi j| ≤ ∑ j, |A i j * xi j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, delta * ‖xi‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hA i j)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm xi j) (abs_nonneg _) hdelta
    _ = (d : ℝ) * delta * ‖xi‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Algsuperdiff.Section5.Support
