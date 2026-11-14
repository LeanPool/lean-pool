/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentEngine

/-!
# MomentHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's Hölder bookkeeping, in the anchor's `lintegral` normal form

## What this module supplies

Step 5 of the proof of `l.bounds.mathcal.E.aL` reads:

> Using these estimates, the restrictions `m − n ≤ γ^{-1}` and
> `p ≤ C^{-1}γ^{-1}s` and **Hölder's inequality**, it is straightforward to see
> that the `p`-th root of the sum over `j ≤ n` of the `p/2`-th moment of the
> first and third terms ... is bounded by the right side.

Each term of `e.apply.sensitivity.J.aL` is a PRODUCT of the Step-4 bullets, and
each bullet is available at EVERY moment `q ∈ [1,∞)` (that is exactly what the
`hence, for every q` sentences of Step 4 deliver).
Hölder therefore costs nothing except a uniform boost of the exponent by the
number of factors.

* `lintegral_rpow_prod_le_of_moments` — an `N`-factor product whose factors
  each obey the normal form at the boosted exponent `N q` obeys it at `q`, with
  the product of the majorants.  This is the reconstruction of the source's
  "Hölder's inequality" for the four terms.
* `lintegral_rpow_mul_le_of_moments` — the two-factor instance, spelled out.
* `lintegral_rpow_sum_le_of_moments` — the companion `ℝ≥0∞` Minkowski step for a
  finite SUM of terms (the three summands of `e.apply.sensitivity.J.aL`, and the
  primal/adjoint pair of `lFreeStep3Majorant`), at `q ≥ 1`.

Both engines are exponent-neutral: no `γ`-power and no `s`-power is moved, and
no constant beyond the product/sum of the caller's own majorants is introduced.

## References

* Mathlib: `ENNReal.lintegral_prod_norm_pow_le`, `ENNReal.lintegral_Lp_add_le`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {ι : Type*}

/-! ## 1. Two `ℝ≥0∞` product identities -/

/-! ## 2. Hölder for a finite product, in the anchor's normal form -/

/-- **The two-factor Hölder step**, spelled out: a product of two observables,
each controlled at the doubled exponent `2q`. -/
theorem lintegral_rpow_mul_le_of_moments {mu : Measure Omega} {X Y : Omega → ℝ≥0∞}
    {RX RY q : ℝ} (hq : 0 < q) (hXm : AEMeasurable X mu) (hYm : AEMeasurable Y mu)
    (hRX : 0 ≤ RX)
    (hX : (∫⁻ omega, X omega ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RX ^ (2 * q))
    (hY : (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RY ^ (2 * q)) :
    (∫⁻ omega, (X omega * Y omega) ^ q ∂mu) ≤ ENNReal.ofReal (RX * RY) ^ q := by
  have h2q : (0 : ℝ) < 2 * q := by linarith only [hq]
  have hint : ∀ omega : Omega, (X omega * Y omega) ^ q =
      (X omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) * (Y omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) := by
    intro omega
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1 <;> congr 1 <;> ring
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := mu)
    (f := fun omega => X omega ^ (2 * q)) (g := fun omega => Y omega ^ (2 * q))
    (hXm.pow_const _) (hYm.pow_const _) (p := (2 : ℝ)⁻¹) (q := (2 : ℝ)⁻¹)
    (by norm_num) (by norm_num) (by norm_num)
  have hstepX : (∫⁻ omega, X omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal RX ^ q := by
    refine le_trans (ENNReal.rpow_le_rpow hX (by norm_num)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hstepY : (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal RY ^ q := by
    refine le_trans (ENNReal.rpow_le_rpow hY (by norm_num)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  calc (∫⁻ omega, (X omega * Y omega) ^ q ∂mu)
      = ∫⁻ omega, (X omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) *
          (Y omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) ∂mu := lintegral_congr hint
    _ ≤ (∫⁻ omega, X omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) := hholder
    _ ≤ ENNReal.ofReal RX ^ q * ENNReal.ofReal RY ^ q :=
        mul_le_mul' hstepX hstepY
    _ = ENNReal.ofReal (RX * RY) ^ q := by
        rw [ENNReal.ofReal_mul hRX, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

/-! ## 3. The companion Minkowski step for a finite sum -/

end

end Algsuperdiff.Section4.Provider.BoundsEaL
