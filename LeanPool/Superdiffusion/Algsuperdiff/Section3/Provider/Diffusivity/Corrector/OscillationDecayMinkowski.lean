/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayAverage
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# OscillationDecayMinkowski

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The triangle inequality for the normalized `L^2` deviation on a cube

The nested-recentring assembly of `OscillationTelescope` opens with a splitting
step: the fine-scale gradient is written as a finite sum of harmonic increments
plus an approximation defect, and the normalized `L^2` oscillation of the sum is
bounded by the sum of the normalized `L^2` deviations of the summands.  That is
the hypothesis `hsplit` of
`le_zpow_mul_add_nsmul_of_nested_decomposition`, and it is the Minkowski
inequality for the seminorm

```
  N (h, c) = || h - c ||_{L2bar (V)} = sqrt (sum_i avg_V (h_i - c_i)^2) .
```

CoarseGraining supplies no lemma about `meanSquareDeviationVecOn` at all, so
the inequality is proved from scratch, and elementarily: the cross term is
controlled by the Cauchy--Schwarz inequality, which is obtained from the
nonnegativity of the quadratic `t -> sum_i int_V (t (f_i - a_i) - (g_i -
b_i))^2` through Mathlib's `discrim_le_zero`.  No `L^p` duality, no `MemLp`
bookkeeping and no transfer to `EuclideanSpace` is used.

This module carries the two ingredients of that argument, at an arbitrary set
`V` and with the integrability of the three moments as explicit binders.  The
triangle inequality itself is assembled from them in
`HarmonicReplaceMinkowski.sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2`
and, in the oscillation form `hsplit` consumes, in
`Closure.GammaTenInteriorMinkowski.sqrt_meanSquareOscillationVecOn_add_le_of_memVectorL2`;
there the binders are square integrability of the two fields, with no
continuity hypothesis.

## Contents

* `setIntegral_sub_sq_expand` -- the expansion of `int_V (t p - q)^2`.
* `sq_sum_setIntegral_mul_le` -- Cauchy--Schwarz for the coordinate-summed
  bilinear form.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- Expansion of the quadratic `int_V (t p - q)^2` in the three moments. -/
theorem setIntegral_sub_sq_expand {V : Set (Vec d)} {p q : Vec d → ℝ}
    (hp2 : IntegrableOn (fun x => p x ^ 2) V volume)
    (hq2 : IntegrableOn (fun x => q x ^ 2) V volume)
    (hpq : IntegrableOn (fun x => p x * q x) V volume) (t : ℝ) :
    ∫ x in V, (t * p x - q x) ^ 2 ∂volume
      = (∫ x in V, p x ^ 2 ∂volume) * (t * t)
        + -(2 * ∫ x in V, p x * q x ∂volume) * t
        + ∫ x in V, q x ^ 2 ∂volume := by
  have hfun : (fun x => (t * p x - q x) ^ 2)
      = fun x => t ^ 2 * p x ^ 2 + (-(2 * t) * (p x * q x) + q x ^ 2) := by
    funext x
    ring
  have h1 : IntegrableOn (fun x => t ^ 2 * p x ^ 2) V volume := hp2.const_mul _
  have h2 : IntegrableOn (fun x => -(2 * t) * (p x * q x)) V volume := hpq.const_mul _
  have h3 : IntegrableOn (fun x => -(2 * t) * (p x * q x) + q x ^ 2) V volume := h2.add hq2
  rw [hfun, integral_add h1 h3, integral_add h2 hq2, integral_const_mul, integral_const_mul]
  ring

/-- **Cauchy--Schwarz for the coordinate-summed bilinear form.** -/
theorem sq_sum_setIntegral_mul_le {V : Set (Vec d)} {p q : Fin d → Vec d → ℝ}
    (hp2 : ∀ i : Fin d, IntegrableOn (fun x => p i x ^ 2) V volume)
    (hq2 : ∀ i : Fin d, IntegrableOn (fun x => q i x ^ 2) V volume)
    (hpq : ∀ i : Fin d, IntegrableOn (fun x => p i x * q i x) V volume) :
    (∑ i : Fin d, ∫ x in V, p i x * q i x ∂volume) ^ 2
      ≤ (∑ i : Fin d, ∫ x in V, p i x ^ 2 ∂volume) *
        ∑ i : Fin d, ∫ x in V, q i x ^ 2 ∂volume := by
  have hlin : ∀ (P Q R : Fin d → ℝ) (t : ℝ),
      ∑ i : Fin d, (P i * (t * t) + -(2 * Q i) * t + R i)
        = (∑ i : Fin d, P i) * (t * t) + -(2 * ∑ i : Fin d, Q i) * t
          + ∑ i : Fin d, R i := by
    intro P Q R t
    simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, neg_mul,
      Finset.sum_neg_distrib]
  have hquad : ∀ t : ℝ, 0 ≤ (∑ i : Fin d, ∫ x in V, p i x ^ 2 ∂volume) * (t * t)
      + -(2 * ∑ i : Fin d, ∫ x in V, p i x * q i x ∂volume) * t
      + ∑ i : Fin d, ∫ x in V, q i x ^ 2 ∂volume := by
    intro t
    have hnn : (0 : ℝ) ≤
        ∑ i : Fin d, ∫ x in V, (t * p i x - q i x) ^ 2 ∂volume :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    have hcongr : ∑ i : Fin d, ∫ x in V, (t * p i x - q i x) ^ 2 ∂volume
        = ∑ i : Fin d, ((∫ x in V, p i x ^ 2 ∂volume) * (t * t)
            + -(2 * ∫ x in V, p i x * q i x ∂volume) * t
            + ∫ x in V, q i x ^ 2 ∂volume) :=
      Finset.sum_congr rfl fun i _ =>
        setIntegral_sub_sq_expand (hp2 i) (hq2 i) (hpq i) t
    rw [hcongr, hlin] at hnn
    exact hnn
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
