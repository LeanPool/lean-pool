/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.RowPairingAnnealed

/-!
# High-contrast homogenization: Provider.Response.RowCellPairingProducer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed cell pairing

Averaging the per-cell pairing over the law is a Cauchy-Schwarz step in `L²` of
the law: the energy side collects the annealed cell energy and the load side
collects, by linearity of the block's diagonal entries, the Schur load of the
annealed block itself.

The coefficient is the recentred sample, whose coarse response is the shear
congruence of the original one, so the load that appears is the hatted load the
response row carries.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Cauchy-Schwarz in `L²` of a measure -/

/-- **Cauchy-Schwarz for Bochner integrals at exponent two.**  Obtained from the
nonnegativity of the quadratic `t ↦ ∫ (t f + g)²` through its discriminant. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x ↦ f x ^ 2) μ)
    (hg : Integrable (fun x ↦ g x ^ 2) μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ) :
    ∫ x, f x * g x ∂μ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun x ↦ sq_nonneg _
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + 2 * (∫ x, f x * g x ∂μ) * t +
        ∫ x, g x ^ 2 ∂μ := by
    intro t
    have hnn : 0 ≤ ∫ x, (t * f x + g x) ^ 2 ∂μ :=
      MeasureTheory.integral_nonneg fun x ↦ sq_nonneg _
    have hpt : ∀ x : α, (t * f x + g x) ^ 2 =
        (t * t) * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2 := by
      intro x; ring
    have h1 : Integrable (fun a ↦ t * t * f a ^ 2) μ := hf.const_mul _
    have h2 : Integrable (fun a ↦ 2 * t * (f a * g a)) μ := hfg.const_mul _
    have h12 : Integrable (fun a ↦ t * t * f a ^ 2 + 2 * t * (f a * g a)) μ :=
      h1.add h2
    have hexp : ∫ x, (t * f x + g x) ^ 2 ∂μ =
        (∫ x, f x ^ 2 ∂μ) * (t * t) + 2 * (∫ x, f x * g x ∂μ) * t +
          ∫ x, g x ^ 2 ∂μ := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
        MeasureTheory.integral_add h12 hg,
        MeasureTheory.integral_add h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring
    rw [hexp] at hnn
    exact hnn
  have hdis :
      discrim (∫ x, f x ^ 2 ∂μ) (2 * ∫ x, f x * g x ∂μ) (∫ x, g x ^ 2 ∂μ) ≤ 0 :=
    discrim_le_zero hquad
  have hsq : (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
    have hd : (2 * ∫ x, f x * g x ∂μ) ^ 2 -
        4 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) ≤ 0 := hdis
    nlinarith only [hd]
  calc ∫ x, f x * g x ∂μ ≤ |∫ x, f x * g x ∂μ| := le_abs_self _
    _ = Real.sqrt ((∫ x, f x * g x ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) :=
        Real.sqrt_mul hA _

/-! ## The recentred coarse block -/

/-! ## The annealed cell pairing -/

end

end HCPolySupport.HighContrast.Response
