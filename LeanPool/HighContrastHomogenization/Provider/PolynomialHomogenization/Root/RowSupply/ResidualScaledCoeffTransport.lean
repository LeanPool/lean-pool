/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.TriadicPhysicalBlockRowTransport
public import LeanPool.HighContrastHomogenization.Analytic.ScaledCoeff

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.ResidualScaledCoeffTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Residual scaling of the physical coefficient sample

After extracting an exact triadic dilation, the remaining dilation acts on
the physically restored coefficient sample.  The two coefficient fields agree
almost everywhere after the elementary scalar change of variables.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Scaling the restored sample by `epsilon * 3^N` is the same almost
everywhere as scaling the original sample by `epsilon`. -/
theorem scaledCoeff_mul_pow_physicalScaleCoeff_ae
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℕ) (a : CoeffSpace d) :
    scaledCoeff (epsilon * (3 : ℝ) ^ N)
        (Quenched.physicalScaleCoefficient N a) =ᵐ[volume]
      scaledCoeff epsilon a := by
  have hlambda : 0 < epsilon * (3 : ℝ) ^ N := by positivity
  have hpull :=
    (quasiMeasurePreserving_smul_vec (d := d)
      (inv_ne_zero hlambda.ne')).tendsto_ae
        (Quenched.physical_scale_coeff_ae N a)
  filter_upwards [hpull] with x hx
  change (Quenched.physicalScaleCoefficient N a).1
      ((epsilon * (3 : ℝ) ^ N)⁻¹ • x) = a.1 (epsilon⁻¹ • x)
  rw [hx]
  unfold rescaleCoeffField triadicDilateVec
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hepsilon.ne']

end

end RowSupply
end HighContrast
end HCPolySupport
