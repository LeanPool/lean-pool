/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RowRetainingGoodScaleInterface

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.AmplitudeRate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The amplitude rate, re-derived from the provider's exports

The formulaic anchored provider transports the physical block row through an
exact triadic dilation before the response aggregation, and the transported
amplitude already contains the requested physical-frame power.  That step is
performed inside the provider's proof but is not exported, so a parallel
provider that consumes the exported package rather than the internal proof has
to re-derive it.  It is re-derived here from exactly three exported conjuncts —
the dilation identity for the microscopic parameter, its residual window, and
the definition of the transported amplitude — together with the certificate's
own structure fields.

No hypothesis beyond the provider's own binder surface is introduced.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- **The transported amplitude carries the physical frame rate.**  From the
exported dilation identity `lambda = epsilon * 3 ^ N`, its residual window and
the exported definition of the transported amplitude, the square root of the
transported amplitude is below the certificate's own amplitude times the
physical frame rate at the unfolded length. -/
theorem sqrt_deltaScaled_le_physicalFrameRate
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d} {a : CoeffSpace d}
    {x epsilon lambda deltaScaled : ℝ} {N : ℕ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hkappa : 0 < kappaRate) (hepsilon : 0 < epsilon)
    (hlambda : lambda = epsilon * (3 : ℝ) ^ N)
    (hlambdaRange : lambda ∈ Set.Icc (1 : ℝ) 3)
    (hdeltaScaled : deltaScaled =
      triadicallyScaledRowAmplitude h.delta (h.activationScale a) N
        (2 * kappaRate)) :
    Real.sqrt deltaScaled ≤ Real.sqrt h.delta * (epsilon * x) ^ kappaRate := by
  have hN : epsilon⁻¹ ≤ (3 : ℝ) ^ N := by
    calc
      epsilon⁻¹ = epsilon⁻¹ * 1 := by ring
      _ ≤ epsilon⁻¹ * (epsilon * (3 : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [← hlambda] using hlambdaRange.1)
          (inv_nonneg.mpr hepsilon.le)
      _ = (3 : ℝ) ^ N := by field_simp [hepsilon.ne']
  have hactivation0 : 0 ≤ h.activationScale a :=
    zero_le_one.trans h.activation_one
  rw [hdeltaScaled]
  exact sqrt_triadicallyScaledRowAmplitude_le_physicalFrameRate
    h.delta_nonneg hactivation0 hepsilon hkappa.le h.activation_le_common hN

end

end RowSupply
end HighContrast
end HCPolySupport
