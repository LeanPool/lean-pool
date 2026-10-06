/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.AmplitudeRate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ScaledAmplitudeBelowOne

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The transported row amplitude is below one

`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorEccentricityBound`
takes `√δ' ≤ 1` as a binder, where
`δ' = triadicallyScaledRowAmplitude h.delta (h.activationScale a) N (2 κ)`
is the amplitude the λ-route's scaled tail carries.

`triadicallyScaledRowAmplitude delta act N kappa = delta * (act / 3 ^ N) ^ kappa`
(`HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.TriadicPhysicalBlockRowTransport`), so
the transport is a *contraction*
as soon as the activation length sits below the dilation `3 ^ N` — which the
provider's own exports give: `λ = ε · 3 ^ N ∈ Icc 1 3` forces `ε⁻¹ ≤ 3 ^ N`, and
the certificate's `activationScale a ≤ x ≤ ε⁻¹`.

So `δ' ≤ δ`, and 21d reduces to `δ ≤ 1` on the row amplitude itself.

**Where `δ ≤ 1` comes from, exactly.**  It is *not* on binder surface,
and it is not a field of `RowRetainingPrintOrderGoodScale`: the row predicate
`Quenched.HasAllLaterPhysicalBlockRow rho kappa C …`
(`HCPoly.Provider.Quenched.CoupledPhysicalBlockDecay`) constrains no
amplitude.  It is supplied one level up, by the **root's quenched hole**:
`HCPoly.Provider.PolynomialHomogenization.RootAssembly` binds `∀ (kappa delta : ℝ), 0 < kappa →
delta ∈ Set.Ioo (0 : ℝ) 1 → …`, and `HCPoly.Provider.PolynomialHomogenization.RootAssembly` feeds
exactly that
`hdeltaRow` into `hhomogenized`.  So `δ ∈ Ioo 0 1` is available at the root and
must travel to the Dirichlet hole through the `GoodScale` predicate — i.e. **21d
is a sub-item of S-1**, not an independent gap.  It is taken here as the
hypothesis `hdelta` in exactly the root's spelling.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- **The triadic transport contracts the amplitude.**  With the activation
length below the dilation, the transported amplitude is below the original. -/
theorem triadicallyScaledRowAmplitude_le_of_activation_le
    {delta act epsilon x lambda kappa : ℝ} {N : ℕ}
    (hdelta : 0 ≤ delta) (hact0 : 0 ≤ act) (hkappa : 0 < kappa)
    (hepsilon : 0 < epsilon)
    (hlambda : lambda = epsilon * (3 : ℝ) ^ N)
    (hlambdaRange : lambda ∈ Set.Icc (1 : ℝ) 3)
    (hactx : act ≤ x) (hscale : x ≤ epsilon⁻¹) :
    triadicallyScaledRowAmplitude delta act N (2 * kappa) ≤ delta := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hN : epsilon⁻¹ ≤ (3 : ℝ) ^ N := by
    calc
      epsilon⁻¹ = epsilon⁻¹ * 1 := by ring
      _ ≤ epsilon⁻¹ * (epsilon * (3 : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [← hlambda] using hlambdaRange.1)
          (inv_nonneg.mpr hepsilon.le)
      _ = (3 : ℝ) ^ N := by field_simp [hepsilon.ne']
  have hle : act ≤ (3 : ℝ) ^ N := hactx.trans (hscale.trans hN)
  have ht0 : (0 : ℝ) ≤ act / (3 : ℝ) ^ N := div_nonneg hact0 h3.le
  have ht1 : act / (3 : ℝ) ^ N ≤ 1 := (div_le_one h3).2 hle
  have hpow : (act / (3 : ℝ) ^ N) ^ (2 * kappa) ≤ 1 :=
    Real.rpow_le_one ht0 ht1 (by linarith only [hkappa])
  rw [triadicallyScaledRowAmplitude]
  calc delta * (act / (3 : ℝ) ^ N) ^ (2 * kappa) ≤ delta * 1 :=
        mul_le_mul_of_nonneg_left hpow hdelta
    _ = delta := mul_one delta

/-- **21d.**  The transported amplitude's square root is below one, from the
provider's own exports together with the root's row-amplitude window
`delta ∈ Set.Ioo 0 1`. -/
theorem sqrt_deltaScaled_le_one [NeZero d]
    {g c kappaRate : ℝ} {abar : Mat d} {a : CoeffSpace d}
    {x epsilon lambda deltaScaled : ℝ} {N : ℕ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hdelta : h.delta ∈ Set.Ioo (0 : ℝ) 1)
    (hkappa : 0 < kappaRate) (hepsilon : 0 < epsilon)
    (hscale : x ≤ epsilon⁻¹)
    (hlambda : lambda = epsilon * (3 : ℝ) ^ N)
    (hlambdaRange : lambda ∈ Set.Icc (1 : ℝ) 3)
    (hdeltaScaled : deltaScaled =
      triadicallyScaledRowAmplitude h.delta (h.activationScale a) N
        (2 * kappaRate)) :
    Real.sqrt deltaScaled ≤ 1 := by
  have hact0 : (0 : ℝ) ≤ h.activationScale a :=
    zero_le_one.trans h.activation_one
  have hstep : deltaScaled ≤ h.delta := by
    rw [hdeltaScaled]
    exact triadicallyScaledRowAmplitude_le_of_activation_le h.delta_nonneg
      hact0 hkappa hepsilon hlambda hlambdaRange h.activation_le_common hscale
  have hone : deltaScaled ≤ 1 := hstep.trans hdelta.2.le
  calc Real.sqrt deltaScaled ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hone
    _ = 1 := Real.sqrt_one

end

end RowSupply
end HighContrast
end HCPolySupport
