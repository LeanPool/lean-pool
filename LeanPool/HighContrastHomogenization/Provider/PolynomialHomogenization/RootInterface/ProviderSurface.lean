/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.GoodScaleInstantiation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RootInterface.ProviderSurface

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Dirichlet provider's binder surface, and what it consumes

Two checks on the restated interface.

**(1) What `RootGoodScale` hands the provider.**  Every row the capstone's
hypothesis table marks as required is supplied: the row-retaining
certificate itself, the positive-definiteness of `symmPart abar` (recovered from
the certificate, which opens with `∃ hS : (symmPart abar).PosDef`), the corrector
threshold window `c ∈ Ioo 0 1`, and the retained row's amplitude window
`delta ∈ Ioo 0 1` — the last being the one the row-retaining structure itself
does *not* carry (it carries only `0 ≤ delta`).

**(2) That the capstone's proved bound feeds the interface clause.**  The clause
reads its rate factor at `x * (Lg * eccentricityFoldFactor abar pEcc)`; the
capstone proves the bound at `x * eccentricityFoldFactor abar p₀`.  Since
the rate factor is increasing in the scale and the constant may be enlarged, any
`Lg ≥ 1` and any `pEcc ≥ p₀` transfer the proved bound to the hole's shape, and
the hole's `ε`-premise is *stronger* than the capstone's `hscale : x ≤ ε⁻¹`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory
open scoped ENNReal
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  witnessEccentricity_nonneg)

noncomputable section

variable {d : ℕ}

/-! ## The fold factor is monotone in its exponent -/

theorem eccentricityFoldFactor_mono (abar : Mat d) {p q : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) :
    eccentricityFoldFactor abar p ≤ eccentricityFoldFactor abar q := by
  have hecc : 0 ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  unfold RowSupply.eccentricityFoldFactor
  rcases le_or_gt 1 (witnessEccentricity (symmPart abar)) with h1 | h1
  · exact max_le_max (le_refl (1 : ℝ))
      (Real.rpow_le_rpow_of_exponent_le h1 hpq)
  · rw [max_eq_left (Real.rpow_le_one hecc h1.le hp)]
    exact le_max_left _ _

/-! ## (1) The provider's binder surface -/

/-- **Everything the Dirichlet provider needs from the certificate.** -/
theorem RootGoodScale.provider_surface [NeZero d] {g kappaRate : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : RootGoodScale d g kappaRate abar a x) :
    ∃ (c : ℝ) (hh : RowSupply.RowRetainingPrintOrderGoodScale
        d g c kappaRate abar a x),
      c ∈ Set.Ioo (0 : ℝ) 1 ∧
      hh.delta ∈ Set.Ioo (0 : ℝ) 1 ∧
      (symmPart abar).PosDef ∧
      0 ≤ hh.delta ∧
      1 ≤ hh.activationScale a ∧
      hh.sourceScale a ≤ hh.activationScale a ∧
      hh.activationScale a ≤ x ∧
      Quenched.HasAllLaterPhysicalBlockRow (Certificate.printRowOrder g)
        (2 * kappaRate) hh.delta (Book.Ch02.constantBlockMatrix abar)
        hh.sourceScale hh.activationScale a := by
  obtain ⟨c, hh, hc, hdelta⟩ := h
  obtain ⟨amp, Xc, hcert, -⟩ := hh.good
  obtain ⟨hS, -⟩ := hcert
  exact ⟨c, hh, hc, hdelta, hS, hh.delta_nonneg, hh.activation_one,
    hh.source_le_activation, hh.activation_le_common, hh.row⟩

/-! ## (2) What the surface consumes -/

/-- The clause's `ε`-premise implies the capstone's. -/
theorem scale_le_of_foldedScale_le {abar : Mat d} {x Lg pEcc epsilon : ℝ}
    (hx : 0 ≤ x) (hLg : 1 ≤ Lg)
    (h : x * (Lg * eccentricityFoldFactor abar pEcc) ≤ epsilon⁻¹) :
    x ≤ epsilon⁻¹ :=
  le_trans (le_mul_of_one_le_right hx
    (one_le_mul_of_one_le_of_one_le hLg
      (one_le_eccentricityFoldFactor abar pEcc))) h

end

end RootInterface
end HighContrast
end HCPolySupport
