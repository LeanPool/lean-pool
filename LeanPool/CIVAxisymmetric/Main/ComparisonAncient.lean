/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Comparison.Direct.Assembly
public import LeanPool.CIVAxisymmetric.Comparison.ComparisonAssembly

/-!
# The public statement `CIV.Main.comparisonAncient`

This module proves the statement `CIV.comparisonAncient`, the last assertion of
`lem:aniso:comparison`. The transfer of essential bounds forward in time
(`CIV.ae_ae_abs_le_of_isDistributionalDriftDiffusion`, on `I = (-∞, T)`) is applied at times where
the decay `eq:aniso:ancient:decay` holds and which tend to `-∞`
(`CIV.comparisonAncient_of_eLpNorm_transfer`).
-/

public section

open MeasureTheory Set
open CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of `lem:aniso:comparison`, ancient assertion with the decay
`eq:aniso:ancient:decay`. -/
theorem comparisonAncient (m d : ℕ) (hd : 1 ≤ d ∧ d ≤ m) (T : ℝ)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hB : IsAdmissibleDrift m (Iio T) B divB)
    (q : Vec m × ℝ → ℝ) (hq : IsLocallyBoundedOn m (Iio T) q)
    (heq : IsDistributionalDriftDiffusion m d (Iio T) B divB q)
    (C κ : ℝ) (hκ : 0 < κ)
    (hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1) T))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ ENNReal.ofReal (C * |τ| ^ (-κ))) :
    (∀ᵐ z ∂(volume.restrict (univ ×ˢ Iio T)), q z = 0) ∧
      ∀ (V : Set (Vec m × ℝ)) (q' : Vec m × ℝ → ℝ), IsOpen V →
        ContinuousOn q' (V ∩ univ ×ˢ Iic T) →
        (∀ᵐ z ∂(volume.restrict (V ∩ univ ×ˢ Iio T)), q' z = q z) →
        ∀ z ∈ V ∩ univ ×ˢ Iic T, q' z = 0 :=
  comparisonAncient_of_eLpNorm_transfer m d hd T B divB hB q hq heq C κ hκ hdecay
    (ae_ae_abs_le_of_isDistributionalDriftDiffusion isOpen_Iio ordConnected_Iio hB hq heq)

end Main
end CIV
