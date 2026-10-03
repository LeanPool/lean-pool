/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodic

/-! The low-frequency gap and L2 splitting used in the centered extension.
These finite spectral estimates do not require the product's mean to vanish. -/

@[expose] public section

namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory Homogenization AVenhance.Infra.Torus
noncomputable section
variable {d : ℕ}

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicCenteredSpectralCoreMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicCenteredSpectralCoreMeasureIsAddHaarMeasure2 :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicCenteredSpectralCoreIsProbabilityMeasure3 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Measure.Subtype.measureSpace

theorem CenteredSpectralCore.torusRepresentative_eq_cellRepresentative
    (x : UnitAddTorus (Fin d)) :
    Torus.unitTorusRepresentative d x = unitCellRepresentative x := by
  exact HMinusOneErgodic.torusRepresentative_eq_cellRepresentative x

theorem CenteredSpectralCore.integral_torusFunction_eq_unitCell {v : Vec d → ℂ} :
    ∫ x : UnitAddTorus (Fin d), torusFunction v x =
      ∫ x in Torus.unitCell d, v x := by
  exact HMinusOneErgodic.integral_torusFunction_eq_unitCell (v := v)

theorem CenteredSpectralCore.cellAverage_absSq_eq_sq {u : Vec d → ℝ} :
    cellAverage (fun x => |u x| ^ 2) = cellAverage (fun x => u x ^ 2) := by
  exact HMinusOneErgodic.cellAverage_absSq_eq_sq (u := u)

theorem CenteredSpectralCore.l2norm_cell_eq_average_absSq {u : Vec d → ℝ} :
    (∫ x in Torus.unitCell d, u x ^ 2) ^ (1 / 2 : ℝ) =
      (cellAverage (fun x => |u x| ^ 2)) ^ (1 / 2 : ℝ) := by
  exact HMinusOneErgodic.l2norm_cell_eq_average_absSq (u := u)

theorem CenteredSpectralCore.mFourierCoeff_zero_eq_integral_local
    (H : UnitAddTorus (Fin d) → ℂ) :
    UnitAddTorus.mFourierCoeff H (0 : Fin d → ℤ) = ∫ x, H x := by
  exact HMinusOneErgodic.mFourierCoeff_zero_eq_integral_local H

theorem centered_lowProjection_fastProduct_mean_gap
    {d N M : ℕ} (hN : 0 < N)
    (hgapPos : 0 < (N : ℝ) - (M : ℝ))
    {f : Vec d → ℝ}
    {g : Vec d → ℝ}
    (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hgMean : cellAverage g = 0) :
    cellAverage (fun x => lowProjection f M x * g x) = 0 ∧
      ∀ q : Fin d → ℤ, ‖q‖ < (N : ℝ) - (M : ℝ) →
        UnitAddTorus.mFourierCoeff
          (torusFunction (fun x => (lowProjection f M x * g x : ℂ))) q = 0 := by
  exact HMinusOneErgodic.lowProjection_fastProduct_mean_gap hN hgapPos hg hg2 hfast hgMean

theorem centered_fastProduct_split_l2_bound
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds (fun x => (f x : ℂ)) Cf r)
    {g : Vec d → ℝ}
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ)) :
    (∫ x in Torus.unitCell d,
      (lowProjection f (N / 2) x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ((cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) +
          32 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) * Cf *
            Real.exp (-r * (N : ℝ) / 4096)) *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) ∧
    (∫ x in Torus.unitCell d,
      (highRemainder f (N / 2) x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        (1024 * ((d : ℝ) + 1) * Cf +
          32 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) * Cf) *
          Real.exp (-r * (N : ℝ) / 4096) *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) := by
  exact HMinusOneErgodic.fastProduct_split_l2_bound hd hN hf hper Cf r hCf hr hderiv
    hg2 hfast hNr

end
end AVenhance.Infra.Ergodic
