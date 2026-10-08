/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing

/-!
# High-contrast homogenization: Analytic.ScaledCoeff

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rescaled coefficient field is locally uniformly elliptic

The Dirichlet estimate `e.random.dirichlet`
is read for the rescaled field `a^ε(x) = a(x/ε)`, and every closure statement
about a weak-gradient pair needs an ellipticity pair for the field it is applied
to on the bounded set it is read on.

The route is the one `HCPoly.Setup.CoefficientSpace` takes for
`translateField`: the transport map is quasi measure preserving for the Lebesgue
measure, so almost-everywhere statements pull back along it.  There the map is a
translation and the input is `MeasurePreserving.quasiMeasurePreserving`; here it
is the dilation `x ↦ ε⁻¹ • x`, which is *not* measure preserving but is quasi
measure preserving — its pushforward is a finite nonzero multiple of the
Lebesgue measure — and the input is
`MeasureTheory.Measure.quasiMeasurePreserving_smul`, available because `volume`
on `Fin d → ℝ` is an additive Haar measure.  The dilation moves no value of `a`,
only where it is read: the ball of radius `R` for `a^ε` is served by the
constants of `a` on the ball of radius `R/ε`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A nonzero scalar dilation of `ℝ^d` is quasi measure preserving for the
Lebesgue measure. -/
theorem quasiMeasurePreserving_smul_vec {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : Vec d => c • x) volume volume :=
  Measure.quasiMeasurePreserving_smul volume hc

/-- The rescaled field is a.e. strongly measurable, so it can be fed to the
weak flux pairing estimates. -/
theorem aestronglyMeasurable_scaledCoeff {ε : ℝ} (hε : 0 < ε) (a : CoeffSpace d) :
    AEStronglyMeasurable (scaledCoeff ε a) volume :=
  a.1.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_smul_vec (inv_ne_zero hε.ne'))

/-- The entries of the rescaled field are a.e. strongly measurable. -/
theorem aestronglyMeasurable_scaledCoeff_apply {ε : ℝ} (hε : 0 < ε)
    (a : CoeffSpace d) (i j : Fin d) :
    AEStronglyMeasurable (fun x => scaledCoeff ε a x i j) volume :=
  (continuous_id.matrix_elem i j).comp_aestronglyMeasurable
    (aestronglyMeasurable_scaledCoeff hε a)

/-- **The rescaled coefficient field `a^ε(x) = a(x/ε)` is locally uniformly
elliptic**: the ball of radius `R` is served by the ellipticity constants of `a`
on the ball of radius `R/ε`. -/
theorem isAELocallyUniformlyElliptic_scaledCoeff {ε : ℝ} (hε : 0 < ε)
    (a : CoeffSpace d) :
    IsAELocallyUniformlyElliptic (scaledCoeff ε a) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := a.2 (ε⁻¹ * R) (by positivity)
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [(quasiMeasurePreserving_smul_vec (d := d)
    (inv_ne_zero hε.ne')).tendsto_ae hell] with x hx hxb
  refine hx (mem_ball_zero_iff.2 ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
  exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hxb) (inv_pos.2 hε)

/-- The essential entry bound of the rescaled field on a bounded set, in the
shape the pairing lemmas take it. -/
theorem ae_abs_entry_le_scaledCoeff {ε : ℝ} (hε : 0 < ε) (a : CoeffSpace d)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ x ∂volume, x ∈ S → ∀ i j, |scaledCoeff ε a x i j| ≤ M := by
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    (isAELocallyUniformlyElliptic_scaledCoeff hε a
      ).exists_ae_isEllipticMatrix_of_isBounded hS
  refine ⟨Lam, le_trans hlam.le hle, ?_⟩
  filter_upwards [hell] with x hx hxS i j
  exact abs_apply_le_of_isEllipticMatrix (hx hxS) i j

end

end HighContrast
end HCPolySupport
