/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient

/-!
# High-contrast homogenization: Analytic.LocalEllipticity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reading the local ellipticity constants on one set

The coefficient class fixed in `s.introduction` is local: a field of the class
carries a pair of ellipticity constants on each bounded set, and the pair belongs
to the set.  Every estimate of the coefficient-Sobolev classes is an estimate on
one ball, one cube or one compact set, and each of them wants its hypothesis in
the shape `∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x)`.

This module converts the class into that shape: on a bounded measurable set, on a
centered Euclidean ball, and on a compact set.  The three statements are the same
extraction read at the three carriers the classes use.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The constants of a bounded measurable set**, in restricted-measure form:
the shape the weighted-energy comparisons consume. -/
theorem IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_restrict
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    {S : Set (Vec d)} (hSm : MeasurableSet S) (hS : Bornology.IsBounded S) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume.restrict S, IsEllipticMatrix lam Lam (b x) := by
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb.exists_ae_isEllipticMatrix_of_isBounded hS
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [ae_restrict_of_ae hell, ae_restrict_mem hSm] with x hx hxS
  exact hx hxS

/-- **The constants of a centered Euclidean ball.**  The Euclidean ball of radius
`R` lies in the ambient ball of the same radius, so the constants of the latter
serve. -/
theorem IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_euclideanBall
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b) {R : ℝ} (hR : 0 < R) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume.restrict (euclideanBall d R), IsEllipticMatrix lam Lam (b x) := by
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb R hR
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [ae_restrict_of_ae hell,
    ae_restrict_mem (isOpen_euclideanBall d R).measurableSet] with x hx hxB
  exact hx (euclideanBallAt_subset_metricBall (0 : Vec d) hR hxB)

/-- **The constants of a compact set.**  A compact subset of `ℝ^d` is bounded and
measurable. -/
theorem IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_isCompact
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume.restrict K, IsEllipticMatrix lam Lam (b x) :=
  hb.exists_ae_isEllipticMatrix_restrict hK.measurableSet hK.isBounded

end

end HighContrast
end HCPolySupport
