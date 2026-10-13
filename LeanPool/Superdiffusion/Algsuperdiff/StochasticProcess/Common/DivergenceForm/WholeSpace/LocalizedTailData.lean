/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedTailFreezing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal

/-!
# LocalizedTailData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Localized split-skew data for the whole-space exhaustion

This module records the structural inputs used by the localized Agmon tail.
The coefficient is split as `a = nu I + ks + kl`: the rough skew part is
bounded only on the ball about the evaluation point, while only the local
divergence of the continuously differentiable skew part is bounded.  The
ambient upper ellipticity constant may depend on the exhaustion cube.

For the stream coefficient, the intended fields are supplied by
`Section5.Field.ScaleDecomposition`, `Section5.Field.LocalSplitBounds`, and
`Section5.Field.FreezingRadius`.  No global small-contrast condition is part
of this datum.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Structural and quantitative local data for the arbitrary-size split-skew
tail estimate.  The local constants may grow with the centre and radius; the
localized family theorem is uniform in the exhaustion index because these
constants do not depend on that index. -/
structure WholeSpaceLocalizedSplitData (A : WholeSpaceAnalyticData d) where
  ks : CoeffField d
  kl : CoeffField d
  split : ∀ y, A.a y = A.nu • (1 : Mat d) + ks y + kl y
  ksSkew : ∀ y, matTranspose (ks y) = -ks y
  klSkew : ∀ y, matTranspose (kl y) = -kl y
  klContDiff : ∀ p q : Fin d, ContDiff ℝ 1 fun y ↦ kl y p q
  roughEllipticityUpper : ℕ → ℝ
  roughEllipticity : ∀ m, IsEllipticFieldOn A.nu (roughEllipticityUpper m)
    (wholeSpaceCube d m) (fun y ↦ A.nu • (1 : Mat d) + ks y)
  holderExponent : ℝ
  holderExponent_mem : holderExponent ∈ Set.Ico (1 / 2 : ℝ) 1
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  delta_le : delta ≤ smallContrastThreshold d holderExponent
  freezingRadius : Vec d → ℝ
  freezingRadius_pos : ∀ x, 0 < freezingRadius x
  smallContrast : ∀ x, CoefficientIdentityDistanceLE
    (euclideanBall x (freezingRadius x))
    (normalizedFrozenCoeff A.nu A.a x) delta
  roughBound : Vec d → ℝ → ℝ
  smoothDivBound : Vec d → ℝ → ℝ
  roughBound_nonneg : ∀ x r, 0 ≤ r → 0 ≤ roughBound x r
  smoothDivBound_nonneg : ∀ x r, 0 ≤ r → 0 ≤ smoothDivBound x r
  roughBound_spec : ∀ x r, 0 ≤ r → ∀ y ∈
    euclideanBall x r, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ roughBound x r ^ 2 * vecNormSq v
  smoothDivBound_spec : ∀ x r, 0 ≤ r → ∀ y ∈
    euclideanBall x r,
      vecNormSq (DivergenceFormProcess.Decay.skewFieldDiv kl y) ≤
        smoothDivBound x r ^ 2

namespace WholeSpaceLocalizedSplitData

variable {A : WholeSpaceAnalyticData d}

/-- The freezing radius clipped to half the source-free radius. -/
def clippedFreezingRadius (L : WholeSpaceLocalizedSplitData A)
    (x : Vec d) (r : ℝ) : ℝ :=
  min (L.freezingRadius x) (r / 2)

/-- The clipped freezing radius is positive whenever the outer radius is. -/
theorem clippedFreezingRadius_pos (L : WholeSpaceLocalizedSplitData A)
    (x : Vec d) {r : ℝ} (hr : 0 < r) :
    0 < L.clippedFreezingRadius x r := by
  exact lt_min (L.freezingRadius_pos x) (half_pos hr)

/-- The clipped radius is admissible for the localized tail estimate. -/
theorem clippedFreezingRadius_le_half (L : WholeSpaceLocalizedSplitData A)
    (x : Vec d) (r : ℝ) : L.clippedFreezingRadius x r ≤ r / 2 :=
  min_le_right _ _

/-- Small contrast persists after clipping the freezing ball. -/
theorem smallContrast_clipped (L : WholeSpaceLocalizedSplitData A)
    (x : Vec d) {r : ℝ} (hr : 0 < r) :
    CoefficientIdentityDistanceLE
      (euclideanBall x (L.clippedFreezingRadius x r))
      (normalizedFrozenCoeff A.nu A.a x) L.delta := by
  apply ae_restrict_of_ae_restrict_of_subset
    (Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
      (L.clippedFreezingRadius_pos x hr).le (min_le_left _ _))
  exact L.smallContrast x

/-- The explicit local two-scale tail for a centre and source-free radius. -/
def tail (L : WholeSpaceLocalizedSplitData A) (mu : PositiveShift)
    (x : Vec d) (r : ℝ) : ℝ :=
  DivergenceFormProcess.Decay.agmonTailFunctionFrozen d A.nu
    (DivergenceFormProcess.Decay.localizedAgmonUpper A.nu (mu : ℝ)
      (L.roughBound x r) (L.smoothDivBound x r))
    A.nu L.holderExponent (Real.sqrt (mu : ℝ) * r)
      (Real.sqrt (mu : ℝ) * L.clippedFreezingRadius x r)

end WholeSpaceLocalizedSplitData

end

end DivergenceFormProcess.Form
