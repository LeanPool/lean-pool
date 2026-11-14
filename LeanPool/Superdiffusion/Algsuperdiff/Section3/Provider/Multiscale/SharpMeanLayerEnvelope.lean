/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SharpLayerEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpSimplexMean
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedConclusion

/-!
# SharpMeanLayerEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-- The affine mass-plus-wave expression used to compare sharp mean budgets. -/
def probeSharpMeanAffine (B C mass wave : ℝ) : ℝ :=
  B * mass + C * Real.sqrt mass * wave

theorem probeSharpMeanAffine_mono {B C mass mass' wave wave' : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hwave : 0 ≤ wave)
    (hmass_le : mass ≤ mass') (hwave_le : wave ≤ wave') :
    probeSharpMeanAffine B C mass wave ≤
      probeSharpMeanAffine B C mass' wave' := by
  unfold probeSharpMeanAffine
  have hsqrt : Real.sqrt mass ≤ Real.sqrt mass' := Real.sqrt_le_sqrt hmass_le
  have hprod : Real.sqrt mass * wave ≤ Real.sqrt mass' * wave' :=
    mul_le_mul hsqrt hwave_le hwave (Real.sqrt_nonneg _)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmass_le hB)
    (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hC)

/-- The geometric envelope for the mass of a Whitney layer. -/
def probeSharpLayerMassEnvelope (d n : ℕ) : ℝ :=
  6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ))

/-- The five-term wave envelope used for one Whitney layer.  The seam re-gauging
factor is deliberately visible. -/
def probeSharpLayerWaveEnvelope (M : ABKModel d) (m : ℤ) (E b : ℝ)
    (k₀ n : ℕ) (L : ℤ) (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^ (2 * M.gamma * (hsep M m E b omega : ℝ)) *
    (5 * (d : ℝ) ^ 2 *
      (waveHeadTerm M m E b (probeSharpLayerAnchor m b k₀ n) omega ^ 2 +
        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2 +
        probeDeepBandGaugedTail M (originCube d m)
            (probeSharpLayerAnchor m b k₀ n) k₀ k₀ omega ^ 2 +
        probeSharpAfterBandTerm M m
            (probeSharpLayerAnchor m b k₀ n) k₀ L omega ^ 2 +
        waveTailTerm M m E b m
            (probeSharpLayerAnchor m b k₀ n) omega ^ 2))


end

end Algsuperdiff.Section3.Provider.Multiscale
