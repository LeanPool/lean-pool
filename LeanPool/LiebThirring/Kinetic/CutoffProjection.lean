/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.Cutoff
public import LeanPool.LiebThirring.Fourier.IntegralL2

/-!
# Cutoff integrals represent the L² projections

The literal low-frequency part of the L² Fourier transform.

The spatial low projection is inverse L² Fourier of the cutoff class.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace LiebThirring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal low-frequency part of the L² Fourier transform. -/
@[expose] noncomputable def lowFrequencyClass (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) : Lp H 2 (volume : Measure Position) :=
  ((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
    (measurableSet_lowMomentumRegion E)).toLp
      ((lowMomentumRegion E).indicator
        (Lp.fourierTransformₗᵢ Position H h : Position → H))

/-- The spatial low projection is inverse L² Fourier of the cutoff class. -/
@[expose] noncomputable def lowFourierProjection (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) : Lp H 2 (volume : Measure Position) :=
  𝓕⁻ (lowFrequencyClass h E)

/-- The continuous raw low field represents the exact inverse L² projection. -/
theorem lowFourierProjection_ae (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) :
    (lowFourierProjection h E : Position → H) =ᵐ[volume] lowFourierField h E :=
  Fourier.fourierInv_toLp_ae_eq (integrable_lowFourierRepresentative h E hE)
    ((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
      (measurableSet_lowMomentumRegion E))

/-- The literal complementary high-frequency class. -/
@[expose] noncomputable def highFrequencyClass (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) : Lp H 2 (volume : Measure Position) :=
  ((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
    (measurableSet_lowMomentumRegion E).compl).toLp
      ((lowMomentumRegion E)ᶜ.indicator
        (Lp.fourierTransformₗᵢ Position H h : Position → H))

/-- The complementary frequency class is Fourier minus its low-frequency part. -/
theorem highFrequencyClass_eq_sub (h : Lp H 2 (volume : Measure Position)) (E : ℝ) :
    highFrequencyClass h E = 𝓕 h - lowFrequencyClass h E := by
  apply Lp.ext
  filter_upwards [
    ((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
      (measurableSet_lowMomentumRegion E).compl).coeFn_toLp,
    ((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
      (measurableSet_lowMomentumRegion E)).coeFn_toLp,
    Lp.coeFn_sub (𝓕 h) (lowFrequencyClass h E)] with ξ hh hl hs
  change highFrequencyClass h E ξ = _ at hh
  change lowFrequencyClass h E ξ = _ at hl
  rw [hh, hs, Pi.sub_apply, hl]
  change (lowMomentumRegion E)ᶜ.indicator ((Lp.fourierTransformₗᵢ Position H h : Lp H 2 volume) :
    Position → H) ξ =
    (Lp.fourierTransformₗᵢ Position H h) ξ - (lowMomentumRegion E).indicator
      ((Lp.fourierTransformₗᵢ Position H h : Lp H 2 volume) : Position → H) ξ
  by_cases hξ : ξ ∈ lowMomentumRegion E
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hξ),
      Set.indicator_of_mem hξ, sub_self]
  · rw [Set.indicator_of_mem (show ξ ∈ (lowMomentumRegion E)ᶜ from hξ),
      Set.indicator_of_notMem hξ, sub_zero]

/-- The fixed representative difference represents inverse L² high projection. -/
theorem highFourierProjection_ae (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) (f : Position → H) (hf : (h : Position → H) =ᵐ[volume] f) :
    ((𝓕⁻ (highFrequencyClass h E) : Lp H 2 volume) : Position → H) =ᵐ[volume]
      (fun x => f x - lowFourierField h E x) := by
  have heq : (𝓕⁻ (highFrequencyClass h E) : Lp H 2 volume) =
      h - lowFourierProjection h E := by
    rw [highFrequencyClass_eq_sub]
    change (Lp.fourierTransformₗᵢ Position H).symm
      ((Lp.fourierTransformₗᵢ Position H) h - lowFrequencyClass h E) = _
    rw [map_sub, LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [heq]
  filter_upwards [Lp.coeFn_sub h (lowFourierProjection h E), hf,
    lowFourierProjection_ae h E hE] with x hs hh hl
  exact hs.trans (congrArg₂ (fun a b : H => a - b) hh hl)

end LiebThirring
end
