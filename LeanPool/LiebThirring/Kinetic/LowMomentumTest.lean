/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.Cutoff

/-!
# One-particle test vectors for low Fourier fields

Literal Fourier-side spin test with negative phase.

The Fourier-side test has the norm of a constant unit-spin indicator.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace LiebThirring

/-- Literal Fourier-side spin test with negative phase. -/
@[expose] noncomputable def lowMomentumTestFourierFunction {q : ℕ} (E : ℝ)
    (x : Position) (s : Fin q) : Position → EuclideanSpace ℂ (Fin q) :=
  (lowMomentumRegion E).indicator (fun ξ =>
    EuclideanSpace.single s (Real.fourierChar (-inner ℝ ξ x) : ℂ))

/-- The Fourier-side test has the norm of a constant unit-spin indicator. -/
theorem norm_lowMomentumTestFourierFunction {q : ℕ} (E : ℝ)
    (x ξ : Position) (s : Fin q) :
    ‖lowMomentumTestFourierFunction E x s ξ‖ =
      ‖(lowMomentumRegion E).indicator
        (fun _ => EuclideanSpace.single s (1 : ℂ)) ξ‖ := by
  classical
  by_cases hξ : ξ ∈ lowMomentumRegion E
  · simp only [lowMomentumTestFourierFunction, Set.indicator_of_mem hξ,
      PiLp.norm_single, Circle.norm_coe, norm_one]
  · simp only [lowMomentumTestFourierFunction, Set.indicator_of_notMem hξ]

/-- Every Fourier-side test is strongly measurable. -/
theorem stronglyMeasurable_lowMomentumTestFourierFunction {q : ℕ} (E : ℝ)
    (x : Position) (s : Fin q) :
    StronglyMeasurable (lowMomentumTestFourierFunction E x s) := by
  have hc : Continuous (fun ξ : Position =>
      EuclideanSpace.single s (Real.fourierChar (-inner ℝ ξ x) : ℂ)) := by
    classical
    change Continuous (fun ξ : Position =>
      WithLp.toLp 2 (Pi.single s (Real.fourierChar (-inner ℝ ξ x) : ℂ) : Fin q → ℂ))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℂ)).comp
    apply continuous_pi
    intro t
    simp only [Pi.single_apply]
    split_ifs <;> fun_prop
  exact hc.stronglyMeasurable.indicator (measurableSet_lowMomentumRegion E)

/-- Finite low-region volume makes the literal Fourier-side test an L² function. -/
theorem memLp_lowMomentumTestFourierFunction {q : ℕ} (E : ℝ) (hE : 0 ≤ E)
    (x : Position) (s : Fin q) :
    MemLp (lowMomentumTestFourierFunction E x s) 2 (volume : Measure Position) := by
  have hc : MemLp ((lowMomentumRegion E).indicator
      (fun _ : Position => EuclideanSpace.single s (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_lowMomentumRegion E)
      (EuclideanSpace.single s (1 : ℂ)) (Or.inr (volume_lowMomentumRegion_ne_top E hE))
  exact hc.congr_norm (stronglyMeasurable_lowMomentumTestFourierFunction E x s).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => (norm_lowMomentumTestFourierFunction E x ξ s).symm))

/-- The exact Fourier-side L² class of the cutoff spin test. -/
@[expose] noncomputable def lowMomentumTestFrequencyClass {q : ℕ} (E : ℝ) (hE : 0 ≤ E)
    (x : Position) (s : Fin q) : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) :=
  (memLp_lowMomentumTestFourierFunction E hE x s).toLp
    (lowMomentumTestFourierFunction E x s)

/-- The spatial one-particle cutoff test is inverse L² Fourier of its literal frequency class. -/
@[expose] noncomputable def lowMomentumTest {q : ℕ} (E : ℝ)
    (x : Position) (s : Fin q) (hE : 0 ≤ E) : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure
      Position) :=
  𝓕⁻ (lowMomentumTestFrequencyClass E hE x s)

/-- Fourier of the test is exactly the prescribed cutoff frequency class. -/
theorem fourier_lowMomentumTest {q : ℕ} (E : ℝ) (hE : 0 ≤ E)
    (x : Position) (s : Fin q) :
    𝓕 (lowMomentumTest E x s hE) = lowMomentumTestFrequencyClass E hE x s :=
  FourierTransform.fourier_fourierInv_eq _

/-- One common literal negative-phase Fourier representative for the test. -/
theorem lowMomentumTest_fourier_ae {q : ℕ} (E : ℝ) (hE : 0 ≤ E)
    (x : Position) (s : Fin q) :
    ((𝓕 (lowMomentumTest E x s hE) : Lp (EuclideanSpace ℂ (Fin q)) 2 volume) :
      Position → EuclideanSpace ℂ (Fin q)) =ᵐ[volume] lowMomentumTestFourierFunction E x s := by
  rw [fourier_lowMomentumTest]
  exact (memLp_lowMomentumTestFourierFunction E hE x s).coeFn_toLp

/-- The test has squared norm equal to the finite low-region volume. -/
theorem lowMomentumTest_norm_sq {q : ℕ} (E : ℝ) (hE : 0 ≤ E)
    (x : Position) (s : Fin q) :
    ‖lowMomentumTest E x s hE‖ ^ 2 = (volume (lowMomentumRegion E)).toReal := by
  classical
  have hn : ‖lowMomentumTestFrequencyClass E hE x s‖ =
      ‖indicatorConstLp (μ := (volume : Measure Position)) 2
        (measurableSet_lowMomentumRegion E) (volume_lowMomentumRegion_ne_top E hE)
        (EuclideanSpace.single s (1 : ℂ))‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
      (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [(memLp_lowMomentumTestFourierFunction E hE x s).coeFn_toLp,
      indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure Position))
        (hs := measurableSet_lowMomentumRegion E)
        (hμs := volume_lowMomentumRegion_ne_top E hE)
        (c := EuclideanSpace.single s (1 : ℂ))] with ξ hf hc
    change lowMomentumTestFrequencyClass E hE x s ξ = _ at hf
    rw [hf, hc]
    exact norm_lowMomentumTestFourierFunction E x ξ s
  change ‖(Lp.fourierTransformₗᵢ Position (EuclideanSpace ℂ (Fin q))).symm
    (lowMomentumTestFrequencyClass E hE x s)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, hn, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [PiLp.norm_single, norm_one, one_mul, ENNReal.toReal_ofNat, Measure.real,
    ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt ENNReal.toReal_nonneg

end LiebThirring
end
