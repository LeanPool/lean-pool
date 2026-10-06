/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedGlobal
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalParameters

/-!
# Global mild evolution of the regularized equation

The zero-force instance of the forced construction gives a global mild
trajectory. Its restriction agrees with the local mild solution by
unrestricted mild uniqueness.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The Leray-projected heat operator sends the zero field to zero. -/
theorem forcedHeatLeray_zero (τ : ℝ) (hτ : 0 ≤ τ) :
    forcedHeatLeray τ hτ (0 : RealVectorL2) = 0 := by
  have hProj : lerayProjectionL2 (0 : ComplexVectorL2) = 0 := by
    apply norm_eq_zero.mp
    have h := lerayProjectionL2_norm_le (0 : ComplexVectorL2)
    simpa using h
  have hHeat : heatSemigroup τ hτ (0 : ComplexVectorL2) = 0 := by
    apply norm_eq_zero.mp
    have h := heatSemigroup_norm_le τ hτ (0 : ComplexVectorL2)
    simpa using h
  simp [forcedHeatLeray, hProj, hHeat]

/-- The zero forcing term has no Duhamel contribution. -/
theorem forcedForceDuhamel_zero (t : ℝ) :
    forcedForceDuhamel (fun _ : ℝ => (0 : RealVectorL2)) t = 0 := by
  simp [forcedForceDuhamel, forcedForceIntegrand, forcedHeatLeray_zero]

/-- The zero-force specialization of the forced solution curve. -/
@[expose]
def regularizedGlobalMildCurve
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    ℝ → RealVectorL2 :=
  forcedSolutionCurve ρ ε hε b hb (h := fun _ => 0)
    stronglyMeasurable_const (fun T => by simp) 

/-- The zero-force global mild curve is continuous in spatial L². -/
theorem regularizedGlobalMildCurve_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    Continuous (regularizedGlobalMildCurve ρ ε hε b hb) := by
  unfold regularizedGlobalMildCurve
  exact continuous_forcedSolutionCurve ρ ε hε b hb
    stronglyMeasurable_const (fun T => by simp)

/-- Every nonnegative-time state of the zero-force mild curve belongs to
the divergence-free L² space. -/
theorem regularizedGlobalMildCurve_mildJData
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b)
    (t : ℝ) (ht : 0 ≤ t) :
    RegularizedMildJData (regularizedGlobalMildCurve ρ ε hε b hb t) := by
  unfold regularizedGlobalMildCurve
  exact forcedSolutionCurve_mildJData ρ ε hε b hb
    stronglyMeasurable_const (fun T => by simp) ht

/-- The global zero-force mild curve starts at the prescribed L² state. -/
theorem regularizedGlobalMildCurve_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    regularizedGlobalMildCurve ρ ε hε b hb 0 = b := by
  unfold regularizedGlobalMildCurve
  exact forcedSolutionCurve_zero ρ ε hε b hb
    stronglyMeasurable_const (fun T => by simp)

/-- The zero-force global mild curve has nonincreasing L² norm. -/
theorem regularizedGlobalMildCurve_norm_le_initial
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖regularizedGlobalMildCurve ρ ε hε b hb t‖ ≤ ‖b‖ := by
  obtain ⟨v, -, -, -, henergy⟩ :=
    forcedSolutionCurve_energy ρ ε hε b hb (h := fun _ => 0)
      stronglyMeasurable_const (fun T => by simp) ht
  have hbalance := henergy t ⟨ht, le_rfl⟩
  have hD : 0 ≤ ∫ s in Ioc 0 t, forcedFourierDissipation (v s) := by
    exact integral_nonneg (fun s => forcedFourierDissipation_nonneg (v s))
  simp only [inner_zero_right, integral_zero, mul_zero, add_zero] at hbalance
  have hnormSq : ‖regularizedGlobalMildCurve ρ ε hε b hb t‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    simpa only [regularizedGlobalMildCurve] using
      (show ‖forcedSolutionCurve ρ ε hε b hb
            stronglyMeasurable_const (fun T => by simp) t‖ ^ 2 ≤ ‖b‖ ^ 2 by
        linarith only [hbalance, hD])
  nlinarith only [hnormSq, norm_nonneg b,
    norm_nonneg (regularizedGlobalMildCurve ρ ε hε b hb t)]

/-- The global zero-force curve satisfies the same nonlinear mild equation
at every nonnegative time. -/
theorem regularizedGlobalMildCurve_mild
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b)
    (t : ℝ) (ht : 0 ≤ t) :
    regularizedGlobalMildCurve ρ ε hε b hb t =
      realHeatOperator t ht b -
        regularizedMildStokesIntegral
          (regularizedMildTensorTrajectory ρ ε hε
            (regularizedGlobalMildCurve ρ ε hε b hb)) t := by
  have h := forcedSolutionCurve_mild ρ ε hε b hb (h := fun _ => 0)
    stronglyMeasurable_const (fun T => by simp) ht
  unfold regularizedGlobalMildCurve regularizedMildTensorTrajectory
  simpa only [forcedMildRHS, forcedForceDuhamel_zero, add_zero] using h

/-- The global zero-force curve restricts to a mild trajectory on every
finite nonnegative interval. -/
theorem regularizedGlobalMildCurve_isTrajectory
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b)
    (T : ℝ) :
    IsRegularizedMildTrajectory ρ ε hε b T
      ⟨fun t : RegularizedMildTimeInterval T =>
          regularizedGlobalMildCurve ρ ε hε b hb t.1,
        (regularizedGlobalMildCurve_continuous ρ ε hε b hb).comp
          continuous_subtype_val⟩ := by
  intro t
  have hmild := regularizedGlobalMildCurve_mild ρ ε hε b hb t.1 t.2.1
  change regularizedGlobalMildCurve ρ ε hε b hb t.1 =
    regularizedMildRightHandSide b
      (fun s => if hs : s ∈ RegularizedMildTimeInterval T then
        regularizedMildTensor ρ ε hε
          (regularizedGlobalMildCurve ρ ε hε b hb (⟨s, hs⟩ :
            RegularizedMildTimeInterval T).1) else 0) t.1 t.2.1
  rw [hmild]
  unfold regularizedMildRightHandSide
  congr 1
  apply regularizedMildStokesIntegral_congr_Icc
  intro s hs
  have hsT : s ∈ RegularizedMildTimeInterval T :=
    ⟨hs.1, hs.2.trans t.2.2⟩
  simp only [regularizedMildTensorTrajectory, dite_eq_left hsT]

end CKN.Leray

end
