/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalShiftPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealDuhamelRestart
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealShiftedStokesTruncation

/-!
# Restart of the global real mild trajectory

The global regularized mild curve satisfies the same mild equation
when viewed from any nonnegative start time.
-/

public section

open MeasureTheory
open scoped Interval ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The global mild curve restricted after a nonnegative start time is
a mild trajectory with its state at that time as initial datum. -/
theorem regularizedGlobalMildCurve_shift_isTrajectory
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    IsRegularizedMildTrajectory ρ ε hε
      (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a) T
      (regularizedGlobalMildCurveShiftPath ρ ε hε b₀ hbJ a T) := by
  let L := a + T
  have hL : 0 ≤ L := add_nonneg ha hT
  let U := regularizedGlobalMildCurve ρ ε hε b₀ hbJ
  let V : C(RegularizedMildTimeInterval L, RealVectorL2) :=
    ⟨fun s => U s.1,
      (regularizedGlobalMildCurve_continuous ρ ε hε b₀ hbJ).comp
        continuous_subtype_val⟩
  let W := regularizedGlobalMildCurveShiftPath ρ ε hε b₀ hbJ a T
  let F := regularizedMildClampedTensorTrajectory ρ ε hε L hL V
  let G := regularizedMildClampedTensorTrajectory ρ ε hε T hT W
  have hVbound : ∀ s, ‖V s‖ ≤ ‖b₀‖ := by
    intro s
    exact regularizedGlobalMildCurve_norm_le_initial
      ρ ε hε b₀ hbJ s.1 s.2.1
  have hWbound : ∀ s, ‖W s‖ ≤ ‖b₀‖ := by
    intro s
    exact regularizedGlobalMildCurve_norm_le_initial
      ρ ε hε b₀ hbJ (a + s.1) (add_nonneg ha s.2.1)
  have hFcont : Continuous F :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε L hL V
  have hGcont : Continuous G :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT W
  let C := regularizedMildMollifierConstant ρ ε * ‖b₀‖ ^ 2
  have hC : 0 ≤ C :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hFbound : ∀ s, ‖F s‖ ≤ C :=
    regularizedMildClampedTensorTrajectory_norm_le
      ρ ε hε L hL V ‖b₀‖ (norm_nonneg b₀) hVbound
  have hGbound : ∀ s, ‖G s‖ ≤ C :=
    regularizedMildClampedTensorTrajectory_norm_le
      ρ ε hε T hT W ‖b₀‖ (norm_nonneg b₀) hWbound
  have htraj : IsRegularizedMildTrajectory ρ ε hε b₀ L V :=
    regularizedGlobalMildCurve_isTrajectory ρ ε hε b₀ hbJ L
  have hVmild (s : RegularizedMildTimeInterval L) :
      V s = realHeatOperator s.1 s.2.1 b₀ -
        ∫ τ in (0 : ℝ)..L, mildShiftedStokesIntegrand F s.1 τ := by
    calc
      V s = regularizedMildRightHandSide b₀
        (fun r => if hr : r ∈ RegularizedMildTimeInterval L then
          regularizedMildTensor ρ ε hε (V ⟨r, hr⟩) else 0) s.1 s.2.1 :=
            htraj s
      _ = regularizedMildLocalMap ρ ε hε b₀ L hL V s :=
        (regularizedMildLocalMap_eq_rightHandSide ρ ε hε b₀ L hL V s).symm
      _ = _ := regularizedMildLocalMap_eq_shifted ρ ε hε b₀ L hL V s
  intro t
  have hat : a + t.1 ≤ L := by dsimp [L]; linarith only [t.2.2]
  have haL : a ≤ L := by dsimp [L]; linarith only [hT]
  let ta : RegularizedMildTimeInterval L := ⟨a, ha, haL⟩
  let tat : RegularizedMildTimeInterval L :=
    ⟨a + t.1, add_nonneg ha t.2.1, hat⟩
  have hIntA : IntervalIntegrable
      (mildShiftedStokesIntegrand F a) volume 0 L :=
    mildShiftedStokesIntegrand_intervalIntegrable
      F hFcont C hFbound hC L a hL
  have hIntAT : IntervalIntegrable
      (mildShiftedStokesIntegrand F (a + t.1)) volume 0 L :=
    mildShiftedStokesIntegrand_intervalIntegrable
      F hFcont C hFbound hC L (a + t.1) hL
  have hA : U a = realHeatOperator a ha b₀ -
      ∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ := by
    have h := hVmild ta
    change U a = realHeatOperator a ha b₀ -
      ∫ τ in (0 : ℝ)..L, mildShiftedStokesIntegrand F a τ at h
    rw [mildShiftedStokesIntegral_truncate F L a ha haL hIntA] at h
    exact h
  have hAT : U (a + t.1) =
      realHeatOperator (a + t.1) (add_nonneg ha t.2.1) b₀ -
        ∫ τ in (0 : ℝ)..(a + t.1),
          mildShiftedStokesIntegrand F (a + t.1) τ := by
    have h := hVmild tat
    change U (a + t.1) =
      realHeatOperator (a + t.1) (add_nonneg ha t.2.1) b₀ -
        ∫ τ in (0 : ℝ)..L,
          mildShiftedStokesIntegrand F (a + t.1) τ at h
    rw [mildShiftedStokesIntegral_truncate
      F L (a + t.1) (add_nonneg ha t.2.1) hat hIntAT] at h
    exact h
  have hRestart := regularisedRealDuhamel_restart
    F hFcont C hFbound hC b₀ a t.1 ha t.2.1
  have hR : U (a + t.1) = realHeatOperator t.1 t.2.1 (U a) -
      ∫ τ in (0 : ℝ)..t.1,
        mildShiftedStokesIntegrand F (a + t.1) τ := by
    rw [← hA, ← hAT] at hRestart
    exact hRestart.symm
  have hIntG : IntervalIntegrable
      (mildShiftedStokesIntegrand G t.1) volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable
      G hGcont C hGbound hC T t.1 hT
  have hGtrunc := mildShiftedStokesIntegral_truncate
    G T t.1 t.2.1 t.2.2 hIntG
  have hFG : (∫ τ in (0 : ℝ)..t.1,
      mildShiftedStokesIntegrand F (a + t.1) τ) =
      ∫ τ in (0 : ℝ)..t.1,
        mildShiftedStokesIntegrand G t.1 τ := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.2.1
    intro τ hτ
    have hτT : τ < a + t.1 := by linarith only [ha, hτ.2]
    have hτpos : 0 < τ := hτ.1
    have hτt : τ < t.1 := hτ.2
    simp only [mildShiftedStokesIntegrand,
      dite_eq_left (show 0 < τ ∧ τ < a + t.1 from ⟨hτpos, hτT⟩),
      dite_eq_left (show 0 < τ ∧ τ < t.1 from ⟨hτpos, hτt⟩)]
    congr 1
    have hsL : a + t.1 - τ ∈ RegularizedMildTimeInterval L := by
      constructor
      · linarith only [ha, hτt]
      · linarith only [hat, hτpos]
    have hsT : t.1 - τ ∈ RegularizedMildTimeInterval T := by
      constructor
      · linarith only [hτt]
      · linarith only [t.2.2, hτpos]
    have hclampL := regularizedMildTimeClamp_eq_of_mem L hL hsL
    have hclampT := regularizedMildTimeClamp_eq_of_mem T hT hsT
    change regularizedMildTensor ρ ε hε
      (V (regularizedMildTimeClamp L hL (a + t.1 - τ))) =
      regularizedMildTensor ρ ε hε
        (W (regularizedMildTimeClamp T hT (t.1 - τ)))
    rw [hclampL, hclampT]
    change regularizedMildTensor ρ ε hε (U (a + t.1 - τ)) =
      regularizedMildTensor ρ ε hε (U (a + (t.1 - τ)))
    congr 1
    ring_nf
  have hWlocal : W t = regularizedMildLocalMap ρ ε hε (U a) T hT W t := by
    rw [regularizedMildLocalMap_eq_shifted]
    change U (a + t.1) = realHeatOperator t.1 t.2.1 (U a) -
      ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand G t.1 τ
    rw [hGtrunc, ← hFG]
    exact hR
  exact hWlocal.trans
    (regularizedMildLocalMap_eq_rightHandSide ρ ε hε (U a) T hT W t)

end CKN.Leray

end
