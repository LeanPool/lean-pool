/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildHeatContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildJIntegral

/-!
# The clamped tensor paths for the local mild map

These extensions let the translated Stokes integral use a fixed time interval
while agreeing with the trajectory on its lifespan.
-/

public section

open MeasureTheory
open scoped Topology

noncomputable section

namespace CKN.Leray

/-- Clamp real time to the closed interval on which a mild trajectory is
defined. -/
@[expose]
def regularizedMildTimeClamp (T : ℝ) (hT : 0 ≤ T) :
    ℝ → RegularizedMildTimeInterval T := fun s =>
  ⟨min T (max 0 s), le_min hT (le_max_left 0 s), min_le_left _ _⟩

/-- The clamping map is continuous. -/
theorem regularizedMildTimeClamp_continuous (T : ℝ) (hT : 0 ≤ T) :
    Continuous (regularizedMildTimeClamp T hT) := by
  apply (continuous_const.min (continuous_const.max continuous_id)).subtype_mk

/-- Clamping does not change a time already in the trajectory interval. -/
theorem regularizedMildTimeClamp_eq_of_mem (T : ℝ) (hT : 0 ≤ T)
    {s : ℝ} (hs : s ∈ RegularizedMildTimeInterval T) :
    regularizedMildTimeClamp T hT s = ⟨s, hs⟩ := by
  apply Subtype.ext
  simp [regularizedMildTimeClamp, max_eq_right hs.1, min_eq_right hs.2]

/-- Extend a trajectory's regularized tensor to every real time by clamping
its argument to the interval. -/
@[expose]
def regularizedMildClampedTensorTrajectory (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    ℝ → RealTensorL2 := fun s =>
  regularizedMildTensor ρ ε hε (u (regularizedMildTimeClamp T hT s))

/-- The clamped tensor path is continuous. -/
theorem regularizedMildClampedTensorTrajectory_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (T : ℝ)
    (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    Continuous (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact regularizedMildTensor_continuousAt ρ ε hε
    (fun q => u (regularizedMildTimeClamp T hT q))
    (u (regularizedMildTimeClamp T hT s))
    ((u.continuous.comp (regularizedMildTimeClamp_continuous T hT)).continuousAt)

/-- A uniform trajectory bound gives the source quadratic tensor bound on
the clamped path. -/
theorem regularizedMildClampedTensorTrajectory_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (T : ℝ)
    (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (R : ℝ) (hR : 0 ≤ R) (hu : ∀ t, ‖u t‖ ≤ R) :
    ∀ s, ‖regularizedMildClampedTensorTrajectory ρ ε hε T hT u s‖ ≤
      regularizedMildMollifierConstant ρ ε * R ^ 2 := by
  intro s
  have hK : 0 ≤ regularizedMildMollifierConstant ρ ε := ENNReal.toReal_nonneg
  have hvalue : ‖u (regularizedMildTimeClamp T hT s)‖ ≤ R :=
    hu (regularizedMildTimeClamp T hT s)
  have hsq : ‖u (regularizedMildTimeClamp T hT s)‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).2 hvalue
  calc
    ‖regularizedMildClampedTensorTrajectory ρ ε hε T hT u s‖ ≤
        regularizedMildMollifierConstant ρ ε *
          ‖u (regularizedMildTimeClamp T hT s)‖ ^ 2 :=
      regularizedMildTensor_norm_le ρ ε hε _
    _ ≤ regularizedMildMollifierConstant ρ ε * R ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hK

/-- The difference of two clamped tensor paths is controlled by the
supremum-norm distance between their trajectories on a common ball. -/
theorem regularizedMildClampedTensorTrajectory_sub_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (T : ℝ)
    (hT : 0 ≤ T) (u v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ t, ‖u t‖ ≤ R) (hv : ∀ t, ‖v t‖ ≤ R) :
    ∀ s, ‖regularizedMildClampedTensorTrajectory ρ ε hε T hT u s -
        regularizedMildClampedTensorTrajectory ρ ε hε T hT v s‖ ≤
      regularizedMildMollifierConstant ρ ε * (2 * R) * ‖u - v‖ := by
  intro s
  let q := regularizedMildTimeClamp T hT s
  have hK : 0 ≤ regularizedMildMollifierConstant ρ ε := ENNReal.toReal_nonneg
  have huq : ‖u q‖ ≤ R := hu q
  have hvq : ‖v q‖ ≤ R := hv q
  have hdiff : ‖u q - v q‖ ≤ ‖u - v‖ := by
    simpa using (u - v).norm_coe_le_norm q
  calc
    ‖regularizedMildClampedTensorTrajectory ρ ε hε T hT u s -
        regularizedMildClampedTensorTrajectory ρ ε hε T hT v s‖ ≤
      regularizedMildMollifierConstant ρ ε * (‖u q‖ + ‖v q‖) * ‖u q - v q‖ := by
        simpa [regularizedMildClampedTensorTrajectory, q] using
          regularizedMildTensor_sub_norm_le ρ ε hε (u q) (v q)
    _ ≤ regularizedMildMollifierConstant ρ ε * (2 * R) * ‖u - v‖ := by
      calc
        regularizedMildMollifierConstant ρ ε * (‖u q‖ + ‖v q‖) * ‖u q - v q‖ ≤
          regularizedMildMollifierConstant ρ ε * (R + R) * ‖u - v‖ := by
            gcongr
        _ = regularizedMildMollifierConstant ρ ε * (2 * R) * ‖u - v‖ := by ring

/-- The right-hand side of the mild equation, written with the translated
integral over the fixed interval `[0,T]`. -/
@[expose]
noncomputable def regularizedMildLocalMap (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    C(RegularizedMildTimeInterval T, RealVectorL2) := by
  let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u
  let C := regularizedMildMollifierConstant ρ ε * ‖u‖ ^ 2
  have hFcont : Continuous F := by
    exact regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
  have hu : ∀ t, ‖u t‖ ≤ ‖u‖ :=
    (regularizedMildTrajectory_norm_le_iff T u ‖u‖ (norm_nonneg _)).1 le_rfl
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    simpa [F, C] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT u
        ‖u‖ (norm_nonneg _) hu
  have hC : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg ‖u‖)
  let nonnegativeTime : RegularizedMildTimeInterval T → {s : ℝ // 0 ≤ s} :=
    fun t => ⟨t, t.2.1⟩
  have hnonnegativeTime : Continuous nonnegativeTime :=
    continuous_subtype_val.subtype_mk fun t => t.2.1
  have hheat : Continuous
      (fun t : RegularizedMildTimeInterval T => realHeatOperator t.1 t.2.1 b) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hAt := (realHeatOperator_continuousAt t.2.1 b).comp
      hnonnegativeTime.continuousAt
    change ContinuousAt
      (fun q => realHeatOperator (nonnegativeTime q).1 (nonnegativeTime q).2 b) t
    exact hAt
  have hintegral : Continuous (fun t : RegularizedMildTimeInterval T =>
      ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ) := by
    exact (mildShiftedStokesIntegral_continuous F hFcont C hFC hC T hT).comp
      continuous_subtype_val
  exact ⟨fun t => realHeatOperator t.1 t.2.1 b -
      ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ,
    hheat.sub hintegral⟩

/-- The value of the local map is the heat evolution minus the translated
Stokes integral. -/
theorem regularizedMildLocalMap_eq_shifted
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    regularizedMildLocalMap ρ ε hε b T hT u t =
      realHeatOperator t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          mildShiftedStokesIntegrand
            (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 τ := by
  rfl

private theorem regularizedMildClampedIntegral_eq_source
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (T : ℝ)
    (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    regularizedMildStokesIntegral
        (fun s => if hs : s ∈ RegularizedMildTimeInterval T then
          regularizedMildTensor ρ ε hε (u ⟨s, hs⟩) else 0) t.1 =
      regularizedMildStokesIntegral
        (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 := by
  unfold regularizedMildStokesIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hsT : s ∈ RegularizedMildTimeInterval T :=
    ⟨hs.1, le_trans hs.2 t.2.2⟩
  have hclamp := regularizedMildTimeClamp_eq_of_mem T hT hsT
  have hclampedF : regularizedMildClampedTensorTrajectory ρ ε hε T hT u s =
      regularizedMildTensor ρ ε hε (u ⟨s, hsT⟩) := by
    simp [regularizedMildClampedTensorTrajectory, hclamp]
  by_cases hst : s < t.1
  · simp [regularizedMildStokesIntegrand, hst, hclampedF,
      RegularizedMildTimeInterval, hsT]
  · simp [regularizedMildStokesIntegrand, hst]

/-- The local map agrees with the mild equation `eq:reg-mild` on the
trajectory interval. -/
theorem regularizedMildLocalMap_eq_rightHandSide
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    regularizedMildLocalMap ρ ε hε b T hT u t =
      regularizedMildRightHandSide b
        (fun s => if hs : s ∈ RegularizedMildTimeInterval T then
          regularizedMildTensor ρ ε hε (u ⟨s, hs⟩) else 0)
        t.1 t.2.1 := by
  let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u
  let C := regularizedMildMollifierConstant ρ ε * ‖u‖ ^ 2
  have hFcont : Continuous F :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
  have hu : ∀ s, ‖u s‖ ≤ ‖u‖ :=
    (regularizedMildTrajectory_norm_le_iff T u ‖u‖ (norm_nonneg _)).1 le_rfl
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    simpa [F, C] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT u
        ‖u‖ (norm_nonneg _) hu
  have hC : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg ‖u‖)
  have hsource := regularizedMildClampedIntegral_eq_source ρ ε hε T hT u t
  dsimp only [regularizedMildLocalMap]
  rw [regularizedMildRightHandSide, hsource,
    regularizedMildStokesIntegral_eq_shifted T t.1 hT t.2.1 t.2.2
      hFcont C hFC hC]
  rfl

/-- The local mild map takes values in the closed Leray data space. -/
theorem regularizedMildLocalMap_isInJ
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    (hb : RegularizedMildJData b) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    RegularizedMildJData (regularizedMildLocalMap ρ ε hε b T hT u t) := by
  let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u
  let C := regularizedMildMollifierConstant ρ ε * ‖u‖ ^ 2
  have hFcont : Continuous F :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
  have hu : ∀ s, ‖u s‖ ≤ ‖u‖ :=
    (regularizedMildTrajectory_norm_le_iff T u ‖u‖ (norm_nonneg _)).1 le_rfl
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    simpa [F, C] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT u
        ‖u‖ (norm_nonneg _) hu
  have hC : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg ‖u‖)
  have hheat := realHeatOperator_isInJ t.2.1 b hb
  have hstokes := regularizedMildStokesIntegral_isInJ F hFcont C T t.1
    hFC hC hT hTpos t.2.1 t.2.2
  have hsub := regularizedMildJData_sub hheat hstokes
  have hEq : regularizedMildLocalMap ρ ε hε b T hT u t =
      realHeatOperator t.1 t.2.1 b - regularizedMildStokesIntegral F t.1 := by
    rw [regularizedMildLocalMap_eq_rightHandSide ρ ε hε b T hT u t,
      regularizedMildRightHandSide,
      regularizedMildClampedIntegral_eq_source ρ ε hε T hT u t]
  rw [hEq]
  exact hsub

end CKN.Leray

end
