/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DelayKernelTransfer
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
C145 exact U1 compile-free construction. Status UNKNOWN_UNCOMPILED.
All eight unchanged frozen U1 targets have candidate proof bodies below.
No elaboration, kernel, source-fidelity acceptance, or axiom verdict is asserted.
The nonlinear solution is constructed by a local inverse and linked to the ODE
by FTC in both directions; the ordinary second derivative is derived explicitly.
-/

@[expose] public section

noncomputable section
namespace C145.ActualResponse
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

/-- A real state indexed by the graph's vertices. -/
abbrev State (n : ℕ) := Fin (n + 1) → ℝ
/-- A real change of coordinates from modal indices to vertex indices. -/
abbrev Frame (n : ℕ) := Fin (n + 1) → Fin (n + 1) → ℝ
/-- The closed observation interval from zero to the horizon. -/
abbrev Time (T : ℝ) := Icc (0 : ℝ) T
/-- A continuous scalar forcing on the observation interval. -/
abbrev Input (T : ℝ) := C(Time T, ℝ)
/-- A continuous vertex-state trajectory on the observation interval. -/
abbrev Path (n : ℕ) (T : ℝ) := C(Time T, State n)
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- The right endpoint as a point of the observation interval. -/
def endTime (T : ℝ) (hT : 0 < T) : Time T :=
  ⟨T, hT.le, le_rfl⟩

/-- Extend a forcing to all real times by clipping to the observation interval. -/
def extendInput {T : ℝ} (hT : 0 < T) (f : Input T) (s : ℝ) : ℝ :=
  f (projIcc 0 T hT.le s)

/-- Extend a trajectory to all real times by clipping to the observation interval. -/
def extendPath {n : ℕ} {T : ℝ} (hT : 0 < T)
    (u : Path n T) (s : ℝ) : State n :=
  u (projIcc 0 T hT.le s)

/-- Restrict a continuous real forcing to the observation interval. -/
def restrictInput (T : ℝ) (g : ℝ → ℝ) (hg : Continuous g) : Input T :=
  ⟨fun t => g t, hg.comp continuous_subtype_val⟩

/-- Pair the vertex state with the signed measurement port. -/
def observe {n : ℕ} (b x : State n) : ℝ := ∑ v, b v * x v

/-- The spectral linear dynamics, coordinatewise square, and scalar forcing through the port. -/
def vectorField {n : ℕ} (Q : Frame n) (rates b : State n)
    (f : ℝ → ℝ) (t : ℝ) (x : State n) : State n :=
  fun v => (∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w * x w) +
    x v ^ 2 + b v * f t

/-- A bound built from the frame entries and the exponential factors on the time horizon. -/
def heatBound {n : ℕ} (Q : Frame n) (rates : State n) (T : ℝ) : ℝ :=
  1 + ∑ i, ∑ v, ∑ w,
    |Q v i| * |Q w i| * Real.exp (|rates i| * T)

/-- Integrate the forced heat response in interaction-picture coordinates. -/
def ipLinear {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) (t : ℝ) : State n :=
  ∫ s in (0 : ℝ)..t,
    extendInput hT f s • C145.Pulse.heatAction Q rates (-s) b

/-- Integrate the product of two trajectories after converting to and from the heat frame. -/
def ipQuadratic {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) (t : ℝ) : State n :=
  ∫ s in (0 : ℝ)..t, C145.Pulse.heatAction Q rates (-s)
    (fun x =>
      C145.Pulse.heatAction Q rates s (extendPath hT v s) x *
      C145.Pulse.heatAction Q rates s (extendPath hT w s) x)

/-- The interaction-picture fixed-point residual obtained by subtracting the quadratic term. -/
def ipResidual {n : ℕ} {T : ℝ}
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T) (v : Path n T) : Path n T :=
  v - B v v

/-- The first state variation as a heat convolution with the forcing direction. -/
def firstState {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (g : Input T) (t : ℝ) : State n :=
  ∫ s in (0 : ℝ)..t,
    extendInput hT g s • C145.Pulse.heatAction Q rates (t - s) b

/-- The bilinear second-order coefficient from the product of the first state variations. -/
def secondState {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (g h : Input T) (t : ℝ) : State n :=
  ∫ s in (0 : ℝ)..t, C145.Pulse.heatAction Q rates (t - s)
    (fun v => firstState hT Q rates b g s v * firstState hT Q rates b h s v)

/-- A response germ that maps zero to zero and solves the forced initial-value problem near zero. -/
def IsActualResponse {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (R : Input T → Path n T) : Prop :=
  R 0 = 0 ∧ ∀ᶠ f in 𝓝 (0 : Input T),
    extendPath hT (R f) 0 = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (extendPath hT (R f))
          (vectorField Q rates b (extendInput hT f) t (extendPath hT (R f) t))
          (Icc (0 : ℝ) T) t

/-- The derivative at zero of the observed response along one forcing direction. -/
def rawFirst {n : ℕ} {T : ℝ} (b : State n)
    (R : Input T → Path n T) (g : Input T) (t : Time T) : ℝ :=
  deriv (fun ε : ℝ => observe b (R (ε • g) t)) 0

/-- Half the second derivative at zero along one forcing direction. -/
def rawQuadratic {n : ℕ} {T : ℝ} (b : State n)
    (R : Input T → Path n T) (g : Input T) (t : Time T) : ℝ :=
  (1 / 2 : ℝ) * deriv (deriv (fun ε : ℝ => observe b (R (ε • g) t))) 0

/-- Half the mixed derivative of the observed response in two forcing directions. -/
def rawMixed {n : ℕ} {T : ℝ} (b : State n)
    (R : Input T → Path n T) (g h : Input T) (t : Time T) : ℝ :=
  (1 / 2 : ℝ) * deriv
    (fun ε : ℝ => deriv (fun δ : ℝ => observe b (R (ε • g + δ • h) t)) 0) 0

/-! Finite heat algebra. No positivity of rates or entries is used. -/

private theorem heatAction_vec_add {n : ℕ} (Q : Frame n) (rates x y : State n)
    (t : ℝ) :
    C145.Pulse.heatAction Q rates t (x + y) =
      C145.Pulse.heatAction Q rates t x + C145.Pulse.heatAction Q rates t y := by
  classical
  funext v
  simp only [C145.Pulse.heatAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem heatAction_vec_smul {n : ℕ} (Q : Frame n) (rates x : State n)
    (t c : ℝ) :
    C145.Pulse.heatAction Q rates t (c • x) =
      c • C145.Pulse.heatAction Q rates t x := by
  classical
  funext v
  simp only [C145.Pulse.heatAction, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, Q v i * Real.exp (-rates i * t) * (∑ u, Q u i * (c * x u))) =
        ∑ i, c * (Q v i * Real.exp (-rates i * t) * (∑ u, Q u i * x u)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hinner : (∑ u, Q u i * (c * x u)) = c * (∑ u, Q u i * x u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        ring
      rw [hinner]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem heatAction_mode {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (t : ℝ) (i : Fin (n + 1)) :
    (∑ v, Q v i * C145.Pulse.heatAction Q rates t x v) =
      Real.exp (-rates i * t) * (∑ u, Q u i * x u) := by
  classical
  unfold C145.Pulse.heatAction
  calc
    (∑ v, Q v i * (∑ j, Q v j * Real.exp (-rates j * t) * (∑ u, Q u j * x u))) =
        ∑ v, ∑ j, Q v i * (Q v j * Real.exp (-rates j * t) * (∑ u, Q u j * x u)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.mul_sum _ _ _
    _ = ∑ j, ∑ v, Q v i * (Q v j * Real.exp (-rates j * t) * (∑ u, Q u j * x u)) :=
      Finset.sum_comm
    _ = ∑ j, (∑ v, Q v i * Q v j) *
        (Real.exp (-rates j * t) * (∑ u, Q u j * x u)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = Real.exp (-rates i * t) * (∑ u, Q u i * x u) := by
      simp_rw [hQ i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

theorem heatAction_zero {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) :
    C145.Pulse.heatAction Q rates 0 x = x := by
  funext v
  simpa only [C145.Pulse.heatAction, mul_zero, Real.exp_zero, mul_one, mul_comm]
    using C145CoordinatePermutation.frame_reconstruction Q hQ x v

theorem heatAction_add {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (s t : ℝ) :
    C145.Pulse.heatAction Q rates (s + t) x =
      C145.Pulse.heatAction Q rates s (C145.Pulse.heatAction Q rates t x) := by
  classical
  funext v
  unfold C145.Pulse.heatAction
  apply Finset.sum_congr rfl
  intro i hi
  have hmode := heatAction_mode Q rates x hQ t i
  unfold C145.Pulse.heatAction at hmode
  rw [hmode]
  rw [mul_add, Real.exp_add]
  ring

private theorem generator_heat_mode {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (t : ℝ) (v : Fin (n + 1)) :
    (∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w *
      C145.Pulse.heatAction Q rates t x w) =
      ∑ i, Q v i * (Real.exp (-rates i * t) * (-rates i)) *
        (∑ u, Q u i * x u) := by
  classical
  unfold C145CoordinatePermutation.spectralGenerator
  simp_rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ w, -(rates i * Q v i * Q w i) *
      C145.Pulse.heatAction Q rates t x w) =
      (-rates i * Q v i) *
        (∑ w, Q w i * C145.Pulse.heatAction Q rates t x w) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w hw
          ring
    _ = _ := by rw [heatAction_mode Q rates x hQ]; ring

theorem heatAction_hasDerivAt {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => C145.Pulse.heatAction Q rates s x)
      (fun v => ∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w *
        C145.Pulse.heatAction Q rates t x w) t := by
  classical
  apply hasDerivAt_pi.mpr
  intro v
  rw [generator_heat_mode Q rates x hQ t v]
  unfold C145.Pulse.heatAction
  apply HasDerivAt.fun_sum
  intro i hi
  simpa only [id_def, mul_one] using
    (((hasDerivAt_id t).const_mul (-rates i)).exp.const_mul (Q v i)).mul_const
      (∑ u, Q u i * x u)

private theorem heatBound_pos {n : ℕ} (Q : Frame n) (rates : State n) (T : ℝ) :
    0 < heatBound Q rates T := by
  unfold heatBound
  positivity

private theorem heat_bound_coordinate {n : ℕ} (Q : Frame n) (rates x : State n)
    (T s : ℝ) (_hT : 0 ≤ T) (hs : |s| ≤ T) (v : Fin (n + 1)) :
    |C145.Pulse.heatAction Q rates s x v| ≤ heatBound Q rates T * ‖x‖ := by
  classical
  have hexp (i : Fin (n + 1)) :
      Real.exp (-rates i * s) ≤ Real.exp (|rates i| * T) := by
    apply Real.exp_le_exp.mpr
    calc
      -rates i * s ≤ |-rates i * s| := le_abs_self _
      _ = |rates i| * |s| := by rw [abs_mul, abs_neg]
      _ ≤ |rates i| * T := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  have hcoord (w : Fin (n + 1)) : |x w| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x w
  calc
    |C145.Pulse.heatAction Q rates s x v| ≤
        ∑ i, ∑ w, |Q v i| * |Q w i| * Real.exp (|rates i| * T) * ‖x‖ := by
      unfold C145.Pulse.heatAction
      calc
        |∑ i, Q v i * Real.exp (-rates i * s) * (∑ w, Q w i * x w)| ≤
            ∑ i, |Q v i * Real.exp (-rates i * s) * (∑ w, Q w i * x w)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ w, |Q v i| * |Q w i| * Real.exp (|rates i| * T) * ‖x‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc
            |Q v i| * Real.exp (-rates i * s) * |∑ w, Q w i * x w| ≤
                |Q v i| * Real.exp (|rates i| * T) * ∑ w, |Q w i| * ‖x‖ := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left (hexp i) (abs_nonneg _)
              · exact (Finset.abs_sum_le_sum_abs _ _).trans <|
                  Finset.sum_le_sum fun w hw => by
                    rw [abs_mul]
                    exact mul_le_mul_of_nonneg_left (hcoord w) (abs_nonneg _)
              · positivity
              · positivity
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w hw
              ring
    _ = (∑ i, ∑ w, |Q v i| * |Q w i| * Real.exp (|rates i| * T)) * ‖x‖ := by
      simp only [Finset.sum_mul]
    _ ≤ (∑ i, ∑ v', ∑ w,
        |Q v' i| * |Q w i| * Real.exp (|rates i| * T)) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.single_le_sum
        (f := fun v' : Fin (n + 1) =>
          ∑ w, |Q v' i| * |Q w i| * Real.exp (|rates i| * T))
        (s := Finset.univ)
        (fun v' hv' => Finset.sum_nonneg fun w hw =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le)
        (Finset.mem_univ v)
    _ ≤ heatBound Q rates T * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      unfold heatBound
      linarith

theorem finite_heat_bound {n : ℕ} (Q : Frame n) (rates x : State n)
    (T s : ℝ) (hT : 0 ≤ T) (hs : |s| ≤ T) :
    0 < heatBound Q rates T ∧
      ‖C145.Pulse.heatAction Q rates s x‖ ≤ heatBound Q rates T * ‖x‖ := by
  refine ⟨heatBound_pos Q rates T, ?_⟩
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (heatBound_pos Q rates T).le (norm_nonneg x))).mpr
  intro v
  simpa only [Real.norm_eq_abs] using heat_bound_coordinate Q rates x T s hT hs v

/-! Actual compact-path integrands and operator constructions. -/

private theorem continuous_extendInput {T : ℝ} (hT : 0 < T) (f : Input T) :
    Continuous (extendInput hT f) :=
  f.continuous.comp continuous_projIcc

private theorem continuous_extendPath {n : ℕ} {T : ℝ} (hT : 0 < T) (v : Path n T) :
    Continuous (extendPath hT v) :=
  v.continuous.comp continuous_projIcc

private theorem extendPath_at {n : ℕ} {T : ℝ} (hT : 0 < T)
    (v : Path n T) (t : Time T) : extendPath hT v (t : ℝ) = v t := by
  unfold extendPath
  congr 1
  apply Subtype.ext
  change max 0 (min T (t : ℝ)) = (t : ℝ)
  rw [min_eq_right t.property.2, max_eq_right t.property.1]

private theorem continuous_heat {n : ℕ} (Q : Frame n) (rates : State n) :
    Continuous (fun p : ℝ × State n => C145.Pulse.heatAction Q rates p.1 p.2) := by
  unfold C145.Pulse.heatAction
  fun_prop

private def linearIntegrand {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) (s : ℝ) : State n :=
  extendInput hT f s • C145.Pulse.heatAction Q rates (-s) b

private def quadraticIntegrand {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) (s : ℝ) : State n :=
  C145.Pulse.heatAction Q rates (-s)
    (fun x => C145.Pulse.heatAction Q rates s (extendPath hT v s) x *
      C145.Pulse.heatAction Q rates s (extendPath hT w s) x)

private theorem continuous_linearIntegrand {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) :
    Continuous (linearIntegrand hT Q rates b f) := by
  exact (continuous_extendInput hT f).smul
    ((continuous_heat Q rates).comp (continuous_neg.prodMk continuous_const))

private theorem continuous_quadraticIntegrand {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) :
    Continuous (quadraticIntegrand hT Q rates v w) := by
  have hv := (continuous_heat Q rates).comp (continuous_id.prodMk (continuous_extendPath hT v))
  have hw := (continuous_heat Q rates).comp (continuous_id.prodMk (continuous_extendPath hT w))
  exact (continuous_heat Q rates).comp (continuous_neg.prodMk (hv.mul hw))

private def linearPath {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) : Path n T :=
  ⟨fun t => ipLinear hT Q rates b f t,
    (intervalIntegral.continuous_primitive
      (fun a c => (continuous_linearIntegrand hT Q rates b f).intervalIntegrable a c) 0).comp
        continuous_subtype_val⟩

private def quadraticPath {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) : Path n T :=
  ⟨fun t => ipQuadratic hT Q rates v w t,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_quadraticIntegrand hT Q rates v w).intervalIntegrable a b) 0).comp
        continuous_subtype_val⟩

private def heatPath {n : ℕ} {T : ℝ} (Q : Frame n) (rates : State n)
    (σ : ℝ) (v : Path n T) : Path n T :=
  ⟨fun t => C145.Pulse.heatAction Q rates (σ * (t : ℝ)) (v t),
    (continuous_heat Q rates).comp
      ((continuous_const.mul continuous_subtype_val).prodMk v.continuous)⟩

private theorem linearPath_norm {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) :
    ‖linearPath hT Q rates b f‖ ≤ (T * heatBound Q rates T * ‖b‖) * ‖f‖ := by
  have hM := (heatBound_pos Q rates T).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖ipLinear hT Q rates b f (t : ℝ)‖ ≤ _
  have hint : ‖ipLinear hT Q rates b f (t : ℝ)‖ ≤
      (‖f‖ * (heatBound Q rates T * ‖b‖)) * |(t : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le t.property.1] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s ≤ T := hs.2.trans t.property.2
    have hheat := (finite_heat_bound Q rates b T (-s) hT.le
      (by simpa only [abs_neg, abs_of_nonneg hs0] using hsT)).2
    rw [norm_smul]
    exact mul_le_mul (f.norm_coe_le_norm _) hheat (norm_nonneg _) (norm_nonneg _)
  calc
    ‖ipLinear hT Q rates b f (t : ℝ)‖ ≤
        (‖f‖ * (heatBound Q rates T * ‖b‖)) * (t : ℝ) := by
      simpa only [sub_zero, abs_of_nonneg t.property.1] using hint
    _ ≤ (‖f‖ * (heatBound Q rates T * ‖b‖)) * T :=
      mul_le_mul_of_nonneg_left t.property.2 (by positivity)
    _ = _ := by ring

private theorem quadraticPath_norm {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) :
    ‖quadraticPath hT Q rates v w‖ ≤ (T * heatBound Q rates T ^ 3) * ‖v‖ * ‖w‖ := by
  have hM := (heatBound_pos Q rates T).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖ipQuadratic hT Q rates v w (t : ℝ)‖ ≤ _
  have hint : ‖ipQuadratic hT Q rates v w (t : ℝ)‖ ≤
      (heatBound Q rates T ^ 3 * ‖v‖ * ‖w‖) * |(t : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le t.property.1] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s ≤ T := hs.2.trans t.property.2
    have hsabs : |s| ≤ T := by simpa only [abs_of_nonneg hs0] using hsT
    have hsa : |-s| ≤ T := by simpa only [abs_neg] using hsabs
    have hv : ‖C145.Pulse.heatAction Q rates s (extendPath hT v s)‖ ≤
        heatBound Q rates T * ‖v‖ :=
      ((finite_heat_bound Q rates _ T s hT.le hsabs).2).trans
        (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm _) hM)
    have hw : ‖C145.Pulse.heatAction Q rates s (extendPath hT w s)‖ ≤
        heatBound Q rates T * ‖w‖ :=
      ((finite_heat_bound Q rates _ T s hT.le hsabs).2).trans
        (mul_le_mul_of_nonneg_left (w.norm_coe_le_norm _) hM)
    calc
      ‖C145.Pulse.heatAction Q rates (-s)
          (fun x => C145.Pulse.heatAction Q rates s (extendPath hT v s) x *
            C145.Pulse.heatAction Q rates s (extendPath hT w s) x)‖ ≤
          heatBound Q rates T *
            ‖C145.Pulse.heatAction Q rates s (extendPath hT v s) *
              C145.Pulse.heatAction Q rates s (extendPath hT w s)‖ :=
        (finite_heat_bound Q rates _ T (-s) hT.le hsa).2
      _ ≤ heatBound Q rates T *
          (‖C145.Pulse.heatAction Q rates s (extendPath hT v s)‖ *
            ‖C145.Pulse.heatAction Q rates s (extendPath hT w s)‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) hM
      _ ≤ heatBound Q rates T * ((heatBound Q rates T * ‖v‖) *
          (heatBound Q rates T * ‖w‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hv hw (norm_nonneg _) (by positivity)) hM
      _ = _ := by ring
  calc
    ‖ipQuadratic hT Q rates v w (t : ℝ)‖ ≤
        (heatBound Q rates T ^ 3 * ‖v‖ * ‖w‖) * (t : ℝ) := by
      simpa only [sub_zero, abs_of_nonneg t.property.1] using hint
    _ ≤ (heatBound Q rates T ^ 3 * ‖v‖ * ‖w‖) * T :=
      mul_le_mul_of_nonneg_left t.property.2 (by positivity)
    _ = _ := by ring

private theorem heatPath_norm {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (σ : ℝ) (hσ : |σ| ≤ 1) (v : Path n T) :
    ‖heatPath Q rates σ v‖ ≤ heatBound Q rates T * ‖v‖ := by
  have hM := (heatBound_pos Q rates T).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hst : |σ * (t : ℝ)| ≤ T := by
    rw [abs_mul, abs_of_nonneg t.property.1]
    calc
      |σ| * (t : ℝ) ≤ 1 * (t : ℝ) :=
        mul_le_mul_of_nonneg_right hσ t.property.1
      _ ≤ T := by simpa only [one_mul] using t.property.2
  exact ((finite_heat_bound Q rates _ T _ hT.le hst).2).trans
    (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hM)

private theorem linearPath_add {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f g : Input T) :
    linearPath hT Q rates b (f + g) =
      linearPath hT Q rates b f + linearPath hT Q rates b g := by
  apply ContinuousMap.ext
  intro t
  change ipLinear hT Q rates b (f + g) (t : ℝ) =
    ipLinear hT Q rates b f (t : ℝ) + ipLinear hT Q rates b g (t : ℝ)
  unfold ipLinear
  simp only [extendInput, ContinuousMap.add_apply, add_smul]
  exact intervalIntegral.integral_add
    ((continuous_linearIntegrand hT Q rates b f).intervalIntegrable _ _)
    ((continuous_linearIntegrand hT Q rates b g).intervalIntegrable _ _)

private theorem linearPath_smul {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (c : ℝ) (f : Input T) :
    linearPath hT Q rates b (c • f) = c • linearPath hT Q rates b f := by
  apply ContinuousMap.ext
  intro t
  change ipLinear hT Q rates b (c • f) (t : ℝ) = c • ipLinear hT Q rates b f (t : ℝ)
  unfold ipLinear
  simp only [extendInput, ContinuousMap.smul_apply, smul_eq_mul, mul_smul]
  exact intervalIntegral.integral_smul c _

private theorem quadraticIntegrand_add_left {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v v' w : Path n T) (s : ℝ) :
    quadraticIntegrand hT Q rates (v + v') w s =
      quadraticIntegrand hT Q rates v w s + quadraticIntegrand hT Q rates v' w s := by
  have hext : extendPath hT (v + v') s = extendPath hT v s + extendPath hT v' s := rfl
  unfold quadraticIntegrand
  simp_rw [hext, heatAction_vec_add, Pi.add_apply]
  have hprod :
      (fun x =>
        (C145.Pulse.heatAction Q rates s (extendPath hT v s) x +
          C145.Pulse.heatAction Q rates s (extendPath hT v' s) x) *
            C145.Pulse.heatAction Q rates s (extendPath hT w s) x) =
      (fun x => C145.Pulse.heatAction Q rates s (extendPath hT v s) x *
        C145.Pulse.heatAction Q rates s (extendPath hT w s) x) +
      (fun x => C145.Pulse.heatAction Q rates s (extendPath hT v' s) x *
        C145.Pulse.heatAction Q rates s (extendPath hT w s) x) := by
    funext x
    exact add_mul _ _ _
  rw [hprod]
  exact heatAction_vec_add Q rates _ _ (-s)

private theorem quadraticIntegrand_smul_left {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (c : ℝ) (v w : Path n T) (s : ℝ) :
    quadraticIntegrand hT Q rates (c • v) w s =
      c • quadraticIntegrand hT Q rates v w s := by
  have hext : extendPath hT (c • v) s = c • extendPath hT v s := rfl
  unfold quadraticIntegrand
  simp_rw [hext, heatAction_vec_smul, Pi.smul_apply, smul_eq_mul]
  have hprod :
      (fun x => (c * C145.Pulse.heatAction Q rates s (extendPath hT v s) x) *
        C145.Pulse.heatAction Q rates s (extendPath hT w s) x) =
      c • (fun x => C145.Pulse.heatAction Q rates s (extendPath hT v s) x *
        C145.Pulse.heatAction Q rates s (extendPath hT w s) x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hprod]
  exact heatAction_vec_smul Q rates _ (-s) c

private theorem quadraticIntegrand_symm {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) (s : ℝ) :
    quadraticIntegrand hT Q rates v w s = quadraticIntegrand hT Q rates w v s := by
  unfold quadraticIntegrand
  congr 1
  funext x
  exact mul_comm _ _

private theorem quadraticPath_add_left {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v v' w : Path n T) :
    quadraticPath hT Q rates (v + v') w =
      quadraticPath hT Q rates v w + quadraticPath hT Q rates v' w := by
  apply ContinuousMap.ext
  intro t
  change (∫ s in (0 : ℝ)..(t : ℝ), quadraticIntegrand hT Q rates (v + v') w s) = _
  simp_rw [quadraticIntegrand_add_left]
  exact intervalIntegral.integral_add
    ((continuous_quadraticIntegrand hT Q rates v w).intervalIntegrable _ _)
    ((continuous_quadraticIntegrand hT Q rates v' w).intervalIntegrable _ _)

private theorem quadraticPath_smul_left {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (c : ℝ) (v w : Path n T) :
    quadraticPath hT Q rates (c • v) w = c • quadraticPath hT Q rates v w := by
  apply ContinuousMap.ext
  intro t
  change (∫ s in (0 : ℝ)..(t : ℝ), quadraticIntegrand hT Q rates (c • v) w s) = _
  simp_rw [quadraticIntegrand_smul_left]
  exact intervalIntegral.integral_smul c _

private theorem quadraticPath_symm {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) :
    quadraticPath hT Q rates v w = quadraticPath hT Q rates w v := by
  apply ContinuousMap.ext
  intro t
  change (∫ s in (0 : ℝ)..(t : ℝ), quadraticIntegrand hT Q rates v w s) = _
  simp_rw [quadraticIntegrand_symm hT Q rates v w]
  rfl

private def linearOperator {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) : Input T →L[ℝ] Path n T :=
  LinearMap.mkContinuous
    { toFun := linearPath hT Q rates b
      map_add' := linearPath_add hT Q rates b
      map_smul' := linearPath_smul hT Q rates b }
    (T * heatBound Q rates T * ‖b‖) (linearPath_norm hT Q rates b)

private def quadraticLinearMap {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) : Path n T →ₗ[ℝ] Path n T →ₗ[ℝ] Path n T :=
  LinearMap.mk₂ ℝ (quadraticPath hT Q rates)
    (quadraticPath_add_left hT Q rates)
    (quadraticPath_smul_left hT Q rates)
    (fun v w w' => by
      rw [quadraticPath_symm hT Q rates v (w + w'), quadraticPath_add_left,
        quadraticPath_symm hT Q rates w v, quadraticPath_symm hT Q rates w' v])
    (fun c v w => by
      rw [quadraticPath_symm hT Q rates v (c • w), quadraticPath_smul_left,
        quadraticPath_symm hT Q rates w v])

private def quadraticOperator {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) : Path n T →L[ℝ] Path n T →L[ℝ] Path n T :=
  (quadraticLinearMap hT Q rates).mkContinuous₂ (T * heatBound Q rates T ^ 3)
    (quadraticPath_norm hT Q rates)

private def heatLinearMap {n : ℕ} {T : ℝ} (Q : Frame n) (rates : State n)
    (σ : ℝ) : Path n T →ₗ[ℝ] Path n T where
  toFun := heatPath Q rates σ
  map_add' v w := by
    apply ContinuousMap.ext
    intro t
    exact heatAction_vec_add Q rates (v t) (w t) _
  map_smul' c v := by
    apply ContinuousMap.ext
    intro t
    exact heatAction_vec_smul Q rates (v t) _ c

private def heatOperator {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (σ : ℝ) (hσ : |σ| ≤ 1) :
    Path n T →L[ℝ] Path n T :=
  (heatLinearMap Q rates σ).mkContinuous (heatBound Q rates T)
    (heatPath_norm hT Q rates σ hσ)

theorem interaction_operators {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) :
    ∃ (L : Input T →L[ℝ] Path n T)
      (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T)
      (Pplus Pminus : Path n T →L[ℝ] Path n T),
      (∀ (f : Input T) (t : Time T), L f t = ipLinear hT Q rates b f t) ∧
      (∀ (v w : Path n T) (t : Time T), B v w t = ipQuadratic hT Q rates v w t) ∧
      (∀ (v : Path n T) (t : Time T),
        Pplus v t = C145.Pulse.heatAction Q rates t (v t)) ∧
      (∀ (v : Path n T) (t : Time T),
        Pminus v t = C145.Pulse.heatAction Q rates (-(t : ℝ)) (v t)) ∧
      (∀ v w : Path n T, B v w = B w v) ∧
      ‖L‖ ≤ T * heatBound Q rates T * ‖b‖ ∧
      ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := Path n T) (F := Path n T →L[ℝ] Path n T)
        (σ₁₂ := RingHom.id ℝ) B ≤ T * heatBound Q rates T ^ 3 ∧
      ‖Pplus‖ ≤ heatBound Q rates T ∧ ‖Pminus‖ ≤ heatBound Q rates T := by
  have hM := (heatBound_pos Q rates T).le
  refine ⟨linearOperator hT Q rates b, quadraticOperator hT Q rates,
    heatOperator hT Q rates 1 (by norm_num), heatOperator hT Q rates (-1) (by norm_num),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f t
    rfl
  · intro v w t
    rfl
  · intro v t
    change C145.Pulse.heatAction Q rates (1 * (t : ℝ)) (v t) = _
    rw [one_mul]
  · intro v t
    change C145.Pulse.heatAction Q rates (-1 * (t : ℝ)) (v t) = _
    rw [neg_one_mul]
  · exact quadraticPath_symm hT Q rates
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  · simpa only [quadraticOperator, ContinuousLinearMap.norm_def, ContinuousLinearMap.opNorm] using
      (LinearMap.mkContinuous₂_norm_le (quadraticLinearMap hT Q rates) (by positivity)
        (quadraticPath_norm hT Q rates))
  · exact LinearMap.mkContinuous_norm_le _ hM _
  · exact LinearMap.mkContinuous_norm_le _ hM _

/-! The residual inverse is genuinely nonlinear; its derivatives are not supplied. -/

private theorem residual_zero {n : ℕ} {T : ℝ}
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T) :
    ipResidual B 0 = 0 := by simp [ipResidual]

private theorem residual_contDiff {n : ℕ} {T : ℝ}
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T) :
    ContDiff ℝ 2 (ipResidual B) := by
  exact contDiff_id.sub
    (B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id))

private theorem residual_hasFDerivAt_zero {n : ℕ} {T : ℝ}
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T) :
    HasFDerivAt (ipResidual B) (ContinuousLinearMap.id ℝ (Path n T)) 0 := by
  have h := (hasFDerivAt_id (0 : Path n T)).sub
    (B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : Path n T))
      (hasFDerivAt_id (0 : Path n T)))
  convert h using 1
  · rfl
  · simp only [id_def, ContinuousLinearMap.map_zero, zero_apply,
      add_zero, sub_zero]

private theorem residual_local_inverse {n : ℕ} {T : ℝ}
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T) :
    ∃ W : Path n T → Path n T,
      W 0 = 0 ∧ ContDiffAt ℝ 2 W 0 ∧
      HasFDerivAt W (ContinuousLinearMap.id ℝ (Path n T)) 0 ∧
      (∀ᶠ v in 𝓝 (0 : Path n T), W (ipResidual B v) = v) ∧
      (∀ᶠ z in 𝓝 (0 : Path n T), ipResidual B (W z) = z) := by
  let e : Path n T ≃L[ℝ] Path n T := ContinuousLinearEquiv.refl ℝ _
  have hc : ContDiffAt ℝ 2 (ipResidual B) 0 := (residual_contDiff B).contDiffAt
  have hd : HasFDerivAt (ipResidual B) (e : Path n T →L[ℝ] Path n T) 0 := by
    simpa [e] using residual_hasFDerivAt_zero B
  have hn : (2 : ℕ∞ω) ≠ 0 := by norm_num
  let W := hc.localInverse hd hn
  have hs := hc.hasStrictFDerivAt hd hn
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [residual_zero] using hc.localInverse_apply_image hd hn
  · simpa only [residual_zero] using hc.to_localInverse hd hn
  · simpa [W, ContDiffAt.localInverse, residual_zero, e] using hs.to_localInverse.hasFDerivAt
  · exact hs.eventually_left_inverse
  · simpa only [W, ContDiffAt.localInverse, residual_zero] using hs.eventually_right_inverse

private theorem exists_interaction_C2_germ {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) :
    ∃ V : Input T → Path n T,
      V 0 = 0 ∧ ContDiffAt ℝ 2 V 0 ∧
      HasFDerivAt V (linearOperator hT Q rates b) 0 ∧
      ∀ᶠ f in 𝓝 (0 : Input T),
        V f = linearPath hT Q rates b f + quadraticPath hT Q rates (V f) (V f) := by
  let L := linearOperator hT Q rates b
  let B := quadraticOperator hT Q rates
  obtain ⟨W, hW0, hcW, hdW, hleft, hright⟩ := residual_local_inverse B
  let V : Input T → Path n T := fun f => W (L f)
  have hL0 : L 0 = 0 := L.map_zero
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · simp only [V, hL0, hW0]
  · have hcW' : ContDiffAt ℝ 2 W (L 0) := by simpa only [hL0] using hcW
    exact hcW'.comp 0 (L.contDiff.contDiffAt)
  · have hdW' : HasFDerivAt W (ContinuousLinearMap.id ℝ (Path n T)) (L 0) := by
      simpa only [hL0] using hdW
    simpa only [V, L, Function.comp_def, ContinuousLinearMap.id_comp] using hdW'.comp 0
      L.hasFDerivAt
  · have hpre := L.continuous.continuousAt.tendsto.eventually
      (show ∀ᶠ z in 𝓝 (L 0), ipResidual B (W z) = z by simpa only [hL0] using hright)
    filter_upwards [hpre] with f hf
    change V f = L f + B (V f) (V f)
    change V f - B (V f) (V f) = L f at hf
    exact sub_eq_iff_eq_add.mp hf

private theorem heat_paths_inverse {n : ℕ} {T : ℝ} (_hT : 0 < T)
    (Q : Frame n) (rates : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (v : Path n T) :
    heatPath Q rates 1 (heatPath Q rates (-1) v) = v ∧
      heatPath Q rates (-1) (heatPath Q rates 1 v) = v := by
  constructor
  · apply ContinuousMap.ext
    intro t
    change C145.Pulse.heatAction Q rates (1 * (t : ℝ))
      (C145.Pulse.heatAction Q rates (-1 * (t : ℝ)) (v t)) = v t
    rw [← heatAction_add Q rates (v t) hQ]
    simpa only [one_mul, neg_one_mul, add_neg_cancel] using heatAction_zero Q rates (v t) hQ
  · apply ContinuousMap.ext
    intro t
    change C145.Pulse.heatAction Q rates (-1 * (t : ℝ))
      (C145.Pulse.heatAction Q rates (1 * (t : ℝ)) (v t)) = v t
    rw [← heatAction_add Q rates (v t) hQ]
    simpa only [one_mul, neg_one_mul, neg_add_cancel] using heatAction_zero Q rates (v t) hQ

private theorem ipLinear_hasDerivAt {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (f : Input T) (t : ℝ) :
    HasDerivAt (ipLinear hT Q rates b f) (linearIntegrand hT Q rates b f t) t :=
  ((continuous_linearIntegrand hT Q rates b f).integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem ipQuadratic_hasDerivAt {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v w : Path n T) (t : ℝ) :
    HasDerivAt (ipQuadratic hT Q rates v w) (quadraticIntegrand hT Q rates v w t) t :=
  ((continuous_quadraticIntegrand hT Q rates v w).integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem heatAction_along_hasDerivWithinAt {n : ℕ} (Q : Frame n)
    (rates : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (v : ℝ → State n) (v' : State n) (S : Set ℝ) (t : ℝ)
    (hv : HasDerivWithinAt v v' S t) :
    HasDerivWithinAt (fun s => C145.Pulse.heatAction Q rates s (v s))
      (fun x => (∑ w, C145CoordinatePermutation.spectralGenerator rates Q x w *
        C145.Pulse.heatAction Q rates t (v t) w) +
          C145.Pulse.heatAction Q rates t v' x) S t := by
  classical
  apply hasDerivWithinAt_pi.mpr
  intro x
  have hmode (i : Fin (n + 1)) :
      HasDerivWithinAt (fun s => ∑ u, Q u i * v s u) (∑ u, Q u i * v' u) S t := by
    apply HasDerivWithinAt.fun_sum
    intro u hu
    exact (hasDerivWithinAt_pi.mp hv u).const_mul (Q u i)
  have hexp (i : Fin (n + 1)) :
      HasDerivWithinAt (fun s => Real.exp (-rates i * s))
        (Real.exp (-rates i * t) * (-rates i)) S t := by
    simpa only [id_def, mul_one] using
      (((hasDerivAt_id t).const_mul (-rates i)).exp).hasDerivWithinAt
  have hd : HasDerivWithinAt
      (fun s => ∑ i, Q x i * Real.exp (-rates i * s) * (∑ u, Q u i * v s u))
      (∑ i, ((Q x i * (Real.exp (-rates i * t) * (-rates i))) * (∑ u, Q u i * v t u) +
        (Q x i * Real.exp (-rates i * t)) * (∑ u, Q u i * v' u))) S t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    exact ((hexp i).const_mul (Q x i)).mul (hmode i)
  convert hd using 1
  · rfl
  · rw [Finset.sum_add_distrib, ← generator_heat_mode Q rates (v t) hQ t x]
    rfl

private theorem heatPath_extend_at {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (v : Path n T) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) T) :
    extendPath hT (heatPath Q rates 1 v) s =
      C145.Pulse.heatAction Q rates s (extendPath hT v s) := by
  let ts : Time T := ⟨s, hs⟩
  change extendPath hT (heatPath Q rates 1 v) (ts : ℝ) =
    C145.Pulse.heatAction Q rates (ts : ℝ) (extendPath hT v (ts : ℝ))
  rw [extendPath_at, extendPath_at]
  change C145.Pulse.heatAction Q rates (1 * s) (v ts) = _
  rw [one_mul]

private theorem interaction_path_is_ode {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (f : Input T) (v : Path n T)
    (hv : v = linearPath hT Q rates b f + quadraticPath hT Q rates v v) :
    extendPath hT (heatPath Q rates 1 v) 0 = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (extendPath hT (heatPath Q rates 1 v))
          (vectorField Q rates b (extendInput hT f) t
            (extendPath hT (heatPath Q rates 1 v) t)) (Icc (0 : ℝ) T) t := by
  have hveq : ∀ s ∈ Icc (0 : ℝ) T,
      extendPath hT v s = ipLinear hT Q rates b f s + ipQuadratic hT Q rates v v s := by
    intro s hs
    let ts : Time T := ⟨s, hs⟩
    change extendPath hT v (ts : ℝ) = _
    rw [extendPath_at]
    exact congrArg (fun p : Path n T => p ts) hv
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  constructor
  · rw [heatPath_extend_at hT Q rates v 0 hzero]
    have hv0 : extendPath hT v 0 = 0 := by
      simpa only [ipLinear, ipQuadratic, intervalIntegral.integral_same, add_zero] using hveq 0
        hzero
    rw [hv0]
    exact heatAction_zero Q rates 0 hQ
  · intro t ht
    have hvder : HasDerivWithinAt (extendPath hT v)
        (linearIntegrand hT Q rates b f t + quadraticIntegrand hT Q rates v v t)
          (Icc (0 : ℝ) T) t :=
      ((ipLinear_hasDerivAt hT Q rates b f t).add
        (ipQuadratic_hasDerivAt hT Q rates v v t)).hasDerivWithinAt.congr_of_mem hveq ht
    have huder := (heatAction_along_hasDerivWithinAt Q rates hQ _ _ _ t hvder).congr_of_mem
      (heatPath_extend_at hT Q rates v) ht
    have hinverse (z : State n) :
        C145.Pulse.heatAction Q rates t (C145.Pulse.heatAction Q rates (-t) z) = z := by
      rw [← heatAction_add Q rates z hQ, add_neg_cancel]
      exact heatAction_zero Q rates z hQ
    have hforcing :
        C145.Pulse.heatAction Q rates t
            (linearIntegrand hT Q rates b f t + quadraticIntegrand hT Q rates v v t) =
          extendInput hT f t • b +
            (fun x => C145.Pulse.heatAction Q rates t (extendPath hT v t) x ^ 2) := by
      unfold linearIntegrand quadraticIntegrand
      rw [heatAction_vec_add, heatAction_vec_smul, hinverse, hinverse]
      congr 1
      funext x
      rw [pow_two]
    convert huder using 1
    funext x
    rw [hforcing, heatPath_extend_at hT Q rates v t ht]
    simp only [vectorField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem exists_actual_C2_response {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) :
    ∃ R : Input T → Path n T,
      IsActualResponse hT Q rates b R ∧ ContDiffAt ℝ 2 R 0 := by
  obtain ⟨V, hV0, hcV, hdV, hVeq⟩ := exists_interaction_C2_germ hT Q rates b
  let P := heatOperator hT Q rates 1 (by norm_num : |(1 : ℝ)| ≤ 1)
  let R : Input T → Path n T := fun f => P (V f)
  refine ⟨R, ⟨?_, ?_⟩, ?_⟩
  · simp only [R, hV0, map_zero]
  · filter_upwards [hVeq] with f hf
    exact interaction_path_is_ode hT Q rates b hQ f (V f) hf
  · exact P.contDiff.contDiffAt.comp 0 hcV

private theorem generator_mode {n : ℕ} (Q : Frame n) (rates x : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (i : Fin (n + 1)) :
    (∑ v, Q v i * (∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w * x w)) =
      -rates i * (∑ w, Q w i * x w) := by
  classical
  have hleft : HasDerivAt (fun t : ℝ => ∑ v, Q v i * C145.Pulse.heatAction Q rates t x v)
      (∑ v, Q v i * (∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w * x w)) 0 := by
    apply HasDerivAt.fun_sum
    intro v hv
    simpa only [heatAction_zero Q rates x hQ] using
      ((hasDerivAt_pi.mp (heatAction_hasDerivAt Q rates x hQ 0)) v).const_mul (Q v i)
  have hright : HasDerivAt (fun t : ℝ => ∑ v, Q v i * C145.Pulse.heatAction Q rates t x v)
      (-rates i * (∑ w, Q w i * x w)) 0 := by
    have heq : (fun t : ℝ => ∑ v, Q v i * C145.Pulse.heatAction Q rates t x v) =
        (fun t : ℝ => Real.exp (-rates i * t) * (∑ w, Q w i * x w)) :=
      funext fun t => heatAction_mode Q rates x hQ t i
    rw [heq]
    simpa only [id_def, mul_one, mul_zero, Real.exp_zero, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (-rates i)).exp).mul_const (∑ w, Q w i * x w)
  exact hleft.unique hright

private theorem heatAction_generator_commutes {n : ℕ} (Q : Frame n)
    (rates x : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (t : ℝ) :
    C145.Pulse.heatAction Q rates t
        (fun v => ∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w * x w) =
      (fun v => ∑ w, C145CoordinatePermutation.spectralGenerator rates Q v w *
        C145.Pulse.heatAction Q rates t x w) := by
  classical
  funext v
  change (∑ i, Q v i * Real.exp (-rates i * t) *
    (∑ u, Q u i * (∑ w, C145CoordinatePermutation.spectralGenerator rates Q u w * x w))) = _
  simp_rw [generator_mode Q rates x hQ]
  rw [generator_heat_mode Q rates x hQ t v]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem heatAction_neg_along_hasDerivWithinAt {n : ℕ} (Q : Frame n)
    (rates : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (u : ℝ → State n) (u' : State n) (S : Set ℝ) (t : ℝ)
    (hu : HasDerivWithinAt u u' S t) :
    HasDerivWithinAt (fun s => C145.Pulse.heatAction Q rates (-s) (u s))
      (fun x => -(∑ w, C145CoordinatePermutation.spectralGenerator rates Q x w *
        C145.Pulse.heatAction Q rates (-t) (u t) w) +
          C145.Pulse.heatAction Q rates (-t) u' x) S t := by
  classical
  apply hasDerivWithinAt_pi.mpr
  intro x
  have hmode (i : Fin (n + 1)) :
      HasDerivWithinAt (fun s => ∑ v, Q v i * u s v) (∑ v, Q v i * u' v) S t := by
    apply HasDerivWithinAt.fun_sum
    intro v hv
    exact (hasDerivWithinAt_pi.mp hu v).const_mul (Q v i)
  have hd : HasDerivWithinAt
      (fun s => ∑ i, Q x i * Real.exp (rates i * s) * (∑ v, Q v i * u s v))
      (∑ i, ((Q x i * (Real.exp (rates i * t) * rates i)) * (∑ v, Q v i * u t v) +
        (Q x i * Real.exp (rates i * t)) * (∑ v, Q v i * u' v))) S t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    with_reducible_and_instances
      simpa only [id_def, mul_one] using
        (((((hasDerivAt_id t).const_mul (rates i)).exp).hasDerivWithinAt).const_mul (Q x
          i)).fun_mul (hmode i)
  convert hd using 1
  · funext s
    simp only [C145.Pulse.heatAction, neg_mul_neg]
  · rw [Finset.sum_add_distrib, generator_heat_mode Q rates (u t) hQ (-t) x]
    simp only [C145.Pulse.heatAction, neg_mul_neg]
    rw [← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

private theorem heatPath_extend_scaled_at {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates : State n) (σ : ℝ) (v : Path n T) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) T) :
    extendPath hT (heatPath Q rates σ v) s =
      C145.Pulse.heatAction Q rates (σ * s) (extendPath hT v s) := by
  let ts : Time T := ⟨s, hs⟩
  change extendPath hT (heatPath Q rates σ v) (ts : ℝ) =
    C145.Pulse.heatAction Q rates (σ * (ts : ℝ)) (extendPath hT v (ts : ℝ))
  rw [extendPath_at, extendPath_at]
  rfl

private theorem actual_path_interaction {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (f : Input T) (u : Path n T) (hinit : extendPath hT u 0 = 0)
    (hode : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath hT u)
        (vectorField Q rates b (extendInput hT f) t (extendPath hT u t)) (Icc (0 : ℝ) T) t) :
    heatPath Q rates (-1) u = linearPath hT Q rates b f +
      quadraticPath hT Q rates (heatPath Q rates (-1) u) (heatPath Q rates (-1) u) := by
  let v := heatPath Q rates (-1) u
  have hplus : ∀ s ∈ Icc (0 : ℝ) T,
      C145.Pulse.heatAction Q rates s (extendPath hT v s) = extendPath hT u s := by
    intro s hs
    rw [heatPath_extend_scaled_at hT Q rates (-1) u s hs, neg_one_mul,
      ← heatAction_add Q rates _ hQ, add_neg_cancel, heatAction_zero Q rates _ hQ]
  have hv0 : extendPath hT v 0 = 0 := by
    rw [heatPath_extend_scaled_at hT Q rates (-1) u 0 ⟨le_rfl, hT.le⟩, hinit]
    simpa only [mul_zero] using heatAction_zero Q rates 0 hQ
  have hvder : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath hT v)
        (linearIntegrand hT Q rates b f s + quadraticIntegrand hT Q rates v v s)
          (Icc (0 : ℝ) T) s := by
    intro s hs
    have hd := (heatAction_neg_along_hasDerivWithinAt Q rates hQ _ _ _ s (hode s hs)).congr_of_mem
      (fun r hr => by
        simpa only [neg_one_mul] using heatPath_extend_scaled_at hT Q rates (-1) u r hr) hs
    convert hd using 1
    have hgen := heatAction_generator_commutes Q rates (extendPath hT u s) hQ (-s)
    have hsplit : vectorField Q rates b (extendInput hT f) s (extendPath hT u s) =
        (fun x => ∑ w, C145CoordinatePermutation.spectralGenerator rates Q x w * extendPath hT u s
          w) +
          (fun x => extendPath hT u s x ^ 2) + extendInput hT f s • b := by
      funext x
      simp only [vectorField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit, heatAction_vec_add, heatAction_vec_add, heatAction_vec_smul, hgen]
    unfold linearIntegrand quadraticIntegrand
    simp_rw [hplus s hs]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [pow_two]
    ring
  apply ContinuousMap.ext
  intro t
  have hint : IntervalIntegrable
      (fun s => linearIntegrand hT Q rates b f s + quadraticIntegrand hT Q rates v v s)
      volume 0 (t : ℝ) :=
    ((continuous_linearIntegrand hT Q rates b f).add
      (continuous_quadraticIntegrand hT Q rates v v)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (continuous_extendPath hT v).continuousOn
    (fun s hs => (hvder s ⟨hs.1.le, hs.2.le.trans t.property.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le t.property.2))) hint
  rw [intervalIntegral.integral_add
    ((continuous_linearIntegrand hT Q rates b f).intervalIntegrable _ _)
    ((continuous_quadraticIntegrand hT Q rates v v).intervalIntegrable _ _),
    hv0, sub_zero, extendPath_at hT v t] at hFTC
  exact hFTC.symm

theorem actual_response_germ_unique {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R S : Input T → Path n T)
    (hR : IsActualResponse hT Q rates b R)
    (hS : IsActualResponse hT Q rates b S)
    (hcR : ContinuousAt R 0) (hcS : ContinuousAt S 0) :
    R =ᶠ[𝓝 (0 : Input T)] S := by
  let L := linearOperator hT Q rates b
  let B := quadraticOperator hT Q rates
  let P := heatOperator hT Q rates (-1) (by norm_num : |(-1 : ℝ)| ≤ 1)
  obtain ⟨W, hW0, hcW, hdW, hleft, hright⟩ := residual_local_inverse B
  have hPR : Tendsto (fun f => P (R f)) (𝓝 (0 : Input T)) (𝓝 (0 : Path n T)) := by
    have hc := P.continuous.continuousAt.comp hcR
    simpa only [Function.comp_apply, Function.comp_def, hR.1,
      ContinuousLinearMap.map_zero] using hc.tendsto
  have hPS : Tendsto (fun f => P (S f)) (𝓝 (0 : Input T)) (𝓝 (0 : Path n T)) := by
    have hc := P.continuous.continuousAt.comp hcS
    simpa only [Function.comp_apply, Function.comp_def, hS.1,
      ContinuousLinearMap.map_zero] using hc.tendsto
  filter_upwards [hR.2, hS.2, hPR.eventually hleft, hPS.eventually hleft] with f hfR hfS hiR hiS
  have hresR : ipResidual B (P (R f)) = L f := by
    change P (R f) - B (P (R f)) (P (R f)) = L f
    apply sub_eq_iff_eq_add.mpr
    exact actual_path_interaction hT Q rates b hQ f (R f) hfR.1 hfR.2
  have hresS : ipResidual B (P (S f)) = L f := by
    change P (S f) - B (P (S f)) (P (S f)) = L f
    apply sub_eq_iff_eq_add.mpr
    exact actual_path_interaction hT Q rates b hQ f (S f) hfS.1 hfS.2
  rw [hresR] at hiR
  rw [hresS] at hiS
  have heq : heatPath Q rates (-1) (R f) = heatPath Q rates (-1) (S f) := hiR.symm.trans hiS
  calc
    R f = heatPath Q rates 1 (heatPath Q rates (-1) (R f)) :=
      (heat_paths_inverse hT Q rates hQ (R f)).1.symm
    _ = heatPath Q rates 1 (heatPath Q rates (-1) (S f)) := congrArg (heatPath Q rates 1) heq
    _ = S f := (heat_paths_inverse hT Q rates hQ (S f)).1

/-! Differentiate the derived nonlinear integral identity twice. -/

private theorem interaction_fderiv_two {n : ℕ} {T : ℝ}
    (L : Input T →L[ℝ] Path n T)
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T)
    (hB : ∀ v w, B v w = B w v)
    (V : Input T → Path n T) (hV0 : V 0 = 0) (hcV : ContDiffAt ℝ 2 V 0)
    (heq : V =ᶠ[𝓝 (0 : Input T)] fun f => L f + B (V f) (V f)) :
    fderiv ℝ V 0 = L ∧
      ∀ g h : Input T, fderiv ℝ (fderiv ℝ V) 0 g h = 2 • B (L g) (L h) := by
  let D := fderiv ℝ V
  have hdiff : ∀ᶠ f in 𝓝 (0 : Input T), DifferentiableAt ℝ V f :=
    (hcV.eventually (by norm_num)).mono fun f hf => hf.differentiableAt (by norm_num)
  have hDeq : D =ᶠ[𝓝 (0 : Input T)] fun f =>
      L + B.precompR (Input T) (V f) (D f) + B.precompL (Input T) (D f) (V f) := by
    filter_upwards [heq.eventuallyEq_nhds, hdiff] with f hf hdf
    have hd := (L.hasFDerivAt.add
      (B.hasFDerivAt_of_bilinear hdf.hasFDerivAt hdf.hasFDerivAt)).congr_of_eventuallyEq hf
    simpa only [add_assoc] using hd.fderiv
  have hD0 : D 0 = L := by
    have hz := hDeq.self_of_nhds
    simpa only [hV0, ContinuousLinearMap.map_zero, zero_apply, zero_add, add_zero] using hz
  refine ⟨hD0, ?_⟩
  intro g h
  have hcD : ContDiffAt ℝ 1 D 0 := hcV.fderiv_right (by norm_num)
  let DD := fderiv ℝ D 0
  have hdD : HasFDerivAt D DD 0 := hcD.differentiableAt_one.hasFDerivAt
  have hdV : HasFDerivAt V L 0 := by
    simpa only [D, hD0] using (hcV.differentiableAt (by norm_num)).hasFDerivAt
  have hdDh : HasFDerivAt (fun f => D f h) (DD.flip h) 0 := by
    simpa using hdD.clm_apply (hasFDerivAt_const h (0 : Input T))
  have hDhEq : (fun f => D f h) =ᶠ[𝓝 (0 : Input T)]
      (fun f => L h + B (V f) (D f h) + B (D f h) (V f)) := by
    filter_upwards [hDeq] with f hf
    exact congrArg (fun K : Input T →L[ℝ] Path n T => K h) hf
  have hright := ((hasFDerivAt_const (L h) (0 : Input T)).add
    (B.hasFDerivAt_of_bilinear hdV hdDh)).add
      (B.hasFDerivAt_of_bilinear hdDh hdV)
  have hsecond := hdDh.unique (hright.congr_of_eventuallyEq hDhEq)
  have hsecondg := congrArg (fun K : Input T →L[ℝ] Path n T => K g) hsecond
  simp only [ContinuousLinearMap.flip_apply, add_apply,
    zero_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, hV0, hD0, map_zero, zero_add, add_zero] at hsecondg
  change DD g h = 2 • B (L g) (L h)
  rw [hsecondg, hB (L h) (L g), two_smul]

private def heatAtOperator {n : ℕ} (Q : Frame n) (rates : State n) (t : ℝ) :
    State n →L[ℝ] State n where
  toFun := C145.Pulse.heatAction Q rates t
  map_add' x y := heatAction_vec_add Q rates x y t
  map_smul' c x := heatAction_vec_smul Q rates x t c
  cont := (continuous_heat Q rates).comp (continuous_const.prodMk continuous_id)

private theorem heat_plus_linear_at {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (g : Input T) (t : Time T) :
    heatPath Q rates 1 (linearOperator hT Q rates b g) t = firstState hT Q rates b g t := by
  change C145.Pulse.heatAction Q rates (1 * (t : ℝ)) (ipLinear hT Q rates b g t) = _
  rw [one_mul]
  change (heatAtOperator Q rates t) (∫ s in (0 : ℝ)..(t : ℝ), linearIntegrand hT Q rates b g s) = _
  rw [← (heatAtOperator Q rates t).intervalIntegral_comp_comm
    ((continuous_linearIntegrand hT Q rates b g).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  change C145.Pulse.heatAction Q rates (t : ℝ)
    (extendInput hT g s • C145.Pulse.heatAction Q rates (-s) b) =
      extendInput hT g s • C145.Pulse.heatAction Q rates ((t : ℝ) - s) b
  rw [heatAction_vec_smul, ← heatAction_add Q rates b hQ, sub_eq_add_neg]

private theorem heat_plus_quadratic_at {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n) (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (g h : Input T) (t : Time T) :
    heatPath Q rates 1
        (quadraticOperator hT Q rates (linearOperator hT Q rates b g) (linearOperator hT Q rates b
          h)) t =
      secondState hT Q rates b g h t := by
  let L := linearOperator hT Q rates b
  change C145.Pulse.heatAction Q rates (1 * (t : ℝ)) (ipQuadratic hT Q rates (L g) (L h) t) = _
  rw [one_mul]
  change (heatAtOperator Q rates t)
    (∫ s in (0 : ℝ)..(t : ℝ), quadraticIntegrand hT Q rates (L g) (L h) s) = _
  rw [← (heatAtOperator Q rates t).intervalIntegral_comp_comm
    ((continuous_quadraticIntegrand hT Q rates (L g) (L h)).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsIcc : s ∈ Icc (0 : ℝ) T := by
    rw [uIcc_of_le t.property.1] at hs
    exact ⟨hs.1, hs.2.trans t.property.2⟩
  let ts : Time T := ⟨s, hsIcc⟩
  have hfirst (k : Input T) :
      C145.Pulse.heatAction Q rates s (extendPath hT (L k) s) = firstState hT Q rates b k s := by
    rw [extendPath_at hT (L k) ts]
    have hk := heat_plus_linear_at hT Q rates b hQ k ts
    change C145.Pulse.heatAction Q rates (1 * (ts : ℝ)) (L k ts) =
      firstState hT Q rates b k (ts : ℝ) at hk
    simpa only [one_mul] using hk
  change C145.Pulse.heatAction Q rates (t : ℝ)
    (C145.Pulse.heatAction Q rates (-s)
      (fun x => C145.Pulse.heatAction Q rates s (extendPath hT (L g) s) x *
        C145.Pulse.heatAction Q rates s (extendPath hT (L h) s) x)) =
      C145.Pulse.heatAction Q rates ((t : ℝ) - s)
        (fun x => firstState hT Q rates b g s x * firstState hT Q rates b h s x)
  rw [← heatAction_add Q rates _ hQ, hfirst g, hfirst h, sub_eq_add_neg]

private def observationOperator {n : ℕ} {T : ℝ} (b : State n) (t : Time T) :
    Path n T →L[ℝ] ℝ :=
  ∑ v, b v • ((ContinuousLinearMap.proj v : State n →L[ℝ] ℝ).comp (ContinuousMap.evalCLM ℝ t))

private theorem observationOperator_apply {n : ℕ} {T : ℝ} (b : State n) (t : Time T)
    (u : Path n T) : observationOperator b t u = observe b (u t) := by
  simp only [observationOperator, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousMap.evalCLM_apply,
    smul_eq_mul, observe]

private theorem ordinary_derivatives_of_germ {n : ℕ} {T : ℝ}
    (L : Input T →L[ℝ] Path n T)
    (B : Path n T →L[ℝ] Path n T →L[ℝ] Path n T)
    (hB : ∀ v w, B v w = B w v)
    (V : Input T → Path n T) (hV0 : V 0 = 0) (hcV : ContDiffAt ℝ 2 V 0)
    (heq : V =ᶠ[𝓝 (0 : Input T)] fun f => L f + B (V f) (V f))
    (J : Path n T →L[ℝ] ℝ) (g h : Input T) :
    deriv (fun ε : ℝ => J (V (ε • g))) 0 = J (L g) ∧
      deriv (fun ε : ℝ => deriv (fun δ : ℝ => J (V (ε • g + δ • h))) 0) 0 =
        2 * J (B (L g) (L h)) ∧
      deriv (deriv (fun ε : ℝ => J (V (ε • g)))) 0 = 2 * J (B (L g) (L g)) := by
  let D := fderiv ℝ V
  obtain ⟨hD0, hDD⟩ := interaction_fderiv_two L B hB V hV0 hcV heq
  have hDD' (k l : Input T) : fderiv ℝ D 0 k l = 2 • B (L k) (L l) := hDD k l
  have hdV : HasFDerivAt V L 0 := by
    simpa only [D, hD0] using (hcV.differentiableAt (by norm_num)).hasFDerivAt
  have hline (k : Input T) (x : ℝ) : HasDerivAt (fun ε : ℝ => ε • k) k x := by
    simpa only [id_def, one_smul] using (hasDerivAt_id x).smul_const k
  have hfirst : HasDerivAt (fun ε : ℝ => J (V (ε • g))) (J (L g)) 0 := by
    have hd : HasDerivAt (fun ε : ℝ => V (ε • g)) (L g) 0 := by
      simpa only [Function.comp_def, zero_smul] using
        hdV.comp_hasDerivAt_of_eq 0 (hline g 0) (by simp)
    exact J.hasFDerivAt.comp_hasDerivAt 0 hd
  refine ⟨hfirst.deriv, ?_, ?_⟩
  · have hcD : ContDiffAt ℝ 1 D 0 := hcV.fderiv_right (by norm_num)
    have hdDh : HasFDerivAt (fun f => D f h) ((fderiv ℝ D 0).flip h) 0 := by
      simpa using hcD.differentiableAt_one.hasFDerivAt.clm_apply
        (hasFDerivAt_const h (0 : Input T))
    have hdOuter : HasDerivAt (fun ε : ℝ => J (D (ε • g) h)) (2 * J (B (L g) (L h))) 0 := by
      have hd := J.hasFDerivAt.comp_hasDerivAt 0
        (show HasDerivAt (fun ε : ℝ => D (ε • g) h)
          (fderiv ℝ D 0 g h) 0 by
            simpa only [Function.comp_def, zero_smul, ContinuousLinearMap.flip_apply] using
              hdDh.comp_hasDerivAt_of_eq 0 (hline g 0) (by simp))
      simpa only [Function.comp_def, hDD' g h, two_smul, J.map_add, two_mul] using hd
    have hdiff : ∀ᶠ f in 𝓝 (0 : Input T), DifferentiableAt ℝ V f :=
      (hcV.eventually (by norm_num)).mono fun f hf => hf.differentiableAt (by norm_num)
    have hlineT : Tendsto (fun ε : ℝ => ε • g) (𝓝 (0 : ℝ)) (𝓝 (0 : Input T)) := by
      simpa only [zero_smul] using (hline g 0).continuousAt.tendsto
    have hdiffLine : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ V (ε • g) := hlineT.eventually hdiff
    have heqOuter : (fun ε : ℝ => deriv (fun δ : ℝ => J (V (ε • g + δ • h))) 0) =ᶠ[𝓝 (0 : ℝ)]
        (fun ε : ℝ => J (D (ε • g) h)) := by
      filter_upwards [hdiffLine] with ε hε
      have hdline : HasDerivAt (fun δ : ℝ => ε • g + δ • h) h 0 := by
        exact (hline h 0).const_add (ε • g)
      have hdx : HasDerivAt (fun δ : ℝ => V (ε • g + δ • h)) (D (ε • g) h) 0 := by
        simpa only [D, Function.comp_def, zero_smul, add_zero] using
          hε.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdline (by simp)
      exact (J.hasFDerivAt.comp_hasDerivAt 0 hdx).deriv
    exact (hdOuter.congr_of_eventuallyEq heqOuter).deriv
  · have hcD : ContDiffAt ℝ 1 D 0 := hcV.fderiv_right (by norm_num)
    have hdDg : HasFDerivAt (fun f => D f g) ((fderiv ℝ D 0).flip g) 0 := by
      simpa using hcD.differentiableAt_one.hasFDerivAt.clm_apply
        (hasFDerivAt_const g (0 : Input T))
    have hdOuter : HasDerivAt (fun ε : ℝ => J (D (ε • g) g)) (2 * J (B (L g) (L g))) 0 := by
      have hd := J.hasFDerivAt.comp_hasDerivAt 0
        (show HasDerivAt (fun ε : ℝ => D (ε • g) g)
          (fderiv ℝ D 0 g g) 0 by
            simpa only [Function.comp_def, zero_smul, ContinuousLinearMap.flip_apply] using
              hdDg.comp_hasDerivAt_of_eq 0 (hline g 0) (by simp))
      simpa only [Function.comp_def, hDD' g g, two_smul, J.map_add, two_mul] using hd
    have hdiff : ∀ᶠ f in 𝓝 (0 : Input T), DifferentiableAt ℝ V f :=
      (hcV.eventually (by norm_num)).mono fun f hf => hf.differentiableAt (by norm_num)
    have hlineT : Tendsto (fun ε : ℝ => ε • g) (𝓝 (0 : ℝ)) (𝓝 (0 : Input T)) := by
      simpa only [zero_smul] using (hline g 0).continuousAt.tendsto
    have hdiffLine : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ V (ε • g) := hlineT.eventually hdiff
    have heqOuter : deriv (fun ε : ℝ => J (V (ε • g))) =ᶠ[𝓝 (0 : ℝ)]
        (fun ε : ℝ => J (D (ε • g) g)) := by
      filter_upwards [hdiffLine] with ε hε
      exact (J.hasFDerivAt.comp_hasDerivAt ε (hε.hasFDerivAt.comp_hasDerivAt ε (hline g ε))).deriv
    exact (hdOuter.congr_of_eventuallyEq heqOuter).deriv

theorem actual_response_variations {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R : Input T → Path n T)
    (hR : IsActualResponse hT Q rates b R) (hcR : ContDiffAt ℝ 2 R 0)
    (g h : Input T) (t : Time T) :
    rawFirst b R g t = observe b (firstState hT Q rates b g t) ∧
      rawMixed b R g h t = observe b (secondState hT Q rates b g h t) ∧
      rawQuadratic b R g t = observe b (secondState hT Q rates b g g t) := by
  let L := linearOperator hT Q rates b
  let B := quadraticOperator hT Q rates
  let Pminus := heatOperator hT Q rates (-1) (by norm_num : |(-1 : ℝ)| ≤ 1)
  let Pplus := heatOperator hT Q rates 1 (by norm_num : |(1 : ℝ)| ≤ 1)
  let V : Input T → Path n T := fun f => Pminus (R f)
  let J := (observationOperator b t).comp Pplus
  have hV0 : V 0 = 0 := by simp only [V, hR.1, map_zero]
  have hcV : ContDiffAt ℝ 2 V 0 := Pminus.contDiff.contDiffAt.comp 0 hcR
  have heq : V =ᶠ[𝓝 (0 : Input T)] fun f => L f + B (V f) (V f) := by
    filter_upwards [hR.2] with f hf
    exact actual_path_interaction hT Q rates b hQ f (R f) hf.1 hf.2
  have hB : ∀ v w, B v w = B w v := quadraticPath_symm hT Q rates
  have hscalar (f : Input T) : observe b (R f t) = J (V f) := by
    rw [show J (V f) = observe b (heatPath Q rates 1 (heatPath Q rates (-1) (R f)) t) by
      exact observationOperator_apply b t _]
    rw [(heat_paths_inverse hT Q rates hQ (R f)).1]
  obtain ⟨hfirst, hmixed, hquad⟩ := ordinary_derivatives_of_germ L B hB V hV0 hcV heq J g h
  have hJfirst : J (L g) = observe b (firstState hT Q rates b g t) := by
    rw [show J (L g) = observe b (heatPath Q rates 1 (L g) t) by
      exact observationOperator_apply b t _]
    rw [heat_plus_linear_at hT Q rates b hQ g t]
  have hJsecond (k : Input T) : J (B (L g) (L k)) = observe b (secondState hT Q rates b g k t) := by
    rw [show J (B (L g) (L k)) = observe b (heatPath Q rates 1 (B (L g) (L k)) t) by
      exact observationOperator_apply b t _]
    rw [heat_plus_quadratic_at hT Q rates b hQ g k t]
  constructor
  · unfold rawFirst
    simp_rw [hscalar]
    exact hfirst.trans hJfirst
  · constructor
    · unfold rawMixed
      simp_rw [hscalar]
      rw [hmixed, hJsecond h]
      ring
    · unfold rawQuadratic
      simp_rw [hscalar]
      rw [hquad, hJsecond g]
      ring

-- Inert audit requests: no axiom printer has run in this workspace.

end C145.ActualResponse
end

end
