/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145UncalibratedSmallH2
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Transfer of response kernels between the time and Laplace domains.
-/

@[expose] public section

noncomputable section
namespace C145.DelayKernel
open MeasureTheory Set
open scoped BigOperators

/-- Observe the heat action on the port through the same port. -/
def firstKernel {n : ℕ}
     (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
     (rates b : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
   ∑ v, b v * C145.Pulse.heatAction Q rates t b v

/-- Observe the heat-propagated product of the two delayed port heat actions. -/
def delayIntegrand {n : ℕ}
     (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
     (rates b : Fin (n + 1) → ℝ) (r₁ r₂ a : ℝ) : ℝ :=
   ∑ v, b v * C145.Pulse.heatAction Q rates a
     (fun u => C145.Pulse.heatAction Q rates (r₁ - a) b u *
       C145.Pulse.heatAction Q rates (r₂ - a) b u) v

/-- Integrate the quadratic delay integrand up to the smaller input delay. -/
def delayKernel {n : ℕ}
     (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
     (rates b : Fin (n + 1) → ℝ) (r₁ r₂ : ℝ) : ℝ :=
   ∫ a in (0 : ℝ)..min r₁ r₂, delayIntegrand Q rates b r₁ r₂ a

/-- The three-exponential delay integral for one triple of modal rates. -/
def scalarDelay (α β γ r₁ r₂ : ℝ) : ℝ :=
   ∫ a in (0 : ℝ)..min r₁ r₂,
     Real.exp (-α * (r₁ - a)) * Real.exp (-β * (r₂ - a)) * Real.exp (-γ * a)

/-- The one-variable Laplace integral over positive times. -/
def laplace (f : ℝ → ℝ) (s : ℝ) : ℝ :=
   ∫ r in Ioi (0 : ℝ), Real.exp (-s * r) * f r

/-- The iterated Laplace integral over the positive delay quadrant. -/
def doubleLaplace (f : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
   ∫ r₁ in Ioi (0 : ℝ), ∫ r₂ in Ioi (0 : ℝ),
     Real.exp (-s * r₁) * Real.exp (-t * r₂) * f r₁ r₂

private theorem heatAction_port_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (t : ℝ) (v : Fin (n + 1)) :
    C145.Pulse.heatAction Q rates t b v =
      ∑ i, C145.Pulse.modalOverlap Q b i * Real.exp (-rates i * t) * Q v i := by
  classical
  unfold C145.Pulse.heatAction
  apply Finset.sum_congr rfl
  intro i hi
  have hInner : (∑ u, Q u i * b u) = C145.Pulse.modalOverlap Q b i := by
    unfold C145.Pulse.modalOverlap
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hInner]
  ring

private theorem delayIntegrand_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (r₁ r₂ a : ℝ) :
    delayIntegrand Q rates b r₁ r₂ a =
      ∑ i, ∑ j, ∑ k,
        C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
          Real.exp (-rates i * (r₁ - a)) *
          Real.exp (-rates j * (r₂ - a)) * Real.exp (-rates k * a) := by
  classical
  let a₀ := C145.Pulse.modalOverlap Q b
  have hProduct (u : Fin (n + 1)) :
      C145.Pulse.heatAction Q rates (r₁ - a) b u *
          C145.Pulse.heatAction Q rates (r₂ - a) b u =
        ∑ i, ∑ j, (a₀ i * a₀ j * Q u i * Q u j) *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) := by
    rw [heatAction_port_expansion, heatAction_port_expansion, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [a₀]
    ring
  have hOutput (x : Fin (n + 1) → ℝ) :
      (∑ v, b v * C145.Pulse.heatAction Q rates a x v) =
        ∑ k, a₀ k * Real.exp (-rates k * a) * (∑ u, Q u k * x u) := by
    calc
      (∑ v, b v * C145.Pulse.heatAction Q rates a x v) =
          ∑ v, ∑ k, b v * (Q v k * Real.exp (-rates k * a) *
            (∑ u, Q u k * x u)) := by
        unfold C145.Pulse.heatAction
        simp only [Finset.mul_sum]
      _ = ∑ k, ∑ v, b v * (Q v k * Real.exp (-rates k * a) *
          (∑ u, Q u k * x u)) := by rw [Finset.sum_comm]
      _ = ∑ k, a₀ k * Real.exp (-rates k * a) * (∑ u, Q u k * x u) := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [a₀, C145.Pulse.modalOverlap]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        ring
  have hProjection (k : Fin (n + 1)) :
      (∑ u, Q u k * (C145.Pulse.heatAction Q rates (r₁ - a) b u *
          C145.Pulse.heatAction Q rates (r₂ - a) b u)) =
        ∑ i, ∑ j, (a₀ i * a₀ j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) := by
    simp_rw [hProduct]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ u, ∑ j, Q u k * ((a₀ i * a₀ j * Q u i * Q u j) *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)))) =
          ∑ i, ∑ j, ∑ u, Q u k * ((a₀ i * a₀ j * Q u i * Q u j) *
            Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, (a₀ i * a₀ j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [C145PhysicalFrame.C, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        ring
  unfold delayIntegrand
  rw [hOutput]
  simp_rw [hProjection]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ k, ∑ j, a₀ k * Real.exp (-rates k * a) *
        ((a₀ i * a₀ j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)))) =
        ∑ i, ∑ j, ∑ k, a₀ k * Real.exp (-rates k * a) *
          ((a₀ i * a₀ j * C145PhysicalFrame.C Q i j k) *
            Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [a₀, C145PhysicalFrame.T]
      ring

theorem firstKernel_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (t : ℝ) :
    firstKernel Q rates b t =
      ∑ i, (C145.Pulse.modalOverlap Q b i) ^ 2 * Real.exp (-rates i * t) := by
  classical
  unfold firstKernel
  simp_rw [heatAction_port_expansion]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ v, b v * (C145.Pulse.modalOverlap Q b i * Real.exp (-rates i * t) * Q v i)) =
        (∑ v, b v * Q v i) * C145.Pulse.modalOverlap Q b i * Real.exp (-rates i * t) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = (C145.Pulse.modalOverlap Q b i) ^ 2 * Real.exp (-rates i * t) := by
      change C145.Pulse.modalOverlap Q b i * C145.Pulse.modalOverlap Q b i * _ = _
      ring

theorem delayKernel_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (r₁ r₂ : ℝ) :
    delayKernel Q rates b r₁ r₂ =
      ∑ i, ∑ j, ∑ k,
        C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
          scalarDelay (rates i) (rates j) (rates k) r₁ r₂ := by
  classical
  have hTerm (i j k : Fin (n + 1)) :
      IntervalIntegrable (fun a : ℝ =>
        C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) *
            Real.exp (-rates k * a)) volume 0 (min r₁ r₂) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hRow (i j : Fin (n + 1)) :
      IntervalIntegrable (fun a : ℝ => ∑ k,
        C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) *
            Real.exp (-rates k * a)) volume 0 (min r₁ r₂) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hPlane (i : Fin (n + 1)) :
      IntervalIntegrable (fun a : ℝ => ∑ j, ∑ k,
        C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
          Real.exp (-rates i * (r₁ - a)) * Real.exp (-rates j * (r₂ - a)) *
            Real.exp (-rates k * a)) volume 0 (min r₁ r₂) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold delayKernel
  simp_rw [delayIntegrand_expansion]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hPlane i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum (fun j _ => hRow i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_finsetSum (fun k _ => hTerm i j k)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [scalarDelay, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a ha
  ring

private theorem integral_exp_linear (q u : ℝ) :
    (∫ a in (0 : ℝ)..u, Real.exp (q * a)) =
      if q = 0 then u else (Real.exp (q * u) - 1) / q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [ite_eq_right hq]
    have hSubstitution := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.exp) (a := (0 : ℝ)) (b := u) q
    simp only [mul_zero, _root_.integral_exp, Real.exp_zero] at hSubstitution
    apply (eq_div_iff hq).2
    simpa only [mul_comm] using hSubstitution

private theorem scalarDelay_factor (α β γ r₁ r₂ : ℝ) :
    scalarDelay α β γ r₁ r₂ =
      Real.exp (-α * r₁ - β * r₂) *
        (∫ a in (0 : ℝ)..min r₁ r₂, Real.exp ((α + β - γ) * a)) := by
  unfold scalarDelay
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a ha
  simp only [← Real.exp_add]
  congr 1
  ring

private theorem scalarDelay_continuous (α β γ : ℝ) :
    Continuous (fun p : ℝ × ℝ => scalarDelay α β γ p.1 p.2) := by
  by_cases hq : α + β - γ = 0
  · simp_rw [scalarDelay_factor, integral_exp_linear, ite_eq_left hq]
    fun_prop
  · simp_rw [scalarDelay_factor, integral_exp_linear, ite_eq_right hq]
    fun_prop

private theorem scalarDelay_nonneg (α β γ r₁ r₂ : ℝ)
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) : 0 ≤ scalarDelay α β γ r₁ r₂ := by
  unfold scalarDelay
  apply intervalIntegral.integral_nonneg_of_forall (le_min h₁ h₂)
  intro a
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (Real.exp_pos _).le

private theorem truncated_exp_integrable (q r : ℝ) (_hr : 0 ≤ r) :
    IntegrableOn ((Iic r).indicator (fun a : ℝ => Real.exp (-q * a)))
      (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun a : ℝ => Real.exp (-q * a)) := by fun_prop
  have hI : Iic r ∩ Ioi (0 : ℝ) = Ioc 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc, and_comm]
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
  simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Iic, hI] using
    (hc.integrableOn_Ioc (a := (0 : ℝ)) (b := r))

private theorem scalarDelay_weighted_truncation (α β γ t r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) :
    Real.exp (-t * z) * scalarDelay α β γ r z =
      Real.exp (-α * r) *
        (∫ a in (0 : ℝ)..z,
          (Iic r).indicator (fun x : ℝ => Real.exp (-(t + γ - α) * x)) a *
            Real.exp (-(t + β) * (z - a))) := by
  have hFactor :
      Real.exp (-t * z) * scalarDelay α β γ r z =
        Real.exp (-α * r) *
          (∫ a in (0 : ℝ)..min r z,
            Real.exp (-(t + γ - α) * a) * Real.exp (-(t + β) * (z - a))) := by
    unfold scalarDelay
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro a ha
    simp only [← Real.exp_add]
    congr 1
    ring
  have hIndicator :
      (fun a : ℝ => (Iic r).indicator (fun x : ℝ => Real.exp (-(t + γ - α) * x)) a *
          Real.exp (-(t + β) * (z - a))) =
        (Iic r).indicator (fun a : ℝ =>
          Real.exp (-(t + γ - α) * a) * Real.exp (-(t + β) * (z - a))) := by
    funext a
    by_cases ha : a ∈ Iic r <;> simp [ha]
  rw [hFactor, hIndicator]
  congr 1
  rcases le_total r z with hrz | hzr
  · rw [min_eq_left hrz]
    exact (intervalIntegral.integral_indicator ⟨hr, hrz⟩).symm
  · rw [min_eq_right hzr]
    symm
    apply intervalIntegral.integral_congr
    intro a ha
    have haz : a ≤ z := (show a ∈ Icc (0 : ℝ) z from by
      simpa only [Set.uIcc_of_le hz] using ha).2
    exact Set.indicator_of_mem (show a ∈ Iic r from le_trans haz hzr) _

private theorem scalarDelay_laplace_right (α β γ t r : ℝ)
    (hr : 0 ≤ r) (hB : 0 < t + β) :
    IntegrableOn (fun z : ℝ => Real.exp (-t * z) * scalarDelay α β γ r z)
      (Ioi (0 : ℝ)) ∧
    (∫ z in Ioi (0 : ℝ), Real.exp (-t * z) * scalarDelay α β γ r z) =
      Real.exp (-α * r) / (t + β) *
        (∫ a in (0 : ℝ)..r, Real.exp (-(t + γ - α) * a)) := by
  let f : ℝ → ℝ := (Iic r).indicator (fun a : ℝ => Real.exp (-(t + γ - α) * a))
  let g : ℝ → ℝ := fun v => Real.exp (-(t + β) * v)
  let c : ℝ → ℝ := fun z => ∫ a in (0 : ℝ)..z, f a * g (z - a)
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := truncated_exp_integrable _ _ hr
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hB) 0
  have hc : IntegrableOn c (Ioi (0 : ℝ)) := by
    have h := (integrable_posConvolution (μ := volume) (ν := volume) hf hg
      (ContinuousLinearMap.mul ℝ ℝ)).integrableOn (s := Ioi (0 : ℝ))
    apply h.congr_fun _ measurableSet_Ioi
    intro z hz
    simp only [posConvolution, Set.indicator_of_mem hz,
      ContinuousLinearMap.mul_apply', c]
  have hPoint (z : ℝ) (hz : 0 ≤ z) :
      Real.exp (-t * z) * scalarDelay α β γ r z = Real.exp (-α * r) * c z :=
    scalarDelay_weighted_truncation α β γ t r z hr hz
  have hInt : IntegrableOn
      (fun z : ℝ => Real.exp (-t * z) * scalarDelay α β γ r z) (Ioi (0 : ℝ)) := by
    exact IntegrableOn.congr_fun
      (f := fun z : ℝ => Real.exp (-α * r) * c z)
      (g := fun z : ℝ => Real.exp (-t * z) * scalarDelay α β γ r z)
      (s := Ioi (0 : ℝ)) (μ := volume)
      (hc.const_mul (Real.exp (-α * r)))
      (fun z hz => (hPoint z hz.le).symm) measurableSet_Ioi
  have hF : (∫ a in Ioi (0 : ℝ), f a) =
      ∫ a in (0 : ℝ)..r, Real.exp (-(t + γ - α) * a) := by
    dsimp only [f]
    rw [setIntegral_indicator measurableSet_Iic]
    have hSet : Ioi (0 : ℝ) ∩ Iic r = Ioc 0 r := rfl
    rw [hSet, ← intervalIntegral.integral_of_le hr]
  have hG : (∫ v in Ioi (0 : ℝ), g v) = 1 / (t + β) := by
    dsimp only [g]
    rw [integral_exp_mul_Ioi (neg_neg_of_pos hB) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ne_of_gt hB]
  have hC : (∫ z in Ioi (0 : ℝ), c z) =
      (∫ a in Ioi (0 : ℝ), f a) * (∫ v in Ioi (0 : ℝ), g v) := by
    simpa only [c, ContinuousLinearMap.mul_apply'] using
      (integral_posConvolution (μ := volume) (ν := volume) hf hg
        (ContinuousLinearMap.mul ℝ ℝ))
  refine ⟨hInt, ?_⟩
  calc
    (∫ z in Ioi (0 : ℝ), Real.exp (-t * z) * scalarDelay α β γ r z) =
        ∫ z in Ioi (0 : ℝ), Real.exp (-α * r) * c z :=
      setIntegral_congr_fun measurableSet_Ioi (fun z hz => hPoint z hz.le)
    _ = Real.exp (-α * r) * (∫ z in Ioi (0 : ℝ), c z) := integral_const_mul _ _
    _ = Real.exp (-α * r) / (t + β) *
        (∫ a in (0 : ℝ)..r, Real.exp (-(t + γ - α) * a)) := by
      rw [hC, hF, hG]
      ring

private theorem scalarDelay_transform (α β γ s t : ℝ)
    (hA : 0 < s + α) (hB : 0 < t + β) (hC : 0 < s + t + γ) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-s * p.1) * Real.exp (-t * p.2) *
        scalarDelay α β γ p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) ∧
    doubleLaplace (scalarDelay α β γ) s t =
      1 / ((s + α) * (t + β) * (s + t + γ)) := by
  let ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let A : ℝ := s + α
  let B : ℝ := t + β
  let C : ℝ := s + t + γ
  let f : ℝ → ℝ := fun a => Real.exp (-C * a)
  let g : ℝ → ℝ := fun v => Real.exp (-A * v)
  let c : ℝ → ℝ := fun r => ∫ a in (0 : ℝ)..r, f a * g (r - a)
  let F : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-s * p.1) * Real.exp (-t * p.2) * scalarDelay α β γ p.1 p.2
  have hf : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hC) 0
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hA) 0
  have hc : IntegrableOn c (Ioi (0 : ℝ)) := by
    have h := (integrable_posConvolution (μ := volume) (ν := volume) hf hg
      (ContinuousLinearMap.mul ℝ ℝ)).integrableOn (s := Ioi (0 : ℝ))
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [posConvolution, Set.indicator_of_mem hr,
      ContinuousLinearMap.mul_apply', c]
  have hOuter (r : ℝ) :
      Real.exp (-s * r) *
          (Real.exp (-α * r) / B *
            (∫ a in (0 : ℝ)..r, Real.exp (-(t + γ - α) * a))) =
        (1 / B) * c r := by
    calc
      Real.exp (-s * r) * (Real.exp (-α * r) / B *
          (∫ a in (0 : ℝ)..r, Real.exp (-(t + γ - α) * a))) =
          (1 / B) * (∫ a in (0 : ℝ)..r,
            Real.exp (-s * r) * Real.exp (-α * r) *
              Real.exp (-(t + γ - α) * a)) := by
        simp only [intervalIntegral.integral_const_mul]
        ring
      _ = (1 / B) * c r := by
        congr 1
        apply intervalIntegral.integral_congr
        intro a ha
        dsimp only [c, f, g, A, C]
        simp only [← Real.exp_add]
        congr 1
        ring
  have hSection (r : ℝ) (hr : 0 ≤ r) : Integrable (fun z => F (r, z)) ρ := by
    have h := (scalarDelay_laplace_right α β γ t r hr hB).1.const_mul (Real.exp (-s * r))
    apply h.congr
    exact Filter.Eventually.of_forall (fun z => by dsimp [F]; ring)
  have hSectionIntegral (r : ℝ) (hr : 0 ≤ r) :
      (∫ z, F (r, z) ∂ρ) = (1 / B) * c r := by
    change (∫ z in Ioi (0 : ℝ), Real.exp (-s * r) * Real.exp (-t * z) *
      scalarDelay α β γ r z) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul, (scalarDelay_laplace_right α β γ t r hr hB).2]
    exact hOuter r
  have hNonneg (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) : 0 ≤ F (r, z) := by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (scalarDelay_nonneg α β γ r z hr hz)
  have hNorm (r : ℝ) (hr : 0 ≤ r) :
      (∫ z, ‖F (r, z)‖ ∂ρ) = (1 / B) * c r := by
    calc
      (∫ z, ‖F (r, z)‖ ∂ρ) = ∫ z, F (r, z) ∂ρ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        exact Real.norm_of_nonneg (hNonneg r z hr hz.le)
      _ = (1 / B) * c r := hSectionIntegral r hr
  have hContinuous : Continuous F := by
    exact ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-s * p.1) * Real.exp (-t * p.2))).mul
        (scalarDelay_continuous α β γ))
  have hProduct : Integrable F (ρ.prod ρ) := by
    apply (integrable_prod_iff hContinuous.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hSection r hr.le
    · exact IntegrableOn.congr_fun
        (f := fun r : ℝ => (1 / B) * c r)
        (g := fun r : ℝ => ∫ z, ‖F (r, z)‖ ∂ρ)
        (s := Ioi (0 : ℝ)) (μ := volume)
        (hc.const_mul (1 / B))
        (fun r hr => (hNorm r hr.le).symm) measurableSet_Ioi
  have hFIntegral : (∫ a in Ioi (0 : ℝ), f a) = 1 / C := by
    change (∫ a in Ioi (0 : ℝ), Real.exp (-(s + t + γ) * a)) = 1 / (s + t + γ)
    rw [integral_exp_mul_Ioi (neg_neg_of_pos hC) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ne_of_gt hC]
  have hGIntegral : (∫ v in Ioi (0 : ℝ), g v) = 1 / A := by
    change (∫ v in Ioi (0 : ℝ), Real.exp (-(s + α) * v)) = 1 / (s + α)
    rw [integral_exp_mul_Ioi (neg_neg_of_pos hA) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ne_of_gt hA]
  have hCIntegral : (∫ r in Ioi (0 : ℝ), c r) = (1 / C) * (1 / A) := by
    have h := integral_posConvolution (μ := volume) (ν := volume) hf hg
      (ContinuousLinearMap.mul ℝ ℝ)
    simpa only [ContinuousLinearMap.mul_apply', hFIntegral, hGIntegral, c] using h
  refine ⟨hProduct, ?_⟩
  change (∫ r in Ioi (0 : ℝ), ∫ z, F (r, z) ∂ρ) = _
  calc
    (∫ r in Ioi (0 : ℝ), ∫ z, F (r, z) ∂ρ) =
        ∫ r in Ioi (0 : ℝ), (1 / B) * c r :=
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => hSectionIntegral r hr.le)
    _ = (1 / B) * ((1 / C) * (1 / A)) := by
      rw [integral_const_mul, hCIntegral]
    _ = 1 / ((s + α) * (t + β) * (s + t + γ)) := by
      dsimp only [A, B, C]
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]

theorem delayKernel_diagonal {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (t : ℝ) :
    delayKernel Q rates b t t = C145.Pulse.coincidentPulse Q rates b t := by
  unfold delayKernel C145.Pulse.coincidentPulse
  rw [min_self]
  have hSub := intervalIntegral.integral_comp_sub_left
    (fun a : ℝ => delayIntegrand Q rates b t t a) (a := (0 : ℝ)) (b := t) t
  simp only [sub_self, sub_zero] at hSub
  rw [← hSub]
  apply intervalIntegral.integral_congr
  intro s hs
  unfold delayIntegrand
  apply Finset.sum_congr rfl
  intro v hv
  have hArg : t - (t - s) = s := by ring
  simp only [hArg, pow_two]

theorem firstKernel_transform {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ)
    (hRates : ∀ i, 0 < rates i) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun r : ℝ => Real.exp (-s * r) * firstKernel Q rates b r)
      (Ioi (0 : ℝ)) ∧
    laplace (firstKernel Q rates b) s =
      C145.H1.firstTransfer rates (C145.Pulse.modalOverlap Q b) s := by
  classical
  let a₀ := C145.Pulse.modalOverlap Q b
  let f : Fin (n + 1) → ℝ → ℝ := fun i r => a₀ i ^ 2 * Real.exp (-(s + rates i) * r)
  have hPos (i : Fin (n + 1)) : 0 < s + rates i := add_pos hs (hRates i)
  have hInt (i : Fin (n + 1)) : IntegrableOn (f i) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hPos i)) 0).const_mul (a₀ i ^ 2)
  have hExpansion (r : ℝ) : Real.exp (-s * r) * firstKernel Q rates b r = ∑ i, f i r := by
    rw [firstKernel_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f, a₀]
    calc
      Real.exp (-s * r) * (C145.Pulse.modalOverlap Q b i ^ 2 * Real.exp (-rates i * r)) =
          C145.Pulse.modalOverlap Q b i ^ 2 * (Real.exp (-s * r) * Real.exp (-rates i * r)) := by
            ring
      _ = C145.Pulse.modalOverlap Q b i ^ 2 * Real.exp (-(s + rates i) * r) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hSum := integrable_finsetSum Finset.univ (fun i _ => hInt i)
  refine ⟨hSum.congr (Filter.Eventually.of_forall (fun r => (hExpansion r).symm)), ?_⟩
  unfold laplace C145.H1.firstTransfer C145.H1.weightedTransfer
  simp_rw [hExpansion]
  rw [integral_finsetSum Finset.univ (fun i _ => hInt i)]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [f, a₀]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (hPos i)) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_gt (hPos i)]

theorem delayKernel_transform {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ)
    (hRates : ∀ i, 0 < rates i) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-s * p.1) * Real.exp (-t * p.2) *
        delayKernel Q rates b p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) ∧
    doubleLaplace (delayKernel Q rates b) s t =
      C145.H2.H rates
        (C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b)) s t := by
  classical
  let ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let T := C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b)
  let f : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ × ℝ → ℝ :=
    fun i j k p => Real.exp (-s * p.1) * Real.exp (-t * p.2) *
      scalarDelay (rates i) (rates j) (rates k) p.1 p.2
  let F : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-s * p.1) * Real.exp (-t * p.2) * delayKernel Q rates b p.1 p.2
  have hA (i : Fin (n + 1)) : 0 < s + rates i := add_pos hs (hRates i)
  have hB (j : Fin (n + 1)) : 0 < t + rates j := add_pos ht (hRates j)
  have hC (k : Fin (n + 1)) : 0 < s + t + rates k := add_pos (add_pos hs ht) (hRates k)
  have hScalar (i j k : Fin (n + 1)) : Integrable (f i j k) (ρ.prod ρ) :=
    (scalarDelay_transform (rates i) (rates j) (rates k) s t (hA i) (hB j) (hC k)).1
  have hTerm (i j k : Fin (n + 1)) :
      Integrable (fun p => T i j k * f i j k p) (ρ.prod ρ) :=
    (hScalar i j k).const_mul (T i j k)
  have hRow (i j : Fin (n + 1)) :
      Integrable (fun p => ∑ k, T i j k * f i j k p) (ρ.prod ρ) :=
    integrable_finsetSum Finset.univ (fun k _ => hTerm i j k)
  have hPlane (i : Fin (n + 1)) :
      Integrable (fun p => ∑ j, ∑ k, T i j k * f i j k p) (ρ.prod ρ) :=
    integrable_finsetSum Finset.univ (fun j _ => hRow i j)
  have hSum : Integrable (fun p => ∑ i, ∑ j, ∑ k, T i j k * f i j k p) (ρ.prod ρ) :=
    integrable_finsetSum Finset.univ (fun i _ => hPlane i)
  have hExpansion (p : ℝ × ℝ) : F p = ∑ i, ∑ j, ∑ k, T i j k * f i j k p := by
    dsimp only [F]
    rw [delayKernel_expansion]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [T, f]
    ring
  have hActual : Integrable F (ρ.prod ρ) :=
    hSum.congr (Filter.Eventually.of_forall (fun p => (hExpansion p).symm))
  refine ⟨hActual, ?_⟩
  calc
    doubleLaplace (delayKernel Q rates b) s t = ∫ p, F p ∂(ρ.prod ρ) :=
      (integral_prod F hActual).symm
    _ = ∫ p, (∑ i, ∑ j, ∑ k, T i j k * f i j k p) ∂(ρ.prod ρ) :=
      integral_congr_ae (Filter.Eventually.of_forall hExpansion)
    _ = ∑ i, ∑ j, ∑ k, ∫ p, T i j k * f i j k p ∂(ρ.prod ρ) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hPlane i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum Finset.univ (fun j _ => hRow i j)]
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_finsetSum Finset.univ (fun k _ => hTerm i j k)
    _ = C145.H2.H rates (C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b)) s t := by
      unfold C145.H2.H
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul, integral_prod (f i j k) (hScalar i j k)]
      change T i j k * doubleLaplace (scalarDelay (rates i) (rates j) (rates k)) s t = _
      rw [(scalarDelay_transform (rates i) (rates j) (rates k) s t
        (hA i) (hB j) (hC k)).2]
      dsimp only [T]
      ring

private theorem rates_pos_of_ground {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (rates : Fin (n + 1) → ℝ) (hGround : rates 0 = μ)
    (hAbove : ∀ i : Fin n, μ < rates i.succ) : ∀ i, 0 < rates i := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
  · rw [hi, hGround]
    exact hμ
  · rw [hj]
    exact lt_trans hμ (hAbove j)

theorem actual_time_kernel_vertex_identification {m n : ℕ}
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 : Fin (m + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround0 : ∀ v, Q0 v 0 = c0)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hRateGround0 : rates0 0 = μ)
    (hRateGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < C145.Pulse.modalOverlap Q0 b0 i)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (hm : m ≤ 4)
    (hK1 : ∀ r : ℝ, 0 ≤ r →
      firstKernel Q0 rates0 b0 r = firstKernel Q1 rates1 b1 r)
    (hK2 : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
      delayKernel Q0 rates0 b0 r₁ r₂ =
        delayKernel Q1 rates1 b1 r₁ r₂) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap Q0 b0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ w, b1 w) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (m + 1)),
          (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator rates0 Q0 v u) ∧
        (∀ v : Fin (m + 1), b1 (π v) = b0 v) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u) := by
  have hPos0 := rates_pos_of_ground μ hμ rates0 hRateGround0 hAbove0
  have hPos1 := rates_pos_of_ground μ hμ rates1 hRateGround1 hAbove1
  have hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer rates0 (C145.Pulse.modalOverlap Q0 b0) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s := by
    intro s hs
    rw [← (firstKernel_transform Q0 rates0 b0 hPos0 s hs).2,
      ← (firstKernel_transform Q1 rates1 b1 hPos1 s hs).2]
    unfold laplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.exp (-s * r) * firstKernel Q0 rates0 b0 r =
      Real.exp (-s * r) * firstKernel Q1 rates1 b1 r
    rw [hK1 r hr.le]
  have hB : ∀ t : ℝ, 0 ≤ t →
      C145.Pulse.coincidentPulse Q0 rates0 b0 t =
        C145.Pulse.coincidentPulse Q1 rates1 b1 t := by
    intro t ht
    rw [← delayKernel_diagonal Q0 rates0 b0 t,
      ← delayKernel_diagonal Q1 rates1 b1 t]
    exact hK2 t t ht ht
  have hH2 : ∀ s t : ℝ, 0 < s → 0 < t →
      C145.H2.H rates0 (C145PhysicalFrame.T Q0 (C145.Pulse.modalOverlap Q0 b0)) s t =
        C145.H2.H rates1 (C145PhysicalFrame.T Q1 (C145.Pulse.modalOverlap Q1 b1)) s t := by
    intro s t hs ht
    rw [← (delayKernel_transform Q0 rates0 b0 hPos0 s t hs ht).2,
      ← (delayKernel_transform Q1 rates1 b1 hPos1 s t hs ht).2]
    unfold doubleLaplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₁ hr₁
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₂ hr₂
    change Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel Q0 rates0 b0 r₁ r₂ =
      Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel Q1 rates1 b1 r₁ r₂
    rw [hK2 r₁ r₂ hr₁.le hr₂.le]
  exact C145.UncalibratedSmallH2.actual_small_H2_vertex_identification
    μ c0 c1 hμ Q0 Q1 rates0 b0 rates1 b1 hQ0 hQ1 hGround0 hGround1
    hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1 hm
    hH1 hB hH2


end C145.DelayKernel
end

end
