/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145PhysicalFrame
public import LeanPool.C145.C145H1ModalCalibration
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
C145: actual finite coincident-pulse data calibrate the signed ground column.
This is a compile-free source proposal. No elaboration or axiom output is claimed.

The heat action is a finite vertex-space formula, and B is its literal integral
with a vertexwise square. Its tensor expansion and its large-time limit are
proved below, rather than supplied as data. Each model has its own frame, port,
constant ground column and physical rates. Positive overlap orientation and a
simple visible spectrum are explicit. The modal equivalence and common signed
constant/port mean are conclusions. A modal equivalence is not a vertex map.

The physical mode set is Fin (n + 1), including the one-vertex case n = 0.
Successor rate entries are physical rates, never mu plus physical rates.
No graph realization, response extraction, raw-jet, H2 or stability join occurs.
-/

@[expose] public section

noncomputable section
namespace C145.Pulse
open Filter
open scoped BigOperators Topology

/-- The actual signed-port scalar product with a frame column. -/
def modalOverlap {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (b : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ v, b v * Q v i

/-- Actual finite spectral action on an arbitrary vertex vector. -/
def heatAction {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates : Fin (n + 1) → ℝ) (t : ℝ)
    (x : Fin (n + 1) → ℝ) (v : Fin (n + 1)) : ℝ :=
  ∑ i, Q v i * Real.exp (-rates i * t) * (∑ u, Q u i * x u)

/-- The square is formed at each vertex before the output heat action. -/
def coincidentPulse {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ∑ v, b v *
    heatAction Q rates (t - s) (fun u => (heatAction Q rates s b u) ^ 2) v

/-- A scalar integral auxiliary; it is not a definition of the observed B. -/
def decayConvolution (α γ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-α * (t - s)) * Real.exp (-γ * s)

/-- The factor whose positivity and occurrence in the actual limit are proved. -/
def groundFactor {n : ℕ} (μ : ℝ)
    (rates a : Fin (n + 1) → ℝ) : ℝ :=
  a 0 * ∑ i, a i ^ 2 / (2 * rates i - μ)

private theorem heatAction_port {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b a : Fin (n + 1) → ℝ)
    (hOverlap : ∀ i, a i = modalOverlap Q b i)
    (t : ℝ) (v : Fin (n + 1)) :
    heatAction Q rates t b v =
      ∑ i, a i * Real.exp (-rates i * t) * Q v i := by
  classical
  unfold heatAction
  apply Finset.sum_congr rfl
  intro i hi
  have hInner : (∑ u, Q u i * b u) = a i := by
    rw [hOverlap i, modalOverlap]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hInner]
  ring

private theorem pulse_integrand_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b a : Fin (n + 1) → ℝ)
    (hOverlap : ∀ i, a i = modalOverlap Q b i) (t s : ℝ) :
    (∑ v, b v * heatAction Q rates (t - s)
      (fun u => (heatAction Q rates s b u) ^ 2) v) =
      ∑ i, ∑ j, ∑ k, C145PhysicalFrame.T Q a i j k *
        Real.exp (-rates k * (t - s)) *
        Real.exp (-(rates i + rates j) * s) := by
  classical
  -- First expand the actual square at a fixed vertex.
  have hSquare (u : Fin (n + 1)) :
      (heatAction Q rates s b u) ^ 2 =
        ∑ i, ∑ j, (a i * a j * Q u i * Q u j) *
          Real.exp (-(rates i + rates j) * s) := by
    rw [heatAction_port Q rates b a hOverlap s u, pow_two,
      Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (a i * Real.exp (-rates i * s) * Q u i) *
          (a j * Real.exp (-rates j * s) * Q u j) =
          (a i * a j * Q u i * Q u j) *
            (Real.exp (-rates i * s) * Real.exp (-rates j * s)) := by ring
      _ = (a i * a j * Q u i * Q u j) *
          Real.exp (-(rates i + rates j) * s) := by
        rw [← Real.exp_add]
        have hArg : -rates i * s + -rates j * s =
            -(rates i + rates j) * s := by ring
        rw [hArg]
  -- Contract the actual output with b; the third overlap is derived here.
  have hOutput (x : Fin (n + 1) → ℝ) :
      (∑ v, b v * heatAction Q rates (t - s) x v) =
        ∑ k, a k * Real.exp (-rates k * (t - s)) *
          (∑ u, Q u k * x u) := by
    calc
      (∑ v, b v * heatAction Q rates (t - s) x v) =
          ∑ v, ∑ k, b v * (Q v k * Real.exp (-rates k * (t - s)) *
            (∑ u, Q u k * x u)) := by
        unfold heatAction
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
      _ = ∑ k, ∑ v, b v * (Q v k * Real.exp (-rates k * (t - s)) *
          (∑ u, Q u k * x u)) := by rw [Finset.sum_comm]
      _ = ∑ k, a k * Real.exp (-rates k * (t - s)) *
          (∑ u, Q u k * x u) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (∑ v, b v * (Q v k * Real.exp (-rates k * (t - s)) *
              (∑ u, Q u k * x u))) =
              (∑ v, b v * Q v k) * Real.exp (-rates k * (t - s)) *
                (∑ u, Q u k * x u) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro v hv
            ring
          _ = a k * Real.exp (-rates k * (t - s)) *
              (∑ u, Q u k * x u) := by
            change modalOverlap Q b k * Real.exp (-rates k * (t - s)) *
              (∑ u, Q u k * x u) = _
            rw [← hOverlap k]
  -- Project the square onto k, keeping the cubic as its actual vertex sum.
  have hProjection (k : Fin (n + 1)) :
      (∑ u, Q u k * (heatAction Q rates s b u) ^ 2) =
        ∑ i, ∑ j, (a i * a j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-(rates i + rates j) * s) := by
    simp_rw [hSquare]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ u, ∑ j, Q u k * ((a i * a j * Q u i * Q u j) *
          Real.exp (-(rates i + rates j) * s))) =
          ∑ i, ∑ j, ∑ u, Q u k * ((a i * a j * Q u i * Q u j) *
            Real.exp (-(rates i + rates j) * s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, (a i * a j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-(rates i + rates j) * s) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [C145PhysicalFrame.C, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        ring
  rw [hOutput]
  simp_rw [hProjection]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ k, ∑ j, a k * Real.exp (-rates k * (t - s)) *
        ((a i * a j * C145PhysicalFrame.C Q i j k) *
          Real.exp (-(rates i + rates j) * s))) =
        ∑ i, ∑ j, ∑ k, a k * Real.exp (-rates k * (t - s)) *
          ((a i * a j * C145PhysicalFrame.C Q i j k) *
            Real.exp (-(rates i + rates j) * s)) := by
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
      unfold C145PhysicalFrame.T
      ring

private theorem exp_mul_interval_integral (q t : ℝ) (hq : q ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (q * s)) = (Real.exp (q * t) - 1) / q := by
  have hSubstitution := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.exp) (a := (0 : ℝ)) (b := t) q
  simp only [mul_zero, _root_.integral_exp, Real.exp_zero] at hSubstitution
  apply (eq_div_iff hq).2
  simpa only [mul_comm] using hSubstitution

private theorem decayConvolution_ne (α γ t : ℝ) (hne : α ≠ γ) :
    decayConvolution α γ t =
      (Real.exp (-α * t) - Real.exp (-γ * t)) / (γ - α) := by
  have hq : α - γ ≠ 0 := sub_ne_zero.mpr hne
  have hFactor : decayConvolution α γ t = Real.exp (-α * t) *
      (∫ s in (0 : ℝ)..t, Real.exp ((α - γ) * s)) := by
    rw [decayConvolution, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [← Real.exp_add]
    congr 1
    ring
  have hProduct : Real.exp (-α * t) * Real.exp ((α - γ) * t) =
      Real.exp (-γ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hFactor, exp_mul_interval_integral (α - γ) t hq]
  calc
    Real.exp (-α * t) * ((Real.exp ((α - γ) * t) - 1) / (α - γ)) =
        (Real.exp (-α * t) * Real.exp ((α - γ) * t) -
          Real.exp (-α * t)) / (α - γ) := by ring
    _ = (Real.exp (-γ * t) - Real.exp (-α * t)) / (α - γ) := by rw [hProduct]
    _ = (Real.exp (-α * t) - Real.exp (-γ * t)) / (γ - α) := by
      have hNeg : γ - α = -(α - γ) := by ring
      rw [hNeg, div_neg]
      ring

private theorem decayConvolution_eq (α t : ℝ) :
    decayConvolution α α t = t * Real.exp (-α * t) := by
  calc
    decayConvolution α α t = ∫ _s in (0 : ℝ)..t, Real.exp (-α * t) := by
      unfold decayConvolution
      apply intervalIntegral.integral_congr
      intro s hs
      change Real.exp (-α * (t - s)) * Real.exp (-α * s) = Real.exp (-α * t)
      rw [← Real.exp_add]
      congr 1
      ring
    _ = t * Real.exp (-α * t) := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]

private theorem tendsto_scaled_exp (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => Real.exp (-δ * t)) atTop (𝓝 0) := by
  have hScale : Tendsto (fun t : ℝ => δ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hScale

private theorem tendsto_time_scaled_exp (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => t * Real.exp (-δ * t)) atTop (𝓝 0) := by
  have hScale : Tendsto (fun t : ℝ => δ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hBase : Tendsto (fun t : ℝ => (δ * t) * Real.exp (-(δ * t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hScale
  have hEq (t : ℝ) : ((δ * t) * Real.exp (-(δ * t))) / δ =
      t * Real.exp (-δ * t) := by
    have hArg : -(δ * t) = -δ * t := by ring
    rw [hArg]
    field_simp [ne_of_gt hδ]
  simpa only [zero_div] using (hBase.div_const δ).congr hEq

private theorem decayConvolution_ground_limit (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (decayConvolution 0 γ) atTop (𝓝 (1 / γ)) := by
  have hQuotient : Tendsto (fun t : ℝ => (1 - Real.exp (-γ * t)) / γ)
      atTop (𝓝 (1 / γ)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _t : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
        (tendsto_scaled_exp γ hγ)).div_const γ
  apply hQuotient.congr
  intro t
  rw [decayConvolution_ne 0 γ t (ne_of_lt hγ)]
  simp only [neg_zero, zero_mul, Real.exp_zero, sub_zero]

private theorem decayConvolution_positive_limit (α γ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) :
    Tendsto (decayConvolution α γ) atTop (𝓝 0) := by
  by_cases hEqual : α = γ
  · subst γ
    have hTime := tendsto_time_scaled_exp α hα
    exact hTime.congr (fun t => (decayConvolution_eq α t).symm)
  · have hQuotient := ((tendsto_scaled_exp α hα).sub
        (tendsto_scaled_exp γ hγ)).div_const (γ - α)
    have hZero : Tendsto
        (fun t : ℝ => (Real.exp (-α * t) - Real.exp (-γ * t)) / (γ - α))
        atTop (𝓝 0) := by
      simpa only [sub_self, zero_div] using hQuotient
    exact hZero.congr (fun t => (decayConvolution_ne α γ t hEqual).symm)

private theorem ground_output_slice {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hGround : ∀ v, Q v 0 = c) (i j : Fin (n + 1)) :
    C145PhysicalFrame.T Q a i j 0 =
      a 0 * c * a i ^ 2 * (if i = j then 1 else 0) := by
  have hSymmetry : C145PhysicalFrame.T Q a i j 0 =
      C145PhysicalFrame.T Q a 0 i j := by
    have hC : C145PhysicalFrame.C Q i j 0 = C145PhysicalFrame.C Q 0 i j := by
      unfold C145PhysicalFrame.C
      apply Finset.sum_congr rfl
      intro v hv
      ring
    unfold C145PhysicalFrame.T
    rw [hC]
    ring
  rw [hSymmetry]
  exact C145PhysicalFrame.ground_slice Q a c hQ hGround i j

private theorem rates_ge_ground {n : ℕ} (μ : ℝ)
    (rates : Fin (n + 1) → ℝ) (hGround : rates 0 = μ)
    (hAbove : ∀ i : Fin n, μ < rates i.succ) (i : Fin (n + 1)) :
    μ ≤ rates i := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · rw [h, hGround]
  · rw [h]
    exact le_of_lt (hAbove j)

private theorem groundFactor_reindex {m n : ℕ} (μ : ℝ)
    (rates0 a0 : Fin (m + 1) → ℝ)
    (rates1 a1 : Fin (n + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (heGround : e 0 = 0)
    (heRates : ∀ i, rates1 (e i) = rates0 i)
    (heOverlaps : ∀ i, a1 (e i) = a0 i) :
    groundFactor μ rates1 a1 = groundFactor μ rates0 a0 := by
  have hZero : a1 0 = a0 0 := by
    simpa only [heGround] using heOverlaps 0
  unfold groundFactor
  rw [hZero, ← e.sum_comp (fun j => a1 j ^ 2 / (2 * rates1 j - μ))]
  simp_rw [heRates, heOverlaps]

private theorem ground_overlap_mean {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (b a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hGround : ∀ v, Q v 0 = c)
    (hOverlap : ∀ i, a i = modalOverlap Q b i) :
    a 0 = c * (∑ v, b v) ∧
      a 0 * c = (∑ v, b v) / (n + 1 : ℝ) := by
  have hOverlapZero : a 0 = c * (∑ v, b v) := by
    rw [hOverlap 0, modalOverlap]
    simp only [hGround, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hN : (n + 1 : ℝ) ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hNormalization := C145PhysicalFrame.ground_normalization Q c hQ hGround
  refine ⟨hOverlapZero, ?_⟩
  apply (eq_div_iff hN).2
  rw [hOverlapZero]
  calc
    (c * ∑ v, b v) * c * (n + 1 : ℝ) =
        (∑ v, b v) * ((n + 1 : ℝ) * c ^ 2) := by ring
    _ = ∑ v, b v := by rw [hNormalization, mul_one]

/-- Actual vertex-space B equals the derived finite modal convolution sum. -/
theorem coincidentPulse_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b a : Fin (n + 1) → ℝ)
    (hOverlap : ∀ i, a i = modalOverlap Q b i) (t : ℝ) :
    coincidentPulse Q rates b t =
      ∑ i, ∑ j, ∑ k, C145PhysicalFrame.T Q a i j k *
        decayConvolution (rates k) (rates i + rates j) t := by
  classical
  let f := fun (i j k : Fin (n + 1)) (s : ℝ) =>
    C145PhysicalFrame.T Q a i j k * Real.exp (-rates k * (t - s)) *
      Real.exp (-(rates i + rates j) * s)
  have hContinuous (i j k : Fin (n + 1)) : Continuous (f i j k) := by
    dsimp only [f]
    fun_prop
  have hIntegrable (i j k : Fin (n + 1)) :
      IntervalIntegrable (f i j k) MeasureTheory.volume 0 t :=
    (hContinuous i j k).intervalIntegrable 0 t
  have hSumJ (i : Fin (n + 1)) :
      IntervalIntegrable (fun s => ∑ j, ∑ k, f i j k s)
        MeasureTheory.volume 0 t := by
    have h : Continuous (fun s => ∑ j, ∑ k, f i j k s) := by fun_prop
    exact h.intervalIntegrable 0 t
  have hSumK (i j : Fin (n + 1)) :
      IntervalIntegrable (fun s => ∑ k, f i j k s)
        MeasureTheory.volume 0 t := by
    have h : Continuous (fun s => ∑ k, f i j k s) := by fun_prop
    exact h.intervalIntegrable 0 t
  calc
    coincidentPulse Q rates b t = ∫ s in (0 : ℝ)..t, ∑ i, ∑ j, ∑ k, f i j k s := by
      unfold coincidentPulse
      apply intervalIntegral.integral_congr
      intro s hs
      exact pulse_integrand_expansion Q rates b a hOverlap t s
    _ = ∑ i, ∫ s in (0 : ℝ)..t, ∑ j, ∑ k, f i j k s :=
      intervalIntegral.integral_finsetSum (fun i hi => hSumJ i)
    _ = ∑ i, ∑ j, ∑ k, ∫ s in (0 : ℝ)..t, f i j k s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_finsetSum (fun j hj => hSumK i j)]
      apply Finset.sum_congr rfl
      intro j hj
      exact intervalIntegral.integral_finsetSum (fun k hk => hIntegrable i j k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [f, decayConvolution]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      ring

/-- Ground scaling is derived inside the actual finite integral, at every t. -/
theorem scaled_coincidentPulse_expansion {n : ℕ}
    (μ : ℝ) (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b a : Fin (n + 1) → ℝ)
    (hOverlap : ∀ i, a i = modalOverlap Q b i) (t : ℝ) :
    Real.exp (μ * t) * coincidentPulse Q rates b t =
      ∑ i, ∑ j, ∑ k, C145PhysicalFrame.T Q a i j k *
        decayConvolution (rates k - μ) (rates i + rates j - μ) t := by
  classical
  have hScale (α γ : ℝ) :
      Real.exp (μ * t) * decayConvolution α γ t =
        decayConvolution (α - μ) (γ - μ) t := by
    unfold decayConvolution
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [coincidentPulse_expansion Q rates b a hOverlap t]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  calc
    Real.exp (μ * t) * (C145PhysicalFrame.T Q a i j k *
        decayConvolution (rates k) (rates i + rates j) t) =
        C145PhysicalFrame.T Q a i j k *
          (Real.exp (μ * t) * decayConvolution (rates k) (rates i + rates j) t) := by ring
    _ = _ := by rw [hScale]

/-- The actual empty-interval coefficient vanishes without spectral premises. -/
theorem coincidentPulse_zero {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) : coincidentPulse Q rates b 0 = 0 := by
  unfold coincidentPulse
  exact intervalIntegral.integral_same

/-- The signed constant is the only sign in the derived large-time factor. -/
theorem signed_ground_limit {n : ℕ} (μ c : ℝ) (hμ : 0 < μ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b a : Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hGround : ∀ v, Q v 0 = c)
    (hRateGround : rates 0 = μ)
    (hAbove : ∀ i : Fin n, μ < rates i.succ)
    (hOverlap : ∀ i, a i = modalOverlap Q b i) :
    Tendsto (fun t : ℝ => Real.exp (μ * t) * coincidentPulse Q rates b t)
      atTop (𝓝 (c * groundFactor μ rates a)) := by
  classical
  have hGamma (i j : Fin (n + 1)) : 0 < rates i + rates j - μ := by
    have hi := rates_ge_ground μ rates hRateGround hAbove i
    have hj := rates_ge_ground μ rates hRateGround hAbove j
    linarith
  let L := fun (i j k : Fin (n + 1)) =>
    if k = 0 then C145PhysicalFrame.T Q a i j 0 / (rates i + rates j - μ) else 0
  have hTerm (i j k : Fin (n + 1)) :
      Tendsto (fun t : ℝ => C145PhysicalFrame.T Q a i j k *
        decayConvolution (rates k - μ) (rates i + rates j - μ) t)
        atTop (𝓝 (L i j k)) := by
    by_cases hk : k = 0
    · subst k
      have h := (decayConvolution_ground_limit (rates i + rates j - μ)
        (hGamma i j)).const_mul (C145PhysicalFrame.T Q a i j 0)
      simpa only [hRateGround, sub_self, L, ite_eq_left rfl, div_eq_mul_inv, one_mul] using h
    · have hAlpha : 0 < rates k - μ := by
        rcases Fin.eq_zero_or_eq_succ k with hZero | ⟨r, hr⟩
        · exact False.elim (hk hZero)
        · rw [hr]
          linarith [hAbove r]
      -- This helper handles alpha = gamma with t * exp(-alpha*t).
      have h := (decayConvolution_positive_limit (rates k - μ)
        (rates i + rates j - μ) hAlpha (hGamma i j)).const_mul
          (C145PhysicalFrame.T Q a i j k)
      simpa only [L, ite_eq_right hk, mul_zero] using h
  have hFinite : Tendsto (fun t : ℝ => ∑ i, ∑ j, ∑ k,
      C145PhysicalFrame.T Q a i j k *
        decayConvolution (rates k - μ) (rates i + rates j - μ) t)
      atTop (𝓝 (∑ i, ∑ j, ∑ k, L i j k)) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro k hk
    exact hTerm i j k
  have hK (i j : Fin (n + 1)) :
      (∑ k, L i j k) = C145PhysicalFrame.T Q a i j 0 /
        (rates i + rates j - μ) := by
    rw [Fin.sum_univ_succ]
    simp only [L, ite_eq_left rfl, Fin.succ_ne_zero, ite_false,
      Finset.sum_const_zero, add_zero]
  have hJ (i : Fin (n + 1)) :
      (∑ j, C145PhysicalFrame.T Q a i j 0 / (rates i + rates j - μ)) =
        a 0 * c * a i ^ 2 / (2 * rates i - μ) := by
    have hSummand (j : Fin (n + 1)) :
        C145PhysicalFrame.T Q a i j 0 / (rates i + rates j - μ) =
          if i = j then a 0 * c * a i ^ 2 / (2 * rates i - μ) else 0 := by
      rw [ground_output_slice Q a c hQ hGround i j]
      by_cases hij : i = j
      · subst j
        have hDenominator : rates i + rates i - μ = 2 * rates i - μ := by ring
        simp only [ite_true, mul_one, hDenominator]
      · simp only [ite_eq_right hij, mul_zero, zero_div]
    simp_rw [hSummand]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hMean := ground_overlap_mean Q b a c hQ hGround hOverlap
  have hCollapse : (∑ i, ∑ j, ∑ k, L i j k) = c * groundFactor μ rates a := by
    simp_rw [hK, hJ]
    calc
      (∑ i, a 0 * c * a i ^ 2 / (2 * rates i - μ)) =
          (a 0 * c) * (∑ i, a i ^ 2 / (2 * rates i - μ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ((∑ v, b v) / (n + 1 : ℝ)) *
          (∑ i, a i ^ 2 / (2 * rates i - μ)) := by rw [hMean.2]
      _ = c * groundFactor μ rates a := by
        rw [← hMean.2]
        unfold groundFactor
        ring
  rw [hCollapse] at hFinite
  exact hFinite.congr (fun t =>
    (scaled_coincidentPulse_expansion μ Q rates b a hOverlap t).symm)

/-- Every denominator is positive before the positive factor is used to cancel. -/
theorem groundFactor_pos {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (rates a : Fin (n + 1) → ℝ)
    (hRateGround : rates 0 = μ)
    (hAbove : ∀ i : Fin n, μ < rates i.succ)
    (ha : ∀ i, 0 < a i) : 0 < groundFactor μ rates a := by
  have hDenominator (i : Fin (n + 1)) : 0 < 2 * rates i - μ := by
    have hi := rates_ge_ground μ rates hRateGround hAbove i
    linarith
  have hSummand (i : Fin (n + 1)) : 0 < a i ^ 2 / (2 * rates i - μ) :=
    div_pos (sq_pos_of_ne_zero (ne_of_gt (ha i))) (hDenominator i)
  have hSum : 0 < ∑ i, a i ^ 2 / (2 * rates i - μ) := by
    apply Finset.sum_pos (fun i hi => hSummand i)
    exact ⟨0, Finset.mem_univ 0⟩
  exact mul_pos (ha 0) hSum

/-- Literal H1 and actual nonnegative-time B data force common signed c and mean.
No matching arrays, size equality, modal equivalence or asymptotic amplitude is
supplied. Each frame and vertex port remains in its own original space. -/
theorem actual_signed_ground_calibration {m n : ℕ}
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 a0 : Fin (m + 1) → ℝ)
    (rates1 b1 a1 : Fin (n + 1) → ℝ)
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
    (ha0 : ∀ i, 0 < a0 i)
    (ha1 : ∀ j, 0 < a1 j)
    (hOverlap0 : ∀ i, a0 i = modalOverlap Q0 b0 i)
    (hOverlap1 : ∀ j, a1 j = modalOverlap Q1 b1 j)
    (hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer rates0 a0 s = C145.H1.firstTransfer rates1 a1 s)
    (hB : ∀ t : ℝ, 0 ≤ t →
      coincidentPulse Q0 rates0 b0 t = coincidentPulse Q1 rates1 b1 t) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, a1 (e i) = a0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ v, b1 v) := by
  obtain ⟨e, hSize, heGround, heRates, heOverlaps⟩ :=
    C145.H1.known_ground_positive_modal_identification μ hμ rates0 a0 rates1 a1
      hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1 hH1
  have hFactor : groundFactor μ rates1 a1 = groundFactor μ rates0 a0 :=
    groundFactor_reindex μ rates0 a0 rates1 a1 e heGround heRates heOverlaps
  have hLimit0 := signed_ground_limit μ c0 hμ Q0 rates0 b0 a0
    hQ0 hGround0 hRateGround0 hAbove0 hOverlap0
  have hLimit1 := signed_ground_limit μ c1 hμ Q1 rates1 b1 a1
    hQ1 hGround1 hRateGround1 hAbove1 hOverlap1
  have hEventual :
      (fun t : ℝ => Real.exp (μ * t) * coincidentPulse Q0 rates0 b0 t) =ᶠ[atTop]
        (fun t : ℝ => Real.exp (μ * t) * coincidentPulse Q1 rates1 b1 t) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hB t ht]
  have hLimits : c0 * groundFactor μ rates0 a0 = c1 * groundFactor μ rates1 a1 :=
    tendsto_nhds_unique_of_eventuallyEq hLimit0 hLimit1 hEventual
  have hPositive : 0 < groundFactor μ rates0 a0 :=
    groundFactor_pos μ hμ rates0 a0 hRateGround0 hAbove0 ha0
  have hConstant : c0 = c1 := by
    apply mul_right_cancel₀ (ne_of_gt hPositive)
    calc
      c0 * groundFactor μ rates0 a0 = c1 * groundFactor μ rates1 a1 := hLimits
      _ = c1 * groundFactor μ rates0 a0 := by rw [hFactor]
  have hOverlapGround : a1 0 = a0 0 := by
    simpa only [heGround] using heOverlaps 0
  have hMean0 := ground_overlap_mean Q0 b0 a0 c0 hQ0 hGround0 hOverlap0
  have hMean1 := ground_overlap_mean Q1 b1 a1 c1 hQ1 hGround1 hOverlap1
  have hMeans : (∑ v, b0 v) = (∑ v, b1 v) := by
    apply mul_left_cancel₀ (C145PhysicalFrame.ground_ne_zero Q0 c0 hQ0 hGround0)
    calc
      c0 * (∑ v, b0 v) = a0 0 := hMean0.1.symm
      _ = a1 0 := hOverlapGround.symm
      _ = c1 * (∑ v, b1 v) := hMean1.1
      _ = c0 * (∑ v, b1 v) := by rw [hConstant]
  exact ⟨e, hSize, heGround, heRates, heOverlaps, hConstant, hMeans⟩


end C145.Pulse
end

end
