/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.ParameterIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
The multivariable Cauchy integral formula on polydiscs, proved by coordinate induction.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Complex
open scoped Topology
namespace KamProject.Arnold1963

/-- The product Cauchy kernel for integration on a polydisc boundary. -/
def cauchyKernel {n : ℕ} (w z : ComplexSpace n) : ℂ := ∏ i, (z i - w i)⁻¹

theorem continuous_torusMap {n : ℕ} (c : ComplexSpace n) (r : RealSpace n) :
    Continuous (torusMap c r) := by
  unfold torusMap
  fun_prop

theorem torusMap_mem_pi_closedBall {n : ℕ} (c : ComplexSpace n) {r : RealSpace n}
    (hr : ∀ i, 0 ≤ r i) (t : RealSpace n) :
    torusMap c r t ∈ pi univ (fun i => closedBall (c i) (r i)) := by
  intro i _
  simp [mem_closedBall, dist_eq_norm, torusMap, abs_of_nonneg (hr i)]

theorem torusMap_sub_ne_zero {n : ℕ} {c w : ComplexSpace n} {r : RealSpace n}
    (hw : ∀ i, w i ∈ ball (c i) (r i)) (t : RealSpace n) (i : Fin n) :
    torusMap c r t i - w i ≠ 0 := by
  intro he
  have hh := hw i
  rw [← sub_eq_zero.mp he] at hh
  have hr : 0 ≤ r i := (dist_nonneg.trans (mem_ball.mp hh).le)
  simp [mem_ball, dist_eq_norm, torusMap, abs_of_nonneg hr] at hh

theorem continuous_cauchy_boundary {n : ℕ} {f : ComplexSpace n → ℂ}
    {c w : ComplexSpace n} {r : RealSpace n} (hr : ∀ i, 0 ≤ r i)
    (hf : ContinuousOn f (pi univ (fun i => closedBall (c i) (r i))))
    (hw : ∀ i, w i ∈ ball (c i) (r i)) :
    Continuous (fun t => cauchyKernel w (torusMap c r t) * f (torusMap c r t)) := by
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact (((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const).inv₀
      (fun t => torusMap_sub_ne_zero hw t i)
  · exact hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_pi_closedBall c hr)

theorem polydisc_cauchy {n : ℕ} {f : ComplexSpace n → ℂ}
    {c w : ComplexSpace n} {r : RealSpace n} (hr : ∀ i, 0 < r i)
    (hf : AnalyticOnNhd ℂ f (pi univ (fun i => closedBall (c i) (r i))))
    (hw : ∀ i, w i ∈ ball (c i) (r i)) :
    torusIntegral (fun z => cauchyKernel w z * f z) c r =
      (2 * Real.pi * I : ℂ) ^ n * f w := by
  induction n with
  | zero => simp [cauchyKernel, torusIntegral_dim0, Subsingleton.elim c w]
  | succ n ih =>
    have hi : TorusIntegrable (fun z => cauchyKernel w z * f z) c r :=
      (continuous_cauchy_boundary (fun i => (hr i).le)
        hf.continuousOn hw).continuousOn.integrableOn_compact
        isCompact_Icc
    rw [torusIntegral_succ hi]
    have he (z : ℂ) (hz : z ∈ sphere (c 0) (r 0)) :
        torusIntegral (fun y => cauchyKernel w (Fin.cons z y) * f (Fin.cons z y))
          (c ∘ Fin.succ) (r ∘ Fin.succ) =
        (z - w 0)⁻¹ * ((2 * Real.pi * I : ℂ) ^ n * f (Fin.cons z (w ∘ Fin.succ))) := by
      have hslice : AnalyticOnNhd ℂ (fun y : ComplexSpace n => f (Fin.cons z y))
          (pi univ (fun i => closedBall (c i.succ) (r i.succ))) := by
        intro y hy
        have ha : AnalyticAt ℂ
            (fun y : ComplexSpace n => (Fin.cons z y : ComplexSpace (n+1))) y := by
          apply AnalyticAt.pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact analyticAt_const
          · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt y
        have hm : Fin.cons z y ∈ pi univ (fun i => closedBall (c i) (r i)) := by
          intro i _
          refine Fin.cases ?_ (fun j => ?_) i
          · exact sphere_subset_closedBall hz
          · exact hy j (mem_univ j)
        exact (hf _ hm).comp (f := fun y : ComplexSpace n => (Fin.cons z y : ComplexSpace (n+1))) ha
      have hk : (fun y : ComplexSpace n => cauchyKernel w (Fin.cons z y) * f (Fin.cons z y)) =
          fun y => (z - w 0)⁻¹ * (cauchyKernel (w ∘ Fin.succ) y * f (Fin.cons z y)) := by
        funext y
        simp [cauchyKernel, Fin.prod_univ_succ, mul_assoc, mul_comm]
      rw [hk, torusIntegral_const_mul]
      exact congrArg (fun a : ℂ => (z - w 0)⁻¹ * a)
        (ih (c := c ∘ Fin.succ) (w := w ∘ Fin.succ) (r := r ∘ Fin.succ)
          (fun i => hr i.succ) hslice (fun i => hw i.succ))
    rw [circleIntegral.integral_congr (hr 0).le he]
    have hd : DifferentiableOn ℂ (fun z => f (Fin.cons z (w ∘ Fin.succ)))
        (closedBall (c 0) (r 0)) := by
      intro z hz
      have hm : Fin.cons z (w ∘ Fin.succ) ∈ pi univ (fun i => closedBall (c i) (r i)) := by
        intro i _
        refine Fin.cases hz (fun j => ball_subset_closedBall (hw j.succ)) i
      have ha : AnalyticAt ℂ (fun z : ℂ => (Fin.cons z (w ∘ Fin.succ) : ComplexSpace (n+1))) z := by
        apply AnalyticAt.pi
        intro i
        exact Fin.cases analyticAt_id (fun _ => analyticAt_const) i
      have hh := (hf _ hm).comp
        (f := fun z : ℂ => (Fin.cons z (w ∘ Fin.succ) : ComplexSpace (n+1))) ha
      exact hh.differentiableAt.differentiableWithinAt
    have hc := hd.circleIntegral_sub_inv_smul (hw 0)
    have hex : (fun z : ℂ => (z - w 0)⁻¹ * ((2 * Real.pi * I : ℂ) ^ n *
        f (Fin.cons z (w ∘ Fin.succ)))) =
        fun z => (2 * Real.pi * I : ℂ) ^ n *
          ((z - w 0)⁻¹ * f (Fin.cons z (w ∘ Fin.succ))) := by funext z; ring
    rw [hex, circleIntegral.integral_const_mul]
    have hwcons : Fin.cons (w 0) (w ∘ Fin.succ) = w := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    simpa [smul_eq_mul, ← mul_assoc, pow_succ, hwcons] using congrArg
      (fun a : ℂ => (2 * Real.pi * I : ℂ) ^ n * a) hc

end KamProject.Arnold1963
