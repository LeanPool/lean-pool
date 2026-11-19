/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryCameronMartin.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinEnergy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Sharp Cameron–Martin response of the actual dissipative drift

This is a comparison theorem for actual driven trajectories. Its curvature
input is strong convexity of the literal potential, not an assumed bound on
an unspecified flow derivative.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Exact finite-time unit-noise covariance. -/
def bakryEmeryResponseCovariance (κ t : ℝ) : ℝ :=
  (1 - Real.exp (-2 * κ * t)) / (2 * κ)

private def responseRegularized (κ ε t : ℝ) : ℝ :=
  bakryEmeryResponseCovariance κ t + ε * Real.exp (-2 * κ * t)

private theorem responseRegularized_pos {κ ε t : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (ht : 0 ≤ t) :
    0 < responseRegularized κ ε t := by
  have he : Real.exp (-2 * κ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hq : 0 ≤ bakryEmeryResponseCovariance κ t :=
    div_nonneg (sub_nonneg.mpr he) (by positivity)
  exact add_pos_of_nonneg_of_pos hq (mul_pos hε (Real.exp_pos _))

private theorem responseRegularized_hasDerivAt (κ ε t : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (responseRegularized κ ε)
      (Real.exp (-2 * κ * t) - 2 * κ * ε * Real.exp (-2 * κ * t)) t := by
  have he := ((hasDerivAt_id t).const_mul (-2 * κ)).exp
  have hd := ((hasDerivAt_const t 1).sub he).div_const (2 * κ)
  have h := hd.add (he.const_mul ε)
  convert h using 1
  · funext s
    rfl
  · simp only [id_eq]
    field_simp
    ring

private theorem responseRegularized_ode (κ ε t : ℝ) (hκ : κ ≠ 0) :
    (Real.exp (-2 * κ * t) - 2 * κ * ε * Real.exp (-2 * κ * t)) +
      2 * κ * responseRegularized κ ε t = 1 := by
  unfold responseRegularized bakryEmeryResponseCovariance
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- The sharp finite-time response bound, proved on the actual controlled
state-difference equation `U' = -∇W(X)+∇W(Y)+u` with `X-Y=U`.
The coefficient tends to `1/(2κ)` at equilibrium. -/
theorem bakryEmeryLangevin_cameronMartin_response
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (X Y U u : ℝ → E) (hu : Continuous u) (T : ℝ) (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hU0 : U 0 = 0)
    (hXY : ∀ s ∈ Ioo 0 T, X s - Y s = U s)
    (hEq : ∀ s ∈ Ioo 0 T, HasDerivAt U
      (bakryEmeryLangevinDrift W (X s) - bakryEmeryLangevinDrift W (Y s) + u s) s) :
    ‖U T‖ ^ 2 ≤ bakryEmeryResponseCovariance κ T * ∫ s in 0..T, ‖u s‖ ^ 2 := by
  have hi : Continuous (fun s => ‖u s‖ ^ 2) := hu.norm.pow 2
  let J : ℝ → ℝ := fun t => ∫ s in 0..t, ‖u s‖ ^ 2
  have hJ (t : ℝ) : HasDerivAt J (‖u t‖ ^ 2) t :=
    (hi.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hJc : Continuous J := continuous_iff_continuousAt.mpr
    (fun t => (hJ t).continuousAt)
  have hb (ε : ℝ) (hε : 0 < ε) :
      ‖U T‖ ^ 2 ≤ responseRegularized κ ε T * J T := by
    let q := responseRegularized κ ε
    let D : ℝ → ℝ := fun t => ‖U t‖ ^ 2 / q t - J t
    have hqc : Continuous q := by
      unfold q responseRegularized bakryEmeryResponseCovariance
      fun_prop
    have hdc : ContinuousOn D (Icc 0 T) :=
      ((hU.norm.pow 2).div hqc.continuousOn (fun t ht =>
        ne_of_gt (responseRegularized_pos hκ hε ht.1))).sub hJc.continuousOn
    have hd (s : ℝ) (hs : s ∈ Ioo 0 T) :
        HasDerivAt D
          ((2 * inner ℝ (U s)
            (bakryEmeryLangevinDrift W (X s) - bakryEmeryLangevinDrift W (Y s) + u s) * q s -
            ‖U s‖ ^ 2 * (Real.exp (-2 * κ * s) - 2 * κ * ε * Real.exp (-2 * κ * s))) /
              q s ^ 2 - ‖u s‖ ^ 2) s :=
      (((hEq s hs).norm_sq).div (responseRegularized_hasDerivAt κ ε s hκ.ne')
        (ne_of_gt (responseRegularized_pos hκ hε hs.1.le))).sub (hJ s)
    have hdn (s : ℝ) (hs : s ∈ Ioo 0 T) : deriv D s ≤ 0 := by
      rw [(hd s hs).deriv]
      have hq : 0 < q s := responseRegularized_pos hκ hε hs.1.le
      have hdis := bakryEmeryLangevinDrift_dissipative W κ hc (X s) (Y s)
        (hW _) (hW _)
      rw [hXY s hs] at hdis
      have hyoung : 2 * q s * inner ℝ (U s) (u s) ≤
          ‖U s‖ ^ 2 + q s ^ 2 * ‖u s‖ ^ 2 := by
        have hn := (real_inner_self_nonneg (x := U s - q s • u s))
        simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
          real_inner_self_eq_norm_sq, conj_trivial] at hn
        rw [real_inner_comm (U s) (u s)] at hn
        nlinarith
      have hode := responseRegularized_ode κ ε s hκ.ne'
      change (Real.exp (-2 * κ * s) - 2 * κ * ε * Real.exp (-2 * κ * s)) +
        2 * κ * q s = 1 at hode
      rw [sub_nonpos, div_le_iff₀ (sq_pos_of_pos hq)]
      simp only [inner_add_right]
      nlinarith [mul_le_mul_of_nonneg_right hdis hq.le]
    have hanti : AntitoneOn D (Icc 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hdc
      · intro s hs
        exact (hd s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        exact hdn s (by simpa only [interior_Icc] using hs)
    have hh := hanti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    have hzero : D 0 = 0 := by simp [D, hU0, J]
    rw [hzero] at hh
    have hratio : ‖U T‖ ^ 2 / q T ≤ J T := sub_nonpos.mp hh
    exact (div_le_iff₀ (responseRegularized_pos hκ hε hT)).mp hratio |>.trans_eq (mul_comm _ _)
  have htend : Tendsto (fun ε => responseRegularized κ ε T * J T) (nhdsWithin 0 (Ioi 0))
      (𝓝 (bakryEmeryResponseCovariance κ T * J T)) := by
    have hc' : Continuous (fun ε => responseRegularized κ ε T * J T) := by
      unfold responseRegularized
      fun_prop
    simpa only [responseRegularized, zero_mul, add_zero] using (hc'.continuousAt (x :=
        0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hb ε hε)

omit [FiniteDimensional ℝ E] in
/-- The sharp response for two actual continuous-noise Langevin
trajectories whose driving paths differ by an integrated continuous control.
No spatial derivative or response bound of the flow is assumed. -/
theorem bakryEmeryLangevin_driven_cameronMartin_response
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N Y₀ Y₁ u : ℝ → E) (hu : Continuous u) (T : ℝ) (hT : 0 ≤ T)
    (hY₀ : ContinuousOn Y₀ (Icc 0 T)) (hY₁ : ContinuousOn Y₁ (Icc 0 T))
    (hYinit : Y₁ 0 = Y₀ 0)
    (hEq₀ : ∀ s ∈ Ioo 0 T, HasDerivAt Y₀
      (bakryEmeryLangevinDrift W (Y₀ s + N s)) s)
    (hEq₁ : ∀ s ∈ Ioo 0 T, HasDerivAt Y₁
      (bakryEmeryLangevinDrift W (Y₁ s + N s + ∫ r in 0..s, u r)) s) :
    ‖(Y₁ T + N T + ∫ r in 0..T, u r) - (Y₀ T + N T)‖ ^ 2 ≤
      bakryEmeryResponseCovariance κ T * ∫ s in 0..T, ‖u s‖ ^ 2 := by
  let H : ℝ → E := fun t => ∫ r in 0..t, u r
  have hH (t : ℝ) : HasDerivAt H (u t) t :=
    (hu.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr
    (fun t => (hH t).continuousAt)
  let U : ℝ → E := fun t => Y₁ t - Y₀ t + H t
  have hU : ContinuousOn U (Icc 0 T) := (hY₁.sub hY₀).add hHc.continuousOn
  have hU0 : U 0 = 0 := by simp [U, H, hYinit]
  have hXY (s : ℝ) : (Y₁ s + N s + H s) - (Y₀ s + N s) = U s := by
    dsimp [U]
    abel
  have h := bakryEmeryLangevin_cameronMartin_response W κ hκ hW hc
    (fun s => Y₁ s + N s + H s) (fun s => Y₀ s + N s) U u hu T hT hU hU0
    (fun s _ => hXY s) (fun s hs => ((hEq₁ s hs).sub (hEq₀ s hs)).add (hH s))
  rw [← hXY T] at h
  exact h

end
end GinibrePoincare
