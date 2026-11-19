/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/LebesgueL2Mollification.lean.
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

public import LeanPool.GinibrePoincare.Concrete.Configuration
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Strong L² convergence of kernel averages of translations

For a continuous compactly supported scalar kernel `K`, the average `∫ y, K y • τ_y u` of the
translates of a Lebesgue L² class `u` is an actual Bochner integral in L². For nonnegative
kernels of mass one it is a contraction, and strong continuity of translation gives
convergence as the kernel support shrinks to the origin. Normalized smooth bumps are the
special case `K = φ.normed volume`. Identification with pointwise convolution is a separate
step.

The API is stated once for a normed group `E` whose `volume` is an additive Haar measure
(`l2Translate`, `l2KernelAverage`, `l2BumpAverage`); the configuration-space names
(`lebesgueL2Translate`, `lebesgueL2KernelAverage`, `lebesgueL2BumpAverage`) are its
specializations to `E = Configuration n`.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-! ### Translation and kernel averages on a general Haar space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- Translation `x ↦ u (x - y)` of a Lebesgue L² class, as the domain action of `-y`. -/
def l2Translate (y : E) (u : Lp V 2 (volume : Measure E)) : Lp V 2 (volume : Measure E) :=
  DomAddAct.mk (-y) +ᵥ u

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem l2Translate_zero (u : Lp V 2 (volume : Measure E)) : l2Translate 0 u = u := by
  simp [l2Translate]

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem norm_l2Translate (y : E) (u : Lp V 2 (volume : Measure E)) :
    ‖l2Translate y u‖ = ‖u‖ :=
  DomAddAct.norm_vadd_Lp _ _

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem l2Translate_ae (y : E) (u : Lp V 2 (volume : Measure E)) :
    (l2Translate y u : E → V) =ᵐ[volume] fun x => u (x - y) := by
  have he := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) u
  filter_upwards [he] with x hx
  simpa only [l2Translate, Equiv.symm_apply_apply, vadd_eq_add, sub_eq_add_neg,
    add_comm] using hx

/-- Bochner average `∫ y, K y • τ_y u` of the translates of a Lebesgue L² class against a
scalar kernel `K`. -/
def l2KernelAverage (K : E → ℝ) (u : Lp V 2 (volume : Measure E)) :
    Lp V 2 (volume : Measure E) :=
  ∫ y, K y • l2Translate y u

omit [CompleteSpace V] in
/-- A nonnegative kernel of mass one averages to a contraction of Lebesgue L². -/
theorem norm_l2KernelAverage_le {K : E → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hpos : ∀ y, 0 ≤ K y)
    (hmass : ∫ y, K y = 1) (u : Lp V 2 (volume : Measure E)) :
    ‖l2KernelAverage K u‖ ≤ ‖u‖ := by
  have ht : ‖l2KernelAverage K u‖ ≤ ∫ y, K y * ‖u‖ := by
    apply norm_integral_le_of_norm_le
      ((hK.integrable_of_hasCompactSupport hKc).mul_const ‖u‖)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, norm_l2Translate, Real.norm_eq_abs, abs_of_nonneg (hpos y)])
  simpa only [integral_mul_const, hmass, one_mul] using ht

variable [LocallyCompactSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem continuous_l2Translate (u : Lp V 2 (volume : Measure E)) :
    Continuous (fun y => l2Translate y u) :=
  (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

omit [CompleteSpace V] in
theorem integrable_l2KernelIntegrand {K : E → ℝ} (hK : Continuous K)
    (hKc : HasCompactSupport K) (u : Lp V 2 (volume : Measure E)) :
    Integrable (fun y => K y • l2Translate y u) :=
  (hK.smul (continuous_l2Translate u)).integrable_of_hasCompactSupport hKc.smul_right

/-- Continuous linear test pairings commute with the kernel average. -/
theorem l2KernelAverage_pairing {K : E → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (u : Lp V 2 (volume : Measure E)) (L : Lp V 2 (volume : Measure E) →L[ℝ] ℝ) :
    L (l2KernelAverage K u) = ∫ y, K y * L (l2Translate y u) := by
  unfold l2KernelAverage
  rw [← L.integral_comp_comm (integrable_l2KernelIntegrand hK hKc u)]
  simp only [map_smul, smul_eq_mul]

/-- The kernel average has the expected translated representative pairing against every
scalar L² test. -/
theorem l2KernelAverage_test_pairing {K : E → ℝ} (hK : Continuous K)
    (hKc : HasCompactSupport K) (u : Lp ℝ 2 (volume : Measure E))
    (w : E → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, l2KernelAverage K u x * w x) = ∫ y, K y * (∫ x, u (x - y) * w x) := by
  let L : Lp ℝ 2 (volume : Measure E) →L[ℝ] ℝ := innerSL ℝ (hw.toLp w)
  have hL (v : Lp ℝ 2 (volume : Measure E)) : L v = ∫ x, v x * w x := by
    change inner ℝ (hw.toLp w) v = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [← hL, l2KernelAverage_pairing hK hKc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [hL]
  congr 1
  apply integral_congr_ae
  filter_upwards [l2Translate_ae y u] with x hx
  rw [hx]

/-- For a nonnegative kernel of mass one, a translation error bound on the support of the
kernel controls the averaged L² error. -/
theorem l2KernelAverage_error_le {K : E → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hpos : ∀ y, 0 ≤ K y)
    (hmass : ∫ y, K y = 1) (u : Lp V 2 (volume : Measure E)) (ε : ℝ)
    (he : ∀ y ∈ Function.support K, ‖l2Translate y u - u‖ ≤ ε) :
    ‖l2KernelAverage K u - u‖ ≤ ε := by
  have hKi : Integrable K volume := hK.integrable_of_hasCompactSupport hKc
  have hconst : Integrable (fun y => K y • u) := hKi.smul_const u
  have hint := integrable_l2KernelIntegrand hK hKc u
  have heq : l2KernelAverage K u - u = ∫ y, K y • (l2Translate y u - u) := by
    unfold l2KernelAverage
    calc
      _ = (∫ y, K y • l2Translate y u) - ∫ y, K y • u := by
        rw [integral_smul_const, hmass, one_smul]
      _ = ∫ y, (K y • l2Translate y u - K y • u) := (integral_sub hint hconst).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => (smul_sub _ _ _).symm)
  rw [heq]
  have hnorm : ‖∫ y, K y • (l2Translate y u - u)‖ ≤ ∫ y, K y * ε := by
    apply norm_integral_le_of_norm_le (hKi.mul_const ε)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hpos y)]
      by_cases hy : K y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (he y hy) (hpos y))
  simpa only [integral_mul_const, hmass, one_mul] using hnorm

/-- Averages against nonnegative mass-one kernels whose supports shrink to the origin
converge strongly in Lebesgue L². -/
theorem l2KernelAverage_tendsto (K : ℕ → E → ℝ)
    (hK : ∀ m, Continuous (K m)) (hKc : ∀ m, HasCompactSupport (K m))
    (hpos : ∀ m y, 0 ≤ K m y) (hmass : ∀ m, ∫ y, K m y = 1)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ m, ∀ y ∈ Function.support (K m), ‖y‖ ≤ r m)
    (u : Lp V 2 (volume : Measure E)) :
    Tendsto (fun m => l2KernelAverage (K m) u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp
    (continuous_l2Translate u).continuousAt (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hr).2 δ hδ)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm]
  apply (l2KernelAverage_error_le (hK m) (hKc m) (hpos m) (hmass m) u (ε / 2)
    ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hd : dist y 0 < δ := by
    rw [dist_zero_right]
    exact (hsupp m y hy).trans_lt (hM m hm)
  simpa only [l2Translate_zero, dist_eq_norm] using (ht hd).le

end General

/-! ### Normalized smooth bumps on a general finite-dimensional space -/

section GeneralBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Bochner average of translated Lebesgue L² classes against a normalized smooth bump. -/
def l2BumpAverage (φ : ContDiffBump (0 : E)) (u : Lp V 2 (volume : Measure E)) :
    Lp V 2 (volume : Measure E) :=
  l2KernelAverage (φ.normed volume) u

omit [CompleteSpace V] in
theorem integrable_l2BumpIntegrand (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure E)) :
    Integrable (fun y => φ.normed volume y • l2Translate y u) :=
  integrable_l2KernelIntegrand φ.continuous_normed φ.hasCompactSupport_normed u

omit [CompleteSpace V] in
/-- A normalized bump average is a contraction on the actual Lebesgue L² space. -/
theorem norm_l2BumpAverage_le (φ : ContDiffBump (0 : E)) (u : Lp V 2 (volume : Measure E)) :
    ‖l2BumpAverage φ u‖ ≤ ‖u‖ :=
  norm_l2KernelAverage_le φ.continuous_normed φ.hasCompactSupport_normed
    φ.nonneg_normed φ.integral_normed u

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem l2BumpAverage_pairing (φ : ContDiffBump (0 : E)) (u : Lp V 2 (volume : Measure E))
    (L : Lp V 2 (volume : Measure E) →L[ℝ] ℝ) :
    L (l2BumpAverage φ u) = ∫ y, φ.normed volume y * L (l2Translate y u) :=
  l2KernelAverage_pairing φ.continuous_normed φ.hasCompactSupport_normed u L

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem l2BumpAverage_test_pairing (φ : ContDiffBump (0 : E))
    (u : Lp ℝ 2 (volume : Measure E)) (w : E → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, l2BumpAverage φ u x * w x) = ∫ y, φ.normed volume y * (∫ x, u (x - y) * w x) :=
  l2KernelAverage_test_pairing φ.continuous_normed φ.hasCompactSupport_normed u w hw

/-- A local translation error bound controls the actual averaged L² error. -/
theorem l2BumpAverage_error_le (φ : ContDiffBump (0 : E)) (u : Lp V 2 (volume : Measure E))
    (ε : ℝ) (he : ∀ y ∈ Function.support (φ.normed volume), ‖l2Translate y u - u‖ ≤ ε) :
    ‖l2BumpAverage φ u - u‖ ≤ ε :=
  l2KernelAverage_error_le φ.continuous_normed φ.hasCompactSupport_normed
    φ.nonneg_normed φ.integral_normed u ε he

/-- Normalized bump averages converge strongly in actual Lebesgue L². -/
theorem l2BumpAverage_tendsto (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) (u : Lp V 2 (volume : Measure E)) :
    Tendsto (fun m => l2BumpAverage (φ m) u) atTop (𝓝 u) :=
  l2KernelAverage_tendsto (fun m => (φ m).normed volume)
    (fun m => (φ m).continuous_normed) (fun m => (φ m).hasCompactSupport_normed)
    (fun m => (φ m).nonneg_normed) (fun m => (φ m).integral_normed) _ hφ
    (fun m y hy => by
      rw [(φ m).support_normed_eq] at hy
      exact (mem_ball_zero_iff.mp hy).le) u

end GeneralBump

/-! ### The configuration space -/

/-- Translation action on Lebesgue L², parameterized for convolution by a bump kernel. -/
def lebesgueL2Translate (n : ℕ) (y : Configuration n)
    (u : Lp V 2 (volume : Measure (Configuration n))) : Lp V 2 (volume : Measure (Configuration
      n)) :=
  l2Translate y u

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem continuous_lebesgueL2Translate (n : ℕ) (u : Lp V 2 (volume : Measure (Configuration n))) :
    Continuous (fun y => lebesgueL2Translate n y u) :=
  continuous_l2Translate u

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem lebesgueL2Translate_zero (n : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) : lebesgueL2Translate n 0 u = u :=
  l2Translate_zero u

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem norm_lebesgueL2Translate (n : ℕ) (y : Configuration n)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    ‖lebesgueL2Translate n y u‖ = ‖u‖ :=
  norm_l2Translate y u

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem lebesgueL2Translate_ae (n : ℕ) (y : Configuration n)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    (lebesgueL2Translate n y u : Configuration n → V) =ᵐ[volume] fun x => u (x - y) :=
  l2Translate_ae y u

/-- Bochner average `∫ y, K y • τ_y u` of the translates of a Lebesgue L² class against a
scalar kernel `K`. -/
def lebesgueL2KernelAverage (n : ℕ) (K : Configuration n → ℝ)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Lp V 2 (volume : Measure (Configuration n)) :=
  l2KernelAverage K u

omit [CompleteSpace V] in
theorem integrable_lebesgueL2KernelIntegrand (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Integrable (fun y => K y • lebesgueL2Translate n y u) :=
  integrable_l2KernelIntegrand hK hKc u

omit [CompleteSpace V] in
/-- A nonnegative kernel of mass one averages to a contraction of Lebesgue L². -/
theorem norm_lebesgueL2KernelAverage_le (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hpos : ∀ y, 0 ≤ K y)
    (hmass : ∫ y, K y = 1) (u : Lp V 2 (volume : Measure (Configuration n))) :
    ‖lebesgueL2KernelAverage n K u‖ ≤ ‖u‖ :=
  norm_l2KernelAverage_le hK hKc hpos hmass u

/-- Continuous linear test pairings commute with the kernel average. -/
theorem lebesgueL2KernelAverage_pairing (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (u : Lp V 2 (volume : Measure (Configuration n)))
    (L : Lp V 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ) :
    L (lebesgueL2KernelAverage n K u) = ∫ y, K y * L (lebesgueL2Translate n y u) :=
  l2KernelAverage_pairing hK hKc u L

/-- The kernel average has the expected translated representative pairing against every
scalar L² test. -/
theorem lebesgueL2KernelAverage_test_pairing (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (u : Lp ℝ 2 (volume : Measure (Configuration n)))
    (w : Configuration n → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, lebesgueL2KernelAverage n K u x * w x) = ∫ y, K y * (∫ x, u (x - y) * w x) :=
  l2KernelAverage_test_pairing hK hKc u w hw

/-- For a nonnegative kernel of mass one, a translation error bound on the support of the
kernel controls the averaged L² error. -/
theorem lebesgueL2KernelAverage_error_le (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hpos : ∀ y, 0 ≤ K y)
    (hmass : ∫ y, K y = 1) (u : Lp V 2 (volume : Measure (Configuration n))) (ε : ℝ)
    (he : ∀ y ∈ Function.support K, ‖lebesgueL2Translate n y u - u‖ ≤ ε) :
    ‖lebesgueL2KernelAverage n K u - u‖ ≤ ε :=
  l2KernelAverage_error_le hK hKc hpos hmass u ε he

/-- Averages against nonnegative mass-one kernels whose supports shrink to the origin
converge strongly in Lebesgue L². -/
theorem lebesgueL2KernelAverage_tendsto (n : ℕ) (K : ℕ → Configuration n → ℝ)
    (hK : ∀ m, Continuous (K m)) (hKc : ∀ m, HasCompactSupport (K m))
    (hpos : ∀ m y, 0 ≤ K m y) (hmass : ∀ m, ∫ y, K m y = 1)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ m, ∀ y ∈ Function.support (K m), ‖y‖ ≤ r m)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Tendsto (fun m => lebesgueL2KernelAverage n (K m) u) atTop (𝓝 u) :=
  l2KernelAverage_tendsto K hK hKc hpos hmass r hr hsupp u

/-- Bochner average of translated Lebesgue L² classes against a normalized smooth bump. -/
def lebesgueL2BumpAverage (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp V 2 (volume : Measure (Configuration n))) : Lp V 2 (volume : Measure (Configuration
      n)) :=
  l2BumpAverage φ u

omit [CompleteSpace V] in
theorem integrable_lebesgueL2BumpIntegrand (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Integrable (fun y => φ.normed volume y • lebesgueL2Translate n y u) :=
  integrable_l2BumpIntegrand φ u

omit [CompleteSpace V] in
/-- A normalized bump average is a contraction on the actual Lebesgue L² space. -/
theorem norm_lebesgueL2BumpAverage_le (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    ‖lebesgueL2BumpAverage n φ u‖ ≤ ‖u‖ :=
  norm_l2BumpAverage_le φ u

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem lebesgueL2BumpAverage_pairing (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp V 2 (volume : Measure (Configuration n)))
    (L : Lp V 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ) :
    L (lebesgueL2BumpAverage n φ u) =
      ∫ y, φ.normed volume y * L (lebesgueL2Translate n y u) :=
  l2BumpAverage_pairing φ u L

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem lebesgueL2BumpAverage_test_pairing (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp ℝ 2 (volume : Measure (Configuration n)))
    (w : Configuration n → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, lebesgueL2BumpAverage n φ u x * w x) =
      ∫ y, φ.normed volume y * (∫ x, u (x - y) * w x) :=
  l2BumpAverage_test_pairing φ u w hw

/-- A local translation error bound controls the actual averaged L² error. -/
theorem lebesgueL2BumpAverage_error_le (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (u : Lp V 2 (volume : Measure (Configuration n))) (ε : ℝ) (_hε : 0 ≤ ε)
    (he : ∀ y ∈ Function.support (φ.normed volume),
      ‖lebesgueL2Translate n y u - u‖ ≤ ε) :
    ‖lebesgueL2BumpAverage n φ u - u‖ ≤ ε :=
  l2BumpAverage_error_le φ u ε he

/-- Normalized bump averages converge strongly in actual Lebesgue L². -/
theorem lebesgueL2BumpAverage_tendsto (n : ℕ)
    (φ : ℕ → ContDiffBump (0 : Configuration n))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Tendsto (fun m => lebesgueL2BumpAverage n (φ m) u) atTop (𝓝 u) :=
  l2BumpAverage_tendsto φ hφ u

end
end GinibrePoincare
