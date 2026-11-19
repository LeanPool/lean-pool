/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticMollification.lean.
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
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Strong L² convergence of normalized bump averages

The averages are actual Bochner integrals of translated L² functions under
Lebesgue measure. Strong continuity of translation gives convergence as the
mollifier radius tends to zero. Identification with pointwise convolution is
a separate step.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Translation of `u` by `y` in Lebesgue `L²`: the domain action of `-y`, giving the class of
`x ↦ u (-y + x)`. -/
def correspondenceWeightedLebesgueL2Translate (y : E)
    (u : Lp V 2 (volume : Measure (E))) : Lp V 2 (volume : Measure (E)) :=
  DomAddAct.mk (-y) +ᵥ u

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem correspondenceWeighted_continuous_lebesgueL2Translate (u : Lp V 2 (volume : Measure (E))) :
    Continuous (fun y => correspondenceWeightedLebesgueL2Translate y u) := by
  exact (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem correspondenceWeighted_lebesgueL2Translate_zero
    (u : Lp V 2 (volume : Measure (E))) : correspondenceWeightedLebesgueL2Translate 0 u = u := by
  simp [correspondenceWeightedLebesgueL2Translate]

omit [NormedSpace ℝ V] [CompleteSpace V] in
@[simp] theorem correspondenceWeighted_norm_lebesgueL2Translate (y : E)
    (u : Lp V 2 (volume : Measure (E))) :
    ‖correspondenceWeightedLebesgueL2Translate y u‖ = ‖u‖ := by
  exact DomAddAct.norm_vadd_Lp _ _

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem correspondenceWeighted_lebesgueL2Translate_ae (y : E)
    (u : Lp V 2 (volume : Measure (E))) :
    (correspondenceWeightedLebesgueL2Translate y u : E → V) =ᵐ[volume] fun x => u (x - y) := by
  have he := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) u
  filter_upwards [he] with x hx
  simpa only [correspondenceWeightedLebesgueL2Translate, Equiv.symm_apply_apply, vadd_eq_add,
      sub_eq_add_neg,
    add_comm] using hx

/-- The average `∫ y, φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u` of the
translates of `u` against the normalized bump `φ`. -/
def correspondenceWeightedLebesgueL2BumpAverage (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) : Lp V 2 (volume : Measure (E)) :=
  ∫ y, φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u

omit [CompleteSpace V] in
theorem correspondenceWeighted_integrable_lebesgueL2BumpIntegrand (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) :
    Integrable (fun y => φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u) :=
  (φ.continuous_normed.smul (correspondenceWeighted_continuous_lebesgueL2Translate
      u)).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.smul_right

omit [CompleteSpace V] in
/-- A normalized bump average is a contraction on the actual Lebesgue L² space. -/
theorem correspondenceWeighted_norm_lebesgueL2BumpAverage_le (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) :
    ‖correspondenceWeightedLebesgueL2BumpAverage φ u‖ ≤ ‖u‖ := by
  have ht : ‖correspondenceWeightedLebesgueL2BumpAverage φ u‖ ≤ ∫ y, φ.normed volume y * ‖u‖ := by
    apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const ‖u‖)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, correspondenceWeighted_norm_lebesgueL2Translate, Real.norm_eq_abs,
        abs_of_nonneg (φ.nonneg_normed y)])
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using ht

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_pairing (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E)))
    (L : Lp V 2 (volume : Measure (E)) →L[ℝ] ℝ) :
    L (correspondenceWeightedLebesgueL2BumpAverage φ u) =
      ∫ y, φ.normed volume y * L (correspondenceWeightedLebesgueL2Translate y u) := by
  unfold correspondenceWeightedLebesgueL2BumpAverage
  rw [← L.integral_comp_comm (correspondenceWeighted_integrable_lebesgueL2BumpIntegrand φ u)]
  simp only [map_smul, smul_eq_mul]

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_test_pairing (φ : ContDiffBump (0 : E))
    (u : Lp ℝ 2 (volume : Measure (E)))
    (w : E → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, correspondenceWeightedLebesgueL2BumpAverage φ u x * w x) =
      ∫ y, φ.normed volume y * (∫ x, u (x - y) * w x) := by
  let L : Lp ℝ 2 (volume : Measure (E)) →L[ℝ] ℝ :=
    innerSL ℝ (hw.toLp w)
  have hL (v : Lp ℝ 2 (volume : Measure (E))) :
      L v = ∫ x, v x * w x := by
    change inner ℝ (hw.toLp w) v = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [← hL]
  rw [correspondenceWeighted_lebesgueL2BumpAverage_pairing]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [hL]
  congr 1
  apply integral_congr_ae
  filter_upwards [correspondenceWeighted_lebesgueL2Translate_ae y u] with x hx
  rw [hx]

/-- A local translation error bound controls the actual averaged L² error. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_error_le (φ : ContDiffBump (0 : E))
    (u : Lp V 2 (volume : Measure (E))) (ε : ℝ) (_hε : 0 ≤ ε)
    (he : ∀ y ∈ Function.support (φ.normed volume),
      ‖correspondenceWeightedLebesgueL2Translate y u - u‖ ≤ ε) :
    ‖correspondenceWeightedLebesgueL2BumpAverage φ u - u‖ ≤ ε := by
  have hconst : Integrable (fun y => φ.normed volume y • u) := φ.integrable_normed.smul_const u
  have hint := correspondenceWeighted_integrable_lebesgueL2BumpIntegrand φ u
  have heq : correspondenceWeightedLebesgueL2BumpAverage φ u - u =
      ∫ y, φ.normed volume y • (correspondenceWeightedLebesgueL2Translate y u - u) := by
    unfold correspondenceWeightedLebesgueL2BumpAverage
    calc
      _ = (∫ y, φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u) -
          ∫ y, φ.normed volume y • u := by rw [φ.integral_normed_smul volume u]
      _ = ∫ y, (φ.normed volume y • correspondenceWeightedLebesgueL2Translate y u - φ.normed volume
          y • u) :=
        (integral_sub hint hconst).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => (smul_sub _ _ _).symm)
  rw [heq]
  have hnorm : ‖∫ y, φ.normed volume y • (correspondenceWeightedLebesgueL2Translate y u - u)‖ ≤
      ∫ y, φ.normed volume y * ε := by
    apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const ε)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y)]
      by_cases hy : φ.normed volume y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (he y hy) (φ.nonneg_normed y))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using hnorm

/-- Normalized bump averages converge strongly in actual Lebesgue L². -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_tendsto
    (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp V 2 (volume : Measure (E))) :
    Tendsto (fun m => correspondenceWeightedLebesgueL2BumpAverage (φ m) u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp
    (correspondenceWeighted_continuous_lebesgueL2Translate u).continuousAt (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hφ).2 δ hδ)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm]
  apply (correspondenceWeighted_lebesgueL2BumpAverage_error_le (φ m) u (ε / 2) (half_pos hε).le
      ?_).trans_lt
    (half_lt_self hε)
  intro y hy
  have hy' : y ∈ Metric.ball (0 : E) (φ m).rOut := by
    rwa [(φ m).support_normed_eq] at hy
  have hd : dist y 0 < δ := (Metric.mem_ball.mp hy').trans (hM m hm)
  have he := ht hd
  simpa only [correspondenceWeighted_lebesgueL2Translate_zero, dist_eq_norm] using he.le

end
end GinibrePoincare
