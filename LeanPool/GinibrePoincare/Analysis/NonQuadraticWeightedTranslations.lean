/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticWeightedTranslations.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticLpMultiplier
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticComplexTestInverse
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Genuine local L² continuity of weighted compact translations -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology Pointwise ContDiff ENNReal
namespace GinibrePoincare
noncomputable section
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The weighted translate `x ↦ ψ (x - a) * exp (-n V x / 2)`. -/
def planarWeightedTranslateFunction (n : ℕ) (V : ℂ → ℝ) (ψ : ℂ → ℂ) (a x : ℂ) :=
  ψ (x - a) * planarPotentialHalfWeight n V x

theorem planarWeightedTranslate_memLp (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) :
    MemLp (planarWeightedTranslateFunction n V ψ a) 2 volume := by
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  have hs : HasCompactSupport (fun x => ψ (x - a)) := by
    simpa only [sub_eq_add_neg, Function.comp_def, Homeomorph.coe_addRight] using hc.comp_homeomorph
        (Homeomorph.addRight (-a))
  exact ((hψ.comp (continuous_id.sub continuous_const)).mul hw).memLp_of_hasCompactSupport
      hs.mul_right

/-- The `L²(ℂ)` class of the weighted translate `x ↦ ψ (x - a) * exp (-n V x / 2)` of a
continuous compactly supported `ψ`. -/
def planarWeightedTranslateL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) : PlanarLebesgueL2 :=
  (planarWeightedTranslate_memLp n V hV ψ hψ hc a).toLp _

/-- Weighted translations are strongly continuous on every actual compact
parameter set. A bounded localized multiplier supplies the proof even when
the global confinement weight is unbounded. -/
theorem planarWeightedTranslateL2_continuousOn_compact
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (A : Set ℂ) (hA : IsCompact A) :
    ContinuousOn (planarWeightedTranslateL2 n V hV ψ hψ hc) A := by
  let S := A + tsupport ψ
  have hS : IsCompact S := hA.add hc
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  let b : ℂ → ℂ := S.indicator (planarPotentialHalfWeight n V)
  have hb : AEStronglyMeasurable b volume := hw.aestronglyMeasurable.indicator hS.measurableSet
  have hbn (x : ℂ) : ‖b x‖ ≤ max C 0 := by
    by_cases hx : x ∈ S
    · simp only [b, Set.indicator_of_mem hx]
      exact (hC x hx).trans (le_max_left _ _)
    · simp only [b, Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _
  let T := boundedComplexL2Multiplier b hb (max C 0) hbn
  have hm : MemLp ψ 2 volume := hψ.memLp_of_hasCompactSupport hc
  let τ : ℂ → PlanarLebesgueL2 := fun a => DomAddAct.mk (-a) +ᵥ hm.toLp ψ
  have hτ : Continuous τ := (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have he (a : ℂ) (ha : a ∈ A) : planarWeightedTranslateL2 n V hV ψ hψ hc a = T (τ a) := by
    apply Lp.ext
    have ht := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-a)) (hm.toLp ψ)
    have htp := (eventually_add_right_iff (volume : Measure ℂ) (-a)).mpr hm.coeFn_toLp
    filter_upwards [(planarWeightedTranslate_memLp n V hV ψ hψ hc a).coeFn_toLp,
      boundedComplexL2Multiplier_coeFn b hb (max C 0) hbn (τ a), ht, htp] with x hx hTx htr hψx
    change (planarWeightedTranslate_memLp n V hV ψ hψ hc a).toLp _ x =
      boundedComplexL2Multiplier b hb (max C 0) hbn (τ a) x
    rw [hx, hTx]
    have htrx : (τ a) x = ψ (x - a) := by
      have htr' : (τ a) x = (hm.toLp ψ) (x - a) := by
        simpa only [τ, Equiv.symm_apply_apply, vadd_eq_add, sub_eq_add_neg, add_comm] using htr
      exact htr'.trans (by simpa only [sub_eq_add_neg] using hψx)
    rw [htrx]
    change ψ (x - a) * planarPotentialHalfWeight n V x = b x * ψ (x - a)
    by_cases hz : ψ (x - a) = 0
    · simp [hz]
    · have hs : x ∈ S := Set.mem_add.mpr ⟨a, ha, x - a,
        subset_closure (by exact hz : x - a ∈ Function.support ψ), by abel⟩
      simp only [b, Set.indicator_of_mem hs]
      exact mul_comm _ _
  exact (T.continuous.comp hτ).continuousOn.congr (fun a ha => he a ha)
/-- Weighted compact translations are genuinely strongly continuous for
all translation parameters, proved by compact localization around each. -/
theorem planarWeightedTranslateL2_continuous
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Continuous (planarWeightedTranslateL2 n V hV ψ hψ hc) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (planarWeightedTranslateL2_continuousOn_compact n V hV ψ hψ hc
    (Metric.closedBall a 1) (isCompact_closedBall a 1)).continuousAt
      (Metric.closedBall_mem_nhds a zero_lt_one)

end
end GinibrePoincare
