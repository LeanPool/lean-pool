/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-! # Quantitative convex growth and monotone threshold exceptions -/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace Bruck

/-- The right derivative of a real function at the given point. -/
noncomputable def wvRightSlope (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin A (Ioi x) x

theorem wv_convex_subgradient_lower {A : ℝ → ℝ} (hA : ConvexOn ℝ univ A)
    (x y : ℝ) : A x + wvRightSlope A x * (y - x) ≤ A y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hh := hA.rightDeriv_le_slope_of_mem_interior
      (by simp : x ∈ interior (univ : Set ℝ)) (mem_univ y) hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hh
    change derivWithin A (Ioi x) x * (y - x) ≤ A y - A x at hh
    dsimp only [wvRightSlope]
    linarith
  · simp
  · have hh := (hA.slope_le_leftDeriv_of_mem_interior (mem_univ y)
      (by simp : x ∈ interior (univ : Set ℝ)) hyx).trans
        (hA.leftDeriv_le_rightDeriv_of_mem_interior (by simp))
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hh
    dsimp only [wvRightSlope]
    nlinarith

theorem wv_convex_affine_error {A : ℝ → ℝ} (hA : ConvexOn ℝ univ A)
    {x y δ K : ℝ} (hδ : |y - x| ≤ δ) (hK : 0 ≤ K)
    (hsl : |wvRightSlope A y - wvRightSlope A x| ≤ K) :
    |A y - A x - wvRightSlope A x * (y - x)| ≤ K * δ := by
  have hlow := wv_convex_subgradient_lower hA x y
  have hupp := wv_convex_subgradient_lower hA y x
  have hprod : (wvRightSlope A y - wvRightSlope A x) * (y - x) ≤ K * δ := by
    calc
      _ ≤ |(wvRightSlope A y - wvRightSlope A x) * (y - x)| := le_abs_self _
      _ = |wvRightSlope A y - wvRightSlope A x| * |y - x| := abs_mul _ _
      _ ≤ K * δ := mul_le_mul hsl hδ (abs_nonneg _) hK
  rw [abs_of_nonneg (by linarith : 0 ≤ A y - A x - wvRightSlope A x * (y - x))]
  nlinarith

/-- The first threshold crossing of a slope on `[1, ∞)`, expressed as an infimum. -/
noncomputable def wvThreshold (L : ℝ → ℝ) (b : ℝ) : ℝ :=
  sInf {x : ℝ | 1 ≤ x ∧ b ≤ L x}

theorem wv_threshold_between {L : ℝ → ℝ} (hL : MonotoneOn L (Ici 1))
    {b x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxb : L x < b) (hyb : b ≤ L y) :
    x ≤ wvThreshold L b ∧ wvThreshold L b ≤ y := by
  have hne : ({t : ℝ | 1 ≤ t ∧ b ≤ L t}).Nonempty := ⟨y, hy, hyb⟩
  constructor
  · apply le_csInf hne
    intro t ht
    by_contra hxt
    have htx : t ≤ x := (lt_of_not_ge hxt).le
    have hh := hL ht.1 hx htx
    linarith [ht.2]
  · exact csInf_le ⟨1, fun t ht => ht.1⟩ ⟨hy, hyb⟩

theorem wv_threshold_no_crossing {L : ℝ → ℝ} (hL : MonotoneOn L (Ici 1))
    {b x δ w : ℝ} (hx : 1 ≤ x - δ) (hδ : 0 ≤ δ) (hw : δ ≤ w)
    (hout : x ∉ Icc (wvThreshold L b - w) (wvThreshold L b + w)) :
    (b ≤ L x → b ≤ L (x - δ)) ∧ (L x < b → L (x + δ) < b) := by
  have hx1 : 1 ≤ x := by linarith
  constructor
  · intro hb
    by_contra hminus
    have ht := wv_threshold_between hL hx hx1 (lt_of_not_ge hminus) hb
    apply hout
    constructor <;> linarith [ht.1, ht.2]
  · intro hb
    by_contra hplus
    have ht := wv_threshold_between hL hx1 (by linarith : 1 ≤ x + δ) hb (le_of_not_gt hplus)
    apply hout
    constructor <;> linarith [ht.1, ht.2]

theorem wv_threshold_intervals_finite_volume {t w : ℕ → ℝ}
    (hs : Summable w) :
    MeasurableSet (⋃ n, Icc (t n - w n) (t n + w n)) ∧
      volume (⋃ n, Icc (t n - w n) (t n + w n)) < ⊤ := by
  constructor
  · exact MeasurableSet.iUnion fun n => measurableSet_Icc
  · calc
      _ ≤ ∑' n, volume (Icc (t n - w n) (t n + w n)) := measure_iUnion_le _
      _ = ∑' n, ENNReal.ofReal (2 * w n) := by
        congr 1
        funext n
        rw [Real.volume_Icc]
        congr 1
        ring
      _ < ⊤ := (hs.mul_left 2).tsum_ofReal_lt_top

end Bruck
