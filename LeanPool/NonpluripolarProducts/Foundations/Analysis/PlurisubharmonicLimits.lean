/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic
public import Mathlib.Topology.Order.Monotone

/-!
# Decreasing limits of disc-plurisubharmonic functions

The functions in the sequence satisfy the disc criterion on one common set.
The proof applies monotone convergence to the nonnegative extended-real
deficits. In particular, the limit is allowed to be identically `⊥`.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

/-- Subtraction from a finite real constant, followed by the nonnegative-part
map, is continuous even at either infinite endpoint. -/
theorem continuous_finiteDeficit (C : ℝ) :
    Continuous (fun z : EReal => ((C : EReal) - z).toENNReal) := by
  have hp : Continuous (fun z : EReal => ((C : EReal), -z)) :=
    continuous_const.prodMk continuous_neg
  have hs : Continuous (fun z : EReal => (C : EReal) - z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [sub_eq_add_neg, Function.comp_def] using!
      (EReal.continuousAt_add (p := ((C : EReal), -z))
        (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).comp
        (f := fun z : EReal => ((C : EReal), -z)) (x := z) hp.continuousAt
  exact EReal.continuous_toENNReal.comp hs

/-- Finite deficits exchange arbitrary infima with suprema; no finiteness of
the values, nor a lower bound for them, is required. -/
theorem finiteDeficit_iInf {ι : Sort*} (C : ℝ) (z : ι → EReal) :
    ((C : EReal) - ⨅ i, z i).toENNReal =
      ⨆ i, ((C : EReal) - z i).toENNReal := by
  apply Antitone.map_iInf_of_continuousAt
    (continuous_finiteDeficit C).continuousAt
  · intro a b hab
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hab)
  · simp [sub_eq_add_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Monotone convergence for angular deficits needs only measurability of
each deficit and pointwise antitonicity of the underlying boundary values.
This form is useful when continuous real boundary majorants are supplied
without a common `DiscPshOn` domain. -/
theorem circleDeficit_iInf_of_antitone_of_measurable
    {u : ℕ → E → EReal} (x v : E) {r : ℝ} (C : ℝ)
    (hm : ∀ n, Measurable fun t : ℝ =>
      ((C : EReal) - u n (x + circleMap 0 r t • v)).toENNReal)
    (hanti : ∀ t : ℝ, Antitone fun n =>
      u n (x + circleMap 0 r t • v)) :
    circleDeficit (fun y => ⨅ n, u n y) x v r C =
      ⨆ n, circleDeficit (u n) x v r C := by
  unfold circleDeficit
  simp_rw [finiteDeficit_iInf]
  apply lintegral_iSup hm
  intro m n hmn t
  exact EReal.toENNReal_le_toENNReal
    (EReal.sub_le_sub le_rfl (hanti t hmn))

/-- Monotone convergence for the actual nonnegative angular deficits of a
decreasing sequence on a common disc domain. -/
theorem circleDeficit_iInf_of_antitone {u : ℕ → E → EReal} {U : Set E}
    (hu : ∀ n, DiscPshOn (u n) U)
    (hanti : ∀ y ∈ U, Antitone (fun n => u n y))
    (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) (C : ℝ) :
    circleDeficit (fun y => ⨅ n, u n y) x v r C =
      ⨆ n, circleDeficit (u n) x v r C := by
  apply circleDeficit_iInf_of_antitone_of_measurable x v C
  · intro n
    exact (hu n).measurable_circle_deficit x v hr hD C
  · intro t
    exact hanti _ (hD (circle_mem_affineClosedDisc x v hr t))

/-- A pointwise decreasing sequence satisfying the disc criterion on one
common set has a limit satisfying the same criterion. The limit may be
identically negative infinity. -/
theorem DiscPshOn.iInf_of_antitone {u : ℕ → E → EReal} {U : Set E}
    (hu : ∀ n, DiscPshOn (u n) U)
    (hanti : ∀ y ∈ U, Antitone (fun n => u n y)) :
    DiscPshOn (fun y => ⨅ n, u n y) U := by
  refine ⟨?_, upperSemicontinuousOn_iInf (fun n => (hu n).upperSemicontinuousOn), ?_⟩
  · intro y hy
    exact ne_of_lt ((iInf_le (fun n => u n y) 0).trans_lt
      (lt_top_iff_ne_top.mpr ((hu 0).ne_top y hy)))
  · intro x v r hr hD C hC
    obtain ⟨B, hB⟩ := (hu 0).exists_disc_upper_bound x v hr.le hD
    let a : ℝ := Max.max 0 (B - C)
    have ha : 0 ≤ a := le_max_left _ _
    have hBC : B ≤ C + a := by
      have : B - C ≤ a := le_max_right _ _
      linarith
    have hbound : ∀ n, ∀ y ∈ affineClosedDisc x v r,
        u n y ≤ ((C + a : ℝ) : EReal) := by
      intro n y hy
      exact (hanti y (hD hy) (Nat.zero_le n)).trans
        ((hB y hy).trans (EReal.coe_le_coe_iff.mpr hBC))
    apply (discSubmean_add_bound_iff x v hr.le C a ha hC).mp
    rw [circleDeficit_iInf_of_antitone hu hanti x v hr.le hD]
    apply iSup_le
    intro n
    apply ((hu n).submean x v r hr hD (C + a) (hbound n)).trans
    exact mul_le_mul_of_nonneg_left
      (EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl
        (iInf_le (fun n => u n x) n))) zero_le

/-- The common-domain disc theorem yields ordinary local plurisubharmonicity
on an open set. This does not assume a local-to-global disc theorem for
arbitrary choices of shrinking germ neighborhoods. -/
theorem DiscPshOn.plurisubharmonicOn_iInf_of_antitone
    {u : ℕ → E → EReal} {U : Set E} (hU : IsOpen U)
    (hu : ∀ n, DiscPshOn (u n) U)
    (hanti : ∀ y ∈ U, Antitone (fun n => u n y)) :
    PlurisubharmonicOn (fun y => ⨅ n, u n y) U :=
  (DiscPshOn.iInf_of_antitone hu hanti).plurisubharmonicOn hU

end SGPT.Foundations.Analysis
