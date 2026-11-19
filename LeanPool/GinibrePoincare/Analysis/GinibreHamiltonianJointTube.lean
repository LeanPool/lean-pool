/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianJointTube.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianJointStability
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathClosedHittingTime

/-! Small noise perturbations cannot leave a compact collision-free trajectory tube. -/

@[expose] public section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenSegment_joint_stays_tube {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z w : Configuration n} {T : ℝ≥0} {X Y : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hY : GinibreDrivenSegment n α M w T Y)
    {K : Set (Configuration n)} (hXK : ∀ t ∈ Icc 0 (T : ℝ), X t ∈ K)
    {r : ℝ} (_ : 0 < r) {L : ℝ≥0} {g : Configuration n → Configuration n}
    (hg : LipschitzWith L g) (he : EqOn g (ginibreLangevinDrift n α) (cthickening r K))
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ * Real.exp ((L : ℝ) * (T : ℝ)) < r)
    (hnoise : ∀ t ∈ Icc 0 (T : ℝ), ‖z - w‖ + ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 (T : ℝ), ‖X t-Y t‖ < r := by
  classical
  let p : ℝ≥0 → ℝ := fun t => (Set.projIcc 0 (T : ℝ) T.property (t : ℝ) : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp (continuous_projIcc.comp
      NNReal.continuous_coe)
  have hpr (t : ℝ≥0) : p t ∈ Icc 0 (T : ℝ) := (Set.projIcc _ _ _ _).property
  have hpe (t : ℝ≥0) (ht : t ≤ T) : p t = (t : ℝ) :=
    congrArg Subtype.val (Set.projIcc_of_mem T.property ⟨t.property, ht⟩)
  let u : ℝ≥0 → Unit → Configuration n := fun t _ => X (p t)-Y (p t)
  have hu : Continuous (fun t => u t ()) :=
    (hX.1.comp_continuous hp hpr).sub (hY.1.comp_continuous hp hpr)
  have h0 : ‖u 0 ()‖ ≤ r := by
    simp only [u, hpe 0 bot_le, NNReal.coe_zero, hX.2.1, hY.2.1]
    have hδr : δ < r := lt_of_le_of_lt (le_mul_of_one_le_right hδ (Real.one_le_exp (mul_nonneg
        L.property T.property))) hsmall
    exact (le_trans (by have h := hnoise 0 ⟨le_rfl, T.property⟩; linarith [norm_nonneg (N 0-M 0)])
        hδr.le)
  intro t ht
  by_contra hn
  have hrt : r ≤ ‖X t-Y t‖ := le_of_not_gt hn
  have hHit : ∃ j ∈ Icc 0 T, u j () ∈ {x | r ≤ ‖x‖} := by
    refine ⟨Real.toNNReal t, ⟨bot_le, (Real.toNNReal_le_iff_le_coe).mpr ht.2⟩, ?_⟩
    change r ≤ ‖X (p (Real.toNNReal t))-Y (p (Real.toNNReal t))‖
    rw [hpe _ ((Real.toNNReal_le_iff_le_coe).mpr ht.2), Real.coe_toNNReal t ht.1]
    exact hrt
  let τ : ℝ≥0 := hittingBtwn u {x | r ≤ ‖x‖} 0 T ()
  have hτT : τ ≤ T := hittingBtwn_le ()
  have hτmem : r ≤ ‖u τ ()‖ := drivenContinuous_closed_hitting_mem u _
    (isClosed_le continuous_const continuous_norm) T () hu hHit
  have hτb (s : ℝ≥0) (hs : s ≤ τ) : ‖u s ()‖ ≤ r :=
    drivenContinuous_norm_le_until_hitting u r T () hu h0 s hs
  have hsub : Icc (0 : ℝ) (τ : ℝ) ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right hτT
  have hXS : GinibreDrivenSegment n α N z τ X := ⟨hX.1.mono hsub, hX.2.1, fun s hs => hX.2.2 s (hsub
      hs)⟩
  have hYS : GinibreDrivenSegment n α M w τ Y := ⟨hY.1.mono hsub, hY.2.1, fun s hs => hY.2.2 s (hsub
      hs)⟩
  have hYSK (s : ℝ) (hs : s ∈ Icc 0 (τ : ℝ)) : Y s ∈ cthickening r K := by
    have hsNN : Real.toNNReal s ≤ τ := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    have hb := hτb _ hsNN
    change ‖X (p (Real.toNNReal s))-Y (p (Real.toNNReal s))‖ ≤ r at hb
    rw [hpe _ (hsNN.trans hτT), Real.coe_toNNReal s hs.1] at hb
    apply mem_cthickening_of_dist_le (Y s) (X s) r K (hXK s (hsub hs))
    simpa only [dist_eq_norm, norm_sub_rev] using hb
  have hstab := ginibreDrivenSegment_joint_stability_in_extension hXS hYS hg he
    (fun s hs => self_subset_cthickening K (hXK s (hsub hs))) hYSK hδ
    (fun s hs => hnoise s (hsub hs)) (τ : ℝ) ⟨τ.property, le_rfl⟩
  have hexp : Real.exp ((L : ℝ)*(τ : ℝ)) ≤ Real.exp ((L : ℝ)*(T : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτT L.property)
  have hbound := hstab.trans (mul_le_mul_of_nonneg_left hexp hδ)
  change r ≤ ‖X (p τ)-Y (p τ)‖ at hτmem
  rw [hpe τ hτT] at hτmem
  linarith

end
end GinibrePoincare
