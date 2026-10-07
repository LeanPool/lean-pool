/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortLocalConstant

/-!
# Phase gap for cutoff derivatives

The normal-phase factor of the cutoff is locally one above the fixed
negative phase gap. Its derivative errors therefore lie below that gap.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The open region above the negative transition gap where the normal
cutoff has completed its transition. -/
@[expose] def buShortAboveGap (scale : ℝ) : Set (Vec3 × ℝ) :=
  {q | buShortYMinus scale < q.1 2 ∧
    1 / 2 < q.2 ∧ q.2 < 1 ∧
    -buShortD scale / 2 <
      buShortFExt (q.1 2) q.2 - buShortB scale}

/-- The region above the negative phase gap is open. -/
theorem buShortAboveGap_isOpen (scale : ℝ) :
    IsOpen (buShortAboveGap scale) := by
  have hheight : Continuous (fun q : Vec3 × ℝ => q.1 2) :=
    (continuous_apply 2).comp continuous_fst
  have htime : Continuous (fun q : Vec3 × ℝ => q.2) := continuous_snd
  have hphase : Continuous (fun q : Vec3 × ℝ =>
      buShortFExt (q.1 2) q.2 - buShortB scale) :=
    buShortFExt_product_smooth.continuous.sub continuous_const
  have hfirst : IsOpen {q : Vec3 × ℝ | buShortYMinus scale < q.1 2} :=
    isOpen_lt continuous_const hheight
  have hsecond : IsOpen {q : Vec3 × ℝ | (1 / 2 : ℝ) < q.2} :=
    isOpen_lt continuous_const htime
  have hthird : IsOpen {q : Vec3 × ℝ | q.2 < 1} :=
    isOpen_lt htime continuous_const
  have hfourth : IsOpen {q : Vec3 × ℝ | -buShortD scale / 2 <
      buShortFExt (q.1 2) q.2 - buShortB scale} :=
    isOpen_lt continuous_const hphase
  have h := hfirst.inter (hsecond.inter (hthird.inter hfourth))
  simpa only [buShortAboveGap, Set.ofPred_and] using h

/-- The smooth normal cutoff is one throughout the region above the gap. -/
theorem buShortEtaExt_eq_one_on_aboveGap
    {scale : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1) :
    EqOn (buShortEtaExt scale) (fun _ => 1) (buShortAboveGap scale) := by
  intro q hq
  rcases hq with ⟨hyminus, hs, hs1, hphase⟩
  have hy2 : 2 ≤ q.1 2 := by
    have h : 1 < 3 / scale := by
      apply (lt_div_iff₀ hscale).2
      linarith only [hscale1]
    have hminus : 2 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      linarith only [h]
    exact (le_of_lt hminus).trans hyminus.le
  have hy : 0 < q.1 2 := lt_of_lt_of_le (by norm_num) hy2
  have hphase' : -buShortD scale / 2 <
      buShortF (q.1 2) q.2 - buShortB scale := by
    rw [← buShortFExt_eq hy2 hs.le]
    exact hphase
  exact buShortEtaExt_eq_one_above_gap hscale hscale1 hy
    hs.le hs1.le hphase'

/-- On the region above the gap, every first, second spatial, and time
derivative of the normal cutoff vanishes. -/
theorem buShortEtaExt_derivatives_zero_aboveGap
    {scale : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortAboveGap scale) :
    (∀ j : Fin 3,
      spatialPartial (buCutScalar (buShortEtaExt scale)) j z = 0) ∧
      (∀ j k : Fin 3,
        spatialSecondPartial (buCutScalar (buShortEtaExt scale)) j k z = 0) ∧
      timePartial (buCutScalar (buShortEtaExt scale)) z = 0 := by
  exact buCutScalar_derivatives_eq_zero_of_eqOn
    (buShortAboveGap_isOpen scale)
    (buShortEtaExt_eq_one_on_aboveGap hscale hscale1) hz

end ESS
