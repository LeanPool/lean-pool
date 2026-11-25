/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicAE
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic

/-!
# The local maximum principle for plurisubharmonic functions

This file isolates the maximum-principle input needed to recover convexity of
an imaginary-translation-invariant plurisubharmonic function.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis

/-- A real affine function of the real coordinate has zero Levi form. -/
theorem leviForm_affine_re (p q : ℝ) (z w : ℂ) :
    leviForm (fun ζ : ℂ => p * ζ.re + q) z w = 0 := by
  let A : ℂ →L[ℝ] ℝ := p • Complex.reCLM
  have hfd : fderiv ℝ (fun ζ : ℂ => p * ζ.re + q) = fun _ => A := by
    funext ζ
    exact (by
      simpa [A, Complex.reCLM_apply, smul_eq_mul] using
        ((Complex.reCLM.hasFDerivAt.const_smul p).add_const q).fderiv)
  rw [leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv, hfd]
  simp

/-- Real affine functions of the real coordinate are globally
plurisubharmonic. -/
theorem plurisubharmonicOn_coe_affine_re (p q : ℝ) (U : Set ℂ) :
    PlurisubharmonicOn (fun z : ℂ => ((p * z.re + q : ℝ) : EReal)) U := by
  have hsmooth : ContDiff ℝ 2 (fun z : ℂ => p * z.re + q) := by
    have hlin : ContDiff ℝ 2 (p • Complex.reCLM : ℂ → ℝ) :=
      (p • Complex.reCLM).contDiff
    simpa [Complex.reCLM_apply, smul_eq_mul] using
      hlin.add (contDiff_const : ContDiff ℝ 2 (fun _ : ℂ => q))
  have hglobal : PlurisubharmonicOn
      (fun z : ℂ => ((p * z.re + q : ℝ) : EReal)) univ :=
    plurisubharmonicOn_of_levi_nonneg hsmooth isOpen_univ
      (fun z _ w => by rw [leviForm_affine_re])
  exact hglobal.mono (Set.subset_univ U)

/-- If a plurisubharmonic function is bounded above by a finite constant on a
ball and reaches that constant at the center, then it is constant on the ball.
This is the local strong maximum principle in the exact form used below. -/
theorem DiscPshOn.eqOn_ball_of_le_of_eq {u : ℂ → EReal} {U : Set ℂ}
    (hu : DiscPshOn u U) (a : ℂ) {R C : ℝ}
    (hBU : ball a R ⊆ U) (hC : ∀ y ∈ ball a R, u y ≤ (C : EReal))
    (ha : u a = (C : EReal)) : EqOn u (fun _ => (C : EReal)) (ball a R) := by
  have hle := hu.ball_deficit_le volume a R C hBU hC
  have hzero : ∫⁻ x in ball a R, ((C : EReal) - u x).toENNReal = 0 := by
    apply le_antisymm
    · simpa [ha] using hle
    · exact bot_le
  have hae0 : (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[
      volume.restrict (ball a R)] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff'
      (hu.aemeasurable_deficit_restrict measurableSet_ball hBU C volume)).mp hzero
  have hae : u =ᵐ[volume.restrict (ball a R)] fun _ => (C : EReal) := by
    filter_upwards [hae0, ae_restrict_mem measurableSet_ball] with x hx hmem
    exact le_antisymm (hC x hmem)
      (EReal.sub_nonpos.mp (EReal.toENNReal_eq_zero_iff.mp hx))
  have hpsh : PlurisubharmonicOn u (ball a R) :=
    (hu.mono hBU).plurisubharmonicOn isOpen_ball
  have hconst : PlurisubharmonicOn (fun _ : ℂ => (C : EReal)) (ball a R) :=
    fun x _ => plurisubharmonicAt_const (C : EReal) (by simp) x
  exact hpsh.eqOn_of_ae_eq hconst isOpen_ball volume hae

/-- An imaginary-translation-invariant plurisubharmonic function cannot attain
a finite upper bound in the interior of an interval while being strictly below
that bound at both endpoints. -/
theorem PlurisubharmonicOn.comp_re_no_finite_strict_interior_max
    {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ => v z.re) (Complex.re ⁻¹' I))
    {a b x C : ℝ} (habI : Icc a b ⊆ I) (hx : x ∈ Ioo a b)
    (hmax : ∀ y ∈ Icc a b, v y ≤ (C : EReal)) (heq : v x = (C : EReal))
    (ha : v a < (C : EReal)) (hb : v b < (C : EReal)) : False := by
  let O : Set ℝ := {y | y ∈ Ioo a b ∧ v y = (C : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro y hy
    have hyI : y ∈ I := habI (Ioo_subset_Icc_self hy.1)
    obtain ⟨U, hU, hyU, hdisc⟩ := hu (y : ℂ) (by simpa using hyI)
    have hopen : IsOpen (U ∩ Complex.re ⁻¹' Ioo a b) :=
      hU.inter (isOpen_Ioo.preimage Complex.continuous_re)
    have hyopen : (y : ℂ) ∈ U ∩ Complex.re ⁻¹' Ioo a b := by
      exact ⟨hyU, by simpa using hy.1⟩
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen (y : ℂ) hyopen
    have hBU : ball (y : ℂ) R ⊆ U := fun z hz => (hball hz).1
    have hCball : ∀ z ∈ ball (y : ℂ) R, v z.re ≤ (C : EReal) := by
      intro z hz
      exact hmax z.re (Ioo_subset_Icc_self (hball hz).2)
    have heqball := hdisc.eqOn_ball_of_le_of_eq (y : ℂ) hBU hCball (by simpa using hy.2)
    refine ⟨R, hR, ?_⟩
    intro q hq
    have hqc : (q : ℂ) ∈ ball (y : ℂ) R := by
      rw [mem_ball, Complex.dist_of_im_eq (by simp)]
      simpa using hq
    exact ⟨(hball hqc).2, by simpa using heqball hqc⟩
  have husc : UpperSemicontinuousOn v (Icc a b) := by
    have hmap : MapsTo (fun y : ℝ => (y : ℂ)) (Icc a b) (Complex.re ⁻¹' I) := by
      intro y hy
      simpa using habI hy
    simpa [Function.comp_def] using
      hu.upperSemicontinuousOn.comp Complex.continuous_ofReal.continuousOn hmap
  have hK : IsCompact (Icc a b ∩ v ⁻¹' Ici (C : EReal)) :=
    husc.isCompact_inter_preimage_Ici isCompact_Icc (C : EReal)
  have hOK : O ⊆ Icc a b ∩ v ⁻¹' Ici (C : EReal) := by
    intro y hy
    exact ⟨Ioo_subset_Icc_self hy.1, by simp [hy.2]⟩
  have hclosure : closure O ∩ Icc a b ⊆ O := by
    intro y hy
    have hyK := closure_minimal hOK hK.isClosed hy.1
    have hyeq : v y = (C : EReal) := le_antisymm (hmax y hy.2) hyK.2
    have hya : y ≠ a := by
      intro h
      subst y
      exact (ne_of_lt ha) hyeq
    have hyb : y ≠ b := by
      intro h
      subst y
      exact (ne_of_lt hb) hyeq
    exact ⟨⟨lt_of_le_of_ne hy.2.1 (Ne.symm hya), lt_of_le_of_ne hy.2.2 hyb⟩, hyeq⟩
  have hnonempty : (Icc a b ∩ O).Nonempty :=
    ⟨x, Ioo_subset_Icc_self hx, hx, heq⟩
  have hall : Icc a b ⊆ O :=
    isPreconnected_Icc.subset_of_closure_inter_subset hO hnonempty hclosure
  have haO := hall (left_mem_Icc.mpr (hx.1.trans hx.2).le)
  exact (ne_of_lt ha) haO.2

/-- The finite values of an imaginary-translation-invariant plurisubharmonic
function lie below the affine chord joining two finite endpoint values. -/
theorem PlurisubharmonicOn.comp_re_toReal_le_affine_chord
    {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ => v z.re) (Complex.re ⁻¹' I))
    {a t b : ℝ} (hat : a < t) (htb : t < b) (habI : Icc a b ⊆ I)
    (ha_top : v a ≠ ⊤) (ha_bot : v a ≠ ⊥)
    (ht_top : v t ≠ ⊤) (ht_bot : v t ≠ ⊥)
    (hb_top : v b ≠ ⊤) (hb_bot : v b ≠ ⊥) :
    (v t).toReal ≤ (v a).toReal +
      (t - a) * ((v b).toReal - (v a).toReal) / (b - a) := by
  let A : ℝ := (v a).toReal
  let B : ℝ := (v b).toReal
  let p : ℝ := (B - A) / (b - a)
  let q : ℝ := A - p * a
  let w : ℝ → EReal := fun x => v x + (((-p) * x + (-q) : ℝ) : EReal)
  have hab : a < b := hat.trans htb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hwpsh : PlurisubharmonicOn (fun z : ℂ => w z.re) (Complex.re ⁻¹' I) := by
    simpa [w] using hu.add
      (plurisubharmonicOn_coe_affine_re (-p) (-q) (Complex.re ⁻¹' I))
  have hwa : w a = 0 := by
    rw [show w a = v a + (((-p) * a + (-q) : ℝ) : EReal) by rfl,
      ← EReal.coe_toReal ha_top ha_bot, ← EReal.coe_add]
    apply EReal.coe_eq_coe_iff.mpr
    dsimp [q, A]
    ring
  have hwb : w b = 0 := by
    rw [show w b = v b + (((-p) * b + (-q) : ℝ) : EReal) by rfl,
      ← EReal.coe_toReal hb_top hb_bot, ← EReal.coe_add]
    apply EReal.coe_eq_coe_iff.mpr
    dsimp [q, p, A, B]
    field_simp [hba]
    ring
  have hwt : w t = (((v t).toReal + ((-p) * t + (-q)) : ℝ) : EReal) := by
    calc
      w t = v t + (((-p) * t + (-q) : ℝ) : EReal) := rfl
      _ = ((v t).toReal : EReal) + (((-p) * t + (-q) : ℝ) : EReal) := by
        rw [EReal.coe_toReal ht_top ht_bot]
      _ = (((v t).toReal + ((-p) * t + (-q)) : ℝ) : EReal) :=
        (EReal.coe_add _ _).symm
  rw [show (v a).toReal + (t - a) * ((v b).toReal - (v a).toReal) / (b - a) =
      A + (t - a) * p by dsimp [A, B, p]; ring]
  by_contra hle
  have hlt : A + (t - a) * p < (v t).toReal := lt_of_not_ge hle
  have hline : p * t + q = A + (t - a) * p := by
    dsimp [q]
    ring
  have hposR : 0 < (v t).toReal + ((-p) * t + (-q)) := by linarith
  have hwtpos : (0 : EReal) < w t := by
    rw [hwt]
    exact EReal.coe_pos.mpr hposR
  have hwusc : UpperSemicontinuousOn w (Icc a b) := by
    have hmap : MapsTo (fun y : ℝ => (y : ℂ)) (Icc a b) (Complex.re ⁻¹' I) := by
      intro y hy
      simpa using habI hy
    simpa [Function.comp_def] using
      hwpsh.upperSemicontinuousOn.comp Complex.continuous_ofReal.continuousOn hmap
  obtain ⟨x, hx, hxmax⟩ := hwusc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨t, hat.le, htb.le⟩) isCompact_Icc
  have htx : w t ≤ w x := hxmax ⟨hat.le, htb.le⟩
  have hxbot : w x ≠ ⊥ := ne_bot_of_gt (hwtpos.trans_le htx)
  have hxtop : w x ≠ ⊤ :=
    (hwpsh (x : ℂ) (by simpa using habI hx)).ne_top
  let C : ℝ := (w x).toReal
  have hxcoe : w x = (C : EReal) := (EReal.coe_toReal hxtop hxbot).symm
  have hCpos : (0 : EReal) < (C : EReal) := by
    rw [← hxcoe]
    exact hwtpos.trans_le htx
  have hxa : x ≠ a := by
    intro h
    subst x
    rw [hwa] at hxcoe
    exact (ne_of_lt hCpos) hxcoe
  have hxb : x ≠ b := by
    intro h
    subst x
    rw [hwb] at hxcoe
    exact (ne_of_lt hCpos) hxcoe
  have hxIoo : x ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  exact hwpsh.comp_re_no_finite_strict_interior_max habI hxIoo
    (fun y hy => by simpa [hxcoe] using hxmax hy) hxcoe
    (by simpa [hwa] using hCpos) (by simpa [hwb] using hCpos)

/-- EReal-valued chord inequality for three finite values. The coefficients are
ordinary real barycentric coordinates, coerced only after they are formed. -/
theorem PlurisubharmonicOn.comp_re_le_chord
    {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ => v z.re) (Complex.re ⁻¹' I))
    {a t b : ℝ} (hat : a < t) (htb : t < b) (habI : Icc a b ⊆ I)
    (ha_top : v a ≠ ⊤) (ha_bot : v a ≠ ⊥)
    (ht_top : v t ≠ ⊤) (ht_bot : v t ≠ ⊥)
    (hb_top : v b ≠ ⊤) (hb_bot : v b ≠ ⊥) :
    v t ≤ (((b - t) / (b - a) : ℝ) : EReal) * v a +
      (((t - a) / (b - a) : ℝ) : EReal) * v b := by
  have hab : a < b := hat.trans htb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hreal := hu.comp_re_toReal_le_affine_chord hat htb habI
    ha_top ha_bot ht_top ht_bot hb_top hb_bot
  have hweight :
      (v a).toReal + (t - a) * ((v b).toReal - (v a).toReal) / (b - a) =
        (b - t) / (b - a) * (v a).toReal +
          (t - a) / (b - a) * (v b).toReal := by
    field_simp [hba]
    ring
  rw [hweight] at hreal
  calc
    v t = ((v t).toReal : EReal) := (EReal.coe_toReal ht_top ht_bot).symm
    _ ≤ (((b - t) / (b - a) * (v a).toReal +
        (t - a) / (b - a) * (v b).toReal : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hreal
    _ = (((b - t) / (b - a) : ℝ) : EReal) * ((v a).toReal : EReal) +
        (((t - a) / (b - a) : ℝ) : EReal) * ((v b).toReal : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    _ = (((b - t) / (b - a) : ℝ) : EReal) * v a +
        (((t - a) / (b - a) : ℝ) : EReal) * v b := by
      rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]

end SGPT.Foundations.Analysis
