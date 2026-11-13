/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3934T1ArcSide
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Module

-- [TABLET NODE: P3934T1ArcSideComparison]

/-!
# P3934T1ArcSideComparison

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ArcComparisonGeometry

private theorem reverseLocal :
    (∀ (k : Bool), ∀ (x : Real), (if k then 0 < x else x < 0) ↔ (if !k then 0 < -x else -x < 0))
        → (∀ (W : Set (Real × Real)), ∀ (z : Real × Real), ∀ (B : Real × Real), ∀ (k : Bool),
            P3934T1LocalSide W z B k → P3934T1LocalSide W z (-B) (!k)) := by
  classical
  intro negSign W z B k h
  rcases h with ⟨r, hr, heq⟩
  refine ⟨r, hr, ?_⟩
  apply Set.ext
  intro q
  change q ∈ W ∩ Metric.ball z r ↔ q ∈ Metric.ball z r ∧ _
  rw [heq]
  simp only [Set.mem_ofPred_eq]
  have hd : (-B).1 * (q.2 - z.2) - (-B).2 * (q.1 - z.1) =
      -(B.1 * (q.2 - z.2) - B.2 * (q.1 - z.1)) := by
    rw [Prod.fst_neg, Prod.snd_neg]
    ring
  rw [hd]
  apply and_congr_right
  intro _
  exact negSign k (B.1 * (q.2 - z.2) - B.2 * (q.1 - z.1))

private theorem hscale (xL xR r1 r2 : ℝ) (Bg Bh : ℝ × ℝ)
    (hr12 : r1 < r2) (hvel : (xR - xL) • Bg = (r2 - r1) • Bh) :
    Bh = ((xR - xL) / (r2 - r1)) • Bg := by
  have hden : r2 - r1 ≠ 0 := ne_of_gt (sub_pos.mpr hr12)
  calc
    Bh = ((r2 - r1)⁻¹ * (r2 - r1)) • Bh := by simp [hden]
    _ = (r2 - r1)⁻¹ • ((r2 - r1) • Bh) := by rw [smul_smul]
    _ = (r2 - r1)⁻¹ • ((xR - xL) • Bg) := by rw [← hvel]
    _ = ((xR - xL) / (r2 - r1)) • Bg := by rw [smul_smul, div_eq_mul_inv, mul_comm]

private theorem localResult (U₁ U₂ : Set (ℝ × ℝ)) (e d : Bool)
    (z Bg Bh : ℝ × ℝ) (scale : ℝ) (hBg : Bg ≠ 0)
    (hscale_pos : 0 < scale) (hscale : Bh = scale • Bg)
    (hlocG : P3934T1LocalSide U₁ z Bg e) (hlocH : P3934T1LocalSide U₂ z Bh d) :
    (U₁ = U₂ → e = d) ∧ (Disjoint U₁ U₂ → e ≠ d) := by
  rcases hlocG with ⟨r, hr, hEqU⟩
  rcases hlocH with ⟨s, hs, hEqV⟩
  let v : Real × Real := (-Bg.2, Bg.1)
  obtain ⟨eps, heps, hbound⟩ := exists_pos_mul_lt (lt_min hr hs) ‖v‖
  have hbound' : eps * ‖v‖ < min r s := by simpa [mul_comm] using hbound
  let qplus : Real × Real := z + eps • v
  let qminus : Real × Real := z - eps • v
  have hdistPlus : dist qplus z = eps * ‖v‖ := by
    rw [dist_eq_norm]
    simp [qplus, norm_smul, Real.norm_eq_abs, abs_of_pos heps]
  have hdistMinus : dist qminus z = eps * ‖v‖ := by
    rw [dist_eq_norm]
    simp [qminus, norm_smul, Real.norm_eq_abs, abs_of_pos heps]
  have hballPlusU : qplus ∈ Metric.ball z r := by
    change dist qplus z < r
    rw [hdistPlus]
    exact lt_of_lt_of_le hbound' (min_le_left r s)
  have hballPlusV : qplus ∈ Metric.ball z s := by
    change dist qplus z < s
    rw [hdistPlus]
    exact lt_of_lt_of_le hbound' (min_le_right r s)
  have hballMinusU : qminus ∈ Metric.ball z r := by
    change dist qminus z < r
    rw [hdistMinus]
    exact lt_of_lt_of_le hbound' (min_le_left r s)
  have hballMinusV : qminus ∈ Metric.ball z s := by
    change dist qminus z < s
    rw [hdistMinus]
    exact lt_of_lt_of_le hbound' (min_le_right r s)
  have hsum : 0 < Bg.1 ^ 2 + Bg.2 ^ 2 := by
    have hc : Bg.1 ≠ 0 ∨ Bg.2 ≠ 0 := by
      by_contra hh
      push Not at hh
      apply hBg
      ext <;> simp [hh.1, hh.2]
    rcases hc with hc | hc
    · have hp := sq_pos_of_ne_zero hc
      nlinarith [sq_nonneg Bg.2]
    · have hp := sq_pos_of_ne_zero hc
      nlinarith [sq_nonneg Bg.1]
  have hdetPlus : Bg.1 * (qplus.2 - z.2) - Bg.2 * (qplus.1 - z.1) =
      eps * (Bg.1 ^ 2 + Bg.2 ^ 2) := by
    simp [qplus, v]
    ring
  have hdetMinus : Bg.1 * (qminus.2 - z.2) - Bg.2 * (qminus.1 - z.1) =
      -(eps * (Bg.1 ^ 2 + Bg.2 ^ 2)) := by
    simp [qminus, v]
    ring
  have hdetPlusPos : 0 < Bg.1 * (qplus.2 - z.2) - Bg.2 * (qplus.1 - z.1) := by
    rw [hdetPlus]
    exact mul_pos heps hsum
  have hdetMinusNeg : Bg.1 * (qminus.2 - z.2) - Bg.2 * (qminus.1 - z.1) < 0 := by
    rw [hdetMinus]
    nlinarith [mul_pos heps hsum]
  have hdetScalePlus : Bh.1 * (qplus.2 - z.2) - Bh.2 * (qplus.1 - z.1) =
      scale * (Bg.1 * (qplus.2 - z.2) - Bg.2 * (qplus.1 - z.1)) := by
    rw [hscale]
    change scale * Bg.1 * (qplus.2 - z.2) - scale * Bg.2 * (qplus.1 - z.1) = _
    ring
  have hdetScaleMinus : Bh.1 * (qminus.2 - z.2) - Bh.2 * (qminus.1 - z.1) =
      scale * (Bg.1 * (qminus.2 - z.2) - Bg.2 * (qminus.1 - z.1)) := by
    rw [hscale]
    change scale * Bg.1 * (qminus.2 - z.2) - scale * Bg.2 * (qminus.1 - z.1) = _
    ring
  have hdetVPlus : 0 < Bh.1 * (qplus.2 - z.2) - Bh.2 * (qplus.1 - z.1) := by
    rw [hdetScalePlus]
    exact mul_pos hscale_pos hdetPlusPos
  have hdetVMinus : Bh.1 * (qminus.2 - z.2) - Bh.2 * (qminus.1 - z.1) < 0 := by
    rw [hdetScaleMinus]
    exact mul_neg_of_pos_of_neg hscale_pos hdetMinusNeg
  have sideMem {W : Set (Real × Real)} {w b : Real × Real} {k : Bool} {R : Real}
      (heq : W ∩ Metric.ball w R =
        {x | x ∈ Metric.ball w R ∧
          if k then 0 < b.1 * (x.2 - w.2) - b.2 * (x.1 - w.1)
          else b.1 * (x.2 - w.2) - b.2 * (x.1 - w.1) < 0})
      (x : Real × Real) (hx : x ∈ Metric.ball w R) :
      x ∈ W ↔ if k then 0 < b.1 * (x.2 - w.2) - b.2 * (x.1 - w.1)
        else b.1 * (x.2 - w.2) - b.2 * (x.1 - w.1) < 0 := by
    have hm := congrArg (fun T : Set (Real × Real) => x ∈ T) heq
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hm
    simpa [hx] using hm
  have hplusU : qplus ∈ U₁ ↔
      (if e then 0 < Bg.1 * (qplus.2 - z.2) - Bg.2 * (qplus.1 - z.1)
        else Bg.1 * (qplus.2 - z.2) - Bg.2 * (qplus.1 - z.1) < 0) := by
    exact sideMem hEqU qplus hballPlusU
  have hminusU : qminus ∈ U₁ ↔
      (if e then 0 < Bg.1 * (qminus.2 - z.2) - Bg.2 * (qminus.1 - z.1)
        else Bg.1 * (qminus.2 - z.2) - Bg.2 * (qminus.1 - z.1) < 0) := by
    exact sideMem hEqU qminus hballMinusU
  have hplusV : qplus ∈ U₂ ↔
      (if d then 0 < Bh.1 * (qplus.2 - z.2) - Bh.2 * (qplus.1 - z.1)
        else Bh.1 * (qplus.2 - z.2) - Bh.2 * (qplus.1 - z.1) < 0) := by
    exact sideMem hEqV qplus hballPlusV
  have hminusV : qminus ∈ U₂ ↔
      (if d then 0 < Bh.1 * (qminus.2 - z.2) - Bh.2 * (qminus.1 - z.1)
        else Bh.1 * (qminus.2 - z.2) - Bh.2 * (qminus.1 - z.1) < 0) := by
    exact sideMem hEqV qminus hballMinusV
  constructor
  · intro hset
    subst U₂
    cases e <;> cases d
    · rfl
    · have hm : qplus ∈ U₁ := (hplusV).2 (by simp [hdetVPlus])
      have hn : qplus ∉ U₁ := by
        intro hh
        have hh' := (hplusU).1 hh
        simp at hh'
        linarith [hdetPlusPos]
      exact False.elim (hn hm)
    · have hm : qplus ∈ U₁ := (hplusU).2 (by simp [hdetPlusPos])
      have hn : qplus ∉ U₁ := by
        intro hh
        have hh' := (hplusV).1 hh
        simp at hh'
        linarith [hdetVPlus]
      exact False.elim (hn hm)
    · rfl
  · intro hdisj heq
    subst d
    cases e
    · have hu : qminus ∈ U₁ := (hminusU).2 (by simp [hdetMinusNeg])
      have hv : qminus ∈ U₂ := (hminusV).2 (by simp [hdetVMinus])
      exact (Set.disjoint_left.mp hdisj) hu hv
    · have hu : qplus ∈ U₁ := (hplusU).2 (by simp [hdetPlusPos])
      have hv : qplus ∈ U₂ := (hplusV).2 (by simp [hdetVPlus])
      exact (Set.disjoint_left.mp hdisj) hu hv

private theorem grange :
    ∀ (S : Set (Real × Real)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (Set.range g
        = S) → (
    let flip : Set.Icc (0 : Real) 1 → Set.Icc (0 : Real) 1 := fun t =>
      ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    ∀ (flip_invol : Function.Involutive flip), ∀ (flip_cont : Continuous flip),
    let flipEquiv :
        Set.Icc (0 : Real) 1 ≃ Set.Icc (0 : Real) 1 :=
      { toFun := flip
        invFun := flip
        left_inv := flip_invol
        right_inv := flip_invol }
    let flipHomeo := Continuous.homeoOfEquivCompactToT2 (f := flipEquiv) flip_cont
    let gr : Set.Icc (0 : Real) 1 → Real × Real := fun t => g (flipHomeo t)
    Set.range gr = S) := by
  classical
  intro S g hgrange flip flip_invol flip_cont flipEquiv flipHomeo gr
  apply Set.ext
  intro z
  constructor
  · rintro ⟨t, rfl⟩
    rw [← hgrange]
    exact ⟨flipHomeo t, rfl⟩
  · intro hz
    rw [← hgrange] at hz
    rcases hz with ⟨t, rfl⟩
    refine ⟨flipHomeo.symm t, ?_⟩
    change g (flipHomeo (flipHomeo.symm t)) = g t
    simp

private theorem hsr :
    ∀ (U : Set (Real × Real)), ∀ (e : Bool), (∀ (W : Set (Real × Real)), ∀ (z : Real × Real), ∀
        (B : Real × Real), ∀ (k : Bool), P3934T1LocalSide W z B k → P3934T1LocalSide W z (-B)
        (!k)) → (∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (s :
            P3723T1PolygonalParameterization g), (P3934T1PolygonalSide U g s e) → (
    let flip :
        Set.Icc (0 : Real) 1 → Set.Icc (0 : Real) 1 := fun t =>
      ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    ∀ (flip_invol : Function.Involutive flip), ∀ (flip_cont : Continuous flip),
    let flipEquiv :
        Set.Icc (0 : Real) 1 ≃ Set.Icc (0 : Real) 1 :=
      { toFun := flip
        invFun := flip
        left_inv := flip_invol
        right_inv := flip_invol }
    let flipHomeo := Continuous.homeoOfEquivCompactToT2 (f := flipEquiv) flip_cont
    ∀ (flipHomeo_apply : ∀ (t : Set.Icc (0 : Real) 1), flipHomeo t = flip t),
    let gr : Set.Icc (0
        : Real) 1 → Real × Real := fun t => g (flipHomeo t)
    let sr : P3723T1PolygonalParameterization gr := by
      refine ⟨s.count, s.positive, fun i => 1 - s.time i.rev, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        have hrev : j.rev < i.rev := by
          have := (Fin.rev_lt_iff (i := j) (j := i.rev)).2 (by simpa using hij)
          simpa using this
        exact sub_lt_sub_left (s.strict hrev) 1
      · simp [Fin.rev_zero, s.finish]
      · simp [Fin.rev_last, s.start]
      · intro i
        let j : Fin s.count := i.rev
        obtain ⟨A, B, hA⟩ := s.affine_on j
        refine ⟨A + B, -B, ?_⟩
        intro t hlow hupp
        have hlow' : s.time j.castSucc ≤ 1 - (t : Real) := by
          have hj : j.castSucc = i.succ.rev := by
            apply Fin.ext
            simp [j, Fin.rev_succ]
          rw [hj]
          exact (le_sub_iff_add_le).2 (by
            simpa [add_comm] using (le_sub_iff_add_le).1 hupp)
        have hupp' : 1 - (t : Real) ≤ s.time j.succ := by
          have hj : j.succ = i.castSucc.rev := by
            apply Fin.ext
            simp [j, Fin.rev_castSucc]
          rw [hj]
          exact (sub_le_iff_le_add).2 (by
            simpa [add_comm] using (sub_le_iff_le_add).1 hlow)
        let u : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1
            t.2.1⟩⟩
        have hseg' := hA u hlow' hupp'
        change g (flipHomeo t) = _
        rw [flipHomeo_apply]
        have hu' : u = flip t := by apply Subtype.ext; rfl
        rw [hu'] at hseg'
        rw [hseg']
        apply Prod.ext
        · change A.1 + (1 - (t : Real)) * B.1 = A.1 + B.1 + (t : Real) * (-B.1)
          ring
        · change A.2 + (1 - (t : Real)) * B.2 = A.2 + B.2 + (t : Real) * (-B.2)
          ring
    P3934T1PolygonalSide U gr sr (!e))) := by
  classical
  intro U e reverseLocal g s hs flip flip_invol flip_cont flipEquiv flipHomeo flipHomeo_apply gr
      sr i
  let j : Fin s.count := i.rev
  obtain ⟨A, B, hB, hseg, hside⟩ := hs j
  refine ⟨A + B, -B, ?_, ?_, ?_⟩
  · intro h
    exact (neg_ne_zero.mpr hB) h
  · intro t hlow hupp
    have hlow' : s.time j.castSucc ≤ 1 - (t : Real) := by
      have hj : j.castSucc = i.succ.rev := by
        simpa only [j] using (Fin.rev_succ i).symm
      change (t : Real) ≤ 1 - s.time i.succ.rev at hupp
      have htime : s.time j.castSucc = s.time i.succ.rev := congrArg s.time hj
      have ht : (t : Real) ≤ 1 - s.time j.castSucc := by rw [htime]; exact hupp
      apply (le_sub_iff_add_le).2
      rw [add_comm]
      exact (le_sub_iff_add_le).1 ht
    have hupp' : 1 - (t : Real) ≤ s.time j.succ := by
      have hj : j.succ = i.castSucc.rev := by
        simpa only [j] using (Fin.rev_castSucc i).symm
      change 1 - s.time i.castSucc.rev ≤ (t : Real) at hlow
      have htime : s.time j.succ = s.time i.castSucc.rev := congrArg s.time hj
      have ht : 1 - s.time j.succ ≤ (t : Real) := by rw [htime]; exact hlow
      apply (sub_le_iff_le_add).2
      rw [add_comm]
      exact (sub_le_iff_le_add).1 ht
    let u : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    have hloc := hseg u hlow' hupp'
    change g (flipHomeo t) = _
    rw [flipHomeo_apply]
    have hu' : u = flip t := by apply Subtype.ext; rfl
    rw [hu'] at hloc
    rw [hloc]
    apply Prod.ext
    · change A.1 + (1 - (t : Real)) * B.1 = A.1 + B.1 + (t : Real) * (-B.1)
      ring
    · change A.2 + (1 - (t : Real)) * B.2 = A.2 + B.2 + (t : Real) * (-B.2)
      ring
  · intro t hlow hupp
    have hlow' : s.time j.castSucc < 1 - (t : Real) := by
      have hj : j.castSucc = i.succ.rev := by
        simpa only [j] using (Fin.rev_succ i).symm
      have hsrtime : sr.time i.succ = 1 - s.time i.succ.rev := rfl
      rw [hsrtime, ← hj] at hupp
      have ht : (t : Real) < 1 - s.time j.castSucc := hupp
      apply (lt_sub_iff_add_lt).2
      rw [add_comm]
      exact (lt_sub_iff_add_lt).1 ht
    have hupp' : 1 - (t : Real) < s.time j.succ := by
      have hj : j.succ = i.castSucc.rev := by
        simpa only [j] using (Fin.rev_castSucc i).symm
      have hsrtime : sr.time i.castSucc = 1 - s.time i.castSucc.rev := rfl
      rw [hsrtime, ← hj] at hlow
      have ht : 1 - s.time j.succ < (t : Real) := hlow
      apply (sub_lt_iff_lt_add).2
      rw [add_comm]
      exact (sub_lt_iff_lt_add).1 ht
    let u : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    have hloc := hside u hlow' hupp'
    have hneg := reverseLocal U (g u) B e hloc
    have hflip : flipHomeo t = u := by apply Subtype.ext; rfl
    change P3934T1LocalSide U (g (flipHomeo t)) (-B) (!e)
    rw [hflip]
    exact hneg

end ArcComparisonGeometry

namespace ArcComparisonMainProof

private theorem negSign :
    ∀ (k : Bool), ∀ (x : Real), (if k then 0 < x else x < 0) ↔
        (if !k then 0 < -x else -x < 0) := by
  classical
  intro k x
  cases k <;> simp [Bool.not]

namespace ArcComparisonCoreFacts

private theorem hgfun_surj :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (hgrange :
        Set.range g = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    Function.Surjective gfun := by
  classical
  intro S g hgrange gfun z
  have hz : (z : Real × Real) ∈ Set.range g := by
    rw [hgrange]
    exact z.property
  rcases hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

private abbrev hhfun_surj :=
  ApollonianSuperharmonic.ArcComparisonMainProof.ArcComparisonCoreFacts.hgfun_surj

end ArcComparisonCoreFacts

private theorem compareCore :
    ∀ (S : Set (Real × Real)), ∀ (a : Real × Real), ∀ (b : Real × Real), ∀ (e : Bool), ∀ (d :
        Bool), ∀ (U₁ : Set (Real × Real)), ∀ (U₂ : Set (Real × Real)), ∀ (g : Set.Icc (0 : Real)
        1 → Real × Real), ∀ (h : Set.Icc (0 : Real) 1 → Real × Real), ∀ (p :
            P3723T1PolygonalParameterization g), ∀ (q : P3723T1PolygonalParameterization h),
            Continuous g → Function.Injective g → Set.range g = S →
      g ⟨0, by norm_num⟩ = a → g ⟨1, by norm_num⟩ = b →
      P3934T1PolygonalSide U₁ g p e →
      Continuous h → Function.Injective h → Set.range h = S →
      h ⟨0, by norm_num⟩ = a → h ⟨1, by norm_num⟩ = b →
      P3934T1PolygonalSide U₂ h q d →
      (U₁ = U₂ → e = d) ∧ (Disjoint U₁ U₂ → e ≠ d) := by
  classical
  intro S a b e d U₁ U₂ g h p q hgcont hginj hgrange hga hgb hps hhcont hhinj hhrange hha hhb hqs
  let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
    ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
  let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
    ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
  have hgfun_inj : Function.Injective gfun := by
    intro x y hxy
    apply hginj
    exact congrArg Subtype.val hxy
  have hhfun_inj : Function.Injective hfun := by
    intro x y hxy
    apply hhinj
    exact congrArg Subtype.val hxy
  have hgfun_surj : Function.Surjective gfun := ArcComparisonCoreFacts.hgfun_surj S g hgrange
  have hhfun_surj : Function.Surjective hfun := ArcComparisonCoreFacts.hhfun_surj S h hhrange
  let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
  let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
  have hgfun_cont : Continuous gfun := by
    apply Continuous.subtype_mk
    exact hgcont
  have hhfun_cont : Continuous hfun := by
    apply Continuous.subtype_mk
    exact hhcont
  let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
  let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
  let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
  have hGH (x : Set.Icc (0 : Real) 1) : GH x = gfun x := by rfl
  have hHH (x : Set.Icc (0 : Real) 1) : HH x = hfun x := by rfl
  have hrel (x : Set.Icc (0 : Real) 1) : h (phi x) = g x := by
    have hm : HH (phi x) = GH x := by simp [phi]
    have hv := congrArg Subtype.val hm
    rw [hHH, hGH] at hv
    exact hv
  let x0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
  let x1 : Set.Icc (0 : Real) 1 := ⟨1, by norm_num⟩
  have hphi0 : phi x0 = x0 := by
    apply hhinj
    rw [hrel, hga, hha]
  have hphi1 : phi x1 = x1 := by
    apply hhinj
    rw [hrel, hgb, hhb]
  have hphi_mono : StrictMono phi := (show
      StrictMono phi
    from by
      classical
      rcases phi.continuous.strictMono_of_inj phi.injective with hm | hm
      · exact hm
      · have h01 : x0 < x1 := by norm_num [x0, x1]
        have := hm h01
        rw [hphi0, hphi1] at this
        have hle : x0 ≤ x1 := by norm_num [x0, x1]
        exact False.elim ((not_lt_of_ge hle) this))
  let i0 : Fin p.count := ⟨0, p.positive⟩
  let j0 : Fin q.count := ⟨0, q.positive⟩
  let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
  let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
  have hi01 : (0 : Fin (p.count + 1)) < i1 := by
    change (0 : Nat) < 1
    norm_num
  have hj01 : (0 : Fin (q.count + 1)) < j1 := by
    change (0 : Nat) < 1
    norm_num
  have hpstart : p.time (0 : Fin (p.count + 1)) = 0 := p.start
  have hqstart : q.time (0 : Fin (q.count + 1)) = 0 := q.start
  have hpi : 0 < p.time i1 := by rw [← hpstart]; exact p.strict hi01
  have hqj : 0 < q.time j1 := by rw [← hqstart]; exact q.strict hj01
  have hpi1 : p.time i1 ≤ 1 := by
    rw [← p.finish]
    exact p.strict.monotone (Fin.le_last i1)
  have hqj1 : q.time j1 ≤ 1 := by
    rw [← q.finish]
    exact q.strict.monotone (Fin.le_last j1)
  let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
  let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
  have hx0a : x0 < α := by exact_mod_cast hpi
  have hφa : x0 < phi α := by
    have := hphi_mono hx0a
    simpa [hphi0] using this
  have hx0b : x0 < β := by exact_mod_cast hqj
  let c : Real := min (phi α : Real) (β : Real)
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min (by exact_mod_cast hφa) (by exact_mod_cast hx0b)
  have hc_le_a : c ≤ (phi α : Real) := min_le_left _ _
  have hc_le_b : c ≤ (β : Real) := min_le_right _ _
  have hc_le_one : c ≤ 1 := (hc_le_a.trans (phi α).property.2)
  let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
    ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
  let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
    ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
  have hr1pos : 0 < (r1 : Real) := by dsimp [r1]; linarith
  have hr12 : (r1 : Real) < (r2 : Real) := by dsimp [r1, r2]; linarith
  have hr2c : (r2 : Real) < c := by dsimp [r2]; linarith
  let xL : Set.Icc (0 : Real) 1 := phi.symm r1
  let xR : Set.Icc (0 : Real) 1 := phi.symm r2
  have hφL : phi xL = r1 := by simp [xL]
  have hφR : phi xR = r2 := by simp [xR]
  have hx0L : x0 < xL := by
    apply hphi_mono.lt_iff_lt.mp
    rw [hphi0, hφL]
    exact_mod_cast hr1pos
  have hxLa : xL < α := by
    apply hphi_mono.lt_iff_lt.mp
    rw [hφL]
    have hr1c : (r1 : Real) < c := by dsimp [r1]; linarith [hcpos]
    exact_mod_cast lt_of_lt_of_le hr1c hc_le_a
  have hxRa : xR < α := by
    apply hphi_mono.lt_iff_lt.mp
    rw [hφR]
    exact_mod_cast lt_of_lt_of_le hr2c hc_le_a
  have hxLR : xL < xR := by
    apply hphi_mono.lt_iff_lt.mp
    rw [hφL, hφR]
    exact_mod_cast hr12
  have hu1β : r1 < β := by
    have h : (r1 : Real) < (β : Real) := lt_of_lt_of_le (by dsimp [r1]; linarith [hcpos]) hc_le_b
    exact_mod_cast h
  have hu2β : r2 < β := by
    have h : (r2 : Real) < (β : Real) := lt_of_lt_of_le hr2c hc_le_b
    exact_mod_cast h
  have hplowL : p.time i0.castSucc ≤ (xL : Real) := by
    rw [show i0.castSucc = (0 : Fin (p.count + 1)) by rfl, hpstart]
    exact xL.property.1
  have hplowR : p.time i0.castSucc ≤ (xR : Real) := by
    rw [show i0.castSucc = (0 : Fin (p.count + 1)) by rfl, hpstart]
    exact xR.property.1
  have hiSucc : i0.succ = i1 := by apply Fin.ext; rfl
  have hiCast : i0.castSucc = (0 : Fin (p.count + 1)) := by apply Fin.ext; rfl
  have hjSucc : j0.succ = j1 := by apply Fin.ext; rfl
  have hjCast : j0.castSucc = (0 : Fin (q.count + 1)) := by apply Fin.ext; rfl
  have hpupL : (xL : Real) ≤ p.time i0.succ := by
    rw [hiSucc]
    exact_mod_cast hxLa.le
  have hpupR : (xR : Real) ≤ p.time i0.succ := by
    rw [hiSucc]
    exact_mod_cast hxRa.le
  have hqLow1 : q.time j0.castSucc ≤ (r1 : Real) := by
    rw [hjCast, hqstart]
    exact r1.property.1
  have hqLow2 : q.time j0.castSucc ≤ (r2 : Real) := by
    rw [hjCast, hqstart]
    exact r2.property.1
  have hqUp1 : (r1 : Real) ≤ q.time j0.succ := by
    rw [hjSucc]
    exact hu1β.le
  have hqUp2 : (r2 : Real) ≤ q.time j0.succ := by
    rw [hjSucc]
    exact hu2β.le
  obtain ⟨Ag, Bg, hBg, hgline, hgside⟩ := hps i0
  obtain ⟨Ah, Bh, hBh, hhline, hhside⟩ := hqs j0
  have hgL := hgline xL hplowL hpupL
  have hgR := hgline xR hplowR hpupR
  have hhL := hhline r1 hqLow1 hqUp1
  have hhR := hhline r2 hqLow2 hqUp2
  have hEqL : Ag + (xL : Real) • Bg = Ah + (r1 : Real) • Bh :=
    hgL.symm.trans ((hrel xL).symm.trans ((congrArg h hφL).trans hhL))
  have hEqR : Ag + (xR : Real) • Bg = Ah + (r2 : Real) • Bh :=
    hgR.symm.trans ((hrel xR).symm.trans ((congrArg h hφR).trans hhR))
  have hvel : ((xR : Real) - (xL : Real)) • Bg = ((r2 : Real) - (r1 : Real)) • Bh := by
    calc
      ((xR : Real) - (xL : Real)) • Bg =
          (Ag + (xR : Real) • Bg) - (Ag + (xL : Real) • Bg) := by module
      _ = (Ah + (r2 : Real) • Bh) - (Ah + (r1 : Real) • Bh) := by rw [hEqR, hEqL]
      _ = ((r2 : Real) - (r1 : Real)) • Bh := by module
  let scale : Real := ((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 : Real))
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact div_pos (sub_pos.mpr (by exact_mod_cast hxLR)) (sub_pos.mpr hr12)
  have hscale := ArcComparisonGeometry.hscale (xL : Real) (xR : Real) (r1 : Real) (r2 : Real)
    Bg Bh hr12 hvel
  let z : Real × Real := g xL
  have hplowLstrict : p.time i0.castSucc < (xL : Real) := by
    rw [hiCast, hpstart]
    exact_mod_cast hx0L
  have hpupLstrict : (xL : Real) < p.time i0.succ := by
    rw [hiSucc]
    exact_mod_cast hxLa
  have hqLow1strict : q.time j0.castSucc < (r1 : Real) := by
    rw [hjCast, hqstart]
    exact_mod_cast hr1pos
  have hqUp1strict : (r1 : Real) < q.time j0.succ := by
    rw [hjSucc]
    exact hu1β
  have hlocG : P3934T1LocalSide U₁ z Bg e := by
    change P3934T1LocalSide U₁ (g xL) Bg e
    exact hgside xL hplowLstrict hpupLstrict
  have hlocH : P3934T1LocalSide U₂ z Bh d := by
    have hh := hhside r1 hqLow1strict hqUp1strict
    have hz : h r1 = g xL := by rw [← hφL, hrel]
    rw [hz] at hh
    change P3934T1LocalSide U₂ (g xL) Bh d at hh
    exact hh
  have localResult := ArcComparisonGeometry.localResult U₁ U₂ e d z Bg Bh scale hBg
    hscale_pos hscale hlocG hlocH
  exact localResult

end ArcComparisonMainProof

theorem P3934T1ArcSideComparison (U V S : Set (Real × Real))
    (a b : Real × Real) (e d : Bool) :
    (P3934T1ArcSide U S a b e → P3934T1ArcSide U S b a (!e)) ∧
    (P3934T1ArcSide U S a b e → P3934T1ArcSide U S a b d → e = d) ∧
    (Disjoint U V → P3934T1ArcSide U S a b e →
      P3934T1ArcSide V S a b d → e ≠ d) := by
-- BODY
  have negSign (k : Bool) (x : Real) :
      (if k then 0 < x else x < 0) ↔
        (if !k then 0 < -x else -x < 0) := ArcComparisonMainProof.negSign k x
  have reverseLocal := ArcComparisonGeometry.reverseLocal negSign
  have compareCore : ∀ (U₁ U₂ : Set (Real × Real))
      (g h : Set.Icc (0 : Real) 1 → Real × Real)
      (p : P3723T1PolygonalParameterization g)
      (q : P3723T1PolygonalParameterization h),
      Continuous g → Function.Injective g → Set.range g = S →
      g ⟨0, by norm_num⟩ = a → g ⟨1, by norm_num⟩ = b →
      P3934T1PolygonalSide U₁ g p e →
      Continuous h → Function.Injective h → Set.range h = S →
      h ⟨0, by norm_num⟩ = a → h ⟨1, by norm_num⟩ = b →
      P3934T1PolygonalSide U₂ h q d →
      (U₁ = U₂ → e = d) ∧ (Disjoint U₁ U₂ → e ≠ d) := ArcComparisonMainProof.compareCore S a b e d
  constructor
  · intro h
    rcases h with ⟨g, hgcont, hginj, hgrange, hga, hgb, s, hs⟩
    let flip : Set.Icc (0 : Real) 1 → Set.Icc (0 : Real) 1 := fun t =>
      ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    have flip_invol : Function.Involutive flip := by
      intro t
      apply Subtype.ext
      exact sub_sub_cancel 1 (t : Real)
    have flip_cont : Continuous flip := by
      dsimp [flip]
      apply Continuous.subtype_mk
      exact continuous_const.sub continuous_subtype_val
    let flipEquiv : Set.Icc (0 : Real) 1 ≃ Set.Icc (0 : Real) 1 :=
      { toFun := flip
        invFun := flip
        left_inv := flip_invol
        right_inv := flip_invol }
    let flipHomeo := Continuous.homeoOfEquivCompactToT2 (f := flipEquiv) flip_cont
    have flipHomeo_apply (t : Set.Icc (0 : Real) 1) : flipHomeo t = flip t := rfl
    let gr : Set.Icc (0 : Real) 1 → Real × Real := fun t => g (flipHomeo t)
    have grcont : Continuous gr := hgcont.comp flipHomeo.continuous
    have grinj : Function.Injective gr := by
      intro x y hxy
      apply flipHomeo.injective
      exact hginj hxy
    have grange := ArcComparisonGeometry.grange S g hgrange flip_invol flip_cont
    let r0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
    let r1 : Set.Icc (0 : Real) 1 := ⟨1, by norm_num⟩
    have flip0 : flipHomeo r0 = r1 := by
      apply Subtype.ext
      change 1 - (0 : Real) = 1
      norm_num
    have flip1 : flipHomeo r1 = r0 := by
      apply Subtype.ext
      change 1 - (1 : Real) = 0
      norm_num
    have hga' : gr ⟨0, by norm_num⟩ = b := by
      change g (flipHomeo r0) = b
      rw [flip0]
      exact hgb
    have hgb' : gr ⟨1, by norm_num⟩ = a := by
      change g (flipHomeo r1) = a
      rw [flip1]
      exact hga
    let sr : P3723T1PolygonalParameterization gr := by
      refine ⟨s.count, s.positive, fun i => 1 - s.time i.rev, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        have hrev : j.rev < i.rev := by
          have := (Fin.rev_lt_iff (i := j) (j := i.rev)).2 (by simpa using hij)
          simpa using this
        exact sub_lt_sub_left (s.strict hrev) 1
      · simp [Fin.rev_zero, s.finish]
      · simp [Fin.rev_last, s.start]
      · intro i
        let j : Fin s.count := i.rev
        obtain ⟨A, B, hA⟩ := s.affine_on j
        refine ⟨A + B, -B, ?_⟩
        intro t hlow hupp
        have hlow' : s.time j.castSucc ≤ 1 - (t : Real) := by
          have hj : j.castSucc = i.succ.rev := by
            apply Fin.ext
            simp [j, Fin.rev_succ]
          rw [hj]
          exact (le_sub_iff_add_le).2 (by
            simpa [add_comm] using (le_sub_iff_add_le).1 hupp)
        have hupp' : 1 - (t : Real) ≤ s.time j.succ := by
          have hj : j.succ = i.castSucc.rev := by
            apply Fin.ext
            simp [j, Fin.rev_castSucc]
          rw [hj]
          exact (sub_le_iff_le_add).2 (by
            simpa [add_comm] using (sub_le_iff_le_add).1 hlow)
        let u : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1
            t.2.1⟩⟩
        have hseg' := hA u hlow' hupp'
        change g (flipHomeo t) = _
        rw [flipHomeo_apply]
        have hu' : u = flip t := by apply Subtype.ext; rfl
        rw [hu'] at hseg'
        rw [hseg']
        apply Prod.ext
        · change A.1 + (1 - (t : Real)) * B.1 = A.1 + B.1 + (t : Real) * (-B.1)
          ring
        · change A.2 + (1 - (t : Real)) * B.2 = A.2 + B.2 + (t : Real) * (-B.2)
          ring
    have hsr := ArcComparisonGeometry.hsr U e reverseLocal
        g s hs flip_invol flip_cont flipHomeo_apply
    refine ⟨gr, grcont, grinj, grange, hga', hgb', sr, ?_⟩
    exact hsr
  · constructor
    · intro hU hV
      rcases hU with ⟨g, hgcont, hginj, hgrange, hga, hgb, p, hps⟩
      rcases hV with ⟨h, hhcont, hhinj, hhrange, hha, hhb, q, hqs⟩
      exact (compareCore U U g h p q hgcont hginj hgrange hga hgb hps
        hhcont hhinj hhrange hha hhb hqs).1 rfl
    · intro hdisj hU hV
      rcases hU with ⟨g, hgcont, hginj, hgrange, hga, hgb, p, hps⟩
      rcases hV with ⟨h, hhcont, hhinj, hhrange, hha, hhb, q, hqs⟩
      exact (compareCore U V g h p q hgcont hginj hgrange hga hgb hps
        hhcont hhinj hhrange hha hhb hqs).2 hdisj

end ApollonianSuperharmonic

end
