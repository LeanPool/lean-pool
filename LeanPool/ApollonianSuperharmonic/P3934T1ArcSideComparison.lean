/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3934T1ArcSide

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

private theorem hscale :
    ∀ (S : Set (Real × Real)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h :
        (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization
        g), ∀ (q : P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀
            (hhrange : Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH :=
        Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), ((c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1
        := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    ((r1 : Real) < (r2 : Real)) → (
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    ∀ (Bg : ℝ × ℝ), ∀ (Bh : ℝ × ℝ), (((xR : Real) - (xL : Real)) • Bg = ((r2 : Real) - (r1 :
        Real)) • Bh) → (
    let scale : Real := ((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 :
        Real))
    Bh = scale • Bg)))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_b hc_le_one r1 r2
      hr12 xL xR Bg Bh hvel scale
  have hfst := congrArg Prod.fst hvel
  have hsnd := congrArg Prod.snd hvel
  change ((xR : Real) - (xL : Real)) * Bg.1 =
    ((r2 : Real) - (r1 : Real)) * Bh.1 at hfst
  change ((xR : Real) - (xL : Real)) * Bg.2 =
    ((r2 : Real) - (r1 : Real)) * Bh.2 at hsnd
  have hden : (r2 : Real) - (r1 : Real) ≠ 0 := ne_of_gt (sub_pos.mpr hr12)
  apply Prod.ext
  · change Bh.1 = scale * Bg.1
    dsimp [scale]
    calc
      Bh.1 = (((r2 : Real) - (r1 : Real)) * Bh.1) / ((r2 : Real) - (r1 : Real)) := by
        field_simp
      _ = (((xR : Real) - (xL : Real)) * Bg.1) / ((r2 : Real) - (r1 : Real)) := by rw [← hfst]
      _ = (((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 : Real))) * Bg.1 := by ring
  · change Bh.2 = scale * Bg.2
    dsimp [scale]
    calc
      Bh.2 = (((r2 : Real) - (r1 : Real)) * Bh.2) / ((r2 : Real) - (r1 : Real)) := by
        field_simp
      _ = (((xR : Real) - (xL : Real)) * Bg.2) / ((r2 : Real) - (r1 : Real)) := by rw [← hsnd]
      _ = (((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 : Real))) * Bg.2 := by ring

private theorem localResult :
    ∀ (S : Set (Real × Real)), ∀ (e : Bool), ∀ (d : Bool), ∀ (U₁ : Set (ℝ × ℝ)), ∀ (U₂ : Set (ℝ ×
        ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc (0 : ℝ) (1 :
        ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
            P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S),
            (P3934T1PolygonalSide U₁ g p e) → (∀ (hhrange : Set.range h = S),
            (P3934T1PolygonalSide U₂ h q d) → (
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH :=
        Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let i0 : Fin p.count := ⟨0, p.positive⟩
    let j0 : Fin q.count := ⟨0, q.positive⟩
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), ((c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1
        := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    ∀ (Bg : ℝ × ℝ), (Bg ≠ (0 : ℝ × ℝ)) → ((∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), p.time
        i0.castSucc < (↑t : ℝ) → (↑t : ℝ) < p.time i0.succ → P3934T1LocalSide U₁ (g t) Bg e) →
        (∀ (Bh : ℝ × ℝ), (∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), q.time j0.castSucc < (↑t :
        ℝ) → (↑t : ℝ) < q.time j0.succ → P3934T1LocalSide U₂ (h t) Bh d) → (
    let scale : Real :=
        ((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 : Real))
    (0 < scale) → ((Bh = scale • Bg) → (
    let z : Real × Real := g xL
    (P3934T1LocalSide U₁ z Bg e) → ((P3934T1LocalSide U₂ z Bh d) → ((U₁ = U₂ → e = d) ∧
        (Disjoint U₁ U₂ → e ≠ d)))))))))))) := by
  classical
  intro S e d U₁ U₂ g h p q hgrange hps hhrange hqs gfun hfun hgfun_inj hhfun_inj hgfun_surj
      hhfun_surj ge he hgfun_cont hhfun_cont GH HH phi i0 j0 i1 j1 hpi hqj hpi1 hqj1 α β c hcpos
      hc_le_b hc_le_one r1 r2 xL xR Bg hBg hgside Bh hhside scale hscale_pos hscale z hlocG hlocH
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

private theorem reverseLocal :
    (∀ (k : Bool), ∀ (x : Real), (if k then 0 < x else x < 0) ↔ (if !k then 0 < -x else -x < 0))
        → (∀ (W : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (B : ℝ × ℝ), ∀ (k : Bool), P3934T1LocalSide W
        z B k → P3934T1LocalSide W z (-B) !k) := by
  classical
  intro negSign
  exact ArcComparisonGeometry.reverseLocal negSign

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

private theorem hhfun_surj :
    ∀ (S : Set (ℝ × ℝ)), ∀ (h : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (hhrange :
        Set.range h = S),
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    Function.Surjective hfun := by
  classical
  intro S h hhrange hfun z
  have hz : (z : Real × Real) ∈ Set.range h := by
    rw [hhrange]
    exact z.property
  rcases hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

private theorem hphi_mono :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (hgrange : Set.range g = S), ∀ (hhrange : Set.range
        h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let x0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
    let x1 : Set.Icc (0 : Real) 1 := ⟨1, by norm_num⟩
    (phi x0 = x0) → ((phi x1 = x1) → (StrictMono phi)) := by
  classical
  intro S g h hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi x0 x1 hphi0 hphi1
  rcases phi.continuous.strictMono_of_inj phi.injective with hm | hm
  · exact hm
  · have h01 : x0 < x1 := by norm_num [x0, x1]
    have := hm h01
    rw [hphi0, hphi1] at this
    have hle : x0 ≤ x1 := by norm_num [x0, x1]
    exact False.elim ((not_lt_of_ge hle) this)

private theorem hx0L :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let x0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
    (phi x0 = x0) → ((StrictMono phi) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    (0 < (r1 : Real)) → (
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    (phi xL = r1) → (x0 < xL))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi x0 hphi0 hphi_mono i1 j1 hpi hqj hpi1 hqj1 α β c hcpos
      hc_le_b hc_le_one r1 hr1pos xL hφL
  by_contra hh
  have hle : xL ≤ x0 := le_of_not_gt hh
  have hm := hphi_mono.monotone hle
  rw [hφL, hphi0] at hm
  have h0r : x0 < r1 := by exact_mod_cast hr1pos
  exact (not_le_of_gt h0r) hm

private theorem hx0R :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let x0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
    (phi x0 = x0) → ((StrictMono phi) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    (0 < (r2 : Real)) → (
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    (phi xR = r2) → (x0 < xR))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi x0 hphi0 hphi_mono i1 j1 hpi hqj hpi1 hqj1 α β c hcpos
      hc_le_b hc_le_one r2 hr2pos xR hφR
  by_contra hh
  have hle : xR ≤ x0 := le_of_not_gt hh
  have hm := hphi_mono.monotone hle
  rw [hφR, hphi0] at hm
  have h0r : x0 < r2 := by exact_mod_cast hr2pos
  exact (not_le_of_gt h0r) hm

private theorem hxLa :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    (StrictMono phi) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (phi α : Real)) → ((c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    (0 < (r1 : Real)) → (((r1 : Real) < (r2 : Real)) → (((r2 : Real) < c) → (
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    (phi xL = r1) → (xL < α))))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi hphi_mono i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_a
      hc_le_b hc_le_one r1 r2 hr1pos hr12 hr2c xL hφL
  by_contra hh
  have hle : α ≤ xL := le_of_not_gt hh
  have hm := hphi_mono.monotone hle
  rw [hφL] at hm
  have hr1c : (r1 : Real) < c := by dsimp [r1]; linarith [hcpos]
  have hrc : (r1 : Real) < (phi α : Real) := lt_of_lt_of_le hr1c hc_le_a
  have hrc' : r1 < phi α := by exact_mod_cast hrc
  exact (not_le_of_gt hrc') hm

private theorem hxRa :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    (StrictMono phi) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (phi α : Real)) → ((c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    ((r2 : Real) < c) → (
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    (phi xR = r2) → (xR < α))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi hphi_mono i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_a
      hc_le_b hc_le_one r2 hr2c xR hφR
  by_contra hh
  have hle : α ≤ xR := le_of_not_gt hh
  have hm := hphi_mono.monotone hle
  rw [hφR] at hm
  have hrc : (r2 : Real) < (phi α : Real) := lt_of_lt_of_le hr2c hc_le_a
  have hrc' : r2 < phi α := by exact_mod_cast hrc
  exact (not_le_of_gt hrc') hm

private theorem hxLR :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    (StrictMono phi) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    ((r1 : Real) < (r2 : Real)) → (
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    (phi xL = r1) → ((phi xR = r2) → (xL < xR))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi hphi_mono i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_b
      hc_le_one r1 r2 hr12 xL xR hφL hφR
  by_contra hh
  have hle : xR ≤ xL := le_of_not_gt hh
  have hm := hphi_mono.monotone hle
  rw [hφR, hφL] at hm
  have hlt : r1 < r2 := by exact_mod_cast hr12
  exact (not_le_of_gt hlt) hm

private theorem hEqL :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    (∀ (x : Set.Icc (0 : Real) 1), h (phi x) = g x) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    (phi xL = r1) → (∀ (Ag : ℝ × ℝ), ∀ (Bg : ℝ × ℝ), ∀ (Ah : ℝ × ℝ), ∀ (Bh : ℝ × ℝ), (g xL = Ag +
        (↑xL : ℝ) • Bg) → ((h r1 = Ah + (↑r1 : ℝ) • Bh) → (Ag + (xL : Real) • Bg = Ah + (r1 :
        Real) • Bh))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi hrel i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_b hc_le_one
      r1 xL hφL Ag Bg Ah Bh hgL hhL
  calc
    Ag + (xL : Real) • Bg = g xL := hgL.symm
    _ = h (phi xL) := (hrel xL).symm
    _ = h r1 := by rw [hφL]
    _ = Ah + (r1 : Real) • Bh := hhL

private theorem hEqR :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    (∀ (x : Set.Icc (0 : Real) 1), h (phi x) = g x) → (
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    (phi xR = r2) → (∀ (Ag : ℝ × ℝ), ∀ (Bg : ℝ × ℝ), ∀ (Ah : ℝ × ℝ), ∀ (Bh : ℝ × ℝ), (g xR = Ag +
        (↑xR : ℝ) • Bg) → ((h r2 = Ah + (↑r2 : ℝ) • Bh) → (Ag + (xR : Real) • Bg = Ah + (r2 :
        Real) • Bh))))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi hrel i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_b hc_le_one
      r2 xR hφR Ag Bg Ah Bh hgR hhR
  calc
    Ag + (xR : Real) • Bg = g xR := hgR.symm
    _ = h (phi xR) := (hrel xR).symm
    _ = h r2 := by rw [hφR]
    _ = Ah + (r2 : Real) • Bh := hhR

private theorem hvel :
    ∀ (S : Set (ℝ × ℝ)), ∀ (g : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (h : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (p : P3723T1PolygonalParameterization g), ∀ (q :
        P3723T1PolygonalParameterization h), ∀ (hgrange : Set.range g = S), ∀ (hhrange :
        Set.range h = S),
    let gfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨g x, by rw [← hgrange]; exact ⟨x, rfl⟩⟩
    let hfun : Set.Icc (0 : Real) 1 → S := fun x =>
      ⟨h x, by rw [← hhrange]; exact ⟨x, rfl⟩⟩
    ∀ (hgfun_inj : Function.Injective gfun), ∀ (hhfun_inj : Function.Injective hfun), ∀
        (hgfun_surj : Function.Surjective gfun), ∀ (hhfun_surj : Function.Surjective hfun),
    let ge : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective gfun ⟨hgfun_inj, hgfun_surj⟩
    let he : Set.Icc (0 : Real) 1 ≃ S := Equiv.ofBijective hfun ⟨hhfun_inj, hhfun_surj⟩
    ∀ (hgfun_cont : Continuous gfun), ∀ (hhfun_cont : Continuous hfun),
    let GH := Continuous.homeoOfEquivCompactToT2 (f := ge) hgfun_cont
    let HH := Continuous.homeoOfEquivCompactToT2 (f := he) hhfun_cont
    let phi : Set.Icc (0 : Real) 1 ≃ₜ Set.Icc (0 : Real) 1 := GH.trans HH.symm
    let i1 : Fin (p.count + 1) := ⟨1, by have hp := p.positive; omega⟩
    let j1 : Fin (q.count + 1) := ⟨1, by have hq := q.positive; omega⟩
    ∀ (hpi : 0 < p.time i1), ∀ (hqj : 0 < q.time j1), ∀ (hpi1 : p.time i1 ≤ 1), ∀ (hqj1 : q.time
        j1 ≤ 1),
    let α : Set.Icc (0 : Real) 1 := ⟨p.time i1, hpi.le, hpi1⟩
    let β : Set.Icc (0 : Real) 1 := ⟨q.time j1, hqj.le, hqj1⟩
    let c : Real := min (phi α : Real) (β : Real)
    ∀ (hcpos : 0 < c), (c ≤ (β : Real)) → (∀ (hc_le_one : c ≤ 1),
    let r1 : Set.Icc (0 : Real) 1 := ⟨c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let r2 : Set.Icc (0 : Real) 1 := ⟨2 * c / 3,
      ⟨by linarith [hcpos], by have := hc_le_one; linarith⟩⟩
    let xL : Set.Icc (0 : Real) 1 := phi.symm r1
    let xR : Set.Icc (0 : Real) 1 := phi.symm r2
    ∀ (Ag : ℝ × ℝ), ∀ (Bg : ℝ × ℝ), ∀ (Ah : ℝ × ℝ), ∀ (Bh : ℝ × ℝ), (Ag + (xL : Real) • Bg = Ah +
        (r1 : Real) • Bh) → ((Ag + (xR : Real) • Bg = Ah + (r2 : Real) • Bh) → (((xR : Real) -
        (xL : Real)) • Bg = ((r2 : Real) - (r1 : Real)) • Bh))) := by
  classical
  intro S g h p q hgrange hhrange gfun hfun hgfun_inj hhfun_inj hgfun_surj hhfun_surj ge he
      hgfun_cont hhfun_cont GH HH phi i1 j1 hpi hqj hpi1 hqj1 α β c hcpos hc_le_b hc_le_one r1 r2
      xL xR Ag Bg Ah Bh hEqL hEqR
  calc
    ((xR : Real) - (xL : Real)) • Bg =
        (Ag + (xR : Real) • Bg) - (Ag + (xL : Real) • Bg) := by module
    _ = (Ah + (r2 : Real) • Bh) - (Ah + (r1 : Real) • Bh) := by rw [hEqR, hEqL]
    _ = ((r2 : Real) - (r1 : Real)) • Bh := by module

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
  have hphi_mono : StrictMono phi := ArcComparisonCoreFacts.hphi_mono S g h hgrange hhrange
      hgfun_inj hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi0 hphi1
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
  have hr2pos : 0 < (r2 : Real) := by dsimp [r2]; linarith
  have hr12 : (r1 : Real) < (r2 : Real) := by dsimp [r1, r2]; linarith
  have hr2c : (r2 : Real) < c := by dsimp [r2]; linarith
  let xL : Set.Icc (0 : Real) 1 := phi.symm r1
  let xR : Set.Icc (0 : Real) 1 := phi.symm r2
  have hφL : phi xL = r1 := by simp [xL]
  have hφR : phi xR = r2 := by simp [xR]
  have hx0L : x0 < xL := ArcComparisonCoreFacts.hx0L S g h p q hgrange hhrange hgfun_inj
      hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi0 hphi_mono hpi hqj hpi1 hqj1
      hcpos hc_le_b hc_le_one hr1pos hφL
  have hx0R : x0 < xR := ArcComparisonCoreFacts.hx0R S g h p q hgrange hhrange hgfun_inj
      hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi0 hphi_mono hpi hqj hpi1 hqj1
      hcpos hc_le_b hc_le_one hr2pos hφR
  have hxLa : xL < α := ArcComparisonCoreFacts.hxLa S g h p q hgrange hhrange hgfun_inj hhfun_inj
      hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi_mono hpi hqj hpi1 hqj1 hcpos hc_le_a
      hc_le_b hc_le_one hr1pos hr12 hr2c hφL
  have hxRa : xR < α := ArcComparisonCoreFacts.hxRa S g h p q hgrange hhrange hgfun_inj hhfun_inj
      hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi_mono hpi hqj hpi1 hqj1 hcpos hc_le_a
      hc_le_b hc_le_one hr2c hφR
  have hxLR : xL < xR := ArcComparisonCoreFacts.hxLR S g h p q hgrange hhrange hgfun_inj
      hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hphi_mono hpi hqj hpi1 hqj1 hcpos
      hc_le_b hc_le_one hr12 hφL hφR
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
  have hEqL : Ag + (xL : Real) • Bg = Ah + (r1 : Real) • Bh := ArcComparisonCoreFacts.hEqL S g h
      p q hgrange hhrange hgfun_inj hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hrel
      hpi hqj hpi1 hqj1 hcpos hc_le_b hc_le_one hφL Ag Bg Ah Bh hgL hhL
  have hEqR : Ag + (xR : Real) • Bg = Ah + (r2 : Real) • Bh := ArcComparisonCoreFacts.hEqR S g h
      p q hgrange hhrange hgfun_inj hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hrel
      hpi hqj hpi1 hqj1 hcpos hc_le_b hc_le_one hφR Ag Bg Ah Bh hgR hhR
  have hvel : ((xR : Real) - (xL : Real)) • Bg = ((r2 : Real) - (r1 : Real)) • Bh :=
      ArcComparisonCoreFacts.hvel S g h p q hgrange hhrange hgfun_inj hhfun_inj hgfun_surj
      hhfun_surj hgfun_cont hhfun_cont hpi hqj hpi1 hqj1 hcpos hc_le_b hc_le_one Ag Bg Ah Bh hEqL
      hEqR
  let scale : Real := ((xR : Real) - (xL : Real)) / ((r2 : Real) - (r1 : Real))
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact div_pos (sub_pos.mpr (by exact_mod_cast hxLR)) (sub_pos.mpr hr12)
  have hscale := ArcComparisonGeometry.hscale S g h p q hgrange hhrange
      hgfun_inj hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hpi hqj hpi1 hqj1 hcpos
      hc_le_b hc_le_one hr12 Bg Bh hvel
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
  have localResult := ArcComparisonGeometry.localResult S e d U₁ U₂ g h p q hgrange hps hhrange
      hqs hgfun_inj
      hhfun_inj hgfun_surj hhfun_surj hgfun_cont hhfun_cont hpi hqj hpi1 hqj1 hcpos hc_le_b
      hc_le_one Bg hBg hgside Bh hhside hscale_pos hscale hlocG hlocH
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
  have reverseLocal := ArcComparisonMainProof.reverseLocal negSign
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
