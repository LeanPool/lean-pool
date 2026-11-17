/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingStability
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingBelow
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingShift
public import Mathlib.Tactic.LinearCombination
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P5188T1E3E4Boundary]

/-!
# P5188T1E3E4Boundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5188T1E3E4Boundary (P P₂ : FordFareyParameter)
    (hq : 1 < P.q) (hp₂ : P₂.p = P.p₂) (hq₂ : P₂.q = P.q₂)
    (g₂ : IntegerLatticeFunction)
    (h₂ : ∀ x ∈ FordDoubledBoundary P₂.q,
      g₂ x = IntegerCeilDiv (P₂.p * x.re * x.im) P₂.q (by exact_mod_cast P₂.q_pos.ne')) :
    (∀ x : GaussianInt,
      (P.q₁ : Int) ≤ x.re ∧ x.re ≤ (P.q : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (P.q₂ : Int) →
      x ∈ FordDoubledBoundary P.q →
      g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im =
        IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne')) ∧
    (∀ x : GaussianInt,
      0 ≤ x.re ∧ x.re ≤ (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ x.im ∧ x.im ≤ (P.q : Int) →
      x ∈ FordDoubledBoundary P.q →
      g₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re =
        IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne')) := by
-- BODY
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have hps : P.p = P.p₁ + P.p₂ := P.sum_p
  have hcross := (P5130T5ParentArithmetic P hq).2.2.2.2.2.2
  have hdet₁ := P.det₁
  have hqpos : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
  have ha : 0 < (P.q₁ : Int) := by have := (P5130T5ParentArithmetic P hq).1; exact_mod_cast this
  have hb : 0 < (P.q₂ : Int) := by have := P.q₂_pos; exact_mod_cast this
  have hbb : (P.q₂ : Int) < P.q := by rw [hsum]; omega
  let a : Int := P.q₁
  let b : Int := P.q₂
  let A : Int := P.p₁
  let D : Int := P.p₂
  have haq : a + b = P.q := by dsimp [a, b]; exact hsum.symm
  have hpq : A + D = P.p := by dsimp [A, D]; exact hps.symm
  have hAq : A * P.q - a * P.p = 1 := by simpa [a, A] using hdet₁
  have hpqa : P.p * a = A * P.q - 1 := by
    have haux : A * P.q - P.p * a = 1 := by
      rw [mul_comm P.p a]
      exact hAq
    omega
  have hAB : A * b - D * a = 1 := by simpa [a, b, A, D] using hcross
  have ceilPerturb := P5188T1CeilingStability
  have ceilBelow := P5188T1CeilingBelow
  have ceilShift := P5188T1CeilingShift
  have ceilZero (d : Int) (hd : d ≠ 0) : IntegerCeilDiv 0 d hd = 0 := by
    simp [IntegerCeilDiv]
  have ceilMul (c t d : Int) (hd : d ≠ 0) :
      IntegerCeilDiv (c * d * t) d (by omega) = c * t := by
    dsimp only [IntegerCeilDiv]
    have he : -(c * d * t) = d * (-c * t) := by ring
    rw [he, Int.mul_ediv_cancel_left _ hd]
    ring
  have e3 (g₂ : IntegerLatticeFunction)
      (h₂ : ∀ x ∈ FordDoubledBoundary P₂.q,
        g₂ x = IntegerCeilDiv (P₂.p * x.re * x.im) P₂.q (by exact_mod_cast P₂.q_pos.ne'))
      (x : GaussianInt)
      (hdom : (P.q₁ : Int) ≤ x.re ∧ x.re ≤ (P.q : Int) ∧
        0 ≤ x.im ∧ x.im ≤ (P.q₂ : Int))
      (hbd : x ∈ FordDoubledBoundary P.q) :
      g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im =
        IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne') := by
    have g₂val (u v : Int) (hu0 : 0 ≤ u) (hu : u ≤ b)
        (hv0 : 0 ≤ v) (hv : v ≤ b)
        (hs : u = 0 ∨ u = 1 ∨ u = b - 1 ∨ u = b ∨
          v = 0 ∨ v = 1 ∨ v = b - 1 ∨ v = b) :
        g₂ ⟨u, v⟩ = IntegerCeilDiv (D * u * v) b (by omega) := by
      have hbd : (⟨u, v⟩ : GaussianInt) ∈ FordDoubledBoundary P₂.q := by
        change (0 ≤ u ∧ u ≤ (P₂.q : Int) ∧ 0 ≤ v ∧ v ≤ (P₂.q : Int)) ∧ _
        refine ⟨⟨hu0, ?_, hv0, ?_⟩, ?_⟩
        · simpa [b, hq₂] using hu
        · simpa [b, hq₂] using hv
        intro hi
        simp at hi
        rcases hs with h | h | h | h | h | h | h | h <;> omega
      simpa [b, D, hp₂, hq₂] using h₂ ⟨u, v⟩ hbd
    have hbox : x ∈ FordVertexDomain P.q := hbd.1
    have hside : x.re = 0 ∨ x.re = 1 ∨ x.re = (P.q : Int) - 1 ∨ x.re = P.q ∨
        x.im = 0 ∨ x.im = 1 ∨ x.im = (P.q : Int) - 1 ∨ x.im = P.q := by
      change x ∈ FordVertexDomain P.q ∧ _ at hbd
      rcases hbd with ⟨_, hn⟩
      simp only [FordVertexDomain] at hbox
      rcases hbox with ⟨hr0, hrq, hi0, hiq⟩
      by_contra hnside
      push Not at hnside
      apply hn
      exact ⟨by omega, by omega, by omega, by omega⟩
    change ((P.q₁ : Int) ≤ x.re ∧ x.re ≤ P.q ∧
      0 ≤ x.im ∧ x.im ≤ P.q₂) at hdom
    change g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im =
      IntegerCeilDiv (P.p * x.re * x.im) P.q _
    set r : Int := x.re - a with r_def
    set s : Int := x.im with s_def
    have hr0 : 0 ≤ r := by rw [r_def]; omega
    have hrs : r ≤ b := by rw [r_def]; omega
    have hs0 : 0 ≤ s := by rw [s_def]; omega
    have hsb : s ≤ b := by rw [s_def]; omega
    have hx : x = ⟨a + r, s⟩ := by ext <;> simp [r_def, s_def]
    have hshift : (⟨a + r, s⟩ : GaussianInt) - ⟨a, 0⟩ = ⟨r, s⟩ := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]
    rw [hx, hshift]
    change g₂ ⟨r, s⟩ + A * s = IntegerCeilDiv (P.p * (a + r) * s) P.q _
    have hE3data :
        (s = 0 ∨ s = 1 ∨ r = b ∨ r = b - 1 ∨
          (r = 0 ∧ a = 1) ∨ (s = b ∧ a = 1)) ∧
        (r = 0 ∨ r = 1 ∨ r = b - 1 ∨ r = b ∨
          s = 0 ∨ s = 1 ∨ s = b - 1 ∨ s = b) := by
      rcases hside with hr | hr | hr | hr | hi | hi | hi | hi
      · omega
      · have ha1 : a = 1 := by omega
        have hr0' : r = 0 := by omega
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hr0', ha1⟩)))),
          Or.inl hr0'⟩
      · have hrb1 : r = b - 1 := by omega
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hrb1))),
          Or.inr (Or.inr (Or.inl hrb1))⟩
      · have hrb : r = b := by omega
        exact ⟨Or.inr (Or.inr (Or.inl hrb)), Or.inr (Or.inr (Or.inr (Or.inl hrb)))⟩
      · exact ⟨Or.inl hi, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))⟩
      · exact ⟨Or.inr (Or.inl hi), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi)))))⟩
      · have ha1 : a = 1 := by dsimp [a]; omega
        have hsb' : s = b := by rw [s_def]; omega
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hsb', ha1⟩)))),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsb'))))))⟩
      · omega
    have hparentVal : g₂ ⟨r, s⟩ = IntegerCeilDiv (D * r * s) b hb.ne' :=
      g₂val r s hr0 hrs hs0 hsb hE3data.2
    rw [hparentVal]
    rcases hE3data.1 with hs0' | hs1 | hrb | hrb1 | ⟨hrzero, ha1⟩ | ⟨hsb', ha1⟩
    · simp only [hs0', mul_zero, ceilZero, zero_add]
    · simp only [hs1, mul_one]
      have hrel : (P.p * r - 1) * b = D * r * P.q - (b - r) := by
        rw [← hpq, ← haq]
        linear_combination r * hAB
      have hmain := ceilPerturb (D * r) (P.p * r - 1) b P.q (b - r)
        hb hbb (by omega) (by omega) hrel
      have hmove : P.p * (a + r) = (P.p * r - 1) + A * P.q := by
        rw [Int.mul_add, hpqa]
        omega
      rw [hmove, ceilShift (P.p * r - 1) A P.q hqpos.ne', hmain]
    · rw [hrb, show a + b = (P.q : Int) from haq,
        ceilMul D s b hb.ne', ceilMul P.p s P.q hqpos.ne', ← hpq]
      ring
    · rw [hrb1, show a + (b - 1) = (P.q : Int) - 1 by omega]
      let M : Int := P.p * (P.q - 1) * s - A * s * P.q
      have hrel : M * b = (D * (b - 1) * s) * P.q - s := by
        dsimp [M]
        rw [← hpq, ← haq]
        linear_combination -s * hAB
      have hmain := ceilPerturb (D * (b - 1) * s) M b P.q s
        hb hbb hs0 hsb hrel
      have hmove : P.p * (P.q - 1) * s = M + (A * s) * P.q := by
        dsimp [M]
        ring
      rw [hmove, ceilShift M (A * s) P.q hqpos.ne', hmain]
    · have hpunit : P.p = A * P.q - 1 := by
        rw [ha1] at hpqa
        simpa using hpqa
      have hnum : P.p * (a + r) * s = (A * s) * P.q - s := by
        rw [ha1, hrzero, hpunit]
        ring
      rw [hnum, ceilBelow (A * s) s P.q hqpos hs0 (by omega)]
      simp only [hrzero, mul_zero, zero_mul, ceilZero, zero_add]
    · have hDa : D = A * b - 1 := by rw [ha1] at hAB; nlinarith [hAB]
      have hq1 : (P.q : Int) = b + 1 := by rw [ha1] at haq; omega
      have hp1 : P.p = A * P.q - 1 := by rw [ha1] at hpqa; simpa using hpqa
      have htopnum : P.p * (1 + r) * b =
          (D * r + A * b - 1) * P.q + (1 + r) := by
        rw [hp1, hDa, hq1]
        ring
      have htop := ceilBelow ((D * r + A * b - 1) + 1) ((P.q : Int) - (1 + r)) P.q hqpos
        (by omega) (by omega)
      have hcomplement : ((D * r + A * b - 1) + 1) * P.q - ((P.q : Int) - (1 + r)) =
          (D * r + A * b - 1) * P.q + (1 + r) := by ring
      rw [hcomplement] at htop
      have hparent : IntegerCeilDiv (D * r * b) b hb.ne' = D * r := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using ceilMul D r b hb.ne'
      rw [hsb', ha1, htopnum, htop, hparent]
      ring
  refine ⟨e3 g₂ h₂, ?_⟩
  intro x hdom hbd
  let swap : GaussianInt → GaussianInt := fun z => ⟨z.im, z.re⟩
  let gswap : IntegerLatticeFunction := fun z => g₂ (swap z)
  have hswapbd (n : Nat) (z : GaussianInt) (hz : z ∈ FordDoubledBoundary n) :
      swap z ∈ FordDoubledBoundary n := by
    change (0 ≤ z.re ∧ z.re ≤ (n : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (n : Int)) ∧ _ at hz
    change (0 ≤ z.im ∧ z.im ≤ (n : Int) ∧ 0 ≤ z.re ∧ z.re ≤ (n : Int)) ∧ _
    exact ⟨⟨hz.1.2.2.1, hz.1.2.2.2, hz.1.1, hz.1.2.1⟩,
      fun hi => hz.2 ⟨hi.2.2.1, hi.2.2.2, hi.1, hi.2.1⟩⟩
  have hgswap : ∀ z ∈ FordDoubledBoundary P₂.q,
      gswap z = IntegerCeilDiv (P₂.p * z.re * z.im) P₂.q
        (by exact_mod_cast P₂.q_pos.ne') := by
    intro z hz
    have hv := h₂ (swap z) (hswapbd P₂.q z hz)
    simpa only [gswap, swap, mul_assoc, mul_left_comm, mul_comm] using hv
  have hdomswap : (P.q₁ : Int) ≤ (swap x).re ∧
      (swap x).re ≤ (P.q : Int) ∧ 0 ≤ (swap x).im ∧ (swap x).im ≤ (P.q₂ : Int) :=
    ⟨hdom.2.2.1, hdom.2.2.2, hdom.1, hdom.2.1⟩
  have hv := e3 gswap hgswap (swap x) hdomswap (hswapbd P.q x hbd)
  have hpoint : swap (swap x - ⟨(P.q₁ : Int), 0⟩) =
      x - ⟨0, (P.q₁ : Int)⟩ := by
    ext <;> simp [swap, Zsqrtd.re_sub, Zsqrtd.im_sub]
  change g₂ (swap (swap x - ⟨(P.q₁ : Int), 0⟩)) + P.p₁ * x.re =
    IntegerCeilDiv (P.p * x.im * x.re) P.q _ at hv
  rw [hpoint] at hv
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hv

end ApollonianSuperharmonic

end
