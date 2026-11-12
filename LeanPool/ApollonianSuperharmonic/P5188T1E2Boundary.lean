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

-- [TABLET NODE: P5188T1E2Boundary]

/-!
# P5188T1E2Boundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SecondEdgeBoundaryConstruction

private theorem hsum (P : FordFareyParameter) : (P.q : Int) = P.q₁ + P.q₂ := by
  classical
  exact_mod_cast P.sum_q

private theorem hps (P : FordFareyParameter) : P.p = P.p₁ + P.p₂ := by
  classical
  exact P.sum_p

private theorem hcross (P : FordFareyParameter) (hq : 1 < P.q) : P.p₁ * (↑P.q₂ : ℤ) - P.p₂ *
    (↑P.q₁ : ℤ) = 1 := by
  classical
  exact (P5130T5ParentArithmetic P hq).2.2.2.2.2.2

private theorem hdet₁ (P : FordFareyParameter) : P.p₁ * (↑P.q : ℤ) - (↑P.q₁ : ℤ) * P.p = 1 := by
  classical
  exact P.det₁

private theorem hdet₂ (P : FordFareyParameter) : P.p₂ * (↑P.q : ℤ) - (↑P.q₂ : ℤ) * P.p = -1 := by
  classical
  exact P.det₂

private theorem hqpos (P : FordFareyParameter) : 0 < (P.q : Int) := by
  classical
  exact_mod_cast P.q_pos

private theorem ha (P : FordFareyParameter) (hq : 1 < P.q) : 0 < (P.q₁ : Int) := by
  classical
  have := (P5130T5ParentArithmetic P hq).1; exact_mod_cast this

private theorem hb (P : FordFareyParameter) : 0 < (P.q₂ : Int) := by
  classical
  have := P.q₂_pos; exact_mod_cast this

private theorem hab (P : FordFareyParameter) : (P.q₁ : Int) < P.q := by
  classical
  have := P.q₁_lt; exact_mod_cast this

private theorem hbb (P : FordFareyParameter) (hsum :
    (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) (ha : 0 < (↑P.q₁ : ℤ)) : (P.q₂ : Int) < P.q := by
  classical
  rw [hsum]; omega

private noncomputable abbrev a (P : FordFareyParameter) : Int := by
  classical
  let a : Int := P.q₁
  exact a

private noncomputable abbrev b (P : FordFareyParameter) : Int := by
  classical
  let b : Int := P.q₂
  exact b

private noncomputable abbrev A (P : FordFareyParameter) : Int := by
  classical
  let A : Int := P.p₁
  exact A

private noncomputable abbrev D (P : FordFareyParameter) : Int := by
  classical
  let D : Int := P.p₂
  exact D

private theorem haq (P : FordFareyParameter) (hsum : (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) : (a
    P) + (b P) = P.q := by
  classical
  let a : Int := P.q₁
  let b : Int := P.q₂
  change (a + b = P.q)
  dsimp [a, b]; exact hsum.symm

private theorem hpq (P : FordFareyParameter) (hps : P.p = P.p₁ + P.p₂) : (A P) + (D P) = P.p := by
  classical
  let A : Int := P.p₁
  let D : Int := P.p₂
  change (A + D = P.p)
  dsimp [A, D]; exact hps.symm

private theorem hAq (P : FordFareyParameter) (hdet₁ : P.p₁ * (↑P.q : ℤ) - (↑P.q₁ : ℤ) * P.p = 1)
    : (A P) * P.q - (a P) * P.p = 1 := by
  classical
  let a : Int := P.q₁
  let A : Int := P.p₁
  change (A * P.q - a * P.p = 1)
  simpa [a, A] using hdet₁

private theorem hpqa (P : FordFareyParameter) (hAq :
    (A P) * (↑P.q : ℤ) - (a P) * P.p = 1) : P.p * (a P) = (A P) * P.q - 1 := by
  classical
  let a : Int := P.q₁
  let A : Int := P.p₁
  change (A * (↑P.q : ℤ) - a * P.p = 1) at hAq
  change (P.p * a = A * P.q - 1)
  have haux : A * P.q - P.p * a = 1 := by
    rw [mul_comm P.p a]
    exact hAq
  omega

private theorem hDq (P : FordFareyParameter) (hdet₂ : P.p₂ * (↑P.q : ℤ) - (↑P.q₂ : ℤ) * P.p = -1)
    : (D P) * P.q - (b P) * P.p = -1 := by
  classical
  let b : Int := P.q₂
  let D : Int := P.p₂
  change (D * P.q - b * P.p = -1)
  simpa [b, D] using hdet₂

private theorem hAB (P : FordFareyParameter) (hcross : P.p₁ * (↑P.q₂ : ℤ) - P.p₂ * (↑P.q₁ : ℤ) =
    1) : (A P) * (b P) - (D P) * (a P) = 1 := by
  classical
  let a : Int := P.q₁
  let b : Int := P.q₂
  let A : Int := P.p₁
  let D : Int := P.p₂
  change (A * b - D * a = 1)
  simpa [a, b, A, D] using hcross

private theorem ceilPerturb : ∀ (N M d q E : ℤ) (hd : 0 < d) (hdq : d < q), 0 ≤ E → E ≤ d → M * d
    = N * q - E → IntegerCeilDiv M q (by omega) = IntegerCeilDiv N d (by omega) := by
  classical
  exact P5188T1CeilingStability

private theorem ceilShift : ∀ (M C q : ℤ) (hq : q ≠ 0), IntegerCeilDiv (M + C * q) q hq =
    IntegerCeilDiv M q hq + C := by
  classical
  exact P5188T1CeilingShift

private theorem ceilZero (d : Int) (hd : d ≠ 0) : IntegerCeilDiv 0 d hd = 0 := by
  classical
  simp [IntegerCeilDiv]

private theorem ceilMul (c t d : Int) (hd : d ≠ 0) :
      IntegerCeilDiv (c * d * t) d (by omega) = c * t := by
  classical
  dsimp only [IntegerCeilDiv]
  have he : -(c * d * t) = d * (-c * t) := by ring
  rw [he, Int.mul_ediv_cancel_left _ hd]
  ring

private theorem g₁val (P : FordFareyParameter) (P₁ : FordFareyParameter) (hp₁ : P₁.p = P.p₁) (hq₁
    : P₁.q = P.q₁) (g₁ : IntegerLatticeFunction) (h₁ : ∀ x ∈ FordDoubledBoundary P₁.q, g₁ x =
    IntegerCeilDiv (P₁.p * x.re * x.im) (↑P₁.q : ℤ) (by exact_mod_cast P₁.q_pos.ne')) (ha : 0 <
        (↑P.q₁ : ℤ))
    (u v : Int) (hu0 : 0 ≤ u) (hu : u ≤ (a P))
      (hv0 : 0 ≤ v) (hv : v ≤ (a P))
      (hs : u = 0 ∨ u = 1 ∨ u = (a P) - 1 ∨ u = (a P) ∨
        v = 0 ∨ v = 1 ∨ v = (a P) - 1 ∨ v = (a P)) :
      g₁ ⟨u, v⟩ = IntegerCeilDiv ((A P) * u * v) (a P) (by exact ne_of_gt ha) := by
  classical
  let a : Int := P.q₁
  let A : Int := P.p₁
  change u ≤ a at hu
  change v ≤ a at hv
  change (u = 0 ∨ u = 1 ∨ u = a - 1 ∨ u = a ∨
    v = 0 ∨ v = 1 ∨ v = a - 1 ∨ v = a) at hs
  change (g₁ ⟨u, v⟩ = IntegerCeilDiv (A * u * v) a (by exact ne_of_gt ha))
  have hbd : (⟨u, v⟩ : GaussianInt) ∈ FordDoubledBoundary P₁.q := by
    change (0 ≤ u ∧ u ≤ (P₁.q : Int) ∧ 0 ≤ v ∧ v ≤ (P₁.q : Int)) ∧ _
    refine ⟨⟨hu0, ?_, hv0, ?_⟩, ?_⟩
    · simpa [a, hq₁] using hu
    · simpa [a, hq₁] using hv
    intro hi
    simp at hi
    rcases hs with h | h | h | h | h | h | h | h <;> omega
  simpa [a, A, hp₁, hq₁] using h₁ ⟨u, v⟩ hbd

private theorem hbox (P : FordFareyParameter) (x : GaussianInt) (hbd : x ∈ FordDoubledBoundary
    P.q) : x ∈ FordVertexDomain P.q := by
  classical
  exact hbd.1

private theorem hside (P : FordFareyParameter) (x : GaussianInt) (hdom
    : (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) (hbd : x ∈
    FordDoubledBoundary P.q) (hsum : (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) (hb : 0 < (↑P.q₂ :
    ℤ)) (hbox : x ∈ FordVertexDomain P.q) : x.re = 0 ∨ x.re = 1 ∨ x.re = (P.q : Int) - 1 ∨ x.re =
    P.q ∨
      x.im = 0 ∨ x.im = 1 ∨ x.im = (P.q : Int) - 1 ∨ x.im = P.q := by
  classical
  change x ∈ FordVertexDomain P.q ∧ _ at hbd
  rcases hbd with ⟨_, hn⟩
  simp only [FordVertexDomain] at hbox
  rcases hbox with ⟨hr0, hrq, hi0, hiq⟩
  by_contra hnside
  push Not at hnside
  apply hn
  exact ⟨by omega, by omega, by omega, by omega⟩

private noncomputable abbrev r (P : FordFareyParameter) (x : GaussianInt) : Int := by
  classical
  let b : Int := P.q₂
  let r : Int := x.re - b
  exact r

private noncomputable abbrev s (P : FordFareyParameter) (x : GaussianInt) : Int := by
  classical
  let b : Int := P.q₂
  let s : Int := x.im - b
  exact s

private theorem hr0 (P : FordFareyParameter) (x : GaussianInt) (hdom :
    (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) : 0 ≤ (r P
    x) := by
  classical
  let b : Int := P.q₂
  let r : Int := x.re - b
  change (0 ≤ r)
  dsimp [r]; omega

private theorem hsa0 (P : FordFareyParameter) (x : GaussianInt) (hdom :
    (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) : 0 ≤ (s P
    x) := by
  classical
  let b : Int := P.q₂
  let s : Int := x.im - b
  change (0 ≤ s)
  dsimp [s]; omega

private theorem hra (P : FordFareyParameter) (x : GaussianInt) (hsum :
    (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) (hdom : (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧
    (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) : (r P x) ≤ (a P) := by
  classical
  let a : Int := P.q₁
  let b : Int := P.q₂
  let r : Int := x.re - b
  change (r ≤ a)
  dsimp [r]; omega

private theorem hsa (P : FordFareyParameter) (x : GaussianInt) (hsum :
    (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) (hdom : (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧
    (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) : (s P x) ≤ (a P) := by
  classical
  let a : Int := P.q₁
  let b : Int := P.q₂
  let s : Int := x.im - b
  change (s ≤ a)
  dsimp [s]; omega

private theorem hx (P : FordFareyParameter) (x : GaussianInt) : x = ⟨(b P) + (r P x), (b P) + (s
    P x)⟩ := by
  classical
  let b : Int := P.q₂
  let r : Int := x.re - b
  let s : Int := x.im - b
  change (x = ⟨b + r, b + s⟩)
  ext <;> simp [r, s]

private theorem hshift (P : FordFareyParameter) (x : GaussianInt) : (⟨(b P) + (r P x), (b P) + (s
    P x)⟩ : GaussianInt) - ⟨(b P), (b P)⟩ = ⟨(r P x), (s P x)⟩ := by
  classical
  let b : Int := P.q₂
  let r : Int := x.re - b
  let s : Int := x.im - b
  change ((⟨b + r, b + s⟩ : GaussianInt) - ⟨b, b⟩ = ⟨r, s⟩)
  ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]

private theorem hE2side (P : FordFareyParameter) (x : GaussianInt)
    (hsum : (↑P.q : ℤ) = (↑P.q₁ : ℤ) + (↑P.q₂ : ℤ)) (ha : 0 < (↑P.q₁ : ℤ)) (hb : 0 < (↑P.q₂ : ℤ))
    (hside : x.re = 0 ∨ x.re = 1 ∨ x.re = (↑P.q : ℤ) - 1 ∨ x.re = (↑P.q : ℤ) ∨ x.im = 0 ∨ x.im =
    1 ∨ x.im = (↑P.q : ℤ) - 1 ∨ x.im = (↑P.q : ℤ)) (hdom : (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ)
    ∧ (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) : (r P x) = (a P) ∨ (r P x) = (a P) - 1 ∨ ((r P x)
    = 0 ∧ (b P) = 1) ∨
      (s P x) = (a P) ∨ (s P x) = (a P) - 1 ∨ ((s P x) = 0 ∧ (b P) = 1) := by
  classical
  let a : Int := P.q₁
  let b : Int := P.q₂
  let r : Int := x.re - b
  let s : Int := x.im - b
  change (r = a ∨ r = a - 1 ∨ (r = 0 ∧ b = 1) ∨
      s = a ∨ s = a - 1 ∨ (s = 0 ∧ b = 1))
  rcases hside with hr | hr | hr | hr | hi | hi | hi | hi
  · dsimp [r]; omega
  · have hble : (P.q₂ : Int) ≤ 1 := by simpa [hr] using hdom.1
    have hb1 : b = 1 := by dsimp [b]; omega
    have hr0' : r = 0 := by dsimp [r, b]; omega
    exact Or.inr (Or.inr (Or.inl ⟨hr0', hb1⟩))
  · refine Or.inr (Or.inl ?_); dsimp [r]; omega
  · exact Or.inl (by dsimp [r]; omega)
  · dsimp [s]; omega
  · have hble : (P.q₂ : Int) ≤ 1 := by simpa [hi] using hdom.2.2.1
    have hb1 : b = 1 := by dsimp [b]; omega
    have hs0' : s = 0 := by dsimp [s, b]; omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs0', hb1⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); dsimp [s]; omega
  · refine Or.inr (Or.inr (Or.inr ?_)); dsimp [s]; omega

end SecondEdgeBoundaryConstruction

theorem P5188T1E2Boundary (P P₁ : FordFareyParameter)
    (hq : 1 < P.q) (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (g₁ : IntegerLatticeFunction)
    (h₁ : ∀ x ∈ FordDoubledBoundary P₁.q,
      g₁ x = IntegerCeilDiv (P₁.p * x.re * x.im) P₁.q (by exact_mod_cast P₁.q_pos.ne'))
    (x : GaussianInt)
    (hdom : (P.q₂ : Int) ≤ x.re ∧ x.re ≤ (P.q : Int) ∧
      (P.q₂ : Int) ≤ x.im ∧ x.im ≤ (P.q : Int))
    (hbd : x ∈ FordDoubledBoundary P.q) :
    g₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
      P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1 =
      IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne') := by
-- BODY
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := SecondEdgeBoundaryConstruction.hsum P
  have hps : P.p = P.p₁ + P.p₂ := SecondEdgeBoundaryConstruction.hps P
  have hcross := SecondEdgeBoundaryConstruction.hcross P hq
  have hdet₁ := SecondEdgeBoundaryConstruction.hdet₁ P
  have hdet₂ := SecondEdgeBoundaryConstruction.hdet₂ P
  have hqpos : 0 < (P.q : Int) := SecondEdgeBoundaryConstruction.hqpos P
  have ha : 0 < (P.q₁ : Int) := SecondEdgeBoundaryConstruction.ha P hq
  have hb : 0 < (P.q₂ : Int) := SecondEdgeBoundaryConstruction.hb P
  have hab : (P.q₁ : Int) < P.q := SecondEdgeBoundaryConstruction.hab P
  have hbb : (P.q₂ : Int) < P.q := SecondEdgeBoundaryConstruction.hbb P hsum ha
  let a : Int := P.q₁
  let b : Int := P.q₂
  let A : Int := P.p₁
  let D : Int := P.p₂
  have haq : a + b = P.q := SecondEdgeBoundaryConstruction.haq P hsum
  have hpq : A + D = P.p := SecondEdgeBoundaryConstruction.hpq P hps
  have hAq : A * P.q - a * P.p = 1 := SecondEdgeBoundaryConstruction.hAq P hdet₁
  have hpqa : P.p * a = A * P.q - 1 := SecondEdgeBoundaryConstruction.hpqa P hAq
  have hDq : D * P.q - b * P.p = -1 := SecondEdgeBoundaryConstruction.hDq P hdet₂
  have hAB : A * b - D * a = 1 := SecondEdgeBoundaryConstruction.hAB P hcross
  have ceilPerturb := SecondEdgeBoundaryConstruction.ceilPerturb
  have ceilShift := SecondEdgeBoundaryConstruction.ceilShift
  have ceilZero (d : Int) (hd : d ≠ 0) : IntegerCeilDiv 0 d hd = 0 :=
      SecondEdgeBoundaryConstruction.ceilZero d hd
  have ceilMul (c t d : Int) (hd : d ≠ 0) :
      IntegerCeilDiv (c * d * t) d (by omega) = c * t := SecondEdgeBoundaryConstruction.ceilMul c
          t d hd
  have g₁val (u v : Int) (hu0 : 0 ≤ u) (hu : u ≤ a)
      (hv0 : 0 ≤ v) (hv : v ≤ a)
      (hs : u = 0 ∨ u = 1 ∨ u = a - 1 ∨ u = a ∨
        v = 0 ∨ v = 1 ∨ v = a - 1 ∨ v = a) :
      g₁ ⟨u, v⟩ = IntegerCeilDiv (A * u * v) a (by omega) := SecondEdgeBoundaryConstruction.g₁val
          P P₁ hp₁ hq₁ g₁ h₁ ha u v hu0 hu hv0 hv hs
  have hbox : x ∈ FordVertexDomain P.q := SecondEdgeBoundaryConstruction.hbox P x hbd
  have hside : x.re = 0 ∨ x.re = 1 ∨ x.re = (P.q : Int) - 1 ∨ x.re = P.q ∨
      x.im = 0 ∨ x.im = 1 ∨ x.im = (P.q : Int) - 1 ∨ x.im = P.q :=
          SecondEdgeBoundaryConstruction.hside P x hdom hbd hsum hb hbox
  change ((P.q₂ : Int) ≤ x.re ∧ x.re ≤ P.q ∧
    (P.q₂ : Int) ≤ x.im ∧ x.im ≤ P.q) at hdom
  let r : Int := x.re - b
  let s : Int := x.im - b
  have hr0 : 0 ≤ r := SecondEdgeBoundaryConstruction.hr0 P x hdom
  have hsa0 : 0 ≤ s := SecondEdgeBoundaryConstruction.hsa0 P x hdom
  have hra : r ≤ a := SecondEdgeBoundaryConstruction.hra P x hsum hdom
  have hsa : s ≤ a := SecondEdgeBoundaryConstruction.hsa P x hsum hdom
  have hx : x = ⟨b + r, b + s⟩ := SecondEdgeBoundaryConstruction.hx P x
  have hshift : (⟨b + r, b + s⟩ : GaussianInt) - ⟨b, b⟩ = ⟨r, s⟩ :=
      SecondEdgeBoundaryConstruction.hshift P x
  rw [hx, hshift]
  change g₁ ⟨r, s⟩ + D * (b + r) + D * (b + s) - D * b + 1 =
    IntegerCeilDiv (P.p * (b + r) * (b + s)) P.q _
  have hE2side : r = a ∨ r = a - 1 ∨ (r = 0 ∧ b = 1) ∨
      s = a ∨ s = a - 1 ∨ (s = 0 ∧ b = 1) := SecondEdgeBoundaryConstruction.hE2side P x hsum ha
          hb hside hdom
  rcases hE2side with hrA | hrA1 | hrzeroPair | hsA | hsA1 | hsZeroPair
  · rw [g₁val r s hr0 hra hsa0 hsa (Or.inr (Or.inr (Or.inr (Or.inl hrA))))]
    have hpedge : IntegerCeilDiv (A * a * s) a (by omega) = A * s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using ceilMul A s a (by omega)
    have hqedge : IntegerCeilDiv (P.p * P.q * (b + s)) P.q (by omega) =
        P.p * (b + s) := by
      simpa [mul_assoc] using ceilMul P.p (b + s) P.q (by omega)
    have hpb : P.p * b = D * P.q + 1 := by
      have haux : D * P.q - P.p * b = -1 := by
        rw [← mul_comm b P.p]
        exact hDq
      omega
    have hcorner : P.p * (b + s) = A * s + D * (b + a + s) + 1 := by
      calc
        P.p * (b + s) = P.p * b + P.p * s := by ring
        _ = (D * P.q + 1) + (A + D) * s := by rw [hpb, ← hpq]
        _ = A * s + D * (b + a + s) + 1 := by rw [show P.q = a + b by omega]; ring
    have hparent : IntegerCeilDiv (A * r * s) a (by omega) = A * s := by
      rw [hrA]
      exact hpedge
    rw [hparent, hrA, show b + a = P.q by omega, hqedge]
    calc
      A * s + D * P.q + D * (b + s) - D * b + 1 =
          A * s + D * (b + a + s) + 1 := by rw [show P.q = a + b by omega]; ring
      _ = P.p * (b + s) := hcorner.symm
  · let C : Int := D * (b + (a - 1) + s) + 1
    let M₀ : Int := P.p * (b + (a - 1)) * (b + s) - C * P.q
    rw [g₁val r s hr0 hra hsa0 hsa (Or.inr (Or.inr (Or.inl hrA1)))]
    have hrel : M₀ * a = (A * (a - 1) * s) * P.q - (a - s) := by
      dsimp [M₀, C]
      rw [← hpq, ← haq]
      linear_combination (a * (a + b - 1) + s) * hAB
    have hmain := ceilPerturb (A * (a - 1) * s) M₀ a P.q (a - s)
      ha hab (by omega) (by omega) hrel
    have hmove : P.p * (b + (a - 1)) * (b + s) = M₀ + C * P.q := by
      dsimp [M₀]
      ring
    have hmove' : P.p * (b + r) * (b + s) = M₀ + C * P.q := by
      rw [hrA1]
      exact hmove
    rw [hmove', ceilShift M₀ C P.q (by omega)]
    have hpar : IntegerCeilDiv (A * r * s) a (by omega) =
        IntegerCeilDiv (A * (a - 1) * s) a (by omega) := by
      rw [hrA1]
    rw [hpar, hrA1, hmain]
    ring
  · rcases hrzeroPair with ⟨hrzero', hb1⟩
    rw [g₁val r s hr0 hra hsa0 hsa (Or.inl hrzero')]
    have hpd : P.p = D * P.q + 1 := by
      have hDq' : D * P.q - P.p = -1 := by simpa [hb1] using hDq
      omega
    have hnum : P.p * (b + r) * (b + s) =
        (D * (1 + s)) * P.q + (1 + s) := by
      simp only [hb1, hrzero', hpd]
      ring
    rw [show A * r * s = 0 by simp [hrzero'], hnum]
    have hEpos : 0 < 1 + s := by omega
    have hEq : 1 + s ≤ P.q := by dsimp [s]; omega
    have htop := P5188T1CeilingBelow (D * (1 + s) + 1)
      ((P.q : Int) - (1 + s)) P.q hqpos (by omega) (by omega)
    have hcomp : (D * (1 + s) + 1) * P.q - ((P.q : Int) - (1 + s)) =
        (D * (1 + s)) * P.q + (1 + s) := by ring
    rw [hcomp] at htop
    rw [htop]
    simp [IntegerCeilDiv, hrzero', hb1]
  · have hsideval : r = 0 ∨ r = 1 ∨ r = a - 1 ∨ r = a ∨
        s = 0 ∨ s = 1 ∨ s = a - 1 ∨ s = a := by
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsA))))))
    rw [g₁val r s hr0 hra hsa0 hsa hsideval]
    have hpedge : IntegerCeilDiv (A * r * a) a (by omega) = A * r := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using ceilMul A r a (by omega)
    have hqedge : IntegerCeilDiv (P.p * (b + r) * P.q) P.q (by omega) =
        P.p * (b + r) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using ceilMul P.p (b + r) P.q (by omega)
    have hpb : P.p * b = D * P.q + 1 := by
      have haux : D * P.q - P.p * b = -1 := by
        rw [← mul_comm b P.p]
        exact hDq
      omega
    have hcorner : P.p * (b + r) = A * r + D * (b + r) + D * a + 1 := by
      calc
        P.p * (b + r) = P.p * b + P.p * r := by ring
        _ = (D * P.q + 1) + (A + D) * r := by rw [hpb, ← hpq]
        _ = A * r + D * (b + r) + D * a + 1 := by rw [show P.q = a + b by omega]; ring
    rw [hsA, show b + a = P.q by omega, hqedge]
    rw [hpedge]
    calc
      A * r + D * (b + r) + D * P.q - D * b + 1 =
          A * r + D * (b + r) + D * a + 1 := by rw [show P.q = a + b by omega]; ring
      _ = P.p * (b + r) := hcorner.symm
  · let C : Int := D * (b + r + (a - 1)) + 1
    let M₀ : Int := P.p * (b + r) * (b + (a - 1)) - C * P.q
    rw [g₁val r s hr0 hra hsa0 hsa (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        hsA1)))))))]
    have hrel : M₀ * a = (A * r * (a - 1)) * P.q - (a - r) := by
      dsimp [M₀, C]
      rw [← hpq, ← haq]
      linear_combination (a * (a + b - 1) + r) * hAB
    have hmain := ceilPerturb (A * r * (a - 1)) M₀ a P.q (a - r)
      ha hab (by omega) (by omega) hrel
    have hmove : P.p * (b + r) * (b + (a - 1)) = M₀ + C * P.q := by
      dsimp [M₀]
      ring
    have hmove' : P.p * (b + r) * (b + s) = M₀ + C * P.q := by
      rw [hsA1]
      exact hmove
    rw [hmove', ceilShift M₀ C P.q (by omega)]
    have hpar : IntegerCeilDiv (A * r * s) a (by omega) =
        IntegerCeilDiv (A * r * (a - 1)) a (by omega) := by rw [hsA1]
    rw [hpar, hsA1, hmain]
    ring
  · rcases hsZeroPair with ⟨hszero, hb1⟩
    rw [g₁val r s hr0 hra hsa0 hsa
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hszero)))))]
    have hpd : P.p = D * P.q + 1 := by
      have hDq' : D * P.q - P.p = -1 := by simpa [hb1] using hDq
      omega
    have hnum : P.p * (b + r) * (b + s) =
        (D * (1 + r)) * P.q + (1 + r) := by
      simp only [hb1, hszero, hpd]
      ring
    have hnumzero : A * r * s = 0 := by
      calc
        A * r * s = A * r * 0 := congrArg (fun z : Int => A * r * z) hszero
        _ = 0 := mul_zero _
    rw [hnumzero, hnum]
    have hEpos : 0 < 1 + r := by omega
    have hEq : 1 + r ≤ P.q := by dsimp [r]; omega
    have htop := P5188T1CeilingBelow (D * (1 + r) + 1)
      ((P.q : Int) - (1 + r)) P.q hqpos (by omega) (by omega)
    have hcomp : (D * (1 + r) + 1) * P.q - ((P.q : Int) - (1 + r)) =
        (D * (1 + r)) * P.q + (1 + r) := by ring
    rw [hcomp] at htop
    rw [htop]
    rw [hb1, hszero]
    rw [ceilZero a ha.ne']
    change 0 + D * (1 + r) + D * 1 - D * 1 + 1 = D * (1 + r) + 1
    rw [zero_add, add_sub_cancel_right]

end ApollonianSuperharmonic

end
