/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordInteriorSquareCoordinates
public import LeanPool.ApollonianSuperharmonic.FordFareySum

public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P4062T1InteriorGeometry]

/-!
# P4062T1InteriorGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InteriorGeometryProof


private theorem hq1pos :
    ∀ (P : FordFareyParameter), (2 < P.q) → ((P.q = P.q₁ + P.q₂) → (0 < P.q₁)) := by
  classical
  intro P hP hsum
  by_contra h
  have hz : P.q₁ = 0 := Nat.eq_zero_of_not_pos h
  have hd := P.det₁
  rw [hz] at hd
  simp only [Nat.cast_zero, zero_mul] at hd
  have hqint : 2 < (P.q : Int) := by exact_mod_cast hP
  by_cases hp : P.p₁ ≤ 0
  · have hqnonneg : 0 ≤ (P.q : Int) := by omega
    have : P.p₁ * (P.q : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hqnonneg
    omega
  · have hp' : 1 ≤ P.p₁ := by omega
    nlinarith


private theorem coord0 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q :
        Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → (∀ (x : GaussianInt), (x ∈ A 0) → (1 ≤ x.re
        ∧ x.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1)) := by
  classical
  intro P A squareCoordinates x hx
  simpa [A, P4062T1RecursiveInteriors] using (squareCoordinates P.q₁ x).mp hx

private theorem coord1 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → (∀ (x : GaussianInt), (x
        ∈ A 1) → ((P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates x hx
  dsimp [A, P4062T1RecursiveInteriors] at hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hb := (squareCoordinates P.q₁ z).mp hz
  simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
  constructor <;> omega

private theorem coord2 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → (∀ (x : GaussianInt), (x
        ∈ A 2) → ((P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates x hx
  dsimp [A, P4062T1RecursiveInteriors] at hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hb := (squareCoordinates P.q₂ z).mp hz
  simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
  constructor <;> omega

private theorem coord3 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → (∀ (x : GaussianInt), (x
        ∈ A 3) → (1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates x hx
  dsimp [A, P4062T1RecursiveInteriors] at hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hb := (squareCoordinates P.q₂ z).mp hz
  simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
  constructor <;> omega

private theorem mem0 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q :
        Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((∀ (x : GaussianInt), (x ∈ A 0) → (1 ≤
        x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1)) → (∀ (x : GaussianInt),
        x ∈ A 0 ↔
      1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1)) := by
  classical
  intro P A squareCoordinates coord0 x
  constructor
  · exact coord0 x
  · intro h
    exact (squareCoordinates P.q₁ x).mpr h

private theorem mem1 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((∀ (x : GaussianInt),
        (x ∈ A 1) → ((P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧ (P.q₂ : Int)+1 ≤ x.im ∧ x.im
        ≤ (P.q : Int)-1)) → (∀ (x : GaussianInt), x ∈ A 1 ↔
      (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates coord1 x
  constructor
  · exact coord1 x
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₁ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp [
        ]

private theorem mem2 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((∀ (x : GaussianInt),
        (x ∈ A 2) → ((P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₂ :
        Int)-1)) → (∀ (x : GaussianInt), x ∈ A 2 ↔
      (P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates coord2 x
  constructor
  · exact coord2 x
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨x - ⟨(P.q₁ : Int), 0⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₂ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp [
        ]

private theorem mem3 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤
        x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((∀ (x : GaussianInt),
        (x ∈ A 3) → (1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧ (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q :
        Int)-1)) → (∀ (x : GaussianInt), x ∈ A 3 ↔
      1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1))) := by
  classical
  intro P A hsum squareCoordinates coord3 x
  constructor
  · exact coord3 x
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨x - ⟨0, (P.q₁ : Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₂ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp [
        ]

private theorem bounds :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (∀ (x : GaussianInt), (x ∈ A 0) → (1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₁
        : Int)-1)) → ((∀ (x : GaussianInt), (x ∈ A 1) → ((P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q :
        Int)-1 ∧ (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1)) → ((∀ (x : GaussianInt), (x ∈ A
        2) → ((P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1)) →
        ((∀ (x : GaussianInt), (x ∈ A 3) → (1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧ (P.q₁ : Int)+1 ≤
        x.im ∧ x.im ≤ (P.q : Int)-1)) → (∀ (i : Fin 4), ∀ (x : GaussianInt), (x ∈ A i) → ((i = 0
        → 1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1) ∧
      (i = 1 → (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) ∧
      (i = 2 → (P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1) ∧
      (i = 3 → 1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
        (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1)))))) := by
  classical
  intro P A coord0 coord1 coord2 coord3 i x hx
  constructor
  · intro hi
    subst i
    exact coord0 x hx
  constructor
  · intro hi
    subst i
    exact coord1 x hx
  constructor
  · intro hi
    subst i
    exact coord2 x hx
  · intro hi
    subst i
    exact coord3 x hx

private theorem adjacentCoordinates :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → ((x.re = y.re ∧ (y.im
        = x.im+1 ∨ x.im = y.im+1)) ∨
      (x.im = y.im ∧ (y.re = x.re+1 ∨ x.re = y.re+1))) := by
  classical
  intro x y h
  rcases h with h | h | h | h
  · subst y
    simp [Zsqrtd.re_add, Zsqrtd.im_add]
  · subst y
    simp [Zsqrtd.re_sub, Zsqrtd.im_sub]
  · subst y
    simp [Zsqrtd.re_add, Zsqrtd.im_add]
  · subst y
    simp [Zsqrtd.re_sub, Zsqrtd.im_sub]

private theorem adjacentSymm :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → (FourNeighborAdjacent
        y x) := by
  classical
  intro x y h
  rcases h with h | h | h | h <;> subst y <;>
    simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem separate01 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (x : GaussianInt), x ∈ A 0 ↔ 1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧ 1 ≤
        x.im ∧ x.im ≤ (P.q₁ : Int)-1) → ((∀ (x : GaussianInt), x ∈ A 1 ↔ (P.q₂ : Int)+1 ≤ x.re ∧
        x.re ≤ (P.q : Int)-1 ∧ (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) → ((∀ (x :
        GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → ((x.re = y.re ∧ (y.im =
        x.im+1 ∨ x.im = y.im+1)) ∨ (x.im = y.im ∧ (y.re = x.re+1 ∨ x.re = y.re+1)))) → (∀ (x :
        GaussianInt), ∀ (y : GaussianInt), (x ∈ A 0) → ((x ∉ A 1) → ((y ∈ A 1) → ((y ∉ A 0) →
        ((FourNeighborAdjacent x y) → (False))))))))) := by
  classical
  intro P A hsum mem0 mem1 adjacentCoordinates x y hx hxn hy hyn hxy
  have bx := mem0 x |>.mp hx
  have byy := mem1 y |>.mp hy
  have hn1 : ¬ ((P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) := by
    intro h
    exact hxn ((mem1 x).mpr h)
  have hn0 : ¬ (1 ≤ y.re ∧ y.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ y.im ∧ y.im ≤ (P.q₁ : Int)-1) := by
    intro h
    exact hyn ((mem0 y).mpr h)
  by_cases hle : P.q₁ ≤ P.q₂
  · rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega
  · have hgt : P.q₂ < P.q₁ := by omega
    have hxsmall : x.re ≤ P.q₂ ∨ x.im ≤ P.q₂ := by
      by_contra h
      push Not at h
      apply hn1
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hylarge : P.q₁ ≤ y.re ∨ P.q₁ ≤ y.im := by
      by_contra h
      push Not at h
      apply hn0
      exact ⟨by omega, by omega, by omega, by omega⟩
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩
    all_goals rcases hxsmall with hxsmall | hxsmall <;>
      rcases hylarge with hylarge | hylarge <;> omega

private theorem separate23 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((0 < P.q₁) → ((∀ (x : GaussianInt), x ∈ A 2 ↔ (P.q₁ : Int)+1 ≤ x.re ∧
        x.re ≤ (P.q : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1) → ((∀ (x : GaussianInt), x ∈ A 3
        ↔ 1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧ (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) → ((∀
        (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → ((x.re = y.re ∧
        (y.im = x.im+1 ∨ x.im = y.im+1)) ∨ (x.im = y.im ∧ (y.re = x.re+1 ∨ x.re = y.re+1)))) → (∀
        (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ A 2) → ((x ∉ A 3) → ((y ∈ A 3) → ((y ∉ A 2)
        → ((FourNeighborAdjacent x y) → (False)))))))))) := by
  classical
  intro P A hsum hq1pos mem2 mem3 adjacentCoordinates x y hx hxn hy hyn hxy
  have bx := mem2 x |>.mp hx
  have byy := mem3 y |>.mp hy
  have hn3 : ¬ (1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) := by
    intro h
    exact hxn ((mem3 x).mpr h)
  have hn2 : ¬ ((P.q₁ : Int)+1 ≤ y.re ∧ y.re ≤ (P.q : Int)-1 ∧
      1 ≤ y.im ∧ y.im ≤ (P.q₂ : Int)-1) := by
    intro h
    exact hyn ((mem2 y).mpr h)
  by_cases hle : P.q₂ ≤ P.q₁
  · rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega
  · have hgt : P.q₁ < P.q₂ := by omega
    have hxout : P.q₂ ≤ x.re ∨ x.im ≤ P.q₁ := by
      by_contra h
      push Not at h
      apply hn3
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hyout : y.re ≤ P.q₁ ∨ P.q₂ ≤ y.im := by
      by_contra h
      push Not at h
      apply hn2
      exact ⟨by omega, by omega, by omega, by omega⟩
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩
    all_goals rcases hxout with hxout | hxout <;>
      rcases hyout with hyout | hyout <;> omega

private theorem crossNo :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (∀ (x : GaussianInt), x ∈ A 0 ↔ 1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₁ :
        Int)-1) → ((∀ (x : GaussianInt), x ∈ A 1 ↔ (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) → ((∀ (x : GaussianInt), x ∈ A 2 ↔ (P.q₁ :
        Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1) → ((∀ (x :
        GaussianInt), x ∈ A 3 ↔ 1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧ (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤
        (P.q : Int)-1) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) →
        ((x.re = y.re ∧ (y.im = x.im+1 ∨ x.im = y.im+1)) ∨ (x.im = y.im ∧ (y.re = x.re+1 ∨ x.re =
        y.re+1)))) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ A 0 ∨ x ∈ A 1) → ((y ∈ A 2 ∨
        y ∈ A 3) → ((FourNeighborAdjacent x y) → (False)))))))) := by
  classical
  intro P A mem0 mem1 mem2 mem3 adjacentCoordinates x y hx hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have bx := mem0 x |>.mp hx
    have byy := mem2 y |>.mp hy
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega
  · have bx := mem0 x |>.mp hx
    have byy := mem3 y |>.mp hy
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega
  · have bx := mem1 x |>.mp hx
    have byy := mem2 y |>.mp hy
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega
  · have bx := mem1 x |>.mp hx
    have byy := mem3 y |>.mp hy
    rcases adjacentCoordinates x y hxy with ⟨hre, hs⟩ | ⟨him, hs⟩ <;> omega

end InteriorGeometryProof

theorem P4062T1InteriorGeometry (P : FordFareyParameter)
    (hP : 2 < P.q) :
    let A := P4062T1RecursiveInteriors P
    (∀ i, A i ⊆ P4062T1InteriorSquare P.q) ∧
    (∀ i j, ∀ x ∈ A i, x ∉ A j → ∀ y ∈ A j, y ∉ A i →
      ¬ FourNeighborAdjacent x y) ∧
    Disjoint (A 0 ∪ A 1) (A 2 ∪ A 3) ∧
    (∀ x ∈ A 0 ∪ A 1, ∀ y ∈ A 2 ∪ A 3,
      ¬ FourNeighborAdjacent x y) ∧
    (P.q₂ < P.q₁ → A 2 ∩ A 3 = ∅) ∧
    (P.q₁ < P.q₂ → A 0 ∩ A 1 = ∅) := by
-- BODY
  classical
  let A := P4062T1RecursiveInteriors P
  have hsum : P.q = P.q₁ + P.q₂ := FordFareySum.denominatorSum P
  have hq1pos : 0 < P.q₁ := InteriorGeometryProof.hq1pos P hP hsum
  have squareCoordinates (q : Nat) (x : GaussianInt) :
      x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := FordInteriorSquareCoordinates.membership q x
  have coord0 (x : GaussianInt) (hx : x ∈ A 0) :
      1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1 := InteriorGeometryProof.coord0 P squareCoordinates x hx
  have coord1 (x : GaussianInt) (hx : x ∈ A 1) :
      (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1 := InteriorGeometryProof.coord1 P hsum
          squareCoordinates x hx
  have coord2 (x : GaussianInt) (hx : x ∈ A 2) :
      (P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1 := InteriorGeometryProof.coord2 P hsum squareCoordinates x hx
  have coord3 (x : GaussianInt) (hx : x ∈ A 3) :
      1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1 := InteriorGeometryProof.coord3 P hsum
          squareCoordinates x hx
  have mem0 (x : GaussianInt) : x ∈ A 0 ↔
      1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1 := InteriorGeometryProof.mem0 P squareCoordinates coord0 x
  have mem1 (x : GaussianInt) : x ∈ A 1 ↔
      (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1 := InteriorGeometryProof.mem1 P hsum
          squareCoordinates coord1 x
  have mem2 (x : GaussianInt) : x ∈ A 2 ↔
      (P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1 := InteriorGeometryProof.mem2 P hsum squareCoordinates
          coord2 x
  have mem3 (x : GaussianInt) : x ∈ A 3 ↔
      1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1 := InteriorGeometryProof.mem3 P hsum
          squareCoordinates coord3 x
  have bounds (i : Fin 4) (x : GaussianInt) (hx : x ∈ A i) :
      (i = 0 → 1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q₁ : Int)-1) ∧
      (i = 1 → (P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) ∧
      (i = 2 → (P.q₁ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int)-1) ∧
      (i = 3 → 1 ≤ x.re ∧ x.re ≤ (P.q₂ : Int)-1 ∧
        (P.q₁ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) := InteriorGeometryProof.bounds P coord0
            coord1 coord2 coord3 i x hx
  have adjacentCoordinates (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      (x.re = y.re ∧ (y.im = x.im+1 ∨ x.im = y.im+1)) ∨
      (x.im = y.im ∧ (y.re = x.re+1 ∨ x.re = y.re+1)) :=
          InteriorGeometryProof.adjacentCoordinates x y h
  have adjacentSymm (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := InteriorGeometryProof.adjacentSymm x y h
  have separate01 (x y : GaussianInt) (hx : x ∈ A 0) (hxn : x ∉ A 1)
      (hy : y ∈ A 1) (hyn : y ∉ A 0) (hxy : FourNeighborAdjacent x y) : False :=
          InteriorGeometryProof.separate01 P hsum mem0 mem1 adjacentCoordinates x y hx hxn hy hyn
          hxy
  have separate23 (x y : GaussianInt) (hx : x ∈ A 2) (hxn : x ∉ A 3)
      (hy : y ∈ A 3) (hyn : y ∉ A 2) (hxy : FourNeighborAdjacent x y) : False :=
          InteriorGeometryProof.separate23 P hsum hq1pos mem2 mem3 adjacentCoordinates x y hx hxn
          hy hyn hxy
  have crossNo (x y : GaussianInt) (hx : x ∈ A 0 ∨ x ∈ A 1)
      (hy : y ∈ A 2 ∨ y ∈ A 3) (hxy : FourNeighborAdjacent x y) : False :=
          InteriorGeometryProof.crossNo P mem0 mem1 mem2 mem3 adjacentCoordinates x y hx hy hxy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    have hcoord : 1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1 := by
      by_cases hi0 : i = 0
      · subst i
        have h := coord0 x hx
        exact ⟨h.1, by omega, h.2.2.1, by omega⟩
      by_cases hi1 : i = 1
      · subst i
        have h := coord1 x hx
        exact ⟨by omega, h.2.1, by omega, h.2.2.2⟩
      by_cases hi2 : i = 2
      · subst i
        have h := coord2 x hx
        exact ⟨by omega, h.2.1, h.2.2.1, by omega⟩
      · have hi3 : i = 3 := by omega
        subst i
        have h := coord3 x hx
        exact ⟨h.1, by omega, by omega, h.2.2.2⟩
    exact (squareCoordinates P.q x).mpr hcoord
  · intro i j x hx hxnot y hy hynot hadj
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl | rfl
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl | rfl
      · exact hxnot hx
      · exact separate01 x y hx hxnot hy hynot hadj
      · exact crossNo x y (Or.inl hx) (Or.inl hy) hadj
      · exact crossNo x y (Or.inl hx) (Or.inr hy) hadj
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl | rfl
      · exact separate01 y x hy hynot hx hxnot (adjacentSymm x y hadj)
      · exact hxnot hx
      · exact crossNo x y (Or.inr hx) (Or.inl hy) hadj
      · exact crossNo x y (Or.inr hx) (Or.inr hy) hadj
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl | rfl
      · exact False.elim (crossNo y x (Or.inl hy) (Or.inl hx)
          (adjacentSymm x y hadj))
      · exact False.elim (crossNo y x (Or.inr hy) (Or.inl hx)
          (adjacentSymm x y hadj))
      · exact hxnot hx
      · exact separate23 x y hx hxnot hy hynot hadj
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl | rfl
      · exact False.elim (crossNo y x (Or.inl hy) (Or.inr hx)
          (adjacentSymm x y hadj))
      · exact False.elim (crossNo y x (Or.inr hy) (Or.inr hx)
          (adjacentSymm x y hadj))
      · exact separate23 y x hy hynot hx hxnot (adjacentSymm x y hadj)
      · exact hxnot hx
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hy with hy | hy
      · have bx := mem0 x |>.mp hx
        have byy := mem2 x |>.mp hy
        omega
      · have bx := mem0 x |>.mp hx
        have byy := mem3 x |>.mp hy
        omega
    · rcases Finset.mem_union.mp hy with hy | hy
      · have bx := mem1 x |>.mp hx
        have byy := mem2 x |>.mp hy
        omega
      · have bx := mem1 x |>.mp hx
        have byy := mem3 x |>.mp hy
        omega
  · intro x hx y hy hadj
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact crossNo x y (Or.inl hx) (Or.inl hy) hadj
      · exact crossNo x y (Or.inl hx) (Or.inr hy) hadj
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact crossNo x y (Or.inr hx) (Or.inl hy) hadj
      · exact crossNo x y (Or.inr hx) (Or.inr hy) hadj
  · intro h
    change A 2 ∩ A 3 = ∅
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty]
    constructor
    · rintro ⟨hx2, hx3⟩
      have b2 := mem2 x |>.mp hx2
      have b3 := mem3 x |>.mp hx3
      omega
    · intro h
      cases h
  · intro h
    change A 0 ∩ A 1 = ∅
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty]
    constructor
    · rintro ⟨hx0, hx1⟩
      have b0 := mem0 x |>.mp hx0
      have b1 := mem1 x |>.mp hx1
      omega
    · intro h
      cases h

end ApollonianSuperharmonic

end
