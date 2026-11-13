/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordInteriorSquareCoordinates
public import LeanPool.ApollonianSuperharmonic.FordFareySum
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderPaths
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import Mathlib.Data.Nat.Dist
public meta import Lean.Meta.Tactic.NormCast
public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors

/-!
# P4112T1PathGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic


-- [TABLET NODE: P4112T1PathGeometry]
namespace PathGeometryProof


private theorem hs :
    ∀ (P : FordFareyParameter),
    let s := P.q₂
    0 < s := by
  classical
  intro P s
  exact P.q₂_pos

private theorem hr :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let r := P.q₁
    (P.q = P.q₁ + P.q₂) → (0 < r)) := by
  classical
  intro P hP r hsum
  by_contra hn
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hn
  have hzero : P.q₁ = 0 := hr0
  have hd := P.det₁
  rw [hzero] at hd
  simp only [Nat.cast_zero, zero_mul] at hd
  by_cases hp : P.p₁ ≤ 0
  · have hqnonneg : 0 ≤ (P.q : Int) := by omega
    have : P.p₁ * (P.q : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hqnonneg
    omega
  · have hp' : 1 ≤ P.p₁ := by omega
    nlinarith

private theorem hrs :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → (r ≠ s)) := by
  classical
  intro P hP r s hsum heq
  have hqeq : P.q = r + r := by
    have hrs' : P.q₁ = P.q₂ := by simpa [r,s] using heq
    simpa [r, hrs'] using hsum
  have hqcast : (P.q : Int) = (r : Int) + (r : Int) := by exact_mod_cast hqeq
  have hq1cast : (P.q₁ : Int) = (r : Int) := by rfl
  have hq2cast : (P.q₂ : Int) = (r : Int) := by
    have hrs' : P.q₁ = P.q₂ := by simpa [r,s] using heq
    exact_mod_cast hrs'.symm
  have hd : (P.p₁ - P.p₂) * (r : Int) = 1 := by
    have h1 := P.det₁
    have h2 := P.det₂
    rw [hqcast, hq1cast] at h1
    rw [hqcast, hq2cast] at h2
    nlinarith
  have hrint2 : 2 ≤ (r : Int) := by
    have hqint : 2 < (P.q : Int) := by exact_mod_cast hP
    rw [hqeq] at hqint
    push_cast at hqint
    omega
  by_cases hc : P.p₁ - P.p₂ ≤ 0
  · have hcprod : (P.p₁-P.p₂) * (r:Int) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (by omega)
    omega
  · have hc' : 1 ≤ P.p₁ - P.p₂ := by omega
    have hprod : 2 ≤ (P.p₁-P.p₂) * (r:Int) := by
      calc
        2 = 1 * 2 := by norm_num
        _ ≤ (P.p₁-P.p₂) * (r:Int) := by
          exact mul_le_mul hc' hrint2 (by norm_num) (by omega)
    omega

private theorem horder :
    ∀ (P : FordFareyParameter),
    let r := P.q₁
    let s := P.q₂
    (r ≠ s) → (r < s ∨ s < r) := by
  classical
  intro P r s hrs
  exact lt_or_gt_of_ne hrs

private abbrev squareCoordinates := ApollonianSuperharmonic.FordInteriorSquareCoordinates.membership

private theorem mem0 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let r := P.q₁
    (∀ (n : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n :
        Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n : Int)-1) → (∀ (x : GaussianInt), x ∈ A 0 ↔
      1 ≤ x.re ∧ x.re ≤ (r : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (r : Int)-1) := by
  classical
  intro P A r squareCoordinates x
  simpa [A,r,P4062T1RecursiveInteriors] using (squareCoordinates r x)

private theorem mem1 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare n ↔ 1 ≤
        x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n : Int)-1) → (∀ (x : GaussianInt), x ∈ A 1 ↔
      (s : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      (s : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1)) := by
  classical
  intro P A s hsum squareCoordinates x
  let r := P.q₁
  constructor
  · intro hx
    dsimp [A,r,s,P4062T1RecursiveInteriors] at hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := (squareCoordinates P.q₁ z).mp hz
    simp only [Zsqrtd.re_add,Zsqrtd.im_add]
    have hq2 : (P.q₂ : Int) = (s : Int) := by rfl
    constructor <;> omega
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x-⟨(s:Int),(s:Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates r _).mpr
      simp only [Zsqrtd.re_sub,Zsqrtd.im_sub]
      have hq2 : (P.q₂ : Int) = (s : Int) := by rfl
      constructor <;> omega
    · ext <;> simp [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_sub,Zsqrtd.im_sub] <;> omega

private theorem mem2 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare n ↔ 1 ≤
        x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n : Int)-1) → (∀ (x : GaussianInt), x ∈ A 2 ↔
      (r : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧
      1 ≤ x.im ∧ x.im ≤ (s : Int)-1)) := by
  classical
  intro P A r s hsum squareCoordinates x
  constructor
  · intro hx
    dsimp [A,r,s,P4062T1RecursiveInteriors] at hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := (squareCoordinates P.q₂ z).mp hz
    simp only [Zsqrtd.re_add,Zsqrtd.im_add]
    have hq1 : (P.q₁ : Int) = (r : Int) := by rfl
    constructor <;> omega
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x-⟨(r:Int),0⟩, ?_, ?_⟩
    · apply (squareCoordinates s _).mpr
      simp only [Zsqrtd.re_sub,Zsqrtd.im_sub]
      have hq1 : (P.q₁ : Int) = (r : Int) := by rfl
      constructor <;> omega
    · ext <;> simp [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_sub,Zsqrtd.im_sub]; omega

private theorem mem3 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare n ↔ 1 ≤
        x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n : Int)-1) → (∀ (x : GaussianInt), x ∈ A 3 ↔
      1 ≤ x.re ∧ x.re ≤ (s : Int)-1 ∧
      (r : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1)) := by
  classical
  intro P A r s hsum squareCoordinates x
  constructor
  · intro hx
    dsimp [A,r,s,P4062T1RecursiveInteriors] at hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := (squareCoordinates P.q₂ z).mp hz
    simp only [Zsqrtd.re_add,Zsqrtd.im_add]
    have hq1 : (P.q₁ : Int) = (r : Int) := by rfl
    constructor <;> omega
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x-⟨0,(r:Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates s _).mpr
      simp only [Zsqrtd.re_sub,Zsqrtd.im_sub]
      have hq1 : (P.q₁ : Int) = (r : Int) := by rfl
      constructor <;> omega
    · ext <;> simp [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_sub,Zsqrtd.im_sub]; omega

private theorem memB0Large :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((0 < s) → ((0 < r) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈
        P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n :
        Int)-1) → (∀ (x : GaussianInt), (s < r) → (x ∈ (B 0).1 ↔
        (x.re = (r:Int) ∧ 1 ≤ x.im ∧ x.im ≤ (s:Int)) ∨
        (x.im = (s:Int) ∧ (r:Int) ≤ x.re ∧ x.re ≤ (P.q:Int)-1)))))) := by
  classical
  intro P B r s hsum hs hr squareCoordinates x hlarge
  change P.q₂ < P.q₁ at hlarge
  simp only [P4062T1RemainderPaths, hlarge, ↓reduceIte, Int.reduceNeg, Fin.isValue,
      Matrix.cons_val_zero, Finset.mem_filter, B]
  rw [squareCoordinates]
  omega

private theorem memB1Large :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((0 < s) → ((0 < r) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈
        P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n :
        Int)-1) → (∀ (x : GaussianInt), (s < r) → (x ∈ (B 1).1 ↔
        (x.im = (r:Int) ∧ 1 ≤ x.re ∧ x.re ≤ (s:Int)) ∨
        (x.re = (s:Int) ∧ (r:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1)))))) := by
  classical
  intro P B r s hsum hs hr squareCoordinates x hlarge
  change P.q₂ < P.q₁ at hlarge
  simp only [P4062T1RemainderPaths, hlarge, ↓reduceIte, Int.reduceNeg, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.mem_filter, B]
  rw [squareCoordinates]
  omega

private theorem memB0Small :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((0 < s) → ((0 < r) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈
        P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n :
        Int)-1) → (∀ (x : GaussianInt), (r < s) → (x ∈ (B 0).1 ↔
        (x.re = (r:Int) ∧ 1 ≤ x.im ∧ x.im ≤ (r:Int)) ∨
        (x.im = (r:Int) ∧ 1 ≤ x.re ∧ x.re ≤ (r:Int))))))) := by
  classical
  intro P B r s hsum hs hr squareCoordinates x hsmall
  change P.q₁ < P.q₂ at hsmall
  have hfalse : ¬ P.q₂ < P.q₁ := by omega
  simp only [P4062T1RemainderPaths, hfalse, ↓reduceIte, Int.reduceNeg, Fin.isValue,
      Matrix.cons_val_zero, Finset.mem_filter, B]
  rw [squareCoordinates]
  omega

private theorem memB1Small :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((0 < s) → ((0 < r) → ((∀ (n : Nat), ∀ (x : GaussianInt), x ∈
        P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (n :
        Int)-1) → (∀ (x : GaussianInt), (r < s) → (x ∈ (B 1).1 ↔
        (x.re = (s:Int) ∧ (s:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1) ∨
        (x.im = (s:Int) ∧ (s:Int) ≤ x.re ∧ x.re ≤ (P.q:Int)-1)))))) := by
  classical
  intro P B r s hsum hs hr squareCoordinates x hsmall
  change P.q₁ < P.q₂ at hsmall
  have hfalse : ¬ P.q₂ < P.q₁ := by omega
  simp only [P4062T1RemainderPaths, hfalse, ↓reduceIte, Int.reduceNeg, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.mem_filter, B]
  rw [squareCoordinates]
  omega

private theorem partition :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    let W := P4062T1InteriorSquare P.q \ E
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (P.q = P.q₁ + P.q₂) → ((0 < s) → ((0 < r) → ((r < s ∨ s < r) → ((∀ (n : Nat), ∀ (x :
        GaussianInt), x ∈ P4062T1InteriorSquare n ↔ 1 ≤ x.re ∧ x.re ≤ (n : Int)-1 ∧ 1 ≤ x.im ∧
        x.im ≤ (n : Int)-1) → ((∀ (x : GaussianInt), x ∈ A 0 ↔ 1 ≤ x.re ∧ x.re ≤ (r : Int)-1 ∧ 1
        ≤ x.im ∧ x.im ≤ (r : Int)-1) → ((∀ (x : GaussianInt), x ∈ A 1 ↔ (s : Int)+1 ≤ x.re ∧ x.re
        ≤ (P.q : Int)-1 ∧ (s : Int)+1 ≤ x.im ∧ x.im ≤ (P.q : Int)-1) → ((∀ (x : GaussianInt), x ∈
        A 2 ↔ (r : Int)+1 ≤ x.re ∧ x.re ≤ (P.q : Int)-1 ∧ 1 ≤ x.im ∧ x.im ≤ (s : Int)-1) → ((∀ (x
            : GaussianInt), x ∈ A 3 ↔ 1 ≤ x.re ∧ x.re ≤ (s : Int)-1 ∧ (r : Int)+1 ≤ x.im ∧ x.im ≤
        (P.q : Int)-1) → ((∀ (x : GaussianInt), (s < r) → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤
        x.im ∧ x.im ≤ (s:Int)) ∨ (x.im = (s:Int) ∧ (r:Int) ≤ x.re ∧ x.re ≤ (P.q:Int)-1))) → ((∀
            (x : GaussianInt), (s < r) → (x ∈ (B 1).1 ↔ (x.im = (r:Int) ∧ 1 ≤ x.re ∧ x.re ≤ (s:Int))
        ∨ (x.re = (s:Int) ∧ (r:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1))) → ((∀ (x : GaussianInt), (r <
        s) → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤ x.im ∧ x.im ≤ (r:Int)) ∨ (x.im = (r:Int) ∧ 1 ≤
        x.re ∧ x.re ≤ (r:Int)))) → ((∀ (x : GaussianInt), (r < s) → (x ∈ (B 1).1 ↔ (x.re =
        (s:Int) ∧ (s:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1) ∨ (x.im = (s:Int) ∧ (s:Int) ≤ x.re ∧ x.re
        ≤ (P.q:Int)-1))) → (W = (B 0).1 ∪ (B 1).1)))))))))))))) := by
  classical
  intro P hP A E W B r s hsum hs hr horder squareCoordinates mem0 mem1 mem2 mem3 memB0Large
      memB1Large memB0Small memB1Small
  ext x
  simp only [W, Finset.mem_sdiff]
  simp only [E, A, Finset.mem_union, not_or]
  rw [squareCoordinates, mem0, mem1, mem2, mem3]
  rcases horder with hsmall | hlarge
  · rw [memB0Small x (by omega), memB1Small x (by omega)]
    constructor <;> intro h <;> omega
  · rw [memB0Large x (by omega), memB1Large x (by omega)]
    constructor <;> intro h <;> omega

private theorem hdisj :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (r < s ∨ s < r) → ((∀ (x : GaussianInt), (s < r) → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤ x.im
        ∧ x.im ≤ (s:Int)) ∨ (x.im = (s:Int) ∧ (r:Int) ≤ x.re ∧ x.re ≤ (P.q:Int)-1))) → ((∀ (x :
            GaussianInt), (s < r) → (x ∈ (B 1).1 ↔ (x.im = (r:Int) ∧ 1 ≤ x.re ∧ x.re ≤ (s:Int)) ∨
        (x.re = (s:Int) ∧ (r:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1))) → ((∀ (x : GaussianInt), (r < s)
        → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤ x.im ∧ x.im ≤ (r:Int)) ∨ (x.im = (r:Int) ∧ 1 ≤
        x.re ∧ x.re ≤ (r:Int)))) → ((∀ (x : GaussianInt), (r < s) → (x ∈ (B 1).1 ↔ (x.re =
        (s:Int) ∧ (s:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1) ∨ (x.im = (s:Int) ∧ (s:Int) ≤ x.re ∧ x.re
        ≤ (P.q:Int)-1))) → (Disjoint (B 0).1 (B 1).1))))) := by
  classical
  intro P B r s horder memB0Large memB1Large memB0Small memB1Small
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases horder with hsmall | hlarge
  · rw [memB0Small x (by omega)] at hx
    rw [memB1Small x (by omega)] at hy
    rcases hx with ⟨hrx,hxl,hxh⟩ | ⟨hxi,hxl,hxh⟩ <;>
      rcases hy with ⟨hry,hyl,hyh⟩ | ⟨hyi,hyl,hyh⟩ <;> omega
  · rw [memB0Large x (by omega)] at hx
    rw [memB1Large x (by omega)] at hy
    rcases hx with ⟨hrx,hxl,hxh⟩ | ⟨hxi,hxl,hxh⟩ <;>
      rcases hy with ⟨hry,hyl,hyh⟩ | ⟨hyi,hyl,hyh⟩ <;> omega

private theorem hcross :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let r := P.q₁
    let s := P.q₂
    (r < s ∨ s < r) → ((∀ (x : GaussianInt), (s < r) → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤ x.im
        ∧ x.im ≤ (s:Int)) ∨ (x.im = (s:Int) ∧ (r:Int) ≤ x.re ∧ x.re ≤ (P.q:Int)-1))) → ((∀ (x :
            GaussianInt), (s < r) → (x ∈ (B 1).1 ↔ (x.im = (r:Int) ∧ 1 ≤ x.re ∧ x.re ≤ (s:Int)) ∨
        (x.re = (s:Int) ∧ (r:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1))) → ((∀ (x : GaussianInt), (r < s)
        → (x ∈ (B 0).1 ↔ (x.re = (r:Int) ∧ 1 ≤ x.im ∧ x.im ≤ (r:Int)) ∨ (x.im = (r:Int) ∧ 1 ≤
        x.re ∧ x.re ≤ (r:Int)))) → ((∀ (x : GaussianInt), (r < s) → (x ∈ (B 1).1 ↔ (x.re =
        (s:Int) ∧ (s:Int) ≤ x.im ∧ x.im ≤ (P.q:Int)-1) ∨ (x.im = (s:Int) ∧ (s:Int) ≤ x.re ∧ x.re
        ≤ (P.q:Int)-1))) → (∀ x ∈ (B 0).1, ∀ y ∈ (B 1).1, ¬ FourNeighborAdjacent x y))))) := by
  classical
  intro P B r s horder memB0Large memB1Large memB0Small memB1Small x hx y hy hadj
  rcases horder with hsmall | hlarge
  · rw [memB0Small x (by omega)] at hx
    rw [memB1Small y (by omega)] at hy
    simp only [FourNeighborAdjacent,
      ] at hadj
    rcases hx with ⟨hxr,hxl,hxh⟩ | ⟨hxi,hxl,hxh⟩ <;>
      rcases hy with ⟨hys,hyl,hyh⟩ | ⟨hyi,hyl,hyh⟩ <;>
      rcases hadj with h | h | h | h <;>
        have hre := congrArg (fun z : GaussianInt => z.re) h <;>
        have him := congrArg (fun z : GaussianInt => z.im) h <;>
        simp [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one] at hre him <;> omega
  · rw [memB0Large x (by omega)] at hx
    rw [memB1Large y (by omega)] at hy
    simp only [FourNeighborAdjacent,
      ] at hadj
    rcases hx with ⟨hxr,hxl,hxh⟩ | ⟨hys,hxl,hxh⟩ <;>
      rcases hy with ⟨hyr,hyl,hyh⟩ | ⟨hxs,hyl,hyh⟩ <;>
      rcases hadj with h | h | h | h <;>
        have hre := congrArg (fun z : GaussianInt => z.re) h <;>
        have him := congrArg (fun z : GaussianInt => z.im) h <;>
        simp [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one] at hre him <;> omega

private theorem natAbsToNat :
    ∀ (z : Int), (0 ≤ z) → (z.natAbs = z.toNat) := by
  classical
  intro z hz
  have h₁ := Int.natAbs_of_nonneg hz
  have h₂ := Int.toNat_of_nonneg hz
  have hn : (z.natAbs : Int) = z.toNat := h₁.trans h₂.symm
  exact_mod_cast hn

private theorem natAbsDist :
    (∀ (z : Int), 0 ≤ z → z.natAbs = z.toNat) →
      ∀ (a : Int), ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat := by
  classical
  intro natAbsToNat a b ha hb
  by_cases hab : a ≤ b
  · have habs : (a-b).natAbs = (b-a).toNat := by
      have h₁ := Int.natAbs_of_nonneg (a := b-a) (by omega)
      have h₂ := Int.toNat_of_nonneg (by omega : 0 ≤ b-a)
      have hn : ((b-a).natAbs : Int) = (b-a).toNat := h₁.trans h₂.symm
      have hn' : (b-a).natAbs = (b-a).toNat := by exact_mod_cast hn
      rw [show a-b = -(b-a) by omega, Int.natAbs_neg]
      exact hn'
    rw [habs]
    have hac : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
    have hbc : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
    simp [Nat.dist]
    omega
  · have hba : b ≤ a := by omega
    have habs : (a-b).natAbs = (a-b).toNat := natAbsToNat _ (by omega)
    rw [habs]
    have hac : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
    have hbc : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
    simp [Nat.dist]
    omega

private theorem distDistDown :
    ∀ (a : Nat),
      ∀ (b : Nat),
        ∀ (c : Nat), a ≤ c → b ≤ c → Nat.dist (Nat.dist a c) (Nat.dist b c) = Nat.dist a b := by
  classical
  intro a b c ha hb
  simp [Nat.dist]
  omega

private theorem distDistUp :
    ∀ (a : Nat),
      ∀ (b : Nat),
        ∀ (c : Nat), c ≤ a → c ≤ b → Nat.dist (Nat.dist a c) (Nat.dist b c) = Nat.dist a b := by
  classical
  intro a b c ha hb
  simp [Nat.dist]
  omega

private theorem natDistOneInt :
    ∀ (a : Int),
      ∀ (b : Int), 0 ≤ a → 0 ≤ b → (Nat.dist a.toNat b.toNat = 1 ↔ a = b + 1 ∨ b = a + 1) := by
  classical
  intro a b ha hb
  have hac : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have hbc : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  simp [Nat.dist]
  omega

private theorem adjacentVertical :
    ∀ (x : GaussianInt),
      ∀ (y : GaussianInt),
        x.re = y.re → (FourNeighborAdjacent x y ↔ x.im = y.im + 1 ∨ y.im = x.im + 1) := by
  classical
  intro x y hfix
  simp [FourNeighborAdjacent, Zsqrtd.ext_iff, hfix]; omega

private theorem adjacentHorizontal :
    ∀ (x : GaussianInt),
      ∀ (y : GaussianInt),
        x.im = y.im → (FourNeighborAdjacent x y ↔ x.re = y.re + 1 ∨ y.re = x.re + 1) := by
  classical
  intro x y hfix
  simp [FourNeighborAdjacent, Zsqrtd.ext_iff, hfix]; omega

private theorem lineVertical :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    (∀ (a : Int), ∀ (b : Int), (0 ≤ a) → ((0 ≤ b) → (Nat.dist a.toNat b.toNat = 1 ↔ a = b+1 ∨ b =
        a+1))) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.re = y.re) →
        (FourNeighborAdjacent x y ↔ x.im = y.im+1 ∨ y.im = x.im+1)) → (∀ (x : GaussianInt), ∀ (y
            : GaussianInt), (x.re = y.re) → ((0 ≤ x.im) → ((0 ≤ y.im) → ((Nat.dist (d x) (d y) =
        Nat.dist x.im.toNat y.im.toNat) → (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)))))) := by
  classical
  intro P B d natDistOneInt adjacentVertical x y hfix hnx hny hlevel
  rw [adjacentVertical x y hfix]
  constructor
  · intro ha
    refine ⟨Or.inl hfix, ?_⟩
    rw [hlevel]
    exact (natDistOneInt x.im y.im hnx hny).2 ha
  · rintro ⟨_, hd⟩
    rw [hlevel] at hd
    exact (natDistOneInt x.im y.im hnx hny).1 hd

private theorem lineHorizontal :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    (∀ (a : Int), ∀ (b : Int), (0 ≤ a) → ((0 ≤ b) → (Nat.dist a.toNat b.toNat = 1 ↔ a = b+1 ∨ b =
        a+1))) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.im = y.im) →
        (FourNeighborAdjacent x y ↔ x.re = y.re+1 ∨ y.re = x.re+1)) → (∀ (x : GaussianInt), ∀ (y
            : GaussianInt), (x.im = y.im) → ((0 ≤ x.re) → ((0 ≤ y.re) → ((Nat.dist (d x) (d y) =
        Nat.dist x.re.toNat y.re.toNat) → (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)))))) := by
  classical
  intro P B d natDistOneInt adjacentHorizontal x y hfix hnx hny hlevel
  rw [adjacentHorizontal x y hfix]
  constructor
  · intro ha
    refine ⟨Or.inr hfix, ?_⟩
    rw [hlevel]
    exact (natDistOneInt x.re y.re hnx hny).2 ha
  · rintro ⟨_, hd⟩
    rw [hlevel] at hd
    exact (natDistOneInt x.re y.re hnx hny).1 hd

private theorem dLarge0Root :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    let r := P.q₁
    let s := P.q₂
    (s < r) → (∀ (x : GaussianInt), (x ∈ (B 0).1) → (d x = (x.re-(r:Int)).natAbs +
        (x.im-(s:Int)).natAbs)) := by
  classical
  intro P B d r s hlarge x hx
  have hroot : (B 0).2 = (⟨(r:Int),(s:Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, r, s, hlarge]
  dsimp [d]
  rw [ite_eq_left hx, hroot]

private theorem dLarge1Root :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    let r := P.q₁
    let s := P.q₂
    (Disjoint (B 0).1 (B 1).1) → ((s < r) → (∀ (x : GaussianInt), (x ∈ (B 1).1) → (d x =
        (x.re-(s:Int)).natAbs + (x.im-(r:Int)).natAbs))) := by
  classical
  intro P B d r s hdisj hlarge x hx
  have hnot : x ∉ (B 0).1 := by
    intro hx0
    exact (Finset.disjoint_left.mp hdisj) hx0 hx
  have hroot : (B 1).2 = (⟨(s:Int),(r:Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, r, s, hlarge]
  dsimp [d]
  rw [ite_eq_right hnot, hroot]

private theorem dSmall0Root :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    let r := P.q₁
    let s := P.q₂
    (r < s) → (∀ (x : GaussianInt), (x ∈ (B 0).1) → (d x = (x.re-(r:Int)).natAbs +
        (x.im-(r:Int)).natAbs)) := by
  classical
  intro P B d r s hsmall x hx
  have hfalse : ¬ P.q₂ < P.q₁ := by omega
  have hroot : (B 0).2 = (⟨(r:Int),(r:Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, r, hfalse]
  dsimp [d]
  rw [ite_eq_left hx, hroot]

private theorem dSmall1Root :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    let r := P.q₁
    let s := P.q₂
    (Disjoint (B 0).1 (B 1).1) → ((r < s) → (∀ (x : GaussianInt), (x ∈ (B 1).1) → (d x =
        (x.re-(s:Int)).natAbs + (x.im-(s:Int)).natAbs))) := by
  classical
  intro P B d r s hdisj hsmall x hx
  have hnot : x ∉ (B 0).1 := by
    intro hx0
    exact (Finset.disjoint_left.mp hdisj) hx0 hx
  have hfalse : ¬ P.q₂ < P.q₁ := by omega
  have hroot : (B 1).2 = (⟨(s:Int),(s:Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, s, hfalse]
  dsimp [d]
  rw [ite_eq_right hnot, hroot]

private theorem dLarge0V :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → d x = (x.re - (r : Int)).natAbs + (x.im - (s : Int)).natAbs) →
          s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → x.re = (r : Int) → 0 ≤ x.im → d x = Nat.dist x.im.toNat s := by
  classical
  intro P B d r s natAbsDist dLarge0Root hlarge x hx hcoord hpos
  rw [dLarge0Root hlarge x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, zero_add]
  simpa using (natAbsDist x.im (s:Int) hpos (by exact_mod_cast (Nat.zero_le s)))

private theorem dLarge0H :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → d x = (x.re - (r : Int)).natAbs + (x.im - (s : Int)).natAbs) →
          s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → x.im = (s : Int) → 0 ≤ x.re → d x = Nat.dist x.re.toNat r := by
  classical
  intro P B d r s natAbsDist dLarge0Root hlarge x hx hcoord hpos
  rw [dLarge0Root hlarge x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, add_zero]
  simpa using (natAbsDist x.re (r:Int) hpos (by exact_mod_cast (Nat.zero_le r)))

private theorem dLarge1V :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → d x = (x.re - (s : Int)).natAbs + (x.im - (r : Int)).natAbs) →
          s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → x.im = (r : Int) → 0 ≤ x.re → d x = Nat.dist x.re.toNat s := by
  classical
  intro P B d r s natAbsDist dLarge1Root hlarge x hx hcoord hpos
  rw [dLarge1Root hlarge x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero]
  simpa using (natAbsDist x.re (s:Int) hpos (by exact_mod_cast (Nat.zero_le s)))

private theorem dLarge1H :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → d x = (x.re - (s : Int)).natAbs + (x.im - (r : Int)).natAbs) →
          s < r →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → x.re = (s : Int) → 0 ≤ x.im → d x = Nat.dist x.im.toNat r := by
  classical
  intro P B d r s natAbsDist dLarge1Root hlarge x hx hcoord hpos
  rw [dLarge1Root hlarge x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero]
  simpa using (natAbsDist x.im (r:Int) hpos (by exact_mod_cast (Nat.zero_le r)))

private theorem dSmall0V :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → d x = (x.re - (r : Int)).natAbs + (x.im - (r : Int)).natAbs) →
          r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → x.re = (r : Int) → 0 ≤ x.im → d x = Nat.dist x.im.toNat r := by
  classical
  intro P B d r s natAbsDist dSmall0Root hsmall x hx hcoord hpos
  rw [dSmall0Root hsmall x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, zero_add]
  simpa using (natAbsDist x.im (r:Int) hpos (by exact_mod_cast (Nat.zero_le r)))

private theorem dSmall0H :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → d x = (x.re - (r : Int)).natAbs + (x.im - (r : Int)).natAbs) →
          r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 0).1 → x.im = (r : Int) → 0 ≤ x.re → d x = Nat.dist x.re.toNat r := by
  classical
  intro P B d r s natAbsDist dSmall0Root hsmall x hx hcoord hpos
  rw [dSmall0Root hsmall x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, add_zero]
  simpa using (natAbsDist x.re (r:Int) hpos (by exact_mod_cast (Nat.zero_le r)))

private theorem dSmall1V :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → d x = (x.re - (s : Int)).natAbs + (x.im - (s : Int)).natAbs) →
          r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → x.re = (s : Int) → 0 ≤ x.im → d x = Nat.dist x.im.toNat s := by
  classical
  intro P B d r s natAbsDist dSmall1Root hsmall x hx hcoord hpos
  rw [dSmall1Root hsmall x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, zero_add]
  simpa using (natAbsDist x.im (s:Int) hpos (by exact_mod_cast (Nat.zero_le s)))

private theorem dSmall1H :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      (∀ (a : Int),
          ∀ (b : Int), 0 ≤ a → 0 ≤ b → (a - b).natAbs = Nat.dist a.toNat b.toNat) →
        (r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → d x = (x.re - (s : Int)).natAbs + (x.im - (s : Int)).natAbs) →
          r < s →
            ∀ (x : GaussianInt),
              x ∈ (B 1).1 → x.im = (s : Int) → 0 ≤ x.re → d x = Nat.dist x.re.toNat s := by
  classical
  intro P B d r s natAbsDist dSmall1Root hsmall x hx hcoord hpos
  rw [dSmall1Root hsmall x hx, hcoord]
  simp only [sub_self, Int.natAbs_zero, add_zero]
  simpa using (natAbsDist x.re (s:Int) hpos (by exact_mod_cast (Nat.zero_le s)))

private theorem adjacentCoordinates :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → (x.re = y.re ∨ x.im =
        y.im) := by
  classical
  intro x y ha
  rcases ha with h | h | h | h
  · right
    have him := congrArg (fun z : GaussianInt => z.im) h
    simpa only [Zsqrtd.im_add, Zsqrtd.im_one, Zsqrtd.im_zero, add_zero] using him.symm
  · right
    have him := congrArg (fun z : GaussianInt => z.im) h
    simpa only [Zsqrtd.im_sub, Zsqrtd.im_one, Zsqrtd.im_zero, sub_zero] using him.symm
  · left
    have hre := congrArg (fun z : GaussianInt => z.re) h
    simpa only [Zsqrtd.re_add, Zsqrtd.re_zero, add_zero] using hre.symm
  · left
    have hre := congrArg (fun z : GaussianInt => z.re) h
    simpa only [Zsqrtd.re_sub, Zsqrtd.re_zero, sub_zero] using hre.symm

private theorem adjacentSymm :
    ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (FourNeighborAdjacent x y) → (FourNeighborAdjacent
        y x) := by
  classical
  intro x y ha
  rcases ha with ha | ha | ha | ha
  · right; left; rw [ha]; simp
  · left; rw [ha]; simp
  · right; right; right; rw [ha]; simp
  · right; right; left; rw [ha]; simp

private theorem cornerVH :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    (∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.re = y.re) → ((0 ≤ x.im) → ((0 ≤ y.im) →
        ((Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat) → (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1))))) → ((∀ (x : GaussianInt), ∀ (y
            : GaussianInt), (x.im = y.im) → ((0 ≤ x.re) → ((0 ≤ y.re) → ((Nat.dist (d x) (d y) =
        Nat.dist x.re.toNat y.re.toNat) → (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im)
        ∧ Nat.dist (d x) (d y) = 1))))) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt),
            (FourNeighborAdjacent x y) → (x.re = y.re ∨ x.im = y.im)) → (∀ (a : Nat), ∀ (b :
            Nat), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.re = (a:Int)) → ((y.im = (b:Int))
            → ((d x =
        Nat.dist x.im.toNat b) → ((d y = Nat.dist y.re.toNat a) → ((0 ≤ x.re) → ((0 ≤ x.im) → ((0
        ≤ y.re) → ((0 ≤ y.im) → (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1))))))))))) := by
  classical
  intro P B d lineVertical lineHorizontal adjacentCoordinates a b x y hxr hyi dVx dHy hxre hxim
      hyre hyim
  by_cases hR : x.re = y.re
  · have hyreRoot : y.re = (a:Int) := by omega
    have hcastY : y.re.toNat = a := by
      have hcast : (y.re.toNat : Int) = (a:Int) := by
        rw [Int.toNat_of_nonneg hyre, hyreRoot]
      exact_mod_cast hcast
    have hyimRoot : y.im.toNat = b := by
      have hcast : (y.im.toNat : Int) = (b:Int) := by
        rw [Int.toNat_of_nonneg hyim, hyi]
      exact_mod_cast hcast
    have hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat := by
      rw [dVx, dHy, hcastY, hyimRoot]
      simp [Nat.dist]
    exact lineVertical x y hR hxim hyim hlevel
  · by_cases hI : x.im = y.im
    · have hximRoot : x.im.toNat = b := by
        have hroot : x.im = (b:Int) := by omega
        have hcast : (x.im.toNat : Int) = (b:Int) := by
          rw [Int.toNat_of_nonneg hxim, hroot]
        exact_mod_cast hcast
      have hxreRoot : x.re.toNat = a := by
        have hcast : (x.re.toNat : Int) = (a:Int) := by
          rw [Int.toNat_of_nonneg hxre, hxr]
        exact_mod_cast hcast
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat := by
        rw [dVx, dHy, hximRoot, hxreRoot]
        simp [Nat.dist]; omega
      exact lineHorizontal x y hI hxre hyre hlevel
    · have hcoord : ¬ (x.re = y.re ∨ x.im = y.im) := by simp [hR, hI]
      have hadj : ¬ FourNeighborAdjacent x y := by
        intro h
        exact hcoord (adjacentCoordinates x y h)
      constructor
      · intro h
        exact False.elim (hadj h)
      · intro h
        exact False.elim (hcoord h.1)

private theorem cornerHV :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (FourNeighborAdjacent x y) → (FourNeighborAdjacent
        y x)) → ((∀ (a : Nat), ∀ (b : Nat), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.re =
        (a:Int)) → ((y.im = (b:Int)) → ((d x = Nat.dist x.im.toNat b) → ((d y = Nat.dist
        y.re.toNat a) → ((0 ≤ x.re) → ((0 ≤ x.im) → ((0 ≤ y.re) → ((0 ≤ y.im) →
        (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) =
        1))))))))) → (∀ (a : Nat), ∀ (b : Nat), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.im =
        (b:Int)) → ((y.re = (a:Int)) → ((d x = Nat.dist x.re.toNat a) → ((d y = Nat.dist
        y.im.toNat b) → ((0 ≤ x.re) → ((0 ≤ x.im) → ((0 ≤ y.re) → ((0 ≤ y.im) →
        (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)))))))))) := by
  classical
  intro P B d adjacentSymm cornerVH a b x y hxi hyr dHx dVy hxre hxim hyre hyim
  have h := cornerVH a b y x hyr hxi dVy dHx hyre hyim hxre hxim
  constructor
  · intro hadj
    have hrhs := h.mp (adjacentSymm hadj)
    refine ⟨?_, ?_⟩
    · rcases hrhs.1 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm
    · exact (Nat.dist_comm _ _).trans hrhs.2
  · rintro ⟨hcoord, hdist⟩
    have hcoord' : y.re = x.re ∨ y.im = x.im := by
      rcases hcoord with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm
    have hdist' : Nat.dist (d y) (d x) = 1 := by
      exact (Nat.dist_comm _ _).symm.trans hdist
    exact adjacentSymm (h.mpr ⟨hcoord', hdist'⟩)

end PathGeometryProof

namespace PathAdjacencyProof

private theorem smallZeroNeighbors :
    ∀ (P : FordFareyParameter),
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    let r := P.q₁
    let s := P.q₂
    ((0 : ℕ) < P.q₁) → ((∀ (x : GaussianInt), r < s → (x ∈ (P4062T1RemainderPaths P (0 : Fin (2
        : ℕ))).1 ↔ x.re = (↑P.q₁ : ℤ) ∧ (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q₁ : ℤ) ∨ x.im = (↑P.q₁ : ℤ)
        ∧ (1 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q₁ : ℤ))) → ((∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), a ≤ c → b ≤
        c → (a.dist c).dist (b.dist c) = a.dist b) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt),
        (x.re = y.re) → ((0 ≤ x.im) → ((0 ≤ y.im) → ((Nat.dist (d x) (d y) = Nat.dist x.im.toNat
        y.im.toNat) → (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d
        y) = 1))))) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.im = y.im) → ((0 ≤ x.re) →
        ((0 ≤ y.re) → ((Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat) →
        (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1))))) →
        (((r < s) → (∀ (x : GaussianInt), (x ∈ (B 0).1) → ((x.re = (r:Int)) → ((0 ≤ x.im) →
        ((x.im ≤ (r:Int)) → (d x = Nat.dist x.im.toNat r)))))) → (((r < s) → (∀ (x :
        GaussianInt), (x ∈ (B 0).1) → ((x.im = (r:Int)) → ((0 ≤ x.re) → ((x.re ≤ (r:Int)) → (d x
        = Nat.dist x.re.toNat r)))))) → ((∀ (a : Nat), ∀ (b : Nat), ∀ (x : GaussianInt), ∀ (y :
        GaussianInt), (x.re = (a:Int)) → ((y.im = (b:Int)) → ((d x = Nat.dist x.im.toNat b) → ((d
        y = Nat.dist y.re.toNat a) → ((0 ≤ x.re) → ((0 ≤ x.im) → ((0 ≤ y.re) → ((0 ≤ y.im) →
        (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) =
        1))))))))) → ((∀ (a : Nat), ∀ (b : Nat), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (x.im
        = (b:Int)) → ((y.re = (a:Int)) → ((d x = Nat.dist x.re.toNat a) → ((d y = Nat.dist
        y.im.toNat b) → ((0 ≤ x.re) → ((0 ≤ x.im) → ((0 ≤ y.re) → ((0 ≤ y.im) →
        (FourNeighborAdjacent x y ↔ (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) =
        1))))))))) → ((r < s) → (∀ (x : GaussianInt), (x ∈ (B 0).1) → (∀ (y : GaussianInt), (y ∈
        (B 0).1) → (FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)))))))))))) := by
  classical
  intro P B d r s hr memB0Small distDistDown lineVertical lineHorizontal dSmall0V dSmall0H
      cornerVH cornerHV hsmall x hx y hy
  have hxB : x ∈ (B 0).1 := by simpa using hx
  have hyB : y ∈ (B 0).1 := by simpa using hy
  have hxChar := (memB0Small x hsmall).mp hxB
  have hyChar := (memB0Small y hsmall).mp hyB
  rcases hxChar with hxV | hxH
  · rcases hyChar with hyV | hyH
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dSmall0V hsmall x hxB hxr (by omega) hxhi
      have dy := dSmall0V hsmall y hyB hyr (by omega) hyhi
      have hxn : x.im.toNat ≤ r := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.im)
        omega
      have hyn : y.im.toNat ≤ r := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.im)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat := by
        rw [dx, dy]
        exact distDistDown _ _ _ hxn hyn
      exact lineVertical x y (by omega) (by omega) (by omega) hlevel
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dSmall0V hsmall x hxB hxr (by omega) hxhi
      have dy := dSmall0H hsmall y hyB hyi (by omega) hyhi
      exact cornerVH r r x y hxr hyi dx dy (by omega) (by omega) (by omega) (by omega)
  · rcases hyChar with hyV | hyH
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dSmall0H hsmall x hxB hxi (by omega) hxhi
      have dy := dSmall0V hsmall y hyB hyr (by omega) hyhi
      exact cornerHV r r x y hxi hyr dx dy (by omega) (by omega) (by omega) (by omega)
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dSmall0H hsmall x hxB hxi (by omega) hxhi
      have dy := dSmall0H hsmall y hyB hyi (by omega) hyhi
      have hxn : x.re.toNat ≤ r := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.re)
        omega
      have hyn : y.re.toNat ≤ r := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.re)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat := by
        rw [dx, dy]
        exact distDistDown _ _ _ hxn hyn
      exact lineHorizontal x y (by omega) (by omega) (by omega) hlevel

private theorem smallOneNeighbors :
    ∀ (P : FordFareyParameter),
      let B := P4062T1RemainderPaths P;
      let d : GaussianInt → Nat := fun x =>
        let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
        (x.re - a.re).natAbs + (x.im - a.im).natAbs;
      let r := P.q₁;
      let s := P.q₂;
      P.q = P.q₁ + P.q₂ →
        (∀ (x : GaussianInt),
            r < s →
              (x ∈ (P4062T1RemainderPaths P (1 : Fin (2 : ℕ))).1 ↔
                x.re = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ) - (1 : ℤ) ∨
                  x.im = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) - (1 : ℤ))) →
          (∀ (a : ℕ),
              ∀ (b : ℕ), ∀ (c : ℕ), c ≤ a → c ≤ b → (a.dist c).dist (b.dist c) = a.dist b) →
            (∀ (x : GaussianInt),
                ∀ (y : GaussianInt),
                  x.re = y.re →
                    0 ≤ x.im →
                      0 ≤ y.im →
                        Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat →
                          (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
              (∀ (x : GaussianInt),
                  ∀ (y : GaussianInt),
                    x.im = y.im →
                      0 ≤ x.re →
                        0 ≤ y.re →
                          Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                (r < s →
                    ∀ (x : GaussianInt),
                      x ∈ (B 1).1 →
                        x.re = (s : Int) →
                          0 ≤ x.im → (s : Int) ≤ x.im → d x = Nat.dist x.im.toNat s) →
                  (r < s →
                      ∀ (x : GaussianInt),
                        x ∈ (B 1).1 →
                          x.im = (s : Int) →
                            0 ≤ x.re → (s : Int) ≤ x.re → d x = Nat.dist x.re.toNat s) →
                    (∀ (a : Nat),
                        ∀ (b : Nat),
                          ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.re = (a : Int) →
                            y.im = (b : Int) →
                            d x = Nat.dist x.im.toNat b →
                            d y = Nat.dist y.re.toNat a →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                      (∀ (a : Nat),
                          ∀ (b : Nat),
                            ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.im = (b : Int) →
                            y.re = (a : Int) →
                            d x = Nat.dist x.re.toNat a →
                            d y = Nat.dist y.im.toNat b →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                        r < s →
                          ∀ (x : GaussianInt),
                            x ∈ (B 1).1 →
                            ∀ (y : GaussianInt),
                            y ∈ (B 1).1 →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) := by
  classical
  intro P B d r s hsum memB1Small distDistUp lineVertical lineHorizontal dSmall1V dSmall1H
      cornerVH cornerHV hsmall x hx y hy
  have hxB : x ∈ (B 1).1 := by simpa using hx
  have hyB : y ∈ (B 1).1 := by simpa using hy
  have hxChar := (memB1Small x hsmall).mp hxB
  have hyChar := (memB1Small y hsmall).mp hyB
  rcases hxChar with hxV | hxH
  · rcases hyChar with hyV | hyH
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dSmall1V hsmall x hxB hxr (by omega) hxlo
      have dy := dSmall1V hsmall y hyB hyr (by omega) hylo
      have hxn : s ≤ x.im.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.im)
        omega
      have hyn : s ≤ y.im.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.im)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat := by
        rw [dx, dy]
        exact distDistUp _ _ _ hxn hyn
      exact lineVertical x y (by omega) (by omega) (by omega) hlevel
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dSmall1V hsmall x hxB hxr (by omega) hxlo
      have dy := dSmall1H hsmall y hyB hyi (by omega) hylo
      exact cornerVH s s x y hxr hyi dx dy (by omega) (by omega) (by omega) (by omega)
  · rcases hyChar with hyV | hyH
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dSmall1H hsmall x hxB hxi (by omega) hxlo
      have dy := dSmall1V hsmall y hyB hyr (by omega) hylo
      exact cornerHV s s x y hxi hyr dx dy (by omega) (by omega) (by omega) (by omega)
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dSmall1H hsmall x hxB hxi (by omega) hxlo
      have dy := dSmall1H hsmall y hyB hyi (by omega) hylo
      have hxn : s ≤ x.re.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.re)
        omega
      have hyn : s ≤ y.re.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.re)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat := by
        rw [dx, dy]
        exact distDistUp _ _ _ hxn hyn
      exact lineHorizontal x y (by omega) (by omega) (by omega) hlevel

private theorem largeZeroNeighbors :
    ∀ (P : FordFareyParameter),
      2 < P.q →
        let B := P4062T1RemainderPaths P;
        let d : GaussianInt → Nat := fun x =>
          let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
          (x.re - a.re).natAbs + (x.im - a.im).natAbs;
        let r := P.q₁;
        let s := P.q₂;
        P.q = P.q₁ + P.q₂ →
          (0 : ℕ) < P.q₁ →
            (∀ (x : GaussianInt),
                s < r →
                  (x ∈ (P4062T1RemainderPaths P (0 : Fin (2 : ℕ))).1 ↔
                    x.re = (↑P.q₁ : ℤ) ∧ (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q₂ : ℤ) ∨
                      x.im = (↑P.q₂ : ℤ) ∧
                        (↑P.q₁ : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) - (1 : ℤ))) →
              (∀ (a : ℕ),
                  ∀ (b : ℕ),
                    ∀ (c : ℕ), a ≤ c → b ≤ c → (a.dist c).dist (b.dist c) = a.dist b) →
                (∀ (a : ℕ),
                    ∀ (b : ℕ),
                      ∀ (c : ℕ), c ≤ a → c ≤ b → (a.dist c).dist (b.dist c) = a.dist b) →
                  (∀ (x : GaussianInt),
                      ∀ (y : GaussianInt),
                        x.re = y.re →
                          0 ≤ x.im →
                            0 ≤ y.im →
                            Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                    (∀ (x : GaussianInt),
                        ∀ (y : GaussianInt),
                          x.im = y.im →
                            0 ≤ x.re →
                            0 ≤ y.re →
                            Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                      (s < r →
                          ∀ (x : GaussianInt),
                            x ∈ (B 0).1 →
                            x.re = (r : Int) →
                            0 ≤ x.im → x.im ≤ (s : Int) → d x = Nat.dist x.im.toNat s) →
                        (s < r →
                            ∀ (x : GaussianInt),
                            x ∈ (B 0).1 →
                            x.im = (s : Int) →
                            0 ≤ x.re → (r : Int) ≤ x.re → d x = Nat.dist x.re.toNat r) →
                          (∀ (a : Nat),
                            ∀ (b : Nat),
                            ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.re = (a : Int) →
                            y.im = (b : Int) →
                            d x = Nat.dist x.im.toNat b →
                            d y = Nat.dist y.re.toNat a →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                            (∀ (a : Nat),
                            ∀ (b : Nat),
                            ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.im = (b : Int) →
                            y.re = (a : Int) →
                            d x = Nat.dist x.re.toNat a →
                            d y = Nat.dist y.im.toNat b →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                            s < r →
                            ∀ (x : GaussianInt),
                            x ∈ (B 0).1 →
                            ∀ (y : GaussianInt),
                            y ∈ (B 0).1 →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) := by
  classical
  intro P hP B d r s hsum hr memB0Large distDistDown distDistUp lineVertical lineHorizontal
      dLarge0V dLarge0H cornerVH cornerHV hlarge x hx y hy
  have hxB : x ∈ (B 0).1 := by simpa using hx
  have hyB : y ∈ (B 0).1 := by simpa using hy
  have hxChar := (memB0Large x hlarge).mp hxB
  have hyChar := (memB0Large y hlarge).mp hyB
  rcases hxChar with hxV | hxH
  · rcases hyChar with hyV | hyH
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dLarge0V hlarge x hxB hxr (by omega) hxhi
      have dy := dLarge0V hlarge y hyB hyr (by omega) hyhi
      have hxn : x.im.toNat ≤ s := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.im)
        omega
      have hyn : y.im.toNat ≤ s := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.im)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat := by
        rw [dx, dy]
        exact distDistDown _ _ _ hxn hyn
      exact lineVertical x y (by omega) (by omega) (by omega) hlevel
    · rcases hxV with ⟨hxr,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dLarge0V hlarge x hxB hxr (by omega) hxhi
      have dy := dLarge0H hlarge y hyB hyi (by omega) hylo
      exact cornerVH r s x y hxr hyi dx dy (by omega) (by omega) (by omega) (by omega)
  · rcases hyChar with hyV | hyH
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyV with ⟨hyr,hylo,hyhi⟩
      have dx := dLarge0H hlarge x hxB hxi (by omega) hxlo
      have dy := dLarge0V hlarge y hyB hyr (by omega) hyhi
      exact cornerHV r s x y hxi hyr dx dy (by omega) (by omega) (by omega) (by omega)
    · rcases hxH with ⟨hxi,hxlo,hxhi⟩
      rcases hyH with ⟨hyi,hylo,hyhi⟩
      have dx := dLarge0H hlarge x hxB hxi (by omega) hxlo
      have dy := dLarge0H hlarge y hyB hyi (by omega) hylo
      have hxn : r ≤ x.re.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.re)
        omega
      have hyn : r ≤ y.re.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.re)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat := by
        rw [dx, dy]
        exact distDistUp _ _ _ hxn hyn
      exact lineHorizontal x y (by omega) (by omega) (by omega) hlevel

private theorem largeOneNeighbors :
    ∀ (P : FordFareyParameter),
      2 < P.q →
        let B := P4062T1RemainderPaths P;
        let d : GaussianInt → Nat := fun x =>
          let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
          (x.re - a.re).natAbs + (x.im - a.im).natAbs;
        let r := P.q₁;
        let s := P.q₂;
        P.q = P.q₁ + P.q₂ →
          (0 : ℕ) < P.q₁ →
            (∀ (x : GaussianInt),
                s < r →
                  (x ∈ (P4062T1RemainderPaths P (1 : Fin (2 : ℕ))).1 ↔
                    x.im = (↑P.q₁ : ℤ) ∧ (1 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q₂ : ℤ) ∨
                      x.re = (↑P.q₂ : ℤ) ∧
                        (↑P.q₁ : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ) - (1 : ℤ))) →
              (∀ (a : ℕ),
                  ∀ (b : ℕ),
                    ∀ (c : ℕ), a ≤ c → b ≤ c → (a.dist c).dist (b.dist c) = a.dist b) →
                (∀ (a : ℕ),
                    ∀ (b : ℕ),
                      ∀ (c : ℕ), c ≤ a → c ≤ b → (a.dist c).dist (b.dist c) = a.dist b) →
                  (∀ (x : GaussianInt),
                      ∀ (y : GaussianInt),
                        x.re = y.re →
                          0 ≤ x.im →
                            0 ≤ y.im →
                            Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                    (∀ (x : GaussianInt),
                        ∀ (y : GaussianInt),
                          x.im = y.im →
                            0 ≤ x.re →
                            0 ≤ y.re →
                            Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                      (s < r →
                          ∀ (x : GaussianInt),
                            x ∈ (B 1).1 →
                            x.im = (r : Int) →
                            0 ≤ x.re → x.re ≤ (s : Int) → d x = Nat.dist x.re.toNat s) →
                        (s < r →
                            ∀ (x : GaussianInt),
                            x ∈ (B 1).1 →
                            x.re = (s : Int) →
                            0 ≤ x.im → (r : Int) ≤ x.im → d x = Nat.dist x.im.toNat r) →
                          (∀ (a : Nat),
                            ∀ (b : Nat),
                            ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.re = (a : Int) →
                            y.im = (b : Int) →
                            d x = Nat.dist x.im.toNat b →
                            d y = Nat.dist y.re.toNat a →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                            (∀ (a : Nat),
                            ∀ (b : Nat),
                            ∀ (x : GaussianInt),
                            ∀ (y : GaussianInt),
                            x.im = (b : Int) →
                            y.re = (a : Int) →
                            d x = Nat.dist x.re.toNat a →
                            d y = Nat.dist y.im.toNat b →
                            0 ≤ x.re →
                            0 ≤ x.im →
                            0 ≤ y.re →
                            0 ≤ y.im →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)) →
                            s < r →
                            ∀ (x : GaussianInt),
                            x ∈ (B 1).1 →
                            ∀ (y : GaussianInt),
                            y ∈ (B 1).1 →
                            (FourNeighborAdjacent x y ↔
                            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) := by
  classical
  intro P hP B d r s hsum hr memB1Large distDistDown distDistUp lineVertical lineHorizontal
      dLarge1V dLarge1H cornerVH cornerHV hlarge x hx y hy
  have hxB : x ∈ (B 1).1 := by simpa using hx
  have hyB : y ∈ (B 1).1 := by simpa using hy
  have hxChar := (memB1Large x hlarge).mp hxB
  have hyChar := (memB1Large y hlarge).mp hyB
  rcases hxChar with hxV | hxH
  · rcases hyChar with hyV | hyH
    · rcases hxV with ⟨hxi,hxlo,hxhi⟩
      rcases hyV with ⟨hyi,hylo,hyhi⟩
      have dx := dLarge1V hlarge x hxB hxi (by omega) hxhi
      have dy := dLarge1V hlarge y hyB hyi (by omega) hyhi
      have hxn : x.re.toNat ≤ s := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.re)
        omega
      have hyn : y.re.toNat ≤ s := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.re)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat := by
        rw [dx, dy]
        exact distDistDown _ _ _ hxn hyn
      exact lineHorizontal x y (by omega) (by omega) (by omega) hlevel
    · rcases hxV with ⟨hxi,hxlo,hxhi⟩
      rcases hyH with ⟨hyr,hylo,hyhi⟩
      have dx := dLarge1V hlarge x hxB hxi (by omega) hxhi
      have dy := dLarge1H hlarge y hyB hyr (by omega) hylo
      exact cornerHV s r x y hxi hyr dx dy (by omega) (by omega) (by omega) (by omega)
  · rcases hyChar with hyV | hyH
    · rcases hxH with ⟨hxr,hxlo,hxhi⟩
      rcases hyV with ⟨hyi,hylo,hyhi⟩
      have dx := dLarge1H hlarge x hxB hxr (by omega) hxlo
      have dy := dLarge1V hlarge y hyB hyi (by omega) hyhi
      exact cornerVH s r x y hxr hyi dx dy (by omega) (by omega) (by omega) (by omega)
    · rcases hxH with ⟨hxr,hxlo,hxhi⟩
      rcases hyH with ⟨hyr,hylo,hyhi⟩
      have dx := dLarge1H hlarge x hxB hxr (by omega) hxlo
      have dy := dLarge1H hlarge y hyB hyr (by omega) hylo
      have hxn : r ≤ x.im.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ x.im)
        omega
      have hyn : r ≤ y.im.toNat := by
        have hc := Int.toNat_of_nonneg (by omega : 0 ≤ y.im)
        omega
      have hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat := by
        rw [dx, dy]
        exact distDistUp _ _ _ hxn hyn
      exact lineVertical x y (by omega) (by omega) (by omega) hlevel

end PathAdjacencyProof

theorem P4112T1PathGeometry (P : FordFareyParameter) (hP : 2 < P.q) :
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    let W := P4062T1InteriorSquare P.q \ E
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    W = (B 0).1 ∪ (B 1).1 ∧ Disjoint (B 0).1 (B 1).1 ∧
    (∀ x ∈ (B 0).1, ∀ y ∈ (B 1).1, ¬ FourNeighborAdjacent x y) ∧
    (∀ j, ∀ x ∈ (B j).1, ∀ y ∈ (B j).1,
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) := by
-- BODY
  classical
  let A := P4062T1RecursiveInteriors P
  let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
  let W := P4062T1InteriorSquare P.q \ E
  let B := P4062T1RemainderPaths P
  let d : GaussianInt → Nat := fun x =>
    let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
    (x.re-a.re).natAbs + (x.im-a.im).natAbs
  change W = (B 0).1 ∪ (B 1).1 ∧ Disjoint (B 0).1 (B 1).1 ∧
    (∀ x ∈ (B 0).1, ∀ y ∈ (B 1).1, ¬ FourNeighborAdjacent x y) ∧
    (∀ j, ∀ x ∈ (B j).1, ∀ y ∈ (B j).1,
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1)
  let r := P.q₁
  let s := P.q₂
  have hsum := FordFareySum.denominatorSum P
  have hs := PathGeometryProof.hs P
  have hr := PathGeometryProof.hr P hP hsum
  have hrs := PathGeometryProof.hrs P hP hsum
  have horder := PathGeometryProof.horder P hrs
  have squareCoordinates (n : Nat) (x : GaussianInt) := PathGeometryProof.squareCoordinates n x
  have mem0 (x : GaussianInt) := PathGeometryProof.mem0 P
          squareCoordinates x
  have mem1 (x : GaussianInt) := PathGeometryProof.mem1 P hsum squareCoordinates x
  have mem2 (x : GaussianInt) := PathGeometryProof.mem2 P hsum squareCoordinates x
  have mem3 (x : GaussianInt) := PathGeometryProof.mem3 P hsum squareCoordinates x
  have memB0Large (x : GaussianInt) (hlarge : s < r) := PathGeometryProof.memB0Large P
            hsum hs hr squareCoordinates x hlarge
  have memB1Large (x : GaussianInt) (hlarge : s < r) := PathGeometryProof.memB1Large P
            hsum hs hr squareCoordinates x hlarge
  have memB0Small (x : GaussianInt) (hsmall : r < s) := PathGeometryProof.memB0Small P hsum hs hr
            squareCoordinates x hsmall
  have memB1Small (x : GaussianInt) (hsmall : r < s) := PathGeometryProof.memB1Small P
            hsum hs hr squareCoordinates x hsmall
  have partition := PathGeometryProof.partition P hP hsum hs hr horder
      squareCoordinates mem0 mem1 mem2 mem3 memB0Large memB1Large memB0Small memB1Small
  have hdisj := PathGeometryProof.hdisj P horder memB0Large memB1Large
      memB0Small memB1Small
  have hcross := PathGeometryProof.hcross P horder memB0Large memB1Large memB0Small memB1Small
  have natAbsToNat (z : Int) (hz : 0 ≤ z) := PathGeometryProof.natAbsToNat z hz
  have natAbsDist (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) := PathGeometryProof.natAbsDist
      natAbsToNat a b
          ha hb
  have distDistDown (a b c : Nat) (ha : a ≤ c) (hb : b ≤ c) := PathGeometryProof.distDistDown a
          b c ha hb
  have distDistUp (a b c : Nat) (ha : c ≤ a) (hb : c ≤ b) := PathGeometryProof.distDistUp a b
          c ha hb
  have natDistOneInt (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) := PathGeometryProof.natDistOneInt a b
          ha hb
  have adjacentVertical (x y : GaussianInt) (hfix : x.re = y.re) :=
      PathGeometryProof.adjacentVertical x y hfix
  have adjacentHorizontal (x y : GaussianInt) (hfix : x.im = y.im) :=
      PathGeometryProof.adjacentHorizontal x y hfix
  have lineVertical (x y : GaussianInt) (hfix : x.re = y.re)
      (hnx : 0 ≤ x.im) (hny : 0 ≤ y.im)
      (hlevel : Nat.dist (d x) (d y) = Nat.dist x.im.toNat y.im.toNat) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 := PathGeometryProof.lineVertical
            P natDistOneInt adjacentVertical x y hfix hnx hny hlevel
  have lineHorizontal (x y : GaussianInt) (hfix : x.im = y.im)
      (hnx : 0 ≤ x.re) (hny : 0 ≤ y.re)
      (hlevel : Nat.dist (d x) (d y) = Nat.dist x.re.toNat y.re.toNat) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 :=
            PathGeometryProof.lineHorizontal P natDistOneInt adjacentHorizontal x y hfix hnx hny
            hlevel
  have dLarge0Root (hlarge : s < r) (x : GaussianInt)
      (hx : x ∈ (B 0).1) :
      d x = (x.re-(r:Int)).natAbs + (x.im-(s:Int)).natAbs := PathGeometryProof.dLarge0Root P
          hlarge x hx
  have dLarge1Root (hlarge : s < r) (x : GaussianInt)
      (hx : x ∈ (B 1).1) :
      d x = (x.re-(s:Int)).natAbs + (x.im-(r:Int)).natAbs := PathGeometryProof.dLarge1Root P
          hdisj hlarge x hx
  have dSmall0Root (hsmall : r < s) (x : GaussianInt)
      (hx : x ∈ (B 0).1) :
      d x = (x.re-(r:Int)).natAbs + (x.im-(r:Int)).natAbs := PathGeometryProof.dSmall0Root P
          hsmall x hx
  have dSmall1Root (hsmall : r < s) (x : GaussianInt)
      (hx : x ∈ (B 1).1) :
      d x = (x.re-(s:Int)).natAbs + (x.im-(s:Int)).natAbs := PathGeometryProof.dSmall1Root P
          hdisj hsmall x hx
  have dLarge0V (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (hcoord : x.re = (r:Int)) (hpos : 0 ≤ x.im) (hbound : x.im ≤ (s:Int)) :
      d x = Nat.dist x.im.toNat s := PathGeometryProof.dLarge0V P natAbsDist dLarge0Root hlarge x
          hx hcoord hpos
  have dLarge0H (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (hcoord : x.im = (s:Int)) (hpos : 0 ≤ x.re) (hbound : (r:Int) ≤ x.re) :
      d x = Nat.dist x.re.toNat r := PathGeometryProof.dLarge0H P natAbsDist dLarge0Root hlarge x
          hx hcoord hpos
  have dLarge1V (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (hcoord : x.im = (r:Int)) (hpos : 0 ≤ x.re) (hbound : x.re ≤ (s:Int)) :
      d x = Nat.dist x.re.toNat s := PathGeometryProof.dLarge1V P natAbsDist dLarge1Root hlarge x
          hx hcoord hpos
  have dLarge1H (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (hcoord : x.re = (s:Int)) (hpos : 0 ≤ x.im) (hbound : (r:Int) ≤ x.im) :
      d x = Nat.dist x.im.toNat r := PathGeometryProof.dLarge1H P natAbsDist dLarge1Root hlarge x
          hx hcoord hpos
  have dSmall0V (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (hcoord : x.re = (r:Int)) (hpos : 0 ≤ x.im) (hbound : x.im ≤ (r:Int)) :
      d x = Nat.dist x.im.toNat r := PathGeometryProof.dSmall0V P natAbsDist dSmall0Root hsmall x
          hx hcoord hpos
  have dSmall0H (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (hcoord : x.im = (r:Int)) (hpos : 0 ≤ x.re) (hbound : x.re ≤ (r:Int)) :
      d x = Nat.dist x.re.toNat r := PathGeometryProof.dSmall0H P natAbsDist dSmall0Root hsmall x
          hx hcoord hpos
  have dSmall1V (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (hcoord : x.re = (s:Int)) (hpos : 0 ≤ x.im) (hbound : (s:Int) ≤ x.im) :
      d x = Nat.dist x.im.toNat s := PathGeometryProof.dSmall1V P natAbsDist dSmall1Root hsmall x
          hx hcoord hpos
  have dSmall1H (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (hcoord : x.im = (s:Int)) (hpos : 0 ≤ x.re) (hbound : (s:Int) ≤ x.re) :
      d x = Nat.dist x.re.toNat s := PathGeometryProof.dSmall1H P natAbsDist dSmall1Root hsmall x
          hx hcoord hpos
  have adjacentCoordinates (x y : GaussianInt) (ha : FourNeighborAdjacent x y) :=
      PathGeometryProof.adjacentCoordinates x y ha
  have adjacentSymm {x y : GaussianInt} (ha : FourNeighborAdjacent x y) :=
      PathGeometryProof.adjacentSymm (x := x) (y := y) ha
  have cornerVH (a b : Nat) (x y : GaussianInt)
      (hxr : x.re = (a:Int)) (hyi : y.im = (b:Int))
      (dVx : d x = Nat.dist x.im.toNat b)
      (dHy : d y = Nat.dist y.re.toNat a)
      (hxre : 0 ≤ x.re) (hxim : 0 ≤ x.im)
      (hyre : 0 ≤ y.re) (hyim : 0 ≤ y.im) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 := PathGeometryProof.cornerVH P
            lineVertical lineHorizontal adjacentCoordinates a b x y hxr hyi dVx dHy hxre hxim
            hyre hyim
  have cornerHV (a b : Nat) (x y : GaussianInt)
      (hxi : x.im = (b:Int)) (hyr : y.re = (a:Int))
      (dHx : d x = Nat.dist x.re.toNat a)
      (dVy : d y = Nat.dist y.im.toNat b)
      (hxre : 0 ≤ x.re) (hxim : 0 ≤ x.im)
      (hyre : 0 ≤ y.re) (hyim : 0 ≤ y.im) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 := PathGeometryProof.cornerHV P
            adjacentSymm cornerVH a b x y hxi hyr dHx dVy hxre hxim hyre hyim
  have smallZeroNeighbors (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (y : GaussianInt) (hy : y ∈ (B 0).1) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 :=
            PathAdjacencyProof.smallZeroNeighbors P hr memB0Small distDistDown lineVertical
            lineHorizontal dSmall0V dSmall0H cornerVH cornerHV hsmall x hx y hy
  have smallOneNeighbors (hsmall : r < s) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (y : GaussianInt) (hy : y ∈ (B 1).1) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 :=
            PathAdjacencyProof.smallOneNeighbors P hsum memB1Small distDistUp lineVertical
            lineHorizontal dSmall1V dSmall1H cornerVH cornerHV hsmall x hx y hy
  have largeZeroNeighbors (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 0).1)
      (y : GaussianInt) (hy : y ∈ (B 0).1) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 :=
            PathAdjacencyProof.largeZeroNeighbors P hP hsum hr memB0Large distDistDown
            distDistUp lineVertical lineHorizontal dLarge0V dLarge0H cornerVH cornerHV hlarge x
            hx y hy
  have largeOneNeighbors (hlarge : s < r) (x : GaussianInt) (hx : x ∈ (B 1).1)
      (y : GaussianInt) (hy : y ∈ (B 1).1) :
      FourNeighborAdjacent x y ↔
        (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1 :=
            PathAdjacencyProof.largeOneNeighbors P hP hsum hr memB1Large distDistDown
            distDistUp lineVertical lineHorizontal dLarge1V dLarge1H cornerVH cornerHV hlarge x
            hx y hy
  refine ⟨partition, hdisj, hcross, ?_⟩
  intro j x hx y hy
  rcases horder with hsmall | hlarge
  · fin_cases j
    · exact smallZeroNeighbors hsmall x hx y hy
    · exact smallOneNeighbors hsmall x hx y hy
  · fin_cases j
    · exact largeZeroNeighbors hlarge x hx y hy
    · exact largeOneNeighbors hlarge x hx y hy

end ApollonianSuperharmonic

end
