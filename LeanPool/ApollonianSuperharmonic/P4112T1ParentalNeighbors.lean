/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordFareySum

public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderPaths
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public meta import Lean.Meta.Tactic.NormCast
public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors

/-!
# P4112T1ParentalNeighbors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Classical decidability for four-neighbor adjacency on the Gaussian integer lattice. -/
@[instance_reducible] noncomputable def fourNeighborDecidability
    (x y : GaussianInt) : Decidable (FourNeighborAdjacent x y) := by
  classical
  infer_instance

attribute [local instance] fourNeighborDecidability


-- [TABLET NODE: P4112T1ParentalNeighbors]
namespace ParentalNeighborLemmas

private theorem adjacent_comm :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), FourNeighborAdjacent x y ↔ FourNeighborAdjacent y x
        := by
  classical
  intro x y
  constructor
  · intro h
    rcases h with h | h | h | h <;> subst y <;> simp [FourNeighborAdjacent]
  · intro h
    rcases h with h | h | h | h <;> subst x <;> simp [FourNeighborAdjacent]

private theorem neighbor_filter :
    (∀ (x : GaussianInt), ∀ (y : GaussianInt), FourNeighborAdjacent x y ↔ FourNeighborAdjacent y
        x) → (∀ (S : Finset GaussianInt), ∀ (x : GaussianInt), S.filter (fun y =>
        FourNeighborAdjacent y x) =
        ({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter
          (fun y => y ∈ S)) := by
  classical
  intro adjacent_comm S x
  ext y
  rw [Finset.mem_filter, Finset.mem_filter]
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  rw [adjacent_comm y x]
  unfold FourNeighborAdjacent
  tauto

private theorem q1pos :
    ∀ (P : FordFareyParameter), (2 < P.q) → (0 < P.q₁) := by
  classical
  intro P hP
  by_contra hz
  have hz : P.q₁ = 0 := by omega
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

private theorem q2posI :
    ∀ (P : FordFareyParameter), 0 < (P.q₂ : Int) := by
  classical
  intro P
  exact_mod_cast P.q₂_pos

private abbrev cross :=
  FordFareySum.determinant

private theorem unequal :
    ∀ (P : FordFareyParameter), (2 < P.q) → ((0 < (P.q₂ : Int)) → ((P.p₁ * (P.q₂ : Int) - (P.q₁ :
        Int) * P.p₂ = 1) → ((P.q = P.q₁ + P.q₂) → (P.q₁ ≠ P.q₂)))) := by
  classical
  intro P hP q2posI cross hsumN heq
  have hm : (P.q₁ : Int) * (P.p₁ - P.p₂) = 1 := by
    have hc := cross
    rw [heq] at hc
    nlinarith [hc]
  have hd : (P.q₁ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, hm.symm⟩
  have hu : (P.q₁ : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le P.q₁)) hd
  have hq1 : P.q₁ = 1 := by exact_mod_cast hu
  have hq2 : P.q₂ = 1 := by omega
  have hq : P.q = 2 := by omega
  have hqgt : 2 < P.q := by exact_mod_cast hP
  omega

private theorem hsum :
    ∀ (P : FordFareyParameter), (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
  classical
  intro P
  exact_mod_cast P.sum_q

private theorem squareCoordinates :
    ∀ (n : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare n ↔
        1 ≤ z.re ∧ z.re ≤ (n : Int) - 1 ∧
        1 ≤ z.im ∧ z.im ≤ (n : Int) - 1 := by
  classical
  intro n z
  unfold P4062T1InteriorSquare
  constructor
  · intro hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
      (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
  · intro hz
    exact Finset.mem_image.mpr ⟨(z.re, z.im),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hz.1, hz.2.1⟩,
        Finset.mem_Icc.mpr hz.2.2⟩, by cases z; rfl⟩

private theorem mem0 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (∀ (n : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare n ↔ 1 ≤ z.re ∧ z.re ≤ (n :
        Int) - 1 ∧ 1 ≤ z.im ∧ z.im ≤ (n : Int) - 1) → (∀ (z : GaussianInt), z ∈ A 0 ↔
      1 ≤ z.re ∧ z.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ z.im ∧ z.im ≤ (P.q₁ : Int)-1) := by
  classical
  intro P A squareCoordinates z
  simpa [A, P4062T1RecursiveInteriors] using (squareCoordinates P.q₁ z)

private theorem mem1 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare n ↔ 1 ≤
        z.re ∧ z.re ≤ (n : Int) - 1 ∧ 1 ≤ z.im ∧ z.im ≤ (n : Int) - 1) → (∀ (z : GaussianInt), z
        ∈ A 1 ↔
      (P.q₂ : Int)+1 ≤ z.re ∧ z.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ z.im ∧ z.im ≤ (P.q : Int)-1)) := by
  classical
  intro P A hsumN squareCoordinates z
  dsimp [A, P4062T1RecursiveInteriors]
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hb := (squareCoordinates P.q₁ w).mp hw
    simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
    constructor <;> omega
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₁ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp []

private theorem mem2 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare n ↔ 1 ≤
        z.re ∧ z.re ≤ (n : Int) - 1 ∧ 1 ≤ z.im ∧ z.im ≤ (n : Int) - 1) → (∀ (z : GaussianInt), z
        ∈ A 2 ↔
      (P.q₁ : Int)+1 ≤ z.re ∧ z.re ≤ (P.q : Int)-1 ∧
      1 ≤ z.im ∧ z.im ≤ (P.q₂ : Int)-1)) := by
  classical
  intro P A hsumN squareCoordinates z
  dsimp [A, P4062T1RecursiveInteriors]
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hb := (squareCoordinates P.q₂ w).mp hw
    simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
    constructor <;> omega
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z - ⟨(P.q₁ : Int), 0⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₂ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp []

private theorem mem3 :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    (P.q = P.q₁ + P.q₂) → ((∀ (n : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare n ↔ 1 ≤
        z.re ∧ z.re ≤ (n : Int) - 1 ∧ 1 ≤ z.im ∧ z.im ≤ (n : Int) - 1) → (∀ (z : GaussianInt), z
        ∈ A 3 ↔
      1 ≤ z.re ∧ z.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ z.im ∧ z.im ≤ (P.q : Int)-1)) := by
  classical
  intro P A hsumN squareCoordinates z
  dsimp [A, P4062T1RecursiveInteriors]
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hb := (squareCoordinates P.q₂ w).mp hw
    simp only [Zsqrtd.re_add, Zsqrtd.im_add] at *
    constructor <;> omega
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z - ⟨0, (P.q₁ : Int)⟩, ?_, ?_⟩
    · apply (squareCoordinates P.q₂ _).mpr
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      constructor <;> omega
    · ext <;> simp []

private theorem hmem :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (z : GaussianInt), z ∈ A 0 ↔ 1
        ≤ z.re ∧ z.re ≤ (P.q₁ : Int)-1 ∧ 1 ≤ z.im ∧ z.im ≤ (P.q₁ : Int)-1) → ((∀ (z :
        GaussianInt), z ∈ A 1 ↔ (P.q₂ : Int)+1 ≤ z.re ∧ z.re ≤ (P.q : Int)-1 ∧ (P.q₂ : Int)+1 ≤
        z.im ∧ z.im ≤ (P.q : Int)-1) → ((∀ (z : GaussianInt), z ∈ A 2 ↔ (P.q₁ : Int)+1 ≤ z.re ∧
        z.re ≤ (P.q : Int)-1 ∧ 1 ≤ z.im ∧ z.im ≤ (P.q₂ : Int)-1) → ((∀ (z : GaussianInt), z ∈ A 3
        ↔ 1 ≤ z.re ∧ z.re ≤ (P.q₂ : Int)-1 ∧ (P.q₁ : Int)+1 ≤ z.im ∧ z.im ≤ (P.q : Int)-1) → (∀
        (a : Int), ∀ (b : Int), (⟨a, b⟩ : GaussianInt) ∈ E ↔
      (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨
      (P.q₂ < a ∧ a < P.q ∧ P.q₂ < b ∧ b < P.q) ∨
      (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨
      (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b < P.q))))))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN mem0 mem1 mem2 mem3 a b
  dsimp [E]
  simp only [Finset.mem_union, mem0, mem1, mem2, mem3]
  constructor <;> intro hz <;> omega

private theorem transpose_involutive :
    let transpose (z : GaussianInt) : GaussianInt := ⟨z.im, z.re⟩
    ∀ (z : GaussianInt), transpose (transpose z) = z := by
  classical
  intro transpose z
  cases z
  rfl

private theorem transpose_mem :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (
    let transpose (z : GaussianInt) : GaussianInt := ⟨z.im, z.re⟩
    ∀ (z : GaussianInt), z ∈ E ↔ transpose z ∈ E))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN hmem transpose z
  cases z with
  | mk a b =>
    dsimp [transpose]
    simp only [hmem]
    constructor <;> intro hz <;> omega

private theorem transpose_candidate :
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    let transpose (z : GaussianInt) : GaussianInt := ⟨z.im, z.re⟩
    ∀ (x : GaussianInt),
      ∀ (z : GaussianInt), z ∈ candidate x ↔ transpose z ∈ candidate (transpose x) := by
  classical
  intro candidate transpose x z
  cases x with
  | mk a b =>
    cases z with
    | mk c d =>
      simp [candidate, transpose, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
        Zsqrtd.ext_iff]
      omega

private theorem transpose_filter_card :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    let transpose (z : GaussianInt) : GaussianInt := ⟨z.im, z.re⟩
    (∀ (z : GaussianInt), transpose (transpose z) = z) → ((∀ (z : GaussianInt), z ∈ E ↔ transpose
        z ∈ E) → ((∀ (x : GaussianInt), ∀ (z : GaussianInt), z ∈ candidate x ↔ transpose z ∈
        candidate (transpose x)) → (∀ (x : GaussianInt), (Finset.filter (fun z => z ∈ E)
        (candidate x)).card =
        (Finset.filter (fun z => z ∈ E) (candidate (transpose x))).card))) := by
  classical
  intro P A E candidate transpose transpose_involutive transpose_mem transpose_candidate x
  apply Finset.card_bij (fun z hz => transpose z)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzC, hzE⟩
    exact Finset.mem_filter.mpr
      ⟨(transpose_candidate x z).mp hzC, (transpose_mem z).mp hzE⟩
  · intro z hz w hw h
    have := congrArg transpose h
    simpa [transpose_involutive] using this
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzC, hzE⟩
    refine ⟨transpose z, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (transpose_candidate (transpose x) z).mp hzC
    · exact (transpose_mem z).mp hzE
    · simp [transpose_involutive]

private theorem rowRVertical :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (∀ (u : Int), ∀ (v : Int), (1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧
      1 ≤ v ∧ v ≤ (P.q : Int)-1) → ((u = P.q₁ ∧ v ≤ P.q₂) → ((P.q₂ <
          P.q₁) → ((({(⟨u, v⟩ : GaussianInt) + 1, ⟨u, v⟩ - 1,
        ⟨u, v⟩ + ⟨0, 1⟩, ⟨u, v⟩ - ⟨0, 1⟩} : Finset GaussianInt).filter
          (fun y => y ∈ E)).card = 2)))))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN hmem u v hb hl ho
  rcases hl with ⟨rfl, hv⟩
  by_cases hroot : v = P.q₂
  · subst v
    have hleft0 : (⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ : GaussianInt) ∈ E := by
      apply (hmem _ _).2
      left
      constructor <;> omega
    have hup0 : (⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ : GaussianInt) ∈ E := by
      apply (hmem _ _).2
      right
      left
      constructor <;> omega
    have hright0 : (⟨(P.q₁ : Int)+1, (P.q₂ : Int)⟩ : GaussianInt) ∉ E := by
      intro hz
      have hz' := (hmem _ _).1 hz
      omega
    have hdown0 : (⟨(P.q₁ : Int), (P.q₂ : Int)-1⟩ : GaussianInt) ∉ E := by
      intro hz
      have hz' := (hmem _ _).1 hz
      omega
    have hleft : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1) ∈ E := by
      rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1 =
        ⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
      exact hleft0
    have hup : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ∈ E := by
      rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩ =
        ⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ by ext <;> simp []]
      exact hup0
    have hright : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + 1) ∉ E := by
      rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + 1 =
        ⟨(P.q₁ : Int)+1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
      exact hright0
    have hdown : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) ∉ E := by
      rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩ =
        ⟨(P.q₁ : Int), (P.q₂ : Int)-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
      exact hdown0
    have hne : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1) ≠
        (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ + ⟨0, 1⟩) := by
      intro he
      have hr := congrArg (fun z : GaussianInt => z.re) he
      simp only [Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_one] at hr
      omega
    have hne' : (⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ : GaussianInt) ≠
        ⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ := by
      intro he
      have hr := congrArg (fun z : GaussianInt => z.re) he
      simp at hr
    simp [Finset.filter_insert, Finset.filter_singleton,
      hleft, hright, hdown, hup0,
      Zsqrtd.ext_iff]
  · have hvlt : v < P.q₂ := by omega
    have hleft0 : (⟨(P.q₁ : Int)-1, v⟩ : GaussianInt) ∈ E := by
      apply (hmem _ _).2
      left
      constructor <;> omega
    have hright0 : (⟨(P.q₁ : Int)+1, v⟩ : GaussianInt) ∈ E := by
      apply (hmem _ _).2
      right
      right
      left
      constructor <;> omega
    have hup0 : (⟨(P.q₁ : Int), v+1⟩ : GaussianInt) ∉ E := by
      intro hz
      have hz' := (hmem _ _).1 hz
      omega
    have hdown0 : (⟨(P.q₁ : Int), v-1⟩ : GaussianInt) ∉ E := by
      intro hz
      have hz' := (hmem _ _).1 hz
      omega
    have hleft : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) - 1) ∈ E := by
      rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) - 1 =
        ⟨(P.q₁ : Int)-1, v⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
      exact hleft0
    have hright : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1) ∈ E := by
      rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1 =
        ⟨(P.q₁ : Int)+1, v⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
      exact hright0
    have hup : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + ⟨0, 1⟩) ∉ E := by
      rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) + ⟨0, 1⟩ =
        ⟨(P.q₁ : Int), v+1⟩ by ext <;> simp []]
      exact hup0
    have hdown : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) - ⟨0, 1⟩) ∉ E := by
      rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) - ⟨0, 1⟩ =
        ⟨(P.q₁ : Int), v-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
      exact hdown0
    have hne : (⟨(P.q₁ : Int)-1, v⟩ : GaussianInt) ≠
        ⟨(P.q₁ : Int)+1, v⟩ := by
      intro he
      have hr := congrArg (fun z : GaussianInt => z.re) he
      simp at hr
      omega
    have hne' : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1) ≠
        (⟨(P.q₁ : Int), v⟩ - 1) := by
      intro he
      have hr := congrArg (fun z : GaussianInt => z.re) he
      simp at hr
      omega
    simp [Finset.filter_insert, Finset.filter_singleton,
      hleft, hright, hdown, hup0,
      hne']

private theorem rowR :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (∀ (u : Int), ∀ (v : Int), (1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧
      1 ≤ v ∧ v ≤ (P.q : Int)-1) → (((u = P.q₁ ∧ v ≤ P.q₂) ∨ (v = P.q₂ ∧ P.q₁ ≤ u)) → ((P.q₂ <
          P.q₁) → ((({(⟨u, v⟩ : GaussianInt) + 1, ⟨u, v⟩ - 1,
        ⟨u, v⟩ + ⟨0, 1⟩, ⟨u, v⟩ - ⟨0, 1⟩} : Finset GaussianInt).filter
          (fun y => y ∈ E)).card = 2)))))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN hmem u v hb hl ho
  rcases hl with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
  · exact rowRVertical P hP q1pos q2posI hsumN hmem _ v hb ⟨rfl, hv⟩ ho
  · by_cases hroot : u = P.q₁
    · subst u
      have hleft0 : (⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        left
        constructor <;> omega
      have hup0 : (⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        right
        left
        constructor <;> omega
      have hright0 : (⟨(P.q₁ : Int)+1, (P.q₂ : Int)⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hdown0 : (⟨(P.q₁ : Int), (P.q₂ : Int)-1⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hleft : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1) ∈ E := by
        rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1 =
          ⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hleft0
      have hup : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ∈ E := by
        rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩ =
          ⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ by ext <;> simp []]
        exact hup0
      have hright : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + 1) ∉ E := by
        rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) + 1 =
          ⟨(P.q₁ : Int)+1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
        exact hright0
      have hdown : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) ∉ E := by
        rw [show (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩ =
          ⟨(P.q₁ : Int), (P.q₂ : Int)-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hdown0
      have hne : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1) ≠
          (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ + ⟨0, 1⟩) := by
        intro he
        have hr := congrArg (fun z : GaussianInt => z.re) he
        simp only [Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_one] at hr
        omega
      have hne' : (⟨(P.q₁ : Int)-1, (P.q₂ : Int)⟩ : GaussianInt) ≠
          ⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ := by
        intro he
        have hr := congrArg (fun z : GaussianInt => z.re) he
        simp at hr
      have hneDirect : ((⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) - 1) ≠
          ⟨(P.q₁ : Int), (P.q₂ : Int)+1⟩ := by
        intro he
        have hr := congrArg (fun z : GaussianInt => z.re) he
        simp at hr
      simp [Finset.filter_insert, Finset.filter_singleton,
        hleft, hright, hdown, hup0,
        hneDirect]
    · have hult : P.q₁ < u := by omega
      have hdown0 : (⟨u, (P.q₂ : Int)-1⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        right
        right
        left
        constructor <;> omega
      have hup0 : (⟨u, (P.q₂ : Int)+1⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        right
        left
        constructor <;> omega
      have hleft0 : (⟨u-1, (P.q₂ : Int)⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hright0 : (⟨u+1, (P.q₂ : Int)⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hdown : ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) ∈ E := by
        rw [show (⟨u, (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩ =
          ⟨u, (P.q₂ : Int)-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hdown0
      have hup : ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ∈ E := by
        rw [show (⟨u, (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩ =
          ⟨u, (P.q₂ : Int)+1⟩ by ext <;> simp []]
        exact hup0
      have hleft : ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) - 1) ∉ E := by
        rw [show (⟨u, (P.q₂ : Int)⟩ : GaussianInt) - 1 =
          ⟨u-1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hleft0
      have hright : ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) + 1) ∉ E := by
        rw [show (⟨u, (P.q₂ : Int)⟩ : GaussianInt) + 1 =
          ⟨u+1, (P.q₂ : Int)⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
        exact hright0
      have hne : (⟨u, (P.q₂ : Int)-1⟩ : GaussianInt) ≠
          ⟨u, (P.q₂ : Int)+1⟩ := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp at hi
        omega
      have hne' : ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ≠
          (⟨u, (P.q₂ : Int)⟩ - ⟨0, 1⟩) := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp at hi
        omega
      have hneDirect : (⟨u, (P.q₂ : Int)+1⟩ : GaussianInt) ≠
          ((⟨u, (P.q₂ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp at hi
        omega
      simp [Finset.filter_insert, Finset.filter_singleton,
        hleft, hright, hdown, hup0,
        hneDirect]

private theorem rowSmallRoot :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    (P.q₁ < P.q₂) → ((Finset.filter (fun z => z ∈ E) (candidate ⟨(P.q₁ : Int), (P.q₁ :
        Int)⟩)).card = 2)))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN hmem candidate ho
  have hright0 : (⟨(P.q₁ : Int)+1, (P.q₁ : Int)⟩ : GaussianInt) ∈ E := by
    apply (hmem _ _).2
    right
    right
    left
    constructor <;> omega
  have hup0 : (⟨(P.q₁ : Int), (P.q₁ : Int)+1⟩ : GaussianInt) ∈ E := by
    apply (hmem _ _).2
    right
    right
    right
    constructor <;> omega
  have hleft0 : (⟨(P.q₁ : Int)-1, (P.q₁ : Int)⟩ : GaussianInt) ∉ E := by
    intro hz
    have hz' := (hmem _ _).1 hz
    omega
  have hdown0 : (⟨(P.q₁ : Int), (P.q₁ : Int)-1⟩ : GaussianInt) ∉ E := by
    intro hz
    have hz' := (hmem _ _).1 hz
    omega
  have hright : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + 1) ∈ E := by
    rw [show (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + 1 =
      ⟨(P.q₁ : Int)+1, (P.q₁ : Int)⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
    exact hright0
  have hup : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ∈ E := by
    rw [show (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩ =
      ⟨(P.q₁ : Int), (P.q₁ : Int)+1⟩ by ext <;> simp []]
    exact hup0
  have hleft : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) - 1) ∉ E := by
    rw [show (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) - 1 =
      ⟨(P.q₁ : Int)-1, (P.q₁ : Int)⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
    exact hleft0
  have hdown : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) ∉ E := by
    rw [show (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) - ⟨0, 1⟩ =
      ⟨(P.q₁ : Int), (P.q₁ : Int)-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
    exact hdown0
  have hne : (⟨(P.q₁ : Int)+1, (P.q₁ : Int)⟩ : GaussianInt) ≠
      ⟨(P.q₁ : Int), (P.q₁ : Int)+1⟩ := by
    intro he
    have hr := congrArg (fun z : GaussianInt => z.re) he
    simp at hr
  have hne' : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + 1) ≠
      ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) := by
    intro he
    have hr := congrArg (fun z : GaussianInt => z.re) he
    simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr
    omega
  have hneDirect : ((⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) + 1) ≠
      ⟨(P.q₁ : Int), (P.q₁ : Int)+1⟩ := by
    intro he
    have hr := congrArg (fun z : GaussianInt => z.re) he
    simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr
    omega
  simp [candidate, Finset.filter_insert, Finset.filter_singleton,
    hleft, hright, hdown, hup0, hneDirect]

private theorem rowSmall :
    ∀ (P : FordFareyParameter), (2 < P.q) → (
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    ((P.q₁ < P.q₂) → ((Finset.filter (fun z => z ∈ E) (candidate ⟨(P.q₁ : Int), (P.q₁ :
        Int)⟩)).card = 2)) → (∀ (u : Int), ∀ (v : Int), (1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧
      1 ≤ v ∧ v ≤ (P.q : Int)-1) → (((u = P.q₁ ∧ v ≤ P.q₁) ∨ (v = P.q₁ ∧ u ≤ P.q₁)) → ((P.q₁ <
          P.q₂) → ((Finset.filter (fun z => z ∈ E) (candidate ⟨u, v⟩)).card = 2))))))))) := by
  classical
  intro P hP A E q1pos q2posI hsumN hmem candidate rowSmallRoot u v hb hl ho
  rcases hl with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
  · by_cases hroot : v = P.q₁
    · subst v
      exact rowSmallRoot ho
    · have hvlt : v < P.q₁ := by omega
      have hleft0 : (⟨(P.q₁ : Int)-1, v⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        left
        constructor <;> omega
      have hright0 : (⟨(P.q₁ : Int)+1, v⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        right
        right
        left
        constructor <;> omega
      have hup0 : (⟨(P.q₁ : Int), v+1⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hdown0 : (⟨(P.q₁ : Int), v-1⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hleft : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) - 1) ∈ E := by
        rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) - 1 =
          ⟨(P.q₁ : Int)-1, v⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hleft0
      have hright : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1) ∈ E := by
        rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1 =
          ⟨(P.q₁ : Int)+1, v⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
        exact hright0
      have hup : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + ⟨0, 1⟩) ∉ E := by
        rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) + ⟨0, 1⟩ =
          ⟨(P.q₁ : Int), v+1⟩ by ext <;> simp []]
        exact hup0
      have hdown : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) - ⟨0, 1⟩) ∉ E := by
        rw [show (⟨(P.q₁ : Int), v⟩ : GaussianInt) - ⟨0, 1⟩ =
          ⟨(P.q₁ : Int), v-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hdown0
      have hne : ((⟨(P.q₁ : Int), v⟩ : GaussianInt) + 1) ≠
          (⟨(P.q₁ : Int), v⟩ - 1) := by
        intro he
        have hr := congrArg (fun z : GaussianInt => z.re) he
        simp at hr
        omega
      simp [candidate, Finset.filter_insert, Finset.filter_singleton,
        hleft, hright, hdown, hup0, hne]
  · by_cases hroot : u = P.q₁
    · subst u
      exact rowSmallRoot ho
    · have hult : u < P.q₁ := by omega
      have hdown0 : (⟨u, (P.q₁ : Int)-1⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        left
        constructor <;> omega
      have hup0 : (⟨u, (P.q₁ : Int)+1⟩ : GaussianInt) ∈ E := by
        apply (hmem _ _).2
        right
        right
        right
        constructor <;> omega
      have hleft0 : (⟨u-1, (P.q₁ : Int)⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hright0 : (⟨u+1, (P.q₁ : Int)⟩ : GaussianInt) ∉ E := by
        intro hz
        have hz' := (hmem _ _).1 hz
        omega
      have hdown : ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) ∈ E := by
        rw [show (⟨u, (P.q₁ : Int)⟩ : GaussianInt) - ⟨0, 1⟩ =
          ⟨u, (P.q₁ : Int)-1⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hdown0
      have hup : ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ∈ E := by
        rw [show (⟨u, (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩ =
          ⟨u, (P.q₁ : Int)+1⟩ by ext <;> simp []]
        exact hup0
      have hleft : ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) - 1) ∉ E := by
        rw [show (⟨u, (P.q₁ : Int)⟩ : GaussianInt) - 1 =
          ⟨u-1, (P.q₁ : Int)⟩ by ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub]]
        exact hleft0
      have hright : ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) + 1) ∉ E := by
        rw [show (⟨u, (P.q₁ : Int)⟩ : GaussianInt) + 1 =
          ⟨u+1, (P.q₁ : Int)⟩ by ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]]
        exact hright0
      have hne : (⟨u, (P.q₁ : Int)-1⟩ : GaussianInt) ≠
          ⟨u, (P.q₁ : Int)+1⟩ := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp at hi
        omega
      have hne' : ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) + ⟨0, 1⟩) ≠
          (⟨u, (P.q₁ : Int)⟩ - ⟨0, 1⟩) := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp only [Zsqrtd.im_add, Zsqrtd.im_sub] at hi
        omega
      have hneDirect : (⟨u, (P.q₁ : Int)+1⟩ : GaussianInt) ≠
          ((⟨u, (P.q₁ : Int)⟩ : GaussianInt) - ⟨0, 1⟩) := by
        intro he
        have hi := congrArg (fun z : GaussianInt => z.im) he
        simp only [Zsqrtd.im_sub] at hi
        omega
      simp [candidate, Finset.filter_insert, Finset.filter_singleton,
        hleft, hright, hdown, hup0, hneDirect]

private theorem reflect_involutive :
    ∀ (P : FordFareyParameter), ((P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int)) → (
    let reflect (z : GaussianInt) : GaussianInt :=
      ⟨(P.q : Int) - z.re, (P.q : Int) - z.im⟩
    ∀ (z : GaussianInt), reflect (reflect z) = z) := by
  classical
  intro P hsum reflect z
  cases z
  simp [reflect, hsum]

private theorem reflect_mem :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    (0 < P.q₁) → ((0 < (P.q₂ : Int)) → ((P.q = P.q₁ + P.q₂) → ((∀ (a : Int), ∀ (b : Int), (⟨a, b⟩
        : GaussianInt) ∈ E ↔ (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨ (P.q₂ < a ∧ a < P.q ∧ P.q₂ <
        b ∧ b < P.q) ∨ (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨ (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b
        < P.q)) → (
    let reflect (z : GaussianInt) : GaussianInt :=
      ⟨(P.q : Int) - z.re, (P.q : Int) - z.im⟩
    ∀ (z : GaussianInt), z ∈ E ↔ reflect z ∈ E)))) := by
  classical
  intro P A E q1pos q2posI hsumN hmem reflect z
  cases z with
  | mk a b =>
    dsimp [reflect]
    simp only [hmem]
    constructor <;> intro hz <;> rcases hz with hz | hz | hz | hz <;> omega

private theorem reflect_candidate :
    ∀ (P : FordFareyParameter),
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    let reflect (z : GaussianInt) : GaussianInt :=
      ⟨(P.q : Int) - z.re, (P.q : Int) - z.im⟩
    ∀ (x : GaussianInt), ∀ (z : GaussianInt), z ∈ candidate x ↔ reflect z ∈ candidate (reflect x)
        := by
  classical
  intro P candidate reflect x z
  cases x with
  | mk a b =>
    cases z with
    | mk c d =>
      simp [candidate, reflect, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
        Zsqrtd.ext_iff]
      omega

private theorem reflect_filter_card :
    ∀ (P : FordFareyParameter),
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    let candidate (z : GaussianInt) : Finset GaussianInt :=
      {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
    let reflect (z : GaussianInt) : GaussianInt :=
      ⟨(P.q : Int) - z.re, (P.q : Int) - z.im⟩
    (∀ (z : GaussianInt), reflect (reflect z) = z) → ((∀ (z : GaussianInt), z ∈ E ↔ reflect z ∈
        E) → ((∀ (x : GaussianInt), ∀ (z : GaussianInt), z ∈ candidate x ↔ reflect z ∈ candidate
        (reflect x)) → (∀ (x : GaussianInt), (Finset.filter (fun z => z ∈ E) (candidate x)).card =
        (Finset.filter (fun z => z ∈ E) (candidate (reflect x))).card))) := by
  classical
  intro P A E candidate reflect reflect_involutive reflect_mem reflect_candidate x
  apply Finset.card_bij (fun z hz => reflect z)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzC, hzE⟩
    exact Finset.mem_filter.mpr
      ⟨(reflect_candidate x z).mp hzC, (reflect_mem z).mp hzE⟩
  · intro z hz w hw h
    have := congrArg reflect h
    simpa [reflect_involutive] using this
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzC, hzE⟩
    refine ⟨reflect z, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [reflect_involutive] using (reflect_candidate (reflect x) z).mp hzC
    · exact (reflect_mem z).mp hzE
    · simp [reflect_involutive]

end ParentalNeighborLemmas

theorem P4112T1ParentalNeighbors (P : FordFareyParameter) (hP : 2 < P.q) :
    let A := P4062T1RecursiveInteriors P
    let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
    let B := P4062T1RemainderPaths P
    ∀ j, ∀ x ∈ (B j).1,
      (E.filter (fun y => FourNeighborAdjacent y x)).card = 2 := by
-- BODY
  classical
  have adjacent_comm (x y : GaussianInt) :
      FourNeighborAdjacent x y ↔ FourNeighborAdjacent y x := ParentalNeighborLemmas.adjacent_comm
          x y
  have neighbor_filter (S : Finset GaussianInt) (x : GaussianInt) :
      S.filter (fun y => FourNeighborAdjacent y x) =
        ({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter
          (fun y => y ∈ S) := ParentalNeighborLemmas.neighbor_filter adjacent_comm S x
  let A := P4062T1RecursiveInteriors P
  let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
  let B := P4062T1RemainderPaths P
  change ∀ j, ∀ x ∈ (B j).1,
    (E.filter (fun y => FourNeighborAdjacent y x)).card = 2
  intro j x hx
  rw [neighbor_filter]
  have q1pos : 0 < P.q₁ := ParentalNeighborLemmas.q1pos P hP
  have q2posI : 0 < (P.q₂ : Int) := ParentalNeighborLemmas.q2posI P
  have cross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := ParentalNeighborLemmas.cross P
  have hsumN := FordFareySum.denominatorSum P
  have unequal : P.q₁ ≠ P.q₂ := ParentalNeighborLemmas.unequal P hP q2posI cross hsumN
  have hsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := ParentalNeighborLemmas.hsum P
  have squareCoordinates (n : Nat) (z : GaussianInt) :
      z ∈ P4062T1InteriorSquare n ↔
        1 ≤ z.re ∧ z.re ≤ (n : Int) - 1 ∧
        1 ≤ z.im ∧ z.im ≤ (n : Int) - 1 := ParentalNeighborLemmas.squareCoordinates n z
  have mem0 (z : GaussianInt) : z ∈ A 0 ↔
      1 ≤ z.re ∧ z.re ≤ (P.q₁ : Int)-1 ∧
      1 ≤ z.im ∧ z.im ≤ (P.q₁ : Int)-1 := ParentalNeighborLemmas.mem0 P squareCoordinates z
  have mem1 (z : GaussianInt) : z ∈ A 1 ↔
      (P.q₂ : Int)+1 ≤ z.re ∧ z.re ≤ (P.q : Int)-1 ∧
      (P.q₂ : Int)+1 ≤ z.im ∧ z.im ≤ (P.q : Int)-1 := ParentalNeighborLemmas.mem1 P hsumN
          squareCoordinates z
  have mem2 (z : GaussianInt) : z ∈ A 2 ↔
      (P.q₁ : Int)+1 ≤ z.re ∧ z.re ≤ (P.q : Int)-1 ∧
      1 ≤ z.im ∧ z.im ≤ (P.q₂ : Int)-1 := ParentalNeighborLemmas.mem2 P hsumN squareCoordinates z
  have mem3 (z : GaussianInt) : z ∈ A 3 ↔
      1 ≤ z.re ∧ z.re ≤ (P.q₂ : Int)-1 ∧
      (P.q₁ : Int)+1 ≤ z.im ∧ z.im ≤ (P.q : Int)-1 := ParentalNeighborLemmas.mem3 P hsumN
          squareCoordinates z
  have hmem (a b : Int) : (⟨a, b⟩ : GaussianInt) ∈ E ↔
      (1 ≤ a ∧ a < P.q₁ ∧ 1 ≤ b ∧ b < P.q₁) ∨
      (P.q₂ < a ∧ a < P.q ∧ P.q₂ < b ∧ b < P.q) ∨
      (P.q₁ < a ∧ a < P.q ∧ 1 ≤ b ∧ b < P.q₂) ∨
      (1 ≤ a ∧ a < P.q₂ ∧ P.q₁ < b ∧ b < P.q) := ParentalNeighborLemmas.hmem P hP q1pos q2posI
          hsumN mem0 mem1 mem2 mem3 a b
  let candidate (z : GaussianInt) : Finset GaussianInt :=
    {z + 1, z - 1, z + ⟨0, 1⟩, z - ⟨0, 1⟩}
  let transpose (z : GaussianInt) : GaussianInt := ⟨z.im, z.re⟩
  have transpose_involutive (z : GaussianInt) : transpose (transpose z) = z :=
      ParentalNeighborLemmas.transpose_involutive z
  have transpose_mem (z : GaussianInt) : z ∈ E ↔ transpose z ∈ E :=
      ParentalNeighborLemmas.transpose_mem P hP q1pos q2posI hsumN hmem z
  have transpose_candidate (x z : GaussianInt) :
      z ∈ candidate x ↔ transpose z ∈ candidate (transpose x) :=
          ParentalNeighborLemmas.transpose_candidate x z
  have transpose_filter_card (x : GaussianInt) :
      (Finset.filter (fun z => z ∈ E) (candidate x)).card =
        (Finset.filter (fun z => z ∈ E) (candidate (transpose x))).card :=
            ParentalNeighborLemmas.transpose_filter_card P transpose_involutive transpose_mem
            transpose_candidate x
  have rowR (u v : Int) (hb : 1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧
      1 ≤ v ∧ v ≤ (P.q : Int)-1)
      (hl : (u = P.q₁ ∧ v ≤ P.q₂) ∨ (v = P.q₂ ∧ P.q₁ ≤ u))
      (ho : P.q₂ < P.q₁) :
      (({(⟨u, v⟩ : GaussianInt) + 1, ⟨u, v⟩ - 1,
        ⟨u, v⟩ + ⟨0, 1⟩, ⟨u, v⟩ - ⟨0, 1⟩} : Finset GaussianInt).filter
          (fun y => y ∈ E)).card = 2 := ParentalNeighborLemmas.rowR P hP q1pos q2posI hsumN hmem
              u v hb hl ho
  have rowSmallRoot (ho : P.q₁ < P.q₂) :
      (Finset.filter (fun z => z ∈ E) (candidate ⟨(P.q₁ : Int), (P.q₁ : Int)⟩)).card = 2 :=
          ParentalNeighborLemmas.rowSmallRoot P hP q1pos q2posI hsumN hmem ho
  have rowSmall (u v : Int) (hb : 1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧
      1 ≤ v ∧ v ≤ (P.q : Int)-1)
      (hl : (u = P.q₁ ∧ v ≤ P.q₁) ∨ (v = P.q₁ ∧ u ≤ P.q₁))
      (ho : P.q₁ < P.q₂) :
      (Finset.filter (fun z => z ∈ E) (candidate ⟨u, v⟩)).card = 2 :=
          ParentalNeighborLemmas.rowSmall P hP q1pos q2posI hsumN hmem rowSmallRoot u v hb hl ho
  let reflect (z : GaussianInt) : GaussianInt :=
    ⟨(P.q : Int) - z.re, (P.q : Int) - z.im⟩
  have reflect_involutive (z : GaussianInt) : reflect (reflect z) = z :=
      ParentalNeighborLemmas.reflect_involutive P hsum z
  have reflect_mem (z : GaussianInt) : z ∈ E ↔ reflect z ∈ E :=
      ParentalNeighborLemmas.reflect_mem P q1pos q2posI hsumN hmem z
  have reflect_candidate (x z : GaussianInt) :
      z ∈ candidate x ↔ reflect z ∈ candidate (reflect x) :=
          ParentalNeighborLemmas.reflect_candidate P x z
  have reflect_filter_card (x : GaussianInt) :
      (Finset.filter (fun z => z ∈ E) (candidate x)).card =
        (Finset.filter (fun z => z ∈ E) (candidate (reflect x))).card :=
            ParentalNeighborLemmas.reflect_filter_card P reflect_involutive reflect_mem
            reflect_candidate x
  dsimp [B] at hx
  fin_cases j
  · rcases x with ⟨u, v⟩
    by_cases h : P.q₂ < P.q₁
    · simp only [P4062T1RemainderPaths, h, ↓reduceIte, Int.reduceNeg, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, Finset.mem_filter] at hx
      rcases hx with ⟨hxbox, hxline⟩
      have hb := (squareCoordinates P.q ⟨u, v⟩).mp hxbox
      exact rowR u v hb hxline h
    · simp only [P4062T1RemainderPaths, h, ↓reduceIte, Int.reduceNeg, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, Finset.mem_filter] at hx
      rcases hx with ⟨hxbox, hxline⟩
      have hb := (squareCoordinates P.q ⟨u, v⟩).mp hxbox
      have ho : P.q₁ < P.q₂ := by omega
      exact rowSmall u v hb hxline ho
  · rcases x with ⟨u, v⟩
    by_cases h : P.q₂ < P.q₁
    · simp only [P4062T1RemainderPaths, h, ↓reduceIte, Int.reduceNeg, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.mem_filter] at hx
      rcases hx with ⟨hxbox, hxline⟩
      have hb := (squareCoordinates P.q ⟨u, v⟩).mp hxbox
      have hb' : 1 ≤ v ∧ v ≤ (P.q : Int)-1 ∧ 1 ≤ u ∧ u ≤ (P.q : Int)-1 :=
        ⟨hb.2.2.1, hb.2.2.2, hb.1, hb.2.1⟩
      rw [transpose_filter_card]
      exact rowR v u hb' hxline h
    · simp only [P4062T1RemainderPaths, h, ↓reduceIte, Int.reduceNeg, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.mem_filter] at hx
      rcases hx with ⟨hxbox, hxline⟩
      have hb := (squareCoordinates P.q ⟨u, v⟩).mp hxbox
      have ho : P.q₁ < P.q₂ := by omega
      have hb' : 1 ≤ (P.q : Int)-u ∧ (P.q : Int)-u ≤ (P.q : Int)-1 ∧
          1 ≤ (P.q : Int)-v ∧ (P.q : Int)-v ≤ (P.q : Int)-1 := by
        change 1 ≤ u ∧ u ≤ (P.q : Int)-1 ∧ 1 ≤ v ∧ v ≤ (P.q : Int)-1 at hb
        rcases hb with ⟨hu1, hu2, hv1, hv2⟩
        constructor <;> omega
      have hl : ((P.q : Int)-u = P.q₁ ∧ (P.q : Int)-v ≤ P.q₁) ∨
          ((P.q : Int)-v = P.q₁ ∧ (P.q : Int)-u ≤ P.q₁) := by
        rcases hxline with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · left
          constructor <;> omega
        · right
          constructor <;> omega
      rw [reflect_filter_card]
      exact rowSmall ((P.q : Int)-u) ((P.q : Int)-v) hb' hl ho

end ApollonianSuperharmonic

end
