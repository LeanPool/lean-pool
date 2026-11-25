/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.CubeAndTetrahedron
public import LeanPool.DehnInvariant.RationalAngles
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The cube intersected with a rhombic dodecahedron
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

private def coordinateIndex (i : Fin 3) (negative : Bool) : Fin 18 :=
  ⟨2 * i.val + negative.toNat, by cases negative <;> simp <;> omega⟩

private def pairIndex (pair : Fin 3) (negativeFirst negativeSecond : Bool) : Fin 18 :=
  ⟨6 + 4 * pair.val + 2 * negativeFirst.toNat + negativeSecond.toNat,
    by cases negativeFirst <;> cases negativeSecond <;> simp <;> omega⟩

/-- The smaller coordinate in each of the three unordered pairs. -/
def firstCoordinate : Fin 3 → Fin 3 := ![0, 0, 1]
/-- The larger coordinate in each of the three unordered pairs. -/
def secondCoordinate : Fin 3 → Fin 3 := ![1, 2, 2]
/-- The coefficient selected by the negative-sign flag. -/
def normalSign (negative : Bool) : ℤ := if negative then -1 else 1

/-- The signed coordinate and signed pair families of normals. -/
inductive NormalIndex
  | coordinate (index : Fin 3) (negative : Bool)
  | pair (index : Fin 3) (negativeFirst negativeSecond : Bool)
  deriving DecidableEq

/-- Decode a face number into its coordinate or coordinate-pair normal. -/
def normalIndex (i : Fin 18) : NormalIndex :=
  if firstSix : i.val < 6 then
    .coordinate ⟨i.val / 2, by omega⟩ (i.val % 2 == 1)
  else
    .pair ⟨(i.val - 6) / 4, by have := i.isLt; omega⟩
      ((i.val - 6) % 4 / 2 == 1) ((i.val - 6) % 2 == 1)

private lemma normalIndex_coordinate : ∀ (i : Fin 3) (negative : Bool),
    normalIndex (coordinateIndex i negative) = .coordinate i negative := by decide +kernel

private lemma normalIndex_pair : ∀ (p : Fin 3) (n₁ n₂ : Bool),
    normalIndex (pairIndex p n₁ n₂) = .pair p n₁ n₂ := by decide +kernel

/-- The signed coordinate and pair normals of the cube–rhombic-dodecahedron intersection. -/
def crZ (i : Fin 18) (j : Fin 3) : ℤ :=
  match normalIndex i with
  | .coordinate index negative => if j = index then normalSign negative else 0
  | .pair index negativeFirst negativeSecond =>
    (if j = firstCoordinate index then normalSign negativeFirst else 0) +
      (if j = secondCoordinate index then normalSign negativeSecond else 0)

/-- Dot products of the normals. -/
def crDot (i j : Fin 18) : ℤ := crZ i 0 * crZ j 0 + crZ i 1 * crZ j 1 + crZ i 2 * crZ j 2

/-- The normals as vectors of ℝ³. -/
noncomputable def crN (i : Fin 18) : R3 := !₂[(crZ i 0 : ℝ), (crZ i 1 : ℝ), (crZ i 2 : ℝ)]

/-- Offsets: `s` for the six cube faces, `c` for the twelve rhombic dodecahedron faces. -/
def crB (s c : ℝ) (i : Fin 18) : ℝ :=
  match normalIndex i with
  | .coordinate .. => s
  | .pair .. => c

/-- **The cube ∩ rhombic dodecahedron solids**: the points with `|x i| ≤ s` (cube) and `|x i ± x
j| ≤ c`
(rhombic dodecahedron). For `s < c < 2 s` the solid has 18 faces; `s = 1`, `c = μ√2` with μ =
1.03125… is
the fair 18-face die. -/
noncomputable def cubeRDSet (s c : ℝ) : Set R3 := sol crN (crB s c)

lemma crN_inner (i j : Fin 18) : ⟪crN i, crN j⟫ = (crDot i j : ℝ) := by
  unfold crN crDot
  rw [inner3]
  push_cast
  rfl

private def angleIndex (i j : Fin 18) : Fin 5 :=
  Fin.ofNat 5 ((4 * crDot i j ^ 2 / (crDot i i * crDot j j)).toNat)

private lemma angleIndex_spec : ∀ i j : Fin 18,
    4 * crDot i j ^ 2 = (angleIndex i j : ℤ) * (crDot i i * crDot j j) := by
  -- The kernel checks the computed index for each pair of normals.
  decide +kernel

/-- The squared cosine of each of the 18 normals with each other is a multiple of one fourth. -/
lemma crDot_table (i j : Fin 18) :
    ∃ k : Fin 5, 4 * crDot i j ^ 2 = (k : ℤ) * (crDot i i * crDot j j) :=
  ⟨angleIndex i j, angleIndex_spec i j⟩

lemma crDot_self_ne : ∀ i : Fin 18, crDot i i ≠ 0 := by decide +kernel

lemma crN_ne_zero (i : Fin 18) : crN i ≠ 0 := by
  intro h
  have h1 := crN_inner i i
  rw [h, inner_zero_left] at h1
  exact crDot_self_ne i (by exact_mod_cast h1.symm)

/-- Any two of the 18 normals make an angle that is a rational multiple of π. -/
lemma crN_angle (i j : Fin 18) : InnerProductGeometry.angle (crN i) (crN j) ∈ ratPi := by
  obtain ⟨k, hk⟩ := crDot_table i j
  apply angle_mem_ratPi_of_gram (crN_ne_zero i) (crN_ne_zero j) (k := (k : ℕ)) (by omega)
  rw [crN_inner, crN_inner, crN_inner]
  exact_mod_cast hk

private lemma crZ_coordinate : ∀ (i : Fin 3) (negative : Bool) (j : Fin 3),
    crZ (coordinateIndex i negative) j = if j = i then normalSign negative else 0 := by
  decide +kernel

private lemma crZ_pair : ∀ (p : Fin 3) (n₁ n₂ : Bool) (j : Fin 3),
    crZ (pairIndex p n₁ n₂) j =
      (if j = firstCoordinate p then normalSign n₁ else 0) +
      (if j = secondCoordinate p then normalSign n₂ else 0) := by
  decide +kernel

private lemma normal_cases : ∀ i : Fin 18,
    (∃ j negative, i = coordinateIndex j negative) ∨
      (∃ p n₁ n₂, i = pairIndex p n₁ n₂) := by decide +kernel

private lemma ordered_pair : ∀ i j : Fin 3, i < j →
    ∃ p, firstCoordinate p = i ∧ secondCoordinate p = j := by decide +kernel

private lemma coordinate_ne : ∀ p, firstCoordinate p ≠ secondCoordinate p := by decide +kernel

private lemma crB_coordinate (s c : ℝ) (i : Fin 3) (negative : Bool) :
    crB s c (coordinateIndex i negative) = s := by
  simp [crB, normalIndex_coordinate]

private lemma crB_pair (s c : ℝ) (p : Fin 3) (n₁ n₂ : Bool) :
    crB s c (pairIndex p n₁ n₂) = c := by
  simp [crB, normalIndex_pair]

private lemma inner_crN (i : Fin 18) (x : R3) :
    ⟪crN i, x⟫ = ∑ j : Fin 3, (crZ i j : ℝ) * x j := by
  rw [crN, inner3, Fin.sum_univ_three]

private lemma inner_crN_coordinate (i : Fin 3) (negative : Bool) (x : R3) :
    ⟪crN (coordinateIndex i negative), x⟫ = (normalSign negative : ℝ) * x i := by
  rw [inner_crN]
  simp [crZ_coordinate, ite_mul]

private lemma inner_crN_pair (p : Fin 3) (n₁ n₂ : Bool) (x : R3) :
    ⟪crN (pairIndex p n₁ n₂), x⟫ =
      (normalSign n₁ : ℝ) * x (firstCoordinate p) +
        (normalSign n₂ : ℝ) * x (secondCoordinate p) := by
  rw [inner_crN]
  simp [crZ_pair, add_mul, ite_mul, Finset.sum_add_distrib]

/-- Membership amounts to the coordinate and pairwise absolute-value bounds. -/
lemma mem_cubeRDSet {s c : ℝ} {x : R3} :
    x ∈ cubeRDSet s c ↔ (∀ i, |x i| ≤ s) ∧ ∀ i j, i ≠ j → |x i + x j| ≤ c ∧ |x i - x j| ≤ c := by
  constructor
  · intro hx
    have axis (i : Fin 3) (negative : Bool) : (normalSign negative : ℝ) * x i ≤ s := by
      simpa only [inner_crN_coordinate, crB_coordinate] using hx (coordinateIndex i negative)
    have pair (p : Fin 3) : |x (firstCoordinate p) + x (secondCoordinate p)| ≤ c ∧
        |x (firstCoordinate p) - x (secondCoordinate p)| ≤ c := by
      have signed (n₁ n₂ : Bool) := hx (pairIndex p n₁ n₂)
      have pp := signed false false
      have pm := signed false true
      have mp := signed true false
      have mm := signed true true
      simp only [inner_crN_pair, crB_pair, normalSign, Bool.false_eq_true, ite_false,
        ite_true, Int.cast_neg, Int.cast_one, one_mul, neg_mul] at pp pm mp mm
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
    have ascending (i j : Fin 3) (hij : i < j) : |x i + x j| ≤ c ∧ |x i - x j| ≤ c := by
      obtain ⟨p, hp, hq⟩ := ordered_pair i j hij
      simpa only [hp, hq] using pair p
    refine ⟨fun i => abs_le.2 ⟨?_, ?_⟩, fun i j different => ?_⟩
    · have bound := axis i true
      simp [normalSign] at bound
      linarith
    · simpa [normalSign] using axis i false
    · rcases lt_or_gt_of_ne different with ordered | ordered
      · exact ascending i j ordered
      · simpa only [add_comm (x j) (x i), abs_sub_comm (x j) (x i)] using ascending j i ordered
  · rintro ⟨axis, pairs⟩ i
    change ⟪crN i, x⟫ ≤ crB s c i
    rcases normal_cases i with ⟨j, negative, rfl⟩ | ⟨p, n₁, n₂, rfl⟩
    · rw [inner_crN_coordinate, crB_coordinate]
      obtain ⟨lower, upper⟩ := abs_le.1 (axis j)
      cases negative <;> simp [normalSign] <;> linarith
    · rw [inner_crN_pair, crB_pair]
      obtain ⟨plus, minus⟩ := pairs _ _ (coordinate_ne p)
      have plus := abs_le.1 plus
      have minus := abs_le.1 minus
      cases n₁ <;> cases n₂ <;> simp [normalSign] <;> linarith

/-- The cube ∩ rhombic dodecahedron solids are convex polytopes. -/
theorem isPoly_cubeRD (s c : ℝ) : IsPoly (cubeRDSet s c) :=
  ⟨bounded_of_coords s (fun _ hx i => (mem_cubeRDSet.1 hx).1 i), Fin 18, inferInstance, crN, _, rfl⟩

/-- **The zero word.** Every cube ∩ rhombic dodecahedron solid has Dehn invariant zero: all
offsets `s`, `c`,
so the whole line of cuts, the fair 18-face die among them. -/
theorem dehnSet_cubeRD (s c : ℝ) : dehnSet (cubeRDSet s c) = 0 :=
  dehnSet_sol_eq_zero_of_rational crN (crB s c) crN_ne_zero crN_angle

/-- The fair 18-face die is the member `s = 1`, `c = μ√2` with μ = 1.03125… (the fair cut, known
numerically
and as a root of a polynomial of degree 6; study of 18 November 2026). The statement holds for
every μ. -/
theorem dehnSet_fairDie18 (μ : ℝ) : dehnSet (cubeRDSet 1 (μ * √2)) = 0 := dehnSet_cubeRD 1 _

/-- The same invariant as every cube. -/
theorem dehnSet_cubeRD_eq_cube (s c t : ℝ) :
    dehnSet (cubeRDSet s c) = dehnSet (cubeSet t) := by
  rw [dehnSet_cubeRD, dehnSet_cube t]

end DehnCanon.Library
