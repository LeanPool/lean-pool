/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3597T1DirectionParity
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import LeanPool.ApollonianSuperharmonic.P3544T1RayParity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Uniform

-- [TABLET NODE: P3597T1SideCrossing]

/-!
# P3597T1SideCrossing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SideCrossingProof

private theorem hidx :
    ∀ (n : Nat), ∀ (i : Fin (n + 3)), i ≠ i + 1 := by
  classical
  intro n i h
  have hv := congrArg Fin.val h
  have hval : (i + 1).val = if i.val = n + 2 then 0 else i.val + 1 := by
    simp [Fin.val_add_eq_ite]
    split_ifs <;> omega
  rw [hval] at hv
  split_ifs at hv <;> omega

private theorem hab :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (i ≠ i + 1) → (a ≠ b) := by
  classical
  intro n p i a b hidx h
  exact hidx (p.injective h)

private theorem hxleft :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), (x
        ∈ openSegment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))) → (
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (a ≠ b) → (x ≠ a)) := by
  classical
  intro n p i x hx a b hab h
  subst x
  have hab' : a = b := left_mem_openSegment_iff.mp hx
  exact hab hab'

private theorem hxright :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), (x
        ∈ openSegment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))) → (
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (a ≠ b) → ((x ≠ a) → (x ≠ b))) := by
  classical
  intro n p i x hx a b hab hxleft h
  subst x
  have hab' : a = b := right_mem_openSegment_iff.mp hx
  exact hab hab'

private theorem hxseg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), (x
        ∈ openSegment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))) → (
    let a := p.vertex i
    let b := p.vertex (i + 1)
    x ∈ segment Real a b) := by
  classical
  intro n p i x hx a b
  exact openSegment_subset_segment Real a b hx

private theorem hxline :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), ((fun (θ : ℝ) => ((1 : ℝ) - θ) • p.vertex i + θ • p.vertex (i + (1 : Fin (n + (3 :
        ℕ))))) q = x) → (x = a + q • (b - a)) := by
  classical
  intro n p i x a b q hxq
  rw [← hxq]
  apply Prod.ext <;> simp [sub_smul] <;> ring

private theorem hx1 :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (x = a + q • (b - a)) → (x.1 = a.1 + q * (b.1 - a.1)) := by
  classical
  intro n p i x a b q hxline
  have h := congrArg Prod.fst hxline
  simpa using h

private theorem hx2 :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (x = a + q • (b - a)) → (x.2 = a.2 + q * (b.2 - a.2)) := by
  classical
  intro n p i x a b q hxline
  have h := congrArg Prod.snd hxline
  simpa using h

private theorem hxnotseg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (x ≠ a) → ((x ≠ b) → ((x ∈ segment ℝ a b) → (∀ j : Fin (n + 3), j ≠ i →
      x ∉ segment Real (p.vertex j) (p.vertex (j + 1))))) := by
  classical
  intro n p i x a b hxleft hxright hxseg j hji hxj
  have hint : x ∈ segment Real a b ∩
      segment Real (p.vertex j) (p.vertex (j + 1)) := ⟨hxseg, hxj⟩
  rw [p.edge_intersection i j (Ne.symm hji)] at hint
  rcases hint with ⟨(h | h), _⟩
  · exact hxleft h
  · exact hxright h

private theorem hnonvertex :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    (x ≠ a) → ((∀ j : Fin (n + 3), j ≠ i → x ∉ segment Real (p.vertex j) (p.vertex (j + 1))) → (∀
        k : Fin (n + 3), p.vertex k ≠ x)) := by
  classical
  intro n p i x a hxleft hxnotseg k hk
  by_cases hki : k = i
  · subst k
    exact hxleft hk.symm
  · apply hxnotseg k hki
    rw [← hk]
    exact left_mem_segment Real _ _

private theorem hparam :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    (∀ j, D j ≠ 0) → (∀ (j : Fin (n + (3 : ℕ))), have t :=
    ((p.vertex j - x).1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        (p.vertex j - x).2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1) /
      (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1);
  have u :=
    ((p.vertex j - x).1 * d.2 - (p.vertex j - x).2 * d.1) /
      (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1);
  x + t • d = p.vertex j + u • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j) ∧
    (∀ (t' : ℝ), ∀ (u' : ℝ), x + t' • d = p.vertex j + u' • (p.vertex (j + (1 : Fin (n + (3 :
        ℕ)))) - p.vertex j) → t' = t ∧ u' = u) ∧
      ((∃ (t' : ℝ), (0 : ℝ) < t' ∧ x + t' • d ∈ segment ℝ (p.vertex j) (p.vertex (j + (1 : Fin (n
          + (3 : ℕ)))))) ↔
        (0 : ℝ) < t ∧ (0 : ℝ) ≤ u ∧ u ≤ (1 : ℝ))) := by
  classical
  intro n p x d D hD j
  exact (P3597T1GenericRayStability p).2.2 x d j (hD j)

private theorem hcontT :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    (∀ j, D j ≠ 0) → (∀ (j : Fin (n + 3)), Continuous (T j)) := by
  classical
  intro n p d D T hD j
  dsimp [T, D]
  apply Continuous.div
  · fun_prop
  · exact continuous_const
  · intro y
    exact hD j

private theorem hcontU :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ j, D j ≠ 0) → (∀ (j : Fin (n + 3)), Continuous (U j)) := by
  classical
  intro n p d D U hD j
  dsimp [U, D]
  apply Continuous.div
  · fun_prop
  · exact continuous_const
  · intro y
    exact hD j

private theorem hTi :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (x.1 = a.1 + q * (b.1 - a.1)) → ((x.2 = a.2 + q * (b.2 - a.2)) → (∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    (∀ j, D j ≠ 0) → (T i x = 0))) := by
  classical
  intro n p i x a b q hx1 hx2 d D T hD
  change ((a.1 - x.1) * (b.2 - a.2) - (a.2 - x.2) * (b.1 - a.1)) /
    (d.1 * (b.2 - a.2) - d.2 * (b.1 - a.1)) = 0
  have hden : d.1 * (p.vertex (i + 1) - p.vertex i).2 -
      d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0 := by
    simpa [D] using hD i
  change d.1 * (b.2 - a.2) - d.2 * (b.1 - a.1) ≠ 0 at hden
  apply (div_eq_zero_iff).2
  left
  rw [hx1, hx2]
  dsimp [a, b]
  ring

private theorem hUi :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (x.1 = a.1 + q * (b.1 - a.1)) → ((x.2 = a.2 + q * (b.2 - a.2)) → (∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ j, D j ≠ 0) → (U i x = q))) := by
  classical
  intro n p i x a b q hx1 hx2 d D U hD
  change ((a.1 - x.1) * d.2 - (a.2 - x.2) * d.1) /
    (d.1 * (b.2 - a.2) - d.2 * (b.1 - a.1)) = q
  have hden : d.1 * (p.vertex (i + 1) - p.vertex i).2 -
      d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0 := by
    simpa [D] using hD i
  apply (div_eq_iff hden).2
  change d.1 * (b.2 - a.2) - d.2 * (b.1 - a.1) ≠ 0 at hden
  rw [hx1, hx2]
  dsimp [a, b]
  ring

private theorem hUzero :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ), (∀ (i :
        Fin (n + (3 : ℕ))), d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ j, D j ≠ 0) → (∀ (j : Fin (n + 3)), U j x ≠ 0)) := by
  classical
  intro n p x d hdv D U hD j h
  change (((p.vertex j).1 - x.1) * d.2 - ((p.vertex j).2 - x.2) * d.1) /
    (d.1 * ((p.vertex (j + 1)).2 - (p.vertex j).2) -
      d.2 * ((p.vertex (j + 1)).1 - (p.vertex j).1)) = 0 at h
  have hden : d.1 * (p.vertex (j + 1) - p.vertex j).2 -
      d.2 * (p.vertex (j + 1) - p.vertex j).1 ≠ 0 := by
    simpa [D] using hD j
  have hn := (div_eq_zero_iff).mp h
  rcases hn with hn | hn
  · have hv0 : d.1 * ((p.vertex j).2 - x.2) -
        d.2 * ((p.vertex j).1 - x.1) = 0 := by nlinarith [hn]
    exact (hdv j) hv0
  · exact hden hn

private theorem hUone :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ), (∀ (i :
        Fin (n + (3 : ℕ))), d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ j, D j ≠ 0) → (∀ (j : Fin (n + 3)), U j x ≠ 1)) := by
  classical
  intro n p x d hdv D U hD j h
  change (((p.vertex j).1 - x.1) * d.2 - ((p.vertex j).2 - x.2) * d.1) /
    (d.1 * ((p.vertex (j + 1)).2 - (p.vertex j).2) -
      d.2 * ((p.vertex (j + 1)).1 - (p.vertex j).1)) = 1 at h
  have hden : d.1 * (p.vertex (j + 1) - p.vertex j).2 -
      d.2 * (p.vertex (j + 1) - p.vertex j).1 ≠ 0 := by
    simpa [D] using hD j
  have hn := (div_eq_iff hden).mp h
  simp only [one_mul, Prod.fst_sub, Prod.snd_sub] at hn
  have hv0 : d.1 * ((p.vertex (j + 1)).2 - x.2) -
      d.2 * ((p.vertex (j + 1)).1 - x.1) = 0 := by
    nlinarith [hn]
  exact (hdv (j + 1)) hv0

private theorem hTne :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), (∀
        j : Fin (n + 3), j ≠ i → x ∉ segment Real (p.vertex j) (p.vertex (j + 1))) → (∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ (j : Fin (n + (3 : ℕ))), have t := ((p.vertex j - x).1 * (p.vertex (j + (1 : Fin (n + (3 :
        ℕ)))) - p.vertex j).2 - (p.vertex j - x).2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j).1) / (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 - d.2 *
        (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1); have u := ((p.vertex j - x).1 *
        d.2 - (p.vertex j - x).2 * d.1) / (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j).2 - d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1); x + t • d
        = p.vertex j + u • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j) ∧ (∀ (t' : ℝ), ∀
        (u' : ℝ), x + t' • d = p.vertex j + u' • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j) → t' = t ∧ u' = u) ∧ ((∃ (t' : ℝ), (0 : ℝ) < t' ∧ x + t' • d ∈ segment ℝ
        (p.vertex j) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) ↔ (0 : ℝ) < t ∧ (0 : ℝ) ≤ u ∧ u ≤
        (1 : ℝ))) → (∀ (j : Fin (n + 3)), (j ≠ i) → ((0 < U j x ∧ U j x < 1) → (T j x ≠ 0)))) := by
  classical
  intro n p i x hxnotseg d D T U hparam j hji hinside ht
  have heq := (hparam j).1
  change x + T j x • d = p.vertex j + U j x •
    (p.vertex (j + 1) - p.vertex j) at heq
  rw [ht, zero_smul, add_zero] at heq
  have hxj : x ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := by
    rw [segment_eq_image]
    let u := U j x
    refine ⟨u, ⟨le_of_lt hinside.1, hinside.2.le⟩, ?_⟩
    change (1 - u) • p.vertex j + u • p.vertex (j + 1) = x
    calc
      (1 - u) • p.vertex j + u • p.vertex (j + 1) =
          p.vertex j + u • (p.vertex (j + 1) - p.vertex j) := by
            apply Prod.ext <;> simp [smul_sub, sub_smul] <;> ring
      _ = x := heq.symm
  exact (hxnotseg j hji) hxj

private theorem hVopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ (j : Fin (n + 3)), Continuous (T j)) → ((∀ (j : Fin (n + 3)), Continuous (U j)) → (
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    ∀ (j : Fin (n + 3)), IsOpen (V j))) := by
  classical
  intro n p i x d D T U hcontT hcontU V j
  dsimp [V]
  split_ifs with hji hu0 hu1 ht
  · simpa only [Set.ofPred_and] using (isOpen_lt
      (continuous_const : Continuous fun _ : Real × Real => (0 : Real)) (hcontU j)).inter
      (isOpen_lt (hcontU j)
        (continuous_const : Continuous fun _ : Real × Real => (1 : Real)))
  · exact isOpen_lt (hcontU j) continuous_const
  · exact isOpen_lt (continuous_const : Continuous fun _ : Real × Real => (1 : Real)) (hcontU j)
  · simpa only [Set.ofPred_and] using (isOpen_lt
      (continuous_const : Continuous fun _ : Real × Real => (0 : Real)) (hcontT j)).inter
      ((isOpen_lt (continuous_const : Continuous fun _ : Real × Real => (0 : Real))
        (hcontU j)).inter (isOpen_lt (hcontU j)
        (continuous_const : Continuous fun _ : Real × Real => (1 : Real))))
  · simpa only [Set.ofPred_and] using (isOpen_lt (hcontT j)
      (continuous_const : Continuous fun _ : Real × Real => (0 : Real))).inter
      ((isOpen_lt (continuous_const : Continuous fun _ : Real × Real => (0 : Real))
        (hcontU j)).inter (isOpen_lt (hcontU j)
        (continuous_const : Continuous fun _ : Real × Real => (1 : Real))))

private theorem hVmem :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (q : ℝ), (q ∈ Set.Ioo (0 : ℝ) (1 : ℝ)) → (∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (U i x = q) → ((∀ (j : Fin (n + 3)), U j x ≠ 0) → ((∀ (j : Fin (n + 3)), U j x ≠ 1) → ((∀ (j
        : Fin (n + 3)), (j ≠ i) → ((0 < U j x ∧ U j x < 1) → (T j x ≠ 0))) → (
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    ∀ j, x ∈ V j))))) := by
  classical
  intro n p i x q hq d D T U hUi hUzero hUone hTne V j
  by_cases hji : j = i
  · subst j
    simp [V, hUi, hq.1, hq.2]
  · have hz := hUzero j
    have ho := hUone j
    by_cases hu0 : U j x < 0
    · simp [V, hji, hu0]
    · by_cases hu1 : 1 < U j x
      · simp [V, hji, hu0, hu1]
      · have hinside : 0 < U j x ∧ U j x < 1 := by
          constructor
          · exact lt_of_le_of_ne (le_of_not_gt hu0) (Ne.symm hz)
          · exact lt_of_le_of_ne (le_of_not_gt hu1) ho
        have htne := hTne j hji hinside
        by_cases ht : 0 < T j x
        · simp [V, hji, hu0, hu1, ht, hinside]
        · have ht' : T j x < 0 := lt_of_le_of_ne (le_of_not_gt ht) htne
          simp [V, hji, hu0, hu1, ht, ht', hinside]

private theorem hVallopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    (∀ (j : Fin (n + 3)), IsOpen (V j)) → (
    let Vall : Set (Real × Real) := ⋂ j, V j
    IsOpen Vall) := by
  classical
  intro n p i x d D T U V hVopen Vall
  dsimp [Vall]
  exact isOpen_iInter_of_finite hVopen

private theorem hxVall :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    (∀ j, x ∈ V j) → (
    let Vall : Set (Real × Real) := ⋂ j, V j
    x ∈ Vall) := by
  classical
  intro n p i x d D T U V hVmem Vall
  exact Set.mem_iInter.mpr hVmem

private theorem hcompactseg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (j : Fin (n + 3)), IsCompact (segment Real
        (p.vertex j) (p.vertex (j + 1))) := by
  classical
  intro n p j
  rw [segment_eq_image]
  apply isCompact_Icc.image
  fun_prop

private theorem hWopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), (∀ (j : Fin (n + 3)),
        IsCompact (segment Real (p.vertex j) (p.vertex (j + 1)))) → (
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    ∀ (j : Fin (n + 3)), IsOpen (W j)) := by
  classical
  intro n p i hcompactseg W j
  dsimp [W]
  split_ifs
  · exact isOpen_univ
  · exact (hcompactseg j).isClosed.isOpen_compl

private theorem hWmem :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), (∀
        j : Fin (n + 3), j ≠ i → x ∉ segment Real (p.vertex j) (p.vertex (j + 1))) → (
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    ∀ j, x ∈ W j) := by
  classical
  intro n p i x hxnotseg W j
  by_cases hji : j = i
  · simp [W, hji]
  · simp [W, hji, hxnotseg j hji]

private theorem hWallopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    (∀ (j : Fin (n + 3)), IsOpen (W j)) → (
    let Wall : Set (Real × Real) := ⋂ j, W j
    IsOpen Wall) := by
  classical
  intro n p i W hWopen Wall
  dsimp [Wall]
  exact isOpen_iInter_of_finite hWopen

private theorem hxWall :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    (∀ j, x ∈ W j) → (
    let Wall : Set (Real × Real) := ⋂ j, W j
    x ∈ Wall) := by
  classical
  intro n p i x W hWmem Wall
  exact Set.mem_iInter.mpr hWmem

private theorem hFexplicit :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    ∀ (y : Real × Real), F y =
      (b.1 - a.1) * (y.2 - a.2) - (y.1 - a.1) * (b.2 - a.2) := by
  classical
  intro n p i a b F y
  simp [F, P3381T1TriangleDeterminant]

private theorem hsegF :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = (b.1 - a.1) * (y.2 - a.2) - (y.1 - a.1) * (b.2 - a.2)) → (∀ (y :
        Real × Real), (y ∈ segment Real a b) → (F y = 0)) := by
  classical
  intro n p i a b F hFexplicit y hy
  rw [segment_eq_image] at hy
  rcases hy with ⟨u, hu, rfl⟩
  rw [hFexplicit]
  simp [sub_smul]
  ring

private theorem hecoord :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (a ≠ b) → ((b.1 - a.1 ≠ 0) ∨ (b.2 - a.2 ≠ 0)) := by
  classical
  intro n p i a b hab
  by_contra h
  push Not at h
  rcases h with ⟨h1, h2⟩
  apply hab
  apply Prod.ext <;> linarith

private theorem hQcont :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    ((b.1 - a.1 ≠ 0) ∨ (b.2 - a.2 ≠ 0)) → (Continuous Q) := by
  classical
  intro n p i a b Q hecoord
  dsimp [Q]
  split_ifs with hfirst
  · have hsecond : b.2 - a.2 ≠ 0 := by
      rcases hecoord with h | h
      · exact False.elim (h hfirst)
      · exact h
    apply Continuous.div
    · fun_prop
    · exact continuous_const
    · intro y
      exact hsecond
  · have hfirst' : b.1 - a.1 ≠ 0 := by
      exact hfirst
    apply Continuous.div
    · fun_prop
    · exact continuous_const
    · intro y
      exact hfirst'

private theorem hQx :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (x.1 = a.1 + q * (b.1 - a.1)) → ((x.2 = a.2 + q * (b.2 - a.2)) → (
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    ((b.1 - a.1 ≠ 0) ∨ (b.2 - a.2 ≠ 0)) → (Q x = q))) := by
  classical
  intro n p i x a b q hx1 hx2 Q hecoord
  dsimp [Q]
  split_ifs with hfirst
  · have hsecond : b.2 - a.2 ≠ 0 := by
      rcases hecoord with h | h
      · exact False.elim (h hfirst)
      · exact h
    apply (div_eq_iff hsecond).2
    rw [hx2]
    ring
  · have hfirst' : b.1 - a.1 ≠ 0 := by
      exact hfirst
    apply (div_eq_iff hfirst').2
    rw [hx1]
    ring

private theorem hQline :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = (b.1 - a.1) * (y.2 - a.2) - (y.1 - a.1) * (b.2 - a.2)) → (
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    ((b.1 - a.1 ≠ 0) ∨ (b.2 - a.2 ≠ 0)) → (∀ (y : Real × Real), (F y = 0) → (y = a + Q y • (b -
        a)))) := by
  classical
  intro n p i a b F hFexplicit Q hecoord y hFy
  have hF' := hFexplicit y
  rw [hFy] at hF'
  by_cases hfirst : b.1 - a.1 = 0
  · have hsecond : b.2 - a.2 ≠ 0 := by
      rcases hecoord with h | h
      · exact False.elim (h hfirst)
      · exact h
    have hQmul : Q y * (b.2 - a.2) = y.2 - a.2 := by
      rw [show Q y = (y.2 - a.2) / (b.2 - a.2) by simp [Q, hfirst]]
      field_simp [hsecond]
    have hy1 : y.1 = a.1 := by
      have : (y.1 - a.1) * (b.2 - a.2) = 0 := by
        simp only [hfirst, zero_mul, zero_sub, zero_eq_neg, mul_eq_zero] at hF'
        rcases hF' with h | h
        · rw [h]
          ring
        · exact (hsecond h).elim
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact (hsecond h).elim
    apply Prod.ext
    · simp [Prod.fst_add, Prod.fst_sub, hfirst, hy1]
    · simp [Prod.snd_add, Prod.snd_sub]
      nlinarith [hQmul]
  · have hfirst' : b.1 - a.1 ≠ 0 := by
      intro h
      exact hfirst h
    have hQmul : Q y * (b.1 - a.1) = y.1 - a.1 := by
      rw [show Q y = (y.1 - a.1) / (b.1 - a.1) by simp [Q, hfirst]]
      field_simp [hfirst']
    have hy2 : y.2 - a.2 = Q y * (b.2 - a.2) := by
      have : (b.1 - a.1) * (y.2 - a.2) =
          (y.1 - a.1) * (b.2 - a.2) := by
        nlinarith [hF']
      rw [← hQmul] at this
      field_simp [hfirst'] at this
      exact this
    apply Prod.ext
    · simp [Prod.fst_add, Prod.fst_sub]
      nlinarith [hQmul]
    · simp [Prod.snd_add, Prod.snd_sub]
      nlinarith [hy2]

private theorem hQlineopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    (Continuous Q) → (
    let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
    IsOpen Qline) := by
  classical
  intro n p i a b Q hQcont Qline
  dsimp [Qline]
  simpa only [Set.ofPred_and] using (isOpen_lt
    (continuous_const : Continuous fun _ : Real × Real => (0 : Real)) hQcont).inter
    (isOpen_lt hQcont (continuous_const : Continuous fun _ : Real × Real => (1 : Real)))

private theorem hxQline :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (q : ℝ), (q ∈ Set.Ioo (0 : ℝ) (1 : ℝ)) → (
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    (Q x = q) → (
    let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
    x ∈ Qline)) := by
  classical
  intro n p i x a b q hq Q hQx Qline
  simp [Qline, hQx, hq.1, hq.2]

private theorem hcontg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    ∀ (j : Fin (n + 3)), Continuous (g j) := by
  classical
  intro n p d g j
  dsimp [g]
  fun_prop

private theorem hGopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    (∀ (j : Fin (n + 3)), Continuous (g j)) → (
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    ∀ (j : Fin (n + 3)), IsOpen (G j)) := by
  classical
  intro n p d g hcontg G j
  dsimp [G]
  exact (isOpen_lt (hcontg j) continuous_const).union
    (isOpen_lt (continuous_const : Continuous fun _ : Real × Real => (0 : Real)) (hcontg j))

private theorem hGmem :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ), (∀ (i :
        Fin (n + (3 : ℕ))), d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) → (
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    ∀ j, x ∈ G j) := by
  classical
  intro n p x d hdv g G j
  have hj := hdv j
  have hj' : g j x ≠ 0 := by simpa [g] using hj
  rcases lt_or_gt_of_ne (Ne.symm hj') with hpos | hneg
  · exact Or.inr hpos
  · exact Or.inl hneg

private theorem hGallopen :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    (∀ (j : Fin (n + 3)), IsOpen (G j)) → (
    let Gall : Set (Real × Real) := ⋂ j, G j
    IsOpen Gall) := by
  classical
  intro n p d g G hGopen Gall
  dsimp [Gall]
  exact isOpen_iInter_of_finite hGopen

private theorem hxGall :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ),
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    (∀ j, x ∈ G j) → (
    let Gall : Set (Real × Real) := ⋂ j, G j
    x ∈ Gall) := by
  classical
  intro n p x d g G hGmem Gall
  exact Set.mem_iInter.mpr hGmem

private theorem hcarrier :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    let Vall : Set (Real × Real) := ⋂ j, V j
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    let Wall : Set (Real × Real) := ⋂ j, W j
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), (y ∈ segment Real a b) → (F y = 0)) → (
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    (∀ (y : Real × Real), (F y = 0) → (y = a + Q y • (b - a))) → (
    let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    let Gall : Set (Real × Real) := ⋂ j, G j
    let N : Set (Real × Real) := Vall ∩ (Wall ∩ (Qline ∩ Gall))
    ∀ (rN : ℝ), (Metric.ball x rN ⊆ N) → (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (y ∈
        P3544T1BoundaryCarrier p ↔ F y = 0)))) := by
  classical
  intro n p i x a b d D T U V Vall W Wall F hsegF Q hQline Qline g G Gall N rN hballN y hy
  have hyN := hballN hy
  constructor
  · intro hc
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
    have hyWall : y ∈ Wall := hyN.2.1
    have hyWj := Set.mem_iInter.mp hyWall j
    by_cases hji : j = i
    · subst j
      exact hsegF y hj
    · have hcompl : y ∈ (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ := by
        simpa [W, hji] using hyWj
      exact False.elim (hcompl hj)
  · intro hFy
    have hyQ : y ∈ Qline := hyN.2.2.1
    rcases hyQ with ⟨hQlo, hQhi⟩
    have hline := hQline y hFy
    have hyseg : y ∈ segment Real a b := by
      rw [segment_eq_image]
      let u := Q y
      have hline' : y = a + u • (b - a) := by simpa [u] using hline
      refine ⟨u, ⟨by simpa [u] using hQlo.le, by simpa [u] using hQhi.le⟩, ?_⟩
      calc
        (1 - u) • a + u • b = a + u • (b - a) := by
          apply Prod.ext <;> simp [smul_sub, sub_smul] <;> ring
        _ = y := hline'.symm
    exact Set.mem_iUnion.mpr ⟨i, hyseg⟩

private theorem hparity :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))),
        d.1 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).2 - d.2 * (p.vertex (i + (1 :
        Fin (n + (3 : ℕ)))) - p.vertex i).1 ≠ (0 : ℝ)) → (∀ (y : Real × Real), (y ∉
        P3544T1BoundaryCarrier p) → ((∀ j, d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
        ≠ 0) → ((y ∈ P3544T1RayParity p ↔
        Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧
          y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 = 1)))) := by
  classical
  intro n p d hde y hyC hgv
  constructor
  · rintro ⟨_, d', hdv', hde', hodd⟩
    exact (P3597T1DirectionParity p y d d' hyC hgv hdv').trans hodd
  · intro hodd
    exact ⟨hyC, d, hgv, hde, hodd⟩

private theorem hparamY :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    (∀ j, D j ≠ 0) → (∀ (y : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), have t :=
    ((p.vertex j - y).1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1) /
      (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1);
  have u :=
    ((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) /
      (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 -
        d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1);
  y + t • d = p.vertex j + u • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j) ∧
    (∀ (t' : ℝ), ∀ (u' : ℝ), y + t' • d = p.vertex j + u' • (p.vertex (j + (1 : Fin (n + (3 :
        ℕ)))) - p.vertex j) → t' = t ∧ u' = u) ∧
      ((∃ (t' : ℝ), (0 : ℝ) < t' ∧ y + t' • d ∈ segment ℝ (p.vertex j) (p.vertex (j + (1 : Fin (n
          + (3 : ℕ)))))) ↔
        (0 : ℝ) < t ∧ (0 : ℝ) ≤ u ∧ u ≤ (1 : ℝ))) := by
  classical
  intro n p d D hD y j
  exact (P3597T1GenericRayStability p).2.2 y d j (hD j)

private theorem hiffX :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ (j : Fin (n + (3 : ℕ))), have t := ((p.vertex j - x).1 * (p.vertex (j + (1 : Fin (n + (3 :
        ℕ)))) - p.vertex j).2 - (p.vertex j - x).2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j).1) / (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).2 - d.2 *
        (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1); have u := ((p.vertex j - x).1 *
        d.2 - (p.vertex j - x).2 * d.1) / (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j).2 - d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1); x + t • d
        = p.vertex j + u • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j) ∧ (∀ (t' : ℝ), ∀
        (u' : ℝ), x + t' • d = p.vertex j + u' • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) -
        p.vertex j) → t' = t ∧ u' = u) ∧ ((∃ (t' : ℝ), (0 : ℝ) < t' ∧ x + t' • d ∈ segment ℝ
        (p.vertex j) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) ↔ (0 : ℝ) < t ∧ (0 : ℝ) ≤ u ∧ u ≤
        (1 : ℝ))) → (∀ (j : Fin (n + 3)), (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex
        j) (p.vertex (j + 1))) ↔
        0 < T j x ∧ 0 ≤ U j x ∧ U j x ≤ 1) := by
  classical
  intro n p x d D T U hparam j
  simpa [T, U, D] using (hparam j).2.2

private theorem hiffY :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ (y : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), have t := ((p.vertex j - y).1 * (p.vertex (j + (1
        : Fin (n + (3 : ℕ)))) - p.vertex j).2 - (p.vertex j - y).2 * (p.vertex (j + (1 : Fin (n +
        (3 : ℕ)))) - p.vertex j).1) / (d.1 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex
        j).2 - d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j).1); have u :=
        ((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / (d.1 * (p.vertex (j + (1 : Fin (n
        + (3 : ℕ)))) - p.vertex j).2 - d.2 * (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex
        j).1); y + t • d = p.vertex j + u • (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) - p.vertex j)
        ∧ (∀ (t' : ℝ), ∀ (u' : ℝ), y + t' • d = p.vertex j + u' • (p.vertex (j + (1 : Fin (n + (3
        : ℕ)))) - p.vertex j) → t' = t ∧ u' = u) ∧ ((∃ (t' : ℝ), (0 : ℝ) < t' ∧ y + t' • d ∈
        segment ℝ (p.vertex j) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) ↔ (0 : ℝ) < t ∧ (0 : ℝ)
        ≤ u ∧ u ≤ (1 : ℝ))) → (∀ (y : Real × Real), ∀ (j : Fin (n + 3)), (∃ t : Real, 0 < t ∧ y +
        t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔
        0 < T j y ∧ 0 ≤ U j y ∧ U j y ≤ 1) := by
  classical
  intro n p d D T U hparamY y j
  simpa [T, U, D] using (hparamY y j).2.2

private theorem hpred :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (∀ (j : Fin (n + 3)), U j x ≠ 0) → ((∀ (j : Fin (n + 3)), U j x ≠ 1) → ((
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    let Vall : Set (Real × Real) := ⋂ j, V j
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    let Wall : Set (Real × Real) := ⋂ j, W j
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    let Gall : Set (Real × Real) := ⋂ j, G j
    let N : Set (Real × Real) := Vall ∩ (Wall ∩ (Qline ∩ Gall))
    ∀ (rN : ℝ), (Metric.ball x rN ⊆ N) → ((∀ (j : Fin (n + 3)), (∃ t : Real, 0 < t ∧ x + t • d ∈
        segment Real (p.vertex j) (p.vertex (j + 1))) ↔ 0 < T j x ∧ 0 ≤ U j x ∧ U j x ≤ 1) → ((∀
        (y : Real × Real), ∀ (j : Fin (n + 3)), (∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real
        (p.vertex j) (p.vertex (j + 1))) ↔ 0 < T j y ∧ 0 ≤ U j y ∧ U j y ≤ 1) → (∀ (y : Real ×
        Real), (y ∈ Metric.ball x rN) → (∀ (j : Fin (n + 3)), (j ≠ i) → (((∃ t : Real, 0 < t ∧ y
        + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔
        (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))))))))))))
            := by
  classical
  intro n p i x a b d D T U hUzero hUone V Vall W Wall Q Qline g G Gall N rN hballN hiffX hiffY
      y hy j hji
  have hyVall : y ∈ Vall := (hballN hy).1
  have hyVj := Set.mem_iInter.mp hyVall j
  rw [hiffY y j, hiffX j]
  by_cases hu0 : U j x < 0
  · have hyU : U j y < 0 := by simpa [V, hji, hu0] using hyVj
    constructor <;> rintro ⟨ht, hU, hU1⟩
    · exact False.elim (not_le_of_gt hyU hU)
    · exact False.elim (not_le_of_gt hu0 hU)
  · by_cases hu1 : 1 < U j x
    · have hyU : 1 < U j y := by simpa [V, hji, hu0, hu1] using hyVj
      constructor <;> rintro ⟨ht, hU, hU1⟩
      · exact False.elim (not_le_of_gt hyU hU1)
      · exact False.elim (not_le_of_gt hu1 hU1)
    · have hinside : 0 < U j x ∧ U j x < 1 := by
        constructor
        · exact lt_of_le_of_ne (le_of_not_gt hu0) (Ne.symm (hUzero j))
        · exact lt_of_le_of_ne (le_of_not_gt hu1) (hUone j)
      by_cases ht : 0 < T j x
      · have hycond : 0 < T j y ∧ 0 < U j y ∧ U j y < 1 := by
          simpa [V, hji, hu0, hu1, ht] using hyVj
        constructor
        · intro h
          exact ⟨ht, hinside.1.le, hinside.2.le⟩
        · intro h
          exact ⟨hycond.1, hycond.2.1.le, hycond.2.2.le⟩
      · have hycond : T j y < 0 ∧ 0 < U j y ∧ U j y < 1 := by
          simpa [V, hji, hu0, hu1, ht] using hyVj
        constructor
        · rintro ⟨hty, _, _⟩
          exact False.elim (not_lt_of_ge (le_of_lt hycond.1) hty)
        · rintro ⟨htx, _, _⟩
          exact False.elim (ht htx)

private theorem hcardSplit :
    ∀ (n : Nat), ∀ (i : Fin (n + 3)), ∀ (A : Fin (n + 3) → Prop), Set.ncard {j | A j} = Set.ncard
        ({j | A j} \ {i}) + @ite Nat (A i) (Classical.propDecidable _) 1 0 := by
  classical
  intro n i A
  by_cases hi : A i
  · have hs : {j | A j} = insert i ({j | A j} \ {i}) := by
      ext j
      by_cases hji : j = i <;> simp [hji, hi]
    rw [hs, Set.ncard_insert_of_notMem (by simp)]
    simp [hi]
  · have hs : {j | A j} = {j | A j} \ {i} := by
      ext j
      simp [hi]
    rw [hs]
    simp [hi]

private theorem hrest :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (d : ℝ × ℝ), ∀ (rN : ℝ), (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (∀ (j : Fin (n +
        3)), (j ≠ i) → (((∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex j) (p.vertex (j
        + 1))) ↔ (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex j) (p.vertex (j +
        1))))))) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    ∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (S y \ {i} = S x \ {i})) := by
  classical
  intro n p i x d rN hpred S y hy
  ext j
  by_cases hji : j = i
  · simp [hji]
  · simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      exact ⟨(hpred y hy j hji).mp hmem, hne⟩
    · rintro ⟨hmem, hne⟩
      exact ⟨(hpred y hy j hji).mpr hmem, hne⟩

private theorem hiX :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    (T i x = 0) → ((∀ (j : Fin (n + 3)), (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex
        j) (p.vertex (j + 1))) ↔ 0 < T j x ∧ 0 ≤ U j x ∧ U j x ≤ 1) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    i ∉ S x)) := by
  classical
  intro n p i x d D T U hTi hiffX S
  let a := p.vertex i
  let b := p.vertex (i + 1)
  change ¬ (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real a b)
  rw [hiffX i]
  simp [hTi]

private theorem hiY :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
    let V : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then {y | 0 < U j y ∧ U j y < 1}
      else if U j x < 0 then {y | U j y < 0}
      else if 1 < U j x then {y | 1 < U j y}
      else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
      else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
    let Vall : Set (Real × Real) := ⋂ j, V j
    let W : Fin (n + 3) → Set (Real × Real) := fun j =>
      if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
    let Wall : Set (Real × Real) := ⋂ j, W j
    let Q : (Real × Real) → Real := fun y =>
      if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
      else (y.1 - a.1) / (b.1 - a.1)
    let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
    let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
    let G : Fin (n + 3) → Set (Real × Real) := fun j =>
      {y | g j y < 0} ∪ {y | 0 < g j y}
    let Gall : Set (Real × Real) := ⋂ j, G j
    let N : Set (Real × Real) := Vall ∩ (Wall ∩ (Qline ∩ Gall))
    ∀ (rN : ℝ), (Metric.ball x rN ⊆ N) → ((∀ (y : Real × Real), ∀ (j : Fin (n + 3)), (∃ t : Real,
        0 < t ∧ y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔ 0 < T j y ∧ 0 ≤ U j y
        ∧ U j y ≤ 1) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    ∀ (y : Real × Real), (y ∈ Metric.ball x rN) → ((i ∈ S y ↔ 0 < T i y)))) := by
  classical
  intro n p i x a b d D T U V Vall W Wall Q Qline g G Gall N rN hballN hiffY S y hy
  change ((∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real a b) ↔ 0 < T i y)
  rw [hiffY y i]
  have hyVi := Set.mem_iInter.mp ((hballN hy).1) i
  have hUy : 0 < U i y ∧ U i y < 1 := by
    simpa [V] using hyVi
  constructor
  · rintro ⟨ht, _, _⟩
    exact ht
  · intro ht
    exact ⟨ht, hUy.1.le, hUy.2.le⟩

private theorem hcount :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real), ∀
        (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    ∀ (rN : ℝ), (∀ (A : Fin (n + 3) → Prop), Set.ncard {j | A j} = Set.ncard ({j | A j} \ {i}) +
        @ite Nat (A i) (Classical.propDecidable _) 1 0) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (S y \ {i} = S x \ {i})) → ((i ∉ S x) → ((∀ (y
        : Real × Real), (y ∈ Metric.ball x rN) → ((i ∈ S y ↔ 0 < T i y))) → (∀ (y : Real × Real),
        (y ∈ Metric.ball x rN) → ((S y).ncard = (S x).ncard + if 0 < T i y then 1 else 0))))) := by
  classical
  intro n p i x d D T rN hcardSplit S hrest hiX hiY y hy
  change {j : Fin (n + 3) | j ∈ S y}.ncard =
    {j : Fin (n + 3) | j ∈ S x}.ncard + if 0 < T i y then 1 else 0
  rw [hcardSplit (fun j => j ∈ S y), hcardSplit (fun j => j ∈ S x)]
  have hrest' : ({j : Fin (n + 3) | j ∈ S y} \ {i}) =
      ({j : Fin (n + 3) | j ∈ S x} \ {i}) := by
    exact hrest y hy
  rw [hrest', ite_eq_right hiX]
  simp only [add_zero]
  rw [hiY y hy]

private theorem hTformula :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = (b.1 - a.1) * (y.2 - a.2) - (y.1 - a.1) * (b.2 - a.2)) → (∀ (y :
        Real × Real), T i y = F y / D i) := by
  classical
  intro n p i a b d D T F hFexplicit y
  rw [hFexplicit]
  dsimp [T, D]
  simp only [show p.vertex (i + 1) = b by rfl, show p.vertex i = a by rfl]
  congr 1; ring

private theorem hmulF :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    (∀ j, D j ≠ 0) → (
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), T i y = F y / D i) → (∀ (y : Real × Real), F y = T i y * D i)) := by
  classical
  intro n p i a b d D T hD F hTformula y
  rw [hTformula y]
  field_simp [hD i]


private theorem hsignPosPos :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = T i y * D i) → (∀ (y : Real × Real), (0 < D i) → ((0 < T i y ↔ 0
        < F y))) := by
  classical
  intro n p i a b d D T F hmulF y hDpos
  constructor
  · intro ht
    have hp := mul_pos ht hDpos
    rw [← hmulF y] at hp
    exact hp
  · intro hF
    by_contra hT
    have hTle : T i y ≤ 0 := le_of_not_gt hT
    have hp := mul_nonpos_of_nonpos_of_nonneg hTle hDpos.le
    rw [← hmulF y] at hp
    linarith

private theorem hsignPosNeg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = T i y * D i) → (∀ (y : Real × Real), (D i < 0) → ((0 < T i y ↔ F
        y < 0))) := by
  classical
  intro n p i a b d D T F hmulF y hDneg
  constructor
  · intro ht
    have hn := mul_neg_of_pos_of_neg ht hDneg
    rw [← hmulF y] at hn
    exact hn
  · intro hF
    by_contra hT
    have hTle : T i y ≤ 0 := le_of_not_gt hT
    have hp := mul_nonneg_of_nonpos_of_nonpos hTle (le_of_lt hDneg)
    rw [← hmulF y] at hp
    linarith

private theorem hsignNegPos :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = T i y * D i) → (∀ (y : Real × Real), (0 < D i) → ((T i y < 0 ↔ F
        y < 0))) := by
  classical
  intro n p i a b d D T F hmulF y hDpos
  constructor
  · intro ht
    have hn := mul_neg_of_neg_of_pos ht hDpos
    rw [← hmulF y] at hn
    exact hn
  · intro hF
    by_contra hT
    have hTnonneg : 0 ≤ T i y := le_of_not_gt hT
    have hp := mul_nonneg hTnonneg hDpos.le
    rw [← hmulF y] at hp
    linarith

private theorem hsignNegNeg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), F y = T i y * D i) → (∀ (y : Real × Real), (D i < 0) → ((T i y < 0 ↔ 0
        < F y))) := by
  classical
  intro n p i a b d D T F hmulF y hDneg
  constructor
  · intro ht
    have htn : 0 < -T i y := by linarith
    have hdn : 0 < -D i := by linarith
    have hp := mul_pos htn hdn
    have heq : (-T i y) * (-D i) = F y := by
      calc
        (-T i y) * (-D i) = T i y * D i := by ring
        _ = F y := (hmulF y).symm
    rw [heq] at hp
    exact hp
  · intro hF
    by_contra hT
    have hTnonneg : 0 ≤ T i y := le_of_not_gt hT
    have hp := mul_nonpos_of_nonneg_of_nonpos hTnonneg (le_of_lt hDneg)
    rw [← hmulF y] at hp
    linarith

private theorem hDpositive :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    (∀ j, D j ≠ 0) → (0 < D i ∨ D i < 0) := by
  classical
  intro n p i d D hD
  exact lt_or_gt_of_ne (Ne.symm (hD i))

private theorem hlocal :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
      (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
        (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    ∀ (rN : ℝ), (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (y ∈ P3544T1BoundaryCarrier p ↔
        F y = 0)) → ((∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (∀ j, d.1 * (p.vertex j -
        y).2 - d.2 * (p.vertex j - y).1 ≠ 0)) → ((∀ (y : Real × Real), (y ∉
        P3544T1BoundaryCarrier p) → ((∀ j, d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
        ≠ 0) → ((y ∈ P3544T1RayParity p ↔ Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧ y +
        t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 = 1)))) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    ((∀ (y : Real ×
        Real), (y ∈ Metric.ball x rN) → ((S y).ncard = (S x).ncard + if 0 < T i y then 1 else 0))
        → ((∀ (y : Real × Real), F y = T i y * D i) → ((∀ (y : Real × Real), (0 < D i) → ((0 < T
        i y ↔ 0 < F y))) → ((∀ (y : Real × Real), (D i < 0) → ((0 < T i y ↔ F y < 0))) → ((∀ (y :
        Real × Real), (0 < D i) → ((T i y < 0 ↔ F y < 0))) → ((∀ (y : Real × Real), (D i < 0) →
        ((T i y < 0 ↔ 0 < F y))) → ((0 < D i ∨ D i < 0) → (
    let s : Bool :=
      if (S x).ncard % 2 = 0 then decide (0 < D i) else decide (D i < 0)
    ∀ (y : Real × Real), (y ∈ Metric.ball x rN) → ((y ∈ P3544T1RayParity p ↔ if s then 0 < F y
        else F y < 0))))))))))))) := by
  classical
  intro n p i x a b d D T F rN hcarrier hgenericY hparity S hcount hmulF hsignPosPos hsignPosNeg
      hsignNegPos hsignNegNeg hDpositive s y hy
  by_cases hyC : y ∈ P3544T1BoundaryCarrier p
  · have hFy := (hcarrier y hy).mp hyC
    simp [P3544T1RayParity, hyC, hFy, s]
  · have hFy : F y ≠ 0 := by
      intro h
      exact hyC ((hcarrier y hy).mpr h)
    have hg := hgenericY y hy
    have hcnt := hcount y hy
    have hTneY : T i y ≠ 0 := by
      intro ht
      apply hFy
      rw [hmulF y, ht]
      simp
    have hcountodd : (S y).ncard % 2 = 1 ↔
        if (S x).ncard % 2 = 0 then 0 < T i y else T i y < 0 := by
      by_cases he : (S x).ncard % 2 = 0
      · by_cases ht : 0 < T i y
        · rw [hcnt, ite_eq_left ht, he]
          simp [Nat.add_mod, he, ht]
        · rw [hcnt, ite_eq_right ht, he]
          simp [he, ht]
      · have ho : (S x).ncard % 2 = 1 := by omega
        by_cases ht : 0 < T i y
        · rw [hcnt, ite_eq_left ht, ho]
          simp [Nat.add_mod, ho]; linarith
        · rw [hcnt, ite_eq_right ht, ho]
          have hTneg : T i y < 0 := lt_of_le_of_ne (le_of_not_gt ht) hTneY
          simp [ho, hTneg]
    have hpar : y ∈ P3544T1RayParity p ↔
        (if (S x).ncard % 2 = 0 then 0 < T i y else T i y < 0) := by
      exact (hparity y hyC hg).trans hcountodd
    rw [hpar]
    by_cases he : (S x).ncard % 2 = 0
    · rcases hDpositive with hDpos | hDneg
      · have hs : s = true := by simp [s, he, hDpos]
        simpa [hs, he] using hsignPosPos y hDpos
      · have hs : s = false := by simp [s, he, not_lt.mpr (le_of_lt hDneg)]
        simpa [hs, he] using hsignPosNeg y hDneg
    · have ho : (S x).ncard % 2 = 1 := by omega
      rcases hDpositive with hDpos | hDneg
      · have hs : s = false := by simp [s, ho, not_lt.mpr (le_of_lt hDpos)]
        simpa [hs, ho] using hsignNegPos y hDpos
      · have hs : s = true := by simp [s, ho, hDneg]
        simpa [hs, ho] using hsignNegNeg y hDneg

private theorem hnormsq :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (a ≠ b) → (0 < (b.1 - a.1)^2 + (b.2 - a.2)^2) := by
  classical
  intro n p i a b hab
  by_cases h1 : b.1 = a.1
  · have h2 : b.2 - a.2 ≠ 0 := by
      intro he
      apply hab
      apply Prod.ext
      · exact h1.symm
      · linarith
    nlinarith [sq_pos_of_ne_zero h2]
  · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h1)]

private theorem hnormal :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    (x ∈ segment ℝ a b) → (
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    (∀ (y : Real × Real), (y ∈ segment Real a b) → (F y = 0)) → (∀ (h : Real), F (x + h • (-(b.2
        - a.2), b.1 - a.1)) =
      h * ((b.1 - a.1)^2 + (b.2 - a.2)^2))) := by
  classical
  intro n p i x a b hxseg F hsegF h
  have hxF : F x = 0 := hsegF x hxseg
  simp [F, P3381T1TriangleDeterminant] at hxF ⊢
  linear_combination hxF

private theorem htransverse :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    ∀ (rN : ℝ), (rN > (0 : ℝ)) → ((0 < (b.1 - a.1)^2 + (b.2 - a.2)^2) → ((∀ (h : Real), F (x + h
        • (-(b.2 - a.2), b.1 - a.1)) = h * ((b.1 - a.1)^2 + (b.2 - a.2)^2)) → (∀ (ε : Real), (0 <
        ε) → (∃ y z : Real × Real, y ∈ Metric.ball x (min rN ε) ∧
        z ∈ Metric.ball x (min rN ε) ∧ 0 < F y ∧ F z < 0)))) := by
  classical
  intro n p i x a b F rN hrN hnormsq hnormal ε hε
  let ρ := min rN ε
  have hρ : 0 < ρ := lt_min hrN hε
  have hc : Continuous (fun h : Real => x + h • (-(b.2 - a.2), b.1 - a.1)) := by fun_prop
  obtain ⟨δ, hδ, hdist⟩ :=
    (Metric.continuousAt_iff.mp (hc.continuousAt (x := 0))) ρ hρ
  have hp : dist (δ / 2) (0 : Real) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hm : dist (-(δ / 2)) (0 : Real) < δ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  let y := x + (δ / 2) • (-(b.2 - a.2), b.1 - a.1)
  let z := x + (-(δ / 2)) • (-(b.2 - a.2), b.1 - a.1)
  have hyρ : y ∈ Metric.ball x ρ := by simpa [y, Metric.mem_ball] using hdist hp
  have hzρ : z ∈ Metric.ball x ρ := by simpa [z, Metric.mem_ball] using hdist hm
  refine ⟨y, z, hyρ, hzρ, ?_, ?_⟩
  · rw [hnormal]
    exact mul_pos (by linarith) hnormsq
  · rw [hnormal]
    exact mul_neg_of_neg_of_pos (by linarith) hnormsq

private theorem hclosureOdd :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    ∀ (rN : ℝ),
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    let s : Bool :=
      if (S x).ncard % 2 = 0 then decide (0 < D i) else decide (D i < 0)
    (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → ((y ∈ P3544T1RayParity p ↔ if s then 0 < F y
        else F y < 0))) → ((∀ (ε : Real), (0 < ε) → (∃ y z : Real × Real, y ∈ Metric.ball x (min
        rN ε) ∧ z ∈ Metric.ball x (min rN ε) ∧ 0 < F y ∧ F z < 0)) → (x ∈ closure
        (P3544T1RayParity p))) := by
  classical
  intro n p i x a b d D F rN S s hlocal htransverse
  rw [mem_closure_iff]
  intro U hUopen hxU
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  obtain ⟨yp, ym, hyp, hym, hFp, hFm⟩ := htransverse ε hε
  have hyN : yp ∈ Metric.ball x rN := Metric.ball_subset_ball (min_le_left _ _) hyp
  have hymN : ym ∈ Metric.ball x rN := Metric.ball_subset_ball (min_le_left _ _) hym
  by_cases hs : s = true
  · have hsign : (if s then 0 < F yp else F yp < 0) := by simp [hs, hFp]
    have hyo := (hlocal yp hyN).mpr hsign
    exact ⟨yp, ⟨hεball (Metric.ball_subset_ball (min_le_right _ _) hyp), hyo⟩⟩
  · have hs' : s = false := Bool.eq_false_of_not_eq_true hs
    have hsign : (if s then 0 < F ym else F ym < 0) := by simp [hs', hFm]
    have hyo := (hlocal ym hymN).mpr hsign
    exact ⟨ym, ⟨hεball (Metric.ball_subset_ball (min_le_right _ _) hym), hyo⟩⟩

private theorem hclosureEven :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + 3)), ∀ (x : Real × Real),
    let a := p.vertex i
    let b := p.vertex (i + 1)
    ∀ (d : ℝ × ℝ),
    let D : Fin (n + 3) → Real := fun j =>
      d.1 * (p.vertex (j + 1) - p.vertex j).2 -
        d.2 * (p.vertex (j + 1) - p.vertex j).1
    let F : (Real × Real) → Real :=
      fun y => P3381T1TriangleDeterminant ![a, b, y]
    ∀ (rN : ℝ), (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → (y ∈ P3544T1BoundaryCarrier p ↔
        F y = 0)) → (
    let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
      z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
    let s : Bool :=
      if (S x).ncard % 2 = 0 then decide (0 < D i) else decide (D i < 0)
    (∀ (y : Real × Real), (y ∈ Metric.ball x rN) → ((y ∈ P3544T1RayParity p ↔ if s then 0 < F y
        else F y < 0))) → ((∀ (ε : Real), (0 < ε) → (∃ y z : Real × Real, y ∈ Metric.ball x (min
        rN ε) ∧ z ∈ Metric.ball x (min rN ε) ∧ 0 < F y ∧ F z < 0)) → (x ∈ closure
        (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ))) := by
  classical
  intro n p i x a b d D F rN hcarrier S s hlocal htransverse
  rw [mem_closure_iff]
  intro U hUopen hxU
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  obtain ⟨yp, ym, hyp, hym, hFp, hFm⟩ := htransverse ε hε
  have hyN : yp ∈ Metric.ball x rN := Metric.ball_subset_ball (min_le_left _ _) hyp
  have hymN : ym ∈ Metric.ball x rN := Metric.ball_subset_ball (min_le_left _ _) hym
  by_cases hs : s = true
  · have hsign : ¬ (if s then 0 < F ym else F ym < 0) := by
      simp [hs]
      linarith
    have hnotO : ym ∉ P3544T1RayParity p := by
      intro hO
      exact hsign ((hlocal ym hymN).mp hO)
    have hnotC : ym ∉ P3544T1BoundaryCarrier p := by
      intro hC
      have : F ym = 0 := (hcarrier ym hymN).mp hC
      linarith
    have hmem : ym ∈ (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ := by
      simp [Set.mem_compl_iff, hnotO, hnotC]
    exact ⟨ym, ⟨hεball (Metric.ball_subset_ball (min_le_right _ _) hym), hmem⟩⟩
  · have hs' : s = false := Bool.eq_false_of_not_eq_true hs
    have hsign : ¬ (if s then 0 < F yp else F yp < 0) := by
      simp [hs']
      linarith
    have hnotO : yp ∉ P3544T1RayParity p := by
      intro hO
      exact hsign ((hlocal yp hyN).mp hO)
    have hnotC : yp ∉ P3544T1BoundaryCarrier p := by
      intro hC
      have : F yp = 0 := (hcarrier yp hyN).mp hC
      linarith
    have hmem : yp ∈ (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ := by
      simp [Set.mem_compl_iff, hnotO, hnotC]
    exact ⟨yp, ⟨hεball (Metric.ball_subset_ball (min_le_right _ _) hyp), hmem⟩⟩

end SideCrossingProof

theorem P3597T1SideCrossing {n : Nat} (p : P3381T1PolygonBoundary n)
    (i : Fin (n + 3)) (x : Real × Real)
    (hx : x ∈ openSegment Real (p.vertex i) (p.vertex (i + 1))) :
    ∃ r : Real, 0 < r ∧
      (∃ s : Bool, ∀ y ∈ Metric.ball x r,
        (y ∈ P3544T1RayParity p ↔
          if s then 0 < P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i + 1), y]
          else P3381T1TriangleDeterminant
            ![p.vertex i, p.vertex (i + 1), y] < 0)) ∧
      x ∈ closure (P3544T1RayParity p) ∧
      x ∈ closure (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ := by
-- BODY
  classical
  let a := p.vertex i
  let b := p.vertex (i + 1)
  have hidx : i ≠ i + 1 := SideCrossingProof.hidx n i
  have hab : a ≠ b := SideCrossingProof.hab n p i hidx
  have hxleft : x ≠ a := SideCrossingProof.hxleft n p i x hx hab
  have hxright : x ≠ b := SideCrossingProof.hxright n p i x hx hab hxleft
  have hxseg : x ∈ segment Real a b := SideCrossingProof.hxseg n p i x hx
  rw [openSegment_eq_image] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  have hxline : x = a + q • (b - a) := SideCrossingProof.hxline n p i x q hxq
  have hx1 : x.1 = a.1 + q * (b.1 - a.1) := SideCrossingProof.hx1 n p i x q hxline
  have hx2 : x.2 = a.2 + q * (b.2 - a.2) := SideCrossingProof.hx2 n p i x q hxline
  have hxnotseg : ∀ j : Fin (n + 3), j ≠ i →
      x ∉ segment Real (p.vertex j) (p.vertex (j + 1)) := SideCrossingProof.hxnotseg n p i x
          hxleft hxright hxseg
  have hnonvertex : ∀ k : Fin (n + 3), p.vertex k ≠ x := SideCrossingProof.hnonvertex n p i x
      hxleft hxnotseg
  have ⟨d, hdv, hde⟩ := (P3597T1GenericRayStability p).1 x hnonvertex
  let D : Fin (n + 3) → Real := fun j =>
    d.1 * (p.vertex (j + 1) - p.vertex j).2 -
      d.2 * (p.vertex (j + 1) - p.vertex j).1
  let T : Fin (n + 3) → (Real × Real) → Real := fun j y =>
    (((p.vertex j - y).1 * (p.vertex (j + 1) - p.vertex j).2 -
      (p.vertex j - y).2 * (p.vertex (j + 1) - p.vertex j).1) / D j)
  let U : Fin (n + 3) → (Real × Real) → Real := fun j y =>
    (((p.vertex j - y).1 * d.2 - (p.vertex j - y).2 * d.1) / D j)
  have hD : ∀ j, D j ≠ 0 := hde
  have hparam (j : Fin (n + 3)) := SideCrossingProof.hparam n p x d hD j
  have hcontT (j : Fin (n + 3)) : Continuous (T j) := SideCrossingProof.hcontT n p d hD j
  have hcontU (j : Fin (n + 3)) : Continuous (U j) := SideCrossingProof.hcontU n p d hD j
  have hTi : T i x = 0 := SideCrossingProof.hTi n p i x q hx1 hx2 d hD
  have hUi : U i x = q := SideCrossingProof.hUi n p i x q hx1 hx2 d hD
  have hUzero (j : Fin (n + 3)) : U j x ≠ 0 := SideCrossingProof.hUzero n p x d hdv hD j
  have hUone (j : Fin (n + 3)) : U j x ≠ 1 := SideCrossingProof.hUone n p x d hdv hD j
  have hTne (j : Fin (n + 3)) (hji : j ≠ i)
      (hinside : 0 < U j x ∧ U j x < 1) : T j x ≠ 0 := SideCrossingProof.hTne n p i x hxnotseg d
          hparam j hji hinside
  let V : Fin (n + 3) → Set (Real × Real) := fun j =>
    if j = i then {y | 0 < U j y ∧ U j y < 1}
    else if U j x < 0 then {y | U j y < 0}
    else if 1 < U j x then {y | 1 < U j y}
    else if 0 < T j x then {y | 0 < T j y ∧ 0 < U j y ∧ U j y < 1}
    else {y | T j y < 0 ∧ 0 < U j y ∧ U j y < 1}
  have hVopen (j : Fin (n + 3)) : IsOpen (V j) := SideCrossingProof.hVopen n p i x d hcontT hcontU j
  have hVmem : ∀ j, x ∈ V j := SideCrossingProof.hVmem n p i x q hq d hUi hUzero hUone hTne
  let Vall : Set (Real × Real) := ⋂ j, V j
  have hVallopen : IsOpen Vall := SideCrossingProof.hVallopen n p i x d hVopen
  have hxVall : x ∈ Vall := SideCrossingProof.hxVall n p i x d hVmem
  obtain ⟨rV, hrV, hballV⟩ := Metric.isOpen_iff.mp hVallopen x hxVall
  have hcompactseg (j : Fin (n + 3)) :
      IsCompact (segment Real (p.vertex j) (p.vertex (j + 1))) := SideCrossingProof.hcompactseg n
          p j
  let W : Fin (n + 3) → Set (Real × Real) := fun j =>
    if j = i then Set.univ else (segment Real (p.vertex j) (p.vertex (j + 1)))ᶜ
  have hWopen (j : Fin (n + 3)) : IsOpen (W j) := SideCrossingProof.hWopen n p i hcompactseg j
  have hWmem : ∀ j, x ∈ W j := SideCrossingProof.hWmem n p i x hxnotseg
  let Wall : Set (Real × Real) := ⋂ j, W j
  have hWallopen : IsOpen Wall := SideCrossingProof.hWallopen n p i hWopen
  have hxWall : x ∈ Wall := SideCrossingProof.hxWall n p i x hWmem
  let F : (Real × Real) → Real :=
    fun y => P3381T1TriangleDeterminant ![a, b, y]
  have hFexplicit (y : Real × Real) : F y =
      (b.1 - a.1) * (y.2 - a.2) - (y.1 - a.1) * (b.2 - a.2) := SideCrossingProof.hFexplicit n p i y
  have hsegF (y : Real × Real) (hy : y ∈ segment Real a b) : F y = 0 := SideCrossingProof.hsegF n
      p i hFexplicit y hy
  let Q : (Real × Real) → Real := fun y =>
    if b.1 - a.1 = 0 then (y.2 - a.2) / (b.2 - a.2)
    else (y.1 - a.1) / (b.1 - a.1)
  have hecoord : (b.1 - a.1 ≠ 0) ∨ (b.2 - a.2 ≠ 0) := SideCrossingProof.hecoord n p i hab
  have hQcont : Continuous Q := SideCrossingProof.hQcont n p i hecoord
  have hQx : Q x = q := SideCrossingProof.hQx n p i x q hx1 hx2 hecoord
  have hQline (y : Real × Real) (hFy : F y = 0) :
      y = a + Q y • (b - a) := SideCrossingProof.hQline n p i hFexplicit hecoord y hFy
  let Qline : Set (Real × Real) := {y | 0 < Q y ∧ Q y < 1}
  have hQlineopen : IsOpen Qline := SideCrossingProof.hQlineopen n p i hQcont
  have hxQline : x ∈ Qline := SideCrossingProof.hxQline n p i x q hq hQx
  let g : Fin (n + 3) → (Real × Real) → Real := fun j y =>
    d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1
  have hcontg (j : Fin (n + 3)) : Continuous (g j) := SideCrossingProof.hcontg n p d j
  let G : Fin (n + 3) → Set (Real × Real) := fun j =>
    {y | g j y < 0} ∪ {y | 0 < g j y}
  have hGopen (j : Fin (n + 3)) : IsOpen (G j) := SideCrossingProof.hGopen n p d hcontg j
  have hGmem : ∀ j, x ∈ G j := SideCrossingProof.hGmem n p x d hdv
  let Gall : Set (Real × Real) := ⋂ j, G j
  have hGallopen : IsOpen Gall := SideCrossingProof.hGallopen n p d hGopen
  have hxGall : x ∈ Gall := SideCrossingProof.hxGall n p x d hGmem
  let N : Set (Real × Real) := Vall ∩ (Wall ∩ (Qline ∩ Gall))
  have hNopen : IsOpen N := hVallopen.inter (hWallopen.inter (hQlineopen.inter hGallopen))
  have hxN : x ∈ N := ⟨hxVall, ⟨hxWall, ⟨hxQline, hxGall⟩⟩⟩
  obtain ⟨rN, hrN, hballN⟩ := Metric.isOpen_iff.mp hNopen x hxN
  have hcarrier (y : Real × Real) (hy : y ∈ Metric.ball x rN) :
      y ∈ P3544T1BoundaryCarrier p ↔ F y = 0 := SideCrossingProof.hcarrier n p i x d hsegF
          hQline rN hballN y hy
  have hgenericY (y : Real × Real) (hy : y ∈ Metric.ball x rN) :
      ∀ j, d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1 ≠ 0 := (show
          ∀ j, d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1 ≠ 0
        from by
          classical
          have hyGall : y ∈ Gall := (hballN hy).2.2.2
          intro j
          have hGj := Set.mem_iInter.mp hyGall j
          have hg : g j y < 0 ∨ 0 < g j y := by simpa [G] using hGj
          rcases hg with h | h
          · simpa [g] using (ne_of_lt h)
          · simpa [g] using (ne_of_gt h))
  have hparity (y : Real × Real) (hyC : y ∉ P3544T1BoundaryCarrier p)
      (hgv : ∀ j, d.1 * (p.vertex j - y).2 - d.2 * (p.vertex j - y).1 ≠ 0) :
      (y ∈ P3544T1RayParity p ↔
        Set.ncard {j : Fin (n + 3) | ∃ t : Real, 0 < t ∧
          y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))} % 2 = 1) :=
              SideCrossingProof.hparity n p d hde y hyC hgv
  have hparamY (y : Real × Real) (j : Fin (n + 3)) := SideCrossingProof.hparamY n p d hD y j
  have hiffX (j : Fin (n + 3)) :
      (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔
        0 < T j x ∧ 0 ≤ U j x ∧ U j x ≤ 1 := SideCrossingProof.hiffX n p x d hparam j
  have hiffY (y : Real × Real) (j : Fin (n + 3)) :
      (∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔
        0 < T j y ∧ 0 ≤ U j y ∧ U j y ≤ 1 := SideCrossingProof.hiffY n p d hparamY y j
  have hpred (y : Real × Real) (hy : y ∈ Metric.ball x rN) (j : Fin (n + 3))
      (hji : j ≠ i) :
      ((∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))) ↔
        (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1)))) :=
            SideCrossingProof.hpred n p i x d hUzero hUone rN hballN hiffX hiffY y hy j hji
  have hcardSplit (A : Fin (n + 3) → Prop) :
      Set.ncard {j | A j} = Set.ncard ({j | A j} \ {i}) + @ite Nat (A i) (Classical.propDecidable
          _) 1 0 :=
          SideCrossingProof.hcardSplit n i A
  let S : (Real × Real) → Set (Fin (n + 3)) := fun z => {j | ∃ t : Real, 0 < t ∧
    z + t • d ∈ segment Real (p.vertex j) (p.vertex (j + 1))}
  have hrest (y : Real × Real) (hy : y ∈ Metric.ball x rN) : S y \ {i} = S x \ {i} :=
      SideCrossingProof.hrest n p i x d rN hpred y hy
  have hiX : i ∉ S x := SideCrossingProof.hiX n p i x d hTi hiffX
  have hiY (y : Real × Real) (hy : y ∈ Metric.ball x rN) :
      (i ∈ S y ↔ 0 < T i y) := SideCrossingProof.hiY n p i x d rN hballN hiffY y hy
  have hcount (y : Real × Real) (hy : y ∈ Metric.ball x rN) :
      (S y).ncard = (S x).ncard + if 0 < T i y then 1 else 0 := SideCrossingProof.hcount n p i x
          d rN hcardSplit hrest hiX hiY y hy
  have hTformula (y : Real × Real) : T i y = F y / D i := SideCrossingProof.hTformula n p i d
      hFexplicit y
  have hmulF (y : Real × Real) : F y = T i y * D i := SideCrossingProof.hmulF n p i d hD hTformula y
  have hsignPosPos (y : Real × Real) (hDpos : 0 < D i) :
      (0 < T i y ↔ 0 < F y) := SideCrossingProof.hsignPosPos n p i d hmulF y hDpos
  have hsignPosNeg (y : Real × Real) (hDneg : D i < 0) :
      (0 < T i y ↔ F y < 0) := SideCrossingProof.hsignPosNeg n p i d hmulF y hDneg
  have hsignNegPos (y : Real × Real) (hDpos : 0 < D i) :
      (T i y < 0 ↔ F y < 0) := SideCrossingProof.hsignNegPos n p i d hmulF y hDpos
  have hsignNegNeg (y : Real × Real) (hDneg : D i < 0) :
      (T i y < 0 ↔ 0 < F y) := SideCrossingProof.hsignNegNeg n p i d hmulF y hDneg
  have hDpositive : 0 < D i ∨ D i < 0 := SideCrossingProof.hDpositive n p i d hD
  let s : Bool :=
    if (S x).ncard % 2 = 0 then decide (0 < D i) else decide (D i < 0)
  have hlocal (y : Real × Real) (hy : y ∈ Metric.ball x rN) :
      (y ∈ P3544T1RayParity p ↔ if s then 0 < F y else F y < 0) := SideCrossingProof.hlocal n p
          i x d rN hcarrier hgenericY hparity hcount hmulF hsignPosPos hsignPosNeg
          hsignNegPos hsignNegNeg hDpositive y hy
  have hnormsq : 0 < (b.1 - a.1)^2 + (b.2 - a.2)^2 := SideCrossingProof.hnormsq n p i hab
  have hnormal (h : Real) : F (x + h • (-(b.2 - a.2), b.1 - a.1)) =
      h * ((b.1 - a.1)^2 + (b.2 - a.2)^2) := SideCrossingProof.hnormal n p i x hxseg hsegF h
  have htransverse (ε : Real) (hε : 0 < ε) :
      ∃ y z : Real × Real, y ∈ Metric.ball x (min rN ε) ∧
        z ∈ Metric.ball x (min rN ε) ∧ 0 < F y ∧ F z < 0 := SideCrossingProof.htransverse n p i x
            rN hrN hnormsq hnormal ε hε
  have hclosureOdd : x ∈ closure (P3544T1RayParity p) := SideCrossingProof.hclosureOdd n p i x
      d rN hlocal htransverse
  have hclosureEven : x ∈ closure (P3544T1RayParity p ∪ P3544T1BoundaryCarrier p)ᶜ :=
      SideCrossingProof.hclosureEven n p i x d rN hcarrier hlocal htransverse
  refine ⟨rN, hrN, ⟨s, ?_⟩, ?_, ?_⟩
  · intro y hy
    exact hlocal y hy
  · exact hclosureOdd
  · exact hclosureEven

end ApollonianSuperharmonic

end
