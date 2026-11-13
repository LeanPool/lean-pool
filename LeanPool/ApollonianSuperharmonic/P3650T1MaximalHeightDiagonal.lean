/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ExposedCornerAffineBasis

public import LeanPool.ApollonianSuperharmonic.P3650T1VisibleDiagonal
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- [TABLET NODE: P3650T1MaximalHeightDiagonal]

/-!
# P3650T1MaximalHeightDiagonal

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MaximalHeightGeometry

private theorem hSne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (¬∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        let S : Finset (Fin (n + 3)) := Finset.univ.filter fun i =>
          i ≠ E.b - 1 ∧ i ≠ E.b ∧ i ≠ E.b + 1 ∧ p.vertex i ∈ Δ
        S.Nonempty) ) := by
  classical
  intro n p E hnotempty Δ S
  by_contra h
  apply hnotempty
  intro i hi
  by_contra hn
  have hm : i ≠ E.b - 1 ∧ i ≠ E.b ∧ i ≠ E.b + 1 ∧ p.vertex i ∈ Δ := by
    exact ⟨by aesop, by aesop, by aesop, hi⟩
  exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩

private theorem hrange :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        ∀ (d : Fin (n + (3 : ℕ))), (d ≠ E.b - (1 : Fin (n + (3 : ℕ))) ∧ d ≠ E.b ∧ d ≠ E.b + (1 :
            Fin (n + (3 : ℕ))) ∧ p.vertex d ∈ Δ) → (∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
            (∀ (i : Fin (3 : ℕ)), (A : Fin (3 : ℕ) → ℝ × ℝ) i = ![p.vertex (E.b - (1 : Fin (n +
            (3 : ℕ)))), p.vertex E.b, p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))] i) → (Set.range A
            = ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real)))) ) := by
  classical
  intro n p E Δ d hdprops A hA
  rw [show (A : Fin 3 → Real × Real) =
    ![p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)] from funext hA]
  ext x
  simp
  tauto

private theorem hmem :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (Δ = convexHull Real (Set.range A)) → (∀ x,
            x ∈ Δ ↔ ∀ i, 0 ≤ A.coord i x) ) := by
  classical
  intro n p E Δ A hΔ x
  rw [hΔ]
  exact (Set.ext_iff.mp A.convexHull_eq_nonneg_coord x).trans (by simp)

private theorem hint :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (Δ = convexHull Real (Set.range A)) → (∀ x,
            x ∈ interior Δ ↔ ∀ i, 0 < A.coord i x) ) := by
  classical
  intro n p E Δ A hΔ x
  rw [hΔ]
  exact (Set.ext_iff.mp A.interior_convexHull x).trans (by simp)

private theorem hsum :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (d : Fin (n + (3 : ℕ))), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), A.coord 0 (p.vertex d) + A.coord 1 (p.vertex d)
            + A.coord 2 (p.vertex d) = 1 ) := by
  classical
  intro n p d A
  simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (p.vertex d)

private theorem hcoord0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), (d ≠ E.b) → ((d ≠ E.b + 1) → (∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ
            (ℝ × ℝ)), (A 1 = p.vertex E.b) → ((A 2 = p.vertex (E.b + 1)) → ((∀ i, 0 ≤ A.coord i
            (p.vertex d)) → ((A.coord 0 (p.vertex d) + A.coord 1 (p.vertex d) + A.coord 2
            (p.vertex d) = 1) → (0 < A.coord 0 (p.vertex d))))))) ) := by
  classical
  intro n p E d hdb hdnext A hA1 hA2 hcoord_nonneg hsum
  have hn : A.coord 0 (p.vertex d) ≠ 0 := by
    intro heq
    have hseg : p.vertex d ∈ segment Real (p.vertex E.b) (p.vertex (E.b + 1)) := by
      rw [← hA1, ← hA2, segment_eq_image_lineMap]
      refine ⟨A.coord 2 (p.vertex d), ⟨hcoord_nonneg 2, ?_⟩, ?_⟩
      · have := hcoord_nonneg 1
        linarith [hsum, heq]
      · apply A.ext_elem
        intro i
        rw [(A.coord i).apply_lineMap]
        fin_cases i <;> simp [AffineMap.lineMap_apply_ring, Fin.ext_iff] <;>
          linarith [hsum, heq]
    have h := p.edge_intersection E.b d (by
      intro heqidx
      exact hdb heqidx.symm)
    have hv : p.vertex d ∈ segment Real (p.vertex E.b) (p.vertex (E.b + 1)) ∩
        segment Real (p.vertex d) (p.vertex (d + 1)) := by
      constructor
      · exact hseg
      · exact left_mem_segment Real _ _
    rw [h] at hv
    rcases hv.1 with hv | hv
    · exact hdb (p.injective hv)
    · exact hdnext (p.injective hv)
  exact lt_of_le_of_ne (hcoord_nonneg 0) (Ne.symm hn)

private theorem hcoord2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), (d ≠ E.b - 1) → ((d ≠ E.b) → (∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ
            (ℝ × ℝ)), (A 0 = p.vertex (E.b - 1)) → ((A 1 = p.vertex E.b) → ((∀ i, 0 ≤ A.coord i
            (p.vertex d)) → ((A.coord 0 (p.vertex d) + A.coord 1 (p.vertex d) + A.coord 2
            (p.vertex d) = 1) → ((0 < A.coord 0 (p.vertex d)) → (0 < A.coord 2 (p.vertex
            d)))))))) ) := by
  classical
  intro n p E d hdprev hdb A hA0 hA1 hcoord_nonneg hsum hcoord0
  have hn : A.coord 2 (p.vertex d) ≠ 0 := by
    intro heq
    have hseg : p.vertex d ∈ segment Real (p.vertex (E.b - 1)) (p.vertex E.b) := by
      rw [← hA0, ← hA1, segment_eq_image_lineMap]
      refine ⟨A.coord 1 (p.vertex d), ⟨hcoord_nonneg 1, ?_⟩, ?_⟩
      · have := hcoord_nonneg 0
        linarith [hsum, heq]
      · apply A.ext_elem
        intro i
        rw [(A.coord i).apply_lineMap]
        fin_cases i <;> simp [AffineMap.lineMap_apply_ring, Fin.ext_iff] <;>
          linarith [hsum, heq]
    have h := p.edge_intersection (E.b - 1) d (by
      intro heqidx
      exact hdprev heqidx.symm)
    have hv : p.vertex d ∈ segment Real (p.vertex (E.b - 1))
        (p.vertex ((E.b - 1) + 1)) ∩ segment Real (p.vertex d) (p.vertex (d + 1)) := by
      constructor
      · simpa only [sub_add_cancel] using hseg
      · exact left_mem_segment Real _ _
    rw [h] at hv
    rcases hv.1 with hv | hv
    · exact hdprev (p.injective hv)
    · have heq : d = E.b := by
        simpa only [sub_add_cancel] using (p.injective hv)
      exact hdb heq
  exact lt_of_le_of_ne (hcoord_nonneg 2) (Ne.symm hn)

private theorem hheightlt :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (∀ i, 0 ≤ A.coord i
            (p.vertex d)) → ((A.coord 0 (p.vertex d) + A.coord 1 (p.vertex d) + A.coord 2
            (p.vertex d) = 1) → ((E.height (p.vertex d) = A.coord 1 (p.vertex d)) → ((0 < A.coord
            0 (p.vertex d)) → ((0 < A.coord 2 (p.vertex d)) → (E.height (p.vertex d) < 1))))) )
            := by
  classical
  intro n p E d A hcoord_nonneg hsum hheightd hcoord0 hcoord2
  rw [hheightd]
  have h1 := hcoord_nonneg 1
  have h2 := hcoord_nonneg 2
  have h0 := hcoord0
  linarith

private theorem hcoordB0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (A 1 = p.vertex E.b) → (
        let B := p.vertex E.b
        A.coord 0 B = 0) ) := by
  classical
  intro n p E A hA1 B
  dsimp [B]
  rw [← hA1]
  simp []

private theorem hcoordB1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (A 1 = p.vertex E.b) → (
        let B := p.vertex E.b
        A.coord 1 B = 1) ) := by
  classical
  intro n p E A hA1 B
  dsimp [B]
  rw [← hA1]
  simp []

private theorem hcoordB2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (A 1 = p.vertex E.b) → (
        let B := p.vertex E.b
        A.coord 2 B = 0) ) := by
  classical
  intro n p E A hA1 B
  dsimp [B]
  rw [← hA1]
  simp []

private theorem hqcoord :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        ∀ t, ∀ i, A.coord i (q t) = (1 - t) * A.coord i B + t * A.coord i P ) := by
  classical
  intro n p E d A B P q t i
  rw [(A.coord i).apply_lineMap]
  simp [AffineMap.lineMap_apply_ring]

private theorem hqheight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (E.height = A.coord
            (1 : Fin (3 : ℕ))) → (
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (A.coord 1 B = 1) → ((∀ t, ∀ i, A.coord i (q t) = (1 - t) * A.coord i B + t * A.coord i
            P) → (∀ t, E.height (q t) = (1 - t) + t * E.height P))) ) := by
  classical
  intro n p E d A hheight B P q hcoordB1 hqcoord t
  rw [hheight, hqcoord t 1, hcoordB1]
  ring

private theorem hqinterior :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        ∀ (d : Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (∀ x, x ∈
            interior Δ ↔ ∀ i, 0 < A.coord i x) → ((∀ i, 0 ≤ A.coord i (p.vertex d)) → ((A.coord 0
            (p.vertex d) + A.coord 1 (p.vertex d) + A.coord 2 (p.vertex d) = 1) → ((0 < A.coord 0
            (p.vertex d)) → ((0 < A.coord 2 (p.vertex d)) → (
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (A.coord 0 B = 0) → ((A.coord 1 B = 1) → ((A.coord 2 B = 0) → ((∀ t, ∀ i, A.coord i (q t)
            = (1 - t) * A.coord i B + t * A.coord i P) → (∀ t, 0 < t → t < 1 → q t ∈ interior
            Δ))))))))) ) := by
  classical
  intro n p E Δ d A hint hcoord_nonneg hsum hcoord0 hcoord2 B P q hcoordB0 hcoordB1 hcoordB2
      hqcoord t ht0 ht1
  apply (hint _).2
  intro i
  fin_cases i
  · change 0 < A.coord (0 : Fin 3) (q t)
    rw [hqcoord t 0, hcoordB0]
    dsimp [P]
    nlinarith [mul_pos ht0 hcoord0]
  · change 0 < A.coord (1 : Fin 3) (q t)
    rw [hqcoord t 1, hcoordB1]
    dsimp [P]
    nlinarith [hcoord_nonneg 1]
  · change 0 < A.coord (2 : Fin 3) (q t)
    rw [hqcoord t 2, hcoordB2]
    dsimp [P]
    nlinarith [mul_pos ht0 hcoord2]

private theorem hqleft :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (E : P3650T1ExposedCorner p),
              ∀ (d : Fin (n + (3 : ℕ))),
                ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
                  A 0 = p.vertex (E.b - 1) →
                    0 < A.coord 2 (p.vertex d) →
                      let B := p.vertex E.b;
                      let P := p.vertex d;
                      let q : Real → Real × Real := AffineMap.lineMap B P;
                      A.coord 2 B = 0 →
                        (∀ t,
                            ∀ i,
                              A.coord i (q t) = (1 - t) * A.coord i B + t * A.coord i P) →
                          ∀ t, 0 < t → q t ∉ segment Real (p.vertex (E.b - 1)) B
    ) := by
  classical
  intro n p E d A hA0 hcoord2 B P q hcoordB2 hqcoord t ht0 hs
  have hcoordprev : A.coord 2 (p.vertex (E.b - 1)) = 0 := by
    rw [← hA0]
    simp []
  rw [segment_eq_image_lineMap] at hs
  obtain ⟨u, hu, heq⟩ := hs
  have heqcoord := congrArg (A.coord 2) heq
  rw [(A.coord 2).apply_lineMap, hcoordprev, hcoordB2] at heqcoord
  have hqtpos : 0 < A.coord 2 (q t) := by
    rw [hqcoord t 2, hcoordB2]
    dsimp [P]
    nlinarith [mul_pos ht0 hcoord2]
  simp [] at heqcoord
  linarith

private theorem hqright :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (E : P3650T1ExposedCorner p),
              ∀ (d : Fin (n + (3 : ℕ))),
                ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
                  A 2 = p.vertex (E.b + 1) →
                    0 < A.coord 0 (p.vertex d) →
                      let B := p.vertex E.b;
                      let P := p.vertex d;
                      let q : Real → Real × Real := AffineMap.lineMap B P;
                      A.coord 0 B = 0 →
                        (∀ t,
                            ∀ i,
                              A.coord i (q t) = (1 - t) * A.coord i B + t * A.coord i P) →
                          ∀ t, 0 < t → q t ∉ segment Real B (p.vertex (E.b + 1))
    ) := by
  classical
  intro n p E d A hA2 hcoord0 B P q hcoordB0 hqcoord t ht0 hs
  have hcoordnext : A.coord 0 (p.vertex (E.b + 1)) = 0 := by
    rw [← hA2]
    simp []
  rw [segment_eq_image_lineMap] at hs
  obtain ⟨u, hu, heq⟩ := hs
  have heqcoord := congrArg (A.coord 0) heq
  rw [(A.coord 0).apply_lineMap, hcoordB0, hcoordnext] at heqcoord
  have hqtpos : 0 < A.coord 0 (q t) := by
    rw [hqcoord t 0, hcoordB0]
    dsimp [P]
    nlinarith [mul_pos ht0 hcoord0]
  simp [] at heqcoord
  linarith

private theorem hqclear :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (j
            : Fin (n + (3 : ℕ))), ∀ (w : ℝ × ℝ), j ≠ E.b - (1 : Fin (n + (3 : ℕ))) → j ≠ E.b → w
            ∈ interior ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))}) → w ∈ segment ℝ (p.vertex j) (p.vertex (j
            + (1 : Fin (n + (3 : ℕ))))) → ∃ (k : Fin (n + (3 : ℕ))), (k = j ∨ k = j + (1 : Fin (n
            + (3 : ℕ)))) ∧ p.vertex k ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} ∧ (E.height : ℝ × ℝ → ℝ) w ≤ (E.height : ℝ
            × ℝ → ℝ) (p.vertex k)) → (
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        let S : Finset (Fin (n + 3)) := Finset.univ.filter fun i =>
          i ≠ E.b - 1 ∧ i ≠ E.b ∧ i ≠ E.b + 1 ∧ p.vertex i ∈ Δ
        ∀ (d : Fin (n + (3 : ℕ))), (∀ x' ∈ S, (E.height : ℝ × ℝ → ℝ) (p.vertex x') ≤ (E.height :
            ℝ × ℝ → ℝ) (p.vertex d)) → (∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (∀ i, 0 ≤
            A.coord i (p.vertex d)) → ((E.height (p.vertex d) = A.coord 1 (p.vertex d)) → (
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (∀ t, 0 < t → t < 1 → q t ∈ interior Δ) → ((∀ t, 0 < t → t < 1 → E.height P < E.height (q
            t)) → ((∀ t, 0 < t → t < 1 → q t ∉ segment Real (p.vertex (E.b - 1)) B) → ((∀ t, 0 <
            t → t < 1 → q t ∉ segment Real B (p.vertex (E.b + 1))) → (∀ t, 0 < t → t < 1 → q t ∉
            P3544T1BoundaryCarrier p)))))))) ) := by
  classical
  intro n p E hentry Δ S d hdmax A hcoord_nonneg hheightd B P q hqinterior hqmargin hqleft
      hqright t ht0 ht1 hc
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
  change q t ∈ segment Real (p.vertex j) (p.vertex (j + 1)) at hj
  have hspecial : j ≠ E.b - 1 ∧ j ≠ E.b := by
    constructor
    · intro h
      exact hqleft t ht0 ht1 (by simpa [h, sub_add_cancel] using hj)
    · intro h
      exact hqright t ht0 ht1 (by simpa [h] using hj)
  obtain ⟨k, hkj, hkΔ, hle⟩ := hentry j (q t) hspecial.1 hspecial.2
    (hqinterior t ht0 ht1) hj
  have hstrict := hqmargin t ht0 ht1
  have hknotb : k ≠ E.b := by
    intro hk
    rcases hkj with hkj | hkj
    · have hjval : j = E.b := hkj.symm.trans hk
      exact hspecial.2 hjval
    · have hjval : j = E.b - 1 := by
        calc
          j = (j + 1) - 1 := by simp
          _ = E.b - 1 := by rw [hkj.symm.trans hk]
      exact hspecial.1 hjval
  have hknotsides : k ≠ E.b - 1 ∧ k ≠ E.b + 1 := by
    constructor
    · intro hk
      have hzero : E.height (p.vertex k) = 0 := by
        simpa [hk] using E.height_prev
      have hnonneg : 0 ≤ E.height P := by
        rw [hheightd]
        exact hcoord_nonneg 1
      linarith
    · intro hk
      have hzero : E.height (p.vertex k) = 0 := by
        simpa [hk] using E.height_next
      have hnonneg : 0 ≤ E.height P := by
        rw [hheightd]
        exact hcoord_nonneg 1
      linarith
  have hkS : k ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨hknotsides.1, hknotb, hknotsides.2, by simpa [Δ] using hkΔ⟩
  have hmax := hdmax k hkS
  linarith

private theorem hPdecomp :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (E : P3650T1ExposedCorner p),
              ∀ (d : Fin (n + (3 : ℕ))),
                ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
                  A 0 = p.vertex (E.b - 1) →
                    A 1 = p.vertex E.b →
                      A 2 = p.vertex (E.b + 1) →
                        let B := p.vertex E.b
                        let P := p.vertex d
                        P =
                          B + A.coord 0 P • (p.vertex (E.b - 1) - B) +
                            A.coord 2 P • (p.vertex (E.b + 1) - B)
    ) := by
  classical
  intro n p E d A hA0 hA1 hA2 B P
  have hcomb := A.linear_combination_coord_eq_self P
  rw [Fin.sum_univ_three, hA0, hA1, hA2] at hcomb
  have hsumP : A.coord 0 P + A.coord 1 P + A.coord 2 P = 1 := by
    simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one P
  have hcoord1P : A.coord 1 P = 1 - A.coord 0 P - A.coord 2 P := by
    linarith [hsumP]
  apply Prod.ext
  · have hxcomb := congrArg Prod.fst hcomb
    change A.coord 0 P * (p.vertex (E.b - 1)).1 +
        A.coord 1 P * B.1 + A.coord 2 P * (p.vertex (E.b + 1)).1 = P.1 at hxcomb
    calc
      P.1 = A.coord 0 P * (p.vertex (E.b - 1)).1 +
          A.coord 1 P * B.1 + A.coord 2 P * (p.vertex (E.b + 1)).1 := by
        exact hxcomb.symm
      _ = B.1 + A.coord 0 P * ((p.vertex (E.b - 1)).1 - B.1) +
          A.coord 2 P * ((p.vertex (E.b + 1)).1 - B.1) := by
        linear_combination B.1 * hsumP
  · have hycomb := congrArg Prod.snd hcomb
    change A.coord 0 P * (p.vertex (E.b - 1)).2 +
        A.coord 1 P * B.2 + A.coord 2 P * (p.vertex (E.b + 1)).2 = P.2 at hycomb
    calc
      P.2 = A.coord 0 P * (p.vertex (E.b - 1)).2 +
          A.coord 1 P * B.2 + A.coord 2 P * (p.vertex (E.b + 1)).2 := by
        exact hycomb.symm
      _ = B.2 + A.coord 0 P * ((p.vertex (E.b - 1)).2 - B.2) +
          A.coord 2 P * ((p.vertex (E.b + 1)).2 - B.2) := by
        linear_combination B.2 * hsumP

private theorem ht₀ball :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        ∀ (r : ℝ), ∀ (u : ℝ), ∀ (v : ℝ), (Set.Ioo u v ⊆ q ⁻¹' Metric.ball B r) → ((u < (0 : ℝ)) →
            (∀ (t₀ : ℝ), ((0 : ℝ) < t₀) → ((t₀ < min v (1 : ℝ)) → (q t₀ ∈ Metric.ball B r)))) )
            := by
  classical
  intro n p E d B P q r u v hsub huv t₀ ht₀ ht₀min
  apply hsub
  exact ⟨by linarith [huv], lt_of_lt_of_le ht₀min (min_le_left _ _)⟩

private theorem hqdecomp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (P = B + A.coord 0 P • (p.vertex (E.b - 1) - B) + A.coord 2 P • (p.vertex (E.b + 1) - B))
            → (∀ (t₀ : ℝ), q t₀ = B + (t₀ * A.coord 0 P) • (p.vertex (E.b - 1) - B) + (t₀ *
            A.coord 2 P) • (p.vertex (E.b + 1) - B)) ) := by
  classical
  intro n p E d A B P q hPdecomp t₀
  rw [show q t₀ = B + t₀ • (P - B) by
    apply Prod.ext <;> simp [q, AffineMap.lineMap_apply_ring, smul_eq_mul] <;> ring]
  have hvec : P - B =
      A.coord 0 P • (p.vertex (E.b - 1) - B) +
      A.coord 2 P • (p.vertex (E.b + 1) - B) := by
    calc
      P - B = (B + A.coord 0 P • (p.vertex (E.b - 1) - B) +
          A.coord 2 P • (p.vertex (E.b + 1) - B)) - B :=
            congrArg (fun x : Real × Real => x - B) hPdecomp
      _ = A.coord 0 P • (p.vertex (E.b - 1) - B) +
          A.coord 2 P • (p.vertex (E.b + 1) - B) := by abel
  rw [hvec]
  module

private theorem hodd0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (0 < A.coord 0
            (p.vertex d)) → ((0 < A.coord 2 (p.vertex d)) → (
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        ∀ (r : ℝ), (∀ x ∈ Metric.ball (p.vertex E.b) r, x ∈ P3544T1RayParity p ↔ ∃ (s : ℝ) (t :
            ℝ), (0 : ℝ) < s ∧ (0 : ℝ) < t ∧ x = p.vertex E.b + s • (p.vertex (E.b - (1 : Fin (n +
            (3 : ℕ)))) - p.vertex E.b) + t • (p.vertex (E.b + (1 : Fin (n + (3 : ℕ)))) - p.vertex
            E.b)) → (∀ (t₀ : ℝ), ((0 : ℝ) < t₀) → ((q t₀ ∈ Metric.ball B r) → ((q t₀ = B + (t₀ *
            A.coord 0 P) • (p.vertex (E.b - 1) - B) + (t₀ * A.coord 2 P) • (p.vertex (E.b + 1) -
            B)) → (q t₀ ∈ P3544T1RayParity p)))))) ) := by
  classical
  intro n p E d A hcoord0 hcoord2 B P q r hcone t₀ ht₀ ht₀ball hqdecomp
  apply (hcone (q t₀) ht₀ball).2
  refine ⟨t₀ * A.coord 0 P, t₀ * A.coord 2 P,
    mul_pos ht₀ hcoord0, mul_pos ht₀ hcoord2, ?_⟩
  simpa only [B, P] using hqdecomp

private theorem hUopen :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (Continuous q) → ((IsOpen (P3544T1RayParity p)) → (
        let I : Set Real := Set.Ioo 0 1
        let U : Set Real := I ∩ q ⁻¹' P3544T1RayParity p
        IsOpen U)) ) := by
  classical
  intro n p E d B P q hqcont hO I U
  change IsOpen (I ∩ q ⁻¹' P3544T1RayParity p)
  exact isOpen_Ioo.inter (hO.preimage hqcont)

private theorem hVopen :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        (∀ t, 0 < t → t < 1 → q t ∉ P3544T1BoundaryCarrier p) → ((Continuous q) → ((∀ x ∉
            P3544T1BoundaryCarrier p, ∃ (r : ℝ), (0 : ℝ) < r ∧ (Metric.ball x r ⊆
            P3544T1RayParity p ∨ Disjoint (Metric.ball x r) (P3544T1RayParity p))) → (
        let I : Set Real := Set.Ioo 0 1
        let V : Set Real := I ∩ (q ⁻¹' P3544T1RayParity p)ᶜ
        IsOpen V))) ) := by
  classical
  intro n p E d B P q hqclear hqcont hballs I V
  apply isOpen_iff_forall_mem_open.mpr
  intro t ht
  rcases ht with ⟨htI, htO⟩
  obtain ⟨ρ, hρ, hballO | hdisj⟩ :=
    hballs (q t) (hqclear t htI.1 htI.2)
  · have hqtball : q t ∈ Metric.ball (q t) ρ := Metric.mem_ball_self hρ
    exact (htO (hballO hqtball)).elim
  · let W : Set Real := I ∩ q ⁻¹' Metric.ball (q t) ρ
    refine ⟨W, ?_, ?_, ?_⟩
    · intro s hs
      rcases hs with ⟨hsI, hsball⟩
      exact ⟨hsI, fun hsO => (Set.disjoint_left.mp hdisj hsball hsO).elim⟩
    · change IsOpen (I ∩ q ⁻¹' Metric.ball (q t) ρ)
      exact isOpen_Ioo.inter (Metric.isOpen_ball.preimage hqcont)
    · exact ⟨htI, Metric.mem_ball_self hρ⟩

private theorem hUVdisj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        let I : Set Real := Set.Ioo 0 1
        let U : Set Real := I ∩ q ⁻¹' P3544T1RayParity p
        let V : Set Real := I ∩ (q ⁻¹' P3544T1RayParity p)ᶜ
        Disjoint U V ) := by
  classical
  intro n p E d B P q I U V
  apply Set.disjoint_left.mpr
  intro t htU htV
  exact htV.2 htU.2

private theorem hIcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        let I : Set Real := Set.Ioo 0 1
        let U : Set Real := I ∩ q ⁻¹' P3544T1RayParity p
        let V : Set Real := I ∩ (q ⁻¹' P3544T1RayParity p)ᶜ
        I ⊆ U ∪ V ) := by
  classical
  intro n p E d B P q I U V t ht
  by_cases ho : q t ∈ P3544T1RayParity p
  · exact Or.inl ⟨ht, ho⟩
  · exact Or.inr ⟨ht, ho⟩

private theorem hIodd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        ∀ (t₀ : ℝ), ((0 : ℝ) < t₀) → ((t₀ < 1) → ((q t₀ ∈ P3544T1RayParity p) → (
        let I : Set Real := Set.Ioo 0 1
        let U : Set Real := I ∩ q ⁻¹' P3544T1RayParity p
        let V : Set Real := I ∩ (q ⁻¹' P3544T1RayParity p)ᶜ
        (I ⊆ U ∨ I ⊆ V) → (I ⊆ q ⁻¹' P3544T1RayParity p)))) ) := by
  classical
  intro n p E d B P q t₀ ht₀ ht₀1 hodd0 I U V hIsplit
  rcases hIsplit with hU | hV
  · intro t ht
    exact (hU ht).2
  · exfalso
    have := (hV ⟨ht₀, ht₀1⟩).2
    exact this hodd0

private theorem hodd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))),
        let B := p.vertex E.b
        let P := p.vertex d
        let q : Real → Real × Real := AffineMap.lineMap B P
        let I : Set Real := Set.Ioo 0 1
        (I ⊆ q ⁻¹' P3544T1RayParity p) → (openSegment Real B P ⊆ P3544T1RayParity p) ) := by
  classical
  intro n p E d B P q I hIodd x hx
  rw [openSegment_eq_image_lineMap] at hx
  simp only [Set.mem_image] at hx
  rcases hx with ⟨t, ht, htx⟩
  have htI : t ∈ I := by simpa [I] using ht
  have hqt := hIodd htI
  change q t ∈ P3544T1RayParity p at hqt
  rw [← htx]
  exact hqt

private theorem hnotprevious :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (d :
            Fin (n + (3 : ℕ))), (d ≠ E.b - 1) → (E.b ≠ d + 1) ) := by
  classical
  intro n p E d hdprev heq
  have hdval : d = E.b - 1 := by
    calc
      d = (d + 1) - 1 := by simp
      _ = E.b - 1 := by rw [heq]
  exact hdprev hdval

private theorem hiS :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let Δ := convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
        let S : Finset (Fin (n + 3)) := Finset.univ.filter fun i =>
          i ≠ E.b - 1 ∧ i ≠ E.b ∧ i ≠ E.b + 1 ∧ p.vertex i ∈ Δ
        ∀ (i : Fin (n + (3 : ℕ))), (i ≠ E.b - (1 : Fin (n + (3 : ℕ)))) → ((i ≠ E.b) → ((i ≠ E.b +
            (1 : Fin (n + (3 : ℕ)))) → ((p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))}) → (i ∈ S)))) ) := by
  classical
  intro n p E Δ S i hiprev hib hinext hiΔ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact ⟨hiprev, hib, hinext, by simpa [Δ] using hiΔ⟩

end MaximalHeightGeometry

theorem P3650T1MaximalHeightDiagonal {n : Nat} (p : P3381T1PolygonBoundary n)
    (E : P3650T1ExposedCorner p)
    (hentry : ∀ (j : Fin (n + 3)) (w : Real × Real), j ≠ E.b - 1 → j ≠ E.b →
      w ∈ interior (convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real))) →
      w ∈ segment Real (p.vertex j) (p.vertex (j + 1)) →
      ∃ k, (k = j ∨ k = j + 1) ∧
        p.vertex k ∈ convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
            Set (Real × Real)) ∧ E.height w ≤ E.height (p.vertex k))
    (hnotempty : ¬ (∀ i, p.vertex i ∈ convexHull Real
      ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
        Set (Real × Real)) → i = E.b - 1 ∨ i = E.b ∨ i = E.b + 1)) :
    ∃ D : P3650T1VisibleDiagonal p E, D.a = E.b ∧
      p.vertex D.b ∈ convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real)) ∧
      ∀ i, i ≠ E.b - 1 → i ≠ E.b → i ≠ E.b + 1 →
        p.vertex i ∈ convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
            Set (Real × Real)) → E.height (p.vertex i) ≤ E.height (p.vertex D.b) := by
-- BODY
  classical
  let Δ := convexHull Real
    ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real))
  let S : Finset (Fin (n + 3)) := Finset.univ.filter fun i =>
    i ≠ E.b - 1 ∧ i ≠ E.b ∧ i ≠ E.b + 1 ∧ p.vertex i ∈ Δ
  have hSne := MaximalHeightGeometry.hSne n p E hnotempty
  obtain ⟨d, hdS, hdmax⟩ := Finset.exists_max_image S (fun i => E.height (p.vertex i)) hSne
  have hdmem : d ∈ S := hdS
  have hdprops := (Finset.mem_filter.mp hdmem).2
  have hdΔ : p.vertex d ∈ Δ := hdprops.2.2.2
  have hdprev : d ≠ E.b - 1 := hdprops.1
  have hdb : d ≠ E.b := hdprops.2.1
  have hdnext : d ≠ E.b + 1 := hdprops.2.2.1
  have hbasis := ExposedCornerAffineBasis n p E
  obtain ⟨A, hA, hheight⟩ := hbasis
  have hA0 : A 0 = p.vertex (E.b - 1) := hA 0
  have hA1 : A 1 = p.vertex E.b := hA 1
  have hA2 : A 2 = p.vertex (E.b + 1) := hA 2
  have hrange : Set.range A =
      ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real)) :=
          MaximalHeightGeometry.hrange n p E d hdprops A hA
  have hΔ : Δ = convexHull Real (Set.range A) := by
    rw [hrange]
  have hmem := MaximalHeightGeometry.hmem n p E A hΔ
  have hint := MaximalHeightGeometry.hint n p E A hΔ
  have hcoord_nonneg : ∀ i, 0 ≤ A.coord i (p.vertex d) := (hmem _).mp hdΔ
  have hsum := MaximalHeightGeometry.hsum n p d A
  have hheightd : E.height (p.vertex d) = A.coord 1 (p.vertex d) := by
    rw [hheight]
  have hcoord0 := MaximalHeightGeometry.hcoord0 n p E d hdb hdnext A hA1 hA2 hcoord_nonneg hsum
  have hcoord2 := MaximalHeightGeometry.hcoord2 n p E d hdprev hdb A hA0 hA1 hcoord_nonneg hsum
      hcoord0
  have hheightlt := MaximalHeightGeometry.hheightlt n p E d A hcoord_nonneg hsum hheightd hcoord0
      hcoord2
  let B := p.vertex E.b
  let P := p.vertex d
  let q : Real → Real × Real := AffineMap.lineMap B P
  have hcoordB0 := MaximalHeightGeometry.hcoordB0 n p E A hA1
  have hcoordB1 := MaximalHeightGeometry.hcoordB1 n p E A hA1
  have hcoordB2 := MaximalHeightGeometry.hcoordB2 n p E A hA1
  have hqcoord := MaximalHeightGeometry.hqcoord n p E d A
  have hqheight := MaximalHeightGeometry.hqheight n p E d A hheight hcoordB1 hqcoord
  have hqinterior := MaximalHeightGeometry.hqinterior n p E d A hint hcoord_nonneg hsum hcoord0
      hcoord2 hcoordB0 hcoordB1 hcoordB2 hqcoord
  have hqmargin := (show
      ∀ t, 0 < t → t < 1 → E.height P < E.height (q t)
    from by
      classical
      intro t ht0 ht1
      rw [hqheight]
      have hprod : 0 < (1 - t) * (1 - E.height P) :=
        mul_pos (by linarith) (by linarith [hheightlt])
      nlinarith)
  have hqleft := (show
      ∀ t, 0 < t → t < 1 → q t ∉ segment Real (p.vertex (E.b - 1)) B
    from by
      intro t ht0 ht1 hs
      exact MaximalHeightGeometry.hqleft n p E d A hA0 hcoord2 hcoordB2 hqcoord t ht0 hs)
  have hqright := (show
      ∀ t, 0 < t → t < 1 → q t ∉ segment Real B (p.vertex (E.b + 1))
    from by
      intro t ht0 ht1 hs
      exact MaximalHeightGeometry.hqright n p E d A hA2 hcoord0 hcoordB0 hqcoord t ht0 hs)
  have hqclear := MaximalHeightGeometry.hqclear n p E hentry d hdmax A hcoord_nonneg hheightd
      hqinterior hqmargin hqleft hqright
  have hPdecomp := MaximalHeightGeometry.hPdecomp n p E d A hA0 hA1 hA2
  obtain ⟨r, hr, hcone⟩ := E.cone_odd
  have hqcont : Continuous q :=
    (AffineMap.lineMap (k := Real) B P).continuous_of_finiteDimensional
  have hqzero : q 0 = B := by
    simp [q]
  have hball := Metric.ball_mem_nhds (q 0) hr
  have hqat0 : ContinuousAt q (0 : Real) := hqcont.continuousAt
  have hpre := hqat0.preimage_mem_nhds hball
  have hcontinuousball := by simpa only [hqzero] using hpre
  obtain ⟨u, v, ⟨huv, hv1⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hcontinuousball
  have hmin : 0 < min v (1 : Real) := lt_min hv1 zero_lt_one
  obtain ⟨t₀, ht₀, ht₀min⟩ := exists_between hmin
  have ht₀1 : t₀ < 1 := lt_of_lt_of_le ht₀min (min_le_right _ _)
  have ht₀ball := MaximalHeightGeometry.ht₀ball n p E d r u v hsub huv t₀ ht₀ ht₀min
  have hqdecomp := MaximalHeightGeometry.hqdecomp n p E d A hPdecomp t₀
  have hodd0 := MaximalHeightGeometry.hodd0 n p E d A hcoord0 hcoord2 r hcone t₀ ht₀ ht₀ball
      hqdecomp
  obtain ⟨_, hO, _, _, hballs, _, _, _, _⟩ := P3544T1LocalParity p
  let I : Set Real := Set.Ioo 0 1
  let U : Set Real := I ∩ q ⁻¹' P3544T1RayParity p
  let V : Set Real := I ∩ (q ⁻¹' P3544T1RayParity p)ᶜ
  have hUopen := MaximalHeightGeometry.hUopen n p E d hqcont hO
  have hVopen := MaximalHeightGeometry.hVopen n p E d hqclear hqcont hballs
  have hUVdisj := MaximalHeightGeometry.hUVdisj n p E d
  have hIcover := MaximalHeightGeometry.hIcover n p E d
  have hIsplit :
      I ⊆ U ∨ I ⊆ V :=
    isPreconnected_Ioo.subset_or_subset hUopen hVopen hUVdisj hIcover
  have hIodd := MaximalHeightGeometry.hIodd n p E d t₀ ht₀ ht₀1 hodd0 hIsplit
  have hodd := MaximalHeightGeometry.hodd n p E d hIodd
  have hnotprevious := MaximalHeightGeometry.hnotprevious n p E d hdprev
  refine ⟨{
    a := E.b
    b := d
    distinct := hdb.symm
    not_next := hdnext
    not_previous := hnotprevious
    clear := ?_
    odd := ?_
    route := Or.inr ⟨rfl, hdprev, hdnext, hdΔ⟩
  }, rfl, hdΔ, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hc
    rw [openSegment_eq_image_lineMap] at hx
    simp only [Set.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    exact hqclear t ht.1 ht.2 hc
  · intro x hx
    exact hodd hx
  · intro i hiprev hib hinext hiΔ
    have hiS := MaximalHeightGeometry.hiS n p E i hiprev hib hinext hiΔ
    exact hdmax i hiS

end ApollonianSuperharmonic

end
