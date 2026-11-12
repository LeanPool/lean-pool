/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public import LeanPool.ApollonianSuperharmonic.P3650T1VisibleDiagonal
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity

-- [TABLET NODE: P3650T1EmptyTriangleDiagonal]

/-!
# P3650T1EmptyTriangleDiagonal

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangleDiagonalGeometry

private theorem hdet :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0 ) := by
  classical
  intro n p E a b c
  simpa [P3381T1TriangleDeterminant, a, b, c] using E.nondegenerate

private theorem hind :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) → (AffineIndependent Real v)
            ) := by
  classical
  intro n p E a b c v hdet
  apply (affineIndependent_iff_of_fintype Real v).mpr
  intro z hz hsum i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hz] at hsum
  have hz' : z 0 + z 1 + z 2 = 0 := by
    simpa [Fin.sum_univ_succ, ← add_assoc] using hz
  have hx : z 0 * a.1 + z 1 * b.1 + z 2 * c.1 = 0 := by
    simpa [Fin.sum_univ_succ, v, ← add_assoc] using congrArg Prod.fst hsum
  have hy : z 0 * a.2 + z 1 * b.2 + z 2 * c.2 = 0 := by
    simpa [Fin.sum_univ_succ, v, ← add_assoc] using congrArg Prod.snd hsum
  have hx' : z 1 * (b.1 - a.1) + z 2 * (c.1 - a.1) = 0 := by
    linear_combination hx - a.1 * hz'
  have hy' : z 1 * (b.2 - a.2) + z 2 * (c.2 - a.2) = 0 := by
    linear_combination hy - a.2 * hz'
  have hz1 : z 1 = 0 := by
    have hz1mul : z 1 * ((b.1 - a.1) * (c.2 - a.2) -
        (c.1 - a.1) * (b.2 - a.2)) = 0 := by
      linear_combination (c.2 - a.2) * hx' - (c.1 - a.1) * hy'
    exact (mul_eq_zero.mp hz1mul).resolve_right hdet
  have hz2 : z 2 = 0 := by
    have hz2mul : z 2 * ((b.1 - a.1) * (c.2 - a.2) -
        (c.1 - a.1) * (b.2 - a.2)) = 0 := by
      linear_combination (b.1 - a.1) * hy' - (b.2 - a.2) * hx'
    exact (mul_eq_zero.mp hz2mul).resolve_right hdet
  fin_cases i <;> simp_all

private theorem hspan :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        (AffineIndependent Real v) → (affineSpan Real (Set.range v) = ⊤) ) := by
  classical
  intro n p E a b c v hind
  apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Module.finrank_prod]

private theorem hheight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        E.height = A.coord 1 ) := by
  classical
  intro n p E a b c v hind hspan A
  apply AffineMap.ext_on A.tot
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp only [AffineBasis.coord_apply]
  · exact E.height_prev
  · exact E.height_top
  · exact E.height_next

private theorem hrangeAt179 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        Set.range A = ({a, b, c} : Set (Real × Real)) ) := by
  classical
  intro n p E a b c v hind hspan A
  rw [show (A : Fin 3 → Real × Real) = ![a, b, c] from funext (by
    intro i
    fin_cases i <;> rfl)]
  ext x
  simp; tauto

private theorem hmemAt186 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (Set.range A = ({a, b, c} : Set (Real × Real))) → (∀ x, x ∈ T ↔ ∀ i, 0 ≤ A.coord i x) )
            := by
  classical
  intro n p E a b c v hind hspan A T hrange x
  exact Set.ext_iff.mp (by simpa [T, hrange] using A.convexHull_eq_nonneg_coord) x

private theorem hint :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (Set.range A = ({a, b, c} : Set (Real × Real))) → (∀ x, x ∈ interior T ↔ ∀ i, 0 < A.coord
            i x) ) := by
  classical
  intro n p E a b c v hind hspan A T hrange x
  exact Set.ext_iff.mp (by simpa [T, hrange] using A.interior_convexHull) x

private theorem hbase :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (convexHull Real ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real ×
            Real))) = T ) := by
  classical
  intro n p E a b c T
  rfl

private theorem hvertexSide :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n
            + (3 : ℕ))), p.vertex j ∈ segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 :
            ℕ))))) ↔ j = i ∨ j = i + (1 : Fin (n + (3 : ℕ))) ) := by
  classical
  intro n p i j
  constructor
  · intro hj
    by_cases hji : j = i
    · exact Or.inl hji
    · have hmem : p.vertex j ∈
          segment Real (p.vertex i) (p.vertex (i + 1)) ∩
            segment Real (p.vertex j) (p.vertex (j + 1)) :=
        ⟨hj, left_mem_segment Real _ _⟩
      rw [p.edge_intersection i j (Ne.symm hji)] at hmem
      rcases hmem.1 with hl | hr
      · exact Or.inl (p.injective hl)
      · exact Or.inr (p.injective hr)
  · rintro (rfl | rfl)
    · exact left_mem_segment Real _ _
    · exact right_mem_segment Real _ _

private theorem hleftFace :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        ∀ x ∈ T, x ∈ segment ℝ a b → (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ) := by
  classical
  intro n p E a b c v hind hspan A T x hx hxs
  have h2a : A.coord 2 a = 0 := by
    change A.coord 2 (A 0) = 0
    exact A.coord_apply_ne (by decide)
  have h2b : A.coord 2 b = 0 := by
    change A.coord 2 (A 1) = 0
    exact A.coord_apply_ne (by decide)
  rw [segment_eq_image_lineMap] at hxs
  obtain ⟨t, ht, rfl⟩ := hxs
  rw [(A.coord 2).apply_lineMap]
  simp only [AffineMap.lineMap_apply_ring,
    ]
  rw [h2a, h2b]
  ring

private theorem hrightFace :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        ∀ x ∈ T, x ∈ segment ℝ b c → (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ) := by
  classical
  intro n p E a b c v hind hspan A T x hx hxs
  have h0b : A.coord 0 b = 0 := by
    change A.coord 0 (A 1) = 0
    exact A.coord_apply_ne (by decide)
  have h0c : A.coord 0 c = 0 := by
    change A.coord 0 (A 2) = 0
    exact A.coord_apply_ne (by decide)
  rw [segment_eq_image_lineMap] at hxs
  obtain ⟨t, ht, rfl⟩ := hxs
  rw [(A.coord 0).apply_lineMap]
  simp only [AffineMap.lineMap_apply_ring,
    ]
  rw [h0b, h0c]
  ring

private theorem hcoordLine :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (i : Fin (3 : ℕ)), ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (s : ℝ), (A.coord i : ℝ × ℝ → ℝ)
            ((AffineMap.lineMap x y : ℝ → ℝ × ℝ) s) = ((1 : ℝ) - s) * (A.coord i : ℝ × ℝ → ℝ) x +
            s * (A.coord i : ℝ × ℝ → ℝ) y ) := by
  classical
  intro n p E a b c v hind hspan A i x y s
  rw [(A.coord i).apply_lineMap, AffineMap.lineMap_apply_ring]

private theorem hacOuter :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) → (a ≠ c) ) := by
  classical
  intro n p E a b c hdet heq
  have hzeroDet : (b.1 - a.1) * (c.2 - a.2) -
      (c.1 - a.1) * (b.2 - a.2) = 0 := by rw [heq]; ring
  exact hdet hzeroDet

private theorem habdist :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let c := p.vertex (E.b + 1)
        (a ≠ c) → (E.b - 1 ≠ E.b + 1) ) := by
  classical
  intro n p E a c hacOuter heq
  have hv : p.vertex (E.b - 1) = p.vertex (E.b + 1) := congrArg p.vertex heq
  exact hacOuter hv

private theorem hbcOuter :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
            p.vertex E.b ≠ p.vertex (E.b + 1) ) := by
  classical
  intro n p E heq
  have hh := congrArg E.height heq
  rw [E.height_top, E.height_next] at hh
  norm_num at hh

private theorem habNext :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), E.b +
            1 ≠ (E.b - 1) + 1 ) := by
  classical
  intro n p E heq
  have hv := congrArg p.vertex heq
  have hidx : (E.b - 1) + 1 = E.b := sub_add_cancel _ _
  rw [hidx] at hv
  have hh := congrArg E.height hv
  rw [E.height_next, E.height_top] at hh
  norm_num at hh

private theorem hcaNext :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ((0 : ℕ) < n) → (∀ (E :
            P3650T1ExposedCorner p), E.b - 1 ≠ (E.b + 1) + 1) ) := by
  classical
  intro n p hn E heq
  have hneg' := congrArg (fun k : Fin (n + 3) => k - E.b) heq
  have hneg : (-1 : Fin (n + 3)) = 1 + 1 := by
    calc
      -1 = (E.b - 1) - E.b := by abel
      _ = (E.b + 1 + 1) - E.b := hneg'
      _ = 1 + 1 := by abel
  have hval1 : (1 : Fin (n + 3)).val = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n + 3)]
  have hval2 : (2 : Fin (n + 3)).val = 2 := by
    simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
  have htwo : (2 : Fin (n + 3)) = 1 + 1 := by
    apply Fin.ext
    have hlt : (1 : Fin (n + 3)).val + (1 : Fin (n + 3)).val < n + 3 := by
      rw [hval1]
      omega
    rw [Fin.val_add_eq_of_add_lt hlt, hval1, hval2]
  have hthree : (3 : Fin (n + 3)) = 0 := by
    calc
      (3 : Fin (n + 3)) = (2 : Fin (n + 3)) + 1 := by
        apply Fin.ext
        have hlt : (2 : Fin (n + 3)).val + (1 : Fin (n + 3)).val < n + 3 := by
          rw [hval2, hval1]
          omega
        rw [Fin.val_add_eq_of_add_lt hlt, hval2, hval1]
        norm_num [Nat.mod_eq_of_lt (by omega : 3 < n + 3),
          Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
      _ = (1 + 1 : Fin (n + 3)) + 1 := by rw [htwo]
      _ = (-1 : Fin (n + 3)) + 1 := by rw [← hneg]
      _ = 0 := by simp
  have hv := congrArg Fin.val hthree
  have hval : (3 : Fin (n + 3)).val = 3 := by
    simp [Nat.mod_eq_of_lt (by omega : 3 < n + 3)]
  rw [hval] at hv
  norm_num at hv

private theorem hintAvoid :
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
            × ℝ → ℝ) (p.vertex k)) → ((∀ (i : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ :
            Set (ℝ × ℝ) → Set (ℝ × ℝ)) {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (∀ x, x ∈ interior T ↔ ∀ i, 0 < A.coord i x) → ((∀ (x : Real × Real), E.height x =
            A.coord 1 x) → ((∀ (x : Real × Real), (x ∈ T) → ((x ∈ segment Real a b) → (A.coord 2
            x = 0))) → ((∀ (x : Real × Real), (x ∈ T) → ((x ∈ segment Real b c) → (A.coord 0 x =
            0))) → (interior T ∩ P3544T1BoundaryCarrier p = ∅)))))) ) := by
  classical
  intro n p E hentry hempty a b c v hind hspan A T hint hheightcoord hleftFace hrightFace
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hxi, hxC⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
  by_cases hja : j = E.b - 1
  · subst j
    have hxface := hleftFace x (interior_subset hxi) (by simpa [a, b] using hj)
    have := (hint x).mp hxi 2
    linarith
  by_cases hjb : j = E.b
  · subst j
    have hxface := hrightFace x (interior_subset hxi) (by simpa [b, c] using hj)
    have := (hint x).mp hxi 0
    linarith
  obtain ⟨k, hkor, hkT, hle⟩ := hentry j x hja hjb hxi hj
  have hkheight : 0 < E.height (p.vertex k) := by
    have : 0 < E.height x := by
      rw [hheightcoord]
      exact (hint x).mp hxi 1
    exact lt_of_lt_of_le this hle
  obtain hka | hkb | hkc := hempty k hkT
  · rw [hka, E.height_prev] at hkheight
    norm_num at hkheight
  · have hkB : k = E.b := hkb
    rcases hkor with hkj | hkj
    · have hjB : j = E.b := hkj.symm.trans hkB
      exact hjb hjB
    · have hjplus : j + 1 = E.b := hkj.symm.trans hkB
      have hjprev : j = E.b - 1 := by
        apply Fin.ext
        by_cases hb0 : E.b.val = 0
        · have hbeq : E.b = 0 := Fin.ext hb0
          rw [hbeq] at hjplus ⊢
          have hjlast : j = Fin.last (n + 2) := by
            apply Fin.ext
            have hjv := congrArg Fin.val hjplus
            by_cases hjlt : j.val + 1 < n + 3
            · have hadd : (j + 1).val = j.val + 1 :=
                Fin.val_add_eq_of_add_lt (by simpa using hjlt)
              rw [hadd] at hjv
              simp at hjv
            · have hjval' : j.val + 1 = n + 3 := by omega
              simp [Fin.val_last]
              omega
          rw [hjlast]
          simp []
        · have hbne : E.b ≠ 0 := fun h => hb0 (congrArg Fin.val h)
          have hjval := congrArg Fin.val hjplus
          have hsub := Fin.val_sub_one_of_ne_zero hbne
          by_cases hjwrap : j.val + 1 = n + 3
          · have hjadd : (j + 1).val = 0 := by
              rw [Fin.val_add_eq_ite]
              simp [hjwrap]
            rw [hjadd] at hjval
            omega
          · have hjlt : j.val + 1 < n + 3 := by omega
            have hjadd : (j + 1).val = j.val + 1 :=
              Fin.val_add_eq_of_add_lt (by simpa using hjlt)
            rw [hjadd] at hjval
            rw [hsub]
            omega
      exact hja hjprev
  · rw [hkc, E.height_next] at hkheight
    norm_num at hkheight

private theorem hcoordA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0 ) := by
  classical
  intro n p E a b c v hind hspan A
  constructor
  · change A.coord 0 (A 0) = 1
    exact A.coord_apply_eq 0
  constructor
  · change A.coord 1 (A 0) = 0
    exact A.coord_apply_ne (by decide)
  · change A.coord 2 (A 0) = 0
    exact A.coord_apply_ne (by decide)

private theorem hcoordB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        A.coord 0 b = 0 ∧ A.coord 1 b = 1 ∧ A.coord 2 b = 0 ) := by
  classical
  intro n p E a b c v hind hspan A
  constructor
  · change A.coord 0 (A 1) = 0
    exact A.coord_apply_ne (by decide)
  constructor
  · change A.coord 1 (A 1) = 1
    exact A.coord_apply_eq 1
  · change A.coord 2 (A 1) = 0
    exact A.coord_apply_ne (by decide)

private theorem hcoordC :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1 ) := by
  classical
  intro n p E a b c v hind hspan A
  constructor
  · change A.coord 0 (A 2) = 0
    exact A.coord_apply_ne (by decide)
  constructor
  · change A.coord 1 (A 2) = 0
    exact A.coord_apply_ne (by decide)
  · change A.coord 2 (A 2) = 1
    exact A.coord_apply_eq 2

private theorem hopenBaseCoords :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c =
            0 ∧ A.coord 2 c = 1) → (∀ x, x ∈ openSegment Real a c → 0 < A.coord 0 x ∧ A.coord 1 x
            = 0 ∧ 0 < A.coord 2 x)) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordA hcoordC x hx
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have h0 : A.coord 0 (AffineMap.lineMap a c t) = 1 - t := by
    rw [(A.coord 0).apply_lineMap]
    rw [AffineMap.lineMap_apply_ring, hcoordA.1, hcoordC.1]
    ring
  have h1 : A.coord 1 (AffineMap.lineMap a c t) = 0 := by
    rw [(A.coord 1).apply_lineMap]
    rw [AffineMap.lineMap_apply_ring, hcoordA.2.1, hcoordC.2.1]
    ring
  have h2 : A.coord 2 (AffineMap.lineMap a c t) = t := by
    rw [(A.coord 2).apply_lineMap]
    rw [AffineMap.lineMap_apply_ring, hcoordA.2.2, hcoordC.2.2]
    ring
  rw [h0, h1, h2]
  exact ⟨sub_pos.mpr ht.2, rfl, ht.1⟩

private theorem hline :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (s : Real), A.coord i
            (AffineMap.lineMap x y s) = (1 - s) * A.coord i x + s * A.coord i y) → (∀ (j : Fin (n
            + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (i : Fin (3 : ℕ)), ∀ (s : ℝ), (A.coord i : ℝ × ℝ → ℝ) (q s) = ((1 : ℝ) - s) * (A.coord
            i : ℝ × ℝ → ℝ) (p.vertex j) + s * (A.coord i : ℝ × ℝ → ℝ) (p.vertex (j + (1 : Fin (n
            + (3 : ℕ)))))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordLine j q i s
  exact hcoordLine i (p.vertex j) (p.vertex (j + 1)) s

private theorem hnotLeft :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 b = 0 ∧ A.coord 1 b =
            1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (∀ (x
            : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → ((x ∈ T) → ((¬j = E.b - (1 : Fin (n + (3 : ℕ)))) →
            ((¬j = E.b) → (∀ (t : ℝ), ((AffineMap.lineMap (p.vertex j) (p.vertex (j + (1 : Fin (n
            + (3 : ℕ))))) : ℝ → ℝ × ℝ) t = x) → (
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → ((Continuous q) → ((∀ (i : Fin 3), Continuous (fun s => A.coord i (q s))) →
            ((∀ (i : Fin 3), ∀ (s : Real), A.coord i (q s) = (1 - s) * A.coord i (p.vertex j) + s
            * A.coord i (p.vertex (j + 1))) → (x ≠ p.vertex j))))))))))))) ) := by
  classical
  intro n p E hempty a b c v hind hspan A T hcoordA hcoordB hcoordC x j hxb hxT hja hjb t hqt q
      hqtq hqcont hfc hline h
  have hjT : p.vertex j ∈ T := by rw [← h]; exact hxT
  obtain hja' | hjb' | hjc' := hempty j (by simpa [T, a, b, c] using hjT)
  · subst j
    have heq := congrArg (A.coord 2) h
    rw [hcoordA.2.2] at heq
    linarith [hxb.2.2]
  · subst j
    have heq := congrArg (A.coord 1) h
    rw [hcoordB.2.1] at heq
    linarith [hxb.2.1]
  · subst j
    have heq := congrArg (A.coord 0) h
    rw [hcoordC.1] at heq
    linarith [hxb.1]

private theorem hnotRight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 b = 0 ∧ A.coord 1 b =
            1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (∀ (x
            : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → ((x ∈ T) → (x ≠ p.vertex (j + 1))))))) ) := by
  classical
  intro n p E hempty a b c v hind hspan A T hcoordA hcoordB hcoordC x j hxb hxT h
  have hjT : p.vertex (j + 1) ∈ T := by rw [← h]; exact hxT
  obtain hja' | hjb' | hjc' := hempty (j + 1) (by simpa [T, a, b, c] using hjT)
  · rw [hja'] at h
    have heq := congrArg (A.coord 2) h
    rw [hcoordA.2.2] at heq
    linarith [hxb.2.2]
  · rw [hjb'] at h
    have heq := congrArg (A.coord 1) h
    rw [hcoordB.2.1] at heq
    linarith [hxb.2.1]
  · rw [hjc'] at h
    have heq := congrArg (A.coord 0) h
    rw [hcoordC.1] at heq
    linarith [hxb.1]

private theorem ht' :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 :
            ℕ))), ∀ (t : ℝ), (t ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → ((x ≠ p.vertex j) → ((x ≠ p.vertex (j + 1)) → (t ∈ Set.Ioo (0 : Real) 1)))) )
            := by
  classical
  intro n p x j t ht q hqtq hnotLeft hnotRight
  constructor
  · by_contra hnot
    have : t = 0 := le_antisymm (not_lt.mp hnot) ht.1
    have hq0 : q 0 = p.vertex j := by simp [q]
    exact hnotLeft (hqtq.symm.trans (by rw [this]; exact hq0))
  · by_contra hnot
    have : t = 1 := le_antisymm ht.2 (not_lt.mp hnot)
    have hq1 : q 1 = p.vertex (j + 1) := by simp [q]
    exact hnotRight (hqtq.symm.trans (by rw [this]; exact hq1))

private theorem hzero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → (∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → ((∀ (i : Fin 3), ∀ (s : Real), A.coord i (q s) = (1 - s) * A.coord i
            (p.vertex j) + s * A.coord i (p.vertex (j + 1))) → ((1 - t) * A.coord 1 (p.vertex j)
            + t * A.coord 1 (p.vertex (j + 1)) = 0))) ) := by
  classical
  intro n p E a b c v hind hspan A x j hxb t q hqtq hline
  calc
    _ = A.coord 1 (q t) := (hline 1 t).symm
    _ = A.coord 1 x := congrArg (A.coord 1) hqtq
    _ = 0 := hxb.2.1

private theorem hqt0At504 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → (∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → (0 < A.coord 0 (q t))) ) := by
  classical
  intro n p E a b c v hind hspan A x j hxb t q hqtq
  calc
     _ = A.coord 0 x := congrArg _ hqtq
     _ > 0 := hxb.1

private theorem hqt2At507 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → (∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → (0 < A.coord 2 (q t))) ) := by
  classical
  intro n p E a b c v hind hspan A x j hxb t q hqtq
  calc
     _ = A.coord 2 x := congrArg _ hqtq
     _ > 0 := hxb.2.2

private theorem hq1At528 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin 3 → Real × Real), ∀ (hind :
            AffineIndependent
            Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), ∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (∀ (i : Fin 3), ∀ (s : Real), A.coord i (q s) = (1 - s) * A.coord i (p.vertex j) + s *
            A.coord i (p.vertex (j + 1))) → ((t ∈ Set.Ioo (0 : Real) 1) → (((1 - t) * A.coord 1
            (p.vertex j) + t * A.coord 1 (p.vertex (j + 1)) = 0) → (((0 : ℝ) < (A.coord (1 : Fin
            (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex j)) → (∀ (s : ℝ), (s < t) → (0 < A.coord 1 (q s))))))
            ) := by
  classical
  intro n p v hind hspan A j t q hline ht' hzero hposj s hst
  have hlineS := hline 1 s
  have : A.coord 1 (q s) =
      ((t - s) / t) * A.coord 1 (p.vertex j) := by
    rw [hlineS]
    have htne : t ≠ 0 := ne_of_gt ht'.1
    have hβ : A.coord 1 (p.vertex (j + 1)) =
        -((1 - t) / t) * A.coord 1 (p.vertex j) := by
      field_simp [htne]
      nlinarith [hzero]
    rw [hβ]
    field_simp [htne]
    ring
  rw [this]
  exact mul_pos (div_pos (sub_pos.mpr hst) ht'.1) hposj

private theorem hqsegAt546 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s : ℝ), (s ∈ Set.Ioo (0 : Real) 1) → (q s ∈ segment Real (p.vertex j) (p.vertex (j +
            1))) ) := by
  classical
  intro n p j q s hs01
  rw [segment_eq_image_lineMap]
  exact ⟨s, ⟨le_of_lt hs01.1, le_of_lt hs01.2⟩, rfl⟩

private theorem hfalseAt549 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (interior T ∩ P3544T1BoundaryCarrier p = ∅) → (∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s : ℝ), (q s ∈ interior T) → ((q s ∈ segment Real (p.vertex j) (p.vertex (j + 1))) →
            (q s ∈ (∅ : Set (Real × Real))))) ) := by
  classical
  intro n p E a b c T hintAvoid j q s hqint hqseg
  rw [← hintAvoid]
  exact ⟨hqint, Set.mem_iUnion.mpr ⟨j, hqseg⟩⟩

private theorem hq1At579 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (v : Fin 3 → Real × Real), ∀ (hind :
            AffineIndependent
            Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), ∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (∀ (i : Fin 3), ∀ (s : Real), A.coord i (q s) = (1 - s) * A.coord i (p.vertex j) + s *
            A.coord i (p.vertex (j + 1))) → ((t ∈ Set.Ioo (0 : Real) 1) → (((1 - t) * A.coord 1
            (p.vertex j) + t * A.coord 1 (p.vertex (j + 1)) = 0) → (((0 : ℝ) < (A.coord (1 : Fin
            (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) → (∀ (s : ℝ), (t < s)
            → (0 < A.coord 1 (q s)))))) ) := by
  classical
  intro n p v hind hspan A j t q hline ht' hzero hposnext s hts
  have hlineS := hline 1 s
  have : A.coord 1 (q s) =
      ((s - t) / (1 - t)) * A.coord 1 (p.vertex (j + 1)) := by
    rw [hlineS]
    have htne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht'.2)
    have hα : A.coord 1 (p.vertex j) =
        -(t / (1 - t)) * A.coord 1 (p.vertex (j + 1)) := by
      field_simp [htne]
      nlinarith [hzero]
    rw [hα]
    field_simp [htne]
    ring
  rw [this]
  exact mul_pos (div_pos (sub_pos.mpr hts) (sub_pos.mpr ht'.2)) hposnext

private theorem hα0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), ∀ (t : ℝ), (t ∈ Set.Ioo (0 : Real) 1) → (((1 - t) * A.coord 1
            (p.vertex j) + t * A.coord 1 (p.vertex (j + 1)) = 0) → (((1 - t) * A.coord 1
            (p.vertex j) ≤ 0) → ((t * A.coord 1 (p.vertex (j + 1)) ≤ 0) → (A.coord 1 (p.vertex j)
            = 0)))) ) := by
  classical
  intro n p E a b c v hind hspan A j t ht' hzero hleftTerm hrightTerm
  have hmul : (1 - t) * A.coord 1 (p.vertex j) = 0 := by linarith [hzero, hrightTerm]
  rcases mul_eq_zero.mp hmul with htone | hαzero
  · exact (False.elim ((ne_of_gt (sub_pos.mpr ht'.2)) htone))
  · exact hαzero

private theorem hβ0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), ∀ (t : ℝ), (t ∈ Set.Ioo (0 : Real) 1) → (((1 - t) * A.coord 1
            (p.vertex j) + t * A.coord 1 (p.vertex (j + 1)) = 0) → (((1 - t) * A.coord 1
            (p.vertex j) ≤ 0) → ((t * A.coord 1 (p.vertex (j + 1)) ≤ 0) → (A.coord 1 (p.vertex (j
            + 1)) = 0)))) ) := by
  classical
  intro n p E a b c v hind hspan A j t ht' hzero hleftTerm hrightTerm
  have hmul : t * A.coord 1 (p.vertex (j + 1)) = 0 := by linarith [hzero, hleftTerm]
  rcases mul_eq_zero.mp hmul with htzero | hβzero
  · exact (False.elim ((ne_of_gt ht'.1) htzero))
  · exact hβzero

private theorem hline1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (∀ (i : Fin 3), ∀ (s : Real), A.coord i (q s) = (1 - s) * A.coord i (p.vertex j) + s *
            A.coord i (p.vertex (j + 1))) → ((A.coord 1 (p.vertex j) = 0) → ((A.coord 1 (p.vertex
            (j + 1)) = 0) → (∀ (s : ℝ), (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q s) = (0 :
            ℝ)))) ) := by
  classical
  intro n p E a b c v hind hspan A j q hline hα0 hβ0 s
  rw [hline 1 s, hα0, hβ0]
  ring

private theorem hzt :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ∀ (t : ℝ),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        (q t = x) → (
        let z0 := A.coord 2 (p.vertex j)
        let z1 := A.coord 2 (p.vertex (j + 1))
        (∀ (s : Real), A.coord 2 (q s) = (1 - s) * z0 + s * z1) → ((1 - t) * z0 + t * z1 =
            A.coord 2 x)) ) := by
  classical
  intro n p E a b c v hind hspan A x j t q hqtq z0 z1 hline2
  calc
    _ = A.coord 2 (q t) := (hline2 t).symm
    _ = A.coord 2 x := congrArg (A.coord 2) hqtq

private theorem hsum0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), A.coord 0 (p.vertex j) + A.coord 1 (p.vertex j) + A.coord 2
            (p.vertex j) = 1 ) := by
  classical
  intro n p E a b c v hind hspan A j
  simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (p.vertex j)

private theorem hsum1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), A.coord 0 (p.vertex (j + 1)) + A.coord 1 (p.vertex (j + 1)) +
            A.coord 2 (p.vertex (j + 1)) = 1 ) := by
  classical
  intro n p E a b c v hind hspan A j
  simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (p.vertex (j + 1))

private theorem hcoord0j :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), (¬(0 : ℝ) < (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex
            j)) → ((A.coord 1 (p.vertex j) = 0) → (
        let z0 := A.coord 2 (p.vertex j)
        (A.coord 0 (p.vertex j) + A.coord 1 (p.vertex j) + A.coord 2 (p.vertex j) = 1) → (A.coord
            0 (p.vertex j) = 1 - z0))) ) := by
  classical
  intro n p E a b c v hind hspan A j hposj hα0 z0 hsum0
  have hh : A.coord 0 (p.vertex j) + z0 = 1 := by
    dsimp [z0] at *
    rw [hα0] at hsum0
    simpa only [add_zero] using hsum0
  linarith

private theorem hcoord01 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))), (¬(0 : ℝ) < (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex
            (j + (1 : Fin (n + (3 : ℕ)))))) → ((A.coord 1 (p.vertex (j + 1)) = 0) → (
        let z1 := A.coord 2 (p.vertex (j + 1))
        (A.coord 0 (p.vertex (j + 1)) + A.coord 1 (p.vertex (j + 1)) + A.coord 2 (p.vertex (j +
            1)) = 1) → (A.coord 0 (p.vertex (j + 1)) = 1 - z1))) ) := by
  classical
  intro n p E a b c v hind hspan A j hposnext hβ0 z1 hsum1
  have hh : A.coord 0 (p.vertex (j + 1)) + z1 = 1 := by
    dsimp [z1] at *
    rw [hβ0] at hsum1
    simpa only [add_zero] using hsum1
  linarith

private theorem hnotIoo0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (∀ x, x ∈ T ↔ ∀ i, 0 ≤ A.coord i x) → ((A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a =
            0) → ((A.coord 0 b = 0 ∧ A.coord 1 b = 1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧
            A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (∀ (j : Fin (n + (3 : ℕ))), (¬(0 : ℝ) < (A.coord
            (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex j)) → ((A.coord 1 (p.vertex j) = 0) → (
        let z0 := A.coord 2 (p.vertex j)
        (A.coord 0 (p.vertex j) = 1 - z0) → (z0 ∉ Set.Ioo (0 : Real) 1)))))))) ) := by
  classical
  intro n p E hempty a b c v hind hspan A T hmem hcoordA hcoordB hcoordC j hposj hα0 z0 hcoord0j hz
  have hjT : p.vertex j ∈ T := (hmem _).mpr (by
    intro i
    fin_cases i
    · change 0 ≤ A.coord 0 (p.vertex j)
      rw [hcoord0j]
      linarith [hz.2]
    · change 0 ≤ A.coord 1 (p.vertex j)
      rw [hα0]
    · change 0 ≤ A.coord 2 (p.vertex j)
      exact le_of_lt hz.1)
  obtain hja' | hjb' | hjc' := hempty j (by simpa [T, a, b, c] using hjT)
  · have hz' : z0 = 0 := by
      simpa [z0, a, hcoordA.2.2] using congrArg (A.coord 2) (congrArg p.vertex hja')
    exact (not_le_of_gt hz.1) (hz'.symm ▸ le_rfl)
  · have : A.coord 1 (p.vertex j) = 1 := by simpa [hjb'] using hcoordB.2.1
    linarith [hα0]
  · have hz' : z0 = 1 := by
      simpa [z0, c, hcoordC.2.2] using congrArg (A.coord 2) (congrArg p.vertex hjc')
    linarith [hz.2]

private theorem hnotIoo1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (∀ x, x ∈ T ↔ ∀ i, 0 ≤ A.coord i x) → ((A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a =
            0) → ((A.coord 0 b = 0 ∧ A.coord 1 b = 1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧
            A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (∀ (j : Fin (n + (3 : ℕ))), (¬(0 : ℝ) < (A.coord
            (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) → ((A.coord
            1 (p.vertex (j + 1)) = 0) → (
        let z1 := A.coord 2 (p.vertex (j + 1))
        (A.coord 0 (p.vertex (j + 1)) = 1 - z1) → (z1 ∉ Set.Ioo (0 : Real) 1)))))))) ) := by
  classical
  intro n p E hempty a b c v hind hspan A T hmem hcoordA hcoordB hcoordC j hposnext hβ0 z1
      hcoord01 hz
  have hjT : p.vertex (j + 1) ∈ T := (hmem _).mpr (by
    intro i
    fin_cases i
    · change 0 ≤ A.coord 0 (p.vertex (j + 1))
      rw [hcoord01]
      linarith [hz.2]
    · change 0 ≤ A.coord 1 (p.vertex (j + 1))
      rw [hβ0]
    · change 0 ≤ A.coord 2 (p.vertex (j + 1))
      exact le_of_lt hz.1)
  obtain hja' | hjb' | hjc' := hempty (j + 1) (by simpa [T, a, b, c] using hjT)
  · have hz' : z1 = 0 := by
      simpa [z1, a, hcoordA.2.2] using
        congrArg (A.coord 2) (congrArg p.vertex hja')
    linarith [hz.1]
  · have : A.coord 1 (p.vertex (j + 1)) = 1 := by simpa [hjb'] using hcoordB.2.1
    linarith [hβ0]
  · have hz' : z1 = 1 := by
      simpa [z1, c, hcoordC.2.2] using
        congrArg (A.coord 2) (congrArg p.vertex hjc')
    exact (not_le_of_gt hz.2) (hz'.symm ▸ le_rfl)

private theorem hz0case :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))),
        let z0 := A.coord 2 (p.vertex j)
        (z0 ∉ Set.Ioo (0 : Real) 1) → (z0 ≤ 0 ∨ 1 ≤ z0) ) := by
  classical
  intro n p E a b c v hind hspan A j z0 hnotIoo0
  by_contra h
  push Not at h
  exact hnotIoo0 ⟨h.1, h.2⟩

private theorem hz1case :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (j : Fin (n + (3 : ℕ))),
        let z1 := A.coord 2 (p.vertex (j + 1))
        (z1 ∉ Set.Ioo (0 : Real) 1) → (z1 ≤ 0 ∨ 1 ≤ z1) ) := by
  classical
  intro n p E a b c v hind hspan A j z1 hnotIoo1
  by_contra h
  push Not at h
  exact hnotIoo1 ⟨h.1, h.2⟩

private theorem hzlt :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x ∧ (A.coord (1 : Fin
            (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ)
            x) → ((A.coord 0 x + A.coord 1 x + A.coord 2 x = 1) → (A.coord 2 x < 1)) ) := by
  classical
  intro n p E a b c v hind hspan A x hxb hxsum
  rw [hxb.2.1] at hxsum
  linarith [hxb.1]

private theorem hstraddle :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        ∀ (x : ℝ × ℝ), ∀ (j : Fin (n + (3 : ℕ))), ((0 : ℝ) < (A.coord (0 : Fin (3 : ℕ)) : ℝ × ℝ →
            ℝ) x ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ) ∧ (0 : ℝ) < (A.coord (2 :
            Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x) → (∀ (t : ℝ), (t ∈ Set.Ioo (0 : Real) 1) → (
        let z0 := A.coord 2 (p.vertex j)
        let z1 := A.coord 2 (p.vertex (j + 1))
        ((1 - t) * z0 + t * z1 = A.coord 2 x) → ((z0 ≤ 0 ∨ 1 ≤ z0) → ((z1 ≤ 0 ∨ 1 ≤ z1) →
            ((A.coord 0 x + A.coord 1 x + A.coord 2 x = 1) → ((z0 ≤ 0 ∧ 1 ≤ z1) ∨ (z1 ≤ 0 ∧ 1 ≤
            z0))))))) ) := by
  classical
  intro n p E a b c v hind hspan A x j hxb t ht' z0 z1 hzt hz0case hz1case hxsum
  rcases hz0case with h0 | h0 <;> rcases hz1case with h1 | h1
  · exfalso
    have hleft : (1 - t) * z0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht'.2.le) h0
    have hright : t * z1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht'.1.le h1
    linarith [hxb.2.2, hleft, hright]
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h1, h0⟩
  · exfalso
    have hleft : 1 - t ≤ (1 - t) * z0 :=
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht'.2.le)
    have hright : t ≤ t * z1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 ht'.1.le
    linarith [hzlt, hzt, hleft, hright]

private theorem hzeroHit :
    (by
      classical
        exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (E : P3650T1ExposedCorner p),
              let a := p.vertex (E.b - 1);
              let b := p.vertex E.b;
              let c := p.vertex (E.b + 1);
              let v : Fin 3 → Real × Real := ![a, b, c];
              ∀ (hind : AffineIndependent Real v),
                ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
                  let A : AffineBasis (Fin 3) Real (Real × Real) :=
                    ⟨v, hind, hspan⟩;
                  ∀ (j : Fin (n + (3 : ℕ))),
                    let q : Real → Real × Real :=
                      AffineMap.lineMap (p.vertex j) (p.vertex (j + 1));
                    (Set.Icc ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q (0 : ℝ)))
                          ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q (1 : ℝ))) ⊆
                        (fun (s : ℝ) =>
                            (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q s)) ''
                          Set.Icc (0 : ℝ) (1 : ℝ)) →
                      ((∀ (i : Fin 3), Continuous (fun s => A.coord i (q s))) →
                        (let z0 := A.coord 2 (p.vertex j);
                        let z1 := A.coord 2 (p.vertex (j + 1));
                        (((z0 ≤ 0 ∧ 1 ≤ z1) ∨ (z1 ≤ 0 ∧ 1 ≤ z0)) →
                          ((A.coord 2 (q 0) = z0) →
                            ((A.coord 2 (q 1) = z1) →
                              (∃ s ∈ Set.Icc (0 : Real) 1,
                                A.coord 2 (q s) = 0))))))) := by
  classical
  intro n p E a b c v hind hspan A j q hrange hfc z0 z1 hstraddle hz0eq hz1eq
  rcases hstraddle with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have hmemRange : 0 ∈ Set.Icc z0 z1 := ⟨h0, by linarith⟩
    obtain ⟨s, hs, heq⟩ := hrange (by simpa [hz0eq, hz1eq] using hmemRange)
    exact ⟨s, hs, heq⟩
  · have hrange' := intermediate_value_Icc' (a := (0 : Real)) (b := 1)
      (by norm_num) (hfc 2).continuousOn
    have hmemRange : 0 ∈ Set.Icc z1 z0 := ⟨h1, by linarith⟩
    obtain ⟨s, hs, heq⟩ := hrange' (by simpa [hz0eq, hz1eq] using hmemRange)
    exact ⟨s, hs, heq⟩

private theorem honeHit :
    (by
      classical
        exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (E : P3650T1ExposedCorner p),
              let a := p.vertex (E.b - 1);
              let b := p.vertex E.b;
              let c := p.vertex (E.b + 1);
              let v : Fin 3 → Real × Real := ![a, b, c];
              ∀ (hind : AffineIndependent Real v),
                ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
                  let A : AffineBasis (Fin 3) Real (Real × Real) :=
                    ⟨v, hind, hspan⟩;
                  ∀ (j : Fin (n + (3 : ℕ))),
                    let q : Real → Real × Real :=
                      AffineMap.lineMap (p.vertex j) (p.vertex (j + 1));
                    (Set.Icc ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q (0 : ℝ)))
                          ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q (1 : ℝ))) ⊆
                        (fun (s : ℝ) =>
                            (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q s)) ''
                          Set.Icc (0 : ℝ) (1 : ℝ)) →
                      ((∀ (i : Fin 3), Continuous (fun s => A.coord i (q s))) →
                        (let z0 := A.coord 2 (p.vertex j);
                        let z1 := A.coord 2 (p.vertex (j + 1));
                        (((z0 ≤ 0 ∧ 1 ≤ z1) ∨ (z1 ≤ 0 ∧ 1 ≤ z0)) →
                          ((A.coord 2 (q 0) = z0) →
                            ((A.coord 2 (q 1) = z1) →
                              (∃ s ∈ Set.Icc (0 : Real) 1,
                                A.coord 2 (q s) = 1))))))) := by
  classical
  intro n p E a b c v hind hspan A j q hrange hfc z0 z1 hstraddle hz0eq hz1eq
  rcases hstraddle with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have hmemRange : 1 ∈ Set.Icc z0 z1 := ⟨by linarith, h1⟩
    obtain ⟨s, hs, heq⟩ := hrange (by simpa [hz0eq, hz1eq] using hmemRange)
    exact ⟨s, hs, heq⟩
  · have hrange' := intermediate_value_Icc' (a := (0 : Real)) (b := 1)
      (by norm_num) (hfc 2).continuousOn
    have hmemRange : 1 ∈ Set.Icc z1 z0 := ⟨by linarith, h0⟩
    obtain ⟨s, hs, heq⟩ := hrange' (by simpa [hz0eq, hz1eq] using hmemRange)
    exact ⟨s, hs, heq⟩

private theorem hqseg0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s0 : ℝ), (s0 ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (q s0 ∈ segment Real (p.vertex j) (p.vertex
            (j + 1))) ) := by
  classical
  intro n p j q s0 hs0
  rw [segment_eq_image_lineMap]
  exact ⟨s0, hs0, rfl⟩

private theorem hqa :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → (∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s0 : ℝ), ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q s0) = (0 : ℝ)) → ((A.coord 1 (q
            s0) = 0) → (q s0 = a))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordA j q s0 hzs0 hq1zero
  apply A.ext_elem
  intro i
  fin_cases i
  · change A.coord 0 (q s0) = A.coord 0 a
    have hsum : A.coord 0 (q s0) + A.coord 1 (q s0) +
        A.coord 2 (q s0) = 1 := by
      simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (q s0)
    rw [hcoordA.1]
    linarith
  · change A.coord 1 (q s0) = A.coord 1 a
    calc
      _ = 0 := hq1zero
      _ = A.coord 1 a := hcoordA.2.1.symm
  · change A.coord 2 (q s0) = A.coord 2 a
    calc
      _ = 0 := hzs0
      _ = A.coord 2 a := hcoordA.2.2.symm

private theorem hsideA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        (∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), p.vertex j ∈ segment Real (p.vertex i)
            (p.vertex (i + 1)) ↔ j = i ∨ j = i + 1) → (∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s0 : ℝ), (q s0 ∈ segment Real (p.vertex j) (p.vertex (j + 1))) → ((q s0 = a) → (E.b -
            1 = j ∨ E.b - 1 = j + 1))) ) := by
  classical
  intro n p E a hvertexSide j q s0 hqseg0 hqa
  apply (hvertexSide j (E.b - 1)).mp
  have : a ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := by
    rw [← hqa]
    exact hqseg0
  simpa [a] using this

private theorem hqseg1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s1 : ℝ), (s1 ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (q s1 ∈ segment Real (p.vertex j) (p.vertex
            (j + 1))) ) := by
  classical
  intro n p j q s1 hs1
  rw [segment_eq_image_lineMap]
  exact ⟨s1, hs1, rfl⟩

private theorem hqc :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let v : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan Real (Set.range v) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s1 : ℝ), ((A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (q s1) = (1 : ℝ)) → ((A.coord 1 (q
            s1) = 0) → (q s1 = c))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordC j q s1 hzs1 hq1one
  apply A.ext_elem
  intro i
  fin_cases i
  · change A.coord 0 (q s1) = A.coord 0 c
    have hsum : A.coord 0 (q s1) + A.coord 1 (q s1) +
        A.coord 2 (q s1) = 1 := by
      simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (q s1)
    rw [hcoordC.1]
    linarith
  · change A.coord 1 (q s1) = A.coord 1 c
    calc
      _ = 0 := hq1one
      _ = A.coord 1 c := hcoordC.2.1.symm
  · change A.coord 2 (q s1) = A.coord 2 c
    calc
      _ = 1 := hzs1
      _ = A.coord 2 c := hcoordC.2.2.symm

private theorem hsideC :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let c := p.vertex (E.b + 1)
        (∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), p.vertex j ∈ segment Real (p.vertex i)
            (p.vertex (i + 1)) ↔ j = i ∨ j = i + 1) → (∀ (j : Fin (n + (3 : ℕ))),
        let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
        ∀ (s1 : ℝ), (q s1 ∈ segment Real (p.vertex j) (p.vertex (j + 1))) → ((q s1 = c) → (E.b +
            1 = j ∨ E.b + 1 = j + 1))) ) := by
  classical
  intro n p E c hvertexSide j q s1 hqseg1 hqc
  apply (hvertexSide j (E.b + 1)).mp
  have : c ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := by
    rw [← hqc]
    exact hqseg1
  simpa [c] using this

private theorem hidxAt807 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (j :
            Fin (n + (3 : ℕ))), (E.b - (1 : Fin (n + (3 : ℕ))) = j) → ((E.b + (1 : Fin (n + (3 :
            ℕ))) = j + (1 : Fin (n + (3 : ℕ)))) → (E.b + 1 = (E.b - 1) + 1)) ) := by
  classical
  intro n p E j ha hc
  calc
    E.b + 1 = j + 1 := hc
    _ = (E.b - 1) + 1 := congrArg (fun k : Fin (n + 3) => k + 1) ha.symm

private theorem hidxAt812 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (j :
            Fin (n + (3 : ℕ))), (E.b - (1 : Fin (n + (3 : ℕ))) = j + (1 : Fin (n + (3 : ℕ)))) →
            ((E.b + (1 : Fin (n + (3 : ℕ))) = j) → (E.b - 1 = (E.b + 1) + 1)) ) := by
  classical
  intro n p E j ha hc
  calc
    E.b - 1 = j + 1 := ha
    _ = (E.b + 1) + 1 := congrArg (fun k : Fin (n + 3) => k + 1) hc.symm

private theorem hlocal :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        ∀ x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r, (y ∈ O ↔ x ∈ O) )
            := by
  classical
  intro n p O C x hx
  obtain ⟨r, hr, hball⟩ := (P3544T1LocalParity p).2.2.2.2.1 x hx
  refine ⟨r, hr, ?_⟩
  intro y hy
  rcases hball with hsub | hdisj
  · have hyO := hsub hy
    have hxO := hsub (Metric.mem_ball_self hr)
    exact ⟨fun _ => hxO, fun _ => hyO⟩
  · have hyO : y ∉ O := fun hyo => Set.disjoint_left.mp hdisj hy hyo
    have hxO : x ∉ O := fun hxo => Set.disjoint_left.mp hdisj
      (Metric.mem_ball_self hr) hxo
    exact ⟨fun hyo => (hyO hyo).elim, fun hxo => (hxO hxo).elim⟩

private theorem hconstOn :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ x : Real × Real, x ∉ C → ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r, (y ∈ O ↔ x ∈ O)) →
            (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x
            ∈ O ↔ y ∈ O)) ) := by
  classical
  intro n p O C hlocal S hconn hSC x hx y hy
  let f : S → Bool := fun z => decide ((z : Real × Real) ∈ O)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨ρ, hρ, hstable⟩ := hlocal z.1 (hSC z.1 z.2)
    let U : Set S := Subtype.val ⁻¹' Metric.ball z.1 ρ
    refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
    · exact Metric.mem_ball_self hρ
    · intro z' hz'
      have hsame := hstable z' hz'
      have hbool : decide ((z' : Real × Real) ∈ O) = decide ((z : Real × Real) ∈ O) := by
        by_cases hzO : (z' : Real × Real) ∈ O
        · by_cases hzbase : (z : Real × Real) ∈ O
          · simp [hzO, hzbase]
          · exact False.elim (hzbase (hsame.mp hzO))
        · by_cases hzbase : (z : Real × Real) ∈ O
          · exact False.elim (hzO (hsame.mpr hzbase))
          · simp [hzO, hzbase]
      simpa [f] using hbool
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn.2
  have heq := hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  change (decide (x ∈ O) = decide (y ∈ O)) at heq
  by_cases hxo : x ∈ O <;> by_cases hyo : y ∈ O <;> simp [hxo, hyo] at heq ⊢

private theorem hcoordm :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let c := p.vertex (E.b + 1)
        ∀ (v : Fin 3 → Real × Real), ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan
            Real (Set.range v)
            = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        ∀ (i : Fin (3 : ℕ)), (A.coord i : ℝ × ℝ → ℝ) m = (1 / 2 : ℝ) * (A.coord i : ℝ × ℝ → ℝ) a
            + (1 / 2 : ℝ) * (A.coord i : ℝ × ℝ → ℝ) c ) := by
  classical
  intro n p E a c v hind hspan A m i
  change A.coord i (AffineMap.lineMap a c (1 / 2 : Real)) = _
  rw [(A.coord i).apply_lineMap, AffineMap.lineMap_apply_ring]
  ring

private theorem hcoordq :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        ∀ (v : Fin 3 → Real × Real), ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan
            Real (Set.range v)
            = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), ∀ (i : Fin (3 : ℕ)), (A.coord i : ℝ × ℝ → ℝ) (q t) = ((1 : ℝ) - t) * (A.coord
            i : ℝ × ℝ → ℝ) b + t * (A.coord i : ℝ × ℝ → ℝ) m ) := by
  classical
  intro n p E a b c v hind hspan A m q t i
  change A.coord i (AffineMap.lineMap b m t) = _
  rw [(A.coord i).apply_lineMap, AffineMap.lineMap_apply_ring]

private theorem hseed0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        ∀ (v : Fin 3 → Real × Real), ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan
            Real (Set.range v)
            = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 b = 0 ∧ A.coord 1 b =
            1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), ((0 : ℝ) < t) → ((∀ (i : Fin 3), A.coord i m = (1 / 2) * A.coord i a + (1 / 2)
            * A.coord i c) → ((∀ (i : Fin 3), A.coord i (q t) = (1 - t) * A.coord i b + t *
            A.coord i m) → (0 < A.coord 0 (q t))))))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordA hcoordB hcoordC m q t ht0 hcoordm hcoordq
  rw [hcoordq 0, hcoordm 0, hcoordB.1, hcoordA.1, hcoordC.1]
  norm_num
  positivity

private theorem hseed1 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        ∀ (v : Fin 3 → Real × Real), ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan
            Real (Set.range v)
            = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 b = 0 ∧ A.coord 1 b =
            1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), (t ∈ Set.Ioo (0 : Real) 1) → ((∀ (i : Fin 3), A.coord i m = (1 / 2) * A.coord
            i a + (1 / 2) * A.coord i c) → ((∀ (i : Fin 3), A.coord i (q t) = (1 - t) * A.coord i
            b + t * A.coord i m) → (0 < A.coord 1 (q t))))))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordA hcoordB hcoordC m q t ht01 hcoordm hcoordq
  rw [hcoordq 1, hcoordm 1, hcoordB.2.1, hcoordA.2.1, hcoordC.2.1]
  norm_num
  exact ht01.2

private theorem hseed2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        ∀ (v : Fin 3 → Real × Real), ∀ (hind : AffineIndependent Real v), ∀ (hspan : affineSpan
            Real (Set.range v)
            = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
        (A.coord 0 a = 1 ∧ A.coord 1 a = 0 ∧ A.coord 2 a = 0) → ((A.coord 0 b = 0 ∧ A.coord 1 b =
            1 ∧ A.coord 2 b = 0) → ((A.coord 0 c = 0 ∧ A.coord 1 c = 0 ∧ A.coord 2 c = 1) → (
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), ((0 : ℝ) < t) → ((∀ (i : Fin 3), A.coord i m = (1 / 2) * A.coord i a + (1 / 2)
            * A.coord i c) → ((∀ (i : Fin 3), A.coord i (q t) = (1 - t) * A.coord i b + t *
            A.coord i m) → (0 < A.coord 2 (q t))))))) ) := by
  classical
  intro n p E a b c v hind hspan A hcoordA hcoordB hcoordC m q t ht0 hcoordm hcoordq
  rw [hcoordq 2, hcoordm 2, hcoordB.2.2, hcoordA.2.2, hcoordC.2.2]
  norm_num
  positivity

private theorem hseedCone :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), ((0 : ℝ) < t) → (∃ s u : Real, 0 < s ∧ 0 < u ∧ q t = b + s • (a - b) + u • (c
            - b)) ) := by
  classical
  intro n p E a b c m q t ht0
  refine ⟨t / 2, t / 2, by positivity, by positivity, ?_⟩
  apply Prod.ext <;> simp [q, m, AffineMap.lineMap_apply_ring] <;> ring

private theorem hinteriorOdd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (interior T ∩ P3544T1BoundaryCarrier p = ∅) → (
        let O := P3544T1RayParity p
        let C := P3544T1BoundaryCarrier p
        (∀ S : Set (Real × Real), IsConnected S → (∀ x, x ∈ S → x ∉ C) → ∀ x ∈ S, ∀ y ∈ S, (x ∈ O
            ↔ y ∈ O)) → (
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), (q t ∈ interior T) → ((q t ∈ O) → ((IsConnected (interior T)) → (interior T ⊆
            O))))) ) := by
  classical
  intro n p E a b c T hintAvoid O C hconstOn m q t hseed hseedOdd hIconn x hx
  have hconst := hconstOn (interior T) hIconn
    (fun y hy => fun hyC => by
      have hmem : y ∈ interior T ∩ P3544T1BoundaryCarrier p := ⟨hy, hyC⟩
      simp [hintAvoid] at hmem) x hx (q t) hseed
  exact hconst.mpr hseedOdd

private theorem hbaseOdd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (∀ x, x ∈ openSegment Real a c → x ∉ P3544T1BoundaryCarrier p) → (
        let O := P3544T1RayParity p
        let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
        let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
        ∀ (t : ℝ), (q t ∈ interior T) → ((Convex Real T) → ((interior T ⊆ O) → (∀ x, x ∈
            openSegment Real a c → x ∈ O)))) ) := by
  classical
  intro n p E a b c T hbaseAvoid O m q t hseed hTconv hinteriorOdd x hx
  let C := P3544T1BoundaryCarrier p
  have hxT : x ∈ T := by
    change x ∈ convexHull Real ({a, b, c} : Set (Real × Real))
    have ha : a ∈ ({a, b, c} : Set (Real × Real)) := by
      exact Or.inl rfl
    have hc : c ∈ ({a, b, c} : Set (Real × Real)) := by
      exact Or.inr (Or.inr rfl)
    exact (segment_subset_convexHull ha hc) (openSegment_subset_segment Real a c hx)
  have hxcl : x ∈ closure (interior T) := by
    rw [hTconv.closure_interior_eq_closure_of_nonempty_interior ⟨q t, hseed⟩]
    exact subset_closure hxT
  have hxclO : x ∈ closure O := closure_mono hinteriorOdd hxcl
  have hclosure : closure O = O ∪ C := by
    simpa [O, C] using (P3544T1LocalParity p).1
  have hxunion : x ∈ O ∪ C := by
    rw [← hclosure]
    exact hxclO
  rcases hxunion with ho | hc
  · exact ho
  · exact False.elim (hbaseAvoid x hx hc)

private theorem hclear :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let a := p.vertex (E.b - 1)
        let c := p.vertex (E.b + 1)
        (∀ x, x ∈ openSegment Real a c → x ∉ P3544T1BoundaryCarrier p) → (
        let C := P3544T1BoundaryCarrier p
        Disjoint (openSegment Real (p.vertex (E.b - 1)) (p.vertex (E.b + 1))) C) ) := by
  classical
  intro n p E a c hbaseAvoid C
  apply Set.disjoint_left.mpr
  intro x hx hxC
  have hx' : x ∈ openSegment Real a c := by simpa [a, c] using hx
  exact hbaseAvoid x hx' hxC

end TriangleDiagonalGeometry

namespace TriangleBaseAvoidance

private theorem hbaseAvoid :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀ (i
            : Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let a := p.vertex (E.b - 1)
        let b := p.vertex E.b
        let c := p.vertex (E.b + 1)
        let triangleVertices : Fin 3 → Real × Real := ![a, b, c]
        ∀ (hind : AffineIndependent ℝ ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))]), ∀ (hspan : affineSpan ℝ (Set.range
            ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b, p.vertex (E.b + (1 : Fin (n
            + (3 : ℕ))))]) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨triangleVertices, hind, hspan⟩
        let T := convexHull Real ({a, b, c} : Set (Real × Real))
        (∀ (x : ℝ × ℝ), x ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} ↔ ∀ (i : Fin (3 : ℕ)), (0 : ℝ) ≤ (A.coord i
                : ℝ × ℝ → ℝ) x) → ((∀ (x : ℝ
            × ℝ), x ∈ interior ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))}) ↔ ∀ (i : Fin (3 : ℕ)), (0 : ℝ) < (A.coord
                i : ℝ × ℝ → ℝ) x) → ((∀ (i :
            Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), p.vertex j ∈ segment ℝ (p.vertex i)
            (p.vertex (i + (1 : Fin (n + (3 : ℕ))))) ↔ j = i ∨ j = i + (1 : Fin (n + (3 : ℕ)))) →
            ((∀ x ∈ T, x ∈ segment ℝ a b → (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ)) →
                ((∀ x ∈ T, x ∈ segment ℝ
            b c → (A.coord (0 : Fin (3 :
            ℕ)) : ℝ × ℝ → ℝ) x = (0 : ℝ)) → ((E.b - (1 : Fin (n + (3 : ℕ))) ≠ E.b + (1 : Fin (n +
            (3 : ℕ)))) → ((E.b + (1 : Fin (n + (3 : ℕ))) ≠ E.b - (1 : Fin (n + (3 : ℕ))) + (1 :
            Fin (n + (3 : ℕ)))) → ((E.b - (1 : Fin (n + (3 : ℕ))) ≠ E.b + (1 : Fin (n + (3 : ℕ)))
            + (1 : Fin (n + (3 : ℕ)))) → ((interior ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))}) ∩ P3544T1BoundaryCarrier p = ∅) → ((
        let A := A; (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (1 : ℝ) ∧ (A.coord (1
            : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ) ∧
            (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) =
            (0 : ℝ)) → ((
        let A := A; (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) = (0 : ℝ) ∧ (A.coord (1 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ)
            (p.vertex E.b) = (1 : ℝ) ∧ (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) =
            (0 : ℝ)) → ((
        let A := A; (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ) ∧ (A.coord (1
            : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ) ∧
            (A.coord (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) =
            (1 : ℝ)) → (∀ x, x ∈ openSegment Real a c → x ∉ P3544T1BoundaryCarrier
            p))))))))))))) ) := by
  classical
  intro n p E hempty a b c triangleVertices hind hspan A T hmem hint hvertexSide hleftFace
      hrightFace habdist habNext hcaNext hintAvoid hcoordA hcoordB hcoordC x hx hxC
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
  have hxb := (TriangleDiagonalGeometry.hopenBaseCoords n p E hind hspan hcoordA hcoordC) x hx
  have hxT : x ∈ T := (hmem x).mpr (by
    intro i
    fin_cases i
    · exact le_of_lt hxb.1
    · change 0 ≤ A.coord 1 x
      rw [hxb.2.1]
    · exact le_of_lt hxb.2.2)
  by_cases hja : j = E.b - 1
  · subst j
    have hface := hleftFace x hxT
      (by simpa [a, b] using hj)
    exact (ne_of_gt hxb.2.2) hface
  by_cases hjb : j = E.b
  · subst j
    have hface := hrightFace x hxT
      (by simpa [b, c] using hj)
    exact (ne_of_gt hxb.1) hface
  rw [segment_eq_image_lineMap] at hj
  obtain ⟨t, ht, hqt⟩ := hj
  let q : Real → Real × Real := AffineMap.lineMap (p.vertex j) (p.vertex (j + 1))
  have hqtq : q t = x := hqt
  have hqcont : Continuous q :=
    (AffineMap.lineMap (k := Real) (p.vertex j) (p.vertex (j +
        1))).continuous_of_finiteDimensional
  have hfc (i : Fin 3) : Continuous (fun s => A.coord i (q s)) :=
    (A.coord i).continuous_of_finiteDimensional.comp hqcont
  have hline (i : Fin 3) (s : Real) :
      A.coord i (q s) = (1 - s) * A.coord i (p.vertex j) +
        s * A.coord i (p.vertex (j + 1)) := TriangleDiagonalGeometry.hline n p E hind hspan
            (TriangleDiagonalGeometry.hcoordLine n p E hind hspan) j i s
  have ht' := TriangleDiagonalGeometry.ht' n p x j t ht hqtq
      (TriangleDiagonalGeometry.hnotLeft n p E hempty hind hspan hcoordA hcoordB hcoordC x j
          hxb hxT hja hjb t hqt hqtq hqcont hfc hline) (TriangleDiagonalGeometry.hnotRight n p
          E hempty hind hspan hcoordA hcoordB hcoordC x j hxb hxT)
  have hzero := TriangleDiagonalGeometry.hzero n p E hind hspan x
          j hxb t hqtq hline
  by_cases hposj : 0 < A.coord 1 (p.vertex j)
  · have hqt0 : 0 < A.coord 0 (q t) := TriangleDiagonalGeometry.hqt0At504 n p E hind hspan x j
      hxb t hqtq
    have hqt2 := TriangleDiagonalGeometry.hqt2At507 n p E hind hspan x j
        hxb t hqtq
    have hn : (fun s => A.coord 0 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
      (hfc 0).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hqt0)
    have hn' : (fun s => A.coord 2 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
      (hfc 2).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hqt2)
    have hn'' : (fun s => A.coord 0 (q s)) ⁻¹' Set.Ioi (0 : Real) ∩
        (fun s => A.coord 2 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
      Filter.inter_mem hn hn'
    obtain ⟨u, v, huv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn''
    have hlow : max u 0 < t := max_lt_iff.mpr ⟨huv.1, ht'.1⟩
    obtain ⟨s, hus, hst⟩ := exists_between hlow
    have hs01 : s ∈ Set.Ioo (0 : Real) 1 := ⟨lt_of_le_of_lt (le_max_right _ _) hus,
      hst.trans ht'.2⟩
    have hsuv : s ∈ Set.Ioo u v :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hus, hst.trans huv.2⟩
    have hq0 : 0 < A.coord 0 (q s) := (hsub hsuv).1
    have hq2 : 0 < A.coord 2 (q s) := (hsub hsuv).2
    have hq1 : 0 < A.coord 1 (q s) := TriangleDiagonalGeometry.hq1At528 n p triangleVertices
        hind hspan j t
        hline ht' hzero hposj s hst
    have hqint : q s ∈ interior T := (hint _).mpr (by
      intro i
      fin_cases i
      · exact hq0
      · exact hq1
      · exact hq2)
    have hqseg := TriangleDiagonalGeometry.hqsegAt546 n p j s hs01
    have hfalse : q s ∈ (∅ : Set (Real × Real)) := TriangleDiagonalGeometry.hfalseAt549 n p E
        hintAvoid j s hqint hqseg
    simp at hfalse
  · by_cases hposnext : 0 < A.coord 1 (p.vertex (j + 1))
    · have hqt0 := TriangleDiagonalGeometry.hqt0At504 n p E hind hspan x
          j hxb t hqtq
      have hqt2 := TriangleDiagonalGeometry.hqt2At507 n p E hind hspan x
          j hxb t hqtq
      have hn : (fun s => A.coord 0 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
        (hfc 0).continuousAt.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds hqt0)
      have hn' : (fun s => A.coord 2 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
        (hfc 2).continuousAt.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds hqt2)
      have hn'' : (fun s => A.coord 0 (q s)) ⁻¹' Set.Ioi (0 : Real) ∩
          (fun s => A.coord 2 (q s)) ⁻¹' Set.Ioi (0 : Real) ∈ nhds t :=
        Filter.inter_mem hn hn'
      obtain ⟨u, v, huv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn''
      have hhigh : t < min v 1 := lt_min huv.2 ht'.2
      obtain ⟨s, hts, hsv⟩ := exists_between hhigh
      have hs01 : s ∈ Set.Ioo (0 : Real) 1 := ⟨ht'.1.trans hts,
        lt_of_lt_of_le hsv (min_le_right _ _)⟩
      have hsuv : s ∈ Set.Ioo u v :=
        ⟨huv.1.trans hts, lt_of_lt_of_le hsv (min_le_left _ _)⟩
      have hq0 : 0 < A.coord 0 (q s) := (hsub hsuv).1
      have hq2 : 0 < A.coord 2 (q s) := (hsub hsuv).2
      have hq1 : 0 < A.coord 1 (q s) := TriangleDiagonalGeometry.hq1At579 n p triangleVertices
          hind hspan j t
          hline ht' hzero hposnext s hts
      have hqint : q s ∈ interior T := (hint _).mpr (by
        intro i
        fin_cases i
        · exact hq0
        · exact hq1
        · exact hq2)
      have hqseg := TriangleDiagonalGeometry.hqsegAt546 n p j s hs01
      have hfalse : q s ∈ (∅ : Set (Real × Real)) := TriangleDiagonalGeometry.hfalseAt549 n p E
          hintAvoid j s hqint hqseg
      simp at hfalse
    · have hαnonpos : A.coord 1 (p.vertex j) ≤ 0 := le_of_not_gt hposj
      have hβnonpos : A.coord 1 (p.vertex (j + 1)) ≤ 0 := le_of_not_gt hposnext
      have hleftTerm : (1 - t) * A.coord 1 (p.vertex j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht'.2.le) hαnonpos
      have hrightTerm : t * A.coord 1 (p.vertex (j + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht'.1.le hβnonpos
      have hα0 := TriangleDiagonalGeometry.hα0 n p E hind hspan j
          t ht' hzero hleftTerm hrightTerm
      have hβ0 := TriangleDiagonalGeometry.hβ0 n p E hind
          hspan j t ht' hzero hleftTerm hrightTerm
      have hline1 (s : Real) := TriangleDiagonalGeometry.hline1 n p E
          hind hspan j hline hα0 hβ0 s
      let z0 := A.coord 2 (p.vertex j)
      let z1 := A.coord 2 (p.vertex (j + 1))
      have hline2 (s : Real) : A.coord 2 (q s) = (1 - s) * z0 + s * z1 := by
        simpa [z0, z1] using hline 2 s
      have hzt : (1 - t) * z0 + t * z1 = A.coord 2 x := TriangleDiagonalGeometry.hzt n p E hind
          hspan x j t hqtq hline2
      have hzpos : 0 < (1 - t) * z0 + t * z1 := by rw [hzt]; exact hxb.2.2
      have hxsum : A.coord 0 x + A.coord 1 x + A.coord 2 x = 1 := by
        simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one x
      have hzlt := TriangleDiagonalGeometry.hzlt n p E hind hspan x hxb hxsum
      have hstraddle := TriangleDiagonalGeometry.hstraddle n p E hind hspan x j hxb t ht' hzt
          (TriangleDiagonalGeometry.hz0case n p E hind hspan j
          (TriangleDiagonalGeometry.hnotIoo0 n p E hempty hind hspan hmem hcoordA hcoordB
          hcoordC j hposj hα0 (TriangleDiagonalGeometry.hcoord0j n p E hind hspan j hposj hα0
          (TriangleDiagonalGeometry.hsum0 n p E hind hspan j))))
          (TriangleDiagonalGeometry.hz1case n p E hind hspan j
          (TriangleDiagonalGeometry.hnotIoo1 n p E hempty hind hspan hmem hcoordA hcoordB
          hcoordC j hposnext hβ0 (TriangleDiagonalGeometry.hcoord01 n p E hind hspan j hposnext
          hβ0 (TriangleDiagonalGeometry.hsum1 n p E hind hspan j))))
          hxsum
      have hrange := intermediate_value_Icc (a := (0 : Real)) (b := 1)
        (by norm_num) (hfc 2).continuousOn
      have hz0eq : A.coord 2 (q 0) = z0 := by simpa [z0] using hline2 0
      have hz1eq : A.coord 2 (q 1) = z1 := by simpa [z1] using hline2 1
      obtain ⟨s0, hs0, hzs0⟩ := (TriangleDiagonalGeometry.hzeroHit n p E hind hspan j hrange hfc
          hstraddle hz0eq hz1eq)
      have hq1zero : A.coord 1 (q s0) = 0 := hline1 s0
      have hsideA := TriangleDiagonalGeometry.hsideA n p E
          hvertexSide j s0 (TriangleDiagonalGeometry.hqseg0 n p j s0 hs0)
              (TriangleDiagonalGeometry.hqa n p E hind hspan hcoordA j s0 hzs0 hq1zero)
      obtain ⟨s1, hs1, hzs1⟩ := (TriangleDiagonalGeometry.honeHit n p E hind hspan j hrange hfc
          hstraddle hz0eq hz1eq)
      have hq1one : A.coord 1 (q s1) = 0 := hline1 s1
      have hsideC := TriangleDiagonalGeometry.hsideC n p E
          hvertexSide j s1 (TriangleDiagonalGeometry.hqseg1 n p j s1 hs1)
              (TriangleDiagonalGeometry.hqc n p E hind hspan hcoordC j s1 hzs1 hq1one)
      rcases hsideA with ha | ha <;> rcases hsideC with hc | hc
      · exact habdist (ha.trans hc.symm)
      · have hidx : E.b + 1 = (E.b - 1) + 1 := TriangleDiagonalGeometry.hidxAt807 n p E j ha hc
        exact habNext hidx
      · have hidx : E.b - 1 = (E.b + 1) + 1 := TriangleDiagonalGeometry.hidxAt812 n p E j ha hc
        exact hcaNext hidx
      · exact habdist (ha.trans hc.symm)

end TriangleBaseAvoidance

theorem P3650T1EmptyTriangleDiagonal {n : Nat} (p : P3381T1PolygonBoundary n)
    (hn : 0 < n) (E : P3650T1ExposedCorner p)
    (hentry : ∀ (j : Fin (n + 3)) (w : Real × Real), j ≠ E.b - 1 → j ≠ E.b →
      w ∈ interior (convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real))) →
      w ∈ segment Real (p.vertex j) (p.vertex (j + 1)) →
      ∃ k, (k = j ∨ k = j + 1) ∧
        p.vertex k ∈ convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
            Set (Real × Real)) ∧ E.height w ≤ E.height (p.vertex k))
    (hempty : ∀ i, p.vertex i ∈ convexHull Real
      ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
        Set (Real × Real)) → i = E.b - 1 ∨ i = E.b ∨ i = E.b + 1) :
    ∃ D : P3650T1VisibleDiagonal p E, D.a = E.b - 1 ∧ D.b = E.b + 1 := by
-- BODY
  classical
  let a := p.vertex (E.b - 1)
  let b := p.vertex E.b
  let c := p.vertex (E.b + 1)
  let triangleVertices : Fin 3 → Real × Real := ![a, b, c]
  have hdet := TriangleDiagonalGeometry.hdet n p E
  have hind := TriangleDiagonalGeometry.hind n p E hdet
  have hspan := TriangleDiagonalGeometry.hspan n p E hind
  let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨triangleVertices, hind, hspan⟩
  have hA0 : A 0 = a := rfl
  have hA1 : A 1 = b := rfl
  have hA2 : A 2 = c := rfl
  have hheight : E.height = A.coord 1 := TriangleDiagonalGeometry.hheight n p E hind hspan
  let T := convexHull Real ({a, b, c} : Set (Real × Real))
  have hrange := TriangleDiagonalGeometry.hrangeAt179 n p E hind hspan
  have hmem := TriangleDiagonalGeometry.hmemAt186 n p E hind
      hspan hrange
  have hint := TriangleDiagonalGeometry.hint n p E
      hind hspan hrange
  have hbase := TriangleDiagonalGeometry.hbase n p E
  have hheightcoord (x : Real × Real) : E.height x = A.coord 1 x := by
    rw [hheight]
  have hvertexSide (i j : Fin (n + 3)) := TriangleDiagonalGeometry.hvertexSide n p i j
  have hleftFace (x : Real × Real) (hx : x ∈ T)
      (hxs : x ∈ segment Real a b) := TriangleDiagonalGeometry.hleftFace n p E
          hind hspan x hx hxs
  have hrightFace (x : Real × Real) (hx : x ∈ T)
      (hxs : x ∈ segment Real b c) := TriangleDiagonalGeometry.hrightFace n p E
          hind hspan x hx hxs
  have habdist := TriangleDiagonalGeometry.habdist n p E (TriangleDiagonalGeometry.hacOuter n p E
      hdet)
  have hbcOuter := TriangleDiagonalGeometry.hbcOuter n p E
  have habNext := TriangleDiagonalGeometry.habNext n p E
  have hcaNext := TriangleDiagonalGeometry.hcaNext n p hn E
  have hintAvoid := TriangleDiagonalGeometry.hintAvoid n p E hentry hempty hind hspan hint
      hheightcoord
      hleftFace hrightFace
  have hcoordA := TriangleDiagonalGeometry.hcoordA n p E hind hspan
  have hcoordB := TriangleDiagonalGeometry.hcoordB n p E hind hspan
  have hcoordC := TriangleDiagonalGeometry.hcoordC n p E hind hspan
  have hbaseAvoid := TriangleBaseAvoidance.hbaseAvoid n p E hempty hind hspan hmem hint
      hvertexSide hleftFace hrightFace habdist habNext hcaNext hintAvoid hcoordA hcoordB hcoordC
  let O := P3544T1RayParity p
  let C := P3544T1BoundaryCarrier p
  obtain ⟨rcone, hrcone, hcone⟩ := E.cone_odd
  let m : Real × Real := AffineMap.lineMap a c (1 / 2 : Real)
  let q : Real → Real × Real := fun t => AffineMap.lineMap b m t
  have hq0 : q 0 = b := by simp [q]
  have hqcont : Continuous q := by
    exact (AffineMap.lineMap (k := Real) b m).continuous_of_finiteDimensional
  have hqball : q ⁻¹' Metric.ball b rcone ∈ nhds (0 : Real) :=
    hqcont.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by rw [hq0]; exact Metric.mem_ball_self hrcone))
  obtain ⟨u, v, huv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hqball
  have hzeroI : (0 : Real) ∈ Set.Ioo u v := huv
  obtain ⟨t, ht0, htmin⟩ : ∃ t : Real, 0 < t ∧ t < min v 1 :=
    exists_between (lt_min hzeroI.2 one_pos)
  have ht01 : t ∈ Set.Ioo (0 : Real) 1 := ⟨ht0, (lt_min_iff.mp htmin).2⟩
  have htuv' : t ∈ Set.Ioo u v := ⟨by linarith [hzeroI.1, ht0],
    (lt_min_iff.mp htmin).1⟩
  have hqnear : q t ∈ Metric.ball b rcone := hsub htuv'
  have hcoordm (i : Fin 3) := TriangleDiagonalGeometry.hcoordm n p E triangleVertices
          hind hspan i
  have hcoordq (i : Fin 3) := TriangleDiagonalGeometry.hcoordq n p E triangleVertices hind
          hspan t i
  have hseed0 : 0 < A.coord 0 (q t) := TriangleDiagonalGeometry.hseed0 n p E triangleVertices
      hind hspan hcoordA
      hcoordB hcoordC t ht0 hcoordm hcoordq
  have hseed1 : 0 < A.coord 1 (q t) := TriangleDiagonalGeometry.hseed1 n p E triangleVertices
      hind hspan hcoordA
      hcoordB hcoordC t ht01 hcoordm hcoordq
  have hseed2 : 0 < A.coord 2 (q t) := TriangleDiagonalGeometry.hseed2 n p E triangleVertices
      hind hspan hcoordA
      hcoordB hcoordC t ht0 hcoordm hcoordq
  have hseed : q t ∈ interior T := (hint _).mpr (by
    intro i
    fin_cases i
    · simpa using hseed0
    · simpa using hseed1
    · simpa using hseed2)
  have hseedOdd : q t ∈ O := (hcone (q t) hqnear).2 (TriangleDiagonalGeometry.hseedCone n p E t ht0)
  have hTconv : Convex Real T := convex_convexHull Real _
  have hIconn : IsConnected (interior T) :=
    (hTconv.interior).isConnected ⟨q t, hseed⟩
  have hbaseOdd : ∀ x, x ∈ openSegment Real a c → x ∈ O := TriangleDiagonalGeometry.hbaseOdd n p
      E hbaseAvoid t hseed hTconv (TriangleDiagonalGeometry.hinteriorOdd n p E hintAvoid
          (TriangleDiagonalGeometry.hconstOn n p (TriangleDiagonalGeometry.hlocal n p)) t hseed
          hseedOdd hIconn)
  refine ⟨⟨E.b - 1, E.b + 1, habdist, habNext, hcaNext, (TriangleDiagonalGeometry.hclear n p E
      hbaseAvoid), ?_, ?_⟩,
    rfl, rfl⟩
  · intro x hx
    exact hbaseOdd x (by simpa [a, c] using hx)
  · exact Or.inl ⟨rfl, rfl, hempty⟩

end ApollonianSuperharmonic

end
