/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCorner
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

-- [TABLET NODE: P3650T1TriangleEntry]

/-!
# P3650T1TriangleEntry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangleEntryGeometry

private theorem hbasis :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∃ A :
            AffineBasis (Fin 3) Real (Real × Real), (∀ i, A i = ![p.vertex (E.b - 1), p.vertex
            E.b, p.vertex (E.b + 1)] i) ∧ E.height = A.coord 1 ) := by
  classical
  intro n p E
  let a := p.vertex (E.b - 1)
  let b := p.vertex E.b
  let c := p.vertex (E.b + 1)
  let v : Fin 3 → Real × Real := ![a, b, c]
  have hdet : (b.1 - a.1) * (c.2 - a.2) -
      (c.1 - a.1) * (b.2 - a.2) ≠ 0 := by
    simpa [P3381T1TriangleDeterminant, a, b, c] using E.nondegenerate
  have hind : AffineIndependent Real v := by
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
      apply (mul_eq_zero.mp (show z 1 * ((b.1 - a.1) * (c.2 - a.2) -
          (c.1 - a.1) * (b.2 - a.2)) = 0 by
        linear_combination (c.2 - a.2) * hx' - (c.1 - a.1) * hy')).resolve_right hdet
    have hz2 : z 2 = 0 := by
      apply (mul_eq_zero.mp (show z 2 * ((b.1 - a.1) * (c.2 - a.2) -
          (c.1 - a.1) * (b.2 - a.2)) = 0 by
        linear_combination (b.1 - a.1) * hy' - (b.2 - a.2) * hx')).resolve_right hdet
    fin_cases i <;> simp_all
  have hspan : affineSpan Real (Set.range v) = ⊤ := by
    apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp [Module.finrank_prod]
  let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
  refine ⟨A, fun _ => rfl, ?_⟩
  apply AffineMap.ext_on A.tot
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp only [AffineBasis.coord_apply]
  · exact E.height_prev
  · exact E.height_top
  · exact E.height_next

private theorem hrange :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (∀ (i : Fin (3 : ℕ)), (A : Fin (3 : ℕ) → ℝ × ℝ)
            i = ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b, p.vertex (E.b + (1 :
            Fin (n + (3 : ℕ))))] i) → (Set.range A = ({p.vertex (E.b - 1), p.vertex E.b,
            p.vertex (E.b + 1)} : Set (Real × Real))) ) := by
  classical
  intro n p E A hA
  rw [show (A : Fin 3 → Real × Real) =
    ![p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)] from funext hA]
  ext x
  simp
  tauto

private theorem hmem :
    (by
      classical
      exact
        ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
        let D := convexHull Real (Set.range A)
        ∀ x, x ∈ D ↔ ∀ i, 0 ≤ A.coord i x ) := by
  classical
  intro A D x
  exact Set.ext_iff.mp A.convexHull_eq_nonneg_coord x

private theorem hint :
    (by
      classical
      exact
        ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)),
        let D := convexHull Real (Set.range A)
        ∀ x, x ∈ interior D ↔ ∀ i, 0 < A.coord i x ) := by
  classical
  intro A D x
  exact Set.ext_iff.mp A.interior_convexHull x

private theorem hpos :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (w :
            ℝ × ℝ), ∀ (A : AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (E.height = A.coord (1 : Fin (3
            : ℕ))) → (
        let D := convexHull Real (Set.range A)
        (w ∈ interior D) → ((∀ x, x ∈ interior D ↔ ∀ i, 0 < A.coord i x) → (0 < E.height w))) )
            := by
  classical
  intro n p E w A hheight D hwD hint
  rw [hheight]
  exact (hint w).mp hwD 1

private theorem hface0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (A 1 = p.vertex E.b) → ((A 2 = p.vertex (E.b +
            1)) → (
        let D := convexHull Real (Set.range A)
        (∀ x, x ∈ D ↔ ∀ i, 0 ≤ A.coord i x) → (∀ x, x ∈ D → A.coord 0 x = 0 → x ∈ segment Real
            (p.vertex E.b) (p.vertex (E.b + 1))))) ) := by
  classical
  intro n p E A hA1 hA2 D hmem x hx hx0
  have hxnonneg := (hmem x).mp hx
  have hxsum : A.coord 0 x + A.coord 1 x + A.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one x
  rw [← hA1, ← hA2, segment_eq_image_lineMap]
  refine ⟨A.coord 2 x, ⟨hxnonneg 2, by linarith [hxnonneg 1]⟩, ?_⟩
  apply A.ext_elem
  intro i
  rw [(A.coord i).apply_lineMap]
  fin_cases i <;> simp [AffineMap.lineMap_apply_ring, Fin.ext_iff] <;>
    linarith only [hxsum, hx0]

private theorem hface2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (A 0 = p.vertex (E.b - 1)) → ((A 1 = p.vertex
            E.b) → (
        let D := convexHull Real (Set.range A)
        (∀ x, x ∈ D ↔ ∀ i, 0 ≤ A.coord i x) → (∀ x, x ∈ D → A.coord 2 x = 0 → x ∈ segment Real
            (p.vertex (E.b - 1)) (p.vertex E.b)))) ) := by
  classical
  intro n p E A hA0 hA1 D hmem x hx hx2
  have hxnonneg := (hmem x).mp hx
  have hxsum : A.coord 0 x + A.coord 1 x + A.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one x
  rw [← hA0, ← hA1, segment_eq_image_lineMap]
  refine ⟨A.coord 1 x, ⟨hxnonneg 1, by linarith [hxnonneg 0]⟩, ?_⟩
  apply A.ext_elem
  intro i
  rw [(A.coord i).apply_lineMap]
  fin_cases i <;> simp [AffineMap.lineMap_apply_ring, Fin.ext_iff] <;>
    linarith only [hxsum, hx2]

private theorem hside :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (j :
            Fin (n + (3 : ℕ))), (j ≠ E.b - (1 : Fin (n + (3 : ℕ)))) → ((j ≠ E.b) → (∀ x, x ∈
            segment Real (p.vertex j) (p.vertex (j + 1)) → x ≠ p.vertex j → x ≠ p.vertex (j + 1)
            → x ∉ segment Real (p.vertex (E.b - 1)) (p.vertex E.b) ∧ x ∉ segment Real (p.vertex
            E.b) (p.vertex (E.b + 1)))) ) := by
  classical
  intro n p E j hjprev hjtop x hx hxj hxj1
  constructor
  · intro hxl
    have hxl' : x ∈ segment Real (p.vertex (E.b - 1))
        (p.vertex (E.b - 1 + 1)) := by simpa only [sub_add_cancel] using hxl
    have hh : x ∈ segment Real (p.vertex j) (p.vertex (j + 1)) ∩
        segment Real (p.vertex (E.b - 1)) (p.vertex (E.b - 1 + 1)) := ⟨hx, hxl'⟩
    rw [p.edge_intersection j (E.b - 1) hjprev] at hh
    exact hh.1.elim hxj hxj1
  · intro hxl
    have hh : x ∈ segment Real (p.vertex j) (p.vertex (j + 1)) ∩
        segment Real (p.vertex E.b) (p.vertex (E.b + 1)) := ⟨hx, hxl⟩
    rw [p.edge_intersection j E.b hjtop] at hh
    exact hh.1.elim hxj hxj1

private theorem hreach :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (j :
            Fin (n + (3 : ℕ))), ∀ (w : ℝ × ℝ), (j ≠ E.b - (1 : Fin (n + (3 : ℕ)))) → ((j ≠ E.b) →
            ((w ∈ segment ℝ (p.vertex j) (p.vertex (j + (1 : Fin (n + (3 : ℕ)))))) → (∀ (A :
            AffineBasis (Fin (3 : ℕ)) ℝ (ℝ × ℝ)), (E.height = A.coord (1 : Fin (3 : ℕ))) → (
        let D := convexHull Real (Set.range A)
        (w ∈ interior D) → ((∀ x, x ∈ D ↔ ∀ i, 0 ≤ A.coord i x) → ((∀ x, x ∈ interior D ↔ ∀ i, 0
            < A.coord i x) → ((0 < E.height w) → ((∀ x, x ∈ D → A.coord 0 x = 0 → x ∈ segment
            Real (p.vertex E.b) (p.vertex (E.b + 1))) → ((∀ x, x ∈ D → A.coord 2 x = 0 → x ∈
            segment Real (p.vertex (E.b - 1)) (p.vertex E.b)) → ((∀ x, x ∈ segment Real (p.vertex
            j) (p.vertex (j + 1)) → x ≠ p.vertex j → x ≠ p.vertex (j + 1) → x ∉ segment Real
            (p.vertex (E.b - 1)) (p.vertex E.b) ∧ x ∉ segment Real (p.vertex E.b) (p.vertex (E.b
            + 1))) → ((¬w = p.vertex j) → ((¬w = p.vertex (j + (1 : Fin (n + (3 : ℕ))))) → (∀ (l
            : Fin (n + 3)), ∀ (k : Fin (n + 3)), (l = j ∧ k = j + 1) ∨ (l = j + 1 ∧ k = j) →
            E.height (p.vertex l) ≤ E.height (p.vertex k) → p.vertex k ∈ D ∧ E.height w ≤
            E.height (p.vertex k)))))))))))))) ) := by
  classical
  intro n p E j w hjprev hjtop hws A hheight D hwD hmem hint hpos hface0 hface2 hside hwj hwj1 l
      k hlk hhk
  have hsegment : segment Real (p.vertex l) (p.vertex k) =
      segment Real (p.vertex j) (p.vertex (j + 1)) := by
    rcases hlk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact segment_symm Real _ _
  have hwl : w ≠ p.vertex l := by
    rcases hlk with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hwj
    · exact hwj1
  have hwk : w ≠ p.vertex k := by
    rcases hlk with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hwj1
    · exact hwj
  have hlkne : p.vertex l ≠ p.vertex k := by
    intro heq
    have hw' : w ∈ segment Real (p.vertex l) (p.vertex k) := by
      rw [hsegment]
      exact hws
    rw [← heq] at hw'
    exact hwl (by simpa only [segment_same, Set.mem_singleton_iff] using hw')
  let q : Real → Real × Real := AffineMap.lineMap (p.vertex l) (p.vertex k)
  have hqinj : Function.Injective q := AffineMap.lineMap_injective Real hlkne
  have hq0 : q 0 = p.vertex l := AffineMap.lineMap_apply_zero _ _
  have hq1 : q 1 = p.vertex k := AffineMap.lineMap_apply_one _ _
  have hqcont : Continuous q :=
    (AffineMap.lineMap (k := Real) (p.vertex l) (p.vertex k)).continuous_of_finiteDimensional
  obtain ⟨t, ht, htq⟩ : ∃ t ∈ Set.Icc (0 : Real) 1, q t = w := by
    have hw' : w ∈ segment Real (p.vertex l) (p.vertex k) := hsegment ▸ hws
    rw [segment_eq_image_lineMap] at hw'
    exact hw'
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    exact hwl (by rw [← htq, ← heq, hq0]))
  have hhq : ∀ s, E.height (q s) =
      (1 - s) * E.height (p.vertex l) + s * E.height (p.vertex k) := by
    intro s
    exact (E.height.apply_lineMap _ _ s).trans (AffineMap.lineMap_apply_ring _ _ s)
  have hhw : E.height w ≤ E.height (p.vertex k) := by
    rw [← htq, hhq]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hhk)]
  let I : Set Real := Set.Icc 0 1 ∩ q ⁻¹' D
  have hDclosed : IsClosed D := (Set.finite_range A).isClosed_convexHull Real
  have hIcompact : IsCompact I := isCompact_Icc.inter_right (hDclosed.preimage hqcont)
  have htI : t ∈ I := by
    refine ⟨ht, ?_⟩
    change q t ∈ D
    rw [htq]
    exact interior_subset hwD
  obtain ⟨m, hmI, hmmax⟩ :=
    hIcompact.exists_isMaxOn ⟨t, htI⟩ continuous_id.continuousOn
  have htm : t ≤ m := hmmax htI
  have hmpos : 0 < m := ht0.trans_le htm
  have hmheight : 0 < E.height (q m) := by
    have hhwle : E.height w ≤ E.height (q m) := by
      rw [← htq, hhq, hhq]
      nlinarith [mul_nonneg (sub_nonneg.mpr htm) (sub_nonneg.mpr hhk)]
    exact hpos.trans_le hhwle
  -- A maximal parameter below one would still be interior.
  have hm1 : m = 1 := by
    by_contra hmne
    have hmlt : m < 1 := lt_of_le_of_ne hmI.1.2 hmne
    have hqmseg : q m ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := by
      rw [← hsegment, segment_eq_image_lineMap]
      exact ⟨m, hmI.1, rfl⟩
    have hqmne : q m ≠ p.vertex j ∧ q m ≠ p.vertex (j + 1) := by
      have hne0 : q m ≠ p.vertex l := by
        intro heq
        have := hqinj (heq.trans hq0.symm)
        linarith
      have hne1 : q m ≠ p.vertex k := by
        intro heq
        have := hqinj (heq.trans hq1.symm)
        linarith
      rcases hlk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne0, hne1⟩
      · exact ⟨hne1, hne0⟩
    have hqmavoid := hside (q m) hqmseg hqmne.1 hqmne.2
    have hqmint : q m ∈ interior D := by
      apply (hint _).mpr
      intro i
      have hn := (hmem _).mp hmI.2 i
      fin_cases i
      · exact lt_of_le_of_ne hn (by
          intro heq
          exact hqmavoid.2 (hface0 _ hmI.2 heq.symm))
      · simpa [hheight, Fin.isValue, Fin.reduceFinMk] using hmheight
      · exact lt_of_le_of_ne hn (by
          intro heq
          exact hqmavoid.1 (hface2 _ hmI.2 heq.symm))
    have hnhds : q ⁻¹' interior D ∩ Set.Iio (1 : Real) ∈ nhds m :=
      Filter.inter_mem (hqcont.continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hqmint)) (Iio_mem_nhds hmlt)
    obtain ⟨u, v, ⟨hum, hmv⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    obtain ⟨s, hms, hsv⟩ := exists_between hmv
    have hs := hsub ⟨hum.trans hms, hsv⟩
    have hsD : q s ∈ D := interior_subset hs.1
    have hsI : s ∈ I := ⟨⟨by linarith, hs.2.le⟩, hsD⟩
    exact (not_lt_of_ge (hmmax hsI)) hms
  refine ⟨?_, hhw⟩
  have hmmem : q m ∈ D := hmI.2
  simpa only [hm1, hq1] using hmmem

end TriangleEntryGeometry

theorem P3650T1TriangleEntry {n : Nat} (p : P3381T1PolygonBoundary n)
    (E : P3650T1ExposedCorner p) :
    ∀ (j : Fin (n + 3)) (w : Real × Real), j ≠ E.b - 1 → j ≠ E.b →
      w ∈ interior (convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real))) →
      w ∈ segment Real (p.vertex j) (p.vertex (j + 1)) →
      ∃ k, (k = j ∨ k = j + 1) ∧
        p.vertex k ∈ convexHull Real
          ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
            Set (Real × Real)) ∧ E.height w ≤ E.height (p.vertex k) := by
-- BODY
  classical
  -- The determinant makes the neighboring vertices an affine basis.
  have hbasis := TriangleEntryGeometry.hbasis n p E
  intro j w hjprev hjtop hw hws
  obtain ⟨A, hA, hheight⟩ := hbasis
  have hA0 : A 0 = p.vertex (E.b - 1) := hA 0
  have hA1 : A 1 = p.vertex E.b := hA 1
  have hA2 : A 2 = p.vertex (E.b + 1) := hA 2
  have hrange : Set.range A =
      ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
        Set (Real × Real)) := TriangleEntryGeometry.hrange n p E A hA
  let D := convexHull Real (Set.range A)
  have hwD : w ∈ interior D := by simpa only [D, hrange] using hw
  have hmem := TriangleEntryGeometry.hmem A
  have hint := TriangleEntryGeometry.hint A
  have hpos := TriangleEntryGeometry.hpos n p E w A hheight hwD hint
  -- Vanishing lateral coordinates identify the two incident polygon sides.
  have hface0 := TriangleEntryGeometry.hface0 n p E A hA1 hA2 hmem
  have hface2 := TriangleEntryGeometry.hface2 n p E A hA0 hA1 hmem
  have hside := TriangleEntryGeometry.hside n p E j hjprev hjtop
  by_cases hwj : w = p.vertex j
  · refine ⟨j, Or.inl rfl, ?_, by rw [hwj]⟩
    exact interior_subset (hwj ▸ hw)
  by_cases hwj1 : w = p.vertex (j + 1)
  · refine ⟨j + 1, Or.inr rfl, ?_, by rw [hwj1]⟩
    exact interior_subset (hwj1 ▸ hw)
  -- Follow the selected side toward its endpoint of greater height.
  have hreach := TriangleEntryGeometry.hreach n p E j w hjprev hjtop hws A hheight hwD hmem hint
      hpos hface0 hface2 hside hwj hwj1
  rcases le_total (E.height (p.vertex j)) (E.height (p.vertex (j + 1))) with hh | hh
  · obtain ⟨hkD, hkh⟩ := hreach j (j + 1) (Or.inl ⟨rfl, rfl⟩) hh
    exact ⟨j + 1, Or.inr rfl, by simpa only [D, hrange] using hkD, hkh⟩
  · obtain ⟨hkD, hkh⟩ := hreach (j + 1) j (Or.inr ⟨rfl, rfl⟩) hh
    exact ⟨j, Or.inl rfl, by simpa only [D, hrange] using hkD, hkh⟩

end ApollonianSuperharmonic

end
