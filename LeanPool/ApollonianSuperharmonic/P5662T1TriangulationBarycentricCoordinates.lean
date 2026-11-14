/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3381T1PairedTriangulation
public import LeanPool.ApollonianSuperharmonic.P3381T1AffineTriangleMap
public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P5662T1TriangulationBarycentricCoordinates]

/-!
# P5662T1TriangulationBarycentricCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5662T1TriangulationBarycentricCoordinates {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    (t : P3381T1PairedTriangulation p X K) :
    (∃ b : Fin t.count → (Real × Real) → Fin 3 → Real,
      (∀ k z, (∑ j, b k z j) = 1) ∧
      (∀ k z, (∑ j, b k z j • p.vertex (t.face k j)) = z) ∧
      (∀ k w, (∑ j, w j) = 1 →
        b k (∑ j, w j • p.vertex (t.face k j)) = w) ∧
      (∀ k j, Continuous (fun z => b k z j)) ∧
      (∀ k z, z ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) ↔
        ∀ j, 0 ≤ b k z j) ∧
      (∀ k i, b k (p.vertex (t.face k i)) = Pi.single i 1) ∧
      (∀ k l z, z ∈ convexHull Real
        (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))) →
        ∀ j, t.face k j ∉ Set.range (t.face l) → b k z j = 0)) ∧
    (∀ i k,
      p.vertex i ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) ↔
        i ∈ Set.range (t.face k)) := by
-- BODY
  have coordinates :
      ∃ b : Fin t.count → (Real × Real) → Fin 3 → Real,
        (∀ k z, (∑ j, b k z j) = 1) ∧
        (∀ k z, (∑ j, b k z j • p.vertex (t.face k j)) = z) ∧
        (∀ k w, (∑ j, w j) = 1 →
          b k (∑ j, w j • p.vertex (t.face k j)) = w) ∧
        (∀ k j, Continuous (fun z => b k z j)) ∧
        (∀ k z, z ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) ↔
          ∀ j, 0 ≤ b k z j) ∧
        (∀ k i, b k (p.vertex (t.face k i)) = Pi.single i 1) ∧
        (∀ k l z, z ∈ convexHull Real
          (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))) →
          ∀ j, t.face k j ∉ Set.range (t.face l) → b k z j = 0) := by
    classical
    let standard : Fin 3 → Real × Real := ![(0, 0), (1, 0), (0, 1)]
    have hstandard : P3381T1TriangleDeterminant standard ≠ 0 := by
      change ((1 : Real) - 0) * (1 - 0) - (0 - 0) * (0 - 0) ≠ 0
      norm_num
    have maps : ∀ k, ∃ A : (Real × Real) ≃ₜ (Real × Real),
        ∀ w : Fin 3 → Real, (∑ j, w j) = 1 →
          A (∑ j, w j • standard j) = ∑ j, w j • p.vertex (t.face k j) := by
      intro k
      exact P3381T1AffineTriangleMap standard (p.vertex ∘ t.face k)
        hstandard (t.source_nondegenerate k)
    choose A hA using maps
    let weights (z : Real × Real) : Fin 3 → Real := ![1 - z.1 - z.2, z.1, z.2]
    have weights_sum (z : Real × Real) : (∑ j, weights z j) = 1 := by
      rw [Fin.sum_univ_three]
      change (1 - z.1 - z.2) + z.1 + z.2 = 1
      ring
    have standard_sum (w : Fin 3 → Real) :
        (∑ j, w j • standard j) = (w 1, w 2) := by
      apply Prod.ext <;> simp [Fin.sum_univ_three, standard]
    have weights_sum_standard (z : Real × Real) :
        (∑ j, weights z j • standard j) = z := by
      rw [standard_sum]
      rfl
    let b (k : Fin t.count) (z : Real × Real) := weights ((A k).symm z)
    have bsum k z : (∑ j, b k z j) = 1 := weights_sum _
    have breconstruct k z : (∑ j, b k z j • p.vertex (t.face k j)) = z := by
      rw [← hA k _ (bsum k z), weights_sum_standard]
      exact (A k).apply_symm_apply z
    have bunique k (w : Fin 3 → Real) (hw : (∑ j, w j) = 1) :
        b k (∑ j, w j • p.vertex (t.face k j)) = w := by
      rw [← hA k w hw]
      change weights ((A k).symm (A k _)) = w
      rw [(A k).symm_apply_apply, standard_sum]
      funext j
      fin_cases j <;> simp [weights]
      simp only [Fin.sum_univ_three] at hw
      linarith
    have bcontinuous k j : Continuous (fun z => b k z j) := by
      fin_cases j <;> dsimp [b, weights]
      all_goals fun_prop
    have hull_weights (S : Set (Fin (n + 3))) k (hS : S ⊆ Set.range (t.face k)) z
        (hz : z ∈ convexHull Real (p.vertex '' S)) :
        (∀ j, 0 ≤ b k z j) ∧ (∀ j, t.face k j ∉ S → b k z j = 0) := by
      obtain ⟨ι, inst, w, v, hw, hsum, hv, heq⟩ :=
        mem_convexHull_iff_exists_fintype.mp hz
      let _ := inst
      choose a ha hva using hv
      have ha' : ∀ r, ∃ j, t.face k j = a r := fun r => hS (ha r)
      choose c hc using ha'
      let W : Fin 3 → Real := fun j => ∑ r, if c r = j then w r else 0
      have hW : (∑ j, W j) = 1 := by
        simpa [W, Finset.sum_comm] using hsum
      have hWz : (∑ j, W j • p.vertex (t.face k j)) = z := by
        simp [W, Finset.sum_smul, Finset.sum_comm, ite_smul, hc, hva, heq]
      have hbW : b k z = W := hWz ▸ bunique k W hW
      rw [hbW]
      constructor
      · intro j
        exact Finset.sum_nonneg fun r _ => by
          split_ifs
          · exact hw r
          · exact le_rfl
      · intro j hj
        apply Finset.sum_eq_zero
        intro r _
        have hne : c r ≠ j := by
          intro h
          apply hj
          rw [← h, hc]
          exact ha r
        simp [hne]
    refine ⟨b, bsum, breconstruct, bunique, bcontinuous, ?_, ?_, ?_⟩
    · intro k z
      constructor
      · intro hz
        rw [Set.range_comp] at hz
        exact (hull_weights _ k (Set.Subset.refl _) z hz).1
      · intro hz
        exact mem_convexHull_of_exists_fintype (b k z) (p.vertex ∘ t.face k)
          hz (bsum k z) (fun j => Set.mem_range_self j) (breconstruct k z)
    · intro k i
      let w : Fin 3 → Real := Pi.single i 1
      have hsum : (∑ j : Fin 3, w j) = 1 := by simp [w]
      have heq : (∑ j : Fin 3, w j •
          p.vertex (t.face k j)) = p.vertex (t.face k i) := by simp [w]
      rw [← heq]
      exact bunique k _ hsum
    · intro k l z hz j hj
      exact (hull_weights _ k Set.inter_subset_left z hz).2 j (by
        intro h
        exact hj h.2)
  have vertex_incidence : ∀ i k,
      p.vertex i ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) ↔
        i ∈ Set.range (t.face k) := by
    obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
      coordinates
    let D k := convexHull Real (Set.range (p.vertex ∘ t.face k))
    intro i k
    constructor
    · intro hik
      obtain ⟨l, j, hlj⟩ := t.vertex_used i
      have hil : p.vertex i ∈ D l := by
        apply subset_convexHull
        exact ⟨j, congrArg p.vertex hlj⟩
      have hic : p.vertex i ∈ convexHull Real
          (p.vertex '' (Set.range (t.face l) ∩ Set.range (t.face k))) := by
        rw [← t.source_intersection]
        exact ⟨hil, hik⟩
      by_contra hi
      have hzero := bcommon l k (p.vertex i) hic j (hlj ▸ hi)
      have hone : b l (p.vertex i) j = 1 := by
        rw [← hlj, bvertex]
        simp
      linarith
    · rintro ⟨j, rfl⟩
      exact subset_convexHull Real _ ⟨j, rfl⟩
  exact ⟨coordinates, vertex_incidence⟩

end ApollonianSuperharmonic

end
