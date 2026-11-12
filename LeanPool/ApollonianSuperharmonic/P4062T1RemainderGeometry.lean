/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderPaths
public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorGeometry
public import LeanPool.ApollonianSuperharmonic.FordLaplacianTable
public import LeanPool.ApollonianSuperharmonic.P4112T1BoundaryMultiplicity
public import LeanPool.ApollonianSuperharmonic.P4112T1ParentalNeighbors
public import LeanPool.ApollonianSuperharmonic.P4112T1LowerNeighbors
public import Mathlib.Data.Nat.Dist

/-!
# P4062T1RemainderGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

-- [TABLET NODE: P4062T1RemainderGeometry]
theorem P4062T1RemainderGeometry (P : FordFareyParameter) (hP : 2 < P.q) :
    (by
      classical
      exact
        let A := P4062T1RecursiveInteriors P
        let E := (A 0 ∪ A 1) ∪ (A 2 ∪ A 3)
        let W := P4062T1InteriorSquare P.q \ E
        let B := P4062T1RemainderPaths P
        let d : GaussianInt → Nat := fun x =>
          let a := if x ∈ (B 0).1 then (B 0).2 else (B 1).2
          (x.re-a.re).natAbs + (x.im-a.im).natAbs
        E ⊆ P4062T1InteriorSquare P.q ∧
        W = (B 0).1 ∪ (B 1).1 ∧ Disjoint (B 0).1 (B 1).1 ∧
        (∀ x ∈ (B 0).1, ∀ y ∈ (B 1).1, ¬ FourNeighborAdjacent x y) ∧
        (∀ j, ∀ x ∈ (B j).1, ∀ y ∈ (B j).1,
          FourNeighborAdjacent x y ↔
            (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) ∧
        (∀ j, ∀ x ∈ (B j).1,
          (E.filter (fun y => FourNeighborAdjacent y x)).card = 2 ∧
          FordBoundaryMultiplicity P x = (if x = (B j).2 then 3 else 2) ∧
          ((B j).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
            (if x = (B j).2 then 0 else 1)) ∧
        (∀ x ∈ W,
          ((E.filter (fun y => FourNeighborAdjacent y x)).card : Int) +
            ((W.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card : Int) =
              2 + FourNeighborLaplacian (FordOdometer P) x) ∧
        (∀ x ∈ W, ∀ y ∈ W, FourNeighborAdjacent x y → d x ≠ d y)
    ) := by
-- BODY
  classical
  intro A E W B d
  obtain ⟨hW, hdisjoint, hcross, hedge⟩ := P4112T1PathGeometry P hP
  have hparent := P4112T1ParentalNeighbors P hP
  have hboundary := P4112T1BoundaryMultiplicity P hP
  change W = (B 0).1 ∪ (B 1).1 at hW
  change (∀ j, ∀ x ∈ (B j).1, ∀ y ∈ (B j).1,
    FourNeighborAdjacent x y ↔
      (x.re = y.re ∨ x.im = y.im) ∧ Nat.dist (d x) (d y) = 1) at hedge
  change (∀ j, ∀ x ∈ (B j).1,
    (E.filter (fun y => FourNeighborAdjacent y x)).card = 2) at hparent
  change (∀ j, ∀ x ∈ (B j).1,
    FordBoundaryMultiplicity P x = (if x = (B j).2 then 3 else 2)) at hboundary
  have hlower : (∀ j, ∀ x ∈ (B j).1,
    ((B j).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
      (if x = (B j).2 then 0 else 1)) := by
    intro j x hx
    convert (P4112T1LowerNeighbors P hP) j x hx using 1;
      congr 2; ext y;
      by_cases hy : y ∈ (B 0).1 <;>
      by_cases hxx : x ∈ (B 0).1 <;>
      simp [d, B, hy, hxx]
  have hA := (P4062T1InteriorGeometry P hP).1
  have hE : E ⊆ P4062T1InteriorSquare P.q := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hA 0 hx
      · exact hA 1 hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hA 2 hx
      · exact hA 3 hx
  have adjacent_symm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h <;> subst y <;> simp [FourNeighborAdjacent]
  have path_subset (j : Fin 2) : (B j).1 ⊆ W := by
    intro x hx
    rw [hW]
    fin_cases j
    · exact Finset.mem_union.mpr (Or.inl hx)
    · exact Finset.mem_union.mpr (Or.inr hx)
  have select_path (x : GaussianInt) (hx : x ∈ W) :
      ∃ j : Fin 2, x ∈ (B j).1 := by
    rw [hW] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩
  have same_path (j : Fin 2) (x : GaussianInt) (hx : x ∈ (B j).1)
      (y : GaussianInt) (hy : y ∈ W) (hyx : FourNeighborAdjacent y x) :
      y ∈ (B j).1 := by
    rw [hW] at hy
    fin_cases j
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact hy
      · exact False.elim (hcross x hx y hy (adjacent_symm hyx))
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact False.elim (hcross y hy x hx hyx)
      · exact hy
  have lower_filter (j : Fin 2) (x : GaussianInt) (hx : x ∈ (B j).1) :
      W.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x) =
        (B j).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hadj, hd⟩
      exact ⟨same_path j x hx y hy hadj, hadj, hd⟩
    · rintro ⟨hy, hadj, hd⟩
      exact ⟨path_subset j hy, hadj, hd⟩
  have square_bounds (x : GaussianInt) (hx : x ∈ P4062T1InteriorSquare P.q) :
      1 ≤ x.re ∧ x.re ≤ (P.q : Int) - 1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q : Int) - 1 := by
    unfold P4062T1InteriorSquare at hx
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    exact ⟨(Finset.mem_Icc.mp hu).1, (Finset.mem_Icc.mp hu).2,
      (Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2⟩
  refine ⟨hE, hW, hdisjoint, hcross, hedge, ?_, ?_, ?_⟩
  · intro j x hx
    exact ⟨hparent j x hx, hboundary j x hx, hlower j x hx⟩
  · intro x hx
    obtain ⟨j, hxj⟩ := select_path x hx
    have hb := square_bounds x (Finset.mem_sdiff.mp hx).1
    have ht := (FordLaplacianTable P).2.2 (by omega) x
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    have hm := hboundary j x hxj
    have hl := hlower j x hxj
    rw [hparent j x hxj, lower_filter j x hxj, hl]
    by_cases hr : x = (B j).2
    · have hm3 : FordBoundaryMultiplicity P x = 3 := by
        simpa only [ite_eq_left hr] using hm
      rw [ite_eq_left hr, ht.2.1 hm3]
      norm_num
    · have hm2 : FordBoundaryMultiplicity P x = 2 := by
        simpa only [ite_eq_right hr] using hm
      rw [ite_eq_right hr, ht.1 hm2]
      norm_num
  · intro x hx y hy hxy
    obtain ⟨j, hxj⟩ := select_path x hx
    have hyj := same_path j x hxj y hy (adjacent_symm hxy)
    have hd := ((hedge j x hxj y hyj).mp hxy).2
    intro heq
    rw [heq, Nat.dist_self] at hd
    omega

end ApollonianSuperharmonic

end
