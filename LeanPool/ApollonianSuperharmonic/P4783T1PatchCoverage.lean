/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1Hexagon
public import LeanPool.ApollonianSuperharmonic.P4715T1PatchFaces
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import LeanPool.ApollonianSuperharmonic.P4783T1ParallelogramFan
public import LeanPool.ApollonianSuperharmonic.P4783T1PatchCoordinates


-- [TABLET NODE: P4783T1PatchCoverage]

/-!
# P4783T1PatchCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4783T1PatchCoverage :
    (⋃ j : Fin 12, convexHull Real (P4715T1Position ''
      Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j)))) =
        P4715T1Hexagon := by
-- BODY
  classical
  let U : Real × Real := (0, 0)
  let V : Real × Real := (-(1/3), -(2/3))
  let X : Real × Real := (-1, -1)
  let Y : Real × Real := (-(4/3), -(2/3))
  let Z : Real × Real := (-1, 0)
  let W : Real × Real := (-(1/3), 1/3)
  let C : Real × Real := (-(1/2), -(1/2))
  let D : Real × Real := (-(5/6), -(1/6))
  let E : Real × Real := (-(11/12), -(7/12))
  let F : Real × Real := (-(5/12), -(1/12))
  let q : Fin 12 → Fin 3 → Real × Real := ![
    ![U, V, C], ![X, V, C], ![Z, Y, D], ![Z, W, D],
    ![X, C, E], ![C, D, E], ![Y, D, E], ![X, Y, E],
    ![U, C, F], ![C, D, F], ![W, D, F], ![U, W, F]]
  have htable (j : Fin 12) :
      P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j) = q j := by
    simpa only [q,U,V,X,Y,Z,W,C,D,E,F, neg_div] using
      P4783T1PatchCoordinates j
  have hK (j : Fin 12) :
      convexHull Real (P4715T1Position ''
        Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) =
      convexHull Real (Set.range (q j)) := by
    rw [← Set.range_comp, htable j]
  have hboundary : P4715T1Position ∘ P4715T1BoundaryCycle =
      ![U, V, X, Y, Z, W] := by
    as_aux_lemma =>
    funext i
    fin_cases i <;> norm_num [P4715T1Position, P4715T1Offsets,
      P4715T1BoundaryCycle, Function.comp_def,
      Matrix.cons_val_zero', Matrix.cons_val_succ', U, V, X, Y, Z, W]
  have hhex : P4715T1Hexagon =
      convexHull Real ({U, V, X, Y, Z, W} : Set (Real × Real)) := by
    unfold P4715T1Hexagon
    rw [hboundary]
    congr 1
    ext z
    simp [Matrix.range_cons]; tauto
  have hconv : Convex Real P4715T1Hexagon := by
    rw [hhex]; exact convex_convexHull _ _
  have hcorner (z : Real × Real) (hz : z ∈ ({U,V,X,Y,Z,W} : Set (Real × Real))) :
      z ∈ P4715T1Hexagon := by
    rw [hhex]; exact subset_convexHull _ _ hz
  have hU := hcorner U (by simp)
  have hV := hcorner V (by simp)
  have hX := hcorner X (by simp)
  have hY := hcorner Y (by simp)
  have hZ := hcorner Z (by simp)
  have hW := hcorner W (by simp)
  have hmid (P Q : Real × Real) (hP : P ∈ P4715T1Hexagon)
      (hQ : Q ∈ P4715T1Hexagon) :
      (1/2 : Real) • P + (1/2 : Real) • Q ∈ P4715T1Hexagon :=
    hconv hP hQ (by norm_num) (by norm_num) (by norm_num)
  have hC : C ∈ P4715T1Hexagon := by
    convert hmid U X hU hX using 1; norm_num [C, U, X]
  have hD : D ∈ P4715T1Hexagon := by
    convert hmid Y W hY hW using 1; norm_num [D, Y, W]
  have hE : E ∈ P4715T1Hexagon := by
    convert hmid X D hX hD using 1; norm_num [E, X, D]
  have hF : F ∈ P4715T1Hexagon := by
    convert hmid U D hU hD using 1; norm_num [F, U, D]
  have range3 (p : Fin 3 → Real × Real) :
      Set.range p = ({p 0, p 1, p 2} : Set (Real × Real)) := by
    ext z
    simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
  have toHull (j : Fin 12) (z : Real × Real) (a b c : Real)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
      (heq : a • q j 0 + b • q j 1 + c • q j 2 = z) :
      z ∈ convexHull Real (Set.range (q j)) := by
    as_aux_lemma =>
    apply mem_convexHull_of_exists_fintype (ι := Fin 3) ![a,b,c] (q j)
    · intro k
      fin_cases k
      · exact ha
      · exact hb
      · exact hc
    · simpa [Fin.sum_univ_succ, add_assoc] using hs
    · intro k; exact Set.mem_range_self k
    · simpa [Fin.sum_univ_succ, add_assoc] using heq
  simp_rw [hK]
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro j
    apply convexHull_min _ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases j <;> fin_cases k <;>
      first | exact hU | exact hV | exact hX | exact hY | exact hZ |
        exact hW | exact hC | exact hD | exact hE | exact hF
  · intro z hz
    have bound (a b r : Real)
        (hv : ∀ w ∈ ({U,V,X,Y,Z,W} : Set (Real × Real)), a*w.1+b*w.2 ≤ r) :
        a*z.1+b*z.2 ≤ r := by
      as_aux_lemma =>
      rw [hhex] at hz
      apply convexHull_min hv (convex_halfSpace_le (f := fun w : Real × Real =>
        a*w.1+b*w.2) ?_ r) hz
      constructor
      · intro p q; simp; ring
      · intro t p; simp; ring
    have hbds : (1/2)*z.1+(1/2)*z.2 ≤ 0 ∧ (-1/2)*z.1+(-1/2)*z.2 ≤ 1 ∧
        2*z.1+(-1)*z.2 ≤ 0 ∧ 1*z.1+(-2)*z.2 ≤ 1 ∧
        (-1)*z.1+2*z.2 ≤ 1 ∧ (-2)*z.1+1*z.2 ≤ 2 := by
      as_aux_lemma =>
      refine ⟨bound (1/2) (1/2) 0 ?_, bound (-1/2) (-1/2) 1 ?_,
        bound 2 (-1) 0 ?_, bound 1 (-2) 1 ?_,
        bound (-1) 2 1 ?_, bound (-2) 1 2 ?_⟩
      all_goals
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num [U,V,X,Y,Z,W]
    let a := -(z.1+z.2)/2
    let b := -3*(z.1-z.2)/2
    have ha : 0 ≤ a := by dsimp [a]; linarith [hbds.1]
    have ha' : a ≤ 1 := by dsimp [a]; linarith [hbds.2.1]
    have hlo : -a ≤ b ∧ a-1 ≤ b := by
      dsimp [a,b]; constructor <;> linarith [hbds.2.2.1, hbds.2.2.2.1]
    have hhi : b ≤ 1+a ∧ b ≤ 2-a := by
      dsimp [a,b]; constructor <;> linarith [hbds.2.2.2.2.1, hbds.2.2.2.2.2]
    by_cases hb : b ≤ 0
    · by_cases ha2 : a ≤ 1/2
      · apply Set.mem_iUnion.mpr
        refine ⟨0, toHull 0 z (1-2*a) (-2*b) (2*a+2*b)
          (by linarith) (by linarith) (by linarith [hlo.1]) (by ring) ?_⟩
        change (1-2*a) • U + (-2*b) • V + (2*a+2*b) • C = z
        ext <;> dsimp [U,V,C,a,b] <;> ring
      · apply Set.mem_iUnion.mpr
        refine ⟨1, toHull 1 z (2*a-1) (-2*b) (2-2*a+2*b)
          (by linarith) (by linarith) (by linarith [hlo.2]) (by ring) ?_⟩
        change (2*a-1) • X + (-2*b) • V + (2-2*a+2*b) • C = z
        ext <;> dsimp [X,V,C,a,b] <;> ring
    · by_cases hb' : 1 ≤ b
      · by_cases ha2 : a ≤ 1/2
        · apply Set.mem_iUnion.mpr
          refine ⟨3, toHull 3 z (2*b-2) (1-2*a) (2*a-2*b+2)
            (by linarith) (by linarith) (by linarith [hhi.1]) (by ring) ?_⟩
          change (2*b-2) • Z + (1-2*a) • W + (2*a-2*b+2) • D = z
          ext <;> dsimp [Z,W,D,a,b] <;> ring
        · apply Set.mem_iUnion.mpr
          refine ⟨2, toHull 2 z (2*b-2) (2*a-1) (4-2*a-2*b)
            (by linarith) (by linarith) (by linarith [hhi.2]) (by ring) ?_⟩
          change (2*b-2) • Z + (2*a-1) • Y + (4-2*a-2*b) • D = z
          ext <;> dsimp [Z,Y,D,a,b] <;> ring
      · by_cases ha2 : a ≤ 1/2
        · have hf := P4783T1ParallelogramFan U C W (2*a) b
            (by linarith) (by linarith) (by linarith) (by linarith)
          have heq : U + (2*a) • C + b • W = z := by
            ext <;> dsimp [U,C,W,a,b] <;> ring
          dsimp only at hf
          rw [heq] at hf
          norm_num [U,C,W] at hf
          rcases hf with hf | hf | hf | hf
          · exact Set.mem_iUnion.mpr ⟨8, by
              rw [range3]
              change z ∈ convexHull Real ({U,C,F} : Set (Real × Real))
              simpa [U,C,F] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨9, by
              rw [range3]
              change z ∈ convexHull Real ({C,D,F} : Set (Real × Real))
              simpa [C,D,F] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨10, by
              rw [range3]
              change z ∈ convexHull Real ({W,D,F} : Set (Real × Real))
              simpa [W,D,F, Set.insert_comm] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨11, by
              rw [range3]
              change z ∈ convexHull Real ({U,W,F} : Set (Real × Real))
              simpa [U,W,F, Set.insert_comm] using hf⟩
        · have hf := P4783T1ParallelogramFan C C W (2*a-1) b
            (by linarith) (by linarith) (by linarith) (by linarith)
          have heq : C + (2*a-1) • C + b • W = z := by
            ext <;> dsimp [C,W,a,b] <;> ring
          dsimp only at hf
          rw [heq] at hf
          norm_num [C,W] at hf
          rcases hf with hf | hf | hf | hf
          · exact Set.mem_iUnion.mpr ⟨4, by
              rw [range3]
              change z ∈ convexHull Real ({X,C,E} : Set (Real × Real))
              simpa [X,C,E, Set.insert_comm] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨7, by
              rw [range3]
              change z ∈ convexHull Real ({X,Y,E} : Set (Real × Real))
              simpa [X,Y,E] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨6, by
              rw [range3]
              change z ∈ convexHull Real ({Y,D,E} : Set (Real × Real))
              simpa [Y,D,E] using hf⟩
          · exact Set.mem_iUnion.mpr ⟨5, by
              rw [range3]
              change z ∈ convexHull Real ({C,D,E} : Set (Real × Real))
              simpa [C,D,E, Set.insert_comm] using hf⟩

end ApollonianSuperharmonic

end
