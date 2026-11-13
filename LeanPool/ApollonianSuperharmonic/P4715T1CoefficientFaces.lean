/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P4715T1HexagonSubdivision
public import LeanPool.ApollonianSuperharmonic.P4715T1PatchEnumeration
public import LeanPool.ApollonianSuperharmonic.P4715T1Region
public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger
public import Mathlib.Analysis.Convex.PathConnected

-- [TABLET NODE: P4715T1CoefficientFaces]

/-!
# P4715T1CoefficientFaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CoefficientFaceProof

private theorem faceDet_eq_delta :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        ∀ (f : PeriodicSubtileFaceIndex), faceDet f = (P4715T1Position (SixSubtileFaceVertices
            f (1 : Fin (3 : ℕ))) - P4715T1Position (SixSubtileFaceVertices f (0 : Fin (3 :
            ℕ)))).1 * (P4715T1Position (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) -
            P4715T1Position (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).2 -
            (P4715T1Position (SixSubtileFaceVertices f (1 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).2 * (P4715T1Position
            (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).1 ) := by
  classical
  intro faceDet f
  simp only [faceDet, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem delta_nonzero :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        (∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ 0) → ((∀ (f : PeriodicSubtileFaceIndex),
            faceDet f = (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)).1 * (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)).2 - (P4715T1Position
            (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices f 0)).2 *
            (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
            (SixSubtileFaceVertices f 0)).1) → (∀ (f : PeriodicSubtileFaceIndex),
            (P4715T1Position (SixSubtileFaceVertices f (1 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).1 * (P4715T1Position
            (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).2 - (P4715T1Position
            (SixSubtileFaceVertices f (1 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).2 * (P4715T1Position
            (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) - P4715T1Position
            (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))).1 ≠ (0 : ℝ))) ) := by
  classical
  intro faceDet faceDet_nonzero faceDet_eq_delta f
  rw [← faceDet_eq_delta f]
  exact faceDet_nonzero f

private theorem Dconvex :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        Convex ℝ D ) := by
  classical
  intro D x hx y hy a b ha hb hab
  dsimp [D] at hx hy ⊢
  have hpos (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : 0 < a*u+b*v := by
    by_cases hza : a = 0
    · have hb1 : b = 1 := by linarith
      subst a
      subst b
      simpa using hv
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hza)
      nlinarith [mul_pos hap hu, mul_nonneg hb (le_of_lt hv)]
  constructor
  · exact hpos _ _ hx.1 hy.1
  · constructor
    · exact hpos _ _ hx.2.1 hy.2.1
    · have hsum : 0 < a * (1 - (x.1+x.2)) + b * (1 - (y.1+y.2)) :=
        hpos _ _ (sub_pos.mpr hx.2.2) (sub_pos.mpr hy.2.2)
      calc
        a*x.1+b*y.1+(a*x.2+b*y.2) = a*(x.1+x.2)+b*(y.1+y.2) := by ring
        _ < a*1+b*1 := by nlinarith
        _ = 1 := by rw [← add_mul, hab]; ring

private theorem D_closure :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        (D ⊆ W) → (∀ [IsClosed W], closure D = W) ) := by
  classical
  intro D W D_subset_W W_closed
  apply Set.Subset.antisymm
  · exact closure_minimal D_subset_W W_closed
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hzw : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1 := by simpa [W] using hz
    let c : ℝ × ℝ := (1/3,1/3)
    let r : ℝ := min (1/2) (ε / (2 * (dist z c + 1)))
    have hr0 : 0 < r := by dsimp [r]; positivity
    have hrhalf : r ≤ 1/2 := min_le_left _ _
    have hrε : r ≤ ε / (2*(dist z c+1)) := min_le_right _ _
    let y : ℝ × ℝ := (1-r) • z + r • c
    have hy : y ∈ D := by
      dsimp [D, y, c] at hz ⊢
      have h1r : 0 ≤ 1-r := by linarith [hrhalf]
      constructor
      · have : 0 < r * (1/3) := mul_pos hr0 (by norm_num)
        nlinarith [mul_nonneg h1r hzw.1]
      · constructor
        · have : 0 < r * (1/3) := mul_pos hr0 (by norm_num)
          nlinarith [mul_nonneg h1r hzw.2.1]
        · have hsum : z.1+z.2 ≤ 1 := hzw.2.2
          nlinarith [mul_nonneg h1r (by linarith : 0 ≤ 1-(z.1+z.2))]
    have hcoord1 : dist y.1 z.1 ≤ r := by
      rw [Real.dist_eq]
      have heq : ((1-r) • z + r • c).1 - z.1 = r * (1/3-z.1) := by dsimp [c]; ring
      rw [heq, abs_mul, abs_of_pos hr0]
      have hc : |(1:ℝ)/3-z.1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [mul_le_mul_of_nonneg_left hc hr0.le]
    have hcoord2 : dist y.2 z.2 ≤ r := by
      rw [Real.dist_eq]
      have heq : ((1-r) • z + r • c).2 - z.2 = r * (1/3-z.2) := by dsimp [c]; ring
      rw [heq, abs_mul, abs_of_pos hr0]
      have hc : |(1:ℝ)/3-z.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [mul_le_mul_of_nonneg_left hc hr0.le]
    have hdist : dist y z ≤ r := by
      rw [Prod.dist_eq]
      exact max_le_iff.mpr ⟨hcoord1, hcoord2⟩
    refine ⟨y, hy, ?_⟩
    calc
      dist z y = dist y z := dist_comm _ _
      _ ≤ r := hdist
      _ < ε := by
        have hden : 0 < 2*(dist z c+1) := by positivity
        have hbound : r * (2*(dist z c+1)) ≤ ε := (le_div_iff₀ hden).mp hrε
        have hdistnonneg : 0 ≤ dist z c := dist_nonneg
        nlinarith

private theorem mem_bottom_segment :
    (by
      classical
      exact
        ∀ (z : ℝ × ℝ), z ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) ↔ z.2 = (0 : ℝ) ∧ (0 :
            ℝ) ≤ z.1 ∧ z.1 ≤ (1 : ℝ) ) := by
  classical
  intro z
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, heq⟩
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, Prod.mk_sub_mk, sub_zero, sub_self,
        Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, vadd_eq_add, Prod.mk_add_mk, add_zero]
        at h1 h2
    exact ⟨h2.symm, by simpa [h1] using ht.1, by simpa [h1] using ht.2⟩
  · rintro ⟨h2,h1,h1le⟩
    refine ⟨z.1, ⟨h1,h1le⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, h2]

private theorem mem_diagonal_segment :
    (by
      classical
      exact
        ∀ (z : ℝ × ℝ), z ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) ↔ z.1 + z.2 = (1 : ℝ)
            ∧ (0 : ℝ) ≤ z.1 ∧ (0 : ℝ) ≤ z.2 ) := by
  classical
  intro z
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, heq⟩
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, Prod.mk_sub_mk, zero_sub, sub_zero,
        Prod.smul_mk, smul_eq_mul, mul_neg, mul_one, vadd_eq_add, Prod.mk_add_mk, add_zero]
        at h1 h2
    exact ⟨by linarith [h1,h2], by linarith [h1,ht.2], by linarith [h2,ht.1]⟩
  · rintro ⟨hsum,h1,h2⟩
    refine ⟨z.2, ⟨h2, by linarith [hsum,h1]⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply]; linarith

private theorem mem_left_segment :
    (by
      classical
      exact
        ∀ (z : ℝ × ℝ), z ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) ↔ z.1 = (0 : ℝ) ∧ (0 :
            ℝ) ≤ z.2 ∧ z.2 ≤ (1 : ℝ) ) := by
  classical
  intro z
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, heq⟩
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, Prod.mk_sub_mk, sub_self, sub_zero,
        Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, vadd_eq_add, Prod.mk_add_mk, add_zero]
        at h1 h2
    exact ⟨h1.symm, by simpa [h2] using ht.1, by simpa [h2] using ht.2⟩
  · rintro ⟨h1,h2,h2le⟩
    refine ⟨z.2, ⟨h2,h2le⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, h1]

private theorem D_frontier :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (IsOpen D) → (
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        (closure D = W) → ((∀ (z : ℝ×ℝ), z ∈ segment ℝ (0,0) (1,0) ↔ z.2=0 ∧ 0≤z.1 ∧ z.1≤1) → ((∀
            (z : ℝ×ℝ), z ∈ segment ℝ (1,0) (0,1) ↔ z.1+z.2=1 ∧ 0≤z.1 ∧ 0≤z.2) → ((∀ (z : ℝ×ℝ), z
            ∈ segment ℝ (0,0) (0,1) ↔ z.1=0 ∧ 0≤z.2 ∧ z.2≤1) → (frontier D = segment ℝ (0,0)
            (1,0) ∪ segment ℝ (1,0) (0,1) ∪ segment ℝ (0,0) (0,1)))))) ) := by
  classical
  intro D Dopen W D_closure mem_bottom_segment mem_diagonal_segment mem_left_segment
  rw [Dopen.frontier_eq, D_closure]
  ext z
  constructor
  · rintro ⟨hzW, hnot⟩
    rcases (by simpa [W] using hzW) with ⟨hz1, hz2, hsum⟩
    have hnot' : ¬ (0<z.1 ∧ 0<z.2 ∧ z.1+z.2<1) := by simpa [D] using hnot
    rcases not_and_or.mp hnot' with h10 | h2
    · have hz10 : z.1=0 := le_antisymm (not_lt.mp h10) hz1
      exact Or.inr ((mem_left_segment z).2 ⟨hz10,hz2, by linarith⟩)
    · rcases not_and_or.mp h2 with h20 | hsum0
      · have hz20 : z.2=0 := le_antisymm (not_lt.mp h20) hz2
        exact Or.inl (Or.inl ((mem_bottom_segment z).2 ⟨hz20,hz1, by linarith⟩))
      · have hzeq : z.1+z.2=1 := le_antisymm hsum (not_lt.mp hsum0)
        exact Or.inl (Or.inr ((mem_diagonal_segment z).2 ⟨hzeq,hz1,hz2⟩))
  · intro hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · have hc := (mem_bottom_segment z).1 hz
        refine ⟨?_, ?_⟩
        · exact ⟨hc.2.1, by simp [hc.1], by linarith [hc.2.2]⟩
        · intro hD
          exact (not_lt_of_ge (by simp [hc.1] : z.2 ≤ 0)) hD.2.1
      · have hc := (mem_diagonal_segment z).1 hz
        refine ⟨?_, ?_⟩
        · exact ⟨hc.2.1, hc.2.2, le_of_eq hc.1⟩
        · intro hD
          exact (not_lt_of_ge (by linarith [hc.1])) hD.2.2
    · have hc := (mem_left_segment z).1 hz
      refine ⟨?_, ?_⟩
      · exact ⟨by simp [hc.1], hc.2.1, by linarith [hc.2.2]⟩
      · intro hD
        exact (not_lt_of_ge (by simp [hc.1] : z.1 ≤ 0)) hD.1

private theorem W_eq_stdHull :
    (by
      classical
      exact
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        let stdPts : Fin 3 → ℝ×ℝ := ![(0,0),(1,0),(0,1)]
        (Convex ℝ W) → (W = convexHull ℝ (Set.range stdPts)) ) := by
  classical
  intro W stdPts W_convex
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2≤1 := by simpa [W] using hz
    let wt : Fin 3 → ℝ := ![1-z.1-z.2,z.1,z.2]
    have hw0 : ∀ i, 0 ≤ wt i := by
      intro i
      fin_cases i <;> simp [wt] <;> linarith
    have hw1 : ∑ i, wt i = 1 := by simp [wt, Fin.sum_univ_succ]
    have hp : ∀ i, stdPts i ∈ Set.range stdPts := fun i => ⟨i,rfl⟩
    have hsum : ∑ i, wt i • stdPts i = z := by
      ext <;> simp [wt,stdPts, Fin.sum_univ_succ]
    exact mem_convexHull_of_exists_fintype wt stdPts hw0 hw1 hp hsum
  · apply convexHull_min
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      fin_cases i <;> norm_num [stdPts, W]
    · exact W_convex

private theorem region_image :
    (by
      classical
      exact
        ∀
          (delta_nonzero :
            ∀ (f : PeriodicSubtileFaceIndex),
              (P4715T1Position (SixSubtileFaceVertices f 1) -
                        P4715T1Position (SixSubtileFaceVertices f 0)).1 *
                    (P4715T1Position (SixSubtileFaceVertices f 2) -
                        P4715T1Position (SixSubtileFaceVertices f 0)).2 -
                  (P4715T1Position (SixSubtileFaceVertices f 1) -
                        P4715T1Position (SixSubtileFaceVertices f 0)).2 *
                    (P4715T1Position (SixSubtileFaceVertices f 2) -
                        P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠
                0),
          let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
            (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2);
          let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
            let d := v.1 * w.2 - v.2 * w.1
            ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d);
          ∀
            (inv_right :
              ∀ (v : ℝ × ℝ),
                ∀ (w : ℝ × ℝ),
                  ∀ (x : ℝ × ℝ), v.1 * w.2 - v.2 * w.1 ≠ 0 → lin v w (invlin v w x) = x),
            ∀
              (inv_left :
                ∀ (v : ℝ × ℝ),
                  ∀ (w : ℝ × ℝ),
                    ∀ (x : ℝ × ℝ),
                      v.1 * w.2 - v.2 * w.1 ≠ 0 → invlin v w (lin v w x) = x),
              let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
                Homeomorph (ℝ × ℝ) (ℝ × ℝ) :=
                { toFun := fun x => q + lin v w x
                  invFun := fun y => invlin v w (y - q)
                  left_inv := fun x => by simp [inv_left, hd]
                  right_inv := fun y => by simp [inv_right, hd]
                  continuous_toFun := by dsimp [lin]; fun_prop
                  continuous_invFun := by dsimp [invlin]; fun_prop };
              let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1};
              ∀ (f : PeriodicSubtileFaceIndex),
                P4715T1Region f =
                  affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0))
                      (P4715T1Position (SixSubtileFaceVertices f 1) -
                        P4715T1Position (SixSubtileFaceVertices f 0))
                      (P4715T1Position (SixSubtileFaceVertices f 2) -
                        P4715T1Position (SixSubtileFaceVertices f 0))
                      (delta_nonzero f) ''
                    D
    ) := by
  classical
  intro delta_nonzero lin invlin inv_right inv_left affineHomeo D f
  ext z
  constructor
  · rintro ⟨s,t,hs,ht,hst,rfl⟩
    refine ⟨(s,t), ⟨hs,ht,hst⟩, ?_⟩
    ext <;> simp [affineHomeo, lin] <;> ring
  · rintro ⟨⟨s,t⟩, ⟨hs,ht,hst⟩, hz⟩
    refine ⟨s,t,hs,ht,hst, ?_⟩
    calc
      z = affineHomeo
          (P4715T1Position (SixSubtileFaceVertices f 0))
          (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
              (SixSubtileFaceVertices f 0))
          (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
              (SixSubtileFaceVertices f 0))
          (delta_nonzero f) (s,t) := hz.symm
      _ = _ := by ext <;> simp [affineHomeo, lin] <;> ring

private theorem W_decomp :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (IsOpen D) → (
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        (D ⊆ W) → ((closure D = W) → (W = D ∪ frontier D))) ) := by
  classical
  intro D Dopen W D_subset_W D_closure
  rw [Dopen.frontier_eq, D_closure]
  ext z
  constructor
  · intro hz
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · exact Or.inr ⟨hz,hzD⟩
  · rintro (hzD | ⟨hzW, hzNot⟩)
    · exact D_subset_W hzD
    · exact hzW

private theorem triangle_image :
    (by
      classical
      exact
        ∀ (delta_nonzero : ∀ (f : PeriodicSubtileFaceIndex), (P4715T1Position
            (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices f 0)).1 *
            (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
            (SixSubtileFaceVertices f 0)).2 - (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)).2 * (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠ 0),
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        let stdPts : Fin 3 → ℝ×ℝ := ![(0,0),(1,0),(0,1)]
        let affineLin (v w : ℝ×ℝ) : (ℝ×ℝ) →ₗ[ℝ] (ℝ×ℝ) := {
          toFun := lin v w
          map_add' := by intro x y; ext <;> simp [lin] <;> ring
          map_smul' := by intro c x; ext <;> simp [lin] <;> ring
        }
        let affineMapTri (q v w : ℝ×ℝ) : AffineMap ℝ (ℝ×ℝ) (ℝ×ℝ) := {
          toFun := fun x => q + lin v w x
          linear := affineLin v w
          map_vadd' := by intro x y; ext <;> simp [affineLin,lin] <;> ring
        }
        (∀ (q : ℝ×ℝ), ∀ (v : ℝ×ℝ), ∀ (w : ℝ×ℝ), convexHull ℝ (affineMapTri q v w '' Set.range
            stdPts) = affineMapTri q v w '' W) → (∀ (f : PeriodicSubtileFaceIndex), convexHull ℝ
            (P4715T1Position '' Set.range (SixSubtileFaceVertices f)) = affineHomeo
            (P4715T1Position (SixSubtileFaceVertices f 0)) (P4715T1Position
            (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices f 0))
            (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
            (SixSubtileFaceVertices f 0)) (delta_nonzero f) '' W) ) := by
  classical
  intro delta_nonzero lin invlin inv_right inv_left affineHomeo W stdPts affineLin affineMapTri
      hull_affine f
  let q := P4715T1Position (SixSubtileFaceVertices f 0)
  let v := P4715T1Position (SixSubtileFaceVertices f 1) - q
  let w := P4715T1Position (SixSubtileFaceVertices f 2) - q
  have hv (i : Fin 3) : affineMapTri q v w (stdPts i) =
      P4715T1Position (SixSubtileFaceVertices f i) := by
    fin_cases i <;> ext <;> simp [affineMapTri, affineLin, lin, stdPts, q, v, w]
  have himage : affineMapTri q v w '' Set.range stdPts =
      P4715T1Position '' Set.range (SixSubtileFaceVertices f) := by
    ext z
    constructor
    · rintro ⟨x,⟨i,rfl⟩,rfl⟩
      exact ⟨SixSubtileFaceVertices f i, ⟨i,rfl⟩, (hv i).symm⟩
    · rintro ⟨x,⟨i,rfl⟩,rfl⟩
      exact ⟨stdPts i, ⟨i,rfl⟩, hv i⟩
  have hmap : (affineMapTri q v w : (ℝ×ℝ) → ℝ×ℝ) =
      affineHomeo q v w (delta_nonzero f) := by
    funext x
    rfl
  rw [← himage, hull_affine]
  rw [hmap]

private theorem hconnected :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        (∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ 0) → (∀ (delta_nonzero : ∀ (f :
            PeriodicSubtileFaceIndex), (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 * (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0)).2 -
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)).2 * (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠ 0),
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (Convex ℝ D) → ((D.Nonempty) → ((∀ (f : PeriodicSubtileFaceIndex), (faceDet f ≠ 0) →
            (P4715T1Region f = affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0))
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)) (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)) (delta_nonzero f) '' D)) → (∀ f,
                IsConnected (P4715T1Region f)))))) := by
  classical
  intro faceDet faceDet_nonzero delta_nonzero lin invlin inv_right inv_left affineHomeo D Dconvex
      D_nonempty region_image f
  rw [region_image f (faceDet_nonzero f)]
  exact (Dconvex.isConnected D_nonempty).image _
    (affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0))
      (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
          (SixSubtileFaceVertices f 0))
      (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
          (SixSubtileFaceVertices f 0))
      (delta_nonzero f)).continuous.continuousOn

private theorem triangle_decomp :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        (∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ 0) → (∀ (delta_nonzero : ∀ (f :
            PeriodicSubtileFaceIndex), (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 * (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0)).2 -
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)).2 * (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠ 0),
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        (frontier D = segment ℝ (0,0) (1,0) ∪ segment ℝ (1,0) (0,1) ∪ segment ℝ (0,0) (0,1)) →
            ((∀ (q : ℝ×ℝ), ∀ (v : ℝ×ℝ), ∀ (w : ℝ×ℝ), ∀ (hd : v.1*w.2-v.2*w.1≠0), ∀ (x : ℝ×ℝ), ∀
                (y : ℝ×ℝ), affineHomeo q v w hd '' segment ℝ x y = segment ℝ (affineHomeo q v w
                hd x)
            (affineHomeo q v w hd y)) → ((∀ (f : PeriodicSubtileFaceIndex), (faceDet f ≠ 0) →
            (P4715T1Region f = affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0))
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)) (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)) (delta_nonzero f) '' D)) → ((W = D ∪
            frontier D) → ((∀ (f : PeriodicSubtileFaceIndex), convexHull ℝ (P4715T1Position ''
            Set.range (SixSubtileFaceVertices f)) = affineHomeo (P4715T1Position
            (SixSubtileFaceVertices f 0)) (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)) (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0))
            (delta_nonzero f) '' W) → (∀ (f : PeriodicSubtileFaceIndex), (convexHull ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' Set.range (SixSubtileFaceVertices f)) =
            P4715T1Region f ∪ (P4715T1Arc (SixSubtileFaceVertices f (0 : Fin (3 : ℕ)))
            (SixSubtileFaceVertices f (1 : Fin (3 : ℕ))) ∪ P4715T1Arc (SixSubtileFaceVertices f
            (1 : Fin (3 : ℕ))) (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) ∪ P4715T1Arc
            (SixSubtileFaceVertices f (2 : Fin (3 : ℕ))) (SixSubtileFaceVertices f (0 : Fin (3 :
            ℕ))))))))))) := by
  classical
  intro faceDet faceDet_nonzero delta_nonzero lin invlin inv_right inv_left affineHomeo D W
      D_frontier image_segment region_image W_decomp triangle_image f
  let q := P4715T1Position (SixSubtileFaceVertices f 0)
  let v := P4715T1Position (SixSubtileFaceVertices f 1) - q
  let w := P4715T1Position (SixSubtileFaceVertices f 2) - q
  let E := affineHomeo q v w (delta_nonzero f)
  rw [triangle_image f, W_decomp, Set.image_union]
  rw [region_image f (faceDet_nonzero f), D_frontier]
  rw [Set.image_union, Set.image_union]
  rw [image_segment q v w (delta_nonzero f), image_segment q v w (delta_nonzero f),
    image_segment q v w (delta_nonzero f)]
  have e0 : E (0,0) = P4715T1Position (SixSubtileFaceVertices f 0) := by
    simp [E, affineHomeo, lin, q]
  have e1 : E (1,0) = P4715T1Position (SixSubtileFaceVertices f 1) := by
    ext <;> simp [E, affineHomeo, lin, q, v]
  have e2 : E (0,1) = P4715T1Position (SixSubtileFaceVertices f 2) := by
    ext <;> simp [E, affineHomeo, lin, q, w]
  simp only [P4715T1Arc]
  rw [e0, e1, e2]
  rw [segment_symm ℝ (P4715T1Position (SixSubtileFaceVertices f 2))
    (P4715T1Position (SixSubtileFaceVertices f 0))]

private theorem std_edge_disjoint :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (∀ (z : ℝ×ℝ), z ∈ segment ℝ (0,0) (1,0) ↔ z.2=0 ∧ 0≤z.1 ∧ z.1≤1) → ((∀ (z : ℝ×ℝ), z ∈
            segment ℝ (1,0) (0,1) ↔ z.1+z.2=1 ∧ 0≤z.1 ∧ 0≤z.2) → ((∀ (z : ℝ×ℝ), z ∈ segment ℝ
            (0,0) (0,1) ↔ z.1=0 ∧ 0≤z.2 ∧ z.2≤1) → (
        let stdPts : Fin 3 → ℝ×ℝ := ![(0,0),(1,0),(0,1)]
        ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j → Disjoint D (segment ℝ (stdPts i)
            (stdPts j))))) ) := by
  classical
  intro D mem_bottom_segment mem_diagonal_segment mem_left_segment stdPts i j hij
  rw [Set.disjoint_left]
  intro z hzD hzS
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have hc := (mem_bottom_segment z).mp (by simpa [stdPts] using hzS)
    exact (not_lt_of_ge (by simp [hc.1] : z.2 ≤ 0)) hzD.2.1
  · have hc := (mem_left_segment z).mp (by simpa [stdPts] using hzS)
    exact (not_lt_of_ge (by simp [hc.1] : z.1 ≤ 0)) hzD.1
  · have hc := (mem_bottom_segment z).mp (by simpa [stdPts, segment_symm ℝ] using hzS)
    exact (not_lt_of_ge (by simp [hc.1] : z.2 ≤ 0)) hzD.2.1
  · exact (hij rfl).elim
  · have hc := (mem_diagonal_segment z).mp (by simpa [stdPts] using hzS)
    exact (not_lt_of_ge (le_of_eq hc.1.symm)) hzD.2.2
  · have hc := (mem_left_segment z).mp (by simpa [stdPts, segment_symm ℝ] using hzS)
    exact (not_lt_of_ge (by simp [hc.1] : z.1 ≤ 0)) hzD.1
  · have hc := (mem_diagonal_segment z).mp (by simpa [stdPts, segment_symm ℝ] using hzS)
    exact (not_lt_of_ge (le_of_eq hc.1.symm)) hzD.2.2
  · exact (hij rfl).elim

private theorem region_disjoint_arc :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        (∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ 0) → (∀ (delta_nonzero : ∀ (f :
            PeriodicSubtileFaceIndex), (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 * (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0)).2 -
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)).2 * (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠ 0),
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (∀ (q : ℝ×ℝ), ∀ (v : ℝ×ℝ), ∀ (w : ℝ×ℝ), ∀ (hd : v.1*w.2-v.2*w.1≠0), ∀ (x : ℝ×ℝ), ∀ (y :
            ℝ×ℝ), affineHomeo q v w hd '' segment ℝ x y = segment ℝ (affineHomeo q v w hd x)
            (affineHomeo q v w hd y)) → (
        let stdPts : Fin 3 → ℝ×ℝ := ![(0,0),(1,0),(0,1)]
        (∀ (f : PeriodicSubtileFaceIndex), (faceDet f ≠ 0) → (P4715T1Region f = affineHomeo
            (P4715T1Position (SixSubtileFaceVertices f 0)) (P4715T1Position
            (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices f 0))
            (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
            (SixSubtileFaceVertices f 0)) (delta_nonzero f) '' D)) → ((∀ (i : Fin 3), ∀ (j : Fin
            3), (i ≠ j) → (Disjoint D (segment ℝ (stdPts i) (stdPts j)))) → (∀ (f :
                PeriodicSubtileFaceIndex), ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j →
                Disjoint
            (P4715T1Region f) (P4715T1Arc (SixSubtileFaceVertices f i)
            (SixSubtileFaceVertices f j))))))) := by
  classical
  intro faceDet faceDet_nonzero delta_nonzero lin invlin inv_right inv_left affineHomeo D
      image_segment stdPts region_image std_edge_disjoint f i j hij
  let q := P4715T1Position (SixSubtileFaceVertices f 0)
  let v := P4715T1Position (SixSubtileFaceVertices f 1) - q
  let w := P4715T1Position (SixSubtileFaceVertices f 2) - q
  let E := affineHomeo q v w (delta_nonzero f)
  have hstd (r : Fin 3) : E (stdPts r) =
      P4715T1Position (SixSubtileFaceVertices f r) := by
    fin_cases r <;> ext <;> simp [stdPts, E, affineHomeo, lin, q, v, w]
  rw [Set.disjoint_left]
  intro z hzR hzA
  rw [region_image f (faceDet_nonzero f)] at hzR
  change z ∈ segment ℝ
    (P4715T1Position (SixSubtileFaceVertices f i))
    (P4715T1Position (SixSubtileFaceVertices f j)) at hzA
  rw [← hstd i, ← hstd j] at hzA
  rw [← image_segment q v w (delta_nonzero f) (stdPts i) (stdPts j)] at hzA
  rcases hzR with ⟨x, hxD, rfl⟩
  rcases hzA with ⟨y, hyS, hxy⟩
  have hxy' : x = y := E.injective hxy.symm
  subst y
  exact (Set.disjoint_left.mp (std_edge_disjoint i j hij)) hxD hyS

private theorem region_shift :
    (by
      classical
      exact
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        let bary (f : PeriodicSubtileFaceIndex) (s t : Real) : ℝ × ℝ :=
          (1 - s - t) • P4715T1Position (SixSubtileFaceVertices f 0) +
            s • P4715T1Position (SixSubtileFaceVertices f 1) +
            t • P4715T1Position (SixSubtileFaceVertices f 2)
        (∀ (k : Int × Int), ∀ (j : Fin 12), ∀ (s : Real), ∀ (t : Real), bary (P4715T1FaceShift
            k (P4715T1PatchFaces j)) s t = translation k (bary (P4715T1PatchFaces j) s t)) →
            (∀ (k : ℤ × ℤ), ∀ (j : Fin (12 : ℕ)), P4715T1Region (P4715T1FaceShift k
            (P4715T1PatchFaces j)) = (⇑(translation k) : ℝ × ℝ → ℝ × ℝ) '' P4715T1Region
            (P4715T1PatchFaces j)) ) := by
  classical
  intro translation bary bary_shift k j
  ext z
  constructor
  · rintro ⟨s,t,hs,ht,hst,hz⟩
    refine ⟨bary (P4715T1PatchFaces j) s t,
      ⟨s,t,hs,ht,hst,rfl⟩, ?_⟩
    change z = bary (P4715T1FaceShift k (P4715T1PatchFaces j)) s t at hz
    rw [bary_shift] at hz
    exact hz.symm
  · rintro ⟨y, ⟨s,t,hs,ht,hst,hy⟩, hz⟩
    subst y
    refine ⟨s,t,hs,ht,hst, ?_⟩
    change z = bary (P4715T1FaceShift k (P4715T1PatchFaces j)) s t
    rw [bary_shift]
    exact hz.symm

private theorem translated_triangle :
    (by
      classical
      exact
        (∀ (k : Int × Int), ∀ (a : PeriodicSubtileIndex), P4715T1Position
            (P4715T1VertexShift k a) = P4715T1Position a + ((k.1 : Real), (k.2 : Real))) →
                ((∀ (k : Int × Int), ∀ (j : Fin 12), ∀ (i : Fin 3), SixSubtileFaceVertices
                (P4715T1FaceShift k (P4715T1PatchFaces j)) i =
            P4715T1VertexShift k (SixSubtileFaceVertices (P4715T1PatchFaces j) i)) → (
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        ∀ (k : ℤ × ℤ), ∀ (j : Fin (12 : ℕ)), (⇑(translation k) : ℝ × ℝ → ℝ × ℝ) '' (convexHull ℝ
            : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' Set.range (SixSubtileFaceVertices
            (P4715T1PatchFaces j))) = (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (P4715T1Position '' Set.range (SixSubtileFaceVertices (P4715T1FaceShift k
            (P4715T1PatchFaces j))))))) := by
  classical
  intro position_shift face_vertex_shift translation k j
  rw [AffineMap.image_convexHull]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨a, ⟨i, rfl⟩, rfl⟩, rfl⟩
    exact ⟨SixSubtileFaceVertices (P4715T1FaceShift k (P4715T1PatchFaces j)) i,
      ⟨i, rfl⟩, by dsimp [translation]; rw [face_vertex_shift, position_shift]⟩
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    refine ⟨P4715T1Position (SixSubtileFaceVertices (P4715T1PatchFaces j) i),
      ⟨SixSubtileFaceVertices (P4715T1PatchFaces j) i, ⟨i, rfl⟩, rfl⟩, ?_⟩
    dsimp [translation]
    rw [face_vertex_shift, position_shift]

private theorem region_subset_tile :
    (by
      classical
      exact
        (⋃ (j : Fin (12 : ℕ)), (fun (j : Fin (12 : ℕ)) => (convexHull ℝ : Set (ℝ × ℝ)
            → Set (ℝ × ℝ)) (P4715T1Position '' (fun (j : Fin (12 : ℕ)) => Set.range
            (SixSubtileFaceVertices (P4715T1PatchFaces j))) j)) j = P4715T1Hexagon) → ((∀ (f
                : PeriodicSubtileFaceIndex), P4715T1Region f ⊆
            convexHull ℝ (P4715T1Position '' Set.range (SixSubtileFaceVertices f))) → (
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        (∀ (k : Int × Int), ∀ (j : Fin 12), translation k '' convexHull ℝ (P4715T1Position ''
            Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) = convexHull ℝ
            (P4715T1Position '' Set.range (SixSubtileFaceVertices (P4715T1FaceShift k
            (P4715T1PatchFaces j))))) → (∀ (k : ℤ × ℤ), ∀ (j : Fin (12 : ℕ)), P4715T1Region
            (P4715T1FaceShift k (P4715T1PatchFaces j)) ⊆ (⇑(translation k) : ℝ × ℝ → ℝ × ℝ)
            '' P4715T1Hexagon)))) := by
  classical
  intro hpatch region_subset_triangle translation translated_triangle k j z hz
  have hzTri := region_subset_triangle (P4715T1FaceShift k (P4715T1PatchFaces j)) hz
  rw [← translated_triangle k j] at hzTri
  rcases hzTri with ⟨y, hyK, rfl⟩
  have hyHex : y ∈ P4715T1Hexagon := by
    rw [← hpatch]
    exact Set.mem_iUnion.mpr ⟨j, hyK⟩
  exact ⟨y, hyHex, rfl⟩

private theorem common_hull_subset_arc :
    (by
      classical
      exact
        (∀ (i : Fin 12), ∀ (j : Fin 12), (i ≠ j) → (∃ a b : Fin 3, a ≠ b ∧ ∀ r : Fin 3,
            SixSubtileFaceVertices (P4715T1PatchFaces i) r ∈ Set.range (SixSubtileFaceVertices
            (P4715T1PatchFaces j)) → r = a ∨ r = b)) → (∀ (i : Fin (12 : ℕ)), ∀ (j : Fin (12 :
            ℕ)), i ≠ j → ∃ (a : Fin (3 : ℕ)) (b : Fin (3 : ℕ)), a ≠ b ∧ (convexHull ℝ : Set (ℝ ×
            ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' (Set.range (SixSubtileFaceVertices
            (P4715T1PatchFaces i)) ∩ Set.range (SixSubtileFaceVertices (P4715T1PatchFaces
            j)))) ⊆ P4715T1Arc (SixSubtileFaceVertices (P4715T1PatchFaces i) a)
            (SixSubtileFaceVertices (P4715T1PatchFaces i) b)) ) := by
  classical
  intro common_edge i j hij
  obtain ⟨a,b,hab,hcommon⟩ := common_edge i j hij
  refine ⟨a,b,hab, ?_⟩
  rw [P4715T1Arc]
  rw [← convexHull_pair]
  apply convexHull_mono
  intro z hz
  rcases hz with ⟨u, hu, rfl⟩
  rcases hu with ⟨hu1, hu2⟩
  rcases Set.mem_range.mp hu1 with ⟨r, hr⟩
  have hmem : SixSubtileFaceVertices (P4715T1PatchFaces i) r ∈
      Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j)) := by
    simpa [hr] using hu2
  rw [← hr]
  rcases hcommon r hmem with h | h
  · rw [h]
    simp
  · rw [h]
    simp

private theorem plane_cover :
    (by
      classical
      exact
        (⋃ (k : ℤ × ℤ), (fun (p : ℝ × ℝ) => p + ((↑k.1 : ℝ), (↑k.2 : ℝ))) ''
            P4715T1Hexagon = Set.univ) → ((⋃ (j : Fin (12 : ℕ)), (fun (j : Fin (12 :
            ℕ)) => (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' (fun (j : Fin
            (12 : ℕ)) => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) j)) j =
            P4715T1Hexagon) → ((∀ (f : PeriodicSubtileFaceIndex), ∀ (i : Fin (3 :
            ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j → AllowedSubtileIncidence (SixSubtileFaceVertices f
            i) (SixSubtileFaceVertices f j)) → ((∀ (f : PeriodicSubtileFaceIndex), convexHull ℝ
                (P4715T1Position '' Set.range
            (SixSubtileFaceVertices f)) = P4715T1Region f ∪ ( P4715T1Arc
            (SixSubtileFaceVertices f 0) (SixSubtileFaceVertices f 1) ∪ P4715T1Arc
            (SixSubtileFaceVertices f 1) (SixSubtileFaceVertices f 2) ∪ P4715T1Arc
            (SixSubtileFaceVertices f 2) (SixSubtileFaceVertices f 0))) → (
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        (∀ (k : Int × Int), ∀ (j : Fin 12), translation k '' convexHull ℝ (P4715T1Position ''
            Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) = convexHull ℝ
            (P4715T1Position '' Set.range (SixSubtileFaceVertices (P4715T1FaceShift k
            (P4715T1PatchFaces j))))) → (Set.range P4715T1Position ∪ {p | ∃ a b,
            AllowedSubtileIncidence a b ∧ p ∈ P4715T1Arc a b} ∪ {p | ∃ f, p ∈ P4715T1Region
            f} = Set.univ)))))) := by
  classical
  intro hcover hpatch hallowed triangle_decomp translation translated_triangle
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    have hphex : p ∈ ⋃ k : Int × Int,
        (fun x : ℝ × ℝ => x + ((k.1 : Real), (k.2 : Real))) '' P4715T1Hexagon := by
      rw [hcover]
      exact Set.mem_univ p
    rcases Set.mem_iUnion.mp hphex with ⟨k, ⟨x, hx, rfl⟩⟩
    rw [← hpatch] at hx
    have hxpatch : x ∈ ⋃ j : Fin 12,
        convexHull ℝ (P4715T1Position '' Set.range
          (SixSubtileFaceVertices (P4715T1PatchFaces j))) := by
      exact hx
    rcases Set.mem_iUnion.mp hxpatch with ⟨j, hxK⟩
    let f := P4715T1FaceShift k (P4715T1PatchFaces j)
    have hpK : translation k x ∈ convexHull ℝ
        (P4715T1Position '' Set.range (SixSubtileFaceVertices f)) := by
      rw [← translated_triangle k j]
      exact ⟨x, hxK, rfl⟩
    rw [triangle_decomp f] at hpK
    rcases hpK with hpR | hpSide
    · exact Or.inr ⟨f, hpR⟩
    · rcases hpSide with hp12or01 | hp20
      · rcases hp12or01 with hp01 | hp12
        · exact Or.inl (Or.inr ⟨SixSubtileFaceVertices f 0,
            SixSubtileFaceVertices f 1, hallowed f 0 1 (by decide), hp01⟩)
        · exact Or.inl (Or.inr ⟨SixSubtileFaceVertices f 1,
            SixSubtileFaceVertices f 2, hallowed f 1 2 (by decide), hp12⟩)
      · exact Or.inl (Or.inr ⟨SixSubtileFaceVertices f 2,
          SixSubtileFaceVertices f 0, hallowed f 2 0 (by decide), hp20⟩)

private theorem pairwise_regions :
    (by
      classical
      exact
        (Pairwise fun (k l : ℤ × ℤ) => Disjoint (interior ((fun (p : ℝ × ℝ) => p +
            ((↑k.1 : ℝ), (↑k.2 : ℝ))) '' P4715T1Hexagon)) (interior ((fun (p : ℝ × ℝ) => p +
            ((↑l.1 : ℝ), (↑l.2 : ℝ))) '' P4715T1Hexagon))) → ((∀ (i : Fin (12 : ℕ)), ∀ (j : Fin
                (12 : ℕ)), i ≠ j → (fun (j : Fin (12 : ℕ)) => (convexHull ℝ : Set (ℝ × ℝ) →
            Set (ℝ × ℝ)) (P4715T1Position '' (fun (j : Fin (12 : ℕ)) => Set.range
            (SixSubtileFaceVertices (P4715T1PatchFaces j))) j)) i ∩ (fun (j : Fin (12 : ℕ)) =>
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' (fun (j : Fin (12 :
            ℕ)) => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) j)) j =
            (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (P4715T1Position '' ((fun (j : Fin (12 :
            ℕ)) => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) i ∩ (fun (j : Fin
            (12 : ℕ)) => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) j))) → ((∀
                f, IsOpen (P4715T1Region f)) → ((∀ (f : PeriodicSubtileFaceIndex),
                P4715T1Region f ⊆ convexHull ℝ (P4715T1Position ''
            Set.range (SixSubtileFaceVertices f))) → ((∀ (f : PeriodicSubtileFaceIndex), ∀ (i :
                Fin 3), ∀ (j : Fin 3), (i ≠ j) → (Disjoint
            (P4715T1Region f) (P4715T1Arc (SixSubtileFaceVertices f i)
            (SixSubtileFaceVertices f j)))) → (
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        (∀ (k : Int × Int), ∀ (j : Fin 12), P4715T1Region (P4715T1FaceShift k
            (P4715T1PatchFaces j)) = translation k '' P4715T1Region (P4715T1PatchFaces j))
            → ((∀ (k : Int × Int), ∀ (j : Fin 12), P4715T1Region (P4715T1FaceShift k
            (P4715T1PatchFaces j)) ⊆ translation k '' P4715T1Hexagon) → ((∀ (i : Fin 12), ∀
                (j : Fin 12), (i ≠ j) → (∃ a b : Fin 3, a ≠ b ∧ convexHull ℝ (P4715T1Position ''
            (Set.range (SixSubtileFaceVertices (P4715T1PatchFaces i)) ∩ Set.range
            (SixSubtileFaceVertices (P4715T1PatchFaces j))) ) ⊆ P4715T1Arc
            (SixSubtileFaceVertices (P4715T1PatchFaces i) a) (SixSubtileFaceVertices
            (P4715T1PatchFaces i) b))) → ((∀ (k : Int × Int), Function.Injective (translation
            k)) → (Pairwise fun f g => Disjoint (P4715T1Region f) (P4715T1Region g)))))))))))
                := by
  classical
  intro hdisj hlocal hopen region_subset_triangle region_disjoint_arc translation region_shift
      region_subset_tile common_hull_subset_arc translation_injective f g hfg
  rw [Set.disjoint_left]
  intro x hxf hxg
  obtain ⟨af, haf, _⟩ := P4715T1PatchEnumeration f
  obtain ⟨ag, hag, _⟩ := P4715T1PatchEnumeration g
  rcases af with ⟨k,j⟩
  rcases ag with ⟨l,i⟩
  by_cases hkl : k = l
  · subst l
    have hji : j ≠ i := by
      intro hji
      apply hfg
      calc
        f = P4715T1FaceShift k (P4715T1PatchFaces j) := haf.symm
        _ = P4715T1FaceShift k (P4715T1PatchFaces i) := by rw [hji]
        _ = g := hag
    rw [← haf, region_shift k j] at hxf
    rw [← hag, region_shift k i] at hxg
    rcases hxf with ⟨y, hyf, hxy⟩
    rcases hxg with ⟨y', hyg, hxy'⟩
    have hyy : y = y' := translation_injective k (hxy.trans hxy'.symm)
    subst y'
    have hyK : y ∈
        convexHull ℝ (P4715T1Position '' Set.range
          (SixSubtileFaceVertices (P4715T1PatchFaces j))) ∩
        convexHull ℝ (P4715T1Position '' Set.range
          (SixSubtileFaceVertices (P4715T1PatchFaces i))) := by
      exact ⟨region_subset_triangle _ hyf, region_subset_triangle _ hyg⟩
    rw [hlocal j i hji] at hyK
    obtain ⟨a,b,hab,hside⟩ := common_hull_subset_arc j i hji
    exact (Set.disjoint_left.mp
      (region_disjoint_arc (P4715T1PatchFaces j) a b hab)) hyf (hside hyK)
  · have hsubf : P4715T1Region f ⊆
        translation k '' P4715T1Hexagon := by
      rw [← haf]
      exact region_subset_tile k j
    have hsubg : P4715T1Region g ⊆
        translation l '' P4715T1Hexagon := by
      rw [← hag]
      exact region_subset_tile l i
    have hxk : x ∈ interior (translation k '' P4715T1Hexagon) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset ((hopen f).mem_nhds hxf) hsubf)
    have hxl : x ∈ interior (translation l '' P4715T1Hexagon) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset ((hopen g).mem_nhds hxg) hsubg)
    exact (Set.disjoint_left.mp (hdisj hkl)) hxk hxl

end CoefficientFaceProof

namespace CoefficientFaceTopology

private theorem position_shift :
    (by
      classical
      exact
        ∀ (k : ℤ × ℤ), ∀ (a : PeriodicSubtileIndex), P4715T1Position (P4715T1VertexShift k a)
            = P4715T1Position a + ((↑k.1 : ℝ), (↑k.2 : ℝ)) ) := by
  classical
  intro k a
  rcases a with ⟨l, m, n⟩
  change ((((m + k.1 : Int) : Real), ((n + k.2 : Int) : Real)) + P4715T1Offsets l) =
    ((((m : Real), (n : Real)) + P4715T1Offsets l) + ((k.1 : Real), (k.2 : Real)))
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;> ring

private theorem face_vertex_shift :
    (by
      classical
      exact
        ∀ (k : ℤ × ℤ), ∀ (j : Fin (12 : ℕ)), ∀ (i : Fin (3 : ℕ)), SixSubtileFaceVertices
            (P4715T1FaceShift k (P4715T1PatchFaces j)) i = P4715T1VertexShift k
            (SixSubtileFaceVertices (P4715T1PatchFaces j) i) ) := by
  classical
  intro k j i
  rcases k with ⟨m,n⟩
  fin_cases j <;> fin_cases i <;>
    simp [P4715T1FaceShift, P4715T1VertexShift, P4715T1PatchFaces,
      SixSubtileFaceVertices] <;> omega

private theorem faceDet_nonzero :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        ∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ (0 : ℝ) ) := by
  classical
  intro faceDet f
  rcases f with ⟨l, m, n⟩
  cases l <;> simp [faceDet, P4715T1Position, P4715T1Offsets,
    SixSubtileFaceVertices] <;> ring_nf <;> norm_num

private theorem inv_right :
    (by
      classical
      exact
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), v.1 * w.2 - v.2 * w.1 ≠ (0 : ℝ) → lin v w
            (invlin v w x) = x ) := by
  classical
  intro lin invlin v w x hd
  dsimp [lin, invlin]
  have hd' : w.2 * v.1 - w.1 * v.2 ≠ 0 := by simpa [mul_comm] using hd
  apply Prod.ext <;> field_simp [hd'] <;> ring

private theorem inv_left :
    (by
      classical
      exact
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), v.1 * w.2 - v.2 * w.1 ≠ (0 : ℝ) → invlin v w
            (lin v w x) = x ) := by
  classical
  intro lin invlin v w x hd
  dsimp [lin, invlin]
  have hd' : v.1 * w.2 - w.1 * v.2 ≠ 0 := by simpa [mul_comm] using hd
  apply Prod.ext <;> field_simp [hd'] <;> ring

private theorem Dopen :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        IsOpen D ) := by
  classical
  intro D
  change IsOpen ({x : ℝ × ℝ | 0 < x.1} ∩
    ({x | 0 < x.2} ∩ {x | x.1 + x.2 < 1}))
  apply (isOpen_lt continuous_const continuous_fst).inter
  apply (isOpen_lt continuous_const continuous_snd).inter
  exact isOpen_lt (continuous_fst.add continuous_snd) continuous_const

private theorem D_nonempty :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        D.Nonempty ) := by
  classical
  intro D
  refine ⟨(1/3,1/3), ?_⟩
  norm_num [D]

private theorem D_subset_W :
    (by
      classical
      exact
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        D ⊆ W ) := by
  classical
  intro D W z hz
  exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩

private theorem W_closed :
    (by
      classical
      exact
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        IsClosed W ) := by
  classical
  intro W
  change IsClosed ({z : ℝ × ℝ | 0 ≤ z.1} ∩
    ({z | 0 ≤ z.2} ∩ {z | z.1+z.2 ≤ 1}))
  apply (isClosed_Ici.preimage continuous_fst).inter
  apply (isClosed_Ici.preimage continuous_snd).inter
  exact isClosed_Iic.preimage (continuous_fst.add continuous_snd)

private theorem image_segment :
    (by
      classical
      exact
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        ∀ (q : ℝ × ℝ), ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (hd : v.1 * w.2 - v.2 * w.1 ≠ (0 : ℝ)), ∀
            (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), (⇑(affineHomeo q v w hd) : ℝ × ℝ → ℝ × ℝ) '' segment ℝ x
            y = segment ℝ ((affineHomeo q v w hd : ℝ × ℝ → ℝ × ℝ) x) ((affineHomeo q v w hd : ℝ ×
            ℝ → ℝ × ℝ) y) ) := by
  classical
  intro lin invlin inv_right inv_left affineHomeo q v w hd x y
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  simp only [Set.image_image]
  congr 1
  funext t
  ext <;> simp [affineHomeo, lin, AffineMap.lineMap_apply] <;> ring

private theorem W_convex :
    (by
      classical
      exact
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        Convex ℝ W ) := by
  classical
  intro W x hx y hy a b ha hb hab
  dsimp [W] at hx hy ⊢
  constructor
  · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
  · constructor
    · nlinarith [mul_nonneg ha hx.2.1, mul_nonneg hb hy.2.1]
    · nlinarith [mul_nonneg ha (by linarith [hx.2.2] : 0 ≤ 1-(x.1+x.2)),
        mul_nonneg hb (by linarith [hy.2.2] : 0 ≤ 1-(y.1+y.2))]

private theorem hull_affine :
    (by
      classical
      exact
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let W : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}
        let stdPts : Fin 3 → ℝ×ℝ := ![(0,0),(1,0),(0,1)]
        (W = convexHull ℝ (Set.range stdPts)) → (
        let affineLin (v w : ℝ×ℝ) : (ℝ×ℝ) →ₗ[ℝ] (ℝ×ℝ) := {
          toFun := lin v w
          map_add' := by intro x y; ext <;> simp [lin] <;> ring
          map_smul' := by intro c x; ext <;> simp [lin] <;> ring
        }
        let affineMapTri (q v w : ℝ×ℝ) : AffineMap ℝ (ℝ×ℝ) (ℝ×ℝ) := {
          toFun := fun x => q + lin v w x
          linear := affineLin v w
          map_vadd' := by intro x y; ext <;> simp [affineLin,lin] <;> ring
        }
        ∀ (q : ℝ × ℝ), ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            ((⇑(affineMapTri q v w) : ℝ × ℝ → ℝ × ℝ) '' Set.range stdPts) = (⇑(affineMapTri q v
            w) : ℝ × ℝ → ℝ × ℝ) '' W)) := by
  classical
  intro lin W stdPts W_eq_stdHull affineLin affineMapTri q v w
  rw [W_eq_stdHull, AffineMap.image_convexHull]

private theorem hopen :
    (by
      classical
      exact
        let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
          let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
          let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
          let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
          p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
            p1.2 * p0.1 + p0.2 * p2.1
        (∀ (f : PeriodicSubtileFaceIndex), faceDet f ≠ 0) → (∀ (delta_nonzero : ∀ (f :
            PeriodicSubtileFaceIndex), (P4715T1Position (SixSubtileFaceVertices f 1) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 * (P4715T1Position
            (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices f 0)).2 -
            (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position
            (SixSubtileFaceVertices f 0)).2 * (P4715T1Position (SixSubtileFaceVertices f 2) -
            P4715T1Position (SixSubtileFaceVertices f 0)).1 ≠ 0),
        let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
        let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
          let d := v.1 * w.2 - v.2 * w.1
          ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
        ∀ (inv_right : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ × ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) →
            (lin v w (invlin v w x) = x)), ∀ (inv_left : ∀ (v : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (x : ℝ ×
            ℝ), (v.1 * w.2 - v.2 * w.1 ≠ 0) → (invlin v w (lin v w x) = x)),
        let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
            Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => q + lin v w x
          invFun := fun y => invlin v w (y - q)
          left_inv := fun x => by simp [inv_left, hd]
          right_inv := fun y => by simp [inv_right, hd]
          continuous_toFun := by dsimp [lin]; fun_prop
          continuous_invFun := by dsimp [invlin]; fun_prop
        }
        let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
        (IsOpen D) → ((∀ (f : PeriodicSubtileFaceIndex), (faceDet f ≠ 0) → (P4715T1Region f =
            affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0)) (P4715T1Position
            (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices f 0))
            (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position
            (SixSubtileFaceVertices f 0)) (delta_nonzero f) '' D)) → (∀ f, IsOpen
            (P4715T1Region f))))) := by
  classical
  intro faceDet faceDet_nonzero delta_nonzero lin invlin inv_right inv_left affineHomeo D Dopen
      region_image f
  rw [region_image f (faceDet_nonzero f)]
  exact (affineHomeo (P4715T1Position (SixSubtileFaceVertices f 0))
    (P4715T1Position (SixSubtileFaceVertices f 1) - P4715T1Position (SixSubtileFaceVertices
        f 0))
    (P4715T1Position (SixSubtileFaceVertices f 2) - P4715T1Position (SixSubtileFaceVertices
        f 0))
    (delta_nonzero f)).isOpen_image.mpr Dopen

private theorem region_subset_triangle :
    (by
      classical
      exact
        (∀ (f : PeriodicSubtileFaceIndex), convexHull ℝ (P4715T1Position '' Set.range
            (SixSubtileFaceVertices f)) = P4715T1Region f ∪ ( P4715T1Arc
            (SixSubtileFaceVertices f 0) (SixSubtileFaceVertices f 1) ∪ P4715T1Arc
            (SixSubtileFaceVertices f 1) (SixSubtileFaceVertices f 2) ∪ P4715T1Arc
            (SixSubtileFaceVertices f 2) (SixSubtileFaceVertices f 0))) → (∀ (f :
            PeriodicSubtileFaceIndex), P4715T1Region f ⊆ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ ×
            ℝ)) (P4715T1Position '' Set.range (SixSubtileFaceVertices f))) ) := by
  classical
  intro triangle_decomp f z hz
  rw [triangle_decomp f]
  exact Or.inl hz

private theorem bary_shift :
    (by
      classical
      exact
        (∀ (k : Int × Int), ∀ (a : PeriodicSubtileIndex), P4715T1Position
            (P4715T1VertexShift k a) = P4715T1Position a + ((k.1 : Real), (k.2 : Real))) →
                ((∀ (k : Int × Int), ∀ (j : Fin 12), ∀ (i : Fin 3), SixSubtileFaceVertices
                (P4715T1FaceShift k (P4715T1PatchFaces j)) i =
            P4715T1VertexShift k (SixSubtileFaceVertices (P4715T1PatchFaces j) i)) → (
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        let bary (f : PeriodicSubtileFaceIndex) (s t : Real) : ℝ × ℝ :=
          (1 - s - t) • P4715T1Position (SixSubtileFaceVertices f 0) +
            s • P4715T1Position (SixSubtileFaceVertices f 1) +
            t • P4715T1Position (SixSubtileFaceVertices f 2)
        ∀ (k : ℤ × ℤ), ∀ (j : Fin (12 : ℕ)), ∀ (s : ℝ), ∀ (t : ℝ), bary (P4715T1FaceShift k
            (P4715T1PatchFaces j)) s t = (translation k : ℝ × ℝ → ℝ × ℝ) (bary
            (P4715T1PatchFaces j) s t)))) := by
  classical
  intro position_shift face_vertex_shift translation bary k j s t
  dsimp [bary, translation]
  rw [face_vertex_shift k j 0, face_vertex_shift k j 1, face_vertex_shift k j 2]
  rw [position_shift, position_shift, position_shift]
  ext <;> simp [smul_add, smul_eq_mul]
  all_goals ring

private theorem translation_injective :
    (by
      classical
      exact
        let translation (k : Int × Int) : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) := {
          toFun := fun x => x + ((k.1 : Real), (k.2 : Real))
          linear := LinearMap.id
          map_vadd' := by intro x y; simp [add_assoc]
        }
        ∀ (k : ℤ × ℤ), Function.Injective (⇑(translation k) : ℝ × ℝ → ℝ × ℝ) ) := by
  classical
  intro translation k x y hxy
  change x + ((k.1 : Real), (k.2 : Real)) =
    y + ((k.1 : Real), (k.2 : Real)) at hxy
  exact add_right_cancel hxy

end CoefficientFaceTopology

theorem P4715T1CoefficientFaces :
    (∀ f, IsOpen (P4715T1Region f)) ∧
    (∀ f, IsConnected (P4715T1Region f)) ∧
    (Pairwise fun f g => Disjoint (P4715T1Region f) (P4715T1Region g)) ∧
    (∀ f, frontier (P4715T1Region f) =
      P4715T1Arc (SixSubtileFaceVertices f 0) (SixSubtileFaceVertices f 1) ∪
      P4715T1Arc (SixSubtileFaceVertices f 1) (SixSubtileFaceVertices f 2) ∪
      P4715T1Arc (SixSubtileFaceVertices f 2) (SixSubtileFaceVertices f 0)) ∧
    Set.range P4715T1Position ∪
      {p | ∃ a b, AllowedSubtileIncidence a b ∧ p ∈ P4715T1Arc a b} ∪
      {p | ∃ f, p ∈ P4715T1Region f} = Set.univ := by
-- BODY
  obtain ⟨hpoly, hboundary, hcover, hdisj, hinter⟩ := P4715T1HexagonTessellation
  obtain ⟨hpatch, hdet, hlocal, htrace⟩ := P4715T1HexagonSubdivision
  obtain ⟨_, _, _, _, hallowed, _⟩ := P4677T2IncidenceLedger
  have position_shift (k : Int × Int) (a : PeriodicSubtileIndex) :=
      CoefficientFaceTopology.position_shift k a
  have face_vertex_shift (k : Int × Int) (j : Fin 12) (i : Fin 3) :=
      CoefficientFaceTopology.face_vertex_shift k j i
  let faceDet (f : PeriodicSubtileFaceIndex) : ℝ :=
    let p0 := P4715T1Position (SixSubtileFaceVertices f 0)
    let p1 := P4715T1Position (SixSubtileFaceVertices f 1)
    let p2 := P4715T1Position (SixSubtileFaceVertices f 2)
    p1.1 * p2.2 - p1.1 * p0.2 - p0.1 * p2.2 - p1.2 * p2.1 +
      p1.2 * p0.1 + p0.2 * p2.1
  have faceDet_nonzero (f : PeriodicSubtileFaceIndex) := CoefficientFaceTopology.faceDet_nonzero f
  have faceDet_eq_delta (f : PeriodicSubtileFaceIndex) := CoefficientFaceProof.faceDet_eq_delta f
  have delta_nonzero (f : PeriodicSubtileFaceIndex) := CoefficientFaceProof.delta_nonzero
                  faceDet_nonzero faceDet_eq_delta f
  let lin (v w x : ℝ × ℝ) : ℝ × ℝ :=
    (x.1 * v.1 + x.2 * w.1, x.1 * v.2 + x.2 * w.2)
  let invlin (v w x : ℝ × ℝ) : ℝ × ℝ :=
    let d := v.1 * w.2 - v.2 * w.1
    ((x.1 * w.2 - x.2 * w.1) / d, (v.1 * x.2 - v.2 * x.1) / d)
  have inv_right (v w x : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
      lin v w (invlin v w x) = x := CoefficientFaceTopology.inv_right v w x hd
  have inv_left (v w x : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
      invlin v w (lin v w x) = x := CoefficientFaceTopology.inv_left v w x hd
  let affineHomeo (q v w : ℝ × ℝ) (hd : v.1 * w.2 - v.2 * w.1 ≠ 0) :
      Homeomorph (ℝ × ℝ) (ℝ × ℝ) := {
    toFun := fun x => q + lin v w x
    invFun := fun y => invlin v w (y - q)
    left_inv := fun x => by simp [inv_left, hd]
    right_inv := fun y => by simp [inv_right, hd]
    continuous_toFun := by dsimp [lin]; fun_prop
    continuous_invFun := by dsimp [invlin]; fun_prop
  }
  let D : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1}
  have Dopen := CoefficientFaceTopology.Dopen
  have Dconvex := CoefficientFaceProof.Dconvex
  have D_nonempty := CoefficientFaceTopology.D_nonempty
  have D_subset_W := CoefficientFaceTopology.D_subset_W
  have W_closed := CoefficientFaceTopology.W_closed
  have D_closure := CoefficientFaceProof.D_closure D_subset_W
  have mem_bottom_segment (z : ℝ×ℝ) := CoefficientFaceProof.mem_bottom_segment z
  have mem_diagonal_segment (z : ℝ×ℝ) := CoefficientFaceProof.mem_diagonal_segment z
  have mem_left_segment (z : ℝ×ℝ) := CoefficientFaceProof.mem_left_segment z
  have D_frontier := CoefficientFaceProof.D_frontier Dopen
          D_closure mem_bottom_segment mem_diagonal_segment mem_left_segment
  have image_segment (q v w : ℝ×ℝ)
      (hd : v.1*w.2-v.2*w.1≠0) (x y : ℝ×ℝ) := CoefficientFaceTopology.image_segment inv_right
          inv_left q v w hd x y
  have W_convex := CoefficientFaceTopology.W_convex
  have W_eq_stdHull := CoefficientFaceProof.W_eq_stdHull
      W_convex
  have hull_affine (q v w : ℝ×ℝ) := CoefficientFaceTopology.hull_affine W_eq_stdHull q v w
  have region_image (f : PeriodicSubtileFaceIndex) (hd : faceDet f ≠ 0) :=
      CoefficientFaceProof.region_image delta_nonzero inv_right
              inv_left f
  have W_decomp := CoefficientFaceProof.W_decomp Dopen D_subset_W D_closure
  have triangle_image (f : PeriodicSubtileFaceIndex) := CoefficientFaceProof.triangle_image
      delta_nonzero inv_right
              inv_left hull_affine f
  have hopen := CoefficientFaceTopology.hopen faceDet_nonzero
      delta_nonzero inv_right inv_left Dopen region_image
  have hconnected := CoefficientFaceProof.hconnected
      faceDet_nonzero delta_nonzero inv_right inv_left Dconvex D_nonempty region_image
  have triangle_decomp (f : PeriodicSubtileFaceIndex) := CoefficientFaceProof.triangle_decomp
      faceDet_nonzero delta_nonzero inv_right
              inv_left D_frontier image_segment region_image W_decomp triangle_image f
  have region_subset_triangle (f : PeriodicSubtileFaceIndex) :=
      CoefficientFaceTopology.region_subset_triangle triangle_decomp f
  have std_edge_disjoint (i j : Fin 3) (hij : i ≠ j) := CoefficientFaceProof.std_edge_disjoint
          mem_bottom_segment mem_diagonal_segment mem_left_segment i j hij
  have region_disjoint_arc (f : PeriodicSubtileFaceIndex) (i j : Fin 3)
      (hij : i ≠ j) := CoefficientFaceProof.region_disjoint_arc faceDet_nonzero delta_nonzero
          inv_right
            inv_left image_segment region_image std_edge_disjoint f i j hij
  have bary_shift (k : Int × Int) (j : Fin 12) (s t : Real) := CoefficientFaceTopology.bary_shift
            position_shift face_vertex_shift k j s t
  have region_shift (k : Int × Int) (j : Fin 12) := CoefficientFaceProof.region_shift bary_shift k j
  have translated_triangle (k : Int × Int) (j : Fin 12) :=
      CoefficientFaceProof.translated_triangle position_shift face_vertex_shift k j
  have common_edge (i j : Fin 12) (hij : i ≠ j) :
      ∃ a b : Fin 3, a ≠ b ∧
        ∀ r : Fin 3,
          SixSubtileFaceVertices (P4715T1PatchFaces i) r ∈
            Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j)) →
          r = a ∨ r = b :=
    (by decide +kernel +revert)
  have region_subset_tile (k : Int × Int) (j : Fin 12) := CoefficientFaceProof.region_subset_tile
      hpatch
            region_subset_triangle translated_triangle k j
  have common_hull_subset_arc (i j : Fin 12) (hij : i ≠ j) :=
      CoefficientFaceProof.common_hull_subset_arc common_edge i j hij
  have translation_injective (k : Int × Int) := CoefficientFaceTopology.translation_injective k
  have plane_cover := CoefficientFaceProof.plane_cover hcover
            hpatch hallowed triangle_decomp translated_triangle
  have pairwise_regions := CoefficientFaceProof.pairwise_regions
          hdisj hlocal hopen region_subset_triangle region_disjoint_arc region_shift
          region_subset_tile common_hull_subset_arc translation_injective
  refine ⟨hopen, hconnected, ?_, ?_, ?_⟩
  · exact pairwise_regions
  · intro f
    let q := P4715T1Position (SixSubtileFaceVertices f 0)
    let v := P4715T1Position (SixSubtileFaceVertices f 1) - q
    let w := P4715T1Position (SixSubtileFaceVertices f 2) - q
    let E := affineHomeo q v w (delta_nonzero f)
    rw [region_image f (faceDet_nonzero f)]
    calc
      frontier (E '' D) = E '' frontier D := (E.image_frontier D).symm
      _ = E '' (segment ℝ (0,0) (1,0) ∪ segment ℝ (1,0) (0,1) ∪
          segment ℝ (0,0) (0,1)) := by rw [D_frontier]
      _ = P4715T1Arc (SixSubtileFaceVertices f 0) (SixSubtileFaceVertices f 1) ∪
          P4715T1Arc (SixSubtileFaceVertices f 1) (SixSubtileFaceVertices f 2) ∪
          P4715T1Arc (SixSubtileFaceVertices f 2) (SixSubtileFaceVertices f 0) := by
        rw [Set.image_union, Set.image_union]
        rw [image_segment q v w (delta_nonzero f), image_segment q v w (delta_nonzero f),
          image_segment q v w (delta_nonzero f)]
        have e0 : E (0,0) = P4715T1Position (SixSubtileFaceVertices f 0) := by
          simp [E, affineHomeo, lin, q]
        have e1 : E (1,0) = P4715T1Position (SixSubtileFaceVertices f 1) := by
          ext <;> simp [E, affineHomeo, lin, q, v]
        have e2 : E (0,1) = P4715T1Position (SixSubtileFaceVertices f 2) := by
          ext <;> simp [E, affineHomeo, lin, q, w]
        simp only [P4715T1Arc]
        rw [e0, e1, e2]
        rw [segment_symm ℝ (P4715T1Position (SixSubtileFaceVertices f 2))
          (P4715T1Position (SixSubtileFaceVertices f 0))]
  · exact plane_cover

end ApollonianSuperharmonic

end
