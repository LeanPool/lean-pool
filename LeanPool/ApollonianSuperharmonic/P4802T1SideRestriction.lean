/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientTranslation
public import LeanPool.ApollonianSuperharmonic.P4793T1SupportingFace
public import LeanPool.ApollonianSuperharmonic.P4793T1FacetForms
public import LeanPool.ApollonianSuperharmonic.P4780T1ActiveFacets
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Inv
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Tactic.IntervalCases


-- [TABLET NODE: P4802T1SideRestriction]

/-!
# P4802T1SideRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem sideBoundary0 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (0 : Fin 6))
      (P4715T1BoundaryCycle (0 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (0 : Fin 6) ∨
      z = P4715T1BoundaryCycle (0 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Int.cast_zero,
        P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, sub_zero, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self,
        one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

private theorem sideBoundary1 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (1 : Fin 6))
      (P4715T1BoundaryCycle (1 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (1 : Fin 6) ∨
      z = P4715T1BoundaryCycle (1 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Fin.reduceAdd, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Int.cast_zero,
        Int.cast_one, Int.cast_neg, P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self, add_left_inj,
        one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

private theorem sideBoundary2 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (2 : Fin 6))
      (P4715T1BoundaryCycle (2 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (2 : Fin 6) ∨
      z = P4715T1BoundaryCycle (2 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Fin.reduceAdd,
        Matrix.cons_val, Int.cast_zero,
        Int.cast_one, Int.cast_neg, P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self,
        sub_neg_eq_add, neg_add_cancel_comm,
        one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

private theorem sideBoundary3 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (3 : Fin 6))
      (P4715T1BoundaryCycle (3 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (3 : Fin 6) ∨
      z = P4715T1BoundaryCycle (3 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Fin.reduceAdd,
        Matrix.cons_val, Int.cast_zero,
        Int.cast_one, Int.cast_neg, P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self, add_left_inj,
        sub_add_cancel_left,
        zero_sub, mul_neg, one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

private theorem sideBoundary4 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (4 : Fin 6))
      (P4715T1BoundaryCycle (4 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (4 : Fin 6) ∨
      z = P4715T1BoundaryCycle (4 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Fin.reduceAdd,
        Matrix.cons_val, Int.cast_zero,
        Int.cast_one, Int.cast_neg, P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, sub_zero, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self,
        sub_neg_eq_add,
        one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

private theorem sideBoundary5 (z : PeriodicSubtileIndex)
    (hz : P4715T1Position z ∈ P4715T1Arc
      (P4715T1BoundaryCycle (5 : Fin 6))
      (P4715T1BoundaryCycle (5 + 1 : Fin 6))) :
    z = P4715T1BoundaryCycle (5 : Fin 6) ∨
      z = P4715T1BoundaryCycle (5 + 1 : Fin 6) := by
  rw [P4715T1Arc, segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, hzt⟩
  cases z with
  | mk label m n =>
    cases label <;>
      simp only [P4715T1Position, P4715T1BoundaryCycle,
        Int.reduceNeg,
        Fin.isValue, Fin.reduceAdd, Matrix.cons_val_zero,
        Matrix.cons_val, Int.cast_zero,
        Int.cast_one, P4715T1Offsets,
        Prod.mk_add_mk, add_zero, zero_add, AffineMap.lineMap_apply,
        vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk,
        smul_eq_mul, vadd_eq_add, Prod.mk.injEq,
        PeriodicSubtileIndex.mk.injEq, true_and, reduceCtorEq,
        false_and, or_false, false_or, or_self, add_left_inj,
        zero_sub, mul_neg, one_div] at hzt ⊢
    all_goals
      have hmloR : (-2 : Real) < (m : Real) := by
        linarith only [hzt.1, ht.1, ht.2]
      have hmhiR : (m : Real) < 2 := by
        linarith only [hzt.1, ht.1, ht.2]
      have hnloR : (-2 : Real) < (n : Real) := by
        linarith only [hzt.2, ht.1, ht.2]
      have hnhiR : (n : Real) < 2 := by
        linarith only [hzt.2, ht.1, ht.2]
      have hmlo : (-2 : Int) < m := by exact_mod_cast hmloR
      have hmhi : m < (2 : Int) := by exact_mod_cast hmhiR
      have hnlo : (-2 : Int) < n := by exact_mod_cast hnloR
      have hnhi : n < (2 : Int) := by exact_mod_cast hnhiR
      interval_cases m <;> interval_cases n <;>
        norm_num at hzt ⊢ <;> linarith only [hzt.1, hzt.2, ht.1, ht.2]

theorem P4802T1SideRestriction (k : Int × Int) (r : Fin 6)
    (S : Set PeriodicSubtileIndex)
    (hS : ∀ z ∈ S, P4715T1Position z ∈
      (fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) :
    convexHull Real (P4715T1Position '' S) ∩
      P4715T1Arc (P4715T1VertexShift k (P4715T1BoundaryCycle r))
        (P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))) =
    convexHull Real (P4715T1Position ''
      (S ∩ {P4715T1VertexShift k (P4715T1BoundaryCycle r),
        P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))})) := by
-- BODY
  have boundary (k : Int × Int) (q : Fin 6) (z : PeriodicSubtileIndex)
      (hz : P4715T1Position z ∈ P4715T1Arc
        (P4715T1VertexShift k (P4715T1BoundaryCycle q))
        (P4715T1VertexShift k (P4715T1BoundaryCycle (q + 1)))) :
      z = P4715T1VertexShift k (P4715T1BoundaryCycle q) ∨
        z = P4715T1VertexShift k (P4715T1BoundaryCycle (q + 1)) := by
    as_aux_lemma =>
      have base (q : Fin 6) (z : PeriodicSubtileIndex)
          (hz : P4715T1Position z ∈ P4715T1Arc
            (P4715T1BoundaryCycle q) (P4715T1BoundaryCycle (q+1))) :
          z = P4715T1BoundaryCycle q ∨ z = P4715T1BoundaryCycle (q+1) := by
        as_aux_lemma =>
          fin_cases q
          · exact sideBoundary0 z hz
          · exact sideBoundary1 z hz
          · exact sideBoundary2 z hz
          · exact sideBoundary3 z hz
          · exact sideBoundary4 z hz
          · exact sideBoundary5 z hz
      rw [(P4715T1CoefficientTranslation k).2.1] at hz
      obtain ⟨x,hx,hxz⟩ := hz
      have hpos : P4715T1Position (P4715T1VertexShift (-k) z) = x := by
        rw [(P4715T1CoefficientTranslation (-k)).1, ← hxz]
        ext <;> simp
      have hh := base q (P4715T1VertexShift (-k) z) (hpos.symm ▸ hx)
      have hinv : P4715T1VertexShift k (P4715T1VertexShift (-k) z) = z := by
        rw [← P4715T1IndexAction.2.1, add_neg_cancel, P4715T1IndexAction.1]
      rcases hh with hh | hh
      · exact Or.inl (hinv.symm.trans (congrArg (P4715T1VertexShift k) hh))
      · exact Or.inr (hinv.symm.trans (congrArg (P4715T1VertexShift k) hh))
  let K : Real × Real := ((k.1 : Real), (k.2 : Real))
  let H := (fun x : Real × Real => x + K) '' P4715T1Hexagon
  let F : (Real × Real) →ᵃ[Real] Real :=
    (P4793T1FacetForms r).comp
      (AffineMap.id Real (Real × Real) - AffineMap.const Real (Real × Real) K)
  have hF (x : Real × Real) : F x = P4793T1FacetForms r (x-K) := rfl
  have hc : Convex Real H := by
    have hh : Convex Real P4715T1Hexagon := convex_convexHull Real _
    simpa only [H, add_comm] using hh.translate K
  have hnonneg (x : Real × Real) (hx : x ∈ H) : 0 ≤ F x := by
    obtain ⟨y,hy,rfl⟩ := hx
    rw [hF, add_sub_cancel_right]
    rw [P4780T1HullHalfspaces] at hy
    rcases hy with ⟨h1,h2,h3,h4,h5,h6⟩
    fin_cases r <;> norm_num [P4793T1FacetForms] <;> linarith
  have hbase : P4715T1Arc (P4715T1BoundaryCycle r)
      (P4715T1BoundaryCycle (r+1)) =
      P4715T1Hexagon ∩ {x | P4793T1FacetForms r x = 0} := by
    rw [P4780T1ActiveFacets]
    congr 1
    ext x
    fin_cases r <;> norm_num [P4793T1FacetForms] <;>
      constructor <;> intro h <;> linarith
  let u := P4715T1VertexShift k (P4715T1BoundaryCycle r)
  let v := P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))
  have hside (x : Real × Real) : x ∈ P4715T1Arc u v ↔
      x ∈ H ∧ F x = 0 := by
    dsimp only [u,v]
    rw [(P4715T1CoefficientTranslation k).2.1, hbase]
    constructor
    · rintro ⟨y,⟨hy,hz⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩, ?_⟩
      change P4793T1FacetForms r y = 0 at hz
      change P4793T1FacetForms r (y+K-K) = 0
      simpa only [add_sub_cancel_right] using hz
    · rintro ⟨⟨y,hy,rfl⟩,hz⟩
      refine ⟨y,⟨hy,?_⟩,rfl⟩
      change P4793T1FacetForms r (y+K-K) = 0 at hz
      change P4793T1FacetForms r y = 0
      simpa only [add_sub_cancel_right] using hz
  have hvertex (z : PeriodicSubtileIndex)
      (hz : P4715T1Position z ∈ P4715T1Arc u v) : z ∈ ({u,v} : Set _) := by
    exact boundary k r z hz
  have hzero : (P4715T1Position '' S) ∩ {x | F x = 0} =
      P4715T1Position '' (S ∩ ({u,v} : Set _)) := by
    ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hf⟩
      exact ⟨z,⟨hz,hvertex z ((hside _).mpr ⟨hS z hz,hf⟩)⟩,rfl⟩
    · rintro ⟨z,⟨hz,hzuv⟩,rfl⟩
      refine ⟨⟨z,hz,rfl⟩, (hside _).mp ?_ |>.2⟩
      rcases hzuv with hzuv | hzuv
      · rw [hzuv]
        exact left_mem_segment Real _ _
      · rw [Set.mem_singleton_iff] at hzuv
        rw [hzuv]
        exact right_mem_segment Real _ _
  have hh := P4793T1SupportingFace (P4715T1Position '' S) F
    (by rintro _ ⟨z,hz,rfl⟩; exact hnonneg _ (hS z hz))
  have hHull : convexHull Real (P4715T1Position '' S) ⊆ H :=
    convexHull_min (by rintro _ ⟨z,hz,rfl⟩; exact hS z hz) hc
  change convexHull Real (P4715T1Position '' S) ∩ P4715T1Arc u v = _
  calc
    _ = convexHull Real (P4715T1Position '' S) ∩ {x | F x = 0} := by
      ext x
      constructor
      · rintro ⟨hx,hy⟩
        exact ⟨hx,((hside x).mp hy).2⟩
      · rintro ⟨hx,hy⟩
        exact ⟨hx,(hside x).mpr ⟨hHull hx,hy⟩⟩
    _ = _ := by rw [hh.2,hzero]

end ApollonianSuperharmonic

end
