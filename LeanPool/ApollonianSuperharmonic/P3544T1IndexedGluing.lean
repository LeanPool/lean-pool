/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSplit
public import LeanPool.ApollonianSuperharmonic.P3511T1SourceDissection
public import LeanPool.ApollonianSuperharmonic.P3652T1ChildFillSeparation
public import LeanPool.ApollonianSuperharmonic.P3652T1ParentOddGluing
public import LeanPool.ApollonianSuperharmonic.P3652T1DiagonalFaceIntersections
public import LeanPool.ApollonianSuperharmonic.P3652T1IndexedFaceLedger

-- [TABLET NODE: P3544T1IndexedGluing]

/-!
# P3544T1IndexedGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3544T1IndexedGluing {n : Nat} {p : P3381T1PolygonBoundary n}
    (S : P3544T1DiagonalSplit p) {XL XR : Set (Real × Real)}
    (L : P3511T1SourceDissection S.left XL)
    (R : P3511T1SourceDissection S.right XR)
    (hL : XL = P3544T1RayParity S.left ∪ P3544T1BoundaryCarrier S.left)
    (hR : XR = P3544T1RayParity S.right ∪ P3544T1BoundaryCarrier S.right)
    (hcL : IsPathConnected (P3544T1RayParity S.left))
    (hcR : IsPathConnected (P3544T1RayParity S.right)) :
    ∃ Z : P3511T1SourceDissection p (XL ∪ XR),
      List.ofFn Z.face = List.ofFn (fun k => S.il ∘ L.face k) ++
        List.ofFn (fun k => S.ir ∘ R.face k) ∧
      XL ∪ XR = P3544T1RayParity p ∪ P3544T1BoundaryCarrier p ∧
      IsPathConnected (P3544T1RayParity p) := by
-- BODY
  classical
  let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
    Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
  obtain ⟨hlist, hdissection, hinjective, hdistinct, hused, hnondegenerate, hedge, _, _⟩ :=
    P3652T1IndexedFaceLedger S L R
  have hsep := P3652T1ChildFillSeparation S hL hR hcL hcR
  obtain ⟨_, hfill, hconnected⟩ := P3652T1ParentOddGluing S hL hR hcL hcR hsep
  have hcross := P3652T1DiagonalFaceIntersections S L R hsep
  have hwithin {m : Nat} (q : P3381T1PolygonBoundary m)
      {X : Set (Real × Real)} (D : P3511T1SourceDissection q X)
      (e : Fin (m + 3) → Fin (n + 3)) (he : Function.Injective e)
      (hq : q.vertex = p.vertex ∘ e) (k l : Fin D.count) :
      convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face k))) ∩
        convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face l))) =
      convexHull Real (p.vertex ''
        (Set.range (e ∘ D.face k) ∩ Set.range (e ∘ D.face l))) := by
    have hv (i : Fin D.count) :
        q.vertex ∘ D.face i = p.vertex ∘ (e ∘ D.face i) := by
      rw [hq]
      rfl
    rw [← hv k, ← hv l, D.intersection]
    congr 1
    rw [Set.range_comp, Set.range_comp, ← Set.image_inter he, Set.image_image, hq]
    rfl
  have hcover : XL ∪ XR =
      ⋃ k, convexHull Real (Set.range (p.vertex ∘ f k)) := by
    ext x
    constructor
    · rintro (hx | hx)
      · rw [L.cover] at hx
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨Fin.castAdd R.count k, ?_⟩
        simpa only [f, Fin.addCases_left, ← Function.comp_assoc, ← S.left_vertex] using hk
      · rw [R.cover] at hx
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨Fin.natAdd L.count k, ?_⟩
        simpa only [f, Fin.addCases_right, ← Function.comp_assoc, ← S.right_vertex] using hk
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      revert hk
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · intro hi
        apply Or.inl
        rw [L.cover]
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        simpa only [f, Fin.addCases_left, ← Function.comp_assoc, ← S.left_vertex] using hi
      · intro hj
        apply Or.inr
        rw [R.cover]
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        simpa only [f, Fin.addCases_right, ← Function.comp_assoc, ← S.right_vertex] using hj
  have hintersection : ∀ k l,
      convexHull Real (Set.range (p.vertex ∘ f k)) ∩
        convexHull Real (Set.range (p.vertex ∘ f l)) =
      convexHull Real (p.vertex '' (Set.range (f k) ∩ Set.range (f l))) := by
    intro k l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) l
      · simpa only [f, Fin.addCases_left] using
          hwithin S.left L S.il S.il_injective S.left_vertex i i'
      · simpa only [f, Fin.addCases_left, Fin.addCases_right] using hcross i j'
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) l
      · simpa only [f, Fin.addCases_left, Fin.addCases_right, Set.inter_comm] using
          hcross i' j
      · simpa only [f, Fin.addCases_right] using
          hwithin S.right R S.ir S.ir_injective S.right_vertex j j'
  let Z : P3511T1SourceDissection p (XL ∪ XR) :=
    { count := L.count + R.count
      count_pos := by
        have hpos := L.count_pos
        omega
      face := f
      dissection := hdissection
      face_injective := hinjective
      face_distinct := hdistinct
      vertex_used := hused
      nondegenerate := hnondegenerate
      cover := hcover
      intersection := hintersection
      edge_count := hedge }
  exact ⟨Z, hlist, hfill, hconnected⟩

end ApollonianSuperharmonic

end
