/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3652T1TriangleFaceRestriction
public import LeanPool.ApollonianSuperharmonic.P3652T1IndexedFaceLedger

-- [TABLET NODE: P3652T1DiagonalFaceIntersections]

/-!
# P3652T1DiagonalFaceIntersections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3652T1DiagonalFaceIntersections {n : Nat} {p : P3381T1PolygonBoundary n}
    (S : P3544T1DiagonalSplit p) {XL XR : Set (Real × Real)}
    (L : P3511T1SourceDissection S.left XL)
    (R : P3511T1SourceDissection S.right XR)
    (hsep : XL ∩ XR = segment Real (p.vertex S.a) (p.vertex S.b)) :
    ∀ k l,
      convexHull Real (Set.range (p.vertex ∘ (S.il ∘ L.face k))) ∩
        convexHull Real (Set.range (p.vertex ∘ (S.ir ∘ R.face l))) =
      convexHull Real (p.vertex ''
        (Set.range (S.il ∘ L.face k) ∩ Set.range (S.ir ∘ R.face l))) := by
-- BODY
  classical
  have hfaces (v : Fin 3 → Fin (n + 3))
      (hv : P3381T1TriangleDeterminant (p.vertex ∘ v) ≠ 0)
      (A B : Set (Fin (n + 3))) (hA : A ⊆ Set.range v) (hB : B ⊆ Set.range v) :
      convexHull Real (p.vertex '' A) ∩ convexHull Real (p.vertex '' B) =
        convexHull Real (p.vertex '' (A ∩ B)) := by
    have hAB : A ∩ B ⊆ Set.range v := fun _ hx => hA hx.1
    have h := P3652T1TriangleFaceRestriction (p.vertex ∘ v) hv
      (v ⁻¹' A) (v ⁻¹' B)
    simpa only [← Set.preimage_inter, Set.image_comp,
      Set.image_preimage_eq_of_subset hA, Set.image_preimage_eq_of_subset hB,
      Set.image_preimage_eq_of_subset hAB] using h
  have hwithin {m : Nat} (q : P3381T1PolygonBoundary m)
      {X : Set (Real × Real)} (D : P3511T1SourceDissection q X)
      (e : Fin (m + 3) → Fin (n + 3)) (he : Function.Injective e)
      (hq : q.vertex = p.vertex ∘ e) (k l : Fin D.count) :
      convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face k))) ∩
        convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face l))) =
      convexHull Real (p.vertex ''
        (Set.range (e ∘ D.face k) ∩ Set.range (e ∘ D.face l))) := by
    have hv (i : Fin D.count) :
        q.vertex ∘ D.face i = p.vertex ∘ (e ∘ D.face i) := by rw [hq]; rfl
    rw [← hv k, ← hv l, D.intersection]
    congr 1
    rw [Set.range_comp, Set.range_comp, ← Set.image_inter he, Set.image_image, hq]
    rfl
  have hclip {m : Nat} (q : P3381T1PolygonBoundary m)
      {X : Set (Real × Real)} (D : P3511T1SourceDissection q X)
      (e : Fin (m + 3) → Fin (n + 3)) (he : Function.Injective e)
      (hq : q.vertex = p.vertex ∘ e) (K : Fin D.count)
      (hKa : S.a ∈ Set.range (e ∘ D.face K))
      (hKb : S.b ∈ Set.range (e ∘ D.face K)) (k : Fin D.count) :
      convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face k))) ∩
        segment Real (p.vertex S.a) (p.vertex S.b) =
      convexHull Real (p.vertex '' (Set.range (e ∘ D.face k) ∩ {S.a, S.b})) := by
    let F := Set.range (e ∘ D.face k)
    let H := Set.range (e ∘ D.face K)
    have hbase : ({S.a, S.b} : Set (Fin (n + 3))) ⊆ H := by
      intro i hi
      rcases Set.mem_insert_iff.mp hi with rfl | hi
      · exact hKa
      · exact Set.mem_singleton_iff.mp hi ▸ hKb
    have hnd : P3381T1TriangleDeterminant (p.vertex ∘ (e ∘ D.face K)) ≠ 0 := by
      simpa only [← Function.comp_assoc, ← hq] using D.nondegenerate K
    have hbaseHull : convexHull Real (p.vertex '' ({S.a, S.b} : Set (Fin (n + 3)))) =
        segment Real (p.vertex S.a) (p.vertex S.b) := by rw [Set.image_pair, convexHull_pair]
    have hbaseSub : segment Real (p.vertex S.a) (p.vertex S.b) ⊆
        convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face K))) := by
      rw [← hbaseHull, Set.range_comp]
      exact convexHull_mono (Set.image_mono hbase)
    have hi : (F ∩ H) ∩ ({S.a, S.b} : Set (Fin (n + 3))) = F ∩ {S.a, S.b} := by
      ext i
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hbase h.2⟩, h.2⟩⟩
    calc
      _ = (convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face k))) ∩
          convexHull Real (Set.range (p.vertex ∘ (e ∘ D.face K)))) ∩
          segment Real (p.vertex S.a) (p.vertex S.b) := by
        ext x
        exact ⟨fun h => ⟨⟨h.1, hbaseSub h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      _ = convexHull Real (p.vertex '' (F ∩ H)) ∩
          convexHull Real (p.vertex '' ({S.a, S.b} : Set (Fin (n + 3)))) := by
        rw [hwithin q D e he hq k K, hbaseHull]
      _ = convexHull Real (p.vertex '' ((F ∩ H) ∩ {S.a, S.b})) :=
        hfaces (e ∘ D.face K) hnd (F ∩ H) {S.a, S.b} Set.inter_subset_right hbase
      _ = _ := by rw [hi]
  obtain ⟨_, _, _, _, _, _, _, ⟨KL, hLa, hLb⟩, ⟨KR, hRa, hRb⟩⟩ :=
    P3652T1IndexedFaceLedger S L R
  have hnd : P3381T1TriangleDeterminant (p.vertex ∘ (S.il ∘ L.face KL)) ≠ 0 := by
    simpa only [← Function.comp_assoc, ← S.left_vertex] using L.nondegenerate KL
  have hbase : ({S.a, S.b} : Set (Fin (n + 3))) ⊆ Set.range (S.il ∘ L.face KL) := by
    intro i hi
    rcases Set.mem_insert_iff.mp hi with rfl | hi
    · exact hLa
    · exact Set.mem_singleton_iff.mp hi ▸ hLb
  intro k l
  have hLsub : convexHull Real (Set.range (p.vertex ∘ (S.il ∘ L.face k))) ⊆ XL := by
    intro x hx
    have hi : x ∈ ⋃ j, convexHull Real (Set.range (S.left.vertex ∘ L.face j)) := by
      apply Set.mem_iUnion.mpr
      exact ⟨k, by simpa only [← Function.comp_assoc, ← S.left_vertex] using hx⟩
    exact L.cover.symm ▸ hi
  have hRsub : convexHull Real (Set.range (p.vertex ∘ (S.ir ∘ R.face l))) ⊆ XR := by
    intro x hx
    have hi : x ∈ ⋃ j, convexHull Real (Set.range (S.right.vertex ∘ R.face j)) := by
      apply Set.mem_iUnion.mpr
      exact ⟨l, by simpa only [← Function.comp_assoc, ← S.right_vertex] using hx⟩
    exact R.cover.symm ▸ hi
  have hcommon : Set.range (S.il ∘ L.face k) ∩ Set.range (S.ir ∘ R.face l) ⊆
      ({S.a, S.b} : Set (Fin (n + 3))) := by
    intro i hi
    rw [← S.common_indices]
    obtain ⟨j, hj⟩ := hi.1
    obtain ⟨z, hz⟩ := hi.2
    exact ⟨⟨L.face k j, hj⟩, ⟨R.face l z, hz⟩⟩
  have hi : (Set.range (S.il ∘ L.face k) ∩ ({S.a, S.b} : Set (Fin (n + 3)))) ∩
      (Set.range (S.ir ∘ R.face l) ∩ {S.a, S.b}) =
      Set.range (S.il ∘ L.face k) ∩ Set.range (S.ir ∘ R.face l) := by
    ext i
    exact ⟨fun h => ⟨h.1.1, h.2.1⟩,
      fun h => ⟨⟨h.1, hcommon h⟩, ⟨h.2, hcommon h⟩⟩⟩
  calc
    _ = (convexHull Real (Set.range (p.vertex ∘ (S.il ∘ L.face k))) ∩
          segment Real (p.vertex S.a) (p.vertex S.b)) ∩
        (convexHull Real (Set.range (p.vertex ∘ (S.ir ∘ R.face l))) ∩
          segment Real (p.vertex S.a) (p.vertex S.b)) := by
      ext x
      constructor
      · intro h
        have he : x ∈ segment Real (p.vertex S.a) (p.vertex S.b) :=
          hsep ▸ (show x ∈ XL ∩ XR from ⟨hLsub h.1, hRsub h.2⟩)
        exact ⟨⟨h.1, he⟩, ⟨h.2, he⟩⟩
      · intro h
        exact ⟨h.1.1, h.2.1⟩
    _ = convexHull Real (p.vertex '' (Set.range (S.il ∘ L.face k) ∩ {S.a, S.b})) ∩
        convexHull Real (p.vertex '' (Set.range (S.ir ∘ R.face l) ∩ {S.a, S.b})) := by
      rw [hclip S.left L S.il S.il_injective S.left_vertex KL hLa hLb k,
        hclip S.right R S.ir S.ir_injective S.right_vertex KR hRa hRb l]
    _ = convexHull Real (p.vertex ''
        ((Set.range (S.il ∘ L.face k) ∩ {S.a, S.b}) ∩
          (Set.range (S.ir ∘ R.face l) ∩ {S.a, S.b}))) :=
      hfaces (S.il ∘ L.face KL) hnd _ _
        (fun _ h => hbase h.2) (fun _ h => hbase h.2)
    _ = _ := by rw [hi]

end ApollonianSuperharmonic

end
