/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints

-- [TABLET NODE: BandPositiveCutBranchCompanionExclusion]

/-!
# BandPositiveCutBranchCompanionExclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositiveCutExclusionGeometry

private theorem positive_of_nonempty :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (X : ProtoTile), (BandPrototile c X) → ((X.cells.Nonempty) →
            (0 < c.1)) ) := by
  classical
  intro c X hX hne
  cases hX with
  | line w x hw => simp at hne
  | unit z x a => norm_num
  | @decompose r hr S X hS hc hf hcent =>
      exact (ProperBandCurvatureStructure r hr).1

private theorem boundary_edge_footprint :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges X) → (e ∈
            FootprintEdges X) ) := by
  classical
  intro X e he
  let I : GaussianInt := ⟨0, 1⟩
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [I, Zsqrtd.ext_iff]
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

private theorem edge_vertex_footprint :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges X) → (∀ (z :
            GaussianInt), (z ∈ e) → (z ∈ FootprintVertices X)) ) := by
  classical
  intro X e he z hz
  rcases he with ⟨c, hc, he⟩
  unfold FootprintVertices
  rw [ite_eq_left ⟨c, hc⟩]
  rcases he with h | h | h | h <;> subst e
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩

private theorem boundary_to_raw :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges X) → (e ∈
            FootprintEdges X)) → ((∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges X) → (∀ (z : GaussianInt), (z ∈ e) → (z ∈ FootprintVertices X))) → (∀
            (X : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈
            FootprintVertices X))) ) := by
  classical
  intro boundary_edge_footprint edge_vertex_footprint X x hx
  by_cases hne : X.cells.Nonempty
  · unfold BoundaryFootprintVertices at hx
    rw [ite_eq_left hne] at hx
    rcases hx with ⟨e, he, hxe⟩
    exact edge_vertex_footprint X e (boundary_edge_footprint X e he) x hxe
  · unfold BoundaryFootprintVertices at hx
    rw [ite_eq_right hne] at hx
    subst x
    simp [FootprintVertices, hne]

private theorem exact_exclusion :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right :
            ExactTileInterfaceTriple U V W), ∀ (adjacent : ExactTileInterfaceTriple U W Z), ∀
            (incomingPoint : GaussianInt), (right.point ≠ incomingPoint) → ((adjacent.point =
            incomingPoint) → (∀ (cut : GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈
            FootprintVertices W) → ((cut ∈ FootprintVertices Z) → (cut ∉ FootprintVertices V)))))
            ) := by
  classical
  intro U V W Z right adjacent incomingPoint hne halign cut hU hW hZ hV
  have hr : cut = right.point :=
    (right.unique_common cut).mp ⟨⟨hU, hV⟩, hW⟩
  have ha : cut = adjacent.point :=
    (adjacent.unique_common cut).mp ⟨⟨hU, hW⟩, hZ⟩
  exact hne (hr.symm.trans (ha.trans halign))

private theorem occurrence_centroid :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3), ∀
            (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - (⟨0, 1⟩ :
            GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))))) ) := by
  classical
  intro r P X i s ho
  change BandPrototile (r i.succ) X ∧ _ ∧ _ at ho
  rcases ho with ⟨_, _, hc⟩
  convert hc using 1;
    ext <;>
    simp [GaussianRealPoint, sub_eq_add_neg, add_comm,
      smul_eq_mul]

private theorem hq3pos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (((0 : ℤ) < (q
            (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3
            : ℕ)), ∀ (j : Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j)
            → (0 < (q 3).1)) ) := by
  classical
  intro q cfg hcurv
  have hnonneg : 0 ≤ (q 3).1 := by
    simpa using hcurv.2.1 (2 : Fin 3)
  have hne : (q 3).1 ≠ 0 := cfg.noLine 3
  omega

private theorem hOpos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → ((∀ (c : CircleCoordinates), ∀ (X :
            ProtoTile), (BandPrototile c X) → ((X.cells.Nonempty) → (0 < c.1))) → (0 <
            (cfg.firstPredecessor 1).1)) ) := by
  classical
  intro q cfg C₀ T cert hO positive_of_nonempty
  have hproto : BandPrototile (cfg.firstPredecessor 1) cert.O := by
    simpa [cert.precursor_eq] using (cert.plus_occurrence 0 false).1
  exact positive_of_nonempty _ _ hproto hO

private theorem hOcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I w
  simpa [cert.precursor_eq, I, w, cfg.firstParentTwo, cfg.firstParentThree]
    using occurrence_centroid cfg.firstPredecessor (cert.P 0 true)
      (cert.Q 0 false) 0 false (cert.plus_occurrence 0 false)

private theorem hQ2cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * t)) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I t
  simpa [I, t, cfg.firstParentTwo, cfg.firstParentThree]
    using occurrence_centroid cfg.firstPredecessor (cert.P 0 true)
      (cert.Q 1 true) 1 true (cert.plus_occurrence 1 true)

private theorem hQ3cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        TileCentroid (cert.Q 2 true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * u)) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I u
  simpa [I, u, cfg.firstParentTwo, cfg.firstParentThree]
    using occurrence_centroid cfg.firstPredecessor (cert.P 0 true)
      (cert.Q 2 true) 2 true (cert.plus_occurrence 2 true)

private theorem hS2cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false) = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * t))) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I t
  simpa [I, t, cfg.firstParentTwo, cfg.firstParentThree]
    using occurrence_centroid cfg.firstPredecessor (cert.P 0 false)
      (cert.S 1 false) 1 false (cert.minus_occurrence 1 false)

private theorem hS3cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        TileCentroid (cert.S 2 false) - TileCentroid (cert.P 0 false) = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * u))) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I u
  simpa [I, u, cfg.firstParentTwo, cfg.firstParentThree]
    using occurrence_centroid cfg.firstPredecessor (cert.P 0 false)
      (cert.S 2 false) 2 false (cert.minus_occurrence 2 false)

private theorem hPminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i
            : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X -
            TileCentroid P = (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint
            ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) ) := by
  classical
  intro q cfg C₀ T cert occurrence_centroid I w
  have hm := occurrence_centroid q T (cert.P 0 false) 0 false
    (cert.outer_occurrence 0 false)
  have hp := occurrence_centroid q T (cert.P 0 true) 0 true
    (cert.outer_occurrence 0 true)
  simp only [I, w] at hm hp ⊢
  calc
    _ = (TileCentroid (cert.P 0 false) - TileCentroid T) -
        (TileCentroid (cert.P 0 true) - TileCentroid T) := by abel
    _ = _ := by rw [hm, hp]; ext <;> simp [GaussianRealPoint, sub_eq_add_neg,
      smul_eq_mul] <;> ring

private theorem hsum :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        w + t + u = 0 ) := by
  classical
  intro q cfg u w t
  simpa [w, t, u, cfg.firstParentTwo, cfg.firstParentThree] using
    (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).1

private theorem gaussianPoint_add :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint x
            + GaussianRealPoint y ) := by
  classical
  intro x y
  ext <;> simp [GaussianRealPoint]

private theorem gaussianPoint_neg :
    (by
      classical
      exact
        ∀ (x : GaussianInt), GaussianRealPoint (-x) = -GaussianRealPoint x ) := by
  classical
  intro x
  ext <;> simp [GaussianRealPoint]

private theorem gaussianPoint_Iminus_one :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), GaussianRealPoint (-x) = -GaussianRealPoint x) → (∀ (x :
            GaussianInt), GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x)) )
            := by
  classical
  intro I gaussianPoint_neg x
  have hx : (I - 1) * x = -((1 - I) * x) := by ring
  rw [hx, gaussianPoint_neg]

private theorem hprod :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (w + t + u = 0) → ((1 - I) * w + (1 - I) * t + (1 - I) * u = 0) ) := by
  classical
  intro q cfg I u w t hsum
  calc
    _ = (1 - I) * (w + t + u) := by ring
    _ = 0 := by rw [hsum]; simp

private theorem hsumGaussianPoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint
            x + GaussianRealPoint y) → (((1 - I) * w + (1 - I) * t + (1 - I) * u = 0) →
            (GaussianRealPoint ((1 - I) * w) + GaussianRealPoint ((1 - I) * t) +
            GaussianRealPoint ((1 - I) * u) = 0)) ) := by
  classical
  intro q cfg I u w t gaussianPoint_add hprod
  calc
    _ = GaussianRealPoint ((1 - I) * w + (1 - I) * t + (1 - I) * u) := by
      rw [← gaussianPoint_add, ← gaussianPoint_add]
    _ = 0 := by rw [hprod]; simp [GaussianRealPoint]

private theorem hsumGaussianPointFst :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (GaussianRealPoint ((1 - I) * w) + GaussianRealPoint ((1 - I) * t) + GaussianRealPoint
            ((1 - I) * u) = 0) → ((GaussianRealPoint ((1 - I) * w)).1 + (GaussianRealPoint ((1 -
            I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) ) := by
  classical
  intro q cfg I u w t hsumGaussianPoint
  simpa using congrArg Prod.fst hsumGaussianPoint

private theorem hsumGaussianPointSnd :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (GaussianRealPoint ((1 - I) * w) + GaussianRealPoint ((1 - I) * t) + GaussianRealPoint
            ((1 - I) * u) = 0) → ((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 -
            I) * t)).2 + (GaussianRealPoint ((1 - I) * u)).2 = 0) ) := by
  classical
  intro q cfg I u w t hsumGaussianPoint
  simpa using congrArg Prod.snd hsumGaussianPoint

private theorem hforward :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (birth (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (2 : Fin (4 : ℕ)) = q (3 : Fin (4
            : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))) → ((∀ (j :
            Fin (3 : ℕ)), BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth j.succ) = (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) * BandVectors.1 (birth j.succ) (birth (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (birth (0 : Fin (4 : ℕ))) (birth j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (birth j.succ) (birth (0 : Fin (4 : ℕ)))) → (u = (⟨0, 1⟩
            : GaussianInt) * BandVectors.1 (birth 3) (birth 0))) ) := by
  classical
  intro q cfg birth u hp2 hf
  simpa [u, hp2.1, hp2.2.2] using (hf (2 : Fin 3)).1

private theorem hreverse :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (u = (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (birth 3) (birth 0)) → (BandVectors.1 (birth
            3) (birth 0) = -(⟨0, 1⟩ : GaussianInt) * u) ) := by
  classical
  intro q cfg birth u hforward
  calc
    _ = -(⟨0, 1⟩ : GaussianInt) *
        ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (birth 3) (birth 0)) := by
          ext <;> simp
    _ = _ := by rw [← hforward]

private theorem hrootAdj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (birth (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (2 : Fin (4 : ℕ)) = q (3 : Fin (4
            : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))) → ((∀ (j :
            Fin (3 : ℕ)), BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth j.succ) = (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) * BandVectors.1 (birth j.succ) (birth (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (birth (0 : Fin (4 : ℕ))) (birth j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (birth j.succ) (birth (0 : Fin (4 : ℕ)))) →
            (BandVectors.1 (birth 0) (birth 2) = (⟨0, 1⟩ : GaussianInt) * w)) ) := by
  classical
  intro q cfg birth w hp2 hf
  simpa [hp2.1, hp2.2.1, w] using (hf (1 : Fin 3)).1

private theorem hargA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 3) (birth 0) = -(⟨0, 1⟩ : GaussianInt) * u) → ((BandVectors.1
            (birth 0) (birth 3) = u) → (BandVectors.1 (birth 3) (birth 0) + BandVectors.1 (birth
            0) (birth 3) = (1 - I) * u)) ) := by
  classical
  intro q cfg birth I u hreverse hforward'
  rw [hreverse, hforward']
  ring

private theorem hargAdj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (birth 0) (birth 2) = (⟨0, 1⟩ : GaussianInt) * w) → ((BandVectors.1 (birth
            2) (birth 0) = w) → (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth 2)
            (birth 0) = (I - 1) * w)) ) := by
  classical
  intro q birth I w hrootAdj hbackAdj
  rw [hrootAdj, hbackAdj]
  ring

private theorem hWcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.Q 1 true) - TileCentroid
            (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)) →
            (((GaussianRealPoint ((1 - I) * w)).1 + (GaussianRealPoint ((1 - I) * t)).1 +
            (GaussianRealPoint ((1 - I) * u)).1 = 0) → (((GaussianRealPoint ((1 - I) * w)).2 +
            (GaussianRealPoint ((1 - I) * t)).2 + (GaussianRealPoint ((1 - I) * u)).2 = 0) →
            ((BandVectors.1 (birth 3) (birth 0) + BandVectors.1 (birth 0) (birth 3) = (1 - I) *
            u) → (TileCentroid cert.O - TileCentroid (cert.Q 1 true) = (1 / 2 : Real) •
            GaussianRealPoint (BandVectors.1 (birth 3) (birth 0) + BandVectors.1 (birth 0) (birth
            3))))))) ) := by
  classical
  intro q cfg C₀ T cert birth I u w t hOcent hQ2cent hsumGaussianPointFst hsumGaussianPointSnd hargA
  calc
    _ = (TileCentroid cert.O - TileCentroid (cert.P 0 true)) -
        (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hOcent, hQ2cent, hargA]
      ext
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointSnd

private theorem hZcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * t)) → ((TileCentroid (cert.S 2 false) - TileCentroid
            (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * u)))
            → ((TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) → (((GaussianRealPoint ((1 - I) * w)).1 +
            (GaussianRealPoint ((1 - I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) →
            (((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 - I) * t)).2 +
            (GaussianRealPoint ((1 - I) * u)).2 = 0) → (TileCentroid (cert.S 2 false) -
            TileCentroid (cert.Q 1 true) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1
            - I) * w))))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hQ2cent hS3cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true)) +
        (TileCentroid (cert.S 2 false) - TileCentroid (cert.P 0 false)) -
        (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hPminus, hS3cent, hQ2cent]
      ext
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointSnd

private theorem hWcent'At387 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (TileCentroid cert.O - TileCentroid
            (cert.Q 1 true) = (1 / 2 : Real) • GaussianRealPoint (BandVectors.1 (birth 3) (birth
            0) + BandVectors.1 (birth 0) (birth 3))) → (TileCentroid cert.O - TileCentroid
            (cert.Q 1 true) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (0 :
            Nat) * (BandVectors.1 (birth 3) (birth 0) + BandVectors.1 (birth 0) (birth 3)))) ) := by
  classical
  intro q cfg C₀ T cert birth hWcent
  simpa using hWcent

private theorem hnotA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 3) = u) → (∀ (right : ExactTileInterfaceTriple (cert.Q (1
            : Fin (3 : ℕ)) true) (TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑(0 : Fin (4 : ℕ)) : ℕ) * if Even (↑(0 : Fin (4 : ℕ)) : ℕ)
            then BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 : ℕ))))
            else BandVectors.1 (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ)))))
            cert.O), ∀ (incoming : ExactTileInterfaceTriple (cert.Q (1 : Fin (3 : ℕ)) true)
            (TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑(0 : Fin (4 : ℕ)) : ℕ) * if Even (↑(0 : Fin (4 : ℕ)) : ℕ) then BandVectors.1
            (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else BandVectors.1
            (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 : ℕ)))))) cert.O), ∀ (adjacent
            : ExactTileInterfaceTriple (cert.Q (1 : Fin (3 : ℕ)) true) cert.O (cert.S (2 : Fin (3
            : ℕ)) false)), (right.point ≠ incoming.point) → ((adjacent.point = incoming.point) →
            ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true)) →
            ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.S (2 : Fin (3 : ℕ)) false)) →
            ((cert.exceptionalSegments.a ∈ FootprintVertices cert.O) →
            (cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation (cert.Q 1 true)
            u)))))))) ) := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion u hforward' right incoming adjacent hne halign haU
      haZ haW
  have hn := exact_exclusion _ _ _ _ right adjacent incoming.point hne halign
    cert.exceptionalSegments.a haU haW haZ
  simpa [hforward'] using hn

private theorem hWcent'At413 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.S 1 false) - TileCentroid
            (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)))
            → ((TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) → (((GaussianRealPoint ((1 - I) * w)).1 +
            (GaussianRealPoint ((1 - I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) →
            (((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 - I) * t)).2 +
            (GaussianRealPoint ((1 - I) * u)).2 = 0) → (TileCentroid cert.O - TileCentroid
            (cert.S 1 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            u))))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hOcent hS2cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid cert.O - TileCentroid (cert.P 0 true)) -
        (TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false)) -
        (TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hOcent, hS2cent, hPminus]
      ext
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointSnd

private theorem hZcent'At426 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid (cert.Q 2 true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * u)) → ((TileCentroid (cert.S 1 false) - TileCentroid
            (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)))
            → ((TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) → (((GaussianRealPoint ((1 - I) * w)).1 +
            (GaussianRealPoint ((1 - I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) →
            (((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 - I) * t)).2 +
            (GaussianRealPoint ((1 - I) * u)).2 = 0) → (TileCentroid (cert.Q 2 true) -
            TileCentroid (cert.S 1 false) = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * w))))))
            ) := by
  classical
  intro q cfg C₀ T cert I u w t hQ3cent hS2cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.Q 2 true) - TileCentroid (cert.P 0 true)) -
        (TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false)) -
        (TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hQ3cent, hS2cent, hPminus]
      ext
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointSnd

private theorem hnotB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 3) = u) → (∀ (right' : ExactTileInterfaceTriple (cert.S
            (1 : Fin (3 : ℕ)) false) (TileTranslation (cert.S (1 : Fin (3 : ℕ)) false) ((⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(2 : Fin (4 : ℕ)) : ℕ) * if Even (↑(2 : Fin (4 : ℕ))
            : ℕ) then BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 :
            ℕ)))) else BandVectors.1 (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 :
            ℕ))))) cert.O), ∀ (incoming' : ExactTileInterfaceTriple (cert.S (1 : Fin (3 : ℕ))
            false) (TileTranslation (cert.S (1 : Fin (3 : ℕ)) false) ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑(2 : Fin (4 : ℕ)) : ℕ) * if Even (↑(2 : Fin (4 : ℕ)) : ℕ) then
            BandVectors.1 (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else
            BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 : ℕ))))))
            cert.O), ∀ (adjacent' : ExactTileInterfaceTriple (cert.S (1 : Fin (3 : ℕ)) false)
            cert.O (cert.Q (2 : Fin (3 : ℕ)) true)), (right'.point ≠ incoming'.point) →
            ((adjacent'.point = incoming'.point) → ((cert.exceptionalSegments.b ∈
            FootprintVertices (cert.S (1 : Fin (3 : ℕ)) false)) → ((cert.exceptionalSegments.b ∈
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true)) → ((cert.exceptionalSegments.b ∈
            FootprintVertices cert.O) → (cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation (cert.S 1 false) (-u)))))))))) ) := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion I hI2 u hforward' right' incoming' adjacent' hne'
      halign' hbU hbZ hbW
  have hn := exact_exclusion _ _ _ _ right' adjacent' incoming'.point hne' halign'
    cert.exceptionalSegments.b hbU hbW hbZ
  simpa [I, hI2, hforward'] using hn

private theorem hback3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (t = I * BandVectors.1 (birth 3) (birth 0)) → (BandVectors.1 (birth 3) (birth 0) = -I *
            t) ) := by
  classical
  intro q cfg birth I t hflip3
  calc
    _ = -I * (I * BandVectors.1 (birth 3) (birth 0)) := by
      ext <;> simp [I]
    _ = _ := by rw [← hflip3]

private theorem hQ2O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.Q 1 true) - TileCentroid
            (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)) →
            (((GaussianRealPoint ((1 - I) * w)).1 + (GaussianRealPoint ((1 - I) * t)).1 +
            (GaussianRealPoint ((1 - I) * u)).1 = 0) → (((GaussianRealPoint ((1 - I) * w)).2 +
            (GaussianRealPoint ((1 - I) * t)).2 + (GaussianRealPoint ((1 - I) * u)).2 = 0) →
            (TileCentroid (cert.Q 1 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * u)))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hOcent hQ2cent hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true)) -
        (TileCentroid cert.O - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hQ2cent, hOcent]
      ext
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointSnd

private theorem hS3O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.S 2 false) - TileCentroid
            (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * u)))
            → ((TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) → (((GaussianRealPoint ((1 - I) * w)).1 +
            (GaussianRealPoint ((1 - I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) →
            (((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 - I) * t)).2 +
            (GaussianRealPoint ((1 - I) * u)).2 = 0) → (TileCentroid (cert.S 2 false) -
            TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hOcent hS3cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.S 2 false) - TileCentroid (cert.P 0 false)) +
        (TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true)) -
        (TileCentroid cert.O - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hS3cent, hPminus, hOcent]
      ext
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointSnd

private theorem hS2O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.S 1 false) - TileCentroid
            (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * t)))
            → ((TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true) = (-1 : Real) •
            GaussianRealPoint ((1 - I) * w)) → (((GaussianRealPoint ((1 - I) * w)).1 +
            (GaussianRealPoint ((1 - I) * t)).1 + (GaussianRealPoint ((1 - I) * u)).1 = 0) →
            (((GaussianRealPoint ((1 - I) * w)).2 + (GaussianRealPoint ((1 - I) * t)).2 +
            (GaussianRealPoint ((1 - I) * u)).2 = 0) → (TileCentroid (cert.S 1 false) -
            TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * u)))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hOcent hS2cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false)) +
        (TileCentroid (cert.P 0 false) - TileCentroid (cert.P 0 true)) -
        (TileCentroid cert.O - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hS2cent, hPminus, hOcent]
      ext
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (-1 / 2 : Real) * hsumGaussianPointSnd

private theorem hQ3O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid cert.O - TileCentroid (cert.P 0 true) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * w))) → ((TileCentroid (cert.Q 2 true) - TileCentroid
            (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * u)) →
            (((GaussianRealPoint ((1 - I) * w)).1 + (GaussianRealPoint ((1 - I) * t)).1 +
            (GaussianRealPoint ((1 - I) * u)).1 = 0) → (((GaussianRealPoint ((1 - I) * w)).2 +
            (GaussianRealPoint ((1 - I) * t)).2 + (GaussianRealPoint ((1 - I) * u)).2 = 0) →
            (TileCentroid (cert.Q 2 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * t)))))) ) := by
  classical
  intro q cfg C₀ T cert I u w t hOcent hQ3cent hsumGaussianPointFst hsumGaussianPointSnd
  calc
    _ = (TileCentroid (cert.Q 2 true) - TileCentroid (cert.P 0 true)) -
        (TileCentroid cert.O - TileCentroid (cert.P 0 true)) := by abel
    _ = _ := by
      rw [hQ3cent, hOcent]
      ext
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointFst
      · simp [smul_eq_mul]
        linear_combination (1 / 2 : Real) * hsumGaussianPointSnd

private theorem hA1Wvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 2) = I * u) → ((BandVectors.1 (birth 2) (birth 0) = u) →
            (I * (BandVectors.1 (birth 0) (birth 2) + BandVectors.1 (birth 2) (birth 0)) = (I -
            1) * u))) ) := by
  classical
  intro q cfg birth I hI2mul u hforward2 hback2
  rw [hforward2, hback2]
  rw [mul_add, ← mul_assoc, hI2mul]
  ring

private theorem hA1Zvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((BandVectors.1 (birth 3) (birth 0) = -I * t) →
            (I * (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0) (birth 3)) = (1 -
            I) * t))) ) := by
  classical
  intro q cfg birth I hI2mul t hforward3 hback3
  rw [hback3, hforward3]
  rw [sub_eq_add_neg, mul_add, ← mul_assoc]
  simp [hI2mul]
  ring

private theorem hA2Wvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((BandVectors.1 (birth 3) (birth 0) = -I * t) →
            (BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth 0) = (1 - I) *
            t)) ) := by
  classical
  intro q cfg birth I t hforward3 hback3
  rw [hforward3, hback3]
  ring

private theorem hA2Zvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 2) = I * u) → ((BandVectors.1 (birth 2) (birth 0) = u) →
            (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth 2) (birth 0) = (I - 1) *
            u)) ) := by
  classical
  intro q cfg birth I u hforward2 hback2
  rw [hforward2, hback2]
  ring

private theorem hB1Wvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 3 = -I) → ((I * I = -1) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 2) = I * u) → ((BandVectors.1 (birth 2) (birth 0) = u) →
            (I ^ 3 * (BandVectors.1 (birth 0) (birth 2) + BandVectors.1 (birth 2) (birth 0)) = (1
            - I) * u)))) ) := by
  classical
  intro q cfg birth I hI3 hI2mul u hforward2 hback2
  rw [hI3, hforward2, hback2]
  rw [mul_add, ← mul_assoc]
  simp [hI2mul]
  ring

private theorem hB1Zvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 3 = -I) → ((I * I = -1) → (
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((BandVectors.1 (birth 3) (birth 0) = -I * t) →
            (I ^ 3 * (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0) (birth 3)) = (I
            - 1) * t)))) ) := by
  classical
  intro q cfg birth I hI3 hI2mul t hforward3 hback3
  rw [hI3, hback3, hforward3]
  rw [sub_eq_add_neg, mul_add, ← mul_assoc]
  simp [hI2mul]
  ring

private theorem hB2Wvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((BandVectors.1 (birth 3) (birth 0) = -I * t) →
            (I ^ 2 * (BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth 0)) =
            -((1 - I) * t)))) ) := by
  classical
  intro q cfg birth I hI2 t hforward3 hback3
  rw [hI2, hforward3, hback3]
  ring

private theorem hB2Zvec :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (birth
            : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 0) (birth 2) = I * u) → ((BandVectors.1 (birth 2) (birth 0) = u) →
            (I ^ 2 * (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth 2) (birth 0)) = (1
            - I) * u))) ) := by
  classical
  intro q cfg birth I hI2 u hforward2 hback2
  rw [hI2, hforward2, hback2]
  ring

private theorem hA1W :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (∀ (x : GaussianInt), GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x))
            → ((TileCentroid (cert.Q 1 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * u))) → ((I * (BandVectors.1 (birth 0) (birth 2)
            + BandVectors.1 (birth 2) (birth 0)) = (I - 1) * u) → (TileCentroid (cert.Q 1 true) -
            TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint (I * (BandVectors.1 (birth
            0) (birth 2) + BandVectors.1 (birth 2) (birth 0)))))) ) := by
  classical
  intro q cfg C₀ T cert birth I u gaussianPoint_Iminus_one hQ2O hA1Wvec
  rw [hA1Wvec, gaussianPoint_Iminus_one]
  simpa [smul_eq_mul] using hQ2O

private theorem hA1Z :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid (cert.S 2 false) - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint
            ((1 - I) * t)) → ((I * (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0)
            (birth 3)) = (1 - I) * t) → (TileCentroid (cert.S 2 false) - TileCentroid cert.O = (1
            / 2 : Real) • GaussianRealPoint (I * (BandVectors.1 (birth 3) (birth 0) -
            BandVectors.1 (birth 0) (birth 3))))) ) := by
  classical
  intro q cfg C₀ T cert birth I t hS3O hA1Zvec
  rw [hA1Zvec]
  exact hS3O

private theorem hA2W :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (TileCentroid (cert.S 2 false) - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint
            ((1 - I) * t)) → ((BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth
            0) = (1 - I) * t) → (TileCentroid (cert.S 2 false) - TileCentroid cert.O = (1 / 2 :
            Real) • GaussianRealPoint (BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth
            3) (birth 0)))) ) := by
  classical
  intro q cfg C₀ T cert birth I t hS3O hA2Wvec
  rw [hA2Wvec]
  exact hS3O

private theorem hA2Z :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (∀ (x : GaussianInt), GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x))
            → ((TileCentroid (cert.Q 1 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * u))) → ((BandVectors.1 (birth 0) (birth 2) -
            BandVectors.1 (birth 2) (birth 0) = (I - 1) * u) → (TileCentroid (cert.Q 1 true) -
            TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint (BandVectors.1 (birth 0)
            (birth 2) - BandVectors.1 (birth 2) (birth 0))))) ) := by
  classical
  intro q cfg C₀ T cert birth I u gaussianPoint_Iminus_one hQ2O hA2Zvec
  rw [hA2Zvec, gaussianPoint_Iminus_one]
  simpa [smul_eq_mul] using hQ2O

private theorem hB1W :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (TileCentroid (cert.S 1 false) - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint
            ((1 - I) * u)) → ((I ^ 3 * (BandVectors.1 (birth 0) (birth 2) + BandVectors.1 (birth
            2) (birth 0)) = (1 - I) * u) → (TileCentroid (cert.S 1 false) - TileCentroid cert.O =
            (1 / 2 : Real) • GaussianRealPoint (I ^ 3 * (BandVectors.1 (birth 0) (birth 2) +
            BandVectors.1 (birth 2) (birth 0))))) ) := by
  classical
  intro q cfg C₀ T cert birth I u hS2O hB1Wvec
  rw [hB1Wvec]
  exact hS2O

private theorem hB1Z :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (∀ (x : GaussianInt), GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x))
            → ((TileCentroid (cert.Q 2 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * t))) → ((I ^ 3 * (BandVectors.1 (birth 3) (birth
            0) - BandVectors.1 (birth 0) (birth 3)) = (I - 1) * t) → (TileCentroid (cert.Q 2
            true) - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint (I ^ 3 *
            (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0) (birth 3)))))) ) := by
  classical
  intro q cfg C₀ T cert birth I t gaussianPoint_Iminus_one hQ3O hB1Zvec
  rw [hB1Zvec, gaussianPoint_Iminus_one]
  simpa [smul_eq_mul] using hQ3O

private theorem hB2W :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (∀ (x : GaussianInt), GaussianRealPoint (-x) = -GaussianRealPoint x) → ((TileCentroid
            (cert.Q 2 true) - TileCentroid cert.O = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * t))) → ((I ^ 2 * (BandVectors.1 (birth 0) (birth 3) +
            BandVectors.1 (birth 3) (birth 0)) = -((1 - I) * t)) → (TileCentroid (cert.Q 2 true)
            - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint (I ^ 2 * (BandVectors.1
            (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth 0)))))) ) := by
  classical
  intro q cfg C₀ T cert birth I t gaussianPoint_neg hQ3O hB2Wvec
  rw [hB2Wvec, gaussianPoint_neg]
  simpa [smul_eq_mul] using hQ3O

private theorem hB2Z :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (TileCentroid (cert.S 1 false) - TileCentroid cert.O = (1 / 2 : Real) • GaussianRealPoint
            ((1 - I) * u)) → ((I ^ 2 * (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth
            2) (birth 0)) = (1 - I) * u) → (TileCentroid (cert.S 1 false) - TileCentroid cert.O =
            (1 / 2 : Real) • GaussianRealPoint (I ^ 2 * (BandVectors.1 (birth 0) (birth 2) -
            BandVectors.1 (birth 2) (birth 0))))) ) := by
  classical
  intro q cfg C₀ T cert birth I u hS2O hB2Zvec
  rw [hB2Zvec]
  exact hS2O

private theorem hnotA1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 2) (birth 0) = u) → ((cert.exceptionalSegments.a ∈
            FootprintVertices cert.O) → ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.Q
            (1 : Fin (3 : ℕ)) true)) → ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.S
            (2 : Fin (3 : ℕ)) false)) → (∀ (rightA1 : ExactTileInterfaceTriple cert.O
            (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(1 : Fin (4 : ℕ)) :
            ℕ) * if Even (↑(1 : Fin (4 : ℕ)) : ℕ) then BandVectors.1 (birth (0 : Fin (4 : ℕ)))
            (birth (Fin.succ (1 : Fin (3 : ℕ)))) else BandVectors.1 (birth (Fin.succ (1 : Fin (3
            : ℕ)))) (birth (0 : Fin (4 : ℕ))))) (cert.Q (1 : Fin (3 : ℕ)) true)), ∀ (incomingA1 :
            ExactTileInterfaceTriple cert.O (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑(1 : Fin (4 : ℕ)) : ℕ) * if Even (↑(1 : Fin (4 : ℕ)) : ℕ) then
            BandVectors.1 (birth (Fin.succ (1 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else
            BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (1 : Fin (3 : ℕ))))))
            (cert.Q (1 : Fin (3 : ℕ)) true)), ∀ (adjacentA1 : ExactTileInterfaceTriple cert.O
            (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)), (rightA1.point ≠
            incomingA1.point) → ((adjacentA1.point = incomingA1.point) →
            (cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O (I *
            u))))))))) ) := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion I u hback2 haO haQ2 haS3 rightA1 incomingA1
      adjacentA1 hneA1 halignA1
  have hn := exact_exclusion _ _ _ _ rightA1 adjacentA1 incomingA1.point
    hneA1 halignA1 cert.exceptionalSegments.a haO haQ2 haS3
  simpa [I, hback2] using hn

private theorem hnotA2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((cert.exceptionalSegments.a ∈
            FootprintVertices cert.O) → ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.Q
            (1 : Fin (3 : ℕ)) true)) → ((cert.exceptionalSegments.a ∈ FootprintVertices (cert.S
            (2 : Fin (3 : ℕ)) false)) → (∀ (rightA2 : ExactTileInterfaceTriple cert.O
            (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(0 : Fin (4 : ℕ)) :
            ℕ) * if Even (↑(0 : Fin (4 : ℕ)) : ℕ) then BandVectors.1 (birth (0 : Fin (4 : ℕ)))
            (birth (Fin.succ (2 : Fin (3 : ℕ)))) else BandVectors.1 (birth (Fin.succ (2 : Fin (3
            : ℕ)))) (birth (0 : Fin (4 : ℕ))))) (cert.S (2 : Fin (3 : ℕ)) false)), ∀ (incomingA2
            : ExactTileInterfaceTriple cert.O (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑(0 : Fin (4 : ℕ)) : ℕ) * if Even (↑(0 : Fin (4 : ℕ)) : ℕ) then
            BandVectors.1 (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else
            BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 : ℕ))))))
            (cert.S (2 : Fin (3 : ℕ)) false)), ∀ (adjacentA2 : ExactTileInterfaceTriple cert.O
            (cert.S (2 : Fin (3 : ℕ)) false) (cert.Q (1 : Fin (3 : ℕ)) true)), (rightA2.point ≠
            incomingA2.point) → ((adjacentA2.point = incomingA2.point) →
            (cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O t)))))))) )
            := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion t hforward3 haO haQ2 haS3 rightA2 incomingA2
      adjacentA2 hneA2 halignA2
  have hn := exact_exclusion _ _ _ _ rightA2 adjacentA2 incomingA2.point
    hneA2 halignA2 cert.exceptionalSegments.a haO haS3 haQ2
  simpa [hforward3] using hn

private theorem hnotB1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 3 = -I) → (
        let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (BandVectors.1 (birth 2) (birth 0) = u) → ((cert.exceptionalSegments.b ∈
            FootprintVertices cert.O) → ((cert.exceptionalSegments.b ∈ FootprintVertices (cert.Q
            (2 : Fin (3 : ℕ)) true)) → ((cert.exceptionalSegments.b ∈ FootprintVertices (cert.S
            (1 : Fin (3 : ℕ)) false)) → (∀ (rightB1 : ExactTileInterfaceTriple cert.O
            (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(3 : Fin (4 : ℕ)) :
            ℕ) * if Even (↑(3 : Fin (4 : ℕ)) : ℕ) then BandVectors.1 (birth (0 : Fin (4 : ℕ)))
            (birth (Fin.succ (1 : Fin (3 : ℕ)))) else BandVectors.1 (birth (Fin.succ (1 : Fin (3
            : ℕ)))) (birth (0 : Fin (4 : ℕ))))) (cert.S (1 : Fin (3 : ℕ)) false)), ∀ (incomingB1
            : ExactTileInterfaceTriple cert.O (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑(3 : Fin (4 : ℕ)) : ℕ) * if Even (↑(3 : Fin (4 : ℕ)) : ℕ) then
            BandVectors.1 (birth (Fin.succ (1 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else
            BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (1 : Fin (3 : ℕ))))))
            (cert.S (1 : Fin (3 : ℕ)) false)), ∀ (adjacentB1 : ExactTileInterfaceTriple cert.O
            (cert.S (1 : Fin (3 : ℕ)) false) (cert.Q (2 : Fin (3 : ℕ)) true)), (rightB1.point ≠
            incomingB1.point) → ((adjacentB1.point = incomingB1.point) →
            (cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O (-((⟨0, 1⟩ :
            GaussianInt) * BandVectors.1 (q 2) (cfg.firstPredecessor 1)))))))))))) ) := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion I hI3 u hback2 hbO hbQ3 hbS2 rightB1 incomingB1
      adjacentB1 hneB1 halignB1
  have hn := exact_exclusion _ _ _ _ rightB1 adjacentB1 incomingB1.point
    hneB1 halignB1 cert.exceptionalSegments.b hbO hbS2 hbQ3
  have hn' := hn
  have hn'' : cert.exceptionalSegments.b ∉ FootprintVertices
      (TileTranslation cert.O (I ^ 3 * BandVectors.1 (birth 2) (birth 0))) := by
    split_ifs at hn' with hparity
    · rcases hparity with ⟨k, hk⟩
      omega
    · simpa [I] using hn'
  have hn''' : cert.exceptionalSegments.b ∉
      FootprintVertices (TileTranslation cert.O (-I * u)) := by
    simpa [hI3, hback2] using hn''
  have hshift : -I * u = -((⟨0, 1⟩ : GaussianInt) *
      BandVectors.1 (q 2) (cfg.firstPredecessor 1)) := by
    dsimp [I, u]
    ring
  rw [hshift] at hn'''
  exact hn'''

private theorem hnotB2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right : ExactTileInterfaceTriple U V W), ∀
            (adjacent : ExactTileInterfaceTriple U W Z), ∀ (incomingPoint : GaussianInt),
            (right.point ≠ incomingPoint) → ((adjacent.point = incomingPoint) → (∀ (cut :
            GaussianInt), (cut ∈ FootprintVertices U) → ((cut ∈ FootprintVertices W) → ((cut ∈
            FootprintVertices Z) → (cut ∉ FootprintVertices V)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (
        let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (birth 0) (birth 3) = t) → ((Even 2) → ((cert.exceptionalSegments.b ∈
            FootprintVertices cert.O) → ((cert.exceptionalSegments.b ∈ FootprintVertices (cert.Q
            (2 : Fin (3 : ℕ)) true)) → ((cert.exceptionalSegments.b ∈ FootprintVertices (cert.S
            (1 : Fin (3 : ℕ)) false)) → (∀ (rightB2 : ExactTileInterfaceTriple cert.O
            (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(2 : Fin (4 : ℕ)) :
            ℕ) * if Even (↑(2 : Fin (4 : ℕ)) : ℕ) then BandVectors.1 (birth (0 : Fin (4 : ℕ)))
            (birth (Fin.succ (2 : Fin (3 : ℕ)))) else BandVectors.1 (birth (Fin.succ (2 : Fin (3
            : ℕ)))) (birth (0 : Fin (4 : ℕ))))) (cert.Q (2 : Fin (3 : ℕ)) true)), ∀ (incomingB2 :
            ExactTileInterfaceTriple cert.O (TileTranslation cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑(2 : Fin (4 : ℕ)) : ℕ) * if Even (↑(2 : Fin (4 : ℕ)) : ℕ) then
            BandVectors.1 (birth (Fin.succ (2 : Fin (3 : ℕ)))) (birth (0 : Fin (4 : ℕ))) else
            BandVectors.1 (birth (0 : Fin (4 : ℕ))) (birth (Fin.succ (2 : Fin (3 : ℕ))))))
            (cert.Q (2 : Fin (3 : ℕ)) true)), ∀ (adjacentB2 : ExactTileInterfaceTriple cert.O
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false)), (rightB2.point ≠
            incomingB2.point) → ((adjacentB2.point = incomingB2.point) →
            (cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-t))))))))))) ) := by
  classical
  intro q cfg C₀ T cert birth exact_exclusion I hI2 t hforward3 hEven2 hbO hbQ3 hbS2 rightB2
      incomingB2 adjacentB2 hneB2 halignB2
  have hn := exact_exclusion _ _ _ _ rightB2 adjacentB2 incomingB2.point
    hneB2 halignB2 cert.exceptionalSegments.b hbO hbQ3 hbS2
  simpa [I, hI2, hEven2, hforward3] using hn

end PositiveCutExclusionGeometry

namespace PositiveCutBranchConclusion

private theorem fourthParentExclusion :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (birth : Fin 4 → CircleCoordinates), (ProperBandQuadruple birth) → ((∀ (X :
            ProtoTile), ∀ x ∈ BoundaryFootprintVertices X, x ∈ FootprintVertices X) → ((∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), ∀ (Z : ProtoTile), ∀ (right :
            ExactTileInterfaceTriple U V W), ∀ (adjacent : ExactTileInterfaceTriple U W Z), ∀
            (incomingPoint : GaussianInt), right.point ≠ incomingPoint → adjacent.point =
            incomingPoint → ∀ cut ∈ FootprintVertices U, cut ∈ FootprintVertices W → cut ∈
            FootprintVertices Z → cut ∉ FootprintVertices V) → ((0 < (q 2).1) → ((0 < (q 3).1) →
            ((0 < (cfg.firstPredecessor 1).1) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → ((I ^ 3 = -I) → ((I * I = -1) → (
        (
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let w := BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); TileCentroid cert.O -
            TileCentroid (cert.P (0 : Fin (3 : ℕ)) true) = (-1 : ℝ) • (1 / 2 : ℝ) •
            GaussianRealPoint (((1 : GaussianInt) - I) * w)) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let t := BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)));
            TileCentroid (cert.Q (1 : Fin (3 : ℕ)) true) - TileCentroid (cert.P (0 : Fin (3 : ℕ))
            true) = (1 / 2 : ℝ) • GaussianRealPoint (((1 : GaussianInt) - I) * t)) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let u := BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)));
            TileCentroid (cert.Q (2 : Fin (3 : ℕ)) true) - TileCentroid (cert.P (0 : Fin (3 : ℕ))
            true) = (1 / 2 : ℝ) • GaussianRealPoint (((1 : GaussianInt) - I) * u)) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let t := BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)));
            TileCentroid (cert.S (1 : Fin (3 : ℕ)) false) - TileCentroid (cert.P (0 : Fin (3 :
            ℕ)) false) = (-1 : ℝ) • (1 / 2 : ℝ) • GaussianRealPoint (((1 : GaussianInt) - I) *
            t)) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let u := BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)));
            TileCentroid (cert.S (2 : Fin (3 : ℕ)) false) - TileCentroid (cert.P (0 : Fin (3 :
            ℕ)) false) = (-1 : ℝ) • (1 / 2 : ℝ) • GaussianRealPoint (((1 : GaussianInt) - I) *
            u)) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let w := BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); TileCentroid (cert.P
            (0 : Fin (3 : ℕ)) false) - TileCentroid (cert.P (0 : Fin (3 : ℕ)) true) = (-1 : ℝ) •
            GaussianRealPoint (((1 : GaussianInt) - I) * w)) → ((∀ (x : GaussianInt),
            GaussianRealPoint (-x) = -GaussianRealPoint x) → ((∀ (x : GaussianInt),
            GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x)) →
            (((GaussianRealPoint (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).1 + (GaussianRealPoint
            (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.1
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).1 +
            (GaussianRealPoint (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))))).1 = (0
            : ℝ)) → (((GaussianRealPoint (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).2 +
            (GaussianRealPoint (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).2 +
            (GaussianRealPoint (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))))).2 = (0
            : ℝ)) → ((birth (0 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ)) ∧ birth (2
            : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)))
            → (((birth 0 = q 2 ∧ birth 2 = q 3 ∧ birth 3 = cfg.firstPredecessor 1) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation (cert.Q 1 true)
            (BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧ cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation (cert.S 1 false) (-BandVectors.1 (q 2)
            (cfg.firstPredecessor 1)))) ∨ ((birth 0 = cfg.firstPredecessor 1 ∧ birth 2 = q 2 ∧
            birth 3 = q 3) ∧ cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation
            cert.O ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O
            (BandVectors.1 (cfg.firstPredecessor 1) (q 3))) ∧ cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation cert.O (-((⟨0, 1⟩ : GaussianInt) * BandVectors.1
            (q 2) (cfg.firstPredecessor 1)))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation cert.O (-BandVectors.1 (cfg.firstPredecessor 1) (q
            3)))))))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert birth hproper boundary_to_raw exact_exclusion hq2pos hq3pos hOpos I hI2
      hI3 hI2mul hOcent hQ2cent hQ3cent hS2cent hS3cent hPminus gaussianPoint_neg
      gaussianPoint_Iminus_one hsumGaussianPointFst hsumGaussianPointSnd hp4
  let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
  let w : GaussianInt := BandVectors.1 (q 3) (q 2)
  let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
  have hf4 := (VectorRecursionLaws birth hproper.1).2.2.2.2 hproper
  have hforward2 : BandVectors.1 (birth 0) (birth 2) = I * u := by
    simpa [I, u, hp4.1, hp4.2.1] using (hf4 (1 : Fin 3)).1
  have hback2 : BandVectors.1 (birth 2) (birth 0) = u := by
    simp [u, hp4.1, hp4.2.1]
  have hforward3 : BandVectors.1 (birth 0) (birth 3) = t := by
    simp [t, hp4.1, hp4.2.2]
  have hflip3 : t = I * BandVectors.1 (birth 3) (birth 0) := by
    simpa [I, t, hp4.1, hp4.2.2] using (hf4 (2 : Fin 3)).1
  have hback3 := PositiveCutExclusionGeometry.hback3 q cfg birth hflip3
  have hOproto : BandPrototile (birth 0) cert.O := by
    simpa [hp4.1, cert.precursor_eq] using (cert.plus_occurrence 0 false).1
  have hQ2proto : BandPrototile (birth 2) (cert.Q 1 true) := by
    simpa [hp4.2.1, cfg.firstParentTwo] using (cert.plus_occurrence 1 true).1
  have hQ3proto : BandPrototile (birth 3) (cert.Q 2 true) := by
    simpa [hp4.2.2, cfg.firstParentThree] using (cert.plus_occurrence 2 true).1
  have hS2proto : BandPrototile (birth 2) (cert.S 1 false) := by
    simpa [hp4.2.1, cfg.firstParentTwo] using (cert.minus_occurrence 1 false).1
  have hS3proto : BandPrototile (birth 3) (cert.S 2 false) := by
    simpa [hp4.2.2, cfg.firstParentThree] using (cert.minus_occurrence 2 false).1
  have hQ2O := PositiveCutExclusionGeometry.hQ2O q cfg C₀ T cert hOcent hQ2cent
      hsumGaussianPointFst
          hsumGaussianPointSnd
  have hS3O := PositiveCutExclusionGeometry.hS3O q
          cfg C₀ T cert hOcent hS3cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  have hS2O := PositiveCutExclusionGeometry.hS2O q
          cfg C₀ T cert hOcent hS2cent hPminus hsumGaussianPointFst hsumGaussianPointSnd
  have hQ3O := PositiveCutExclusionGeometry.hQ3O q cfg C₀ T cert hOcent hQ3cent
      hsumGaussianPointFst
          hsumGaussianPointSnd
  have hbirth2pos : 0 < (birth 2).1 := by simpa [hp4.2.1] using hq2pos
  have hbirth3pos : 0 < (birth 3).1 := by simpa [hp4.2.2] using hq3pos
  have hbirth0pos : 0 < (birth 0).1 := by
    simpa [hp4.1, cert.precursor_eq] using hOpos
  have hEven2 : Even 2 := by decide
  have hEven3 : ¬ Even 3 := by decide
  have hA1W : TileCentroid (cert.Q 1 true) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I * (BandVectors.1 (birth 0) (birth 2) + BandVectors.1 (birth 2) (birth 0))) :=
            PositiveCutExclusionGeometry.hA1W q cfg C₀ T cert birth gaussianPoint_Iminus_one
            hQ2O (PositiveCutExclusionGeometry.hA1Wvec q cfg birth hI2mul hforward2 hback2)
  have hA1Z : TileCentroid (cert.S 2 false) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I * (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0) (birth 3))) :=
            PositiveCutExclusionGeometry.hA1Z q cfg C₀ T cert birth hS3O
                (PositiveCutExclusionGeometry.hA1Zvec q cfg birth hI2mul hforward3 hback3)
  have hA2W : TileCentroid (cert.S 2 false) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth 0)) :=
            PositiveCutExclusionGeometry.hA2W q cfg C₀ T cert birth hS3O
                (PositiveCutExclusionGeometry.hA2Wvec q cfg birth hforward3 hback3)
  have hA2Z : TileCentroid (cert.Q 1 true) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth 2) (birth 0)) :=
            PositiveCutExclusionGeometry.hA2Z q cfg C₀ T cert birth gaussianPoint_Iminus_one
            hQ2O (PositiveCutExclusionGeometry.hA2Zvec q cfg birth hforward2 hback2)
  have hB1W : TileCentroid (cert.S 1 false) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I ^ 3 * (BandVectors.1 (birth 0) (birth 2) + BandVectors.1 (birth 2) (birth 0))) :=
            PositiveCutExclusionGeometry.hB1W q cfg C₀ T cert birth hS2O
                (PositiveCutExclusionGeometry.hB1Wvec q cfg birth hI3 hI2mul hforward2 hback2)
  have hB1Z : TileCentroid (cert.Q 2 true) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I ^ 3 * (BandVectors.1 (birth 3) (birth 0) - BandVectors.1 (birth 0) (birth 3))) :=
            PositiveCutExclusionGeometry.hB1Z q cfg C₀ T cert birth gaussianPoint_Iminus_one
            hQ3O (PositiveCutExclusionGeometry.hB1Zvec q cfg birth hI3 hI2mul hforward3 hback3)
  have hB2W : TileCentroid (cert.Q 2 true) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I ^ 2 * (BandVectors.1 (birth 0) (birth 3) + BandVectors.1 (birth 3) (birth 0))) :=
            PositiveCutExclusionGeometry.hB2W q cfg C₀ T cert birth gaussianPoint_neg hQ3O
                (PositiveCutExclusionGeometry.hB2Wvec q cfg birth hI2 hforward3 hback3)
  have hB2Z : TileCentroid (cert.S 1 false) - TileCentroid cert.O =
      (1 / 2 : Real) • GaussianRealPoint
        (I ^ 2 * (BandVectors.1 (birth 0) (birth 2) - BandVectors.1 (birth 2) (birth 0))) :=
            PositiveCutExclusionGeometry.hB2Z q cfg C₀ T cert birth hS2O
                (PositiveCutExclusionGeometry.hB2Zvec q cfg birth hI2 hforward2 hback2)
  have haBoundary := (cert.exceptionalSegments.first_cut_unique
    cert.exceptionalSegments.a).mpr rfl
  have haO := boundary_to_raw cert.O cert.exceptionalSegments.a haBoundary.2.2
  have haQ2 := boundary_to_raw (cert.Q 1 true) cert.exceptionalSegments.a haBoundary.1
  have haS3 := boundary_to_raw (cert.S 2 false) cert.exceptionalSegments.a haBoundary.2.1
  have hbBoundary := (cert.exceptionalSegments.second_cut_unique
    cert.exceptionalSegments.b).mpr rfl
  have hbO := boundary_to_raw cert.O cert.exceptionalSegments.b hbBoundary.2.2
  have hbQ3 := boundary_to_raw (cert.Q 2 true) cert.exceptionalSegments.b hbBoundary.1
  have hbS2 := boundary_to_raw (cert.S 1 false) cert.exceptionalSegments.b hbBoundary.2.1
  have endpointA1 := BandOrientedChildParentEndpoints birth hproper
    (1 : Fin 3) 1 cert.O (cert.Q 1 true) (cert.S 2 false)
    hOproto hQ2proto hS3proto hbirth0pos hbirth2pos hbirth3pos
    (by
      have hs := add_comm (BandVectors.1 (birth 0) (birth 2))
        (BandVectors.1 (birth 2) (birth 0))
      rw [hs] at hA1W
      simpa [I] using hA1W)
    (by simpa [I] using hA1Z)
  rcases endpointA1 with ⟨rightA1, incomingA1, adjacentA1, hneA1, halignA1, _, _, _⟩
  have hnotA1 := PositiveCutExclusionGeometry.hnotA1 q cfg C₀ T cert
          birth exact_exclusion hback2 haO haQ2 haS3 rightA1 incomingA1 adjacentA1 hneA1 halignA1
  have endpointA2 := BandOrientedChildParentEndpoints birth hproper
    (2 : Fin 3) 0 cert.O (cert.S 2 false) (cert.Q 1 true)
    hOproto hS3proto hQ2proto hbirth0pos hbirth3pos hbirth2pos
    (by simpa [add_comm] using hA2W) (by simpa using hA2Z)
  rcases endpointA2 with ⟨rightA2, incomingA2, adjacentA2, hneA2, halignA2, _, _, _⟩
  have hnotA2 := PositiveCutExclusionGeometry.hnotA2 q cfg C₀ T cert birth
          exact_exclusion hforward3 haO haQ2 haS3 rightA2 incomingA2 adjacentA2 hneA2 halignA2
  have endpointB1 := BandOrientedChildParentEndpoints birth hproper
    (1 : Fin 3) 3 cert.O (cert.S 1 false) (cert.Q 2 true)
    hOproto hS2proto hQ3proto hbirth0pos hbirth2pos hbirth3pos
    (by
      have hs := add_comm (BandVectors.1 (birth 0) (birth 2))
        (BandVectors.1 (birth 2) (birth 0))
      rw [hs] at hB1W
      simpa [I] using hB1W)
    (by simpa [I, hEven3] using hB1Z)
  rcases endpointB1 with ⟨rightB1, incomingB1, adjacentB1, hneB1, halignB1, _, _, _⟩
  have hnotB1 := PositiveCutExclusionGeometry.hnotB1
            q cfg C₀ T cert birth exact_exclusion hI3 hback2 hbO hbQ3 hbS2 rightB1 incomingB1
            adjacentB1 hneB1 halignB1
  have endpointB2 := BandOrientedChildParentEndpoints birth hproper
    (2 : Fin 3) 2 cert.O (cert.Q 2 true) (cert.S 1 false)
    hOproto hQ3proto hS2proto hbirth0pos hbirth3pos hbirth2pos
    (by simpa [I, add_comm] using hB2W) (by simpa using hB2Z)
  rcases endpointB2 with ⟨rightB2, incomingB2, adjacentB2, hneB2, halignB2, _, _, _⟩
  exact Or.inr ⟨hp4, hnotA1, hnotA2, hnotB1, (PositiveCutExclusionGeometry.hnotB2 q cfg C₀ T
      cert birth exact_exclusion hI2 hforward3 hEven2 hbO hbQ3 hbS2 rightB2 incomingB2
      adjacentB2 hneB2 halignB2)⟩

end PositiveCutBranchConclusion

theorem BandPositiveCutBranchCompanionExclusion
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hO : cert.O.cells.Nonempty)
    (birth : Fin 4 → CircleCoordinates)
    (hproper : ProperBandQuadruple birth)
    (hbranch :
      (birth 0 = q 2 ∧ birth 2 = q 3 ∧
        birth 3 = cfg.firstPredecessor 1) ∨
      (birth 0 = cfg.firstPredecessor 1 ∧ birth 2 = q 2 ∧
        birth 3 = q 3)) :
    ((birth 0 = q 2 ∧ birth 2 = q 3 ∧
        birth 3 = cfg.firstPredecessor 1) ∧
      cert.exceptionalSegments.a ∉ FootprintVertices
        (TileTranslation (cert.Q 1 true)
          (BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧
      cert.exceptionalSegments.b ∉ FootprintVertices
        (TileTranslation (cert.S 1 false)
          (-BandVectors.1 (q 2) (cfg.firstPredecessor 1)))) ∨
    ((birth 0 = cfg.firstPredecessor 1 ∧ birth 2 = q 2 ∧
        birth 3 = q 3) ∧
      cert.exceptionalSegments.a ∉ FootprintVertices
        (TileTranslation cert.O
          ((⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧
      cert.exceptionalSegments.a ∉ FootprintVertices
        (TileTranslation cert.O
          (BandVectors.1 (cfg.firstPredecessor 1) (q 3))) ∧
      cert.exceptionalSegments.b ∉ FootprintVertices
        (TileTranslation cert.O
          (-((⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 2) (cfg.firstPredecessor 1)))) ∧
      cert.exceptionalSegments.b ∉ FootprintVertices
        (TileTranslation cert.O
          (-BandVectors.1 (cfg.firstPredecessor 1) (q 3)))) := by
-- BODY
  have boundary_to_raw := PositiveCutExclusionGeometry.boundary_to_raw
      (PositiveCutExclusionGeometry.boundary_edge_footprint)
      (PositiveCutExclusionGeometry.edge_vertex_footprint)
  have exact_exclusion := PositiveCutExclusionGeometry.exact_exclusion
  have occurrence_centroid := PositiveCutExclusionGeometry.occurrence_centroid
  have hcurv := ProperBandCurvatureStructure q cfg.proper
  have hq2pos : 0 < (q 2).1 := by have := cfg.secondLarge; omega
  have hq3pos : 0 < (q 3).1 := PositiveCutExclusionGeometry.hq3pos q cfg hcurv
  have hOpos : 0 < (cfg.firstPredecessor 1).1 := PositiveCutExclusionGeometry.hOpos q cfg C₀ T
      cert hO (PositiveCutExclusionGeometry.positive_of_nonempty)
  let I : GaussianInt := ⟨0, 1⟩
  have hI2 : I ^ 2 = -1 := by dsimp [I]; decide
  have hI3 : I ^ 3 = -I := by dsimp [I]; decide
  have hI2mul : I * I = -1 := by dsimp [I]; decide
  let u : GaussianInt := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
  let w : GaussianInt := BandVectors.1 (q 3) (q 2)
  let t : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
  have hOcent := PositiveCutExclusionGeometry.hOcent q cfg C₀ T cert occurrence_centroid
  have hQ2cent := PositiveCutExclusionGeometry.hQ2cent q
          cfg C₀ T cert occurrence_centroid
  have hQ3cent := PositiveCutExclusionGeometry.hQ3cent q
          cfg C₀ T cert occurrence_centroid
  have hS2cent := PositiveCutExclusionGeometry.hS2cent q cfg C₀ T cert occurrence_centroid
  have hS3cent := PositiveCutExclusionGeometry.hS3cent q cfg C₀ T cert occurrence_centroid
  have hPminus := PositiveCutExclusionGeometry.hPminus q cfg
          C₀ T cert occurrence_centroid
  have gaussianPoint_neg (x : GaussianInt) :
      GaussianRealPoint (-x) = -GaussianRealPoint x :=
          PositiveCutExclusionGeometry.gaussianPoint_neg x
  have gaussianPoint_Iminus_one (x : GaussianInt) :
      GaussianRealPoint ((I - 1) * x) = -GaussianRealPoint ((1 - I) * x) :=
          PositiveCutExclusionGeometry.gaussianPoint_Iminus_one gaussianPoint_neg x
  have hsumGaussianPoint := PositiveCutExclusionGeometry.hsumGaussianPoint q
            cfg (PositiveCutExclusionGeometry.gaussianPoint_add)
                (PositiveCutExclusionGeometry.hprod q cfg (PositiveCutExclusionGeometry.hsum q cfg))
  have hsumGaussianPointFst := PositiveCutExclusionGeometry.hsumGaussianPointFst q cfg
      hsumGaussianPoint
  have hsumGaussianPointSnd := PositiveCutExclusionGeometry.hsumGaussianPointSnd q cfg
      hsumGaussianPoint
  rcases hbranch with hp2 | hp4
  · -- The two p2 endpoint packages are used only in this branch.
    have hf := (VectorRecursionLaws birth hproper.1).2.2.2.2 hproper
    have hforward' : BandVectors.1 (birth 0) (birth 3) = u := by
      simp [u, hp2.1, hp2.2.2]
    have hbackAdj : BandVectors.1 (birth 2) (birth 0) = w := by
      simp [hp2.1, hp2.2.1, w]
    have hargA : BandVectors.1 (birth 3) (birth 0) +
        BandVectors.1 (birth 0) (birth 3) = (1 - I) * u := PositiveCutExclusionGeometry.hargA q
            cfg birth (PositiveCutExclusionGeometry.hreverse q cfg birth
                (PositiveCutExclusionGeometry.hforward q cfg birth hp2 hf)) hforward'
    have hargAdj : BandVectors.1 (birth 0) (birth 2) -
        BandVectors.1 (birth 2) (birth 0) = (I - 1) * w := PositiveCutExclusionGeometry.hargAdj q
            birth (PositiveCutExclusionGeometry.hrootAdj q cfg birth hp2 hf) hbackAdj
    have hU : BandPrototile (birth 0) (cert.Q 1 true) := by
      simpa [hp2.1, cfg.firstParentTwo] using (cert.plus_occurrence 1 true).1
    have hW : BandPrototile (birth 3) cert.O := by
      simpa [hp2.2.2, cert.precursor_eq] using (cert.plus_occurrence 0 false).1
    have hZ : BandPrototile (birth 2) (cert.S 2 false) := by
      simpa [hp2.2.1, cfg.firstParentThree] using (cert.minus_occurrence 2 false).1
    have hUpos : 0 < (birth 0).1 := by simpa [hp2.1] using hq2pos
    have hWpos : 0 < (birth 3).1 := by simpa [hp2.2.2] using hOpos
    have hZpos : 0 < (birth 2).1 := by simpa [hp2.2.1] using hq3pos
    have hWcent' : TileCentroid cert.O - TileCentroid (cert.Q 1 true) =
        (1 / 2 : Real) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
            (BandVectors.1 (birth 3) (birth 0) + BandVectors.1 (birth 0) (birth 3))) :=
                PositiveCutExclusionGeometry.hWcent'At387 q cfg C₀ T cert birth
                    (PositiveCutExclusionGeometry.hWcent q cfg C₀ T cert birth hOcent hQ2cent
                    hsumGaussianPointFst hsumGaussianPointSnd hargA)
    have hZcent' := (PositiveCutExclusionGeometry.hZcent q cfg C₀ T cert hQ2cent hS3cent hPminus
        hsumGaussianPointFst hsumGaussianPointSnd)
    have endpoint := BandOrientedChildParentEndpoints birth hproper
      (2 : Fin 3) 0 (cert.Q 1 true) cert.O (cert.S 2 false)
      hU hW hZ hUpos hWpos hZpos hWcent'
      (by simpa [I, hargAdj, gaussianPoint_Iminus_one] using hZcent')
    rcases endpoint with ⟨right, incoming, adjacent, hne, halign, _, _, _⟩
    have haBoundary := (cert.exceptionalSegments.first_cut_unique
      cert.exceptionalSegments.a).mpr rfl
    have haU := boundary_to_raw (cert.Q 1 true) cert.exceptionalSegments.a haBoundary.1
    have haZ := boundary_to_raw (cert.S 2 false) cert.exceptionalSegments.a haBoundary.2.1
    have haW := boundary_to_raw cert.O cert.exceptionalSegments.a haBoundary.2.2
    have hnotA := PositiveCutExclusionGeometry.hnotA q cfg C₀ T cert
            birth exact_exclusion hforward' right incoming adjacent hne halign haU haZ haW
    have hU' : BandPrototile (birth 0) (cert.S 1 false) := by
      simpa [hp2.1, cfg.firstParentTwo] using (cert.minus_occurrence 1 false).1
    have hZ' : BandPrototile (birth 2) (cert.Q 2 true) := by
      simpa [hp2.2.1, cfg.firstParentThree] using (cert.plus_occurrence 2 true).1
    have hWcent' : TileCentroid cert.O - TileCentroid (cert.S 1 false) =
        (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) * u)) :=
            PositiveCutExclusionGeometry.hWcent'At413 q cfg C₀ T cert hOcent hS2cent hPminus
            hsumGaussianPointFst hsumGaussianPointSnd
    have hZcent' : TileCentroid (cert.Q 2 true) - TileCentroid (cert.S 1 false) =
        (1 / 2 : Real) • GaussianRealPoint ((1 - I) * w) :=
            PositiveCutExclusionGeometry.hZcent'At426 q cfg C₀ T cert hQ3cent hS2cent hPminus
            hsumGaussianPointFst hsumGaussianPointSnd
    have endpoint' := BandOrientedChildParentEndpoints birth hproper
      (2 : Fin 3) 2 (cert.S 1 false) cert.O (cert.Q 2 true)
      hU' hW hZ' hUpos hWpos hZpos
      (by simpa [I, hI2, hargA, gaussianPoint_neg] using hWcent')
      (by simpa [I, hI2, hargAdj, gaussianPoint_Iminus_one, gaussianPoint_neg] using hZcent')
    rcases endpoint' with ⟨right', incoming', adjacent', hne', halign', _, _, _⟩
    have hbBoundary := (cert.exceptionalSegments.second_cut_unique
      cert.exceptionalSegments.b).mpr rfl
    have hbU := boundary_to_raw (cert.S 1 false) cert.exceptionalSegments.b hbBoundary.2.1
    have hbZ := boundary_to_raw (cert.Q 2 true) cert.exceptionalSegments.b hbBoundary.1
    have hbW := boundary_to_raw cert.O cert.exceptionalSegments.b hbBoundary.2.2
    exact Or.inl ⟨hp2, hnotA, (PositiveCutExclusionGeometry.hnotB q cfg C₀ T cert birth
        exact_exclusion hI2 hforward' right' incoming' adjacent' hne' halign' hbU hbZ hbW)⟩
  · -- The four p4 endpoint packages are used only in this branch.
    have fourthParentExclusion :
      ((birth 0 = q 2 ∧ birth 2 = q 3 ∧
          birth 3 = cfg.firstPredecessor 1) ∧
        cert.exceptionalSegments.a ∉ FootprintVertices
          (TileTranslation (cert.Q 1 true)
            (BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧
        cert.exceptionalSegments.b ∉ FootprintVertices
          (TileTranslation (cert.S 1 false)
            (-BandVectors.1 (q 2) (cfg.firstPredecessor 1)))) ∨
      ((birth 0 = cfg.firstPredecessor 1 ∧ birth 2 = q 2 ∧
          birth 3 = q 3) ∧
        cert.exceptionalSegments.a ∉ FootprintVertices
          (TileTranslation cert.O
            ((⟨0, 1⟩ : GaussianInt) *
              BandVectors.1 (q 2) (cfg.firstPredecessor 1))) ∧
        cert.exceptionalSegments.a ∉ FootprintVertices
          (TileTranslation cert.O
            (BandVectors.1 (cfg.firstPredecessor 1) (q 3))) ∧
        cert.exceptionalSegments.b ∉ FootprintVertices
          (TileTranslation cert.O
            (-((⟨0, 1⟩ : GaussianInt) *
              BandVectors.1 (q 2) (cfg.firstPredecessor 1)))) ∧
        cert.exceptionalSegments.b ∉ FootprintVertices
          (TileTranslation cert.O
            (-BandVectors.1 (cfg.firstPredecessor 1) (q 3)))) :=
                PositiveCutBranchConclusion.fourthParentExclusion q cfg C₀ T cert birth hproper
                boundary_to_raw exact_exclusion hq2pos hq3pos hOpos hI2 hI3 hI2mul hOcent hQ2cent
                hQ3cent hS2cent hS3cent hPminus gaussianPoint_neg gaussianPoint_Iminus_one
                hsumGaussianPointFst hsumGaussianPointSnd hp4
    exact fourthParentExclusion


end ApollonianSuperharmonic

end
