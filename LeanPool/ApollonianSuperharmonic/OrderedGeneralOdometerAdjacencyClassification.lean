/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.P4261T1CentralCoordinates
public import LeanPool.ApollonianSuperharmonic.P4261T1RightCoordinates
public import LeanPool.ApollonianSuperharmonic.P4261T1EdgeExterior
public import LeanPool.ApollonianSuperharmonic.P4261T1SubtileCoordinates
public import LeanPool.ApollonianSuperharmonic.P4261T1ExteriorAdjacency
public import LeanPool.ApollonianSuperharmonic.P4261T1ContactAdjacency

-- [TABLET NODE: OrderedGeneralOdometerAdjacencyClassification]

/-!
# OrderedGeneralOdometerAdjacencyClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OdometerAdjacencyGeometry

private theorem normalize :
    (by
      classical
      exact
        ∀ (C : BandCircle), (¬((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction g (FordCircleCoordinate P.p P.q) = C.1.1) ∨ ∃ (g :
            BandPackingSymmetry) (K : DiamondParameter), BandPackingSymmetryCircleAction g
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))) = C.1.1)) → (∀ (q : Fin 4 →
            CircleCoordinates), (ProperBandQuadruple q) → ((q 0 = C.1.1) → (∃ (g :
            BandPackingSymmetry) (qbar : Fin 4 → CircleCoordinates), Nonempty
            (BandOrderedGeneralConfiguration qbar) ∧ qbar 0 = BandPackingSymmetryCircleAction g
            C.1.1))) ) := by
  classical
  intro C horbit q hq hqC
  obtain ⟨r, g, hregime⟩ := BandRegimeClassification q hq
  let qrot : Fin 4 → CircleCoordinates :=
    ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
  let qbar := BandPackingSymmetryQuadrupleAction g qrot
  have hchild : qbar 0 = BandPackingSymmetryCircleAction g C.1.1 := by
    simp [qbar, qrot, BandPackingSymmetryQuadrupleAction, hqC]
  obtain ⟨ginv, hcancel, _⟩ := BandPackingSymmetryInversePhaseCancellation.2 g
  have hgeneral : Nonempty (BandOrderedGeneralConfiguration qbar) := by
    change Xor (∃ P : FordFareyParameter, 1 < P.q ∧
        qbar = FordRecursiveQuadruple P)
      (Xor (∃ K : DiamondParameter, 1 < K.1 ∧ qbar = DiamondRecursiveQuadruple K)
        (Nonempty (BandOrderedGeneralConfiguration qbar))) at hregime
    rcases hregime with ⟨⟨P, _, heq⟩, _⟩ | ⟨hrest, _⟩
    · exfalso
      apply horbit
      left
      refine ⟨ginv, P, ?_⟩
      have he : FordCircleCoordinate P.p P.q =
          BandPackingSymmetryCircleAction g C.1.1 := by
        simpa [heq, FordRecursiveQuadruple] using hchild
      rw [he, hcancel]
    · rcases hrest with ⟨⟨K, _, heq⟩, _⟩ | ⟨hgeneral, _⟩
      · exfalso
        apply horbit
        right
        refine ⟨ginv, K, ?_⟩
        have he : DiamondRecursiveQuadruple K 0 =
            BandPackingSymmetryCircleAction g C.1.1 := by
          simpa [heq] using hchild
        rw [he, hcancel]
      · exact hgeneral
  exact ⟨g, qbar, hgeneral, hchild⟩

private theorem imageCircle :
    (by
      classical
      exact
        (-(1 : Fin 3) = 2) → ((-(2 : Fin 3) = 1) → (∀ (g : BandPackingSymmetry), ∀ (D :
            BandCircle), ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∀ (j : Fin
            4), (p j = D.1.1) → (∃ Dg : BandCircle, Dg.1.1 = BandPackingSymmetryCircleAction g
            D.1.1)))) ) := by
  classical
  intro neg1 neg2 g D p hp j hj
  let pg := BandPackingSymmetryQuadrupleAction g p
  have hpg := BandPackingSymmetryProperCovariance g p hp
  have hpos : 0 < (BandPackingSymmetryCircleAction g D.1.1).1 := by
    rw [(BandPackingSymmetryCovariance g).1]
    exact D.2
  have hoccurs : ∃ k : Fin 4, pg k = BandPackingSymmetryCircleAction g D.1.1 := by
    cases hrev : BandPackingSymmetryReversesOrientation g <;> fin_cases j
    all_goals
      first
      | exact ⟨0, by simpa [pg, BandPackingSymmetryQuadrupleAction, hrev, neg1, neg2] using
          (congrArg (BandPackingSymmetryCircleAction g) hj)⟩
      | exact ⟨1, by simpa [pg, BandPackingSymmetryQuadrupleAction, hrev, neg1, neg2] using
          (congrArg (BandPackingSymmetryCircleAction g) hj)⟩
      | exact ⟨2, by simpa [pg, BandPackingSymmetryQuadrupleAction, hrev, neg1, neg2] using
          (congrArg (BandPackingSymmetryCircleAction g) hj)⟩
      | exact ⟨3, by simpa [pg, BandPackingSymmetryQuadrupleAction, hrev, neg1, neg2] using
          (congrArg (BandPackingSymmetryCircleAction g) hj)⟩
  obtain ⟨k, hk⟩ := hoccurs
  exact ⟨⟨⟨BandPackingSymmetryCircleAction g D.1.1,
    Or.inl hpos, pg, hpg.1, k, hk⟩, hpos⟩, rfl⟩

private theorem transportS :
    (by
      classical
      exact
        (-(1 : Fin 3) = 2) → ((-(2 : Fin 3) = 1) → (∀ (g : BandPackingSymmetry), ∀ (A :
            BandCircle), ∀ (B : BandCircle), ∀ (Ag : BandCircle), ∀ (Bg : BandCircle), (Ag.1.1 =
            BandPackingSymmetryCircleAction g A.1.1) → ((Bg.1.1 = BandPackingSymmetryCircleAction
            g B.1.1) → (∀ (V : ProtoTile), ∀ (W : ProtoTile), ∀ (f : PartialOdometer), ∀ (k :
            PartialOdometer), (SubtileLatticeAdjacent A B V W f k) → (SubtileLatticeAdjacent Ag
            Bg (BandPackingSymmetryTileAction g V) (BandPackingSymmetryTileAction g W)
            (BandPackingSymmetryPartialOdometerAction g f)
            (BandPackingSymmetryPartialOdometerAction g k)))))) ) := by
  classical
  intro neg1 neg2 g A B Ag Bg hA hB V W f k hadj
  rcases hadj with ⟨hf, hk, p, p', hp, hp', q, i, s, hq, hqA, hqiB, hc, hx, hy⟩
  have hfq : TileOdometer (q 0) V f := by simpa [hqA] using hf
  have hkq : TileOdometer (q i.succ) W k := by simpa [hqiB] using hk
  have hpos : 0 < (q i.succ).1 := by simpa [hqiB] using B.2
  obtain ⟨d, r, r', s', _, _, hfg, hkg, hpr, hpr', hcg, hxg, hyg, _⟩ :=
    SubtileLatticeAdjacentPackingSymmetryTransport g q hq i s hpos
      V W f k p p' hfq hkq hp hp' hc hx hy
  let qg := BandPackingSymmetryQuadrupleAction g q
  let ig : Fin 3 := if BandPackingSymmetryReversesOrientation g then -i else i
  have hqgA : qg 0 = Ag.1.1 := by
    simp [qg, BandPackingSymmetryQuadrupleAction, hqA, hA]
  have hqgB : qg ig.succ = Bg.1.1 := by
    calc
      qg ig.succ = BandPackingSymmetryCircleAction g (q i.succ) := by
        cases hrev : BandPackingSymmetryReversesOrientation g <;> fin_cases i <;>
          simp [qg, ig, BandPackingSymmetryQuadrupleAction, hrev, neg1, neg2]
      _ = Bg.1.1 := (congrArg (BandPackingSymmetryCircleAction g) hqiB).trans hB.symm
  refine ⟨by simpa only [← hqgA] using hfg,
    by simpa only [← hqgB] using hkg, r, r', hpr, hpr', qg, ig, s',
    BandPackingSymmetryProperCovariance g q hq, hqgA, hqgB, hcg, hxg, hyg⟩

private theorem transportL :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (A : BandCircle), ∀ (Ag : BandCircle), (Ag.1.1 =
            BandPackingSymmetryCircleAction g A.1.1) → (∀ (V : ProtoTile), ∀ (W : ProtoTile), ∀
            (f : PartialOdometer), ∀ (k : PartialOdometer), (1 < A.1.1.1) → ((LeftLatticeAdjacent
            A V W f k) → (LeftLatticeAdjacent Ag (BandPackingSymmetryTileAction g V)
            (BandPackingSymmetryTileAction g W) (BandPackingSymmetryPartialOdometerAction g f)
            (BandPackingSymmetryPartialOdometerAction g k)))) ) := by
  classical
  intro g A Ag hA V W f k hlarge hadj
  rcases hadj with ⟨hf, hk, p, p', hp, hp', hunit | hproper⟩
  · omega
  rcases hproper with ⟨q, i, e, hq, hqA, hc, hx, hy⟩
  have hfq : TileOdometer (q 0) V f := by simpa [hqA] using hf
  have hkq : TileOdometer (q 0) W k := by simpa [hqA] using hk
  obtain ⟨d, r, r', _, hfg, hkg, hpr, hpr', hcg, hxg, hyg, _⟩ :=
    LeftLatticeAdjacentPackingSymmetryTransport g q hq i e V W f k
      p p' hfq hkq hp hp' hc hx hy
  have hqgA : BandPackingSymmetryQuadrupleAction g q 0 = Ag.1.1 := by
    simp [BandPackingSymmetryQuadrupleAction, hqA, hA]
  refine ⟨by simpa only [← hqgA] using hfg,
    by simpa only [← hqgA] using hkg, r, r', hpr, hpr',
    Or.inr ⟨BandPackingSymmetryQuadrupleAction g q,
    (if BandPackingSymmetryReversesOrientation g then -i else i), xor e d,
    BandPackingSymmetryProperCovariance g q hq, hqgA, hcg, hxg, hyg⟩⟩

private theorem layout :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (D :
            BandCircle), (q 0 = D.1.1) → (∀ (V : ProtoTile), (BandPrototile (q 0) V) → (Nonempty
            (BandOrderedGeneralLayoutCertificate q cfg D V))) ) := by
  classical
  intro q cfg D hD V hV
  apply BandOrderedGeneralLayout q cfg D hD V hV
  · intro p W S hp hW hS hcover _
    have facts := BandTileSimultaneousInduction p hp W hW
    exact ⟨facts.1, facts.2.1, facts.2.2.1 S hS hcover⟩
  · intro E W hW _
    cases hW with
    | line w x hw => simp [QuarterTurnSymmetric, TileRealization]
    | unit z x anchor =>
        intro p
        norm_num [TileRealization, TileCentroid, ClosedSquareRealization]
        constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩
        all_goals constructor <;> constructor <;> linarith
    | decompose hp hS hcells hfoot hcent =>
        exact (BandTileSimultaneousInduction _ hp _
          (.decompose hp hS hcells hfoot hcent)).2.2.2.1
  · intro p W U hp hW _ hlarge i hU hc
    exact (BandTileSimultaneousInduction p hp W hW).2.2.2.2.2.1 hlarge i U hU hc
  · intro p W U Z hp hW _ i hU hZ hcU hcZ
    exact (BandTileSimultaneousInduction p hp W hW).2.2.2.2.2.2.1 i U Z hU hZ hcU hcZ

private theorem hgsubAt296 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (C' : BandCircle), ∀
            (T' : ProtoTile), ∀ (h' : PartialOdometer), (TileSubodometer C.1.1 C'.1.1 T T' h h')
                → (∀ (g : BandPackingSymmetry), ∀
            (Cg : BandCircle), (Cg.1.1 = BandPackingSymmetryCircleAction g C.1.1) → (∀ (Dg :
            BandCircle), (Dg.1.1 = BandPackingSymmetryCircleAction g C'.1.1) → (TileSubodometer
                Cg.1.1 Dg.1.1 (BandPackingSymmetryTileAction
            g T) (BandPackingSymmetryTileAction g T') (BandPackingSymmetryPartialOdometerAction g
            h) (BandPackingSymmetryPartialOdometerAction g h')))) ) := by
  classical
  intro C T h C' T' h' hsub g Cg hCg Dg hDg
  rw [hCg, hDg]
  exact (BandPackingSymmetryMarkedDataCovariance.1 g _ _ _ _ _ _).mp hsub

private theorem hedgeg :
    (by
      classical
      exact
        ∀ (T₀ : ProtoTile), ∀ (T' : ProtoTile), ((FootprintEdges T' ∩ FootprintEdges
            T₀).Nonempty) → (∀ (g : BandPackingSymmetry), (FootprintEdges
            (BandPackingSymmetryTileAction g T') ∩ FootprintEdges (BandPackingSymmetryTileAction
            g T₀)).Nonempty) ) := by
  classical
  intro T₀ T' hedge g
  obtain ⟨edge, hleft, hright⟩ := hedge
  have edges := (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.2.1
  refine ⟨edge.image (BandPackingSymmetryVectorAction g), ?_, ?_⟩
  · rw [edges]; exact ⟨edge, hleft, rfl⟩
  · rw [edges]; exact ⟨edge, hright, rfl⟩

private theorem hgsubAt347 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T₀ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (C' : BandCircle), ∀
            (T' : ProtoTile), ∀ (h' : PartialOdometer), (TileSubodometer C.1.1 C'.1.1 T₀ T' h₀
                h') → (∀ (g : BandPackingSymmetry),
            ∀ (Cg : BandCircle), (Cg.1.1 = BandPackingSymmetryCircleAction g C.1.1) → (∀ (Dg :
            BandCircle), (Dg.1.1 = BandPackingSymmetryCircleAction g C'.1.1) → (TileSubodometer
                Cg.1.1 Dg.1.1 (BandPackingSymmetryTileAction
            g T₀) (BandPackingSymmetryTileAction g T') (BandPackingSymmetryPartialOdometerAction
            g h₀) (BandPackingSymmetryPartialOdometerAction g h')))) ) := by
  classical
  intro C T₀ h₀ C' T' h' hsub g Cg hCg Dg hDg
  rw [hCg, hDg]
  exact (BandPackingSymmetryMarkedDataCovariance.1 g _ _ _ _ _ _).mp hsub

private theorem heqOrig :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (C' : BandCircle), ∀ (g : BandPackingSymmetry), ∀ (Ig :
            BandCircle), (Ig.1.1 = BandPackingSymmetryCircleAction g Cᵢ.1.1) → (∀ (Dg :
            BandCircle), (Dg.1.1 = BandPackingSymmetryCircleAction g C'.1.1) → (∀ (ginv :
                BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction g C) = C) →
            ((Dg = Ig) → (C' = Cᵢ)))) ) := by
  classical
  intro Cᵢ C' g Ig hIg Dg hDg ginv hcancel heq
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun D : BandCircle => D.1.1) heq
  rw [hDg, hIg] at he
  simpa only [hcancel] using congrArg (BandPackingSymmetryCircleAction ginv) he

private theorem hab :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀ : PartialOdometer),
            ∀ (g : BandPackingSymmetry), ∀ (qbar : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration qbar), ∀ (Cg : BandCircle), ∀ (Ig : BandCircle), ∀
            (cert : BandOrderedGeneralLayoutCertificate qbar cfg Cg
            (BandPackingSymmetryTileAction g T₀)), ∀ (a : PeriodicSubtileIndex), (a ∈
            P4261T1ExteriorIndices) → ((P4261T1PlacedOdometer cert
            (BandPackingSymmetryPartialOdometerAction g h₀) Ig (BandPackingSymmetryTileAction g
            T) (BandPackingSymmetryPartialOdometerAction g h) a) → (∀ (b : PeriodicSubtileIndex),
            (b.first = (0 : ℤ)) → ((b.second = (0 : ℤ)) → ((¬AllowedSubtileIncidence a b) → (a ≠
            b))))) ) := by
  classical
  intro T T₀ h h₀ g qbar cfg Cg Ig cert a ha pa b hb₁ hb₂ hinc heq
  have hzero : a.first = 0 ∧ a.second = 0 := by simpa [heq] using And.intro hb₁ hb₂
  have ha' := ha
  simp only [P4261T1ExteriorIndices, Finset.mem_insert, Finset.mem_singleton] at ha'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hzero

private theorem hsmall :
    (by
      classical
      exact
        ∀ (T₀ : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (qbar : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀ (Cg :
            BandCircle), ∀ (cert : BandOrderedGeneralLayoutCertificate qbar cfg Cg
            (BandPackingSymmetryTileAction g T₀)), ∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), (FootprintVertices (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v b) = ∅ ∨ (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b)).Subsingleton) → (((FootprintVertices (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v a)) ∩ FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v b)).Subsingleton) ) := by
  classical
  intro T₀ g qbar cfg Cg cert a b hraw
  rcases hraw with hempty | hsmall
  · rw [hempty]; exact Set.subsingleton_empty
  · exact hsmall

private theorem forward :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (f : PartialOdometer), ∀ (z : GaussianInt), (z ∈ f.domain)
            → (BandPackingSymmetryVectorAction g z ∈ (BandPackingSymmetryPartialOdometerAction g
            f).domain) ) := by
  classical
  intro g f z hz
  change _ ∈ ((BandPackingSymmetryPartialOdometerAction g f).domain : Set GaussianInt)
  rw [(BandPackingSymmetryPartialOdometerActionFormulas g f f).1]
  exact ⟨z, hz, rfl⟩

end OdometerAdjacencyGeometry

theorem OrderedGeneralOdometerAdjacencyClassification :
    ∀ (C : BandCircle),
      (¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C.1.1) ∨
            (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C.1.1))) →
      (∀ (T T₀ : ProtoTile) (h h₀ : PartialOdometer),
        RightLatticeAdjacent C T T₀ h h₀ →
        ∀ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer),
          TileSubodometer C.1.1 C'.1.1 T T' h h' →
          (FootprintEdges T' ∩ FootprintEdges T₀).Nonempty →
          SubtileLatticeAdjacent C C' T₀ T' h₀ h') ∧
      (∀ (Cᵢ : BandCircle) (T T₀ : ProtoTile)
          (h h₀ : PartialOdometer),
        SubtileLatticeAdjacent C Cᵢ T₀ T h₀ h →
        ∀ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer),
          TileSubodometer C.1.1 C'.1.1 T₀ T' h₀ h' →
          (∃ x, x ∈ h'.domain ∧ x ∈ h.domain) →
          (((h'.domain : Set GaussianInt) ∩
              (h.domain : Set GaussianInt)).Subsingleton ∨
            (C' = Cᵢ ∧ LeftLatticeAdjacent Cᵢ T T' h h') ∨
            SubtileLatticeAdjacent Cᵢ C' T T' h h' ∨
            SubtileLatticeAdjacent C' Cᵢ T' T h' h)) := by
-- BODY
  classical
  intro C horbit
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  -- Normalize the presentation belonging to the actual adjacency witness.
  have normalize (q : Fin 4 → CircleCoordinates)
      (hq : ProperBandQuadruple q) (hqC : q 0 = C.1.1) :
      ∃ (g : BandPackingSymmetry) (qbar : Fin 4 → CircleCoordinates),
        Nonempty (BandOrderedGeneralConfiguration qbar) ∧
        qbar 0 = BandPackingSymmetryCircleAction g C.1.1 := OdometerAdjacencyGeometry.normalize C
            horbit q hq hqC
  have imageCircle (g : BandPackingSymmetry) (D : BandCircle)
      (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (j : Fin 4) (hj : p j = D.1.1) :
      ∃ Dg : BandCircle, Dg.1.1 = BandPackingSymmetryCircleAction g D.1.1 :=
          OdometerAdjacencyGeometry.imageCircle neg1 neg2 g D p hp j hj
  have transportS (g : BandPackingSymmetry) (A B Ag Bg : BandCircle)
      (hA : Ag.1.1 = BandPackingSymmetryCircleAction g A.1.1)
      (hB : Bg.1.1 = BandPackingSymmetryCircleAction g B.1.1)
      (V W : ProtoTile) (f k : PartialOdometer)
      (hadj : SubtileLatticeAdjacent A B V W f k) :
      SubtileLatticeAdjacent Ag Bg
        (BandPackingSymmetryTileAction g V) (BandPackingSymmetryTileAction g W)
        (BandPackingSymmetryPartialOdometerAction g f)
        (BandPackingSymmetryPartialOdometerAction g k) := OdometerAdjacencyGeometry.transportS
            neg1 neg2 g A B Ag Bg hA hB V W f k hadj
  have transportL (g : BandPackingSymmetry) (A Ag : BandCircle)
      (hA : Ag.1.1 = BandPackingSymmetryCircleAction g A.1.1)
      (V W : ProtoTile) (f k : PartialOdometer)
      (hlarge : 1 < A.1.1.1)
      (hadj : LeftLatticeAdjacent A V W f k) :
      LeftLatticeAdjacent Ag
        (BandPackingSymmetryTileAction g V) (BandPackingSymmetryTileAction g W)
        (BandPackingSymmetryPartialOdometerAction g f)
        (BandPackingSymmetryPartialOdometerAction g k) := OdometerAdjacencyGeometry.transportL g
            A Ag hA V W f k hlarge hadj
  -- Construct the layout from its existing smaller-tile premises.
  have layout (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
      (D : BandCircle) (hD : q 0 = D.1.1) (V : ProtoTile)
      (hV : BandPrototile (q 0) V) :
      Nonempty (BandOrderedGeneralLayoutCertificate q cfg D V) :=
          OdometerAdjacencyGeometry.layout q cfg D hD V hV
  constructor
  · intro T T₀ h h₀ hadj C' T' h' hsub hedge
    obtain ⟨hO, hO₀, p, p₀, hp, hp₀, q, i, e, hq, hqC, hc, hx, hy⟩ := hadj
    obtain ⟨g, qbar, ⟨cfg⟩, hchild⟩ := normalize q hq hqC
    obtain ⟨Cg, hCg⟩ := imageCircle g C q hq 0 hqC
    rcases hsub.2.2.2.2.2 with ⟨pdec, j, hpdec, hpdecC, hpdecD, _⟩
    obtain ⟨Dg, hDg⟩ := imageCircle g C' pdec hpdec j.succ hpdecD
    have hgsub : TileSubodometer Cg.1.1 Dg.1.1
        (BandPackingSymmetryTileAction g T) (BandPackingSymmetryTileAction g T')
        (BandPackingSymmetryPartialOdometerAction g h)
        (BandPackingSymmetryPartialOdometerAction g h') := OdometerAdjacencyGeometry.hgsubAt296 C
            T h C' T' h' hsub g Cg hCg Dg hDg
    obtain ⟨d, r, r₀, _, hOg, hO₀g, hrg, hr₀g, hcg, hxg, hyg, _⟩ :=
      RightLatticeAdjacentPackingSymmetryTransport g q hq i e T T₀ h h₀ p p₀
        (by simpa [hqC] using hO) (by simpa [hqC] using hO₀) hp hp₀ hc hx hy
    have hqgC : BandPackingSymmetryQuadrupleAction g q 0 = Cg.1.1 := by
      simp [BandPackingSymmetryQuadrupleAction, hqC, hCg]
    have hOg' : TileOdometer Cg.1.1 (BandPackingSymmetryTileAction g T)
        (BandPackingSymmetryPartialOdometerAction g h) := by simpa only [hqgC] using hOg
    have hO₀g' : TileOdometer Cg.1.1 (BandPackingSymmetryTileAction g T₀)
        (BandPackingSymmetryPartialOdometerAction g h₀) := by simpa only [hqgC] using hO₀g
    have hadjg : RightLatticeAdjacent Cg
        (BandPackingSymmetryTileAction g T) (BandPackingSymmetryTileAction g T₀)
        (BandPackingSymmetryPartialOdometerAction g h)
        (BandPackingSymmetryPartialOdometerAction g h₀) :=
      ⟨hOg', hO₀g', r, r₀, hrg, hr₀g, BandPackingSymmetryQuadrupleAction g q,
        (if BandPackingSymmetryReversesOrientation g then -i else i),
        xor (xor e d) (BandPackingSymmetryReversesOrientation g),
        BandPackingSymmetryProperCovariance g q hq, hqgC, hcg, hxg, hyg⟩
    have hbarC : qbar 0 = Cg.1.1 := hchild.trans hCg.symm
    obtain ⟨cert⟩ := layout qbar cfg Cg hbarC (BandPackingSymmetryTileAction g T₀)
      (by simpa only [hbarC] using TileOdometerBandPrototile _ _ _ hO₀g')
    obtain ⟨a, ha, ⟨placed⟩⟩ := P4261T1RightCoordinates cert _ _ _ hadjg _ _ _ hgsub
    have hedgeg : (FootprintEdges (BandPackingSymmetryTileAction g T') ∩
        FootprintEdges (BandPackingSymmetryTileAction g T₀)).Nonempty :=
            OdometerAdjacencyGeometry.hedgeg T₀ T' hedge g
    have haext := P4261T1EdgeExterior cert _ a placed.cells ha hedgeg
    have result := P4261T1ExteriorAdjacency cert _ hO₀g' _ _ _ a haext placed
    obtain ⟨ginv, hcancel, _, _, _, htile, _, _, _, hfun, _⟩ :=
      BandPackingSymmetryInversePhaseCancellation.2 g
    have hbackC : C.1.1 = BandPackingSymmetryCircleAction ginv Cg.1.1 := by
      rw [hCg, hcancel]
    have hbackD : C'.1.1 = BandPackingSymmetryCircleAction ginv Dg.1.1 := by
      rw [hDg, hcancel]
    have back := transportS ginv Cg Dg C C' hbackC hbackD _ _ _ _ result
    simpa only [htile, hfun] using back
  · intro Cᵢ T T₀ h h₀ hadj C' T' h' hsub _hmeet
    obtain ⟨hO₀, hO, p₀, p, hp₀, hp, q, i, s, hq, hqC, hqi, hc, hx, hy⟩ := hadj
    obtain ⟨g, qbar, ⟨cfg⟩, hchild⟩ := normalize q hq hqC
    obtain ⟨Cg, hCg⟩ := imageCircle g C q hq 0 hqC
    obtain ⟨Ig, hIg⟩ := imageCircle g Cᵢ q hq i.succ hqi
    rcases hsub.2.2.2.2.2 with ⟨pdec, j, hpdec, hpdecC, hpdecD, _⟩
    obtain ⟨Dg, hDg⟩ := imageCircle g C' pdec hpdec j.succ hpdecD
    have hgsub : TileSubodometer Cg.1.1 Dg.1.1
        (BandPackingSymmetryTileAction g T₀) (BandPackingSymmetryTileAction g T')
        (BandPackingSymmetryPartialOdometerAction g h₀)
        (BandPackingSymmetryPartialOdometerAction g h') := OdometerAdjacencyGeometry.hgsubAt347 C
            T₀ h₀ C' T' h' hsub g Cg hCg Dg hDg
    have hadj' : SubtileLatticeAdjacent C Cᵢ T₀ T h₀ h :=
      ⟨hO₀, hO, p₀, p, hp₀, hp, q, i, s, hq, hqC, hqi, hc, hx, hy⟩
    have hadjg := transportS g C Cᵢ Cg Ig hCg hIg _ _ _ _ hadj'
    have hO₀g := hadjg.1
    have hbarC : qbar 0 = Cg.1.1 := hchild.trans hCg.symm
    obtain ⟨cert⟩ := layout qbar cfg Cg hbarC (BandPackingSymmetryTileAction g T₀)
      (by simpa only [hbarC] using TileOdometerBandPrototile _ _ _ hO₀g)
    obtain ⟨a, ha, ⟨pa⟩⟩ := P4261T1SubtileCoordinates cert _ _ _ _ hadjg
    obtain ⟨b, hb₁, hb₂, ⟨pb⟩⟩ := P4261T1CentralCoordinates cert _ _ _ _ hgsub
    obtain ⟨ginv, hcancel, _, _, _, htile, _, hvec, _, hfun, _⟩ :=
      BandPackingSymmetryInversePhaseCancellation.2 g
    have hbackI : Cᵢ.1.1 = BandPackingSymmetryCircleAction ginv Ig.1.1 := by
      rw [hIg, hcancel]
    have hbackD : C'.1.1 = BandPackingSymmetryCircleAction ginv Dg.1.1 := by
      rw [hDg, hcancel]
    by_cases hinc : AllowedSubtileIncidence a b
    · rcases P4261T1ContactAdjacency cert _ _ _ _ _ _ _ a b ha hb₁ hb₂ pa pb hinc with
        ⟨heq, hlarge, hleft⟩ | hforward | hreverse
      · have heqOrig : C' = Cᵢ := OdometerAdjacencyGeometry.heqOrig Cᵢ C' g Ig hIg Dg hDg ginv
          hcancel heq
        right; left
        refine ⟨heqOrig, ?_⟩
        have back := transportL ginv Ig Cᵢ hbackI _ _ _ _ hlarge hleft
        simpa only [htile, hfun] using back
      · right; right; left
        have back := transportS ginv Ig Dg Cᵢ C' hbackI hbackD _ _ _ _ hforward
        simpa only [htile, hfun] using back
      · right; right; right
        have back := transportS ginv Dg Ig C' Cᵢ hbackD hbackI _ _ _ _ hreverse
        simpa only [htile, hfun] using back
    · -- A nonledger contact stays a raw subsingleton, not a reversed adjacency.
      have hab : a ≠ b := OdometerAdjacencyGeometry.hab T T₀ h h₀ g qbar cfg Cg Ig cert a ha pa b
          hb₁ hb₂ hinc
      have hraw := (BandOriginalOccurrenceIntersectionClassification qbar cfg Cg
        (BandPackingSymmetryTileAction g T₀) cert a b hab).2 hinc
      have hsmall : ((FootprintVertices
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)) ∩
          FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
              b)).Subsingleton := OdometerAdjacencyGeometry.hsmall T₀ g qbar cfg Cg cert a b hraw
      have hsmallg : (((BandPackingSymmetryPartialOdometerAction g h').domain : Set GaussianInt) ∩
          (BandPackingSymmetryPartialOdometerAction g h).domain).Subsingleton :=
              (show
                  (((BandPackingSymmetryPartialOdometerAction g h').domain :
                  Set GaussianInt) ∩ (BandPackingSymmetryPartialOdometerAction
                  g h).domain).Subsingleton
                from by
                  classical
                  rw [pb.domain, pa.domain, Set.inter_comm]
                  exact hsmall)
      left
      intro x hx y hy
      have forward (f : PartialOdometer) (z : GaussianInt) (hz : z ∈ f.domain) :
          BandPackingSymmetryVectorAction g z ∈
            (BandPackingSymmetryPartialOdometerAction g f).domain :=
                OdometerAdjacencyGeometry.forward g f z hz
      have he := hsmallg
        ⟨forward h' x hx.1, forward h x hx.2⟩
        ⟨forward h' y hy.1, forward h y hy.2⟩
      simpa only [hvec] using congrArg (BandPackingSymmetryVectorAction ginv) he

end ApollonianSuperharmonic

end
