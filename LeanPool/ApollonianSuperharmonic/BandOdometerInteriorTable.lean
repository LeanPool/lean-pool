/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4120T1RootNormalization
public import LeanPool.ApollonianSuperharmonic.P4120T1AffineComparison
public import LeanPool.ApollonianSuperharmonic.P4120T1FordGeometry
public import LeanPool.ApollonianSuperharmonic.P4120T1DiamondGeometry
public import LeanPool.ApollonianSuperharmonic.P4120T1GeneralRowData
public import LeanPool.ApollonianSuperharmonic.P4120T1GeneralDescent
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorStarClassification
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOuterMixedOdometerRows
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNestedRightOdometerRows
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLargestParentOdometerRows
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPositiveCutOdometerRows
public import LeanPool.ApollonianSuperharmonic.FordCenteredInteriorOdometerStencil

-- [TABLET NODE: BandOdometerInteriorTable]

/-!
# BandOdometerInteriorTable

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InteriorTableGeometry

private theorem orderedGeneralRowDispatch :
    (by
      classical
      exact
        ∀ (q' : Fin 4 → CircleCoordinates), ∀ (cfg' : BandOrderedGeneralConfiguration q'), ∀ (C0'
            : BandCircle), ∀ (T' : ProtoTile), ∀ (cert' : BandOrderedGeneralLayoutCertificate q'
            cfg' C0' T'), ∀ (h' : PartialOdometer), ∀ (P' : Fin 3 → Bool → ProtoTile), ∀ (r' :
            Fin 3 → Bool → PartialOdometer), ∀ (Q' : Fin 3 → Bool → ProtoTile), ∀ (S' : Fin 3 →
            Bool → ProtoTile), ∀ (u' : Fin 3 → Bool → PartialOdometer), ∀ (v' : Fin 3 → Bool →
            PartialOdometer), ∀ (g'' : IntegerLatticeFunction), ∀ (x' : GaussianInt), ∀ (marked :
            Bool), BandOrderedGeneralOdometerRowData q' cfg' C0' T' cert' h' P' r' Q' S' u' v'
            g'' → BandOrderedGeneralInteriorWebRow cert' x' marked → (marked = true →
            FourNeighborLaplacian g'' x' = 0) ∧ (marked = false → FourNeighborLaplacian g'' x' =
            1) ) := by
  classical
  intro q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data row
  cases row with
  | outer12 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer12 left_mem right_mem star coarseThird webCompanion)
        (Or.inl ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩)
  | outer13 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer13 left_mem right_mem star coarseThird webCompanion)
        (Or.inr (Or.inl
          ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩))
  | outer21 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer21 left_mem right_mem star coarseThird webCompanion)
        (Or.inr (Or.inr (Or.inl
          ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩)))
  | outer31 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer31 left_mem right_mem star coarseThird webCompanion)
        (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩))))
  | outer23 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer23 left_mem right_mem star coarseThird webCompanion)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩)))))
  | outer32 left_mem right_mem star coarseThird webCompanion =>
      exact BandOrderedGeneralOuterMixedOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.outer32 left_mem right_mem star coarseThird webCompanion)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨left_mem, right_mem, star, coarseThird, webCompanion, rfl⟩)))))
  | rightPositive left_mem right_mem star squares =>
      have result := BandOrderedGeneralNestedRightOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.rightPositive left_mem right_mem star squares)
        (Or.inl ⟨left_mem, right_mem, star, squares, rfl⟩)
      exact ⟨result.2, result.1⟩
  | rightReflected left_mem right_mem star squares =>
      have result := BandOrderedGeneralNestedRightOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.rightReflected left_mem right_mem star squares)
        (Or.inr ⟨left_mem, right_mem, star, squares, rfl⟩)
      exact ⟨result.2, result.1⟩
  | largestPositive left_mem right_mem star companion =>
      exact BandOrderedGeneralLargestParentOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.largestPositive left_mem right_mem star companion)
        (Or.inl ⟨left_mem, right_mem, star, companion, rfl⟩)
  | largestReflected left_mem right_mem star companion =>
      exact BandOrderedGeneralLargestParentOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' marked data
        (.largestReflected left_mem right_mem star companion)
        (Or.inr ⟨left_mem, right_mem, star, companion, rfl⟩)
  | leftPositiveCut unmarked at_cut geometry =>
      have lap := BandOrderedGeneralPositiveCutOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' data geometry
      constructor
      · intro marked_true
        simp [unmarked] at marked_true
      · intro _
        exact lap
  | rightPositiveCut unmarked at_cut geometry =>
      have lap := BandOrderedGeneralPositiveCutOdometerRows
        q' cfg' C0' T' cert' h' P' r' Q' S' u' v' g'' x' data geometry
      constructor
      · intro marked_true
        simp [unmarked] at marked_true
      · intro _
        exact lap

private theorem layout :
    (by
      classical
      exact
        ∀ (qn : Fin (4 : ℕ) → CircleCoordinates), ∀ (Tn : ProtoTile), ∀ (hqn :
            ProperBandQuadruple qn), (BandPrototile (qn (0 : Fin (4 : ℕ))) Tn) → (∀ (cfg :
            BandOrderedGeneralConfiguration qn), ∀ (hpos : (0 : ℤ) < (qn (0 : Fin (4 : ℕ))).1),
        let C : BandCircle :=
          ⟨⟨qn 0, ⟨Or.inl hpos, ⟨qn, hqn.1, ⟨0, rfl⟩⟩⟩⟩, hpos⟩
        Nonempty (BandOrderedGeneralLayoutCertificate qn cfg C Tn)) ) := by
  classical
  intro qn Tn hqn hTn cfg hpos C
  apply BandOrderedGeneralLayout qn cfg C rfl Tn hTn
  · intro q' T' S' hq' hT' hocc hcells _
    have hI := BandTileSimultaneousInduction q' hq' T' hT'
    exact ⟨hI.1, hI.2.1, hI.2.2.1 S' hocc hcells⟩
  · intro D U hU _
    cases hU with
    | line w z hw =>
        intro p
        simp [TileRealization, TileCentroid]
    | unit z a anchor =>
        intro p
        have hc : TileCentroid (⟨{a}, anchor⟩ : ProtoTile) =
            (((a.re : Int) : Real) + (1 / 2 : Real),
              ((a.im : Int) : Real) + (1 / 2 : Real)) := by
          simp [TileCentroid]
        rw [hc]
        rcases p with ⟨px, py⟩
        simp only [TileRealization, Finset.mem_singleton, Set.mem_iUnion]
        simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
        constructor
        · rintro ⟨b, rfl, hlo, hhi⟩
          refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
            linarith [hlo.1, hlo.2, hhi.1, hhi.2]
        · rintro ⟨b, rfl, hlo, hhi⟩
          refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
            linarith [hlo.1, hlo.2, hhi.1, hhi.2]
    | @decompose q' hq' S' U' hS hcells hfoot hcent =>
        exact (BandTileSimultaneousInduction q' hq' U
          (.decompose hq' hS hcells hfoot hcent)).2.2.2.1
  · intro q' T' U hq' hT' _ hlarge i hU hcentU
    exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.1
      hlarge i U hU hcentU
  · intro q' T' U V hq' hT' _ i hU hV hcentU hcentV
    exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.2.1
      i U V hU hV hcentU hcentV

private theorem obsAt414 :
    (by
      classical
      exact
        ∀ (qn : Fin (4 : ℕ) → CircleCoordinates), ∀ (Tn : ProtoTile), ∀ (Sn : Fin (3 : ℕ) → Bool
            → ProtoTile), ∀ (hqn : ProperBandQuadruple qn), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence qn Tn i s (Sn i s)) → (∀ (cfg : BandOrderedGeneralConfiguration
            qn), ∀ (hpos : (0 : ℤ) < (qn (0 : Fin (4 : ℕ))).1),
        let C : BandCircle :=
          ⟨⟨qn 0, ⟨Or.inl hpos, ⟨qn, hqn.1, ⟨0, rfl⟩⟩⟩⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate qn cfg C Tn), ∀ i, ∀ s, FootprintVertices
            (Sn i s) = FootprintVertices (cert.P i s) ∧ BoundaryFootprintVertices (Sn i s) =
            BoundaryFootprintVertices (cert.P i s)) ) := by
  classical
  intro qn Tn Sn hqn hSn cfg hpos C cert i s
  have hc : TileCentroid (Sn i s) = TileCentroid (cert.P i s) :=
    sub_left_injective ((hSn i s).2.2.trans (cert.outer_occurrence i s).2.2.symm)
  obtain ⟨hcell, hanchor⟩ := BandPrototileCentroidUnique
    (qn i.succ) (Sn i s) (cert.P i s)
    (hSn i s).1 (cert.outer_occurrence i s).1 hc
  have ho := ProtoTileObservableExtensionality _ _ hcell hanchor
  exact ⟨ho.1, ho.2.1⟩

private theorem hcount :
    (by
      classical
      exact
        ∀ (qn : Fin (4 : ℕ) → CircleCoordinates), ∀ (Tn : ProtoTile), ∀ (Sn : Fin (3 : ℕ) → Bool
            → ProtoTile), ∀ (xn : GaussianInt), ∀ (hqn : ProperBandQuadruple qn), ∀ (cfg :
            BandOrderedGeneralConfiguration qn), ∀ (hpos : (0 : ℤ) < (qn (0 : Fin (4 : ℕ))).1),
        let C : BandCircle :=
          ⟨⟨qn 0, ⟨Or.inl hpos, ⟨qn, hqn.1, ⟨0, rfl⟩⟩⟩⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate qn cfg C Tn), (∀ i, ∀ s, FootprintVertices
            (Sn i s) = FootprintVertices (cert.P i s) ∧ BoundaryFootprintVertices (Sn i s) =
            BoundaryFootprintVertices (cert.P i s)) → (Nat.card
            {a : Fin 3 × Bool // xn ∈ BoundaryFootprintVertices (Sn a.1 a.2)} = Nat.card
            {a : Fin 3 × Bool // xn ∈ BoundaryFootprintVertices (cert.P a.1 a.2)}) ) := by
  classical
  intro qn Tn Sn xn hqn cfg hpos C cert obs
  have hp : (fun a : Fin 3 × Bool =>
      xn ∈ BoundaryFootprintVertices (Sn a.1 a.2)) =
      (fun a : Fin 3 × Bool =>
        xn ∈ BoundaryFootprintVertices (cert.P a.1 a.2)) := by
    funext a
    rw [(obs a.1 a.2).2]
  change Nat.card (Subtype _) = Nat.card (Subtype _)
  rw [hp]

end InteriorTableGeometry

theorem BandOdometerInteriorTable :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (T : ProtoTile), ∀ (S : Fin 3
        → Bool → ProtoTile), ∀ (h : PartialOdometer), ∀ (hs : Fin 3 → Bool → PartialOdometer), ∀
        (g : IntegerLatticeFunction), (BandPrototile (q 0) T) → ((TileOdometer (q 0) T h) →
        ((GlobalOdometerExtends g h) → ((∀ i, ∀ s, BandSubtileOccurrence q T i s (S i s)) → ((∀
        x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) → ((∀ i, ∀ s, TileOdometer (q i.succ) (S i s)
        (hs i s)) → ((∀ i, ∀ s, GlobalOdometerExtends g (hs i s)) → (∀ (x : GaussianInt), (x ∈
        FootprintVertices T) → ((x ∉ BoundaryFootprintVertices T) → (
    let k := Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (S is.1 is.2)}
    (k = 2 → GaussianRealPoint x ≠ TileCentroid T →
      FourNeighborLaplacian g x = 1) ∧
    (k = 2 → GaussianRealPoint x = TileCentroid T →
      FourNeighborLaplacian g x = 0) ∧
    (k = 3 → FourNeighborLaplacian g x = 0) ∧
    (k = 4 → GaussianRealPoint x ≠ TileCentroid T →
      FourNeighborLaplacian g x = -1) ∧
    (k = 4 → GaussianRealPoint x = TileCentroid T →
      FourNeighborLaplacian g x = -2) ∧
    ((k = 2 ∨ k = 3 ∨ k = 4) ∨
      ∃ i : Fin 3, ∃ s : Bool,
        0 < (q i.succ).1 ∧
        x ∈ FootprintVertices (S i s) ∧
        x ∉ BoundaryFootprintVertices (S i s)))))))))))) := by
  intro q hq T S h hs g hT hodo hext hS hcells hsub hrest x hx hxb
-- BODY
  obtain ⟨qn, Tn, Sn, hn, gn, xn, e, hqn, hTn, hodon, hextn,
      hSn, hcellsn, hxn, hxbn, hobsn, hcountn, hcentern, hlapn, regimes⟩ :=
    P4120T1RootNormalization q hq T S h g hT hodo hext hS hcells x hx hxb
  suffices result :
      let k := Nat.card {a : Fin 3 × Bool //
        xn ∈ BoundaryFootprintVertices (Sn a.1 a.2)}
      (k = 2 → GaussianRealPoint xn ≠ TileCentroid Tn →
        FourNeighborLaplacian gn xn = 1) ∧
      (k = 2 → GaussianRealPoint xn = TileCentroid Tn →
        FourNeighborLaplacian gn xn = 0) ∧
      (k = 3 → FourNeighborLaplacian gn xn = 0) ∧
      (k = 4 → GaussianRealPoint xn ≠ TileCentroid Tn →
        FourNeighborLaplacian gn xn = -1) ∧
      (k = 4 → GaussianRealPoint xn = TileCentroid Tn →
        FourNeighborLaplacian gn xn = -2) ∧
      ((k = 2 ∨ k = 3 ∨ k = 4) ∨
        ∃ i : Fin 3, ∃ s : Bool, 0 < (qn i.succ).1 ∧
          xn ∈ FootprintVertices (Sn i s) ∧
          xn ∉ BoundaryFootprintVertices (Sn i s)) by
    dsimp only at result ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hk hnc
      exact hlapn.symm.trans
        (result.1 (hcountn.trans hk) (fun hc => hnc (hcentern.mp hc)))
    · intro hk hc
      exact hlapn.symm.trans (result.2.1 (hcountn.trans hk) (hcentern.mpr hc))
    · intro hk
      exact hlapn.symm.trans (result.2.2.1 (hcountn.trans hk))
    · intro hk hnc
      exact hlapn.symm.trans
        (result.2.2.2.1 (hcountn.trans hk) (fun hc => hnc (hcentern.mp hc)))
    · intro hk hc
      exact hlapn.symm.trans
        (result.2.2.2.2.1 (hcountn.trans hk) (hcentern.mpr hc))
    · rcases result.2.2.2.2.2 with hd | ⟨i, s, hp, hf, hb⟩
      · left
        rcases hd with hk | hk | hk
        · exact Or.inl (hcountn.symm.trans hk)
        · exact Or.inr (Or.inl (hcountn.symm.trans hk))
        · exact Or.inr (Or.inr (hcountn.symm.trans hk))
      · right
        obtain ⟨a, ha⟩ := e.surjective (i, s)
        have obs := hobsn a
        rw [ha] at obs
        exact ⟨a.1, a.2, by simpa only [obs.1] using hp,
          obs.2.1.mp hf, fun hboundary => hb (obs.2.2.mpr hboundary)⟩
  have orderedGeneralRowDispatch := InteriorTableGeometry.orderedGeneralRowDispatch
  have orderedGeneralCenteredDispatch := FordCenteredInteriorOdometerStencil
  dsimp only
  rcases regimes with ⟨P, hP, hqP⟩ | ⟨K, hK, hqK⟩ | ⟨cfg⟩
  · subst qn
    obtain ⟨f, hfodo, _, hfvalue⟩ := FordTileOdometerRestriction P
    obtain ⟨u, hu, ha, hlap⟩ :=
      P4120T1AffineComparison ((FordRecursiveQuadruple P) 0)
        Tn (FordTile P.q) hn f gn (FordOdometer P)
        (ProperBandCurvatureStructure _ hqn).1 hodon hfodo hextn hfvalue
        xn hxn hxbn
    have geometry := P4120T1FordGeometry P hP Tn Sn u hu ha hSn xn hxn hxbn
    dsimp only at geometry
    obtain ⟨bounds, hcount, htwo, hfour, hdescent⟩ := geometry
    have table := (FordLaplacianTable P).2.2 hP (xn - u)
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
    dsimp only at table
    refine ⟨?_, ?_, ?_, ?_, ?_, hdescent⟩
    · intro hk _
      exact hlap.trans (table.1 (hcount.symm.trans hk))
    · intro hk hc
      exact (htwo hk hc).elim
    · intro hk
      exact hlap.trans (table.2.1 (hcount.symm.trans hk))
    · intro hk hnc
      exact (hnc (hfour hk).2).elim
    · intro hk _
      exact hlap.trans (table.2.2 (hcount.symm.trans hk))
  · subst qn
    obtain ⟨f, hfodo, _, _, _, hfvalue, _⟩ := DiamondTileOdometerRestriction K
    obtain ⟨u, hu, ha, hlap⟩ :=
      P4120T1AffineComparison ((DiamondRecursiveQuadruple K) 0)
        Tn (DiamondTile K.1) hn f gn (DiamondOdometer K)
        (ProperBandCurvatureStructure _ hqn).1 hodon hfodo hextn hfvalue
        xn hxn hxbn
    have geometry := P4120T1DiamondGeometry K hK Tn Sn u hu ha hSn xn hxn hxbn
    dsimp only at geometry
    obtain ⟨htwo, hthree, hfour, hdescent⟩ := geometry
    refine ⟨?_, ?_, ?_, ?_, ?_, hdescent⟩
    · intro hk hnc
      have facts := htwo hk
      have hnz : (xn - u).re ≠ 0 := fun hz => hnc (facts.2.2.1.mp hz)
      rw [hlap, (DiamondLaplacianTable K).2.2 _ facts.1]
      simp only [ite_eq_left facts.2.1, ite_eq_right hnz]
      norm_num
    · intro hk hc
      have facts := htwo hk
      have hz : (xn - u).re = 0 := facts.2.2.1.mpr hc
      rw [hlap, (DiamondLaplacianTable K).2.2 _ facts.1]
      simp only [ite_eq_left facts.2.1, ite_eq_left hz]
      norm_num
    · intro hk
      exact (hthree hk).elim
    · intro hk _
      have facts := hfour hk
      rw [hlap, (DiamondLaplacianTable K).2.2 _ facts.1]
      simp only [ite_eq_right facts.2.1, ite_eq_right facts.2.2.1]
      norm_num
    · intro hk hc
      exact ((hfour hk).2.2.2 hc).elim
  · obtain ⟨cfg⟩ := cfg
    have hpos := (ProperBandCurvatureStructure qn hqn).1
    let C : BandCircle :=
      ⟨⟨qn 0, ⟨Or.inl hpos, ⟨qn, hqn.1, ⟨0, rfl⟩⟩⟩⟩, hpos⟩
    have layout := InteriorTableGeometry.layout qn Tn hqn hTn cfg hpos
    obtain ⟨cert⟩ := layout
    obtain ⟨P, r, Q, S', u, v, data⟩ :=
      P4120T1GeneralRowData qn cfg C Tn cert hn gn hodon hextn
    have obs : ∀ i s,
        FootprintVertices (Sn i s) = FootprintVertices (cert.P i s) ∧
        BoundaryFootprintVertices (Sn i s) =
          BoundaryFootprintVertices (cert.P i s) := InteriorTableGeometry.obsAt414 qn Tn Sn hqn
              hSn cfg hpos cert
    have hcount :
        Nat.card {a : Fin 3 × Bool // xn ∈ BoundaryFootprintVertices (Sn a.1 a.2)} =
        Nat.card {a : Fin 3 × Bool //
          xn ∈ BoundaryFootprintVertices (cert.P a.1 a.2)} := InteriorTableGeometry.hcount qn Tn
              Sn xn hqn cfg hpos cert obs
    have classification := BandOrderedGeneralInteriorStarClassification
      qn cfg C Tn cert (BandTileSimultaneousInduction qn hqn Tn hTn).1
      xn hxn hxbn
    have descent := P4120T1GeneralDescent qn cfg C Tn cert xn hxn hxbn
    dsimp only at classification descent
    rw [← hcount] at classification descent
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hk hnc
      exact (orderedGeneralRowDispatch qn cfg C Tn cert hn P r Q S' u v
        gn xn false data (classification.1 hk hnc)).2 rfl
    · intro hk hc
      exact orderedGeneralCenteredDispatch qn cfg C Tn cert hn P r Q S' u v
        gn xn data hextn (hcount.symm.trans hk) hc (classification.2.2.2 hk hc)
    · intro hk
      exact (orderedGeneralRowDispatch qn cfg C Tn cert hn P r Q S' u v
        gn xn true data (classification.2.1 hk).1).1 rfl
    · intro hk _
      exact (classification.2.2.1 hk).elim
    · intro hk _
      exact (classification.2.2.1 hk).elim
    · rcases descent with hd | ⟨i, s, hp, hf, hb⟩
      · exact Or.inl hd
      · right
        refine ⟨i, s, hp, ?_, ?_⟩
        · rw [(obs i s).1]
          exact hf
        · rw [(obs i s).2]
          exact hb

end ApollonianSuperharmonic

end
