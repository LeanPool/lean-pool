/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P4590T1PositivePrototileDisk
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.LatticeTileNonempty

public import LeanPool.ApollonianSuperharmonic.BandExceptionalRestorationSectorOrder
public import LeanPool.ApollonianSuperharmonic.BandPositiveCutBranchCompanionExclusion
public import LeanPool.ApollonianSuperharmonic.PositiveCutCompanionRow
public import LeanPool.ApollonianSuperharmonic.ThreeOwnerDesignatedOppositePair

-- [TABLET NODE: BandOrderedGeneralPositiveCutGeometry]

/-!
# BandOrderedGeneralPositiveCutGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositiveCutGeometry

private theorem birthData :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let ρ := cfg.firstPredecessor
        (((ρ (1 : Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (ρ (2 : Fin (4 : ℕ))).1 = (0 : ℤ) ∧ (ρ (3 : Fin (4
            : ℕ))).1 = (1 : ℤ) ∨ (ρ (1 : Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (ρ (2 : Fin (4 : ℕ))).1 = (1
            : ℤ) ∧ (ρ (3 : Fin (4 : ℕ))).1 = (0 : ℤ) ∨ (ρ (1 : Fin (4 : ℕ))).1 = (0 : ℤ) ∧ (ρ (2
            : Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (ρ (3 : Fin (4 : ℕ))).1 = (1 : ℤ)) ∨ (∃ (p : Fin (4 :
            ℕ) → CircleCoordinates), ProperBandQuadruple p ∧ ρ = ![((2 : ℤ) * (p (0 : Fin (4 :
            ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p
            (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
            * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin
            (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 :
            Fin (4 : ℕ)) = ρ (1 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 : ℕ)) = ρ (2 : Fin (4 : ℕ)) ∧ p (3
            : Fin (4 : ℕ)) = ρ (3 : Fin (4 : ℕ)) ∧ (ρ (2 : Fin (4 : ℕ))).1 < (ρ (1 : Fin (4 :
            ℕ))).1 ∧ (ρ (3 : Fin (4 : ℕ))).1 < (ρ (1 : Fin (4 : ℕ))).1) ∨ (∃ (p : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple p ∧ ![ρ (0 : Fin (4 : ℕ)), ρ (2 : Fin (4 :
            ℕ)), ρ (3 : Fin (4 : ℕ)), ρ (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1
            + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin
            (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2
            : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 :
            ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin
            (4 : ℕ)) = ρ (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 : ℕ)) = ρ (3 : Fin (4 : ℕ)) ∧ p (3 :
            Fin (4 : ℕ)) = ρ (1 : Fin (4 : ℕ)) ∧ (ρ (3 : Fin (4 : ℕ))).1 < (ρ (2 : Fin (4 :
            ℕ))).1 ∧ (ρ (1 : Fin (4 : ℕ))).1 < (ρ (2 : Fin (4 : ℕ))).1) ∨ ∃ (p : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple p ∧ ![ρ (0 : Fin (4 : ℕ)), ρ (3 : Fin (4 :
            ℕ)), ρ (1 : Fin (4 : ℕ)), ρ (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1
            + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin
            (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2
            : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 :
            ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin
            (4 : ℕ)) = ρ (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 : ℕ)) = ρ (1 : Fin (4 : ℕ)) ∧ p (3 :
            Fin (4 : ℕ)) = ρ (2 : Fin (4 : ℕ)) ∧ (ρ (1 : Fin (4 : ℕ))).1 < (ρ (3 : Fin (4 :
            ℕ))).1 ∧ (ρ (2 : Fin (4 : ℕ))).1 < (ρ (3 : Fin (4 : ℕ))).1) → ((ρ 2 = q 2) → ((ρ 3 =
            q 3) → ((4 ≤ (ρ 2).1) → (∃ birth : Fin 4 → CircleCoordinates, ProperBandQuadruple
            birth ∧ ((birth 0 = q 2 ∧ birth 2 = q 3 ∧ birth 3 = ρ 1) ∨ (birth 0 = ρ 1 ∧ birth 2 =
            q 2 ∧ birth 3 = q 3)))))) ) := by
  classical
  intro q cfg ρ genealogy hρ2 hρ3 hlarge
  rcases genealogy with roots | p2 | p4 | bad
  · rcases roots with ⟨_, h₂, _⟩ | ⟨_, h₂, _⟩ | ⟨_, h₂, _⟩
    · omega
    · omega
    · omega
  · rcases p2 with ⟨birth, hp, _, h0, h2, h3, _, _⟩
    refine ⟨birth, hp, Or.inr ?_⟩
    exact ⟨by simpa [ρ] using h0, h2.trans hρ2,
      h3.trans hρ3⟩
  · rcases p4 with ⟨birth, hp, _, h0, h2, h3, _, _⟩
    refine ⟨birth, hp, Or.inl ?_⟩
    exact ⟨h0.trans hρ2, h2.trans hρ3,
      by simpa [ρ] using h3⟩
  · rcases bad with ⟨birth, hp, _, h0, h2, h3, _, hlt⟩
    have h₂ : (ρ 3).1 ≤ (ρ 2).1 := by
      simpa [ρ, cfg.firstParentTwo, cfg.firstParentThree] using cfg.order23
    have hbad : (ρ 2).1 < (ρ 3).1 := by
      exact hlt
    omega

private abbrev prototile_lattice := ApollonianSuperharmonic.P4590T1PositivePrototileDisk

private abbrev tile_nonempty := ApollonianSuperharmonic.LatticeTileNonempty.cells

private theorem positive_of_nonempty :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (X : ProtoTile), BandPrototile c X → X.cells.Nonempty → 0 <
            c.1 ) := by
  classical
  intro c X hX hne
  induction hX with
  | line w x hw => simp at hne
  | unit z x anchor => norm_num
  | @decompose r hr S X hS hcells hfoot hcentroid ih =>
    exact (ProperBandCurvatureStructure r hr).1

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
    simpa using hcurv.2.1 ⟨2, by decide⟩
  have hne : (q 3).1 ≠ 0 := cfg.noLine 3
  omega



private theorem boundary_incident :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈
            FootprintVertices X)) → (∀ (X : ProtoTile), ∀ (x : GaussianInt), (X.cells.Nonempty) →
            ((x ∈ BoundaryFootprintVertices X) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            X.cells))) ) := by
  classical
  intro boundary_to_raw X x hne hx
  have hraw := boundary_to_raw X x hx
  unfold FootprintVertices at hraw
  rw [ite_eq_left hne] at hraw
  rcases hraw with ⟨z, hz, hcorner⟩
  rcases hcorner with h | h | h | h
  · refine ⟨0, ?_⟩
    simpa [LatticeVertexIncidentCell, h] using hz
  · refine ⟨1, ?_⟩
    have : x - 1 = z := by rw [h]; simp
    simpa [LatticeVertexIncidentCell, this] using hz
  · refine ⟨3, ?_⟩
    have : x - ⟨0, 1⟩ = z := by rw [h]; abel
    simpa [LatticeVertexIncidentCell, this] using hz
  · refine ⟨2, ?_⟩
    have : x - 1 - ⟨0, 1⟩ = z := by rw [h]; abel
    simpa [LatticeVertexIncidentCell, this] using hz

private abbrev raw_incident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem getLast_mem_of_eq_some :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ (l : List α), ∀ (x : α), (l.getLast? = some x) → (x ∈ l) ) := by
  classical
  intro α l x h
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h; subst x; simp
    | cons b l =>
      have h' : (b :: l).getLast? = some x := by simpa using h
      exact List.mem_cons_of_mem a (ih h')

private theorem head_mem_of_eq_some :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ (l : List α), ∀ (x : α), (l.head? = some x) → (x ∈ l) ) := by
  classical
  intro α l x h
  cases l with
  | nil => simp at h
  | cons a l => simp at h; subst x; simp

private theorem hAowners :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → ((ExceptionalRestorationSectorData (cert.P (0
            : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 : ℕ)) false) cert.O (cert.Q (1 : Fin (3 :
            ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false) (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1
            : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3 : ℕ)) true) (cert.P (1 : Fin (3 : ℕ))
            false) (cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm :
            PeriodicSubtileFaceIndex → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) →
            ((cert.exceptionalSegments.a ∈ cert.exceptionalSegments.left) → (∀ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q 1 true).cells ∨
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2 false).cells ∨
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ cert.O.cells))) ) := by
  classical
  intro q cfg C₀ T cert hO sector haLeft j
  have ho := sector.left_owners cert.exceptionalSegments.a haLeft (Or.inl hO) j
  rcases ho with hq | hs | hc | ho
  · exact Or.inl hq
  · exact Or.inr (Or.inl hs)
  · exact False.elim ((sector.positive_first_cut_no_companion hO j) hc.2)
  · exact Or.inr (Or.inr ho.2)

private theorem hBowners :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → ((ExceptionalRestorationSectorData (cert.P (0
            : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 : ℕ)) false) cert.O (cert.Q (1 : Fin (3 :
            ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false) (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1
            : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3 : ℕ)) true) (cert.P (1 : Fin (3 : ℕ))
            false) (cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm :
            PeriodicSubtileFaceIndex → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) →
            ((cert.exceptionalSegments.b ∈ cert.exceptionalSegments.right) → (∀ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells ∨
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells ∨
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ cert.O.cells))) ) := by
  classical
  intro q cfg C₀ T cert hO sector hbRight j
  have ho := sector.right_owners cert.exceptionalSegments.b hbRight (Or.inl hO) j
  rcases ho with hq | hs | hc | ho
  · exact Or.inl hq
  · exact Or.inr (Or.inl hs)
  · exact False.elim ((sector.positive_second_cut_no_companion hO j) hc.2)
  · exact Or.inr (Or.inr ho.2)

private theorem touching_disjoint :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (TileTouching X Y) → ((X.cells.Nonempty) →
            ((Y.cells.Nonempty) → (Disjoint X.cells Y.cells))) ) := by
  classical
  intro X Y h hneX hneY
  rcases h with ⟨_, _, hd, _⟩ | hX | hY
  · exact hd
  · have hempty : ¬ X.cells.Nonempty := by simp [hX.1]
    exact (hempty hneX).elim
  · have hempty : ¬ Y.cells.Nonempty := by simp [hY.1]
    exact (hempty hneY).elim

private theorem houterIntersection :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (cert.P 0 true).cells ∩ (cert.P 0 false).cells = cert.O.cells ) := by
  classical
  intro q cfg C₀ T cert
  have gzero : GaussianTranslation (0 : GaussianInt) = id := by
    funext z
    simp [GaussianTranslation]
  simpa [SubtileOccurrenceInterpretation, TileTranslation, GaussianTranslation,
    gzero] using
    (BandOriginalPairSeparation cert.P cert.O cert.u cert.v
      cert.exceptionalSegments.precursor_in_left
      cert.exceptionalSegments.precursor_in_right cert.partition).1 0 0

private theorem hQ1S1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Disjoint cert.O.cells (cert.Q (1 : Fin (3 : ℕ)) true).cells) → (((cert.P 0
            true).cells ∩ (cert.P 0 false).cells = cert.O.cells) → (Disjoint (cert.Q 1
            true).cells (cert.S 1 false).cells)) ) := by
  classical
  intro q cfg C₀ T cert hOQ1 houterIntersection
  rw [Finset.disjoint_left]
  intro x hxQ hxS
  have hxP : x ∈ (cert.P 0 true).cells :=
    (cert.plus_union x).2 ⟨1, true, hxQ⟩
  have hxM : x ∈ (cert.P 0 false).cells :=
    (cert.minus_union x).2 ⟨1, false, hxS⟩
  have hxO : x ∈ cert.O.cells := by
    rw [← houterIntersection]
    exact Finset.mem_inter.mpr ⟨hxP, hxM⟩
  exact Finset.disjoint_left.mp hOQ1.symm hxQ hxO

private theorem selectA_Q :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (LatticeTile (cert.Q 1 true)) → ((LatticeTile (cert.S 2 false)) →
            ((LatticeTile cert.O) → ((NoCheckerboardCellVertex (↑(cert.Q (1 : Fin (3 : ℕ))
            true).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑(cert.S (2 : Fin (3 :
            ℕ)) false).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑cert.O.cells :
            Set LatticeCell)) → ((∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ (cert.Q 1 true).cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2 false).cells) →
            ((∀ j : Fin 4, LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q 1
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈
            cert.O.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ cert.O.cells) → ((Disjoint (cert.Q (1 : Fin (3 : ℕ))
            true).cells (cert.S (2 : Fin (3 : ℕ)) false).cells) → ((Disjoint (cert.S (2 : Fin (3
            : ℕ)) false).cells cert.O.cells) → ((Disjoint cert.O.cells (cert.Q (1 : Fin (3 : ℕ))
            true).cells) → (∀ D, D = cert.Q 1 true ∨ D = cert.S 2 false ∨ D = cert.O → ∃ U V R :
            ProtoTile, (D = U ∨ D = V) ∧ ((U = cert.Q 1 true ∧ V = cert.S 2 false ∧ R = cert.O) ∨
            (U = cert.S 2 false ∧ V = cert.Q 1 true ∧ R = cert.O) ∨ (U = cert.Q 1 true ∧ V =
            cert.O ∧ R = cert.S 2 false) ∨ (U = cert.O ∧ V = cert.Q 1 true ∧ R = cert.S 2 false)
            ∨ (U = cert.S 2 false ∧ V = cert.O ∧ R = cert.Q 1 true) ∨ (U = cert.O ∧ V = cert.S 2
            false ∧ R = cert.Q 1 true)) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ U.cells ∧ LatticeVertexIncidentCell
            cert.exceptionalSegments.a (j + 2) ∈ V.cells) ∧ cert.exceptionalSegments.a ∈
            FootprintVertices U ∧ cert.exceptionalSegments.a ∈ FootprintVertices V ∧ (∀ y, y =
            cert.exceptionalSegments.a ∨ y = cert.exceptionalSegments.a + 1 ∨ y =
            cert.exceptionalSegments.a - 1 ∨ y = cert.exceptionalSegments.a + ⟨0, 1⟩ ∨ y =
            cert.exceptionalSegments.a - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈
            FootprintVertices V)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hQ2lat hS3lat hOlat hQ2check hS3check hOcheck hQ2occ hS3occ hAowners
      hOoccA hQS hSO hOQ D hD
  exact ThreeOwnerDesignatedOppositePair (cert.Q 1 true) (cert.S 2 false) cert.O
    cert.exceptionalSegments.a hQ2lat hS3lat hOlat hQS hSO hOQ
    hQ2check hS3check hOcheck hAowners hQ2occ hS3occ hOoccA D hD

private theorem selectB_Q :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (LatticeTile (cert.Q 2 true)) → ((LatticeTile (cert.S 1 false)) →
            ((LatticeTile cert.O) → ((NoCheckerboardCellVertex (↑(cert.Q (2 : Fin (3 : ℕ))
            true).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑(cert.S (1 : Fin (3 :
            ℕ)) false).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑cert.O.cells :
            Set LatticeCell)) → ((∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells) →
            ((∀ j : Fin 4, LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈
            cert.O.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ cert.O.cells) → ((Disjoint (cert.Q (2 : Fin (3 : ℕ))
            true).cells (cert.S (1 : Fin (3 : ℕ)) false).cells) → ((Disjoint (cert.S (1 : Fin (3
            : ℕ)) false).cells cert.O.cells) → ((Disjoint cert.O.cells (cert.Q (2 : Fin (3 : ℕ))
            true).cells) → (∀ D, D = cert.Q 2 true ∨ D = cert.S 1 false ∨ D = cert.O → ∃ U V R :
            ProtoTile, (D = U ∨ D = V) ∧ ((U = cert.Q 2 true ∧ V = cert.S 1 false ∧ R = cert.O) ∨
            (U = cert.S 1 false ∧ V = cert.Q 2 true ∧ R = cert.O) ∨ (U = cert.Q 2 true ∧ V =
            cert.O ∧ R = cert.S 1 false) ∨ (U = cert.O ∧ V = cert.Q 2 true ∧ R = cert.S 1 false)
            ∨ (U = cert.S 1 false ∧ V = cert.O ∧ R = cert.Q 2 true) ∨ (U = cert.O ∧ V = cert.S 1
            false ∧ R = cert.Q 2 true)) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ U.cells ∧ LatticeVertexIncidentCell
            cert.exceptionalSegments.b (j + 2) ∈ V.cells) ∧ cert.exceptionalSegments.b ∈
            FootprintVertices U ∧ cert.exceptionalSegments.b ∈ FootprintVertices V ∧ (∀ y, y =
            cert.exceptionalSegments.b ∨ y = cert.exceptionalSegments.b + 1 ∨ y =
            cert.exceptionalSegments.b - 1 ∨ y = cert.exceptionalSegments.b + ⟨0, 1⟩ ∨ y =
            cert.exceptionalSegments.b - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈
            FootprintVertices V)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check hS2check hOcheck hQ3occ hS2occ hBowners
      hOoccB hQ3S2 hS2O hOQ3 D hD
  exact ThreeOwnerDesignatedOppositePair (cert.Q 2 true) (cert.S 1 false) cert.O
    cert.exceptionalSegments.b hQ3lat hS2lat hOlat hQ3S2 hS2O hOQ3
    hQ3check hS2check hOcheck hBowners hQ3occ hS2occ hOoccB D hD

private theorem normalize_selected :
    (by
      classical
      exact
        ∀ (X : ProtoTile),
          ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile),
              ∀ (x : GaussianInt),
                X ≠ Y →
                  X ≠ Z →
                    (∃ U V R : ProtoTile,
                        (X = U ∨ X = V) ∧
                          (U = X ∧ V = Y ∧ R = Z ∨
                              U = Y ∧ V = X ∧ R = Z ∨
                                U = X ∧ V = Z ∧ R = Y ∨
                                U = Z ∧ V = X ∧ R = Y ∨
                                U = Y ∧ V = Z ∧ R = X ∨ U = Z ∧ V = Y ∧ R = X) ∧
                            (∃ j : Fin 4,
                                LatticeVertexIncidentCell x j ∈ U.cells ∧
                                LatticeVertexIncidentCell x (j + 2) ∈ V.cells) ∧
                              x ∈ FootprintVertices U ∧
                                x ∈ FootprintVertices V ∧
                                ∀ y,
                                y = x ∨
                                y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) →
                      ∃ W : ProtoTile,
                        (W = Y ∨ W = Z) ∧
                          ∃ j : Fin 4,
                            LatticeVertexIncidentCell x j ∈ X.cells ∧
                              LatticeVertexIncidentCell x (j + 2) ∈ W.cells ∧
                                x ∈ FootprintVertices X ∧
                                x ∈ FootprintVertices W ∧
                                ∀ y,
                                y = x ∨
                                y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                y ∈ FootprintVertices X ∨ y ∈ FootprintVertices W
    ) := by
  classical
  intro X Y Z x hXY hXZ hsel
  rcases hsel with ⟨U, V, R, hD, hperm, hopp, hU, hV, hstar⟩
  have reverse (A B : ProtoTile)
      (hopp : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ A.cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ B.cells)
      (hA : x ∈ FootprintVertices A) (hB : x ∈ FootprintVertices B)
      (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ FootprintVertices A ∨ y ∈ FootprintVertices B) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ B.cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ A.cells ∧
        x ∈ FootprintVertices B ∧ x ∈ FootprintVertices A ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ FootprintVertices B ∨ y ∈ FootprintVertices A) := by
    rcases hopp with ⟨j, hjA, hjB⟩
    have hindex : (j + 2) + 2 = j := by fin_cases j <;> decide
    refine ⟨j + 2, hjB, ?_, hB, hA, ?_⟩
    · simpa [hindex] using hjA
    · intro y hy
      rcases hstar y hy with ha | hb
      · exact Or.inr ha
      · exact Or.inl hb
  rcases hperm with p1 | p2 | p3 | p4 | p5 | p6
  · rcases p1 with ⟨hUX, hVY, hRZ⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · rcases hopp with ⟨j, hjX, hjY⟩
      exact ⟨Y, Or.inl rfl, j, hjX, hjY, hU, hV, hstar⟩
    · exact (hXY h).elim
  · rcases p2 with ⟨hUY, hVX, hRZ⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · exact (hXY h).elim
    · rcases reverse Y X hopp hU hV hstar with
        ⟨j, hjX, hjY, hcx, hpx, hcover⟩
      exact ⟨Y, Or.inl rfl, j, hjX, hjY, hcx, hpx, hcover⟩
  · rcases p3 with ⟨hUX, hVZ, hRY⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · rcases hopp with ⟨j, hjX, hjZ⟩
      exact ⟨Z, Or.inr rfl, j, hjX, hjZ, hU, hV, hstar⟩
    · exact (hXZ h).elim
  · rcases p4 with ⟨hUZ, hVX, hRY⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · exact (hXZ h).elim
    · rcases reverse Z X hopp hU hV hstar with
        ⟨j, hjX, hjZ, hcx, hpx, hcover⟩
      exact ⟨Z, Or.inr rfl, j, hjX, hjZ, hcx, hpx, hcover⟩
  · rcases p5 with ⟨hUY, hVZ, hRX⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · exact (hXY h).elim
    · exact (hXZ h).elim
  · rcases p6 with ⟨hUZ, hVY, hRX⟩
    subst U; subst V; subst R
    rcases hD with h | h
    · exact (hXZ h).elim
    · exact (hXY h).elim

private theorem ne_of_disjoint :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → ((X.cells.Nonempty) →
            (X ≠ Y)) ) := by
  classical
  intro X Y h hne hXYeq
  subst Y
  rcases hne with ⟨c, hc⟩
  exact Finset.disjoint_left.mp h hc hc

private theorem selectB_S :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (LatticeTile (cert.Q 2 true)) → ((LatticeTile (cert.S 1 false)) →
            ((LatticeTile cert.O) → ((NoCheckerboardCellVertex (↑(cert.Q (2 : Fin (3 : ℕ))
            true).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑(cert.S (1 : Fin (3 :
            ℕ)) false).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑cert.O.cells :
            Set LatticeCell)) → ((∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells) →
            ((∀ j : Fin 4, LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈
            cert.O.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ cert.O.cells) → ((Disjoint (cert.Q (2 : Fin (3 : ℕ))
            true).cells (cert.S (1 : Fin (3 : ℕ)) false).cells) → ((Disjoint (cert.S (1 : Fin (3
            : ℕ)) false).cells cert.O.cells) → ((Disjoint cert.O.cells (cert.Q (2 : Fin (3 : ℕ))
            true).cells) → (∀ D, D = cert.S 1 false ∨ D = cert.Q 2 true ∨ D = cert.O → ∃ U V R :
            ProtoTile, (D = U ∨ D = V) ∧ ((U = cert.S 1 false ∧ V = cert.Q 2 true ∧ R = cert.O) ∨
            (U = cert.Q 2 true ∧ V = cert.S 1 false ∧ R = cert.O) ∨ (U = cert.S 1 false ∧ V =
            cert.O ∧ R = cert.Q 2 true) ∨ (U = cert.O ∧ V = cert.S 1 false ∧ R = cert.Q 2 true) ∨
            (U = cert.Q 2 true ∧ V = cert.O ∧ R = cert.S 1 false) ∨ (U = cert.O ∧ V = cert.Q 2
            true ∧ R = cert.S 1 false)) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ U.cells ∧ LatticeVertexIncidentCell
            cert.exceptionalSegments.b (j + 2) ∈ V.cells) ∧ cert.exceptionalSegments.b ∈
            FootprintVertices U ∧ cert.exceptionalSegments.b ∈ FootprintVertices V ∧ (∀ y, y =
            cert.exceptionalSegments.b ∨ y = cert.exceptionalSegments.b + 1 ∨ y =
            cert.exceptionalSegments.b - 1 ∨ y = cert.exceptionalSegments.b + ⟨0, 1⟩ ∨ y =
            cert.exceptionalSegments.b - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈
            FootprintVertices V)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check hS2check hOcheck hQ3occ hS2occ hBowners
      hOoccB hQ3S2 hS2O hOQ3 D hD
  have owners : ∀ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ cert.O.cells := by
    intro j
    rcases hBowners j with hq | hs | ho
    · exact Or.inr (Or.inl hq)
    · exact Or.inl hs
    · exact Or.inr (Or.inr ho)
  exact ThreeOwnerDesignatedOppositePair (cert.S 1 false) (cert.Q 2 true) cert.O
    cert.exceptionalSegments.b hS2lat hQ3lat hOlat hQ3S2.symm hOQ3.symm hS2O.symm
    hS2check hQ3check hOcheck owners hS2occ hQ3occ hOoccB D hD

private theorem selectA_O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (LatticeTile (cert.Q 1 true)) → ((LatticeTile (cert.S 2 false)) →
            ((LatticeTile cert.O) → ((NoCheckerboardCellVertex (↑(cert.Q (1 : Fin (3 : ℕ))
            true).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑(cert.S (2 : Fin (3 :
            ℕ)) false).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑cert.O.cells :
            Set LatticeCell)) → ((∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ (cert.Q 1 true).cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2 false).cells) →
            ((∀ j : Fin 4, LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q 1
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈
            cert.O.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ cert.O.cells) → ((Disjoint (cert.Q (1 : Fin (3 : ℕ))
            true).cells (cert.S (2 : Fin (3 : ℕ)) false).cells) → ((Disjoint (cert.S (2 : Fin (3
            : ℕ)) false).cells cert.O.cells) → ((Disjoint cert.O.cells (cert.Q (1 : Fin (3 : ℕ))
            true).cells) → (∀ D, D = cert.O ∨ D = cert.Q 1 true ∨ D = cert.S 2 false → ∃ U V R :
            ProtoTile, (D = U ∨ D = V) ∧ ((U = cert.O ∧ V = cert.Q 1 true ∧ R = cert.S 2 false) ∨
            (U = cert.Q 1 true ∧ V = cert.O ∧ R = cert.S 2 false) ∨ (U = cert.O ∧ V = cert.S 2
            false ∧ R = cert.Q 1 true) ∨ (U = cert.S 2 false ∧ V = cert.O ∧ R = cert.Q 1 true) ∨
            (U = cert.Q 1 true ∧ V = cert.S 2 false ∧ R = cert.O) ∨ (U = cert.S 2 false ∧ V =
            cert.Q 1 true ∧ R = cert.O)) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ U.cells ∧ LatticeVertexIncidentCell
            cert.exceptionalSegments.a (j + 2) ∈ V.cells) ∧ cert.exceptionalSegments.a ∈
            FootprintVertices U ∧ cert.exceptionalSegments.a ∈ FootprintVertices V ∧ (∀ y, y =
            cert.exceptionalSegments.a ∨ y = cert.exceptionalSegments.a + 1 ∨ y =
            cert.exceptionalSegments.a - 1 ∨ y = cert.exceptionalSegments.a + ⟨0, 1⟩ ∨ y =
            cert.exceptionalSegments.a - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈
            FootprintVertices V)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hQ2lat hS3lat hOlat hQ2check hS3check hOcheck hQ2occ hS3occ hAowners
      hOoccA hQS hSO hOQ D hD
  have owners : ∀ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ cert.O.cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q 1 true).cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2 false).cells := by
    intro j
    rcases hAowners j with hq | hs | ho
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hs)
    · exact Or.inl ho
  exact ThreeOwnerDesignatedOppositePair cert.O (cert.Q 1 true) (cert.S 2 false)
    cert.exceptionalSegments.a hOlat hQ2lat hS3lat hOQ hQS hSO
    hOcheck hQ2check hS3check owners hOoccA hQ2occ hS3occ D hD

private theorem selectB_O :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (LatticeTile (cert.Q 2 true)) → ((LatticeTile (cert.S 1 false)) →
            ((LatticeTile cert.O) → ((NoCheckerboardCellVertex (↑(cert.Q (2 : Fin (3 : ℕ))
            true).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑(cert.S (1 : Fin (3 :
            ℕ)) false).cells : Set LatticeCell)) → ((NoCheckerboardCellVertex (↑cert.O.cells :
            Set LatticeCell)) → ((∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells) →
            ((∀ j : Fin 4, LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈
            cert.O.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ cert.O.cells) → ((Disjoint (cert.Q (2 : Fin (3 : ℕ))
            true).cells (cert.S (1 : Fin (3 : ℕ)) false).cells) → ((Disjoint (cert.S (1 : Fin (3
            : ℕ)) false).cells cert.O.cells) → ((Disjoint cert.O.cells (cert.Q (2 : Fin (3 : ℕ))
            true).cells) → (∀ D, D = cert.O ∨ D = cert.S 1 false ∨ D = cert.Q 2 true → ∃ U V R :
            ProtoTile, (D = U ∨ D = V) ∧ ((U = cert.O ∧ V = cert.S 1 false ∧ R = cert.Q 2 true) ∨
            (U = cert.S 1 false ∧ V = cert.O ∧ R = cert.Q 2 true) ∨ (U = cert.O ∧ V = cert.Q 2
            true ∧ R = cert.S 1 false) ∨ (U = cert.Q 2 true ∧ V = cert.O ∧ R = cert.S 1 false) ∨
            (U = cert.S 1 false ∧ V = cert.Q 2 true ∧ R = cert.O) ∨ (U = cert.Q 2 true ∧ V =
            cert.S 1 false ∧ R = cert.O)) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ U.cells ∧ LatticeVertexIncidentCell
            cert.exceptionalSegments.b (j + 2) ∈ V.cells) ∧ cert.exceptionalSegments.b ∈
            FootprintVertices U ∧ cert.exceptionalSegments.b ∈ FootprintVertices V ∧ (∀ y, y =
            cert.exceptionalSegments.b ∨ y = cert.exceptionalSegments.b + 1 ∨ y =
            cert.exceptionalSegments.b - 1 ∨ y = cert.exceptionalSegments.b + ⟨0, 1⟩ ∨ y =
            cert.exceptionalSegments.b - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈
            FootprintVertices V)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check hS2check hOcheck hQ3occ hS2occ hBowners
      hOoccB hQ3S2 hS2O hOQ3 D hD
  have owners : ∀ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ cert.O.cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells ∨
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells := by
    intro j
    rcases hBowners j with hq | hs | ho
    · exact Or.inr (Or.inr hq)
    · exact Or.inr (Or.inl hs)
    · exact Or.inl ho
  exact ThreeOwnerDesignatedOppositePair cert.O (cert.S 1 false) (cert.Q 2 true)
    cert.exceptionalSegments.b hOlat hS2lat hQ3lat hS2O.symm hQ3S2.symm hOQ3.symm
    hOcheck hS2check hQ3check owners hOoccB hS2occ hQ3occ D hD

private theorem hI2mul :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (I * I = -1) ) := by
  classical
  intro I hI2
  calc
    I * I = I ^ 2 := by ring
    _ = -1 := hI2

private theorem hnotEven3 :
    (by
      classical
      exact
        ¬Even 3
    ) := by
  classical
  rintro ⟨n, hn⟩
  omega

private theorem occurrence_centroid :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3), ∀
            (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))))) ) := by
  classical
  intro I r P X i s ho
  change BandPrototile (r i.succ) X ∧ _ ∧ _ at ho
  rcases ho with ⟨_, _, hc⟩
  convert hc using 1;
    ext <;>
    simp [GaussianRealPoint, I, sub_eq_add_neg, add_comm,
      smul_eq_mul]

private theorem hvector :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let ρ := cfg.firstPredecessor
        (ρ 2 = q 2) → ((ρ 3 = q 3) → (
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (ρ (2 : Fin (4 : ℕ))) (ρ (0 : Fin (4 : ℕ))) = BandVectors.1 (ρ (2 : Fin (4
            : ℕ))) (ρ (1 : Fin (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (ρ
            (3 : Fin (4 : ℕ))) (ρ (2 : Fin (4 : ℕ))) ∧ BandVectors.1 (ρ (0 : Fin (4 : ℕ))) (ρ (3
            : Fin (4 : ℕ))) = BandVectors.1 (ρ (1 : Fin (4 : ℕ))) (ρ (3 : Fin (4 : ℕ))) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (ρ (3 : Fin (4 : ℕ))) (ρ (2 : Fin (4 :
            ℕ))) ∧ BandVectors.2 (ρ (2 : Fin (4 : ℕ))) (ρ (0 : Fin (4 : ℕ))) = BandVectors.2 (ρ
            (2 : Fin (4 : ℕ))) (ρ (1 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (ρ (3 : Fin (4 : ℕ))) (ρ (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (ρ (0 : Fin
            (4 : ℕ))) (ρ (3 : Fin (4 : ℕ))) = BandVectors.2 (ρ (1 : Fin (4 : ℕ))) (ρ (3 : Fin (4
            : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (ρ (3 : Fin (4 : ℕ))) (ρ
            (2 : Fin (4 : ℕ)))) → ((ρ 0 = q 1) → (BandVectors.1 (q 1) (q 3) = I * BandVectors.1
            (q 3) (q 2) + BandVectors.1 (ρ 1) (ρ 3))))) ) := by
  classical
  intro q cfg ρ hρ2 hρ3 I hstep hρ0
  simpa [I, hρ0, hρ2, hρ3, add_comm] using hstep.2.1

private theorem hP0cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.P 0
            true) - TileCentroid T = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1
            (q 3) (q 2))) ) := by
  classical
  intro q cfg C₀ T cert I occurrence_centroid
  simpa [I] using occurrence_centroid q T (cert.P 0 true) 0 true
    (cert.outer_occurrence 0 true)

private theorem hP1cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.P 1
            true) - TileCentroid T = (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1
            (q 1) (q 3))) ) := by
  classical
  intro q cfg C₀ T cert I occurrence_centroid
  simpa [I] using occurrence_centroid q T (cert.P 1 true) 1 true
    (cert.outer_occurrence 1 true)

private theorem hQ2cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.Q 1
            true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (ρ 1) (ρ 3))) ) := by
  classical
  intro q cfg C₀ T cert ρ I occurrence_centroid
  simpa [I] using occurrence_centroid ρ (cert.P 0 true) (cert.Q 1 true) 1 true
    (cert.plus_occurrence 1 true)

private theorem translation_centroid :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation X z) = TileCentroid
            X + GaussianRealPoint z ) := by
  classical
  intro X z
  rw [(TileTranslationFormulas X z).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem hP0abs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.P 0 true) - TileCentroid T = (1 / 2 : Real) • GaussianRealPoint ((1 -
            I) * BandVectors.1 (q 3) (q 2))) → (TileCentroid (cert.P 0 true) = TileCentroid T +
            (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1 (q 3) (q 2))) ) := by
  classical
  intro q cfg C₀ T cert I hP0cent
  calc
    _ = (TileCentroid (cert.P 0 true) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [hP0cent]; exact add_comm _ _

private theorem hQ2abs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3))) → (TileCentroid (cert.Q 1
            true) = TileCentroid (cert.P 0 true) + (1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (ρ 1) (ρ 3))) ) := by
  classical
  intro q cfg C₀ T cert ρ I hQ2cent
  calc
    _ = (TileCentroid (cert.Q 1 true) - TileCentroid (cert.P 0 true)) +
        TileCentroid (cert.P 0 true) := by abel
    _ = _ := by rw [hQ2cent]; exact add_comm _ _

private theorem hP1abs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.P 1 true) - TileCentroid T = (1 / 2 : Real) • GaussianRealPoint ((1 -
            I) * BandVectors.1 (q 1) (q 3))) → (TileCentroid (cert.P 1 true) = TileCentroid T +
            (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1 (q 1) (q 3))) ) := by
  classical
  intro q cfg C₀ T cert I hP1cent
  calc
    _ = (TileCentroid (cert.P 1 true) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [hP1cent]; exact add_comm _ _


private theorem pointDouble :
    (by
      classical
      exact
        ∀ (x : GaussianInt), GaussianRealPoint (2 * x) = (2 : Real) • GaussianRealPoint x ) := by
  classical
  intro x
  ext <;> simp [GaussianRealPoint, Prod.smul_mk, smul_eq_mul]

private theorem hpoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) =
            GaussianRealPoint x + GaussianRealPoint y) → ((∀ (x : GaussianInt), GaussianRealPoint
            (2 * x) = (2 : Real) • GaussianRealPoint x) → (GaussianRealPoint ((1 - I) * (I *
            BandVectors.1 (q 3) (q 2) + BandVectors.1 (ρ 1) (ρ 3))) = GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 3) (q 2)) + GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ
            3)) + (2 : Real) • GaussianRealPoint (I * BandVectors.1 (q 3) (q 2))))) ) := by
  classical
  intro q cfg ρ I hI2mul pointAdd pointDouble
  have hv : (1 - I) * (I * BandVectors.1 (q 3) (q 2) +
      BandVectors.1 (ρ 1) (ρ 3)) =
      (1 - I) * BandVectors.1 (q 3) (q 2) +
        (1 - I) * BandVectors.1 (ρ 1) (ρ 3) +
          2 * (I * BandVectors.1 (q 3) (q 2)) := by
    have hm (x : GaussianInt) : (1 - I) * (I * x) =
        (1 - I) * x + 2 * (I * x) := by
      rw [sub_mul, one_mul, ← mul_assoc, hI2mul]
      ring
    rw [mul_add, hm]
    ring
  rw [hv, pointAdd, pointAdd, pointDouble]

private theorem hfixedPlusCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (q 1) (q 3) = I * BandVectors.1 (q 3) (q 2) + BandVectors.1 (ρ 1) (ρ 3)) →
            ((∀ (X : ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation X z) =
            TileCentroid X + GaussianRealPoint z) → ((TileCentroid (cert.P 0 true) = TileCentroid
            T + (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1 (q 3) (q 2))) →
            ((TileCentroid (cert.Q 1 true) = TileCentroid (cert.P 0 true) + (1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3))) → ((TileCentroid (cert.P 1
            true) = TileCentroid T + (1 / 2 : Real) • GaussianRealPoint ((1 - I) * BandVectors.1
            (q 1) (q 3))) → ((GaussianRealPoint ((1 - I) * (I * BandVectors.1 (q 3) (q 2) +
            BandVectors.1 (ρ 1) (ρ 3))) = GaussianRealPoint ((1 - I) * BandVectors.1 (q 3) (q 2))
            + GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3)) + (2 : Real) •
            GaussianRealPoint (I * BandVectors.1 (q 3) (q 2))) → (TileCentroid (TileTranslation
            (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))) = TileCentroid (cert.P 1 true)))))))
            ) := by
  classical
  intro q cfg C₀ T cert ρ I hvector translation_centroid hP0abs hQ2abs hP1abs hpoint
  rw [translation_centroid, hQ2abs, hP0abs, hP1abs, hvector, hpoint]
  ext <;> simp [smul_eq_mul] <;> ring

private theorem hfixedPlusNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty (cert.Q (1 : Fin (3 : ℕ)) true).cells) → (
        let I : GaussianInt := ⟨0, 1⟩
        (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))).cells.Nonempty) ) := by
  classical
  intro q cfg C₀ T cert hQ2ne I
  rw [(TileTranslationFormulas (cert.Q 1 true)
    (I * BandVectors.1 (q 3) (q 2))).1]
  exact hQ2ne.image _

private theorem hfixedPlusAbsent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → ((ExceptionalRestorationSectorData (cert.P (0
            : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 : ℕ)) false) cert.O (cert.Q (1 : Fin (3 :
            ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false) (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1
            : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3 : ℕ)) true) (cert.P (1 : Fin (3 : ℕ))
            false) (cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm :
            PeriodicSubtileFaceIndex → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((∀ (X : ProtoTile), ∀ (x :
            GaussianInt), (X.cells.Nonempty) → ((x ∈ FootprintVertices X) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ X.cells))) → (
        let I : GaussianInt := ⟨0, 1⟩
        ((TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) (I * BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))).cells = (cert.P (1 : Fin (3 : ℕ)) true).cells ∧
            ((TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) (I * BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))).cells = ∅ → (TileTranslation (cert.Q (1 : Fin (3 : ℕ))
            true) (I * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).anchor =
            (cert.P (1 : Fin (3 : ℕ)) true).anchor)) → (((TileTranslation (cert.Q 1 true) (I *
            BandVectors.1 (q 3) (q 2))).cells.Nonempty) → (cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q
            2)))))))) ) := by
  classical
  intro q cfg C₀ T cert hO sector raw_incident I hfixedPlusUnique hfixedPlusNonempty ha
  rcases raw_incident _ _ hfixedPlusNonempty ha with ⟨j, hj⟩
  have hp : LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈
      (cert.P 1 true).cells := by rw [hfixedPlusUnique.1] at hj; exact hj
  exact (sector.positive_first_cut_no_companion hO j) hp

private theorem hP0minuscent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.P 0
            false) - TileCentroid T = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 3) (q 2)))) ) := by
  classical
  intro q cfg C₀ T cert I occurrence_centroid
  simpa [I] using occurrence_centroid q T (cert.P 0 false) 0 false
    (cert.outer_occurrence 0 false)

private theorem hP1minuscent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.P 1
            false) - TileCentroid T = (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 1) (q 3)))) ) := by
  classical
  intro q cfg C₀ T cert I occurrence_centroid
  simpa [I] using occurrence_centroid q T (cert.P 1 false) 1 false
    (cert.outer_occurrence 1 false)

private theorem hS1cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (X : ProtoTile), ∀ (i : Fin 3),
            ∀ (s : Bool), (BandSubtileOccurrence r P i s X) → (TileCentroid X - TileCentroid P =
            (if s then (1 : Real) else -1) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I) *
            BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ)))))) → (TileCentroid (cert.S 1
            false) - TileCentroid (cert.P 0 false) = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3)))) ) := by
  classical
  intro q cfg C₀ T cert ρ I occurrence_centroid
  simpa [I] using occurrence_centroid ρ (cert.P 0 false) (cert.S 1 false) 1 false
    (cert.minus_occurrence 1 false)

private theorem hP0minusabs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.P 0 false) - TileCentroid T = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (q 3) (q 2)))) → (TileCentroid (cert.P 0
            false) = TileCentroid T + (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 3) (q 2)))) ) := by
  classical
  intro q cfg C₀ T cert I hP0minuscent
  calc
    _ = (TileCentroid (cert.P 0 false) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [hP0minuscent]; exact add_comm _ _

private theorem hS1abs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false) = (-1 : Real) • ((1 / 2 :
            Real) • GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3)))) → (TileCentroid
            (cert.S 1 false) = TileCentroid (cert.P 0 false) + (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3)))) ) := by
  classical
  intro q cfg C₀ T cert ρ I hS1cent
  calc
    _ = (TileCentroid (cert.S 1 false) - TileCentroid (cert.P 0 false)) +
        TileCentroid (cert.P 0 false) := by abel
    _ = _ := by rw [hS1cent]; exact add_comm _ _

private theorem hP1minusabs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let I : GaussianInt := ⟨0, 1⟩
        (TileCentroid (cert.P 1 false) - TileCentroid T = (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (q 1) (q 3)))) → (TileCentroid (cert.P 1
            false) = TileCentroid T + (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 1) (q 3)))) ) := by
  classical
  intro q cfg C₀ T cert I hP1minuscent
  calc
    _ = (TileCentroid (cert.P 1 false) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [hP1minuscent]; exact add_comm _ _


private theorem hfixedMinusCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (q 1) (q 3) = I * BandVectors.1 (q 3) (q 2) + BandVectors.1 (ρ 1) (ρ 3)) →
            ((∀ (X : ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation X z) =
            TileCentroid X + GaussianRealPoint z) → ((GaussianRealPoint ((1 - I) * (I *
            BandVectors.1 (q 3) (q 2) + BandVectors.1 (ρ 1) (ρ 3))) = GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 3) (q 2)) + GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ
            3)) + (2 : Real) • GaussianRealPoint (I * BandVectors.1 (q 3) (q 2))) →
            ((TileCentroid (cert.P 0 false) = TileCentroid T + (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (q 3) (q 2)))) → ((TileCentroid (cert.S 1
            false) = TileCentroid (cert.P 0 false) + (-1 : Real) • ((1 / 2 : Real) •
            GaussianRealPoint ((1 - I) * BandVectors.1 (ρ 1) (ρ 3)))) → ((TileCentroid (cert.P 1
            false) = TileCentroid T + (-1 : Real) • ((1 / 2 : Real) • GaussianRealPoint ((1 - I)
            * BandVectors.1 (q 1) (q 3)))) → ((∀ (z : GaussianInt), GaussianRealPoint (-z) =
            -GaussianRealPoint z) → (TileCentroid (TileTranslation (cert.S 1 false) (-I *
            BandVectors.1 (q 3) (q 2))) = TileCentroid (cert.P 1 false)))))))) ) := by
  classical
  intro q cfg C₀ T cert ρ I hvector translation_centroid hpoint hP0minusabs hS1abs hP1minusabs
      pointNeg
  rw [translation_centroid, hS1abs, hP0minusabs, hP1minusabs, hvector]
  have hshift : -I * BandVectors.1 (q 3) (q 2) =
      -(I * BandVectors.1 (q 3) (q 2)) := by ring
  rw [hshift, pointNeg, hpoint]
  ext <;> simp [smul_eq_mul] <;> ring

private theorem hfixedMinusNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty (cert.S (1 : Fin (3 : ℕ)) false).cells) → (
        let I : GaussianInt := ⟨0, 1⟩
        (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2))).cells.Nonempty) ) := by
  classical
  intro q cfg C₀ T cert hS2ne I
  rw [(TileTranslationFormulas (cert.S 1 false)
    (-I * BandVectors.1 (q 3) (q 2))).1]
  exact hS2ne.image _

private theorem hfixedMinusAbsent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → ((ExceptionalRestorationSectorData (cert.P (0
            : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 : ℕ)) false) cert.O (cert.Q (1 : Fin (3 :
            ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false) (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1
            : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3 : ℕ)) true) (cert.P (1 : Fin (3 : ℕ))
            false) (cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm :
            PeriodicSubtileFaceIndex → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((∀ (X : ProtoTile), ∀ (x :
            GaussianInt), (X.cells.Nonempty) → ((x ∈ FootprintVertices X) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ X.cells))) → (
        let I : GaussianInt := ⟨0, 1⟩
        ((TileTranslation (cert.S (1 : Fin (3 : ℕ)) false) (-I * BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))).cells = (cert.P (1 : Fin (3 : ℕ)) false).cells ∧
            ((TileTranslation (cert.S (1 : Fin (3 : ℕ)) false) (-I * BandVectors.1 (q (3 : Fin (4
            : ℕ))) (q (2 : Fin (4 : ℕ))))).cells = ∅ → (TileTranslation (cert.S (1 : Fin (3 : ℕ))
            false) (-I * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).anchor =
            (cert.P (1 : Fin (3 : ℕ)) false).anchor)) → (((TileTranslation (cert.S 1 false) (-I *
            BandVectors.1 (q 3) (q 2))).cells.Nonempty) → (cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q
            2)))))))) ) := by
  classical
  intro q cfg C₀ T cert hO sector raw_incident I hfixedMinusUnique hfixedMinusNonempty hb
  rcases raw_incident _ _ hfixedMinusNonempty hb with ⟨j, hj⟩
  have hp : LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈
      (cert.P 1 false).cells := by rw [hfixedMinusUnique.1] at hj; exact hj
  exact (sector.positive_second_cut_no_companion hO j) hp

private theorem p2_a_O_row :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → (
        let ρ := cfg.firstPredecessor
        ∀ (birth : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple birth) → (((birth (0 :
            Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (2 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧
            birth (3 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation (cert.Q (1 : Fin (3
            : ℕ)) true) (BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 :
            ℕ))))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation (cert.S (1
            : Fin (3 : ℕ)) false) (-BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1
            : Fin (4 : ℕ))))) ∨ (birth (0 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))
            ∧ birth (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = q (3 :
            Fin (4 : ℕ))) ∧ cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation
            cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation cert.O (BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation cert.O (-((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))))) →
            ((BandPrototile (ρ 1) cert.O) → ((BandPrototile (q 2) (cert.Q 1 true)) →
            ((BandPrototile (q 3) (cert.S 2 false)) → ((cert.Q (1 : Fin (3 : ℕ)) true ≠ cert.S (1
            : Fin (3 : ℕ)) false) → ((cert.S (2 : Fin (3 : ℕ)) false ≠ cert.O) → ((cert.Q (2 :
            Fin (3 : ℕ)) true ≠ cert.O) → ((∃ (W : ProtoTile), (W = cert.S (2 : Fin (3 : ℕ))
            false ∨ W = cert.O) ∧ ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∧
            LatticeVertexIncidentCell cert.exceptionalSegments.a (j + (2 : Fin (4 : ℕ))) ∈
            W.cells ∧ cert.exceptionalSegments.a ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ))
            true) ∧ cert.exceptionalSegments.a ∈ FootprintVertices W ∧ ∀ (y : GaussianInt), y =
            cert.exceptionalSegments.a ∨ y = cert.exceptionalSegments.a + (1 : GaussianInt) ∨ y
            = cert.exceptionalSegments.a - (1 : GaussianInt) ∨ y = cert.exceptionalSegments.a +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = cert.exceptionalSegments.a - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∨ y ∈
            FootprintVertices W) → (
        let I : GaussianInt := ⟨0, 1⟩
        ((TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) (I * BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))).cells = (cert.P (1 : Fin (3 : ℕ)) true).cells ∧
            ((TileTranslation (cert.Q (1 : Fin (3 : ℕ)) true) (I * BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))).cells = ∅ → (TileTranslation (cert.Q (1 : Fin (3 : ℕ))
            true) (I * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).anchor =
            (cert.P (1 : Fin (3 : ℕ)) true).anchor)) → ((cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))))
            → ((birth 0 = q 2 ∧ birth 2 = q 3 ∧ birth 3 = ρ 1) → (Nonempty
            (PositiveCutCompanionRow cert cert.exceptionalSegments.a)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hO ρ birth hproper branchExclusions hOproto hQ2proto hS3proto hneQ1S1
      hneA_SO hneB_QO selected_p2_a I hfixedPlusUnique hfixedPlusAbsent hp2
  have hbP2 : birth = ![q 2, birth 1, q 3, ρ 1] := by
    funext i
    fin_cases i
    · exact hp2.1
    · rfl
    · exact hp2.2.1
    · exact hp2.2.2
  have hnotQ2a : cert.exceptionalSegments.a ∉ FootprintVertices
      (TileTranslation (cert.Q 1 true) (BandVectors.1 (q 2) (ρ 1))) := by
    rcases branchExclusions with hEx | hEx
    · exact hEx.2.1
    · have hcycle : birth 3 = birth 0 := hp2.2.2.trans hEx.1.1.symm
      have hlt := hproper.2 2
      change (birth 3).1 < (birth 0).1 at hlt
      rw [hcycle] at hlt
      omega
  rcases selected_p2_a with ⟨W, hW, ⟨j, hj, hj2, hchild, hparent, hstar⟩⟩
  rcases hW with hWS | hWO
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 1,
      rotation := 1,
      child := cert.Q 1 true,
      parent := cert.S 2 false,
      proper := hproper,
      childPrototile := by simpa [hp2.1] using hQ2proto,
      parentPrototile := by simpa [hp2.2.1] using hS3proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) (cert.Q 1 true)
          (I ^ 1 * (if Even 1 then BandVectors.1 (birth 0) (birth 2)
            else BandVectors.1 (birth 2) (birth 0)))
          (by simpa [hp2.1] using hQ2proto),
      rightAbsent := by
        simpa [I, hp2.1, hp2.2.1] using hfixedPlusAbsent,
      fixedPlusCompanion := by
        intro _ _
        simpa [I, hp2.1, hp2.2.1] using
          (show (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))).cells =
            (cert.P 1 true).cells ∧
            ((TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))).cells = ∅ →
              (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))).anchor =
                (cert.P 1 true).anchor) from hfixedPlusUnique),
      fixedMinusCompanion := by
        intro hchildEq _
        exact (hneQ1S1 hchildEq).elim,
      literalRow := Or.inl ⟨hbP2, rfl, rfl, rfl, rfl, rfl⟩
    }⟩
  · subst W
    refine ⟨{
        precursorNonempty := hO,
        birth := birth,
        parentIndex := 2,
        rotation := 0,
        child := cert.Q 1 true,
        parent := cert.O,
        proper := hproper,
        childPrototile := by simpa [hp2.1] using hQ2proto,
        parentPrototile := by simpa [hp2.2.2] using hOproto,
        child_mem := hchild,
        parent_mem := hparent,
        opposite := ⟨j, hj, hj2⟩,
        star := hstar,
        rightPrototile := by
          exact BandPrototileTranslation (birth 0) (cert.Q 1 true)
            (I ^ 0 * (if Even 0 then BandVectors.1 (birth 0) (birth 3)
              else BandVectors.1 (birth 3) (birth 0)))
            (by simpa [hp2.1] using hQ2proto),
        rightAbsent := by
          simpa [I, hp2.1, hp2.2.2] using hnotQ2a,
        fixedPlusCompanion := by
          intro _ hparentEq
          exact (hneA_SO hparentEq.symm).elim,
        fixedMinusCompanion := by
          intro _ hparentEq
          exact (hneB_QO hparentEq.symm).elim,
        literalRow := Or.inr (Or.inl
          ⟨hbP2, rfl, rfl, rfl, rfl, rfl⟩)
    }⟩

private theorem p2_b_O_row :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → (
        let ρ := cfg.firstPredecessor
        ∀ (birth : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple birth) → (((birth (0 :
            Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (2 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧
            birth (3 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation (cert.Q (1 : Fin (3
            : ℕ)) true) (BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 :
            ℕ))))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation (cert.S (1
            : Fin (3 : ℕ)) false) (-BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1
            : Fin (4 : ℕ))))) ∨ (birth (0 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))
            ∧ birth (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = q (3 :
            Fin (4 : ℕ))) ∧ cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation
            cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation cert.O (BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation cert.O (-((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))))) →
            ((BandPrototile (ρ 1) cert.O) → ((BandPrototile (q 3) (cert.Q 2 true)) →
            ((BandPrototile (q 2) (cert.S 1 false)) → ((cert.Q (1 : Fin (3 : ℕ)) true ≠ cert.S (1
            : Fin (3 : ℕ)) false) → ((cert.Q (2 : Fin (3 : ℕ)) true ≠ cert.O) → ((∃ (W :
            ProtoTile), (W = cert.Q (2 : Fin (3 : ℕ)) true ∨ W = cert.O) ∧ ∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S (1 : Fin (3 : ℕ))
            false).cells ∧ LatticeVertexIncidentCell cert.exceptionalSegments.b (j + (2 : Fin (4
            : ℕ))) ∈ W.cells ∧ cert.exceptionalSegments.b ∈ FootprintVertices (cert.S (1 : Fin
            (3 : ℕ)) false) ∧ cert.exceptionalSegments.b ∈ FootprintVertices W ∧ ∀ (y :
            GaussianInt), y = cert.exceptionalSegments.b ∨ y = cert.exceptionalSegments.b + (1
            : GaussianInt) ∨ y = cert.exceptionalSegments.b - (1 : GaussianInt) ∨ y =
            cert.exceptionalSegments.b + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y =
            cert.exceptionalSegments.b - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈
            FootprintVertices (cert.S (1 : Fin (3 : ℕ)) false) ∨ y ∈ FootprintVertices W) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → ((I ^ 3 = -I) → ((¬ (∃ r : ℕ, 3 = r + r)) → (((TileTranslation (cert.S (1
            : Fin (3 : ℕ)) false) (-I * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
            ℕ))))).cells = (cert.P (1 : Fin (3 : ℕ)) false).cells ∧ ((TileTranslation (cert.S (1
            : Fin (3 : ℕ)) false) (-I * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
            ℕ))))).cells = ∅ → (TileTranslation (cert.S (1 : Fin (3 : ℕ)) false) (-I *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).anchor = (cert.P (1 : Fin
            (3 : ℕ)) false).anchor)) → ((cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2)))) → ((birth 0 = q
            2 ∧ birth 2 = q 3 ∧ birth 3 = ρ 1) → (Nonempty (PositiveCutCompanionRow cert
            cert.exceptionalSegments.b)))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hO ρ birth hproper branchExclusions hOproto hQ3proto hS2proto hneQ1S1
      hneB_QO' selected_p2_b I hI2 hI3 hodd3 hfixedMinusUnique hfixedMinusAbsent hp2
  have hbP2 : birth = ![q 2, birth 1, q 3, ρ 1] := by
    funext i
    fin_cases i
    · exact hp2.1
    · rfl
    · exact hp2.2.1
    · exact hp2.2.2
  have hnotS2b : cert.exceptionalSegments.b ∉ FootprintVertices
      (TileTranslation (cert.S 1 false) (-BandVectors.1 (q 2) (ρ 1))) := by
    rcases branchExclusions with hEx | hEx
    · exact hEx.2.2
    · have hcycle : birth 3 = birth 0 := hp2.2.2.trans hEx.1.1.symm
      have hlt := hproper.2 2
      change (birth 3).1 < (birth 0).1 at hlt
      rw [hcycle] at hlt
      omega
  rcases selected_p2_b with ⟨W, hW, ⟨j, hj, hj2, hchild, hparent, hstar⟩⟩
  rcases hW with hWQ | hWO
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 1,
      rotation := 3,
      child := cert.S 1 false,
      parent := cert.Q 2 true,
      proper := hproper,
      childPrototile := by simpa [hp2.1] using hS2proto,
      parentPrototile := by simpa [hp2.2.1] using hQ3proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) (cert.S 1 false)
          (I ^ 3 * (if Even 3 then BandVectors.1 (birth 0) (birth 2)
            else BandVectors.1 (birth 2) (birth 0)))
          (by simpa [hp2.1] using hS2proto),
      rightAbsent := by
        simpa [Even, hodd3, I, hp2.1, hp2.2.1, hI3] using hfixedMinusAbsent,
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneQ1S1 hchildEq.symm).elim,
      fixedMinusCompanion := by
        intro _ _
        simpa [Even, hodd3, I, hp2.1, hp2.2.1, hI3] using
          (show (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2))).cells =
            (cert.P 1 false).cells ∧
            ((TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2))).cells = ∅ →
              (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2))).anchor =
                (cert.P 1 false).anchor) from hfixedMinusUnique),
      literalRow := Or.inr (Or.inr (Or.inl ⟨hbP2, rfl, rfl, rfl, rfl, rfl⟩))
    }⟩
  · subst W
    have hnotS2b' : cert.exceptionalSegments.b ∉ FootprintVertices
        (TileTranslation (cert.S 1 false) (-BandVectors.1 (q 2) (ρ 1))) := hnotS2b
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 2,
      rotation := 2,
      child := cert.S 1 false,
      parent := cert.O,
      proper := hproper,
      childPrototile := by simpa [hp2.1] using hS2proto,
      parentPrototile := by simpa [hp2.2.2] using hOproto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) (cert.S 1 false)
          (I ^ 2 * (if Even 2 then BandVectors.1 (birth 0) (birth 3)
            else BandVectors.1 (birth 3) (birth 0)))
          (by simpa [hp2.1] using hS2proto),
      rightAbsent := by
        simpa [I, hp2.1, hp2.2.2, hI2] using hnotS2b',
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneQ1S1 hchildEq.symm).elim,
      fixedMinusCompanion := by
        intro _ hparentEq
        exact (hneB_QO' hparentEq.symm).elim,
      literalRow := Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hbP2, rfl, rfl, rfl, rfl, rfl⟩)))
    }⟩

private theorem p4_exclusions :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let ρ := cfg.firstPredecessor
        ∀ (birth : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple birth) → (((birth (0 :
            Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (2 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧
            birth (3 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation (cert.Q (1 : Fin (3
            : ℕ)) true) (BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 :
            ℕ))))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation (cert.S (1
            : Fin (3 : ℕ)) false) (-BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1
            : Fin (4 : ℕ))))) ∨ (birth (0 : Fin (4 : ℕ)) = cfg.firstPredecessor (1 : Fin (4 : ℕ))
            ∧ birth (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ birth (3 : Fin (4 : ℕ)) = q (3 :
            Fin (4 : ℕ))) ∧ cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation
            cert.O ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation cert.O (BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))) ∧ cert.exceptionalSegments.b ∉
            FootprintVertices (TileTranslation cert.O (-((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        (birth 0 = ρ 1 ∧ birth 2 = q 2 ∧ birth 3 = q 3) → (cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation cert.O (I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O
            (BandVectors.1 (ρ 1) (q 3))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation cert.O (-I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (ρ 1) (q 3)))))) ) := by
  classical
  intro q cfg C₀ T cert ρ birth hproper branchExclusions I hp4
  rcases branchExclusions with hEx | hEx
  · have hcycle : birth 3 = birth 0 := hEx.1.2.2.trans hp4.1.symm
    have hlt := hproper.2 2
    change (birth 3).1 < (birth 0).1 at hlt
    rw [hcycle] at hlt
    omega
  · exact ⟨hEx.2.1, hEx.2.2.1,
      (by simpa [neg_mul] using hEx.2.2.2.1), hEx.2.2.2.2⟩

private theorem p4_a_row :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → (
        let ρ := cfg.firstPredecessor
        ∀ (birth : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple birth) →
            ((BandPrototile (ρ 1) cert.O) → ((BandPrototile (q 2) (cert.Q 1 true)) →
            ((BandPrototile (q 3) (cert.S 2 false)) → ((cert.O ≠ cert.Q (1 : Fin (3 : ℕ)) true) →
            ((cert.O ≠ cert.S (1 : Fin (3 : ℕ)) false) → ((∃ (W : ProtoTile), (W = cert.Q (1 :
            Fin (3 : ℕ)) true ∨ W = cert.S (2 : Fin (3 : ℕ)) false) ∧ ∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ cert.O.cells ∧
            LatticeVertexIncidentCell cert.exceptionalSegments.a (j + (2 : Fin (4 : ℕ))) ∈
            W.cells ∧ cert.exceptionalSegments.a ∈ FootprintVertices cert.O ∧
            cert.exceptionalSegments.a ∈ FootprintVertices W ∧ ∀ (y : GaussianInt), y =
            cert.exceptionalSegments.a ∨ y = cert.exceptionalSegments.a + (1 : GaussianInt) ∨ y
            = cert.exceptionalSegments.a - (1 : GaussianInt) ∨ y = cert.exceptionalSegments.a +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = cert.exceptionalSegments.a - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices cert.O ∨ y ∈ FootprintVertices W) → (
        let I : GaussianInt := ⟨0, 1⟩
        ((birth 0 = ρ 1 ∧ birth 2 = q 2 ∧ birth 3 = q 3) → (cert.exceptionalSegments.a ∉
            FootprintVertices (TileTranslation cert.O (I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O
            (BandVectors.1 (ρ 1) (q 3))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation cert.O (-I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (ρ 1) (q 3))))) → ((birth 0 = ρ 1 ∧ birth 2 = q 2 ∧ birth 3 = q 3) →
            (Nonempty (PositiveCutCompanionRow cert cert.exceptionalSegments.a))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hO ρ birth hproper hOproto hQ2proto hS3proto hneA_OQ hneB_OS
      selected_p4_a I p4_exclusions hp4
  have hbP4 : birth = ![ρ 1, birth 1, q 2, q 3] := by
    funext i
    fin_cases i
    · exact hp4.1
    · rfl
    · exact hp4.2.1
    · exact hp4.2.2
  rcases selected_p4_a with ⟨W, hW, ⟨j, hj, hj2, hchild, hparent, hstar⟩⟩
  rcases hW with hWQ | hWS
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 1,
      rotation := 1,
      child := cert.O,
      parent := cert.Q 1 true,
      proper := hproper,
      childPrototile := by simpa [hp4.1] using hOproto,
      parentPrototile := by simpa [hp4.2.1] using hQ2proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) cert.O
          (I ^ 1 * (if Even 1 then BandVectors.1 (birth 0) (birth 2)
            else BandVectors.1 (birth 2) (birth 0)))
          (by simpa [hp4.1] using hOproto),
      rightAbsent := by
        simpa [I, hp4.1, hp4.2.1] using (p4_exclusions hp4).1,
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneA_OQ hchildEq).elim,
      fixedMinusCompanion := by
        intro hchildEq _
        exact (hneB_OS hchildEq).elim,
      literalRow := Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hbP4, rfl, rfl, rfl, rfl, rfl⟩))))
    }⟩
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 2,
      rotation := 0,
      child := cert.O,
      parent := cert.S 2 false,
      proper := hproper,
      childPrototile := by simpa [hp4.1] using hOproto,
      parentPrototile := by simpa [hp4.2.2] using hS3proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) cert.O
          (I ^ 0 * (if Even 0 then BandVectors.1 (birth 0) (birth 3)
            else BandVectors.1 (birth 3) (birth 0)))
          (by simpa [hp4.1] using hOproto),
      rightAbsent := by
        simpa [I, hp4.1, hp4.2.2] using (p4_exclusions hp4).2.1,
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneA_OQ hchildEq).elim,
      fixedMinusCompanion := by
        intro hchildEq _
        exact (hneB_OS hchildEq).elim,
      literalRow := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hbP4, rfl, rfl, rfl, rfl, rfl⟩)))))
    }⟩

private theorem p4_b_row :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (Finset.Nonempty cert.O.cells) → (
        let ρ := cfg.firstPredecessor
        ∀ (birth : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple birth) →
            ((BandPrototile (ρ 1) cert.O) → ((BandPrototile (q 3) (cert.Q 2 true)) →
            ((BandPrototile (q 2) (cert.S 1 false)) → ((cert.O ≠ cert.Q (1 : Fin (3 : ℕ)) true) →
            ((cert.O ≠ cert.S (1 : Fin (3 : ℕ)) false) → ((∃ (W : ProtoTile), (W = cert.S (1 :
            Fin (3 : ℕ)) false ∨ W = cert.Q (2 : Fin (3 : ℕ)) true) ∧ ∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ cert.O.cells ∧
            LatticeVertexIncidentCell cert.exceptionalSegments.b (j + (2 : Fin (4 : ℕ))) ∈
            W.cells ∧ cert.exceptionalSegments.b ∈ FootprintVertices cert.O ∧
            cert.exceptionalSegments.b ∈ FootprintVertices W ∧ ∀ (y : GaussianInt), y =
            cert.exceptionalSegments.b ∨ y = cert.exceptionalSegments.b + (1 : GaussianInt) ∨ y
            = cert.exceptionalSegments.b - (1 : GaussianInt) ∨ y = cert.exceptionalSegments.b +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = cert.exceptionalSegments.b - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices cert.O ∨ y ∈ FootprintVertices W) → (
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → ((I ^ 3 = -I) → ((¬ (∃ r : ℕ, 3 = r + r)) → (((birth 0 = ρ 1 ∧ birth 2 = q
            2 ∧ birth 3 = q 3) → (cert.exceptionalSegments.a ∉ FootprintVertices
            (TileTranslation cert.O (I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.a ∉ FootprintVertices (TileTranslation cert.O
            (BandVectors.1 (ρ 1) (q 3))) ∧ cert.exceptionalSegments.b ∉ FootprintVertices
            (TileTranslation cert.O (-I * BandVectors.1 (q 2) (ρ 1))) ∧
            cert.exceptionalSegments.b ∉ FootprintVertices (TileTranslation cert.O
            (-BandVectors.1 (ρ 1) (q 3))))) → ((birth 0 = ρ 1 ∧ birth 2 = q 2 ∧ birth 3 = q 3) →
            (Nonempty (PositiveCutCompanionRow cert cert.exceptionalSegments.b)))))))))))))) )
            := by
  classical
  intro q cfg C₀ T cert hO ρ birth hproper hOproto hQ3proto hS2proto hneA_OQ hneB_OS
      selected_p4_b I hI2 hI3 hodd3 p4_exclusions hp4
  have hbP4 : birth = ![ρ 1, birth 1, q 2, q 3] := by
    funext i
    fin_cases i
    · exact hp4.1
    · rfl
    · exact hp4.2.1
    · exact hp4.2.2
  rcases selected_p4_b with ⟨W, hW, ⟨j, hj, hj2, hchild, hparent, hstar⟩⟩
  rcases hW with hWS | hWQ
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 1,
      rotation := 3,
      child := cert.O,
      parent := cert.S 1 false,
      proper := hproper,
      childPrototile := by simpa [hp4.1] using hOproto,
      parentPrototile := by simpa [hp4.2.1] using hS2proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) cert.O
          (I ^ 3 * (if Even 3 then BandVectors.1 (birth 0) (birth 2)
            else BandVectors.1 (birth 2) (birth 0)))
          (by simpa [hp4.1] using hOproto),
      rightAbsent := by
        simpa [Even, hodd3, I, hp4.1, hp4.2.1, hI3] using
          (p4_exclusions hp4).2.2.1,
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneA_OQ hchildEq).elim,
      fixedMinusCompanion := by
        intro hchildEq _
        exact (hneB_OS hchildEq).elim,
      literalRow := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hbP4, rfl, rfl, rfl, rfl, rfl⟩))))))
    }⟩
  · subst W
    refine ⟨{
      precursorNonempty := hO,
      birth := birth,
      parentIndex := 2,
      rotation := 2,
      child := cert.O,
      parent := cert.Q 2 true,
      proper := hproper,
      childPrototile := by simpa [hp4.1] using hOproto,
      parentPrototile := by simpa [hp4.2.2] using hQ3proto,
      child_mem := hchild,
      parent_mem := hparent,
      opposite := ⟨j, hj, hj2⟩,
      star := hstar,
      rightPrototile := by
        exact BandPrototileTranslation (birth 0) cert.O
          (I ^ 2 * (if Even 2 then BandVectors.1 (birth 0) (birth 3)
            else BandVectors.1 (birth 3) (birth 0)))
          (by simpa [hp4.1] using hOproto),
      rightAbsent := by
        simpa [I, hp4.1, hp4.2.2, hI2] using
          (p4_exclusions hp4).2.2.2,
      fixedPlusCompanion := by
        intro hchildEq _
        exact (hneA_OQ hchildEq).elim,
      fixedMinusCompanion := by
        intro hchildEq _
        exact (hneB_OS hchildEq).elim,
      literalRow := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hbP4, rfl, rfl, rfl, rfl, rfl⟩))))))
    }⟩

end PositiveCutGeometry

theorem BandOrderedGeneralPositiveCutGeometry
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hO : cert.O.cells.Nonempty) :
    Nonempty (PositiveCutCompanionRow cert cert.exceptionalSegments.a) ∧
      Nonempty (PositiveCutCompanionRow cert cert.exceptionalSegments.b) := by
-- BODY
  let ρ := cfg.firstPredecessor
  have genealogy := BandParentBoundaryGenealogy ρ cfg.firstProper
  have hρ2 : ρ 2 = q 2 := by simpa [ρ] using cfg.firstParentTwo
  have hρ3 : ρ 3 = q 3 := by simpa [ρ] using cfg.firstParentThree
  have hlarge : 4 ≤ (ρ 2).1 := by
    simpa [ρ, cfg.firstParentTwo] using cfg.secondLarge
  have birthData := PositiveCutGeometry.birthData q cfg genealogy hρ2 hρ3 hlarge
  rcases birthData with ⟨birth, hproper, hbranch⟩
  have branchExclusions :=
    BandPositiveCutBranchCompanionExclusion q cfg C₀ T cert hO
      birth hproper hbranch
  have sector := BandExceptionalRestorationSectorOrder q cfg C₀ T cert
  have prototile_lattice := PositiveCutGeometry.prototile_lattice
  have tile_nonempty := PositiveCutGeometry.tile_nonempty
  have hcurv := ProperBandCurvatureStructure q cfg.proper
  have hq3pos := PositiveCutGeometry.hq3pos q cfg hcurv
  have hOproto : BandPrototile (ρ 1) cert.O := by
    simpa [cert.precursor_eq] using (cert.plus_occurrence 0 false).1
  have hOpos : 0 < (ρ 1).1 := by
    exact (PositiveCutGeometry.positive_of_nonempty) (ρ 1) cert.O hOproto hO
  have hQ2proto : BandPrototile (q 2) (cert.Q 1 true) := by
    simpa [cfg.firstParentTwo] using (cert.plus_occurrence 1 true).1
  have hS3proto : BandPrototile (q 3) (cert.S 2 false) := by
    simpa [cfg.firstParentThree] using (cert.minus_occurrence 2 false).1
  have hQ3proto : BandPrototile (q 3) (cert.Q 2 true) := by
    simpa [cfg.firstParentThree] using (cert.plus_occurrence 2 true).1
  have hS2proto : BandPrototile (q 2) (cert.S 1 false) := by
    simpa [cfg.firstParentTwo] using (cert.minus_occurrence 1 false).1
  have hQ2lat : LatticeTile (cert.Q 1 true) := by
    exact prototile_lattice _ _ hQ2proto (by have h := cfg.secondLarge; omega)
  have hS3lat : LatticeTile (cert.S 2 false) := by
    exact prototile_lattice _ _ hS3proto hq3pos
  have hQ3lat : LatticeTile (cert.Q 2 true) := by
    exact prototile_lattice _ _ hQ3proto hq3pos
  have hS2lat : LatticeTile (cert.S 1 false) := by
    exact prototile_lattice _ _ hS2proto (by have h := cfg.secondLarge; omega)
  have hOlat : LatticeTile cert.O := prototile_lattice _ _ hOproto hOpos
  have hQ2ne := tile_nonempty _ hQ2lat
  have hS3ne := tile_nonempty _ hS3lat
  have hQ3ne := tile_nonempty _ hQ3lat
  have hS2ne := tile_nonempty _ hS2lat
  have hOne := tile_nonempty _ hOlat
  have no_checker (X : ProtoTile) (hX : LatticeTile X) :
      NoCheckerboardCellVertex (X.cells : Set LatticeCell) :=
    (LatticeTileGridStructure X hX).2.1
  have hQ2check := no_checker _ hQ2lat
  have hS3check := no_checker _ hS3lat
  have hQ3check := no_checker _ hQ3lat
  have hS2check := no_checker _ hS2lat
  have hOcheck := no_checker _ hOlat
  have boundary_incident := PositiveCutGeometry.boundary_incident
      (BoundaryFootprintInclusion.boundaryVertex (BoundaryFootprintInclusion.boundaryEdge)
      (BoundaryFootprintInclusion.edgeVertex))
  have raw_incident := PositiveCutGeometry.raw_incident
  have haLeft : cert.exceptionalSegments.a ∈ cert.exceptionalSegments.left :=
    (PositiveCutGeometry.getLast_mem_of_eq_some) _ _ cert.exceptionalSegments.left_last
  have hbRight : cert.exceptionalSegments.b ∈ cert.exceptionalSegments.right :=
    (PositiveCutGeometry.head_mem_of_eq_some) _ _ cert.exceptionalSegments.right_head
  have hcutA := (cert.exceptionalSegments.first_cut_unique
    cert.exceptionalSegments.a).mpr rfl
  have hcutB := (cert.exceptionalSegments.second_cut_unique
    cert.exceptionalSegments.b).mpr rfl
  have hQ2occ : ∃ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q 1 true).cells :=
    boundary_incident _ _ hQ2ne hcutA.1
  have hS3occ : ∃ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S 2 false).cells :=
    boundary_incident _ _ hS3ne hcutA.2.1
  have hQ3occ : ∃ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q 2 true).cells :=
    boundary_incident _ _ hQ3ne hcutB.1
  have hS2occ : ∃ j : Fin 4,
      LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S 1 false).cells :=
    boundary_incident _ _ hS2ne hcutB.2.1
  have hAowners := PositiveCutGeometry.hAowners q cfg C₀ T cert hO sector haLeft
  have hBowners := PositiveCutGeometry.hBowners q cfg C₀ T cert hO sector hbRight
  have hOoccA := sector.positive_first_cut_precursor hO
  have hOoccB := sector.positive_second_cut_precursor hO
  have touching_disjoint := PositiveCutGeometry.touching_disjoint
  have hQS := touching_disjoint _ _ cert.precursor_first.1 hQ2ne hS3ne
  have hSO := touching_disjoint _ _ cert.precursor_first.2.1 hS3ne hOne
  have hOQ := touching_disjoint _ _ cert.precursor_first.2.2.1 hOne hQ2ne
  have hQ3S2 := touching_disjoint _ _ cert.precursor_second.1 hQ3ne hS2ne
  have hS2O := touching_disjoint _ _ cert.precursor_second.2.1 hS2ne hOne
  have hOQ3 := touching_disjoint _ _ cert.precursor_second.2.2.1 hOne hQ3ne
  have hQ2S2 := touching_disjoint _ _ cert.double_first.1 hQ2ne hS3ne
  have hOQ1 := touching_disjoint _ _ cert.precursor_first.2.2.1 hOne hQ2ne
  have hS1O := touching_disjoint _ _ cert.precursor_second.2.1 hS2ne hOne
  have selectB_Q := PositiveCutGeometry.selectB_Q q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check
      hS2check hOcheck hQ3occ hS2occ hBowners hOoccB hQ3S2 hS2O hOQ3
  have normalize_selected := PositiveCutGeometry.normalize_selected
  have ne_of_disjoint := PositiveCutGeometry.ne_of_disjoint
  have hneQ2S2 := ne_of_disjoint _ _ hQ2S2 hQ2ne
  have hneQ1S1 := ne_of_disjoint _ _ (PositiveCutGeometry.hQ1S1 q cfg C₀ T cert hOQ1
      (PositiveCutGeometry.houterIntersection q cfg C₀ T cert)) hQ2ne
  have hneA_QS := ne_of_disjoint _ _ hQS hQ2ne
  have hneA_QO := ne_of_disjoint _ _ hOQ.symm hQ2ne
  have hneA_SO := ne_of_disjoint _ _ hSO hS3ne
  have hneB_QS := ne_of_disjoint _ _ hQ3S2 hQ3ne
  have hneB_QO := ne_of_disjoint _ _ hOQ3.symm hQ3ne
  have hneB_SO := ne_of_disjoint _ _ hS2O hS2ne
  have hneB_SQ := ne_of_disjoint _ _ hQ3S2.symm hS2ne
  have hneB_SO' := ne_of_disjoint _ _ hS2O hS2ne
  have hneB_QO' := ne_of_disjoint _ _ hOQ3.symm hQ3ne
  have hneA_OQ := ne_of_disjoint _ _ hOQ hOne
  have hneA_OS := ne_of_disjoint _ _ hSO.symm hOne
  have hneB_OS := ne_of_disjoint _ _ hS2O.symm hOne
  have hneB_OQ := ne_of_disjoint _ _ hOQ3 hOne
  have selected_p2_a := normalize_selected (cert.Q 1 true) (cert.S 2 false) cert.O
    cert.exceptionalSegments.a hneA_QS hneA_QO
    ((PositiveCutGeometry.selectA_Q q cfg C₀ T cert hQ2lat hS3lat hOlat hQ2check hS3check hOcheck
        hQ2occ hS3occ hAowners hOoccA hQS hSO hOQ) (cert.Q 1 true) (Or.inl rfl))
  have selected_p2_b := normalize_selected (cert.S 1 false) (cert.Q 2 true) cert.O
    cert.exceptionalSegments.b hneB_SQ hneB_SO'
    ((PositiveCutGeometry.selectB_S q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check hS2check hOcheck
        hQ3occ hS2occ hBowners hOoccB hQ3S2 hS2O hOQ3) (cert.S 1 false) (Or.inl rfl))
  have selected_p4_a := normalize_selected cert.O (cert.Q 1 true) (cert.S 2 false)
    cert.exceptionalSegments.a hneA_OQ hneA_OS
    ((PositiveCutGeometry.selectA_O q cfg C₀ T cert hQ2lat hS3lat hOlat hQ2check hS3check hOcheck
        hQ2occ hS3occ hAowners hOoccA hQS hSO hOQ) cert.O (Or.inl rfl))
  have selected_p4_b := normalize_selected cert.O (cert.S 1 false) (cert.Q 2 true)
    cert.exceptionalSegments.b hneB_OS hneB_OQ
    ((PositiveCutGeometry.selectB_O q cfg C₀ T cert hQ3lat hS2lat hOlat hQ3check hS2check hOcheck
        hQ3occ hS2occ hBowners hOoccB hQ3S2 hS2O hOQ3) cert.O (Or.inl rfl))
  let I : GaussianInt := ⟨0, 1⟩
  have hI2 : I ^ 2 = -1 := by dsimp [I]; decide
  have hI3 : I ^ 3 = -I := by dsimp [I]; decide
  have hnotEven3 := PositiveCutGeometry.hnotEven3
  have hodd3 : ¬ (∃ r : ℕ, 3 = r + r) := by omega
  have occurrence_centroid := PositiveCutGeometry.occurrence_centroid
  have vectorSystem : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  have hstep := vectorSystem.2.2.1 ρ cfg.firstProper.1
  have hρ0 : ρ 0 = q 1 := by simpa [ρ] using cfg.firstChild
  have hvector := PositiveCutGeometry.hvector q cfg hρ2 hρ3 hstep hρ0
  have translation_centroid := PositiveCutGeometry.translation_centroid
  have hpoint := PositiveCutGeometry.hpoint q cfg (PositiveCutGeometry.hI2mul hI2)
      (GaussianRealPointProperties.add) (PositiveCutGeometry.pointDouble)
  have hfixedPlusProto : BandPrototile (q 2)
      (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2))) :=
    BandPrototileTranslation (q 2) (cert.Q 1 true)
      (I * BandVectors.1 (q 3) (q 2)) hQ2proto
  have hP1proto : BandPrototile (q 2) (cert.P 1 true) :=
    (cert.outer_occurrence 1 true).1
  have hfixedPlusUnique := BandPrototileCentroidUnique (q 2)
    (TileTranslation (cert.Q 1 true) (I * BandVectors.1 (q 3) (q 2)))
    (cert.P 1 true) hfixedPlusProto hP1proto (PositiveCutGeometry.hfixedPlusCentroid q cfg C₀ T
        cert hvector translation_centroid (PositiveCutGeometry.hP0abs q cfg C₀ T cert
        (PositiveCutGeometry.hP0cent q cfg C₀ T cert occurrence_centroid))
        (PositiveCutGeometry.hQ2abs q cfg C₀ T cert (PositiveCutGeometry.hQ2cent q cfg C₀ T cert
        occurrence_centroid)) (PositiveCutGeometry.hP1abs q cfg C₀ T cert
        (PositiveCutGeometry.hP1cent q cfg C₀ T cert occurrence_centroid)) hpoint)
  have hfixedMinusProto : BandPrototile (q 2)
      (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2))) :=
    BandPrototileTranslation (q 2) (cert.S 1 false)
      (-I * BandVectors.1 (q 3) (q 2)) hS2proto
  have hP1minusproto : BandPrototile (q 2) (cert.P 1 false) :=
    (cert.outer_occurrence 1 false).1
  have hfixedMinusUnique := BandPrototileCentroidUnique (q 2)
    (TileTranslation (cert.S 1 false) (-I * BandVectors.1 (q 3) (q 2)))
    (cert.P 1 false) hfixedMinusProto hP1minusproto (PositiveCutGeometry.hfixedMinusCentroid q
        cfg C₀ T cert hvector translation_centroid hpoint (PositiveCutGeometry.hP0minusabs q cfg
        C₀ T cert (PositiveCutGeometry.hP0minuscent q cfg C₀ T cert occurrence_centroid))
        (PositiveCutGeometry.hS1abs q cfg C₀ T cert (PositiveCutGeometry.hS1cent q cfg C₀ T cert
        occurrence_centroid)) (PositiveCutGeometry.hP1minusabs q cfg C₀ T cert
        (PositiveCutGeometry.hP1minuscent q cfg C₀ T cert occurrence_centroid))
        (GaussianRealPointProperties.negation))
  have p2_a_O_row := PositiveCutGeometry.p2_a_O_row q cfg C₀ T cert hO birth hproper
      branchExclusions hOproto hQ2proto hS3proto hneQ1S1 hneA_SO hneB_QO selected_p2_a
      hfixedPlusUnique (PositiveCutGeometry.hfixedPlusAbsent q cfg C₀ T cert hO sector
      raw_incident hfixedPlusUnique (PositiveCutGeometry.hfixedPlusNonempty q cfg C₀ T cert hQ2ne))
  have p2_b_O_row := PositiveCutGeometry.p2_b_O_row q cfg C₀ T cert hO birth hproper
      branchExclusions hOproto hQ3proto hS2proto hneQ1S1 hneB_QO' selected_p2_b hI2 hI3 hodd3
      hfixedMinusUnique (PositiveCutGeometry.hfixedMinusAbsent q cfg C₀ T cert hO sector
      raw_incident hfixedMinusUnique (PositiveCutGeometry.hfixedMinusNonempty q cfg C₀ T cert
      hS2ne))
  have p4_exclusions := PositiveCutGeometry.p4_exclusions q cfg C₀ T cert birth hproper
      branchExclusions
  have p4_a_row := PositiveCutGeometry.p4_a_row q cfg C₀ T cert hO birth hproper hOproto hQ2proto
      hS3proto hneA_OQ hneB_OS selected_p4_a p4_exclusions
  have p4_b_row := PositiveCutGeometry.p4_b_row q cfg C₀ T cert hO birth hproper hOproto hQ3proto
      hS2proto hneA_OQ hneB_OS selected_p4_b hI2 hI3 hodd3 p4_exclusions
  rcases hbranch with hp2 | hp4
  · exact ⟨p2_a_O_row hp2, p2_b_O_row hp2⟩
  · exact ⟨p4_a_row hp4, p4_b_row hp4⟩

end ApollonianSuperharmonic

end
