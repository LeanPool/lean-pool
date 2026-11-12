/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.CurvatureOneTileBase
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: P4339T1PrecursorSupportGeometry]

/-!
# P4339T1PrecursorSupportGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4339T1PrecursorSupportGeometry
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    TileCentroid cert.O = TileCentroid T ∧
    (cert.O.cells = ∅ ↔ (cfg.firstPredecessor 1).1 = 0) ∧
    BandPrototile (cfg.firstPredecessor 1) cert.O ∧
    (cert.O.cells.Nonempty → LatticeTile cert.O) ∧
    (cert.Q 1 true).cells.Nonempty ∧
    (cert.S 2 false).cells.Nonempty ∧
    (cert.P 0 true).cells ∩ (cert.P 0 false).cells = cert.O.cells ∧
    (∀ (i : Fin 3) (s : Bool) (j : Fin 3) (t : Bool),
      (i, s) ≠ (j, t) → ¬ (i = 0 ∧ j = 0) →
      Disjoint (cert.P i s).cells (cert.P j t).cells) := by
-- BODY
  classical
  have hband : BandPrototile (cfg.firstPredecessor 1) cert.O := by
    rw [cert.precursor_eq]
    exact (cert.plus_occurrence 0 false).1
  have hOA : cert.O.cells ⊆ (cert.P 0 true).cells := by
    intro z hz
    apply (cert.plus_union z).mpr
    exact ⟨0, false, by simpa only [← cert.precursor_eq] using hz⟩
  have hOB : cert.O.cells ⊆ (cert.P 0 false).cells := by
    intro z hz
    exact (cert.minus_union z).mpr ⟨0, true, by rw [← cert.precursor_cells]; exact hz⟩
  have hseparate := BandOriginalPairSeparation
    cert.P cert.O cert.u cert.v hOA hOB cert.partition
  have htranslation_zero : GaussianTranslation 0 = id := by
    funext z
    exact add_zero z
  have hpair : (cert.P 0 true).cells ∩ (cert.P 0 false).cells = cert.O.cells := by
    simpa [SubtileOccurrenceInterpretation, TileTranslation, htranslation_zero]
      using hseparate.1 0 0
  have hcentroid : TileCentroid cert.O = TileCentroid T := by
    have hsame : TileCentroid cert.O = TileCentroid (cert.S 0 true) := by
      simp only [TileCentroid, ← cert.precursor_cells]
      split_ifs with hn
      · rfl
      · rw [cert.precursor_anchor (Finset.not_nonempty_iff_eq_empty.mp hn)]
    have hp := (cert.outer_occurrence 0 true).2.2
    have hm := (cert.outer_occurrence 0 false).2.2
    have hnp := (cert.minus_occurrence 0 true).2.2
    have hnm := (cert.plus_occurrence 0 false).2.2
    rw [← cert.precursor_eq] at hnm
    rw [← hsame] at hnp
    simp only [Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul] at hp hm hnp hnm
    apply Prod.ext
    · have a := congrArg Prod.fst hp
      have b := congrArg Prod.fst hm
      have c := congrArg Prod.fst hnp
      have d := congrArg Prod.fst hnm
      simp only [Prod.fst_sub, Prod.fst_neg] at a b c d
      linarith
    · have a := congrArg Prod.snd hp
      have b := congrArg Prod.snd hm
      have c := congrArg Prod.snd hnp
      have d := congrArg Prod.snd hnm
      simp only [Prod.snd_sub, Prod.snd_neg] at a b c d
      linarith
  have zero_empty (d : CircleCoordinates) (U : ProtoTile)
      (hb : BandPrototile d U) (hz : d.1 = 0) : U.cells = ∅ := by
    cases hb with
    | line => rfl
    | unit => norm_num at hz
    | decompose hp _ _ _ _ =>
        have hpos := (ProperBandCurvatureStructure _ hp).1
        omega
  have positive_nonempty (d : CircleCoordinates) (U : ProtoTile)
      (hb : BandPrototile d U) (hpos : 0 < d.1) : U.cells.Nonempty := by
    cases hb with
    | line => norm_num at hpos
    | unit => exact Finset.singleton_nonempty _
    | @decompose p hp S V hS hc hf ht =>
        exact (LatticeTileGridStructure U (BandTileSimultaneousInduction p hp U
          (BandPrototile.decompose hp hS hc hf ht)).1).1.1
  have hzero : cert.O.cells = ∅ ↔ (cfg.firstPredecessor 1).1 = 0 :=
    ⟨cert.precursor_zero_curvature, zero_empty _ _ hband⟩
  have hdisk : cert.O.cells.Nonempty → LatticeTile cert.O := by
    have nonempty_disk (d : CircleCoordinates) (U : ProtoTile)
        (hb : BandPrototile d U)
        (hancestry : ∃ p : Fin 4 → CircleCoordinates,
          SemiProperQuadruple p ∧ ∃ j : Fin 4, p j = d)
        (hn : U.cells.Nonempty) : LatticeTile U := by
      cases hb with
      | line => simp at hn
      | unit z x anchor =>
          let B : BandCircle :=
            ⟨⟨(1, 1 + 2 * z), ⟨Or.inl (by norm_num), hancestry⟩⟩, by norm_num⟩
          obtain ⟨V, hV, harea, _⟩ := CurvatureOneTileBase B rfl
          obtain ⟨y, hy⟩ := Finset.card_eq_one.mp harea
          have ht := (TileDiskAreaCovariance V (x - y)).1.mp hV
          have hcells : (TileTranslation V (x - y)).cells = {x} := by
            rw [(TileTranslationFormulas V (x - y)).1, hy]
            simp [GaussianTranslation]
          change TopologicalDisk (TileRealization _) at ht ⊢
          simpa only [TileRealization, hcells] using ht
      | @decompose p hp S V hS hc hf ht =>
          exact (BandTileSimultaneousInduction p hp U
            (BandPrototile.decompose hp hS hc hf ht)).1
    exact nonempty_disk _ _ hband
      ⟨cfg.firstPredecessor, cfg.firstProper.1, 1, rfl⟩
  have hQ : (cert.Q 1 true).cells.Nonempty := by
    apply positive_nonempty _ _ (cert.plus_occurrence 1 true).1
    change 0 < (cfg.firstPredecessor 2).1
    rw [cfg.firstParentTwo]
    have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 1
    change 0 ≤ (q 2).1 at hn
    have hz := cfg.noLine 2
    change 0 < (q 2).1
    omega
  have hS : (cert.S 2 false).cells.Nonempty := by
    apply positive_nonempty _ _ (cert.minus_occurrence 2 false).1
    change 0 < (cfg.firstPredecessor 3).1
    rw [cfg.firstParentThree]
    have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 2
    change 0 ≤ (q 3).1 at hn
    have hz := cfg.noLine 3
    change 0 < (q 3).1
    omega
  refine ⟨hcentroid, hzero, hband, hdisk, hQ, hS, hpair, ?_⟩
  let idx (i : Fin 3) (s : Bool) : PeriodicSubtileIndex :=
    ⟨if i = 0 then (if s then .A else .B)
      else if i = 1 then (if s then .C else .D)
      else (if s then .E else .F), 0, 0⟩
  have idx_cells (i : Fin 3) (s : Bool) :
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v (idx i s)).cells =
        (cert.P i s).cells := by
    fin_cases i <;> cases s <;>
      simp [idx, SubtileOccurrenceInterpretation, TileTranslation, htranslation_zero]
  intro i s j t hne hnot
  have hidx : idx i s ≠ idx j t := by
    clear * - i s j t hne idx
    intro he
    apply hne
    fin_cases i <;> cases s <;> fin_cases j <;> cases t <;> simp_all [idx]
  have hnopair : ¬ (((idx i s).label = .A ∧ (idx j t).label = .B ∨
          (idx i s).label = .B ∧ (idx j t).label = .A) ∧
        (idx i s).first = (idx j t).first ∧
        (idx i s).second = (idx j t).second) := by
    clear * - i s j t hnot idx
    fin_cases i <;> cases s <;> fin_cases j <;> cases t <;> simp_all [idx]
  simpa only [idx_cells] using hseparate.2 (idx i s) (idx j t) hidx hnopair

end ApollonianSuperharmonic

end
