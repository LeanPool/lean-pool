/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralChildInterfaces
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPeriodicBlockCells
public import LeanPool.ApollonianSuperharmonic.IncomingSuperbasisRelation
public import LeanPool.ApollonianSuperharmonic.TileT1DiskArea
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleLatticeTouching
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: TileT3TranslateTouching]

/-!
# TileT3TranslateTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileT3TranslateTouching (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hcurrentT2 : QuarterTurnSymmetric T) (i : Fin 3) :
    TouchingTriple T
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
      (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))) := by
-- BODY
  classical
  have hroot : BandPrototile (q 0) T := by
    apply BandPrototile.decompose cfg.proper
    · intro j s
      exact (cert.outer_occurrence j s).1
    · exact cert.outer_union
    · intro j s
      exact (cert.outer_occurrence j s).2.1
    · intro j s
      exact (cert.outer_occurrence j s).2.2
  have hdisk := (TileT1DiskArea q cfg C₀ T hroot cert).1
  have hdisk₁ : LatticeTile
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) :=
    (TileDiskAreaCovariance T (BandVectors.1 (q i.succ) (q 0))).1.mp hdisk
  have hdisk₂ : LatticeTile
      (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))) :=
    (TileDiskAreaCovariance T (-BandVectors.1 (q ((i + 1).succ)) (q 0))).1.mp hdisk
  have hblocks := (BandOrderedGeneralPeriodicBlockCells q cfg C₀ T cert).2
  obtain ⟨g, _, hcenter, _⟩ := QuarterTurnSymmetricCenteredTransport T hcurrentT2
  have hcell (a x : GaussianInt) (hx : x ∈ (TileTranslation T a).cells) :
      GaussianQuarterTurn x - 1 + g ∈
        (TileTranslation T (GaussianQuarterTurn a)).cells := by
    rw [(TileTranslationFormulas T a).1] at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : GaussianQuarterTurn y - 1 + g ∈ T.cells := by
      rw [← hcenter, (TileTranslationFormulas (TileQuarterTurn T) g).1]
      apply Finset.mem_image.mpr
      refine ⟨GaussianQuarterTurn y - 1, ?_, rfl⟩
      rw [(TileQuarterTurnFormulas T).1]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    rw [(TileTranslationFormulas T (GaussianQuarterTurn a)).1]
    refine Finset.mem_image.mpr ⟨GaussianQuarterTurn y - 1 + g, hy', ?_⟩
    ext <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> ring
  have htransfer (a b : GaussianInt)
      (h : Disjoint (TileTranslation T (GaussianQuarterTurn a)).cells
        (TileTranslation T (GaussianQuarterTurn b)).cells) :
      Disjoint (TileTranslation T a).cells (TileTranslation T b).cells := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp h (hcell a x hx) (hcell b x hy)
  have hmul (z : GaussianInt) :
      GaussianQuarterTurn z = (⟨0, 1⟩ : GaussianInt) * z := by
    ext <;> simp [GaussianQuarterTurn]
  have hturn₀ : GaussianQuarterTurn (0 : GaussianInt) = 0 := by
    rw [hmul, mul_zero]
  have hzero : (TileTranslation T 0).cells = T.cells := by
    rw [(TileTranslationFormulas T 0).1]
    have hidentity : GaussianTranslation (0 : GaussianInt) = id := by
      funext z
      exact add_zero z
    rw [hidentity, Finset.image_id]
  have hflip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper
  have hturn₁ : GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) = cert.u := by
    rw [hmul, cert.period_u]
    simpa using (hflip 0).1.symm
  have hturn₂ : GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) = cert.v := by
    rw [hmul, cert.period_v]
    simpa using (hflip 1).1.symm
  have hsum : BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
      BandVectors.1 (q 3) (q 0) = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using (IncomingSuperbasisRelation q cfg.proper).1
  have hthird : BandVectors.1 (q 3) (q 0) =
      -BandVectors.1 (q 1) (q 0) - BandVectors.1 (q 2) (q 0) := by
    linear_combination hsum
  have hturn₃ : GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) =
      -cert.u - cert.v := by
    rw [hthird, hmul, mul_sub, mul_neg, ← hmul, ← hmul, hturn₁, hturn₂]
  let p : Fin 3 → Int × Int := ![(1, 0), (0, 1), (-1, -1)]
  have hcoords (j : Fin 3) : GaussianQuarterTurn (BandVectors.1 (q j.succ) (q 0)) =
      ((p j).1 : GaussianInt) * cert.u + ((p j).2 : GaussianInt) * cert.v := by
    fin_cases j <;> simp [p, hturn₁, hturn₂, hturn₃, sub_eq_add_neg]
  have hnegcoords (j : Fin 3) :
      GaussianQuarterTurn (-BandVectors.1 (q j.succ) (q 0)) =
        ((-(p j).1 : Int) : GaussianInt) * cert.u +
          ((-(p j).2 : Int) : GaussianInt) * cert.v := by
    rw [hmul, mul_neg, ← hmul, hcoords]
    simp [neg_mul, add_comm]
  have hneq₀₁ : (0, 0) ≠ p i := by fin_cases i <;> simp [p]
  have hneq₁₂ : p i ≠ (-(p (i + 1)).1, -(p (i + 1)).2) := by
    fin_cases i <;> decide +kernel
  have hneq₂₀ : (-(p (i + 1)).1, -(p (i + 1)).2) ≠ (0, 0) := by
    fin_cases i <;> decide +kernel
  have hdisjoint₀₁ : Disjoint T.cells
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0))).cells := by
    have h := hblocks 0 0 (p i).1 (p i).2 hneq₀₁
    have h' : Disjoint (TileTranslation T 0).cells
        (TileTranslation T (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))).cells := by
      simpa [hcoords] using h
    have h'' := htransfer 0 (BandVectors.1 (q i.succ) (q 0))
      (by simpa only [hturn₀] using h')
    simpa only [hzero] using h''
  have hdisjoint₁₂ : Disjoint
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0))).cells
      (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))).cells := by
    apply htransfer
    rw [hcoords, hnegcoords]
    exact hblocks (p i).1 (p i).2 (-(p (i + 1)).1) (-(p (i + 1)).2) hneq₁₂
  have hdisjoint₂₀ : Disjoint
      (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))).cells T.cells := by
    have h := hblocks (-(p (i + 1)).1) (-(p (i + 1)).2) 0 0 hneq₂₀
    have h' : Disjoint
        (TileTranslation T (GaussianQuarterTurn (-BandVectors.1 (q ((i + 1).succ)) (q 0)))).cells
        (TileTranslation T 0).cells := by
      simpa [hnegcoords] using h
    have h'' := htransfer (-BandVectors.1 (q ((i + 1).succ)) (q 0)) 0
      (by simpa only [hturn₀] using h')
    simpa only [hzero] using h''
  obtain ⟨E⟩ := (BandOrderedGeneralChildInterfaces q cfg C₀ T cert hcurrentT2).1 i
  exact ExactTileInterfaceTripleLatticeTouching T
    (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
    (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))) E
    hdisk hdisk₁ hdisk₂ hdisjoint₀₁ hdisjoint₁₂ hdisjoint₂₀

end ApollonianSuperharmonic

end
