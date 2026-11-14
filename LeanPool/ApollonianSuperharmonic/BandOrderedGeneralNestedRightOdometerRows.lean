/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorWebRow
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.OdometerWeb

-- [TABLET NODE: BandOrderedGeneralNestedRightOdometerRows]

/-!
# BandOrderedGeneralNestedRightOdometerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralNestedRightOdometerRows
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 -> Bool -> ProtoTile)
    (r : Fin 3 -> Bool -> PartialOdometer)
    (Q S : Fin 3 -> Bool -> ProtoTile)
    (u v : Fin 3 -> Bool -> PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt) (marked : Bool)
    (data : BandOrderedGeneralOdometerRowData
      q cfg C0 T cert h P r Q S u v g)
    (row : BandOrderedGeneralInteriorWebRow cert x marked)
    (right :
      (exists
        (left_mem : x ∈ FootprintVertices (cert.Q 1 true))
        (right_mem : x ∈ FootprintVertices (cert.P 1 true))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.Q 1 true) \/
            y ∈ FootprintVertices (cert.P 1 true))
        (squares :
          (forall z, z = x \/ z = x - 1 \/ z = x - ⟨0, 1⟩ \/
              z = x - 1 - ⟨0, 1⟩ ->
            z ∈ (cert.Q 1 true).cells \/
              z ∈ (cert.P 1 true).cells) <-> marked = false),
        row = .rightPositive left_mem right_mem star squares) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.S 1 false))
        (right_mem : x ∈ FootprintVertices (cert.P 1 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.S 1 false) \/
            y ∈ FootprintVertices (cert.P 1 false))
        (squares :
          (forall z, z = x \/ z = x - 1 \/ z = x - ⟨0, 1⟩ \/
              z = x - 1 - ⟨0, 1⟩ ->
            z ∈ (cert.S 1 false).cells \/
              z ∈ (cert.P 1 false).cells) <-> marked = false),
        row = .rightReflected left_mem right_mem star squares)) :
    (marked = false -> FourNeighborLaplacian g x = 1) /\
    (marked = true -> FourNeighborLaplacian g x = 0) := by
-- BODY
  have laws0 := VectorRecursionLaws q cfg.proper.1
  have hv13 : BandVectors.1 (q 1) (q 3) =
      -BandVectors.1 (q 2) (q 1) - BandVectors.1 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
          BandVectors.1 (q 2) (q 1) := by ring
      _ = 0 := laws0.1
  have ha13 : BandVectors.2 (q 1) (q 3) =
      -BandVectors.2 (q 2) (q 1) - BandVectors.2 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
          BandVectors.2 (q 2) (q 1) := by ring
      _ = 0 := laws0.2.1
  have laws := VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1
  have rotated := VectorRecursionLaws _
    (SemiProperQuadruple.rotate cfg.firstProper.1)
  have hv : BandVectors.1 (q 2) (q 1) =
      BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) -
        (Zsqrtd.mk 0 1 : GaussianInt) * BandVectors.1 (q 3) (q 2) := by
    simpa [cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree]
      using rotated.2.2.1
  have ha : BandVectors.2 (q 2) (q 1) =
      BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) +
        (Zsqrtd.mk 0 1 : GaussianInt) * BandVectors.2 (q 3) (q 2) := by
    simpa [cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree]
      using rotated.2.2.2.1
  have hvs := laws.1
  have has := laws.2.1
  rw [cfg.firstParentTwo] at hv ha
  rw [cfg.firstParentTwo, cfg.firstParentThree] at hvs has
  have hv43 : BandVectors.1 (cfg.firstPredecessor 1) (q 3) =
      -BandVectors.1 (q 2) (q 1) -
        (1 + (Zsqrtd.mk 0 1 : GaussianInt)) * BandVectors.1 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = (BandVectors.1 (q 3) (q 2) +
          BandVectors.1 (cfg.firstPredecessor 1) (q 3) +
          BandVectors.1 (q 2) (cfg.firstPredecessor 1)) +
          (BandVectors.1 (q 2) (q 1) -
            (BandVectors.1 (q 2) (cfg.firstPredecessor 1) -
              (Zsqrtd.mk 0 1 : GaussianInt) * BandVectors.1 (q 3) (q 2))) := by
        ring
      _ = 0 := by rw [hvs, hv]; ring
  have ha43 : BandVectors.2 (cfg.firstPredecessor 1) (q 3) =
      -BandVectors.2 (q 2) (q 1) -
        (1 - (Zsqrtd.mk 0 1 : GaussianInt)) * BandVectors.2 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = (BandVectors.2 (q 3) (q 2) +
          BandVectors.2 (cfg.firstPredecessor 1) (q 3) +
          BandVectors.2 (q 2) (cfg.firstPredecessor 1)) +
          (BandVectors.2 (q 2) (q 1) -
            (BandVectors.2 (q 2) (cfg.firstPredecessor 1) +
              (Zsqrtd.mk 0 1 : GaussianInt) * BandVectors.2 (q 3) (q 2))) := by
        ring
      _ = 0 := by rw [has, ha]; ring
  have flip := (VectorRecursionLaws cfg.secondPredecessor
    cfg.secondProper.1).2.2.2.2 cfg.secondProper 0
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    cfg.secondChild, cfg.secondParentOne] at flip
  have positive : 0 < (q 2).1 := by linarith [cfg.secondLarge]
  let C2 : BandCircle :=
    ⟨⟨q 2, Or.inl positive, q, cfg.proper.1, 2, rfl⟩, positive⟩
  -- Keep the nested leaf first, with its own defined slope witness.
  have makeRight (s : Bool) (N : ProtoTile) (k : PartialOdometer)
      (hNk : TileOdometer (q 2) N k)
      (hcent : TileCentroid N - TileCentroid (P 0 s) =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1) (q 3)) -
              (-(GaussianRealPoint
                (BandVectors.1 (cfg.firstPredecessor 1) (q 3))).2,
                (GaussianRealPoint
                  (BandVectors.1 (cfg.firstPredecessor 1) (q 3))).1))))
      (hslope : exists p pi : Real × Real,
        PartialOdometerSlope (r 0 s) = some p /\
        PartialOdometerSlope k = some pi /\
        pi.1 - p.1 = (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor 1) (q 3)).re : Int) -
            ((BandVectors.2 (cfg.firstPredecessor 1) (q 3)).im : Int)) /\
        pi.2 - p.2 = (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor 1) (q 3)).im : Int) +
            ((BandVectors.2 (cfg.firstPredecessor 1) (q 3)).re : Int))) :
      RightLatticeAdjacent C2 N (P 1 s) k (r 1 s) := by
    obtain ⟨p, p1, hp, hp1, hp1x, hp1y⟩ :=
      (data.hPslope 0 s).resolve_left (cfg.noLine 1)
    obtain ⟨p', p2, hp', hp2, hp2x, hp2y⟩ :=
      (data.hPslope 1 s).resolve_left (cfg.noLine 2)
    have hbase : p' = p := Option.some.inj (hp'.symm.trans hp)
    subst p'
    obtain ⟨p1', pn, hp1', hpn, hpnx, hpny⟩ := hslope
    have hbase1 : p1' = p1 := Option.some.inj (hp1'.symm.trans hp1)
    subst p1'
    refine ⟨hNk, data.hP 1 s, pn, p2, hpn, hp2,
      cfg.secondPredecessor, 0, s, cfg.secondProper, cfg.secondChild, ?_, ?_, ?_⟩
    · have hc1 := data.hPcent 0 s
      have hc2 := data.hPcent 1 s
      have hn1 := congrArg Prod.fst hcent
      have hn2 := congrArg Prod.snd hcent
      have hc1x := congrArg Prod.fst hc1
      have hc1y := congrArg Prod.snd hc1
      have hc2x := congrArg Prod.fst hc2
      have hc2y := congrArg Prod.snd hc2
      apply Prod.ext
      · cases s <;>
          simp [GaussianRealPoint, cfg.secondChild, cfg.secondParentOne,
            hv13, hv43, flip.1] at hn1 hc1x hc2x ⊢ <;> linarith
      · cases s <;>
          simp [GaussianRealPoint, cfg.secondChild, cfg.secondParentOne,
            hv13, hv43, flip.1] at hn2 hc1y hc2y ⊢ <;> linarith
    · cases s <;>
        simp [cfg.secondChild, cfg.secondParentOne, ha13, ha43, flip.2]
          at hp1x hp2x hpnx ⊢ <;> linarith
    · cases s <;>
        simp [cfg.secondChild, cfg.secondParentOne, ha13, ha43, flip.2]
          at hp1y hp2y hpny ⊢ <;> linarith
  have rightPositive : RightLatticeAdjacent C2
      (Q 1 true) (P 1 true) (u 1 true) (r 1 true) := by
    apply makeRight true (Q 1 true) (u 1 true)
    · simpa [cfg.firstParentTwo] using data.hQ 1 true
    · simpa [cfg.firstParentThree] using data.hQcent 1 true
    · have hs := (data.hQslope 1 true).resolve_left (by
        simpa [cfg.firstParentTwo] using cfg.noLine 2)
      simpa [cfg.firstParentThree] using hs
  have rightReflected : RightLatticeAdjacent C2
      (S 1 false) (P 1 false) (v 1 false) (r 1 false) := by
    apply makeRight false (S 1 false) (v 1 false)
    · simpa [cfg.firstParentTwo] using data.hS 1 false
    · simpa [cfg.firstParentThree] using data.hScent 1 false
    · have hs := (data.hSslope 1 false).resolve_left (by
        simpa [cfg.firstParentTwo] using cfg.noLine 2)
      simpa [cfg.firstParentThree] using hs
  have finish (N R : ProtoTile) (k l : PartialOdometer)
      (adj : RightLatticeAdjacent C2 N R k l)
      (extk : GlobalOdometerExtends g k) (extl : GlobalOdometerExtends g l)
      (compat : OdometerCompatibility k l)
      (memk : x ∈ FootprintVertices N) (meml : x ∈ FootprintVertices R)
      (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
        y ∈ FootprintVertices N \/ y ∈ FootprintVertices R)
      (squares : (forall z, z = x \/ z = x - 1 \/ z = x - ⟨0, 1⟩ \/
          z = x - 1 - ⟨0, 1⟩ -> z ∈ N.cells \/ z ∈ R.cells) <-> marked = false) :
      (marked = false -> FourNeighborLaplacian g x = 1) /\
      (marked = true -> FourNeighborLaplacian g x = 0) := by
    have domk := PositiveCurvatureTileOdometerDomain (q 2) N k positive adj.1
    have doml := PositiveCurvatureTileOdometerDomain (q 2) R l positive adj.2.1
    have web := (OdometerWeb.1 C2 N R k l g x compat extk extl
      (by
        change x ∈ (k.domain : Set GaussianInt)
        rw [domk]
        exact memk)
      (by
        change x ∈ (l.domain : Set GaussianInt)
        rw [doml]
        exact meml)
      (by
        intro y hy
        change y ∈ (k.domain : Set GaussianInt) ∨ y ∈ (l.domain : Set GaussianInt)
        rw [domk, doml]
        exact star y hy)).2 adj
    constructor
    · intro hm
      exact web.1 (squares.mpr hm)
    · intro hm
      apply web.2
      intro full
      have := squares.mp full
      simp [hm] at this
  rcases right with pos | neg
  · obtain ⟨memQ, memP, star, squares, _⟩ := pos
    apply finish (Q 1 true) (P 1 true) (u 1 true) (r 1 true)
      rightPositive (data.hextQ 1 true) (data.hextP 1 true)
    · exact data.hcompat _ _ ⟨1, true, Or.inr (Or.inl rfl)⟩
        ⟨1, true, Or.inl rfl⟩
    · simpa [(data.hobsQ 1 true).2.1] using memQ
    · simpa [(data.hobsP 1 true).2.1] using memP
    · simpa [(data.hobsQ 1 true).2.1, (data.hobsP 1 true).2.1] using star
    · simpa [(data.hobsQ 1 true).1, (data.hobsP 1 true).1] using squares
  · obtain ⟨memS, memP, star, squares, _⟩ := neg
    apply finish (S 1 false) (P 1 false) (v 1 false) (r 1 false)
      rightReflected (data.hextS 1 false) (data.hextP 1 false)
    · exact data.hcompat _ _ ⟨1, false, Or.inr (Or.inr rfl)⟩
        ⟨1, false, Or.inl rfl⟩
    · simpa [(data.hobsS 1 false).2.1] using memS
    · simpa [(data.hobsP 1 false).2.1] using memP
    · simpa [(data.hobsS 1 false).2.1, (data.hobsP 1 false).2.1] using star
    · simpa [(data.hobsS 1 false).1, (data.hobsP 1 false).1] using squares

end ApollonianSuperharmonic

end
