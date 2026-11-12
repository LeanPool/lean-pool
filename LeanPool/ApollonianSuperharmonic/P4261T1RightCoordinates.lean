/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.TileSubodometerLiteralDecompositionPiece
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4261T1RightCoordinates]

/-!
# P4261T1RightCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightCoordinateGeometry

private theorem hcurv₀ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), (BandOrderedGeneralLayoutCertificate q cfg C₀ T₀) →
            (1 < C₀.1.1.1) ) := by
  classical
  intro q cfg C₀ T₀ cert
  have hh := cfg.childLarge
  rw [cert.child_eq] at hh
  omega

private theorem hvector :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (q'' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i'' : Fin (3 : ℕ)), ∀
            (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3 : ℕ) → Bool →
            PartialOdometer), (q'' i''.succ = C.1.1) → ((T.cells = (S' i'' s).cells) →
            (((↑h.domain : Set GaussianInt) = (↑(hs' i'' s).domain : Set GaussianInt)) → ((∀ x ∈
            h.domain, h.value x = (hs' i'' s).value x) → (∀ (r : Fin (3 : ℕ)), (∀ (j : Fin (3 :
            ℕ)), q'' j.succ = q (j + r).succ) → (
        let j : Fin 3 := i'' + r
        (q'' i''.succ = q j.succ) → (BandVectors.1 (q'' ((i'' + 2).succ)) (q'' ((i'' + 1).succ))
            = BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ)))))))) ) := by
  classical
  intro q C T h q'' i'' s S' hs' hq''i hselectedCells hselectedDomain hselectedValue r hrotate j
      hparent
  rw [hrotate (i'' + 2), hrotate (i'' + 1)]; dsimp [j]; fin_cases r <;> fin_cases i'' <;> rfl

private theorem hslopeVector :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (q'' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i'' : Fin (3 : ℕ)), ∀
            (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3 : ℕ) → Bool →
            PartialOdometer), (q'' i''.succ = C.1.1) → ((T.cells = (S' i'' s).cells) →
            (((↑h.domain : Set GaussianInt) = (↑(hs' i'' s).domain : Set GaussianInt)) → ((∀ x ∈
            h.domain, h.value x = (hs' i'' s).value x) → (∀ (r : Fin (3 : ℕ)), (∀ (j : Fin (3 :
            ℕ)), q'' j.succ = q (j + r).succ) → (
        let j : Fin 3 := i'' + r
        (q'' i''.succ = q j.succ) → ((BandVectors.1 (q'' ((i'' + 2).succ)) (q'' ((i'' + 1).succ))
            = BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ))) → (BandVectors.2 (q'' ((i'' +
            2).succ)) (q'' ((i'' + 1).succ)) = BandVectors.2 (q ((j + 2).succ)) (q ((j +
            1).succ))))))))) ) := by
  classical
  intro q C T h q'' i'' s S' hs' hq''i hselectedCells hselectedDomain hselectedValue r hrotate j
      hparent hvector
  rw [hrotate (i'' + 2), hrotate (i'' + 1)]; dsimp [j]; fin_cases r <;> fin_cases i'' <;> rfl

private theorem hsCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (N : ProtoTile), ∀ (q'' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileCentroid (S' j t) - TileCentroid
            N = (if t = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q'' (j + (2 : Fin (3 : ℕ))).succ) (q'' (j + (1 : Fin (3 : ℕ))).succ))
            - (-(GaussianRealPoint (BandVectors.1 (q'' (j + (2 : Fin (3 : ℕ))).succ) (q'' (j + (1
            : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q'' (j + (2 : Fin (3 :
            ℕ))).succ) (q'' (j + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (R : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (R i s) - TileCentroid N
            = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (BandVectors.1 (q'' ((i'' + 2).succ)) (q'' ((i'' + 1).succ)) = BandVectors.1 (q ((j +
            2).succ)) (q ((j + 1).succ))) → (TileCentroid (S' i'' s) = TileCentroid (R j s)))) )
            := by
  classical
  intro q N q'' i'' s S' hcent' R hrootCent r j hvector
  calc
    TileCentroid (S' i'' s) =
        (TileCentroid (S' i'' s) - TileCentroid N) + TileCentroid N := by abel
    _ = (TileCentroid (R j s) - TileCentroid N) + TileCentroid N := by
      rw [hcent' i'' s, hrootCent j s, hvector]
    _ = TileCentroid (R j s) := by abel

private theorem hbandSelected :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (q'' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i'' :
            Fin (3 : ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3
            : ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileOdometer (q''
            j.succ) (S' j t) (hs' j t)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (q'' i''.succ = q j.succ) → (BandPrototile (q j.succ) (S' i'' s))) ) := by
  classical
  intro q q'' i'' s S' hs' hchild' r j hparent
  rw [← hparent]
  exact TileOdometerBandPrototile _ _ _ (hchild' i'' s)

private theorem hgeom :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), (q' (0 : Fin (4 : ℕ)) =
            C₀.1.1) → ((TileCentroid T₀ - TileCentroid N = (if e' = true then (1 : ℝ) else (-1 :
            ℝ)) • GaussianRealPoint (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i'.succ))) → ((p0.1
            - pN.1 = (if e' = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q' (0 : Fin (4
            : ℕ))) (q' i'.succ)).re : ℝ)) → ((p0.2 - pN.2 = (if e' = true then (1 : ℝ) else (-1 :
            ℝ)) * (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q' i'.succ)).im : ℝ)) → (∀ (ra : Fin
            (3 : ℕ)),
        let k : Fin 3 := i' + ra
        (q' i'.succ = q k.succ) → (
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (
        let V := BandVectors.1;
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let U := V (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let W := V (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); V (q (1 : Fin (4 : ℕ))) (q (3 :
            Fin (4 : ℕ))) = -U - W ∧ V (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = I * U ∧ V (q
            (3 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = I * (U + W) ∧ V (q (2 : Fin (4 : ℕ))) (q
            (3 : Fin (4 : ℕ))) = I * W ∧ V (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = U - I *
            (U + W) ∧ V (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = W + I * U ∧ V (q (0 : Fin
            (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -U - W + I * W ∧ V (cfg.firstPredecessor (2 : Fin
            (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) + V (cfg.firstPredecessor (0 : Fin
            (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ))) = ((1 : GaussianInt) + I) * U ∧ V
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) + V
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) =
            (I - (1 : GaussianInt)) * (U + W) ∧ V (cfg.secondPredecessor (1 : Fin (4 : ℕ)))
            (cfg.secondPredecessor (0 : Fin (4 : ℕ))) + V (cfg.secondPredecessor (0 : Fin (4 :
            ℕ))) (cfg.secondPredecessor (1 : Fin (4 : ℕ))) = ((1 : GaussianInt) + I) * W) →
            (GaussianRealPoint ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) = -((if
            e' = true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.1 (q' 0) (q'
            i'.succ))))))))) ) := by
  classical
  intro q cfg C₀ T₀ cert N pN p0 q' i' e' hq'0 hcentAdj hslopeAdj1 hslopeAdj2 ra k hAdjChild μ m
      n hforms
  have hchild : q' i'.succ = q k.succ := hAdjChild
  rw [cert.period_u, cert.period_v, hq'0, cert.child_eq, hchild]
  have h01 := hforms.2.2.2.2.1
  have h02 := hforms.2.2.2.2.2.1
  have h03 := hforms.2.2.2.2.2.2.1
  dsimp only at hforms h01 h02 h03
  have hsum : BandVectors.1 (q 0) (q 3) =
      -BandVectors.1 (q 0) (q 1) - BandVectors.1 (q 0) (q 2) := by
    rw [h01, h02, h03]
    ring
  rw [cert.child_eq] at hsum
  have hsumPoint := congrArg GaussianRealPoint hsum
  simp [GaussianRealPoint] at hsumPoint
  have hkvals : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkvals with hk | hk | hk
  · have : k = 0 := Fin.ext hk
    cases e' <;> simp [m, n, μ, GaussianRealPoint, this]
  · have : k = 1 := Fin.ext hk
    cases e' <;> simp [m, n, μ, GaussianRealPoint, this]
  · have : k = 2 := Fin.ext hk
    cases e' <;> simp [m, n, μ, GaussianRealPoint, this] <;>
      constructor <;> linarith [hsumPoint.1, hsumPoint.2]

private theorem hNcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin (3 :
            ℕ)), ∀ (e' : Bool), (q' (0 : Fin (4 : ℕ)) = C₀.1.1) → ((TileCentroid T₀ -
            TileCentroid N = (if e' = true then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint
            (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i'.succ))) → (∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) = -((if e' =
            true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.1 (q' 0) (q' i'.succ))))
            → (TileCentroid N - TileCentroid T₀ = GaussianRealPoint ((m : GaussianInt) * cert.u +
            (n : GaussianInt) * cert.v)))) ) := by
  classical
  intro q cfg C₀ T₀ cert N q' i' e' hq'0 hcentAdj ra k μ m n hgeom
  have := hcentAdj
  rw [hq'0] at this
  rw [hq'0] at hgeom
  calc
    TileCentroid N - TileCentroid T₀ = -(TileCentroid T₀ - TileCentroid N) := by abel
    _ = _ := by rw [this, hgeom]

private theorem hPshiftCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀
            (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        TileCentroid Pshift = TileCentroid (cert.P j s) + GaussianRealPoint shift ) := by
  classical
  intro q cfg C₀ T₀ cert i' e' i'' s r j ra k μ m n shift Pshift
  have hc := (TileTranslationFormulas (cert.P j s) shift).2.2.2.2.1
  dsimp [Pshift, GaussianRealPoint]
  exact hc

private theorem hlayoutCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s
            : Bool), TileCentroid (R i s) - TileCentroid N = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (TileCentroid N - TileCentroid T₀ = GaussianRealPoint ((m : GaussianInt) * cert.u + (n :
            GaussianInt) * cert.v)) → ((BandSubtileOccurrence q T₀ j s (cert.P j s)) → (
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        (TileCentroid Pshift = TileCentroid (cert.P j s) + GaussianRealPoint shift) →
            (TileCentroid (R j s) = TileCentroid Pshift)))) ) := by
  classical
  intro q cfg C₀ T₀ cert N i' e' i'' s R hrootCent r j ra k μ m n hNcent hlayoutOcc shift Pshift
      hPshiftCent
  calc
    TileCentroid (R j s) =
        (TileCentroid (R j s) - TileCentroid T₀) + TileCentroid T₀ := by abel
    _ = (TileCentroid (cert.P j s) - TileCentroid T₀ + GaussianRealPoint shift) + TileCentroid
        T₀ := by
      have heq : TileCentroid (R j s) - TileCentroid T₀ =
          TileCentroid (cert.P j s) - TileCentroid T₀ + GaussianRealPoint shift := by
        calc
          TileCentroid (R j s) - TileCentroid T₀ =
              (TileCentroid (R j s) - TileCentroid N) +
                (TileCentroid N - TileCentroid T₀) := by abel
          _ = (TileCentroid (cert.P j s) - TileCentroid T₀ + GaussianRealPoint shift) := by
            rw [hrootCent j s, hNcent, hlayoutOcc.2.2]
      rw [heq]
    _ = TileCentroid Pshift := by rw [hPshiftCent]; abel

private theorem hparentNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (cert.P j s).cells.Nonempty ) := by
  classical
  intro q cfg C₀ T₀ cert i'' s r j
  rcases cert.parent_lattice j s with ⟨e⟩
  have hball : (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by simp
  have hreal : (e ⟨(0 : ℝ × ℝ), hball⟩ : ℝ × ℝ) ∈
      TileRealization (cert.P j s) := (e ⟨0, hball⟩).property
  simp only [TileRealization, Set.mem_iUnion] at hreal
  rcases hreal with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

private theorem hselectedNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), (T.cells = (S' i''
            s).cells) → (∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ((S' i'' s).cells = (R j s).cells) → (∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        ((R j s).cells = Pshift.cells) → (((cert.P j s).cells.Nonempty) → (T.cells.Nonempty)))) )
            := by
  classical
  intro q cfg C₀ T₀ cert T i' e' i'' s S' hselectedCells R r j hselectedCellsFresh ra k μ m n
      shift Pshift hlayoutCells hparentNonempty
  rw [hselectedCells, hselectedCellsFresh, hlayoutCells]
  have hnonempty : Pshift.cells.Nonempty := by
    by_contra he
    have hempty : Pshift.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hsource : (cert.P j s).cells = ∅ :=
      (TileTranslationFormulas (cert.P j s) shift).2.2.1.mp hempty
    rcases hparentNonempty with ⟨x, hx⟩
    rw [hsource] at hx
    simp at hx
  exact hnonempty

private theorem hcellsT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), (T.cells = (S' i''
            s).cells) → (∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ((S' i'' s).cells = (R j s).cells) → (∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        ((R j s).cells = Pshift.cells) → (T.cells = Pshift.cells))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' e' i'' s S' hselectedCells R r j hselectedCellsFresh ra k μ m n
      shift Pshift hlayoutCells
  calc T.cells = (S' i'' s).cells := hselectedCells
    _ = (R j s).cells := hselectedCellsFresh
    _ = Pshift.cells := hlayoutCells

private theorem hfootT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        ((cert.P j s).cells.Nonempty) → ((T.cells.Nonempty) → ((T.cells = Pshift.cells) →
            (FootprintVertices T = FootprintVertices Pshift))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' e' i'' s r j ra k μ m n shift Pshift hparentNonempty
      hselectedNonempty hcellsT
  have hshiftNonempty : Pshift.cells.Nonempty := by
    by_contra he
    have hempty : Pshift.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hsource : (cert.P j s).cells = ∅ :=
      (TileTranslationFormulas (cert.P j s) shift).2.2.1.mp hempty
    rcases hparentNonempty with ⟨x, hx⟩
    rw [hsource] at hx
    simp at hx
  simp only [FootprintVertices, ite_eq_left hselectedNonempty, ite_eq_left hshiftNonempty]
  rw [hcellsT]

private theorem hchildPositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → ((BandCircle) →
            (∀ (i'' : Fin (3 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        0 < (q j.succ).1)) ) := by
  classical
  intro q cfg C₀ i'' r j
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 j
  have hne := cfg.noLine j.succ
  omega

private theorem hdomainFresh :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (R : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (R i s) (rH i s)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (0 < (q j.succ).1) → (((rH j s).domain : Set GaussianInt) = FootprintVertices (R j s))) )
            := by
  classical
  intro q i'' s R rH hrootChildren r j hchildPositive
  exact PositiveCurvatureTileOdometerDomain (q j.succ) (R j s) (rH j s)
      hchildPositive (hrootChildren j s)

private theorem hdomainSelected :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (q'' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i'' :
            Fin (3 : ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3
            : ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileOdometer (q''
            j.succ) (S' j t) (hs' j t)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (q'' i''.succ = q j.succ) → ((0 < (q j.succ).1) → (((hs' i'' s).domain : Set GaussianInt)
            = FootprintVertices (S' i'' s)))) ) := by
  classical
  intro q q'' i'' s S' hs' hchild' r j hparent hchildPositive
  exact PositiveCurvatureTileOdometerDomain (q j.succ) (S' i'' s) (hs' i'' s)
      hchildPositive (by rw [← hparent]; exact hchild' i'' s)

private theorem hdomainSelFresh :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (hs' : Fin (3 : ℕ) → Bool → PartialOdometer), (T.cells = (S' i''
            s).cells) → (∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (rH : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ((S' i'' s).cells = (R j s).cells) → ((T.cells.Nonempty) → ((((rH j s).domain : Set
            GaussianInt) = FootprintVertices (R j s)) → ((((hs' i'' s).domain : Set GaussianInt)
            = FootprintVertices (S' i'' s)) → (((hs' i'' s).domain : Set GaussianInt) = (rH j
            s).domain))))) ) := by
  classical
  intro T i'' s S' hs' hselectedCells R rH r j hselectedCellsFresh hselectedNonempty hdomainFresh
      hdomainSelected
  have hneSelected : (S' i'' s).cells.Nonempty := by rw [← hselectedCells]; exact
      hselectedNonempty
  have hneFresh : (R j s).cells.Nonempty := by rw [← hselectedCellsFresh]; exact hneSelected
  rw [hdomainSelected, hdomainFresh]
  simp only [FootprintVertices, ite_eq_left hneSelected, ite_eq_left hneFresh]
  rw [hselectedCellsFresh]

private theorem hdomainSuppliedFresh :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (hs' : Fin (3 : ℕ) → Bool
            → PartialOdometer), ((↑h.domain : Set GaussianInt) = (↑(hs' i'' s).domain : Set
            GaussianInt)) → (∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (((hs' i'' s).domain : Set GaussianInt) = (rH j s).domain) → ((h.domain : Set
            GaussianInt) = (rH j s).domain)) ) := by
  classical
  intro h i'' s hs' hselectedDomain rH r j hdomainSelFresh
  calc (h.domain : Set GaussianInt) = (hs' i'' s).domain := hselectedDomain
    _ = (rH j s).domain := hdomainSelFresh

private theorem hvalueSuppliedFresh :
    (by
      classical
      exact
        ∀ (hN : PartialOdometer), ∀ (h : PartialOdometer), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀
            (hs' : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), ∀ x
            ∈ (hs' j t).domain, hN.value x = (hs' j t).value x) → (((↑h.domain : Set GaussianInt)
            = (↑(hs' i'' s).domain : Set GaussianInt)) → ((∀ x ∈ h.domain, h.value x = (hs' i''
            s).value x) → (∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), ∀ x ∈ (rH i s).domain, hN.value x = (rH i s).value x) → (∀ (r : Fin (3 :
            ℕ)),
        let j : Fin 3 := i'' + r
        ((h.domain : Set GaussianInt) = (rH j s).domain) → (∀ x, h.value x = (rH j s).value
            x))))) ) := by
  classical
  intro hN h i'' s hs' hvalue' hselectedDomain hselectedValue rH hrootValue r j
      hdomainSuppliedFresh x
  by_cases hx : x ∈ h.domain
  · have hx' : x ∈ (hs' i'' s).domain := by
      have hfin : h.domain = (hs' i'' s).domain := Finset.coe_injective hselectedDomain
      rw [hfin] at hx
      exact hx
    have hv₁ := hselectedValue x hx
    have hv₂ := hvalue' i'' s x hx'
    have hxFresh : x ∈ (rH j s).domain := by
      have hfin : h.domain = (rH j s).domain := Finset.coe_injective hdomainSuppliedFresh
      rw [hfin] at hx
      exact hx
    exact hv₁.trans (hv₂.symm.trans (hrootValue j s x hxFresh))
  · have hxFresh : x ∉ (rH j s).domain := by
      intro hxF
      exact hx ((Set.ext_iff.mp hdomainSuppliedFresh x).mpr hxF)
    rw [h.value_outside x hx, (rH j s).value_outside x hxFresh]

private theorem hfunEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (N : ProtoTile), ∀ (hN : PartialOdometer), ∀ (C : BandCircle), ∀
            (T : ProtoTile), ∀ (h : PartialOdometer), (TileSubodometer C₀.1.1 C.1.1 N T hN h) →
            (∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (hs' : Fin (3 : ℕ) → Bool → PartialOdometer),
            ((↑h.domain : Set GaussianInt) = (↑(hs' i'' s).domain : Set GaussianInt)) → ((∀ x ∈
            h.domain, h.value x = (hs' i'' s).value x) → (∀ (rH : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ((h.domain : Set GaussianInt) = FootprintVertices T) → (((h.domain : Set GaussianInt) =
            (rH j s).domain) → ((∀ x, h.value x = (rH j s).value x) → (h = rH j s)))))) ) := by
  classical
  intro C₀ N hN C T h hsub i'' s hs' hselectedDomain hselectedValue rH r j hdomainT
      hdomainSuppliedFresh hvalueSuppliedFresh
  cases h with
  | mk hd hv hout =>
    have hdomEq : hd = (rH j s).domain := Finset.coe_injective hdomainSuppliedFresh
    have hvalEq : hv = (rH j s).value := funext hvalueSuppliedFresh
    cases hdomEq
    cases hvalEq
    rfl

private theorem hsumA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (BandVectors.2
            (q 0) (q 3) = -BandVectors.2 (q 0) (q 1) - BandVectors.2 (q 0) (q 2)) ) := by
  classical
  intro q cfg
  have laws := VectorRecursionLaws q cfg.proper.1
  have laws2 := VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.proper.1)
  have laws3 := VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
  have ha2 : BandVectors.2 (q 2) (q 0) =
      BandVectors.2 (q 2) (q 1) +
        ({ re := 0, im := 1 } : GaussianInt) * BandVectors.2 (q 3) (q 2) := by
    simpa using laws2.2.2.2.1
  have ha3 : BandVectors.2 (q 3) (q 0) =
      BandVectors.2 (q 3) (q 2) +
        ({ re := 0, im := 1 } : GaussianInt) * BandVectors.2 (q 1) (q 3) := by
    simpa using laws3.2.2.2.1
  have f1 := (laws.2.2.2.2 cfg.proper 0).2
  have f2 := (laws.2.2.2.2 cfg.proper 1).2
  have f3 := (laws.2.2.2.2 cfg.proper 2).2
  change BandVectors.2 (q 0) (q 1) = _ at f1
  change BandVectors.2 (q 0) (q 2) = _ at f2
  change BandVectors.2 (q 0) (q 3) = _ at f3
  have hsum := laws.2.1
  have h13 : BandVectors.2 (q 1) (q 3) =
      -BandVectors.2 (q 2) (q 1) - BandVectors.2 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
          BandVectors.2 (q 2) (q 1) := by ring
      _ = 0 := hsum
  rw [f1, f2, f3]
  change -({ re := 0, im := 1 } : GaussianInt) * BandVectors.2 (q 3) (q 0) =
    -(-({ re := 0, im := 1 } : GaussianInt) * BandVectors.2 (q 1) (q 0)) -
      -({ re := 0, im := 1 } : GaussianInt) * BandVectors.2 (q 2) (q 0)
  rw [laws.2.2.2.1, ha2, ha3, h13]
  ring

private theorem hsumARe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).re =
            -((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))))).re - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).re ∧ ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).im =
            -((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))))).im - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).im) → ((GaussianInt.toComplex
            (BandVectors.2 (q 0) (q 3))).re = -(GaussianInt.toComplex (BandVectors.2 (q 0) (q
            1))).re - (GaussianInt.toComplex (BandVectors.2 (q 0) (q 2))).re) ) := by
  classical
  intro q hsumAPoint
  exact hsumAPoint.1

private theorem hsumAIm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).re =
            -((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))))).re - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).re ∧ ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))).im =
            -((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))))).im - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))).im) → ((GaussianInt.toComplex
            (BandVectors.2 (q 0) (q 3))).im = -(GaussianInt.toComplex (BandVectors.2 (q 0) (q
            1))).im - (GaussianInt.toComplex (BandVectors.2 (q 0) (q 2))).im) ) := by
  classical
  intro q hsumAPoint
  exact hsumAPoint.2

private theorem hSlopePeriod :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (T : ProtoTile), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (q' :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), (q' (0 : Fin
            (4 : ℕ)) = C₀.1.1) → ((TileCentroid T₀ - TileCentroid N = (if e' = true then (1 : ℝ)
            else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q'
            i'.succ))) → ((p0.1 - pN.1 = (if e' = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q' i'.succ)).re : ℝ)) → ((p0.2 - pN.2 = (if
            e' = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q'
            i'.succ)).im : ℝ)) → (∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (R : Fin (3 : ℕ) → Bool
            → ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        (q' i'.succ = q k.succ) → (
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) = -((if e' =
            true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.1 (q' 0) (q' i'.succ))))
            → ((TileCentroid N - TileCentroid T₀ = GaussianRealPoint ((m : GaussianInt) * cert.u
            + (n : GaussianInt) * cert.v)) → (
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        (BandPrototile (q j.succ) Pshift) → ((TileCentroid Pshift = TileCentroid (cert.P j s) +
            GaussianRealPoint shift) → ((TileCentroid (R j s) = TileCentroid Pshift) → (((R j
            s).cells = Pshift.cells) → ((T.cells = Pshift.cells) → ((FootprintVertices T =
            FootprintVertices Pshift) → (((GaussianInt.toComplex (BandVectors.2 (q 0) (q 3))).re
            = -(GaussianInt.toComplex (BandVectors.2 (q 0) (q 1))).re - (GaussianInt.toComplex
            (BandVectors.2 (q 0) (q 2))).re) → (((GaussianInt.toComplex (BandVectors.2 (q 0) (q
            3))).im = -(GaussianInt.toComplex (BandVectors.2 (q 0) (q 1))).im -
            (GaussianInt.toComplex (BandVectors.2 (q 0) (q 2))).im) → (GaussianRealPoint ((m :
            GaussianInt) * BandVectors.2 (q 0) (q 1) + (n : GaussianInt) * BandVectors.2 (q 0) (q
            2)) = -((if e' = true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.2 (q' 0)
            (q' i'.succ)))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T₀ cert N T pN p0 q' i' e' hq'0 hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r j ra k
      hAdjChild μ m n hgeom hNcent shift Pshift hbandShift hPshiftCent hlayoutCent hlayoutCells
      hcellsT hfootT hsumARe hsumAIm
  rw [hq'0, cert.child_eq, hAdjChild]
  have hkvals : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkvals with hk | hk | hk
  · have hkEq : k = 0 := Fin.ext hk
    cases e' <;> simp [m, n, μ, GaussianRealPoint, hkEq]
  · have hkEq : k = 1 := Fin.ext hk
    cases e' <;> simp [m, n, μ, GaussianRealPoint, hkEq]
  · have hkEq : k = 2 := Fin.ext hk
    rw [cert.child_eq] at hsumARe hsumAIm
    cases e' <;> simp [m, n, μ, GaussianRealPoint, hkEq] <;>
      constructor <;> linarith [hsumARe, hsumAIm]

private theorem hAdjSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (T : ProtoTile), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (q' :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), (q' (0 : Fin
            (4 : ℕ)) = C₀.1.1) → ((TileCentroid T₀ - TileCentroid N = (if e' = true then (1 : ℝ)
            else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q'
            i'.succ))) → ((p0.1 - pN.1 = (if e' = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q' i'.succ)).re : ℝ)) → ((p0.2 - pN.2 = (if
            e' = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q'
            i'.succ)).im : ℝ)) → (∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (R : Fin (3 : ℕ) → Bool
            → ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) = -((if e' =
            true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.1 (q' 0) (q' i'.succ))))
            → ((TileCentroid N - TileCentroid T₀ = GaussianRealPoint ((m : GaussianInt) * cert.u
            + (n : GaussianInt) * cert.v)) → (
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        (BandPrototile (q j.succ) Pshift) → ((TileCentroid Pshift = TileCentroid (cert.P j s) +
            GaussianRealPoint shift) → ((TileCentroid (R j s) = TileCentroid Pshift) → (((R j
            s).cells = Pshift.cells) → ((T.cells = Pshift.cells) → ((FootprintVertices T =
            FootprintVertices Pshift) → ((GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q
            0) (q 1) + (n : GaussianInt) * BandVectors.2 (q 0) (q 2)) = -((if e' = true then (1 :
            ℝ) else -1) • GaussianRealPoint (BandVectors.2 (q' 0) (q' i'.succ)))) → ((pN.1 -
            p0.1, pN.2 - p0.2) = -((if e' = true then (1 : ℝ) else -1) • GaussianRealPoint
            (BandVectors.2 (q' 0) (q' i'.succ)))))))))))))))) ) := by
  classical
  intro q cfg C₀ T₀ cert N T pN p0 q' i' e' hq'0 hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r j ra k
      μ m n hgeom hNcent shift Pshift hbandShift hPshiftCent hlayoutCent hlayoutCells hcellsT
      hfootT hSlopePeriod
  rw [hq'0]
  apply Prod.ext
  · change pN.1 - p0.1 = _
    rw [hq'0] at hslopeAdj1
    cases e' <;> simp [GaussianRealPoint] at hslopeAdj1 ⊢ <;> linarith
  · change pN.2 - p0.2 = _
    rw [hq'0] at hslopeAdj2
    cases e' <;> simp [GaussianRealPoint] at hslopeAdj2 ⊢ <;> linarith

private theorem hSlopeShift :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q 1) + (n : GaussianInt) *
            BandVectors.2 (q 0) (q 2)) = -((if e' = true then (1 : ℝ) else -1) •
            GaussianRealPoint (BandVectors.2 (q' 0) (q' i'.succ)))) → (((pN.1 - p0.1, pN.2 -
            p0.2) = -((if e' = true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.2 (q'
            0) (q' i'.succ)))) → (GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q
            1) + (n : GaussianInt) * BandVectors.2 (q 0) (q 2)) = (pN.1 - p0.1, pN.2 - p0.2))) )
            := by
  classical
  intro q pN p0 q' i' e' ra k μ m n hSlopePeriod hAdjSlope
  rw [hSlopePeriod, hAdjSlope]

private theorem hslopeActual :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (rH : Fin (3 : ℕ) → Bool
            → PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        (h = rH j s) → (∀ (ps : ℝ × ℝ), (PartialOdometerSlope (rH j s) = some ps) →
            (PartialOdometerSlope h = some ps)) ) := by
  classical
  intro h i'' s rH r j hfunEq ps hps
  rw [hfunEq]
  exact hps

private theorem hslopeOffset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (pN : ℝ × ℝ), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀
            (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ps : ℝ × ℝ), (ps.1 - pN.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ))) → ((ps.2 - pN.2 = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q
            (j + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (ps - pN = (if s = true then (1 : ℝ) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) )
            := by
  classical
  intro q pN i'' s r j ps hpx hpy
  apply Prod.ext
  · change ps.1 - pN.1 = (if s = true then (1 : ℝ) else -1) *
      ((((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).re : ℝ) -
        ((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).im : ℝ)) / 2)
    rw [hpx]
    ring
  · change ps.2 - pN.2 = (if s = true then (1 : ℝ) else -1) *
      ((((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).im : ℝ) +
        ((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).re : ℝ)) / 2)
    rw [hpy]
    ring

private theorem hslopeFinal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (i' : Fin (3 : ℕ)),
            ∀ (e' : Bool), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q 1) + (n : GaussianInt) *
            BandVectors.2 (q 0) (q 2)) = (pN.1 - p0.1, pN.2 - p0.2)) → (∀ (ps : ℝ × ℝ), (ps - pN
            = (if s = true then (1 : ℝ) else -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j +
            2).succ)) (q ((j + 1).succ)))) → (ps - p0 = (if s = true then (1 : ℝ) else -1) •
            P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))) +
            GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q 1) + (n : GaussianInt)
            * BandVectors.2 (q 0) (q 2)))) ) := by
  classical
  intro q pN p0 i' e' i'' s r j ra k μ m n hSlopeShift ps hslopeOffset
  calc
    ps - p0 = (ps - pN) + (pN - p0) := by ext <;> simp
    _ = _ := by rw [hslopeOffset, hSlopeShift]; ext <;> rfl

private theorem labelExists :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ∀ (kk : Fin 3), ∀ (t : Bool), ∃ l : SixSubtileLabel, slot l = (kk, t) ∧
            SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨l, m, n⟩ = TileTranslation
            (cert.P kk t) shift ) := by
  classical
  intro q cfg C₀ T₀ cert i' e' ra k μ m n shift slot kk t
  fin_cases kk <;> cases t
  all_goals first
    | refine ⟨.A, rfl, ?_⟩
    | refine ⟨.B, rfl, ?_⟩
    | refine ⟨.C, rfl, ?_⟩
    | refine ⟨.D, rfl, ?_⟩
    | refine ⟨.E, rfl, ?_⟩
    | refine ⟨.F, rfl, ?_⟩
  all_goals simp [SubtileOccurrenceInterpretation, shift]

private theorem hshiftNonemptyAt458 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), ∀ (i'' : Fin (3 : ℕ)), ∀ (s : Bool), ∀
            (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        ((cert.P j s).cells.Nonempty) → (Pshift.cells.Nonempty) ) := by
  classical
  intro q cfg C₀ T₀ cert i' e' i'' s r j ra k μ m n shift Pshift hparentNonempty
  by_contra he
  have hempty : Pshift.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hsource : (cert.P j s).cells = ∅ :=
    (TileTranslationFormulas (cert.P j s) shift).2.2.1.mp hempty
  rcases hparentNonempty with ⟨x, hx⟩
  rw [hsource] at hx
  simp at hx

private theorem hmn :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (N : ProtoTile), ∀ (T : ProtoTile), ∀ (pN : ℝ × ℝ), ∀ (p0 : ℝ × ℝ), ∀ (q' :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (e' : Bool), (TileCentroid
            T₀ - TileCentroid N = (if e' = true then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint
            (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i'.succ))) → ((p0.1 - pN.1 = (if e' = true
            then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q'
            i'.succ)).re : ℝ)) → ((p0.2 - pN.2 = (if e' = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q' (0 : Fin (4 : ℕ))) (q' i'.succ)).im : ℝ)) → (∀ (i'' : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i'' + r
        ∀ (ra : Fin (3 : ℕ)),
        let k : Fin 3 := i' + ra
        let μ : Int := if e' = true then -1 else 1
        let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
        let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
        (GaussianRealPoint ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) = -((if e' =
            true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.1 (q' 0) (q' i'.succ))))
            → ((TileCentroid N - TileCentroid T₀ = GaussianRealPoint ((m : GaussianInt) * cert.u
            + (n : GaussianInt) * cert.v)) → (
        let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
        let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
        (BandPrototile (q j.succ) Pshift) → ((TileCentroid Pshift = TileCentroid (cert.P j s) +
            GaussianRealPoint shift) → ((TileCentroid (R j s) = TileCentroid Pshift) → (((R j
            s).cells = Pshift.cells) → ((T.cells = Pshift.cells) → ((FootprintVertices T =
            FootprintVertices Pshift) → ((GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q
            0) (q 1) + (n : GaussianInt) * BandVectors.2 (q 0) (q 2)) = -((if e' = true then (1 :
            ℝ) else -1) • GaussianRealPoint (BandVectors.2 (q' 0) (q' i'.succ)))) → (((pN.1 -
            p0.1, pN.2 - p0.2) = -((if e' = true then (1 : ℝ) else -1) • GaussianRealPoint
            (BandVectors.2 (q' 0) (q' i'.succ)))) → ((GaussianRealPoint ((m : GaussianInt) *
            BandVectors.2 (q 0) (q 1) + (n : GaussianInt) * BandVectors.2 (q 0) (q 2)) = (pN.1 -
            p0.1, pN.2 - p0.2)) → (∀ (ps : ℝ × ℝ), (ps - p0 = (if s = true then (1 : ℝ) else -1)
            • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))) +
            GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q 1) + (n : GaussianInt)
            * BandVectors.2 (q 0) (q 2))) → (
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        (∀ (kk : Fin 3), ∀ (t : Bool), ∃ l : SixSubtileLabel, slot l = (kk, t) ∧
            SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨l, m, n⟩ = TileTranslation
            (cert.P kk t) shift) → (∀ (l : SixSubtileLabel), (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v (⟨l, m, n⟩ : PeriodicSubtileIndex) = TileTranslation (cert.P j
            s) shift) → (
        let a : PeriodicSubtileIndex := ⟨l, m, n⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v a = Pshift) →
            ((Pshift.cells.Nonempty) → ((TileCentroid T = TileCentroid Pshift) → (m ≠ 0 ∨ n ≠
            0)))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T₀ cert N T pN p0 q' i' e' hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r j ra k μ m n
      hgeom hNcent shift Pshift hbandShift hPshiftCent hlayoutCent hlayoutCells hcellsT hfootT
      hSlopePeriod hAdjSlope hSlopeShift ps hslopeFinal slot labelExists l hocc a hoccTile
      hshiftNonempty hcentroidT
  have hkvals : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkvals with hk | hk | hk
  · have hh : k = 0 := Fin.ext hk
    left
    cases e' <;> norm_num [m, μ, hh]
  · have hh : k = 1 := Fin.ext hk
    right
    cases e' <;> norm_num [n, μ, hh]
  · have hh : k = 2 := Fin.ext hk
    left
    have hμ : μ ≠ 0 := by cases e' <;> simp [μ]
    have hm : m = -μ := by simp [m, hh]
    rw [hm]
    exact neg_ne_zero.mpr hμ

end RightCoordinateGeometry

theorem P4261T1RightCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (N : ProtoTile) (hN h₀ : PartialOdometer)
    (hadj : RightLatticeAdjacent C₀ N T₀ hN h₀)
    (C : BandCircle) (T : ProtoTile) (h : PartialOdometer)
    (hsub : TileSubodometer C₀.1.1 C.1.1 N T hN h) :
    ∃ a : PeriodicSubtileIndex, (a.first ≠ 0 ∨ a.second ≠ 0) ∧
      Nonempty (P4261T1PlacedOdometer cert h₀ C T h a) := by
-- BODY
  classical
  rcases hadj with ⟨hON, hO0, pN, p0, hpN, hp0, q', i', e', hq', hq'0,
    hcentAdj, hslopeAdj1, hslopeAdj2⟩
  have hroot : TileOdometer C₀.1.1 N hN := hON
  have hcurv₀ : 1 < C₀.1.1.1 := RightCoordinateGeometry.hcurv₀ q cfg C₀ T₀ cert
  obtain ⟨q'', i'', s, S', hs', hproper'', hq''0, hq''i,
    hband₀, hchild', hcells', hfoot', hcent', hdom', hvalue', hcompat', hslope',
    hselectedCells, hselectedDomain, hselectedValue⟩ :=
    TileSubodometerLiteralDecompositionPiece C₀ C N T hN h
      hcurv₀ hsub
  obtain ⟨R, rH, hbandRoot, hrootChildren, hrootCells, hrootFoot,
    hrootCent, hrootDomain, hrootValue, hrootCompat, hrootSlope⟩ :=
    TileOdometerReindexedDecomposition q cfg.proper N hN
      (by simpa [cert.child_eq] using hcurv₀) (by simpa [cert.child_eq] using hroot)
  obtain ⟨r, hrotate, _⟩ :=
    BandPredecessorNoCollision q q'' cfg.proper hproper''
      (by rw [cert.child_eq, hq''0])
  let j : Fin 3 := i'' + r
  have hparent : q'' i''.succ = q j.succ := by
    simpa [j] using hrotate i''
  have hvector := RightCoordinateGeometry.hvector q C T h q'' i'' s S' hs' hq''i hselectedCells
      hselectedDomain hselectedValue r hrotate hparent
  have hslopeVector := RightCoordinateGeometry.hslopeVector q C T h q'' i'' s S' hs' hq''i
      hselectedCells hselectedDomain hselectedValue r hrotate hparent hvector
  have hsCent := RightCoordinateGeometry.hsCent q N q'' i'' s S' hcent' R hrootCent r hvector
  have hbandSelected := RightCoordinateGeometry.hbandSelected q q'' i'' s S' hs' hchild' r hparent
  have hbandFresh : BandPrototile (q j.succ) (R j s) :=
    TileOdometerBandPrototile _ _ _ (hrootChildren j s)
  have hselectedCellsFresh : (S' i'' s).cells = (R j s).cells :=
    (BandPrototileCentroidUnique (q j.succ) _ _ hbandSelected hbandFresh hsCent).1
  obtain ⟨ra, hrotateA, _⟩ :=
    BandPredecessorNoCollision q q' cfg.proper hq'
      (by rw [cert.child_eq, hq'0])
  let k : Fin 3 := i' + ra
  have hAdjChild : q' i'.succ = q k.succ := by simpa [k] using hrotateA i'
  let μ : Int := if e' = true then -1 else 1
  let m : Int := if k = 0 then μ else if k = 2 then -μ else 0
  let n : Int := if k = 1 then μ else if k = 2 then -μ else 0
  have hforms := P3055T1ParentVectorNormalForms q cfg
  have hgeom := RightCoordinateGeometry.hgeom q cfg C₀ T₀ cert N pN p0 q' i' e' hq'0 hcentAdj
      hslopeAdj1 hslopeAdj2 ra hAdjChild hforms
  have hNcent := RightCoordinateGeometry.hNcent q cfg C₀ T₀ cert N q' i' e' hq'0 hcentAdj ra hgeom
  have hlayoutOcc := cert.outer_occurrence j s
  have hbandLayout : BandPrototile (q j.succ) (cert.P j s) := hlayoutOcc.1
  let shift : GaussianInt := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
  let Pshift : ProtoTile := TileTranslation (cert.P j s) shift
  have hbandShift : BandPrototile (q j.succ) Pshift :=
    BandPrototileTranslation (q j.succ) (cert.P j s) shift hbandLayout
  have hPshiftCent := RightCoordinateGeometry.hPshiftCent q cfg C₀ T₀ cert i' e' i'' s r ra
  have hlayoutCent := RightCoordinateGeometry.hlayoutCent q cfg C₀ T₀ cert N i' e' i'' s R
      hrootCent r ra hNcent hlayoutOcc hPshiftCent
  have hlayoutCells : (R j s).cells = Pshift.cells :=
    (BandPrototileCentroidUnique (q j.succ) _ _ hbandFresh hbandShift hlayoutCent).1
  have hparentNonempty := RightCoordinateGeometry.hparentNonempty q cfg C₀ T₀ cert i'' s r
  have hselectedNonempty := RightCoordinateGeometry.hselectedNonempty q cfg C₀ T₀ cert T i' e'
      i'' s S' hselectedCells R r hselectedCellsFresh ra hlayoutCells hparentNonempty
  have hcellsT : T.cells = Pshift.cells := RightCoordinateGeometry.hcellsT q cfg C₀ T₀ cert T i'
      e' i'' s S' hselectedCells R r hselectedCellsFresh ra hlayoutCells
  have hfootT : FootprintVertices T = FootprintVertices Pshift := RightCoordinateGeometry.hfootT
      q cfg C₀ T₀ cert T i' e' i'' s r ra hparentNonempty hselectedNonempty hcellsT
  have hchildPositive := RightCoordinateGeometry.hchildPositive q cfg C₀ i'' r
  have hdomainT : (h.domain : Set GaussianInt) = FootprintVertices T :=
    PositiveCurvatureTileOdometerDomain C.1.1 T h C.property hsub.2.1
  have hdomainFresh := RightCoordinateGeometry.hdomainFresh q i'' s R rH hrootChildren r
      hchildPositive
  have hdomainSelected := RightCoordinateGeometry.hdomainSelected q q'' i'' s S' hs' hchild' r
      hparent hchildPositive
  have hdomainSelFresh := RightCoordinateGeometry.hdomainSelFresh T i'' s S' hs' hselectedCells R
      rH r hselectedCellsFresh hselectedNonempty hdomainFresh hdomainSelected
  have hdomainSuppliedFresh := RightCoordinateGeometry.hdomainSuppliedFresh h i'' s hs'
      hselectedDomain rH r hdomainSelFresh
  have hvalueSuppliedFresh := RightCoordinateGeometry.hvalueSuppliedFresh hN h i'' s hs' hvalue'
      hselectedDomain hselectedValue rH hrootValue r hdomainSuppliedFresh
  have hfunEq := RightCoordinateGeometry.hfunEq C₀ N hN C T h hsub i'' s hs' hselectedDomain
      hselectedValue rH r hdomainT hdomainSuppliedFresh hvalueSuppliedFresh
  have hsumA := RightCoordinateGeometry.hsumA q cfg
  have hsumAPoint := congrArg GaussianRealPoint hsumA
  simp? [GaussianRealPoint] at hsumAPoint
  have hsumARe := RightCoordinateGeometry.hsumARe q hsumAPoint
  have hsumAIm := RightCoordinateGeometry.hsumAIm q hsumAPoint
  have hSlopePeriod := RightCoordinateGeometry.hSlopePeriod q cfg C₀ T₀ cert N T pN p0 q' i' e'
      hq'0 hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r ra hAdjChild hgeom hNcent hbandShift
      hPshiftCent hlayoutCent hlayoutCells hcellsT hfootT hsumARe hsumAIm
  have hAdjSlope := RightCoordinateGeometry.hAdjSlope q cfg C₀ T₀ cert N T pN p0 q' i' e' hq'0
      hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r ra hgeom hNcent hbandShift hPshiftCent hlayoutCent
      hlayoutCells hcellsT hfootT hSlopePeriod
  have hSlopeShift := RightCoordinateGeometry.hSlopeShift q pN p0 q' i' e' ra hSlopePeriod hAdjSlope
  rcases hrootSlope j s with hzero | ⟨p, ps, hp, hps, hpx, hpy⟩
  · have hpos := cfg.noLine j.succ
    omega
  have hpEq : p = pN := Option.some.inj (hp.symm.trans hpN)
  subst p
  have hslopeActual := RightCoordinateGeometry.hslopeActual h i'' s rH r hfunEq ps hps
  have hslopeOffset := RightCoordinateGeometry.hslopeOffset q pN i'' s r ps hpx hpy
  have hslopeFinal : ps - p0 =
      (if s = true then (1 : ℝ) else -1) •
        P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))) +
      GaussianRealPoint ((m : GaussianInt) * BandVectors.2 (q 0) (q 1) +
        (n : GaussianInt) * BandVectors.2 (q 0) (q 2)) := RightCoordinateGeometry.hslopeFinal q
            pN p0 i' e' i'' s r ra hSlopeShift ps hslopeOffset
  let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
    | .A => (0, true)
    | .B => (0, false)
    | .C => (1, true)
    | .D => (1, false)
    | .E => (2, true)
    | .F => (2, false)
  have labelExists : ∀ (kk : Fin 3) (t : Bool),
      ∃ l : SixSubtileLabel,
        slot l = (kk, t) ∧
          SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨l, m, n⟩ =
            TileTranslation (cert.P kk t) shift  := RightCoordinateGeometry.labelExists q cfg C₀
                T₀ cert i' e' ra
  obtain ⟨l, hl, hocc⟩ := labelExists j s
  let a : PeriodicSubtileIndex := ⟨l, m, n⟩
  have hoccTile : SubtileOccurrenceInterpretation cert.P cert.u cert.v a = Pshift := by
    simpa [a, Pshift] using hocc
  have hshiftNonempty : Pshift.cells.Nonempty := RightCoordinateGeometry.hshiftNonemptyAt458 q
      cfg C₀ T₀ cert i' e' i'' s r ra hparentNonempty
  have hcentroidT : TileCentroid T = TileCentroid Pshift := by
    simp [TileCentroid, hshiftNonempty, hcellsT]
  have hmn : m ≠ 0 ∨ n ≠ 0 := RightCoordinateGeometry.hmn q cfg C₀ T₀ cert N T pN p0 q' i' e'
      hcentAdj hslopeAdj1 hslopeAdj2 i'' s R r ra hgeom hNcent hbandShift hPshiftCent hlayoutCent
      hlayoutCells hcellsT hfootT hSlopePeriod hAdjSlope hSlopeShift ps hslopeFinal labelExists l
      hocc hoccTile hshiftNonempty hcentroidT
  refine ⟨a, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [a]
    rcases hmn with hm | hn
    · exact Or.inl hm
    · exact Or.inr hn
  · change C.1.1 = q (slot l).1.succ
    have hCeq : C.1.1 = q j.succ := hq''i.symm.trans hparent
    simpa only [hl] using hCeq
  · exact hsub.2.1
  · rw [hcellsT, hoccTile]
  · rw [hcentroidT, hoccTile]
  · rw [hdomainT, hfootT, hoccTile]
  · exact p0
  · exact ps
  · exact hp0
  · exact hslopeActual
  · change ps - p0 =
      (if (slot l).2 then (1 : ℝ) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q (((slot l).1 + 2).succ)) (q (((slot l).1 + 1).succ))) +
      GaussianRealPoint
        ((a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
          (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2))
    simp [a, hl, hslopeFinal]

end ApollonianSuperharmonic

end
