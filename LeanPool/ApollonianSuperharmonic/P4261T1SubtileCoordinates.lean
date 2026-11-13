/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandLayoutParentNonempty

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.P4261T1ExteriorIndices
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileCanonicalRows
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4261T1SubtileCoordinates]

/-!
# P4261T1SubtileCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SubtileCoordinateGeometry

private theorem hu :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀),
        let outgoing : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q 0) (q k.succ)
        cert.u = outgoing 0 ) := by
  classical
  intro q cfg C₀ T₀ cert outgoing
  rw [cert.period_u]
  rfl

private theorem hv :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀),
        let outgoing : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q 0) (q k.succ)
        cert.v = outgoing 1 ) := by
  classical
  intro q cfg C₀ T₀ cert outgoing
  rw [cert.period_v]
  rfl

private theorem hcentroidRows :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀),
        let edge : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q ((k + 2).succ)) (q ((k + 1).succ))
        ∀ k, ∀ e, TileCentroid (cert.P k e) - TileCentroid T₀ = (if e = true then (1 : ℝ) else
            -1) • ((1 / 2 : ℝ) • (GaussianRealPoint (edge k) - (-((GaussianRealPoint (edge
            k)).2), (GaussianRealPoint (edge k)).1))) ) := by
  classical
  intro q cfg C₀ T₀ cert edge k e
  simpa [edge] using (cert.outer_occurrence k e).2.2

private theorem rows :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        let edge : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q ((k + 2).succ)) (q ((k + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q k.succ) (q 0)
        let outgoing : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q 0) (q k.succ)
        (edge 0 + edge 1 + edge 2 = 0) → ((incoming 0 = edge 1 - (⟨0, 1⟩ : GaussianInt) * edge 2)
            → ((incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0) → ((incoming 2 = edge 0 -
            (⟨0, 1⟩ : GaussianInt) * edge 1) → ((∀ k, outgoing k = (⟨0, 1⟩ : GaussianInt) *
            incoming k) → ((cert.u = outgoing 0) → ((cert.v = outgoing 1) → ((∀ k, ∀ e,
            TileCentroid (cert.P k e) - TileCentroid T₀ = (if e = true then (1 : ℝ) else -1) •
            ((1 / 2 : ℝ) • (GaussianRealPoint (edge k) - (-((GaussianRealPoint (edge k)).2),
            (GaussianRealPoint (edge k)).1)))) → (
        let uIndex := if j = (0 : Fin (3 : ℕ)) then if s = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            s = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if j = (1 : Fin (3 : ℕ)) then if s = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex)
            else if s = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if s = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1 :
            ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let vIndex := if j = (0 : Fin (3 : ℕ)) then if s = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            s = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if j = (1 : Fin (3 : ℕ)) then if s = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            if s = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if s = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.A, (-1 :
            ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if s = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let U := SubtileOccurrenceInterpretation cert.P cert.u cert.v uIndex;
        let V := SubtileOccurrenceInterpretation cert.P cert.u cert.v vIndex; TileCentroid U -
            TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * (incoming j + outgoing j)) ∧ TileCentroid V - TileCentroid T₀ = (1 / 2 :
            ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s :
            ℕ) then incoming (j + (1 : Fin (3 : ℕ))) - outgoing (j + (1 : Fin (3 : ℕ))) else
            outgoing (j - (1 : Fin (3 : ℕ))) - incoming (j - (1 : Fin (3 : ℕ)))))))))))) ) := by
  classical
  intro q cfg C₀ T₀ cert i' s r j edge incoming outgoing hsuper hin0 hin1 hin2 hflip hu hv
      hcentroidRows
  exact BandOrderedGeneralSubtileCanonicalRows
    cert.P T₀ cert.u cert.v j s edge incoming outgoing hsuper hin0 hin1 hin2
    hflip hu hv hcentroidRows

private theorem tableFacts :
    (by
      classical
      exact
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ∀ (k : Fin 3), ∀ (t : Fin 4), ∀ (b : PeriodicSubtileIndex), (b = makeIndex k t) → (b ∈
            P4261T1ExteriorIndices ∧ (slot b.label).1 = k ∧ (slot b.label).2 = (if b.label = .A
            ∨ b.label = .C ∨ b.label = .E then true else false)) ) := by
  classical
  intro makeIndex slot k t b hb
  subst b
  fin_cases k <;> fin_cases t <;>
    simp [makeIndex, slot, P4261T1ExteriorIndices]

private theorem hslot :
    (by
      classical
      exact
        ∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        (a ∈ P4261T1ExteriorIndices ∧ (slot a.label).1 = j ∧ (slot a.label).2 = if a.label =
            SixSubtileLabel.A ∨ a.label = SixSubtileLabel.C ∨ a.label = SixSubtileLabel.E then
            true else false) → ((slot a.label).1 = j ∧ (slot a.label).2 = (if a.label = .A ∨
            a.label = .C ∨ a.label = .E then true else false)) ) := by
  classical
  intro i' s r j makeIndex a slot htable
  exact ⟨htable.2.1, htable.2.2⟩

private theorem hsuppliedCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin (3 :
            ℕ)), ∀ (s : Fin (4 : ℕ)), (q' (0 : Fin (4 : ℕ)) = C₀.1.1) → ((TileCentroid T -
            TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * (BandVectors.1 (q' i'.succ) (q' (0 : Fin (4 : ℕ))) + BandVectors.1 (q'
            (0 : Fin (4 : ℕ))) (q' i'.succ)))) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (q' i'.succ = q j.succ) → (
        let incoming : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q k.succ) (q 0)
        let outgoing : Fin 3 → GaussianInt := fun k =>
          BandVectors.1 (q 0) (q k.succ)
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        (TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) - TileCentroid T₀
            = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (incoming j +
            outgoing j))) → (TileCentroid T = TileCentroid (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a))))) ) := by
  classical
  intro q cfg C₀ T₀ cert T q' i' s hq₀ hcent r j hparent incoming outgoing makeIndex a hrowCentroid
  have hcent' : TileCentroid T - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (incoming j + outgoing j)) := by
    have h := hcent
    rw [hparent, hq₀, ← cert.child_eq] at h
    simpa [incoming, outgoing, j] using h
  calc
    TileCentroid T = (TileCentroid T - TileCentroid T₀) + TileCentroid T₀ := by abel
    _ = (TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) -
          TileCentroid T₀) + TileCentroid T₀ := by rw [hcent', hrowCentroid]
    _ = TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) := by abel

private abbrev hparentNonempty := ApollonianSuperharmonic.BandLayoutParentNonempty.cells

private theorem hbandOcc :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T₀ : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀),
                  ∀ (i' : Fin (3 : ℕ)),
                    ∀ (s : Fin (4 : ℕ)),
                      ∀ (r : Fin (3 : ℕ)),
                        let j : Fin 3 := i' + r;
                        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex :=
                          fun k t =>
                          if k = 0 then
                            if t = 0 then ⟨.A, 0, -1⟩
                            else
                              if t = 1 then ⟨.B, 1, 1⟩
                              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
                          else
                            if k = 1 then
                              if t = 0 then ⟨.C, 1, 1⟩
                              else
                                if t = 1 then ⟨.D, -1, 0⟩
                                else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
                            else
                              if t = 0 then ⟨.E, -1, 0⟩
                              else
                                if t = 1 then ⟨.F, 0, -1⟩
                                else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩;
                        let a : PeriodicSubtileIndex := makeIndex j s;
                        let slot : SixSubtileLabel → Fin 3 × Bool := fun l =>
                          match l with
                          | .A => (0, true)
                          | .B => (0, false)
                          | .C => (1, true)
                          | .D => (1, false)
                          | .E => (2, true)
                          | .F => (2, false);
                        (BandPrototile (q (slot a.label).1.succ)
                          (SubtileOccurrenceInterpretation cert.P cert.u cert.v a))) := by
  classical
  intro q cfg C₀ T₀ cert i' s r j makeIndex a slot
  rcases a with ⟨lab, m, n⟩
  cases lab <;> simp only [SubtileOccurrenceInterpretation, slot] <;>
    exact BandPrototileTranslation _ _ _ (cert.outer_occurrence _ _).1

private theorem hbandT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), (TileOdometer C.1.1 T h) → (∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), (q' i'.succ = C.1.1) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (q' i'.succ = q j.succ) → (BandPrototile (q j.succ) T))) ) := by
  classical
  intro q C T h hchild q' i' hqi r j hparent
  have heq : C.1.1 = q j.succ := hqi.symm.trans hparent
  rw [← heq]
  exact TileOdometerBandPrototile _ _ _ hchild

private theorem hcells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 :
            ℕ)),
        let j : Fin 3 := i' + r
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ((slot a.label).1 = j ∧ (slot a.label).2 = (if a.label = .A ∨ a.label = .C ∨ a.label = .E
            then true else false)) → ((TileCentroid T = TileCentroid
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)) → ((BandPrototile (q (slot
            a.label).1.succ) (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)) →
            ((BandPrototile (q j.succ) T) → (T.cells = (SubtileOccurrenceInterpretation cert.P
            cert.u cert.v a).cells)))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' s r j makeIndex a slot hslot hsuppliedCentroid hbandOcc hbandT
  exact (BandPrototileCentroidUnique (q j.succ) T _ hbandT
      (by simpa [hslot.1] using hbandOcc) hsuppliedCentroid).1

private theorem hoccNonempty :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C₀ : BandCircle),
              ∀ (T₀ : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀),
                  ∀ (i' : Fin (3 : ℕ)),
                    ∀ (s : Fin (4 : ℕ)),
                      ∀ (r : Fin (3 : ℕ)),
                        let j : Fin 3 := i' + r;
                        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex :=
                          fun k t =>
                          if k = 0 then
                            if t = 0 then ⟨.A, 0, -1⟩
                            else
                              if t = 1 then ⟨.B, 1, 1⟩
                              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
                          else
                            if k = 1 then
                              if t = 0 then ⟨.C, 1, 1⟩
                              else
                                if t = 1 then ⟨.D, -1, 0⟩
                                else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
                            else
                              if t = 0 then ⟨.E, -1, 0⟩
                              else
                                if t = 1 then ⟨.F, 0, -1⟩
                                else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩;
                        let a : PeriodicSubtileIndex := makeIndex j s;
                        ((∀ k, ∀ e, (cert.P k e).cells.Nonempty) →
                          ((SubtileOccurrenceInterpretation cert.P cert.u cert.v
                              a).cells.Nonempty))) := by
  classical
  intro q cfg C₀ T₀ cert i' s r j makeIndex a hparentNonempty
  rcases a with ⟨lab, m, n⟩
  cases lab <;>
    rcases hparentNonempty _ _ with ⟨x, hx⟩ <;>
    refine ⟨GaussianTranslation ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) x,
        ?_⟩ <;>
    simpa [SubtileOccurrenceInterpretation, TileTranslation, Finset.mem_image] using
      (show ∃ y ∈ (cert.P _ _).cells,
          GaussianTranslation ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) y =
            GaussianTranslation ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) x from
        ⟨x, hx, rfl⟩)

private theorem hfoot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 :
            ℕ)),
        let j : Fin 3 := i' + r
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        (T.cells = (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells) →
            (((SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells.Nonempty) →
            ((T.cells.Nonempty) → (FootprintVertices T = FootprintVertices
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' s r j makeIndex a hcells hoccNonempty hTNonempty
  simp only [FootprintVertices, ite_eq_left hTNonempty, ite_eq_left hoccNonempty]
  rw [hcells]

private theorem hdomain :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), (TileOdometer
            C.1.1 T h) → (∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        (FootprintVertices T = FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v a)) → ((h.domain : Set GaussianInt) = FootprintVertices
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a))) ) := by
  classical
  intro q cfg C₀ T₀ cert C T h hchild i' s r j makeIndex a hfoot
  calc
    (h.domain : Set GaussianInt) = FootprintVertices T :=
      PositiveCurvatureTileOdometerDomain C.1.1 T h C.property hchild
    _ = FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) := hfoot

private theorem hcircle :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (C : BandCircle), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), (q' i'.succ = C.1.1) →
            (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (q' i'.succ = q j.succ) → (
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let a : PeriodicSubtileIndex := makeIndex j s
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ((slot a.label).1 = j ∧ (slot a.label).2 = (if a.label = .A ∨ a.label = .C ∨ a.label = .E
            then true else false)) → (C.1.1 = q (slot a.label).1.succ))) ) := by
  classical
  intro q C q' i' s hqi r j hparent makeIndex a slot hslot
  rw [hslot.1]
  exact hqi.symm.trans hparent

private theorem hAedgeAux :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (k : Fin 3), BandVectors.2 (q ((k + 2).succ))
            (q ((k + 1).succ)) = (![B, -A - B, A] : Fin 3 → GaussianInt) k) ) := by
  classical
  intro q A B hA13 k
  fin_cases k <;> simp [A, B, hA13]

private theorem hAroot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (q 0) (q 1) = A + I * (A + B)) → ((BandVectors.2 (q 0) (q 2) = B - I * A)
            → ((BandVectors.2 (q 0) (q 3) = -A - B - I * B) → (∀ k : Fin 3, BandVectors.2 (q 0)
            (q k.succ) = (![A + I * (A + B), B - I * A, -A - B - I * B] : Fin 3 → GaussianInt)
            k))) ) := by
  classical
  intro q I A B hA01 hA02 hA03 k
  fin_cases k <;> simp [hA01, hA02, hA03]

private theorem hrowPointAux :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
          if k = 0 then
            if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
              else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
          else if k = 1 then
            if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
              else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
          else
            if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
              else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (q 0) (q 1) = A + I * (A + B)) → ((BandVectors.2 (q 0) (q 2) = B - I * A)
            → ((∀ (k : Fin 3), BandVectors.2 (q ((k + 2).succ)) (q ((k + 1).succ)) = (![B, -A -
            B, A] : Fin 3 → GaussianInt) k) → ((∀ k : Fin 3, BandVectors.2 (q 0) (q k.succ) =
            (![A + I * (A + B), B - I * A, -A - B - I * B] : Fin 3 → GaussianInt) k) → (∀ (k :
            Fin 3), ∀ (t : Fin 4), (1 / 2 : ℝ) • GaussianRealPoint ((-I) ^ t.val * (I *
            BandVectors.2 (q 0) (q k.succ) + BandVectors.2 (q 0) (q k.succ))) = (if (slot
            (makeIndex k t).label).2 then (1 : ℝ) else -1) • P4250T1SlopeOffset (BandVectors.2
            (q ((k + 2).succ)) (q ((k + 1).succ))) + GaussianRealPoint (((makeIndex k t).first :
            GaussianInt) * BandVectors.2 (q 0) (q 1) + ((makeIndex k t).second : GaussianInt) *
            BandVectors.2 (q 0) (q 2)))))) ) := by
  classical
  intro q makeIndex slot I A B hA01 hA02 hAedgeAux hAroot k t
  rw [hAroot k, hAedgeAux k, hA01, hA02]
  fin_cases k <;> fin_cases t <;>
    simp [makeIndex, slot, A, B, I, GaussianRealPoint, pow_succ,
      P4250T1SlopeOffset, -GaussianInt.intCast_re,
      -GaussianInt.intCast_im] <;> ring_nf <;> trivial

private theorem hslopePair :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ : ℝ × ℝ), ∀ (i' : Fin (3 : ℕ)),
            ∀ (s : Fin (4 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        let I : GaussianInt := ⟨0, 1⟩
        (pᵢ.1 - p₀.1 = (2 : ℝ)⁻¹ * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^
            (↑s : ℕ) * (I * BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) + BandVectors.2 (q (0
            : Fin (4 : ℕ))) (q j.succ)))).1) → ((pᵢ.2 - p₀.2 = (2 : ℝ)⁻¹ * (GaussianRealPoint
            ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (I * BandVectors.2 (q (0 : Fin (4
            : ℕ))) (q j.succ) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ)))).2) → (pᵢ - p₀ =
            (1 / 2 : ℝ) • GaussianRealPoint ((-I) ^ s.val * (I * BandVectors.2 (q 0) (q j.succ) +
            BandVectors.2 (q 0) (q j.succ))))) ) := by
  classical
  intro q p₀ pᵢ i' s r j I hs1 hs2
  apply Prod.ext
  · simpa only [Prod.fst_sub, Prod.smul_mk, GaussianRealPoint,
      smul_eq_mul, one_div] using hs1
  · simpa only [Prod.snd_sub, Prod.smul_mk, GaussianRealPoint,
      smul_eq_mul, one_div] using hs2

end SubtileCoordinateGeometry

theorem P4261T1SubtileCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer) (C : BandCircle) (T : ProtoTile) (h : PartialOdometer)
    (hadj : SubtileLatticeAdjacent C₀ C T₀ T h₀ h) :
    ∃ a : PeriodicSubtileIndex, a ∈ P4261T1ExteriorIndices ∧
      Nonempty (P4261T1PlacedOdometer cert h₀ C T h a) := by
-- BODY
  focus
    classical
    rcases hadj with ⟨_, hchild, p₀, pᵢ, hp₀, hpᵢ, q', i', s, hproper,
      hq₀, hqi, hcent, hslope₁, hslope₂⟩
    obtain ⟨r, hrotate, _⟩ :=
      BandPredecessorNoCollision q q' cfg.proper hproper (by
        rw [cert.child_eq, hq₀])
    let j : Fin 3 := i' + r
    have hparent : q' i'.succ = q j.succ := by
      simpa [j] using hrotate i'
    let edge : Fin 3 → GaussianInt := fun k =>
      BandVectors.1 (q ((k + 2).succ)) (q ((k + 1).succ))
    let incoming : Fin 3 → GaussianInt := fun k =>
      BandVectors.1 (q k.succ) (q 0)
    let outgoing : Fin 3 → GaussianInt := fun k =>
      BandVectors.1 (q 0) (q k.succ)
    have hvlaws := VectorRecursionLaws q cfg.proper.1
    have hvlaws₂ := VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.proper.1)
    have hvlaws₃ := VectorRecursionLaws _
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
    have hsuper : edge 0 + edge 1 + edge 2 = 0 := by
      dsimp [edge]
      linear_combination hvlaws.1
    have hin0 : incoming 0 = edge 1 - (⟨0, 1⟩ : GaussianInt) * edge 2 := by
      simpa [incoming, edge] using hvlaws.2.2.1
    have hin1 : incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0 := by
      simpa [incoming, edge] using hvlaws₂.2.2.1
    have hin2 : incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1 := by
      simpa [incoming, edge] using hvlaws₃.2.2.1
    have hflip (k : Fin 3) : outgoing k = (⟨0, 1⟩ : GaussianInt) * incoming k := by
      simpa [outgoing, incoming] using (hvlaws.2.2.2.2 cfg.proper k).1
    have hu := SubtileCoordinateGeometry.hu q cfg C₀ T₀ cert
    have hv := SubtileCoordinateGeometry.hv q cfg C₀ T₀ cert
    have hcentroidRows := SubtileCoordinateGeometry.hcentroidRows q cfg C₀ T₀ cert
    have rows := SubtileCoordinateGeometry.rows q cfg C₀ T₀ cert i' s r hsuper hin0 hin1 hin2
        hflip hu hv hcentroidRows
    let makeIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex := fun k t =>
      if k = 0 then
        if t = 0 then ⟨.A, 0, -1⟩ else if t = 1 then ⟨.B, 1, 1⟩
          else if t = 2 then ⟨.B, 0, 1⟩ else ⟨.A, -1, -1⟩
      else if k = 1 then
        if t = 0 then ⟨.C, 1, 1⟩ else if t = 1 then ⟨.D, -1, 0⟩
          else if t = 2 then ⟨.D, -1, -1⟩ else ⟨.C, 1, 0⟩
      else
        if t = 0 then ⟨.E, -1, 0⟩ else if t = 1 then ⟨.F, 0, -1⟩
          else if t = 2 then ⟨.F, 1, 0⟩ else ⟨.E, 0, 1⟩
    let a : PeriodicSubtileIndex := makeIndex j s
    let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
      | .A => (0, true)
      | .B => (0, false)
      | .C => (1, true)
      | .D => (1, false)
      | .E => (2, true)
      | .F => (2, false)
    have tableFacts := SubtileCoordinateGeometry.tableFacts
    have htable := tableFacts j s a rfl
    have ha := htable.1
    have hslot : (slot a.label).1 = j ∧ (slot a.label).2 =
        (if a.label = .A ∨ a.label = .C ∨ a.label = .E then true else false) :=
            SubtileCoordinateGeometry.hslot i' s r htable
    have hrowCentroid :
        TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) - TileCentroid T₀ =
          (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val * (incoming j + outgoing j)) := by
      simpa [a, j, incoming, outgoing] using rows.1
    have hsuppliedCentroid := SubtileCoordinateGeometry.hsuppliedCentroid q cfg C₀ T₀ cert T q'
        i' s hq₀ hcent r hparent hrowCentroid
    have hparentNonempty := SubtileCoordinateGeometry.hparentNonempty q cfg C₀ T₀ cert
    have hbandOcc := SubtileCoordinateGeometry.hbandOcc q cfg C₀ T₀ cert i' s r
    have hbandT := SubtileCoordinateGeometry.hbandT q C T h hchild q' i' hqi r hparent
    have hcells : T.cells = (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells :=
        SubtileCoordinateGeometry.hcells q cfg C₀ T₀ cert T i' s r hslot hsuppliedCentroid
        hbandOcc hbandT
    have hoccNonempty :
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells.Nonempty :=
            SubtileCoordinateGeometry.hoccNonempty q cfg C₀ T₀ cert i' s r hparentNonempty
    have hTNonempty : T.cells.Nonempty := by rw [hcells]; exact hoccNonempty
    have hfoot := SubtileCoordinateGeometry.hfoot q cfg C₀ T₀ cert T i' s r hcells hoccNonempty
        hTNonempty
    have hdomain := SubtileCoordinateGeometry.hdomain q cfg C₀ T₀ cert C T h hchild i' s r hfoot
    have hrootSlope : PartialOdometerSlope h₀ = some p₀ := hp₀
    have hfunctionSlope : PartialOdometerSlope h = some pᵢ := hpᵢ
    have hcircle := SubtileCoordinateGeometry.hcircle q C q' i' s hqi r hparent hslot
    let I : GaussianInt := ⟨0, 1⟩
    let A : GaussianInt := BandVectors.2 (q 2) (q 1)
    let B : GaussianInt := BandVectors.2 (q 3) (q 2)
    have hA13 : BandVectors.2 (q 1) (q 3) = -A - B := by
      dsimp [A, B]
      linear_combination hvlaws.2.1
    have hA01 : BandVectors.2 (q 0) (q 1) = A + I * (A + B) := by
      have hin := hvlaws.2.2.2.1
      have hf := (hvlaws.2.2.2.2 cfg.proper 0).2
      calc
        BandVectors.2 (q 0) (q 1) =
            -(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 1) (q 0) := hf
        _ = -(⟨0, 1⟩ : GaussianInt) *
            (BandVectors.2 (q 1) (q 3) + (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 2) (q 1)) :=
                by rw [hin]
        _ = A + I * (A + B) := by rw [hA13]; dsimp [I, A, B]; ext <;> simp <;> ring
    have hA02 : BandVectors.2 (q 0) (q 2) = B - I * A := by
      have hin := hvlaws₂.2.2.2.1
      have hf := (hvlaws.2.2.2.2 cfg.proper 1).2
      have hin' : BandVectors.2 (q 2) (q 0) = A + I * B := by
        simpa [A, B] using hin
      calc
        BandVectors.2 (q 0) (q 2) =
            -(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 2) (q 0) := hf
        _ = -(⟨0, 1⟩ : GaussianInt) * (A + I * B) := by rw [hin']
        _ = B - I * A := by dsimp [I]; ext <;> simp <;> ring
    have hA03 : BandVectors.2 (q 0) (q 3) = -A - B - I * B := by
      have hin := hvlaws₃.2.2.2.1
      have hf := (hvlaws.2.2.2.2 cfg.proper 2).2
      have hin' : BandVectors.2 (q 3) (q 0) = B + I * (-A - B) := by
        simpa [A, B, hA13, add_comm, add_left_comm, add_assoc] using hin
      calc
        BandVectors.2 (q 0) (q 3) =
            -(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 3) (q 0) := hf
        _ = -(⟨0, 1⟩ : GaussianInt) * (B + I * (-A - B)) := by rw [hin']
        _ = -A - B - I * B := by dsimp [I]; ext <;> simp <;> ring
    have hAedgeAux := SubtileCoordinateGeometry.hAedgeAux q hA13
    have hAroot := SubtileCoordinateGeometry.hAroot q hA01 hA02 hA03
    have hrowPointAux := SubtileCoordinateGeometry.hrowPointAux q hA01 hA02 hAedgeAux hAroot
    refine ⟨a, ha, ⟨?_⟩⟩
    refine ⟨hcircle, hchild, hcells, hsuppliedCentroid, hdomain, p₀, pᵢ,
      hrootSlope, hfunctionSlope, ?_⟩
    have hflipAffine : ∀ k : Fin 3,
        BandVectors.2 (q k.succ) (q 0) =
          I * BandVectors.2 (q 0) (q k.succ) := by
      intro k
      rw [(hvlaws.2.2.2.2 cfg.proper k).2]
      dsimp [I]
      ext <;> simp
    have hs1 := by
      simpa [hparent, hq₀, cert.child_eq.symm, hflipAffine j] using hslope₁
    have hs2 := by
      simpa [hparent, hq₀, cert.child_eq.symm, hflipAffine j] using hslope₂
    have hslopePair := SubtileCoordinateGeometry.hslopePair q p₀ pᵢ i' s r hs1 hs2
    have hrowPoint :
        (1 / 2 : ℝ) • GaussianRealPoint
          ((-I) ^ s.val * (I * BandVectors.2 (q 0) (q j.succ) +
            BandVectors.2 (q 0) (q j.succ))) =
          (if (slot a.label).2 then (1 : ℝ) else -1) •
            P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))) +
          GaussianRealPoint ((a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
            (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2)) := by
      simpa [a] using hrowPointAux j s
    change pᵢ - p₀ =
      (if (slot a.label).2 then (1 : ℝ) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q ((slot a.label).1 + 2).succ)
            (q ((slot a.label).1 + 1).succ)) +
      GaussianRealPoint
        ((a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
          (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2))
    rw [hslot.1]
    exact hslopePair.trans hrowPoint

end ApollonianSuperharmonic

end
