/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4418T3OuterCompanionAlignment
public import LeanPool.ApollonianSuperharmonic.P4387T1ParentSlopeNormalForms
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowAlignment
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileSubodometer

-- [TABLET NODE: P4418T3PresentedRowAdjacency]

/-!
# P4418T3PresentedRowAdjacency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PresentedRowAdjacencyGeometry

private theorem selected_cells :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (bundle.pieces bundle.selectedSlot bundle.selectedSign).cells = (occurrence
            placement.centralIndex).cells ) := by
  classical
  intro C D T N h k x bundle placement cert occurrence
  rw [placement.selected_central_index]
  exact placement.piece_layout_cells _ _

private theorem selected_centroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ((bundle.pieces bundle.selectedSlot bundle.selectedSign).cells = (occurrence
            placement.centralIndex).cells) → (TileCentroid (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) = TileCentroid (occurrence placement.centralIndex)) ) := by
  classical
  intro C D T N h k x bundle placement cert occurrence selected_cells
  apply (ProtoTileObservableExtensionality _ _ selected_cells _).2.2.2.2
  intro he
  rw [placement.selected_central_index]
  exact placement.piece_layout_empty_anchor _ _ he

private theorem translate_zero_centroid :
    (by
      classical
      exact
        ∀ (V : ProtoTile), TileCentroid (TileTranslation V 0) = TileCentroid V ) := by
  classical
  intro V
  rw [(TileTranslationFormulas _ _).2.2.2.2.1]
  simp []

private theorem central_centroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        let sign : SixSubtileLabel → Bool := fun l => match l with
          | .A | .C | .E => true
          | .B | .D | .F => false
        (∀ (V : ProtoTile), TileCentroid (TileTranslation V 0) = TileCentroid V) → (TileCentroid
            (occurrence placement.centralIndex) = TileCentroid (cert.P (slot
            placement.centralIndex.label) (sign placement.centralIndex.label))) ) := by
  classical
  intro C D T N h k x bundle placement cert occurrence slot sign translate_zero_centroid
  rcases placement.central_index with he | he | he | he | he | he
  all_goals
    rw [he]
    simp [occurrence, SubtileOccurrenceInterpretation, slot, sign,
      translate_zero_centroid]

private theorem positive_parent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedFixedCircle
            bundle.normalizedRoot bundle.normalizedFixed bundle.normalizedRootFunction
            bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces bundle.functions
            bundle.selectedSlot bundle.selectedSign bundle.routedDirection) → ((Fin 4) → (
        let q := bundle.normalizedPresentation
        ∀ (j : Fin 3), 0 < (q j.succ).1)) ) := by
  classical
  intro C D T N h k x bundle placement s q j
  let cfg := bundle.configuration
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 j
  have hne := cfg.noLine j.succ
  change 0 ≤ (q j.succ).1 at hn
  change (q j.succ).1 ≠ 0 at hne
  omega

private theorem area_of_band :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (V : ProtoTile), 0 < c.1 → BandPrototile c V → TileArea V =
            Int.toNat c.1 ) := by
  classical
  intro c V hc hV
  cases hV with
  | line w x hw => simp at hc
  | unit z x anchor => simp [TileArea]
  | @decompose t ht S V hS hcells hfoot hcentroid =>
      exact (BandTileSimultaneousInduction t ht V
        (BandPrototile.decompose ht hS hcells hfoot hcentroid)).2.1

private theorem occurrence_area :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (∀ (j : Fin 3), 0 < (q j.succ).1) → ((∀ (c : CircleCoordinates), ∀ (V : ProtoTile), 0 <
            c.1 → BandPrototile c V → TileArea V = Int.toNat c.1) → (∀ (a :
            PeriodicSubtileIndex), TileArea (occurrence a) = Int.toNat (q (slot
            a.label).succ).1)) ) := by
  classical
  intro C D T N h k x bundle placement q cert occurrence slot positive_parent area_of_band a
  cases a with
  | mk l m n =>
    cases l <;> simp only [occurrence, SubtileOccurrenceInterpretation, slot]
    all_goals
      rw [(TileDiskAreaCovariance _ _).2.2.2.1]
      exact area_of_band _ _ (positive_parent _) (cert.outer_occurrence _ _).1

private theorem selected_slot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), (Fin 4) → (
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        ((bundle.pieces bundle.selectedSlot bundle.selectedSign).cells = (occurrence
            placement.centralIndex).cells) → ((∀ (j : Fin 3), 0 < (q j.succ).1) → ((∀ (a :
            PeriodicSubtileIndex), TileArea (occurrence a) = Int.toNat (q (slot a.label).succ).1)
            → ((TileArea (bundle.pieces bundle.selectedSlot bundle.selectedSign) = Int.toNat (q
            bundle.selectedSlot.succ).1) → (bundle.selectedSlot = slot
            placement.centralIndex.label))))) ) := by
  classical
  intro C D T N h k x bundle placement s q cert occurrence slot selected_cells positive_parent
      occurrence_area selected_area
  let cfg := bundle.configuration
  have heq : Int.toNat (q bundle.selectedSlot.succ).1 =
      Int.toNat (q (slot placement.centralIndex.label).succ).1 := by
    rw [← selected_area, ← occurrence_area]
    exact congrArg Finset.card selected_cells
  have hp := positive_parent bundle.selectedSlot
  have hq := positive_parent (slot placement.centralIndex.label)
  have hc : (q bundle.selectedSlot.succ).1 =
      (q (slot placement.centralIndex.label).succ).1 := by omega
  have injective (j k : Fin 3) (he : (q j.succ).1 = (q k.succ).1) : j = k := by
    have h12 := cfg.order12
    change (q 2).1 < (q 1).1 at h12
    have h23 := cfg.secondProper.2 0
    change (cfg.secondPredecessor 1).1 < (cfg.secondPredecessor 0).1 at h23
    rw [cfg.secondParentOne, cfg.secondChild] at h23
    change (q 3).1 < (q 2).1 at h23
    have h13 := lt_trans h23 h12
    fin_cases j <;> fin_cases k
    all_goals first
      | rfl
      | exact False.elim ((ne_of_lt h12) he)
      | exact False.elim ((ne_of_lt h12) he.symm)
      | exact False.elim ((ne_of_lt h23) he)
      | exact False.elim ((ne_of_lt h23) he.symm)
      | exact False.elim ((ne_of_lt h13) he)
      | exact False.elim ((ne_of_lt h13) he.symm)
  exact injective _ _ hc

private theorem cyclic_nonzero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (∀ (j : Fin 3), BandVectors.1 (q ((j + 2).succ)) (q
            ((j + 1).succ)) ≠ 0) ) := by
  classical
  intro C D T N h k x bundle q positive_parent j
  let cfg := bundle.configuration
  fin_cases j
  · exact VectorNonvanishing _ cfg.proper.1 3 2 (by decide)
      (Or.inl (positive_parent 2))
  · exact VectorNonvanishing _ cfg.proper.1 1 3 (by decide)
      (Or.inl (positive_parent 0))
  · exact VectorNonvanishing _ cfg.proper.1 2 1 (by decide)
      (Or.inl (positive_parent 1))

private theorem signed_injective :
    (by
      classical
      exact
        ∀ (v : GaussianInt), (v ≠ 0) → (∀ (b : Bool), ∀ (c : Bool), ((if b = true then (1 : ℝ)
            else -1) •
              ((1 / 2 : ℝ) • (GaussianRealPoint v -
                (-(GaussianRealPoint v).2, (GaussianRealPoint v).1))) =
            (if c = true then (1 : ℝ) else -1) •
              ((1 / 2 : ℝ) • (GaussianRealPoint v -
                (-(GaussianRealPoint v).2, (GaussianRealPoint v).1)))) → (b = c)) ) := by
  classical
  intro v hv b c he
  have nonzero : (1 / 2 : ℝ) • (GaussianRealPoint v -
      (-(GaussianRealPoint v).2, (GaussianRealPoint v).1)) ≠ (0 : ℝ × ℝ) := by
    intro hz
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    simp [GaussianRealPoint, -GaussianInt.intCast_re, -GaussianInt.intCast_im] at hx hy
    apply hv
    apply Zsqrtd.ext
    · exact_mod_cast (show (v.re : ℝ) = 0 by linarith)
    · exact_mod_cast (show (v.im : ℝ) = 0 by linarith)
  have he' := smul_left_injective ℝ nonzero he
  cases b <;> cases c <;> first | rfl | norm_num at he'

private theorem selected_sign :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        let sign : SixSubtileLabel → Bool := fun l => match l with
          | .A | .C | .E => true
          | .B | .D | .F => false
        (TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) = TileCentroid
            (occurrence placement.centralIndex)) → ((TileCentroid (occurrence
            placement.centralIndex) = TileCentroid (cert.P (slot placement.centralIndex.label)
            (sign placement.centralIndex.label))) → ((bundle.selectedSlot = slot
            placement.centralIndex.label) → ((∀ (j : Fin 3), BandVectors.1 (q ((j + 2).succ)) (q
            ((j + 1).succ)) ≠ 0) → ((∀ (v : GaussianInt), (v ≠ 0) → (∀ (b : Bool), ∀ (c : Bool),
            ((if b = true then (1 : ℝ) else -1) • ((1 / 2 : ℝ) • (GaussianRealPoint v -
            (-(GaussianRealPoint v).2, (GaussianRealPoint v).1))) = (if c = true then (1 : ℝ)
            else -1) • ((1 / 2 : ℝ) • (GaussianRealPoint v - (-(GaussianRealPoint v).2,
            (GaussianRealPoint v).1)))) → (b = c))) → (bundle.selectedSign = sign
            placement.centralIndex.label))))) ) := by
  classical
  intro C D T N h k x bundle placement q cert occurrence slot sign selected_centroid
      central_centroid selected_slot cyclic_nonzero signed_injective
  have hc := congrArg (fun a : ℝ × ℝ => a - TileCentroid bundle.normalizedRoot)
    (selected_centroid.trans central_centroid)
  simp only [bundle.piece_centroid, selected_slot] at hc
  rw [(cert.outer_occurrence _ _).2.2] at hc
  exact signed_injective _ (cyclic_nonzero _) _ _ hc

private theorem fixed_circle :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (row :
            BandOrderedGeneralSelectedContactRow bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedRoot placement.layout
            placement.exteriorIndex placement.centralIndex), ∀ (r : Fin 4 → CircleCoordinates), ∀
            (i : Fin 3), ∀ (s : Fin 4),
        let q := bundle.normalizedPresentation
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (bundle.normalizedFixedCircle.1.1 =
            bundle.normalizedPresentation ((match placement.exteriorIndex.label with
              | SixSubtileLabel.A => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.B => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.C => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.D => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.E => (3 : Fin (4 : ℕ))
              | SixSubtileLabel.F => (3 : Fin (4 : ℕ))
              )) ∧
            ((↑s : ℕ) = (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              | SixSubtileLabel.C => if placement.exteriorIndex.second = (0 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.D => if placement.exteriorIndex.second = (0 : ℤ) then (1 : ℕ)
                  else (2 : ℕ)
              | SixSubtileLabel.E => if placement.exteriorIndex.first = (0 : ℤ) then (3 : ℕ) else
                  (0 : ℕ)
              | SixSubtileLabel.F => if placement.exteriorIndex.first = (0 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              )) ∧ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ) else
            BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ)))) = match P3996T1SRowTable
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedRoot placement.layout row with
            | some z => z.oldShift
            | none =>
              (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then
                  -placement.layout.u else placement.layout.u
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then
                  placement.layout.u else -placement.layout.u
              | SixSubtileLabel.C => -placement.layout.v
              | SixSubtileLabel.D => placement.layout.v
              | SixSubtileLabel.E => (0 : ℤ√(-1 : ℤ))
              | SixSubtileLabel.F => (0 : ℤ√(-1 : ℤ))
              )) →
            (bundle.normalizedFixedCircle.1.1 = q (slot placement.exteriorIndex.label).succ) ) := by
  classical
  intro C D T N h k x bundle placement row r i s q slot outer
  cases he : placement.exteriorIndex.label <;> simpa [slot, he, q] using outer.1

private theorem selected_slope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (p : ℝ × ℝ), (PartialOdometerSlope
            (bundle.functions bundle.selectedSlot bundle.selectedSign) = some p) → (
        let q := bundle.normalizedPresentation
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        let sign : SixSubtileLabel → Bool := fun l => match l with
          | .A | .C | .E => true
          | .B | .D | .F => false
        (bundle.selectedSlot = slot placement.centralIndex.label) → ((bundle.selectedSign = sign
            placement.centralIndex.label) → (p - bundle.normalizedRootSlope = (if sign
            placement.centralIndex.label = true then (1 : ℝ) else -1) • ((1 / 2 : ℝ) •
            GaussianRealPoint ((1 + (⟨0, 1⟩ : GaussianInt)) * BandVectors.2 (q ((slot
            placement.centralIndex.label + 2).succ)) (q ((slot placement.centralIndex.label +
            1).succ))))))) ) := by
  classical
  intro C D T N h k x bundle placement p hp q slot sign selected_slot selected_sign
  let cfg := bundle.configuration
  have raw : p - bundle.normalizedRootSlope =
      (if bundle.selectedSign = true then (1 : ℝ) else -1) •
        ((1 / 2 : ℝ) • GaussianRealPoint
          ((1 + (⟨0, 1⟩ : GaussianInt)) *
            BandVectors.2 (q ((bundle.selectedSlot + 2).succ))
              (q ((bundle.selectedSlot + 1).succ)))) := by
    rcases bundle.piece_slope bundle.selectedSlot bundle.selectedSign with
      hz | ⟨p₀, p₁, hp₀, hp₁, hx, hy⟩
    · exact False.elim (cfg.noLine _ hz)
    · have he₀ : p₀ = bundle.normalizedRootSlope :=
        Option.some.inj (hp₀.symm.trans bundle.normalized_root_slope)
      have he₁ : p₁ = p := Option.some.inj (hp₁.symm.trans hp)
      subst p₀
      subst p₁
      cases hs : bundle.selectedSign <;> apply Prod.ext
      all_goals
        simp [hs, GaussianRealPoint, q,
          -GaussianInt.intCast_re, -GaussianInt.intCast_im] at hx hy ⊢
        linarith
  simpa only [selected_slot, selected_sign] using raw

private theorem affine_incoming :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        ∀ (j : Fin 3), BandVectors.2 (q j.succ) (q 0) = (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q
            0) (q j.succ) ) := by
  classical
  intro C D T N h k x bundle q j
  let cfg := bundle.configuration
  have hf := ((VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper j).2
  rw [hf]
  ext <;> simp

private theorem fixed_slope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (row :
            BandOrderedGeneralSelectedContactRow bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedRoot placement.layout
            placement.exteriorIndex placement.centralIndex), ∀ (r : Fin 4 → CircleCoordinates), ∀
            (i : Fin 3), ∀ (s : Fin 4), (r (0 : Fin (4 : ℕ)) = bundle.normalizedCircle.1.1) → ((r
                i.succ =
            bundle.normalizedFixedCircle.1.1) →
            ((bundle.normalizedFixedSlope.1 - bundle.normalizedRootSlope.1 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r
            i.succ)))).1) → ((bundle.normalizedFixedSlope.2 - bundle.normalizedRootSlope.2 = ((1
            / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
            (BandVectors.2 (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ)))
            (r i.succ)))).2) → (
        let q := bundle.normalizedPresentation
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (bundle.normalizedFixedCircle.1.1 =
            bundle.normalizedPresentation ((match placement.exteriorIndex.label with
              | SixSubtileLabel.A => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.B => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.C => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.D => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.E => (3 : Fin (4 : ℕ))
              | SixSubtileLabel.F => (3 : Fin (4 : ℕ))
              )) ∧
            ((↑s : ℕ) = (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              | SixSubtileLabel.C => if placement.exteriorIndex.second = (0 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.D => if placement.exteriorIndex.second = (0 : ℤ) then (1 : ℕ)
                  else (2 : ℕ)
              | SixSubtileLabel.E => if placement.exteriorIndex.first = (0 : ℤ) then (3 : ℕ) else
                  (0 : ℕ)
              | SixSubtileLabel.F => if placement.exteriorIndex.first = (0 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              )) ∧ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ) else
            BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ)))) = match P3996T1SRowTable
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedRoot placement.layout row with
            | some z => z.oldShift
            | none =>
              (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then
                  -placement.layout.u else placement.layout.u
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then
                  placement.layout.u else -placement.layout.u
              | SixSubtileLabel.C => -placement.layout.v
              | SixSubtileLabel.D => placement.layout.v
              | SixSubtileLabel.E => (0 : ℤ√(-1 : ℤ))
              | SixSubtileLabel.F => (0 : ℤ√(-1 : ℤ))
              )) →
            ((bundle.normalizedFixedCircle.1.1 = q (slot placement.exteriorIndex.label).succ) →
            ((∀ (j : Fin 3), BandVectors.2 (q j.succ) (q 0) = (⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 (q 0) (q j.succ)) → (bundle.normalizedFixedSlope -
            bundle.normalizedRootSlope = (1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt)
            ^ ((match placement.exteriorIndex.label with
              | .A => if placement.exteriorIndex.first = -1 then 3 else 0
              | .B => if placement.exteriorIndex.first = 1 then 1 else 2
              | .C => if placement.exteriorIndex.second = 0 then 3 else 0
              | .D => if placement.exteriorIndex.second = 0 then 1 else 2
              | .E => if placement.exteriorIndex.first = 0 then 3 else 0
              | .F => if placement.exteriorIndex.first = 0 then 1 else 2
              )) * ((⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 (q 0) (q (slot placement.exteriorIndex.label).succ) + BandVectors.2 (q
            0) (q (slot placement.exteriorIndex.label).succ)))))))))) ) := by
  classical
  intro C D T N h k x bundle placement row r i s hr0 hri hslopex hslopey q slot outer
      fixed_circle affine_incoming
  have he : bundle.normalizedFixedSlope - bundle.normalizedRootSlope =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
            BandVectors.2 (r 0) (r i.succ))) := Prod.ext hslopex hslopey
  have hroot : r 0 = q 0 := hr0.trans bundle.normalized_circle_eq.symm
  rw [hroot, hri, fixed_circle, affine_incoming, outer.2.1] at he
  exact he

private theorem selected_odometer :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (C' : BandCircle),
            (C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ) → (TileOdometer
            C'.1.1 (bundle.pieces bundle.selectedSlot bundle.selectedSign) (bundle.functions
            bundle.selectedSlot bundle.selectedSign)) ) := by
  classical
  intro C D T N h k x bundle C' hC'
  rw [hC']
  exact bundle.piece_odometer _ _

private theorem row_geometry :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cfg := bundle.configuration
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row' :
            BandOrderedGeneralSelectedContactRow q cfg bundle.normalizedCircle
            bundle.normalizedRoot cert a b), (TileCentroid bundle.normalizedFixed = TileCentroid
                (occurrence a)) → ((TileCentroid (bundle.pieces bundle.selectedSlot
                bundle.selectedSign) =
            TileCentroid (occurrence b)) → (∀ (z : P3996T1SRowParameters), (P3996T1SRowTable
                q cfg bundle.normalizedCircle
            bundle.normalizedRoot cert row' = some z) → (ProperBandQuadruple z.predecessor ∧ (if
                z.childIsExterior then TileCentroid (bundle.pieces bundle.selectedSlot
                bundle.selectedSign) - TileCentroid bundle.normalizedFixed else TileCentroid
                bundle.normalizedFixed - TileCentroid (bundle.pieces bundle.selectedSlot
                bundle.selectedSign)) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
                z.rotation.val * (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor
                0) + BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ)))))) ) := by
  classical
  intro C D T N h k x bundle placement q cfg cert occurrence a b row' hfixed hselected z hz
  obtain ⟨hproper, _, _, _, _, _, hindices, _, _, hc, _⟩ :=
    P3996T1SRowAlignment q cfg bundle.normalizedCircle
      bundle.normalizedRoot cert _ _ row' z hz
  refine ⟨hproper, ?_⟩
  cases hf : z.childIsExterior
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hindices ⊢
    rw [hselected, hfixed]
    simpa only [hindices.1, hindices.2] using hc
  · simp only [hf, ↓reduceIte] at hindices ⊢
    rw [hselected, hfixed]
    simpa only [hindices.1, hindices.2] using hc

private theorem sub :
    (by
      classical
      exact
        ∀ (z : P3996T1SRowParameters), ∀ (A : BandCircle), ∀ (B : BandCircle), ∀ (V :
            ProtoTile), ∀ (W : ProtoTile), ∀ (f : PartialOdometer), ∀ (g : PartialOdometer), ∀
            (pV : ℝ × ℝ), ∀ (pW : ℝ × ℝ), (TileOdometer A.1.1 V f) → ((TileOdometer B.1.1 W g) →
            ((PartialOdometerSlope f = some pV) → ((PartialOdometerSlope g = some pW) →
            ((ProperBandQuadruple z.predecessor) → ((z.predecessor 0 = A.1.1) → ((z.predecessor
            z.parentSlot.succ = B.1.1) → ((TileCentroid W - TileCentroid V =
            (1 / 2 : ℝ) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
                (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                  BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ)))) → ((pW -
                      pV = (1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
              (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ)))) →
                    (ProperBandQuadruple z.predecessor ∧ z.predecessor 0 = A.1.1 ∧ z.predecessor
                    z.parentSlot.succ = B.1.1 ∧ TileCentroid W - TileCentroid V = (1 / 2 : ℝ) •
                    GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val * (BandVectors.1
                    (z.predecessor z.parentSlot.succ) (z.predecessor 0) + BandVectors.1
                    (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧ pW - pV = (1 / 2 : ℝ)
                    • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
                    (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                    BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
                    SubtileLatticeAdjacent A B V W f g))))))))) ) := by
  classical
  intro z A B V W f g pV pW hV hW hf hg hr h0 hj hc hs
  exact ⟨hr, h0, hj, hc, hs, hV, hW, pV, pW, hf, hg,
    z.predecessor, z.parentSlot, z.rotation, hr, h0, hj, hc,
    congrArg Prod.fst hs, congrArg Prod.snd hs⟩

private theorem left :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (C' : BandCircle), ∀
            (p : ℝ × ℝ), (PartialOdometerSlope (bundle.functions bundle.selectedSlot
            bundle.selectedSign) = some p) → ((TileOdometer C'.1.1 (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) (bundle.functions bundle.selectedSlot
            bundle.selectedSign)) → (∀ (r' : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), ∀ (e :
            Bool), (ProperBandQuadruple r') → ((r' 0 = bundle.normalizedFixedCircle.1.1) →
            ((C'.1.1 = bundle.normalizedFixedCircle.1.1) → ((TileCentroid (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) -
              TileCentroid bundle.normalizedFixed =
            (if e = true then (1 : ℝ) else -1) •
              GaussianRealPoint (BandVectors.1 (r' j.succ) (r' 0))) → ((p -
                  bundle.normalizedFixedSlope =
            (if e = true then (1 : ℝ) else -1) •
              GaussianRealPoint (BandVectors.2 (r' j.succ) (r' 0))) → (C' =
                  bundle.normalizedFixedCircle ∧ LeftLatticeAdjacent bundle.normalizedFixedCircle
                  bundle.normalizedFixed (bundle.pieces bundle.selectedSlot bundle.selectedSign)
                  bundle.normalizedFixedFunction (bundle.functions bundle.selectedSlot
                  bundle.selectedSign)))))))) ) := by
  classical
  intro C D T N h k x bundle C' p hp selected_odometer r' j e hr' h0 heq hc hs
  refine ⟨Subtype.ext (Subtype.ext heq), bundle.normalized_fixed_odometer,
    ?_, bundle.normalizedFixedSlope, p, bundle.normalized_fixed_slope, hp,
    Or.inr ⟨r', j, e, hr', h0, hc, ?_, ?_⟩⟩
  · simpa only [heq] using selected_odometer
  · cases e <;> simpa [GaussianRealPoint] using congrArg Prod.fst hs
  · cases e <;> simpa [GaussianRealPoint] using congrArg Prod.snd hs

end PresentedRowAdjacencyGeometry

namespace PresentedAdjacencyConclusion

private theorem presentedAdjacency :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (row :
            BandOrderedGeneralSelectedContactRow bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedRoot placement.layout
            placement.exteriorIndex placement.centralIndex), ∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (C' : BandCircle), ∀
            (p : ℝ × ℝ), (PartialOdometerSlope (bundle.functions bundle.selectedSlot
            bundle.selectedSign) = some p) → (
        let q := bundle.normalizedPresentation
        let cfg := bundle.configuration
        let cert := placement.layout
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let slot : SixSubtileLabel → Fin 3 := fun l => match l with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        let sign : SixSubtileLabel → Bool := fun l => match l with
          | .A | .C | .E => true
          | .B | .D | .F => false
        (bundle.normalizedFixedCircle.1.1 =
            bundle.normalizedPresentation ((match placement.exteriorIndex.label with
              | SixSubtileLabel.A => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.B => (1 : Fin (4 : ℕ))
              | SixSubtileLabel.C => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.D => (2 : Fin (4 : ℕ))
              | SixSubtileLabel.E => (3 : Fin (4 : ℕ))
              | SixSubtileLabel.F => (3 : Fin (4 : ℕ))
              )) ∧
            ((↑s : ℕ) = (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              | SixSubtileLabel.C => if placement.exteriorIndex.second = (0 : ℤ) then (3 : ℕ)
                  else (0 : ℕ)
              | SixSubtileLabel.D => if placement.exteriorIndex.second = (0 : ℤ) then (1 : ℕ)
                  else (2 : ℕ)
              | SixSubtileLabel.E => if placement.exteriorIndex.first = (0 : ℤ) then (3 : ℕ) else
                  (0 : ℕ)
              | SixSubtileLabel.F => if placement.exteriorIndex.first = (0 : ℤ) then (1 : ℕ) else
                  (2 : ℕ)
              )) ∧ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ) else
            BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ)))) = match P3996T1SRowTable
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedRoot placement.layout row with
            | some z => z.oldShift
            | none =>
              (match placement.exteriorIndex.label with
              | SixSubtileLabel.A => if placement.exteriorIndex.first = (-1 : ℤ) then
                  -placement.layout.u else placement.layout.u
              | SixSubtileLabel.B => if placement.exteriorIndex.first = (1 : ℤ) then
                  placement.layout.u else -placement.layout.u
              | SixSubtileLabel.C => -placement.layout.v
              | SixSubtileLabel.D => placement.layout.v
              | SixSubtileLabel.E => (0 : ℤ√(-1 : ℤ))
              | SixSubtileLabel.F => (0 : ℤ√(-1 : ℤ))
              )) → ((TileCentroid
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) = TileCentroid (occurrence
            placement.centralIndex)) → ((TileCentroid bundle.normalizedFixed = TileCentroid
            (occurrence placement.exteriorIndex)) → ((TileCentroid (occurrence
            placement.centralIndex) = TileCentroid (cert.P (slot placement.centralIndex.label)
            (sign placement.centralIndex.label))) → ((C'.1.1 = q (slot
            placement.centralIndex.label).succ) → ((bundle.normalizedFixedCircle.1.1 =
                bundle.normalizedPresentation (slot placement.exteriorIndex.label).succ) → ((p -
            bundle.normalizedRootSlope = (if sign placement.centralIndex.label = true then (1 :
            ℝ) else -1) • ((1 / 2 : ℝ) • GaussianRealPoint ((1 + (⟨0, 1⟩ : GaussianInt)) *
            BandVectors.2 (q ((slot placement.centralIndex.label + 2).succ)) (q ((slot
            placement.centralIndex.label + 1).succ))))) → ((bundle.normalizedFixedSlope -
            bundle.normalizedRootSlope = (1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt)
            ^ (((match placement.exteriorIndex.label with
              | .A => if placement.exteriorIndex.first = -1 then 3 else 0
              | .B => if placement.exteriorIndex.first = 1 then 1 else 2
              | .C => if placement.exteriorIndex.second = 0 then 3 else 0
              | .D => if placement.exteriorIndex.second = 0 then 1 else 2
              | .E => if placement.exteriorIndex.first = 0 then 3 else 0
              | .F => if placement.exteriorIndex.first = 0 then 1 else 2
              ) )) * ((⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 (q 0) (q (slot placement.exteriorIndex.label).succ) + BandVectors.2 (q
            0) (q (slot placement.exteriorIndex.label).succ)))) → ((TileOdometer C'.1.1
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) (bundle.functions
            bundle.selectedSlot bundle.selectedSign)) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), ∀ (row' : BandOrderedGeneralSelectedContactRow q cfg
            bundle.normalizedCircle bundle.normalizedRoot cert a b), (TileCentroid
            bundle.normalizedFixed = TileCentroid (occurrence a)) → ((TileCentroid (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) = TileCentroid (occurrence b)) → (∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg bundle.normalizedCircle
            bundle.normalizedRoot cert row' = some z) → (ProperBandQuadruple z.predecessor ∧ (if
            z.childIsExterior then TileCentroid (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) - TileCentroid bundle.normalizedFixed else TileCentroid
            bundle.normalizedFixed - TileCentroid (bundle.pieces bundle.selectedSlot
            bundle.selectedSign)) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            z.rotation.val * (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
            BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))))))) → ((∀ (z :
            P3996T1SRowParameters), ∀ (A : BandCircle), ∀ (B : BandCircle), ∀ (V : ProtoTile),
            ∀ (W : ProtoTile), ∀ (f : PartialOdometer), ∀ (g : PartialOdometer), ∀ (pV : ℝ × ℝ),
            ∀ (pW : ℝ × ℝ), (TileOdometer A.1.1 V f) → ((TileOdometer B.1.1 W g) →
            ((PartialOdometerSlope f = some pV) → ((PartialOdometerSlope g = some pW) →
            ((ProperBandQuadruple z.predecessor) → ((z.predecessor 0 = A.1.1) → ((z.predecessor
            z.parentSlot.succ = B.1.1) → ((TileCentroid W - TileCentroid V = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val * (BandVectors.1
            (z.predecessor z.parentSlot.succ) (z.predecessor 0) + BandVectors.1 (z.predecessor 0)
            (z.predecessor z.parentSlot.succ)))) → ((pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val * (BandVectors.2 (z.predecessor
            z.parentSlot.succ) (z.predecessor 0) + BandVectors.2 (z.predecessor 0) (z.predecessor
            z.parentSlot.succ)))) → (ProperBandQuadruple z.predecessor ∧ z.predecessor 0 = A.1.1
            ∧ z.predecessor z.parentSlot.succ = B.1.1 ∧ TileCentroid W - TileCentroid V = (1 / 2
            : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val * (BandVectors.1
            (z.predecessor z.parentSlot.succ) (z.predecessor 0) + BandVectors.1 (z.predecessor 0)
            (z.predecessor z.parentSlot.succ))) ∧ pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val * (BandVectors.2 (z.predecessor
            z.parentSlot.succ) (z.predecessor 0) + BandVectors.2 (z.predecessor 0) (z.predecessor
            z.parentSlot.succ))) ∧ SubtileLatticeAdjacent A B V W f g)))))))))) → ((∀ (r' : Fin 4
            → CircleCoordinates), ∀ (j : Fin 3), ∀ (e : Bool), (ProperBandQuadruple r') → ((r' 0
            = bundle.normalizedFixedCircle.1.1) → ((C'.1.1 = bundle.normalizedFixedCircle.1.1) →
            ((TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) - TileCentroid
            bundle.normalizedFixed = (if e = true then (1 : ℝ) else -1) • GaussianRealPoint
            (BandVectors.1 (r' j.succ) (r' 0))) → ((p - bundle.normalizedFixedSlope = (if e =
            true then (1 : ℝ) else -1) • GaussianRealPoint (BandVectors.2 (r' j.succ) (r' 0))) →
            (C' = bundle.normalizedFixedCircle ∧ LeftLatticeAdjacent bundle.normalizedFixedCircle
            bundle.normalizedFixed (bundle.pieces bundle.selectedSlot bundle.selectedSign)
            bundle.normalizedFixedFunction (bundle.functions bundle.selectedSlot
            bundle.selectedSign))))))) → ((BandVectors.2 (bundle.normalizedPresentation (1 : Fin
            (4 : ℕ))) (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) = -BandVectors.2
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ))) - BandVectors.2 (bundle.normalizedPresentation (3 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ)))) → ((BandVectors.2
            (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * (BandVectors.2
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ))) + BandVectors.2 (bundle.normalizedPresentation (3 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))))) → ((BandVectors.2
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ))) = BandVectors.2 (bundle.normalizedPresentation (2 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (1 : Fin (4 : ℕ))) - -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * (BandVectors.2 (bundle.normalizedPresentation (2 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (1 : Fin (4 : ℕ))) + BandVectors.2
            (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) (bundle.normalizedPresentation (2 :
            Fin (4 : ℕ))))) → ((BandVectors.2 (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) = BandVectors.2
            (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) (bundle.normalizedPresentation (2 :
            Fin (4 : ℕ))) + -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ)))) → ((BandVectors.2 (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) = -BandVectors.2
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ))) - BandVectors.2 (bundle.normalizedPresentation (3 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) + -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (bundle.normalizedPresentation (3 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ)))) → ((BandVectors.2
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) +
            BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin
            (4 : ℕ))) = ((1 : GaussianInt) + -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2
            (bundle.normalizedPresentation (2 : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 :
            Fin (4 : ℕ)))) → ((BandVectors.2 (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) = (-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) - (1 : GaussianInt)) * (BandVectors.2 (bundle.normalizedPresentation (2
            : Fin (4 : ℕ))) (bundle.normalizedPresentation (1 : Fin (4 : ℕ))) + BandVectors.2
            (bundle.normalizedPresentation (3 : Fin (4 : ℕ))) (bundle.normalizedPresentation (2 :
            Fin (4 : ℕ))))) → ((BandVectors.2 (cfg.secondPredecessor (1 : Fin (4 : ℕ)))
            (cfg.secondPredecessor (0 : Fin (4 : ℕ))) + BandVectors.2 (cfg.secondPredecessor (0 :
            Fin (4 : ℕ))) (cfg.secondPredecessor (1 : Fin (4 : ℕ))) = ((1 : GaussianInt) + -(⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (bundle.normalizedPresentation (3 :
            Fin (4 : ℕ))) (bundle.normalizedPresentation (2 : Fin (4 : ℕ)))) → (
        let S := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let f := bundle.functions bundle.selectedSlot bundle.selectedSign
        let directed := fun (z : P3996T1SRowParameters)
            (A B : BandCircle) (V W : ProtoTile) (f g : PartialOdometer)
            (pV pW : ℝ × ℝ) =>
          ProperBandQuadruple z.predecessor ∧
          z.predecessor 0 = A.1.1 ∧
          z.predecessor z.parentSlot.succ = B.1.1 ∧
          TileCentroid W - TileCentroid V =
            (1 / 2 : ℝ) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
                (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                 BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
          pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
              (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
               BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
          SubtileLatticeAdjacent A B V W f g
        match P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedRoot placement.layout row with
        | none => C' = bundle.normalizedFixedCircle ∧
            LeftLatticeAdjacent bundle.normalizedFixedCircle bundle.normalizedFixed S
              bundle.normalizedFixedFunction f
        | some z =>
            if z.childIsExterior then
              directed z bundle.normalizedFixedCircle C' bundle.normalizedFixed S
                bundle.normalizedFixedFunction f bundle.normalizedFixedSlope p
            else
              directed z C' bundle.normalizedFixedCircle S bundle.normalizedFixed
                f bundle.normalizedFixedFunction p
                    bundle.normalizedFixedSlope))))))))))))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement row r i s C' p hp q cfg cert occurrence slot sign outer
      selected_centroid fixed_centroid central_centroid selected_circle fixed_circle
      selected_slope fixed_slope selected_odometer row_geometry sub left a13 a31 a01 a02 a03
      sum12 sum13 sum23
  generalize ha : placement.exteriorIndex = a at row fixed_circle fixed_centroid fixed_slope ⊢
  generalize hb : placement.centralIndex = b at row selected_circle
  rw [hb] at selected_slope selected_centroid central_centroid
  cases row
  case' positiveL1 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.firstPredecessor 1 true cfg.firstProper
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.firstChild, cfg.firstParentTwo]
      rw [← neg_sub, presentation]
      simp
  case' positiveL2 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.firstPredecessor 2 true cfg.firstProper
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.firstChild, cfg.firstParentThree]
      rw [← neg_sub, presentation]
      simp
  case' positiveL3 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.secondPredecessor 0 true cfg.secondProper
    · exact cfg.secondChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.secondChild, cfg.secondParentOne]
      rw [← neg_sub, presentation]
      simp
  case' reflectedL1 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.firstPredecessor 1 false cfg.firstProper
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.firstChild, cfg.firstParentTwo]
      rw [← neg_sub, presentation]
  case' reflectedL2 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.firstPredecessor 2 false cfg.firstProper
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.firstChild, cfg.firstParentThree]
      rw [← neg_sub, presentation]
  case' reflectedL3 hne presentation =>
    simp only [P3996T1SRowTable]
    apply left cfg.secondPredecessor 0 false cfg.secondProper
    · exact cfg.secondChild.trans fixed_circle.symm
    · exact selected_circle.trans fixed_circle.symm
    · rw [fixed_centroid, selected_centroid, central_centroid]
      norm_num [slot, sign, Fin.succ]
      simp only [cfg.secondChild, cfg.secondParentOne]
      rw [← neg_sub, presentation]
  case' positiveS1 presentation =>
    have geo := row_geometry _ _ (.positiveS1 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact cfg.firstParentTwo.trans selected_circle.symm
  case' positiveS2 presentation =>
    have geo := row_geometry _ _ (.positiveS2 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact cfg.firstParentThree.trans selected_circle.symm
  case' positiveS3 presentation =>
    have geo := row_geometry _ _ (.positiveS3 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.secondChild.trans fixed_circle.symm
    · exact cfg.secondParentOne.trans selected_circle.symm
  case' positiveS4 presentation =>
    have geo := row_geometry _ _ (.positiveS4 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans selected_circle.symm
    · exact cfg.firstParentTwo.trans fixed_circle.symm
  case' positiveS5 presentation =>
    have geo := row_geometry _ _ (.positiveS5 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans selected_circle.symm
    · exact cfg.firstParentThree.trans fixed_circle.symm
  case' positiveS6 presentation =>
    have geo := row_geometry _ _ (.positiveS6 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.secondChild.trans selected_circle.symm
    · exact cfg.secondParentOne.trans fixed_circle.symm
  case' reflectedS1 presentation =>
    have geo := row_geometry _ _ (.reflectedS1 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact cfg.firstParentTwo.trans selected_circle.symm
  case' reflectedS2 presentation =>
    have geo := row_geometry _ _ (.reflectedS2 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans fixed_circle.symm
    · exact cfg.firstParentThree.trans selected_circle.symm
  case' reflectedS3 presentation =>
    have geo := row_geometry _ _ (.reflectedS3 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable, ↓reduceIte]
    refine sub _ _ _ _ _ _ _ _ _ bundle.normalized_fixed_odometer selected_odometer
      bundle.normalized_fixed_slope hp geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.secondChild.trans fixed_circle.symm
    · exact cfg.secondParentOne.trans selected_circle.symm
  case' reflectedS4 presentation =>
    have geo := row_geometry _ _ (.reflectedS4 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans selected_circle.symm
    · exact cfg.firstParentTwo.trans fixed_circle.symm
  case' reflectedS5 presentation =>
    have geo := row_geometry _ _ (.reflectedS5 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.firstChild.trans selected_circle.symm
    · exact cfg.firstParentThree.trans fixed_circle.symm
  case' reflectedS6 presentation =>
    have geo := row_geometry _ _ (.reflectedS6 presentation)
      fixed_centroid selected_centroid _ rfl
    simp only [P3996T1SRowTable]
    refine sub _ _ _ _ _ _ _ _ _ selected_odometer bundle.normalized_fixed_odometer
      hp bundle.normalized_fixed_slope geo.1 ?_ ?_ geo.2 ?_
    · exact cfg.secondChild.trans selected_circle.symm
    · exact cfg.secondParentOne.trans fixed_circle.symm
  all_goals
    first
    | rw [show p - bundle.normalizedFixedSlope =
        (p - bundle.normalizedRootSlope) -
          (bundle.normalizedFixedSlope - bundle.normalizedRootSlope) by abel,
        selected_slope, fixed_slope]
    | rw [show bundle.normalizedFixedSlope - p =
        (bundle.normalizedFixedSlope - bundle.normalizedRootSlope) -
          (p - bundle.normalizedRootSlope) by abel, fixed_slope, selected_slope]
    norm_num [slot, sign, Fin.add_def, Fin.add, Fin.succ]
    try simp only [sum12, sum13, sum23]
    simp only [q, cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree,
      cfg.secondChild, cfg.secondParentOne, a01, a02, a03, a13, a31]
    ext <;> norm_num [GaussianRealPoint, pow_succ,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

end PresentedAdjacencyConclusion

theorem P4418T3PresentedRowAdjacency :
    ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
        PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
        BandOrderedGeneralSubtilePlacement
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixedCircle
      bundle.normalizedRoot bundle.normalizedFixed
      bundle.normalizedRootFunction bundle.normalizedFixedFunction
      bundle.normalizedPoint bundle.pieces bundle.functions
      bundle.selectedSlot bundle.selectedSign bundle.routedDirection), ∀ (row :
          BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedRoot placement.layout
      placement.exteriorIndex placement.centralIndex), ∀ (r : Fin 4 → CircleCoordinates), ∀ (i :
          Fin 3), ∀ (s : Fin 4), (ProperBandQuadruple r) → ((r 0 = bundle.normalizedCircle.1.1) →
          ((r i.succ = bundle.normalizedFixedCircle.1.1) → ((TileCentroid bundle.normalizedFixed -
        TileCentroid bundle.normalizedRoot =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
           BandVectors.1 (r 0) (r i.succ)))) → ((bundle.normalizedFixedSlope.1 -
        bundle.normalizedRootSlope.1 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).1) → ((bundle.normalizedFixedSlope.2 -
        bundle.normalizedRootSlope.2 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).2) → (∀ (C' : BandCircle), ∀ (p : ℝ × ℝ), (C'.1.1 =
               bundle.normalizedPresentation bundle.selectedSlot.succ) → ((PartialOdometerSlope
      (bundle.functions bundle.selectedSlot bundle.selectedSign) = some p) → ((TileSubodometer
          bundle.normalizedCircle.1.1 C'.1.1
      bundle.normalizedRoot (bundle.pieces bundle.selectedSlot bundle.selectedSign)
      bundle.normalizedRootFunction
      (bundle.functions bundle.selectedSlot bundle.selectedSign)) → (
    let S := bundle.pieces bundle.selectedSlot bundle.selectedSign
    let f := bundle.functions bundle.selectedSlot bundle.selectedSign
    let directed := fun (z : P3996T1SRowParameters)
        (A B : BandCircle) (V W : ProtoTile) (f g : PartialOdometer)
        (pV pW : ℝ × ℝ) =>
      ProperBandQuadruple z.predecessor ∧
      z.predecessor 0 = A.1.1 ∧
      z.predecessor z.parentSlot.succ = B.1.1 ∧
      TileCentroid W - TileCentroid V =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
             BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
          (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
           BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      SubtileLatticeAdjacent A B V W f g
    match P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedRoot placement.layout row with
    | none => C' = bundle.normalizedFixedCircle ∧
        LeftLatticeAdjacent bundle.normalizedFixedCircle bundle.normalizedFixed S
          bundle.normalizedFixedFunction f
    | some z =>
        if z.childIsExterior then
          directed z bundle.normalizedFixedCircle C' bundle.normalizedFixed S
            bundle.normalizedFixedFunction f bundle.normalizedFixedSlope p
        else
          directed z C' bundle.normalizedFixedCircle S bundle.normalizedFixed
            f bundle.normalizedFixedFunction p bundle.normalizedFixedSlope))))))))) := by
  intro C D T N h k x bundle placement row r i s hr hr0 hri hcentroid hslopex hslopey C' p hC' hp
      hsub
-- BODY
  classical
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let cert := placement.layout
  let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let slot : SixSubtileLabel → Fin 3 := fun l => match l with
    | .A | .B => 0
    | .C | .D => 1
    | .E | .F => 2
  let sign : SixSubtileLabel → Bool := fun l => match l with
    | .A | .C | .E => true
    | .B | .D | .F => false
  have outer := P4418T3OuterCompanionAlignment C D T N h k x
    bundle placement row r i s hr hr0 hri hcentroid hslopex hslopey
  have selected_cells := PresentedRowAdjacencyGeometry.selected_cells
            C D T N h k x bundle placement
  have selected_centroid :
      TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) =
        TileCentroid (occurrence placement.centralIndex) :=
            PresentedRowAdjacencyGeometry.selected_centroid C D T N h k x bundle placement
            selected_cells
  have fixed_centroid : TileCentroid bundle.normalizedFixed =
      TileCentroid (occurrence placement.exteriorIndex) :=
    (ProtoTileObservableExtensionality _ _ placement.fixed_exterior_cells
      placement.fixed_exterior_empty_anchor).2.2.2.2.symm
  have central_centroid : TileCentroid (occurrence placement.centralIndex) =
      TileCentroid (cert.P (slot placement.centralIndex.label)
        (sign placement.centralIndex.label)) := PresentedRowAdjacencyGeometry.central_centroid C
            D T N h k x bundle placement (PresentedRowAdjacencyGeometry.translate_zero_centroid)
  have positive_parent := PresentedRowAdjacencyGeometry.positive_parent C D T N h k x bundle
      placement s
  have area_of_band := PresentedRowAdjacencyGeometry.area_of_band
  have selected_area :
      TileArea (bundle.pieces bundle.selectedSlot bundle.selectedSign) =
        Int.toNat (q bundle.selectedSlot.succ).1 :=
    area_of_band _ _ (positive_parent _)
      (TileOdometerBandPrototile _ _ _ (bundle.piece_odometer _ _))
  have selected_slot := PresentedRowAdjacencyGeometry.selected_slot C D T N h k x bundle
      placement s selected_cells
      positive_parent (PresentedRowAdjacencyGeometry.occurrence_area C D T N h k x bundle
          placement positive_parent area_of_band) selected_area
  have selected_circle : C'.1.1 = q (slot placement.centralIndex.label).succ := by
    exact hC'.trans (congrArg (fun j : Fin 3 => q j.succ) selected_slot)
  have fixed_circle := PresentedRowAdjacencyGeometry.fixed_circle C
          D T N h k x bundle placement row r i s outer
  have selected_slope : p - bundle.normalizedRootSlope =
      (if sign placement.centralIndex.label = true then (1 : ℝ) else -1) •
        ((1 / 2 : ℝ) • GaussianRealPoint
          ((1 + (⟨0, 1⟩ : GaussianInt)) *
            BandVectors.2 (q ((slot placement.centralIndex.label + 2).succ))
              (q ((slot placement.centralIndex.label + 1).succ)))) :=
                  PresentedRowAdjacencyGeometry.selected_slope C D T N h k x bundle placement p
                  hp selected_slot (PresentedRowAdjacencyGeometry.selected_sign C D T N h k x
                      bundle placement selected_centroid central_centroid selected_slot
                      (PresentedRowAdjacencyGeometry.cyclic_nonzero C D T N h k x bundle
                      positive_parent) (PresentedRowAdjacencyGeometry.signed_injective))
  -- The proper affine flip is used on this actual normalized tuple.
  have fixed_slope : bundle.normalizedFixedSlope - bundle.normalizedRootSlope =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^
          ((match placement.exteriorIndex.label with
            | .A => if placement.exteriorIndex.first = -1 then 3 else 0
            | .B => if placement.exteriorIndex.first = 1 then 1 else 2
            | .C => if placement.exteriorIndex.second = 0 then 3 else 0
            | .D => if placement.exteriorIndex.second = 0 then 1 else 2
            | .E => if placement.exteriorIndex.first = 0 then 3 else 0
            | .F => if placement.exteriorIndex.first = 0 then 1 else 2
            )) *
          ((⟨0, 1⟩ : GaussianInt) *
              BandVectors.2 (q 0) (q (slot placement.exteriorIndex.label).succ) +
            BandVectors.2 (q 0) (q (slot placement.exteriorIndex.label).succ))) :=
                PresentedRowAdjacencyGeometry.fixed_slope C D T N h k x bundle placement row r i
                s hr0 hri hslopex hslopey outer fixed_circle
                    (PresentedRowAdjacencyGeometry.affine_incoming C D T N h k x bundle)
  have selected_odometer := PresentedRowAdjacencyGeometry.selected_odometer C D T N h k x bundle
      C' hC'
  have row_geometry (a b : PeriodicSubtileIndex)
      (row' : BandOrderedGeneralSelectedContactRow q cfg bundle.normalizedCircle
        bundle.normalizedRoot cert a b)
      (hfixed : TileCentroid bundle.normalizedFixed = TileCentroid (occurrence a))
      (hselected : TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) =
        TileCentroid (occurrence b))
      (z : P3996T1SRowParameters)
      (hz : P3996T1SRowTable q cfg bundle.normalizedCircle
        bundle.normalizedRoot cert row' = some z) :
      ProperBandQuadruple z.predecessor ∧
        (if z.childIsExterior then
          TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) -
            TileCentroid bundle.normalizedFixed
        else TileCentroid bundle.normalizedFixed -
          TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign)) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
              BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) :=
                  PresentedRowAdjacencyGeometry.row_geometry C D T N h k x bundle placement a b
                  row' hfixed hselected z hz
  have sub (z : P3996T1SRowParameters)
      (A B : BandCircle) (V W : ProtoTile) (f g : PartialOdometer)
      (pV pW : ℝ × ℝ)
      (hV : TileOdometer A.1.1 V f) (hW : TileOdometer B.1.1 W g)
      (hf : PartialOdometerSlope f = some pV)
      (hg : PartialOdometerSlope g = some pW)
      (hr : ProperBandQuadruple z.predecessor)
      (h0 : z.predecessor 0 = A.1.1)
      (hj : z.predecessor z.parentSlot.succ = B.1.1)
      (hc : TileCentroid W - TileCentroid V =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
              BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))))
      (hs : pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
          (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
            BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ)))) :
      ProperBandQuadruple z.predecessor ∧
        z.predecessor 0 = A.1.1 ∧
        z.predecessor z.parentSlot.succ = B.1.1 ∧
        TileCentroid W - TileCentroid V =
          (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
              (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
        pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
              BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
        SubtileLatticeAdjacent A B V W f g := PresentedRowAdjacencyGeometry.sub z A B V W f g pV
            pW hV hW hf hg hr h0 hj hc hs
  have left (r' : Fin 4 → CircleCoordinates) (j : Fin 3) (e : Bool)
      (hr' : ProperBandQuadruple r')
      (h0 : r' 0 = bundle.normalizedFixedCircle.1.1)
      (heq : C'.1.1 = bundle.normalizedFixedCircle.1.1)
      (hc : TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) -
          TileCentroid bundle.normalizedFixed =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.1 (r' j.succ) (r' 0)))
      (hs : p - bundle.normalizedFixedSlope =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.2 (r' j.succ) (r' 0))) :
      C' = bundle.normalizedFixedCircle ∧
        LeftLatticeAdjacent bundle.normalizedFixedCircle bundle.normalizedFixed
          (bundle.pieces bundle.selectedSlot bundle.selectedSign)
          bundle.normalizedFixedFunction
          (bundle.functions bundle.selectedSlot bundle.selectedSign) :=
              PresentedRowAdjacencyGeometry.left C D T N h k x bundle C' p hp selected_odometer
              r' j e hr' h0 heq hc hs
  obtain ⟨a13, a12, a31, a23, a01, a02, a03, sum12, sum13, sum23⟩ :=
    P4387T1ParentSlopeNormalForms q cfg
  simp only [q] at a13 a12 a31 a23 a01 a02 a03 sum12 sum13 sum23
  have fin2 : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
  have fin3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
  -- Keep the table's predecessor, parent slot, rotation, and directed order.
  have presentedAdjacency :
    let S := bundle.pieces bundle.selectedSlot bundle.selectedSign
    let f := bundle.functions bundle.selectedSlot bundle.selectedSign
    let directed := fun (z : P3996T1SRowParameters)
        (A B : BandCircle) (V W : ProtoTile) (f g : PartialOdometer)
        (pV pW : ℝ × ℝ) =>
      ProperBandQuadruple z.predecessor ∧
      z.predecessor 0 = A.1.1 ∧
      z.predecessor z.parentSlot.succ = B.1.1 ∧
      TileCentroid W - TileCentroid V =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
             BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      pW - pV = (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
          (BandVectors.2 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
           BandVectors.2 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      SubtileLatticeAdjacent A B V W f g
    match P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedRoot placement.layout row with
    | none => C' = bundle.normalizedFixedCircle ∧
        LeftLatticeAdjacent bundle.normalizedFixedCircle bundle.normalizedFixed S
          bundle.normalizedFixedFunction f
    | some z =>
        if z.childIsExterior then
          directed z bundle.normalizedFixedCircle C' bundle.normalizedFixed S
            bundle.normalizedFixedFunction f bundle.normalizedFixedSlope p
        else
          directed z C' bundle.normalizedFixedCircle S bundle.normalizedFixed
            f bundle.normalizedFixedFunction p bundle.normalizedFixedSlope :=
                PresentedAdjacencyConclusion.presentedAdjacency C D T N h k x bundle placement
                row r i s C' p hp outer selected_centroid fixed_centroid central_centroid
                selected_circle fixed_circle selected_slope fixed_slope selected_odometer
                row_geometry sub left a13 a31 a01 a02 a03 sum12 sum13 sum23
  exact presentedAdjacency


end ApollonianSuperharmonic

end
