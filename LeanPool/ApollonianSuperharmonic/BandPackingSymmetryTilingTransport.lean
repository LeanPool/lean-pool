/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretationCovariance
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance

-- [TABLET NODE: BandPackingSymmetryTilingTransport]

/-!
# BandPackingSymmetryTilingTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TilingTransportProof

private theorem quarter_translate :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation T x) =
            TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x)
    ) := by
  classical
  intro T x
  cases T with
  | mk cells anchor =>
    have map : (fun z : GaussianInt => GaussianQuarterTurn (z + x) - 1) =
        (fun z : GaussianInt => (GaussianQuarterTurn z - 1) +
          GaussianQuarterTurn x) := by
      funext z
      ext <;> simp [GaussianQuarterTurn, add_comm]; ring
    apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
      ProtoTile.mk c d)
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        Finset.image_image, Function.comp_def, map]
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        GaussianQuarterTurn, add_comm]

private theorem quarter_symmetryAt181 :
    (by
      classical
      exact
        ∀ T : ProtoTile, QuarterTurnSymmetric T ↔ QuarterTurnSymmetric (TileQuarterTurn T)
    ) := by
  classical
  intro T
  unfold QuarterTurnSymmetric
  have first := TileQuarterTurnFormulas T
  simp only [first.2.2.2.1, first.2.2.2.2.1]
  simp only [Set.mem_image]
  constructor
  · intro h p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      refine ⟨((TileCentroid T).1 - (q.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (q.1 - (TileCentroid T).1)), (h q).mp hq, ?_⟩
      dsimp
      ring
    · intro hp
      rcases hp with ⟨q, hq, hpq⟩
      have heq' := congrArg Prod.fst hpq
      have heq'' := congrArg Prod.snd hpq
      dsimp at heq' heq''
      have qeq : q =
          ((TileCentroid T).1 - ((-p.1) - (TileCentroid T).2),
            (TileCentroid T).2 + (p.2 - (TileCentroid T).1)) := by
        apply Prod.ext
        · dsimp
          linarith [heq'']
        · dsimp
          linarith [heq']
      refine ⟨(p.2, -p.1), ?_, ?_⟩
      · apply (h (p.2, -p.1)).mpr
        exact qeq ▸ hq
      · dsimp
        ring
  · intro h p
    constructor
    · intro hp
      have hh := h (-p.2, p.1)
      have hr : (-p.2, p.1) ∈ (fun p => (-p.2, p.1)) ''
          TileRealization T := ⟨p, hp, rfl⟩
      rcases hh.mp hr with ⟨q, hq, heq⟩
      have heq' := congrArg Prod.fst heq
      have heq'' := congrArg Prod.snd heq
      have qeq : q =
          ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
            (TileCentroid T).2 + (p.1 - (TileCentroid T).1)) := by
        apply Prod.ext <;> dsimp at heq' heq'' ⊢ <;> linarith
      rw [← qeq]
      exact hq
    · intro hp
      have hh := h (-p.2, p.1)
      have hc : ∃ x ∈ TileRealization T,
          (-x.2, x.1) =
            (-(TileCentroid T).2 - ((-p.2, p.1).2 - (TileCentroid T).1),
              (TileCentroid T).1 + ((-p.2, p.1).1 -
                -(TileCentroid T).2)) := by
        refine ⟨((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
          (TileCentroid T).2 + (p.1 - (TileCentroid T).1)), hp, ?_⟩
        dsimp
        ring_nf
      rcases hh.mpr hc with ⟨q, hq, heq⟩
      have heq' := congrArg Prod.fst heq
      have heq'' := congrArg Prod.snd heq
      dsimp at heq' heq''
      rw [show q = p by apply Prod.ext <;> linarith] at hq
      exact hq

private theorem image_subsingletonAt247 :
    (by
      classical
      exact
        ∀ (f : GaussianInt → GaussianInt), Function.Injective f → ∀ (A : Set GaussianInt), ∀ (B :
            Set GaussianInt), (A ∩ B).Subsingleton ↔ (f '' A ∩ f '' B).Subsingleton
    ) := by
  classical
  intro f hf A B
  constructor
  · intro h x hx y hy
    rcases hx with ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rcases hy with ⟨⟨c, hc, rfl⟩, ⟨d, hd, hcd⟩⟩
    have hab' : a = b := hf hab.symm
    have hcd' : c = d := hf hcd.symm
    subst b
    subst d
    exact congrArg f (h ⟨ha, hb⟩ ⟨hc, hd⟩)
  · intro h a ha b hb
    apply hf
    exact h ⟨⟨a, ha.1, rfl⟩, ⟨a, ha.2, rfl⟩⟩
      ⟨⟨b, hb.1, rfl⟩, ⟨b, hb.2, rfl⟩⟩

private theorem quarter_symmetryAt307 :
    (by
      classical
      exact
        ∀ T : ProtoTile, QuarterTurnSymmetric T ↔ QuarterTurnSymmetric (TileQuarterTurn T)
    ) := by
  classical
  intro T
  unfold QuarterTurnSymmetric
  have first := TileQuarterTurnFormulas T
  simp only [first.2.2.2.1, first.2.2.2.2.1]
  simp only [Set.mem_image]
  constructor
  · intro h p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      refine ⟨((TileCentroid T).1 - (q.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (q.1 - (TileCentroid T).1)), (h q).mp hq, ?_⟩
      dsimp
      ring
    · intro hp
      rcases hp with ⟨q, hq, hpq⟩
      have heq' := congrArg Prod.fst hpq
      have heq'' := congrArg Prod.snd hpq
      dsimp at heq' heq''
      have qeq : q =
          ((TileCentroid T).1 - ((-p.1) - (TileCentroid T).2),
            (TileCentroid T).2 + (p.2 - (TileCentroid T).1)) := by
        apply Prod.ext
        · dsimp
          linarith [heq'']
        · dsimp
          linarith [heq']
      refine ⟨(p.2, -p.1), ?_, ?_⟩
      · apply (h (p.2, -p.1)).mpr
        exact qeq ▸ hq
      · dsimp
        ring
  · intro h p
    constructor
    · intro hp
      have hh := h (-p.2, p.1)
      have hr : (-p.2, p.1) ∈ (fun p => (-p.2, p.1)) ''
          TileRealization T := ⟨p, hp, rfl⟩
      rcases hh.mp hr with ⟨q, hq, heq⟩
      have heq' := congrArg Prod.fst heq
      have heq'' := congrArg Prod.snd heq
      have qeq : q =
          ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
            (TileCentroid T).2 + (p.1 - (TileCentroid T).1)) := by
        apply Prod.ext <;> dsimp at heq' heq'' ⊢ <;> linarith
      rw [← qeq]
      exact hq
    · intro hp
      have hh := h (-p.2, p.1)
      have hc : ∃ x ∈ TileRealization T,
          (-x.2, x.1) =
            (-(TileCentroid T).2 - ((-p.2, p.1).2 - (TileCentroid T).1),
              (TileCentroid T).1 + ((-p.2, p.1).1 -
                -(TileCentroid T).2)) := by
        refine ⟨((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
          (TileCentroid T).2 + (p.1 - (TileCentroid T).1)), hp, ?_⟩
        dsimp
        ring_nf
      rcases hh.mpr hc with ⟨q, hq, heq⟩
      have heq' := congrArg Prod.fst heq
      have heq'' := congrArg Prod.snd heq
      dsimp at heq' heq''
      rw [show q = p by apply Prod.ext <;> linarith] at hq
      exact hq

private theorem reflection_symmetry :
    (by
      classical
      exact
        ∀ T : ProtoTile, QuarterTurnSymmetric T ↔ QuarterTurnSymmetric (TileReflection T)
    ) := by
  classical
  intro T
  unfold QuarterTurnSymmetric
  have first := TileReflectionFormulas T
  simp only [first.2.2.2.1, first.2.2.2.2.1]
  simp only [Set.mem_image]
  constructor
  · intro h p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      let y := ((TileCentroid T).1 + q.2 - (TileCentroid T).2,
        (TileCentroid T).2 - q.1 + (TileCentroid T).1)
      refine ⟨y, ?_, ?_⟩
      · apply (h y).mpr
        convert hq using 1; dsimp [y]; ring
      · dsimp [y]
        ring_nf
    · intro hp
      rcases hp with ⟨q, hq, hpq⟩
      have first_eq := congrArg Prod.fst hpq
      have second_eq := congrArg Prod.snd hpq
      dsimp at first_eq second_eq
      refine ⟨(p.1, -p.2), ?_, ?_⟩
      · have hq' := (h q).mp hq
        convert hq' using 1
        apply Prod.ext <;> dsimp at first_eq second_eq ⊢ <;>
          ring_nf at first_eq second_eq ⊢ <;> linarith
      · apply Prod.ext <;> dsimp; linarith
  · intro h p
    constructor
    · intro hp
      let target := ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (p.1 - (TileCentroid T).1))
      have hc : ∃ x ∈ TileRealization T,
          (x.1, -x.2) =
            ((TileCentroid T).1 - ((target.1, -target.2).2 -
              -(TileCentroid T).2),
              -(TileCentroid T).2 + ((target.1, -target.2).1 -
                (TileCentroid T).1)) := by
        refine ⟨p, hp, ?_⟩
        dsimp [target]
        ring
      rcases (h (target.1, -target.2)).mpr hc with ⟨q, hq, heq⟩
      have first_eq := congrArg Prod.fst heq
      have second_eq := congrArg Prod.snd heq
      have qeq : q = target := by
        apply Prod.ext <;> dsimp at first_eq second_eq ⊢ <;> linarith
      change target ∈ TileRealization T
      exact qeq ▸ hq
    · intro hp
      let target := ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (p.1 - (TileCentroid T).1))
      have hc : ∃ x ∈ TileRealization T,
          (x.1, -x.2) = (target.1, -target.2) :=
        ⟨target, hp, rfl⟩
      rcases (h (target.1, -target.2)).mp hc with ⟨q, hq, heq⟩
      have first_eq := congrArg Prod.fst heq
      have second_eq := congrArg Prod.snd heq
      have qeq : q = p := by
        apply Prod.ext <;> dsimp [target] at first_eq second_eq ⊢ <;> linarith
      exact qeq ▸ hq

private theorem image_subsingletonAt436 :
    (by
      classical
      exact
        ∀ (f : GaussianInt → GaussianInt), Function.Injective f → ∀ (A : Set GaussianInt), ∀ (B :
            Set GaussianInt), (A ∩ B).Subsingleton ↔ (f '' A ∩ f '' B).Subsingleton
    ) := by
  classical
  intro f hf A B
  constructor
  · intro h x hx y hy
    rcases hx with ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rcases hy with ⟨⟨c, hc, rfl⟩, ⟨d, hd, hcd⟩⟩
    have hab' : a = b := hf hab.symm
    have hcd' : c = d := hf hcd.symm
    subst b
    subst d
    exact congrArg f (h ⟨ha, hb⟩ ⟨hc, hd⟩)
  · intro h a ha b hb
    apply hf
    exact h ⟨⟨a, ha.1, rfl⟩, ⟨a, ha.2, rfl⟩⟩
      ⟨⟨b, hb.1, rfl⟩, ⟨b, hb.2, rfl⟩⟩

end TilingTransportProof

namespace TilingTransportDetails

private theorem quarter_injective :
    (by
      classical
      exact
        Function.Injective GaussianQuarterTurn ) := by
  classical
  intro a b hab
  apply Zsqrtd.ext
  · simpa [GaussianQuarterTurn] using
      congrArg (fun z : GaussianInt => z.im) hab
  · simpa [GaussianQuarterTurn] using
      congrArg (fun z : GaussianInt => z.re) hab

private theorem reflection_injective :
    (by
      classical
      exact
        Function.Injective (fun z : GaussianInt => -GaussianReflection z) ) := by
  classical
  intro a b hab
  apply Zsqrtd.ext
  · simpa [GaussianReflection] using
      congrArg (fun z : GaussianInt => z.re) hab
  · simpa [GaussianReflection] using
      congrArg (fun z : GaussianInt => z.im) hab

private theorem composite_injective :
    (by
      classical
      exact
        Function.Injective (fun z : GaussianInt => GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianReflection z))) ) := by
  classical
  intro a b hab
  apply Zsqrtd.ext
  · simpa [GaussianQuarterTurn, GaussianReflection] using
      congrArg (fun z : GaussianInt => z.re) hab
  · simpa [GaussianQuarterTurn, GaussianReflection] using
      congrArg (fun z : GaussianInt => z.im) hab

end TilingTransportDetails

namespace TilingTransportCases

private theorem negation :
    (∀ T, LatticeTile T ↔
          LatticeTile (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)) ∧
        (∀ T, TileArea (BandPackingSymmetryTileAction BandPackingSymmetry.negate T) = TileArea T) ∧
        (∀ T U,
          BandPackingSymmetryTileAction BandPackingSymmetry.negate (TileCellComplement T U) =
            TileCellComplement (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)
              (BandPackingSymmetryTileAction BandPackingSymmetry.negate U)) ∧
        (∀ T U, TileTouching T U ↔
          TileTouching (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)
            (BandPackingSymmetryTileAction BandPackingSymmetry.negate U)) ∧
        (∀ T, QuarterTurnSymmetric T ↔
          QuarterTurnSymmetric (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)) ∧
        (∀ T U V, TouchingTriple T U V ↔
          TouchingTriple (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)
            (BandPackingSymmetryTileAction BandPackingSymmetry.negate U)
            (BandPackingSymmetryTileAction BandPackingSymmetry.negate V)) ∧
        (∀ T v,
          BandPackingSymmetryTileAction BandPackingSymmetry.negate (TileTranslation T v) =
            TileTranslation (BandPackingSymmetryTileAction BandPackingSymmetry.negate T)
              (BandPackingSymmetryVectorAction BandPackingSymmetry.negate v)) ∧
        (∀ T, FootprintVertices (BandPackingSymmetryTileAction BandPackingSymmetry.negate T) =
          BandPackingSymmetryVectorAction BandPackingSymmetry.negate '' FootprintVertices T) ∧
        (∀ T, FootprintEdges (BandPackingSymmetryTileAction BandPackingSymmetry.negate T) =
          (fun e : Finset GaussianInt =>
            e.image (BandPackingSymmetryVectorAction BandPackingSymmetry.negate)) ''
                FootprintEdges T) ∧
        (∀ T U,
          (FootprintVertices T ∩ FootprintVertices U).Subsingleton ↔
            (FootprintVertices (BandPackingSymmetryTileAction BandPackingSymmetry.negate T) ∩
              FootprintVertices
                (BandPackingSymmetryTileAction BandPackingSymmetry.negate U)).Subsingleton) ∧
        ∀ (S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
            (o : PeriodicSubtileIndex),
          BandPackingSymmetryTileAction BandPackingSymmetry.negate
              (SubtileOccurrenceInterpretation S u v o) =
            SubtileOccurrenceInterpretation
              (fun i s => BandPackingSymmetryTileAction BandPackingSymmetry.negate (S i s))
              (BandPackingSymmetryVectorAction BandPackingSymmetry.negate u)
              (BandPackingSymmetryVectorAction BandPackingSymmetry.negate v) o := by
  have quarter_symmetry := TilingTransportProof.quarter_symmetryAt181
  have image_subsingleton (f : GaussianInt → GaussianInt)
      (hf : Function.Injective f) (A B : Set GaussianInt) :=
          TilingTransportProof.image_subsingletonAt247 f hf A B
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T
    exact (TileDiskAreaCovariance T 0).2.1
  · intro T
    exact (TileDiskAreaCovariance T 0).2.2.2.2.1
  · intro T U
    exact (TileCellComplementCovariance T U 0).2.1
  · intro T U
    exact (TileTouchingCovariance T U 0).2.1
  · intro T
    exact quarter_symmetry T
  · intro T U V
    exact (TouchingTripleCovariance T U V 0).2.1
  · intro T v
    exact (TilingTransportProof.quarter_translate) T v
  · intro T
    have h := (TileQuarterTurnFormulas T).2.2.2.2.2.1
    change FootprintVertices (TileQuarterTurn T) =
      GaussianQuarterTurn '' FootprintVertices T
    exact h
  · intro T
    simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    change FootprintEdges (TileQuarterTurn T) =
      (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
        FootprintEdges T
    exact (TileQuarterTurnFormulas T).2.2.2.2.2.2.1
  · intro T U
    simp only [BandPackingSymmetryTileAction]
    rw [(TileQuarterTurnFormulas T).2.2.2.2.2.1,
      (TileQuarterTurnFormulas U).2.2.2.2.2.1]
    exact
      (image_subsingleton GaussianQuarterTurn (TilingTransportDetails.quarter_injective)
        (FootprintVertices T) (FootprintVertices U))
  · intro S u v o
    change TileQuarterTurn (SubtileOccurrenceInterpretation S u v o) = _
    exact (SubtileOccurrenceInterpretationCovariance S u v 0 o).2.1

private theorem conjugation :
    (∀ T, LatticeTile T ↔
          LatticeTile (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)) ∧
        (∀ T, TileArea (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T) = TileArea
            T) ∧
        (∀ T U,
          BandPackingSymmetryTileAction BandPackingSymmetry.conjugate (TileCellComplement T U) =
            TileCellComplement (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)
              (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate U)) ∧
        (∀ T U, TileTouching T U ↔
          TileTouching (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)
            (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate U)) ∧
        (∀ T, QuarterTurnSymmetric T ↔
          QuarterTurnSymmetric (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)) ∧
        (∀ T U V, TouchingTriple T U V ↔
          TouchingTriple (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)
            (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate U)
            (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate V)) ∧
        (∀ T v,
          BandPackingSymmetryTileAction BandPackingSymmetry.conjugate (TileTranslation T v) =
            TileTranslation (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T)
              (BandPackingSymmetryVectorAction BandPackingSymmetry.conjugate v)) ∧
        (∀ T, FootprintVertices (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T) =
          BandPackingSymmetryVectorAction BandPackingSymmetry.conjugate '' FootprintVertices T) ∧
        (∀ T, FootprintEdges (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T) =
          (fun e : Finset GaussianInt =>
            e.image (BandPackingSymmetryVectorAction BandPackingSymmetry.conjugate)) ''
                FootprintEdges T) ∧
        (∀ T U,
          (FootprintVertices T ∩ FootprintVertices U).Subsingleton ↔
            (FootprintVertices (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate T) ∩
              FootprintVertices
                (BandPackingSymmetryTileAction BandPackingSymmetry.conjugate U)).Subsingleton) ∧
        ∀ (S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
            (o : PeriodicSubtileIndex),
          BandPackingSymmetryTileAction BandPackingSymmetry.conjugate
              (SubtileOccurrenceInterpretation S u v o) =
            SubtileOccurrenceInterpretation
              (fun i s => BandPackingSymmetryTileAction BandPackingSymmetry.conjugate (S i s))
              (BandPackingSymmetryVectorAction BandPackingSymmetry.conjugate u)
              (BandPackingSymmetryVectorAction BandPackingSymmetry.conjugate v) o := by
  have quarter_symmetry := TilingTransportProof.quarter_symmetryAt307
  have image_subsingleton (f : GaussianInt → GaussianInt)
      (hf : Function.Injective f) (A B : Set GaussianInt) :=
          TilingTransportProof.image_subsingletonAt436 f hf A B
  have reflection_injective : Function.Injective
      (fun z : GaussianInt => -GaussianReflection z) :=
          TilingTransportDetails.reflection_injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T
    exact ((TileDiskAreaCovariance T 0).2.2.1).trans
      ((TileDiskAreaCovariance (TileReflection T) 0).2.1.trans
        ((TileDiskAreaCovariance (TileQuarterTurn (TileReflection T)) 0).2.1))
  · intro T
    exact (TileDiskAreaCovariance (TileQuarterTurn (TileReflection T)) 0).2.2.2.2.1.trans
      ((TileDiskAreaCovariance (TileReflection T) 0).2.2.2.2.1.trans
        (TileDiskAreaCovariance T 0).2.2.2.2.2)
  · intro T U
    simp only [BandPackingSymmetryTileAction]
    rw [(TileCellComplementCovariance T U 0).2.2,
      (TileCellComplementCovariance (TileReflection T) (TileReflection U) 0).2.1,
      (TileCellComplementCovariance (TileQuarterTurn (TileReflection T))
        (TileQuarterTurn (TileReflection U)) 0).2.1]
  · intro T U
    simp only [BandPackingSymmetryTileAction]
    exact (TileTouchingCovariance T U 0).2.2.trans
      ((TileTouchingCovariance (TileReflection T) (TileReflection U) 0).2.1.trans
        ((TileTouchingCovariance (TileQuarterTurn (TileReflection T))
          (TileQuarterTurn (TileReflection U)) 0).2.1))
  · intro T
    simpa [BandPackingSymmetryTileAction] using
      ((TilingTransportProof.reflection_symmetry) T).trans
        ((quarter_symmetry (TileReflection T)).trans
          (quarter_symmetry (TileQuarterTurn (TileReflection T))))
  · intro T U V
    simp only [BandPackingSymmetryTileAction]
    exact (TouchingTripleCovariance T U V 0).2.2.trans
      ((TouchingTripleCovariance (TileReflection T) (TileReflection U)
        (TileReflection V) 0).2.1.trans
        ((TouchingTripleCovariance (TileQuarterTurn (TileReflection T))
          (TileQuarterTurn (TileReflection U))
          (TileQuarterTurn (TileReflection V)) 0).2.1))
  · intro T v
    simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    cases T with
    | mk cells anchor =>
      apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt => ProtoTile.mk c d)
      · simp only [TileQuarterTurn, TileReflection, Int.reduceNeg, TileTranslation,
          GaussianTranslation, Finset.image_image, Function.comp_def]
        congr 1
        funext x
        ext <;> simp [GaussianQuarterTurn, GaussianReflection]; ring
      · simp only [GaussianQuarterTurn, Int.reduceNeg, TileQuarterTurn, TileReflection,
          GaussianReflection, TileTranslation, GaussianTranslation, Zsqrtd.re_add,
          Zsqrtd.im_add, neg_add_rev, neg_neg]
        ext <;> simp []; ring
  · intro T
    simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection T))).2.2.2.2.2.1,
      (TileQuarterTurnFormulas (TileReflection T)).2.2.2.2.2.1,
      (TileReflectionFormulas T).2.2.2.2.2.1]
    simp only [Set.image_image]
    congr 1
  · intro T
    simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection T))).2.2.2.2.2.2.1,
      (TileQuarterTurnFormulas (TileReflection T)).2.2.2.2.2.2.1,
      (TileReflectionFormulas T).2.2.2.2.2.2.1]
    simp only [Set.image_image]
    congr 1
    funext e
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
      refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
      ext <;> simp [GaussianQuarterTurn, GaussianReflection]
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      refine Finset.mem_image.mpr
        ⟨GaussianQuarterTurn (GaussianReflection x), ?_, ?_⟩
      · refine Finset.mem_image.mpr
          ⟨GaussianReflection x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
      · ext <;> simp [GaussianQuarterTurn, GaussianReflection]
  · intro T U
    simp only [BandPackingSymmetryTileAction]
    rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection T))).2.2.2.2.2.1,
      (TileQuarterTurnFormulas (TileReflection T)).2.2.2.2.2.1,
      (TileReflectionFormulas T).2.2.2.2.2.1,
      (TileQuarterTurnFormulas (TileQuarterTurn (TileReflection U))).2.2.2.2.2.1,
      (TileQuarterTurnFormulas (TileReflection U)).2.2.2.2.2.1,
      (TileReflectionFormulas U).2.2.2.2.2.1]
    simp only [Set.image_image]
    exact image_subsingleton (fun z : GaussianInt =>
      GaussianQuarterTurn (GaussianQuarterTurn (GaussianReflection z)))
      (TilingTransportDetails.composite_injective) _ _
  · intro S u v o
    simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    rw [(SubtileOccurrenceInterpretationCovariance S u v 0 o).2.2,
      (SubtileOccurrenceInterpretationCovariance
        (fun i s => TileReflection (S i s)) (GaussianReflection u)
        (GaussianReflection v) 0 o).2.1,
      (SubtileOccurrenceInterpretationCovariance
        (fun i s => TileQuarterTurn (TileReflection (S i s)))
        (GaussianQuarterTurn (GaussianReflection u))
        (GaussianQuarterTurn (GaussianReflection v)) 0 o).2.1]
    congr 1

end TilingTransportCases

theorem BandPackingSymmetryTilingTransport (g : BandPackingSymmetry) :
    (∀ T, LatticeTile T ↔
      LatticeTile (BandPackingSymmetryTileAction g T)) ∧
    (∀ T, TileArea (BandPackingSymmetryTileAction g T) = TileArea T) ∧
    (∀ T U,
      BandPackingSymmetryTileAction g (TileCellComplement T U) =
        TileCellComplement (BandPackingSymmetryTileAction g T)
          (BandPackingSymmetryTileAction g U)) ∧
    (∀ T U, TileTouching T U ↔
      TileTouching (BandPackingSymmetryTileAction g T)
        (BandPackingSymmetryTileAction g U)) ∧
    (∀ T, QuarterTurnSymmetric T ↔
      QuarterTurnSymmetric (BandPackingSymmetryTileAction g T)) ∧
    (∀ T U V, TouchingTriple T U V ↔
      TouchingTriple (BandPackingSymmetryTileAction g T)
        (BandPackingSymmetryTileAction g U)
        (BandPackingSymmetryTileAction g V)) ∧
    (∀ T v,
      BandPackingSymmetryTileAction g (TileTranslation T v) =
        TileTranslation (BandPackingSymmetryTileAction g T)
          (BandPackingSymmetryVectorAction g v)) ∧
    (∀ T, FootprintVertices (BandPackingSymmetryTileAction g T) =
      BandPackingSymmetryVectorAction g '' FootprintVertices T) ∧
    (∀ T, FootprintEdges (BandPackingSymmetryTileAction g T) =
      (fun e : Finset GaussianInt =>
        e.image (BandPackingSymmetryVectorAction g)) '' FootprintEdges T) ∧
    (∀ T U,
      (FootprintVertices T ∩ FootprintVertices U).Subsingleton ↔
        (FootprintVertices (BandPackingSymmetryTileAction g T) ∩
          FootprintVertices
            (BandPackingSymmetryTileAction g U)).Subsingleton) ∧
    ∀ (S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
        (o : PeriodicSubtileIndex),
      BandPackingSymmetryTileAction g
          (SubtileOccurrenceInterpretation S u v o) =
        SubtileOccurrenceInterpretation
          (fun i s => BandPackingSymmetryTileAction g (S i s))
          (BandPackingSymmetryVectorAction g u)
          (BandPackingSymmetryVectorAction g v) o := by
-- BODY
  induction g with
  | identity =>
      simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | shift w =>
      simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
  | negate => exact TilingTransportCases.negation
  | conjugate => exact TilingTransportCases.conjugation
  | comp g h ihg ihh =>
      rcases ihg with ⟨lg, ag, cg, tg, sg, qg, vg, fg, eg, pg, og⟩
      rcases ihh with ⟨lh, ah, ch, th, sh, qh, vh, fh, eh, ph, oh⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro T
        exact (lh T).trans (lg _)
      · intro T
        change TileArea (BandPackingSymmetryTileAction g
          (BandPackingSymmetryTileAction h T)) = TileArea T
        rw [ag, ah]
      · intro T U
        simp only [BandPackingSymmetryTileAction]
        rw [ch, cg]
      · intro T U
        exact (th T U).trans (tg _ _)
      · intro T
        exact (sh T).trans (sg _)
      · intro T U V
        exact (qh T U V).trans (qg _ _ _)
      · intro T v
        simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
        rw [vh, vg]
      · intro T
        simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
        rw [fg, fh]
        ext x
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          simpa [BandPackingSymmetryVectorAction] using ⟨z, hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          refine ⟨BandPackingSymmetryVectorAction h z, ?_, rfl⟩
          exact ⟨z, hz, rfl⟩
      · intro T
        simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
        rw [eg, eh]
        simp only [Set.image_image, Finset.image_image]
        congr 1
      · intro T U
        change (FootprintVertices T ∩ FootprintVertices U).Subsingleton ↔
          (FootprintVertices (BandPackingSymmetryTileAction g
            (BandPackingSymmetryTileAction h T)) ∩
            FootprintVertices (BandPackingSymmetryTileAction g
              (BandPackingSymmetryTileAction h U))).Subsingleton
        exact (ph T U).trans (pg _ _)
      · intro S u v o
        simp only [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
        rw [oh, og]

end ApollonianSuperharmonic

end
