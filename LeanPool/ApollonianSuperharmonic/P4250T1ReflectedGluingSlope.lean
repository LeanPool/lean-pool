/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidBounds

public import LeanPool.ApollonianSuperharmonic.P4250T1SlopeOffset
public import LeanPool.ApollonianSuperharmonic.P4250T1DefinedHalfIntegralSlope
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.TileOdometerCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport

-- [TABLET NODE: P4250T1ReflectedGluingSlope]

/-!
# P4250T1ReflectedGluingSlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ReflectedGluingGeometry

private theorem hpositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q (0 : Fin
            3).succ).1) ) := by
  classical
  intro q cfg
  have hn := cfg.noLine (1 : Fin 4)
  have hp := (ProperBandCurvatureStructure q cfg.proper).2.1 (0 : Fin 3)
  have hp' : 0 ≤ (q (1 : Fin 4)).1 := by simpa using hp
  change (q (1 : Fin 4)).1 ≠ 0 at hn
  change 0 < (q (1 : Fin 4)).1
  omega

private theorem hpchild :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real ×
            Real), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 +
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i
            + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (pchild : ℝ × ℝ), (PartialOdometerSlope (h (0 : Fin (3 : ℕ)) true) = some pchild) →
            (pchild = s0 + P4250T1SlopeOffset v)) ) := by
  classical
  intro q h s0 hp i v pchild hchild
  have he := hp 0 true
  rw [hchild] at he
  simpa [i, v] using Option.some.inj he

private theorem htwo_s0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s0 : Real × Real),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (pchild : ℝ × ℝ), ∀ (ai : GaussianInt), ((2 : ℝ) • pchild = GaussianRealPoint ai) →
            ((pchild = s0 + P4250T1SlopeOffset v) → ((2 : Real) • s0 = GaussianRealPoint (ai -
            (v + GaussianQuarterTurn v)))) ) := by
  classical
  intro q s0 i v pchild ai hhalf hpchild
  have hcoords := congrArg (fun x : Real × Real => (2 * x.1, 2 * x.2)) hhalf
  have hpc := congrArg Prod.fst hpchild
  have hpi := congrArg Prod.snd hpchild
  apply Prod.ext <;>
    simp [GaussianRealPoint, P4250T1SlopeOffset, GaussianQuarterTurn, v] at hcoords hpc hpi ⊢
        <;>
    linarith

private theorem hcenterIntegral :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (Finset.Nonempty (cert.P (0 : Fin (3 : ℕ)) true).cells) → (∃ u : GaussianInt, (2
            : Real) • TileCentroid T = GaussianRealPoint u) ) := by
  classical
  intro q cfg C T cert hcells
  have hroot : BandPrototile (q 0) T := by
    apply BandPrototile.decompose cfg.proper
      (fun j s => (cert.outer_occurrence j s).1)
    · exact cert.outer_union
    · intro j s
      exact (cert.outer_occurrence j s).2.1
    · intro j s
      exact (cert.outer_occurrence j s).2.2
  have hrootne : T.cells.Nonempty := by
    obtain ⟨z, hz⟩ := hcells
    exact ⟨z, (cert.outer_union z).2 ⟨0, true, hz⟩⟩
  exact BandPrototileCentroidBounds.integralDoubleCenter T hrootne
    (BandPrototileCentralSymmetry (q 0) T hroot)

private theorem positive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (j : Fin 3),
            0 < (q j.succ).1) ) := by
  classical
  intro q cfg j
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 j
  have hne := cfg.noLine j.succ
  omega

private theorem reflectedChild :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → ((∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 :
            ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt), ((2 : ℝ) • TileCentroid T = GaussianRealPoint
            u) → (
        let a := ai - (v + GaussianQuarterTurn v)
        (GaussianRealPoint a = (2 : Real) • s0) → ((∀ (j : Fin 3), 0 < (q j.succ).1) → (
        let reflectedK (j : Fin 3) (s : Bool) : PartialOdometer :=
          PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (h j (!s))) u a 0
        ∀ (j : Fin 3), ∀ (s : Bool), TileOdometer (q j.succ) (cert.P j s) (reflectedK j s) ∧
            PartialOdometerSlope (reflectedK j s) = some (s0 + (if s = true then (1 : Real) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j +
            1).succ))))))))) ) := by
  classical
  intro q cfg C T cert h s0 ho hp i v ai u hu a ha positive reflectedK j s
  let U := cert.P j (!s)
  let V := cert.P j s
  let k := reflectedK j s
  have hhalf := (TileOdometerCentralSymmetry (q j.succ) U (h j (!s))
    (ho j (!s))).1
  have hk : TileOdometer (q j.succ) (TileTranslation (TileHalfTurn U) u) k := by
    exact TileOdometerAffineTranslation (q j.succ) (TileHalfTurn U)
      (PartialOdometerHalfTurn (h j (!s))) u a 0 hhalf
  have hUband : BandPrototile (q j.succ) U :=
    TileOdometerBandPrototile _ _ _ (ho j (!s))
  have hVband : BandPrototile (q j.succ) V :=
    (cert.outer_occurrence j s).1
  have hcentSum : TileCentroid V + TileCentroid U =
      (2 : Real) • TileCentroid T := by
    have hvs := (cert.outer_occurrence j s).2.2
    have hus := (cert.outer_occurrence j (!s)).2.2
    cases s <;> apply Prod.ext
    all_goals
      first
      | (have h1 := congrArg Prod.fst hvs
         have h2 := congrArg Prod.fst hus
         dsimp at h1 h2 ⊢
         linarith)
      | (have h1 := congrArg Prod.snd hvs
         have h2 := congrArg Prod.snd hus
         dsimp at h1 h2 ⊢
         linarith)
  have hcent : TileCentroid (TileTranslation (TileHalfTurn U) u) =
      TileCentroid V := by
    rw [(TileTranslationFormulas (TileHalfTurn U) u).2.2.2.2.1,
      (TileHalfTurnFormulas U).2.2.2.2.2.2.2.1]
    have hr := congrArg Prod.fst hcentSum
    have hi := congrArg Prod.snd hcentSum
    have hur := congrArg Prod.fst hu
    have hui := congrArg Prod.snd hu
    simp only [Prod.smul_fst, smul_eq_mul, GaussianRealPoint, Int.reduceNeg,
        GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.smul_snd] at hur hui
    rw [← GaussianInt.intCast_re u] at hur
    rw [← GaussianInt.intCast_im u] at hui
    dsimp at hr hi
    apply Prod.ext <;> dsimp <;> linarith
  have hsupp := (BandPrototileCentroidUnique (q j.succ)
    (TileTranslation (TileHalfTurn U) u) V
    (BandPrototileTranslation (q j.succ) (TileHalfTurn U) u
      (TileOdometerBandPrototile _ _ _ hhalf)) hVband hcent).1
  have hkV : TileOdometer (q j.succ) V k := by
    exact PositiveCurvatureTileOdometerSupportTransport (q j.succ)
      (TileTranslation (TileHalfTurn U) u) V k (positive j) hk hVband hsupp
  have hare : (a.re : Real) = 2 * s0.1 := by
    have hh := congrArg Prod.fst ha
    simpa [GaussianRealPoint] using hh
  have haim : (a.im : Real) = 2 * s0.2 := by
    have hh := congrArg Prod.snd ha
    simpa [GaussianRealPoint] using hh
  have hsl : PartialOdometerSlope k = some
      (s0 + (if s = true then (1 : Real) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ)))) := by
    rw [(PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn (h j (!s))) u a 0).2.2.2.2.2,
      (PartialOdometerHalfTurnFormulas (h j (!s))).2.2.2.2.2.2,
      hp j (!s)]
    simp only [Option.map_some]
    congr 1
    cases s <;> apply Prod.ext <;>
      simp [] at hare haim ⊢ <;> linarith
  exact ⟨hkV, hsl⟩

private theorem childNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (q i.succ) (cert.P i s) (h i s)) → ((∀ (j : Fin 3), 0 < (q j.succ).1) →
            (∀ (j : Fin 3), ∀ (s : Bool), (cert.P j s).cells.Nonempty)) ) := by
  classical
  intro q cfg C T cert h ho positive j s
  rcases P4250T1DefinedHalfIntegralSlope (q j.succ) (cert.P j s)
    (h j s) (positive j) (ho j s) with ⟨p, b, hp, hb, hne⟩
  exact hne

private theorem rootNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (j : Fin 3), ∀ (s : Bool), (cert.P j s).cells.Nonempty) → (T.cells.Nonempty) )
            := by
  classical
  intro q cfg C T cert childNonempty
  obtain ⟨z, hz⟩ := childNonempty 0 true
  exact ⟨z, (cert.outer_union z).2 ⟨0, true, hz⟩⟩

private theorem rootFoot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (j : Fin 3), ∀ (s : Bool), (cert.P j s).cells.Nonempty) → ((T.cells.Nonempty)
            → (∀ z, z ∈ FootprintVertices T ↔ ∃ j s, z ∈ FootprintVertices (cert.P j s))) ) := by
  classical
  intro q cfg C T cert childNonempty rootNonempty z
  simp only [FootprintVertices, ite_eq_left rootNonempty, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hcorner⟩
    obtain ⟨j, s, hxchild⟩ := (cert.outer_union x).mp hx
    refine ⟨j, s, ?_⟩
    simp only [ite_eq_left (childNonempty j s), Set.mem_ofPred_eq]
    exact ⟨x, hxchild, hcorner⟩
  · rintro ⟨j, s, hz⟩
    simp only [ite_eq_left (childNonempty j s), Set.mem_ofPred_eq] at hz
    rcases hz with ⟨x, hxchild, hcorner⟩
    exact ⟨x, (cert.outer_union x).2 ⟨j, s, hxchild⟩, hcorner⟩

private theorem affineHalfMem :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        ∀ (f : PartialOdometer), ∀ (z : GaussianInt), z ∈ (PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn f) u a 0).domain ↔ u - z ∈ f.domain ) := by
  classical
  intro q i v ai u a f z
  rw [(PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn f) u a 0).1]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' := (PartialOdometerHalfTurnFormulas f).1 y |>.mp hy
    have he' : u - z = -y := by
      dsimp [GaussianTranslation] at he
      rw [← he]
      simp [sub_eq_add_neg, add_comm]
    simpa [he'] using hy'
  · intro hz
    refine ⟨z - u, (PartialOdometerHalfTurnFormulas f).1 (z - u) |>.mpr ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
    · simp [GaussianTranslation, sub_eq_add_neg, add_comm]

private theorem reflectedFoot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (
        let reflectedK (j : Fin 3) (s : Bool) : PartialOdometer :=
          PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (h j (!s))) u a 0
        (∀ (j : Fin 3), ∀ (s : Bool), TileOdometer (q j.succ) (cert.P j s) (reflectedK j s) ∧
            PartialOdometerSlope (reflectedK j s) = some (s0 + (if s = true then (1 : Real) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) →
            ((∀ (f : PartialOdometer), ∀ (z : GaussianInt), z ∈ (PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn f) u a 0).domain ↔ u - z ∈ f.domain) → (∀ (j : Fin 3), ∀ (s
            : Bool), ∀ (z : GaussianInt), z ∈ FootprintVertices (cert.P j s) ↔ u - z ∈
            FootprintVertices (cert.P j (!s)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho i v ai u a positive reflectedK reflectedChild affineHalfMem j s z
  have hk := reflectedChild j s
  let k := reflectedK j s
  have hkd := PositiveCurvatureTileOdometerDomain (q j.succ)
    (cert.P j s) k (positive j) hk.1
  have hopd := PositiveCurvatureTileOdometerDomain (q j.succ)
    (cert.P j (!s)) (h j (!s)) (positive j) (ho j (!s))
  calc
    z ∈ FootprintVertices (cert.P j s) ↔ z ∈ (k.domain : Set GaussianInt) :=
      (Set.ext_iff.mp hkd z).symm
    _ ↔ u - z ∈ (h j (!s)).domain := by
      dsimp [k, reflectedK]
      exact affineHalfMem (h j (!s)) z
    _ ↔ u - z ∈ FootprintVertices (cert.P j (!s)) :=
      Set.ext_iff.mp hopd (u - z)

private theorem hgsharpdom :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (g : PartialOdometer), ((↑g.domain : Set GaussianInt) = FootprintVertices T) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (∀ z, z ∈ FootprintVertices T ↔ ∃ j s, z ∈ FootprintVertices (cert.P j s)) → ((∀ (f :
            PartialOdometer), ∀ (z : GaussianInt), z ∈ (PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn f) u a 0).domain ↔ u - z ∈ f.domain) → ((∀ (j : Fin 3), ∀ (s
            : Bool), ∀ (z : GaussianInt), z ∈ FootprintVertices (cert.P j s) ↔ u - z ∈
            FootprintVertices (cert.P j (!s))) → (
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        (gsharp.domain : Set GaussianInt) = FootprintVertices T)))) ) := by
  classical
  intro q cfg C T cert g hgdom i v ai u a rootFoot affineHalfMem reflectedFoot gsharp
  ext z
  have hroot : u - z ∈ (g.domain : Set GaussianInt) ↔ z ∈ FootprintVertices T := by
    rw [Set.ext_iff.mp hgdom (u - z), rootFoot (u - z), rootFoot z]
    constructor
    · rintro ⟨j, s, hz⟩
      exact ⟨j, !s, (reflectedFoot j (!s) z).mpr (by simpa using hz)⟩
    · rintro ⟨j, s, hz⟩
      exact ⟨j, !s, (reflectedFoot j s z).mp hz⟩
  simpa [gsharp] using (affineHalfMem g z).trans hroot

private theorem childOdoConst :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → ((∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 :
            ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (
        let reflectedK (j : Fin 3) (s : Bool) : PartialOdometer :=
          PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (h j (!s))) u a 0
        (∀ (j : Fin 3), ∀ (s : Bool), TileOdometer (q j.succ) (cert.P j s) (reflectedK j s) ∧
            PartialOdometerSlope (reflectedK j s) = some (s0 + (if s = true then (1 : Real) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) →
            ((∀ (j : Fin 3), ∀ (s : Bool), (cert.P j s).cells.Nonempty) → (∀ (j : Fin 3), ∀ (s :
            Bool), ∃ c : Int, ∀ x, x ∈ (reflectedK j s).domain → (h j s).value x - (reflectedK j
            s).value x = c))))) ) := by
  classical
  intro q cfg C T cert h s0 ho hp i v ai u a positive reflectedK reflectedChild childNonempty j s
  let V := cert.P j s
  let k := reflectedK j s
  obtain ⟨shift, ⟨hcellsEq, _, aa, bb, hdomains, hvalues⟩, _⟩ :=
    TileOdometerTranslationUniqueness (q j.succ) V V k (h j s)
      (positive j) (reflectedChild j s).1 (ho j s)
  have hcentEq : TileCentroid V =
      TileCentroid (TileTranslation V shift) := by
    have hne := childNonempty j s
    have htne : (TileTranslation V shift).cells.Nonempty := by
      rw [(TileTranslationFormulas V shift).1]
      exact Finset.image_nonempty.mpr hne
    simp only [TileCentroid, ite_eq_left htne, hcellsEq]
  rw [(TileTranslationFormulas V shift).2.2.2.2.1] at hcentEq
  have hre : (shift.re : Real) = 0 := by
    have hh := congrArg Prod.fst hcentEq
    dsimp at hh
    linarith
  have him : (shift.im : Real) = 0 := by
    have hh := congrArg Prod.snd hcentEq
    dsimp at hh
    linarith
  have hshift : shift = 0 := by
    apply Zsqrtd.ext
    · exact_mod_cast hre
    · exact_mod_cast him
  have hdeq : k.domain =
      (PartialOdometerAffineTranslate (h j s) 0 aa bb).domain := by
    ext x
    rw [(PartialOdometerAffineTranslateFormulas (h j s) 0 aa bb).2.1]
    simpa [hshift] using hdomains x
  have hveq : k.value =
      (PartialOdometerAffineTranslate (h j s) 0 aa bb).value := by
    funext x
    by_cases hx : x ∈ k.domain
    · have hx' : x ∈
          (PartialOdometerAffineTranslate (h j s) 0 aa bb).domain := by
        rw [← hdeq]
        exact hx
      rw [hvalues x hx,
        (PartialOdometerAffineTranslateFormulas (h j s) 0 aa bb).2.2.1 x hx']
      simp [hshift]
    · rw [k.value_outside x hx,
        (PartialOdometerAffineTranslate (h j s) 0 aa bb).value_outside x]
      have hx' : x ∉
          (PartialOdometerAffineTranslate (h j s) 0 aa bb).domain := by
        intro hm
        apply hx
        rw [hdeq]
        exact hm
      exact hx'
  have heq : k = PartialOdometerAffineTranslate (h j s) 0 aa bb := by
    generalize k = K at hdeq hveq ⊢
    cases K
    simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
    exact ⟨hdeq, hveq⟩
  have hslopes := (reflectedChild j s).2
  change PartialOdometerSlope k = _ at hslopes
  rw [heq, (PartialOdometerAffineTranslateFormulas
    (h j s) 0 aa bb).2.2.2.2.2, hp j s] at hslopes
  simp only [Option.map_some] at hslopes
  have haa : aa = 0 := by
    have he := congrArg Prod.fst (Option.some.inj hslopes)
    have hi := congrArg Prod.snd (Option.some.inj hslopes)
    have hrealr : (aa.re : Real) = 0 := by
      simp only [Fin.isValue, ite_smul, one_smul, neg_smul, Prod.fst_add, Int.reduceNeg,
          GaussianInt.intCast_re, add_eq_left] at he
      rw [← GaussianInt.intCast_re aa] at he
      linarith
    have hreali : (aa.im : Real) = 0 := by
      simp only [Fin.isValue, ite_smul, one_smul, neg_smul, Prod.snd_add, Int.reduceNeg,
          GaussianInt.intCast_im, add_eq_left] at hi
      rw [← GaussianInt.intCast_im aa] at hi
      linarith
    apply Zsqrtd.ext
    · exact_mod_cast hrealr
    · exact_mod_cast hreali
  refine ⟨-bb, ?_⟩
  intro x hx
  have hv : k.value x = (h j s).value x + bb := by
    simpa [hshift, haa] using hvalues x hx
  have hv' : (reflectedK j s).value x = (h j s).value x + bb := by
    simpa [k] using hv
  rw [hv']
  omega

private theorem gChildConst :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (q i.succ) (cert.P i s) (h i s)) → (∀ (g : PartialOdometer), ((↑g.domain
            : Set GaussianInt) = FootprintVertices T) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            OdometerCompatibility g (h i s)) → ((∀ (j : Fin 3), 0 < (q j.succ).1) → ((∀ (j : Fin
            3), ∀ (s : Bool), (cert.P j s).cells.Nonempty) → (∀ (j : Fin 3), ∀ (s : Bool), ∃ c :
            Int, ∀ x, x ∈ (h j s).domain → g.value x - (h j s).value x = c))))) ) := by
  classical
  intro q cfg C T cert h ho g hgdom hgcompat positive childNonempty j s
  rcases hgcompat j s with hdisj | ⟨c, hc⟩
  · obtain ⟨z, hz⟩ := childNonempty j s
    have hzfoot : z ∈ FootprintVertices (cert.P j s) := by
      simp only [FootprintVertices, childNonempty j s, ↓reduceIte, Int.reduceNeg,
          Set.mem_ofPred_eq]
      exact ⟨z, hz, Or.inl rfl⟩
    have hdomChild := PositiveCurvatureTileOdometerDomain (q j.succ)
      (cert.P j s) (h j s) (positive j) (ho j s)
    have hzchild : z ∈ (h j s).domain :=
      (Set.ext_iff.mp hdomChild z).mpr hzfoot
    have hzroot : z ∈ g.domain := by
      apply (Set.ext_iff.mp hgdom z).mpr
      exact (cert.outer_occurrence j s).2.1 hzfoot
    exact False.elim (Set.disjoint_left.mp hdisj hzroot hzchild)
  · refine ⟨-c, ?_⟩
    intro x hx
    have hxg : x ∈ g.domain := by
      apply (Set.ext_iff.mp hgdom x).mpr
      exact (cert.outer_occurrence j s).2.1
        ((Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
          (q j.succ) (cert.P j s) (h j s) (positive j) (ho j s)) x).mp hx)
    have hv := hc x hxg hx
    omega

private theorem gsharpChildConst :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), ∀ (g :
            PartialOdometer),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (
        let reflectedK (j : Fin 3) (s : Bool) : PartialOdometer :=
          PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (h j (!s))) u a 0
        (∀ (j : Fin 3), ∀ (s : Bool), TileOdometer (q j.succ) (cert.P j s) (reflectedK j s) ∧
            PartialOdometerSlope (reflectedK j s) = some (s0 + (if s = true then (1 : Real) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) →
            ((∀ (f : PartialOdometer), ∀ (z : GaussianInt), z ∈ (PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn f) u a 0).domain ↔ u - z ∈ f.domain) → (
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        ((gsharp.domain : Set GaussianInt) = FootprintVertices T) → ((∀ (j : Fin 3), ∀ (s :
            Bool), ∃ c : Int, ∀ x, x ∈ (h j s).domain → g.value x - (h j s).value x = c) → (∀ (j
            : Fin 3), ∀ (s : Bool), ∃ c : Int, ∀ x, x ∈ (reflectedK j s).domain → gsharp.value x
            - (reflectedK j s).value x = c))))) ) := by
  classical
  intro q cfg C T cert h s0 g i v ai u a positive reflectedK reflectedChild affineHalfMem gsharp
      hgsharpdom gChildConst j s
  obtain ⟨c, hc⟩ := gChildConst j (!s)
  let k := reflectedK j s
  have hkd := PositiveCurvatureTileOdometerDomain (q j.succ)
    (cert.P j s) k (positive j) (reflectedChild j s).1
  have hrootChild : FootprintVertices (cert.P j s) ⊆ FootprintVertices T :=
    (cert.outer_occurrence j s).2.1
  refine ⟨c, ?_⟩
  intro x hx
  have hxroot : x ∈ (gsharp.domain : Set GaussianInt) := by
    rw [Set.ext_iff.mp hgsharpdom]
    exact hrootChild ((Set.ext_iff.mp hkd x).mp hx)
  have hy : u - x ∈ (h j (!s)).domain :=
    (affineHalfMem (h j (!s)) x).mp hx
  have hgv := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn g) u a 0).2.2.1 x hxroot
  have hkv := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn (h j (!s))) u a 0).2.2.1 x hx
  have hgd := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn g) u a 0).2.1 x |>.mp hxroot
  have hkd' := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn (h j (!s))) u a 0).2.1 x |>.mp hx
  have hgv' := (PartialOdometerHalfTurnFormulas g).2.1 (x - u) hgd
  have hkv' := (PartialOdometerHalfTurnFormulas (h j (!s))).2.1
    (x - u) hkd'
  rw [hgv, hkv, hgv', hkv']
  have hc' := hc (u - x) hy
  simp [] at hc' ⊢
  omega

private theorem sharpCompat :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (∀ (g :
            PartialOdometer),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (
        let reflectedK (j : Fin 3) (s : Bool) : PartialOdometer :=
          PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (h j (!s))) u a 0
        (∀ (j : Fin 3), ∀ (s : Bool), TileOdometer (q j.succ) (cert.P j s) (reflectedK j s) ∧
            PartialOdometerSlope (reflectedK j s) = some (s0 + (if s = true then (1 : Real) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) → (
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        (∀ (j : Fin 3), ∀ (s : Bool), ∃ c : Int, ∀ x, x ∈ (reflectedK j s).domain → (h j s).value
            x - (reflectedK j s).value x = c) → ((∀ (j : Fin 3), ∀ (s : Bool), ∃ c : Int, ∀ x, x
            ∈ (reflectedK j s).domain → gsharp.value x - (reflectedK j s).value x = c) → (∀ j, ∀
            s, OdometerCompatibility gsharp (h j s)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho g i v ai u a positive reflectedK reflectedChild gsharp
      childOdoConst gsharpChildConst j s
  obtain ⟨c₁, hc₁⟩ := gsharpChildConst j s
  obtain ⟨c₂, hc₂⟩ := childOdoConst j s
  have hkd := PositiveCurvatureTileOdometerDomain (q j.succ)
    (cert.P j s) (reflectedK j s) (positive j) (reflectedChild j s).1
  have hhd := PositiveCurvatureTileOdometerDomain (q j.succ)
    (cert.P j s) (h j s) (positive j) (ho j s)
  have hsame : ((reflectedK j s).domain : Set GaussianInt) =
      ((h j s).domain : Set GaussianInt) := hkd.trans hhd.symm
  right
  refine ⟨c₂ - c₁, ?_⟩
  intro x hxg hx
  have hxk : x ∈ (reflectedK j s).domain :=
    (Set.ext_iff.mp hsame.symm x).mp hx
  have hleft := hc₂ x hxk
  have hright := hc₁ x hxk
  omega

private theorem hdomEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : PartialOdometer),
            ((↑g.domain : Set GaussianInt) = FootprintVertices T) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        ((gsharp.domain : Set GaussianInt) = FootprintVertices T) → (∀ (c : ℤ), gsharp.domain =
            (PartialOdometerAffineTranslate g 0 0 c).domain)) ) := by
  classical
  intro q T g hgdom i v ai u a gsharp hgsharpdom c
  ext x
  rw [(PartialOdometerAffineTranslateFormulas g 0 0 c).2.1]
  have h1 := Set.ext_iff.mp hgsharpdom x
  have h2 := Set.ext_iff.mp hgdom x
  simpa using h1.trans h2.symm

private theorem hvalEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : PartialOdometer),
            ((↑g.domain : Set GaussianInt) = FootprintVertices T) → (
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        ((gsharp.domain : Set GaussianInt) = FootprintVertices T) → (∀ (c : ℤ), (∀ x ∈ g.domain,
            gsharp.value x - g.value x = c) → ((gsharp.domain = (PartialOdometerAffineTranslate g
            0 0 c).domain) → (gsharp.value = (PartialOdometerAffineTranslate g 0 0 c).value)))) )
            := by
  classical
  intro q T g hgdom i v ai u a gsharp hgsharpdom c hc hdomEq
  funext x
  by_cases hx : x ∈ g.domain
  · have hxsharp : x ∈ gsharp.domain := by
      exact (Set.ext_iff.mp (hgsharpdom.trans hgdom.symm) x).mpr hx
    have hxt : x ∈ (PartialOdometerAffineTranslate g 0 0 c).domain := by
      simpa only [hdomEq] using hxsharp
    rw [(PartialOdometerAffineTranslateFormulas g 0 0 c).2.2.1 x hxt]
    have hv := hc x hx
    simp [] at hv ⊢
    omega
  · have hxsharp : x ∉ gsharp.domain := by
      intro hmem
      apply hx
      exact (Set.ext_iff.mp (hgsharpdom.trans hgdom.symm) x).mp hmem
    rw [gsharp.value_outside x hxsharp,
      (PartialOdometerAffineTranslate g 0 0 c).value_outside x]
    intro hmem
    apply hx
    have hm := (PartialOdometerAffineTranslateFormulas g 0 0 c).2.1 x |>.mp hmem
    simpa using hm

private theorem hsharpEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (g : PartialOdometer),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        ∀ (c : ℤ), (gsharp.domain = (PartialOdometerAffineTranslate g 0 0 c).domain) →
            ((gsharp.value = (PartialOdometerAffineTranslate g 0 0 c).value) → (gsharp =
            PartialOdometerAffineTranslate g 0 0 c)) ) := by
  classical
  intro q g i v ai u a gsharp c hdomEq hvalEq
  generalize gsharp = G at hdomEq hvalEq ⊢
  cases G
  simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
  exact ⟨hdomEq, hvalEq⟩

private theorem hsharpSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (g : PartialOdometer),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        ∀ (c : ℤ), (gsharp = PartialOdometerAffineTranslate g 0 0 c) → (PartialOdometerSlope
            gsharp = PartialOdometerSlope g) ) := by
  classical
  intro q g i v ai u a gsharp c hsharpEq
  rw [hsharpEq, (PartialOdometerAffineTranslateFormulas g 0 0 c).2.2.2.2.2]
  simp

private theorem hchildSquares :
    (by
      classical
      exact
        ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (pchild : ℝ × ℝ), (PartialOdometerSlope (h (0 :
            Fin (3 : ℕ)) true) = some pchild) → ((PartialOdometerSquares (h 0 true)).Nonempty) )
            := by
  classical
  intro h pchild hchild
  by_contra hn
  have hnone : PartialOdometerSlope (h 0 true) = none := by
    simp [PartialOdometerSlope, hn]
  rw [hnone] at hchild
  cases hchild

private theorem hgchild :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (q i.succ) (cert.P i s) (h i s)) → (∀ (g : PartialOdometer), ((↑g.domain
            : Set GaussianInt) = FootprintVertices T) → ((∀ (j : Fin 3), 0 < (q j.succ).1) → ((h
            0 true).domain ⊆ g.domain))) ) := by
  classical
  intro q cfg C T cert h ho g hgdom positive y hy
  apply (Set.ext_iff.mp hgdom y).mpr
  have hdomChild := PositiveCurvatureTileOdometerDomain
    (q (0 : Fin 3).succ) (cert.P 0 true) (h 0 true) (positive 0) (ho 0 true)
  exact (cert.outer_occurrence 0 true).2.1
    ((Set.ext_iff.mp hdomChild y).mp hy)

private theorem hgSqNonempty :
    (by
      classical
      exact
        ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (g : PartialOdometer), ∀ (x : GaussianInt), (x
            ∈ PartialOdometerSquares (h (0 : Fin (3 : ℕ)) true)) → (((h 0 true).domain ⊆
            g.domain) → ((PartialOdometerSquares g).Nonempty)) ) := by
  classical
  intro h g x hx hgchild
  refine ⟨x, ?_⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hx0, hx1, hxi, hx1i⟩
  exact ⟨hgchild hx0, hgchild hx1, hgchild hxi, hgchild hx1i⟩

private theorem hcov :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (g : PartialOdometer),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt), ∀ (u : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
        PartialOdometerSlope gsharp = (PartialOdometerSlope g).map (fun p => (-p.1 + (a.re :
            Real), -p.2 + (a.im : Real))) ) := by
  classical
  intro q g i v ai u a gsharp
  rw [(PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn g) u a 0).2.2.2.2.2,
    (PartialOdometerHalfTurnFormulas g).2.2.2.2.2.2]
  simp only [Option.map_map, Function.comp_def]

private theorem haRe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s0 : Real × Real),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (GaussianRealPoint a = (2 : Real) • s0) → ((a.re : Real) = 2 * s0.1) ) := by
  classical
  intro q s0 i v ai a ha
  have hh := congrArg Prod.fst ha
  simpa [GaussianRealPoint] using hh

private theorem haIm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s0 : Real × Real),
        let i : Fin 3 := 0
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
        ∀ (ai : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v)
        (GaussianRealPoint a = (2 : Real) • s0) → ((a.im : Real) = 2 * s0.2) ) := by
  classical
  intro q s0 i v ai a ha
  have hh := congrArg Prod.snd ha
  simpa [GaussianRealPoint] using hh

private theorem hpEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s0 : Real × Real), ∀ (g : PartialOdometer),
        let i : Fin 3 := 0;
        let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ));
        ∀ (ai : GaussianInt),
        let a := ai - (v + GaussianQuarterTurn v);
        let p : Real × Real :=
          ((∑ x ∈ PartialOdometerSquares g,
              ((g.value (x + 1) - g.value x + g.value (x + 1 + ⟨0, 1⟩) -
                g.value (x + ⟨0, 1⟩) : Int) : Real)) /
            (2 * ((PartialOdometerSquares g).card : Real)),
           (∑ x ∈ PartialOdometerSquares g,
              ((g.value (x + ⟨0, 1⟩) - g.value x + g.value (x + 1 + ⟨0, 1⟩) -
                g.value (x + 1) : Int) : Real)) /
            (2 * ((PartialOdometerSquares g).card : Real)));
        (some p = some (-p.1 + (↑a.re : ℝ), -p.2 + (↑a.im : ℝ))) → (((a.re : Real) = 2 * s0.1) →
            (((a.im : Real) = 2 * s0.2) → (p = s0))) ) := by
  classical
  intro q s0 g i v ai a p hcov haRe haIm
  have hpair := Option.some.inj hcov
  apply Prod.ext
  · have hh := congrArg Prod.fst hpair
    dsimp at hh
    linarith [haRe]
  · have hh := congrArg Prod.snd hpair
    dsimp at hh
    linarith [haIm]

end ReflectedGluingGeometry

theorem P4250T1ReflectedGluingSlope
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (h : Fin 3 → Bool → PartialOdometer) (s0 : Real × Real)
    (ho : ∀ i s, TileOdometer (q i.succ) (cert.P i s) (h i s))
    (hp : ∀ i s, PartialOdometerSlope (h i s) = some
      (s0 + (if s = true then (1 : Real) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)))))
    (g : PartialOdometer)
    (hgdom : (g.domain : Set GaussianInt) = FootprintVertices T)
    (hgcompat : ∀ i s, OdometerCompatibility g (h i s))
    (hunique : ∀ g' : PartialOdometer,
      (g'.domain : Set GaussianInt) = FootprintVertices T →
      (∀ i s, OdometerCompatibility g' (h i s)) →
      ∃ c : Int, ∀ x, x ∈ g.domain → g'.value x - g.value x = c) :
    ∃ u a : GaussianInt,
      (2 : Real) • TileCentroid T = GaussianRealPoint u ∧
      (2 : Real) • s0 = GaussianRealPoint a ∧
      PartialOdometerSlope g = some s0 := by
-- BODY
  classical
  let i : Fin 3 := 0
  let v := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
  have hpositive := ReflectedGluingGeometry.hpositive q cfg
  obtain ⟨pchild, ai, hchild, hhalf, hcells⟩ :=
    P4250T1DefinedHalfIntegralSlope (q (0 : Fin 3).succ) (cert.P 0 true)
      (h 0 true) hpositive (ho 0 true)
  have htwo_s0 := ReflectedGluingGeometry.htwo_s0 q s0 pchild ai hhalf
      (ReflectedGluingGeometry.hpchild q h s0 hp pchild hchild)
  have hcenterIntegral := ReflectedGluingGeometry.hcenterIntegral q cfg C T cert hcells
  obtain ⟨u, hu⟩ := hcenterIntegral
  let a := ai - (v + GaussianQuarterTurn v)
  have ha : GaussianRealPoint a = (2 : Real) • s0 := htwo_s0.symm
  have positive := ReflectedGluingGeometry.positive q cfg
  have reflectedChild := ReflectedGluingGeometry.reflectedChild q cfg C T cert h s0 ho hp ai u hu
      ha positive
  have childNonempty := ReflectedGluingGeometry.childNonempty q cfg C T cert h ho positive
  have affineHalfMem := ReflectedGluingGeometry.affineHalfMem q ai u
  let gsharp := PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u a 0
  have hgsharpdom := ReflectedGluingGeometry.hgsharpdom q cfg C T cert g hgdom ai u
      (ReflectedGluingGeometry.rootFoot q cfg C T cert childNonempty
      (ReflectedGluingGeometry.rootNonempty q cfg C T cert childNonempty)) affineHalfMem
      (ReflectedGluingGeometry.reflectedFoot q cfg C T cert h s0 ho ai u positive reflectedChild
      affineHalfMem)
  have sharpCompat := ReflectedGluingGeometry.sharpCompat q cfg C T cert h s0 ho g ai u positive
      reflectedChild (ReflectedGluingGeometry.childOdoConst q cfg C T cert h s0 ho hp ai u
      positive reflectedChild childNonempty) (ReflectedGluingGeometry.gsharpChildConst q cfg C T
      cert h s0 g ai u positive reflectedChild affineHalfMem hgsharpdom
      (ReflectedGluingGeometry.gChildConst q cfg C T cert h ho g hgdom hgcompat positive
      childNonempty))
  obtain ⟨c, hc⟩ := hunique gsharp hgsharpdom sharpCompat
  have hdomEq := ReflectedGluingGeometry.hdomEq q T g hgdom ai u hgsharpdom c
  have hsharpSlope : PartialOdometerSlope gsharp = PartialOdometerSlope g :=
      ReflectedGluingGeometry.hsharpSlope q g ai u c (ReflectedGluingGeometry.hsharpEq q g ai u c
      hdomEq (ReflectedGluingGeometry.hvalEq q T g hgdom ai u hgsharpdom c hc hdomEq))
  have hchildSquares := ReflectedGluingGeometry.hchildSquares h pchild hchild
  obtain ⟨x, hx⟩ := hchildSquares
  have hgSqNonempty : (PartialOdometerSquares g).Nonempty := ReflectedGluingGeometry.hgSqNonempty
      h g x hx (ReflectedGluingGeometry.hgchild q cfg C T cert h ho g hgdom positive)
  let p : Real × Real :=
    ((∑ x ∈ PartialOdometerSquares g,
        ((g.value (x + 1) - g.value x + g.value (x + 1 + ⟨0, 1⟩) -
          g.value (x + ⟨0, 1⟩) : Int) : Real)) /
      (2 * ((PartialOdometerSquares g).card : Real)),
     (∑ x ∈ PartialOdometerSquares g,
        ((g.value (x + ⟨0, 1⟩) - g.value x + g.value (x + 1 + ⟨0, 1⟩) -
          g.value (x + 1) : Int) : Real)) /
      (2 * ((PartialOdometerSquares g).card : Real)))
  have hgslope : PartialOdometerSlope g = some p := by
    simp [PartialOdometerSlope, hgSqNonempty, p]
  have hcov : PartialOdometerSlope gsharp =
      (PartialOdometerSlope g).map (fun p =>
        (-p.1 + (a.re : Real), -p.2 + (a.im : Real))) := ReflectedGluingGeometry.hcov q g ai u
  rw [hsharpSlope, hgslope] at hcov
  simp only [Option.map_some] at hcov
  have hpEq : p = s0 := ReflectedGluingGeometry.hpEq q s0 g ai hcov
      (ReflectedGluingGeometry.haRe q s0 ai ha) (ReflectedGluingGeometry.haIm q s0 ai ha)
  refine ⟨u, a, hu, ha.symm, ?_⟩
  rw [hgslope, hpEq]

end ApollonianSuperharmonic

end
