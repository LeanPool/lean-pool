/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn

-- [TABLET NODE: BandPrototileCentralSymmetry]

/-!
# BandPrototileCentralSymmetry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CentralSymmetryProof

private theorem pair :
    ∀ (T : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
        ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandPrototile (q i.succ) (S i s)) → ((∀
        (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T = (if s = true
        then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2
        : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
        (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
        (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
        ℕ))).succ))).1))) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), CentrallyReflectedAt
        (TileCentroid (S i s)) (S i s) (S i s)) → (∀ i : Fin 3, CentrallyReflectedAt
        (TileCentroid T) (S i true) (S i false)))) := by
  classical
  intro T q S hS hcentroid ih i
  let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let u := GaussianQuarterTurn w - w
  have hplus := hcentroid i true
  have hminus := hcentroid i false
  have hu_re : (u.re : Real) =
      -(GaussianRealPoint w).1 - (GaussianRealPoint w).2 := by
    change (((-w.im - w.re : Int) : Real)) =
      -((w.re : Int) : Real) - ((w.im : Int) : Real)
    norm_num
    ring
  have hu_im : (u.im : Real) =
      (GaussianRealPoint w).1 - (GaussianRealPoint w).2 := by
    change (((w.re - w.im : Int) : Real)) =
      ((w.re : Int) : Real) - ((w.im : Int) : Real)
    norm_num
  have hurexp : (u.re : Real) =
      -((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).re : Real) -
        ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).im : Real) := by
    simpa [w, GaussianRealPoint] using hu_re
  have huimexp : (u.im : Real) =
      ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).re : Real) -
        ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).im : Real) := by
    simpa [w, GaussianRealPoint] using hu_im
  have hcent : TileCentroid (TileTranslation (S i true) u) =
      TileCentroid (S i false) := by
    rw [(TileTranslationFormulas (S i true) u).2.2.2.2.1]
    have hre := congrArg Prod.fst hplus
    have him := congrArg Prod.snd hplus
    have hrem := congrArg Prod.fst hminus
    have himm := congrArg Prod.snd hminus
    dsimp [w] at hre him hrem himm
    dsimp [w, GaussianRealPoint] at hu_re hu_im
    have hre' : (TileCentroid (S i true)).1 - (TileCentroid T).1 =
        (1 / 2 : Real) * (((w.re : Int) : Real) + ((w.im : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using hre
    have him' : (TileCentroid (S i true)).2 - (TileCentroid T).2 =
        (1 / 2 : Real) * (((w.im : Int) : Real) - ((w.re : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using him
    have hrem' : (TileCentroid (S i false)).1 - (TileCentroid T).1 =
        -(1 / 2 : Real) * (((w.re : Int) : Real) + ((w.im : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using hrem
    have himm' : (TileCentroid (S i false)).2 - (TileCentroid T).2 =
        -(1 / 2 : Real) * (((w.im : Int) : Real) - ((w.re : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using himm
    apply Prod.ext
    · change (TileCentroid (S i true)).1 + (u.re : Real) = _
      rw [hu_re]
      linarith [hrem']
    · change (TileCentroid (S i true)).2 + (u.im : Real) = _
      rw [hu_im]
      linarith [himm']
  have translated : BandPrototile (q i.succ) (TileTranslation (S i true) u) :=
    BandPrototileTranslation (q i.succ) (S i true) u (hS i true)
  have unique := BandPrototileCentroidUnique (q i.succ)
    (TileTranslation (S i true) u) (S i false) translated (hS i false) hcent
  have hcells' : (TileTranslation (S i true) u).cells = (S i false).cells := unique.1
  have hreal : TileRealization (TileTranslation (S i true) u) =
      TileRealization (S i false) := by
    rw [TileRealization, hcells', TileRealization]
  have hcentral := ih i true
  have hreflect : CentrallyReflectedAt (TileCentroid T)
      (S i true) (S i false) := by
    rw [CentrallyReflectedAt, ← hreal,
      (TileTranslationFormulas (S i true) u).2.2.2.1]
    nth_rewrite 1 [hcentral]
    rw [Set.image_image]
    have map_eq :
        (fun z : Real × Real =>
          ((2 * (TileCentroid (S i true)).1 - z.1,
            2 * (TileCentroid (S i true)).2 - z.2).1 + (u.re : Real),
           (2 * (TileCentroid (S i true)).1 - z.1,
            2 * (TileCentroid (S i true)).2 - z.2).2 + (u.im : Real))) =
        (fun z : Real × Real =>
          (2 * (TileCentroid T).1 - z.1, 2 * (TileCentroid T).2 - z.2)) := by
      funext z
      apply Prod.ext
      · dsimp
        rw [hurexp]
        have hx := congrArg Prod.fst hplus
        have hr := congrArg Prod.fst hminus
        dsimp [w, GaussianRealPoint] at hx hr ⊢
        ring_nf at hx hr ⊢
        linarith
      · dsimp
        rw [huimexp]
        have hy := congrArg Prod.snd hplus
        have hi := congrArg Prod.snd hminus
        dsimp [w, GaussianRealPoint] at hy hi ⊢
        ring_nf at hy hi ⊢
        linarith
    rw [map_eq]
  exact hreflect

private theorem realization :
    ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x : LatticeCell), x ∈ T.cells
        ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) → (TileRealization T = ⋃ i : Fin 3,
        ⋃ s : Bool, TileRealization (S i s)) := by
  classical
  intro T S hcells
  ext p
  simp only [TileRealization, Set.mem_iUnion]
  constructor
  · intro hp
    rcases hp with ⟨x, hx, hp⟩
    rcases (hcells x).mp hx with ⟨i, s, hs⟩
    exact ⟨i, s, x, hs, hp⟩
  · intro hp
    rcases hp with ⟨i, s, x, hs, hp⟩
    exact ⟨x, (hcells x).mpr ⟨i, s, hs⟩, hp⟩

private theorem hq' :
    ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (x : ℝ × ℝ), ∀ (i : Fin (3 :
        ℕ)), (TileRealization (S i false) = (fun (z : ℝ × ℝ) => ((2 : ℝ) * (TileCentroid T).1 -
        z.1, (2 : ℝ) * (TileCentroid T).2 - z.2)) '' TileRealization (S i true)) → ((x ∈
        TileRealization (S i false)) → ((2 * (TileCentroid T).1 - x.1, 2 * (TileCentroid T).2 -
        x.2) ∈ TileRealization (S i true))) := by
  classical
  intro T S x i pairEq hx
  rcases (pairEq ▸ hx) with ⟨q, hq, hqeq⟩
  have heq : (2 * (TileCentroid T).1 - x.1,
      2 * (TileCentroid T).2 - x.2) = q := by
    rw [← hqeq]
    dsimp
    ring_nf
  rw [heq]
  exact hq

end CentralSymmetryProof

theorem BandPrototileCentralSymmetry : ∀ (C : CircleCoordinates)
    (T : ProtoTile),
    BandPrototile C T → CentrallyReflectedAt (TileCentroid T) T T := by
-- BODY
  intro C T hT
  induction hT with
  | line w x hw =>
      rw [CentrallyReflectedAt, TileRealization]
      simp
  | unit z x =>
      rw [CentrallyReflectedAt]
      ext p
      simp only [TileRealization, Finset.mem_singleton, Set.mem_iUnion,
        Set.mem_image]
      have hx : ({x} : FiniteTile).Nonempty := Finset.singleton_nonempty x
      simp only [TileCentroid, ite_eq_left hx, Finset.sum_singleton, Finset.card_singleton]
      constructor
      · intro hp
        rcases hp with ⟨i, hi, hp⟩
        subst i
        refine ⟨(2 * (((x.re : Int) : Real) + 1 / 2) - p.1,
          2 * (((x.im : Int) : Real) + 1 / 2) - p.2),
          ⟨x, rfl, ?_⟩, ?_⟩
        · simp only [ClosedSquareRealization, Set.mem_Icc] at hp ⊢
          change (_ ≤ _ ∧ _ ≤ _) ∧ (_ ≤ _ ∧ _ ≤ _) at hp ⊢
          have hpx := hp.1.1
          have hpy := hp.1.2
          have hqx := hp.2.1
          have hqy := hp.2.2
          constructor
          · constructor <;> norm_num at * <;> linarith
          · constructor <;> norm_num at * <;> linarith
        · apply Prod.ext <;> dsimp <;> ring
      · intro hp
        rcases hp with ⟨q, ⟨a, ha, hqa⟩, hqp⟩
        subst a
        refine ⟨x, rfl, ?_⟩
        simp only [ClosedSquareRealization, Set.mem_Icc] at hqa ⊢
        change (_ ≤ _ ∧ _ ≤ _) ∧ (_ ≤ _ ∧ _ ≤ _) at hqa ⊢
        have hr := congrArg Prod.fst hqp
        have hi := congrArg Prod.snd hqp
        dsimp at hr hi
        have hpx := hqa.1.1
        have hpy := hqa.1.2
        have hqx := hqa.2.1
        have hqy := hqa.2.2
        constructor
        · constructor <;> norm_num at * <;> linarith
        · constructor <;> norm_num at * <;> linarith
  | @decompose q hq S T hS hcells hfoot hcentroid ih =>
      have pair : ∀ i : Fin 3,
          CentrallyReflectedAt (TileCentroid T) (S i true) (S i false) :=
              CentralSymmetryProof.pair T q S hS hcentroid ih
      rw [CentrallyReflectedAt]
      have realization : TileRealization T =
          ⋃ i : Fin 3, ⋃ s : Bool, TileRealization (S i s) := CentralSymmetryProof.realization T
              S hcells
      rw [realization]
      ext p
      simp only [Set.mem_iUnion, Set.mem_image]
      change (∃ i s, p ∈ TileRealization (S i s)) ↔
        ∃ x, (∃ i s, x ∈ TileRealization (S i s)) ∧
          (2 * (TileCentroid T).1 - x.1, 2 * (TileCentroid T).2 - x.2) = p
      constructor
      · rintro ⟨i, s, hp⟩
        have pairEq := pair i
        change TileRealization (S i false) =
          (fun z : Real × Real =>
            (2 * (TileCentroid T).1 - z.1, 2 * (TileCentroid T).2 - z.2)) ''
            TileRealization (S i true) at pairEq
        by_cases hs : s = true
        · subst s
          refine ⟨(2 * (TileCentroid T).1 - p.1,
            2 * (TileCentroid T).2 - p.2), ⟨i, false, ?_⟩, ?_⟩
          · rw [pairEq]
            exact ⟨p, hp, rfl⟩
          · apply Prod.ext <;> dsimp <;> ring
        · have hs' : s = false := Bool.eq_false_of_not_eq_true hs
          subst s
          rcases (pairEq ▸ hp) with ⟨q, hq, hqp⟩
          exact ⟨q, ⟨i, true, hq⟩, hqp⟩
      · rintro ⟨x, ⟨i, s, hx⟩, hxp⟩
        have pairEq := pair i
        change TileRealization (S i false) =
          (fun z : Real × Real =>
            (2 * (TileCentroid T).1 - z.1, 2 * (TileCentroid T).2 - z.2)) ''
            TileRealization (S i true) at pairEq
        by_cases hs : s = true
        · subst s
          refine ⟨i, false, ?_⟩
          rw [pairEq]
          exact ⟨x, hx, hxp⟩
        · have hs' : s = false := Bool.eq_false_of_not_eq_true hs
          subst s
          have hq' : (2 * (TileCentroid T).1 - x.1,
              2 * (TileCentroid T).2 - x.2) ∈ TileRealization (S i true) :=
                  CentralSymmetryProof.hq' T S x i pairEq hx
          rw [← hxp]
          exact ⟨i, true, hq'⟩

end ApollonianSuperharmonic

end
