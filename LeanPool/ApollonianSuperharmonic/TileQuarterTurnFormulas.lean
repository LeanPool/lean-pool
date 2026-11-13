/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianCoordinateFacts

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: TileQuarterTurnFormulas]

/-!
# TileQuarterTurnFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace QuarterTurnFormulas

private theorem quarter_re_int (x : GaussianInt) :
      (GaussianQuarterTurn x - 1).re = -x.im - 1 := by
  classical
  rcases x with ⟨a, b⟩
  rfl

private theorem quarter_im_int (x : GaussianInt) :
      (GaussianQuarterTurn x - 1).im = x.re := by
  classical
  rcases x with ⟨a, b⟩
  simp [GaussianQuarterTurn]

private theorem quarter_re_cast (x : GaussianInt) :
      ((GaussianQuarterTurn x - 1).re : Real) = -(x.im : Real) - 1 := by
  classical
  have quarter_re_int (x : GaussianInt) :
      (GaussianQuarterTurn x - 1).re = -x.im - 1 := quarter_re_int x
  rw [quarter_re_int]
  norm_num

private theorem quarter_im_cast (x : GaussianInt) :
      ((GaussianQuarterTurn x - 1).im : Real) = (x.re : Real) := by
  classical
  have quarter_im_int (x : GaussianInt) :
      (GaussianQuarterTurn x - 1).im = x.re := quarter_im_int x
  rw [quarter_im_int]

private theorem quarter_re_base (x : GaussianInt) :
      (GaussianInt.toComplex (GaussianQuarterTurn x)).re = -(x.im : Real) := by
  classical
  rcases x with ⟨a, b⟩
  simp [GaussianQuarterTurn, GaussianInt.toComplex_def]

private theorem quarter_im_base (x : GaussianInt) :
      (GaussianInt.toComplex (GaussianQuarterTurn x)).im = (x.re : Real) := by
  classical
  rcases x with ⟨a, b⟩
  simp [GaussianQuarterTurn, GaussianInt.toComplex_def]

private abbrev gaussian_equal := GaussianCoordinateFacts.equal

private theorem turn_up (a : GaussianInt) :
      GaussianQuarterTurn (a + ⟨0, 1⟩) = GaussianQuarterTurn a - 1 := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp [GaussianQuarterTurn]; omega

private theorem turn_right (a : GaussianInt) :
      GaussianQuarterTurn (a + 1) = GaussianQuarterTurn a + ⟨0, 1⟩ := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp [GaussianQuarterTurn]

private theorem turn_up_right (a : GaussianInt) :
      GaussianQuarterTurn (a + 1 + ⟨0, 1⟩) =
        GaussianQuarterTurn a - 1 + ⟨0, 1⟩ := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp [GaussianQuarterTurn]; omega

private theorem minus_one_add_one (u : GaussianInt) : u - 1 + 1 = u := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp

private theorem minus_one_add_up (u : GaussianInt) :
      u - 1 + ⟨0, 1⟩ = ⟨u.re - 1, u.im + 1⟩ := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp

private abbrev pair_swap := GaussianCoordinateFacts.pairSwap

private noncomputable def cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩

private theorem inverse_formula (z : GaussianInt) :
        GaussianQuarterTurn (cellInverse z) - 1 = z := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  change (GaussianQuarterTurn (cellInverse z) - 1 = z)
  apply gaussian_equal <;> simp [cellInverse, GaussianQuarterTurn]

private theorem forward_formula (a : GaussianInt) :
        cellInverse (GaussianQuarterTurn a - 1) = a := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  change (cellInverse (GaussianQuarterTurn a - 1) = a)
  apply gaussian_equal <;> simp [cellInverse, GaussianQuarterTurn]

private theorem quarter_inverse (a : GaussianInt) :
        cellInverse (GaussianQuarterTurn a) = a - ⟨0, 1⟩ := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  change (cellInverse (GaussianQuarterTurn a) = a - ⟨0, 1⟩)
  apply gaussian_equal <;> simp [cellInverse, GaussianQuarterTurn]; omega

private theorem q_inverse (z : GaussianInt) :
      GaussianQuarterTurn (cellInverse z) = z + 1 := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  have inverse_formula (z : GaussianInt) :
        GaussianQuarterTurn (cellInverse z) - 1 = z := inverse_formula z
  have hz := inverse_formula z
  change (GaussianQuarterTurn (cellInverse z) = z + 1)
  apply gaussian_equal <;> simp [cellInverse, GaussianQuarterTurn] at hz ⊢

private theorem turn_up_left (a : GaussianInt) :
      GaussianQuarterTurn (⟨0, 1⟩ + a) = GaussianQuarterTurn a - 1 := by
  classical
  have turn_up (a : GaussianInt) :
      GaussianQuarterTurn (a + ⟨0, 1⟩) = GaussianQuarterTurn a - 1 := turn_up a
  rw [add_comm]
  exact turn_up a

private abbrev turn_one_up := ApollonianSuperharmonic.QuarterTurnFormulas.turn_up_right

private theorem one_sub_one (u : GaussianInt) : u + 1 - 1 = u := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  apply gaussian_equal <;> simp

private theorem inverse_horizontal (z : GaussianInt) :
        cellInverse (z - ⟨0, 1⟩) = cellInverse z - 1 := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  change cellInverse (z - ⟨0, 1⟩) = cellInverse z - 1
  apply gaussian_equal <;> simp [cellInverse]

private theorem inverse_vertical (z : GaussianInt) :
        cellInverse (z - 1) = cellInverse z + ⟨0, 1⟩ := by
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_equal u v hre him
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  change cellInverse (z - 1) = cellInverse z + ⟨0, 1⟩
  apply gaussian_equal <;> simp [cellInverse]

private theorem cell_formula (T : ProtoTile) (z : GaussianInt) :
        z ∈ (TileQuarterTurn T).cells ↔ cellInverse z ∈ T.cells := by
  classical
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  have inverse_formula (z : GaussianInt) :
        GaussianQuarterTurn (cellInverse z) - 1 = z := inverse_formula z
  have forward_formula (a : GaussianInt) :
        cellInverse (GaussianQuarterTurn a - 1) = a := forward_formula a
  change z ∈ T.cells.image (fun x => GaussianQuarterTurn x - 1) ↔ cellInverse z ∈ T.cells
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, hza⟩
    rw [← hza, forward_formula]
    exact ha
  · intro hz
    exact Finset.mem_image.mpr ⟨cellInverse z, hz, inverse_formula z⟩

private theorem edge_formula (T : ProtoTile) :
        BoundaryFootprintEdges (TileQuarterTurn T) =
          (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
            BoundaryFootprintEdges T := by
  classical
  have turn_up (a : GaussianInt) :
      GaussianQuarterTurn (a + ⟨0, 1⟩) = GaussianQuarterTurn a - 1 := turn_up a
  have turn_right (a : GaussianInt) :
      GaussianQuarterTurn (a + 1) = GaussianQuarterTurn a + ⟨0, 1⟩ := turn_right a
  have pair_swap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} := pair_swap u v
  let cellInverse : GaussianInt → GaussianInt := fun z =>
      ⟨(z + 1).im, -(z + 1).re⟩
  have forward_formula (a : GaussianInt) :
        cellInverse (GaussianQuarterTurn a - 1) = a := forward_formula a
  have quarter_inverse (a : GaussianInt) :
        cellInverse (GaussianQuarterTurn a) = a - ⟨0, 1⟩ := quarter_inverse a
  have q_inverse (z : GaussianInt) :
      GaussianQuarterTurn (cellInverse z) = z + 1 := q_inverse z
  have turn_up_left (a : GaussianInt) :
      GaussianQuarterTurn (⟨0, 1⟩ + a) = GaussianQuarterTurn a - 1 := turn_up_left a
  have turn_one_up (a : GaussianInt) :
      GaussianQuarterTurn (a + 1 + ⟨0, 1⟩) =
        GaussianQuarterTurn a - 1 + ⟨0, 1⟩ := turn_one_up a
  have one_sub_one (u : GaussianInt) : u + 1 - 1 = u := one_sub_one u
  have inverse_horizontal (z : GaussianInt) :
        cellInverse (z - ⟨0, 1⟩) = cellInverse z - 1 := inverse_horizontal z
  have inverse_vertical (z : GaussianInt) :
        cellInverse (z - 1) = cellInverse z + ⟨0, 1⟩ := inverse_vertical z
  have cell_formula (z : GaussianInt) :
        z ∈ (TileQuarterTurn T).cells ↔ cellInverse z ∈ T.cells := cell_formula T z
  ext e
  change (∃ z : GaussianInt,
      (e = {z, z + 1} ∧
        ((z ∈ (TileQuarterTurn T).cells ∧
            z - ⟨0, 1⟩ ∉ (TileQuarterTurn T).cells) ∨
          (z ∉ (TileQuarterTurn T).cells ∧
            z - ⟨0, 1⟩ ∈ (TileQuarterTurn T).cells))) ∨
      (e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ (TileQuarterTurn T).cells ∧
            z - 1 ∉ (TileQuarterTurn T).cells) ∨
          (z ∉ (TileQuarterTurn T).cells ∧
            z - 1 ∈ (TileQuarterTurn T).cells)))) ↔
    ∃ f, f ∈ BoundaryFootprintEdges T ∧
      f.image GaussianQuarterTurn = e
  constructor
  · rintro ⟨z, hz⟩
    rcases hz with ⟨he, hp⟩ | ⟨he, hp⟩
    · refine ⟨{cellInverse z, cellInverse z + ⟨0, 1⟩}, ?_, ?_⟩
      · refine ⟨cellInverse z, Or.inr ⟨rfl, ?_⟩⟩
        simpa [cell_formula, inverse_horizontal] using hp
      · subst e
        simp [Finset.image_insert, pair_swap, q_inverse, turn_up_left,
          one_sub_one, add_comm]
    · refine ⟨{cellInverse z + ⟨0, 1⟩, cellInverse z + 1 + ⟨0, 1⟩}, ?_, ?_⟩
      · refine ⟨cellInverse z + ⟨0, 1⟩,
          Or.inl ⟨by ext w; simp [add_comm, add_left_comm], ?_⟩⟩
        simpa [cell_formula, inverse_vertical, and_comm, or_comm] using hp
      · subst e
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [turn_up, turn_one_up, q_inverse, one_sub_one]
  · rintro ⟨f, ⟨a, ha⟩, he⟩
    rcases ha with hf | hf
    · rcases hf with ⟨hf, hp⟩
      refine ⟨GaussianQuarterTurn a, ?_⟩
      right
      refine ⟨?_, ?_⟩
      · subst f
        rw [← he]
        simp [Finset.image_insert, turn_right, pair_swap,
          ]
      · simpa [cell_formula, quarter_inverse, forward_formula, and_comm, or_comm] using hp
    · rcases hf with ⟨hf, hp⟩
      refine ⟨GaussianQuarterTurn a - 1, ?_⟩
      left
      refine ⟨?_, ?_⟩
      · subst f
        rw [← he]
        simp [Finset.image_insert, turn_up, pair_swap,
          add_comm]
      · simpa [cell_formula, inverse_horizontal, forward_formula] using hp

end QuarterTurnFormulas

private theorem quarterTurnCentroid (T : ProtoTile) :
    TileCentroid (TileQuarterTurn T) = (-(TileCentroid T).2, (TileCentroid T).1) := by
  have quarter_re_cast := QuarterTurnFormulas.quarter_re_cast
  have quarter_im_cast := QuarterTurnFormulas.quarter_im_cast
  have quarter_re_base := QuarterTurnFormulas.quarter_re_base
  have quarter_im_base := QuarterTurnFormulas.quarter_im_base
  dsimp [TileQuarterTurn]
  by_cases h : T.cells.Nonempty
  · have hinj : Function.Injective (fun x : GaussianInt => GaussianQuarterTurn x - 1) := by
      intro a b hab
      rcases a with ⟨a, c⟩
      rcases b with ⟨b, d⟩
      simp only [GaussianQuarterTurn, Int.reduceNeg, sub_left_inj, Zsqrtd.mk.injEq, neg_inj]
          at hab ⊢
      exact ⟨hab.2, hab.1⟩
    have coordRe (x : GaussianInt) :
        (GaussianInt.toComplex x).re = (x.re : Real) := by
      exact (GaussianInt.intCast_re x).symm
    have coordIm (x : GaussianInt) :
        (GaussianInt.toComplex x).im = (x.im : Real) := by
      exact (GaussianInt.intCast_im x).symm
    have sumReInt (x : GaussianInt) :
        ((GaussianQuarterTurn x - 1).re : Real) = -(x.im : Real) - 1 :=
      quarter_re_cast x
    have sumImInt (x : GaussianInt) :
        ((GaussianQuarterTurn x - 1).im : Real) = (x.re : Real) :=
      quarter_im_cast x
    simp only [TileCentroid, Finset.image_nonempty, h, ↓reduceIte, Int.reduceNeg,
        Int.cast_sum, GaussianInt.intCast_re, one_div, GaussianInt.intCast_im, neg_add_rev,
        Prod.mk.injEq, add_left_inj]
    rw [Finset.card_image_of_injective T.cells hinj]
    rw [Finset.sum_image hinj.injOn]
    rw [Finset.sum_image hinj.injOn]
    simp only [coordRe, coordIm, sumReInt, sumImInt,
      Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    have cardReal : (Finset.card T.cells : Real) ≠ 0 := by
      exact_mod_cast h.card_pos.ne'
    constructor
    · field_simp [cardReal]
      rw [Finset.sum_const]
      ring
    · simp
  · simp [TileCentroid, h, quarter_re_base, quarter_im_base]

theorem TileQuarterTurnFormulas : ∀ T : ProtoTile,
    (TileQuarterTurn T).cells =
      T.cells.image (fun x => GaussianQuarterTurn x - 1) ∧
    (TileQuarterTurn T).anchor = GaussianQuarterTurn T.anchor ∧
    ((TileQuarterTurn T).cells = ∅ ↔ T.cells = ∅) ∧
    TileRealization (TileQuarterTurn T) =
      (fun p : Real × Real => (-p.2, p.1)) '' TileRealization T ∧
    TileCentroid (TileQuarterTurn T) =
      (-(TileCentroid T).2, (TileCentroid T).1) ∧
    FootprintVertices (TileQuarterTurn T) =
      GaussianQuarterTurn '' FootprintVertices T ∧
    FootprintEdges (TileQuarterTurn T) =
      (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
        FootprintEdges T ∧
    BoundaryFootprintVertices (TileQuarterTurn T) =
      GaussianQuarterTurn '' BoundaryFootprintVertices T ∧
    BoundaryFootprintEdges (TileQuarterTurn T) =
      (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
        BoundaryFootprintEdges T := by
-- BODY
  intro T
  have quarter_re_cast (x : GaussianInt) :
      ((GaussianQuarterTurn x - 1).re : Real) = -(x.im : Real) - 1 :=
          QuarterTurnFormulas.quarter_re_cast x
  have quarter_im_cast (x : GaussianInt) :
      ((GaussianQuarterTurn x - 1).im : Real) = (x.re : Real) :=
          QuarterTurnFormulas.quarter_im_cast x
  have turn_up (a : GaussianInt) :
      GaussianQuarterTurn (a + ⟨0, 1⟩) = GaussianQuarterTurn a - 1 := QuarterTurnFormulas.turn_up a
  have turn_right (a : GaussianInt) :
      GaussianQuarterTurn (a + 1) = GaussianQuarterTurn a + ⟨0, 1⟩ :=
          QuarterTurnFormulas.turn_right a
  have turn_up_right (a : GaussianInt) :
      GaussianQuarterTurn (a + 1 + ⟨0, 1⟩) =
        GaussianQuarterTurn a - 1 + ⟨0, 1⟩ := QuarterTurnFormulas.turn_up_right a
  have minus_one_add_one (u : GaussianInt) : u - 1 + 1 = u :=
      QuarterTurnFormulas.minus_one_add_one u
  have minus_one_add_up (u : GaussianInt) :
      u - 1 + ⟨0, 1⟩ = ⟨u.re - 1, u.im + 1⟩ := QuarterTurnFormulas.minus_one_add_up u
  have pair_swap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} :=
      GaussianCoordinateFacts.pairSwap u v
  dsimp [TileQuarterTurn]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp
  constructor
  · ext p
    simp only [TileRealization, ClosedSquareRealization, Set.mem_iUnion,
      Set.mem_image, Set.mem_Icc, Prod.le_def, Finset.mem_image]
    constructor
    · rintro ⟨i, ⟨j, hj, rfl⟩, hlow, hupp⟩
      refine ⟨(p.2, -p.1), ?_, ?_⟩
      · rw [quarter_re_cast, quarter_im_cast] at hlow hupp
        rcases hlow with ⟨h₁, h₂⟩
        rcases hupp with ⟨h₃, h₄⟩
        simp only []
        refine ⟨j, hj, ?_⟩
        refine ⟨⟨h₂, ?_⟩, h₄, ?_⟩
        · norm_num at h₁ h₃ ⊢
          linarith [h₁, h₃]
        · norm_num at h₁ h₃ ⊢
          linarith [h₁, h₃]
      · simp
    · rintro ⟨x, ⟨i, hi, hlow, hupp⟩, rfl⟩
      refine ⟨GaussianQuarterTurn i - 1, ⟨i, hi, rfl⟩, ?_, ?_⟩
      · rw [quarter_re_cast, quarter_im_cast]
        rcases hlow with ⟨h₁, h₂⟩
        rcases hupp with ⟨h₃, h₄⟩
        simp only []
        constructor <;> linarith
      · rw [quarter_re_cast, quarter_im_cast]
        constructor <;> linarith
  constructor
  · exact quarterTurnCentroid T
  constructor
  · ext v
    by_cases h : T.cells.Nonempty
    · have hnew : (T.cells.image (fun x => GaussianQuarterTurn x - 1)).Nonempty :=
        h.image _
      simp only [FootprintVertices, hnew, ↓reduceIte, Finset.mem_image, Int.reduceNeg,
          exists_exists_and_eq_and, sub_add_cancel, Set.mem_ofPred_eq, h, Set.mem_image]
      constructor
      · rintro ⟨a, ha, hv⟩
        rcases hv with rfl | rfl | rfl | rfl
        · refine ⟨a + ⟨0, 1⟩, ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
          exact turn_up a
        · refine ⟨a, ⟨a, ha, Or.inl rfl⟩, ?_⟩
          simp [GaussianQuarterTurn]
        · refine ⟨a + 1 + ⟨0, 1⟩,
            ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
          exact turn_up_right a
        · refine ⟨a + 1, ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
          exact turn_right a
      · rintro ⟨x, ⟨a, ha, hx⟩, hv⟩
        refine ⟨a, ha, ?_⟩
        rcases hx with rfl | rfl | rfl | rfl
        · refine Or.inr (Or.inl ?_)
          rw [← hv]
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [← hv]
          exact turn_right a
        · refine Or.inl ?_
          rw [← hv]
          exact turn_up a
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [← hv]
          exact turn_up_right a
    · simp [FootprintVertices, h, GaussianQuarterTurn]
  constructor
  · ext e
    simp only [FootprintEdges, Set.mem_ofPred_eq]
    have turn_shift (a : GaussianInt) :
        GaussianQuarterTurn (a + 1) - 1 =
          GaussianQuarterTurn a - 1 + ⟨0, 1⟩ := by
      rw [← turn_up (a + 1), turn_up_right]
    constructor
    · rintro ⟨z, hz, he⟩
      rcases Finset.mem_image.mp hz with ⟨a, ha, hza⟩
      subst z
      rcases he with h0 | h1 | h2 | h3
      · refine ⟨{a, a + ⟨0, 1⟩}, ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
        rw [h0]
        simp [Finset.image_insert, turn_up, pair_swap, minus_one_add_one,
          ]
      · refine ⟨{a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩},
          ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
        rw [h1]
        simp [Finset.image_insert, turn_up, pair_swap,
          minus_one_add_up, turn_shift]
      · refine ⟨{a, a + 1}, ⟨a, ha, Or.inl rfl⟩, ?_⟩
        rw [h2]
        simp [Finset.image_insert, turn_right, pair_swap, minus_one_add_one,
          ]
      · refine ⟨{a + 1, a + 1 + ⟨0, 1⟩},
          ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
        rw [h3]
        simp [Finset.image_insert, turn_right, turn_up_right, pair_swap,
          minus_one_add_one, minus_one_add_up]
    · rintro ⟨f, ⟨a, ha, hf⟩, he⟩
      refine ⟨GaussianQuarterTurn a - 1,
        Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
      rcases hf with h0 | h1 | h2 | h3
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [← he, h0]
        simp [Finset.image_insert, turn_right, pair_swap,
          minus_one_add_one]
      · refine Or.inl ?_
        rw [← he, h1]
        simp [Finset.image_insert, turn_up, pair_swap, minus_one_add_one,
          ]
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [← he, h2]
        simp [Finset.image_insert, turn_right, turn_up_right, pair_swap,
          minus_one_add_one, minus_one_add_up]
      · refine Or.inr (Or.inl ?_)
        rw [← he, h3]
        simp only [Int.reduceNeg, pair_swap, Finset.image_insert, turn_up,
            Finset.image_singleton, minus_one_add_up]
        rw [turn_shift, ← minus_one_add_up]
  have edge_formula :
        BoundaryFootprintEdges (TileQuarterTurn T) =
          (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) ''
            BoundaryFootprintEdges T := QuarterTurnFormulas.edge_formula T
  constructor
  · by_cases h : T.cells.Nonempty
    · simp only [BoundaryFootprintVertices, ite_eq_left h]
      have imageNonempty : (T.cells.image (fun x => GaussianQuarterTurn x - 1)).Nonempty :=
        h.image _
      simp only [ite_eq_left imageNonempty]
      change {v | ∃ e ∈ BoundaryFootprintEdges (TileQuarterTurn T), v ∈ e} = _
      rw [edge_formula]
      ext v
      constructor
      · rintro ⟨e, ⟨f, hf, rfl⟩, hv⟩
        rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
        exact ⟨z, ⟨f, hf, hz⟩, rfl⟩
      · rintro ⟨z, ⟨f, hf, hz⟩, rfl⟩
        exact ⟨f.image GaussianQuarterTurn, ⟨f, hf, rfl⟩,
          Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    · simp [BoundaryFootprintVertices, h,
        GaussianQuarterTurn]
  · exact edge_formula

end ApollonianSuperharmonic

end
