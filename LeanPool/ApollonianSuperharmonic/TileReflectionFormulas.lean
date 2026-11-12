/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TileReflection

-- [TABLET NODE: TileReflectionFormulas]

/-!
# TileReflectionFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ReflectionFormulas

private noncomputable def f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩

private theorem gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := by
  classical
  rcases u with ⟨u, w⟩
  rcases v with ⟨v, z⟩
  simp_all

private theorem reflection_involutive (z : GaussianInt) :
      GaussianReflection (GaussianReflection z) = z := by
  classical
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  apply gaussian_ext <;> simp [GaussianReflection]

private theorem f_involutive (z : GaussianInt) : f (f z) = z := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (f z) = z)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem reflection_one (z : GaussianInt) :
      GaussianReflection (z + 1) = GaussianReflection z + 1 := by
  classical
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  apply gaussian_ext <;> simp [GaussianReflection]

private theorem reflection_up (z : GaussianInt) :
      GaussianReflection (z + ⟨0, 1⟩) = f z := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (GaussianReflection (z + ⟨0, 1⟩) = f z)
  apply gaussian_ext <;> simp [f, GaussianReflection]; omega

private theorem reflection_one_up (z : GaussianInt) :
      GaussianReflection (z + 1 + ⟨0, 1⟩) = f z + 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (GaussianReflection (z + 1 + ⟨0, 1⟩) = f z + 1)
  apply gaussian_ext <;> simp [f, GaussianReflection]; omega

private theorem f_one (z : GaussianInt) : f (z + 1) = f z + 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (z + 1) = f z + 1)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_up (z : GaussianInt) : f (z + ⟨0, 1⟩) = f z - ⟨0, 1⟩ := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (z + ⟨0, 1⟩) = f z - ⟨0, 1⟩)
  apply gaussian_ext <;> simp [f, GaussianReflection]; omega

private theorem reflection_f (z : GaussianInt) : GaussianReflection (f z) = z + ⟨0, 1⟩ := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (GaussianReflection (f z) = z + ⟨0, 1⟩)
  apply gaussian_ext <;> simp [f, GaussianReflection]; omega

private theorem f_reflection (z : GaussianInt) : f (GaussianReflection z) = z - ⟨0, 1⟩ := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (GaussianReflection z) = z - ⟨0, 1⟩)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_sub_up (z : GaussianInt) : f (z - ⟨0, 1⟩) = GaussianReflection z := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (z - ⟨0, 1⟩) = GaussianReflection z)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_sub_one (z : GaussianInt) : f (z - 1) = f z - 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f (z - 1) = f z - 1)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_add_up (z : GaussianInt) : f z + ⟨0, 1⟩ = GaussianReflection z := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f z + ⟨0, 1⟩ = GaussianReflection z)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_add_one_up (z : GaussianInt) :
      f z + 1 + ⟨0, 1⟩ = GaussianReflection z + 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have gaussian_ext (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := gaussian_ext u v hre him
  change (f z + 1 + ⟨0, 1⟩ = GaussianReflection z + 1)
  apply gaussian_ext <;> simp [f, GaussianReflection]

private theorem f_re_cast (z : GaussianInt) : ((f z).re : Real) = (z.re : Real) := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  change (((f z).re : Real) = (z.re : Real))
  rcases z with ⟨a, b⟩
  simp [f, GaussianReflection]

private theorem f_re (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).re = (GaussianInt.toComplex z).re := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  change ((GaussianInt.toComplex (f z)).re = (GaussianInt.toComplex z).re)
  rcases z with ⟨a, b⟩
  simp [f, GaussianReflection]

private theorem f_im (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).im =
        -(GaussianInt.toComplex z).im - 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  change ((GaussianInt.toComplex (f z)).im =
        -(GaussianInt.toComplex z).im - 1)
  rcases z with ⟨a, b⟩
  simp [f, GaussianReflection]

private theorem reflectedCellRe (z : GaussianInt) :
      (GaussianInt.toComplex (GaussianReflection z - ⟨0, 1⟩)).re =
        (GaussianInt.toComplex z).re := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have f_re (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).re = (GaussianInt.toComplex z).re := f_re z
  change (GaussianInt.toComplex (f z)).re = _
  exact f_re z

private theorem reflectedCellIm (z : GaussianInt) :
      (GaussianInt.toComplex (GaussianReflection z - ⟨0, 1⟩)).im =
        -(GaussianInt.toComplex z).im - 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have f_im (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).im =
        -(GaussianInt.toComplex z).im - 1 := f_im z
  change (GaussianInt.toComplex (f z)).im = _
  exact f_im z

private theorem f_im_cast (z : GaussianInt) :
      ((f z).im : Real) = -(z.im : Real) - 1 := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  change (((f z).im : Real) = -(z.im : Real) - 1)
  rcases z with ⟨a, b⟩
  simp [f, GaussianReflection]

private theorem pair_swap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} := by
  classical
  ext z
  simp [or_comm]

private theorem cell_formula (T : ProtoTile) (z : GaussianInt) :
      z ∈ (TileReflection T).cells ↔ f z ∈ T.cells := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have f_involutive (z : GaussianInt) : f (f z) = z := f_involutive z
  change (z ∈ (TileReflection T).cells ↔ f z ∈ T.cells)
  change z ∈ T.cells.image f ↔ _
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    simpa only [f_involutive] using ha
  · intro hz
    exact Finset.mem_image.mpr ⟨f z, hz, f_involutive z⟩

private theorem edge_formula (T : ProtoTile) :
      BoundaryFootprintEdges (TileReflection T) =
        (fun e : Finset GaussianInt => e.image GaussianReflection) ''
          BoundaryFootprintEdges T := by
  classical
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have reflection_involutive (z : GaussianInt) :
      GaussianReflection (GaussianReflection z) = z := reflection_involutive z
  have f_involutive (z : GaussianInt) : f (f z) = z := f_involutive z
  have reflection_one (z : GaussianInt) :
      GaussianReflection (z + 1) = GaussianReflection z + 1 := reflection_one z
  have reflection_up (z : GaussianInt) :
      GaussianReflection (z + ⟨0, 1⟩) = f z := reflection_up z
  have reflection_f (z : GaussianInt) : GaussianReflection (f z) = z + ⟨0, 1⟩ := reflection_f z
  have f_reflection (z : GaussianInt) : f (GaussianReflection z) = z - ⟨0, 1⟩ := f_reflection z
  have f_sub_up (z : GaussianInt) : f (z - ⟨0, 1⟩) = GaussianReflection z := f_sub_up z
  have f_sub_one (z : GaussianInt) : f (z - 1) = f z - 1 := f_sub_one z
  have f_add_up (z : GaussianInt) : f z + ⟨0, 1⟩ = GaussianReflection z := f_add_up z
  have pair_swap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} := pair_swap u v
  have cell_formula (z : GaussianInt) :
      z ∈ (TileReflection T).cells ↔ f z ∈ T.cells := cell_formula T z
  ext e
  change (∃ z : GaussianInt,
      (e = {z, z + 1} ∧
        ((z ∈ (TileReflection T).cells ∧
            z - ⟨0, 1⟩ ∉ (TileReflection T).cells) ∨
          (z ∉ (TileReflection T).cells ∧
            z - ⟨0, 1⟩ ∈ (TileReflection T).cells))) ∨
      (e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ (TileReflection T).cells ∧
            z - 1 ∉ (TileReflection T).cells) ∨
          (z ∉ (TileReflection T).cells ∧
            z - 1 ∈ (TileReflection T).cells)))) ↔
    ∃ q, q ∈ BoundaryFootprintEdges T ∧
      q.image GaussianReflection = e
  constructor
  · rintro ⟨z, hz⟩
    rcases hz with ⟨he, hp⟩ | ⟨he, hp⟩
    · refine ⟨{GaussianReflection z, GaussianReflection z + 1}, ?_, ?_⟩
      · refine ⟨GaussianReflection z, Or.inl ⟨rfl, ?_⟩⟩
        simpa [cell_formula, f_sub_up, f_reflection, and_comm, or_comm]
          using hp
      · subst e
        simp [Finset.image_insert, reflection_involutive, reflection_one]
    · refine ⟨{f z, f z + ⟨0, 1⟩}, ?_, ?_⟩
      · refine ⟨f z, Or.inr ⟨rfl, ?_⟩⟩
        simpa [cell_formula, f_involutive, f_sub_one] using hp
      · subst e
        simp [Finset.image_insert, reflection_f, reflection_up,
          f_involutive, pair_swap]
  · rintro ⟨q, ⟨a, ha⟩, he⟩
    rcases ha with ⟨hq, hp⟩ | ⟨hq, hp⟩
    · refine ⟨GaussianReflection a, Or.inl ⟨?_, ?_⟩⟩
      · subst q
        rw [← he]
        simp [Finset.image_insert, reflection_one]
      · simpa only [cell_formula, f_reflection, f_sub_up,
          reflection_involutive, not_iff_not, and_comm, or_comm] using hp
    · refine ⟨f a, Or.inr ⟨?_, ?_⟩⟩
      · subst q
        rw [← he]
        simp [Finset.image_insert, reflection_up, f_add_up, pair_swap]
      · simpa [cell_formula, f_involutive, f_sub_one] using hp

end ReflectionFormulas

theorem TileReflectionFormulas : ∀ T : ProtoTile,
    (TileReflection T).cells =
      T.cells.image (fun x => GaussianReflection x - ⟨0, 1⟩) ∧
    (TileReflection T).anchor = GaussianReflection T.anchor ∧
    ((TileReflection T).cells = ∅ ↔ T.cells = ∅) ∧
    TileRealization (TileReflection T) =
      (fun p : Real × Real => (p.1, -p.2)) '' TileRealization T ∧
    TileCentroid (TileReflection T) =
      ((TileCentroid T).1, -(TileCentroid T).2) ∧
    FootprintVertices (TileReflection T) =
      GaussianReflection '' FootprintVertices T ∧
    FootprintEdges (TileReflection T) =
      (fun e : Finset GaussianInt => e.image GaussianReflection) ''
        FootprintEdges T ∧
    BoundaryFootprintVertices (TileReflection T) =
      GaussianReflection '' BoundaryFootprintVertices T ∧
    BoundaryFootprintEdges (TileReflection T) =
      (fun e : Finset GaussianInt => e.image GaussianReflection) ''
        BoundaryFootprintEdges T := by
-- BODY
  intro T
  let f : GaussianInt → GaussianInt := fun z => GaussianReflection z - ⟨0, 1⟩
  have f_involutive (z : GaussianInt) : f (f z) = z := ReflectionFormulas.f_involutive z
  have reflection_one (z : GaussianInt) :
      GaussianReflection (z + 1) = GaussianReflection z + 1 := ReflectionFormulas.reflection_one z
  have reflection_up (z : GaussianInt) :
      GaussianReflection (z + ⟨0, 1⟩) = f z := ReflectionFormulas.reflection_up z
  have reflection_one_up (z : GaussianInt) :
      GaussianReflection (z + 1 + ⟨0, 1⟩) = f z + 1 := ReflectionFormulas.reflection_one_up z
  have f_one (z : GaussianInt) : f (z + 1) = f z + 1 := ReflectionFormulas.f_one z
  have f_add_up (z : GaussianInt) : f z + ⟨0, 1⟩ = GaussianReflection z :=
      ReflectionFormulas.f_add_up z
  have f_add_one_up (z : GaussianInt) :
      f z + 1 + ⟨0, 1⟩ = GaussianReflection z + 1 := ReflectionFormulas.f_add_one_up z
  have f_re_cast (z : GaussianInt) : ((f z).re : Real) = (z.re : Real) :=
      ReflectionFormulas.f_re_cast z
  have f_re (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).re = (GaussianInt.toComplex z).re := ReflectionFormulas.f_re z
  have f_im (z : GaussianInt) :
      (GaussianInt.toComplex (f z)).im =
        -(GaussianInt.toComplex z).im - 1 := ReflectionFormulas.f_im z
  have f_im_cast (z : GaussianInt) :
      ((f z).im : Real) = -(z.im : Real) - 1 := ReflectionFormulas.f_im_cast z
  have pair_swap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} :=
      ReflectionFormulas.pair_swap u v
  dsimp [TileReflection]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp [GaussianReflection]
  constructor
  · ext p
    simp only [TileRealization, ClosedSquareRealization, Set.mem_iUnion,
      Set.mem_image, Set.mem_Icc, Prod.le_def, Finset.mem_image]
    constructor
    · rintro ⟨i, ⟨j, hj, rfl⟩, hlow, hupp⟩
      refine ⟨(p.1, -p.2), ?_, ?_⟩
      · change ((f j).re : Real) ≤ p.1 ∧ ((f j).im : Real) ≤ p.2 at hlow
        change p.1 ≤ ((f j).re : Real) + 1 ∧
          p.2 ≤ ((f j).im : Real) + 1 at hupp
        rw [f_re_cast, f_im_cast] at hlow hupp
        rcases hlow with ⟨h₁, h₂⟩
        rcases hupp with ⟨h₃, h₄⟩
        simp only []
        refine ⟨j, hj, ?_⟩
        exact ⟨⟨h₁, by linarith⟩, h₃, by linarith⟩
      · simp
    · rintro ⟨x, ⟨i, hi, hlow, hupp⟩, rfl⟩
      refine ⟨f i, ⟨i, hi, ?_⟩, ?_, ?_⟩
      · rfl
      · change ((f i).re : Real) ≤ x.1 ∧ ((f i).im : Real) ≤ -x.2
        rw [f_re_cast, f_im_cast]
        rcases hlow with ⟨h₁, h₂⟩
        rcases hupp with ⟨h₃, h₄⟩
        exact ⟨h₁, by linarith⟩
      · change x.1 ≤ ((f i).re : Real) + 1 ∧
          -x.2 ≤ ((f i).im : Real) + 1
        rw [f_re_cast, f_im_cast]
        exact ⟨hupp.1, by linarith [hlow.2]⟩
  constructor
  · by_cases h : T.cells.Nonempty
    · have hinj : Function.Injective f := by
        intro a b hab
        simpa only [f_involutive] using congrArg f hab
      simp? [TileCentroid, h]
      rw [Finset.card_image_of_injective T.cells hinj]
      rw [Finset.sum_image hinj.injOn]
      rw [Finset.sum_image hinj.injOn]
      simp only [f_re, f_im,
        Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, Finset.sum_const]
      have cardReal : (Finset.card T.cells : Real) ≠ 0 := by
        exact_mod_cast h.card_pos.ne'
      constructor
      · trivial
      · field_simp [cardReal]
        ring
    · simp [TileCentroid, h, GaussianReflection]
  constructor
  · ext v
    by_cases h : T.cells.Nonempty
    · have hnew :
          (T.cells.image (fun x => GaussianReflection x - ⟨0, 1⟩)).Nonempty :=
        h.image _
      simp? [FootprintVertices, h, hnew]
      constructor
      · rintro ⟨a, ha, hv⟩
        rcases hv with rfl | rfl | rfl | rfl
        · refine ⟨a + ⟨0, 1⟩, ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
          exact reflection_up a
        · refine ⟨a + 1 + ⟨0, 1⟩,
            ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
          exact reflection_one_up a
        · refine ⟨a, ⟨a, ha, Or.inl rfl⟩, ?_⟩
          rfl
        · refine ⟨a + 1, ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
          rw [reflection_one, ← f_add_one_up]
      · rintro ⟨x, ⟨a, ha, hx⟩, hv⟩
        refine ⟨a, ha, ?_⟩
        rcases hx with rfl | rfl | rfl | rfl
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [← hv]
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [← hv]
          rw [reflection_one, ← f_add_one_up]
        · refine Or.inl ?_
          rw [← hv]
          exact reflection_up a
        · refine Or.inr (Or.inl ?_)
          rw [← hv]
          exact reflection_one_up a
    · simp [FootprintVertices, h, GaussianReflection]
  constructor
  · ext e
    simp only [FootprintEdges, Set.mem_ofPred_eq, Set.mem_image,
      Finset.mem_image]
    constructor
    · rintro ⟨z, ⟨a, ha, rfl⟩, he⟩
      rcases he with h0 | h1 | h2 | h3
      · refine ⟨{a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩},
          ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
        rw [h0]
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [reflection_up, reflection_one_up]
      · refine ⟨{a, a + ⟨0, 1⟩},
          ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
        rw [h1]
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [reflection_up]
        change ({GaussianReflection a, f a} : Finset GaussianInt) =
          {f a, f a + ⟨0, 1⟩}
        rw [f_add_up]
        exact pair_swap _ _
      · refine ⟨{a + 1, a + 1 + ⟨0, 1⟩},
          ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
        rw [h2]
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [reflection_one, reflection_one_up]
        change ({GaussianReflection a + 1, f a + 1} : Finset GaussianInt) =
          {f a + 1, f a + 1 + ⟨0, 1⟩}
        rw [f_add_one_up]
        exact pair_swap _ _
      · refine ⟨{a, a + 1}, ⟨a, ha, Or.inl rfl⟩, ?_⟩
        rw [h3]
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [reflection_one]
        change ({GaussianReflection a, GaussianReflection a + 1} :
          Finset GaussianInt) = {f a + ⟨0, 1⟩, f a + 1 + ⟨0, 1⟩}
        rw [f_add_up, f_add_one_up]
    · rintro ⟨q, ⟨a, ha, hq⟩, he⟩
      refine ⟨f a, ⟨a, ha, rfl⟩, ?_⟩
      rcases hq with h0 | h1 | h2 | h3
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [← he, h0]
        simp [Finset.image_insert, reflection_one, f_add_up, f_add_one_up]
      · refine Or.inr (Or.inl ?_)
        rw [← he, h1]
        simp [Finset.image_insert, reflection_up, f_add_up, pair_swap]
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [← he, h2]
        simp [Finset.image_insert, reflection_one, reflection_one_up,
          f_add_one_up, pair_swap]
      · refine Or.inl ?_
        rw [← he, h3]
        simp [Finset.image_insert, reflection_up, f_one]
  have edge_formula :
      BoundaryFootprintEdges (TileReflection T) =
        (fun e : Finset GaussianInt => e.image GaussianReflection) ''
          BoundaryFootprintEdges T := ReflectionFormulas.edge_formula T
  constructor
  · by_cases h : T.cells.Nonempty
    · simp only [BoundaryFootprintVertices, ite_eq_left h]
      have hnew :
          (T.cells.image (fun x => GaussianReflection x - ⟨0, 1⟩)).Nonempty :=
        h.image _
      simp only [ite_eq_left hnew]
      change {v | ∃ e ∈ BoundaryFootprintEdges (TileReflection T), v ∈ e} = _
      rw [edge_formula]
      ext v
      constructor
      · rintro ⟨e, ⟨q, hq, rfl⟩, hv⟩
        rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
        exact ⟨z, ⟨q, hq, hz⟩, rfl⟩
      · rintro ⟨z, ⟨q, hq, hz⟩, rfl⟩
        exact ⟨q.image GaussianReflection, ⟨q, hq, rfl⟩,
          Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    · have hnew :
          ¬(T.cells.image (fun x => GaussianReflection x - ⟨0, 1⟩)).Nonempty := by
        simpa using h
      simp [BoundaryFootprintVertices, h, GaussianReflection]
  · exact edge_formula

end ApollonianSuperharmonic

end
