/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership

-- [TABLET NODE: P4670T1ComplementReflection]

/-!
# P4670T1ComplementReflection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ComplementReflectionConstruction

private noncomputable abbrev H (c : ℝ × ℝ) : Real × Real → Real × Real := by
  classical
  exact fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)

private theorem hmemAB (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hAB : TileRealization B = (H
    c) '' TileRealization A) (p : Real × Real) : p ∈ TileRealization A ↔
      (H c) p ∈ TileRealization B := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  change (TileRealization B = H '' TileRealization A) at hAB
  change (p ∈ TileRealization A ↔
      H p ∈ TileRealization B)
  rw [hAB]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨q, hq, hqp⟩
    have : q = p := by
      obtain ⟨hx, hy⟩ := Prod.mk.inj hqp
      ext <;> linarith
    exact this ▸ hq

private theorem hmemO (O : ProtoTile) (c : ℝ × ℝ) (hO : TileRealization O = (H c) ''
    TileRealization O) (p : Real × Real) : p ∈ TileRealization O ↔
      (H c) p ∈ TileRealization O := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  change (TileRealization O = H '' TileRealization O) at hO
  change (p ∈ TileRealization O ↔
      H p ∈ TileRealization O)
  constructor
  · intro hp
    rw [hO]
    exact ⟨p, hp, rfl⟩
  · intro hp
    have hHp : H p ∈ H '' TileRealization O := by
      rw [← hO]
      exact hp
    obtain ⟨q, hq, hqp⟩ := hHp
    have : q = p := by
      obtain ⟨hx, hy⟩ := Prod.mk.inj hqp
      ext <;> linarith
    subst q
    exact hq

private theorem hbackAB (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hmemAB : ∀ (p : ℝ × ℝ), p ∈
    TileRealization A ↔ (H c) p ∈ TileRealization B) (p : Real × Real) : p ∈ TileRealization B ↔
      (H c) p ∈ TileRealization A := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ H p ∈ TileRealization B) at hmemAB
  change (p ∈ TileRealization B ↔
      H p ∈ TileRealization A)
  constructor
  · intro hp
    have hHH : H (H p) = p := by dsimp [H]; ext <;> ring
    have hp' : H (H p) ∈ TileRealization B := by simpa only [hHH] using hp
    exact (hmemAB _).mpr hp'
  · intro hp
    have hp' := (hmemAB _).mp hp
    have hHH : H (H p) = p := by dsimp [H]; ext <;> ring
    simpa only [hHH] using hp'

private theorem hneB (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hA : Finset.Nonempty A.cells)
    (hmemAB : ∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ (H c) p ∈ TileRealization B) :
    B.cells.Nonempty := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ H p ∈ TileRealization B) at hmemAB
  obtain ⟨q, hq⟩ := hA
  have hp : GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real) ∈
      TileRealization A := (P3776T1CellCenterMembership A q).2 hq
  have hpr := (hmemAB _).mp hp
  simp only [TileRealization, Set.mem_iUnion] at hpr
  obtain ⟨z, hz, _⟩ := hpr
  exact ⟨z, hz⟩

private noncomputable abbrev amax (A : ProtoTile) (hA : Finset.Nonempty A.cells) : Int := by
  classical
  exact (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)

private noncomputable abbrev bmin (B : ProtoTile) (hneB : Finset.Nonempty B.cells) : Int := by
  classical
  exact (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)

private theorem hmaxmem (A : ProtoTile) (hA : Finset.Nonempty A.cells) : (amax A hA) ∈
    A.cells.image (fun z => z.re) := by
  classical
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  change (amax ∈ A.cells.image (fun z => z.re))
  exact Finset.max'_mem _ _

private theorem hbminmem (B : ProtoTile) (hneB : Finset.Nonempty B.cells) : (bmin B hneB) ∈
    B.cells.image (fun z => z.re) := by
  classical
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change (bmin ∈ B.cells.image (fun z => z.re))
  exact Finset.min'_mem _ _

private theorem hpointA (A : ProtoTile) (hA : Finset.Nonempty A.cells) (qa : LatticeCell) (haq :
    qa ∈ A.cells) (haqre : qa.re = (amax A hA)) : ((((amax A hA) : Int) : Real) + 1,
      (qa.im : Real)) ∈ TileRealization A := by
  classical
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  change (qa.re = amax) at haqre
  change ((((amax : Int) : Real) + 1,
      (qa.im : Real)) ∈ TileRealization A)
  simp only [TileRealization, Set.mem_iUnion]
  refine ⟨qa, haq, ?_⟩
  simp [ClosedSquareRealization, haqre, Set.mem_Icc, Prod.le_def]

private theorem hpointB (B : ProtoTile) (hneB : Finset.Nonempty B.cells) (qb : LatticeCell) (hqb
    : qb ∈ B.cells) (hqbim : qb.re = (bmin B hneB)) : ((((bmin B hneB) : Int) : Real), (qb.im :
    Real)) ∈
      TileRealization B := by
  classical
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change (qb.re = bmin) at hqbim
  change ((((bmin : Int) : Real), (qb.im : Real)) ∈
      TileRealization B)
  simp only [TileRealization, Set.mem_iUnion]
  refine ⟨qb, hqb, ?_⟩
  simp [ClosedSquareRealization, hqbim, Set.mem_Icc, Prod.le_def]

private theorem hpointAtoB (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hA : Finset.Nonempty
    A.cells) (hmemAB : ∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ (H c) p ∈ TileRealization B) (qa :
    LatticeCell) (hpointA : ((↑(amax A hA) : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization A) : (H c)
    ((↑(amax A hA) : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization B := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ H p ∈ TileRealization B) at hmemAB
  change (((↑amax : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization A) at hpointA
  change (H ((↑amax : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization B)
  exact (hmemAB _).mp hpointA

private theorem hpointBtoA (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hbackAB : ∀ (p : ℝ × ℝ),
    p ∈ TileRealization B ↔ (H c) p ∈ TileRealization A) (hneB : Finset.Nonempty B.cells) (qb :
    LatticeCell) (hpointB : ((↑(bmin B hneB) : ℝ), (↑qb.im : ℝ)) ∈ TileRealization B) : (H c)
    ((↑(bmin B hneB) : ℝ), (↑qb.im : ℝ)) ∈ TileRealization A := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization B ↔ H p ∈ TileRealization A) at hbackAB
  change (((↑bmin : ℝ), (↑qb.im : ℝ)) ∈ TileRealization B) at hpointB
  change (H ((↑bmin : ℝ), (↑qb.im : ℝ)) ∈ TileRealization A)
  exact (hbackAB _).mp hpointB

private theorem hmaxbound (A : ProtoTile) (hA : Finset.Nonempty A.cells) (p : Real × Real) (hp :
    p ∈ TileRealization A) :
      p.1 ≤ ((amax A hA) : Real) + 1 := by
  classical
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  change (p.1 ≤ (amax : Real) + 1)
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  have hzr : z.re ≤ amax := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpz
  exact le_trans hpz.2.1 (by exact_mod_cast (Int.add_le_add_right hzr 1))

private theorem hbminbound (B : ProtoTile) (hneB : Finset.Nonempty B.cells) (p : Real × Real) (hp
    : p ∈ TileRealization B) :
      ((bmin B hneB) : Real) ≤ p.1 := by
  classical
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change ((bmin : Real) ≤ p.1)
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpz
  have hzr : bmin ≤ z.re := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  exact le_trans (by exact_mod_cast hzr) hpz.1.1

private theorem hxb (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hA : Finset.Nonempty A.cells)
    (hneB : Finset.Nonempty B.cells) (qa : LatticeCell) (qb : LatticeCell) (hpointAtoB : (H c)
    ((↑(amax A hA) : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization B) (hpointBtoA : (H c) ((↑(bmin B
    hneB) : ℝ), (↑qb.im : ℝ)) ∈ TileRealization A) (hmaxbound : ∀ p ∈ TileRealization A, p.1 ≤
    (↑(amax A hA) : ℝ) + 1) (hbminbound : ∀ p ∈ TileRealization B, (↑(bmin B hneB) : ℝ) ≤ p.1) :
    ((bmin B hneB) : Real) = 2 * c.1 - (((amax A hA) : Real) + 1) := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change (H ((↑amax : ℝ) + 1, (↑qa.im : ℝ)) ∈ TileRealization B) at hpointAtoB
  change (H ((↑bmin : ℝ), (↑qb.im : ℝ)) ∈ TileRealization A) at hpointBtoA
  change (∀ p ∈ TileRealization A, p.1 ≤ (↑amax : ℝ) + 1) at hmaxbound
  change (∀ p ∈ TileRealization B, (↑bmin : ℝ) ≤ p.1) at hbminbound
  change ((bmin : Real) = 2 * c.1 - ((amax : Real) + 1))
  apply le_antisymm
  · have hb := hbminbound _ hpointAtoB
    exact hb
  · have ha := hmaxbound _ hpointBtoA
    dsimp [H] at hpointBtoA
    linarith

private theorem hcx (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hA : Finset.Nonempty A.cells)
    (hneB : Finset.Nonempty B.cells) (hxb : (↑(bmin B hneB) : ℝ) = 2 * c.1 - ((↑(amax A hA) : ℝ)
    + 1)) : ∃ dx : Int, (dx : Real) = 2 * c.1 := by
  classical
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  change ((↑bmin : ℝ) = 2 * c.1 - ((↑amax : ℝ) + 1)) at hxb
  refine ⟨bmin + amax + 1, ?_⟩
  rw [Int.cast_add, Int.cast_add, Int.cast_one]
  linarith [hxb]

private noncomputable abbrev aimax (A : ProtoTile) (hA : Finset.Nonempty A.cells) : Int := by
  classical
  exact (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)

private noncomputable abbrev bimin (B : ProtoTile) (hneB : Finset.Nonempty B.cells) : Int := by
  classical
  exact (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)

private theorem haimem (A : ProtoTile) (hA : Finset.Nonempty A.cells) : (aimax A hA) ∈
    A.cells.image (fun z => z.im) := by
  classical
  let aimax : Int := (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)
  change (aimax ∈ A.cells.image (fun z => z.im))
  exact Finset.max'_mem _ _

private theorem hbimem (B : ProtoTile) (hneB : Finset.Nonempty B.cells) : (bimin B hneB) ∈
    B.cells.image (fun z => z.im) := by
  classical
  let bimin : Int := (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)
  change (bimin ∈ B.cells.image (fun z => z.im))
  exact Finset.min'_mem _ _

private theorem hpointAy (A : ProtoTile) (hA : Finset.Nonempty A.cells) (qay : LatticeCell) (haqy
    : qay ∈ A.cells) (haqim : qay.im = (aimax A hA)) : ((qay.re : Real), ((aimax A hA) : Real) +
    1) ∈ TileRealization A := by
  classical
  let aimax : Int := (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)
  change (qay.im = aimax) at haqim
  change (((qay.re : Real), (aimax : Real) + 1) ∈ TileRealization A)
  simp only [TileRealization, Set.mem_iUnion]
  refine ⟨qay, haqy, ?_⟩
  simp [ClosedSquareRealization, haqim, Set.mem_Icc, Prod.le_def]

private theorem hpointBy (B : ProtoTile) (hneB : Finset.Nonempty B.cells) (qby : LatticeCell)
    (hqby : qby ∈ B.cells) (hqbim' : qby.im = (bimin B hneB)) : ((qby.re : Real), ((bimin B hneB)
    : Real)) ∈ TileRealization B := by
  classical
  let bimin : Int := (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)
  change (qby.im = bimin) at hqbim'
  change (((qby.re : Real), (bimin : Real)) ∈ TileRealization B)
  simp only [TileRealization, Set.mem_iUnion]
  refine ⟨qby, hqby, ?_⟩
  simp [ClosedSquareRealization, hqbim', Set.mem_Icc, Prod.le_def]

private theorem hmaxY (A : ProtoTile) (hA : Finset.Nonempty A.cells) (p : Real × Real) (hp : p ∈
    TileRealization A) :
      p.2 ≤ ((aimax A hA) : Real) + 1 := by
  classical
  let aimax : Int := (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)
  change (p.2 ≤ (aimax : Real) + 1)
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  have hzr : z.im ≤ aimax := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpz
  exact le_trans hpz.2.2 (by exact_mod_cast (Int.add_le_add_right hzr 1))

private theorem hbminY (B : ProtoTile) (hneB : Finset.Nonempty B.cells) (p : Real × Real) (hp : p
    ∈ TileRealization B) :
      ((bimin B hneB) : Real) ≤ p.2 := by
  classical
  let bimin : Int := (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)
  change ((bimin : Real) ≤ p.2)
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpz
  have hzr : bimin ≤ z.im := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  exact le_trans (by exact_mod_cast hzr) hpz.1.2

private theorem hcy (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hA : Finset.Nonempty A.cells)
    (hmemAB : ∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ (H c) p ∈ TileRealization B) (hbackAB : ∀ (p
    : ℝ × ℝ), p ∈ TileRealization B ↔ (H c) p ∈ TileRealization A) (hneB : Finset.Nonempty
    B.cells) (qay : LatticeCell) (qby : LatticeCell) (hpointAy : ((↑qay.re : ℝ), (↑(aimax A hA) :
    ℝ) + 1) ∈ TileRealization A) (hpointBy : ((↑qby.re : ℝ), (↑(bimin B hneB) : ℝ)) ∈
    TileRealization B) (hmaxY : ∀ p ∈ TileRealization A, p.2 ≤ (↑(aimax A hA) : ℝ) + 1) (hbminY :
    ∀ p ∈ TileRealization B, (↑(bimin B hneB) : ℝ) ≤ p.2) : ∃ dy : Int, (dy : Real) = 2 * c.2 := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let aimax : Int := (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)
  let bimin : Int := (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ H p ∈ TileRealization B) at hmemAB
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization B ↔ H p ∈ TileRealization A) at hbackAB
  change (((↑qay.re : ℝ), (↑aimax : ℝ) + 1) ∈ TileRealization A) at hpointAy
  change (((↑qby.re : ℝ), (↑bimin : ℝ)) ∈ TileRealization B) at hpointBy
  change (∀ p ∈ TileRealization A, p.2 ≤ (↑aimax : ℝ) + 1) at hmaxY
  change (∀ p ∈ TileRealization B, (↑bimin : ℝ) ≤ p.2) at hbminY
  have hby := (hmemAB _).mp hpointAy
  have hbacky := (hbackAB _).mp hpointBy
  have hbi : (bimin : Real) = 2 * c.2 - ((aimax : Real) + 1) := by
    apply le_antisymm
    · exact hbminY _ hby
    · have ha := hmaxY _ hbacky
      dsimp [H] at hbacky
      linarith
  refine ⟨bimin + aimax + 1, ?_⟩
  rw [Int.cast_add, Int.cast_add, Int.cast_one]
  linarith [hbi]

private noncomputable abbrev w (dx : ℤ) (dy : ℤ) : GaussianInt := by
  classical
  exact ⟨dx, dy⟩

private theorem hw (c : ℝ × ℝ) (dx : ℤ) (hdx : (↑dx : ℝ) = 2 * c.1) (dy : ℤ) (hdy : (↑dy : ℝ) = 2
    * c.2) : GaussianRealPoint (w dx dy) = (2 * c.1, 2 * c.2) := by
  classical
  let w : GaussianInt := ⟨dx, dy⟩
  change (GaussianRealPoint w = (2 * c.1, 2 * c.2))
  change ((dx : Real), (dy : Real)) = (2 * c.1, 2 * c.2)
  exact Prod.ext hdx hdy

private noncomputable abbrev f (dx : ℤ) (dy : ℤ) : GaussianInt → GaussianInt := by
  classical
  let w : GaussianInt := ⟨dx, dy⟩
  exact fun q => w - q - 1 - ⟨0, 1⟩

private theorem Hcenter (c : ℝ × ℝ) (dx : ℤ) (hdx : (↑dx : ℝ) = 2 * c.1) (dy : ℤ) (hdy : (↑dy :
    ℝ) = 2 * c.2) (hw : GaussianRealPoint (w dx dy) = (2 * c.1, 2 * c.2)) (q : GaussianInt) :
      (H c) (GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real)) =
        GaussianRealPoint ((f dx dy) q) + ((1 / 2, 1 / 2) : Real × Real) := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (GaussianRealPoint w = (2 * c.1, 2 * c.2)) at hw
  change (H (GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real)) =
        GaussianRealPoint (f q) + ((1 / 2, 1 / 2) : Real × Real))
  have hx := congrArg Prod.fst hw
  have hy := congrArg Prod.snd hw
  dsimp [GaussianRealPoint] at hx hy
  change (2 * c.1 - ((q.re : Real) + 1 / 2),
    2 * c.2 - ((q.im : Real) + 1 / 2)) =
    ((((w.re - q.re - 1 - 0 : Int) : Real) + 1 / 2),
      (((w.im - q.im - 0 - 1 : Int) : Real) + 1 / 2))
  push_cast
  exact Prod.ext (by linarith) (by linarith)

private theorem hcellAB (A : ProtoTile) (B : ProtoTile) (c : ℝ × ℝ) (hmemAB : ∀ (p : ℝ × ℝ), p ∈
    TileRealization A ↔ (H c) p ∈ TileRealization B) (dx : ℤ) (dy : ℤ) (Hcenter : ∀ (q :
    GaussianInt), (H c) (GaussianRealPoint q + (1 / 2, 1 / 2)) = GaussianRealPoint ((f dx dy) q)
    + (1 / 2, 1 / 2)) (q : GaussianInt) : q ∈ A.cells ↔
      (f dx dy) q ∈ B.cells := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization A ↔ H p ∈ TileRealization B) at hmemAB
  change (∀ (q : GaussianInt), H (GaussianRealPoint q + (1 / 2, 1 / 2)) = GaussianRealPoint (f q)
      + (1 / 2, 1 / 2)) at Hcenter
  change (q ∈ A.cells ↔
      f q ∈ B.cells)
  rw [← P3776T1CellCenterMembership, ← P3776T1CellCenterMembership,
    hmemAB, Hcenter]

private theorem hcellO (O : ProtoTile) (c : ℝ × ℝ) (hmemO : ∀ (p : ℝ × ℝ), p ∈ TileRealization O
    ↔ (H c) p ∈ TileRealization O) (dx : ℤ) (dy : ℤ) (Hcenter : ∀ (q : GaussianInt), (H c)
    (GaussianRealPoint q + (1 / 2, 1 / 2)) = GaussianRealPoint ((f dx dy) q) + (1 / 2, 1 / 2)) (q
    : GaussianInt) : q ∈ O.cells ↔
      (f dx dy) q ∈ O.cells := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (∀ (p : ℝ × ℝ), p ∈ TileRealization O ↔ H p ∈ TileRealization O) at hmemO
  change (∀ (q : GaussianInt), H (GaussianRealPoint q + (1 / 2, 1 / 2)) = GaussianRealPoint (f q)
      + (1 / 2, 1 / 2)) at Hcenter
  change (q ∈ O.cells ↔
      f q ∈ O.cells)
  rw [← P3776T1CellCenterMembership, ← P3776T1CellCenterMembership,
    hmemO, Hcenter]

private theorem hf (dx : ℤ) (dy : ℤ) : Function.Involutive (f dx dy) := by
  classical
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (Function.Involutive f)
  intro q
  dsimp [f]
  abel

private theorem hcellComp (A : ProtoTile) (B : ProtoTile) (O : ProtoTile) (dx : ℤ) (dy : ℤ)
    (hcellAB : ∀ (q : GaussianInt), q ∈ A.cells ↔ (f dx dy) q ∈ B.cells) (hcellO : ∀ (q :
    GaussianInt), q ∈ O.cells ↔ (f dx dy) q ∈ O.cells) (q : GaussianInt) :
      q ∈ A.cells \ O.cells ↔ (f dx dy) q ∈ B.cells \ O.cells := by
  classical
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (∀ (q : GaussianInt), q ∈ A.cells ↔ f q ∈ B.cells) at hcellAB
  change (∀ (q : GaussianInt), q ∈ O.cells ↔ f q ∈ O.cells) at hcellO
  change (q ∈ A.cells \ O.cells ↔ f q ∈ B.cells \ O.cells)
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  exact ⟨fun ⟨ha, hno⟩ =>
      ⟨(hcellAB q).mp ha, fun hqo => hno ((hcellO q).mpr hqo)⟩,
    fun ⟨hb, hno⟩ =>
      ⟨(hcellAB q).mpr hb, fun hqo => hno ((hcellO q).mp hqo)⟩⟩

private theorem hsquare (c : ℝ × ℝ) (dx : ℤ) (dy : ℤ) (hw : GaussianRealPoint (w dx dy) = (2 *
    c.1, 2 * c.2)) (q : GaussianInt) (p : Real × Real) :
      p ∈ ClosedSquareRealization q ↔ (H c) p ∈ ClosedSquareRealization ((f dx dy) q) := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (GaussianRealPoint w = (2 * c.1, 2 * c.2)) at hw
  change (p ∈ ClosedSquareRealization q ↔ H p ∈ ClosedSquareRealization (f q))
  have hx := congrArg Prod.fst hw
  have hy := congrArg Prod.snd hw
  dsimp [GaussianRealPoint] at hx hy
  have hfre : ((f q).re : Real) = 2 * c.1 - (q.re : Real) - 1 := by
    change ((w.re - q.re - 1 - 0 : Int) : Real) = _
    push_cast
    rw [hx]
    ring
  have hfim : ((f q).im : Real) = 2 * c.2 - (q.im : Real) - 1 := by
    change ((w.im - q.im - 0 - 1 : Int) : Real) = _
    push_cast
    rw [hy]
    ring
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
  constructor
  · rintro ⟨⟨hxl, hyl⟩, ⟨hxu, hyu⟩⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp [H] at *
    · rw [hfre]; linarith
    · rw [hfim]; linarith
    · rw [hfre]; linarith
    · rw [hfim]; linarith
  · rintro ⟨⟨hxl, hyl⟩, ⟨hxu, hyu⟩⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp [H] at *
    · rw [hfre] at hxl; linarith
    · rw [hfim] at hyl; linarith
    · rw [hfre] at hxu; linarith
    · rw [hfim] at hyu; linarith

private theorem hreal (A : ProtoTile) (B : ProtoTile) (O : ProtoTile) (c : ℝ × ℝ) (dx : ℤ) (dy :
    ℤ) (hf : Function.Involutive (f dx dy)) (hcellComp : ∀ (q : GaussianInt), q ∈ A.cells \
    O.cells ↔ (f dx dy) q ∈ B.cells \ O.cells) (hsquare : ∀ (q : GaussianInt) (p : ℝ × ℝ), p ∈
    ClosedSquareRealization q ↔ (H c) p ∈ ClosedSquareRealization ((f dx dy) q)) (p : Real × Real) :
      p ∈ TileRealization (TileCellComplement A O) ↔
        (H c) p ∈ TileRealization (TileCellComplement B O) := by
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let w : GaussianInt := ⟨dx, dy⟩
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  change (Function.Involutive f) at hf
  change (∀ (q : GaussianInt), q ∈ A.cells \ O.cells ↔ f q ∈ B.cells \ O.cells) at hcellComp
  change (∀ (q : GaussianInt) (p : ℝ × ℝ), p ∈ ClosedSquareRealization q ↔ H p ∈
      ClosedSquareRealization (f q)) at hsquare
  change (p ∈ TileRealization (TileCellComplement A O) ↔
        H p ∈ TileRealization (TileCellComplement B O))
  constructor
  · intro hp
    simp only [TileCellComplement, TileRealization, Set.mem_iUnion] at hp ⊢
    obtain ⟨q, hq, hpq⟩ := hp
    refine ⟨f q, (hcellComp q).mp hq, (hsquare q p).mp hpq⟩
  · intro hp
    simp only [TileCellComplement, TileRealization, Set.mem_iUnion] at hp ⊢
    obtain ⟨q, hq, hpq⟩ := hp
    refine ⟨f q, ?_, ?_⟩
    · exact (hcellComp (f q)).mpr (by simpa only [hf q] using hq)
    · exact (hsquare (f q) p).mpr (by simpa only [hf q] using hpq)

end ComplementReflectionConstruction

theorem P4670T1ComplementReflection (A B O : ProtoTile) (c : Real × Real)
    (hA : A.cells.Nonempty)
    (hAB : CentrallyReflectedAt c A B)
    (hO : CentrallyReflectedAt c O O) :
    CentrallyReflectedAt c (TileCellComplement A O)
      (TileCellComplement B O) := by
-- BODY
  classical
  let H : Real × Real → Real × Real :=
    fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  change TileRealization B = H '' TileRealization A at hAB
  change TileRealization O = H '' TileRealization O at hO
  have hmemAB (p : Real × Real) : p ∈ TileRealization A ↔
      H p ∈ TileRealization B := ComplementReflectionConstruction.hmemAB A B c hAB p
  have hmemO (p : Real × Real) : p ∈ TileRealization O ↔
      H p ∈ TileRealization O := ComplementReflectionConstruction.hmemO O c hO p
  have hbackAB (p : Real × Real) : p ∈ TileRealization B ↔
      H p ∈ TileRealization A := ComplementReflectionConstruction.hbackAB A B c hmemAB p
  have hneB : B.cells.Nonempty := ComplementReflectionConstruction.hneB A B c hA hmemAB
  let amax : Int := (A.cells.image fun z => z.re).max'
    (Finset.image_nonempty.mpr hA)
  let bmin : Int := (B.cells.image fun z => z.re).min'
    (Finset.image_nonempty.mpr hneB)
  have hmaxmem : amax ∈ A.cells.image (fun z => z.re) := ComplementReflectionConstruction.hmaxmem
      A hA
  have hbminmem : bmin ∈ B.cells.image (fun z => z.re) :=
      ComplementReflectionConstruction.hbminmem B hneB
  obtain ⟨qa, haq, haqre⟩ := Finset.mem_image.mp hmaxmem
  obtain ⟨qb, hqb, hqbim⟩ := Finset.mem_image.mp hbminmem
  have hpointA : (((amax : Int) : Real) + 1,
      (qa.im : Real)) ∈ TileRealization A := ComplementReflectionConstruction.hpointA A hA qa haq
          haqre
  have hpointB : (((bmin : Int) : Real), (qb.im : Real)) ∈
      TileRealization B := ComplementReflectionConstruction.hpointB B hneB qb hqb hqbim
  have hpointAtoB := ComplementReflectionConstruction.hpointAtoB A B c hA hmemAB qa hpointA
  have hpointBtoA := ComplementReflectionConstruction.hpointBtoA A B c hbackAB hneB qb hpointB
  have hmaxbound (p : Real × Real) (hp : p ∈ TileRealization A) :
      p.1 ≤ (amax : Real) + 1 := ComplementReflectionConstruction.hmaxbound A hA p hp
  have hbminbound (p : Real × Real) (hp : p ∈ TileRealization B) :
      (bmin : Real) ≤ p.1 := ComplementReflectionConstruction.hbminbound B hneB p hp
  have hxb : (bmin : Real) = 2 * c.1 - ((amax : Real) + 1) :=
      ComplementReflectionConstruction.hxb A B c hA hneB qa qb hpointAtoB hpointBtoA hmaxbound
      hbminbound
  have hcx : ∃ dx : Int, (dx : Real) = 2 * c.1 := ComplementReflectionConstruction.hcx A B c hA
      hneB hxb
  let aimax : Int := (A.cells.image fun z => z.im).max'
    (Finset.image_nonempty.mpr hA)
  let bimin : Int := (B.cells.image fun z => z.im).min'
    (Finset.image_nonempty.mpr hneB)
  have haimem : aimax ∈ A.cells.image (fun z => z.im) := ComplementReflectionConstruction.haimem
      A hA
  have hbimem : bimin ∈ B.cells.image (fun z => z.im) := ComplementReflectionConstruction.hbimem
      B hneB
  obtain ⟨qay, haqy, haqim⟩ := Finset.mem_image.mp haimem
  obtain ⟨qby, hqby, hqbim'⟩ := Finset.mem_image.mp hbimem
  have hpointAy : ((qay.re : Real), (aimax : Real) + 1) ∈ TileRealization A :=
      ComplementReflectionConstruction.hpointAy A hA qay haqy haqim
  have hpointBy : ((qby.re : Real), (bimin : Real)) ∈ TileRealization B :=
      ComplementReflectionConstruction.hpointBy B hneB qby hqby hqbim'
  have hmaxY (p : Real × Real) (hp : p ∈ TileRealization A) :
      p.2 ≤ (aimax : Real) + 1 := ComplementReflectionConstruction.hmaxY A hA p hp
  have hbminY (p : Real × Real) (hp : p ∈ TileRealization B) :
      (bimin : Real) ≤ p.2 := ComplementReflectionConstruction.hbminY B hneB p hp
  have hcy : ∃ dy : Int, (dy : Real) = 2 * c.2 := ComplementReflectionConstruction.hcy A B c hA
      hmemAB hbackAB hneB qay qby hpointAy hpointBy hmaxY hbminY
  obtain ⟨dx, hdx⟩ := hcx
  obtain ⟨dy, hdy⟩ := hcy
  let w : GaussianInt := ⟨dx, dy⟩
  have hw : GaussianRealPoint w = (2 * c.1, 2 * c.2) := ComplementReflectionConstruction.hw c dx
      hdx dy hdy
  let f : GaussianInt → GaussianInt := fun q => w - q - 1 - ⟨0, 1⟩
  have Hcenter (q : GaussianInt) :
      H (GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real)) =
        GaussianRealPoint (f q) + ((1 / 2, 1 / 2) : Real × Real) :=
            ComplementReflectionConstruction.Hcenter c dx hdx dy hdy hw q
  have hcellAB (q : GaussianInt) : q ∈ A.cells ↔
      f q ∈ B.cells := ComplementReflectionConstruction.hcellAB A B c hmemAB dx dy Hcenter q
  have hcellO (q : GaussianInt) : q ∈ O.cells ↔
      f q ∈ O.cells := ComplementReflectionConstruction.hcellO O c hmemO dx dy Hcenter q
  have hf : Function.Involutive f := ComplementReflectionConstruction.hf dx dy
  have hcellComp (q : GaussianInt) :
      q ∈ A.cells \ O.cells ↔ f q ∈ B.cells \ O.cells :=
          ComplementReflectionConstruction.hcellComp A B O dx dy hcellAB hcellO q
  have hsquare (q : GaussianInt) (p : Real × Real) :
      p ∈ ClosedSquareRealization q ↔ H p ∈ ClosedSquareRealization (f q) :=
          ComplementReflectionConstruction.hsquare c dx dy hw q p
  have hreal (p : Real × Real) :
      p ∈ TileRealization (TileCellComplement A O) ↔
        H p ∈ TileRealization (TileCellComplement B O) := ComplementReflectionConstruction.hreal
            A B O c dx dy hf hcellComp hsquare p
  change TileRealization (TileCellComplement B O) =
    H '' TileRealization (TileCellComplement A O)
  ext p
  constructor
  · intro hp
    have hH : H (H p) = p := by dsimp [H]; ext <;> ring
    have hp' : H p ∈ TileRealization (TileCellComplement A O) := by
      exact (hreal (H p)).mpr (by simpa only [hH] using hp)
    exact ⟨H p, hp', hH⟩
  · rintro ⟨q, hq, rfl⟩
    exact (hreal q).mp hq

end ApollonianSuperharmonic

end
