/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.DiamondParameter
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: DiamondBaseT2]

/-!
# DiamondBaseT2

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondQuarterTurnConstruction

private noncomputable abbrev k (K : DiamondParameter) : Nat := by
  classical
  exact K.1

private theorem hk (K : DiamondParameter) : 0 < (k K) := by
  classical
  let k : Nat := K.1
  dsimp only [DiamondQuarterTurnConstruction.k] at *
  change (0 < k)
  exact K.2

private theorem mem_domain (K : DiamondParameter) (z : GaussianInt) : z ∈ DiamondCellDomain (k K) ↔
      ∃ y : Nat, y < 2 * (k K) ∧
        (let r := Nat.min (y + 1) (2 * (k K) - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)) := by
  classical
  let k : Nat := K.1
  dsimp only [DiamondQuarterTurnConstruction.k] at *
  change (z ∈ DiamondCellDomain k ↔
      ∃ y : Nat, y < 2 * k ∧
        (let r := Nat.min (y + 1) (2 * k - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)))
  simp only [DiamondCellDomain, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨y, hy, j, hj, hz⟩
    refine ⟨y, hy, ?_⟩
    have hre := congrArg Zsqrtd.re hz
    have him := congrArg Zsqrtd.im hz
    simp only [Nat.cast_min, Nat.cast_add, Nat.cast_one, Int.reduceNeg] at hre him
    have hj' : (j : Int) < 2 * ((y + 1).min (2 * k - y) : Int) := by
      exact_mod_cast hj
    norm_num [Nat.cast_min] at hre ⊢
    have hcast : ((2 * k - y : Nat) : Int) = 2 * (k : Int) - y := by omega
    rw [hcast] at hre ⊢
    refine ⟨him.symm, ?_⟩
    have hmin1 : min ((y : Int) + 1) (2 * (k : Int) - y) ≤ (y : Int) + 1 :=
      min_le_left _ _
    have hmin2 : min ((y : Int) + 1) (2 * (k : Int) - y) ≤ 2 * (k : Int) - y :=
      min_le_right _ _
    have hj'' : (j : Int) < 2 * (min ((y : Int) + 1) (2 * (k : Int) - y)) := by
      simpa [Nat.cast_min, hcast] using hj'
    omega
  · rintro ⟨y, hy, him, hbounds⟩
    rcases hbounds with ⟨hlo, hhi⟩
    let r := Nat.min (y + 1) (2 * k - y)
    refine ⟨y, hy, ?_⟩
    refine ⟨(z.re + r).toNat, ?_, ?_⟩
    · omega
    · apply Zsqrtd.ext
      · have hnon : 0 ≤ z.re + (r : Int) := by omega
        rw [Int.toNat_of_nonneg hnon]
        simp [r]
      · simp [him]

private noncomputable abbrev domain (K : DiamondParameter) : Finset GaussianInt := by
  classical
  let k : Nat := K.1
  exact DiamondCellDomain k

private theorem domain_nonempty (K : DiamondParameter) : (domain K).Nonempty := by
  classical
  let k : Nat := K.1
  have hk : 0 < k := hk K
  have mem_domain (z : GaussianInt) : z ∈ DiamondCellDomain k ↔
      ∃ y : Nat, y < 2 * k ∧
        (let r := Nat.min (y + 1) (2 * k - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)) := mem_domain K z
  let domain : Finset GaussianInt := DiamondCellDomain k
  change (domain.Nonempty)
  refine ⟨(⟨0, 0⟩ : GaussianInt), ?_⟩
  rw [mem_domain]
  refine ⟨0, by omega, ?_⟩
  norm_num
  exact hk

private noncomputable abbrev reflectX : GaussianInt → GaussianInt := by
  classical
  exact fun z => (⟨-z.re - 1, z.im⟩ : GaussianInt)

private noncomputable abbrev reflectY (K : DiamondParameter) : GaussianInt → GaussianInt := by
  classical
  let k : Nat := K.1
  exact fun z => (⟨z.re, 2 * (k : Int) - 1 - z.im⟩ : GaussianInt)

private theorem reflectX_mem (K : DiamondParameter) (z : GaussianInt) (hz : z ∈ (domain K)) :
    reflectX z ∈ (domain K) := by
  classical
  let k : Nat := K.1
  have mem_domain (z : GaussianInt) : z ∈ DiamondCellDomain k ↔
      ∃ y : Nat, y < 2 * k ∧
        (let r := Nat.min (y + 1) (2 * k - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)) := mem_domain K z
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectX : GaussianInt → GaussianInt :=
    fun z => (⟨-z.re - 1, z.im⟩ : GaussianInt)
  change (reflectX z ∈ domain)
  rw [mem_domain] at hz ⊢
  rcases hz with ⟨y, hy, him, hlo, hhi⟩
  norm_num [Nat.cast_min] at hlo hhi ⊢
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · simp [reflectX, him]
  · simp [reflectX]
    omega
  · simp [reflectX]
    omega

private theorem reflectY_mem (K : DiamondParameter) (z : GaussianInt) (hz : z ∈ (domain K)) :
    (reflectY K) z ∈ (domain K) := by
  classical
  let k : Nat := K.1
  have mem_domain (z : GaussianInt) : z ∈ DiamondCellDomain k ↔
      ∃ y : Nat, y < 2 * k ∧
        (let r := Nat.min (y + 1) (2 * k - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)) := mem_domain K z
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectY : GaussianInt → GaussianInt :=
    fun z => (⟨z.re, 2 * (k : Int) - 1 - z.im⟩ : GaussianInt)
  change (reflectY z ∈ domain)
  rw [mem_domain] at hz ⊢
  rcases hz with ⟨y, hy, him, hlo, hhi⟩
  have hcast : ((2 * k - y : Nat) : Int) = 2 * (k : Int) - y := by omega
  have hr : (2 * k - 1 - y + 1).min (2 * k - (2 * k - 1 - y)) =
      (y + 1).min (2 * k - y) := by
    have hfirst : 2 * k - 1 - y + 1 = 2 * k - y := by omega
    have hsecond : 2 * k - (2 * k - 1 - y) = y + 1 := by omega
    rw [hfirst, hsecond]
    exact Nat.min_comm _ _
  refine ⟨2 * k - 1 - y, by omega, ?_, ?_, ?_⟩
  · simp only [Int.reduceNeg, reflectY]
    have hsub : ((2 * k - 1 - y : Nat) : Int) = 2 * (k : Int) - 1 - y := by omega
    rw [hsub]
    omega
  · rw [hr]
    change -(Nat.min (y + 1) (2 * k - y) : Int) ≤ z.re
    exact hlo
  · rw [hr]
    change z.re < (Nat.min (y + 1) (2 * k - y) : Int)
    exact hhi

private theorem sum_re_reflect (K : DiamondParameter) : (domain K).sum (fun z => z.re) =
      (domain K).sum (fun z => (reflectX z).re) := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectX : GaussianInt → GaussianInt :=
    fun z => (⟨-z.re - 1, z.im⟩ : GaussianInt)
  have reflectX_mem (z : GaussianInt) (hz : z ∈ domain) : reflectX z ∈ domain := reflectX_mem K z hz
  change (domain.sum (fun z => z.re) =
      domain.sum (fun z => (reflectX z).re))
  apply Finset.sum_bij (fun z hz => reflectX z)
  · exact fun z hz => reflectX_mem z hz
  · intro z hz w hw heq
    apply Zsqrtd.ext
    · simp [reflectX] at heq ⊢
      omega
    · simp only [Int.reduceNeg, Zsqrtd.mk.injEq, sub_left_inj, neg_inj, reflectX] at heq ⊢
      exact heq.2
  · intro z hz
    refine ⟨reflectX z, reflectX_mem z hz, ?_⟩
    apply Zsqrtd.ext <;> simp [reflectX]
  · intro z hz
    simp [reflectX]

private theorem sum_re_formula (K : DiamondParameter) : (domain K).sum (fun z => z.re) * 2 =
      -((domain K).card : Int) := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectX : GaussianInt → GaussianInt :=
    fun z => (⟨-z.re - 1, z.im⟩ : GaussianInt)
  have sum_re_reflect : domain.sum (fun z => z.re) =
      domain.sum (fun z => (reflectX z).re) := sum_re_reflect K
  change (domain.sum (fun z => z.re) * 2 =
      -(domain.card : Int))
  have hsum := sum_re_reflect
  simp only [reflectX] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const] at hsum
  simp at hsum
  linarith

private theorem sum_im_reflect (K : DiamondParameter) : (domain K).sum (fun z => z.im) =
      (domain K).sum (fun z => ((reflectY K) z).im) := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectY : GaussianInt → GaussianInt :=
    fun z => (⟨z.re, 2 * (k : Int) - 1 - z.im⟩ : GaussianInt)
  have reflectY_mem (z : GaussianInt) (hz : z ∈ domain) : reflectY z ∈ domain := reflectY_mem K z hz
  change (domain.sum (fun z => z.im) =
      domain.sum (fun z => (reflectY z).im))
  apply Finset.sum_bij (fun z hz => reflectY z)
  · exact fun z hz => reflectY_mem z hz
  · intro z hz w hw heq
    apply Zsqrtd.ext
    · simp only [Int.reduceNeg, Zsqrtd.mk.injEq, sub_right_inj, reflectY] at heq ⊢
      exact heq.1
    · simp [reflectY] at heq ⊢
      omega
  · intro z hz
    refine ⟨reflectY z, reflectY_mem z hz, ?_⟩
    apply Zsqrtd.ext <;> simp [reflectY]
  · intro z hz
    simp [reflectY]

private theorem sum_im_formula (K : DiamondParameter) : (domain K).sum (fun z => z.im) * 2 =
      (2 * ((k K) : Int) - 1) * (domain K).card := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let reflectY : GaussianInt → GaussianInt :=
    fun z => (⟨z.re, 2 * (k : Int) - 1 - z.im⟩ : GaussianInt)
  have sum_im_reflect : domain.sum (fun z => z.im) =
      domain.sum (fun z => (reflectY z).im) := sum_im_reflect K
  dsimp only [DiamondQuarterTurnConstruction.k] at *
  change (domain.sum (fun z => z.im) * 2 =
      (2 * (k : Int) - 1) * domain.card)
  have hsum := sum_im_reflect
  simp only [reflectY] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const] at hsum
  simp at hsum
  linarith

private theorem centroid_formula (K : DiamondParameter) : TileCentroid (DiamondTile (k K)) = (0,
    ((k K) : Real)) := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  have domain_nonempty : domain.Nonempty := domain_nonempty K
  have sum_re_formula : domain.sum (fun z => z.re) * 2 =
      -(domain.card : Int) := sum_re_formula K
  have sum_im_formula : domain.sum (fun z => z.im) * 2 =
      (2 * (k : Int) - 1) * domain.card := sum_im_formula K
  dsimp only [DiamondQuarterTurnConstruction.k] at *
  change (TileCentroid (DiamondTile k) = (0, (k : Real)))
  change (if domain.Nonempty then
    (((domain.sum (fun z => z.re) : Int) : Real) / domain.card + (1 / 2 : Real),
     ((domain.sum (fun z => z.im) : Int) : Real) / domain.card + (1 / 2 : Real))
    else _) = _
  rw [ite_eq_left domain_nonempty]
  apply Prod.ext <;> dsimp
  · have hc : (0 : Real) < domain.card := by exact_mod_cast domain_nonempty.card_pos
    have hs : ((domain.sum (fun z => z.re) : Int) : Real) * 2 =
        -(domain.card : Real) := by exact_mod_cast sum_re_formula
    field_simp
    linarith
  · have hc : (0 : Real) < domain.card := by exact_mod_cast domain_nonempty.card_pos
    have hs : ((domain.sum (fun z => z.im) : Int) : Real) * 2 =
        (2 * (k : Real) - 1) * domain.card := by exact_mod_cast sum_im_formula
    field_simp
    linarith

private noncomputable abbrev rotate (K : DiamondParameter) : GaussianInt → GaussianInt := by
  classical
  let k : Nat := K.1
  exact fun z => (⟨(k : Int) - 1 - z.im, z.re + k⟩ : GaussianInt)

private theorem rotate_mem (K : DiamondParameter) (z : GaussianInt) (hz : z ∈ (domain K)) :
    (rotate K) z ∈ (domain K) := by
  classical
  let k : Nat := K.1
  have mem_domain (z : GaussianInt) : z ∈ DiamondCellDomain k ↔
      ∃ y : Nat, y < 2 * k ∧
        (let r := Nat.min (y + 1) (2 * k - y);
         z.im = (y : Int) ∧ -(r : Int) ≤ z.re ∧ z.re < (r : Int)) := mem_domain K z
  let domain : Finset GaussianInt := DiamondCellDomain k
  let rotate : GaussianInt → GaussianInt :=
    fun z => (⟨(k : Int) - 1 - z.im, z.re + k⟩ : GaussianInt)
  change (rotate z ∈ domain)
  rw [mem_domain] at hz ⊢
  rcases hz with ⟨y, hy, him, hlo, hhi⟩
  have hrk : ((y + 1).min (2 * k - y) : Int) ≤ (k : Int) := by
    norm_num [Nat.cast_min]
    by_cases hycenter : y < k <;> omega
  have hnon : 0 ≤ z.re + (k : Int) := by omega
  let yn : Nat := (z.re + (k : Int)).toNat
  have hyn : (yn : Int) = z.re + (k : Int) := by
    dsimp [yn]
    rw [Int.toNat_of_nonneg hnon]
  have hynlt : yn < 2 * k := by omega
  refine ⟨yn, hynlt, ?_, ?_, ?_⟩
  · dsimp [rotate]
    rw [hyn]
  · dsimp [rotate]
    norm_num [Nat.cast_min] at hlo hhi ⊢
    by_cases hycenter : y < k <;> by_cases hxneg : z.re < 0 <;> omega
  · dsimp [rotate]
    norm_num [Nat.cast_min] at hlo hhi ⊢
    by_cases hycenter : y < k <;> by_cases hxneg : z.re < 0 <;> omega

private theorem rotate_injective (K : DiamondParameter) : Set.InjOn (rotate K) ((domain K) : Set
    GaussianInt) := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let rotate : GaussianInt → GaussianInt :=
    fun z => (⟨(k : Int) - 1 - z.im, z.re + k⟩ : GaussianInt)
  change (Set.InjOn rotate (domain : Set GaussianInt))
  intro z hz w hw heq
  apply Zsqrtd.ext
  · have h := congrArg Zsqrtd.im heq
    simp [rotate] at h
    omega
  · have h := congrArg Zsqrtd.re heq
    simp [rotate] at h
    omega

private theorem rotate_surjective (K : DiamondParameter) (z : GaussianInt) (hz : z ∈ (domain K)) :
      ∃ w ∈ (domain K), (rotate K) w = z := by
  classical
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  let rotate : GaussianInt → GaussianInt :=
    fun z => (⟨(k : Int) - 1 - z.im, z.re + k⟩ : GaussianInt)
  have rotate_mem (z : GaussianInt) (hz : z ∈ domain) : rotate z ∈ domain := rotate_mem K z hz
  have rotate_injective : Set.InjOn rotate (domain : Set GaussianInt) := rotate_injective K
  change (∃ w ∈ domain, rotate w = z)
  have himage : Finset.image rotate domain = domain := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
      exact rotate_mem b hb
    · rw [Finset.card_image_iff.mpr rotate_injective]
  have : z ∈ Finset.image rotate domain := by rw [himage]; exact hz
  exact Finset.mem_image.mp this

end DiamondQuarterTurnConstruction

theorem DiamondBaseT2 (K : DiamondParameter) :
    QuarterTurnSymmetric (DiamondTile K.1) := by
-- BODY
  let k : Nat := K.1
  let domain : Finset GaussianInt := DiamondCellDomain k
  have centroid_formula : TileCentroid (DiamondTile k) = (0, (k : Real)) :=
      DiamondQuarterTurnConstruction.centroid_formula K
  let rotate : GaussianInt → GaussianInt :=
    fun z => (⟨(k : Int) - 1 - z.im, z.re + k⟩ : GaussianInt)
  have rotate_mem (z : GaussianInt) (hz : z ∈ domain) : rotate z ∈ domain :=
      DiamondQuarterTurnConstruction.rotate_mem K z hz
  have rotate_surjective (z : GaussianInt) (hz : z ∈ domain) :
      ∃ w ∈ domain, rotate w = z := DiamondQuarterTurnConstruction.rotate_surjective K z hz
  change QuarterTurnSymmetric (DiamondTile k)
  unfold QuarterTurnSymmetric
  rw [centroid_formula]
  intro p
  simp only [TileRealization, DiamondTile]
  norm_num
  change (∃ x ∈ domain, p ∈ ClosedSquareRealization x) ↔
    ∃ x ∈ domain, ((k : Real) - p.2, (k : Real) + p.1) ∈
      ClosedSquareRealization x
  constructor
  · rintro ⟨z, hz, hp⟩
    refine ⟨rotate z, rotate_mem z hz, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hp ⊢
    change (((z.re : Int) : Real) ≤ p.1 ∧ ((z.im : Int) : Real) ≤ p.2) ∧
      (p.1 ≤ (z.re : Real) + 1 ∧ p.2 ≤ (z.im : Real) + 1) at hp
    change (((((k : Int) - 1 - z.im : Int) : Real) ≤ (k : Real) - p.2 ∧
      (((z.re + k : Int) : Real) ≤ (k : Real) + p.1)) ∧
      ((k : Real) - p.2 ≤ (((k : Int) - 1 - z.im : Int) : Real) + 1 ∧
      (k : Real) + p.1 ≤ ((z.re + k : Int) : Real) + 1))
    push_cast at hp ⊢
    rcases hp with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  · rintro ⟨z, hz, hq⟩
    obtain ⟨w, hw, hzw⟩ := rotate_surjective z hz
    subst z
    refine ⟨w, hw, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hq ⊢
    change (((((k : Int) - 1 - w.im : Int) : Real) ≤ (k : Real) - p.2 ∧
      (((w.re + k : Int) : Real) ≤ (k : Real) + p.1)) ∧
      ((k : Real) - p.2 ≤ (((k : Int) - 1 - w.im : Int) : Real) + 1 ∧
      (k : Real) + p.1 ≤ ((w.re + k : Int) : Real) + 1)) at hq
    change (((w.re : Int) : Real) ≤ p.1 ∧ ((w.im : Int) : Real) ≤ p.2) ∧
      (p.1 ≤ (w.re : Real) + 1 ∧ p.2 ≤ (w.im : Real) + 1)
    push_cast at hq ⊢
    rcases hq with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    constructor
    · constructor <;> linarith
    · constructor <;> linarith

end ApollonianSuperharmonic

end
