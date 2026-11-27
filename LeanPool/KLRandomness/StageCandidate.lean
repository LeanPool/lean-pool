/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListWeights
public import LeanPool.KLRandomness.NoDrop

/-!
# Sparse-list entries as affine blocks on a concrete pool

The finite search produces Boolean matrices on `Fin M`.  This file embeds
their selected columns into natural-number coordinates through an injective
pool enumeration.  The syndrome is left free: changing it does not change
any of the rank calculations.
-/

@[expose] public section

noncomputable section

namespace Klr.StageCandidate

open SparseListSearch SparseListWeights SparseSearch AffineCode FiniteMeasure
open RandomMatrix AffineObservation
open scoped BigOperators

variable {M m r : ℕ}

/-- A coded column, read at the dimensions guaranteed by `GoodEntry`. -/
def columns (a : Entry) (M r : ℕ) (j : Fin M) (i : Fin r) : ZMod 2 :=
  boolEquivF2 (entry (rows a.2) i.val j.val)

theorem columns_zero_off_support {a : Entry} (ha : GoodEntry M m r a)
    {j : Fin M} (hj : j ∉ support M a) : columns a M r j = 0 := by
  have hm : a.1.getD j.val false = false := by
    simpa [support, SparseListCode.mem_maskSet] using hj
  funext i
  simp only [columns, Pi.zero_apply, ha.2.2.2.2.2 i.val i.isLt j.val j.isLt hm]
  rfl

theorem restricted_columns_surjective {a : Entry} (ha : GoodEntry M m r a) :
    Function.Surjective (restrictedMap (columns a M r) (support M a) (K := ZMod 2)) := by
  have hw := ha.2.2.1
  have hr := ha.2.2.2.1
  cases hw
  cases hr
  exact ha.restricted_fullRank

theorem masked_columns_surjective {a : Entry} (ha : GoodEntry M m r a)
    (d : List Bool) (hd : maskedFullRank a.2 d = true) :
    Function.Surjective
      (restrictedMap (columns a M r) (SparseListCode.maskSet M d) (K := ZMod 2)) := by
  have hw := ha.2.2.1
  have hr := ha.2.2.2.1
  cases hw
  cases hr
  exact (maskedFullRank_eq_true a.2 d).mp hd

/-- The executable rank checker at the dimensions supplied by `GoodEntry`. -/
theorem maskedFullRank_iff_columns_surjective {a : Entry} (ha : GoodEntry M m r a)
    (d : List Bool) :
    maskedFullRank a.2 d = true ↔ Function.Surjective
      (restrictedMap (columns a M r) (SparseListCode.maskSet M d) (K := ZMod 2)) := by
  have hw := ha.2.2.1
  have hr := ha.2.2.2.1
  cases hw
  cases hr
  exact maskedFullRank_eq_true a.2 d

/-- The selected natural-number positions of a concrete pool. -/
def positions (e : Fin M → ℕ) (a : Entry) : Finset ℕ := (support M a).image e

/-- The mask coordinates and their actual natural-number positions are equivalent. -/
def positionEquiv (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry) :
    support M a ≃ positions e a :=
  Equiv.ofBijective
    (fun j => ⟨e j.val, Finset.mem_image_of_mem e j.property⟩)
    ⟨fun j k h => Subtype.ext (he (congrArg Subtype.val h)), by
      rintro ⟨p, hp⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨⟨j, hj⟩, rfl⟩⟩

@[simp] theorem positionEquiv_val (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (j : support M a) : (positionEquiv e he a j).val = e j.val := rfl

/-- Pull an assignment on actual positions back to the selected mask coordinates. -/
def pullback (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry) :
    (positions e a → ZMod 2) →ₗ[ZMod 2] (support M a → ZMod 2) where
  toFun x j := x (positionEquiv e he a j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullback_surjective (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry) :
    Function.Surjective (pullback e he a) := by
  intro x
  refine ⟨fun p => x ((positionEquiv e he a).symm p), ?_⟩
  ext j
  simp [pullback]

/-- The affine block represented by a checked sparse-list entry, on the given pool. -/
def block (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2) : AffineBlock where
  support := positions e a
  rank := r
  matrix := (restrictedMap (columns a M r) (support M a)).comp (pullback e he a)
  fullRank := (restricted_columns_surjective ha).comp (pullback_surjective e he a)
  syndrome := y

@[simp] theorem block_support (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (ha : GoodEntry M m r a) (y : Fin r → ZMod 2) :
    (block e he a ha y).support = (support M a).image e := rfl

@[simp] theorem block_rank (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (ha : GoodEntry M m r a) (y : Fin r → ZMod 2) :
    (block e he a ha y).rank = r := rfl

theorem block_support_card (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (ha : GoodEntry M m r a) (y : Fin r → ZMod 2) :
    (block e he a ha y).support.card = m := by
  rw [block_support, Finset.card_image_of_injective _ he]
  exact (SparseListCode.card_maskSet M a.1 ha.1).trans ha.2.1

theorem block_support_subset (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (ha : GoodEntry M m r a) (y : Fin r → ZMod 2) :
    (block e he a ha y).support ⊆ Finset.univ.image e :=
  Finset.image_subset_image (Finset.subset_univ _)

theorem block_matrix_single (e : Fin M → ℕ) (he : Function.Injective e)
    (a : Entry) (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (j : support M a) :
    (block e he a ha y).matrix (Pi.single (positionEquiv e he a j) 1) =
      columns a M r j.val := by
  classical
  have hp : pullback e he a (Pi.single (positionEquiv e he a j) 1) = Pi.single j 1 := by
    ext k
    simp [pullback, Pi.single_apply, (positionEquiv e he a).injective.eq_iff]
  change restrictedMap (columns a M r) (support M a)
    (pullback e he a (Pi.single (positionEquiv e he a j) 1)) = _
  rw [hp]
  exact columnMap_single _ j

end Klr.StageCandidate
