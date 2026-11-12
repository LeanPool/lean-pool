/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TilingLatticeIndex
public import LeanPool.ApollonianSuperharmonic.TilingLatticeInclusion

-- [TABLET NODE: IntegralityLatticeIndex]

/-!
# IntegralityLatticeIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegralityLatticeIndex (C : BandCircle) :
    ∃ R : Finset GaussianInt,
      LatticeFundamentalSet (IntegralityLattice C) R ∧
        R.card = C.1.1.1.natAbs := by
-- BODY
  classical
  obtain ⟨S, hS, hScard⟩ := TilingLatticeIndex C
  have contain : TilingLattice C ≤ IntegralityLattice C := TilingLatticeInclusion C
  let quotientMap : GaussianInt → GaussianInt ⧸ IntegralityLattice C :=
    QuotientAddGroup.mk' (IntegralityLattice C)
  have quotient_surjective : Function.Surjective quotientMap := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (IntegralityLattice C) x
    exact ⟨y, rfl⟩
  let representativeMap : S → GaussianInt ⧸ IntegralityLattice C :=
    fun r => quotientMap r.1
  have representativeMap_surjective : Function.Surjective representativeMap := by
    intro x
    obtain ⟨y, rfl⟩ := quotient_surjective x
    obtain ⟨r, hr, hyr⟩ := (hS y).exists
    refine ⟨⟨r, hr⟩, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hneg := (TilingLattice C).neg_mem hyr
    exact contain (by simpa [sub_eq_add_neg, add_comm] using hneg)
  let : Finite (GaussianInt ⧸ IntegralityLattice C) :=
    Finite.of_surjective representativeMap representativeMap_surjective
  let : Fintype (GaussianInt ⧸ IntegralityLattice C) := Fintype.ofFinite _
  let index : ℕ := Fintype.card (GaussianInt ⧸ IntegralityLattice C)
  have index_le : index ≤ C.1.1.1.natAbs := by
    dsimp [index]
    calc
      Fintype.card (GaussianInt ⧸ IntegralityLattice C) ≤ Fintype.card S :=
        Fintype.card_le_of_surjective representativeMap representativeMap_surjective
      _ = S.card := by simp
      _ = C.1.1.1.natAbs := hScard
  have index_pos : 0 < index := by
    dsimp [index]
    exact Fintype.card_pos
  have card_multiple (z : GaussianInt ⧸ IntegralityLattice C) :
      index • z = 0 := by
    have hs := Fintype.sum_equiv (Equiv.addLeft z) (fun x => z + x)
      (fun x => x) (fun x => rfl)
    have hs' : (∑ x : GaussianInt ⧸ IntegralityLattice C, (z + x)) =
        ∑ x : GaussianInt ⧸ IntegralityLattice C, x := by
      simpa using hs
    rw [Finset.sum_add_distrib, Finset.sum_const] at hs'
    have hz : index • z + (∑ x : GaussianInt ⧸ IntegralityLattice C, x) =
        0 + (∑ x : GaussianInt ⧸ IntegralityLattice C, x) := by
      simp [index]
    exact add_right_cancel hz
  have multiple (z : GaussianInt) : index • z ∈ IntegralityLattice C := by
    have hzero : quotientMap (index • z) = 0 := by
      simp [quotientMap, index]
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hzero
    simpa using hmem
  have hreal := multiple (1 : GaussianInt)
  have himag := multiple (⟨0, 1⟩ : GaussianInt)
  have hreal0 := hreal 0
  have himag1 := himag 1
  obtain ⟨n0, hn0⟩ := hreal0
  obtain ⟨n1, hn1⟩ := himag1
  have trace_integral :
      index * ((1 + C.1.1.2.re) / (2 * C.1.1.1) : ℝ) +
        index * ((1 - C.1.1.2.re) / (2 * C.1.1.1) : ℝ) ∈ Set.range (fun n : ℤ => (n : ℝ)) := by
    refine ⟨n0 + n1, ?_⟩
    have hs := congrArg₂ (fun a b : ℝ => a + b) hn0 hn1
    convert hs.symm using 1 <;>
      simp [CircleMatrix, BandCircleEuclideanData, Matrix.mulVec]; ring
  have index_lower : C.1.1.1.natAbs ≤ index := by
    obtain ⟨n, hn⟩ := trace_integral
    have hcpos : (0 : ℝ) < C.1.1.1 := by exact_mod_cast C.2
    have hratio : (n : ℝ) = (index : ℝ) / C.1.1.1 := by
      calc
        (n : ℝ) = (index : ℝ) * ((1 + C.1.1.2.re) / (2 * C.1.1.1)) +
            (index : ℝ) * ((1 - C.1.1.2.re) / (2 * C.1.1.1)) := hn
        _ = (index : ℝ) / C.1.1.1 := by field_simp; ring
    have hnpos : 0 < n := by
      have hi : (0 : ℝ) < index := by exact_mod_cast index_pos
      have : (0 : ℝ) < (index : ℝ) / C.1.1.1 := div_pos hi hcpos
      exact_mod_cast (hratio ▸ this)
    have hprod : (n : ℝ) * C.1.1.1 = index := by
      rw [hratio]
      field_simp
    have hprod_int : n * C.1.1.1 = (index : ℤ) := by
      exact_mod_cast hprod
    have hc_nonneg : (0 : ℤ) ≤ C.1.1.1 := le_of_lt C.2
    have hc_nat : (C.1.1.1.natAbs : ℤ) = C.1.1.1 := Int.natAbs_of_nonneg hc_nonneg
    have hnat : (C.1.1.1.natAbs : ℤ) ≤ (index : ℤ) := by
      rw [hc_nat, ← hprod_int]
      have hn_one : (1 : ℤ) ≤ n := by omega
      have hfactor : 0 ≤ (n - 1) * C.1.1.1 :=
        mul_nonneg (by omega) hc_nonneg
      nlinarith
    exact_mod_cast hnat
  have index_eq : index = C.1.1.1.natAbs := Nat.le_antisymm index_le index_lower
  have map_injective : Function.Injective representativeMap := by
    intro a b hab
    by_contra different
    have not_injective : ¬ Function.Injective representativeMap := by
      intro injective
      exact different (injective hab)
    have contradiction := Fintype.card_lt_of_surjective_not_injective
      representativeMap representativeMap_surjective not_injective
    have same : Fintype.card S = C.1.1.1.natAbs := by simp [hScard]
    rw [same, ← index_eq] at contradiction
    exact (Nat.lt_irrefl _ contradiction)
  refine ⟨S, ?_, ?_⟩
  · intro x
    obtain ⟨r, hr, hxr⟩ := (hS x).exists
    refine ⟨r, ⟨hr, contain hxr⟩, ?_⟩
    intro s hs
    have equal_subtypes : (⟨s, hs.1⟩ : S) = ⟨r, hr⟩ := by
      apply map_injective
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have difference := (IntegralityLattice C).sub_mem (contain hxr) hs.2
      convert difference using 1; abel
    exact congrArg Subtype.val equal_subtypes
  · calc
      S.card = C.1.1.1.natAbs := hScard

end ApollonianSuperharmonic

end
