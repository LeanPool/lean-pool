/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCellTransport
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# High-contrast homogenization: Entry.Source.Subdivision

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source subdivision support

This file starts the source-multiplier construction near `e.source.multiplier`, `l.source.whitney`
by exposing two reusable facts needed before the stopping minimum is built:
integer-stationary transport of the `z = 0` dagger event, and the corresponding
coarse-block translation identity for the qualitative coefficient carrier.

No source multiplier, radius, or new definition is introduced here.
-/

open HCPolySupport.HighContrast (CoeffSpace blockScale coarseBlock coarseBlock_eq_of_ae_eq
  measurable_translateCoeff translateCoeff)
open HCPolySupport.HighContrast (adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Source

open Set MeasureTheory
open HCPolySupport.HighContrast.Geometry

/-- The lower half-grid bound: from `-b ≤ w` and a positive scale `s`, the scaled
lower endpoint stays below `s w`. -/
private lemma half_mul_lt_mul_of_neg_le {s b w : ℝ} (hs : 0 < s) (h : -b ≤ w) :
    -((1 : ℝ) / 2) * ((2 * b + 1) * s) < s * w := by
  have h1 : -((1 : ℝ) / 2) * (2 * b + 1) < w := by linarith only [h]
  have h2 : s * (-((1 : ℝ) / 2) * (2 * b + 1)) < s * w :=
    mul_lt_mul_of_pos_left h1 hs
  calc
    -((1 : ℝ) / 2) * ((2 * b + 1) * s) =
        s * (-((1 : ℝ) / 2) * (2 * b + 1)) := by ring
    _ < s * w := h2

/-- The upper half-grid bound: from `w ≤ b` and a positive scale `s`, `s w` stays below
the scaled upper endpoint. -/
private lemma mul_lt_half_mul_of_le {s b w : ℝ} (hs : 0 < s) (h : w ≤ b) :
    s * w < (1 : ℝ) / 2 * ((2 * b + 1) * s) := by
  have h1 : w < (1 : ℝ) / 2 * (2 * b + 1) := by linarith only [h]
  have h2 : s * w < s * ((1 : ℝ) / 2 * (2 * b + 1)) :=
    mul_lt_mul_of_pos_left h1 hs
  calc
    s * w < s * ((1 : ℝ) / 2 * (2 * b + 1)) := h2
    _ = (1 : ℝ) / 2 * ((2 * b + 1) * s) := by ring

/-- Cancelling a positive scale `s` in the scaled lower half-grid bound gives `-b - 1 < w`. -/
private lemma neg_succ_lt_of_half_mul_lt {s b w : ℝ} (hs : 0 < s)
    (h : -((1 : ℝ) / 2) * ((2 * b + 1) * s) < s * w) : -b - 1 < w := by
  have h2 : s * (-((1 : ℝ) / 2) * (2 * b + 1)) < s * w := by
    calc
      s * (-((1 : ℝ) / 2) * (2 * b + 1)) =
          -((1 : ℝ) / 2) * ((2 * b + 1) * s) := by ring
      _ < s * w := h
  have h1 : -((1 : ℝ) / 2) * (2 * b + 1) < w := lt_of_mul_lt_mul_left h2 hs.le
  linarith only [h1]

/-- Cancelling a positive scale `s` in the scaled upper half-grid bound gives `w < b + 1`. -/
private lemma lt_succ_of_mul_lt_half_mul {s b w : ℝ} (hs : 0 < s)
    (h : s * w < (1 : ℝ) / 2 * ((2 * b + 1) * s)) : w < b + 1 := by
  have h2 : s * w < s * ((1 : ℝ) / 2 * (2 * b + 1)) := by
    calc
      s * w < (1 : ℝ) / 2 * ((2 * b + 1) * s) := h
      _ = s * ((1 : ℝ) / 2 * (2 * b + 1)) := by ring
  have h1 : w < (1 : ℝ) / 2 * (2 * b + 1) := lt_of_mul_lt_mul_left h2 hs.le
  linarith only [h1]

noncomputable section

variable {d : ℕ}

/-- Translating a coefficient field is the same as translating the coarse-block domain.
This is the general form of the adapted-cell covariance used by the S2 locality support,
made public in the source namespace for standard-cell applications. -/
theorem coarseBlock_translateCoeff_eq_translateSet
    (U : Set (Vec d)) (z : Fin d → ℤ) (a : CoeffSpace d) :
    coarseBlock U (translateCoeff z a) =
      coarseBlock (translateSet (HCPolySupport.Source.AKL.intTranslation z) U) a := by
  calc
    coarseBlock U (translateCoeff z a)
        = coarseBlockMatrix U
            (translateCoeffField (HCPolySupport.Source.AKL.intTranslation z) (⇑a.1)) := by
          simpa [translateCoeffField] using!
            (coarseBlock_eq_of_ae_eq (U := U) (translateCoeff z a)
              (HCPolySupport.Source.AKL.translateField_ae z a.1))
    _ = coarseBlockMatrix
          (translateSet (HCPolySupport.Source.AKL.intTranslation z) U) (⇑a.1) := by
          exact (coarseBlockMatrix_translateSet_eq_translateCoeffField
            (HCPolySupport.Source.AKL.intTranslation z) U (⇑a.1)).symm
    _ = coarseBlock (translateSet (HCPolySupport.Source.AKL.intTranslation z) U) a := rfl

/-- The dagger bound, transported from the `z = 0` event to all integer translates.
The conclusion is intentionally still written on `translateCoeff z a`; later source files
may rewrite domains with `coarseBlock_translateCoeff_eq_translateSet` when a geometric
cell identity is available. -/
theorem stationary_all_integer_dagger_event
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P g E Ψ K S) :
    ∀ᵐ a ∂P, ∀ z : Fin d → ℤ, ∀ m : ℤ,
      S (translateCoeff z a) ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (translateCoeff z a))
          (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E) := by
  refine eventually_countable_forall.mpr ?_
  intro z
  have hmap :
      ∀ᵐ b ∂Measure.map (translateCoeff z) P, ∀ m : ℤ, S b ≤ (3 : ℝ) ^ m →
        ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
          standardCellCenter k w ∈ centeredCube d m →
          BlockMatLoewnerLE (coarseBlock (standardCell d k w) b)
            (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E) := by
    simpa [hstat z] using hdag.coarse_bound
  exact ae_of_ae_map (measurable_translateCoeff z).aemeasurable hmap

/-- The source index condition is a product of integer intervals. -/
theorem sourceCenter_mem_iff (d jStar r : ℕ) (w : Fin d → ℤ)
    (b : ℕ) (hb : 3 ^ jStar = 2 * b + 1) :
    standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
      centeredCube d ((2 * jStar + r : ℕ) : ℤ) ↔
      ∀ i, -(b : ℤ) ≤ w i ∧ w i ≤ (b : ℤ) := by
  have hpow : (3 : ℝ) ^ (2 * jStar + r) =
      (2 * (b : ℝ) + 1) * (3 : ℝ) ^ (jStar + r) := by
    have hbR : (3 : ℝ) ^ jStar = 2 * (b : ℝ) + 1 := by exact_mod_cast hb
    rw [show 2 * jStar + r = jStar + (jStar + r) by omega, pow_add, hbR]
  rw [Recurrence.mem_centeredCube_iff]
  simp only [standardCellCenter, zpow_natCast]
  rw [hpow]
  have hpos : 0 < (3 : ℝ) ^ (jStar + r) := by positivity
  constructor
  · intro h i
    obtain ⟨hl, hu⟩ := h i
    have hlR : -(b : ℝ) - 1 < (w i : ℝ) := neg_succ_lt_of_half_mul_lt hpos hl
    have huR : (w i : ℝ) < (b : ℝ) + 1 := lt_succ_of_mul_lt_half_mul hpos hu
    have hlZ : -(b : ℤ) - 1 < w i := by exact_mod_cast hlR
    have huZ : w i < (b : ℤ) + 1 := by exact_mod_cast huR
    omega
  · intro h i
    have hl : -(b : ℝ) ≤ (w i : ℝ) := by exact_mod_cast (h i).1
    have hu : (w i : ℝ) ≤ (b : ℝ) := by exact_mod_cast (h i).2
    constructor
    · exact half_mul_lt_mul_of_neg_le hpos hl
    · exact mul_lt_half_mul_of_le hpos hu

/-- Exactly `3^(d*jStar)` source indices, independently of the offset. -/
theorem sourceCenterSet_finite_card (d jStar r : ℕ) :
    {w : Fin d → ℤ | standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
      centeredCube d ((2 * jStar + r : ℕ) : ℤ)}.Finite ∧
    {w : Fin d → ℤ | standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
      centeredCube d ((2 * jStar + r : ℕ) : ℤ)}.ncard = 3 ^ (d * jStar) := by
  obtain ⟨b, hb⟩ : Odd ((3 : ℕ) ^ jStar) := Odd.pow (by decide)
  let F : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(b : ℤ)) b
  have hset : {w : Fin d → ℤ | standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
      centeredCube d ((2 * jStar + r : ℕ) : ℤ)} = (F : Set (Fin d → ℤ)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, F, Fintype.mem_piFinset, Finset.mem_Icc]
    exact sourceCenter_mem_iff d jStar r w b hb
  rw [hset]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  have hcard : (Finset.Icc (-(b : ℤ)) (b : ℤ)).card = 3 ^ jStar := by
    rw [Int.card_Icc, hb]
    omega
  simp [F, Fintype.card_piFinset, hcard, ← pow_mul, Nat.mul_comm]

/-- The real source center is the image of the literal integer translation in the minimum. -/
theorem intTranslation_sourceCenter {d : ℕ} (jStar r : ℕ) (w : Fin d → ℤ) :
    HCPolySupport.Source.AKL.intTranslation (fun i => (3 : ℤ) ^ (jStar + r) * w i) =
      standardCellCenter ((jStar + r : ℕ) : ℤ) w := by
  ext i
  simp only [HCPolySupport.Source.AKL.intTranslation, standardCellCenter, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, zpow_natCast]

/-- Every aligned cube has an aligned ancestor at every coarser integer generation. -/
theorem exists_standardCell_ancestor {d : ℕ} {k m : ℤ} (hkm : k ≤ m) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ, standardCell d k w ⊆ standardCell d m v := by
  have h (n : ℕ) : ∃ v : Fin d → ℤ, standardCell d k w ⊆ standardCell d (k + n) v := by
    induction n with
    | zero => exact ⟨w, by simp⟩
    | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨Transport.gridParent v, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        hv.trans (Transport.standardCell_subset_parent (k + n) v)
  have hm : k + ((m - k).toNat : ℤ) = m := by rw [Int.toNat_of_nonneg (by omega)]; omega
  simpa only [hm] using h (m - k).toNat

/-- A standard cube is the identity-metric adapted cube at its actual center. -/
theorem standardCell_eq_adapted_identity {d : ℕ} (k : ℤ) (w : Fin d → ℤ) :
    standardCell d k w = adaptedCellTranslate (1 : Mat d) k (standardCellCenter k w) := by
  rw [Recurrence.standardCell_eq_image, Transport.adaptedCellTranslate_eq_image]
  simp [matVecMul_eq_mulVec]

/-- The fixed-generation standard subcubes partition a standard parent a.e. -/
theorem standardCell_subdivision_null {d : ℕ} {k m : ℤ} (hkm : k ≤ m) (v : Fin d → ℤ) :
    volume (standardCell d m v \ ⋃ w : {w : Fin d → ℤ |
      standardCell d k w ⊆ standardCell d m v}, standardCell d k w) = 0 := by
  apply measure_mono_null (t := gridFaces d k) _ (volume_gridFaces k)
  intro x hx
  by_contra hface
  obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hface
  have hsub := standardCell_subset_of_mem hkm hw hx.1
  exact hx.2 (mem_iUnion.mpr ⟨⟨w, hsub⟩, hw⟩)

/-- Aligned translation by a coarser center preserves the finer standard grid. -/
theorem translate_standardCell_by_coarser_center {d : ℕ}
    (k : ℤ) (n : ℕ) (v w : Fin d → ℤ) :
    translateSet (standardCellCenter (k + n) v) (standardCell d k w) =
      standardCell d k (fun i => w i + (3 : ℤ) ^ n * v i) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Recurrence.mem_standardCell_iff,
    Recurrence.mem_standardCell_iff]
  have hp : (3 : ℝ) ^ (k + n) = (3 : ℝ) ^ k * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
  simp only [standardCellCenter, Pi.sub_apply, Int.cast_add, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, hp]
  apply forall_congr'
  intro i
  constructor <;> intro h <;> constructor
  · linarith only [h.1]
  · linarith only [h.2]
  · linarith only [h.1]
  · linarith only [h.2]

end

end HCPolySupport.HighContrast.Source
