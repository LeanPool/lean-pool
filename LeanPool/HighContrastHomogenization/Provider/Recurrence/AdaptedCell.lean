/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RoundedGrid

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted cells as linear images of the standard aligned cubes

An adapted cell `⋄_j^q = q□_j` is the image of a centered triadic cube under the
grid map, and an aligned adapted cell `3^j q w + ⋄_j^q` is the image of the
standard aligned cube `3^j w + □_j` under the same map.
Since a rounded grid is invertible, every incidence question about adapted cells
is the corresponding question about standard cubes, transported by an injection.

This file records that transport and the combinatorial clauses of the aligned
subdivision in the coarse-block properties taken from HC: an aligned scale-`j`
cell has its
center in the scale-`p` parent exactly when each of its indices is one of the
`3^{p-j}` admissible ones, such a cell is contained in the parent, distinct
aligned cells at the same scale are disjoint, and the admissible indices number
`3^{d(p-j)}`.  That the cells cover the parent up to a null set is proved in the
companion file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The grid map is injective -/

/-- A positive definite grid matrix acts injectively on vectors. -/
theorem matVecMul_injective {q : Mat d} (hq : q.PosDef) :
    Function.Injective (matVecMul q) :=
  Matrix.mulVec_injective_of_isUnit hq.isUnit

/-! ## Scale bookkeeping -/

/-- The scale ratio between two triadic scales, as an integer. -/
theorem intCast_three_pow_toNat {j p : ℤ} (hjp : j ≤ p) :
    (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) = (3 : ℝ) ^ (p - j) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p - j = (n : ℤ) :=
    ⟨(p - j).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [hn, Int.toNat_natCast, zpow_natCast]
  push_cast
  ring

/-- The parent scale factors through the child scale. -/
theorem zpow_three_split {j p : ℤ} (hjp : j ≤ p) :
    (3 : ℝ) ^ p = (3 : ℝ) ^ j * (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) := by
  rw [intCast_three_pow_toNat hjp, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

/-- The scale ratio is odd, so no index sits on the boundary of the parent. -/
theorem odd_three_pow (n : ℕ) : ∃ m : ℤ, (3 : ℤ) ^ n = 2 * m + 1 :=
  Odd.pow (by decide)

/-! ## Membership in the standard aligned cubes -/

/-- Membership in a centered triadic cube, coordinatewise. -/
theorem mem_centeredCube_iff {k : ℤ} {x : Vec d} :
    x ∈ centeredCube d k ↔ ∀ i, -((1 : ℝ) / 2) * (3 : ℝ) ^ k < x i ∧
      x i < (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
  mem_openCubeSet_originCube_iff

/-- Membership in a standard aligned cube, coordinatewise. -/
theorem mem_standardCell_iff {k : ℤ} {w : Fin d → ℤ} {x : Vec d} :
    x ∈ standardCell d k w ↔ ∀ i, ((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ k < x i ∧
      x i < ((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ k := by
  simp [standardCell, openCubeSet, translateCube, originCube, cubeScaleFactor]

/-- A standard aligned cube is the translate of the centered cube by its own
center. -/
theorem standardCell_eq_image (k : ℤ) (w : Fin d → ℤ) :
    standardCell d k w = (fun y => standardCellCenter k w + y) '' centeredCube d k := by
  ext x
  simp only [Set.mem_image, mem_standardCell_iff]
  constructor
  · intro hx
    refine ⟨x - standardCellCenter k w, ?_, by abel⟩
    rw [mem_centeredCube_iff]
    intro i
    obtain ⟨h1, h2⟩ := hx i
    have hc : (x - standardCellCenter k w) i = x i - (3 : ℝ) ^ k * (w i : ℝ) := rfl
    rw [hc]
    constructor <;> linarith only [h1, h2]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centeredCube_iff] at hy
    intro i
    obtain ⟨h1, h2⟩ := hy i
    have hc : (standardCellCenter k w + y) i = (3 : ℝ) ^ k * (w i : ℝ) + y i := rfl
    rw [hc]
    constructor <;> linarith only [h1, h2]

/-! ## Adapted cells as images -/

/-- The center of an aligned adapted cell is the image of the standard center. -/
theorem adaptedCellCenter_eq (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellCenter q k w = matVecMul q (standardCellCenter k w) := by
  rw [adaptedCellCenter, ← matVecMul_smul]
  rfl

/-- **An aligned adapted cell is the grid image of a standard aligned cube.** -/
theorem adaptedCellAt_eq_image (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt q k w = matVecMul q '' standardCell d k w := by
  rw [standardCell_eq_image, Set.image_image, adaptedCellAt, adaptedCell,
    Set.image_image]
  refine Set.image_congr' fun y => ?_
  rw [matVecMul_add, ← adaptedCellCenter_eq]
  rfl

/-! ## The aligned centers inside the parent cell -/

/-- **The index set of the aligned subdivision.**  For scales `j ≤ p`, the center
`3^j q w` lies in the parent cell `⋄_p^q` exactly when each index `w i` is one of
the `3^{p-j}` admissible values. -/
theorem adaptedCellCenter_mem_adaptedCell_iff {q : Mat d} (hq : q.PosDef)
    {j p : ℤ} (hjp : j ≤ p) (w : Fin d → ℤ) :
    adaptedCellCenter q j w ∈ adaptedCell q p ↔
      ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat := by
  have hj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [adaptedCellCenter_eq, adaptedCell, (matVecMul_injective hq).mem_set_image,
    mem_centeredCube_iff]
  refine forall_congr' fun i => ?_
  have hc : standardCellCenter j w i = (3 : ℝ) ^ j * (w i : ℝ) := rfl
  rw [hc, zpow_three_split hjp]
  constructor
  · rintro ⟨h1, h2⟩
    have hR : (2 : ℝ) * (w i : ℝ) < (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) :=
      lt_of_mul_lt_mul_left
        (by linarith only [h2] :
          (3 : ℝ) ^ j * (2 * (w i : ℝ)) <
            (3 : ℝ) ^ j * (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) hj.le
    have hL : -((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) < (2 : ℝ) * (w i : ℝ) :=
      lt_of_mul_lt_mul_left
        (by linarith only [h1] :
          (3 : ℝ) ^ j * (-((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ))) <
            (3 : ℝ) ^ j * (2 * (w i : ℝ))) hj.le
    have hRZ : 2 * w i < (3 : ℤ) ^ (p - j).toNat := by exact_mod_cast hR
    have hLZ : -((3 : ℤ) ^ (p - j).toNat) < 2 * w i := by exact_mod_cast hL
    rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] <;> omega
  · intro h
    have hRZ : 2 * w i < (3 : ℤ) ^ (p - j).toNat := by
      rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at h <;> omega
    have hLZ : -((3 : ℤ) ^ (p - j).toNat) < 2 * w i := by
      rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at h <;> omega
    have hR : (2 : ℝ) * (w i : ℝ) < (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) := by
      exact_mod_cast hRZ
    have hL : -((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) < (2 : ℝ) * (w i : ℝ) := by
      exact_mod_cast hLZ
    have hR' := mul_lt_mul_of_pos_left hR hj
    have hL' := mul_lt_mul_of_pos_left hL hj
    exact ⟨by linarith only [hL'], by linarith only [hR']⟩

/-! ## Containment of the children in the parent -/

/-- **Each aligned child cell lies in the parent cell.**  The scale ratio is odd,
so the closed child cells stay inside the open parent. -/
theorem adaptedCellAt_subset_adaptedCell {q : Mat d} (hq : q.PosDef) {j p : ℤ}
    (hjp : j ≤ p) {w : Fin d → ℤ} (hw : adaptedCellCenter q j w ∈ adaptedCell q p) :
    adaptedCellAt q j w ⊆ adaptedCell q p := by
  have hw' := (adaptedCellCenter_mem_adaptedCell_iff hq hjp w).mp hw
  obtain ⟨m, hm⟩ := odd_three_pow (p - j).toNat
  have hj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [adaptedCellAt_eq_image, adaptedCell]
  refine Set.image_mono ?_
  intro x hx
  rw [mem_standardCell_iff] at hx
  rw [mem_centeredCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hupZ : 2 * w i + 1 ≤ (3 : ℤ) ^ (p - j).toNat := by
    have h := hw' i
    rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at h <;> omega
  have hloZ : -((3 : ℤ) ^ (p - j).toNat) ≤ 2 * w i - 1 := by
    have h := hw' i
    rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at h <;> omega
  have hup : (2 : ℝ) * (w i : ℝ) + 1 ≤ (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) := by
    exact_mod_cast hupZ
  have hlo : -((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) ≤ (2 : ℝ) * (w i : ℝ) - 1 := by
    exact_mod_cast hloZ
  have hup' : ((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ j ≤
      (1 / 2 : ℝ) * ((3 : ℝ) ^ j * (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hup hj.le
    linarith only [this]
  have hlo' : -((1 : ℝ) / 2) * ((3 : ℝ) ^ j * (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ)) ≤
      ((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hlo hj.le
    linarith only [this]
  rw [zpow_three_split hjp]
  exact ⟨by linarith only [h1, hlo'], by linarith only [h2, hup']⟩

/-! ## Disjointness -/

/-- **Distinct aligned cells at the same scale are disjoint.** -/
theorem disjoint_adaptedCellAt {q : Mat d} (hq : q.PosDef) (k : ℤ)
    {w w' : Fin d → ℤ} (hww : w ≠ w') :
    Disjoint (adaptedCellAt q k w) (adaptedCellAt q k w') := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ w' i := Function.ne_iff.mp hww
  rw [adaptedCellAt_eq_image, adaptedCellAt_eq_image, Set.disjoint_iff]
  rintro x ⟨⟨y, hy, rfl⟩, ⟨y', hy', hyy⟩⟩
  have hyeq : y' = y := matVecMul_injective hq hyy
  subst hyeq
  rw [mem_standardCell_iff] at hy hy'
  obtain ⟨h1, h2⟩ := hy i
  obtain ⟨h3, h4⟩ := hy' i
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have hstepZ : w i + 1 ≤ w' i := by omega
    have hstep : ((w i : ℝ)) + 1 ≤ ((w' i : ℝ)) := by exact_mod_cast hstepZ
    have hmul := mul_le_mul_of_nonneg_right hstep hk.le
    linarith only [h2, h3, hmul]
  · have hstepZ : w' i + 1 ≤ w i := by omega
    have hstep : ((w' i : ℝ)) + 1 ≤ ((w i : ℝ)) := by exact_mod_cast hstepZ
    have hmul := mul_le_mul_of_nonneg_right hstep hk.le
    linarith only [h1, h4, hmul]

/-! ## The scaled adapted lattice -/

/-! ## The count -/

/-- **The aligned subdivision has `3^{d(p-j)}` cells.**  The admissible indices
form a finite set of the size prescribed by the coarse-block properties taken
from HC. -/
theorem exists_finset_adaptedCellCenter_mem {q : Mat d} (hq : q.PosDef) {j p : ℤ}
    (hjp : j ≤ p) :
    ∃ Z : Finset (Fin d → ℤ),
      ↑Z = {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p} ∧
        Z.card = 3 ^ (d * (p - j).toNat) := by
  classical
  set n : ℕ := (p - j).toNat with hn
  obtain ⟨m, hm⟩ := odd_three_pow n
  have hcast : ((3 ^ n : ℕ) : ℤ) = 2 * m + 1 := by rw [← hm]; push_cast; ring
  refine ⟨Fintype.piFinset fun _ : Fin d => Finset.Icc (-m) m, ?_, ?_⟩
  · ext w
    rw [Set.mem_ofPred_eq, adaptedCellCenter_mem_adaptedCell_iff hq hjp]
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    refine forall_congr' fun i => ?_
    rw [← hn, hm, ← abs_le]
    omega
  · rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hcard : (m + 1 - -m).toNat = 3 ^ n := by
      have hxx : m + 1 - -m = ((3 ^ n : ℕ) : ℤ) := by omega
      rw [hxx, Int.toNat_natCast]
    rw [hcard, ← pow_mul, Nat.mul_comm]

/-- **The aligned subdivision has `3^{d(p-j)}` cells.**  This is the counting
clause of the coarse-block properties taken from HC. -/
theorem ncard_adaptedCellCenter_mem {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p) :
    {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p}.ncard
      = 3 ^ (d * (p - j).toNat) := by
  obtain ⟨Z, hZ, hcard⟩ := exists_finset_adaptedCellCenter_mem hq hjp
  rw [← hZ, Set.ncard_coe_finset, hcard]

end

end Recurrence
end HighContrast
end HCPolySupport
