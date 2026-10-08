/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AlignedSubdivision

/-!
# High-contrast homogenization: Entry.Geometry.StandardCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Standard aligned cubes

The centered triadic cube `□_j = (-3^j/2, 3^j/2)^d` and the standard aligned cubes
`z + □_k` with `z = 3^k w`, `w ∈ ℤ^d`, of the paper, built on the
`TriadicCube` descriptors of CoarseGraining.  This file holds the cube API that
`l.source.whitney` needs: membership, volume, nesting-or-disjointness of aligned
cubes, parents, and the null set of grid faces.
-/

open HCPolySupport.HighContrast (centeredCube standardCell standardCellCenter)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-! ## Definitions -/

/-! ## Membership -/

theorem centeredCube_eq_standardCell (j : ℤ) : centeredCube d j = standardCell d j 0 := by
  ext x
  simp [Recurrence.mem_centeredCube_iff, Recurrence.mem_standardCell_iff]

theorem standardCell_eq_pi_Ioo (k : ℤ) (w : Fin d → ℤ) :
    standardCell d k w =
      Set.pi Set.univ fun i =>
        Set.Ioo (((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ k) (((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ k) := by
  ext x
  simp [Recurrence.mem_standardCell_iff]

theorem measurableSet_standardCell (k : ℤ) (w : Fin d → ℤ) :
    MeasurableSet (standardCell d k w) :=
  measurableSet_openCubeSet _

theorem isOpen_standardCell (k : ℤ) (w : Fin d → ℤ) : IsOpen (standardCell d k w) := by
  rw [standardCell_eq_pi_Ioo]
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioo

/-! ## Volume -/

theorem volume_standardCell (k : ℤ) (w : Fin d → ℤ) :
    volume (standardCell d k w) = ENNReal.ofReal ((3 : ℝ) ^ k) ^ d := by
  rw [standardCell_eq_pi_Ioo, volume_pi_pi]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hside : ∀ i : Fin d,
      volume (Set.Ioo (((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ k) (((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ k))
        = ENNReal.ofReal ((3 : ℝ) ^ k) := by
    intro i
    rw [Real.volume_Ioo]
    congr 1
    ring
  rw [Finset.prod_congr rfl fun i _ => hside i]
  simp

theorem volume_centeredCube (j : ℤ) :
    volume (centeredCube d j) = ENNReal.ofReal ((3 : ℝ) ^ j) ^ d := by
  rw [centeredCube_eq_standardCell, volume_standardCell]

theorem volume_standardCell_pos (k : ℤ) (w : Fin d → ℤ) :
    0 < volume (standardCell d k w) := by
  rw [volume_standardCell]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr h3) d


/-! ## Nesting and disjointness of aligned cubes -/

/-- One-dimensional core of "aligned triadic cubes are nested or disjoint": if the open
intervals `((w - 1/2) a, (w + 1/2) a)` and `((w' - 1/2) 3^n a, (w' + 1/2) 3^n a)` share a
point, the first lies inside the second.  Uses only that `3^n` is odd. -/
theorem triadic_interval_subset_of_mem {a : ℝ} (ha : 0 < a) (n : ℕ) {w w' : ℤ} {x : ℝ}
    (h1 : ((w : ℝ) - 1 / 2) * a < x) (h2 : x < ((w : ℝ) + 1 / 2) * a)
    (h3 : ((w' : ℝ) - 1 / 2) * ((3 : ℝ) ^ n * a) < x)
    (h4 : x < ((w' : ℝ) + 1 / 2) * ((3 : ℝ) ^ n * a)) :
    ((w' : ℝ) - 1 / 2) * ((3 : ℝ) ^ n * a) ≤ ((w : ℝ) - 1 / 2) * a ∧
      ((w : ℝ) + 1 / 2) * a ≤ ((w' : ℝ) + 1 / 2) * ((3 : ℝ) ^ n * a) := by
  obtain ⟨m, hm⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hm' : (3 : ℝ) ^ n = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  rw [hm'] at h3 h4 ⊢
  -- divide out `a`
  have hA : ((w : ℝ) - 1 / 2) < ((w' : ℝ) + 1 / 2) * (2 * (m : ℝ) + 1) := by
    have := h1.trans h4
    nlinarith only [ha, this]
  have hB : ((w' : ℝ) - 1 / 2) * (2 * (m : ℝ) + 1) < ((w : ℝ) + 1 / 2) := by
    have := h3.trans h2
    nlinarith only [ha, this]
  -- integer consequences
  have hA' : w - (2 * m + 1) * w' ≤ m := by
    have : (w : ℝ) - (2 * (m : ℝ) + 1) * w' < (m : ℝ) + 1 := by linarith only [hA]
    have h : w - (2 * m + 1) * w' < m + 1 := by exact_mod_cast this
    omega
  have hB' : (2 * m + 1) * w' - w ≤ m := by
    have : (2 * (m : ℝ) + 1) * w' - (w : ℝ) < (m : ℝ) + 1 := by linarith only [hB]
    have h : (2 * m + 1) * w' - w < m + 1 := by exact_mod_cast this
    omega
  have hA'' : ((w : ℝ) - (2 * (m : ℝ) + 1) * w') ≤ m := by exact_mod_cast hA'
  have hB'' : ((2 * (m : ℝ) + 1) * w' - (w : ℝ)) ≤ m := by exact_mod_cast hB'
  constructor <;> nlinarith only [ha, hA'', hB'']

/-- Aligned triadic cubes of generations `k ≤ k'` are nested or disjoint. -/
theorem standardCell_subset_or_disjoint {k k' : ℤ} (hkk' : k ≤ k') (w w' : Fin d → ℤ) :
    standardCell d k w ⊆ standardCell d k' w' ∨
      Disjoint (standardCell d k w) (standardCell d k' w') := by
  by_cases hdis : Disjoint (standardCell d k w) (standardCell d k' w')
  · exact Or.inr hdis
  left
  obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp hdis
  rw [Recurrence.mem_standardCell_iff] at hx hx'
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hpow : (3 : ℝ) ^ k' = (3 : ℝ) ^ ((k' - k).toNat) * (3 : ℝ) ^ k := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  intro y hy
  rw [Recurrence.mem_standardCell_iff] at hy ⊢
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  obtain ⟨hlo', hhi'⟩ := hx' i
  rw [hpow] at hlo' hhi' ⊢
  obtain ⟨hL, hR⟩ := triadic_interval_subset_of_mem h3 ((k' - k).toNat) hlo hhi hlo' hhi'
  exact ⟨hL.trans_lt (hy i).1, (hy i).2.trans_le hR⟩

/-- Distinct aligned cubes of the same generation are disjoint. -/
theorem standardCell_disjoint_of_ne (k : ℤ) {w w' : Fin d → ℤ} (hww' : w ≠ w') :
    Disjoint (standardCell d k w) (standardCell d k w') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hww'
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Recurrence.mem_standardCell_iff] at hx hx'
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  obtain ⟨hlo, hhi⟩ := hx i
  obtain ⟨hlo', hhi'⟩ := hx' i
  have h1 : ((w i : ℝ) - 1 / 2) < ((w' i : ℝ) + 1 / 2) := by
    have := hlo.trans hhi'
    nlinarith only [h3, this]
  have h2 : ((w' i : ℝ) - 1 / 2) < ((w i : ℝ) + 1 / 2) := by
    have := hlo'.trans hhi
    nlinarith only [h3, this]
  have h1' : w i < w' i + 1 := by
    have : (w i : ℝ) < (w' i : ℝ) + 1 := by linarith only [h1]
    exact_mod_cast this
  have h2' : w' i < w i + 1 := by
    have : (w' i : ℝ) < (w i : ℝ) + 1 := by linarith only [h2]
    exact_mod_cast this
  exact hi (by omega)

/-- A cube of generation `k` is contained in a cube of generation `k' ≥ k` that meets it. -/
theorem standardCell_subset_of_mem {k k' : ℤ} (hkk' : k ≤ k') {w w' : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ standardCell d k w) (hx' : x ∈ standardCell d k' w') :
    standardCell d k w ⊆ standardCell d k' w' := by
  rcases standardCell_subset_or_disjoint hkk' w w' with h | h
  · exact h
  · exact absurd hx' (Set.disjoint_left.mp h hx)

/-- The generation and index of an aligned cube are determined by the cube (for `d ≥ 1`). -/
theorem eq_of_standardCell_eq [NeZero d] {k k' : ℤ} {w w' : Fin d → ℤ}
    (h : standardCell d k w = standardCell d k' w') : k = k' ∧ w = w' := by
  have hk : k = k' := by
    have hvol := congrArg (fun s => (volume s).toReal) h
    simp only [volume_standardCell, ENNReal.toReal_pow] at hvol
    have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    have h3' : (0 : ℝ) < (3 : ℝ) ^ k' := by positivity
    rw [ENNReal.toReal_ofReal h3.le, ENNReal.toReal_ofReal h3'.le] at hvol
    have hbase : (3 : ℝ) ^ k = (3 : ℝ) ^ k' :=
      (pow_left_inj₀ h3.le h3'.le (NeZero.ne d)).mp hvol
    exact zpow_right_injective₀ (by norm_num) (by norm_num) hbase
  subst hk
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hdis := standardCell_disjoint_of_ne (d := d) k hne
  rw [h, disjoint_self, Set.bot_eq_empty] at hdis
  exact (Set.nonempty_of_mem (Recurrence.standardCellCenter_mem_standardCell k w')).ne_empty hdis

/-! ## Size -/

/-- Two points of an aligned cube of generation `k` are at squared Euclidean distance at
most `d 3^{2k}`. -/
theorem sum_sq_sub_le_of_mem_standardCell {k : ℤ} {w : Fin d → ℤ} {x x' : Vec d}
    (hx : x ∈ standardCell d k w) (hx' : x' ∈ standardCell d k w) :
    ∑ i, (x i - x' i) ^ 2 ≤ (d : ℝ) * ((3 : ℝ) ^ k) ^ 2 := by
  rw [Recurrence.mem_standardCell_iff] at hx hx'
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), (x i - x' i) ^ 2 ≤ ((3 : ℝ) ^ k) ^ 2 := by
    intro i _
    obtain ⟨hlo, hhi⟩ := hx i
    obtain ⟨hlo', hhi'⟩ := hx' i
    have hd1 : x i - x' i < (3 : ℝ) ^ k := by nlinarith only [hhi, hlo']
    have hd2 : -((3 : ℝ) ^ k) < x i - x' i := by nlinarith only [hlo, hhi']
    nlinarith only [hd1, hd2]
  have := Finset.sum_le_card_nsmul Finset.univ (fun i => (x i - x' i) ^ 2) _ hterm
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

/-- An aligned cube of generation `k` lies in the sup-metric ball of radius `3^k` about any
of its points. -/
theorem standardCell_subset_ball {k : ℤ} {w : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ standardCell d k w) :
    standardCell d k w ⊆ Metric.ball x ((3 : ℝ) ^ k) := by
  intro y hy
  rw [Recurrence.mem_standardCell_iff] at hx hy
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [Metric.mem_ball, dist_pi_lt_iff h3]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  obtain ⟨hlo', hhi'⟩ := hy i
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · nlinarith only [hhi', hlo]
  · nlinarith only [hlo', hhi]

/-! ## Grid faces -/

/-- The faces of the generation-`k` grid: the hyperplanes `x_i = (n + 1/2) 3^k`. -/
@[expose]
def gridFaces (d : ℕ) (k : ℤ) : Set (Vec d) :=
  ⋃ i : Fin d, ⋃ n : ℤ, {x | x i = ((n : ℝ) + 1 / 2) * (3 : ℝ) ^ k}

theorem volume_gridFaces (k : ℤ) : volume (gridFaces d k) = 0 := by
  unfold gridFaces
  refine measure_iUnion_null fun i => measure_iUnion_null fun n => ?_
  exact Recurrence.volume_coord_eq i _

/-- A point off the generation-`k` grid faces lies in an aligned cube of generation `k`. -/
theorem exists_mem_standardCell_of_not_mem_gridFaces {k : ℤ} {x : Vec d}
    (hx : x ∉ gridFaces d k) : ∃ w : Fin d → ℤ, x ∈ standardCell d k w := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  refine ⟨fun i => ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋, ?_⟩
  rw [Recurrence.mem_standardCell_iff]
  intro i
  set w : ℤ := ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ with hw
  have hfl := Int.floor_le (x i / (3 : ℝ) ^ k + 1 / 2)
  have hfl' := Int.lt_floor_add_one (x i / (3 : ℝ) ^ k + 1 / 2)
  rw [← hw] at hfl hfl'
  have hdiv : x i / (3 : ℝ) ^ k * (3 : ℝ) ^ k = x i := div_mul_cancel₀ _ h3.ne'
  have hlo : ((w : ℝ) - 1 / 2) * (3 : ℝ) ^ k ≤ x i := by
    nlinarith only [h3, hfl, hdiv]
  have hhi : x i < ((w : ℝ) + 1 / 2) * (3 : ℝ) ^ k := by
    nlinarith only [h3, hfl', hdiv]
  refine ⟨lt_of_le_of_ne hlo ?_, hhi⟩
  intro heq
  apply hx
  simp only [gridFaces, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨i, w - 1, ?_⟩
  rw [← heq]
  push_cast
  ring

end HCPolySupport.HighContrast.Geometry
