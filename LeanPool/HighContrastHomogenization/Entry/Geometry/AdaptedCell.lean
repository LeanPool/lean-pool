/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Instances.Matrix
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyLayer

/-!
# High-contrast homogenization: Entry.Geometry.AdaptedCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted cells

The adapted cell `⋄_j^q = q □_j` and its translate `W = y + ⋄_j^q` of the paper,
together with the two facts about `W` that `l.source.whitney` uses: its volume under the
change of variables `x = y + q v`, and the strip estimate
`|{x ∈ W : dist(x, ∂W) ≤ s}| / |W| ≤ 2 d |q⁻¹| s 3^{-j}`.

The definitions `adaptedCell` and `adaptedCellTranslate` live in `HCPoly.Setup.Geometry`
(imported here), so that they can be used without these proofs.
The bound `|q⁻¹| ≤ K` of `e.rounded.grid.bounds` enters only through the hypothesis
`InverseNormLE q K`, i.e. `|v| ≤ K |q v|` for all `v` (stated with squared Euclidean norms).
-/

open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory Matrix

variable {d : ℕ}

/-! ## Definitions -/

/-- The operator-norm bound `|q⁻¹| ≤ K`, in the form `|v|² ≤ K² |q v|²` for every `v`. -/
@[expose]
def InverseNormLE (q : Mat d) (K : ℝ) : Prop :=
  ∀ v : Vec d, vecNormSq v ≤ K ^ 2 * vecNormSq (matVecMul q v)

theorem matVecMul_eq_mulVec (q : Mat d) (v : Vec d) : matVecMul q v = q *ᵥ v := rfl

theorem mem_adaptedCellTranslate_iff {q : Mat d} {j : ℤ} {y x : Vec d} :
    x ∈ adaptedCellTranslate q j y ↔ ∃ v ∈ centeredCube d j, y + matVecMul q v = x := by
  rw [Transport.adaptedCellTranslate_eq_image]
  rfl

/-! ## Volume under the change of variables -/

theorem volume_adaptedCellTranslate (q : Mat d) (j : ℤ) (y : Vec d) :
    volume (adaptedCellTranslate q j y)
      = ENNReal.ofReal |q.det| * ENNReal.ofReal ((3 : ℝ) ^ j) ^ d := by
  rw [Transport.adaptedCellTranslate_eq_image, Transport.volume_image_affine, volume_centeredCube]

/-! ## Invertibility from the inverse bound -/

theorem vecNormSq_eq_zero_iff {v : Vec d} : vecNormSq v = 0 ↔ v = 0 := by
  rw [vecNormSq_eq_sum_sq]
  constructor
  · intro h
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).mp h
    funext i
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (this i (Finset.mem_univ i))
  · rintro rfl
    simp

theorem InverseNormLE.isUnit {q : Mat d} {K : ℝ} (hq : InverseNormLE q K) : IsUnit q := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v v' hvv'
  have hsub : q *ᵥ (v - v') = 0 := by
    rw [Matrix.mulVec_sub, hvv', sub_self]
  have h := hq (v - v')
  rw [matVecMul_eq_mulVec, hsub, vecNormSq_eq_zero_iff.mpr rfl, mul_zero] at h
  have h0 : vecNormSq (v - v') = 0 := le_antisymm h (vecNormSq_nonneg _)
  exact sub_eq_zero.mp (vecNormSq_eq_zero_iff.mp h0)

theorem InverseNormLE.det_ne_zero {q : Mat d} {K : ℝ} (hq : InverseNormLE q K) :
    q.det ≠ 0 :=
  isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det q |>.mp hq.isUnit)

theorem volume_adaptedCellTranslate_pos {q : Mat d} {K : ℝ} (hq : InverseNormLE q K)
    (j : ℤ) (y : Vec d) : 0 < volume (adaptedCellTranslate q j y) := by
  rw [volume_adaptedCellTranslate]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hq.det_ne_zero)).ne'
    (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr h3) d).ne'

/-- For invertible `q`, the translate `y + q □_j` is the preimage of `□_j` under
`x ↦ q⁻¹ (x - y)`. -/
theorem adaptedCellTranslate_eq_preimage {q : Mat d} (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    adaptedCellTranslate q j y = (fun x => q⁻¹ *ᵥ (x - y)) ⁻¹' centeredCube d j := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  ext x
  rw [mem_adaptedCellTranslate_iff, Set.mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [matVecMul_eq_mulVec, add_sub_cancel_left, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul q
      hdet,
      Matrix.one_mulVec]
    exact hv
  · intro hx
    refine ⟨q⁻¹ *ᵥ (x - y), hx, ?_⟩
    rw [matVecMul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv q hdet,
      Matrix.one_mulVec, add_sub_cancel]

theorem isOpen_adaptedCellTranslate {q : Mat d} (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    IsOpen (adaptedCellTranslate q j y) := by
  rw [adaptedCellTranslate_eq_preimage hq, centeredCube_eq_standardCell]
  exact (isOpen_standardCell j 0).preimage
    (Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const))

/-! ## The strip estimate -/

/-- The part of `□_j` within `t` of its boundary, coordinatewise: points of `□_j` with some
coordinate of absolute value at least `3^j/2 - t`. -/
@[expose]
def boundaryStrips (d : ℕ) (j : ℤ) (t : ℝ) : Set (Vec d) :=
  {v | v ∈ centeredCube d j ∧ ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |v i|}

/-- One coordinate strip of `□_j` of width `t`, as a product set. -/
@[expose]
public def coordStrip (d : ℕ) (j : ℤ) (t : ℝ) (i : Fin d) : Set (Vec d) :=
  Set.pi Set.univ (Function.update
    (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j)) i
    (Set.Icc (-(1 / 2 : ℝ) * (3 : ℝ) ^ j) (-(1 / 2 : ℝ) * (3 : ℝ) ^ j + t) ∪
      Set.Icc ((1 / 2 : ℝ) * (3 : ℝ) ^ j - t) ((1 / 2 : ℝ) * (3 : ℝ) ^ j)))

private theorem boundaryStrips_subset_iUnion (j : ℤ) (t : ℝ) :
    boundaryStrips d j t ⊆ ⋃ i, coordStrip d j t i := by
  classical
  rintro v ⟨hv, i, hi⟩
  rw [Recurrence.mem_centeredCube_iff] at hv
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  intro i' _
  by_cases hi' : i' = i
  · subst hi'
    rw [Function.update_self]
    obtain ⟨hlo, hhi⟩ := hv i'
    rcases le_or_gt 0 (v i') with h0 | h0
    · rw [abs_of_nonneg h0] at hi
      exact Or.inr ⟨hi, hhi.le⟩
    · rw [abs_of_neg h0] at hi
      exact Or.inl ⟨hlo.le, by linarith only [hi]⟩
  · rw [Function.update_of_ne hi']
    exact Set.mem_Ioo.mpr (hv i')

private theorem volume_coordStrip_le [NeZero d] (j : ℤ) {t : ℝ} (ht : 0 ≤ t) (i : Fin d) :
    volume (coordStrip d j t i) ≤ ENNReal.ofReal (2 * t) * ENNReal.ofReal ((3 : ℝ) ^ j) ^ (d -
      1) := by
  classical
  unfold coordStrip
  rw [volume_pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    Function.update_self]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hrest : ∏ x ∈ Finset.univ.erase i, volume (Function.update
      (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j)) i
      (Set.Icc (-(1 / 2 : ℝ) * (3 : ℝ) ^ j) (-(1 / 2 : ℝ) * (3 : ℝ) ^ j + t) ∪
        Set.Icc ((1 / 2 : ℝ) * (3 : ℝ) ^ j - t) ((1 / 2 : ℝ) * (3 : ℝ) ^ j)) x)
      = ENNReal.ofReal ((3 : ℝ) ^ j) ^ (d - 1) := by
    rw [Finset.prod_congr rfl fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx), Real.volume_Ioo]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    congr 2
    ring
  rw [hrest]
  refine mul_le_mul_left ?_ _
  refine (measure_union_le _ _).trans ?_
  rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith only [ht]) (by
    linarith only [ht])]
  exact ENNReal.ofReal_le_ofReal (by linarith only [ht])

theorem volume_boundaryStrips_le [NeZero d] (j : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    volume (boundaryStrips d j t)
      ≤ ENNReal.ofReal (2 * (d : ℝ) * t * ((3 : ℝ) ^ j) ^ (d - 1)) := by
  refine (measure_mono (boundaryStrips_subset_iUnion j t)).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => volume_coordStrip_le j ht i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [← ENNReal.ofReal_pow h3.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by ring_nf; exact le_rfl)

/-- Points of `W` within Euclidean distance `s` of a point outside `W` lie in the image of the
boundary strips of width `K s`. -/
theorem mem_image_boundaryStrips {q : Mat d} {K : ℝ} (hK : 0 ≤ K) (hq : InverseNormLE q K)
    {j : ℤ} {y x x' : Vec d} {s : ℝ} (hs : 0 ≤ s) (hx : x ∈ adaptedCellTranslate q j y)
    (hx' : x' ∉ adaptedCellTranslate q j y) (hdist : ∑ i, (x i - x' i) ^ 2 ≤ s ^ 2) :
    x ∈ (fun v => y + matVecMul q v) '' boundaryStrips d j (K * s) := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  obtain ⟨v, hv, rfl⟩ := mem_adaptedCellTranslate_iff.mp hx
  set v' : Vec d := q⁻¹ *ᵥ (x' - y) with hv'
  have hx'eq : y + matVecMul q v' = x' := by
    rw [hv', matVecMul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv q hdet,
      Matrix.one_mulVec, add_sub_cancel]
  have hv'not : v' ∉ centeredCube d j := fun h =>
    hx' (mem_adaptedCellTranslate_iff.mpr ⟨v', h, hx'eq⟩)
  refine ⟨v, ⟨hv, ?_⟩, rfl⟩
  -- the difference `v - v'` is controlled by `x - x'`
  have hdiff : ∑ i, (v i - v' i) ^ 2 ≤ (K * s) ^ 2 := by
    have h := hq (v - v')
    rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, matVecMul_eq_mulVec, Matrix.mulVec_sub] at h
    have hxx : ∀ i, (q *ᵥ v - q *ᵥ v') i = (y + matVecMul q v) i - x' i := by
      intro i
      rw [← hx'eq]
      simp [matVecMul_eq_mulVec]
    simp only [Pi.sub_apply] at h
    have hsum : ∑ i, ((q *ᵥ v) i - (q *ᵥ v') i) ^ 2 = ∑ i, ((y + matVecMul q v) i - x' i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hxx i]
      rfl
    rw [hsum] at h
    calc ∑ i, (v i - v' i) ^ 2 ≤ K ^ 2 * ∑ i, ((y + matVecMul q v) i - x' i) ^ 2 := by
          simpa using h
      _ ≤ K ^ 2 * s ^ 2 := by gcongr
      _ = (K * s) ^ 2 := by ring
  -- some coordinate of `v'` is outside `(-3^j/2, 3^j/2)`
  rw [Recurrence.mem_centeredCube_iff] at hv'not
  push Not at hv'not
  obtain ⟨i, hi⟩ := hv'not
  refine ⟨i, ?_⟩
  have hcoord : (v i - v' i) ^ 2 ≤ (K * s) ^ 2 :=
    (Finset.single_le_sum (fun i _ => sq_nonneg (v i - v' i)) (Finset.mem_univ i)).trans hdiff
  have habs : |v i - v' i| ≤ K * s := abs_le_of_sq_le_sq hcoord (by positivity)
  have hv'i : (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |v' i| := by
    by_contra hcon
    push Not at hcon
    rw [abs_lt] at hcon
    exact absurd hcon.2 (not_lt.mpr (hi (by linarith only [hcon.1])))
  have := abs_sub_abs_le_abs_sub (v' i) (v i)
  rw [abs_sub_comm] at this
  linarith only [hv'i, habs, this]

/-- **The strip estimate.**  If every point of `A ⊆ W` is within Euclidean distance `s` of a
point outside `W`, then `|A| ≤ 2 d K s 3^{-j} |W|`, where `|q⁻¹| ≤ K`. -/
theorem volume_le_of_near_complement [NeZero d] {q : Mat d} {K : ℝ} (hK : 0 ≤ K)
    (hq : InverseNormLE q K) {j : ℤ} {y : Vec d} {A : Set (Vec d)} {s : ℝ} (hs : 0 ≤ s)
    (hAW : A ⊆ adaptedCellTranslate q j y)
    (hA : ∀ x ∈ A, ∃ x', x' ∉ adaptedCellTranslate q j y ∧ ∑ i, (x i - x' i) ^ 2 ≤ s ^ 2) :
    volume A ≤ ENNReal.ofReal (2 * (d : ℝ) * (K * s) * (3 : ℝ) ^ (-j)) *
      volume (adaptedCellTranslate q j y) := by
  have hsub : A ⊆ (fun v => y + matVecMul q v) '' boundaryStrips d j (K * s) := by
    intro x hx
    obtain ⟨x', hx', hdist⟩ := hA x hx
    exact mem_image_boundaryStrips hK hq hs (hAW hx) hx' hdist
  refine (measure_mono hsub).trans ?_
  rw [Transport.volume_image_affine, volume_adaptedCellTranslate]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hKs : 0 ≤ K * s := by positivity
  refine (mul_le_mul_right (volume_boundaryStrips_le j hKs) _).trans ?_
  rw [← ENNReal.ofReal_pow h3.le, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  subst hd'
  simp only [Nat.add_sub_cancel]
  rw [_root_.zpow_neg, pow_succ]
  field_simp

end HCPolySupport.HighContrast.Geometry
