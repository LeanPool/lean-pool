/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Setup.SpectralNorm
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# High-contrast homogenization: Provider.Transport.WhitneyLayer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The boundary layer of a target cell

The maximal filling of `l.two.grid.whitney` selects a cell of one
grid inside a cell of another exactly when the selected cell fits and its parent
does not.  Every cell it selects, and every point it fails to cover, therefore
lies in a thin layer along the boundary of the target: the escaping ancestor
joins a point of the target to a point outside it, and the whole ancestor has
diameter comparable to its own side length.

This file proves the measure of that layer, the boundary-layer volume of an
adapted cube, in the form the row and residual bounds of
`e.source.whitney.volumes` consume.  In the
coordinates of the target the layer is the union of the `2d` coordinate slabs
along the faces of a centered triadic cube, and each slab has relative volume at
most twice the layer width over the side length.  The escaping ancestor
contributes its own side length through the cross-grid factor `|p^{-1}q|`: a
displacement inside an ancestor of the second grid has length at most
`√d 3^c` there, and the linear change of coordinates to the first grid multiplies
lengths by at most the operator norm of `p^{-1}q`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The operator norm controls a coordinate of a displacement -/

private theorem le_of_sq_le_sq₀ {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  have hsq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hv] at hsq
  exact le_trans (le_abs_self u) hsq

private theorem norm_toLp_sq₀ (z : Vec d) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d))‖ ^ 2 = vecNormSq z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecNormSq_matVecMul_le₀ (M : Mat d) (z : Vec d) :
    vecNormSq (matVecMul M z) ≤ ‖M‖ ^ 2 * vecNormSq z := by
  have hT : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M (WithLp.toLp 2 z)
      = WithLp.toLp 2 (matVecMul M z) := rfl
  have hle : ‖(WithLp.toLp 2 (matVecMul M z) : EuclideanSpace ℝ (Fin d))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d))‖ := by
    rw [← hT]
    exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M).le_opNorm _
  have hsq : ‖(WithLp.toLp 2 (matVecMul M z) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
      (‖M‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d))‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [norm_toLp_sq₀, mul_pow, norm_toLp_sq₀] at hsq

/-- **A coordinate of a linear image is controlled by the operator norm.**  If
every coordinate of `z` is at most `c` in modulus, then every coordinate of
`M z` is at most `‖M‖ √d c`. -/
theorem abs_matVecMul_le_of_abs_le (M : Mat d) {z : Vec d} {c : ℝ}
    (hz : ∀ k, |z k| ≤ c) (i : Fin d) :
    |matVecMul M z i| ≤ ‖M‖ * (Real.sqrt d * c) := by
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hz i)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hzsq : vecNormSq z ≤ (d : ℝ) * c ^ 2 := by
    have hterm : ∀ k ∈ Finset.univ, z k * z k ≤ c ^ 2 := by
      intro k _
      have := hz k
      have hsq : |z k| ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [sq_abs] at hsq
      calc z k * z k = z k ^ 2 := (sq (z k)).symm
        _ ≤ c ^ 2 := hsq
    have hsum := Finset.sum_le_sum hterm
    simpa [vecNormSq, vecDot, Finset.sum_const, Finset.card_univ, mul_comm] using hsum
  have hcoord : (matVecMul M z i) ^ 2 ≤ vecNormSq (matVecMul M z) := by
    refine Finset.single_le_sum (f := fun k => matVecMul M z k * matVecMul M z k)
      (fun k _ => mul_self_nonneg _) (Finset.mem_univ i) |>.trans_eq' ?_
    exact (sq _).symm
  have hMsq : (0 : ℝ) ≤ ‖M‖ ^ 2 := sq_nonneg _
  have hchain : (matVecMul M z i) ^ 2 ≤ (‖M‖ * (Real.sqrt d * c)) ^ 2 := by
    have h1 : vecNormSq (matVecMul M z) ≤ ‖M‖ ^ 2 * ((d : ℝ) * c ^ 2) :=
      (vecNormSq_matVecMul_le₀ M z).trans (mul_le_mul_of_nonneg_left hzsq hMsq)
    have hroot : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt hd
    have hexp : (‖M‖ * (Real.sqrt d * c)) ^ 2 = ‖M‖ ^ 2 * ((d : ℝ) * c ^ 2) := by
      rw [mul_pow, mul_pow, hroot]
    rw [hexp]
    exact hcoord.trans h1
  refine le_of_sq_le_sq₀ (by positivity) ?_
  rwa [sq_abs]

/-! ## The slab along one pair of faces of a centered cube -/

/-- The volume of a centered triadic cube as the product of its side lengths. -/
theorem volume_centeredCube_eq_prod (j : ℤ) :
    volume (centeredCube d j) = ∏ _i : Fin d, ENNReal.ofReal ((3 : ℝ) ^ j) := by
  have hpi : centeredCube d j = Set.univ.pi fun _ : Fin d =>
      Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) := by
    ext x
    rw [Recurrence.mem_centeredCube_iff]
    simp [Set.mem_pi]
  rw [hpi, volume_pi, MeasureTheory.Measure.pi_pi]
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [Real.volume_Ioo]
  ring_nf

private theorem volume_slabLine_le₀ (j : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    volume (Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) ∩
        {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |s|}) ≤ ENNReal.ofReal (2 * t) := by
  have hsub : Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) ∩
      {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |s|} ⊆
      Set.Icc (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) (t - (1 / 2 : ℝ) * (3 : ℝ) ^ j) ∪
        Set.Icc ((1 / 2 : ℝ) * (3 : ℝ) ^ j - t) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) := by
    rintro s ⟨⟨hlo, hhi⟩, habs⟩
    rw [Set.mem_ofPred_eq] at habs
    rcases le_or_gt 0 s with hs | hs
    · exact Or.inr ⟨by rwa [abs_of_nonneg hs] at habs, hhi.le⟩
    · refine Or.inl ⟨hlo.le, ?_⟩
      rw [abs_of_neg hs] at habs
      linarith only [habs]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith only [ht])
    (by linarith only [ht])]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith only []

/-- **The boundary layer of a centered triadic cube.**  The points of `□_j` within
`t` of one of the `2d` faces have relative volume at most `2 d t 3^{-j}`; this is
the boundary-layer volume bound in the coordinates of the cube. -/
theorem volume_layer_centeredCube_le (j : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    volume {z : Vec d | z ∈ centeredCube d j ∧
        ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} ≤
      ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) * volume (centeredCube d j) := by
  classical
  set c : ℝ := 2 * t * (3 : ℝ) ^ (-j) with hc
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hcmul : ENNReal.ofReal c * ENNReal.ofReal ((3 : ℝ) ^ j) = ENNReal.ofReal (2 * t) := by
    rw [← ENNReal.ofReal_mul hc0, hc]
    congr 1
    rw [zpow_neg]
    field_simp
  have hrow : ∀ i : Fin d,
      volume {z : Vec d | z ∈ centeredCube d j ∧
          (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} ≤
        ENNReal.ofReal c * volume (centeredCube d j) := by
    intro i
    have hpi : {z : Vec d | z ∈ centeredCube d j ∧
        (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} =
        Set.univ.pi fun k : Fin d =>
          if k = i then
            Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) ∩
              {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |s|}
          else Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Recurrence.mem_centeredCube_iff]
      constructor
      · rintro ⟨hz, hi⟩ k
        by_cases hk : k = i
        · subst hk
          rw [ite_eq_left rfl]
          exact ⟨⟨(hz k).1, (hz k).2⟩, hi⟩
        · rw [ite_eq_right hk]
          exact ⟨(hz k).1, (hz k).2⟩
      · intro h
        refine ⟨fun k => ?_, ?_⟩
        · by_cases hk : k = i
          · subst hk
            have := h k
            rw [ite_eq_left rfl] at this
            exact ⟨this.1.1, this.1.2⟩
          · have := h k
            rw [ite_eq_right hk] at this
            exact ⟨this.1, this.2⟩
        · have := h i
          rw [ite_eq_left rfl] at this
          exact this.2
    calc volume {z : Vec d | z ∈ centeredCube d j ∧
            (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|}
        = ∏ k : Fin d, volume (if k = i then
            Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j) ∩
              {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |s|}
            else Set.Ioo (-((1 : ℝ) / 2) * (3 : ℝ) ^ j) ((1 / 2 : ℝ) * (3 : ℝ) ^ j)) := by
          rw [hpi, volume_pi, MeasureTheory.Measure.pi_pi]
      _ ≤ ∏ k : Fin d, ((if k = i then ENNReal.ofReal c else 1) *
            ENNReal.ofReal ((3 : ℝ) ^ j)) := by
          refine Finset.prod_le_prod fun k _ => ?_
          by_cases hk : k = i
          · subst hk
            rw [ite_eq_left rfl, ite_eq_left rfl, hcmul]
            exact volume_slabLine_le₀ j ht
          · rw [ite_eq_right hk, ite_eq_right hk, one_mul, Real.volume_Ioo]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            ring
      _ = (∏ k : Fin d, if k = i then ENNReal.ofReal c else 1) *
            ∏ _k : Fin d, ENNReal.ofReal ((3 : ℝ) ^ j) := Finset.prod_mul_distrib
      _ = ENNReal.ofReal c * volume (centeredCube d j) := by
          rw [volume_centeredCube_eq_prod,
            Finset.prod_ite_eq' Finset.univ i fun _ => ENNReal.ofReal c]
          simp
  have hcover : {z : Vec d | z ∈ centeredCube d j ∧
      ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} ⊆
      ⋃ i : Fin d, {z : Vec d | z ∈ centeredCube d j ∧
        (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} := by
    rintro z ⟨hz, i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hz, hi⟩
  refine (measure_mono hcover).trans ((measure_iUnion_fintype_le volume _).trans ?_)
  refine (Finset.sum_le_sum fun i _ => hrow i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  congr 2
  rw [hc]
  ring

/-! ## The layer of a target cell of a second grid -/

/-- A translated adapted cell is the affine image of the centered cube. -/
theorem adaptedCellTranslate_eq_image (p : Mat d) (j : ℤ) (y : Vec d) :
    adaptedCellTranslate p j y = (fun z => y + matVecMul p z) '' centeredCube d j := by
  rw [adaptedCellTranslate, adaptedCell, Set.image_image]

/-- An affine image scales volume by the modulus of the determinant. -/
theorem volume_image_affine (p : Mat d) (y : Vec d) (S : Set (Vec d)) :
    volume ((fun z => y + matVecMul p z) '' S) = ENNReal.ofReal |p.det| * volume S := by
  have h1 : (fun z => y + matVecMul p z) '' S = (fun x => y + x) '' (matVecMul p '' S) := by
    rw [Set.image_image]
  have h2 : volume ((fun x => y + x) '' (matVecMul p '' S)) = volume (matVecMul p '' S) := by
    rw [Set.image_add_left]
    exact measure_preimage_add volume _ _
  have h3 := MeasureTheory.Measure.addHaar_image_linearMap
    (μ := (volume : Measure (Vec d))) (Matrix.mulVecLin p) S
  have h4 : LinearMap.det (Matrix.mulVecLin p) = p.det := by
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' p
  rw [h1, h2]
  rw [h4] at h3
  exact h3

/-- **The cells that escape the target lie in its boundary layer.**  If every
point of `A` lies in the target cell `y + ⋄_j^p` and also in some aligned
`q`-cell of scale `c` that is *not* contained in the target, then `A` has
relative volume at most `2 d^{3/2} |p^{-1}q| 3^{c-j}`.

This is the boundary-layer volume of an adapted cube in the form the row and
residual bounds of `e.source.whitney.volumes` consume: for a selected cell of
scale `a < n` the escaping ancestor is its own parent, `c = a + 1`, and for a
point left uncovered at the cutoff `J` it is the cell of scale `c = J` that
contains it. -/
theorem volume_le_of_escaping_ancestor {p q : Mat d} (hp : p.PosDef) {j c : ℤ}
    {y : Vec d} {A : Set (Vec d)} (hAW : A ⊆ adaptedCellTranslate p j y)
    (hesc : ∀ x ∈ A, ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
      ¬ adaptedCellAt q c v ⊆ adaptedCellTranslate p j y) :
    volume A ≤
      ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (c - j)) *
        volume (adaptedCellTranslate p j y) := by
  classical
  set t : ℝ := ‖p⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ c) with htdef
  have ht : 0 ≤ t := by positivity
  have hdet : IsUnit p.det := (Matrix.isUnit_iff_isUnit_det p).mp hp.isUnit
  have hinv : ∀ w : Vec d, matVecMul p (matVecMul p⁻¹ w) = w := by
    intro w
    show p *ᵥ p⁻¹ *ᵥ w = w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsub : A ⊆ (fun z => y + matVecMul p z) ''
      {z : Vec d | z ∈ centeredCube d j ∧
        ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} := by
    intro x hxA
    obtain ⟨xt, hxt, hxeq⟩ := (adaptedCellTranslate_eq_image p j y ▸ hAW hxA)
    obtain ⟨v, hxv, hvesc⟩ := hesc x hxA
    obtain ⟨zp, hzpv, hzpW⟩ := Set.not_subset.mp hvesc
    set zt : Vec d := matVecMul p⁻¹ (zp - y) with hztdef
    have hzeq : y + matVecMul p zt = zp := by rw [hztdef, hinv]; abel
    have hztout : zt ∉ centeredCube d j := by
      intro hmem
      exact hzpW (adaptedCellTranslate_eq_image p j y ▸ ⟨zt, hmem, hzeq⟩)
    obtain ⟨x', hx', hx'eq⟩ := (Recurrence.adaptedCellAt_eq_image q c v ▸ hxv)
    obtain ⟨z', hz', hz'eq⟩ := (Recurrence.adaptedCellAt_eq_image q c v ▸ hzpv)
    have hpx : matVecMul p xt = x - y := eq_sub_of_add_eq' hxeq
    have hpz : matVecMul p zt = zp - y := eq_sub_of_add_eq' hzeq
    have hdiff : xt - zt = matVecMul (p⁻¹ * q) (x' - z') := by
      have hp1 : matVecMul p (xt - zt) = matVecMul q (x' - z') := by
        rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, hpx, hpz,
          sub_eq_add_neg (a := x'), matVecMul_add, matVecMul_neg, hx'eq, hz'eq]
        abel
      have hp2 : matVecMul p⁻¹ (matVecMul p (xt - zt)) = xt - zt := by
        show p⁻¹ *ᵥ p *ᵥ (xt - zt) = xt - zt
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
      rw [← hp2, hp1, matVecMul_mul]
    have hcell : ∀ k, |(x' - z') k| ≤ (3 : ℝ) ^ c := by
      intro k
      rw [Recurrence.mem_standardCell_iff] at hx' hz'
      have h1 := hx' k
      have h2 := hz' k
      have hxz : (x' - z') k = x' k - z' k := rfl
      rw [hxz, abs_le]
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
    have hclose : ∀ i, |xt i - zt i| ≤ t := by
      intro i
      have := abs_matVecMul_le_of_abs_le (p⁻¹ * q) hcell i
      rw [← hdiff] at this
      exact this
    obtain ⟨i, hi⟩ : ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |zt i| := by
      by_contra hcon
      push Not at hcon
      refine hztout (Recurrence.mem_centeredCube_iff.mpr fun i => ?_)
      have := hcon i
      rw [abs_lt] at this
      exact ⟨by linarith only [this.1], this.2⟩
    refine ⟨xt, ⟨hxt, i, ?_⟩, hxeq⟩
    have h1 := hclose i
    have h2 : |zt i| - |xt i| ≤ |xt i - zt i| := by
      rw [abs_sub_comm]
      exact abs_sub_abs_le_abs_sub _ _
    linarith only [hi, h1, h2]
  calc volume A
      ≤ volume ((fun z => y + matVecMul p z) ''
          {z : Vec d | z ∈ centeredCube d j ∧
            ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|}) := measure_mono hsub
    _ = ENNReal.ofReal |p.det| *
          volume {z : Vec d | z ∈ centeredCube d j ∧
            ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} := volume_image_affine p y _
    _ ≤ ENNReal.ofReal |p.det| *
          (ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) * volume (centeredCube d j)) :=
        mul_le_mul' le_rfl (volume_layer_centeredCube_le j ht)
    _ = ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) *
          (ENNReal.ofReal |p.det| * volume (centeredCube d j)) := by ring
    _ = ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (c - j)) *
          volume (adaptedCellTranslate p j y) := by
        have harg : 2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)
            = 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (c - j) := by
          rw [htdef, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg]
          field_simp
        rw [adaptedCellTranslate_eq_image p j y, volume_image_affine p y (centeredCube d j), harg]

end

end Transport
end HighContrast
end HCPolySupport
