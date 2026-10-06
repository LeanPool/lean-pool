/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisonsOneSided

/-!
# High-contrast homogenization: Entry.Annealed.BridgeBoundarySum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The boundary sum, drift advance, and normalization sandwich

`p.successful.short.bridge`. The boundary estimate retains
`1-(1-γ)/8` through a separate maximum-weight inequality. Empty integer
intervals are allowed. Every inverse normalization uses a positive definite
actual annealed mean.

-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale blockSub
  blockTrace blockVecDot_blockMatVecMul_eq_sum gridRatio matSqrt normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell centeredCube)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Multiscale
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable section

private theorem bridge_telescope {E : Type*} [AddCommGroup E]
    (f : ℤ → E) {r m : ℤ} (hrm : r ≤ m) :
    f r = f m + ∑ j ∈ Finset.Icc (r + 1) m, (f (j - 1) - f j) := by
  classical
  induction m, hrm using Int.leInduction with
  | base => simp
  | succ m hrm ih =>
    have he : Finset.Icc (r + 1) (m + 1) = insert (m + 1) (Finset.Icc (r + 1) m) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [he, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_sub_cancel_right]
    rw [ih]
    abel

private lemma bridge_self_le_three_halves_mul {P : ℝ} (hP : 0 ≤ P) :
    P ≤ (3 / 2 : ℝ) * P := by
  linarith only [hP]

private theorem bridge_geometric_interval (J cap m : ℤ) :
    (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ ((r : ℝ) - m)) ≤
      (3 / 2 : ℝ) * (3 : ℝ) ^ ((cap : ℝ) - m) := by
  classical
  by_cases hJ : J ≤ cap
  · induction cap, hJ using Int.leInduction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      exact bridge_self_le_three_halves_mul (Real.rpow_nonneg (by norm_num) _)
    | succ cap hJ ih =>
      have he : Finset.Icc J (cap + 1) = insert (cap + 1) (Finset.Icc J cap) := by
        ext r
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hp : (3 : ℝ) ^ (((cap + 1 : ℤ) : ℝ) - m) = 3 * (3 : ℝ) ^ ((cap : ℝ) - m) := by
        rw [show ((cap + 1 : ℤ) : ℝ) - m = 1 + ((cap : ℝ) - m) by push_cast; ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
      rw [he, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hp]
      linarith only [ih]
  · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
    positivity

/-- Both branches of the maximum split retain the printed boundary exponent. -/
theorem bridge_boundary_weight_split {a L t : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (3 : ℝ) ^ (-max L t) ≤ (3 : ℝ) ^ (-(1 - a) * L) * (3 : ℝ) ^ (-a * t) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  by_cases hLt : L ≤ t
  · rw [max_eq_right hLt]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hLt) (sub_nonneg.mpr ha.2)]
  · rw [max_eq_left (le_of_not_ge hLt)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hLt)) ha.1]

private theorem bridge_triangular_sum (J m L : ℤ) (w b : ℤ → ℝ) :
    (∑ r ∈ Finset.Icc J (m - L), w r * ∑ j ∈ Finset.Icc (r + 1) m, b j) =
      ∑ j ∈ Finset.Icc (J + 1) m, (∑ r ∈ Finset.Icc J (min (m - L) (j - 1)), w r) * b j := by
  classical
  have hi (r : ℤ) (hr : r ∈ Finset.Icc J (m - L)) :
      Finset.Icc (r + 1) m = (Finset.Icc (J + 1) m).filter (fun j => r < j) := by
    ext j
    have hrr := Finset.mem_Icc.mp hr
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  calc
    _ = ∑ r ∈ Finset.Icc J (m - L), ∑ j ∈ Finset.Icc (J + 1) m,
        if r < j then w r * b j else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hi r hr, Finset.sum_filter, Finset.mul_sum]
      simp only [mul_ite, mul_zero]
    _ = ∑ j ∈ Finset.Icc (J + 1) m, ∑ r ∈ Finset.Icc J (m - L),
        if r < j then w r * b j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have he : (Finset.Icc J (m - L)).filter (fun r => r < j) =
          Finset.Icc J (min (m - L) (j - 1)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
        omega
      rw [← Finset.sum_filter, ← Finset.sum_mul, he]

private theorem bridge_full_sub {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext (i | i) (j | j) <;> rfl

private theorem bridge_congr_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A ≤ B) (S : Matrix ι ι ℝ) (hS : S.IsHermitian) :
    S * A * S ≤ S * B * S := by
  apply Matrix.le_iff.mpr
  have ht := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same S
  simpa only [hS.eq, mul_sub, sub_mul] using ht

/-- Removing a positive definite normalization preserves the quadratic order.
The inverse is used only after its nonsingularity has been established. -/
theorem bridge_unnormalize_order {d : ℕ} {A B F : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hF : (toFullBlockMat F).PosDef)
    (h : BlockMatLoewnerLE (normalizedBlock A F) (normalizedBlock B F)) :
    BlockMatLoewnerLE A B := by
  let R := matSqrt (toFullBlockMat F)⁻¹
  have hR : R.PosDef := matSqrt_inv_posDef_full hF
  have hN (H : BlockMat d) (hH : (toFullBlockMat H).IsHermitian) :
      (toFullBlockMat (normalizedBlock H F)).IsHermitian := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change (R * toFullBlockMat H * R).IsHermitian
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hR.isHermitian.eq, hH.eq, mul_assoc]
  have hm := (fullBlock_le_iff (hN A hA) (hN B hB)).2 h
  have hi := bridge_congr_order hm R⁻¹ hR.inv.isHermitian
  have hRiR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hRRi := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hc (H : BlockMat d) : R⁻¹ * toFullBlockMat (normalizedBlock H F) * R⁻¹ =
      toFullBlockMat H := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change R⁻¹ * (R * toFullBlockMat H * R) * R⁻¹ = _
    calc
      _ = (R⁻¹ * R) * toFullBlockMat H * (R * R⁻¹) := by simp only [mul_assoc]
      _ = _ := by rw [hRiR, hRRi, one_mul, mul_one]
  rw [hc, hc] at hi
  exact (fullBlock_le_iff hA hB).1 hi

private theorem bridge_matrix_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosSemidef) : H ≤ H.trace • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply le_algebraMap_of_spectrum_le (ha := hH.isHermitian)
  intro x hx
  obtain ⟨i, rfl⟩ := hH.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [hH.isHermitian.trace_eq_sum_eigenvalues]
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using
    Finset.single_le_sum (fun i _ => hH.eigenvalues_nonneg i) (Finset.mem_univ i)

/-- A positive increment is bounded by the trace of its normalization, times
the normalizer. This is the full matrix increment used in the boundary sum. -/
theorem bridge_increment_trace_bound {d : ℕ} (H F : BlockMat d)
    (hH : (toFullBlockMat H).PosSemidef) (hF : (toFullBlockMat F).PosDef) :
    0 ≤ blockTrace (normalizedBlock H F) ∧
      BlockMatLoewnerLE H (blockScale (blockTrace (normalizedBlock H F)) F) := by
  let R := matSqrt (toFullBlockMat F)⁻¹
  have hR := matSqrt_inv_posDef_full hF
  have hN : (toFullBlockMat (normalizedBlock H F)).PosSemidef := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, R, hR.isHermitian.eq] using
      hH.conjTranspose_mul_mul_same R
  refine ⟨hN.trace_nonneg, ?_⟩
  have ht := bridge_matrix_le_trace hN
  have hscale (c : ℝ) : toFullBlockMat (blockScale c F) = c • toFullBlockMat F := by
    ext (i | i) (j | j) <;> rfl
  have hnscale (c : ℝ) : toFullBlockMat (normalizedBlock (blockScale c F) F) = c • 1 := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, hscale, Matrix.mul_smul, Matrix.smul_mul,
      matSqrt_inv_conj hF]
  apply bridge_unnormalize_order hH.isHermitian
    (by rw [hscale]; simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hF.isHermitian.eq]) hF
  apply (fullBlock_le_iff hN.isHermitian _).1
  · simpa only [hnscale, blockTrace] using ht
  · rw [hnscale]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]

private theorem bridge_normalized_sub_trace {d : ℕ} (A B F : BlockMat d) :
    blockTrace (blockSub (normalizedBlock A F) (normalizedBlock B F)) =
      blockTrace (normalizedBlock (blockSub A B) F) := by
  simp only [blockTrace, bridge_full_sub, normalizedBlock, toFullBlockMat_ofFullBlockMat,
    mul_sub, sub_mul]

private theorem bridge_quadratic_sub {d : ℕ} (A B : BlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (blockSub A B) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) -
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul B v) := by
  have h := blockVecDot_blockMatVecMul_ofFullBlockMat_sub A B v
  change blockVecDot v (blockMatVecMul (blockSub A B) v) = _ at h
  rw [h]
  ring

private theorem bridge_boundary_coefficient (J m L j : ℤ) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∑ r ∈ Finset.Icc J (min (m - L) (j - 1)), (3 : ℝ) ^ ((r : ℝ) - m)) ≤
      (3 / 2 : ℝ) * (3 : ℝ) ^ (-(1 - a) * L) * (3 : ℝ) ^ (-a * ((m : ℝ) - j)) := by
  have hm : ((min (m - L) (j - 1) : ℤ) : ℝ) - m ≤
      -max (L : ℝ) ((m : ℝ) - j) := by
    exact_mod_cast (show min (m - L) (j - 1) - m ≤ -max L (m - j) by omega)
  calc
    _ ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (((min (m - L) (j - 1) : ℤ) : ℝ) - m) :=
      bridge_geometric_interval J _ m
    _ ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (-max (L : ℝ) ((m : ℝ) - j)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hm) (by norm_num)
    _ ≤ (3 / 2 : ℝ) * ((3 : ℝ) ^ (-(1 - a) * L) * (3 : ℝ) ^ (-a * ((m : ℝ) - j))) :=
      mul_le_mul_of_nonneg_left (bridge_boundary_weight_split ha) (by norm_num)
    _ = _ := by ring

private theorem bridge_boundary_family {d : ℕ} (A : ℤ → BlockMat d)
    (hpos : ∀ r, (toFullBlockMat (A r)).PosDef) (J m L : ℤ) (hL : 0 ≤ L)
    (horder : ∀ j ∈ Set.Icc (J + 1) m, BlockMatLoewnerLE (A j) (A (j - 1)))
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    BlockMatLoewnerLE
      (ofFullBlockMat (∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m) • toFullBlockMat (A r)))
      (blockScale ((3 / 2 : ℝ) * ((3 : ℝ) ^ (-(L : ℝ)) + (3 : ℝ) ^ (-(1 - a) * L) *
        ∑ j ∈ Finset.Icc (J + 1) m, (3 : ℝ) ^ (-a * ((m : ℝ) - j)) *
          blockTrace (blockSub (normalizedBlock (A (j - 1)) (A m)) (normalizedBlock (A j) (A m)))))
        (A m)) := by
  classical
  let D := fun j => blockTrace
    (blockSub (normalizedBlock (A (j - 1)) (A m)) (normalizedBlock (A j) (A m)))
  have hi (j : ℤ) (hj : j ∈ Finset.Icc (J + 1) m) :
      0 ≤ D j ∧ BlockMatLoewnerLE (blockSub (A (j - 1)) (A j)) (blockScale (D j) (A m)) := by
    have hdiff : (toFullBlockMat (blockSub (A (j - 1)) (A j))).PosSemidef := by
      rw [bridge_full_sub]
      exact Matrix.le_iff.mp ((fullBlock_le_iff (hpos j).isHermitian (hpos (j - 1)).isHermitian).2
        (horder j (Finset.mem_Icc.mp hj)))
    simpa only [D, bridge_normalized_sub_trace] using
      bridge_increment_trace_bound (blockSub (A (j - 1)) (A j)) (A m) hdiff (hpos m)
  intro v
  let f := fun r => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A r) v)
  have hf0 : 0 ≤ f m := by
    apply mul_nonneg (by norm_num)
    simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, star_trivial] using
      (hpos m).posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec v)
  have hinc (j : ℤ) (hj : j ∈ Finset.Icc (J + 1) m) : f (j - 1) - f j ≤ D j * f m := by
    have h := (hi j hj).2 v
    rwa [bridge_quadratic_sub, Source.quadratic_blockScale] at h
  have hpoint (r : ℤ) (hr : r ∈ Finset.Icc J (m - L)) :
      f r ≤ (1 + ∑ j ∈ Finset.Icc (r + 1) m, D j) * f m := by
    have hr' := Finset.mem_Icc.mp hr
    rw [bridge_telescope f (by omega : r ≤ m), add_mul, one_mul, Finset.sum_mul]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact hinc j (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩)
  have hgeom : (∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m)) ≤
      (3 / 2 : ℝ) * (3 : ℝ) ^ (-(L : ℝ)) := by
    convert bridge_geometric_interval J (m - L) m using 1
    congr 2
    push_cast
    ring
  have hcoeff :
      (∑ j ∈ Finset.Icc (J + 1) m,
        (∑ r ∈ Finset.Icc J (min (m - L) (j - 1)), (3 : ℝ) ^ ((r : ℝ) - m)) * D j) ≤
      ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(1 - a) * L)) *
        ∑ j ∈ Finset.Icc (J + 1) m, (3 : ℝ) ^ (-a * ((m : ℝ) - j)) * D j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (bridge_boundary_coefficient J m L j a ha) (hi j hj).1
  rw [bridge_quadratic_sum, Source.quadratic_blockScale]
  have hscale (r : ℤ) : (1 / 2 : ℝ) * blockVecDot v
      (blockMatVecMul (ofFullBlockMat ((3 : ℝ) ^ ((r : ℝ) - m) • toFullBlockMat (A r))) v) =
      (3 : ℝ) ^ ((r : ℝ) - m) * f r := Source.quadratic_blockScale _ _ _
  simp_rw [hscale]
  change _ ≤ ((3 / 2 : ℝ) * ((3 : ℝ) ^ (-(L : ℝ)) + (3 : ℝ) ^ (-(1 - a) * L) *
    ∑ j ∈ Finset.Icc (J + 1) m, (3 : ℝ) ^ (-a * ((m : ℝ) - j)) * D j)) * f m
  calc
    _ ≤ ∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m) *
        ((1 + ∑ j ∈ Finset.Icc (r + 1) m, D j) * f m) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hpoint r hr) (by positivity))
    _ = ((∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m)) +
        ∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m) *
          ∑ j ∈ Finset.Icc (r + 1) m, D j) * f m := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ((∑ r ∈ Finset.Icc J (m - L), (3 : ℝ) ^ ((r : ℝ) - m)) +
        ∑ j ∈ Finset.Icc (J + 1) m,
          (∑ r ∈ Finset.Icc J (min (m - L) (j - 1)), (3 : ℝ) ^ ((r : ℝ) - m)) * D j) * f m := by
      rw [bridge_triangular_sum]
    _ ≤ ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(L : ℝ)) +
        ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(1 - a) * L)) *
          ∑ j ∈ Finset.Icc (J + 1) m, (3 : ℝ) ^ (-a * ((m : ℝ) - j)) * D j) * f m :=
      mul_le_mul_of_nonneg_right (add_le_add hgeom hcoeff) hf0
    _ = _ := by ring

/-- `e.bridge.boundary.sum`, with an explicit universal geometric constant.
This holds also for an empty generation interval and for `L=0`. -/
theorem bridge_boundary_sum (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (j : ℤ) (L : ℕ) :
    BlockMatLoewnerLE
      (ofFullBlockMat (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ)),
        (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) r)))
      (blockScale ((3 / 2 : ℝ) * ((3 : ℝ) ^ (-(L : ℝ)) +
        (3 : ℝ) ^ (-(1 - (1 - γ) / 8) * (L : ℝ)) * determinantDrift P γ (explicitRoundedGrid jStar m) jStar j))
        (adaptedMean P (explicitRoundedGrid jStar m) j)) := by
  have h := bridge_boundary_family (fun r => adaptedMean P (explicitRoundedGrid jStar m) r)
    (fun r => adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r)
    jStar j L (by positivity)
    (fun r hr => adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj m hm
      (r - 1) r (by have := hr.1; omega) (by omega))
    ((1 - γ) / 8) ⟨by linarith only [hγ.2], by linarith only [hγ.1]⟩
  simpa only [determinantDrift, relMean, Int.cast_natCast] using h

/-- The actual determinant drift is nonnegative; positivity of its normalized
increments is proved before reading the real sum. Empty ranges need no exception. -/
theorem bridge_determinantDrift_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (n : ℤ) :
    0 ≤ determinantDrift P γ (explicitRoundedGrid jStar m) jStar n := by
  let A := fun r => adaptedMean P (explicitRoundedGrid jStar m) r
  have hp := fun r => adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r
  unfold determinantDrift
  apply Finset.sum_nonneg
  intro j hjn
  have hh := Finset.mem_Icc.mp hjn
  have ho := adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj m hm
    (j - 1) j (by omega) (by omega)
  have hdiff : (toFullBlockMat (blockSub (A (j - 1)) (A j))).PosSemidef := by
    rw [bridge_full_sub]
    exact Matrix.le_iff.mp ((fullBlock_le_iff (hp j).isHermitian (hp (j - 1)).isHermitian).2 ho)
  apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
  simpa only [relMean, bridge_normalized_sub_trace] using
    (bridge_increment_trace_bound (blockSub (A (j - 1)) (A j)) (A n) hdiff (hp n)).1

private theorem bridge_exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.abs_exp_sub_one_le (by rwa [abs_of_nonneg hx0] : |x| ≤ 1)
  rw [abs_of_nonneg hx0] at h
  exact (le_abs_self _).trans h

/-- The printed drift advance is applied at both lengths, with the intermediate
loss controlled using nonnegative loss on `[n+L,n+2L]`. All constants are numerical. -/
theorem bridge_drift_advance_pair (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (n : ℤ) (hn : (jStar : ℤ) ≤ n) (L : ℕ) (hL : 1 ≤ L)
    (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hD : determinantDrift P γ (explicitRoundedGrid jStar m) jStar n ≤ ε)
    (hΔ : detIncrement P (explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤ ε) :
    let Δ := detIncrement P (explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ))
    let δ := Real.exp ((d : ℝ)⁻¹ * Δ) - 1
    δ ∈ Set.Icc (0 : ℝ) 1 ∧ δ ≤ 2 * ε ∧ (1 + δ) ^ d = Real.exp Δ ∧
      Real.exp Δ - 1 ≤ 2 * ε ∧
      determinantDrift P γ (explicitRoundedGrid jStar m) jStar (n + (L : ℤ)) +
        determinantDrift P γ (explicitRoundedGrid jStar m) jStar (n + 2 * (L : ℤ)) ≤ 10 * ε := by
  intro Δ δ
  let q := explicitRoundedGrid jStar m
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith only [hdR]
  have hΔ0 : 0 ≤ Δ := logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm
    n (n + 2 * (L : ℤ)) hn (by omega)
  let x := (d : ℝ)⁻¹ * Δ
  have hx0 : 0 ≤ x := mul_nonneg (inv_nonneg.mpr hd0.le) hΔ0
  have hxhalf : x ≤ 1 / 2 := by
    calc
      _ = Δ / (d : ℝ) := by dsimp [x]; ring
      _ ≤ 1 / (d : ℝ) := div_le_div_of_nonneg_right (hΔ.trans hε.2) hd0.le
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hdR
  have hxε : x ≤ ε := by
    calc
      _ = Δ / (d : ℝ) := by dsimp [x]; ring
      _ ≤ Δ := div_le_self hΔ0 (by linarith only [hdR])
      _ ≤ ε := hΔ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx0)
  have hδx : δ ≤ 2 * x := bridge_exp_sub_one_le_two_mul hx0 (by linarith only [hxhalf])
  have hδ1 : δ ≤ 1 := by linarith only [hδx, hxhalf]
  have hδε : δ ≤ 2 * ε := by linarith only [hδx, hxε]
  have hpower : (1 + δ) ^ d = Real.exp Δ := by
    rw [show 1 + δ = Real.exp x by dsimp [δ, x]; ring, ← Real.exp_nat_mul]
    congr 1
    dsimp only [x]
    rw [← mul_assoc, mul_inv_cancel₀ hd0.ne', one_mul]
  have hExp : Real.exp Δ - 1 ≤ 2 * ε :=
    (bridge_exp_sub_one_le_two_mul hΔ0 (hΔ.trans hε.2)).trans (by linarith only [hΔ])
  have hDn0 := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm n
  have hadv (s : ℤ) (hs : 1 ≤ s) (hsL : s ≤ 2 * (L : ℤ)) :
      determinantDrift P γ q jStar (n + s) ≤ 5 * ε := by
    have hl0 := logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm
      n (n + s) hn (by omega)
    have hr0 := logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm
      (n + s) (n + 2 * (L : ℤ)) (by omega) (by omega)
    have hle : detIncrement P q n (n + s) ≤ ε := by
      have ht := logDetLoss_add P q n (n + s) (n + 2 * (L : ℤ))
      linarith only [ht, hr0, hΔ]
    have he : Real.exp (detIncrement P q n (n + s)) - 1 ≤ 2 * ε :=
      (bridge_exp_sub_one_le_two_mul hl0 (hle.trans hε.2)).trans (by linarith only [hle])
    have he3 : Real.exp (detIncrement P q n (n + s)) ≤ 3 := by linarith only [he, hε.2]
    have hw : (3 : ℝ) ^ (-((1 - γ) / 8) * (s : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg (by linarith only [hγ.2]) (by norm_num)))
        (by exact_mod_cast (show 0 ≤ s by omega))
    have hb := determinantDrift_advance_of_posDef_antitone P γ hγ.2.le q jStar n s hn hs
      (fun r _ => adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r)
      (fun r hr => adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj m hm
        (r - 1) r (by have := hr.1; omega) (by omega))
    have hmul : (3 : ℝ) ^ (-((1 - γ) / 8) * (s : ℝ)) *
        Real.exp (detIncrement P q n (n + s)) * determinantDrift P γ q jStar n ≤ 3 * ε := by
      calc
        _ ≤ Real.exp (detIncrement P q n (n + s)) * determinantDrift P γ q jStar n := by
          rw [mul_assoc]
          exact mul_le_of_le_one_left (mul_nonneg (Real.exp_pos _).le hDn0) hw
        _ ≤ 3 * determinantDrift P γ q jStar n := mul_le_mul_of_nonneg_right he3 hDn0
        _ ≤ _ := mul_le_mul_of_nonneg_left hD (by norm_num)
    linarith only [hb, hmul, he]
  refine ⟨⟨hδ0, hδ1⟩, hδε, hpower, hExp, ?_⟩
  have h₁ := hadv L (by exact_mod_cast hL) (by omega)
  have h₂ := hadv (2 * (L : ℤ)) (by omega) le_rfl
  linarith only [h₁, h₂]

/-- The three means in the old grid share the terminal normalizer. The upper
factor is the exponential of the unscaled log-determinant loss. -/
theorem bridge_mean_sandwich (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (n : ℤ) (hn : (jStar : ℤ) ≤ n) (L : ℕ) :
    let q := explicitRoundedGrid jStar m
    let F := adaptedMean P q (n + 2 * (L : ℤ))
    BlockMatLoewnerLE F (adaptedMean P q (n + (L : ℤ))) ∧
      BlockMatLoewnerLE (adaptedMean P q (n + (L : ℤ))) (adaptedMean P q n) ∧
      BlockMatLoewnerLE (adaptedMean P q n)
        (blockScale (Real.exp (detIncrement P q n (n + 2 * (L : ℤ)))) F) := by
  intro q F
  have hp := fun r => adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r
  have ho := fun j k hjk hkl => adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj
    m hm j k hjk hkl
  refine ⟨ho _ _ (by omega) (by omega), ho _ _ hn (by omega), ?_⟩
  let A := adaptedMean P q n
  let c := Real.exp (detIncrement P q n (n + 2 * (L : ℤ)))
  have hF : (toFullBlockMat F).PosDef := hp _
  have hA : (toFullBlockMat A).PosDef := hp _
  have hR := matSqrt_inv_posDef_full hF
  have hN : (toFullBlockMat (normalizedBlock A F)).PosSemidef := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hR.isHermitian.eq] using
      hA.posSemidef.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat F)⁻¹)
  have hI : (1 : FullBlockMat d) ≤ toFullBlockMat (normalizedBlock A F) := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat] using
      Recurrence.one_le_normalize hF ((fullBlock_le_iff hF.isHermitian hA.isHermitian).2 (ho _ _ hn (by omega)))
  have hb := matrix_le_det_smul_one hN.isHermitian hI
  have hdet := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm
    n (n + 2 * (L : ℤ)) hn (by omega)).2.2.1
  change (toFullBlockMat (normalizedBlock A F)).det = c at hdet
  rw [hdet] at hb
  have hscale : toFullBlockMat (blockScale c F) = c • toFullBlockMat F := by
    ext (i | i) (j | j) <;> rfl
  have hnscale : toFullBlockMat (normalizedBlock (blockScale c F) F) = c • 1 := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, hscale, Matrix.mul_smul, Matrix.smul_mul,
      matSqrt_inv_conj hF]
  change BlockMatLoewnerLE A (blockScale c F)
  apply bridge_unnormalize_order hA.isHermitian
    (by rw [hscale]; simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul,
      star_trivial, hF.isHermitian.eq]) hF
  apply (fullBlock_le_iff hN.isHermitian _).1
  · simpa only [hnscale] using hb
  · rw [hnscale]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]

private theorem bridge_quadratic_add {d : ℕ} (A B : BlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul
      (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) +
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul B v) := by
  conv_rhs => rw [← ofFullBlockMat_toFullBlockMat A, ← ofFullBlockMat_toFullBlockMat B]
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

private theorem bridge_scalar_errors (u v K ε w T x a h b c C : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hw : 0 ≤ w) (hT : 0 ≤ T) (hx : 0 ≤ x)
    (hCεu : 2 + 45 * u * K ≤ C) (hCεv : 45 * v * K ≤ C)
    (hCwu : 5 * u ≤ C) (hCwv : 5 * v ≤ C) (hCu : u ≤ C) (hCv : v ≤ C)
    (ha : a ≤ (1 + 2 * ε) * x)
    (hb : b ≤ (9 / 2 : ℝ) * (w + 10 * ε) * x)
    (hc : c ≤ (9 / 2 : ℝ) * (w + 10 * ε) * x)
    (hupp : h - a ≤ u * K * b + u * T * x)
    (hlow : x - h ≤ v * K * c + v * T * x) :
    h - x ≤ (C * ε + C * K * w + C * T) * x ∧
      x - h ≤ (C * ε + C * K * w + C * T) * x := by
  have hbu := mul_le_mul_of_nonneg_left hb (mul_nonneg hu hK)
  have hcv := mul_le_mul_of_nonneg_left hc (mul_nonneg hv hK)
  have heu := mul_le_mul_of_nonneg_right hCεu hε
  have hev := mul_le_mul_of_nonneg_right hCεv hε
  have hwu : (9 / 2 : ℝ) * u * K * w ≤ C * K * w := by
    apply mul_le_mul_of_nonneg_right _ hw
    exact mul_le_mul_of_nonneg_right (by linarith only [hCwu, hu]) hK
  have hwv : (9 / 2 : ℝ) * v * K * w ≤ C * K * w := by
    apply mul_le_mul_of_nonneg_right _ hw
    exact mul_le_mul_of_nonneg_right (by linarith only [hCwv, hv]) hK
  have htu := mul_le_mul_of_nonneg_right hCu hT
  have htv := mul_le_mul_of_nonneg_right hCv hT
  have heux := mul_le_mul_of_nonneg_right (add_le_add (add_le_add heu hwu) htu) hx
  have hevx := mul_le_mul_of_nonneg_right (add_le_add (add_le_add hev hwv) htv) hx
  constructor <;> nlinarith only [ha, hbu, hcv, hupp, hlow, heux, hevx]

/-- Both actual Whitney errors relative to the terminal old-grid mean. The
boundary decay retains `1-(1-γ)/8`; the source tail is enlarged only after the
three-generation sandwich and the two drift advances have been established. -/
theorem bridge_endpoint_errors (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
            gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
            ∀ (n : ℤ) (L : ℕ), (jStar : ℤ) ≤ n → 1 ≤ L →
              adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                  adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                centeredCube d (2 * (jStar : ℤ)) →
              ∀ ε : ℝ, ε ∈ Set.Icc (0 : ℝ) 1 →
                determinantDrift P γ (explicitRoundedGrid jStar m) jStar n ≤ ε →
                detIncrement P (explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤ ε →
                let F := adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))
                let H := adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))
                let T := (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) +
                  Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) * (1 + (n : ℝ) + L - jStar) *
                    (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar))
                BlockMatLoewnerLE (blockSub H F)
                    (blockScale (C * ε + C * K₀ * (3 : ℝ) ^ (-(L : ℝ)) + C * T) F) ∧
                  BlockMatLoewnerLE (blockSub F H)
                    (blockScale (C * ε + C * K₀ * (3 : ℝ) ^ (-(L : ℝ)) + C * T) F) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨CsU, Cu, hCsU, hCu, hupper⟩ := bridge_upper_comparison d hd γ hγ K₀ hK₀
  obtain ⟨CsV, Cv, hCsV, hCv, hlower⟩ := bridge_lower_comparison d hd γ hγ K₀ hK₀
  let C := 2 + 45 * (Cu + Cv) * K₀ + 5 * (Cu + Cv) + (Cu + Cv)
  have hK0 : 0 ≤ K₀ := by linarith only [hK₀]
  have hC : 0 < C := by dsimp [C]; positivity
  have hCεu : 2 + 45 * Cu * K₀ ≤ C := by
    dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg hCv.le hK0]
  have hCεv : 45 * Cv * K₀ ≤ C := by
    dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg hCu.le hK0]
  have hCwu : 5 * Cu ≤ C := by dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg (add_nonneg hCu.le hCv.le) hK0]
  have hCwv : 5 * Cv ≤ C := by dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg (add_nonneg hCu.le hCv.le) hK0]
  have hCuC : Cu ≤ C := by dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg (add_nonneg hCu.le hCv.le) hK0]
  have hCvC : Cv ≤ C := by dsimp [C]; nlinarith only [hCu, hCv, mul_nonneg (add_nonneg hCu.le hCv.le) hK0]
  refine ⟨max CsU CsV, C, hCsU.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio n L hn hL
    hcontain ε hε hD hΔ F H T
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsrcU := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left CsU CsV) hlog)).trans hsrc
  have hsrcV := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right CsU CsV) hlog)).trans hsrc
  have hu := hupper P E Ψ K S hstat hdag jStar hj hsrcU m mPlus hm hmPlus hratio n L hn hL hcontain
  have hv := hlower P E Ψ K S hstat hdag jStar hj hsrcV m mPlus hm hmPlus hratio n L hn hL hcontain
  let q := explicitRoundedGrid jStar m
  let A := fun r => adaptedMean P q r
  let w := (3 : ℝ) ^ (-(L : ℝ))
  let W := 1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2
  have hW : 0 ≤ W := by dsimp [W]; have := one_le_aspectRatio_of_coarseEllipticityDagger hdag; positivity
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hnR : (jStar : ℝ) ≤ n := by exact_mod_cast hn
  have hT : 0 ≤ T := mul_nonneg (mul_nonneg hW (by linarith only [hnR, hLn]))
    (Real.rpow_nonneg (by norm_num) _)
  have htail (s : ℝ) (hs : 0 ≤ s) :
      W * (3 : ℝ) ^ (-(1 - γ) * ((n : ℝ) + s - jStar)) ≤ T := by
    have he : -(1 - γ) * ((n : ℝ) + s - jStar) ≤ -((1 - γ) / 8) * ((n : ℝ) - jStar) := by
      nlinarith only [hγ.2, hnR, hs, mul_nonneg (sub_nonneg.mpr hnR) hs]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
    calc
      _ ≤ W * (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar)) := mul_le_mul_of_nonneg_left hp hW
      _ ≤ T := by
        dsimp [T]
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right hW (by linarith only [hnR, hLn]))
          (Real.rpow_nonneg (by norm_num) _)
  have hadv := bridge_drift_advance_pair d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm
    n hn L hL ε hε hD hΔ
  have hExp := hadv.2.2.2.1
  have hDrifts := hadv.2.2.2.2
  have hmid0 := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + (L : ℤ))
  have hend0 := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hmid : determinantDrift P γ q jStar (n + (L : ℤ)) ≤ 10 * ε := by linarith only [hDrifts, hend0]
  have hend : determinantDrift P γ q jStar (n + 2 * (L : ℤ)) ≤ 10 * ε := by linarith only [hDrifts, hmid0]
  have hmeans := bridge_mean_sandwich d hd P γ E Ψ K S hstat hdag jStar hj m hm n hn L
  have hdecay : (3 : ℝ) ^ (-(1 - (1 - γ) / 8) * (L : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    apply mul_nonpos_of_nonpos_of_nonneg _ hLn
    linarith only [hγ.1]
  have hboundary (j : ℤ) (hDj0 : 0 ≤ determinantDrift P γ q jStar j)
      (hDj : determinantDrift P γ q jStar j ≤ 10 * ε)
      (hjF : BlockMatLoewnerLE (A j) (blockScale 3 F)) :
      BlockMatLoewnerLE (ofFullBlockMat
        (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ)), (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (A r)))
        (blockScale ((9 / 2 : ℝ) * (w + 10 * ε)) F) := by
    have hb := bridge_boundary_sum d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm j L
    intro z
    have hz := hb z
    have hf := hjF z
    simp only [Source.quadratic_blockScale] at hz hf ⊢
    have hcoef : (3 / 2 : ℝ) * (w + (3 : ℝ) ^ (-(1 - (1 - γ) / 8) * (L : ℝ)) *
        determinantDrift P γ q jStar j) ≤ (3 / 2 : ℝ) * (w + 10 * ε) := by
      have ht := (mul_le_of_le_one_left hDj0 hdecay).trans hDj
      linarith only [ht]
    have hAj0 : 0 ≤ (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (A j) z) := by
      apply mul_nonneg (by norm_num)
      simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, star_trivial] using
        (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm j).posSemidef.dotProduct_mulVec_nonneg
          (toFullBlockVec z)
    have h₁ := mul_le_mul_of_nonneg_right hcoef hAj0
    have hbc : 0 ≤ (3 / 2 : ℝ) * (w + 10 * ε) :=
      mul_nonneg (by norm_num) (add_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) hε.1))
    have h₂ := mul_le_mul_of_nonneg_left hf hbc
    linarith only [hz, h₁, h₂]
  have hFpos := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hF0 (z : BlockVec d) : 0 ≤ (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul F z) := by
    apply mul_nonneg (by norm_num)
    simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, star_trivial] using
      hFpos.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec z)
  have hAF : BlockMatLoewnerLE (A n) (blockScale (1 + 2 * ε) F) := by
    intro z
    have hh := hmeans.2.2 z
    simp only [Source.quadratic_blockScale] at hh ⊢
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hExp]) (hF0 z))
  have hmidF : BlockMatLoewnerLE (A (n + (L : ℤ))) (blockScale 3 F) := by
    intro z
    have hh := hmeans.2.1 z
    have ha := hAF z
    simp only [Source.quadratic_blockScale] at ha ⊢
    exact hh.trans (ha.trans (mul_le_mul_of_nonneg_right (by linarith only [hε.2]) (hF0 z)))
  have hendF : BlockMatLoewnerLE (A (n + 2 * (L : ℤ))) (blockScale 3 F) := by
    intro z
    simp only [Source.quadratic_blockScale]
    change (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul F z) ≤ 3 * _
    linarith only [hF0 z]
  have hbU := hboundary (n + (L : ℤ)) hmid0 hmid hmidF
  have hbV := hboundary (n + 2 * (L : ℤ)) hend0 hend hendF
  have heU : n + (L : ℤ) - (L : ℤ) = n := by omega
  have heV : n + 2 * (L : ℤ) - (L : ℤ) = n + (L : ℤ) := by omega
  simp only [heU, heV, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hbU hbV
  have hweightU (r : ℤ) : (r : ℝ) - ((n : ℝ) + L) = (r : ℝ) - n - L := by ring
  have hweightV (r : ℤ) : (r : ℝ) - ((n : ℝ) + 2 * L) = (r : ℝ) - n - 2 * L := by ring
  simp only [hweightU] at hbU
  simp only [hweightV] at hbV
  have hboth (z : BlockVec d) := by
    have hu' := hu z
    have hv' := hv z
    have hbU' := hbU z
    have hbV' := hbV z
    have hAF' := hAF z
    simp only [bridge_quadratic_sub, bridge_quadratic_add, Source.quadratic_blockScale] at hu' hv' hbU' hbV' hAF'
    have htu := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (htail L hLn) hCu.le) (hF0 z)
    have htv := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (htail (2 * L) (by positivity)) hCv.le) (hF0 z)
    dsimp only [W] at htu htv
    simp only [← mul_assoc] at htu htv
    exact bridge_scalar_errors Cu Cv K₀ ε w T _ _
      ((1 / 2 : ℝ) * blockVecDot z (blockMatVecMul H z)) _ _ C hCu.le hCv.le hK0 hε.1
      (Real.rpow_nonneg (by norm_num) _) hT (hF0 z) hCεu hCεv hCwu hCwv hCuC hCvC hAF' hbU' hbV'
      (by linarith only [hu', htu]) (by linarith only [hv', htv])
  constructor
  · intro z
    simpa only [bridge_quadratic_sub, Source.quadratic_blockScale] using (hboth z).1
  · intro z
    simpa only [bridge_quadratic_sub, Source.quadratic_blockScale] using (hboth z).2

end
end HCPolySupport.HighContrast.Annealed
