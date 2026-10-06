/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportProfile

/-!
# High-contrast homogenization: Entry.Annealed.TransportDriftAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Abel summation and the drift-weight algebra of the two-grid transport

The finite summation-by-parts identity on integer intervals, the exact base-three difference of
the exponential drift weights, and the resulting total-mass-one identity those weights satisfy.
The same algebra is applied to the actual determinant drift and the actual normalized means,
separating the terminal boundary trace from the interior geometric convolution of trace
excesses, and is quantified into the error, sum, bulk, boundary, source and scalar-assembly
bounds that supply the drift term of `p.two.grid.transport`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockScale blockSub blockTrace
  normalizedBlock)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Finite summation by parts, including the one-increment interval. -/
theorem transport_abel_identity (w f : ℤ → ℝ) (J t : ℤ) (hJt : J < t) :
    (∑ r ∈ Finset.Icc (J + 1) t, w r * (f (r - 1) - f r)) =
      w (J + 1) * f J + ∑ j ∈ Finset.Icc (J + 1) (t - 1), (w (j + 1) - w j) * f j - w t * f t := by
  classical
  induction t, (show J + 1 ≤ t by omega) using Int.leInduction with
  | base => simp only [Finset.Icc_self, Finset.sum_singleton, add_sub_cancel_right,
      Finset.Icc_eq_empty_of_lt (show J < J + 1 by omega), Finset.sum_empty]; ring
  | succ t ht ih =>
    have htop : Finset.Icc (J + 1) (t + 1) = insert (t + 1) (Finset.Icc (J + 1) t) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hmid : Finset.Icc (J + 1) ((t + 1) - 1) = insert t (Finset.Icc (J + 1) (t - 1)) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [htop, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hmid,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_sub_cancel_right, ih (by omega)]
    ring

/-- The printed drift weight difference, with its fixed one-generation shift. -/
theorem transport_abel_weight (a : ℝ) (t j : ℤ) :
    (3 : ℝ) ^ (-a * ((t : ℝ) - ((j : ℝ) + 1))) - (3 : ℝ) ^ (-a * ((t : ℝ) - j)) =
      (1 - (3 : ℝ) ^ (-a)) * (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) := by
  have he : -a * ((t : ℝ) - j) = -a + -a * ((t : ℝ) - j - 1) := by ring
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  rw [show -a * ((t : ℝ) - (j + 1)) = -a * ((t : ℝ) - j - 1) by ring]
  ring

/-- The Abel coefficients have total mass one, even when the interior sum is empty. -/
theorem transport_abel_mass (a : ℝ) (J t : ℤ) (hJt : J < t) :
    (3 : ℝ) ^ (-a * ((t : ℝ) - J - 1)) + (1 - (3 : ℝ) ^ (-a)) *
      ∑ j ∈ Finset.Icc (J + 1) (t - 1), (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) = 1 := by
  have h := transport_abel_identity (fun r => (3 : ℝ) ^ (-a * ((t : ℝ) - r))) (fun _ => 1) J t hJt
  simp only [sub_self, mul_zero, Finset.sum_const_zero, mul_one, mul_zero, Real.rpow_zero] at h
  simp only [transport_abel_weight, ← Finset.mul_sum, Int.cast_add, Int.cast_one] at h
  rw [show -a * ((t : ℝ) - ((J : ℝ) + 1)) = -a * ((t : ℝ) - J - 1) by ring] at h
  linarith only [h]

/-- The trace of a block difference is the difference of its traces. -/
theorem transport_trace_sub {d : ℕ} (A B : BlockMat d) :
    blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
  rw [blockTrace, toFullBlockMat_blockSub_annealed, Matrix.trace_sub]; rfl

/-- Abel summation for the actual determinant drift and actual normalized means. -/
theorem transport_determinantDrift_abel {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d)
    (jStar : ℕ) (t : ℤ) (hJt : (jStar : ℤ) < t) (ht : (toFullBlockMat (adaptedMean P q t)).PosDef) :
    determinantDrift P γ q jStar t =
      (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - jStar - 1)) *
        blockTrace (blockSub (relMean P q jStar t) (Book.Ch02.blockIdentity d)) +
      (1 - (3 : ℝ) ^ (-((1 - γ) / 8))) *
        ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) (t - 1),
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - j - 1)) *
            blockTrace (blockSub (relMean P q j t) (Book.Ch02.blockIdentity d)) := by
  let f := fun j => blockTrace (blockSub (relMean P q j t) (Book.Ch02.blockIdentity d))
  have hf : f t = 0 := by simp only [f, relMean, normalizedBlock_self_of_posDef _ ht, transport_trace_sub, sub_self]
  have hdiff (j : ℤ) : blockTrace (blockSub (relMean P q (j - 1) t) (relMean P q j t)) = f (j - 1) - f j := by
    simp only [f, transport_trace_sub]; ring
  have h := transport_abel_identity (fun r => (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - r))) f jStar t hJt
  simp only [transport_abel_weight, mul_assoc, ← Finset.mul_sum, hf, mul_zero, sub_zero, Int.cast_add, Int.cast_one, Int.cast_natCast] at h
  rw [show -((1 - γ) / 8) * ((t : ℝ) - ((jStar : ℝ) + 1)) = -((1 - γ) / 8) * ((t : ℝ) - jStar - 1) by ring] at h
  simpa only [determinantDrift, hdiff] using h

/-- A mass-one nonnegative Abel combination accumulates a uniform error once. -/
theorem transport_abel_error (a : ℝ) (ha : 0 ≤ a) (J t : ℤ) (hJt : J < t)
    (f g : ℤ → ℝ) (D : ℝ) (hfg : ∀ j ∈ Finset.Icc J (t - 1), f j ≤ g j + D) :
    (3 : ℝ) ^ (-a * ((t : ℝ) - J - 1)) * f J + (1 - (3 : ℝ) ^ (-a)) *
      ∑ j ∈ Finset.Icc (J + 1) (t - 1), (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) * f j ≤
    (3 : ℝ) ^ (-a * ((t : ℝ) - J - 1)) * g J + (1 - (3 : ℝ) ^ (-a)) *
      ∑ j ∈ Finset.Icc (J + 1) (t - 1), (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) * g j + D := by
  have hc : 0 ≤ 1 - (3 : ℝ) ^ (-a) := sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [ha]))
  have hsum := Finset.sum_le_sum (s := Finset.Icc (J + 1) (t - 1)) (fun j hj => mul_le_mul_of_nonneg_left
    (hfg j (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; omega, (Finset.mem_Icc.mp hj).2⟩))
    (by positivity : 0 ≤ (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1))))
  have hh := add_le_add (mul_le_mul_of_nonneg_left (hfg J (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
    (by positivity : 0 ≤ (3 : ℝ) ^ (-a * ((t : ℝ) - J - 1)))) (mul_le_mul_of_nonneg_left hsum hc)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at hh
  have hm := congrArg (fun x : ℝ => x * D) (transport_abel_mass a J t hJt)
  nlinarith only [hh, hm]

/-- The weighted sum of all nonnegative trace excesses is controlled by its Abel expression. -/
theorem transport_abel_sum_bound (a : ℝ) (ha : 0 < a) (J m : ℤ) (hJm : J < m)
    (f : ℤ → ℝ) (hf : ∀ j ∈ Finset.Icc J (m - 1), 0 ≤ f j) (D : ℝ)
    (hD : (3 : ℝ) ^ (-a * ((m : ℝ) - J - 1)) * f J + (1 - (3 : ℝ) ^ (-a)) *
      (∑ j ∈ Finset.Icc (J + 1) (m - 1), (3 : ℝ) ^ (-a * ((m : ℝ) - j - 1)) * f j) = D) :
    (∑ j ∈ Finset.Icc J (m - 1), (3 : ℝ) ^ (-a * ((m : ℝ) - j - 1)) * f j) ≤
      (1 / (1 - (3 : ℝ) ^ (-a))) * D := by
  classical
  have hc := (transport_geometric_Icc a ha J m).1
  have he : Finset.Icc J (m - 1) = insert J (Finset.Icc (J + 1) (m - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hfJ := hf J (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc, he,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  have hq : 0 ≤ (3 : ℝ) ^ (-a) := by positivity
  have hterm : 0 ≤ (3 : ℝ) ^ (-a * ((m : ℝ) - J - 1)) * f J := mul_nonneg (by positivity) hfJ
  nlinarith only [hD, mul_nonneg hq hterm]

/-- Translating the bulk generation shifts its weight by exactly two bridge lengths. -/
theorem transport_drift_bulk_weights (a : ℝ) (J n : ℤ) (L : ℕ) (f : ℤ → ℝ)
    (hf : ∀ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1), 0 ≤ f r) :
    (∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + (L : ℤ) - 1),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) * f (j - (L : ℤ))) ≤
      (3 : ℝ) ^ (2 * a * (L : ℝ)) *
        ∑ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1),
          (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r := by
  classical
  have he : (∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + (L : ℤ) - 1),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) * f (j - (L : ℤ))) =
      (3 : ℝ) ^ (2 * a * (L : ℝ)) * ∑ r ∈ Finset.Icc J (n - 1),
        (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r := by
    rw [Finset.mul_sum]
    apply Finset.sum_bij (fun j _ => j - (L : ℤ))
    · intro j hj; have := Finset.mem_Icc.mp hj; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j _ k _ h; omega
    · intro r hr; refine ⟨r + (L : ℤ), ?_, by omega⟩
      have := Finset.mem_Icc.mp hr; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j _
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2; push_cast; ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr; have := Finset.mem_Icc.mp hr; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro r hr _; exact mul_nonneg (by positivity) (hf r hr)

/-- The boundary trace sum is a geometric convolution normalized at the old terminal scale. -/
theorem transport_drift_boundary_weights (a : ℝ) (ha : a < 1) (J n : ℤ) (L : ℕ)
    (f : ℤ → ℝ) (hf : ∀ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1), 0 ≤ f r) :
    (∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + (L : ℤ) - 1),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) *
        ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) ≤
      ((3 : ℝ) ^ (a * (L : ℝ)) / (1 - (3 : ℝ) ^ (-(1 - a)))) *
        ∑ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1),
          (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r := by
  let S := Finset.Icc (J + (L : ℤ)) (n + (L : ℤ) - 1)
  let U := Finset.Icc J (n + 2 * (L : ℤ) - 1)
  let T := fun j => Finset.Icc J (j - (L : ℤ) - 1)
  let F := fun r : ℤ => (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r
  have h := transport_geometric_convolution (1 - a) (by linarith only [ha]) S U T
    (n + (L : ℤ)) (fun j hj => by have := (Finset.mem_Icc.mp hj).2; omega)
    (fun j hj r hr => by
      have := Finset.mem_Icc.mp hj; have := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    (fun j _ r hr => by have := (Finset.mem_Icc.mp hr).2; omega)
    F (fun r hr => mul_nonneg (by positivity) (hf r hr))
  calc
    _ = (3 : ℝ) ^ (a * (L : ℝ)) *
        ∑ j ∈ S, ∑ r ∈ T j, (3 : ℝ) ^ (-(1 - a) * ((j : ℝ) - r)) * F r := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
      dsimp only [F]
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2; ring
    _ ≤ (3 : ℝ) ^ (a * (L : ℝ)) * ((1 / (1 - (3 : ℝ) ^ (-(1 - a)))) * ∑ r ∈ U, F r) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by dsimp only [U, F]; ring

/-- Trace excesses of actual normalized means are nonnegative throughout the ordered range. -/
theorem transport_drift_trace_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (r t : ℤ) (hJr : (jStar : ℤ) ≤ r) (hrt : r ≤ t) :
    0 ≤ blockTrace (blockSub (relMean P (explicitRoundedGrid jStar m) r t) (Book.Ch02.blockIdentity d)) := by
  have h := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm r t hJr hrt).1
  rw [transport_trace_sub]
  exact sub_nonneg.mpr (Source.blockTrace_le_of_order h)

/-- Linearity of the normalized trace keeps the identity contribution explicit. -/
theorem transport_normalized_trace_sum {d : ℕ} (A : ℤ → BlockMat d) (F : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (I : Finset ℤ) (b : ℤ) (w : ℤ → ℝ) (C D : ℝ) :
    blockTrace (normalizedBlock (ofFullBlockMat
      (toFullBlockMat (A b) + C • (∑ r ∈ I, w r • toFullBlockMat (A r)) + D • toFullBlockMat F)) F) =
      blockTrace (normalizedBlock (A b) F) +
        C * (∑ r ∈ I, w r * blockTrace (normalizedBlock (A r) F)) + D * (2 * (d : ℝ)) := by
  simp only [blockTrace, normalizedBlock, toFullBlockMat_ofFullBlockMat, mul_add, add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    matSqrt_inv_conj hF, Matrix.trace_one,
    BlockCoord, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul]

/-- Taking a normalized trace of the Whitney matrix bound separates excess and identity. -/
theorem transport_drift_trace_comparison {d : ℕ} (A : ℤ → BlockMat d) (H F : BlockMat d)
    (hA : ∀ r, (toFullBlockMat (A r)).PosDef) (hH : (toFullBlockMat H).PosDef)
    (hF : (toFullBlockMat F).PosDef) (I : Finset ℤ) (b : ℤ) (w : ℤ → ℝ)
    (hw : ∀ r, 0 ≤ w r) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbound : BlockMatLoewnerLE H (ofFullBlockMat
      (toFullBlockMat (A b) + C • (∑ r ∈ I, w r • toFullBlockMat (A r)) + D • toFullBlockMat F))) :
    blockTrace (blockSub (normalizedBlock H F) (Book.Ch02.blockIdentity d)) ≤
      blockTrace (blockSub (normalizedBlock (A b) F) (Book.Ch02.blockIdentity d)) +
        C * (∑ r ∈ I, w r * blockTrace (blockSub (normalizedBlock (A r) F) (Book.Ch02.blockIdentity d))) +
        (2 * (d : ℝ)) * C * (∑ r ∈ I, w r) + (2 * (d : ℝ)) * D := by
  have hsum : (∑ r ∈ I, w r • toFullBlockMat (A r)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun r _ =>
      Matrix.nonneg_iff_posSemidef.mpr ((hA r).posSemidef.smul (hw r)))
  have hB : (toFullBlockMat (ofFullBlockMat
      (toFullBlockMat (A b) + C • (∑ r ∈ I, w r • toFullBlockMat (A r)) + D • toFullBlockMat F))).IsHermitian := by
    rw [toFullBlockMat_ofFullBlockMat]
    exact (((hA b).posSemidef.add (hsum.smul hC)).add (hF.posSemidef.smul hD)).isHermitian
  have ht := Source.blockTrace_le_of_order (transport_normalized_order hH.isHermitian hB hF hbound)
  rw [transport_normalized_trace_sum A F hF I b w C D] at ht
  simp only [transport_trace_excess, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  linarith only [ht]

/-- Scalar geometric bound for the boundary identity row, including an empty row. -/
theorem transport_drift_identity_row (J j : ℤ) (L : ℕ) :
    (∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j)) ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * (3 : ℝ) ^ (-(L : ℝ)) := by
  have h := (transport_geometric_Icc 1 (by norm_num) J (j - (L : ℤ) - 1)).2
  calc
    _ = (3 : ℝ) ^ (-(L : ℝ) - 1) *
      ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ (-(1 : ℝ) * (((j - (L : ℤ) - 1 : ℤ) : ℝ) - r)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1; push_cast; ring
    _ ≤ (3 : ℝ) ^ (-(L : ℝ) - 1) * (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only []))
        (one_div_nonneg.mpr (transport_geometric_Icc 1 (by norm_num) J j).1.le)

/-- Nonnegative Abel coefficients are bounded by the corresponding full geometric sum. -/
theorem transport_abel_le_sum (a : ℝ) (J t : ℤ) (hJt : J < t) (f : ℤ → ℝ)
    (hf : ∀ j ∈ Finset.Icc J (t - 1), 0 ≤ f j) :
    (3 : ℝ) ^ (-a * ((t : ℝ) - J - 1)) * f J + (1 - (3 : ℝ) ^ (-a)) *
      (∑ j ∈ Finset.Icc (J + 1) (t - 1), (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) * f j) ≤
      ∑ j ∈ Finset.Icc J (t - 1), (3 : ℝ) ^ (-a * ((t : ℝ) - j - 1)) * f j := by
  classical
  have he : Finset.Icc J (t - 1) = insert J (Finset.Icc (J + 1) (t - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [he, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  apply add_le_add le_rfl
  apply mul_le_of_le_one_left
  · exact Finset.sum_nonneg fun j hj => mul_nonneg (by positivity)
      (hf j (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; omega, (Finset.mem_Icc.mp hj).2⟩))
  · have h : 0 ≤ (3 : ℝ) ^ (-a) := by positivity
    linarith only [h]

/-- Each early-source or late-source weight is paid by the printed source decay. -/
theorem transport_drift_source_weight (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (J n j : ℤ) (hj : J ≤ j) (L : ℕ) (hL : 1 ≤ L) :
    (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) *
      (if j < J + (L : ℤ) then 1 else (3 : ℝ) ^ (-b * ((j : ℝ) - J))) ≤
      (3 : ℝ) ^ (-a * ((n : ℝ) - J)) := by
  split_ifs with he
  · rw [mul_one]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgap : 0 ≤ (J : ℝ) + L - j - 1 := by exact_mod_cast (show 0 ≤ J + (L : ℤ) - j - 1 by omega)
    nlinarith only [mul_nonneg ha hgap]
  · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgap : 0 ≤ (j : ℝ) - J := by exact_mod_cast sub_nonneg.mpr hj
    have hlen : 0 ≤ (L : ℝ) - 1 := by exact_mod_cast (show 0 ≤ (L : ℤ) - 1 by omega)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hab) hgap, mul_nonneg ha hlen]

/-- Summing the common source weight retains the printed linear factor in the scale gap. -/
theorem transport_drift_source_weights (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (J n : ℤ) (hn : J ≤ n) (L : ℕ) (hL : 1 ≤ L) :
    (∑ j ∈ Finset.Icc J (n + (L : ℤ) - 1),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) *
        (if j < J + (L : ℤ) then 1 else (3 : ℝ) ^ (-b * ((j : ℝ) - J)))) ≤
      ((n : ℝ) + L - J) * (3 : ℝ) ^ (-a * ((n : ℝ) - J)) := by
  have hcard : ((Finset.Icc J (n + (L : ℤ) - 1)).card : ℝ) = (n : ℝ) + L - J := by
    rw [Int.card_Icc]
    have hnat := Int.toNat_of_nonneg (show 0 ≤ (n + (L : ℤ) - 1) + 1 - J by omega)
    have hcast : (((n + (L : ℤ) - 1) + 1 - J).toNat : ℝ) = (n : ℝ) + L - J := by
      have hnat' : (((n + (L : ℤ) - 1) + 1 - J).toNat : ℤ) = n + (L : ℤ) - J := by omega
      exact_mod_cast hnat'
    exact hcast
  calc
    _ ≤ ∑ _j ∈ Finset.Icc J (n + (L : ℤ) - 1), (3 : ℝ) ^ (-a * ((n : ℝ) - J)) :=
      Finset.sum_le_sum fun j hj => transport_drift_source_weight a b ha hab J n j (Finset.mem_Icc.mp hj).1 L hL
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Assemble the Abel terms after the uniform comparison and identity errors have been separated. -/
theorem transport_drift_scalar_assembly (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b)
    (J n : ℤ) (hn : J ≤ n) (L : ℕ) (hL : 1 ≤ L) (f g : ℤ → ℝ)
    (hf : ∀ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1), 0 ≤ f r)
    (A Cb Y E : ℝ) (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hY : 0 ≤ Y)
    (hpoint : ∀ j ∈ Finset.Icc J (n + (L : ℤ) - 1),
      g j ≤ A * (if j < J + (L : ℤ) then 0 else
        f (j - (L : ℤ)) + Cb * ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
        Y * (if j < J + (L : ℤ) then 1 else (3 : ℝ) ^ (-b * ((j : ℝ) - J))) + E) :
    (3 : ℝ) ^ (-a * ((n : ℝ) + L - J - 1)) * g J + (1 - (3 : ℝ) ^ (-a)) *
      (∑ j ∈ Finset.Icc (J + 1) (n + (L : ℤ) - 1), (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1)) * g j) ≤
      A * (3 : ℝ) ^ (2 * a * (L : ℝ)) * (1 + Cb / (1 - (3 : ℝ) ^ (-(1 - a)))) *
        (∑ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1), (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r) +
      Y * ((n : ℝ) + L - J) * (3 : ℝ) ^ (-a * ((n : ℝ) - J)) + E := by
  classical
  let U := Finset.Icc J (n + (L : ℤ) - 1)
  let V := Finset.Icc (J + (L : ℤ)) (n + (L : ℤ) - 1)
  let old := fun j : ℤ => if j < J + (L : ℤ) then 0 else
    f (j - (L : ℤ)) + Cb * ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r
  let src := fun j : ℤ => if j < J + (L : ℤ) then 1 else (3 : ℝ) ^ (-b * ((j : ℝ) - J))
  let w := fun j : ℤ => (3 : ℝ) ^ (-a * ((n : ℝ) + L - j - 1))
  let h := fun j => A * old j + Y * src j
  let T := ∑ r ∈ Finset.Icc J (n + 2 * (L : ℤ) - 1), (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r
  have hT : 0 ≤ T := Finset.sum_nonneg fun r hr => mul_nonneg (by positivity) (hf r hr)
  have ho0 (j : ℤ) (hj : j ∈ U) : 0 ≤ old j := by
    dsimp only [old]
    split_ifs with he
    · exact le_rfl
    · have hjj := Finset.mem_Icc.mp hj
      exact add_nonneg (hf _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (mul_nonneg hCb (Finset.sum_nonneg fun r hr => mul_nonneg (by positivity)
          (hf r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩))))
  have hs0 (j : ℤ) : 0 ≤ src j := by dsimp only [src]; split_ifs <;> positivity
  have hh0 (j : ℤ) (hj : j ∈ U) : 0 ≤ h j := add_nonneg (mul_nonneg hA (ho0 j hj)) (mul_nonneg hY (hs0 j))
  have herr := transport_abel_error a ha.le J (n + (L : ℤ)) (by omega) g h E hpoint
  have hsum := transport_abel_le_sum a J (n + (L : ℤ)) (by omega) h hh0
  simp only [Int.cast_add, Int.cast_natCast] at herr hsum
  have heOld : (∑ j ∈ U, w j * old j) =
      (∑ j ∈ V, w j * f (j - (L : ℤ))) +
        Cb * ∑ j ∈ V, w j * ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r := by
    have hVU : V ⊆ U := fun j hj => Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj).1; omega, (Finset.mem_Icc.mp hj).2⟩
    have hzero (j : ℤ) (hj : j ∈ U) (hjV : j ∉ V) : w j * old j = 0 := by
      have he : j < J + (L : ℤ) := by
        have := Finset.mem_Icc.mp hj
        simp only [V, Finset.mem_Icc] at hjV
        omega
      simp only [old, ite_eq_left he, mul_zero]
    rw [← Finset.sum_subset hVU hzero, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj
    rw [show old j = f (j - (L : ℤ)) + Cb * ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1),
      (3 : ℝ) ^ ((r : ℝ) - j) * f r by exact ite_eq_right (not_lt.mpr (Finset.mem_Icc.mp hj).1)]
    ring
  have hbulk := transport_drift_bulk_weights a J n L f hf
  have hboundary := transport_drift_boundary_weights a ha1 J n L f hf
  have hGrow : (3 : ℝ) ^ (a * (L : ℝ)) ≤ (3 : ℝ) ^ (2 * a * (L : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [mul_nonneg ha.le (Nat.cast_nonneg L)])
  have hden := (transport_geometric_Icc (1 - a) (by linarith only [ha1]) J n).1
  have hboundary' : (∑ j ∈ V, w j * ∑ r ∈ Finset.Icc J (j - (L : ℤ) - 1),
      (3 : ℝ) ^ ((r : ℝ) - j) * f r) ≤
      ((3 : ℝ) ^ (2 * a * (L : ℝ)) / (1 - (3 : ℝ) ^ (-(1 - a)))) * T :=
    hboundary.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hGrow hden.le) hT)
  have hold : (∑ j ∈ U, w j * old j) ≤
      (3 : ℝ) ^ (2 * a * (L : ℝ)) * (1 + Cb / (1 - (3 : ℝ) ^ (-(1 - a)))) * T := by
    rw [heOld]
    calc
      _ ≤ (3 : ℝ) ^ (2 * a * (L : ℝ)) * T +
          Cb * (((3 : ℝ) ^ (2 * a * (L : ℝ)) / (1 - (3 : ℝ) ^ (-(1 - a)))) * T) :=
        add_le_add hbulk (mul_le_mul_of_nonneg_left hboundary' hCb)
      _ = _ := by ring
  have hsource := transport_drift_source_weights a b ha.le hab J n hn L hL
  calc
    _ ≤ (∑ j ∈ U, w j * h j) + E := herr.trans (add_le_add hsum le_rfl)
    _ = A * (∑ j ∈ U, w j * old j) + Y * (∑ j ∈ U, w j * src j) + E := by
      simp only [h, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
    _ ≤ A * ((3 : ℝ) ^ (2 * a * (L : ℝ)) * (1 + Cb / (1 - (3 : ℝ) ^ (-(1 - a)))) * T) +
        Y * (((n : ℝ) + L - J) * (3 : ℝ) ^ (-a * ((n : ℝ) - J))) + E :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hold hA) (mul_le_mul_of_nonneg_left hsource hY)) le_rfl
    _ = _ := by ring

/-- A source matrix upper bound controls its normalized trace excess. -/
theorem transport_normalized_trace_scalar_bound {d : ℕ} (A F : BlockMat d)
    (hA : (toFullBlockMat A).PosSemidef) (hF : (toFullBlockMat F).PosDef)
    (M : ℝ) (hM : 0 ≤ M) (hbound : BlockMatLoewnerLE A (blockScale M F)) :
    blockTrace (blockSub (normalizedBlock A F) (Book.Ch02.blockIdentity d)) ≤ 2 * (d : ℝ) * M := by
  have h := Source.blockTrace_le_of_order (transport_normalized_psd_bound hA hF hM hbound).2
  change blockTrace (normalizedBlock A F) ≤ Matrix.trace (toFullBlockMat (blockScale M (Book.Ch02.blockIdentity d))) at h
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity, Matrix.trace_smul, Matrix.trace_one] at h
  simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, smul_eq_mul] at h
  rw [transport_trace_excess]
  nlinarith only [h, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

end
end HCPolySupport.HighContrast.Annealed
