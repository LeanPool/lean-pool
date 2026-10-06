/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureCauchy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialLimit

public section

open CKN

open MeasureTheory Set Filter CKN.Foundation.Parabolic
noncomputable section
namespace ESS

private theorem compact_field_spatial_decay
    (f : Vec3 × ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Vec3 × ℝ,
      |f z| ≤ C * (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) := by
  let w : Vec3 × ℝ → ℝ := fun z =>
    f z * (1 + vec3EuclideanNorm z.1) ^ m
  have hwc : Continuous w := by
    dsimp [w]
    exact hf.mul (((continuous_const.add
      (CKN.continuous_vec3EuclideanNorm.comp continuous_fst)).pow m))
  have hws : HasCompactSupport w := hfc.mul_right
  obtain ⟨C, hC⟩ := hws.exists_bound_of_continuous hwc
  have hC0 : 0 ≤ C := (norm_nonneg (w (0,0))).trans (hC (0,0))
  refine ⟨C, hC0, ?_⟩
  intro z
  let b : ℝ := 1 + vec3EuclideanNorm z.1
  have hb : 0 < b := by
    dsimp [b]
    linarith only [vec3EuclideanNorm_nonneg z.1]
  have hpow : 0 < b ^ m := pow_pos hb _
  have hbound : |f z| * b ^ m ≤ C := by
    have h := hC z
    simpa only [w, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hb.le _), b] using h
  calc
    |f z| = (|f z| * b ^ m) * (b ^ m)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hpow.ne', mul_one]
    _ ≤ C * (b ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hpow.le)
    _ = C * b ^ (-(m : ℝ)) := by
      rw [Real.rpow_neg hb.le]
      simp only [Real.rpow_natCast]

/-- Smooth compact space-time tests satisfy the decay hypotheses of the
Riesz pressure duality formula. -/
theorem blowup_compact_test_rieszPressurePotentialDecay
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    CKN.Leray.RieszPressurePotentialDecay ψ := by
  let K : Set ℝ := Prod.snd '' tsupport ψ
  have hK : IsCompact K := hψc.isCompact.image continuous_snd
  have htime : ∀ t ∉ K, ∀ x, ψ (x,t) = 0 := by
    intro t ht x
    exact image_eq_zero_of_notMem_tsupport (fun hz =>
      ht ⟨(x,t), hz, rfl⟩)
  obtain ⟨C₀, hC₀, hval⟩ :=
    compact_field_spatial_decay ψ hψ.continuous hψc 2
  have hgradData (i : Fin 3) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
        |CKN.Leray.rieszPressureJointDirection ψ i z| ≤
          C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    apply compact_field_spatial_decay
      (CKN.Leray.rieszPressureJointDirection ψ i)
      ((CKN.Leray.rieszPressureJointDirection_contDiff hψ i).continuous)
      (by
        exact hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i, (0 : ℝ))) 3
  choose C₁ hC₁ hgrad using hgradData
  have hhessData (i j : Fin 3) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
        |CKN.Leray.rieszPressureJointHessian ψ i j z| ≤
          C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
    apply compact_field_spatial_decay
      (CKN.Leray.rieszPressureJointHessian ψ i j)
      ((CKN.Leray.rieszPressureJointHessian_contDiff hψ i j).continuous)
      (CKN.Leray.rieszPressureJointHessian_hasCompactSupport hψc i j) 4
  choose C₂ hC₂ hhess using hhessData
  refine ⟨⟨K, hK, htime⟩, ⟨C₀, hC₀, ?_⟩,
    ⟨∑ i : Fin 3, C₁ i, Finset.sum_nonneg fun i _ => hC₁ i, ?_⟩,
    ⟨∑ i : Fin 3, ∑ j : Fin 3, C₂ i j,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC₂ i j, ?_⟩⟩
  · intro z
    simpa only [Nat.cast_ofNat] using hval z
  · intro i z
    exact (hgrad i z).trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j hj => hC₁ j) (Finset.mem_univ i))
        (Real.rpow_nonneg
          (add_nonneg zero_le_one (vec3EuclideanNorm_nonneg _)) _))
  · intro i j z
    have hsum : C₂ i j ≤ ∑ i : Fin 3, ∑ j : Fin 3, C₂ i j := by
      exact (Finset.single_le_sum
        (fun l hl => hC₂ i l) (Finset.mem_univ j)).trans
        (Finset.single_le_sum
          (fun k hk => Finset.sum_nonneg fun l _ => hC₂ k l)
          (Finset.mem_univ i))
    exact (hhess i j z).trans
      (mul_le_mul_of_nonneg_right
        hsum (Real.rpow_nonneg
          (add_nonneg zero_le_one (vec3EuclideanNorm_nonneg _)) _))

end ESS
