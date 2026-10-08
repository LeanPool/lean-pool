/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumSlice

/-!
# The time-slice pairings of transport, force and pressure

At a fixed time the pairing of the divergence source with the Leray
projection of a test transform is the transport pairing plus the pairing of
the Riesz pressure with the divergence of the test, and the pairing of the
force transform with the projected test is the force pairing plus the pairing
of the force pressure with the divergence of the test. These are the
remaining terms of `eq:reg-momentum-forced` on one time slice.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

theorem integrable_re_inner_of_memLp' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Y X : L2Vec3 → E} (hY : MemLp Y 2 volume) (hX : MemLp X 2 volume) :
    Integrable (fun ξ => (inner ℂ (Y ξ) (X ξ)).re) := by
  have hY2 := hY.integrable_norm_pow two_ne_zero
  have hX2 := hX.integrable_norm_pow two_ne_zero
  refine Integrable.mono' ((hY2.add hX2).div_const 2) ?_
    (Eventually.of_forall fun ξ => ?_)
  · exact (Complex.continuous_re.comp_aestronglyMeasurable
      (hY.aestronglyMeasurable.inner hX.aestronglyMeasurable))
  · rw [Real.norm_eq_abs]
    change _ ≤ (‖Y ξ‖ ^ 2 + ‖X ξ‖ ^ 2) / 2
    have h1 := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (Y ξ) (X ξ))
    nlinarith only [h1, sq_nonneg (‖Y ξ‖ - ‖X ξ‖)]

section Slice

variable {φ : Vec3 × ℝ → Vec3}

/-- The divergence of a time slice of a test. -/
@[expose]
def sliceDiv (φ : Vec3 × ℝ → Vec3) (t : ℝ) : Vec3 → ℝ :=
  fun x => ∑ k : Fin 3, spaceDeriv k φ (x, t) k

theorem sliceDiv_contDiff (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sliceDiv φ t) :=
  ContDiff.sum fun k _ => contDiff_pi.1 (contDiff_slice (contDiff_spaceDeriv hφ k) t) k

theorem hasCompactSupport_slice_component (hφc : HasCompactSupport φ) (t : ℝ) (k : Fin 3) :
    HasCompactSupport (fun x => φ (x, t) k) :=
  (hasCompactSupport_slice hφc t).comp_left (g := fun v : Vec3 => v k) rfl

theorem sliceDiv_hasCompactSupport (hφc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (sliceDiv φ t) := by
  have h : ∀ k : Fin 3, HasCompactSupport (fun x => spaceDeriv k φ (x, t) k) := fun k =>
    hasCompactSupport_slice_component (hasCompactSupport_spaceDeriv hφc k) t k
  have heq : sliceDiv φ t = (fun x => spaceDeriv 0 φ (x, t) 0) +
      (fun x => spaceDeriv 1 φ (x, t) 1) + (fun x => spaceDeriv 2 φ (x, t) 2) := by
    funext x
    simp [sliceDiv, Fin.sum_univ_three]
  rw [heq]
  exact ((h 0).add (h 1)).add (h 2)

/-- The transform of the divergence of a test slice is `2πi ⟨ξ, Φ⟩`. -/
theorem fourier_sliceDiv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (t : ℝ)
    (ξ : L2Vec3) :
    𝓕 (scalTestField (sliceDiv φ t)) ξ =
      (2 * Real.pi * Complex.I) * inner ℂ (complexifyFrequency ξ) (testHat φ (ξ, t)) := by
  have hk : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceDeriv k φ (x, t) k) := fun k =>
    contDiff_pi.1 (contDiff_slice (contDiff_spaceDeriv hφ k) t) k
  have hkc : ∀ k : Fin 3, HasCompactSupport (fun x => spaceDeriv k φ (x, t) k) := fun k =>
    hasCompactSupport_slice_component (hasCompactSupport_spaceDeriv hφc k) t k
  have hsum : 𝓕 (scalTestField (sliceDiv φ t)) ξ =
      ∑ k : Fin 3, 𝓕 (scalTestField (fun x => spaceDeriv k φ (x, t) k)) ξ := by
    rw [Real.fourier_eq]
    simp_rw [Real.fourier_eq]
    rw [← integral_finsetSum _ fun k _ => integrable_fourier_integrand_scalTest (hk k) (hkc k) ξ]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [scalTestField, sliceDiv, Complex.ofReal_sum, Finset.smul_sum]
  have hterm : ∀ k : Fin 3, 𝓕 (scalTestField (fun x => spaceDeriv k φ (x, t) k)) ξ =
      (2 * Real.pi * Complex.I) * (((ξ k : ℝ) : ℂ) * testHat φ (ξ, t) k) := by
    intro k
    rw [← fourier_testField_apply (contDiff_slice (contDiff_spaceDeriv hφ k) t)
      (hasCompactSupport_slice (hasCompactSupport_spaceDeriv hφc k) t)]
    change testHat (spaceDeriv k φ) (ξ, t) k = _
    rw [testHat_spaceDeriv hφ hφc k (ξ, t), PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hsum, inner_complexifyFrequency_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => hterm k

/-- The transport and quadratic pressure pairing on one time slice. -/
theorem integral_transport_pressure_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : RealTensorL2) {Fh : L2Vec3 → ComplexTensor3}
    (hFh : Fh =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 T) :
      L2Vec3 → ComplexTensor3))
    {q : Vec3 → ℝ}
    (hq : q =ᵐ[volume] rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp T))
    (t : ℝ) :
    ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ (Fh ξ)))
        (leraySymbol ξ (testHat φ (ξ, t)))).re =
      (∫ x, ∑ j : Fin 3, ∑ i : Fin 3, forcedTensorComp T j i x * spaceDeriv j φ (x, t) i) +
        ∫ x, q x * sliceDiv φ t x := by
  set Fc := Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 T) with hFc
  have hFm : MemLp Fh 2 volume := (Lp.memLp Fc).ae_eq hFh.symm
  set χ := sliceDiv φ t with hχ
  have hχs := sliceDiv_contDiff hφ t
  have hχc := sliceDiv_hasCompactSupport hφc t
  set Θ := gradTestSchwartz (fun x => φ (x, t)) (contDiff_slice hφ t)
    (hasCompactSupport_slice hφc t) with hΘ
  let a : L2Vec3 → ℝ := fun ξ => (inner ℂ (Fh ξ) ((𝓕 Θ) ξ)).re
  let b : L2Vec3 → ℝ := fun ξ =>
    (conj (pressureApplyFormula ξ (Fh ξ)) * 𝓕 (scalTestField χ) ξ).re
  have ha : ∀ ξ, a ξ = (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) •
      tensorDivergenceLinear ξ (Fh ξ))) (testHat φ (ξ, t))).re := fun ξ => by
    simp only [a]
    rw [hΘ, fourier_gradTestSchwartz, inner_sum_rowSlot]
    rfl
  have hsplit : ∀ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ (Fh ξ)))
      (leraySymbol ξ (testHat φ (ξ, t)))).re = a ξ + b ξ := fun ξ => by
    rw [inner_divergence_leray, ha, ← fourier_sliceDiv hφ hφc t ξ, Complex.add_re]
  have haint : Integrable a := integrable_re_inner_of_memLp' hFm ((𝓕 Θ).memLp 2)
  have hχ2 : MemLp (fun ξ => 𝓕 (scalTestField χ) ξ) 2 volume := by
    have h := (𝓕 (scalTestSchwartz χ hχs hχc)).memLp 2 (μ := (volume : Measure L2Vec3))
    exact h
  have hbint : Integrable b := by
    have hF2 := hFm.integrable_norm_pow two_ne_zero
    have hχ2' := hχ2.integrable_norm_pow two_ne_zero
    refine Integrable.mono' ((hF2.add hχ2').div_const 2) ?_ (Eventually.of_forall fun ξ => ?_)
    · have hP : AEStronglyMeasurable (fun ξ => pressureApplyFormula ξ (Fh ξ)) volume :=
        (pressureApplyFormula_measurable.comp_aemeasurable
          (aemeasurable_id.prodMk hFm.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
      exact Complex.continuous_re.comp_aestronglyMeasurable
        ((Complex.continuous_conj.comp_aestronglyMeasurable hP).mul hχ2.aestronglyMeasurable)
    · rw [Real.norm_eq_abs]
      change _ ≤ (‖Fh ξ‖ ^ 2 + ‖𝓕 (scalTestField χ) ξ‖ ^ 2) / 2
      have h1 : |b ξ| ≤ ‖Fh ξ‖ * ‖𝓕 (scalTestField χ) ξ‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (pressureApplyFormula_norm_le ξ (Fh ξ)) (norm_nonneg _)
      nlinarith only [h1, sq_nonneg (‖Fh ξ‖ - ‖𝓕 (scalTestField χ) ξ‖)]
  simp_rw [hsplit]
  rw [integral_add haint hbint]
  congr 1
  · rw [show (fun ξ => a ξ) = fun ξ => (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) •
        tensorDivergenceLinear ξ (Fh ξ))) (testHat φ (ξ, t))).re from funext ha]
    rw [show (∫ x, ∑ j : Fin 3, ∑ i : Fin 3, forcedTensorComp T j i x *
        spaceDeriv j φ (x, t) i) = ∫ x, ∑ j : Fin 3, ∑ i : Fin 3, forcedTensorComp T j i x *
        CKN.spatialDeriv (fun y => φ (y, t) i) j x from by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [← spatialPartial_eq_spaceDeriv hφ i j (x, t)]
      rfl]
    rw [integral_transport_eq_fourier T (contDiff_slice hφ t) (hasCompactSupport_slice hφc t)]
    refine integral_congr_ae ?_
    filter_upwards [hFh] with ξ hξ
    rw [hξ]
    rfl
  · have h1 : ∫ ξ, b ξ = ∫ ξ, (conj (pressureApplyFormula ξ ((Fc : L2Vec3 → ComplexTensor3) ξ)) *
        𝓕 (scalTestField χ) ξ).re := by
      refine integral_congr_ae ?_
      filter_upwards [hFh] with ξ hξ
      simp only [b]
      rw [hξ]
    rw [h1, ← integral_mul_quadPressureTilde T χ hχs hχc]
    refine integral_congr_ae ?_
    filter_upwards [hq, rieszPressure_ae_eq_quadPressureTilde T] with x hx1 hx2
    rw [hx1, hx2, mul_comm]

/-- The force and force pressure pairing on one time slice. -/
theorem integral_force_pressure_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {F : Vec3 → Vec3} (hF2 : MemLp F 2 volume)
    {Hh : L2Vec3 → ComplexVec3}
    (hHh : Hh =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
      (complexifyVectorL2 (realVectorL2OfCoordinateFunction F hF2)) : L2Vec3 → ComplexVec3))
    {pf : Vec3 → ℝ} (hpfl : LocallyIntegrable pf volume)
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) pf (forcePressureGradientFunction F hF2))
    (t : ℝ) :
    ∫ ξ, (inner ℂ (Hh ξ) (leraySymbol ξ (testHat φ (ξ, t)))).re =
      (∫ x, ∑ i : Fin 3, F x i * φ (x, t) i) + ∫ x, pf x * sliceDiv φ t x := by
  set W := realVectorL2OfCoordinateFunction F hF2 with hWdef
  set ℱV := Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 with hℱV
  have hre : realPartVectorL2 (complexifyVectorL2 W) = W := by
    apply Lp.ext
    filter_upwards [realPartValue.coeFn_compLpL (p := 2) (μ := volume) (complexifyVectorL2 W),
      complexifyValue.coeFn_compLpL (p := 2) (μ := volume) W] with x hreal hcomplex
    change (realPartValue.compLpL 2 volume (complexifyValue.compLpL 2 volume W)) x = W x
    change (realPartValue.compLpL 2 volume (complexifyValue.compLpL 2 volume W)) x =
      realPartValue ((complexifyValue.compLpL 2 volume W) x) at hreal
    rw [hreal, hcomplex]
    apply PiLp.ext
    intro i
    simp [realPartValue, realPartValueLinear, complexifyValue, complexifyValueLinear,
      complexifyFrequency]
  set Z := complexifyVectorL2 W - lerayProjectionL2 (complexifyVectorL2 W) with hZdef
  have hZ : realPartVectorL2 Z = forcePressureGradientL2 W := by
    rw [hZdef, map_sub, hre, forcePressureGradientL2, realLerayProjection]
  have hLZ : ℱV (lerayProjectionL2 (complexifyVectorL2 W)) =
      lerayFourierMultiplier (ℱV (complexifyVectorL2 W)) := by
    unfold lerayProjectionL2
    exact LinearIsometryEquiv.apply_symm_apply _ _
  have hY : (fun ξ => Hh ξ - leraySymbol ξ (Hh ξ)) =ᵐ[volume] (ℱV Z : L2Vec3 → ComplexVec3) := by
    rw [hZdef, map_sub, hLZ]
    have hM := measurableFourierMultiplier_ae_eq
      (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z)
      (ℱV (complexifyVectorL2 W))
    filter_upwards [Lp.coeFn_sub (ℱV (complexifyVectorL2 W))
      (lerayFourierMultiplier (ℱV (complexifyVectorL2 W))), hM, hHh] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply]
    change _ = _ - measurableFourierMultiplier _ _ _ _ (ℱV (complexifyVectorL2 W)) ξ
    rw [h2, h3, leraySymbol_apply_eq_formula]
  have hHm : MemLp Hh 2 volume := (Lp.memLp _).ae_eq hHh.symm
  have hYm : MemLp (fun ξ => Hh ξ - leraySymbol ξ (Hh ξ)) 2 volume :=
    (Lp.memLp _).ae_eq hY.symm
  have hΦm := memLp_testHat_slice hφ hφc t
  have hpoint : ∀ ξ, (inner ℂ (Hh ξ) (leraySymbol ξ (testHat φ (ξ, t)))).re =
      (inner ℂ (Hh ξ) (testHat φ (ξ, t))).re -
        (inner ℂ (Hh ξ - leraySymbol ξ (Hh ξ)) (testHat φ (ξ, t))).re := fun ξ => by
    rw [leraySymbol, ← Submodule.inner_starProjection_left_eq_right, inner_sub_left,
      Complex.sub_re]
    ring
  simp_rw [hpoint]
  rw [integral_sub (integrable_re_inner_of_memLp hHm hΦm) (integrable_re_inner_of_memLp hYm hΦm)]
  have hW : F =ᵐ[volume] realVectorL2Representative W :=
    (realVectorL2OfCoordinateFunction_rep F hF2).symm
  have hA := integral_slice_test_eq_fourier hφ hφc hW hre hHh t
  have hB := integral_slice_test_eq_fourier hφ hφc
    (w := forcePressureGradientFunction F hF2) (EventuallyEq.rfl) hZ hY t
  rw [← hA, ← hB]
  -- the weak gradient of the force pressure
  have hG2 : MemLp (forcePressureGradientFunction F hF2) 2 volume :=
    forcePressureGradientFunction_memLp F hF2
  have hk : ∀ k : Fin 3, ∫ x, pf x * spaceDeriv k φ (x, t) k =
      -∫ x, forcePressureGradientFunction F hF2 x k * φ (x, t) k := by
    intro k
    have h := hpf k (fun x => φ (x, t) k) (contDiff_pi.1 (contDiff_slice hφ t) k)
      (hasCompactSupport_slice_component hφc t k) (subset_univ _)
    have hfd : ∀ x, fderiv ℝ (fun x => φ (x, t) k) x (CKN.basisVec k) =
        spaceDeriv k φ (x, t) k := fun x => spatialPartial_eq_spaceDeriv hφ k k (x, t)
    simp only [Measure.restrict_univ, hfd] at h
    exact h
  have hint1 : ∀ k : Fin 3, Integrable fun x => pf x * spaceDeriv k φ (x, t) k := by
    intro k
    have h := hpfl.integrable_smul_right_of_hasCompactSupport
      (contDiff_pi.1 (contDiff_slice (contDiff_spaceDeriv hφ k) t) k).continuous
      (hasCompactSupport_slice_component (hasCompactSupport_spaceDeriv hφc k) t k)
    exact h
  have hint2 : ∀ k : Fin 3, Integrable fun x =>
      forcePressureGradientFunction F hF2 x k * φ (x, t) k := fun k =>
    integrable_mul_slice (hG2.eval k) hφ hφc t k
  have hsum : ∫ x, pf x * sliceDiv φ t x =
      -∫ x, ∑ k : Fin 3, forcePressureGradientFunction F hF2 x k * φ (x, t) k := by
    simp only [sliceDiv, Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => hint1 k, integral_finsetSum _ fun k _ => hint2 k,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hk k
  rw [hsum]
  ring

end Slice

end CKN.Leray

end
