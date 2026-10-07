/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumPressureId

/-!
# The time-slice pairings of the momentum identity

At a fixed time the pairings of the velocity with the time derivative of a
space-time test and of its weak gradient with the spatial gradient of the test
are frequency pairings with the transform of the test and with its damped
symbol. These are the time and viscous terms of `eq:reg-momentum-forced` on
one time slice.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ComplexConjugate

noncomputable section

namespace CKN.Leray

section Slice

variable {φ : Vec3 × ℝ → Vec3}

theorem memLp_slice_component (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (t : ℝ) (i : Fin 3) : MemLp (fun x => φ (x, t) i) 2 volume :=
  ((contDiff_slice hφ t).continuous.memLp_of_hasCompactSupport (p := 2)
    (hasCompactSupport_slice hφc t)).eval i

theorem integrable_mul_slice {v : Vec3 → ℝ} (hv : MemLp v 2 volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (t : ℝ) (i : Fin 3) :
    Integrable (fun x => v x * φ (x, t) i) :=
  hv.integrable_mul (memLp_slice_component hφ hφc t i)

theorem memLp_testHat_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (t : ℝ) : MemLp (fun ξ => testHat φ (ξ, t)) 2 volume := by
  have h := (𝓕 (testSchwartz (fun x => φ (x, t)) (contDiff_slice hφ t)
    (hasCompactSupport_slice hφc t))).memLp 2 (μ := (volume : Measure L2Vec3))
  exact h

theorem integrable_re_inner_of_memLp {Y X : L2Vec3 → ComplexVec3} (hY : MemLp Y 2 volume)
    (hX : MemLp X 2 volume) : Integrable (fun ξ => (inner ℂ (Y ξ) (X ξ)).re) := by
  have hY2 := hY.integrable_norm_pow two_ne_zero
  have hX2 := hX.integrable_norm_pow two_ne_zero
  refine Integrable.mono' ((hY2.add hX2).div_const 2) ?_
    (Eventually.of_forall fun ξ => ?_)
  · exact (Complex.continuous_re.comp_aestronglyMeasurable
      (hY.aestronglyMeasurable.inner hX.aestronglyMeasurable))
  · rw [Real.norm_eq_abs]
    exact abs_re_inner_le_half (Y ξ) (X ξ)

/-- The pairing of a velocity slice with a test slice in frequency
variables. -/
theorem integral_slice_test_eq_fourier (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {W : RealVectorL2} {w : Vec3 → Vec3} (hw : w =ᵐ[volume] realVectorL2Representative W)
    {Z : ComplexVectorL2} (hZ : realPartVectorL2 Z = W) {Y : L2Vec3 → ComplexVec3}
    (hY : Y =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3))
    (t : ℝ) :
    ∫ x, ∑ i : Fin 3, w x i * φ (x, t) i = ∫ ξ, (inner ℂ (Y ξ) (testHat φ (ξ, t))).re := by
  have hw' : w =ᵐ[volume] realVectorL2Representative (realPartVectorL2 Z) := by
    rw [hZ]
    exact hw
  have h := integral_test_eq_fourier Z hw' (fun x => φ (x, t)) (contDiff_slice hφ t)
    (hasCompactSupport_slice hφc t)
  have h1 : ∫ x, ∑ i : Fin 3, w x i * φ (x, t) i =
      ∫ x, ∑ i : Fin 3, φ (x, t) i * w x i := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h]
  refine integral_congr_ae ?_
  filter_upwards [hY] with ξ hξ
  rw [hξ]
  rfl

/-- The damped symbol of a test is minus the sum of its second spatial
derivatives. -/
theorem lam_smul_testHat (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (p : L2Vec3 × ℝ) :
    ((forcedFourierLam p.1 : ℝ) : ℂ) • testHat φ p =
      -∑ j : Fin 3, testHat (spaceDeriv j (spaceDeriv j φ)) p := by
  have hj : ∀ j : Fin 3, testHat (spaceDeriv j (spaceDeriv j φ)) p =
      (((2 * Real.pi * Complex.I) * ((p.1 j : ℝ) : ℂ)) ^ 2) • testHat φ p := by
    intro j
    rw [testHat_spaceDeriv (contDiff_spaceDeriv hφ j) (hasCompactSupport_spaceDeriv hφc j) j p,
      testHat_spaceDeriv hφ hφc j p, smul_smul, sq]
  simp only [hj]
  rw [← Finset.sum_smul, ← neg_smul]
  congr 1
  rw [forcedFourierLam, norm_sq_eq_sum_coord, Fin.sum_univ_three, Fin.sum_univ_three]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) ^ 2 *
    (((p.1 0 : ℝ) : ℂ) ^ 2 + ((p.1 1 : ℝ) : ℂ) ^ 2 + ((p.1 2 : ℝ) : ℂ) ^ 2)) * Complex.I_sq

/-- The viscous pairing on one time slice in frequency variables. -/
theorem integral_viscous_eq_fourier (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {W : RealVectorL2} {w : Vec3 → Vec3} (hw : w =ᵐ[volume] realVectorL2Representative W)
    {Z : ComplexVectorL2} (hZ : realPartVectorL2 Z = W) {Y : L2Vec3 → ComplexVec3}
    (hY : Y =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3))
    (t : ℝ) {Dw : Vec3 → Fin 3 → Vec3}
    (hweak : ∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => w x i)
      (fun x => Dw x i))
    (hDw : ∀ i j, MemLp (fun x => Dw x i j) 2 volume) :
    ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j * spaceDeriv j φ (x, t) i =
      ∫ ξ, (inner ℂ (Y ξ) (((forcedFourierLam ξ : ℝ) : ℂ) • testHat φ (ξ, t))).re := by
  have hw2 : MemLp w 2 volume := (realVectorL2Representative_memLp_two W).ae_eq hw.symm
  have hYm : MemLp Y 2 volume := (Lp.memLp _).ae_eq hY.symm
  have hφ2 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (spaceDeriv j (spaceDeriv j φ)) := fun j =>
    contDiff_spaceDeriv (contDiff_spaceDeriv hφ j) j
  have hφ2c : ∀ j, HasCompactSupport (spaceDeriv j (spaceDeriv j φ)) := fun j =>
    hasCompactSupport_spaceDeriv (hasCompactSupport_spaceDeriv hφc j) j
  -- the frequency side
  have hR : ∫ ξ, (inner ℂ (Y ξ) (((forcedFourierLam ξ : ℝ) : ℂ) • testHat φ (ξ, t))).re =
      -∑ j : Fin 3, ∫ x, ∑ i : Fin 3, w x i * spaceDeriv j (spaceDeriv j φ) (x, t) i := by
    have hint : ∀ j : Fin 3, Integrable fun ξ =>
        (inner ℂ (Y ξ) (testHat (spaceDeriv j (spaceDeriv j φ)) (ξ, t))).re := fun j =>
      integrable_re_inner_of_memLp hYm (memLp_testHat_slice (hφ2 j) (hφ2c j) t)
    have h1 : ∀ ξ, (inner ℂ (Y ξ) (((forcedFourierLam ξ : ℝ) : ℂ) • testHat φ (ξ, t))).re =
        -∑ j : Fin 3, (inner ℂ (Y ξ) (testHat (spaceDeriv j (spaceDeriv j φ)) (ξ, t))).re := by
      intro ξ
      rw [lam_smul_testHat hφ hφc (ξ, t), inner_neg_right, inner_sum, Complex.neg_re,
        Complex.re_sum]
    simp_rw [h1]
    rw [integral_neg, integral_finsetSum _ fun j _ => hint j]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (integral_slice_test_eq_fourier (hφ2 j) (hφ2c j) hw hZ hY t).symm
  -- the physical side
  have hint1 : ∀ i j : Fin 3, Integrable fun x => Dw x i j * spaceDeriv j φ (x, t) i :=
    fun i j => integrable_mul_slice (hDw i j) (contDiff_spaceDeriv hφ j)
      (hasCompactSupport_spaceDeriv hφc j) t i
  have hint2 : ∀ i j : Fin 3, Integrable fun x => w x i * spaceDeriv j (spaceDeriv j φ) (x, t) i :=
    fun i j => integrable_mul_slice (hw2.eval i) (hφ2 j) (hφ2c j) t i
  have hibp : ∀ i j : Fin 3, ∫ x, Dw x i j * spaceDeriv j φ (x, t) i =
      -∫ x, w x i * spaceDeriv j (spaceDeriv j φ) (x, t) i := by
    intro i j
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceDeriv j φ (x, t) i) :=
      contDiff_pi.1 (contDiff_slice (contDiff_spaceDeriv hφ j) t) i
    have hψc : HasCompactSupport (fun x => spaceDeriv j φ (x, t) i) :=
      (hasCompactSupport_slice (hasCompactSupport_spaceDeriv hφc j) t).comp_left
        (g := fun v : Vec3 => v i) rfl
    have h := hweak i j (fun x => spaceDeriv j φ (x, t) i) hψ hψc (subset_univ _)
    have hfd : ∀ x, fderiv ℝ (fun x => spaceDeriv j φ (x, t) i) x (CKN.basisVec j) =
        spaceDeriv j (spaceDeriv j φ) (x, t) i := fun x =>
      spatialPartial_eq_spaceDeriv (contDiff_spaceDeriv hφ j) i j (x, t)
    simp only [Measure.restrict_univ, hfd] at h
    linarith only [h]
  rw [hR, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
  simp_rw [integral_finsetSum _ fun j _ => hint1 _ j, hibp]
  rw [Finset.sum_comm]
  simp_rw [integral_finsetSum _ fun i _ => hint2 i _]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]

end Slice

end CKN.Leray

end
