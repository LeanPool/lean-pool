/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumWeak

/-!
# The momentum identity on one time slice

On every time slice where the velocity has a square-integrable weak gradient
and the force and force pressure have their slice properties, the spatial
integral of the integrand of `eq:reg-momentum-forced` is the combination of
frequency pairings that the frequency weak form sets to zero after
integration in time.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

/-- The integrand of `eq:reg-momentum-forced` for the forced regularized
solution, with the space-time derivatives of the test. -/
@[expose]
def forcedMomentumIntegrand (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3}
    (ha : CKN.IsInJ a) (f : ParabolicPoint → Vec3) (hf : CKN.IsLocallySquareIntegrableForce f)
    (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  -(∑ i : Fin 3, forcedRegRep ρ ε hε ha hf z i * timeDeriv φ z i) -
    ∑ i : Fin 3, ∑ j : Fin 3,
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j *
        forcedRegRep ρ ε hε ha hf z i * spaceDeriv j φ z i +
    ∑ i : Fin 3, ∑ j : Fin 3,
      forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z i j * spaceDeriv j φ z i -
    (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z) *
      stDiv φ z -
    ∑ i : Fin 3, f z i * φ z i

theorem integral_six_combo {A1 A2 A3 A4 A5 A6 : Vec3 → ℝ} (h1 : Integrable A1)
    (h2 : Integrable A2) (h3 : Integrable A3) (h4 : Integrable A4) (h5 : Integrable A5)
    (h6 : Integrable A6) :
    ∫ x, (-A1 x - A2 x + A3 x - (A4 x + A5 x) - A6 x) =
      -(∫ x, A1 x) - (∫ x, A2 x) + (∫ x, A3 x) - ((∫ x, A4 x) + ∫ x, A5 x) - ∫ x, A6 x := by
  have j1 : Integrable (fun x => -A1 x) := h1.neg
  have j2 : Integrable (fun x => -A1 x - A2 x) := j1.sub h2
  have j3 : Integrable (fun x => -A1 x - A2 x + A3 x) := j2.add h3
  have j45 : Integrable (fun x => A4 x + A5 x) := h4.add h5
  have j5 : Integrable (fun x => -A1 x - A2 x + A3 x - (A4 x + A5 x)) := j3.sub j45
  rw [integral_sub j5 h6, integral_sub j3 j45, integral_add j2 h3, integral_sub j1 h2,
    integral_neg, integral_add h4 h5]

theorem forcedMomentumIntegrand_eq (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) (φ : Vec3 × ℝ → Vec3) (x : Vec3) (t : ℝ) :
    forcedMomentumIntegrand ρ ε hε ha f hf φ (x, t) =
      -(∑ i : Fin 3, forcedRegRep ρ ε hε ha hf (x, t) i * timeDeriv φ (x, t) i) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) j *
            forcedRegRep ρ ε hε ha hf (x, t) i * spaceDeriv j φ (x, t) i) +
        (∑ i : Fin 3, ∑ j : Fin 3, forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i j *
          spaceDeriv j φ (x, t) i) -
        (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t) * sliceDiv φ t x +
          forcePressure f hf (x, t) * sliceDiv φ t x) -
        ∑ i : Fin 3, f (x, t) i * φ (x, t) i := by
  simp only [forcedMomentumIntegrand, stDiv, sliceDiv]
  ring

section Slice

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)
  {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)

include hφ hφc in
/-- The momentum integrand on one time slice in frequency variables. -/
theorem integral_forcedMomentumIntegrand_slice {t : ℝ} {Y : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 → ComplexTensor3} {Hh : L2Vec3 → ComplexVec3}
    (hZ : ∃ Z : ComplexVectorL2, realPartVectorL2 Z = forcedRegCurve ρ ε hε ha hf t ∧
      Y =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3))
    (hFh : Fh =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2
      (regularizedMildTensor ρ ε hε (forcedRegCurve ρ ε hε ha hf t))) : L2Vec3 → ComplexTensor3))
    (hHh : Hh =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2
      (forcedForceSlice (forcedForceMod f hf) t)) : L2Vec3 → ComplexVec3))
    (hweak : ∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => forcedRegRep ρ ε hε ha hf (x, t) i)
      (fun x => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i))
    (hDu : ∀ i j, MemLp (fun x => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i j) 2
      volume)
    (hF2 : MemLp (fun x => forcedForceMod f hf (x, t)) 2 volume)
    (hFf : (fun x => forcedForceMod f hf (x, t)) =ᵐ[volume] fun x => f (x, t))
    (hft : MemLp (fun x => f (x, t)) 2 volume)
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
      (forcePressureGradientFunction (fun x => f (x, t)) hft))
    (hpfl : LocallyIntegrable (fun x => forcePressure f hf (x, t)) volume) :
    ∫ x, forcedMomentumIntegrand ρ ε hε ha f hf φ (x, t) =
      -(∫ ξ, (inner ℂ (Y ξ) (testHat (timeDeriv φ) (ξ, t))).re) +
        (∫ ξ, (inner ℂ (Y ξ) (((forcedFourierLam ξ : ℝ) : ℂ) • testHat φ (ξ, t))).re) -
        (∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ (Fh ξ)))
          (leraySymbol ξ (testHat φ (ξ, t)))).re) -
        ∫ ξ, (inner ℂ (Hh ξ) (leraySymbol ξ (testHat φ (ξ, t)))).re := by
  obtain ⟨Z, hZre, hY⟩ := hZ
  set u := forcedRegRep ρ ε hε ha hf with hudef
  set U := forcedRegCurve ρ ε hε ha hf with hUdef
  set Tt := regularizedMildTensor ρ ε hε (U t) with hTt
  have hrep := forcedRegRep_slice ρ ε hε ha hf t
  have hu2 : MemLp (fun x => u (x, t)) 2 volume := forcedRegRep_memLp ρ ε hε ha hf t
  -- the time pairing
  have hA : ∫ x, ∑ i : Fin 3, u (x, t) i * timeDeriv φ (x, t) i =
      ∫ ξ, (inner ℂ (Y ξ) (testHat (timeDeriv φ) (ξ, t))).re :=
    integral_slice_test_eq_fourier (contDiff_timeDeriv hφ) (hasCompactSupport_timeDeriv hφc)
      hrep hZre hY t
  -- the viscous pairing
  have hB := integral_viscous_eq_fourier hφ hφc hrep hZre hY t hweak hDu
  -- the transport and quadratic pressure pairing
  have hq : (fun x => forcedQuadPressure ρ ε hε U (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp Tt) :=
    forcedQuadPressure_slice ρ ε hε U t
  have hC := integral_transport_pressure_slice hφ hφc Tt hFh hq t
  have hJ : (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i * spaceDeriv j φ (x, t) i) =ᵐ[volume]
      fun x => ∑ j : Fin 3, ∑ i : Fin 3, forcedTensorComp Tt j i x * spaceDeriv j φ (x, t) i := by
    have hall := ae_all_iff.2 fun j => ae_all_iff.2 fun i =>
      regPressureTensorSlice_ae_eq ρ ε hε hrep j i
    filter_upwards [hall] with x hx
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← hx j i]
    rfl
  -- the force and force pressure pairing
  have hR : realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft =
      forcedForceSlice (forcedForceMod f hf) t := by
    unfold forcedForceSlice
    rw [dite_eq_left hF2]
    apply realVectorL2Representative_injective_ae
    exact (realVectorL2OfCoordinateFunction_rep _ _).trans
      (hFf.symm.trans (realVectorL2OfCoordinateFunction_rep _ _).symm)
  have hHh' : Hh =ᵐ[volume] (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2
      (realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft)) : L2Vec3 → ComplexVec3) := by
    rw [hR]
    exact hHh
  have hD := integral_force_pressure_slice hφ hφc hft hHh' hpfl hpf t
  -- integrability of the pieces
  have hi1 : Integrable fun x => ∑ i : Fin 3, u (x, t) i * timeDeriv φ (x, t) i :=
    integrable_finsetSum _ fun i _ => integrable_mul_slice (hu2.eval i)
      (contDiff_timeDeriv hφ) (hasCompactSupport_timeDeriv hφc) t i
  have hi2 : Integrable fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i * spaceDeriv j φ (x, t) i := by
    refine Integrable.congr ?_ hJ.symm
    refine integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => ?_
    have h1 := memLp_forcedTensorComp Tt j i
    rw [ofReal_two_eq] at h1
    exact integrable_mul_slice h1 (contDiff_spaceDeriv hφ j) (hasCompactSupport_spaceDeriv hφc j)
      t i
  have hi3 : Integrable fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      forcedMollifiedGrad u (x, t) i j * spaceDeriv j φ (x, t) i :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_mul_slice (hDu i j) (contDiff_spaceDeriv hφ j)
        (hasCompactSupport_spaceDeriv hφc j) t i
  have hq2 : MemLp (fun x => forcedQuadPressure ρ ε hε U (x, t)) 2 volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq hq.symm
  have hdiv2 : MemLp (sliceDiv φ t) 2 volume :=
    (sliceDiv_contDiff hφ t).continuous.memLp_of_hasCompactSupport
      (sliceDiv_hasCompactSupport hφc t)
  have hi4 : Integrable fun x => forcedQuadPressure ρ ε hε U (x, t) * sliceDiv φ t x :=
    hq2.integrable_mul hdiv2
  have hi5 : Integrable fun x => forcePressure f hf (x, t) * sliceDiv φ t x := by
    have h := hpfl.integrable_smul_right_of_hasCompactSupport
      (sliceDiv_contDiff hφ t).continuous (sliceDiv_hasCompactSupport hφc t)
    exact h
  have hi6 : Integrable fun x => ∑ i : Fin 3, f (x, t) i * φ (x, t) i :=
    integrable_finsetSum _ fun i _ => integrable_mul_slice (hft.eval i) hφ hφc t i
  simp_rw [forcedMomentumIntegrand_eq]
  rw [integral_six_combo hi1 hi2 hi3 hi4 hi5 hi6, hA, ← hB, integral_congr_ae hJ, hC, hD]
  ring

end Slice

end CKN.Leray

end
