/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyTest

/-!
# The weak time derivative of the mollified velocity

At every spatial point `x`, the spatial mollification `∫ η(x - y) u(y, t) dy`
of the forced regularized velocity is continuous in time and has weak time
derivative `-∫ K(x; y, t) dy`, where `K` is the kernel of the point-tested
momentum identity `eq:reg-momentum-forced`. This is the time regularity used
in the local energy inequality `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

section Weak

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The mollified velocity at a point. -/
@[expose]
def leW (η : Vec3 → ℝ) (x : Vec3) (t : ℝ) (k : Fin 3) : ℝ :=
  ∫ y, η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k

/-- The source of the mollified velocity at a point. -/
@[expose]
def leS (η : Vec3 → ℝ) (x : Vec3) (t : ℝ) (k : Fin 3) : ℝ :=
  ∫ y, leKernel ρ ε hε ha f hf η x k (y, t)

/-- The point field `η(x - ·) e_k`. -/
@[expose]
def lePointField (η : Vec3 → ℝ) (x : Vec3) (k : Fin 3) : Vec3 → Vec3 :=
  fun y => η (x - y) • CKN.basisVec k

theorem memLp_lePointField {η : Vec3 → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (x : Vec3) (k : Fin 3) : MemLp (lePointField η x k) 2 volume := by
  have hc : Continuous (lePointField η x k) :=
    (hη.comp (continuous_const.sub continuous_id)).smul continuous_const
  have hs : HasCompactSupport (lePointField η x k) := by
    have h1 : HasCompactSupport (fun y => η (x - y)) := by
      have := hηc.comp_homeomorph (Homeomorph.subLeft x)
      exact this
    exact h1.smul_right
  exact hc.memLp_of_hasCompactSupport hs

theorem leW_eq_inner {η : Vec3 → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (x : Vec3) (t : ℝ) (k : Fin 3) :
    leW ρ ε hε ha hf η x t k = inner ℝ (forcedRegCurve ρ ε hε ha hf t)
      (realVectorL2OfCoordinateFunction (lePointField η x k) (memLp_lePointField hη hηc x k)) := by
  rw [inner_realVectorL2OfCoordinateFunction (forcedRegRep_slice ρ ε hε ha hf t)]
  unfold leW
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [lePointField, Pi.smul_apply, smul_eq_mul, CKN.basisVec, Pi.single_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem continuous_leW {η : Vec3 → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (x : Vec3) (k : Fin 3) : Continuous fun t => leW ρ ε hε ha hf η x t k := by
  simp_rw [leW_eq_inner ρ ε hε ha hf hη hηc x _ k]
  exact (continuous_forcedRegCurve ρ ε hε ha hf).inner continuous_const

/-- The weak time derivative of the mollified velocity at a point. -/
theorem hasWeakDerivOn_leW {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (x : Vec3) (k : Fin 3) {T : ℝ} (hT : 0 < T) :
    CKN.HasWeakDerivOn (Ioo 0 T) (fun t => leW ρ ε hε ha hf η x t k)
      (fun t => -leS ρ ε hε ha hf η x t k) := by
  intro θ hθtest
  obtain ⟨hθ, hθc, hθs⟩ := hθtest
  have hφ := lePointTest_contDiff x k hη hθ
  have hφc := lePointTest_hasCompactSupport x k hηc hθc
  have hTs := lePointTest_tsupport x k hηc hθc hθs
  have hw := forcedReg_weak_form ρ ε hε ha hf hφ hφc hT hTs
  have hEint := integrable_forcedMomentumIntegrand ρ ε hε ha hf hφ hφc hT
  have hηu : ∀ t, Integrable fun y => η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k := by
    intro t
    have h1 : MemLp (fun y => η (x - y)) 2 volume :=
      ((memLp_lePointField hη.continuous hηc x k).eval k).congr_norm
        ((hη.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun y => by simp [lePointField, CKN.basisVec])
    exact h1.integrable_mul ((forcedRegRep_memLp ρ ε hε ha hf t).eval k)
  have hslice : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      ∫ y, forcedMomentumIntegrand ρ ε hε ha f hf (lePointTest η θ x k) (y, t) =
        θ t * leS ρ ε hε ha hf η x t k - deriv θ t * leW ρ ε hε ha hf η x t k := by
    filter_upwards [hEint.prod_left_ae] with t ht
    have hA : Integrable fun y => deriv θ t * (η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k) :=
      (hηu t).const_mul _
    have heq : ∀ y, θ t * leKernel ρ ε hε ha f hf η x k (y, t) =
        forcedMomentumIntegrand ρ ε hε ha f hf (lePointTest η θ x k) (y, t) +
          deriv θ t * (η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k) := by
      intro y
      rw [forcedMomentumIntegrand_lePointTest ρ ε hε ha f hf hη hθ x k (y, t)]
      ring
    have hK : ∫ y, θ t * leKernel ρ ε hε ha f hf η x k (y, t) =
        (∫ y, forcedMomentumIntegrand ρ ε hε ha f hf (lePointTest η θ x k) (y, t)) +
          deriv θ t * ∫ y, η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k := by
      simp_rw [heq]
      rw [integral_add ht hA, integral_const_mul]
    rw [integral_const_mul] at hK
    unfold leS leW
    linarith only [hK]
  have hθ'c : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  have hint1 : IntegrableOn (fun t => deriv θ t * leW ρ ε hε ha hf η x t k) (Ioo 0 T) :=
    ((hθ'c.mul (continuous_leW ρ ε hε ha hf hη.continuous hηc x k)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun t => ∫ y, forcedMomentumIntegrand ρ ε hε ha f hf
      (lePointTest η θ x k) (y, t)) (Ioo 0 T) := hEint.integral_prod_right
  have hθS : ∫ t in Ioo 0 T, θ t * leS ρ ε hε ha hf η x t k =
      ∫ t in Ioo 0 T, deriv θ t * leW ρ ε hε ha hf η x t k := by
    have h1 : ∫ t in Ioo 0 T, θ t * leS ρ ε hε ha hf η x t k =
        ∫ t in Ioo 0 T, ((∫ y, forcedMomentumIntegrand ρ ε hε ha f hf (lePointTest η θ x k)
          (y, t)) + deriv θ t * leW ρ ε hε ha hf η x t k) := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hslice] with t ht hts
      rw [ht hts]
      ring
    rw [h1, integral_add hint2 hint1, hw, zero_add]
  have e1 : ∫ t in Ioo 0 T, leW ρ ε hε ha hf η x t k * deriv θ t =
      ∫ t in Ioo 0 T, deriv θ t * leW ρ ε hε ha hf η x t k :=
    integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
  have e2 : ∫ t in Ioo 0 T, -leS ρ ε hε ha hf η x t k * θ t =
      -∫ t in Ioo 0 T, θ t * leS ρ ε hε ha hf η x t k := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  rw [e1, e2, hθS, neg_neg]

end Weak

end CKN.Leray

end
