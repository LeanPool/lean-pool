/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyConv

/-!
# The mollified energy identity on one time slice

On a time slice where the gradient, the force and the force pressure have
their slice properties, the source of the mollified forced regularized
velocity is a sum of convolutions, and the spatial pairing `∑ₖ ∫ wₖ Sₖ ψ`
equals, after integration by parts, the mollified transport-minus-viscous,
pressure and force pairings of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

theorem integrable_mul_of_hasCompactSupport_right {g h : Vec3 → ℝ} (hg : Continuous g)
    (hh : Continuous h) (hhc : HasCompactSupport h) : Integrable fun x => g x * h x :=
  (hg.mul hh).integrable_of_hasCompactSupport hhc.mul_left

section Delta

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The source as a sum of convolutions on a good time slice. -/
theorem leSF_eq_conv {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {t : ℝ} (k : Fin 3)
    (hA : ∀ j, MemLp (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume)
    (hF2 : MemLp (fun y => forcedForceMod f hf (y, t)) 2 volume)
    (hft : MemLp (fun x => f (x, t)) 2 volume)
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
      (forcePressureGradientFunction (fun x => f (x, t)) hft))
    (hpfl : LocallyIntegrable (fun x => forcePressure f hf (x, t)) volume) (x : Vec3) :
    leSF ρ ε hε ha hf η x t k =
      (∑ j : Fin 3, leConv (CKN.spatialDeriv η j) (fun y => leTensor ρ ε hε ha hf j k (y, t)) x) +
        leConv (CKN.spatialDeriv η k)
          (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x +
        leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x -
        leConv η (fun y => forcedForceMod f hf (y, t) k) x := by
  have hq2 : MemLp (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
      volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq
      (forcedQuadPressure_slice ρ ε hε (forcedRegCurve ρ ε hε ha hf) t).symm
  have hdη : ∀ j, Continuous (CKN.spatialDeriv η j) := fun j =>
    (CKN.contDiff_spatialDeriv_smooth hη j).continuous
  have hdηc : ∀ j, HasCompactSupport (CKN.spatialDeriv η j) := fun j =>
    CKN.hasCompactSupport_spatialDeriv hηc j
  have iA : ∀ j, Integrable fun y =>
      leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y) := fun j =>
    integrable_mul_reflect (hA j) (hdη j) (hdηc j) x
  have iq : Integrable fun y =>
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
        CKN.spatialDeriv η k (x - y) :=
    integrable_mul_reflect hq2 (hdη k) (hdηc k) x
  have ip : Integrable fun y => forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y) := by
    have h := hpfl.integrable_smul_right_of_hasCompactSupport
      ((hdη k).comp (continuous_const.sub continuous_id))
      ((hdηc k).comp_homeomorph (Homeomorph.subLeft x))
    exact h
  have iF : Integrable fun y => forcedForceMod f hf (y, t) k * η (x - y) :=
    integrable_mul_reflect (hF2.eval k) hη.continuous hηc x
  unfold leSF leKernelF lePressure
  have e1 : ∀ y, (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
      CKN.spatialDeriv η j (x - (y, t).1) +
      (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) +
        forcePressure f hf (y, t)) * CKN.spatialDeriv η k (x - (y, t).1) -
      forcedForceMod f hf (y, t) k * η (x - (y, t).1)) =
      (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y)) +
        (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
          CKN.spatialDeriv η k (x - y) +
          forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)) -
        forcedForceMod f hf (y, t) k * η (x - y) := fun y => by
    simp only
    ring
  simp_rw [e1]
  have jA : Integrable fun y => ∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
      CKN.spatialDeriv η j (x - y) := integrable_finsetSum _ fun j _ => iA j
  have jqp : Integrable fun y =>
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
        CKN.spatialDeriv η k (x - y) +
      forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y) := iq.add ip
  have jAqp : Integrable fun y => (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
      CKN.spatialDeriv η j (x - y)) +
      (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
        CKN.spatialDeriv η k (x - y) +
      forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)) := jA.add jqp
  rw [integral_sub jAqp iF, integral_add jA jqp, integral_add iq ip,
    integral_finsetSum _ fun j _ => iA j, integral_forcePressure_mul_reflect hf hη hηc hpf x k]
  simp only [integral_mul_reflect_eq_leConv]
  ring

theorem leW_eq_leConv (η : Vec3 → ℝ) (x : Vec3) (t : ℝ) (k : Fin 3) :
    leW ρ ε hε ha hf η x t k = leConv η (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x := by
  unfold leW
  rw [← integral_mul_reflect_eq_leConv]
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

theorem fderiv_leConv_mul {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) {g : Vec3 → ℝ} (hg : MemLp g 2 volume) {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Vec3) (j : Fin 3) :
    fderiv ℝ (fun y => leConv η g y * ψ y) x (CKN.basisVec j) =
      leConv (CKN.spatialDeriv η j) g x * ψ x + leConv η g x * fderiv ℝ ψ x (CKN.basisVec j) := by
  have hc := leConv_contDiff hη hηc (hg.locallyIntegrable (by norm_num))
  have hd : HasFDerivAt (fun y => leConv η g y * ψ y)
      (leConv η g x • fderiv ℝ ψ x + ψ x • fderiv ℝ (leConv η g) x) x :=
    ((hc.differentiable (by simp)) x).hasFDerivAt.mul ((hψ.differentiable (by simp)) x).hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_leConv hη hηc hg x j]
  ring

/-- The mollified energy pairing in one direction on a good time slice. -/
theorem integral_leW_mul_leSF {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) {t : ℝ} (k : Fin 3)
    (hA : ∀ j, MemLp (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume)
    (hF2 : MemLp (fun y => forcedForceMod f hf (y, t)) 2 volume)
    (hft : MemLp (fun x => f (x, t)) 2 volume)
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
      (forcePressureGradientFunction (fun x => f (x, t)) hft))
    (hpfl : LocallyIntegrable (fun x => forcePressure f hf (x, t)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k * ψ x =
      -(∑ j : Fin 3, ∫ x, leConv η (fun y => leTensor ρ ε hε ha hf j k (y, t)) x *
          (leConv (CKN.spatialDeriv η j) (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x * ψ x +
            leConv η (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x *
              fderiv ℝ ψ x (CKN.basisVec j))) -
        (∫ x, leConv η (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x *
          (leConv (CKN.spatialDeriv η k) (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x * ψ x +
            leConv η (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x *
              fderiv ℝ ψ x (CKN.basisVec k))) +
        (∫ x, leConv η (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x * ψ x *
          leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x) -
        ∫ x, leConv η (fun y => forcedForceMod f hf (y, t) k) x *
          (leConv η (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x * ψ x) := by
  set uk : Vec3 → ℝ := fun y => forcedRegRep ρ ε hε ha hf (y, t) k with huk
  have hu2 : MemLp uk 2 volume := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
  have hq2 : MemLp (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
      volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq
      (forcedQuadPressure_slice ρ ε hε (forcedRegCurve ρ ε hε ha hf) t).symm
  have hG2 : MemLp (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) 2 volume :=
    (forcePressureGradientFunction_memLp (fun x => f (x, t)) hft).eval k
  set a : Vec3 → ℝ := fun y => leConv η uk y * ψ y with hadef
  have hac : HasCompactSupport a := hψc.mul_left
  have hasm : ContDiff ℝ (⊤ : ℕ∞) a :=
    (leConv_contDiff hη hηc (hu2.locallyIntegrable (by norm_num))).mul hψ
  have hcont : ∀ {κ g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) κ → HasCompactSupport κ →
      MemLp g 2 volume → Continuous (leConv κ g) := fun hκ hκc hg =>
    (leConv_contDiff hκ hκc (hg.locallyIntegrable (by norm_num))).continuous
  have hdη : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv η j) := fun j =>
    CKN.contDiff_spatialDeriv_smooth hη j
  have hdηc : ∀ j, HasCompactSupport (CKN.spatialDeriv η j) := fun j =>
    CKN.hasCompactSupport_spatialDeriv hηc j
  have iA : ∀ j, Integrable fun x =>
      a x * leConv (CKN.spatialDeriv η j) (fun y => leTensor ρ ε hε ha hf j k (y, t)) x :=
    fun j => (hasm.continuous.mul (hcont (hdη j) (hdηc j) (hA j))).integrable_of_hasCompactSupport
      hac.mul_right
  have iq : Integrable fun x => a x * leConv (CKN.spatialDeriv η k)
      (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x :=
    (hasm.continuous.mul (hcont (hdη k) (hdηc k) hq2)).integrable_of_hasCompactSupport
      hac.mul_right
  have iG : Integrable fun x => a x * leConv η
      (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x :=
    (hasm.continuous.mul (hcont hη hηc hG2)).integrable_of_hasCompactSupport hac.mul_right
  have iF : Integrable fun x => a x * leConv η (fun y => forcedForceMod f hf (y, t) k) x :=
    (hasm.continuous.mul (hcont hη hηc (hF2.eval k))).integrable_of_hasCompactSupport
      hac.mul_right
  have hsplit : ∀ x, leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k * ψ x =
      (∑ j : Fin 3, a x * leConv (CKN.spatialDeriv η j)
        (fun y => leTensor ρ ε hε ha hf j k (y, t)) x) +
      a x * leConv (CKN.spatialDeriv η k)
        (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x +
      a x * leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x -
      a x * leConv η (fun y => forcedForceMod f hf (y, t) k) x := fun x => by
    rw [leW_eq_leConv, leSF_eq_conv ρ ε hε ha hf hη hηc k hA hF2 hft hpf hpfl x]
    simp only [a, huk, Fin.sum_univ_three]
    ring
  simp_rw [hsplit]
  have j1 : Integrable fun x => ∑ j : Fin 3, a x * leConv (CKN.spatialDeriv η j)
      (fun y => leTensor ρ ε hε ha hf j k (y, t)) x := integrable_finsetSum _ fun j _ => iA j
  have j2 : Integrable fun x => (∑ j : Fin 3, a x * leConv (CKN.spatialDeriv η j)
      (fun y => leTensor ρ ε hε ha hf j k (y, t)) x) + a x * leConv (CKN.spatialDeriv η k)
        (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x :=
    j1.add iq
  have j3 : Integrable fun x => (∑ j : Fin 3, a x * leConv (CKN.spatialDeriv η j)
      (fun y => leTensor ρ ε hε ha hf j k (y, t)) x) + a x * leConv (CKN.spatialDeriv η k)
        (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x +
      a x * leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x :=
    j2.add iG
  rw [integral_sub j3 iF, integral_add j2 iG, integral_add j1 iq,
    integral_finsetSum _ fun j _ => iA j]
  have hibp : ∀ j, ∫ x, a x * leConv (CKN.spatialDeriv η j)
      (fun y => leTensor ρ ε hε ha hf j k (y, t)) x =
      -∫ x, leConv η (fun y => leTensor ρ ε hε ha hf j k (y, t)) x *
        (leConv (CKN.spatialDeriv η j) uk x * ψ x +
          leConv η uk x * fderiv ℝ ψ x (CKN.basisVec j)) := by
    intro j
    rw [integral_mul_leConv_spatialDeriv hη hηc (hA j) hasm hac j]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [a]
    rw [fderiv_leConv_mul hη hηc hu2 hψ x j]
    ring
  have hibq : ∫ x, a x * leConv (CKN.spatialDeriv η k)
      (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x =
      -∫ x, leConv η (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) x *
        (leConv (CKN.spatialDeriv η k) uk x * ψ x +
          leConv η uk x * fderiv ℝ ψ x (CKN.basisVec k)) := by
    rw [integral_mul_leConv_spatialDeriv hη hηc hq2 hasm hac k]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [a]
    rw [fderiv_leConv_mul hη hηc hu2 hψ x k]
    ring
  simp_rw [hibp]
  rw [hibq, Finset.sum_neg_distrib]
  have e3 : ∫ x, a x * leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x
      = ∫ x, leConv η uk x * ψ x *
          leConv η (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) x := rfl
  have e4 : ∫ x, a x * leConv η (fun y => forcedForceMod f hf (y, t) k) x =
      ∫ x, leConv η (fun y => forcedForceMod f hf (y, t) k) x * (leConv η uk x * ψ x) :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e3, e4]
  ring

end Delta

end CKN.Leray

end
