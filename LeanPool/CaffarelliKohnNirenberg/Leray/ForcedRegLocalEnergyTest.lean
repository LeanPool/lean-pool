/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentum
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim

/-!
# Point tests of the momentum identity

For a fixed spatial point `x`, a direction `k` and a smooth time test `θ`, the
space-time field `θ(t) η(x - y) e_k` is an admissible test of
`eq:reg-momentum-forced`. Its time and spatial derivatives are explicit, and
the momentum integrand splits into the time derivative of the test times the
velocity and the test times an explicit kernel. This is the first step of the
local energy inequality `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The point test `θ(t) η(x - y) e_k`. -/
@[expose]
def lePointTest (η : Vec3 → ℝ) (θ : ℝ → ℝ) (x : Vec3) (k : Fin 3) : Vec3 × ℝ → Vec3 :=
  fun z => (θ z.2 * η (x - z.1)) • CKN.basisVec k

section PointTest

variable {η : Vec3 → ℝ} {θ : ℝ → ℝ} (x : Vec3) (k : Fin 3)

theorem lePointTest_contDiff (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) :
    ContDiff ℝ (⊤ : ℕ∞) (lePointTest η θ x k) :=
  ((hθ.comp contDiff_snd).mul (hη.comp (contDiff_const.sub contDiff_fst))).smul contDiff_const

theorem lePointTest_support_subset :
    Function.support (lePointTest η θ x k) ⊆ ((fun y => x - y) '' tsupport η) ×ˢ tsupport θ := by
  intro z hz
  refine ⟨⟨x - z.1, ?_, by simp⟩, ?_⟩
  · by_contra h
    exact hz (by simp [lePointTest, image_eq_zero_of_notMem_tsupport h])
  · by_contra h
    exact hz (by simp [lePointTest, image_eq_zero_of_notMem_tsupport h])

theorem lePointTest_hasCompactSupport (hηc : HasCompactSupport η) (hθc : HasCompactSupport θ) :
    HasCompactSupport (lePointTest η θ x k) :=
  HasCompactSupport.of_support_subset_isCompact
    ((hηc.image (continuous_const.sub continuous_id)).prod hθc)
    (lePointTest_support_subset x k)

theorem lePointTest_tsupport (hηc : HasCompactSupport η) (hθc : HasCompactSupport θ) {T : ℝ}
    (hθs : tsupport θ ⊆ Ioo 0 T) :
    ∀ z ∈ tsupport (lePointTest η θ x k), z.2 ∈ Ioo 0 T := by
  intro z hz
  have hK : IsCompact (((fun y => x - y) '' tsupport η) ×ˢ tsupport θ) :=
    (hηc.image (continuous_const.sub continuous_id)).prod hθc
  have h := closure_minimal (lePointTest_support_subset x k) hK.isClosed hz
  exact hθs h.2

theorem hasFDerivAt_lePointTest_scalar (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (z : Vec3 × ℝ) :
    HasFDerivAt (fun w : Vec3 × ℝ => θ w.2 * η (x - w.1))
      (θ z.2 • ((fderiv ℝ η (x - z.1)).comp (-(ContinuousLinearMap.fst ℝ Vec3 ℝ))) +
        η (x - z.1) • ((fderiv ℝ θ z.2).comp (ContinuousLinearMap.snd ℝ Vec3 ℝ))) z := by
  have h1 : HasFDerivAt (fun w : Vec3 × ℝ => θ w.2)
      ((fderiv ℝ θ z.2).comp (ContinuousLinearMap.snd ℝ Vec3 ℝ)) z :=
    ((hθ.differentiable (by simp)) z.2).hasFDerivAt.comp z hasFDerivAt_snd
  have h2 : HasFDerivAt (fun w : Vec3 × ℝ => η (x - w.1))
      ((fderiv ℝ η (x - z.1)).comp (-(ContinuousLinearMap.fst ℝ Vec3 ℝ))) z := by
    have hs : HasFDerivAt (fun w : Vec3 × ℝ => x - w.1) (-(ContinuousLinearMap.fst ℝ Vec3 ℝ)) z :=
      (hasFDerivAt_fst.const_sub x)
    exact ((hη.differentiable (by simp)) (x - z.1)).hasFDerivAt.comp z hs
  have h := h1.mul h2
  convert h using 1

theorem timeDeriv_lePointTest (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (z : Vec3 × ℝ) :
    timeDeriv (lePointTest η θ x k) z = (deriv θ z.2 * η (x - z.1)) • CKN.basisVec k := by
  have h := (hasFDerivAt_lePointTest_scalar x hη hθ z).smul_const (CKN.basisVec k)
  unfold timeDeriv lePointTest
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    map_zero, neg_zero, smul_eq_mul, mul_zero, zero_add]
  rw [mul_comm]
  rfl

theorem spaceDeriv_lePointTest (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (j : Fin 3) (z : Vec3 × ℝ) :
    spaceDeriv j (lePointTest η θ x k) z =
      (-(θ z.2 * CKN.spatialDeriv η j (x - z.1))) • CKN.basisVec k := by
  have h := (hasFDerivAt_lePointTest_scalar x hη hθ z).smul_const (CKN.basisVec k)
  unfold spaceDeriv lePointTest
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    map_zero, map_neg, smul_eq_mul, mul_zero, add_zero, CKN.spatialDeriv, mul_neg]

end PointTest

theorem sum_sum_ite_eq_fin (k : Fin 3) (A : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, (if i = k then A i j else 0) = ∑ j : Fin 3, A k j := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

section Kernel

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  (f : ParabolicPoint → Vec3) (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The kernel of the point-tested momentum identity. -/
@[expose]
def leKernel (η : Vec3 → ℝ) (x : Vec3) (k : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  ∑ j : Fin 3, (regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j *
      forcedRegRep ρ ε hε ha hf z k - forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z k j) *
      CKN.spatialDeriv η j (x - z.1) +
    (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z) *
      CKN.spatialDeriv η k (x - z.1) -
    f z k * η (x - z.1)

theorem forcedMomentumIntegrand_lePointTest {η : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (x : Vec3) (k : Fin 3)
    (z : Vec3 × ℝ) :
    forcedMomentumIntegrand ρ ε hε ha f hf (lePointTest η θ x k) z =
      -(deriv θ z.2 * (η (x - z.1) * forcedRegRep ρ ε hε ha hf z k)) +
        θ z.2 * leKernel ρ ε hε ha f hf η x k z := by
  simp only [forcedMomentumIntegrand, timeDeriv_lePointTest x k hη hθ,
    spaceDeriv_lePointTest x k hη hθ, stDiv, lePointTest, leKernel, Pi.smul_apply, smul_eq_mul,
    CKN.basisVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [sum_sum_ite_eq_fin k (fun i j => regUniformMollifiedVelocity ρ ε hε
      (forcedRegRep ρ ε hε ha hf) z j * forcedRegRep ρ ε hε ha hf z i *
        -(θ z.2 * CKN.spatialDeriv η j (x - z.1))),
    sum_sum_ite_eq_fin k (fun i j => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z i j *
      -(θ z.2 * CKN.spatialDeriv η j (x - z.1)))]
  simp only [Fin.sum_univ_three]
  ring

end Kernel

end CKN.Leray

end
