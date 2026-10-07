/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierLemmaAssembly

/-!
# The physical regularization kernel

The scalar kernel induced by the regularized equation's profile is
smooth, compactly supported, nonnegative and has unit mass. These
properties instantiate the ordered Sobolev contraction estimate in
`eq:lps-Hm-energy`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The physical scalar regularization kernel has the smoothness,
support and normalization required for `H^m` contraction
(`eq:lps-Hm-energy`). -/
theorem lps_regUniformMollifierKernel_properties
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (CKN.Leray.regUniformMollifierKernel ρ ε hε) ∧
    HasCompactSupport (CKN.Leray.regUniformMollifierKernel ρ ε hε) ∧
    (∀ x, 0 ≤ CKN.Leray.regUniformMollifierKernel ρ ε hε x) ∧
    (∫ x : Vec3, CKN.Leray.regUniformMollifierKernel ρ ε hε x = 1) := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.Leray.regUniformMollifierKernel ρ ε hε) := by
    have hto : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => WithLp.toLp 2 x) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 x))
    exact contDiff_const.mul
      (ρ.smooth.comp ((contDiff_const_smul ε⁻¹).comp hto))
  have hcompact : HasCompactSupport
      (CKN.Leray.regUniformMollifierKernel ρ ε hε) := by
    let hhomeo : Vec3 ≃ₜ L2Vec3 := CKN.Foundation.Parabolic.vec3Homeomorph
    let hscale : L2Vec3 ≃ₜ L2Vec3 := Homeomorph.smulOfNeZero ε⁻¹
      (inv_ne_zero (ne_of_gt hε))
    have hcomp := ρ.compact.comp_homeomorph (hhomeo.trans hscale)
    have hcompact' : HasCompactSupport (fun x : Vec3 =>
        (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x)) := hcomp.mul_left
    have heq : CKN.Leray.regUniformMollifierKernel ρ ε hε = fun x : Vec3 =>
        (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x) := by
      funext x
      simp [CKN.Leray.regUniformMollifierKernel, CKN.Leray.regMollifierKernel,
        hhomeo, hscale, Homeomorph.trans_apply]
    rw [heq]
    exact hcompact'
  have hnonneg (x : Vec3) :
      0 ≤ CKN.Leray.regUniformMollifierKernel ρ ε hε x :=
    CKN.Leray.regMollifierKernel_nonneg ρ ε hε (WithLp.toLp 2 x)
  have hone : (∫ x : Vec3,
      CKN.Leray.regUniformMollifierKernel ρ ε hε x) = 1 := by
    calc
      (∫ x : Vec3, CKN.Leray.regUniformMollifierKernel ρ ε hε x) =
          ∫ x : L2Vec3, CKN.Leray.regMollifierKernel ρ ε hε x := by
            exact CKN.Leray.vec3ToL2Vec3_measurePreserving.integral_comp
              (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding _
      _ = 1 := CKN.Leray.regMollifierKernel_integral_eq_one ρ ε hε
  exact ⟨hsmooth, hcompact, hnonneg, hone⟩

end ESS
