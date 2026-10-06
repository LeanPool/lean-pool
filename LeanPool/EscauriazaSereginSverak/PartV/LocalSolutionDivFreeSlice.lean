/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingKernel

/-!
# Heat-kernel pairings of a double-divergence-free slice

At a fixed positive time `r`, the spatial derivative `∂_j Γ(·, r)` of the heat
kernel is paired with the translates `y ↦ ∫ g_ij(w) ∂_i ψ(w + y) dw` of a
square-integrable tensor `g` against the derivatives of a test function `ψ`.
Moving `∂_j` from the kernel onto `ψ` and exchanging the integrals turns the
pairing into `-∫ Γ(y, r) ∑_ij ∫ g_ij(w) ∂_i ∂_j ψ(w + y) dw dy`, which vanishes
when `∑_ij ∂_i ∂_j g_ij = 0` in the sense of distributions. This is the
fixed-time step in the proof that the forced heat response of a
double-divergence-free tensor is divergence free (`prop:pv-local-solution`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- For integrable `k`, square-integrable `g` and continuous compactly
supported `φ`, the function `(y, w) ↦ k(y) g(w) φ(w + y)` is integrable on
`Vec3 × Vec3`: the inner integral is bounded by `(‖g‖₂² + ‖φ‖₂²) / 2`
uniformly in `y`. -/
theorem integrable_mul_mul_translate {k g φ : Vec3 → ℝ} (hk : Integrable k)
    (hg : MemLp g 2 volume) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun q : Vec3 × Vec3 => k q.1 * (g q.2 * φ (q.2 + q.1)))
      ((volume : Measure Vec3).prod volume) := by
  have hφ2 : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport hφc
  have hmeas : AEStronglyMeasurable (fun q : Vec3 × Vec3 => k q.1 * (g q.2 * φ (q.2 + q.1)))
      ((volume : Measure Vec3).prod volume) :=
    hk.aestronglyMeasurable.comp_fst.mul (hg.aestronglyMeasurable.comp_snd.mul
      (hφ.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable)
  set C : ℝ := ((∫ w, g w ^ 2) + ∫ w, φ w ^ 2) / 2 with hC
  have hφy (y : Vec3) : MemLp (fun w : Vec3 => φ (w + y)) 2 volume :=
    (hφ.comp (continuous_id.add continuous_const)).memLp_of_hasCompactSupport
      (hφc.comp_homeomorph (Homeomorph.addRight y))
  have hslice (y : Vec3) : Integrable (fun w : Vec3 => g w * φ (w + y)) :=
    hg.integrable_mul (hφy y)
  have hbound (y : Vec3) : ∫ w, ‖k y * (g w * φ (w + y))‖ ≤ ‖k y‖ * C := by
    have hpt (w : Vec3) : ‖k y * (g w * φ (w + y))‖ ≤
        ‖k y‖ * ((g w ^ 2 + φ (w + y) ^ 2) / 2) := by
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith only [sq_nonneg (|g w| - |φ (w + y)|), sq_abs (g w), sq_abs (φ (w + y))]
    have hsq : Integrable (fun w : Vec3 => (g w ^ 2 + φ (w + y) ^ 2) / 2) :=
      (hg.integrable_sq.add (hφy y).integrable_sq).div_const 2
    calc
      ∫ w, ‖k y * (g w * φ (w + y))‖ ≤ ∫ w, ‖k y‖ * ((g w ^ 2 + φ (w + y) ^ 2) / 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _)
          (hsq.const_mul _) (Eventually.of_forall hpt)
      _ = ‖k y‖ * C := by
        rw [integral_const_mul, integral_div, integral_add hg.integrable_sq (hφy y).integrable_sq,
          integral_add_right_eq_self (fun w => φ w ^ 2) y]
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun y => (hslice y).const_mul (k y), ?_⟩
  refine Integrable.mono' (hk.norm.mul_const C) hmeas.norm.integral_prod_right' ?_
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
  exact hbound y

/-- At a positive time the spatial derivative of the heat kernel is integrable
in space. -/
theorem heatKernelSpaceDerivative_slice_integrable {r : ℝ} (hr : 0 < r) (j : Fin 3) :
    Integrable (fun y : Vec3 => heatKernelSpaceDerivative y r j) := by
  have hmeas : Measurable (fun y : Vec3 => heatKernelSpaceDerivative y r j) :=
    (heatKernelSpaceDerivative_vecTime_measurable j).comp (measurable_id.prodMk measurable_const)
  refine Integrable.mono' ((heatKernelGradientMajorant_slice_integrable hr).const_mul 100)
    hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans ?_ (heatKernelGradientNorm_le_majorant hr)
  exact Finset.single_le_sum (f := fun k => |heatKernelSpaceDerivative y r k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ j)

/-- Integration by parts in space against the spatial derivative of the heat
kernel at a positive time: `∫ ∂_j Γ(y, r) φ(w + y) dy = -∫ Γ(y, r) ∂_j φ(w + y) dy`. -/
theorem integral_heatKernelSpaceDerivative_mul_translate {r : ℝ} (hr : 0 < r)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (w : Vec3) (j : Fin 3) :
    ∫ y : Vec3, heatKernelSpaceDerivative y r j * φ (w + y) =
      -∫ y : Vec3, heatKernel y r * fderiv ℝ φ (w + y) (CKN.basisVec j) := by
  let F : Vec3 → ℝ := fun y => heatKernel y r
  let Gs : Vec3 → ℝ := fun y => φ (w + y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    have heq : F = fun y : Vec3 => (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, y i ^ 2) / (4 * r)) := by
      funext y
      exact heatKernel_eq_formula_sum hr
    rw [heq]
    fun_prop
  have hGs : ContDiff ℝ (⊤ : ℕ∞) Gs := hφ.comp (contDiff_const.add contDiff_id)
  have hGsc : HasCompactSupport Gs := hφc.comp_homeomorph (Homeomorph.addLeft w)
  have hDF (y : Vec3) : fderiv ℝ F y (CKN.basisVec j) = heatKernelSpaceDerivative y r j :=
    heatKernel_fderiv_apply_basisVec hr j
  have hDGs (y : Vec3) : fderiv ℝ Gs y (CKN.basisVec j) =
      fderiv ℝ φ (w + y) (CKN.basisVec j) := by
    change fderiv ℝ (fun y => φ (w + y)) y (CKN.basisVec j) = _
    rw [fderiv_comp_add_left]
  have hDGsc : Continuous (fun y => fderiv ℝ Gs y (CKN.basisVec j)) :=
    (hGs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDGscs : HasCompactSupport (fun y => fderiv ℝ Gs y (CKN.basisVec j)) :=
    hGsc.fderiv_apply (𝕜 := ℝ) _
  have hDFc : Continuous (fun y => fderiv ℝ F y (CKN.basisVec j)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun y => fderiv ℝ F y (CKN.basisVec j) * Gs y) :=
    (hDFc.mul hGs.continuous).integrable_of_hasCompactSupport hGsc.mul_left
  have h2 : Integrable (fun y => F y * fderiv ℝ Gs y (CKN.basisVec j)) :=
    (hF.continuous.mul hDGsc).integrable_of_hasCompactSupport hDGscs.mul_left
  have h3 : Integrable (fun y => F y * Gs y) :=
    (hF.continuous.mul hGs.continuous).integrable_of_hasCompactSupport hGsc.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun y _ => (hF.differentiable (by simp)) y)
    (fun y _ => (hGs.differentiable (by simp)) y)
  have hleft : (fun y : Vec3 => heatKernelSpaceDerivative y r j * φ (w + y)) =
      fun y => fderiv ℝ F y (CKN.basisVec j) * Gs y := by
    funext y
    rw [hDF]
  have hright : (fun y : Vec3 => heatKernel y r * fderiv ℝ φ (w + y) (CKN.basisVec j)) =
      fun y => F y * fderiv ℝ Gs y (CKN.basisVec j) := by
    funext y
    rw [hDGs]
  rw [hleft, hright, hibp, neg_neg]

/-- Moving the spatial derivative from the heat kernel onto the test function:
for square-integrable `g` and a smooth compactly supported `ψ`,
`∫ ∂_j Γ(y, r) ∫ g(w) ∂_i ψ(w + y) dw dy = -∫ Γ(y, r) ∫ g(w) ∂_i ∂_j ψ(w + y) dw dy`. -/
theorem kernel_translate_pairing_eq {r : ℝ} (hr : 0 < r) {g : Vec3 → ℝ}
    (hg : MemLp g 2 volume) {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    ∫ y : Vec3, heatKernelSpaceDerivative y r j *
        ∫ w : Vec3, g w * fderiv ℝ ψ (w + y) (CKN.basisVec i) =
      -∫ y : Vec3, heatKernel y r * ∫ w : Vec3, g w * CKN.mixedSecond ψ i j (w + y) := by
  set d : Vec3 → ℝ := CKN.spatialDeriv ψ i with hd_def
  have hd : ContDiff ℝ (⊤ : ℕ∞) d := CKN.contDiff_spatialDeriv_smooth hψ i
  have hdc : HasCompactSupport d := hψc.fderiv_apply (𝕜 := ℝ) _
  set m : Vec3 → ℝ := CKN.mixedSecond ψ i j with hm_def
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := CKN.contDiff_mixedSecond_smooth hψ i j
  have hmc : HasCompactSupport m :=
    (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)).fderiv_apply (𝕜 := ℝ) _
  have hdm (x : Vec3) : fderiv ℝ d x (CKN.basisVec j) = m x :=
    (CKN.mixedSecond_swap hψ i j x).symm
  have hK := heatKernelSpaceDerivative_slice_integrable hr j
  have hΓ : Integrable (fun y : Vec3 => heatKernel y r) := heatKernel_integrable hr
  have hA1 := integrable_mul_mul_translate hK hg hd.continuous hdc
  have hA2 := integrable_mul_mul_translate hΓ hg hm.continuous hmc
  calc
    ∫ y : Vec3, heatKernelSpaceDerivative y r j * ∫ w : Vec3, g w * d (w + y) =
        ∫ y : Vec3, ∫ w : Vec3, heatKernelSpaceDerivative y r j * (g w * d (w + y)) := by
      congr 1
      funext y
      rw [integral_const_mul]
    _ = ∫ w : Vec3, ∫ y : Vec3, heatKernelSpaceDerivative y r j * (g w * d (w + y)) :=
      integral_integral_swap hA1
    _ = ∫ w : Vec3, g w * ∫ y : Vec3, heatKernelSpaceDerivative y r j * d (w + y) := by
      congr 1
      funext w
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ w : Vec3, -∫ y : Vec3, heatKernel y r * (g w * m (w + y)) := by
      congr 1
      funext w
      rw [integral_heatKernelSpaceDerivative_mul_translate hr hd hdc w j, mul_neg,
        ← integral_const_mul]
      congr 2
      funext y
      rw [hdm]
      ring
    _ = -∫ y : Vec3, ∫ w : Vec3, heatKernel y r * (g w * m (w + y)) := by
      rw [integral_neg, ← integral_integral_swap hA2]
    _ = -∫ y : Vec3, heatKernel y r * ∫ w : Vec3, g w * m (w + y) := by
      congr 2
      funext y
      rw [integral_const_mul]

/-- The heat-kernel pairing of a double-divergence-free square-integrable
tensor vanishes: if `∑_ij ∫ g_ij ∂_i ∂_j φ = 0` for every smooth compactly
supported `φ`, then `∑_ij ∫ ∂_j Γ(y, r) ∫ g_ij(w) ∂_i ψ(w + y) dw dy = 0`. -/
theorem kernel_translate_pairing_sum_eq_zero {r : ℝ} (hr : 0 < r)
    {g : Fin 3 → Fin 3 → Vec3 → ℝ} (hg : ∀ i j, MemLp (g i j) 2 volume)
    (hdd : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, g i j y * CKN.mixedSecond φ i j y = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, heatKernelSpaceDerivative y r j *
      ∫ w : Vec3, g i j w * fderiv ℝ ψ (w + y) (CKN.basisVec i) = 0 := by
  have hE (i j : Fin 3) := kernel_translate_pairing_eq hr (hg i j) hψ hψc i j
  simp only [hE]
  set f : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    heatKernel y r * ∫ w : Vec3, g i j w * CKN.mixedSecond ψ i j (w + y) with hf_def
  have hΓ : Integrable (fun y : Vec3 => heatKernel y r) := heatKernel_integrable hr
  have hfint (i j : Fin 3) : Integrable (f i j) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (CKN.mixedSecond ψ i j) :=
      CKN.contDiff_mixedSecond_smooth hψ i j
    have hmc : HasCompactSupport (CKN.mixedSecond ψ i j) :=
      (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)).fderiv_apply (𝕜 := ℝ) _
    have h := (integrable_mul_mul_translate hΓ (hg i j) hm.continuous hmc).integral_prod_left
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [f]
    rw [integral_const_mul]
  have hzero (y : Vec3) : ∑ i : Fin 3, ∑ j : Fin 3, f i j y = 0 := by
    have hψy : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 => ψ (z - -y)) :=
      hψ.comp (contDiff_id.sub contDiff_const)
    have hψyc : HasCompactSupport (fun z : Vec3 => ψ (z - -y)) :=
      hψc.comp_homeomorph (Homeomorph.subRight (-y))
    have htr (i j : Fin 3) (w : Vec3) :
        CKN.mixedSecond (fun z : Vec3 => ψ (z - -y)) i j w = CKN.mixedSecond ψ i j (w + y) := by
      rw [CKN.mixedSecond_sub_const hψ, sub_neg_eq_add]
    have h := hdd _ hψy hψyc
    simp only [htr] at h
    simp only [f, ← Finset.mul_sum, h, mul_zero]
  have hsum : ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, f i j y = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y, f i j y := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hfint i j)]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hfint i j
  have htot : ∑ i : Fin 3, ∑ j : Fin 3, ∫ y, f i j y = 0 := by
    rw [← hsum]
    simp only [hzero, integral_zero]
  simp only [Finset.sum_neg_distrib, neg_eq_zero]
  exact htot

end ESS

end
