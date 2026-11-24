/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosedProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedHessianDivergence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotStokes

/-!
# Closedness of the smooth currents `[M] ∧ γ₁ ∧ ⋯ ∧ γ_p`

Let `(M, ω)` be a compact Kähler manifold of dimension `N` and `γ₀, …, γ_{p-1}` smooth closed real
`(1,1)`-forms.  The smooth current `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}`
(`SmoothCurrentTraceMeasure.smoothCurrent`) is closed in the sense of
`ClosedProductCurrents.IsClosedCurrent` (`isClosedCurrent_smoothCurrent`): for chart-smooth `f, g`
and closed real `(1,1)`-forms `β`,

`∫_M Π₁₁ d(f dg) ∧ β₀ ∧ ⋯ ∧ β_{k-1} ∧ γ₀ ∧ ⋯ ∧ γ_{p-1} = 0`.

This is Stokes' theorem for `d(f dg ∧ P)`, `P` a product of closed `(1,1)`-forms
(`demailly-cadg:III.1`, `d[M] = 0` wedged with closed smooth forms).  The proof avoids a general
Leibniz rule for exterior products (the Skoda–El Mir extension argument,
D2 UPDATE): it uses the project's mixed-Hessian divergence calculus.

* **Euclidean identity** (`integral_pairMatrix_cofactor_eq_zero`).  On `ℂᵐ⁺¹`, for smooth `F, G`
  with `F` compactly supported and smooth `ρ₁, …, ρₘ`,
  `∫ ∑ⱼₖ (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF) Cⱼₖ = 0`, `C` the cofactor field of `(ddᶜρ₁, …, ddᶜρₘ)` in the
  first slot.  Since `C` is divergence free in the `∂` and in the `∂bar` directions
  (`MixedHessian.sum_dDir_cofactorField`, `sum_dbarDir_cofactorField`), the integrand is the
  divergence `∑ ∂ⱼ(F ∂barₖG Cⱼₖ) - ∂barₖ(F ∂ⱼG Cⱼₖ)` (`pairMatrix_cofactor_eq_sum_wirt`).
* **The coefficient matrix** of `Π₁₁ (dF ∧ dG)` is `-2πi (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF)`
  (`normalizedHermitianMatrix_pi11_eq`), so in a chart where the closed slots are `ddᶜρᵢ`, the
  density of `Π₁₁ d(f dg) ∧ θ₁ ∧ ⋯` is `Re(-2πi ∑ⱼₖ (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF) Cⱼₖ) / πᴺ`
  (`actualMixedTopDensity_closedSlots_eq`).
* **One slot chart** (`setIntegral_closedSlots_eq_zero`): local potentials of all slots
  (`GlobalSlotStokes.SlotChart`), cut-offs to globally smooth data, then the Euclidean identity.
* **On the manifold** (`integral_topRatio_eq_zero_of_slotChart`, `integral_topRatio_eq_zero`):
  change of variables to the chart (`setIntegral_image_eq`, signed version of
  `SmoothMixedMeasureDensity.setLIntegral_image_eq`) and a chart-smooth partition of unity
  subordinate to slot charts, `d(f dg) = ∑ₐ d(χₐ f dg)`.

## Main results

* `pairMatrix`, `pairMatrix_cofactor_eq_sum_wirt`, `integral_pairMatrix_cofactor_eq_zero`.
* `normalizedHermitianMatrix_pi11_eq`, `actualMixedTopDensity_update_eq`,
  `actualMixedTopDensity_closedSlots_eq`.
* `setIntegral_closedSlots_eq_zero`, `setIntegral_image_eq`,
  `integral_topRatio_eq_zero_of_slotChart`, `integral_topRatio_eq_zero`.
* `closedTestForm_coeff`, `isClosedCurrent_smoothCurrent`, `isClosedCurrent_smoothCurrentOf`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere MixedHessian StronglyPositiveForms

/-! ### The Euclidean identity -/

section Euclid

variable {n : ℕ}

/-- The first-order matrix `∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF` of two real functions. -/
def pairMatrix (F G : ComplexModel n → ℝ) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k =>
    wirt (-Complex.I) (coordinateVector j) (fun y => (F y : ℂ)) z *
        wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) z -
      wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) z *
        wirt Complex.I (coordinateVector k) (fun y => (F y : ℂ)) z

variable {m : ℕ} {ρ : Fin m → ComplexModel (m + 1) → ℝ}

/-- **Divergence form.**
`∑ⱼₖ (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF) Cⱼₖ = ∑ⱼₖ ∂ⱼ(F ∂barₖG Cⱼₖ) - ∂barₖ(F ∂ⱼG Cⱼₖ)`
for the cofactor field `C` of `(ddᶜρ₁, …, ddᶜρₘ)`, which is divergence free in both directions. -/
theorem pairMatrix_cofactor_eq_sum_wirt (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    {F G : ComplexModel (m + 1) → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (z : ComplexModel (m + 1)) :
    ∑ j, ∑ k, pairMatrix F G z j k * cofactorField ρ j k z =
      ∑ j, ∑ k, (wirt (-Complex.I) (coordinateVector j) (fun y => (F y : ℂ) *
          (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z -
        wirt Complex.I (coordinateVector k) (fun y => (F y : ℂ) *
          (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hFc : ContDiff ℝ ∞ (fun y => (F y : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hGc : ContDiff ℝ ∞ (fun y => (G y : ℂ)) := Complex.ofRealCLM.contDiff.comp hG
  have hd {H : ComplexModel (m + 1) → ℂ} (hH : ContDiff ℝ ∞ H) : DifferentiableAt ℝ H z :=
    hH.differentiable (by simp) z
  have hterm (j k : Fin (m + 1)) :
      wirt (-Complex.I) (coordinateVector j) (fun y => (F y : ℂ) *
          (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z -
        wirt Complex.I (coordinateVector k) (fun y => (F y : ℂ) *
          (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z =
      pairMatrix F G z j k * cofactorField ρ j k z +
        (F z : ℂ) * wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) z *
          wirt (-Complex.I) (coordinateVector j) (cofactorField ρ j k) z -
        (F z : ℂ) * wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) z *
          wirt Complex.I (coordinateVector k) (cofactorField ρ j k) z := by
    have hW := contDiff_wirt (c := Complex.I) (v := coordinateVector k) hGc
    have hD := contDiff_wirt (c := -Complex.I) (v := coordinateVector j) hGc
    have hC := contDiff_cofactorField hρ j k
    have hcomm : wirt (-Complex.I) (coordinateVector j)
        (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ))) z =
        wirt Complex.I (coordinateVector k)
          (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ))) z :=
      wirt_wirt_comm (hGc.contDiffAt.of_le h2)
    rw [wirt_mul (hd hFc) (hd (hW.mul hC)), wirt_mul (hd hW) (hd hC),
      wirt_mul (hd hFc) (hd (hD.mul hC)), wirt_mul (hd hD) (hd hC), hcomm, pairMatrix]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ j, ∑ k, (F z : ℂ) * wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) z *
      wirt (-Complex.I) (coordinateVector j) (cofactorField ρ j k) z = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, sum_dDir_cofactorField hρ, mul_zero]
  have e2 : ∑ j, ∑ k, (F z : ℂ) *
      wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) z *
        wirt Complex.I (coordinateVector k) (cofactorField ρ j k) z = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, sum_dbarDir_cofactorField hρ, mul_zero]
  rw [e1, e2, add_zero, sub_zero]

/-- **Stokes for `d(F dG) ∧ ddᶜρ₁ ∧ ⋯ ∧ ddᶜρₘ` on `ℂᵐ⁺¹`**, `F` compactly supported:
`∫ ∑ⱼₖ (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF) Cⱼₖ = 0`. -/
theorem integral_pairMatrix_cofactor_eq_zero (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    {F G : ComplexModel (m + 1) → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) :
    ∫ z, ∑ j, ∑ k, pairMatrix F G z j k * cofactorField ρ j k z = 0 := by
  have hFc' : ContDiff ℝ ∞ (fun y => (F y : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hGc : ContDiff ℝ ∞ (fun y => (G y : ℂ)) := Complex.ofRealCLM.contDiff.comp hG
  have hFcs : HasCompactSupport (fun y => (F y : ℂ)) := hFc.comp_left Complex.ofReal_zero
  have hsm1 (j k : Fin (m + 1)) : ContDiff ℝ ∞ (fun y => (F y : ℂ) *
      (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) y * cofactorField ρ j k y)) :=
    hFc'.mul ((contDiff_wirt hGc).mul (contDiff_cofactorField hρ j k))
  have hsm2 (j k : Fin (m + 1)) : ContDiff ℝ ∞ (fun y => (F y : ℂ) *
      (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) y *
        cofactorField ρ j k y)) :=
    hFc'.mul ((contDiff_wirt hGc).mul (contDiff_cofactorField hρ j k))
  have hc1 (j k : Fin (m + 1)) : HasCompactSupport (fun y => (F y : ℂ) *
      (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) y * cofactorField ρ j k y)) :=
    hFcs.mul_right
  have hc2 (j k : Fin (m + 1)) : HasCompactSupport (fun y => (F y : ℂ) *
      (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) y *
        cofactorField ρ j k y)) :=
    hFcs.mul_right
  have hi (c : ℂ) (v : ComplexModel (m + 1)) {H : ComplexModel (m + 1) → ℂ}
      (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) : Integrable (wirt c v H) :=
    (contDiff_wirt hH).continuous.integrable_of_hasCompactSupport (HasCompactSupport.wirt hHc c v)
  have hik (j k : Fin (m + 1)) : Integrable (fun z =>
      wirt (-Complex.I) (coordinateVector j) (fun y => (F y : ℂ) *
          (wirt Complex.I (coordinateVector k) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z -
        wirt Complex.I (coordinateVector k) (fun y => (F y : ℂ) *
          (wirt (-Complex.I) (coordinateVector j) (fun y => (G y : ℂ)) y *
            cofactorField ρ j k y)) z) :=
    (hi _ _ (hsm1 j k) (hc1 j k)).sub (hi _ _ (hsm2 j k) (hc2 j k))
  simp_rw [pairMatrix_cofactor_eq_sum_wirt hρ hF hG]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hik j k]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hik j k]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_sub (hi _ _ (hsm1 j k) (hc1 j k)) (hi _ _ (hsm2 j k) (hc2 j k)),
    integral_wirt_eq_zero _ ((hsm1 j k).of_le (by simp)) (hc1 j k),
    integral_wirt_eq_zero _ ((hsm2 j k).of_le (by simp)) (hc2 j k), sub_zero]

end Euclid

/-! ### The normalized matrix of `Π₁₁ (dF ∧ dG)` -/

section Matrix

variable {n : ℕ}

theorem wirt_ofReal_apply {F : ComplexModel n → ℝ} {z : ComplexModel n}
    (hF : DifferentiableAt ℝ F z) (c : ℂ) (v : ComplexModel n) :
    wirt c v (fun y => (F y : ℂ)) z =
      ((fderiv ℝ F z v : ℂ) + c * (fderiv ℝ F z (Complex.I • v) : ℂ)) / 2 := by
  have hc : fderiv ℝ (fun y => (F y : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ F z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  simp only [wirt, hc, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

open ClosedProductCurrents in
/-- **The coefficient matrix of `Π₁₁ (dF ∧ dG)`** is `-2πi (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF)`. -/
theorem normalizedHermitianMatrix_pi11_eq {F G : ComplexModel n → ℝ} {z : ComplexModel n}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) {A : RealForm n 2}
    (hA : ∀ u v, A ![u, v] =
      fderiv ℝ F z u * fderiv ℝ G z v - fderiv ℝ F z v * fderiv ℝ G z u) :
    normalizedHermitianMatrix (pi11 A) =
      (-2 * (Real.pi : ℂ) * Complex.I) • pairMatrix F G z := by
  ext j k
  have hII : Complex.I • Complex.I • coordinateVector k = -(coordinateVector k : ComplexModel n)
    := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [normalizedHermitianMatrix, pi11_apply, hII, hA, map_neg, Matrix.smul_apply,
    pairMatrix, wirt_ofReal_apply hF, wirt_ofReal_apply hG, smul_eq_mul]
  push_cast
  ring_nf
  rw [Complex.I_sq, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq, neg_one_mul]]
  ring

end Matrix

/-! ### Cut-offs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function smooth on an open set, multiplied by a smooth function supported in it, is
smooth everywhere. -/
theorem contDiff_mul_of_tsupport_subset {D : Set E} (hD : IsOpen D) {ψ ρ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψD : tsupport ψ ⊆ D) (hρ : ContDiffOn ℝ ∞ ρ D) :
    ContDiff ℝ ∞ (fun z => ψ z * ρ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ D
  · exact hψ.contDiffAt.mul (hρ.contDiffAt (hD.mem_nhds hz))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hψD h)] with y hy
    simp [hy]

end Cutoff

/-! ### The density in a chart where the slots have potentials -/

section Algebra

variable {m : ℕ}

open ClosedProductCurrents

theorem pairMatrix_eq_zero_of_eventuallyEq {n : ℕ} {F G : ComplexModel n → ℝ}
    {z : ComplexModel n} (hF : F =ᶠ[𝓝 z] 0) : pairMatrix F G z = 0 := by
  have h0 : fderiv ℝ (fun y => (F y : ℂ)) z = 0 := by
    have hc : (fun y => (F y : ℂ)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [hF] with y hy
      simp [hy]
    rw [hc.fderiv_eq, fderiv_const_apply]
  ext j k
  simp [pairMatrix, wirt, h0]

theorem swap_succ_ne (i₀ : Fin (m + 1)) (j : Fin m) : Equiv.swap 0 i₀ j.succ ≠ i₀ := by
  intro h
  have : Equiv.swap 0 i₀ j.succ = Equiv.swap 0 i₀ 0 := by rw [h, Equiv.swap_apply_left]
  exact Fin.succ_ne_zero j ((Equiv.swap 0 i₀).injective this)

/-- Moving the distinguished slot `i₀` to the front. -/
theorem actualMixedTopDensity_update_eq {θ : Fin (m + 1) → RealForm (m + 1) 2}
    (hθ : ∀ i, IsOneOne (θ i)) (i₀ : Fin (m + 1)) {A : RealForm (m + 1) 2} (hA : IsOneOne A) :
    actualMixedTopDensity (Function.update θ i₀ A) =
      (mixedCoefficient (Fin.cons (normalizedHermitianMatrix A)
        (fun j : Fin m => normalizedHermitianMatrix (θ (Equiv.swap 0 i₀ j.succ))) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re / Real.pi ^ (m + 1) := by
  classical
  have hslots : ∀ i, IsOneOne (Function.update θ i₀ A i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa using hA
    · simpa [Function.update_of_ne h] using hθ i
  have hfun : (fun i => normalizedHermitianMatrix (Function.update θ i₀ A (Equiv.swap 0 i₀ i))) =
      (Fin.cons (normalizedHermitianMatrix A)
        (fun j : Fin m => normalizedHermitianMatrix (θ (Equiv.swap 0 i₀ j.succ))) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Equiv.swap_apply_left]
    · simp [Function.update_of_ne (swap_succ_ne i₀ j)]
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity _ hslots,
    ← normalizedMixedTopDensity_perm (Function.update θ i₀ A) (Equiv.swap 0 i₀)]
  simp only [normalizedMixedTopDensity]
  rw [hfun]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- **The density of `Π₁₁ d(f dg) ∧ ddᶜρ₁ ∧ ⋯` in a chart**, the slot `i₀` carrying
`Π₁₁ d(f dg)` and the others `ddᶜρᵢ`. -/
theorem actualMixedTopDensity_closedSlots_eq (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
    (i₀ : Fin (m + 1)) {f g : M → ℝ} (hf : ChartSmooth (n := m + 1) f)
    (hg : ChartSmooth (n := m + 1) g) (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) {ρ : Fin (m + 1) → ComplexModel (m + 1) → ℝ}
    (hρ : ∀ i, ContDiffAt ℝ 2 (ρ i) z) (hθρ : ∀ i, smoothDDC (ρ i) z = (θ i).val.coeff e z) :
    actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
        (pi11 ((exactPair f g hf hg).coeff e z))) =
      ((-2 * (Real.pi : ℂ) * Complex.I) * ∑ j, ∑ k,
        pairMatrix (fun y => f (e.val.symm y)) (fun y => g (e.val.symm y)) z j k *
          cofactor (fun i : Fin m => complexHessian (ρ (Equiv.swap 0 i₀ i.succ)) z) j k).re /
        Real.pi ^ (m + 1) := by
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hF : DifferentiableAt ℝ (fun y => f (e.val.symm y)) z :=
    ((hf e).contDiffAt hnhds).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (fun y => g (e.val.symm y)) z :=
    ((hg e).contDiffAt hnhds).differentiableAt (by simp)
  rw [actualMixedTopDensity_update_eq (fun i => (θ i).2.2 e z hz) i₀ (isOneOne_pi11 _),
    normalizedHermitianMatrix_pi11_eq hF hG (exactPair_coeff_apply f g hf hg e hz),
    MixedHessian.mixedCoefficient_cons]
  simp only [← hθρ, normalizedHermitianMatrix_smoothDDC (hρ _), Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

end Algebra

section SlotChartIntegral

open ClosedProductCurrents GlobalSlotStokes

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- **Stokes in one slot chart.**  If `f` is supported in a chart domain on which every slot
`θᵢ` has a smooth potential, the density of `Π₁₁ d(f dg) ∧ θ₁ ∧ ⋯` (the slot `i₀` replaced by
`Π₁₁ d(f dg)`) has integral zero over the domain. -/
theorem setIntegral_closedSlots_eq_zero {θ : Fin N → ClosedRealOneOneForm N M}
    {κ : ClosedRealOneOneForm N M} (J : SlotChart θ κ) (i₀ : Fin N) {f g : M → ℝ}
    (hf : ChartSmooth (n := N) f) (hg : ChartSmooth (n := N) g)
    (hfJ : tsupport f ⊆ (J.source : Set M)) (hfK : IsCompact (tsupport f)) :
    ∫ z in (J.domain : Set (ComplexModel N)), actualMixedTopDensity
      (Function.update (fun i => (θ i).val.coeff J.chart z) i₀
        (pi11 ((exactPair f g hf hg).coeff J.chart z))) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos i₀.pos).symm⟩
  classical
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel (m + 1))) ⊆ e.val.target := J.domain_le_target
  obtain ⟨φ, hφs, hφc, hφD, hφeq, -⟩ := J.exists_coordinate_test hf hfJ hfK
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := D) hφc hφD
  set ψ : ComplexModel (m + 1) → ℝ := ⇑χ with hψ
  have hψs : ContDiff ℝ ∞ ψ := χ.contDiff
  have hψD : tsupport ψ ⊆ (D : Set (ComplexModel (m + 1))) := χ.tsupport_subset
  set Gt : ComplexModel (m + 1) → ℝ := fun z => ψ z * g (e.val.symm z) with hGt
  have hGts : ContDiff ℝ ∞ Gt :=
    contDiff_mul_of_tsupport_subset D.isOpen hψs hψD ((hg e).mono hDt)
  set ρt : Fin (m + 1) → ComplexModel (m + 1) → ℝ := fun i z => ψ z * J.potential i z with hρt
  have hρts : ∀ i, ContDiff ℝ ∞ (ρt i) := fun i =>
    contDiff_mul_of_tsupport_subset D.isOpen hψs hψD (J.localPotential i).2.2.1
  set ρ' : Fin m → ComplexModel (m + 1) → ℝ := fun j => ρt (Equiv.swap 0 i₀ j.succ) with hρ'
  have hρ's : ∀ j, ContDiff ℝ ∞ (ρ' j) := fun j => hρts _
  set c : ℂ := -2 * (Real.pi : ℂ) * Complex.I with hc
  set X : ComplexModel (m + 1) → ℂ := fun z =>
    ∑ j, ∑ k, pairMatrix φ Gt z j k * cofactorField ρ' j k z with hX
  have hX0 : ∀ z, z ∉ tsupport φ → X z = 0 := by
    intro z hz
    simp [hX, pairMatrix_eq_zero_of_eventuallyEq (G := Gt) (notMem_tsupport_iff_eventuallyEq.mp
      hz)]
  -- the pointwise identity on the domain
  have hpt : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
        (pi11 ((exactPair f g hf hg).coeff e z))) = (c * X z).re / Real.pi ^ (m + 1) := by
    intro z hz
    have hzt := hDt hz
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hρC : ∀ i, ContDiffAt ℝ 2 (J.potential i) z := fun i =>
      ((J.localPotential i).2.2.1.contDiffAt (D.isOpen.mem_nhds hz)).of_le h2
    rw [actualMixedTopDensity_closedSlots_eq θ i₀ hf hg e hzt hρC
      fun i => (J.localPotential i).2.2.2 hz]
    congr 3
    by_cases hzφ : z ∈ tsupport φ
    · have hψ1 : ∀ᶠ y in 𝓝 z, ψ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hzφ)
      have hF : (fun y => (f (e.val.symm y) : ℂ)) =ᶠ[𝓝 z] fun y => (φ y : ℂ) := by
        filter_upwards [D.isOpen.mem_nhds hz] with y hy
        rw [hφeq hy]
      have hG : (fun y => (g (e.val.symm y) : ℂ)) =ᶠ[𝓝 z] fun y => (Gt y : ℂ) := by
        filter_upwards [hψ1] with y hy
        simp [hGt, hy]
      have hpair : pairMatrix (fun y => f (e.val.symm y)) (fun y => g (e.val.symm y)) z =
          pairMatrix φ Gt z := by
        ext j k
        simp only [pairMatrix, wirt, hF.fderiv_eq, hG.fderiv_eq]
      have hhess : ∀ i, complexHessian (J.potential i) z = complexHessian (ρt i) z := by
        intro i
        have hloc : J.potential i =ᶠ[𝓝 z] ρt i := by
          filter_upwards [hψ1] with y hy
          simp [hρt, hy]
        rw [← normalizedHermitianMatrix_smoothDDC (hρC i),
          ← normalizedHermitianMatrix_smoothDDC ((hρts i).contDiffAt.of_le h2),
          smoothDDC_congr hloc]
      simp only [hpair, hhess, hX, cofactorField, hρ']
    · have hφ0 := notMem_tsupport_iff_eventuallyEq.mp hzφ
      have hF0 : (fun y => f (e.val.symm y)) =ᶠ[𝓝 z] 0 := by
        filter_upwards [D.isOpen.mem_nhds hz, hφ0] with y hy hy0
        have h1 : φ y = f (e.val.symm y) := hφeq hy
        rw [← h1]
        exact hy0
      rw [hX0 z hzφ, pairMatrix_eq_zero_of_eventuallyEq hF0]
      simp
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt]
  have hXc : Continuous X := by
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    refine Continuous.mul ?_ (contDiff_cofactorField hρ's j k).continuous
    have hφc' : ContDiff ℝ ∞ (fun y => (φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hφs
    have hGc' : ContDiff ℝ ∞ (fun y => (Gt y : ℂ)) := Complex.ofRealCLM.contDiff.comp hGts
    simp only [pairMatrix]
    exact ((contDiff_wirt hφc').continuous.mul (contDiff_wirt hGc').continuous).sub
      ((contDiff_wirt hGc').continuous.mul (contDiff_wirt hφc').continuous)
  have hXcs : HasCompactSupport X :=
    hφc.mono' fun z hz => by_contra fun h => hz (hX0 z h)
  have hXi : Integrable X := hXc.integrable_of_hasCompactSupport hXcs
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [hX0 z fun h => hz (hφD h), mul_zero, Complex.zero_re, zero_div]]
  rw [integral_div]
  have hre : ∫ z, (c * X z).re = (∫ z, c * X z).re :=
    integral_re (𝕜 := ℂ) (hXi.const_mul c)
  rw [hre, integral_const_mul, hX, integral_pairMatrix_cofactor_eq_zero hρ's hφs hGts hφc]
  simp

end SlotChartIntegral

/-! ### On the manifold -/

section Global

open ClosedProductCurrents GlobalSlotStokes ChartPartition IntegrationCurrent TopDegreeDensity
  SmoothMixedMeasureDensity GlobalNonPluripolar ProductTestForms CurrentTraceMeasure
  FirstPass.PositiveClasses

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

omit [IsComplexManifold N M] in
theorem eq_vec_two' (w : Fin 2 → ComplexModel N) : w = ![w 0, w 1] := by
  funext i
  fin_cases i <;> rfl

/-- `d(f dg)` vanishes at a point near which `f` vanishes. -/
theorem exactPair_coeff_eq_zero {f g : M → ℝ} (hf : ChartSmooth (n := N) f)
    (hg : ChartSmooth (n := N) g) {e : ComplexChart N M} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (h0 : (fun y => f (e.val.symm y)) =ᶠ[𝓝 z] 0) :
    (exactPair f g hf hg).coeff e z = 0 := by
  have hd : fderiv ℝ (fun y => f (e.val.symm y)) z = 0 := by
    rw [h0.fderiv_eq]
    exact fderiv_const_apply 0
  ext w
  rw [eq_vec_two' w, exactPair_coeff_apply f g hf hg e hz, hd]
  simp

omit [IsComplexManifold N M] in
/-- A function vanishing near `x` vanishes near `e x` in every chart at `x`. -/
theorem chart_eventuallyEq_zero {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) {e : ComplexChart N M}
    (hxe : x ∈ e.val.source) : (fun y => f (e.val.symm y)) =ᶠ[𝓝 (e.val x)] 0 := by
  have h := notMem_tsupport_iff_eventuallyEq.mp hx
  have hc : ContinuousAt e.val.symm (e.val x) := e.val.continuousAt_symm (e.val.map_source hxe)
  rw [ContinuousAt, e.val.left_inv hxe] at hc
  exact hc.eventually h

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Change of variables** for the integral of a continuous function against the global mixed
measure of smooth semipositive forms, on the inverse image of a measurable piece of a chart. -/
theorem setIntegral_image_eq
    {θ : Fin N → ClosedRealOneOneForm N M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart N M)
    {K : Set (ComplexModel N)} (hK : MeasurableSet K) (hKe : K ⊆ e.val.target)
    {G : M → ℝ} (hG : Continuous G) :
    ∫ x in e.val.symm '' K, G x ∂(globalMixedMeasure θ (fun _ _ => 0) hθ) =
      ∫ z in K, (chartDensity θ e z).toReal * G (e.val.symm z) := by
  have hae : AEMeasurable e.val.symm ((volume.restrict K).withDensity (chartDensity θ e)) :=
    ((e.val.continuousOn_symm.mono hKe).aemeasurable hK).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [restrict_image_eq_map hθ e hK hKe, integral_map hae hG.aestronglyMeasurable]
  have hd : AEMeasurable (chartDensity θ e) (volume.restrict K) :=
    ((continuousOn_chartDensity θ e).mono hKe).aemeasurable hK
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- **Stokes on the manifold, chart-supported case.**  Let `Φ` be a top-degree form whose
density is, in every chart, the mixed density of the slots `θ` with the slot `i₀` replaced by
`Π₁₁ d(f dg)`.  If `f` is supported in a slot chart, then `∫_M Φ = 0`. -/
theorem integral_topRatio_eq_zero_of_slotChart (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} {κ : ClosedRealOneOneForm N M} (J : SlotChart θ κ)
    (i₀ : Fin N) {f g : M → ℝ} (hf : ChartSmooth (n := N) f) (hg : ChartSmooth (n := N) g)
    (hfJ : tsupport f ⊆ (J.source : Set M)) (hfK : IsCompact (tsupport f))
    (Φ : SmoothRealForm N M (2 * N))
    (hΦ : ∀ (e : ComplexChart N M) z, z ∈ e.val.target → topDensity (Φ.coeff e z) =
      actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
        (pi11 ((exactPair f g hf hg).coeff e z)))) :
    ∫ x, topRatio w.form.val Φ x ∂(kahlerVolume w) = 0 := by
  classical
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel N)) ⊆ e.val.target := J.domain_le_target
  -- `Φ` vanishes off the support of `f`
  have hzero : ∀ x, x ∉ (J.source : Set M) → topRatio w.form.val Φ x = 0 := by
    intro x hx
    have hxf : x ∉ tsupport f := fun h => hx (hfJ h)
    have hxs := mem_complexChartAt_source (n := N) x
    have hz := (complexChartAt (n := N) x).val.map_source hxs
    have hslot : pi11 ((exactPair f g hf hg).coeff (complexChartAt (n := N) x)
        ((complexChartAt (n := N) x).val x)) = 0 := by
      rw [exactPair_coeff_eq_zero hf hg hz (chart_eventuallyEq_zero hxf hxs)]
      ext v
      simp [pi11]
    simp only [topRatio, chartRatio]
    rw [hΦ _ _ hz, hslot, ← actualMixedTopDensityMultilinear_apply,
      actualMixedTopDensityMultilinear.map_coord_zero i₀ (by simp), zero_div]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have himage : (J.source : Set M) = e.val.symm '' D := by
    rw [e.val.symm_image_eq_source_inter_preimage hDt]
    rfl
  have hω : ∀ _ : Fin N, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin N => w.form) (fun _ _ => 0) hω := rfl
  rw [himage, hvol, setIntegral_image_eq hω e D.isOpen.measurableSet hDt
    (continuous_topRatio w.isKahler.1 Φ)]
  have hpt : ∀ z ∈ (D : Set (ComplexModel N)),
      (chartDensity (fun _ : Fin N => w.form) e z).toReal * topRatio w.form.val Φ (e.val.symm z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
          (pi11 ((exactPair f g hf hg).coeff e z))) := by
    intro z hz
    have hzt : z ∈ e.val.target := hDt hz
    have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hR : topRatio w.form.val Φ (e.val.symm z) = chartRatio w.form.val Φ e z := by
      rw [topRatio_eq_chartRatio w.isKahler.1 Φ hx, e.val.right_inv hzt]
    have hden : topDensity ((formPow w.form.val N).coeff e z) =
        actualMixedTopDensity fun _ => w.form.val.coeff e z := by
      rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
    have hpos := topDensity_formPow_pos w.isKahler.1 hzt
    rw [hR, chartRatio, chartDensity, ← hden, ENNReal.toReal_ofReal hpos.le,
      mul_div_cancel₀ _ hpos.ne', hΦ e z hzt]
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt]
  exact setIntegral_closedSlots_eq_zero J i₀ hf hg hfJ hfK

/-- **Stokes on the manifold** `∫_M Π₁₁ d(f dg) ∧ θ₁ ∧ ⋯ = 0` for closed real `(1,1)`-forms
`θᵢ`: for a family `Φ f` of top-degree forms whose densities are, in every chart, the mixed
densities of the slots `θ` with the slot `i₀` replaced by `Π₁₁ d(f dg)`, `∫_M Φ f = 0`
(partition of unity subordinate to slot charts, then `integral_topRatio_eq_zero_of_slotChart`). -/
theorem integral_topRatio_eq_zero (w : KahlerBackground N M) (θ : Fin N → ClosedRealOneOneForm N M)
    (i₀ : Fin N) {g : M → ℝ} (hg : ChartSmooth (n := N) g)
    (Φ : (f : M → ℝ) → ChartSmooth (n := N) f → SmoothRealForm N M (2 * N))
    (hΦ : ∀ (f : M → ℝ) (hf : ChartSmooth (n := N) f) (e : ComplexChart N M) z,
      z ∈ e.val.target → topDensity ((Φ f hf).coeff e z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
          (pi11 ((exactPair f g hf hg).coeff e z))))
    {f : M → ℝ} (hf : ChartSmooth (n := N) f) :
    ∫ x, topRatio w.form.val (Φ f hf) x ∂(kahlerVolume w) = 0 := by
  classical
  obtain ⟨r, χ, idx, hχs, -, hχS, hχK, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := N)
      (fun J : SlotChart θ w.form => J.source) fun x => SlotChart.exists_mem_source θ w.form x
  have hχf : ∀ a, ChartSmooth (n := N) (fun x => χ a x * f x) := fun a =>
    chartSmooth_mul (hχs a) hf
  have hpiece : ∀ a, ∫ x, topRatio w.form.val (Φ _ (hχf a)) x ∂(kahlerVolume w) = 0 := fun a =>
    integral_topRatio_eq_zero_of_slotChart w (idx a) i₀ (hχf a) hg
      (tsupport_mul_subset_left.trans (hχS a))
      ((hχK a).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left) _
      (hΦ _ (hχf a))
  have hsplitc : ∀ (e : ComplexChart N M) z, z ∈ e.val.target →
      chartRatio w.form.val (Φ f hf) e z = ∑ a, chartRatio w.form.val (Φ _ (hχf a)) e z := by
    intro e z hz
    have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
    have hfun : (fun y => f (e.val.symm y)) =
        fun y => ∑ a, (fun y => χ a (e.val.symm y) * f (e.val.symm y)) y := by
      funext y
      rw [← Finset.sum_mul, hsum, one_mul]
    have hfd : fderiv ℝ (fun y => f (e.val.symm y)) z =
        ∑ a, fderiv ℝ (fun y => χ a (e.val.symm y) * f (e.val.symm y)) z := by
      rw [hfun, fderiv_fun_sum fun a _ =>
        (((hχf a) e).contDiffAt hnhds).differentiableAt (by simp)]
    have hcoeff : (exactPair f g hf hg).coeff e z =
        ∑ a, (exactPair _ g (hχf a) hg).coeff e z := by
      ext w
      rw [eq_vec_two' w, ContinuousAlternatingMap.sum_apply, exactPair_coeff_apply f g hf hg e hz]
      simp only [exactPair_coeff_apply _ g (hχf _) hg e hz, hfd, _root_.sum_apply,
        Finset.sum_mul, ← Finset.sum_sub_distrib]
    have hΦa : ∀ a, topDensity ((Φ _ (hχf a)).coeff e z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
          (pi11 ((exactPair _ g (hχf a) hg).coeff e z))) := fun a => hΦ _ (hχf a) e z hz
    have hpi : pi11 ((exactPair f g hf hg).coeff e z) =
        ∑ a, pi11 ((exactPair _ g (hχf a) hg).coeff e z) := by
      rw [hcoeff, ← pi11CLM_apply, map_sum]
      rfl
    unfold chartRatio
    rw [← Finset.sum_div, hΦ f hf e z hz]
    simp only [hΦa]
    rw [hpi, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_sum]
    rfl
  have hsplit : ∀ x, topRatio w.form.val (Φ f hf) x =
      ∑ a, topRatio w.form.val (Φ _ (hχf a)) x := fun x =>
    hsplitc _ _ ((complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x))
  simp_rw [hsplit]
  rw [integral_finsetSum _ fun a _ => integrable_topRatio w _]
  exact Finset.sum_eq_zero fun a _ => hpiece a

end Global

/-! ### Closedness of the smooth currents -/

section SmoothCurrent

open ClosedProductCurrents ProductTestForms PositiveProductCurrents IntegrationCurrent
  TopDegreeDensity SmoothCurrentTraceMeasure FirstPass.PositiveClasses

section Coeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The coefficients of the closed test form** `Π₁₁ d(f dg) ∧ β₀ ∧ ⋯ ∧ β_{k-1}`. -/
theorem closedTestForm_coeff {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) (e : ComplexChart n M) (z : ComplexModel n),
      ((closedTestForm f g hf hg k β : testSpace n M (k + 1)) :
          SmoothRealForm n M (2 * (k + 1))).coeff e z =
        wedgeProd (k + 1) (Fin.cons (pi11 ((exactPair f g hf hg).coeff e z))
          fun j => (β j).val.coeff e z)
  | 0, _, _, _ => rfl
  | k + 1, β, e, z => by
    change coordinateWedge (((closedTestForm f g hf hg k fun j => β j.castSucc :
        testSpace n M (k + 1)) : SmoothRealForm n M (2 * (k + 1))).coeff e z)
      ((β (Fin.last k)).val.coeff e z) = _
    rw [closedTestForm_coeff hf hg k, ← wedgeProd_snoc, ← Fin.cons_snoc_eq_snoc_cons]
    congr 2
    exact Fin.snoc_init_self (fun j => (β j).val.coeff e z)

end Coeff

variable {q p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + p)) M]
  [IsComplexManifold (q + p) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The smooth currents `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` are closed** (for closed real `(1,1)`-forms
`γⱼ`, no positivity needed): `∫_M Π₁₁ d(f dg) ∧ β₀ ∧ ⋯ ∧ β_{k-1} ∧ γ₀ ∧ ⋯ ∧ γ_{p-1} = 0`. -/
theorem isClosedCurrent_smoothCurrent (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M) : IsClosedCurrent (smoothCurrent w γ) := by
  classical
  rcases q with _ | k
  · trivial
  intro f g hf hg β
  rw [smoothCurrent_apply, integrationCurrent_apply]
  set θ : Fin (k + 1 + p) → ClosedRealOneOneForm (k + 1 + p) M :=
    Fin.append (Fin.cons w.form β) γ with hθ
  set i₀ : Fin (k + 1 + p) := Fin.castAdd p 0 with hi₀
  refine integral_topRatio_eq_zero w θ i₀ hg (fun f hf =>
    ((chainTestLM p (fun j => (γ j).val) (fun j => (γ j).2.2) (k + 1)
      (closedTestForm f g hf hg k β) : testSpace (k + 1 + p) M (k + 1 + p)) :
        SmoothRealForm (k + 1 + p) M (2 * (k + 1 + p)))) ?_ hf
  intro f' hf' e z _
  rw [chainTestLM_coeff p _ _ (k + 1) _ e z (closedTestForm_coeff hf' hg k β e z),
    topDensity_wedgeProd]
  congr 1
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [Fin.append_left]
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [hi₀]
    · have hne : Fin.castAdd p j.succ ≠ i₀ := by
        rw [hi₀]
        exact fun h => Fin.succ_ne_zero j (Fin.castAdd_inj.mp h)
      rw [Function.update_of_ne hne, hθ, Fin.append_left]
      simp
  · rw [Fin.append_right]
    have hne : Fin.natAdd (k + 1) b ≠ i₀ := by
      rw [hi₀]
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [Function.update_of_ne hne, hθ, Fin.append_right]

/-- **Closedness on a manifold of dimension `N = q + p`.** -/
theorem isClosedCurrent_smoothCurrentOf {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] (w : KahlerBackground N M) {q p : ℕ} (h : q + p = N)
    (γ : Fin p → ClosedRealOneOneForm N M) : IsClosedCurrent (smoothCurrentOf w h γ) := by
  subst h
  exact isClosedCurrent_smoothCurrent w γ

end SmoothCurrent

end SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness
