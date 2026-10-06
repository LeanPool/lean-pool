/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.MixedTermIntegrationByParts
public import LeanPool.CIVAxisymmetric.Closure.AnnulusBoundsEnstrophy
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialGradPairBridge

/-!
# The `∂_zχ`-carrying error term of `eq:aniso:closure:mixed:bound` is a plain constant

`mixedTermFactorDz`'s first summand carries `∂_zχ`, hence is supported in a closed set `A` on
which the order-`≤ 2` annulus data of `lem:aniso:annulus` bounds every factor: `u_θ`, `∂_r u_z`
and `ω_z`, all read at the meridional representative, together with `χ` and `∂_zχ` themselves,
which are globally bounded because `χ` is smooth with compact support. Multiplying these
uniform bounds by the (finite, time-independent) `L¹` norm `∫ |χ| |∂_zχ|` — rather than by the
measure of `A`, which need not be tracked — bounds the whole error integral by a constant that
does not depend on `t`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The `∂_zχ`-carrying error term of `mixedTermFactorDz`, weighted by `u_θ` at the
representative, is bounded by a plain constant: it is supported in `A`, where the order-`≤ 2`
annulus data bounds `u_θ`, `∂_r u_z` and `ω_z` uniformly, and `χ`, `∂_zχ` are globally bounded. -/
theorem exists_abs_integral_swirl_mul_dzChi_error_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ} (hMu : 0 ≤ Mu)
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      |∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1
          * (2 * χ x * fderiv ℝ χ x (basisVec 2)
            * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
              * curlComp u 2 (meridional (polarR x) (x 2), t)))| ≤ C := by
  have hcontDz : Continuous (fun x : Vec3 => fderiv ℝ χ x (basisVec 2)) := by
    have hpair : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ χ p.1) p.2) :=
      hχ.continuous_fderiv_apply (by simp)
    exact hpair.comp (continuous_id.prodMk continuous_const)
  have hWeight : Continuous (fun x : Vec3 => |χ x| * |fderiv ℝ χ x (basisVec 2)|) :=
    hχ.continuous.abs.mul hcontDz.abs
  have hWeightSupp : HasCompactSupport (fun x : Vec3 => |χ x| * |fderiv ℝ χ x (basisVec 2)|) := by
    refine HasCompactSupport.intro hχs (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  have hWeightInt : Integrable (fun x : Vec3 => |χ x| * |fderiv ℝ χ x (basisVec 2)|) :=
    hWeight.integrable_of_hasCompactSupport hWeightSupp
  have hWeightNn : (0 : ℝ) ≤ ∫ x : Vec3, |χ x| * |fderiv ℝ χ x (basisVec 2)| :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨4 * Mu ^ 3 * ∫ x : Vec3, |χ x| * |fderiv ℝ χ x (basisVec 2)|, ?_, fun t ht => ?_⟩
  · exact mul_nonneg (by positivity) hWeightNn
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hpt : ∀ x : Vec3, |u (meridional (polarR x) (x 2), t) 1
        * (2 * χ x * fderiv ℝ χ x (basisVec 2)
          * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
            * curlComp u 2 (meridional (polarR x) (x 2), t)))|
      ≤ 4 * Mu ^ 3 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|) := by
    intro x
    by_cases hxA : x ∈ A
    · have hAsubx := hAsub hxA
      have hrepnorm : vec3EuclideanNorm (meridional (polarR x) (x 2)) = vec3EuclideanNorm x :=
        vec3EuclideanNorm_polarR_rep x
      have hRm : Rm < vec3EuclideanNorm (meridional (polarR x) (x 2)) := by
        rw [hrepnorm]; exact hAsubx.1
      have hRp : vec3EuclideanNorm (meridional (polarR x) (x 2)) < Rp := by
        rw [hrepnorm]; exact hAsubx.2
      have hbounds := abs_apply_and_vorticityField_le_of_multiPartial_le hbound hMu
        (meridional (polarR x) (x 2)) hRm hRp t ht
      have hswirl : |u (meridional (polarR x) (x 2), t) 1| ≤ Mu := (hbounds 1).1
      have hcurl : |curlComp u 2 (meridional (polarR x) (x 2), t)| ≤ 2 * Mu := by
        have := (hbounds 2).2
        simpa [vorticityField] using this
      have hfirst : |spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)| ≤ Mu := by
        have hmp := hbound (meridional (polarR x) (x 2)) hRm hRp t ht 2 (Pi.single 0 1)
          (by decide)
        rwa [multiPartial_single_eq_spatialPartial] at hmp
      calc |u (meridional (polarR x) (x 2), t) 1
            * (2 * χ x * fderiv ℝ χ x (basisVec 2)
              * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
                * curlComp u 2 (meridional (polarR x) (x 2), t)))|
          = |u (meridional (polarR x) (x 2), t) 1| * (2 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|))
              * (|spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)|
                * |curlComp u 2 (meridional (polarR x) (x 2), t)|) := by
            simp only [abs_mul]
            ring
        _ ≤ Mu * (2 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|)) * (Mu * (2 * Mu)) := by
            have h1 : (0:ℝ) ≤ 2 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|) := by positivity
            have h2 : (0:ℝ) ≤ |spatialPartial (fun w => u w 2) 0
                (meridional (polarR x) (x 2), t)| := abs_nonneg _
            gcongr
        _ = 4 * Mu ^ 3 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|) := by ring
    · have hz : fderiv ℝ χ x (basisVec 2) = 0 := by rw [hχA x hxA]; simp
      rw [hz]
      simp
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hrepMap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) := by
    have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
      unfold meridional
      have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
      have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
      fun_prop
    exact hc.continuousOn
  have hmapsTo : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun _ hx => rep_mem_vec3Ball hx
  have hFInt : Integrable (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1
      * (2 * χ x * fderiv ℝ χ x (basisVec 2)
        * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
          * curlComp u 2 (meridional (polarR x) (x 2), t)))) := by
    refine integrable_of_cutoff hχs (hρU.trans hρ1)
      (((continuousOn_vel_slice hu 1 htmem).comp' hrepMap hmapsTo).mul
        (((continuousOn_const.mul hχ.continuous.continuousOn).mul hcontDz.continuousOn).mul
          (((continuousOn_dvel_slice hu 2 0 htmem).comp' hrepMap hmapsTo).mul
            ((continuousOn_curl_slice hu 2 htmem).comp' hrepMap hmapsTo))))
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  calc |∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1
        * (2 * χ x * fderiv ℝ χ x (basisVec 2)
          * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
            * curlComp u 2 (meridional (polarR x) (x 2), t)))|
      ≤ ∫ x : Vec3, |u (meridional (polarR x) (x 2), t) 1
          * (2 * χ x * fderiv ℝ χ x (basisVec 2)
            * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
              * curlComp u 2 (meridional (polarR x) (x 2), t)))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, 4 * Mu ^ 3 * (|χ x| * |fderiv ℝ χ x (basisVec 2)|) :=
        integral_mono hFInt.abs (hWeightInt.const_mul _) hpt
    _ = 4 * Mu ^ 3 * ∫ x : Vec3, |χ x| * |fderiv ℝ χ x (basisVec 2)| := integral_const_mul _ _

end CIV
