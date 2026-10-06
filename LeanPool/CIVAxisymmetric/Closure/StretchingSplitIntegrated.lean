/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingSplit
public import LeanPool.CIVAxisymmetric.Closure.AxisMeasureZero

/-!
# The tested vortex-stretching term of `eq:aniso:closure:tested`, split

The pointwise splitting `stretching_eq_stretchGTerm` of the vortex-stretching scalar
`(ω·∇u)·ω` of `eq:aniso:closure:stretch` holds off the vertical axis.  The axis is
Lebesgue-null (`ae_polarR_ne_zero`), and each of the three summands is integrable against
`χ²` because it is continuous on the unit ball and vanishes off the support of the cutoff.
Integrating therefore turns the pointwise splitting into the identity

`cutoffStretching χ u t = ∫ χ² G-term + I(t) - ∫ χ² 2 (u_θ ω_r/r) ω_θ`,

with `I(t) = ∫ χ² (∂_r u_z) ω_r ω_z` the mixed term of `eq:aniso:closure:mixed`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The mixed summand `(∂_r u_z) ω_r ω_z` of `eq:aniso:closure:stretch`, read at the
meridional representative of `x`.  Weighted by `χ²` and integrated it is the term `I` of
`eq:aniso:closure:mixed`. -/
@[expose] def stretchMixedTerm (u : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) : ℝ :=
  spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
    * curlComp u 0 (meridional (polarR x) (x 2), t)
    * curlComp u 2 (meridional (polarR x) (x 2), t)

/-- The mixed summand is continuous on the unit ball: it is built from continuous slices of
`∇u` and of the curl composed with the continuous representative map. -/
theorem continuousOn_stretchMixedTerm {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => stretchMixedTerm u x t) (vec3Ball (0 : Vec3) 1) := by
  have hrepmap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) := by
    have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
      unfold meridional
      have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
      have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
      fun_prop
    exact hc.continuousOn
  have hmaps : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun x hx => rep_mem_vec3Ball hx
  have hd20 : ContinuousOn (fun x : Vec3 => spatialPartial (fun w => u w 2) 0 (x, t))
      (vec3Ball (0 : Vec3) 1) := continuousOn_dvel_slice hu 2 0 ht
  have hc0 : ContinuousOn (fun x : Vec3 => curlComp u 0 (x, t)) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_curl_slice hu 0 ht
  have hc2 : ContinuousOn (fun x : Vec3 => curlComp u 2 (x, t)) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_curl_slice hu 2 ht
  exact ((hd20.comp' hrepmap hmaps).mul (hc0.comp' hrepmap hmaps)).mul
    (hc2.comp' hrepmap hmaps)

/-- The `χ²`-weighted mixed summand is integrable. -/
theorem integrable_cutoff_sq_stretchMixedTerm {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Integrable (fun x : Vec3 => χ x ^ 2 * stretchMixedTerm u x t) := by
  refine integrable_of_cutoff hχs hχU
    (((hχ.pow 2).continuous.continuousOn).mul (continuousOn_stretchMixedTerm hu ht))
    (fun x hx => ?_)
  rw [image_eq_zero_of_notMem_tsupport hx]; ring

/-- The `χ²`-weighted four-term part is integrable. -/
theorem integrable_cutoff_sq_stretchGTerm {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Integrable (fun x : Vec3 => χ x ^ 2 * stretchGTerm u x t) := by
  refine integrable_of_cutoff hχs hχU
    (((hχ.pow 2).continuous.continuousOn).mul (continuousOn_stretchGTerm haxi hu ht))
    (fun x hx => ?_)
  rw [image_eq_zero_of_notMem_tsupport hx]; ring

/-- The `χ²`-weighted angular summand is integrable. -/
theorem integrable_cutoff_sq_stretchAngular {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Integrable (fun x : Vec3 => χ x ^ 2 * (2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t))) := by
  have hrepmap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) := by
    have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
      unfold meridional
      have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
      have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
      fun_prop
    exact hc.continuousOn
  have hmaps : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun x hx => rep_mem_vec3Ball hx
  have hc1 : ContinuousOn (fun x : Vec3 => curlComp u 1 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) := (continuousOn_curl_slice hu 1 ht).comp' hrepmap hmaps
  refine integrable_of_cutoff hχs hχU
    (((hχ.pow 2).continuous.continuousOn).mul
      ((continuousOn_const.mul (continuousOn_stretchAngularSwirl haxi hu ht)).mul hc1))
    (fun x hx => ?_)
  rw [image_eq_zero_of_notMem_tsupport hx]; ring

/-- The `χ²`-weighted vortex-stretching integrand is integrable. -/
theorem integrable_cutoff_sq_stretching {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      vorticityField u (x, t) j * spatialPartial (fun w => u w i) j (x, t)
        * vorticityField u (x, t) i) := by
  refine integrable_of_cutoff hχs hχU
    (((hχ.pow 2).continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ =>
        continuousOn_finsetSum Finset.univ (fun j _ =>
          ((continuousOn_curl_slice hu j ht).mul
            (continuousOn_dvel_slice hu i j ht)).mul
              (continuousOn_curl_slice hu i ht)))))
    (fun x hx => ?_)
  rw [image_eq_zero_of_notMem_tsupport hx]; ring

/-- **`eq:aniso:closure:stretch`, integrated against `χ²`.** The tested vortex-stretching
term of `eq:aniso:closure:tested` is the four-term part, plus the mixed term `I` of
`eq:aniso:closure:mixed`, minus the angular term of `eq:aniso:closure:angular:bound`. -/
theorem cutoffStretching_eq_stretchGTerm_add_mixed_sub_angular {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    cutoffStretching χ u t
      = (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t)
        + (∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t)
        - ∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hG := integrable_cutoff_sq_stretchGTerm haxi hu hχ hχs hχU ht
  have hM := integrable_cutoff_sq_stretchMixedTerm hu hχ hχs hχU ht
  have hA := integrable_cutoff_sq_stretchAngular haxi hu hχ hχs hχU ht
  have hae : (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        vorticityField u (x, t) j * spatialPartial (fun w => u w i) j (x, t)
          * vorticityField u (x, t) i)
      =ᵐ[volume] fun x : Vec3 => (χ x ^ 2 * stretchGTerm u x t
        + χ x ^ 2 * stretchMixedTerm u x t)
        - χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)) := by
    filter_upwards [ae_polarR_ne_zero] with x hx
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hz : ((x : Vec3), t) ∈ unitCylinder := ⟨hxb, ht⟩
      have hpt := stretching_eq_stretchGTerm haxi hu1 hz hx
      show χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t)
            * curlComp u i (x, t) = _
      rw [hpt]
      show _ = (χ x ^ 2 * stretchGTerm u x t + χ x ^ 2 * stretchMixedTerm u x t)
        - χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t))
      unfold stretchMixedTerm
      ring
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hχU hm))
      rw [hχ0]
      ring
  show (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      vorticityField u (x, t) j * spatialPartial (fun w => u w i) j (x, t)
        * vorticityField u (x, t) i) = _
  rw [integral_congr_ae hae]
  have hsub : (∫ x : Vec3, ((χ x ^ 2 * stretchGTerm u x t + χ x ^ 2 * stretchMixedTerm u x t)
        - χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t))))
      = (∫ x : Vec3, (χ x ^ 2 * stretchGTerm u x t + χ x ^ 2 * stretchMixedTerm u x t))
        - ∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)) :=
    integral_sub (hG.add hM) hA
  have hadd : (∫ x : Vec3, (χ x ^ 2 * stretchGTerm u x t + χ x ^ 2 * stretchMixedTerm u x t))
      = (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t)
        + ∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t := integral_add hG hM
  rw [hsub, hadd]

end CIV
