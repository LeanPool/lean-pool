/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingSplitIntegrated
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The `z` integration by parts of `eq:aniso:closure:mixed`

The mixed summand of the tested vortex-stretching term is

`I = ∫ χ² (∂_r u_z) ω_r ω_z dx`.

Off the axis `ω_r = -∂_z u_θ` (`eq:aniso:vorticity`, `curlComp_zero_meridional`), and the
axis is Lebesgue-null, so `I = -∫ χ² (∂_r u_z) (∂_z u_θ) ω_z dx`.  Integrating by parts in
the vertical direction moves `∂_z` off the swirl:

`I = ∫ u_θ ∂_z(χ² (∂_r u_z) ω_z) dx`,

which is `eq:aniso:closure:mixed`.  There is no boundary term because the factor carrying
the cutoff is compactly supported.

Every quantity here is a cylindrical scalar, read at the meridional representative
`meridional (polarR x) (x 2)` of `x`.  The representative map does not move the vertical
coordinate, so such a composite has a vertical **line** derivative at every point — including
on the axis, where the representative map is not differentiable — and that line derivative is
the vertical derivative of the meridional quantity at the representative.  Mathlib's
integration by parts for line derivatives is exactly what this needs.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Vertical line derivatives of meridional quantities -/

/-- Shifting a point vertically does not change its polar radius. -/
theorem polarR_add_smul_basisVec_two (x : Vec3) (s : ℝ) :
    polarR (x + s • (basisVec 2 : Vec3)) = polarR x := by
  unfold polarR
  congr 1
  have h0 : (x + s • (basisVec 2 : Vec3)) 0 = x 0 := by simp [basisVec]
  have h1 : (x + s • (basisVec 2 : Vec3)) 1 = x 1 := by simp [basisVec]
  rw [h0, h1]

/-- Shifting a point vertically shifts its vertical coordinate. -/
theorem apply_two_add_smul_basisVec_two (x : Vec3) (s : ℝ) :
    (x + s • (basisVec 2 : Vec3)) 2 = x 2 + s := by simp [basisVec]

/-- A vertical shift of a meridional point is the meridional point of the shifted height. -/
theorem meridional_add_smul_basisVec_two (r z s : ℝ) :
    meridional r (z + s) = meridional r z + s • (basisVec 2 : Vec3) := by
  funext i
  fin_cases i <;> simp [meridional, basisVec]

/-- A meridional quantity composed with the representative map has a vertical line derivative
at every point, namely the vertical derivative of the quantity at the representative. -/
theorem hasLineDerivAt_comp_polarRRep {F : Vec3 → ℝ} {x : Vec3}
    (hF : DifferentiableAt ℝ F (meridional (polarR x) (x 2))) :
    HasLineDerivAt ℝ (fun y : Vec3 => F (meridional (polarR y) (y 2)))
      (fderiv ℝ F (meridional (polarR x) (x 2)) (basisVec 2)) x (basisVec 2) := by
  have hline : HasLineDerivAt ℝ F
      (fderiv ℝ F (meridional (polarR x) (x 2)) (basisVec 2))
      (meridional (polarR x) (x 2)) (basisVec 2) :=
    hF.hasFDerivAt.hasLineDerivAt _
  have heq : (fun s : ℝ => F (meridional (polarR (x + s • (basisVec 2 : Vec3)))
        ((x + s • (basisVec 2 : Vec3)) 2)))
      = fun s : ℝ => F (meridional (polarR x) (x 2) + s • (basisVec 2 : Vec3)) := by
    funext s
    rw [polarR_add_smul_basisVec_two, apply_two_add_smul_basisVec_two,
      meridional_add_smul_basisVec_two]
  change HasDerivAt (fun s : ℝ => F (meridional (polarR (x + s • (basisVec 2 : Vec3)))
      ((x + s • (basisVec 2 : Vec3)) 2))) _ 0
  rw [heq]
  exact hline

/-- The Leibniz rule for line derivatives. -/
theorem hasLineDerivAt_mul {f g : Vec3 → ℝ} {f' g' : ℝ} {x v : Vec3}
    (hf : HasLineDerivAt ℝ f f' x v) (hg : HasLineDerivAt ℝ g g' x v) :
    HasLineDerivAt ℝ (fun y : Vec3 => f y * g y) (f' * g x + f x * g') x v := by
  have h := HasDerivAt.mul hf hg
  have hx : x + (0 : ℝ) • v = x := by simp
  rw [hx] at h
  exact h

/-- A constant has vanishing line derivative. -/
theorem hasLineDerivAt_const_zero (x v : Vec3) :
    HasLineDerivAt ℝ (fun _ : Vec3 => (0 : ℝ)) 0 x v :=
  hasDerivAt_const (0 : ℝ) 0

/-! ### Smoothness of the derivative slices -/

/-- A spatial derivative of the velocity slice is smooth on the unit ball. -/
theorem contDiffOn_slice_partial {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => spatialPartial (fun w => u w i) j (y, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => u (y, t) i) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_pi.1 (contDiffOn_spatialSlice hu ht) i
  exact (hcomp.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by simp)).clm_apply contDiffOn_const

/-- The vorticity slice is smooth on the unit ball. -/
theorem contDiffOn_slice_curl {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => curlComp u i (y, t)) (vec3Ball (0 : Vec3) 1) :=
  (contDiffOn_slice_partial hu (i + 2) (i + 1) ht).sub
    (contDiffOn_slice_partial hu (i + 1) (i + 2) ht)

/-- A spatial derivative of the velocity slice is differentiable inside the unit ball. -/
theorem differentiableAt_slice_partial {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {y : Vec3} (hy : y ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun y' : Vec3 => spatialPartial (fun w => u w i) j (y', t)) y :=
  ((contDiffOn_slice_partial hu i j ht).differentiableOn
    (by simp)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hy)

/-- The velocity slice is differentiable inside the unit ball. -/
theorem differentiableAt_slice_component {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {y : Vec3} (hy : y ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun y' : Vec3 => u (y', t) i) y :=
  ((contDiffOn_pi.1 (contDiffOn_spatialSlice hu ht) i).differentiableOn
    (by simp)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hy)

/-- The vorticity slice is differentiable inside the unit ball. -/
theorem differentiableAt_slice_curl {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {y : Vec3} (hy : y ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun y' : Vec3 => curlComp u i (y', t)) y :=
  ((contDiffOn_slice_curl hu i ht).differentiableOn
    (by simp)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hy)

/-! ### The factor carried by the cutoff, and its vertical derivative -/

/-- The factor `χ² (∂_r u_z) ω_z` of `eq:aniso:closure:mixed`, read at the meridional
representative of `x`. -/
@[expose] def mixedTermFactor (u : ParabolicPoint → Vec3) (χ : Vec3 → ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  χ x ^ 2 * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
    * curlComp u 2 (meridional (polarR x) (x 2), t))

/-- The vertical derivative `∂_z (χ² (∂_r u_z) ω_z)` of `eq:aniso:closure:mixed`: the cutoff
error term carrying `∂_zχ`, and the two terms carrying `∂_z∂_r u_z` and `∂_z ω_z`. -/
@[expose] def mixedTermFactorDz (u : ParabolicPoint → Vec3) (χ : Vec3 → ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  2 * χ x * fderiv ℝ χ x (basisVec 2)
      * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
        * curlComp u 2 (meridional (polarR x) (x 2), t))
    + χ x ^ 2
      * (spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)
            * curlComp u 2 (meridional (polarR x) (x 2), t)
        + spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
            * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t))

/-- The cutoff-carrying factor vanishes off the support of the cutoff. -/
theorem mixedTermFactor_eq_zero_of_notMem_tsupport {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ}
    {x : Vec3} (hx : x ∉ tsupport χ) (t : ℝ) : mixedTermFactor u χ x t = 0 := by
  unfold mixedTermFactor
  rw [image_eq_zero_of_notMem_tsupport hx]
  ring

/-- Its vertical derivative vanishes off the support of the cutoff. -/
theorem mixedTermFactorDz_eq_zero_of_notMem_tsupport {u : ParabolicPoint → Vec3}
    {χ : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport χ) (t : ℝ) :
    mixedTermFactorDz u χ x t = 0 := by
  have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hd : fderiv ℝ χ x (basisVec 2) = 0 := by
    have heq : χ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    simp [heq.fderiv_eq]
  unfold mixedTermFactorDz
  rw [hzero, hd]
  ring

/-- The cutoff-carrying factor is supported inside the support of the cutoff. -/
theorem tsupport_mixedTermFactor_subset (u : ParabolicPoint → Vec3) (χ : Vec3 → ℝ) (t : ℝ) :
    tsupport (fun x : Vec3 => mixedTermFactor u χ x t) ⊆ tsupport χ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
  by_contra hcon
  exact hx (mixedTermFactor_eq_zero_of_notMem_tsupport hcon t)

/-- **The vertical line derivative of `χ² (∂_r u_z) ω_z`.** The cutoff is globally smooth and
the two meridional factors are smooth at the representative of every point of the support of
the cutoff; off that support the factor vanishes identically nearby. -/
theorem hasLineDerivAt_mixedTermFactor {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) (x : Vec3) :
    HasLineDerivAt ℝ (fun y : Vec3 => mixedTermFactor u χ y t)
      (mixedTermFactorDz u χ x t) x (basisVec 2) := by
  by_cases hx : x ∈ tsupport χ
  · have hrep : meridional (polarR x) (x 2) ∈ vec3Ball (0 : Vec3) 1 :=
      rep_mem_vec3Ball (hχU hx)
    have hc : HasLineDerivAt ℝ χ (fderiv ℝ χ x (basisVec 2)) x (basisVec 2) :=
      ((hχ.differentiable (by simp)).differentiableAt).hasFDerivAt.hasLineDerivAt _
    have h1 : HasLineDerivAt ℝ (fun y : Vec3 => χ y ^ 2)
        (2 * χ x * fderiv ℝ χ x (basisVec 2)) x (basisVec 2) := by
      have hcc := hasLineDerivAt_mul hc hc
      have hfun : (fun y : Vec3 => χ y * χ y) = fun y : Vec3 => χ y ^ 2 := by
        funext y; ring
      have hval : fderiv ℝ χ x (basisVec 2) * χ x + χ x * fderiv ℝ χ x (basisVec 2)
          = 2 * χ x * fderiv ℝ χ x (basisVec 2) := by ring
      rw [hfun, hval] at hcc
      exact hcc
    have h2 : HasLineDerivAt ℝ
        (fun y : Vec3 => spatialPartial (fun w => u w 2) 0 (meridional (polarR y) (y 2), t))
        (spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t))
        x (basisVec 2) :=
      hasLineDerivAt_comp_polarRRep (differentiableAt_slice_partial hu 2 0 ht hrep)
    have h3 : HasLineDerivAt ℝ
        (fun y : Vec3 => curlComp u 2 (meridional (polarR y) (y 2), t))
        (spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t))
        x (basisVec 2) :=
      hasLineDerivAt_comp_polarRRep (differentiableAt_slice_curl hu 2 ht hrep)
    exact hasLineDerivAt_mul h1 (hasLineDerivAt_mul h2 h3)
  · have heq : (fun y : Vec3 => mixedTermFactor u χ y t) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      exact mixedTermFactor_eq_zero_of_notMem_tsupport hy t
    rw [mixedTermFactorDz_eq_zero_of_notMem_tsupport hx t]
    exact (hasLineDerivAt_const_zero x (basisVec 2)).congr_of_eventuallyEq heq

/-! ### Continuity and integrability of the three integrands -/

private lemma continuousOn_rep_map :
    ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2)) (vec3Ball (0 : Vec3) 1) := by
  have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
    unfold meridional
    have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
    have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
    fun_prop
  exact hc.continuousOn

private lemma mapsTo_rep_map :
    Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun _ hx => rep_mem_vec3Ball hx

private lemma continuousOn_mixedTermFactor {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => mixedTermFactor u χ x t) (vec3Ball (0 : Vec3) 1) :=
  ((hχ.pow 2).continuous.continuousOn).mul
    (((continuousOn_dvel_slice hu 2 0 ht).comp' continuousOn_rep_map mapsTo_rep_map).mul
      ((continuousOn_curl_slice hu 2 ht).comp' continuousOn_rep_map mapsTo_rep_map))

private lemma continuousOn_mixedTermFactorDz {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => mixedTermFactorDz u χ x t) (vec3Ball (0 : Vec3) 1) := by
  have hdχ : Continuous (fun x : Vec3 => fderiv ℝ χ x (basisVec 2)) := by
    have hpair : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ χ p.1) p.2) :=
      hχ.continuous_fderiv_apply (by simp)
    exact hpair.comp (continuous_id.prodMk continuous_const)
  have hA : ContinuousOn
      (fun x : Vec3 => spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_dvel_slice hu 2 0 ht).comp' continuousOn_rep_map mapsTo_rep_map
  have hWz : ContinuousOn
      (fun x : Vec3 => curlComp u 2 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_curl_slice hu 2 ht).comp' continuousOn_rep_map mapsTo_rep_map
  have hdA : ContinuousOn
      (fun x : Vec3 =>
        spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) := by
    have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (y, t))
        (vec3Ball (0 : Vec3) 1) :=
      ((contDiffOn_slice_partial hu 2 0 ht).fderiv_of_isOpen (isOpen_vec3Ball 0 1)
        (by simp)).clm_apply contDiffOn_const
    exact hsmooth.continuousOn.comp' continuousOn_rep_map mapsTo_rep_map
  have hdWz : ContinuousOn
      (fun x : Vec3 =>
        spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_dcurl_slice hu 2 2 ht).comp' continuousOn_rep_map mapsTo_rep_map
  exact ((((continuousOn_const.mul hχ.continuous.continuousOn).mul hdχ.continuousOn).mul
      (hA.mul hWz)).add
    (((hχ.pow 2).continuous.continuousOn).mul ((hdA.mul hWz).add (hA.mul hdWz))))

private lemma continuousOn_swirl_rep {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1)
      (vec3Ball (0 : Vec3) 1) :=
  (continuousOn_vel_slice hu 1 ht).comp' continuousOn_rep_map mapsTo_rep_map

private lemma continuousOn_dzswirl_rep {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn
      (fun x : Vec3 => spatialPartial (fun w => u w 1) 2 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
  (continuousOn_dvel_slice hu 1 2 ht).comp' continuousOn_rep_map mapsTo_rep_map

/-! ### `eq:aniso:closure:mixed` -/

/-- **`eq:aniso:closure:mixed`.** The mixed summand `I = ∫ χ² (∂_r u_z) ω_r ω_z` of the tested
vortex-stretching term equals `∫ u_θ ∂_z(χ² (∂_r u_z) ω_z)`: off the axis `ω_r = -∂_z u_θ`,
the axis is Lebesgue-null, and the vertical integration by parts has no boundary term because
the factor carrying the cutoff is compactly supported. -/
theorem integral_cutoff_sq_stretchMixedTerm_eq {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    (∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t)
      = ∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1 * mixedTermFactorDz u χ x t := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hfg' : Integrable (fun x : Vec3 =>
      u (meridional (polarR x) (x 2), t) 1 * mixedTermFactorDz u χ x t) := by
    refine integrable_of_cutoff hχs hχU
      ((continuousOn_swirl_rep hu ht).mul (continuousOn_mixedTermFactorDz hu hχ ht))
      (fun x hx => ?_)
    rw [mixedTermFactorDz_eq_zero_of_notMem_tsupport hx t]; ring
  have hf'g : Integrable (fun x : Vec3 =>
      spatialPartial (fun w => u w 1) 2 (meridional (polarR x) (x 2), t)
        * mixedTermFactor u χ x t) := by
    refine integrable_of_cutoff hχs hχU
      ((continuousOn_dzswirl_rep hu ht).mul (continuousOn_mixedTermFactor hu hχ ht))
      (fun x hx => ?_)
    rw [mixedTermFactor_eq_zero_of_notMem_tsupport hx t]; ring
  have hfg : Integrable (fun x : Vec3 =>
      u (meridional (polarR x) (x 2), t) 1 * mixedTermFactor u χ x t) := by
    refine integrable_of_cutoff hχs hχU
      ((continuousOn_swirl_rep hu ht).mul (continuousOn_mixedTermFactor hu hχ ht))
      (fun x hx => ?_)
    rw [mixedTermFactor_eq_zero_of_notMem_tsupport hx t]; ring
  have hibp : (∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1 * mixedTermFactorDz u χ x t)
      = -∫ x : Vec3, spatialPartial (fun w => u w 1) 2 (meridional (polarR x) (x 2), t)
          * mixedTermFactor u χ x t :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) hf'g hfg' hfg
      (fun x hx => hasLineDerivAt_comp_polarRRep
        (differentiableAt_slice_component hu 1 ht
          (rep_mem_vec3Ball (hχU (tsupport_mixedTermFactor_subset u χ t hx)))))
      (fun x _ => hasLineDerivAt_mixedTermFactor hu hχ hχU ht x)
  have hae : (fun x : Vec3 => χ x ^ 2 * stretchMixedTerm u x t)
      =ᵐ[volume] fun x : Vec3 =>
        -(spatialPartial (fun w => u w 1) 2 (meridional (polarR x) (x 2), t)
          * mixedTermFactor u χ x t) := by
    filter_upwards [ae_polarR_ne_zero] with x hx
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hzrep : ((meridional (polarR x) (x 2) : Vec3), t) ∈ unitCylinder :=
        ⟨rep_mem_vec3Ball hxb, ht⟩
      have hplane : ((meridional (polarR x) (x 2) : Vec3), t).1 1 = 0 := by
        change meridional (polarR x) (x 2) 1 = 0
        simp [meridional]
      have hr : ((meridional (polarR x) (x 2) : Vec3), t).1 0 ≠ 0 := by
        change meridional (polarR x) (x 2) 0 ≠ 0
        rw [meridional_apply_zero]; exact hx
      have hω := curlComp_zero_meridional haxi hu1 hzrep hplane hr
      unfold stretchMixedTerm mixedTermFactor
      rw [hω]
      ring
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hχU hm))
      unfold stretchMixedTerm mixedTermFactor
      rw [hχ0]
      ring
  rw [integral_congr_ae hae, integral_neg, hibp]

end CIV
