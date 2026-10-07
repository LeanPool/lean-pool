/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.CartesianVorticityEquation
public import LeanPool.CIVAxisymmetric.Identities.PlaneTransfer
public import LeanPool.CIVAxisymmetric.Identities.PartialSmooth
public import LeanPool.CIVAxisymmetric.Closure.EllipticBounds
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The tested enstrophy balance `eq:aniso:closure:tested`

This file proves the differential inequality `eq:aniso:closure:tested` of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803.

Let `u` be a classical solution on the unit cylinder, `ω = curl u` its Cartesian vorticity
(`vorticityField`), and `χ` a smooth cutoff whose support is a compact subset of the unit
ball. With

`Y t = ∫ χ² |ω(·, t)|²`,  `M t = ∫ χ² |∇ω(·, t)|²`,

the vorticity equation `cartesian_vorticity_pde` tested against `χ² ω` gives

`½ Y' + M ≤ ∫ χ² (ω·∇u)·ω + C (Y + 1)`.

The three tested terms are recorded separately:

* the transport term is `∫ χ² ω·(u·∇ω) = -½ ∫ |ω|² u·∇(χ²)`; the divergence-free condition
  removes the term `χ² (div u) |ω|²`, and the right-hand side is supported where `∇χ ≠ 0`;
* the diffusion term is `∫ χ² ω·Δω = -M + ½ ∫ |ω|² Δ(χ²)`, obtained by two integrations by
  parts, so that the cutoff error only sees `ω` itself and not `∇ω`;
* the force term obeys `|∫ χ² ω·curl f| ≤ C (Y + 1)`, since `curl f` is bounded by twice the
  `C²` bound of the force.

Every integration by parts is an instance of
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`: the cutoff-carrying factor is globally
smooth with compact support, so the other factor — built from `u` and its derivatives — only
has to be differentiable on the unit ball.

This module carries the time differentiation of `Y` and the three tested terms; the resulting
differential inequality is assembled in `CIV.Closure.EnstrophyBalance`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### The cutoff-weighted quantities -/

/-- The cutoff enstrophy `Y t = ‖χ ω(·, t)‖_{L²}²` of `lem:aniso:closure`. -/
@[expose] def cutoffEnstrophy (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (vorticityField u (x, t) i) ^ 2

/-- The cutoff enstrophy dissipation `M t = ‖χ ∇ω(·, t)‖_{L²}²` of `lem:aniso:closure`. -/
@[expose] def cutoffEnstrophyDissipation (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
    (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2

/-- The tested vortex-stretching term `∫ χ² (ω·∇u)·ω` of `eq:aniso:closure:tested`. -/
@[expose] def cutoffStretching (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
    vorticityField u (x, t) j * spatialPartial (fun w => u w i) j (x, t)
      * vorticityField u (x, t) i

/-! ### Cutoff weights and fields smooth on an open set

A *weight* is a globally smooth, compactly supported scalar whose support lies inside the
open set `U` on which the velocity is smooth. Weight times `U`-smooth field is globally
continuous with compact support, hence integrable; this is what makes every integration by
parts below legitimate. -/

/-- A function continuous on an open set and vanishing outside a closed subset of it is
continuous everywhere. -/
private lemma continuous_of_continuousOn_zero_off {F : Vec3 → ℝ} {U K : Set Vec3}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hF : ContinuousOn F U)
    (hzero : ∀ x : Vec3, x ∉ K → F x = 0) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ K
  · exact hF.continuousAt (hU.mem_nhds (hKU hx))
  · have heq : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      exact hzero y hy
    exact heq.continuousAt

/-- A weight times anything vanishes outside the support of the weight. -/
private lemma weight_mul_zero_off {ψ g : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport ψ) :
    ψ x * g x = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- A weight times anything is supported inside the support of the weight. -/
private lemma tsupport_weight_mul_subset (ψ g : Vec3 → ℝ) :
    tsupport (fun x : Vec3 => ψ x * g x) ⊆ tsupport ψ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport ψ)
  by_contra hcon
  exact hx (weight_mul_zero_off hcon)

/-- A weight supported in `U` times a field continuous on `U` is continuous everywhere. -/
private lemma continuous_weight_mul {ψ g : Vec3 → ℝ} {U : Set Vec3}
    (hU : IsOpen U) (hψ : Continuous ψ) (hψU : tsupport ψ ⊆ U) (hg : ContinuousOn g U) :
    Continuous (fun x : Vec3 => ψ x * g x) :=
  continuous_of_continuousOn_zero_off hU (isClosed_tsupport ψ) hψU
    (hψ.continuousOn.mul hg) (fun _ hx => weight_mul_zero_off hx)

/-- A compactly supported weight times anything has compact support. -/
private lemma hasCompactSupport_weight_mul {ψ g : Vec3 → ℝ} (hψs : HasCompactSupport ψ) :
    HasCompactSupport (fun x : Vec3 => ψ x * g x) :=
  HasCompactSupport.intro hψs (fun _ hx => weight_mul_zero_off hx)

/-- A weight supported in `U` times a field continuous on `U` is integrable. -/
private lemma integrable_weight_mul {ψ g : Vec3 → ℝ} {U : Set Vec3}
    (hU : IsOpen U) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hg : ContinuousOn g U) : Integrable (fun x : Vec3 => ψ x * g x) :=
  (continuous_weight_mul hU hψ hψU hg).integrable_of_hasCompactSupport
    (hasCompactSupport_weight_mul hψs)

/-- A weight supported in `U` times a field smooth on `U` is smooth everywhere. -/
private lemma contDiff_weight_mul {ψ g : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψU : tsupport ψ ⊆ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport ψ
  · exact hψ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hψU hx)))
  · have heq : (fun y : Vec3 => ψ y * g y) =ᶠ[nhds x] (fun _ : Vec3 => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
      exact weight_mul_zero_off hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- A directional derivative vanishes outside the support. -/
private lemma dirDeriv_zero_off_tsupport {F : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport F)
    (j : Fin 3) : fderiv ℝ F x (basisVec j) = 0 := by
  have heq : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp [heq.fderiv_eq]

/-- A directional derivative of a smooth function is continuous. -/
private lemma continuous_dirDeriv {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin 3) :
    Continuous (fun x : Vec3 => fderiv ℝ F x (basisVec j)) := by
  have hpair : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ F p.1) p.2) :=
    hF.continuous_fderiv_apply (by simp)
  exact hpair.comp (continuous_id.prodMk continuous_const)

/-- A directional derivative of a smooth function is smooth. -/
private lemma contDiff_dirDeriv {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ F x (basisVec j)) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

/-- A directional derivative of a compactly supported function has compact support. -/
private lemma hasCompactSupport_dirDeriv {F : Vec3 → ℝ} (hFs : HasCompactSupport F) (j : Fin 3) :
    HasCompactSupport (fun x : Vec3 => fderiv ℝ F x (basisVec j)) :=
  HasCompactSupport.intro hFs (fun _ hx => dirDeriv_zero_off_tsupport hx j)

/-- A directional derivative is supported inside the support of the function. -/
private lemma tsupport_dirDeriv_subset (F : Vec3 → ℝ) (j : Fin 3) :
    tsupport (fun x : Vec3 => fderiv ℝ F x (basisVec j)) ⊆ tsupport F := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport F)
  by_contra hcon
  exact hx (dirDeriv_zero_off_tsupport hcon j)

/-- A directional derivative of a field smooth on an open set is continuous there. -/
private lemma continuousOn_dirDeriv {G : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (j : Fin 3) :
    ContinuousOn (fun x : Vec3 => fderiv ℝ G x (basisVec j)) U :=
  (hG.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const

/-- A directional derivative of a field smooth on an open set is smooth there. -/
private lemma contDiffOn_dirDeriv {G : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ G x (basisVec j)) U :=
  (hG.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- **Integration by parts against a cutoff weight.** If `F` is globally smooth with compact
support inside the open set `U` and `G` is smooth on `U`, then `∫ F ∂ⱼG = -∫ (∂ⱼF) G`. Only
`F` has to be globally smooth: `G` is differentiated only on the support of `F`. -/
private lemma integral_weight_mul_fderiv {F G : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : HasCompactSupport F) (hFU : tsupport F ⊆ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (j : Fin 3) :
    ∫ x : Vec3, F x * fderiv ℝ G x (basisVec j)
      = - ∫ x : Vec3, fderiv ℝ F x (basisVec j) * G x := by
  have hGcont : ContinuousOn G U := hG.continuousOn
  have hGd : ContinuousOn (fun x : Vec3 => fderiv ℝ G x (basisVec j)) U :=
    continuousOn_dirDeriv hU hG j
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact integrable_weight_mul hU (continuous_dirDeriv hF j) (hasCompactSupport_dirDeriv hFs j)
      ((tsupport_dirDeriv_subset F j).trans hFU) hGcont
  · exact integrable_weight_mul hU hF.continuous hFs hFU hGd
  · exact integrable_weight_mul hU hF.continuous hFs hFU hGcont
  · exact fun x _ => (hF.differentiable (by simp)).differentiableAt
  · exact fun x hx => (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hFU hx))

/-! ### Two elementary derivative rules -/

/-- The directional derivative of a product. -/
private lemma dirDeriv_mul {c d : Vec3 → ℝ} {x : Vec3} (hc : DifferentiableAt ℝ c x)
    (hd : DifferentiableAt ℝ d x) (j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => c y * d y) x (basisVec j)
      = fderiv ℝ c x (basisVec j) * d x + c x * fderiv ℝ d x (basisVec j) := by
  have h : HasFDerivAt (fun y : Vec3 => c y * d y)
      (c x • fderiv ℝ d x + d x • fderiv ℝ c x) x := hc.hasFDerivAt.mul hd.hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The directional derivative of the squared length of a three-component field. -/
private lemma dirDeriv_sumSq {a : Fin 3 → Vec3 → ℝ} {x : Vec3}
    (ha : ∀ i : Fin 3, DifferentiableAt ℝ (a i) x) (j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => ∑ i : Fin 3, (a i y) ^ 2) x (basisVec j)
      = 2 * ∑ i : Fin 3, a i x * fderiv ℝ (a i) x (basisVec j) := by
  have hsq : ∀ i : Fin 3, HasFDerivAt (fun y : Vec3 => (a i y) ^ 2)
      ((2 * a i x) • fderiv ℝ (a i) x) x := by
    intro i
    have h := ((ha i).hasFDerivAt).pow 2
    have hcoef : (2 : ℕ) • a i x ^ (2 - 1) = 2 * a i x := by
      norm_num
    rwa [hcoef] at h
  have hsum : HasFDerivAt (fun y : Vec3 => ∑ i : Fin 3, (a i y) ^ 2)
      (∑ i : Fin 3, (2 * a i x) • fderiv ℝ (a i) x) x := by
    simp only [Fin.sum_univ_three]
    exact ((hsq 0).add (hsq 1)).add (hsq 2)
  rw [hsum.fderiv]
  simp only [Fin.sum_univ_three, add_apply, smul_apply, smul_eq_mul]
  ring

/-! ### Integrating a finite sum, and integrability under a cutoff -/

/-- Exchanging a three-term sum with an integral. -/
private lemma integral_sum3 {f : Fin 3 → Vec3 → ℝ} (hf : ∀ i : Fin 3, Integrable (f i)) :
    ∫ x : Vec3, ∑ i : Fin 3, f i x = ∑ i : Fin 3, ∫ x : Vec3, f i x :=
  integral_finsetSum Finset.univ (fun i _ => hf i)

/-- A function continuous on the unit ball and vanishing off the support of the cutoff is
integrable. -/
theorem integrable_of_cutoff {χ : Vec3 → ℝ} (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {F : Vec3 → ℝ}
    (hF : ContinuousOn F (vec3Ball 0 1)) (hzero : ∀ x : Vec3, x ∉ tsupport χ → F x = 0) :
    Integrable F :=
  (continuous_of_continuousOn_zero_off (isOpen_vec3Ball 0 1) (isClosed_tsupport χ) hχU hF
    hzero).integrable_of_hasCompactSupport (HasCompactSupport.intro hχs hzero)

/-! ### The square of a cutoff -/

/-- The square of a cutoff vanishes outside its support. -/
private lemma sq_zero_off_tsupport {χ : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport χ) :
    χ x ^ 2 = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hx]; ring

/-- The square of a compactly supported cutoff has compact support. -/
private lemma hasCompactSupport_sq {χ : Vec3 → ℝ} (hχs : HasCompactSupport χ) :
    HasCompactSupport (fun x : Vec3 => χ x ^ 2) :=
  HasCompactSupport.intro hχs (fun _ hx => sq_zero_off_tsupport hx)

/-- The square of a cutoff is supported inside the support of the cutoff. -/
private lemma tsupport_sq_subset (χ : Vec3 → ℝ) :
    tsupport (fun x : Vec3 => χ x ^ 2) ⊆ tsupport χ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
  by_contra hcon
  exact hx (sq_zero_off_tsupport hcon)

/-! ### Slices of the velocity and of the vorticity

The repo's classical partial derivatives are read on a time slice: `spatialPartial g j (x, t)`
is `fderiv ℝ (fun y => g (y, t)) x (basisVec j)` by definition, and `vorticityField u z i` is
`curlComp u i z`. The proofs below work with the `fderiv` form throughout. -/

section Velocity

variable {u : ParabolicPoint → Vec3}

/-- Each Cartesian component of the curl of a smooth velocity is smooth on the cylinder. -/
private lemma contDiffOn_curlComp
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => curlComp u i z) unitCylinder :=
  (contDiffOn_spatialPartial (contDiffOn_component hu (i + 2)) (i + 1)).sub
    (contDiffOn_spatialPartial (contDiffOn_component hu (i + 1)) (i + 2))

/-- The time slices of the components of the curl are smooth on the unit ball. -/
private lemma contDiffOn_curlComp_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => curlComp u i (x, s)) (vec3Ball 0 1) :=
  contDiffOn_spatialSlice (contDiffOn_curlComp hu i) hs

/-- The time slices of the components of the velocity are smooth on the unit ball. -/
private lemma contDiffOn_velocity_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, s) i) (vec3Ball 0 1) :=
  contDiffOn_spatialSlice (contDiffOn_component hu i) hs

/-- The squared length of the vorticity is smooth on the unit ball at each time. -/
private lemma contDiffOn_sumSqVorticity_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ∑ i : Fin 3, (vorticityField u (x, s) i) ^ 2) (vec3Ball 0 1) := by
  have h : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (curlComp u i (x, s)) ^ 2) (vec3Ball 0 1) :=
    fun i => (contDiffOn_curlComp_slice hu i hs).pow 2
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, s)) ^ 2) (vec3Ball 0 1) := by
    simp only [Fin.sum_univ_three]
    exact ((h 0).add (h 1)).add (h 2)
  exact hsum

/-- The classical time derivative of the vorticity is continuous on the cylinder. -/
private lemma continuousOn_timePartial_curlComp
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContinuousOn (fun z : Vec3 × ℝ => timePartial (curlComp u i) z) unitCylinder := by
  have h : ContDiffOn ℝ ((0 : ℕ) + 1) (fun z : Vec3 × ℝ => curlComp u i z) unitCylinder :=
    (contDiffOn_curlComp hu i).of_le (by norm_num)
  exact contDiffOn_zero.mp (contDiffOn_timePartial_of_contDiffOn h)

/-- The time slice of the classical time derivative of the vorticity is continuous. -/
private lemma continuousOn_timePartial_curlComp_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => timePartial (curlComp u i) (x, s)) (vec3Ball 0 1) :=
  (continuousOn_timePartial_curlComp hu i).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ hy => ⟨hy, hs⟩)

/-- Along a fixed spatial point the vorticity has the classical time derivative. -/
private lemma hasDerivAt_curlComp_time
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {x : Vec3} {s : ℝ} (hz : ((x, s) : ParabolicPoint) ∈ unitCylinder) :
    HasDerivAt (fun σ : ℝ => curlComp u i (x, σ)) (timePartial (curlComp u i) (x, s)) s := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => curlComp u i w)
      ((x, s) : ParabolicPoint) :=
    ((contDiffOn_curlComp hu i).differentiableOn (by norm_num) (x, s) hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fun σ : ℝ => curlComp u i (x, σ)) s :=
    hjoint.comp s (hasFDerivAt_prodMk_right x s).differentiableAt
  exact hd.hasDerivAt

end Velocity

/-! ### Differentiating the enstrophy under the integral sign -/

/-- The elementary derivative rule behind the time differentiation of `Y`: for three scalar
functions of time, `(c ∑ᵢ aᵢ²)' = c (2 ∑ᵢ aᵢ aᵢ')`. -/
private lemma hasDerivAt_const_mul_sumSq {a : Fin 3 → ℝ → ℝ} {a' : Fin 3 → ℝ} {σ c : ℝ}
    (h : ∀ i : Fin 3, HasDerivAt (a i) (a' i) σ) :
    HasDerivAt (fun s : ℝ => c * ∑ i : Fin 3, (a i s) ^ 2)
      (c * (2 * ∑ i : Fin 3, a i σ * a' i)) σ := by
  have h2 : ∀ i : Fin 3, HasDerivAt (fun s : ℝ => (a i s) ^ 2) (2 * (a i σ * a' i)) σ := by
    intro i
    have hp := (h i).pow 2
    have hval : ((2 : ℕ) : ℝ) * a i σ ^ (2 - 1) * a' i = 2 * (a i σ * a' i) := by
      norm_num
      ring
    rw [hval] at hp
    exact hp
  have hsum : HasDerivAt (fun s : ℝ => ∑ i : Fin 3, (a i s) ^ 2)
      (∑ i : Fin 3, 2 * (a i σ * a' i)) σ := by
    simp only [Fin.sum_univ_three]
    exact ((h2 0).add (h2 1)).add (h2 2)
  have hcm := hsum.const_mul c
  have hval : c * ∑ i : Fin 3, 2 * (a i σ * a' i) = c * (2 * ∑ i : Fin 3, a i σ * a' i) := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hval] at hcm
  exact hcm

/-- A three-term Cauchy–Schwarz-free bound: a sum of three products of quantities bounded by
`B` is bounded by `3B²`. -/
private lemma abs_sum3_mul_le {a b : Fin 3 → ℝ} {B : ℝ} (ha : ∀ i : Fin 3, |a i| ≤ B)
    (hb : ∀ i : Fin 3, |b i| ≤ B) : |∑ i : Fin 3, a i * b i| ≤ 3 * B ^ 2 := by
  have hB : 0 ≤ B := le_trans (abs_nonneg (a 0)) (ha 0)
  have hterm : ∀ i : Fin 3, |a i * b i| ≤ B ^ 2 := by
    intro i
    rw [abs_mul, sq]
    exact mul_le_mul (ha i) (hb i) (abs_nonneg _) hB
  calc |∑ i : Fin 3, a i * b i| ≤ ∑ i : Fin 3, |a i * b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 3 * B ^ 2 := by simp [Finset.sum_const]

section Velocity2

variable {u : ParabolicPoint → Vec3}

/-- **Stage (i) of `eq:aniso:closure:tested`.** The cutoff enstrophy is differentiable in
time and its derivative is obtained by differentiating under the integral sign. The
domination is uniform on a compact time slab inside the cylinder, where `ω` and `∂_t ω` are
bounded by continuity, and the cutoff makes the spatial support compact. -/
theorem hasDerivAt_cutoffEnstrophy
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    HasDerivAt (cutoffEnstrophy χ u)
      (∫ x : Vec3, χ x ^ 2 * (2 * ∑ i : Fin 3,
        vorticityField u (x, t) i * timePartial (curlComp u i) (x, t))) t := by
  obtain ⟨ht1, ht2⟩ := ht
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨ht1, ht2⟩
  have hU : IsOpen (vec3Ball 0 1 : Set Vec3) := isOpen_vec3Ball 0 1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hsqU : tsupport (fun x : Vec3 => χ x ^ 2) ⊆ vec3Ball 0 1 :=
    (tsupport_sq_subset χ).trans hχU
  -- a time radius whose closed slab still sits inside the cylinder
  have hmin0 : 0 < min (t + 1) (-t) := lt_min (by linarith only [ht1]) (by linarith only [ht2])
  have hε0 : 0 < (min (t + 1) (-t)) / 2 := by linarith only [hmin0]
  have hεa : (min (t + 1) (-t)) / 2 ≤ (t + 1) / 2 := by
    have h := min_le_left (t + 1) (-t)
    linarith only [h]
  have hεb : (min (t + 1) (-t)) / 2 ≤ (-t) / 2 := by
    have h := min_le_right (t + 1) (-t)
    linarith only [h]
  have hIccsub : Icc (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2)
      ⊆ Ioo (-1 : ℝ) 0 := by
    intro s hs
    exact ⟨by linarith only [hs.1, hεa, ht1], by linarith only [hs.2, hεb, ht2]⟩
  -- uniform bounds for the vorticity and its time derivative on the compact slab
  have hKcpt : IsCompact ((tsupport χ) ×ˢ
      (Icc (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2))) :=
    hχs.prod isCompact_Icc
  have hKsub : (tsupport χ) ×ˢ
      (Icc (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2)) ⊆ unitCylinder := by
    intro z hz
    exact ⟨hχU hz.1, hIccsub hz.2⟩
  have hΨ : ContinuousOn (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, (|curlComp u i z| + |timePartial (curlComp u i) z|)) unitCylinder := by
    have h : ∀ i : Fin 3, ContinuousOn
        (fun z : Vec3 × ℝ => |curlComp u i z| + |timePartial (curlComp u i) z|) unitCylinder :=
      fun i => ((contDiffOn_curlComp hu i).continuousOn.abs).add
        ((continuousOn_timePartial_curlComp hu i).abs)
    simp only [Fin.sum_univ_three]
    exact ((h 0).add (h 1)).add (h 2)
  obtain ⟨B, hB⟩ := hKcpt.exists_bound_of_continuousOn (hΨ.mono hKsub)
  have hBsplit : ∀ z ∈ (tsupport χ) ×ˢ
      (Icc (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2)), ∀ i : Fin 3,
      |curlComp u i z| ≤ B ∧ |timePartial (curlComp u i) z| ≤ B := by
    intro z hz i
    have hsingle : |curlComp u i z| + |timePartial (curlComp u i) z|
        ≤ ∑ k : Fin 3, (|curlComp u k z| + |timePartial (curlComp u k) z|) :=
      Finset.single_le_sum
        (f := fun k : Fin 3 => |curlComp u k z| + |timePartial (curlComp u k) z|)
        (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    have hnorm := hB z hz
    rw [Real.norm_eq_abs] at hnorm
    have hle : ∑ k : Fin 3, (|curlComp u k z| + |timePartial (curlComp u k) z|) ≤ B :=
      le_trans (le_abs_self _) hnorm
    exact ⟨by linarith only [hsingle, hle, abs_nonneg (timePartial (curlComp u i) z)],
      by linarith only [hsingle, hle, abs_nonneg (curlComp u i z)]⟩
  -- the hypotheses of the parametric differentiation lemma
  have hsnbhd : Ioo (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2) ∈ nhds t :=
    Ioo_mem_nhds (by linarith only [hε0]) (by linarith only [hε0])
  have hFmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, s)) ^ 2) volume := by
    filter_upwards [Ioo_mem_nhds ht1 ht2] with s hs
    exact (continuous_weight_mul hU hsqχ.continuous hsqU
      (contDiffOn_sumSqVorticity_slice hu hs).continuousOn).aestronglyMeasurable
  have hFint : Integrable
      (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) :=
    integrable_weight_mul hU hsqχ.continuous hsqs hsqU
      (contDiffOn_sumSqVorticity_slice hu htmem).continuousOn
  have hprodcont : ∀ s ∈ Ioo (-1 : ℝ) 0, ContinuousOn
      (fun x : Vec3 => 2 * ∑ i : Fin 3,
        curlComp u i (x, s) * timePartial (curlComp u i) (x, s)) (vec3Ball 0 1) := by
    intro s hs
    have h : ∀ i : Fin 3, ContinuousOn
        (fun x : Vec3 => curlComp u i (x, s) * timePartial (curlComp u i) (x, s))
        (vec3Ball 0 1) :=
      fun i => (contDiffOn_curlComp_slice hu i hs).continuousOn.mul
        (continuousOn_timePartial_curlComp_slice hu i hs)
    have hsum : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3,
        curlComp u i (x, s) * timePartial (curlComp u i) (x, s)) (vec3Ball 0 1) := by
      simp only [Fin.sum_univ_three]
      exact ((h 0).add (h 1)).add (h 2)
    exact continuousOn_const.mul hsum
  have hF'meas : AEStronglyMeasurable
      (fun x : Vec3 => χ x ^ 2 * (2 * ∑ i : Fin 3,
        curlComp u i (x, t) * timePartial (curlComp u i) (x, t))) volume :=
    (continuous_weight_mul hU hsqχ.continuous hsqU (hprodcont t htmem)).aestronglyMeasurable
  have hbound : ∀ᵐ x : Vec3, ∀ s ∈ Ioo (t - (min (t + 1) (-t)) / 2)
      (t + (min (t + 1) (-t)) / 2),
      ‖χ x ^ 2 * (2 * ∑ i : Fin 3,
        curlComp u i (x, s) * timePartial (curlComp u i) (x, s))‖ ≤ 6 * B ^ 2 * χ x ^ 2 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    intro s hs
    by_cases hx : x ∈ tsupport χ
    · have hzK : ((x, s) : Vec3 × ℝ) ∈ (tsupport χ) ×ˢ
          (Icc (t - (min (t + 1) (-t)) / 2) (t + (min (t + 1) (-t)) / 2)) :=
        ⟨hx, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
      have hb1 : ∀ i : Fin 3, |curlComp u i (x, s)| ≤ B := fun i => (hBsplit _ hzK i).1
      have hb2 : ∀ i : Fin 3, |timePartial (curlComp u i) (x, s)| ≤ B :=
        fun i => (hBsplit _ hzK i).2
      have hS := abs_sum3_mul_le hb1 hb2
      have hsq : (0 : ℝ) ≤ χ x ^ 2 := sq_nonneg _
      have h2 : |2 * ∑ i : Fin 3,
          curlComp u i (x, s) * timePartial (curlComp u i) (x, s)| ≤ 6 * B ^ 2 := by
        rw [abs_mul]
        have habs : |(2 : ℝ)| = 2 := by norm_num
        rw [habs]
        linarith only [hS]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsq]
      have hmul := mul_le_mul_of_nonneg_left h2 hsq
      linarith only [hmul]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχ0]
      norm_num
  have hboundint : Integrable (fun x : Vec3 => 6 * B ^ 2 * χ x ^ 2) :=
    (hsqχ.continuous.integrable_of_hasCompactSupport hsqs).const_mul (6 * B ^ 2)
  have hdiff : ∀ᵐ x : Vec3, ∀ s ∈ Ioo (t - (min (t + 1) (-t)) / 2)
      (t + (min (t + 1) (-t)) / 2),
      HasDerivAt (fun σ : ℝ => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, σ)) ^ 2)
        (χ x ^ 2 * (2 * ∑ i : Fin 3,
          curlComp u i (x, s) * timePartial (curlComp u i) (x, s))) s := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    intro s hs
    by_cases hx : x ∈ tsupport χ
    · have hzU : ((x, s) : ParabolicPoint) ∈ unitCylinder :=
        hKsub ⟨hx, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
      exact hasDerivAt_const_mul_sumSq (a := fun i => fun σ : ℝ => curlComp u i (x, σ))
        (a' := fun i => timePartial (curlComp u i) (x, s))
        (fun i => hasDerivAt_curlComp_time hu i hzU)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hfun : (fun σ : ℝ => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, σ)) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext σ
        rw [hχ0]
        ring
      rw [hfun, hχ0]
      simpa using hasDerivAt_const s (0 : ℝ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, s)) ^ 2)
    (F' := fun s x => χ x ^ 2 * (2 * ∑ i : Fin 3,
      curlComp u i (x, s) * timePartial (curlComp u i) (x, s)))
    (bound := fun x : Vec3 => 6 * B ^ 2 * χ x ^ 2) (x₀ := t)
    hsnbhd hFmeas hFint hF'meas hbound hboundint hdiff
  exact key.2

end Velocity2

/-! ### Continuity of the slice quantities -/

section Slices

variable {u : ParabolicPoint → Vec3}

/-- The time slice of a component of the curl is continuous on the unit ball. -/
theorem continuousOn_curl_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => curlComp u i (x, t)) (vec3Ball 0 1) :=
  (contDiffOn_curlComp_slice hu i ht).continuousOn

/-- A spatial derivative of the vorticity is continuous on the unit ball. -/
theorem continuousOn_dcurl_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
      (vec3Ball 0 1) :=
  continuousOn_dirDeriv (isOpen_vec3Ball 0 1) (contDiffOn_curlComp_slice hu i ht) j

/-- A second spatial derivative of the vorticity is continuous on the unit ball. -/
theorem continuousOn_ddcurl_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
        (basisVec j)) (vec3Ball 0 1) :=
  continuousOn_dirDeriv (isOpen_vec3Ball 0 1)
    (contDiffOn_dirDeriv (isOpen_vec3Ball 0 1) (contDiffOn_curlComp_slice hu i ht) j) j

/-- The time slice of a component of the velocity is continuous on the unit ball. -/
theorem continuousOn_vel_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => u (x, t) i) (vec3Ball 0 1) :=
  (contDiffOn_velocity_slice hu i ht).continuousOn

/-- A spatial derivative of the velocity is continuous on the unit ball. -/
theorem continuousOn_dvel_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j))
      (vec3Ball 0 1) :=
  continuousOn_dirDeriv (isOpen_vec3Ball 0 1) (contDiffOn_velocity_slice hu i ht) j

/-- The vorticity components are differentiable at each point of the unit ball. -/
private lemma differentiableAt_curl_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    DifferentiableAt ℝ (fun y : Vec3 => curlComp u i (y, t)) x :=
  ((contDiffOn_curlComp_slice hu i ht).differentiableOn (by simp)).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hx)

/-- The velocity components are differentiable at each point of the unit ball. -/
private lemma differentiableAt_vel_slice
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    DifferentiableAt ℝ (fun y : Vec3 => u (y, t) i) x :=
  ((contDiffOn_velocity_slice hu i ht).differentiableOn (by simp)).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hx)

end Slices

/-! ### Stage (ii)(a): the transport term -/

section Transport

variable {u : ParabolicPoint → Vec3}

/-- **The tested transport term of `eq:aniso:closure:tested`.** Testing `u·∇ω` against `χ² ω`
and integrating by parts gives `∫ χ² ω·(u·∇ω) = -½ ∫ |ω|² u·∇(χ²)`; the term
`½ ∫ χ² (div u) |ω|²` produced by the product rule vanishes because `u` is divergence free.
The right-hand side is supported where `∇χ ≠ 0`. -/
theorem integral_cutoff_vorticity_transport
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hdivu : ∀ z ∈ unitCylinder, ∑ j : Fin 3, spatialPartial (fun w => u w j) j z = 0)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, vorticityField u (x, t) i *
          ∑ j : Fin 3, u (x, t) j * spatialPartial (fun w => vorticityField u w i) j (x, t)
      = -(1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (vorticityField u (x, t) i) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j := by
  have hUo : IsOpen (vec3Ball 0 1 : Set Vec3) := isOpen_vec3Ball 0 1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hsqU : tsupport (fun x : Vec3 => χ x ^ 2) ⊆ vec3Ball 0 1 :=
    (tsupport_sq_subset χ).trans hχU
  have hG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) (vec3Ball 0 1) :=
    contDiffOn_sumSqVorticity_slice hu ht
  have hFj : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2 * u (x, t) j) :=
    fun j => contDiff_weight_mul hUo hsqχ hsqU (contDiffOn_velocity_slice hu j ht)
  have hFjs : ∀ j : Fin 3, HasCompactSupport (fun x : Vec3 => χ x ^ 2 * u (x, t) j) :=
    fun _ => hasCompactSupport_weight_mul hsqs
  have hFjU : ∀ j : Fin 3, tsupport (fun x : Vec3 => χ x ^ 2 * u (x, t) j) ⊆ vec3Ball 0 1 :=
    fun _ => (tsupport_weight_mul_subset _ _).trans hsqU
  -- the pointwise derivative of `|ω|²`
  have hGd : ∀ (j : Fin 3) (x : Vec3), x ∈ vec3Ball 0 1 →
      fderiv ℝ (fun y : Vec3 => ∑ i : Fin 3, (curlComp u i (y, t)) ^ 2) x (basisVec j)
        = 2 * ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) := by
    intro j x hx
    exact dirDeriv_sumSq (fun i => differentiableAt_curl_slice hu i ht hx) j
  -- the two integrands
  have hLpt : ∀ (j : Fin 3) (x : Vec3),
      (χ x ^ 2 * u (x, t) j) *
          fderiv ℝ (fun y : Vec3 => ∑ i : Fin 3, (curlComp u i (y, t)) ^ 2) x (basisVec j)
        = (χ x ^ 2 * u (x, t) j) * (2 * ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
    intro j x
    by_cases hx : x ∈ vec3Ball 0 1
    · rw [hGd j x hx]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hχU hm))
      rw [hχ0]
      ring
  have hdivchi : ∀ x : Vec3,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j)
        = ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j := by
    intro x
    by_cases hx : x ∈ vec3Ball 0 1
    · have hprod : ∀ j : Fin 3,
          fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j)
            = fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j
              + χ x ^ 2 * fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) :=
        fun j => dirDeriv_mul (hsqχ.differentiable (by simp)).differentiableAt
          (differentiableAt_vel_slice hu j ht hx) j
      have hdv : ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 :=
        hdivu (x, t) ⟨hx, ht⟩
      simp only [hprod]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdv, mul_zero, add_zero]
    · have hxχ : x ∉ tsupport χ := fun hm => hx (hχU hm)
      have h1 : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) = 0 :=
        fun j => dirDeriv_zero_off_tsupport
          (fun hm => hxχ (tsupport_sq_subset χ (tsupport_weight_mul_subset _ _ hm))) j
      have h2 : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) = 0 :=
        fun j => dirDeriv_zero_off_tsupport (fun hm => hxχ (tsupport_sq_subset χ hm)) j
      simp [h1, h2]
  have hRpt : ∀ x : Vec3,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) *
          ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2
        = (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
            ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j := by
    intro x
    rw [← Finset.sum_mul, hdivchi x, Finset.sum_mul, ← Finset.sum_mul, mul_comm]
  -- integrability of the two families
  have hprodc : ∀ j : Fin 3, ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, curlComp u i (x, t) *
      fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) := by
    intro j
    have h : ∀ i : Fin 3, ContinuousOn (fun x : Vec3 => curlComp u i (x, t) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) :=
      fun i => (continuousOn_curl_slice hu i ht).mul (continuousOn_dcurl_slice hu i j ht)
    simp only [Fin.sum_univ_three]
    exact ((h 0).add (h 1)).add (h 2)
  have hLint : ∀ j : Fin 3, Integrable (fun x : Vec3 => (χ x ^ 2 * u (x, t) j) *
      (2 * ∑ i : Fin 3, curlComp u i (x, t) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))) := by
    intro j
    refine integrable_of_cutoff hχs hχU
      (((hsqχ.continuous.continuousOn).mul (continuousOn_vel_slice hu j ht)).mul
        (continuousOn_const.mul (hprodc j))) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hRint : ∀ j : Fin 3, Integrable
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) *
        ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    intro j
    refine integrable_of_cutoff hχs hχU
      ((continuous_dirDeriv (hFj j) j).continuousOn.mul hG.continuousOn) (fun x hx => ?_)
    rw [dirDeriv_zero_off_tsupport
      (fun hm => hx (tsupport_sq_subset χ (tsupport_weight_mul_subset _ _ hm))) j, zero_mul]
  -- integration by parts in each direction
  have hIBP : ∀ j : Fin 3,
      ∫ x : Vec3, (χ x ^ 2 * u (x, t) j) * (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
        = - ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) *
            ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    intro j
    rw [← integral_congr_ae (Filter.Eventually.of_forall (fun x => hLpt j x))]
    exact integral_weight_mul_fderiv hUo (hFj j) (hFjs j) (hFjU j) hG j
  -- assemble
  have hsum : ∫ x : Vec3, ∑ j : Fin 3, (χ x ^ 2 * u (x, t) j) *
        (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
      = - ∫ x : Vec3, ∑ j : Fin 3,
          fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) *
            ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    rw [integral_sum3 hLint, integral_sum3 hRint,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hIBP j)]
    simp
  have hleft : ∫ x : Vec3, ∑ j : Fin 3, (χ x ^ 2 * u (x, t) j) *
        (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
      = 2 * ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
          ∑ j : Fin 3, u (x, t) j *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Fin.sum_univ_three]
    ring
  have hright : ∫ x : Vec3, ∑ j : Fin 3,
        fderiv ℝ (fun y : Vec3 => χ y ^ 2 * u (y, t) j) x (basisVec j) *
          ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2
      = ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j :=
    integral_congr_ae (Filter.Eventually.of_forall hRpt)
  rw [hleft, hright] at hsum
  change (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
      ∑ j : Fin 3, u (x, t) j *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
    = -(1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
        ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j
  linarith only [hsum]

end Transport

/-! ### Stage (ii)(b): the diffusion term -/

section Diffusion

variable {u : ParabolicPoint → Vec3}

private theorem integrable_cutoff_vorticity_mixed
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Integrable (fun x : Vec3 => ∑ j : Fin 3,
      fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hCcont : ContinuousOn (fun x : Vec3 => ∑ j : Fin 3,
      fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) := by
    have hin : ∀ j : Fin 3, ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, curlComp u i (x, t) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) := by
      intro j
      have h : ∀ i : Fin 3, ContinuousOn (fun x : Vec3 => curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) :=
        fun i => (continuousOn_curl_slice hu i ht).mul (continuousOn_dcurl_slice hu i j ht)
      simp only [Fin.sum_univ_three]
      exact ((h 0).add (h 1)).add (h 2)
    have h : ∀ j : Fin 3, ContinuousOn (fun x : Vec3 =>
        fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
          ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) :=
      fun j => (continuous_dirDeriv hsqχ j).continuousOn.mul (hin j)
    exact continuousOn_finsetSum Finset.univ (fun j _ => h j)
  have hCint : Integrable (fun x : Vec3 => ∑ j : Fin 3,
      fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
    refine integrable_of_cutoff hχs hχU hCcont (fun x hx => ?_)
    have h : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) = 0 :=
      fun j => dirDeriv_zero_off_tsupport (fun hm => hx (tsupport_sq_subset χ hm)) j
    simp [h]
  exact hCint

private theorem integral_mul_sum_mul_sum (a : Vec3 → ℝ) (b : Fin 3 → Vec3 → ℝ)
    (c : Fin 3 → Fin 3 → Vec3 → ℝ) :
    (∫ x : Vec3, a x * ∑ i : Fin 3, b i x * ∑ j : Fin 3, c i j x) =
      ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (a x * b i x) * c i j x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Fin.sum_univ_three]
  ring

private theorem integral_cutoff_sumSq_deriv
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ∀ j : Fin 3,
      ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
          (2 * ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
        = - ∫ x : Vec3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) *
              ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
  have hUo : IsOpen (vec3Ball 0 1 : Set Vec3) := isOpen_vec3Ball 0 1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hsqU : tsupport (fun x : Vec3 => χ x ^ 2) ⊆ vec3Ball 0 1 :=
    (tsupport_sq_subset χ).trans hχU
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) (vec3Ball 0 1) :=
    contDiffOn_sumSqVorticity_slice hu ht
  have hPj : ∀ j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) :=
    fun j => contDiff_dirDeriv hsqχ j
  have hPjs : ∀ j : Fin 3, HasCompactSupport
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) :=
    fun j => hasCompactSupport_dirDeriv hsqs j
  have hPjU : ∀ j : Fin 3, tsupport
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) ⊆ vec3Ball 0 1 :=
    fun j => (tsupport_dirDeriv_subset _ j).trans hsqU
  have hQd : ∀ (j : Fin 3) (x : Vec3), x ∈ vec3Ball 0 1 →
      fderiv ℝ (fun y : Vec3 => ∑ i : Fin 3, (curlComp u i (y, t)) ^ 2) x (basisVec j)
        = 2 * ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) :=
    fun j x hx => dirDeriv_sumSq (fun i => differentiableAt_curl_slice hu i ht hx) j
  have hIBP2 : ∀ j : Fin 3,
      ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
          (2 * ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
        = - ∫ x : Vec3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) *
              ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    intro j
    have hpt : ∀ x : Vec3,
        fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
            fderiv ℝ (fun y : Vec3 => ∑ i : Fin 3, (curlComp u i (y, t)) ^ 2) x (basisVec j)
          = fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
            (2 * ∑ i : Fin 3, curlComp u i (x, t) *
              fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
      intro x
      by_cases hx : x ∈ vec3Ball 0 1
      · rw [hQd j x hx]
      · have hxχ : x ∉ tsupport χ := fun hm => hx (hχU hm)
        rw [dirDeriv_zero_off_tsupport (fun hm => hxχ (tsupport_sq_subset χ hm)) j]
        ring
    rw [← integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_weight_mul_fderiv hUo (hPj j) (hPjs j) (hPjU j) hQ j
  exact hIBP2

/-- **The tested diffusion term of `eq:aniso:closure:tested`.** Testing `Δω` against `χ² ω`
and integrating by parts twice gives `∫ χ² ω·Δω = -M + ½ ∫ |ω|² Δ(χ²)`. The second
integration by parts moves the surviving derivative off `∇ω`, so that the cutoff error only
involves `ω` itself on the annulus where `χ` is not locally constant. -/
theorem integral_cutoff_vorticity_diffusion
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, vorticityField u (x, t) i *
          ∑ j : Fin 3, spatialSecondPartial (fun w => vorticityField u w i) j j (x, t)
      = - cutoffEnstrophyDissipation χ u t
        + (1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (vorticityField u (x, t) i) ^ 2) *
            ∑ j : Fin 3, fderiv ℝ
              (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
                (basisVec j) := by
  have hUo : IsOpen (vec3Ball 0 1 : Set Vec3) := isOpen_vec3Ball 0 1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hsqU : tsupport (fun x : Vec3 => χ x ^ 2) ⊆ vec3Ball 0 1 :=
    (tsupport_sq_subset χ).trans hχU
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) (vec3Ball 0 1) :=
    contDiffOn_sumSqVorticity_slice hu ht
  -- the weights χ² ωᵢ and ∂ⱼ(χ²)
  have hWi : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2 * curlComp u i (x, t)) :=
    fun i => contDiff_weight_mul hUo hsqχ hsqU (contDiffOn_curlComp_slice hu i ht)
  have hWis : ∀ i : Fin 3,
      HasCompactSupport (fun x : Vec3 => χ x ^ 2 * curlComp u i (x, t)) :=
    fun _ => hasCompactSupport_weight_mul hsqs
  have hWiU : ∀ i : Fin 3,
      tsupport (fun x : Vec3 => χ x ^ 2 * curlComp u i (x, t)) ⊆ vec3Ball 0 1 :=
    fun _ => (tsupport_weight_mul_subset _ _).trans hsqU
  have hWi0 : ∀ (i : Fin 3) (x : Vec3), x ∉ tsupport χ →
      x ∉ tsupport (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) :=
    fun _ _ hx hm => hx (tsupport_sq_subset χ (tsupport_weight_mul_subset _ _ hm))
  have hPj : ∀ j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) :=
    fun j => contDiff_dirDeriv hsqχ j
  -- first integration by parts
  have hIBP1 : ∀ i j : Fin 3,
      ∫ x : Vec3, (χ x ^ 2 * curlComp u i (x, t)) * fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
            (basisVec j)
        = - ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) :=
    fun i j => integral_weight_mul_fderiv hUo (hWi i) (hWis i) (hWiU i)
      (contDiffOn_dirDeriv hUo (contDiffOn_curlComp_slice hu i ht) j) j
  -- the product rule for the weight χ² ωᵢ
  have hdW : ∀ (i j : Fin 3) (x : Vec3),
      fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j)
        = fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * curlComp u i (x, t)
          + χ x ^ 2 * fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) := by
    intro i j x
    by_cases hx : x ∈ vec3Ball 0 1
    · exact dirDeriv_mul (hsqχ.differentiable (by simp)).differentiableAt
        (differentiableAt_curl_slice hu i ht hx) j
    · have hxχ : x ∉ tsupport χ := fun hm => hx (hχU hm)
      rw [dirDeriv_zero_off_tsupport (hWi0 i x hxχ) j,
        dirDeriv_zero_off_tsupport (fun hm => hxχ (tsupport_sq_subset χ hm)) j,
        image_eq_zero_of_notMem_tsupport hxχ]
      ring
  -- second integration by parts
  have hIBP2 := integral_cutoff_sumSq_deriv hu hχ hχs hχU ht
  -- integrability of every integrand that appears
  have hAint : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
      (χ x ^ 2 * curlComp u i (x, t)) * fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
          (basisVec j)) := by
    intro i j
    refine integrable_of_cutoff hχs hχU
      (((hsqχ.continuous.continuousOn).mul (continuousOn_curl_slice hu i ht)).mul
        (continuousOn_ddcurl_slice hu i j ht)) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hBint : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
    intro i j
    refine integrable_of_cutoff hχs hχU
      ((continuous_dirDeriv (hWi i) j).continuousOn.mul (continuousOn_dcurl_slice hu i j ht))
      (fun x hx => ?_)
    rw [dirDeriv_zero_off_tsupport (hWi0 i x hx) j, zero_mul]
  have hCint := integrable_cutoff_vorticity_mixed hu hχ hχs hχU ht
  have hEcont : ContinuousOn (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2) (vec3Ball 0 1) := by
    have h : ∀ i j : Fin 3, ContinuousOn (fun x : Vec3 =>
        (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2) (vec3Ball 0 1) :=
      fun i j => (continuousOn_dcurl_slice hu i j ht).pow 2
    have hin : ∀ i : Fin 3, ContinuousOn (fun x : Vec3 => ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2) (vec3Ball 0 1) := by
      intro i
      simp only [Fin.sum_univ_three]
      exact (((h i 0).add (h i 1)).add (h i 2))
    exact (hsqχ.continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ => hin i))
  have hEint : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2) := by
    refine integrable_of_cutoff hχs hχU hEcont (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hJint : ∀ j : Fin 3, Integrable (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))) := by
    intro j
    have hin : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, curlComp u i (x, t) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) := by
      have h : ∀ i : Fin 3, ContinuousOn (fun x : Vec3 => curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) (vec3Ball 0 1) :=
        fun i => (continuousOn_curl_slice hu i ht).mul (continuousOn_dcurl_slice hu i j ht)
      simp only [Fin.sum_univ_three]
      exact ((h 0).add (h 1)).add (h 2)
    refine integrable_of_cutoff hχs hχU
      ((continuous_dirDeriv hsqχ j).continuousOn.mul (continuousOn_const.mul hin))
      (fun x hx => ?_)
    rw [dirDeriv_zero_off_tsupport (fun hm => hx (tsupport_sq_subset χ hm)) j, zero_mul]
  have hKint : ∀ j : Fin 3, Integrable (fun x : Vec3 => fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) *
        ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    intro j
    refine integrable_of_cutoff hχs hχU
      ((continuous_dirDeriv (hPj j) j).continuousOn.mul hQ.continuousOn) (fun x hx => ?_)
    rw [dirDeriv_zero_off_tsupport
      (fun hm => hx (tsupport_sq_subset χ ((tsupport_dirDeriv_subset _ j) hm))) j, zero_mul]
  -- assembling the first integration by parts
  have hD1 := integral_mul_sum_mul_sum (fun x => χ x ^ 2)
    (fun i x => curlComp u i (x, t)) (fun i j x => fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
        (basisVec j))
  have hD2 := integral_sum_sum_eq (fun i j x : _ => (χ x ^ 2 * curlComp u i (x, t)) * fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
        (basisVec j)) hAint
  have hD3 : (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        (χ x ^ 2 * curlComp u i (x, t)) * fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x
            (basisVec j))
      = - ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hIBP1 i j))]
    simp
  have hD4 := integral_sum_sum_eq (fun i j x : _ =>
      fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) hBint
  have hD5 : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun y : Vec3 => χ y ^ 2 * curlComp u i (y, t)) x (basisVec j) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
      = (∫ x : Vec3, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
            ∑ i : Fin 3, curlComp u i (x, t) *
              fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
        + ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2 := by
    rw [← integral_add hCint hEint]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hdW, Fin.sum_univ_three]
    ring
  -- assembling the second integration by parts
  have hE1 : (∑ j : Fin 3, ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)))
      = - ∑ j : Fin 3, ∫ x : Vec3, fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) *
            ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hIBP2 j)]
    simp
  have hE2 : (∫ x : Vec3, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
        (2 * ∑ i : Fin 3, curlComp u i (x, t) *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)))
      = 2 * ∫ x : Vec3, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) *
          ∑ i : Fin 3, curlComp u i (x, t) *
            fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Fin.sum_univ_three]
    ring
  have hE3 : (∫ x : Vec3, ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) *
          ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)
      = ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
              (basisVec j) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [← Finset.sum_mul, mul_comm]
  have hE4 := integral_sum3 hJint
  have hE5 := integral_sum3 hKint
  change (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
        ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
          fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j))
      = - (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) ^ 2)
        + (1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
            ∑ j : Fin 3, fderiv ℝ
              (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
                (basisVec j)
  rw [hD1, hD2, hD3, ← hD4, hD5]
  rw [hE4, hE1, ← hE5, hE3] at hE2
  linarith only [hE2]

end Diffusion

/-! ### Stage (ii)(c): the force term -/

/-- A first Cartesian partial derivative is a multi-index derivative of order one. -/
private lemma exists_multiPartial_of_spatialPartial (g : ParabolicPoint → ℝ) (c : Fin 3) :
    ∃ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 ∧ multiPartial g α = spatialPartial g c := by
  fin_cases c
  · exact ⟨![1, 0, 0], by decide, rfl⟩
  · exact ⟨![0, 1, 0], by decide, rfl⟩
  · exact ⟨![0, 0, 1], by decide, rfl⟩

/-- The triangle inequality for a difference. -/
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |(-b)| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- A `C²`-bounded force has a curl bounded by twice the `C²` bound. -/
private lemma abs_curlComp_le_of_forceC2 {f : ParabolicPoint → Vec3} {M : ℝ}
    (hM : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ M)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i : Fin 3) :
    |curlComp f i z| ≤ 2 * |M| := by
  have hpart : ∀ m c : Fin 3, |spatialPartial (fun w => f w m) c z| ≤ |M| := by
    intro m c
    obtain ⟨α, hα, he⟩ := exists_multiPartial_of_spatialPartial (fun w => f w m) c
    have h := hM z hz m α hα
    rw [he] at h
    exact le_trans h (le_abs_self M)
  have h1 := hpart (i + 2) (i + 1)
  have h2 := hpart (i + 1) (i + 2)
  have hc : curlComp f i z = spatialPartial (fun w => f w (i + 2)) (i + 1) z
      - spatialPartial (fun w => f w (i + 1)) (i + 2) z := rfl
  rw [hc]
  have h3 := abs_sub_le_abs_add_abs (spatialPartial (fun w => f w (i + 2)) (i + 1) z)
    (spatialPartial (fun w => f w (i + 1)) (i + 2) z)
  linarith only [h1, h2, h3]

/-- The elementary bound behind the force term: three products with a uniformly bounded
factor are controlled by the squared length plus a constant, so no Cauchy–Schwarz inequality
in `L²` is needed. -/
private lemma abs_sum3_mul_le_half {a b : Fin 3 → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ i : Fin 3, |b i| ≤ K) :
    |∑ i : Fin 3, a i * b i| ≤ K / 2 * (∑ i : Fin 3, (a i) ^ 2) + 3 * K / 2 := by
  have hterm : ∀ i : Fin 3, |a i * b i| ≤ K / 2 * (a i) ^ 2 + K / 2 := by
    intro i
    rw [abs_mul]
    have h2 : |a i| * |b i| ≤ |a i| * K := mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    have h3 : 2 * |a i| ≤ (a i) ^ 2 + 1 := by
      nlinarith only [sq_nonneg (|a i| - 1), sq_abs (a i)]
    have h4 : |a i| * K ≤ ((a i) ^ 2 + 1) / 2 * K :=
      mul_le_mul_of_nonneg_right (by linarith only [h3]) hK
    linarith only [h2, h4]
  calc |∑ i : Fin 3, a i * b i| ≤ ∑ i : Fin 3, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, (K / 2 * (a i) ^ 2 + K / 2) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = K / 2 * (∑ i : Fin 3, (a i) ^ 2) + 3 * K / 2 := by
        simp only [Fin.sum_univ_three]
        ring

section Force

variable {u : ParabolicPoint → Vec3}

/-- **The tested force term of `eq:aniso:closure:tested`.** Since `curl f` is bounded by twice
the `C²` bound `eq:interior:force:c-two` of the force, the tested force term obeys
`|∫ χ² ω·curl f| ≤ C (Y + 1)` with a constant depending only on that bound and on `χ`, on the
time window `(t₀, 0)`. -/
theorem abs_integral_cutoff_vorticity_force_le
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ 0,
      |∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
          vorticityField u (x, t) i * curlComp f i (x, t)|
        ≤ C * (cutoffEnstrophy χ u t + 1) := by
  obtain ⟨Mf, hMf'⟩ := hMf
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hchiint : Integrable (fun x : Vec3 => χ x ^ 2) :=
    hsqχ.continuous.integrable_of_hasCompactSupport hsqs
  have hchinn : (0 : ℝ) ≤ ∫ x : Vec3, χ x ^ 2 := integral_nonneg (fun x => sq_nonneg (χ x))
  have hA : (0 : ℝ) ≤ |Mf| := abs_nonneg Mf
  refine ⟨|Mf| + 3 * |Mf| * (∫ x : Vec3, χ x ^ 2), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ 3 * |Mf| * (∫ x : Vec3, χ x ^ 2) :=
      mul_nonneg (by linarith only [hA]) hchinn
    linarith only [hA, h2]
  intro t ht
  have ht1 : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hfb : ∀ (i : Fin 3) (x : Vec3), x ∈ vec3Ball 0 1 → |curlComp f i (x, t)| ≤ 2 * |Mf| :=
    fun i x hx => abs_curlComp_le_of_forceC2 hMf' ⟨hx, ht1⟩ i
  have hpt : ∀ x : Vec3, |χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) * curlComp f i (x, t)|
      ≤ |Mf| * (χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) + 3 * |Mf| * χ x ^ 2 := by
    intro x
    by_cases hx : x ∈ vec3Ball 0 1
    · have hb := abs_sum3_mul_le_half (a := fun i : Fin 3 => curlComp u i (x, t))
        (b := fun i : Fin 3 => curlComp f i (x, t)) (K := 2 * |Mf|)
        (by linarith only [hA]) (fun i => hfb i x hx)
      have hsq : (0 : ℝ) ≤ χ x ^ 2 := sq_nonneg _
      rw [abs_mul, abs_of_nonneg hsq]
      have hmul := mul_le_mul_of_nonneg_left hb hsq
      linarith only [hmul]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hχU hm))
      rw [hχ0]
      norm_num
  have hFint : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3,
      curlComp u i (x, t) * curlComp f i (x, t)) := by
    refine integrable_of_cutoff hχs hχU
      ((hsqχ.continuous.continuousOn).mul (continuousOn_finsetSum Finset.univ (fun i _ =>
        (continuousOn_curl_slice hu i ht1).mul (continuousOn_curl_slice hf i ht1))))
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hYint : Integrable
      (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    refine integrable_of_cutoff hχs hχU
      ((hsqχ.continuous.continuousOn).mul (contDiffOn_sumSqVorticity_slice hu ht1).continuousOn)
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hY : (0 : ℝ) ≤ cutoffEnstrophy χ u t :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (vorticityField u (x, t) i))))
  have hIY : (0 : ℝ) ≤ 3 * |Mf| * (∫ x : Vec3, χ x ^ 2) * cutoffEnstrophy χ u t :=
    mul_nonneg (mul_nonneg (by linarith only [hA]) hchinn) hY
  calc |∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) * curlComp f i (x, t)|
      ≤ ∫ x : Vec3, |χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) * curlComp f i (x, t)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, (|Mf| * (χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)
          + 3 * |Mf| * χ x ^ 2) :=
        integral_mono hFint.abs ((hYint.const_mul _).add (hchiint.const_mul _)) hpt
    _ = |Mf| * cutoffEnstrophy χ u t + 3 * |Mf| * ∫ x : Vec3, χ x ^ 2 := by
        rw [integral_add (hYint.const_mul _) (hchiint.const_mul _), integral_const_mul,
          integral_const_mul]
        rfl
    _ ≤ (|Mf| + 3 * |Mf| * (∫ x : Vec3, χ x ^ 2)) * (cutoffEnstrophy χ u t + 1) := by
        nlinarith only [hA, hIY]

end Force

/-! ### Stage (ii)(d): the two cutoff errors are bounded -/

/-- Three squares bounded by `M` sum to at most `3M²`. -/
private lemma sum3_sq_le {a : Fin 3 → ℝ} {M : ℝ} (h : ∀ i : Fin 3, |a i| ≤ M) :
    ∑ i : Fin 3, (a i) ^ 2 ≤ 3 * M ^ 2 := by
  have hterm : ∀ i : Fin 3, (a i) ^ 2 ≤ M ^ 2 := by
    intro i
    have hi := h i
    nlinarith only [hi, abs_nonneg (a i), sq_abs (a i)]
  simp only [Fin.sum_univ_three]
  linarith only [hterm 0, hterm 1, hterm 2]

/-- A three-term sum of products with a uniformly bounded factor. -/
private lemma abs_sum3_mul_le_mul_sum_abs {a b : Fin 3 → ℝ} {M : ℝ}
    (h : ∀ i : Fin 3, |b i| ≤ M) : |∑ i : Fin 3, a i * b i| ≤ M * ∑ i : Fin 3, |a i| := by
  have hterm : ∀ i : Fin 3, |a i * b i| ≤ M * |a i| := by
    intro i
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
  calc |∑ i : Fin 3, a i * b i| ≤ ∑ i : Fin 3, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, M * |a i| := Finset.sum_le_sum (fun i _ => hterm i)
    _ = M * ∑ i : Fin 3, |a i| := by rw [← Finset.mul_sum]

/-- Where `∇χ` vanishes, so does `∇(χ²)`. -/
private lemma dirDeriv_sq_eq_zero {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {y : Vec3}
    (h : fderiv ℝ χ y = 0) (j : Fin 3) :
    fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j) = 0 := by
  have hd := ((hχ.differentiable (by simp)).differentiableAt (x := y)).hasFDerivAt.pow 2
  rw [h] at hd
  rw [hd.fderiv]
  simp

/-- A directional derivative vanishes where the function vanishes near the point. -/
private lemma dirDeriv_eq_zero_of_eventuallyEq {F : Vec3 → ℝ} {x : Vec3}
    (h : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ)) (j : Fin 3) :
    fderiv ℝ F x (basisVec j) = 0 := by
  simp [h.fderiv_eq]

/-- Outside a closed set carrying `∇χ`, the second derivatives of `χ²` vanish as well. -/
private lemma dirDeriv_dirDeriv_sq_eq_zero {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {x : Vec3} (hx : x ∉ A) (j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
        (basisVec j) = 0 := by
  refine dirDeriv_eq_zero_of_eventuallyEq ?_ j
  filter_upwards [hAcl.isOpen_compl.mem_nhds hx] with y hy
  exact dirDeriv_sq_eq_zero hχ (hχA y hy) j

section CutoffErrors

variable {u : ParabolicPoint → Vec3}

/-- **The transport cutoff error is bounded.** The term `½ ∫ |ω|² u·∇(χ²)` produced by the
transport integration by parts is supported where `∇χ ≠ 0`, so the bounds for `|u|` and `|ω|`
there, on the time window `(t₀, 0)`, make it a constant. -/
theorem abs_integral_cutoff_gradient_error_le
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu Mω : ℝ} (hMu : 0 ≤ Mu)
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hωbd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |vorticityField u (x, t) i| ≤ Mω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ 0,
      |∫ x : Vec3, (∑ i : Fin 3, (vorticityField u (x, t) i) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j| ≤ C := by
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hsqU : tsupport (fun x : Vec3 => χ x ^ 2) ⊆ vec3Ball 0 1 :=
    (tsupport_sq_subset χ).trans hχU
  have hWcont : Continuous (fun x : Vec3 => ∑ j : Fin 3,
      |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)|) :=
    continuous_finsetSum Finset.univ (fun j _ => (continuous_dirDeriv hsqχ j).abs)
  have hWsupp : ∀ x : Vec3, x ∉ tsupport χ →
      ∑ j : Fin 3, |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| = 0 := by
    intro x hx
    have h : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) = 0 :=
      fun j => dirDeriv_zero_off_tsupport (fun hm => hx (tsupport_sq_subset χ hm)) j
    simp [h]
  have hWint : Integrable (fun x : Vec3 => ∑ j : Fin 3,
      |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)|) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hχs hWsupp)
  have hWnn : (0 : ℝ) ≤ ∫ x : Vec3, ∑ j : Fin 3,
      |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨3 * Mω ^ 2 * Mu * ∫ x : Vec3, ∑ j : Fin 3,
      |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)|, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 3 * Mω ^ 2 * Mu := by positivity
    exact mul_nonneg h1 hWnn
  intro t ht
  have ht1 : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hpt : ∀ x : Vec3, |(∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j|
        ≤ 3 * Mω ^ 2 * Mu * ∑ j : Fin 3,
            |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| := by
    intro x
    by_cases hx : x ∈ A
    · have hP : ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 ≤ 3 * Mω ^ 2 :=
        sum3_sq_le (fun i => hωbd x hx t ht i)
      have hPnn : (0 : ℝ) ≤ ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hQ : |∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j|
          ≤ Mu * ∑ j : Fin 3, |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| :=
        abs_sum3_mul_le_mul_sum_abs (fun j => hubd x hx t ht j)
      have hQnn : (0 : ℝ) ≤ Mu * ∑ j : Fin 3,
          |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| :=
        mul_nonneg hMu (Finset.sum_nonneg (fun j _ => abs_nonneg _))
      rw [abs_mul, abs_of_nonneg hPnn]
      have hstep := mul_le_mul hP hQ (abs_nonneg _) (by positivity)
      linarith only [hstep]
    · have h : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) = 0 :=
        fun j => dirDeriv_sq_eq_zero hχ (hχA x hx) j
      simp [h]
  have hLint : Integrable (fun x : Vec3 => (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j) := by
    refine integrable_of_cutoff hχs hχU
      ((contDiffOn_sumSqVorticity_slice hu ht1).continuousOn.mul
        (continuousOn_finsetSum Finset.univ (fun j _ =>
          (continuous_dirDeriv hsqχ j).continuousOn.mul (continuousOn_vel_slice hu j ht1))))
      (fun x hx => ?_)
    have h : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) = 0 :=
      fun j => dirDeriv_zero_off_tsupport (fun hm => hx (tsupport_sq_subset χ hm)) j
    simp [h]
  change |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j| ≤ _
  calc |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
        ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j|
      ≤ ∫ x : Vec3, |(∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, 3 * Mω ^ 2 * Mu * ∑ j : Fin 3,
          |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| :=
        integral_mono hLint.abs (hWint.const_mul _) hpt
    _ = 3 * Mω ^ 2 * Mu * ∫ x : Vec3, ∑ j : Fin 3,
          |fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)| := integral_const_mul _ _

/-- **The diffusion cutoff error is bounded.** The term `½ ∫ |ω|² Δ(χ²)` left by the second
integration by parts sees only `ω` itself, on the set where `χ` is not locally constant, and
on the time window `(t₀, 0)`. -/
theorem abs_integral_cutoff_laplacian_error_le
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mω : ℝ}
    (hωbd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |vorticityField u (x, t) i| ≤ Mω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ 0,
      |∫ x : Vec3, (∑ i : Fin 3, (vorticityField u (x, t) i) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
              (basisVec j)| ≤ C := by
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hsqs : HasCompactSupport (fun x : Vec3 => χ x ^ 2) := hasCompactSupport_sq hχs
  have hPj : ∀ j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) :=
    fun j => contDiff_dirDeriv hsqχ j
  have hPjs : ∀ j : Fin 3, HasCompactSupport
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j)) :=
    fun j => hasCompactSupport_dirDeriv hsqs j
  have hzero : ∀ (x : Vec3), x ∉ tsupport χ → ∀ j : Fin 3, fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) = 0 := by
    intro x hx j
    exact dirDeriv_zero_off_tsupport
      (fun hm => hx (tsupport_sq_subset χ ((tsupport_dirDeriv_subset _ j) hm))) j
  have hWcont : Continuous (fun x : Vec3 => ∑ j : Fin 3, |fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|) :=
    continuous_finsetSum Finset.univ (fun j _ => (continuous_dirDeriv (hPj j) j).abs)
  have hWsupp : ∀ x : Vec3, x ∉ tsupport χ → ∑ j : Fin 3, |fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)| = 0 := by
    intro x hx
    simp [hzero x hx]
  have hWint : Integrable (fun x : Vec3 => ∑ j : Fin 3, |fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hχs hWsupp)
  have hWnn : (0 : ℝ) ≤ ∫ x : Vec3, ∑ j : Fin 3, |fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)| :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨3 * Mω ^ 2 * ∫ x : Vec3, ∑ j : Fin 3, |fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|,
    ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 3 * Mω ^ 2 := by positivity
    exact mul_nonneg h1 hWnn
  intro t ht
  have ht1 : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hpt : ∀ x : Vec3, |(∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|
        ≤ 3 * Mω ^ 2 * ∑ j : Fin 3, |fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
              (basisVec j)| := by
    intro x
    by_cases hx : x ∈ A
    · have hP : ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 ≤ 3 * Mω ^ 2 :=
        sum3_sq_le (fun i => hωbd x hx t ht i)
      have hPnn : (0 : ℝ) ≤ ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hQ := Finset.abs_sum_le_sum_abs
        (fun j : Fin 3 => fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j))
        Finset.univ
      rw [abs_mul, abs_of_nonneg hPnn]
      have hstep := mul_le_mul hP hQ (abs_nonneg _) (by positivity)
      linarith only [hstep]
    · have h : ∀ j : Fin 3, fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j) = 0 :=
        fun j => dirDeriv_dirDeriv_sq_eq_zero hχ hAcl hχA hx j
      simp [h]
  have hLint : Integrable (fun x : Vec3 => (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)) := by
    refine integrable_of_cutoff hχs hχU
      ((contDiffOn_sumSqVorticity_slice hu ht1).continuousOn.mul
        (continuousOn_finsetSum Finset.univ (fun j _ =>
          (continuous_dirDeriv (hPj j) j).continuousOn)))
      (fun x hx => ?_)
    simp [hzero x hx]
  change |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)| ≤ _
  calc |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
        ∑ j : Fin 3, fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|
      ≤ ∫ x : Vec3, |(∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
              (basisVec j)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, 3 * Mω ^ 2 * ∑ j : Fin 3, |fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)| :=
        integral_mono hLint.abs (hWint.const_mul _) hpt
    _ = 3 * Mω ^ 2 * ∫ x : Vec3, ∑ j : Fin 3, |fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)| :=
        integral_const_mul _ _

end CutoffErrors

end CIV
