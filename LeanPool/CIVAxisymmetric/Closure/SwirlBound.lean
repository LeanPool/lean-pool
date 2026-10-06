/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AxisMaximumPrinciple
public import LeanPool.CIVAxisymmetric.Identities.WeightedSwirl
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Identities.PlaneTransfer
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm
public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient
public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The swirl bound `eq:aniso:closure:w`

The weighted swirl component `ψ = (−t)^η u_θ` obeys the parabolic equation
`weighted_swirl_pde` off the axis, with zeroth-order coefficient
`γ = r⁻² + u_r/r + η/(−t)`. When `η > 0` and the meridional quantity `G` is small enough
that `|u_r/r| ≤ η/(−t)` on `(t_η, 0)` (hypothesis `hG`), `γ ≥ 0`, and
`CIV.axisMaximumPrinciple` bounds `ψ` on the closed meridional half-disc by its parabolic
boundary values plus the accumulated source. This file assembles that bound, first on the
meridional plane (`swirl_bound`) and then, through the swirl coefficient `swirlCoeffAt`, at
every off-axis point of the ball (`swirl_bound_ball`).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-! ### The chain rule through the meridional embedding -/

section MeridionalChainRule

/-- First-order chain rule for a scalar composed with the `r`-directed meridional embedding.
The embedding's derivative is the public `CIV.hasDerivAt_meridional_fst` of
`CIV.Zoom.ChainRule` at unit radial speed. -/
private lemma hasDerivAt_comp_meridional_fst {g : Vec3 → ℝ} {r₀ x₃ : ℝ}
    (hg : DifferentiableAt ℝ g (meridional r₀ x₃)) :
    HasDerivAt (fun r : ℝ => g (meridional r x₃))
      (fderiv ℝ g (meridional r₀ x₃) (basisVec 0)) r₀ :=
  hg.hasFDerivAt.comp_hasDerivAt r₀
    (by simpa using hasDerivAt_meridional_fst 1 x₃ r₀)

/-- First-order chain rule for a scalar composed with the `z`-directed meridional embedding.
The embedding's derivative is the public `CIV.hasDerivAt_meridional_snd` of
`CIV.Zoom.ChainRule` at unit vertical speed and zero offset. -/
private lemma hasDerivAt_comp_meridional_snd {g : Vec3 → ℝ} {x₁ z₀ : ℝ}
    (hg : DifferentiableAt ℝ g (meridional x₁ z₀)) :
    HasDerivAt (fun z : ℝ => g (meridional x₁ z))
      (fderiv ℝ g (meridional x₁ z₀) (basisVec 2)) z₀ :=
  hg.hasFDerivAt.comp_hasDerivAt z₀
    (by simpa using hasDerivAt_meridional_snd x₁ 0 1 z₀)

/-- The preimage of the unit ball under the `r`-directed meridional embedding is open. -/
private lemma isOpen_meridional_fst_preimage (x₃ : ℝ) :
    IsOpen {r : ℝ | meridional r x₃ ∈ vec3Ball (0 : Vec3) 1} := by
  have hcont : Continuous (fun r : ℝ => meridional r x₃) := by unfold meridional; fun_prop
  exact (isOpen_vec3Ball 0 1).preimage hcont

/-- The preimage of the unit ball under the `z`-directed meridional embedding is open. -/
private lemma isOpen_meridional_snd_preimage (x₁ : ℝ) :
    IsOpen {z : ℝ | meridional x₁ z ∈ vec3Ball (0 : Vec3) 1} := by
  have hcont : Continuous (fun z : ℝ => meridional x₁ z) := by unfold meridional; fun_prop
  exact (isOpen_vec3Ball 0 1).preimage hcont

/-- Second-order chain rule for a scalar composed with the `r`-directed meridional embedding:
the second derivative of `r ↦ g (meridional r x₃)` at `r₀` is the corresponding iterated
Fréchet derivative of `g`. -/
private lemma hasDerivAt_deriv_comp_meridional_fst {g : Vec3 → ℝ} {r₀ x₃ : ℝ}
    (hg : ContDiffOn ℝ 2 g (vec3Ball (0 : Vec3) 1))
    (hmem : meridional r₀ x₃ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun r : ℝ => deriv (fun r' : ℝ => g (meridional r' x₃)) r)
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 0)) (meridional r₀ x₃) (basisVec 0))
      r₀ := by
  have hg1 : DifferentiableOn ℝ g (vec3Ball (0 : Vec3) 1) :=
    (hg.of_le (by norm_num)).differentiableOn_one
  have heq : (fun r : ℝ => deriv (fun r' : ℝ => g (meridional r' x₃)) r)
      =ᶠ[nhds r₀] (fun r : ℝ => fderiv ℝ g (meridional r x₃) (basisVec 0)) := by
    filter_upwards [(isOpen_meridional_fst_preimage x₃).mem_nhds hmem] with r hr
    exact (hasDerivAt_comp_meridional_fst
      (hg1.differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hr))).deriv
  have h_contDiff_fderiv : ContDiffOn ℝ 1 (fderiv ℝ g) (vec3Ball (0 : Vec3) 1) :=
    hg.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  have h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ g) (meridional r₀ x₃) :=
    (h_contDiff_fderiv.differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hmem)
  have hgd : DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 0)) (meridional r₀ x₃) :=
    h_diff_fderiv.clm_apply (differentiableAt_const _)
  exact (hasDerivAt_comp_meridional_fst hgd).congr_of_eventuallyEq heq

/-- Second-order chain rule for a scalar composed with the `z`-directed meridional embedding. -/
private lemma hasDerivAt_deriv_comp_meridional_snd {g : Vec3 → ℝ} {x₁ z₀ : ℝ}
    (hg : ContDiffOn ℝ 2 g (vec3Ball (0 : Vec3) 1))
    (hmem : meridional x₁ z₀ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun z : ℝ => deriv (fun z' : ℝ => g (meridional x₁ z')) z)
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 2)) (meridional x₁ z₀) (basisVec 2))
      z₀ := by
  have hg1 : DifferentiableOn ℝ g (vec3Ball (0 : Vec3) 1) :=
    (hg.of_le (by norm_num)).differentiableOn_one
  have heq : (fun z : ℝ => deriv (fun z' : ℝ => g (meridional x₁ z')) z)
      =ᶠ[nhds z₀] (fun z : ℝ => fderiv ℝ g (meridional x₁ z) (basisVec 2)) := by
    filter_upwards [(isOpen_meridional_snd_preimage x₁).mem_nhds hmem] with z hz
    exact (hasDerivAt_comp_meridional_snd
      (hg1.differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hz))).deriv
  have h_contDiff_fderiv : ContDiffOn ℝ 1 (fderiv ℝ g) (vec3Ball (0 : Vec3) 1) :=
    hg.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  have h_diff_fderiv : DifferentiableAt ℝ (fderiv ℝ g) (meridional x₁ z₀) :=
    (h_contDiff_fderiv.differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hmem)
  have hgd : DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ g y (basisVec 2)) (meridional x₁ z₀) :=
    h_diff_fderiv.clm_apply (differentiableAt_const _)
  exact (hasDerivAt_comp_meridional_snd hgd).congr_of_eventuallyEq heq

end MeridionalChainRule

/-! ### The weighted swirl profile and its translation into `dr`, `dz`, `dtPast` -/

section Profile

/-- The weighted swirl component `(−t)^η u_θ`, read as a function of the spatial point alone
at a fixed time `t`. -/
@[expose] private def swirlSlice (η : ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) (y : Vec3) : ℝ :=
  (-t) ^ η * u (y, t) 1

/-- The weighted swirl profile `ψ ((r, z), t) = (−t)^η u_θ (meridional r z, t)` on the
meridional half-plane, the function to which `CIV.axisMaximumPrinciple` is applied. -/
@[expose] private def swirlProfile (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  swirlSlice η u p.2 (meridional p.1.1 p.1.2)

/-- The time slice `s ↦ (−s)^η u_θ (z.1, s)` of the weighted swirl component is differentiable
at an interior time. -/
private lemma differentiableAt_weighted_swirl_time (η : ℝ) (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => (-s) ^ η * u (z.1, s) 1) z.2 := by
  have hz_time : z.2 ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hpos : 0 < -z.2 := by linarith only [hz_time.2]
  have hneg : -z.2 ≠ 0 := by linarith only [hpos]
  have h_weight_hasDerivAt : HasDerivAt (fun t : ℝ => (-t) ^ η) (-η * (-z.2) ^ (η - 1)) z.2 := by
    have h_neg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) z.2 := by
      simpa [neg_one_mul] using (hasDerivAt_id z.2).const_mul (-1)
    have h_rpow : HasDerivAt (fun t : ℝ => t ^ η) (η * (-z.2) ^ (η - 1)) (-z.2) :=
      Real.hasDerivAt_rpow_const (Or.inl hneg)
    have h_comp : HasDerivAt (fun t : ℝ => (-t) ^ η) (η * (-z.2) ^ (η - 1) * (-1)) z.2 :=
      h_rpow.comp z.2 h_neg
    rw [show η * (-z.2) ^ (η - 1) * (-1) = -η * (-z.2) ^ (η - 1) from by ring] at h_comp
    exact h_comp
  have h_cont : ContDiffOn ℝ 1 (fun s : ℝ => u (z.1, s)) (Ioo (-1 : ℝ) 0) :=
    hu1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s hs => ⟨hz.1, hs⟩)
  have h_diff_at : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s)) z.2 :=
    h_cont.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hz.2)
  have h_diff_time_slice : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 1) z.2 :=
    differentiableAt_pi.1 h_diff_at 1
  exact (h_weight_hasDerivAt.mul h_diff_time_slice.hasDerivAt).differentiableAt

/-- `dtPast` of the swirl profile is the weighted swirl equation's `timePartial`, at an
interior time: the one-sided derivative agrees with the two-sided one because the swirl
profile is differentiable there. -/
private lemma dtPast_swirlProfile_eq (η : ℝ) (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) (p : (ℝ × ℝ) × ℝ)
    (hz : ((meridional p.1.1 p.1.2, p.2) : ParabolicPoint) ∈ unitCylinder) :
    dtPast (swirlProfile η u) p
      = timePartial (fun w => (-w.2) ^ η * u w 1) (meridional p.1.1 p.1.2, p.2) := by
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => (-s) ^ η * u (meridional p.1.1 p.1.2, s) 1) p.2 :=
    differentiableAt_weighted_swirl_time η u hu1 hz
  show derivWithin (fun t : ℝ => (-t) ^ η * u (meridional p.1.1 p.1.2, t) 1) (Iic p.2) p.2 = _
  rw [hdiff.derivWithin (uniqueDiffWithinAt_Iic p.2)]
  rfl

/-- `dr` of the swirl profile is the weighted swirl equation's `spatialPartial` in the first
coordinate. -/
private lemma dr_swirlProfile_eq (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hdiff : DifferentiableAt ℝ (swirlSlice η u p.2) (meridional p.1.1 p.1.2)) :
    dr (swirlProfile η u) p
      = spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 (meridional p.1.1 p.1.2, p.2) := by
  show deriv (fun r : ℝ => swirlSlice η u p.2 (meridional r p.1.2)) p.1.1 = _
  rw [(hasDerivAt_comp_meridional_fst hdiff).deriv]
  rfl

/-- `dz` of the swirl profile is the weighted swirl equation's `spatialPartial` in the third
coordinate. -/
private lemma dz_swirlProfile_eq (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hdiff : DifferentiableAt ℝ (swirlSlice η u p.2) (meridional p.1.1 p.1.2)) :
    dz (swirlProfile η u) p
      = spatialPartial (fun w => (-w.2) ^ η * u w 1) 2 (meridional p.1.1 p.1.2, p.2) := by
  show deriv (fun z : ℝ => swirlSlice η u p.2 (meridional p.1.1 z)) p.1.2 = _
  rw [(hasDerivAt_comp_meridional_snd hdiff).deriv]
  rfl

/-- `dr (dr ·)` of the swirl profile is the weighted swirl equation's iterated `spatialPartial`
in the first coordinate. -/
private lemma dr_dr_swirlProfile_eq (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hg : ContDiffOn ℝ 2 (swirlSlice η u p.2) (vec3Ball (0 : Vec3) 1))
    (hmem : meridional p.1.1 p.1.2 ∈ vec3Ball (0 : Vec3) 1) :
    dr (dr (swirlProfile η u)) p
      = spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 0 0 (meridional p.1.1 p.1.2, p.2) := by
  show deriv (fun r : ℝ => deriv (fun r' : ℝ => swirlSlice η u p.2 (meridional r' p.1.2)) r)
      p.1.1 = _
  rw [(hasDerivAt_deriv_comp_meridional_fst hg hmem).deriv]
  rfl

/-- `dz (dz ·)` of the swirl profile is the weighted swirl equation's iterated `spatialPartial`
in the third coordinate. -/
private lemma dz_dz_swirlProfile_eq (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hg : ContDiffOn ℝ 2 (swirlSlice η u p.2) (vec3Ball (0 : Vec3) 1))
    (hmem : meridional p.1.1 p.1.2 ∈ vec3Ball (0 : Vec3) 1) :
    dz (dz (swirlProfile η u)) p
      = spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 2 2 (meridional p.1.1 p.1.2, p.2) := by
  show deriv (fun z : ℝ => deriv (fun z' : ℝ => swirlSlice η u p.2 (meridional p.1.1 z')) z)
      p.1.2 = _
  rw [(hasDerivAt_deriv_comp_meridional_snd hg hmem).deriv]
  rfl

end Profile

/-! ### The drift, zeroth-order coefficient and source, and the translated PDE -/

section Pde

/-- The radial drift `u_r`, read on the meridional plane. -/
@[expose] private def swirlDriftR (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  u (meridional p.1.1 p.1.2, p.2) 0

/-- The vertical drift `u_z`, read on the meridional plane. -/
@[expose] private def swirlDriftZ (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  u (meridional p.1.1 p.1.2, p.2) 2

/-- The zeroth-order coefficient `γ = r⁻² + u_r/r + η/(−t)` of the weighted swirl equation. -/
@[expose] private def swirlZeroth (η : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  1 / p.1.1 ^ 2 + u (meridional p.1.1 p.1.2, p.2) 0 / p.1.1 + η / (-p.2)

/-- The weighted source `(−t)^η f_θ`, read on the meridional plane. -/
@[expose] private def swirlSource (η : ℝ) (f : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (-p.2) ^ η * f (meridional p.1.1 p.1.2, p.2) 1

/-- The weighted swirl equation, translated into the profile derivatives `dr`, `dz`, `dtPast`
that `CIV.axisMaximumPrinciple` requires. -/
private lemma hpde_swirlProfile (η : ℝ) (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (a b t : ℝ) (hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder) (ha : a ≠ 0) :
    dtPast (swirlProfile η u) ((a, b), t)
        + swirlDriftR u ((a, b), t) * dr (swirlProfile η u) ((a, b), t)
        + swirlDriftZ u ((a, b), t) * dz (swirlProfile η u) ((a, b), t)
        + swirlZeroth η u ((a, b), t) * swirlProfile η u ((a, b), t)
      = dr (dr (swirlProfile η u)) ((a, b), t) + 1 / a * dr (swirlProfile η u) ((a, b), t)
        + dz (dz (swirlProfile η u)) ((a, b), t) + swirlSource η f ((a, b), t) := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hswirl :
      timePartial (fun w => (-w.2) ^ η * u w 1) (meridional a b, t)
          + u (meridional a b, t) 0
              * spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 (meridional a b, t)
          + u (meridional a b, t) 2
              * spatialPartial (fun w => (-w.2) ^ η * u w 1) 2 (meridional a b, t)
          - (spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 0 0 (meridional a b, t)
              + spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 (meridional a b, t) / a
              + spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 2 2 (meridional a b, t))
          + (1 / a ^ 2 + u (meridional a b, t) 0 / a + η / (-t))
              * ((-t) ^ η * u (meridional a b, t) 1)
        = (-t) ^ η * f (meridional a b, t) 1 :=
    weighted_swirl_pde η u pr f hsol haxi hfaxi (meridional a b, t) hz rfl ha
  have hdiff1 : DifferentiableAt ℝ (swirlSlice η u t) (meridional a b) := by
    have hcomp : DifferentiableAt ℝ (fun y : Vec3 => u (y, t) 1) (meridional a b) :=
      differentiableAt_spatialSlice (contDiffOn_component hu1 1) hz
    exact hcomp.const_mul _
  have hdiff2 : ContDiffOn ℝ 2 (swirlSlice η u t) (vec3Ball (0 : Vec3) 1) := by
    have hspatial := contDiffOn_spatialSlice (contDiffOn_component hu2 1) hz.2
    have hmul : ContDiffOn ℝ 2 (fun y : Vec3 => (-t) ^ η * u (y, t) 1) (vec3Ball (0 : Vec3) 1) :=
      contDiffOn_const.mul hspatial
    exact hmul
  have hmemball : meridional a b ∈ vec3Ball (0 : Vec3) 1 := hz.1
  have hdt : dtPast (swirlProfile η u) ((a, b), t)
      = timePartial (fun w => (-w.2) ^ η * u w 1) (meridional a b, t) :=
    dtPast_swirlProfile_eq η u hu1 ((a, b), t) hz
  have hdr : dr (swirlProfile η u) ((a, b), t)
      = spatialPartial (fun w => (-w.2) ^ η * u w 1) 0 (meridional a b, t) :=
    dr_swirlProfile_eq η u ((a, b), t) hdiff1
  have hdz : dz (swirlProfile η u) ((a, b), t)
      = spatialPartial (fun w => (-w.2) ^ η * u w 1) 2 (meridional a b, t) :=
    dz_swirlProfile_eq η u ((a, b), t) hdiff1
  have hdrdr : dr (dr (swirlProfile η u)) ((a, b), t)
      = spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 0 0 (meridional a b, t) :=
    dr_dr_swirlProfile_eq η u ((a, b), t) hdiff2 hmemball
  have hdzdz : dz (dz (swirlProfile η u)) ((a, b), t)
      = spatialSecondPartial (fun w => (-w.2) ^ η * u w 1) 2 2 (meridional a b, t) :=
    dz_dz_swirlProfile_eq η u ((a, b), t) hdiff2 hmemball
  have hswirlDriftR : swirlDriftR u ((a, b), t) = u (meridional a b, t) 0 := rfl
  have hswirlDriftZ : swirlDriftZ u ((a, b), t) = u (meridional a b, t) 2 := rfl
  have hswirlZeroth : swirlZeroth η u ((a, b), t)
      = 1 / a ^ 2 + u (meridional a b, t) 0 / a + η / (-t) := rfl
  have hswirlProfile : swirlProfile η u ((a, b), t) = (-t) ^ η * u (meridional a b, t) 1 := rfl
  have hswirlSource : swirlSource η f ((a, b), t) = (-t) ^ η * f (meridional a b, t) 1 := rfl
  rw [hdt, hdr, hdz, hdrdr, hdzdz, hswirlDriftR, hswirlDriftZ, hswirlZeroth, hswirlProfile,
    hswirlSource]
  linear_combination hswirl

end Pde

/-! ### Embedding the meridional half-disc in the unit cylinder -/

section Embedding

/-- The affine embedding `(y₁, y₂) ↦ (y₁, 0, y₂)` of the meridional plane is everywhere
smooth. -/
private lemma contDiff_meridional_embed :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3)) := by
  have heq : (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3))
      = fun y : ℝ × ℝ => y.1 • (basisVec 0 : Vec3) + y.2 • basisVec 2 := by
    funext y
    ext i
    fin_cases i <;> simp [meridional, basisVec_apply]
  rw [heq]
  exact (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)

/-- A meridional point at radius `≤ Rstar < 1` and a time in `(−1, 0)` lies in the unit
cylinder. -/
private lemma meridional_mem_unitCylinder_of_lt_one {r z t Rstar : ℝ}
    (hR1 : Rstar < 1) (hRpos : 0 < Rstar) (hrz : r ^ 2 + z ^ 2 ≤ Rstar ^ 2)
    (htη1 : -1 < t) (ht0 : t < 0) :
    ((meridional r z, t) : ParabolicPoint) ∈ unitCylinder := by
  rw [meridional_mem_unitCylinder_iff]
  refine ⟨?_, htη1, ht0⟩
  have hRsq : Rstar ^ 2 < 1 := by nlinarith only [hR1, hRpos]
  linarith only [hrz, hRsq]

end Embedding

/-! ### The hypotheses of `CIV.axisMaximumPrinciple` for the swirl profile -/

section MaximumPrincipleHypotheses

variable (η : ℝ) (u : ParabolicPoint → Vec3)

/-- The swirl profile is continuous on the closed meridional half-disc. -/
private lemma continuousOn_swirlProfile
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ContinuousOn (swirlProfile η u) (axisClosedDomain Rstar tη s) := by
  have hmaps : Set.MapsTo (fun p : (ℝ × ℝ) × ℝ => ((meridional p.1.1 p.1.2, p.2) : Vec3 × ℝ))
      (axisClosedDomain Rstar tη s) unitCylinder := by
    rintro p ⟨-, hrz, ht1, ht2⟩
    exact meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz (lt_of_lt_of_le htη1 ht1)
      (lt_of_le_of_lt ht2 hs0)
  have hcont_e : Continuous
      (fun p : (ℝ × ℝ) × ℝ => ((meridional p.1.1 p.1.2, p.2) : Vec3 × ℝ)) :=
    (contDiff_meridional_embed.continuous.comp continuous_fst).prodMk continuous_snd
  have hcont1 : ContinuousOn (fun w : Vec3 × ℝ => u w 1) unitCylinder :=
    (contDiffOn_component hu1 1).continuousOn
  have hF_cont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => u (meridional p.1.1 p.1.2, p.2) 1)
      (axisClosedDomain Rstar tη s) :=
    hcont1.comp hcont_e.continuousOn hmaps
  have hweight_cont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => (-p.2) ^ η)
      (axisClosedDomain Rstar tη s) := by
    refine ContinuousOn.rpow_const (continuous_neg.comp continuous_snd).continuousOn ?_
    rintro p ⟨-, -, -, hp2⟩
    exact Or.inl (by linarith only [lt_of_le_of_lt hp2 hs0])
  exact hweight_cont.mul hF_cont

/-- The swirl profile vanishes on the axis. -/
private lemma haxis_swirlProfile (haxi : IsAxisymmetricOn u unitCylinder)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ∀ zc tc : ℝ, |zc| ≤ Rstar → tη ≤ tc → tc ≤ s → swirlProfile η u ((0, zc), tc) = 0 := by
  intro zc tc hzc htc1 htc2
  have hrz : (0 : ℝ) ^ 2 + zc ^ 2 ≤ Rstar ^ 2 := by
    nlinarith only [abs_le.mp hzc |>.1, abs_le.mp hzc |>.2, hRpos.le]
  have hmem : ((meridional 0 zc, tc) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz (by linarith only [htη1, htc1])
      (lt_of_le_of_lt htc2 hs0)
  have hzero : u (meridional 0 zc, tc) 1 = 0 := apply_axis_one haxi hmem rfl rfl
  show (-tc) ^ η * u (meridional 0 zc, tc) 1 = 0
  rw [hzero, mul_zero]

/-- The swirl profile is `C²` in space and differentiable within `Iic` in time, at every
interior point of the meridional half-disc. -/
private lemma hreg_swirlProfile
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ∀ p ∈ axisDomain Rstar tη s,
      ContDiffAt ℝ 2 (fun y : ℝ × ℝ => swirlProfile η u (y, p.2)) p.1 ∧
        DifferentiableWithinAt ℝ (fun t : ℝ => swirlProfile η u (p.1, t)) (Iic p.2) p.2 := by
  rintro ⟨⟨a, b⟩, t⟩ ⟨-, hab, ht1, ht2⟩
  have hrz : a ^ 2 + b ^ 2 ≤ Rstar ^ 2 := hab.le
  have hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz (lt_of_lt_of_le htη1 ht1.le)
      (lt_of_le_of_lt ht2 hs0)
  refine ⟨?_, ?_⟩
  · have hu_at : ContDiffAt ℝ 2 (fun y : Vec3 => u (y, t) 1) (meridional a b) :=
      (contDiffOn_spatialSlice (contDiffOn_component hu2 1) hz.2).contDiffAt
        ((isOpen_vec3Ball 0 1).mem_nhds hz.1)
    have hemb_at : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3)) (a, b) :=
      (contDiff_meridional_embed.of_le (by norm_num)).contDiffAt
    have hcompose : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => u (meridional y.1 y.2, t) 1) (a, b) :=
      hu_at.fun_comp (a, b) hemb_at
    have : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (-t) ^ η * u (meridional y.1 y.2, t) 1) (a, b) :=
      contDiffAt_const.mul hcompose
    exact this
  · have hdiff : DifferentiableAt ℝ (fun s' : ℝ => (-s') ^ η * u (meridional a b, s') 1) t :=
      differentiableAt_weighted_swirl_time η u hu1 hz
    exact hdiff.differentiableWithinAt

/-- The zeroth-order coefficient `γ = r⁻² + u_r/r + η/(−t)` is nonnegative on the meridional
half-disc, using the smallness hypothesis `hG` on `u_r/r = radialQuotient u`. -/
private lemma hγ_swirlProfile (Rstar tη : ℝ) (hRpos : 0 < Rstar)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    (s : ℝ) (hs0 : s < 0) :
    ∀ p ∈ axisDomain Rstar tη s, 0 ≤ swirlZeroth η u p := by
  rintro ⟨⟨a, b⟩, t⟩ ⟨ha0, hab, ht1, ht2⟩
  have htmem : t ∈ Ioo tη (0 : ℝ) := ⟨ht1, lt_of_le_of_lt ht2 hs0⟩
  have hmem : meridional a b ∈ vec3Ball (0 : Vec3) Rstar :=
    (meridional_mem_vec3Ball_zero_iff a b Rstar).2 ⟨hab, hRpos⟩
  have hbound := hG t htmem a b hmem
  have hrq : radialQuotient u (meridional a b, t) = u (meridional a b, t) 0 / a := by
    unfold radialQuotient
    split_ifs with hcase
    · exact absurd hcase ha0.ne'
    · rfl
  rw [hrq] at hbound
  have habs := abs_le.mp hbound
  show 0 ≤ 1 / a ^ 2 + u (meridional a b, t) 0 / a + η / (-t)
  have h1 : (0 : ℝ) ≤ 1 / a ^ 2 := by positivity
  linarith only [h1, habs.1]

/-- The weighted source `(−t)^η f_θ` is bounded on the meridional half-disc by
`(−t_η)^η M_f`, using monotonicity of `(−t)^η` for `t_η < t < 0` and `η > 0`. -/
private lemma hF_swirlProfile (f : ParabolicPoint → Vec3)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar tη : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hη : 0 < η) (htη1 : -1 < tη)
    (s : ℝ) (hs0 : s < 0) :
    ∀ p ∈ axisDomain Rstar tη s, |swirlSource η f p| ≤ (-tη) ^ η * Mf := by
  rintro ⟨⟨a, b⟩, t⟩ ⟨ha0, hab, ht1, ht2⟩
  have hrz : a ^ 2 + b ^ 2 ≤ Rstar ^ 2 := hab.le
  have ht0 : t < 0 := lt_of_le_of_lt ht2 hs0
  have hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz (lt_of_lt_of_le htη1 ht1.le) ht0
  have hfbound : |f (meridional a b, t) 1| ≤ Mf := hMf _ hz
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) hfbound
  have htpos : 0 ≤ -t := by linarith only [ht0]
  have hrpow_le : (-t) ^ η ≤ (-tη) ^ η :=
    Real.rpow_le_rpow htpos (by linarith only [ht1]) hη.le
  have hrpow_nonneg : 0 ≤ (-t) ^ η := Real.rpow_nonneg htpos η
  show |(-t) ^ η * f (meridional a b, t) 1| ≤ (-tη) ^ η * Mf
  rw [abs_mul, abs_of_nonneg hrpow_nonneg]
  calc (-t) ^ η * |f (meridional a b, t) 1| ≤ (-t) ^ η * Mf :=
        mul_le_mul_of_nonneg_left hfbound hrpow_nonneg
    _ ≤ (-tη) ^ η * Mf := mul_le_mul_of_nonneg_right hrpow_le hMf_nonneg

end MaximumPrincipleHypotheses

/-! ### The boundary bound, including the corner shared by the two pieces -/

section Boundary

/-- At the corner `t = t_η`, `r² + z² = R_*²` shared by the two pieces of the parabolic
boundary, the swirl is bounded by `M_i`: it is the limit, along `c ↑ 1`, of its values
`u (meridional (c r) (c z), τ)` on the open ball `vec3Ball 0 R_*` where `hinit` applies. -/
private lemma abs_swirl_boundary_corner_le (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar τ Mi : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hτ1 : -1 < τ) (hτ2 : τ < 0)
    (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, τ) 1| ≤ Mi)
    (r z : ℝ) (hrz : r ^ 2 + z ^ 2 = Rstar ^ 2) :
    |u (meridional r z, τ) 1| ≤ Mi := by
  have hτmem : τ ∈ Ioo (-1 : ℝ) 0 := ⟨hτ1, hτ2⟩
  have hmem_cyl : ((meridional r z, τ) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz.le hτ1 hτ2
  have hspatial : ContDiffOn ℝ 1 (fun y : Vec3 => u (y, τ) 1) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_spatialSlice (contDiffOn_component hu1 1) hτmem
  have hcont : ContinuousAt (fun y : Vec3 => u (y, τ) 1) (meridional r z) :=
    hspatial.continuousOn.continuousAt ((isOpen_vec3Ball 0 1).mem_nhds hmem_cyl.1)
  have hg_tendsto : Filter.Tendsto (fun y : Vec3 => u (y, τ) 1) (nhds (meridional r z))
      (nhds (u (meridional r z, τ) 1)) := hcont
  have hpath : Continuous (fun c : ℝ => meridional (c * r) (c * z)) := by
    unfold meridional; fun_prop
  have hf_tendsto : Filter.Tendsto (fun c : ℝ => meridional (c * r) (c * z))
      (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)) (nhds (meridional r z)) := by
    have hbase : Filter.Tendsto (fun c : ℝ => meridional (c * r) (c * z)) (nhds (1 : ℝ))
        (nhds (meridional (1 * r) (1 * z))) := hpath.continuousAt
    rw [one_mul, one_mul] at hbase
    exact hbase.mono_left nhdsWithin_le_nhds
  have hcomp : Filter.Tendsto (fun c : ℝ => u (meridional (c * r) (c * z), τ) 1)
      (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)) (nhds (u (meridional r z, τ) 1)) :=
    hg_tendsto.comp hf_tendsto
  have hnorm : vec3EuclideanNorm (meridional r z) = Rstar := by
    rw [vec3EuclideanNorm_meridional, hrz]
    exact Real.sqrt_sq hRpos.le
  have hbound : ∀ c ∈ Set.Ioo (0 : ℝ) 1, |u (meridional (c * r) (c * z), τ) 1| ≤ Mi := by
    intro c hc
    refine hinit (meridional (c * r) (c * z)) ?_
    rw [mem_vec3Ball, sub_zero, vec3EuclideanNorm_meridional]
    have hsq : (c * r) ^ 2 + (c * z) ^ 2 = (c * Rstar) ^ 2 := by
      rw [show (c * Rstar) ^ 2 = c ^ 2 * Rstar ^ 2 from by ring, ← hrz]; ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (by nlinarith only [hc.1, hRpos] : (0 : ℝ) < c *
      Rstar)]
    exact mul_lt_of_lt_one_left hRpos hc.2
  have : (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
    right_nhdsWithin_Ioo_neBot (show (0 : ℝ) < 1 by norm_num)
  have habs_tendsto : Filter.Tendsto (fun c : ℝ => |u (meridional (c * r) (c * z), τ) 1|)
      (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)) (nhds |u (meridional r z, τ) 1|) :=
    (continuous_abs.tendsto _).comp hcomp
  exact le_of_tendsto habs_tendsto (Filter.eventually_of_mem self_mem_nhdsWithin hbound)

/-- The swirl profile is bounded on the parabolic boundary `axisParabolicBoundary Rstar tη s`
by `(−t_η)^η max(M_b, M_i)`: `hinit` on the open ball at `t = t_η`, `hbdry` on the sphere for
`t_η < t ≤ s`, and the corner where they meet by continuity. -/
private lemma abs_swirlProfile_le_boundary (η : ℝ) (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar tη : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hη : 0 < η) (htη1 : -1 < tη)
    (htη2 : tη < 0) (Mb Mi : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |u (x, t) 1| ≤ Mb)
    (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi)
    (s : ℝ) (hs0 : s < 0) :
    ∀ p ∈ axisParabolicBoundary Rstar tη s, |swirlProfile η u p| ≤ (-tη) ^ η * max Mb Mi := by
  have hrpow_tη_nonneg : 0 ≤ (-tη) ^ η := Real.rpow_nonneg (by linarith only [htη2]) η
  rintro ⟨⟨a, b⟩, t⟩ hp
  rcases hp with hinit_piece | hbdry_piece
  · obtain ⟨_ha0, hab, ht⟩ := hinit_piece
    have ht_eq : t = tη := ht
    show |(-t) ^ η * u (meridional a b, t) 1| ≤ (-tη) ^ η * max Mb Mi
    rw [ht_eq, abs_mul, abs_of_nonneg hrpow_tη_nonneg]
    rcases hab.lt_or_eq with hab' | hab'
    · have hmem : meridional a b ∈ vec3Ball (0 : Vec3) Rstar :=
        (meridional_mem_vec3Ball_zero_iff a b Rstar).2 ⟨hab', hRpos⟩
      have hb := hinit _ hmem
      calc (-tη) ^ η * |u (meridional a b, tη) 1| ≤ (-tη) ^ η * Mi :=
            mul_le_mul_of_nonneg_left hb hrpow_tη_nonneg
        _ ≤ (-tη) ^ η * max Mb Mi := mul_le_mul_of_nonneg_left (le_max_right _ _) hrpow_tη_nonneg
    · have hcorner : |u (meridional a b, tη) 1| ≤ Mi :=
        abs_swirl_boundary_corner_le u hu1 Rstar tη Mi hRpos hR1 htη1 htη2 hinit a b hab'
      calc (-tη) ^ η * |u (meridional a b, tη) 1| ≤ (-tη) ^ η * Mi :=
            mul_le_mul_of_nonneg_left hcorner hrpow_tη_nonneg
        _ ≤ (-tη) ^ η * max Mb Mi := mul_le_mul_of_nonneg_left (le_max_right _ _) hrpow_tη_nonneg
  · obtain ⟨_ha0, hab, ht1, ht2⟩ := hbdry_piece
    have ht0 : t < 0 := lt_of_le_of_lt ht2 hs0
    have hrpow_t_nonneg : 0 ≤ (-t) ^ η := Real.rpow_nonneg (by linarith only [ht0]) η
    show |(-t) ^ η * u (meridional a b, t) 1| ≤ (-tη) ^ η * max Mb Mi
    rw [abs_mul, abs_of_nonneg hrpow_t_nonneg]
    rcases ht1.lt_or_eq with ht1' | ht1'
    · have htmem : t ∈ Ioo tη (0 : ℝ) := ⟨ht1', ht0⟩
      have hnorm : vec3EuclideanNorm (meridional a b) = Rstar := by
        rw [vec3EuclideanNorm_meridional, hab]
        exact Real.sqrt_sq hRpos.le
      have hb := hbdry (meridional a b) hnorm t htmem
      have hrpow_le : (-t) ^ η ≤ (-tη) ^ η :=
        Real.rpow_le_rpow (by linarith only [ht0]) (by linarith only [ht1']) hη.le
      have hMb_nonneg : 0 ≤ Mb := le_trans (abs_nonneg _) hb
      calc (-t) ^ η * |u (meridional a b, t) 1| ≤ (-t) ^ η * Mb :=
            mul_le_mul_of_nonneg_left hb hrpow_t_nonneg
        _ ≤ (-tη) ^ η * Mb := mul_le_mul_of_nonneg_right hrpow_le hMb_nonneg
        _ ≤ (-tη) ^ η * max Mb Mi := mul_le_mul_of_nonneg_left (le_max_left _ _) hrpow_tη_nonneg
    · have ht1'_eq : tη = t := ht1'
      rw [← ht1'_eq]
      have hcorner : |u (meridional a b, tη) 1| ≤ Mi :=
        abs_swirl_boundary_corner_le u hu1 Rstar tη Mi hRpos hR1 htη1 htη2 hinit a b hab
      calc (-tη) ^ η * |u (meridional a b, tη) 1| ≤ (-tη) ^ η * Mi :=
            mul_le_mul_of_nonneg_left hcorner hrpow_tη_nonneg
        _ ≤ (-tη) ^ η * max Mb Mi := mul_le_mul_of_nonneg_left (le_max_right _ _) hrpow_tη_nonneg

end Boundary

/-! ### The swirl bound, `eq:aniso:closure:w`, on the meridional plane -/

section SwirlBound

/-- The swirl bound at a meridional point with `r ≥ 0`: the maximum principle
`CIV.axisMaximumPrinciple`, applied to the weighted swirl profile with drift `(u_r, u_z)`,
zeroth-order coefficient `γ = r⁻² + u_r/r + η/(−t) ≥ 0` (from `hG`) and source `(−t)^η f_θ`. -/
private lemma swirl_bound_core (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1)
    (tη η : ℝ) (htη1 : -1 < tη) (htη2 : tη < 0) (hη : 0 < η)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |u (x, t) 1| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi)
    (t : ℝ) (htη_lt : tη < t) (ht0 : t < 0)
    (r z : ℝ) (hr0 : 0 ≤ r) (hrz : r ^ 2 + z ^ 2 < Rstar ^ 2) :
    (-t) ^ η * |u (meridional r z, t) 1|
      ≤ (-tη) ^ η * max Mb Mi + (-tη) ^ η * Mf * (t - tη) := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have ht_range : (-1 : ℝ) < t := lt_trans htη1 htη_lt
  have hzmem : ((meridional r z, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_lt_one hR1 hRpos hrz.le ht_range ht0
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf _ hzmem)
  have hrpow_tη_nonneg : 0 ≤ (-tη) ^ η := Real.rpow_nonneg (by linarith only [htη2]) η
  have hM : (0 : ℝ) ≤ (-tη) ^ η * Mf := mul_nonneg hrpow_tη_nonneg hMf_nonneg
  have hcont : ContinuousOn (swirlProfile η u) (axisClosedDomain Rstar tη t) :=
    continuousOn_swirlProfile η u hu1 Rstar tη t hRpos hR1 ht0 htη1
  have haxis : ∀ zc tc : ℝ, |zc| ≤ Rstar → tη ≤ tc → tc ≤ t →
      swirlProfile η u ((0, zc), tc) = 0 :=
    haxis_swirlProfile η u haxi Rstar tη t hRpos hR1 ht0 htη1
  have hreg := hreg_swirlProfile η u hu1 hu2 Rstar tη t hRpos hR1 ht0 htη1
  have hγ := hγ_swirlProfile η u Rstar tη hRpos hG t ht0
  have hF := hF_swirlProfile η f Mf hMf Rstar tη hRpos hR1 hη htη1 t ht0
  have hpde : ∀ p ∈ axisDomain Rstar tη t,
      dtPast (swirlProfile η u) p + swirlDriftR u p * dr (swirlProfile η u) p
          + swirlDriftZ u p * dz (swirlProfile η u) p
          + swirlZeroth η u p * swirlProfile η u p
        = dr (dr (swirlProfile η u)) p + 1 / p.1.1 * dr (swirlProfile η u) p
          + dz (dz (swirlProfile η u)) p + swirlSource η f p := by
    rintro ⟨⟨a, b⟩, t'⟩ ⟨ha0, hab, ht1', ht2'⟩
    have hz' : ((meridional a b, t') : ParabolicPoint) ∈ unitCylinder :=
      meridional_mem_unitCylinder_of_lt_one hR1 hRpos hab.le (lt_of_lt_of_le htη1 ht1'.le)
        (lt_of_le_of_lt ht2' ht0)
    exact hpde_swirlProfile η u pr f hsol haxi hfaxi a b t' hz' ha0.ne'
  have hbound := abs_swirlProfile_le_boundary η u hu1 Rstar tη hRpos hR1 hη htη1 htη2 Mb Mi
    hbdry hinit t ht0
  have hmax := axisMaximumPrinciple Rstar tη t 1 ((-tη) ^ η * Mf) hRpos htη_lt hM
    (swirlProfile η u) (swirlDriftR u) (swirlDriftZ u) (swirlZeroth η u) (swirlSource η f)
    hcont haxis hreg hγ hF hpde ((-tη) ^ η * max Mb Mi) hbound
  have hmemcd : ((r, z), t) ∈ axisClosedDomain Rstar tη t := ⟨hr0, hrz.le, htη_lt.le, le_refl t⟩
  have hfinal := hmax ((r, z), t) hmemcd
  have heq : swirlProfile η u ((r, z), t) = (-t) ^ η * u (meridional r z, t) 1 := rfl
  rw [heq, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith only [ht0]) η)] at hfinal
  exact hfinal

/-- The swirl bound `eq:aniso:closure:w`: for `t ∈ (t_η, 0)` and a meridional point in
`vec3Ball 0 R_*`, the weighted swirl `(−t)^η u_θ` is bounded by its value on the parabolic
boundary `(−t_η)^η max(M_b, M_i)` plus the accumulated weighted source
`(−t_η)^η M_f (t − t_η)`, derived by applying `CIV.axisMaximumPrinciple` at
`s := t` and reading off its conclusion `m + M (p.2 − t₁)` there: since
`M := (−t_η)^η M_f` bounds `(−t)^η |f_θ|` uniformly for `t_η < t < 0` (monotonicity of
`(−t)^η`, `η > 0`) and `p.2 − t₁ = t − t_η` at `p = ((x₁, x₃), t)`, this is the sharp
instantiation of the maximum principle's own bound, not a further relaxation of it. -/
theorem swirl_bound (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hR : 0 < Rstar ∧ Rstar < 1) (tη η : ℝ) (htη : tη ∈ Ioo (-1 : ℝ) 0)
    (hη : 0 < η)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |u (x, t) 1| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi) :
    ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
      (-t) ^ η * |u (meridional x₁ x₃, t) 1|
        ≤ (-tη) ^ η * max Mb Mi + (-tη) ^ η * Mf * (t - tη) := by
  intro t ht x₁ x₃ hmem
  rcases le_total 0 x₁ with hx1 | hx1
  · have hrz : x₁ ^ 2 + x₃ ^ 2 < Rstar ^ 2 :=
      ((meridional_mem_vec3Ball_zero_iff x₁ x₃ Rstar).1 hmem).1
    exact swirl_bound_core u pr f hsol haxi hfaxi Mf hMf Rstar hR.1 hR.2 tη η htη.1 htη.2 hη
      hG Mb hbdry Mi hinit t ht.1 ht.2 x₁ x₃ hx1 hrz
  · have hrz : (-x₁) ^ 2 + x₃ ^ 2 < Rstar ^ 2 := by
      have hlt : x₁ ^ 2 + x₃ ^ 2 < Rstar ^ 2 :=
        ((meridional_mem_vec3Ball_zero_iff x₁ x₃ Rstar).1 hmem).1
      rw [neg_sq]; exact hlt
    have hr0 : (0 : ℝ) ≤ -x₁ := by linarith only [hx1]
    have hcore := swirl_bound_core u pr f hsol haxi hfaxi Mf hMf Rstar hR.1 hR.2 tη η htη.1 htη.2 hη
      hG Mb hbdry Mi hinit t ht.1 ht.2 (-x₁) x₃ hr0 hrz
    have hzmem : ((meridional (-x₁) x₃, t) : ParabolicPoint) ∈ unitCylinder :=
      meridional_mem_unitCylinder_of_lt_one hR.2 hR.1 hrz.le (lt_trans htη.1 ht.1) ht.2
    have hkey : u (meridional (- -x₁) x₃, t) 1 = -u (meridional (-x₁) x₃, t) 1 :=
      apply_meridional_reflect_one haxi hzmem
    rw [neg_neg] at hkey
    rw [hkey, abs_neg]
    exact hcore

/-- The swirl bound `eq:aniso:closure:w` at every off-axis point of `vec3Ball 0 R_*`, not
only on the meridional plane. The raw Cartesian component `u (x, t) 1` is not invariant
under the rotations about the axis, so it is the swirl coefficient `swirlCoeffAt u = Γ / r`
that carries the meridional conclusion of `swirl_bound` to a general point: writing
`x = Q_φ (r, 0, z)` with `r ≥ 0` (`exists_rotZ_meridional`), the point is off the axis
exactly when `r > 0`, the rotation preserves the Euclidean norm, and
`swirlCoeffAt_rotZ_meridional` identifies `swirlCoeffAt u (x, t)` with the meridional value
`u ((r, 0, z), t) 1` to which `swirl_bound` applies. -/
theorem swirl_bound_ball (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hR : 0 < Rstar ∧ Rstar < 1) (tη η : ℝ) (htη : tη ∈ Ioo (-1 : ℝ) 0)
    (hη : 0 < η)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |u (x, t) 1| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi) :
    ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar, (x 0 ≠ 0 ∨ x 1 ≠ 0) →
      (-t) ^ η * |swirlCoeffAt u (x, t)|
        ≤ (-tη) ^ η * max Mb Mi + (-tη) ^ η * Mf * (t - tη) := by
  intro t ht x hx hoff
  obtain ⟨φ, x₁, x₃, hx₁, hxeq⟩ := exists_rotZ_meridional x
  have hx₁pos : 0 < x₁ := by
    rcases hx₁.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, rotZ_meridional] at hxeq
      rcases hoff with h0 | h1
      · exact h0 (by rw [hxeq]; simp)
      · exact h1 (by rw [hxeq]; simp)
  have hball : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar := by
    rw [mem_vec3Ball, sub_zero] at hx ⊢
    rw [hxeq, vec3EuclideanNorm_eq_of_rotZ_meridional] at hx
    rw [vec3EuclideanNorm_meridional]
    exact hx
  have hzmem : ((x : Vec3), t) ∈ unitCylinder := by
    refine ⟨?_, ⟨lt_trans htη.1 ht.1, ht.2⟩⟩
    rw [mem_vec3Ball, sub_zero] at hx ⊢
    linarith only [hx, hR.2]
  have hswirl : swirlCoeffAt u ((x : Vec3), t) = u (meridional x₁ x₃, t) 1 := by
    rw [hxeq]
    exact swirlCoeffAt_rotZ_meridional haxi hx₁pos (by rwa [← hxeq])
  rw [hswirl]
  exact swirl_bound u pr f hsol haxi hfaxi Mf hMf Rstar hR tη η htη hη hG Mb hbdry Mi hinit
    t ht x₁ x₃ hball

end SwirlBound

end CIV
