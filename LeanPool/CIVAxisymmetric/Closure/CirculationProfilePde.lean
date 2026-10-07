/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Axis.MeridionalScalarChainRule
public import LeanPool.CIVAxisymmetric.Closure.CirculationProfile
public import LeanPool.CIVAxisymmetric.Statements.AxisDomain
public import LeanPool.CIVAxisymmetric.Statements.Dr
public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import LeanPool.CIVAxisymmetric.Statements.Dz
public import LeanPool.CIVAxisymmetric.Identities.CirculationEquation

/-!
# The circulation profile as an input to the axis maximum principle

`CIV.circulation_pde` (`eq:aniso:circulation:pde`) is stated in the Cartesian derivative
calculus `timePartial`/`spatialPartial`/`spatialSecondPartial` on the meridional plane.
`CIV.axisMaximumPrinciple` instead consumes the half-disc operators `dtPast`, `dr`, `dz`.
This file transports the equation between the two, through the meridional chain rules of
`CIV/Axis/MeridionalScalarChainRule.lean`, and records the regularity hypothesis
(`hreg_circulationProfile`) the maximum principle asks for.

The resulting equation `hpde_circulationProfile` is `lem:aniso:axis`'s
`eq:aniso:axis:pde` with drift `(u_r, u_z)`, exponent `k = −1`, zeroth-order coefficient
`γ = 0` and source `r f_θ`, exactly as the proof of `lem:aniso:annulus` reads it.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### The `C²` spatial slice of the circulation -/

/-- The circulation of a `C²` field is `C²` on the cylinder: it is a polynomial in the
coordinates and the components of `u`. -/
theorem contDiffOn_circulation (u : ParabolicPoint → Vec3)
    (hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder) :
    ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => circulation u z) unitCylinder := by
  have h0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 0) unitCylinder :=
    ((contDiff_apply ℝ ℝ 0).comp contDiff_fst).contDiffOn
  have h1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 1) unitCylinder :=
    ((contDiff_apply ℝ ℝ 1).comp contDiff_fst).contDiffOn
  exact (h0.mul (contDiffOn_component hu2 1)).sub (h1.mul (contDiffOn_component hu2 0))

/-- The spatial slice of the circulation at a fixed time is `C²` on the unit ball. -/
theorem contDiffOn_circulation_slice (u : ParabolicPoint → Vec3)
    (hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ 2 (fun y : Vec3 => circulation u (y, t)) (vec3Ball (0 : Vec3) 1) :=
  contDiffOn_spatialSlice (contDiffOn_circulation u hu2) ht

/-- The spatial slice of the circulation is differentiable at every point of the cylinder. -/
theorem differentiableAt_circulation_slice (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun y : Vec3 => circulation u (y, z.2)) z.1 := by
  have h0 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => w.1 0) unitCylinder :=
    ((contDiff_apply ℝ ℝ 0).comp contDiff_fst).contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => w.1 1) unitCylinder :=
    ((contDiff_apply ℝ ℝ 1).comp contDiff_fst).contDiffOn
  have hcirc : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => circulation u w) unitCylinder :=
    (h0.mul (contDiffOn_component hu1 1)).sub (h1.mul (contDiffOn_component hu1 0))
  exact ((contDiffOn_spatialSlice hcirc hz.2).differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hz.1)

/-- The time slice of the circulation is differentiable at every point of the cylinder. -/
theorem differentiableAt_circulation_time (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => circulation u (z.1, s)) z.2 := by
  have h_cont : ContDiffOn ℝ 1 (fun s : ℝ => u (z.1, s)) (Ioo (-1 : ℝ) 0) :=
    hu1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun s hs => ⟨hz.1, hs⟩
  have h_slice : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s)) z.2 :=
    h_cont.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hz.2)
  have h0 : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 0) z.2 := differentiableAt_pi.1 h_slice 0
  have h1 : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 1) z.2 := differentiableAt_pi.1 h_slice 1
  exact (h1.const_mul (z.1 0)).sub (h0.const_mul (z.1 1))

/-! ### Regularity of the circulation profile -/

/-- The regularity hypothesis of `CIV.axisMaximumPrinciple` for the circulation profile:
`C²` in the half-disc variables and differentiable from the past in time, at every interior
point of the half-disc. -/
theorem hreg_circulationProfile (u : ParabolicPoint → Vec3)
    (hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ∀ p ∈ axisDomain Rstar tη s,
      ContDiffAt ℝ 2 (fun y : ℝ × ℝ => circulationProfile u (y, p.2)) p.1 ∧
        DifferentiableWithinAt ℝ (fun t : ℝ => circulationProfile u (p.1, t)) (Iic p.2) p.2 := by
  rintro ⟨⟨a, b⟩, t⟩ ⟨ha0, hab, ht1, ht2⟩
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu2.of_le (by norm_num)
  have ht_mem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans htη1 ht1, lt_of_le_of_lt ht2 hs0⟩
  have hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder :=
    mapsTo_meridional_axisClosedDomain Rstar tη s hRpos hR1 hs0 htη1
      (show ((a, b), t) ∈ axisClosedDomain Rstar tη s from ⟨ha0.le, hab.le, ht1.le, ht2⟩)
  refine ⟨?_, ?_⟩
  · have hfun : (fun y : ℝ × ℝ => circulationProfile u (y, t))
        = fun y : ℝ × ℝ => y.1 * u (meridional y.1 y.2, t) 1 := by
      funext y
      exact circulationProfile_apply u (y, t)
    rw [hfun]
    have hu_at : ContDiffAt ℝ 2 (fun y : Vec3 => u (y, t) 1) (meridional a b) :=
      (contDiffOn_spatialSlice (contDiffOn_component hu2 1) ht_mem).contDiffAt
        ((isOpen_vec3Ball 0 1).mem_nhds hz.1)
    have hemb_at : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3)) (a, b) :=
      (contDiff_meridional_uncurry.of_le (by norm_num)).contDiffAt
    exact contDiffAt_fst.mul (hu_at.fun_comp (a, b) hemb_at)
  · have hfun : (fun t' : ℝ => circulationProfile u ((a, b), t'))
        = fun t' : ℝ => circulation u (meridional a b, t') := by
      funext t'
      rfl
    rw [hfun]
    exact (differentiableAt_circulation_time u hu1 hz).differentiableWithinAt

/-! ### Translating `dtPast`, `dr`, `dz` into the Cartesian derivative calculus -/

/-- `dtPast` of the circulation profile is `timePartial` of the circulation. -/
theorem dtPast_circulationProfile_eq (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder) (p : (ℝ × ℝ) × ℝ)
    (hz : ((meridional p.1.1 p.1.2, p.2) : ParabolicPoint) ∈ unitCylinder) :
    dtPast (circulationProfile u) p
      = timePartial (circulation u) (meridional p.1.1 p.1.2, p.2) := by
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => circulation u (meridional p.1.1 p.1.2, s)) p.2 :=
    differentiableAt_circulation_time u hu1 hz
  change derivWithin (fun t => circulation u (meridional p.1.1 p.1.2, t)) (Iic p.2) p.2 = _
  rw [hdiff.derivWithin (uniqueDiffWithinAt_Iic p.2)]
  rfl

/-- `dr` of the circulation profile is `∂₁` of the circulation. -/
theorem dr_circulationProfile_eq (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hdiff : DifferentiableAt ℝ (fun y : Vec3 => circulation u (y, p.2))
      (meridional p.1.1 p.1.2)) :
    dr (circulationProfile u) p
      = spatialPartial (circulation u) 0 (meridional p.1.1 p.1.2, p.2) := by
  change deriv (fun r : ℝ => circulation u (meridional r p.1.2, p.2)) p.1.1 = _
  rw [(hasDerivAt_comp_meridional_fst hdiff).deriv]
  rfl

/-- `dz` of the circulation profile is `∂₃` of the circulation. -/
theorem dz_circulationProfile_eq (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hdiff : DifferentiableAt ℝ (fun y : Vec3 => circulation u (y, p.2))
      (meridional p.1.1 p.1.2)) :
    dz (circulationProfile u) p
      = spatialPartial (circulation u) 2 (meridional p.1.1 p.1.2, p.2) := by
  change deriv (fun z : ℝ => circulation u (meridional p.1.1 z, p.2)) p.1.2 = _
  rw [(hasDerivAt_comp_meridional_snd hdiff).deriv]
  rfl

/-- `dr (dr ·)` of the circulation profile is `∂₁²` of the circulation. -/
theorem dr_dr_circulationProfile_eq (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hg : ContDiffOn ℝ 2 (fun y : Vec3 => circulation u (y, p.2)) (vec3Ball (0 : Vec3) 1))
    (hmem : meridional p.1.1 p.1.2 ∈ vec3Ball (0 : Vec3) 1) :
    dr (dr (circulationProfile u)) p
      = spatialSecondPartial (circulation u) 0 0 (meridional p.1.1 p.1.2, p.2) := by
  change deriv (fun r : ℝ => deriv (fun r' : ℝ => circulation u (meridional r' p.1.2, p.2)) r)
      p.1.1 = _
  rw [(hasDerivAt_deriv_comp_meridional_fst hg hmem).deriv]
  rfl

/-- `dz (dz ·)` of the circulation profile is `∂₃²` of the circulation. -/
theorem dz_dz_circulationProfile_eq (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ)
    (hg : ContDiffOn ℝ 2 (fun y : Vec3 => circulation u (y, p.2)) (vec3Ball (0 : Vec3) 1))
    (hmem : meridional p.1.1 p.1.2 ∈ vec3Ball (0 : Vec3) 1) :
    dz (dz (circulationProfile u)) p
      = spatialSecondPartial (circulation u) 2 2 (meridional p.1.1 p.1.2, p.2) := by
  change deriv (fun z : ℝ => deriv (fun z' : ℝ => circulation u (meridional p.1.1 z', p.2)) z)
      p.1.2 = _
  rw [(hasDerivAt_deriv_comp_meridional_snd hg hmem).deriv]
  rfl

/-! ### The equation `eq:aniso:axis:pde` for the circulation profile -/

/-- The circulation equation `eq:aniso:circulation:pde`, written in the half-disc calculus
`CIV.axisMaximumPrinciple` consumes: drift `(u_r, u_z)`, exponent `k = −1`, no zeroth-order
term and source `r f_θ`. -/
theorem hpde_circulationProfile (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (a b t : ℝ) (hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder) (ha : a ≠ 0) :
    dtPast (circulationProfile u) ((a, b), t)
        + u (meridional a b, t) 0 * dr (circulationProfile u) ((a, b), t)
        + u (meridional a b, t) 2 * dz (circulationProfile u) ((a, b), t)
      = dr (dr (circulationProfile u)) ((a, b), t)
        + (-1 : ℝ) / a * dr (circulationProfile u) ((a, b), t)
        + dz (dz (circulationProfile u)) ((a, b), t) + a * f (meridional a b, t) 1 := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hdiff : DifferentiableAt ℝ (fun y : Vec3 => circulation u (y, t)) (meridional a b) :=
    differentiableAt_circulation_slice u hu1 hz
  have hg : ContDiffOn ℝ 2 (fun y : Vec3 => circulation u (y, t)) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_circulation_slice u hu2 hz.2
  rw [dtPast_circulationProfile_eq u hu1 ((a, b), t) hz,
    dr_circulationProfile_eq u ((a, b), t) hdiff,
    dz_circulationProfile_eq u ((a, b), t) hdiff,
    dr_dr_circulationProfile_eq u ((a, b), t) hg hz.1,
    dz_dz_circulationProfile_eq u ((a, b), t) hg hz.1]
  have hplane : ((meridional a b, t) : ParabolicPoint).1 1 = 0 := rfl
  have hfst : ((meridional a b, t) : ParabolicPoint).1 0 = a := rfl
  have hne : ((meridional a b, t) : ParabolicPoint).1 0 ≠ 0 := by rw [hfst]; exact ha
  have hpde := circulation_pde u pr f hsol haxi hfaxi (meridional a b, t) hz hplane hne
  rw [hfst] at hpde
  rw [div_eq_inv_mul] at hpde ⊢
  dsimp only
  linarith only [hpde]

end CIV
