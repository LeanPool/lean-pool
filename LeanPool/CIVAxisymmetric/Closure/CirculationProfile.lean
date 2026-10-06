/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AxisClosedDomain
public import LeanPool.CIVAxisymmetric.Statements.Circulation
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm

/-!
# The circulation profile on the meridional half-disc

`CIV.axisMaximumPrinciple` (`lem:aniso:axis`) consumes a scalar on the half-disc
`(r, z, t)`, so the circulation `Γ = CIV.circulation u` has to be read through the
meridional embedding. `circulationProfile u ((r, z), t) = Γ (u, ((r, 0, z), t))`, which
`circulationProfile_apply` evaluates as `r · u_θ`.

This file supplies the three structural hypotheses of the maximum principle that do not
involve derivatives: continuity on the closed domain, vanishing on the axis (`Γ = r u_θ`
has the factor `r`, so no smoothness at `r = 0` is needed for this), and the evenness of
`Γ` under the reflection `r ↦ −r` of the meridional plane, which carries the conclusion
from the half-disc `r ≥ 0` to the full disc.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The circulation, read on the meridional plane as a function of `(r, z, t)`. -/
@[expose] def circulationProfile (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  circulation u (meridional p.1.1 p.1.2, p.2)

/-- The circulation profile is `r · u_θ`: the second component of `meridional` is `0`, so the
`x₂ u₁` term of `Γ` drops out. -/
theorem circulationProfile_apply (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) :
    circulationProfile u p = p.1.1 * u (meridional p.1.1 p.1.2, p.2) 1 := by
  show (meridional p.1.1 p.1.2 : Vec3) 0 * u (meridional p.1.1 p.1.2, p.2) 1
      - (meridional p.1.1 p.1.2 : Vec3) 1 * u (meridional p.1.1 p.1.2, p.2) 0
    = p.1.1 * u (meridional p.1.1 p.1.2, p.2) 1
  have h0 : (meridional p.1.1 p.1.2 : Vec3) 0 = p.1.1 := rfl
  have h1 : (meridional p.1.1 p.1.2 : Vec3) 1 = 0 := rfl
  rw [h0, h1, zero_mul, sub_zero]

/-- A meridional point of radius at most `R_* < 1`, at a time of `(−1, 0)`, lies in the unit
cylinder. Stated with the two coordinates explicit, so that no projection has to be unfolded
where it is used. -/
theorem meridional_mem_unitCylinder_of_sq_le {a b t Rstar : ℝ} (hRpos : 0 < Rstar)
    (hR1 : Rstar < 1) (hab : a ^ 2 + b ^ 2 ≤ Rstar ^ 2) (ht1 : -1 < t) (ht2 : t < 0) :
    ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder := by
  have hRsq : Rstar ^ 2 < 1 := by nlinarith only [hR1, hRpos]
  exact (meridional_mem_unitCylinder_iff a b t).2 ⟨by linarith only [hab, hRsq], ht1, ht2⟩

/-- The meridional embedding of the closed half-disc of radius `R_* < 1` at times in
`[t_η, s] ⊆ (−1, 0)` lands in the unit cylinder. -/
theorem mapsTo_meridional_axisClosedDomain (Rstar tη s : ℝ) (hRpos : 0 < Rstar)
    (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    MapsTo (fun p : (ℝ × ℝ) × ℝ => ((meridional p.1.1 p.1.2, p.2) : Vec3 × ℝ))
      (axisClosedDomain Rstar tη s) unitCylinder := by
  rintro p ⟨-, hrz, hp1, hp2⟩
  exact meridional_mem_unitCylinder_of_sq_le hRpos hR1 hrz
    (lt_of_lt_of_le htη1 hp1) (lt_of_le_of_lt hp2 hs0)

/-- The meridional embedding `(r, z) ↦ (r, 0, z)` of `ℝ × ℝ` into `Vec3` is the linear map
`y ↦ y₁ e₁ + y₂ e₃`, hence smooth. -/
theorem contDiff_meridional_uncurry :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3)) := by
  have heq : (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3))
      = fun y : ℝ × ℝ => y.1 • (basisVec 0 : Vec3) + y.2 • basisVec 2 := by
    funext y
    ext i
    fin_cases i <;> simp [meridional, basisVec_apply]
  rw [heq]
  exact (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)

/-- The meridional embedding `(r, z) ↦ (r, 0, z)` of `ℝ × ℝ` into `Vec3` is continuous. -/
theorem continuous_meridional_uncurry :
    Continuous (fun y : ℝ × ℝ => (meridional y.1 y.2 : Vec3)) :=
  contDiff_meridional_uncurry.continuous

/-- The circulation profile is continuous on the closed half-disc `axisClosedDomain`, the
first hypothesis of `CIV.axisMaximumPrinciple`. Only `C¹` regularity of `u` is used. -/
theorem continuousOn_circulationProfile (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ContinuousOn (circulationProfile u) (axisClosedDomain Rstar tη s) := by
  have hmaps := mapsTo_meridional_axisClosedDomain Rstar tη s hRpos hR1 hs0 htη1
  have hcont_e : Continuous
      (fun p : (ℝ × ℝ) × ℝ => ((meridional p.1.1 p.1.2, p.2) : Vec3 × ℝ)) :=
    (continuous_meridional_uncurry.comp continuous_fst).prodMk continuous_snd
  have hcomp : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => u (meridional p.1.1 p.1.2, p.2) 1)
      (axisClosedDomain Rstar tη s) :=
    (contDiffOn_component hu1 1).continuousOn.comp hcont_e.continuousOn hmaps
  have hprod : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ => p.1.1 * u (meridional p.1.1 p.1.2, p.2) 1)
      (axisClosedDomain Rstar tη s) :=
    (continuous_fst.comp continuous_fst).continuousOn.mul hcomp
  exact hprod.congr fun p _ => circulationProfile_apply u p

/-- The circulation vanishes on the axis, the second hypothesis of
`CIV.axisMaximumPrinciple`: `Γ = r u_θ` carries the factor `r`, so the value at `r = 0` is
`0` with no appeal to regularity. -/
theorem circulationProfile_axis_eq_zero (u : ParabolicPoint → Vec3) (zc tc : ℝ) :
    circulationProfile u ((0, zc), tc) = 0 := by
  rw [circulationProfile_apply]
  exact zero_mul _

/-- The circulation profile is even under the reflection `r ↦ −r` of the meridional plane:
both `r` and `u_θ` change sign (`apply_meridional_reflect_one`), so `Γ = r u_θ` does not. -/
theorem circulationProfile_meridional_even {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) {r z t : ℝ}
    (hz : ((meridional r z : Vec3), t) ∈ unitCylinder) :
    circulationProfile u ((-r, z), t) = circulationProfile u ((r, z), t) := by
  rw [circulationProfile_apply, circulationProfile_apply]
  have hkey : u (meridional (-r) z, t) 1 = -u (meridional r z, t) 1 :=
    apply_meridional_reflect_one haxi hz
  show (-r) * u (meridional (-r) z, t) 1 = r * u (meridional r z, t) 1
  rw [hkey]
  ring

end CIV
