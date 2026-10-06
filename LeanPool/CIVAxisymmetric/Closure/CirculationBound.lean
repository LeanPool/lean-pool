/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Axis.ScalarParabolicBoundaryBound
public import LeanPool.CIVAxisymmetric.Closure.CirculationBoundaryData
public import LeanPool.CIVAxisymmetric.Closure.CirculationProfilePde
public import LeanPool.CIVAxisymmetric.Statements.AxisMaximumPrinciple
public import LeanPool.CIVAxisymmetric.Identities.PlaneTransfer

/-!
# The circulation bound `eq:aniso:circulation:bound`

The last step of `lem:aniso:annulus`. On the regular annulus `{R_- < |x| < R_+} × (t_0, 0)`
the velocity is bounded, so for `R_* ∈ (R_-, R_+)` the circulation `Γ = r u_θ` is bounded on
the lateral boundary `∂B(R_*) × (t_0, 0)` by `2 R_* M`; and `u` is smooth at time `t_0`, so
`Γ` is bounded on `B(R_*)` there. Between those two data sets the axis maximum
principle `CIV.axisMaximumPrinciple` (`lem:aniso:axis`) fills in the interior: `Γ` obeys
`eq:aniso:axis:pde` with drift `(u_r, u_z)`, exponent `k = −1`, no zeroth-order term and
source `r f_θ`, and it vanishes on the axis, so it is bounded on the closed half-disc by its
parabolic-boundary values plus the accumulated source `R_* M_f (t − t_0)`.

Two remarks on the shape of the argument. First, the maximum principle is applied with its
final time `s` set to the time at which the bound is read, so the constant it produces never
mentions an auxiliary `s`; the manuscript's `s ↑ 0` is the monotone step
`t − t_0 ≤ −t_0 = |t_0|`. Second, `Γ` is invariant under the rotations about the axis
(`circulation_rotZ_invariant`) and every point of `Vec3` is such a rotation of a meridional
point with `r ≥ 0` (`exists_rotZ_meridional`), so the half-disc bound transfers to the whole
ball `B(R_*)` — axis and inner ball included, which is what
`eq:aniso:circulation:bound` asserts.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### The data of the circulation instantiation of `lem:aniso:axis` -/

/-- The radial drift `u_r`, read on the meridional plane. -/
@[expose] def circulationDriftR (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  u (meridional p.1.1 p.1.2, p.2) 0

/-- The vertical drift `u_z`, read on the meridional plane. -/
@[expose] def circulationDriftZ (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  u (meridional p.1.1 p.1.2, p.2) 2

/-- The source `r f_θ` of the circulation equation, read on the meridional plane. -/
@[expose] def circulationSource (f : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  p.1.1 * f (meridional p.1.1 p.1.2, p.2) 1

/-- The source of the circulation equation obeys `|r f_θ| ≤ R_* M_f` on the half-disc of
radius `R_*`, the uniform source bound `CIV.axisMaximumPrinciple` asks for. -/
theorem abs_circulationSource_le (f : ParabolicPoint → Vec3)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar tη s : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hs0 : s < 0) (htη1 : -1 < tη) :
    ∀ p ∈ axisDomain Rstar tη s, |circulationSource f p| ≤ Rstar * Mf := by
  rintro ⟨⟨a, b⟩, t⟩ ⟨ha0, hab, ht1, ht2⟩
  have hz : ((meridional a b, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_sq_le hRpos hR1 hab.le (lt_of_lt_of_le htη1 ht1.le)
      (lt_of_le_of_lt ht2 hs0)
  have hfbound : |f (meridional a b, t) 1| ≤ Mf := hMf _ hz
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) hfbound
  have ha_abs : |a| ≤ Rstar := by
    have habs : |a| ^ 2 ≤ Rstar ^ 2 := by
      rw [sq_abs]
      nlinarith only [hab, sq_nonneg b]
    exact le_of_sq_le_sq habs hRpos.le
  show |a * f (meridional a b, t) 1| ≤ Rstar * Mf
  rw [abs_mul]
  exact mul_le_mul ha_abs hfbound (abs_nonneg _) (le_trans (abs_nonneg _) ha_abs)

/-! ### The circulation bound on the meridional half-disc -/

/-- The circulation bound on the closed meridional half-disc `r ≥ 0`, by one application of
the axis maximum principle `CIV.axisMaximumPrinciple` to the circulation profile with
drift `(u_r, u_z)`, exponent `k = −1`, zeroth-order coefficient `γ = 0` and source `r f_θ`.
The bound is read at the final time `s := t`, so the constant `max (M_b, M_i) + R_* M_f
(t − t_η)` does not depend on any auxiliary final time: this is the manuscript's
"neither depends on `s`". -/
theorem abs_circulationProfile_le_of_nonneg (u : ParabolicPoint → Vec3)
    (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1)
    (tη : ℝ) (htη1 : -1 < tη) (htη2 : tη < 0)
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ),
      |circulation u (x, t)| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |circulation u (x, tη)| ≤ Mi)
    (t : ℝ) (htη_lt : tη < t) (ht0 : t < 0)
    (r z : ℝ) (hr0 : 0 ≤ r) (hrz : r ^ 2 + z ^ 2 < Rstar ^ 2) :
    |circulationProfile u ((r, z), t)| ≤ max Mb Mi + Rstar * Mf * (t - tη) := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  have hcirc1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => circulation u w) unitCylinder :=
    (contDiffOn_circulation u hu2).of_le (by norm_num)
  have hzbase : ((meridional r z, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_sq_le hRpos hR1 hrz.le (lt_trans htη1 htη_lt) ht0
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf _ hzbase)
  have hM : (0 : ℝ) ≤ Rstar * Mf := mul_nonneg hRpos.le hMf_nonneg
  have hcont : ContinuousOn (circulationProfile u) (axisClosedDomain Rstar tη t) :=
    continuousOn_circulationProfile u hu1 Rstar tη t hRpos hR1 ht0 htη1
  have haxis : ∀ zc tc : ℝ, |zc| ≤ Rstar → tη ≤ tc → tc ≤ t →
      circulationProfile u ((0, zc), tc) = 0 :=
    fun zc tc _ _ _ => circulationProfile_axis_eq_zero u zc tc
  have hreg := hreg_circulationProfile u hu2 Rstar tη t hRpos hR1 ht0 htη1
  have hF := abs_circulationSource_le f Mf hMf Rstar tη t hRpos hR1 ht0 htη1
  have hpde : ∀ p ∈ axisDomain Rstar tη t,
      dtPast (circulationProfile u) p + circulationDriftR u p * dr (circulationProfile u) p
          + circulationDriftZ u p * dz (circulationProfile u) p
          + (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) p * circulationProfile u p
        = dr (dr (circulationProfile u)) p + (-1 : ℝ) / p.1.1 * dr (circulationProfile u) p
          + dz (dz (circulationProfile u)) p + circulationSource f p := by
    rintro ⟨⟨a, b⟩, t'⟩ ⟨ha0, hab, ht1, ht2⟩
    have hz' : ((meridional a b, t') : ParabolicPoint) ∈ unitCylinder :=
      meridional_mem_unitCylinder_of_sq_le hRpos hR1 hab.le (lt_of_lt_of_le htη1 ht1.le)
        (lt_of_le_of_lt ht2 ht0)
    have hkey := hpde_circulationProfile u pr f hsol haxi hfaxi a b t' hz' ha0.ne'
    show dtPast (circulationProfile u) ((a, b), t')
        + u (meridional a b, t') 0 * dr (circulationProfile u) ((a, b), t')
        + u (meridional a b, t') 2 * dz (circulationProfile u) ((a, b), t')
        + (0 : ℝ) * circulationProfile u ((a, b), t')
      = dr (dr (circulationProfile u)) ((a, b), t')
        + (-1 : ℝ) / a * dr (circulationProfile u) ((a, b), t')
        + dz (dz (circulationProfile u)) ((a, b), t') + a * f (meridional a b, t') 1
    linarith only [hkey]
  have hbound : ∀ p ∈ axisParabolicBoundary Rstar tη t,
      |circulationProfile u p| ≤ max Mb Mi :=
    abs_scalar_meridional_le_boundary (circulation u) hcirc1 Rstar tη hRpos hR1 htη1 htη2
      Mb Mi hbdry hinit t ht0
  have hmax := axisMaximumPrinciple Rstar tη t (-1 : ℝ) (Rstar * Mf) hRpos htη_lt hM
    (circulationProfile u) (circulationDriftR u) (circulationDriftZ u)
    (fun _ => (0 : ℝ)) (circulationSource f)
    hcont haxis hreg (fun _ _ => le_refl (0 : ℝ)) hF hpde (max Mb Mi) hbound
  have hfinal := hmax ((r, z), t) ⟨hr0, hrz.le, htη_lt.le, le_refl t⟩
  exact hfinal

/-! ### From the half-disc to the whole ball -/

/-- The circulation bound on the whole ball `B(R_*)`, axis and inner ball included: the
circulation is invariant under the rotations about the axis (`circulation_rotZ_invariant`),
and every point of `Vec3` is such a rotation of a meridional point with `r ≥ 0`
(`exists_rotZ_meridional`), so the half-disc bound transfers verbatim. The final time enters
only through `t − t_η ≤ −t_η`, which is the manuscript's `M_f |t_0|` and its `s ↑ 0`. -/
theorem abs_circulation_le_of_boundary_data (u : ParabolicPoint → Vec3)
    (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1)
    (tη : ℝ) (htη1 : -1 < tη) (htη2 : tη < 0)
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ),
      |circulation u (x, t)| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |circulation u (x, tη)| ≤ Mi) :
    ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      |circulation u (x, t)| ≤ max Mb Mi + Rstar * Mf * (-tη) := by
  intro t ht x hx
  obtain ⟨φ, x₁, x₃, hx₁, hxeq⟩ := exists_rotZ_meridional x
  have hnorm_lt : Real.sqrt (x₁ ^ 2 + x₃ ^ 2) < Rstar := by
    have hxnorm : vec3EuclideanNorm x < Rstar := by
      rw [mem_vec3Ball, sub_zero] at hx
      exact hx
    rw [hxeq, vec3EuclideanNorm_eq_of_rotZ_meridional] at hxnorm
    exact hxnorm
  have hsq : x₁ ^ 2 + x₃ ^ 2 < Rstar ^ 2 := (Real.sqrt_lt' hRpos).1 hnorm_lt
  have hzmer : ((meridional x₁ x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    meridional_mem_unitCylinder_of_sq_le hRpos hR1 hsq.le (lt_trans htη1 ht.1) ht.2
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf _ hzmer)
  have hM : (0 : ℝ) ≤ Rstar * Mf := mul_nonneg hRpos.le hMf_nonneg
  have hrot : circulation u ((rotZ φ (meridional x₁ x₃) : Vec3), t)
      = circulation u (meridional x₁ x₃, t) :=
    circulation_rotZ_invariant haxi hzmer φ
  have hhalf : |circulationProfile u ((x₁, x₃), t)|
      ≤ max Mb Mi + Rstar * Mf * (t - tη) :=
    abs_circulationProfile_le_of_nonneg u pr f hsol haxi hfaxi Mf hMf Rstar hRpos hR1
      tη htη1 htη2 Mb hbdry Mi hinit t ht.1 ht.2 x₁ x₃ hx₁ hsq
  have hprof : circulationProfile u ((x₁, x₃), t) = circulation u (meridional x₁ x₃, t) := rfl
  rw [hprof] at hhalf
  have hxval : circulation u (x, t) = circulation u (meridional x₁ x₃, t) := by
    rw [hxeq]; exact hrot
  rw [hxval]
  have hmono : Rstar * Mf * (t - tη) ≤ Rstar * Mf * (-tη) :=
    mul_le_mul_of_nonneg_left (by linarith only [ht.2]) hM
  linarith only [hhalf, hmono]

/-! ### The initial data at time `t_η` -/

/-- At any time of `(−1, 0)` the circulation is bounded on `B(R_*)` for `R_* < 1`: `u` is
smooth there, so `Γ` is continuous on the compact closure of the ball. This is the
manuscript's "the former are finite since `u` is smooth at time `t_0`". -/
theorem exists_bound_circulation_slice (u : ParabolicPoint → Vec3)
    (hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder)
    (Rstar : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (τ : ℝ) (hτ : τ ∈ Ioo (-1 : ℝ) 0) :
    ∃ Mi : ℝ, ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |circulation u (x, τ)| ≤ Mi := by
  have hKcpt : IsCompact (closure (vec3Ball (0 : Vec3) Rstar)) :=
    isCompact_closure_vec3Ball hRpos
  have hKsub : closure (vec3Ball (0 : Vec3) Rstar) ⊆ vec3Ball 0 1 := by
    rw [closure_vec3Ball hRpos]
    intro y hy
    have hy' : vec3EuclideanNorm (y - 0) ≤ Rstar := hy
    rw [mem_vec3Ball]
    exact lt_of_le_of_lt hy' hR1
  have hcirc1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => circulation u w) unitCylinder := by
    have h0 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => w.1 0) unitCylinder :=
      ((contDiff_apply ℝ ℝ 0).comp contDiff_fst).contDiffOn
    have h1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => w.1 1) unitCylinder :=
      ((contDiff_apply ℝ ℝ 1).comp contDiff_fst).contDiffOn
    exact (h0.mul (contDiffOn_component hu1 1)).sub (h1.mul (contDiffOn_component hu1 0))
  have hcont : ContinuousOn (fun y : Vec3 => circulation u (y, τ))
      (closure (vec3Ball (0 : Vec3) Rstar)) :=
    ((contDiffOn_spatialSlice hcirc1 hτ).continuousOn).mono hKsub
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn hcont
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x (subset_closure hx)
  rwa [Real.norm_eq_abs] at h

/-! ### The azimuthal force bound of `eq:interior:force:c-two` -/

/-- The order-`0` case of `CIV.ForceC2Bounded` (`eq:interior:force:c-two`): one constant bounds the
azimuthal component of the force on the whole cylinder. -/
theorem exists_bound_force_swirl_of_forceC2Bounded (f : ParabolicPoint → Vec3)
    (hMf : ForceC2Bounded f) : ∃ Mf : ℝ, ∀ z ∈ unitCylinder, |f z 1| ≤ Mf := by
  obtain ⟨Mf, hMf0⟩ := hMf
  refine ⟨Mf, fun z hz => ?_⟩
  have h := hMf0 z hz 1 ![0, 0, 0] (by decide)
  simpa [multiPartial] using h

/-! ### `eq:aniso:circulation:bound` -/

/-- The circulation bound `eq:aniso:circulation:bound` on `B(R_*) × (t_0, 0)`, given a bound
`M_b` for `Γ` on the lateral boundary `∂B(R_*) × (t_0, 0)`. The initial constant is produced
here, from the smoothness of `u` at time `t_0`. -/
theorem exists_circulation_bound_ball (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hR : 0 < Rstar ∧ Rstar < 1) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ),
      |circulation u (x, t)| ≤ Mb) :
    ∃ CΓ : ℝ, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨hRpos, hR1⟩ := hR
  obtain ⟨ht₀1, ht₀2⟩ := ht₀
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1.of_le (by decide)
  obtain ⟨Mi, hinit⟩ :=
    exists_bound_circulation_slice u hu1 Rstar hRpos hR1 t₀ ⟨ht₀1, ht₀2⟩
  exact ⟨max Mb Mi + Rstar * Mf * (-t₀),
    abs_circulation_le_of_boundary_data u pr f hsol haxi hfaxi Mf hMf Rstar hRpos hR1
      t₀ ht₀1 ht₀2 Mb hbdry Mi hinit⟩

/-- The circulation bound `eq:aniso:circulation:bound` of `lem:aniso:annulus`: from the
regular annulus chosen in its proof — a bound `M` for `|u|` on `{R_- < |x| < R_+} × (t_0, 0)` — the
circulation obeys `eq:aniso:circulation:bound` on `B(R_*) × (t_0, 0)` for every
`R_* ∈ (R_-, R_+)`, axis and inner ball included. The lateral data is `|Γ| ≤ 2 R_* M` on
`∂B(R_*)` (`circulation_hbdry_of_annulus_bound`); the initial data comes from the smoothness
of `u` at time `t_0`; the interior is filled in by the maximum principle
`CIV.axisMaximumPrinciple` applied to `Γ` with `k = −1`, `γ = 0` and source `r f_θ`. -/
theorem forall_Rstar_exists_circulation_bound_ball_of_annulus_bound
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rlo Rhi t₀ M : ℝ) (hRlo : 0 ≤ Rlo) (hRhi : Rhi < 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M) :
    ∀ Rstar ∈ Ioo Rlo Rhi, ∃ CΓ : ℝ, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      |circulation u (x, t)| ≤ CΓ := by
  intro Rstar hRstar
  have hRpos : 0 < Rstar := lt_of_le_of_lt hRlo hRstar.1
  have hR1 : Rstar < 1 := lt_trans hRstar.2 hRhi
  exact exists_circulation_bound_ball u pr f hsol haxi hfaxi Mf hMf Rstar ⟨hRpos, hR1⟩ t₀ ht₀
    (2 * Rstar * M) (circulation_hbdry_of_annulus_bound hbound Rstar hRstar)

/-- `lem:aniso:annulus`'s circulation clause in full: for `0 ≤ R₁ < R₀ < 1` there are radii
`R₁ < R_- < R_+ < R₀` and a time `t_0 ∈ (−1, 0)` such that, for every `R_* ∈ (R_-, R_+)`,
the circulation is bounded on the whole cylinder `B(R_*) × (t_0, 0)`. -/
theorem exists_regular_annulus_circulation_bound_ball (q : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsw : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du pr f)
    (henergy : GlobalEnergyClass u Du pr)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1) :
    ∃ Rlo Rhi t₀ : ℝ, R₁ < Rlo ∧ Rlo < Rhi ∧ Rhi < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      ∀ Rstar ∈ Ioo Rlo Rhi, ∃ CΓ : ℝ, ∀ t ∈ Ioo t₀ (0 : ℝ),
        ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Mf, hMf1⟩ := exists_bound_force_swirl_of_forceC2Bounded f hMf
  obtain ⟨Rlo, Rhi, t₀, M, hR₁lo, hlo_hi, hhi_R₀, ht₀, hbound⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du pr f hsw henergy hsol.1
      hsol.2.1 hsol.2.2.1 hMf R₁ R₀ hR₁ hR₁R₀ hR₀
  refine ⟨Rlo, Rhi, t₀, hR₁lo, hlo_hi, hhi_R₀, ht₀, ?_⟩
  exact forall_Rstar_exists_circulation_bound_ball_of_annulus_bound u pr f hsol haxi hfaxi
    Mf hMf1 Rlo Rhi t₀ M (le_of_lt (lt_of_le_of_lt hR₁ hR₁lo)) (lt_trans hhi_R₀ hR₀) ht₀ hbound

/-! ### The circulation bound of `lem:aniso:annulus` -/

/-- The circulation bound `eq:aniso:circulation:bound` in the proof of `lem:aniso:annulus`.
Fix `R_* ∈ (R_-, R_+)`. For `s ∈ (t_0, 0)` the set `closure B(R_*) × [t_0, s]` is a compact
subset of `Q` on which `u` is smooth, so `Γ = r u_θ` is continuous there
(`continuousOn_circulationProfile`), smooth off the axis (`hreg_circulationProfile`), and
vanishes on the axis since `|Γ| ≤ r |u|` (`circulationProfile_axis_eq_zero`). The circulation
equation `eq:aniso:circulation:pde` is of the form `eq:aniso:axis:pde` with `k = −1`,
`γ = 0` and source `r f_θ` with `|r f_θ| ≤ R_* M_f` (`hpde_circulationProfile`,
`abs_circulationSource_le`, from `eq:interior:force:c-two`). `lem:aniso:axis`, in the form
`CIV.axisMaximumPrinciple`, bounds `|Γ|` on `closure B(R_*) × [t_0, s]` by its values at time
`t_0` and on `∂B(R_*) × [t_0, s]` plus `M_f |t_0|`; the former are finite since `u` is smooth
at time `t_0` (`exists_bound_circulation_slice`), the latter at most `2 R_*` times the bound
on `u` on the annulus (`circulation_hbdry_of_annulus_bound`); neither depends on `s`, and
`s ↑ 0` gives `eq:aniso:circulation:bound`. -/
theorem step_annulus_circulation_bound (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (Rm Rp t₀ M : ℝ) (hRm : 0 ≤ Rm) (hRp : Rp < 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (hannulus : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M)
    (Rstar : ℝ) (hRstar : Rstar ∈ Ioo Rm Rp) :
    ∃ CΓ : ℝ, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      |circulation u (x, t)| ≤ CΓ := by
  obtain ⟨Mf, hMf1⟩ := exists_bound_force_swirl_of_forceC2Bounded f hMf
  exact forall_Rstar_exists_circulation_bound_ball_of_annulus_bound u pr f hsol haxi hfaxi
    Mf hMf1 Rm Rp t₀ M hRm hRp ht₀ hannulus Rstar hRstar

end CIV
