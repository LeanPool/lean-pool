/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteLiftBounds
public import LeanPool.CIVAxisymmetric.Zoom.RescaledEquation
public import LeanPool.CIVAxisymmetric.Zoom.FiniteLiftCalculus
public import LeanPool.CIVAxisymmetric.Zoom.LiftedWeakForm

/-!
# The lifted finite-axis equation off the axis

Off the axis `X = 0`, the lifted potential vorticity `Ω̃_n = Ω_n ∘ L` of `eq:aniso:zoom:lifted`,
with `L(X, Z, τ) = (|X|, Z, τ)`, is smooth and satisfies pointwise
`∂_τ Ω̃_n + B_n · ∇Ω̃_n = Δ_X Ω̃_n + δ_n² ∂_ZZ Ω̃_n + ∂_Z F̃_n + G̃_n`, where `B_n` is the drift of
`eq:drift:Bn:def`, `F_n = S_n² / R²` is the swirl flux and `G_n` the force term of
`eq:aniso:zoom:finite:equation` (`finLift_pde`); the divergence of `B_n` there is
`2 V_n / R = finDriftDiv` (`finLift_div`). This is the lift to `ℝ⁴`: the radial operator
`∂_RR + 3 R⁻¹ ∂_R` is the Laplacian of `ℝ⁴` acting on the lift. Integrating by parts
(`integral_liftedResidual_eq`) turns the equation into the identity
`integral_finResidual_eq_of_subset_finLiftDomain` for test functions supported off the axis.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The open set of meridional points off the axis whose zoomed image lies in the unit
cylinder. -/
@[expose] def finMeridionalDomain (lam h zc : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 < p.1.1 ∧ zoomPoint lam h zc p ∈ unitCylinder}

theorem isOpen_finMeridionalDomain (lam h zc : ℝ) : IsOpen (finMeridionalDomain lam h zc) :=
  (isOpen_lt continuous_const (continuous_fst.comp continuous_fst)).inter
    (isOpen_unitCylinder_prod.preimage (continuous_zoomPoint lam h zc))

/-- The lift maps the off-axis lifted domain into the off-axis meridional domain. -/
theorem zoomLiftPoint_mem_finMeridionalDomain {lam h zc : ℝ} {z : Vec 5 × ℝ}
    (hz : z ∈ finLiftDomain lam h zc) : zoomLiftPoint z ∈ finMeridionalDomain lam h zc :=
  ⟨hz.1, hz.2⟩

/-- The potential vorticity of a smooth field, read through the zoom map, is smooth off the
axis. -/
theorem contDiffOn_potentialVorticity_zoomPoint {lam h zc : ℝ} (hlam : 0 < lam)
    {v : ParabolicPoint → Vec3}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => v z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => potentialVorticity v (zoomPoint lam h zc p))
      (finMeridionalDomain lam h zc) := by
  set D : Set (Vec3 × ℝ) := {z | z ∈ unitCylinder ∧ z.1 0 ≠ 0} with hD
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.1 0) D :=
    ((contDiff_apply ℝ ℝ (0 : Fin 3)).comp contDiff_fst).contDiffOn
  have hazi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => azimuthalVorticity v z) D :=
    (contDiffOn_azimuthalVorticity hv).mono fun z hz => hz.1
  have hPV : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => potentialVorticity v z) D :=
    (hazi.div hrad fun z hz => hz.2).congr fun z hz => potentialVorticity_eq_div v hz.2
  refine hPV.comp (contDiff_zoomPoint lam h zc).contDiffOn fun p hp => ⟨hp.2, ?_⟩
  have h0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by simp [zoomPoint, meridional]
  rw [h0]
  exact mul_ne_zero hlam.ne' hp.1.ne'

/-- A component of a smooth field, read through the zoom map, is smooth off the axis. -/
theorem contDiffOn_component_zoomPoint {lam h zc : ℝ} {v : ParabolicPoint → Vec3}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => v z) unitCylinder) (k : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => v (zoomPoint lam h zc p) k) (finMeridionalDomain lam h zc) :=
  (contDiffOn_component hv k).comp (contDiff_zoomPoint lam h zc).contDiffOn fun _ hp => hp.2

theorem contDiffOn_zoomOmega_finMeridional {lam h zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zoomOmega lam h zc u) (finMeridionalDomain lam h zc) :=
  contDiffOn_const.mul (contDiffOn_potentialVorticity_zoomPoint hlam hu)

theorem contDiffOn_zoomForce_finMeridional {lam h zc : ℝ} (hlam : 0 < lam)
    {f : ParabolicPoint → Vec3} (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z)
      unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zoomForce lam h zc f) (finMeridionalDomain lam h zc) :=
  contDiffOn_const.mul (contDiffOn_potentialVorticity_zoomPoint hlam hf)

theorem contDiffOn_zoomV_finMeridional {lam h zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zoomV lam h zc u) (finMeridionalDomain lam h zc) :=
  contDiffOn_const.mul (contDiffOn_component_zoomPoint hu 0)

theorem contDiffOn_zoomW_finMeridional {lam h zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zoomW lam h zc u) (finMeridionalDomain lam h zc) :=
  contDiffOn_const.mul (contDiffOn_component_zoomPoint hu 2)

/-- The swirl flux `S_n² / R²` is smooth off the axis. -/
theorem contDiffOn_zoomSwirlFlux_finMeridional {lam h zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2)
      (finMeridionalDomain lam h zc) := by
  have hS : ContDiffOn ℝ (⊤ : ℕ∞) (zoomS lam h zc u) (finMeridionalDomain lam h zc) :=
    contDiffOn_const.mul (contDiffOn_component_zoomPoint hu 1)
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.1.1 ^ 2)
      (finMeridionalDomain lam h zc) :=
    ((contDiff_fst.comp contDiff_fst).pow 2).contDiffOn
  exact (hS.pow 2).div hR fun q hq => pow_ne_zero 2 hq.1.ne'

/-- A function smooth off the axis in the meridional variables lifts to a function smooth off
the axis in the lifted variables. -/
theorem contDiffOn_comp_zoomLiftPoint {lam h zc : ℝ} {g : (ℝ × ℝ) × ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (finMeridionalDomain lam h zc)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => g (zoomLiftPoint z)) (finLiftDomain lam h zc) :=
  hg.comp (contDiffOn_zoomLiftPoint.mono fun _ hz => hz.1) fun _ hz =>
    zoomLiftPoint_mem_finMeridionalDomain hz

/-- A function smooth off the axis is differentiable at the lift of an off-axis point. -/
theorem differentiableAt_of_finLiftDomain {lam h zc : ℝ} {g : (ℝ × ℝ) × ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (finMeridionalDomain lam h zc)) {z : Vec 5 × ℝ}
    (hz : z ∈ finLiftDomain lam h zc) : DifferentiableAt ℝ g (zoomLiftPoint z) :=
  (hg.differentiableOn (by simp) _ (zoomLiftPoint_mem_finMeridionalDomain hz)).differentiableAt
    ((isOpen_finMeridionalDomain lam h zc).mem_nhds (zoomLiftPoint_mem_finMeridionalDomain hz))

/-- The radial components of the lifted drift, as functions. -/
theorem zoomDrift_apply_fun_of_ne (lam h zc : ℝ) (u : ParabolicPoint → Vec3) {i : Fin 5}
    (hi : i ≠ 4) :
    (fun w => zoomDrift lam h zc u w i)
      = fun w => zoomV lam h zc u (zoomLiftPoint w) * (w.1 i / zoomLiftRadius w.1) := by
  funext w
  simp [zoomDrift, hi]

/-- The vertical component of the lifted drift, as a function. -/
theorem zoomDrift_apply_fun_four (lam h zc : ℝ) (u : ParabolicPoint → Vec3) :
    (fun w => zoomDrift lam h zc u w 4) = fun w => zoomW lam h zc u (zoomLiftPoint w) := by
  funext w
  simp [zoomDrift]

/-- The components of the lifted drift are smooth off the axis. -/
theorem contDiffOn_zoomDrift_apply {lam h zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 5) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w => zoomDrift lam h zc u w i) (finLiftDomain lam h zc) := by
  by_cases hi : i = 4
  · subst hi
    rw [zoomDrift_apply_fun_four]
    exact contDiffOn_comp_zoomLiftPoint (contDiffOn_zoomW_finMeridional hu)
  · rw [zoomDrift_apply_fun_of_ne lam h zc u hi]
    have hR : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec 5 × ℝ => zoomLiftRadius w.1)
        (finLiftDomain lam h zc) :=
      ((contDiff_fst.comp contDiff_fst).comp_contDiffOn contDiffOn_zoomLiftPoint).mono
        fun _ hz => hz.1
    have hX : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec 5 × ℝ => w.1 i) (finLiftDomain lam h zc) :=
      ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffOn
    exact (contDiffOn_comp_zoomLiftPoint (contDiffOn_zoomV_finMeridional hu)).mul
      (hX.div hR fun _ hz => hz.1.ne')

/-- The four squared radial coordinates sum to the squared lifted radius. -/
theorem sum_sq_eq_zoomLiftRadius_sq (X : Vec 5) :
    X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 = zoomLiftRadius X ^ 2 := by
  rw [zoomLiftRadius, Real.sq_sqrt (by positivity)]

/-- The two radial sums produced by the lift. -/
theorem sum_radial_lift_identities {X : Vec 5} (hR : 0 < zoomLiftRadius X) :
    (X 0 / zoomLiftRadius X) ^ 2 + (X 1 / zoomLiftRadius X) ^ 2 + (X 2 / zoomLiftRadius X) ^ 2
        + (X 3 / zoomLiftRadius X) ^ 2 = 1 ∧
      (1 / zoomLiftRadius X - X 0 ^ 2 / zoomLiftRadius X ^ 3)
        + (1 / zoomLiftRadius X - X 1 ^ 2 / zoomLiftRadius X ^ 3)
        + (1 / zoomLiftRadius X - X 2 ^ 2 / zoomLiftRadius X ^ 3)
        + (1 / zoomLiftRadius X - X 3 ^ 2 / zoomLiftRadius X ^ 3) = 3 / zoomLiftRadius X := by
  have hs := sum_sq_eq_zoomLiftRadius_sq X
  have hne : zoomLiftRadius X ≠ 0 := hR.ne'
  constructor
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination -hs

/-- The divergence of the lifted drift off the axis is `2 V_n / R`. -/
theorem finLift_div {lam h zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {z : Vec 5 × ℝ} (hz : z ∈ finLiftDomain lam h zc) :
    ∑ i, fderiv ℝ (fun w => zoomDrift lam h zc u w i) z (basisVec i, 0)
      = finDriftDiv lam h zc u z := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hR : 0 < zoomLiftRadius z.1 := hz.1
  have hV := differentiableAt_of_finLiftDomain (contDiffOn_zoomV_finMeridional (lam := lam)
    (h := h) (zc := zc) hu) hz
  have hW := differentiableAt_of_finLiftDomain (contDiffOn_zoomW_finMeridional (lam := lam)
    (h := h) (zc := zc) hu) hz
  have hrad : ∀ i : Fin 5, i ≠ 4 →
      fderiv ℝ (fun w => zoomDrift lam h zc u w i) z (basisVec i, 0)
        = dr (zoomV lam h zc u) (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) ^ 2
          + zoomV lam h zc u (zoomLiftPoint z)
            * (1 / zoomLiftRadius z.1 - z.1 i ^ 2 / zoomLiftRadius z.1 ^ 3) := by
    intro i hi
    rw [zoomDrift_apply_fun_of_ne lam h zc u hi]
    exact fderiv_comp_zoomLiftPoint_mul_dir hR hV hi
  have h4 : fderiv ℝ (fun w => zoomDrift lam h zc u w 4) z (basisVec 4, 0)
      = dz (zoomW lam h zc u) (zoomLiftPoint z) := by
    rw [zoomDrift_apply_fun_four]
    exact fderiv_comp_zoomLiftPoint_vertical hR hW
  have hdiv := zoom_divergence_identity lam h zc hlam u pr f hsol haxi (zoomLiftPoint z) hz.2
    hR.ne'
  have hdef : finDriftDiv lam h zc u z
      = 2 * zoomV lam h zc u (zoomLiftPoint z) / zoomLiftRadius z.1 := by
    simp [finDriftDiv, hR.ne']
  obtain ⟨h1, h2⟩ := sum_radial_lift_identities hR
  rw [Fin.sum_univ_five, hrad 0 (by decide), hrad 1 (by decide), hrad 2 (by decide),
    hrad 3 (by decide), h4, hdef]
  have hp : (zoomLiftPoint z).1.1 = zoomLiftRadius z.1 := rfl
  rw [hp] at hdiv
  linear_combination hdiv + dr (zoomV lam h zc u) (zoomLiftPoint z) * h1
    + zoomV lam h zc u (zoomLiftPoint z) * h2

/-- The lifted potential vorticity is the lift of `zoomOmega`. -/
theorem zoomOmegaLift_eq_fun (lam h zc : ℝ) (u : ParabolicPoint → Vec3) :
    zoomOmegaLift lam h zc u = fun w => zoomOmega lam h zc u (zoomLiftPoint w) := rfl

/-- The lifted equation `eq:aniso:zoom:lifted` off the axis: the lift to `ℝ⁴` applied to
`eq:aniso:zoom:finite:equation`. -/
theorem finLift_pde {lam h zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {z : Vec 5 × ℝ} (hz : z ∈ finLiftDomain lam h zc) :
    fderiv ℝ (zoomOmegaLift lam h zc u) z (0, 1)
        + ∑ i, zoomDrift lam h zc u z i * fderiv ℝ (zoomOmegaLift lam h zc u) z (basisVec i, 0)
      = (∑ i : Fin 5, if (i : ℕ) < 4 then
          fderiv ℝ (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec i, 0)) z
            (basisVec i, 0) else 0)
        + (lam ^ (2 * h)) ^ 2 * fderiv ℝ (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w
            (basisVec 4, 0)) z (basisVec 4, 0)
        + fderiv ℝ (fun w => zoomS lam h zc u (zoomLiftPoint w) ^ 2
            / (zoomLiftPoint w).1.1 ^ 2) z (basisVec 4, 0)
        + zoomForce lam h zc f (zoomLiftPoint z) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  set O := finMeridionalDomain lam h zc with hO
  set S := finLiftDomain lam h zc with hS
  have hOo : IsOpen O := isOpen_finMeridionalDomain lam h zc
  have hSo : IsOpen S := isOpen_finLiftDomain lam h zc
  have hR : 0 < zoomLiftRadius z.1 := hz.1
  set Ω := zoomOmega lam h zc u with hΩdef
  have hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω O := contDiffOn_zoomOmega_finMeridional hlam hu
  have hdrΩ : ContDiffOn ℝ (⊤ : ℕ∞) (dr Ω) O := contDiffOn_dr hOo hΩ
  have hdzΩ : ContDiffOn ℝ (⊤ : ℕ∞) (dz Ω) O := contDiffOn_dz hOo hΩ
  have hq : zoomOmegaLift lam h zc u = fun w => Ω (zoomLiftPoint w) := rfl
  -- first derivatives, at every off-axis point
  have hrad : ∀ w ∈ S, ∀ i : Fin 5, i ≠ 4 →
      fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec i, 0)
        = dr Ω (zoomLiftPoint w) * (w.1 i / zoomLiftRadius w.1) := by
    intro w hw i hi
    rw [hq]
    exact fderiv_comp_zoomLiftPoint_radial hw.1 (differentiableAt_of_finLiftDomain hΩ hw) hi
  have hver : ∀ w ∈ S, fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec 4, 0)
      = dz Ω (zoomLiftPoint w) := by
    intro w hw
    rw [hq]
    exact fderiv_comp_zoomLiftPoint_vertical hw.1 (differentiableAt_of_finLiftDomain hΩ hw)
  have htime : fderiv ℝ (zoomOmegaLift lam h zc u) z (0, 1) = dtPast Ω (zoomLiftPoint z) := by
    rw [hq]
    exact fderiv_comp_zoomLiftPoint_time hR (differentiableAt_of_finLiftDomain hΩ hz)
  -- second derivatives
  have hrad2 : ∀ i : Fin 5, i ≠ 4 →
      fderiv ℝ (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec i, 0)) z (basisVec i, 0)
        = dr (dr Ω) (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) ^ 2
          + dr Ω (zoomLiftPoint z) * (1 / zoomLiftRadius z.1 - z.1 i ^ 2 / zoomLiftRadius z.1 ^
            3) := by
    intro i hi
    have heq : (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec i, 0))
        =ᶠ[𝓝 z] fun w => dr Ω (zoomLiftPoint w) * (w.1 i / zoomLiftRadius w.1) := by
      filter_upwards [hSo.mem_nhds hz] with w hw
      exact hrad w hw i hi
    rw [heq.fderiv_eq]
    exact fderiv_comp_zoomLiftPoint_mul_dir hR (differentiableAt_of_finLiftDomain hdrΩ hz) hi
  have hver2 : fderiv ℝ (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec 4, 0)) z
      (basisVec 4, 0) = dz (dz Ω) (zoomLiftPoint z) := by
    have heq : (fun w => fderiv ℝ (zoomOmegaLift lam h zc u) w (basisVec 4, 0))
        =ᶠ[𝓝 z] fun w => dz Ω (zoomLiftPoint w) := by
      filter_upwards [hSo.mem_nhds hz] with w hw
      exact hver w hw
    rw [heq.fderiv_eq]
    exact fderiv_comp_zoomLiftPoint_vertical hR (differentiableAt_of_finLiftDomain hdzΩ hz)
  have hswirl : fderiv ℝ (fun w => zoomS lam h zc u (zoomLiftPoint w) ^ 2
      / (zoomLiftPoint w).1.1 ^ 2) z (basisVec 4, 0)
      = dz (fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2) (zoomLiftPoint z) :=
    fderiv_comp_zoomLiftPoint_vertical (g := fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2) hR
      (differentiableAt_of_finLiftDomain (contDiffOn_zoomSwirlFlux_finMeridional hu) hz)
  have hB : ∀ i : Fin 5, i ≠ 4 → zoomDrift lam h zc u z i
      = zoomV lam h zc u (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) := by
    intro i hi
    simp [zoomDrift, hi]
  have hB4 : zoomDrift lam h zc u z 4 = zoomW lam h zc u (zoomLiftPoint z) := by
    simp [zoomDrift]
  have hpde := zoomOmega_pde lam h zc hlam u pr f hsol haxi (zoomLiftPoint z) hz.2 hR.ne'
  have hp : (zoomLiftPoint z).1.1 = zoomLiftRadius z.1 := rfl
  rw [hp] at hpde
  obtain ⟨h1, h2⟩ := sum_radial_lift_identities hR
  rw [sum_fin_five_ite_lt_four, Fin.sum_univ_five, htime, hrad z hz 0 (by decide),
    hrad z hz 1 (by decide), hrad z hz 2 (by decide), hrad z hz 3 (by decide), hver z hz,
    hrad2 0 (by decide), hrad2 1 (by decide), hrad2 2 (by decide), hrad2 3 (by decide), hver2,
    hswirl, hB 0 (by decide), hB 1 (by decide), hB 2 (by decide), hB 3 (by decide), hB4]
  have hF : zoomForce lam h zc f (zoomLiftPoint z)
      = lam ^ 5 * lam ^ (2 * h) * potentialVorticity f (zoomPoint lam h zc (zoomLiftPoint z)) :=
    rfl
  rw [hF]
  linear_combination hpde
    + (zoomV lam h zc u (zoomLiftPoint z) * dr Ω (zoomLiftPoint z)
      - dr (dr Ω) (zoomLiftPoint z)) * h1 - dr Ω (zoomLiftPoint z) * h2

/-- The residual identity off the axis: against a test function supported in a compact subset of
the off-axis lifted domain, the pairing of `Ω̃_n` with the adjoint operator of
`eq:aniso:zoom:finite:limit` equals `δ_n² ∫ Ω̃_n ∂_ZZ ψ - ∫ F̃_n ∂_Z ψ + ∫ G̃_n ψ`. -/
theorem integral_finResidual_eq_of_subset_finLiftDomain {lam h zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {K : Set (Vec 5 × ℝ)} (hK : IsCompact K) (hKS : K ⊆ finLiftDomain lam h zc)
    {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψK : tsupport ψ ⊆ K) :
    ∫ z, zoomOmegaLift lam h zc u z *
        (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (zoomDrift lam h zc u z)
          - finDriftDiv lam h zc u z * ψ z - partialLaplacian 5 4 ψ z)
      = ∫ z, ((lam ^ (2 * h)) ^ 2 * zoomOmegaLift lam h zc u z
            * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z (basisVec 4, 0)
          - zoomS lam h zc u (zoomLiftPoint z) ^ 2 / (zoomLiftPoint z).1.1 ^ 2
            * fderiv ℝ ψ z (basisVec 4, 0)
          + zoomForce lam h zc f (zoomLiftPoint z) * ψ z) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder := hsol.2.2.1
  exact integral_liftedResidual_eq (isOpen_finLiftDomain lam h zc) hK hKS ((lam ^ (2 * h)) ^ 2)
    (contDiffOn_comp_zoomLiftPoint (contDiffOn_zoomOmega_finMeridional hlam hu))
    (contDiffOn_zoomDrift_apply hu)
    (contDiffOn_comp_zoomLiftPoint (g := fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2)
      (contDiffOn_zoomSwirlFlux_finMeridional hu))
    (contDiffOn_comp_zoomLiftPoint (contDiffOn_zoomForce_finMeridional hlam hf)).continuousOn
    (fun z hz => finLift_div hlam hsol haxi hz) (fun z hz => finLift_pde hlam hsol haxi hz)
    hψ hψc hψK

end CIV
