/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.VorticityDivergenceForm
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.LevelSums
public import LeanPool.CIVAxisymmetric.Reduction.SpatialPartialCongrSpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Spatial derivatives of the vorticity equation in divergence form

If `∂ₜw − Δw = ∑ₘ ∂ₘ Yₘ` on the unit cylinder with smooth `w` and `Y`, then each spatial derivative
satisfies `∂ₜ(∂ⱼw) − Δ(∂ⱼw) = ∑ₘ ∂ₘ(∂ⱼYₘ)`. Applied to the divergence form of the vorticity
equation, this gives the equations of the first and second spatial derivatives of the vorticity
used at the successive levels of the interior estimates in the proof of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem isOpen_vec3Ball_zero_one : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1

/-- A spatial partial of a sum of three fields smooth on the unit cylinder is the sum of the
spatial partials. -/
theorem spatialPartial_fin3_sum_unitCylinder {G : Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ m, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => G m z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => ∑ m, G m w) j z = ∑ m, spatialPartial (G m) j z := by
  have hd : ∀ m, DifferentiableAt ℝ (fun x : Vec3 => G m (x, z.2)) z.1 := fun m =>
    differentiableAt_spatialSlice ((hG m).of_le (by norm_num)) hz
  simp only [Fin.sum_univ_three]
  rw [spatialPartial_add_of_differentiableAt ((hd 0).add (hd 1)) (hd 2),
    spatialPartial_add_of_differentiableAt (hd 0) (hd 1)]

/-- Differentiating a heat equation in divergence form in a spatial direction. -/
theorem heat_divergence_equation_spatialPartial {w : ParabolicPoint → ℝ}
    {Y : Fin 3 → ParabolicPoint → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) unitCylinder)
    (hY : ∀ m, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Y m z) unitCylinder)
    (heq : ∀ z ∈ unitCylinder, timePartial w z - ∑ m, spatialSecondPartial w m m z =
      ∑ m, spatialPartial (Y m) m z) (j : Fin 3) :
    ∀ z ∈ unitCylinder,
      timePartial (fun v => spatialPartial w j v) z -
          ∑ m, spatialSecondPartial (fun v => spatialPartial w j v) m m z =
        ∑ m, spatialPartial (fun v => spatialPartial (Y m) j v) m z := by
  intro z hz
  have hΩ := isOpen_vec3Ball_zero_one
  have hI : IsOpen (Ioo (-1 : ℝ) 0) := isOpen_Ioo
  have hsp : ∀ {g : ParabolicPoint → ℝ},
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder → ∀ k,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g k z) unitCylinder :=
    fun hg k => contDiffOn_spatialPartial hg k
  -- the identity differentiated in direction `j`
  have hcongr := spatialPartial_congr_of_eqOn_spaceTimeSet
    (v := fun v => timePartial w v - ∑ m, spatialSecondPartial w m m v)
    (u := fun v => ∑ m, spatialPartial (Y m) m v) hΩ hI (fun v hv => heq v hv) hz j
  -- left side
  have hA : DifferentiableAt ℝ (fun x : Vec3 => timePartial w (x, z.2)) z.1 :=
    differentiableAt_spatialSlice ((contDiffOn_timePartial hw).of_le (by norm_num)) hz
  have hB : ∀ m, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial w m m z) unitCylinder := fun m => hsp (hsp hw m) m
  have hBs : DifferentiableAt ℝ (fun x : Vec3 => ∑ m, spatialSecondPartial w m m (x, z.2)) z.1 := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => ∑ m, spatialSecondPartial w m m z) unitCylinder :=
      ContDiffOn.sum (fun m _ => hB m)
    exact differentiableAt_spatialSlice (hc.of_le (by norm_num)) hz
  rw [spatialPartial_sub_of_differentiableAt hA hBs,
    spatialPartial_fin3_sum_unitCylinder hB hz j,
    spatialPartial_fin3_sum_unitCylinder (fun m => hsp (hY m) m) hz j,
    spatialPartial_timePartial_comm hw hz j] at hcongr
  -- commute the derivatives in each term
  have hL : ∀ m, spatialPartial (fun v => spatialSecondPartial w m m v) j z =
      spatialSecondPartial (fun v => spatialPartial w j v) m m z := by
    intro m
    have h1 : spatialPartial (fun v => spatialSecondPartial w m m v) j z =
        spatialSecondPartial (fun v => spatialPartial w m v) m j z := rfl
    rw [h1, spatialSecondPartial_comm (hsp hw m) hz m j]
    change spatialPartial (fun v => spatialPartial (fun v' => spatialPartial w m v') j v) m z =
      spatialPartial (fun v => spatialPartial (fun v' => spatialPartial w j v') m v) m z
    exact spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI
      (fun v hv => spatialSecondPartial_comm hw hv m j) hz m
  have hR : ∀ m, spatialPartial (fun v => spatialPartial (Y m) m v) j z =
      spatialPartial (fun v => spatialPartial (Y m) j v) m z := fun m =>
    spatialSecondPartial_comm (hY m) hz m j
  simp only [hL, hR] at hcongr
  exact hcongr

/-- The vorticity components, and the fluxes of the divergence form, are smooth on the unit
cylinder for a classical solution. -/
theorem contDiffOn_serrinVortFlux {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) (i m : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinVortFlux u f i m z) unitCylinder := by
  have hu := hcl.1
  have hf := hcl.2.2.1
  have hc := contDiffOn_curlComp_unitCylinder hu
  have hui : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z k) unitCylinder :=
    fun k => (contDiffOn_pi.mp hu) k
  have hfk : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z k) unitCylinder :=
    fun k => (contDiffOn_pi.mp hf) k
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinForceFlux f i m z) unitCylinder := by
    unfold serrinForceFlux
    split_ifs
    · exact hfk _
    · exact (hfk _).neg
    · exact contDiffOn_const
  unfold serrinVortFlux
  exact (((hc m).mul (hui i)).sub ((hui m).mul (hc i))).add hF

/-- The equation of the first spatial derivatives of the vorticity. -/
theorem vorticity_first_derivative_equation {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ z ∈ unitCylinder, ∀ i j : Fin 3,
      timePartial (fun w => spatialPartial (curlComp u i) j w) z -
          ∑ m, spatialSecondPartial (fun w => spatialPartial (curlComp u i) j w) m m z =
        ∑ m, spatialPartial (fun w => spatialPartial (serrinVortFlux u f i m) j w) m z := by
  intro z hz i j
  exact heat_divergence_equation_spatialPartial (contDiffOn_curlComp_unitCylinder hcl.1 i)
    (fun m => contDiffOn_serrinVortFlux hcl i m)
    (fun z hz => vorticity_divergence_form hcl z hz i) j z hz

/-- The equation of the second spatial derivatives of the vorticity. -/
theorem vorticity_second_derivative_equation {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hcl : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ z ∈ unitCylinder, ∀ i j l : Fin 3,
      timePartial (fun w => spatialPartial (fun w' => spatialPartial (curlComp u i) j w') l w) z -
          ∑ m, spatialSecondPartial
            (fun w => spatialPartial (fun w' => spatialPartial (curlComp u i) j w') l w) m m z =
        ∑ m, spatialPartial (fun w => spatialPartial
            (fun w' => spatialPartial (serrinVortFlux u f i m) j w') l w) m z := by
  intro z hz i j l
  exact heat_divergence_equation_spatialPartial
    (contDiffOn_spatialPartial (contDiffOn_curlComp_unitCylinder hcl.1 i) j)
    (fun m => contDiffOn_spatialPartial (contDiffOn_serrinVortFlux hcl i m) j)
    (fun z hz => vorticity_first_derivative_equation hcl z hz i j) l z hz

end CIV
