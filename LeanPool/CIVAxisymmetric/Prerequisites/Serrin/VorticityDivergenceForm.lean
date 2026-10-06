/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.CartesianVorticityEquation
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn

/-!
# Vorticity Divergence Form

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Antisymmetric force flux, with `∑ₘ ∂ₘ F_{im} = (curl f)_i`. -/
@[expose] def serrinForceFlux (f : ParabolicPoint → Vec3) (i m : Fin 3) (z : ParabolicPoint) : ℝ :=
  if m = i + 1 then f z (i + 2) else if m = i + 2 then -f z (i + 1) else 0

/-- Divergence-form flux of the vorticity equation, `ω_m u_i - u_m ω_i + F_{im}`. -/
@[expose] def serrinVortFlux (u f : ParabolicPoint → Vec3) (i m : Fin 3) (z : ParabolicPoint) : ℝ :=
  curlComp u m z * u z i - u z m * curlComp u i z + serrinForceFlux f i m z

/-- The sum of spatial partial derivatives of the vorticity components vanishes on the unit
cylinder. This is the key cancellation `∑_m ∂_m ω_m = 0` that follows from the antisymmetry
of the curl. -/
theorem sum_spatialPartial_curlComp_eq_zero {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ∀ z ∈ unitCylinder, ∑ m, spatialPartial (curlComp u m) m z = 0 := by
  intro z hz
  have huc0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 0) unitCylinder :=
    contDiffOn_component hu 0
  have huc1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1) unitCylinder :=
    contDiffOn_component hu 1
  have huc2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 2) unitCylinder :=
    contDiffOn_component hu 2
  have hFtop : ∀ m : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (m + 2)) unitCylinder := by
    intro m; exact contDiffOn_component hu (m + 2)
  have hGtop : ∀ m : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (m + 1)) unitCylinder := by
    intro m; exact contDiffOn_component hu (m + 1)
  have hSP : ∀ (m j : Fin 3),
      spatialPartial (curlComp u m) j z
        = spatialSecondPartial (fun v => u v (m + 2)) j (m + 1) z
          - spatialSecondPartial (fun v => u v (m + 1)) j (m + 2) z := by
    intro m j
    have hcurlU : curlComp u m = (fun w : ParabolicPoint =>
        spatialPartial (fun v => u v (m + 2)) (m + 1) w
          - spatialPartial (fun v => u v (m + 1)) (m + 2) w) := rfl
    rw [hcurlU]
    have hFm_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w : Vec3 × ℝ => spatialPartial (fun v => u v (m + 2)) (m + 1) w) unitCylinder :=
      contDiffOn_spatialPartial (hFtop m) (m + 1)
    have hGm_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w : Vec3 × ℝ => spatialPartial (fun v => u v (m + 1)) (m + 2) w) unitCylinder :=
      contDiffOn_spatialPartial (hGtop m) (m + 2)
    rw [spatialPartial_sub_of_differentiableAt (i := j)
      (differentiableAt_spatialSlice (hFm_smooth.of_le (by norm_num)) hz)
      (differentiableAt_spatialSlice (hGm_smooth.of_le (by norm_num)) hz)]
    -- Goal: spatialPartial (spatialPartial (fun v => u v (m + 2)) (m + 1)) j z - ... = ...
    -- Rewrite using spatialSecondPartial_comm
    rw [← spatialSecondPartial, ← spatialSecondPartial]
    rw [spatialSecondPartial_comm (g := fun v => u v (m + 2)) (hFtop m) hz (m + 1) j,
      spatialSecondPartial_comm (g := fun v => u v (m + 1)) (hGtop m) hz (m + 2) j]
  rw [Fin.sum_univ_three]
  have h0 := hSP 0 0
  have h1 := hSP 1 1
  have h2 := hSP 2 2
  -- Simplify Fin arithmetic
  have h01 : (0 : Fin 3) + 1 = 1 := by decide
  have h02 : (0 : Fin 3) + 2 = 2 := by decide
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h12 : (1 : Fin 3) + 2 = 0 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  have h22 : (2 : Fin 3) + 2 = 1 := by decide
  simp [h01, h02, h11, h12, h21, h22] at h0 h1 h2
  rw [h0, h1, h2]
  have hc01 : spatialSecondPartial (fun v => u v 0) 2 1 z =
      spatialSecondPartial (fun v => u v 0) 1 2 z :=
    spatialSecondPartial_comm huc0 hz 2 1
  have hc02 : spatialSecondPartial (fun v => u v 1) 0 2 z =
      spatialSecondPartial (fun v => u v 1) 2 0 z :=
    spatialSecondPartial_comm huc1 hz 0 2
  have hc12 : spatialSecondPartial (fun v => u v 2) 1 0 z =
      spatialSecondPartial (fun v => u v 2) 0 1 z :=
    spatialSecondPartial_comm huc2 hz 1 0
  rw [hc01, hc02, hc12]
  ring

/-- Product rule for the classical spatial partial derivative on the unit cylinder: when both
factors are smooth, the derivative of the product is the sum of the standard Leibniz terms. -/
theorem spatialPartial_mul_of_contDiffOn {a b : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => a z) unitCylinder)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => b z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => a w * b w) j z =
      spatialPartial a j z * b z + a z * spatialPartial b j z := by
  have ha_diff : DifferentiableAt ℝ (fun x : Vec3 => a (x, z.2)) z.1 :=
    differentiableAt_spatialSlice (ha.of_le (by norm_num)) hz
  have hb_diff : DifferentiableAt ℝ (fun x : Vec3 => b (x, z.2)) z.1 :=
    differentiableAt_spatialSlice (hb.of_le (by norm_num)) hz
  rw [spatialPartial_mul_of_differentiableAt ha_diff hb_diff]
  ring

/-- The divergence of the antisymmetric force flux equals the curl of the forcing:
`∑_m ∂_m F_{im} = (curl f)_i`. -/
theorem sum_spatialPartial_serrinForceFlux {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) :
    ∀ z ∈ unitCylinder, ∀ i,
      ∑ m, spatialPartial (serrinForceFlux f i m) m z = curlComp f i z := by
  intro z hz i
  have hfTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder := hf
  fin_cases i <;>
    simp [serrinForceFlux, curlComp, Fin.sum_univ_three, spatialPartial] <;>
    ring

/-- The vorticity equation in divergence form on the unit cylinder:
`∂_t ω − Δω = div(ω ⊗ u − u ⊗ ω) + curl f`, i.e. the form in which the interior estimates
of the proof of `lem:aniso:annulus` use it. -/
theorem vorticity_divergence_form {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ z ∈ unitCylinder, ∀ i : Fin 3,
      timePartial (curlComp u i) z - ∑ m, spatialSecondPartial (curlComp u i) m m z =
        ∑ m, spatialPartial (serrinVortFlux u f i m) m z := by
  intro z hz i
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hcl.1
  have hfTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w) unitCylinder := hcl.2.2.1
  have h_pde := cartesian_vorticity_pde u p f hcl z hz i
  -- h_pde: timePartial (curlComp u i) z + ∑ j, u z j * spatialPartial (curlComp u i) j z
  --         - ∑ j, spatialSecondPartial (curlComp u i) j j z
  --       = ∑ j, curlComp u j z * spatialPartial (fun w => u w i) j z + curlComp f i z
  have h_sum_curl : ∑ m, spatialPartial (curlComp u m) m z = 0 :=
    sum_spatialPartial_curlComp_eq_zero huTop z hz
  have h_sum_force : ∑ m, spatialPartial (serrinForceFlux f i m) m z = curlComp f i z :=
    sum_spatialPartial_serrinForceFlux hfTop z hz i
  have h_ucomp_i : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w i) unitCylinder :=
    contDiffOn_component huTop i
  have h_fcomp : ∀ k : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w k) unitCylinder := by
    intro k; exact contDiffOn_component hfTop k
  have h_curlComp : ∀ m : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => curlComp u m w) unitCylinder := by
    intro m
    have h0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (m + 2)) unitCylinder :=
      contDiffOn_component huTop (m + 2)
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (m + 1)) unitCylinder :=
      contDiffOn_component huTop (m + 1)
    exact (contDiffOn_spatialPartial h0 (m + 1)).sub
      (contDiffOn_spatialPartial h1 (m + 2))
  -- Expand the RHS sum using linearity of spatialPartial
  have h_expand : ∑ m, spatialPartial (serrinVortFlux u f i m) m z =
      (∑ m, spatialPartial (curlComp u m) m z) * u z i
      + ∑ m, curlComp u m z * spatialPartial (fun w => u w i) m z
      - (∑ m, spatialPartial (fun w => u w m) m z) * curlComp u i z
      - ∑ m, u z m * spatialPartial (curlComp u i) m z
      + ∑ m, spatialPartial (serrinForceFlux f i m) m z := by
    have h_term : ∀ m : Fin 3,
        spatialPartial
          (fun w => curlComp u m w * u w i - u w m * curlComp u i w + serrinForceFlux f i m w) m z
        = spatialPartial (curlComp u m) m z * u z i + curlComp u m z * spatialPartial (fun w =>
          u w i) m z
          - (spatialPartial (fun w => u w m) m z * curlComp u i z
            + u z m * spatialPartial (curlComp u i) m z)
          + spatialPartial (serrinForceFlux f i m) m z := by
      intro m
      have h_diff_mul : DifferentiableAt ℝ
          (fun x : Vec3 => curlComp u m (x, z.2) * u (x, z.2) i) z.1 := by
        apply DifferentiableAt.mul
        · exact differentiableAt_spatialSlice ((h_curlComp m).of_le (by norm_num)) hz
        · exact differentiableAt_spatialSlice (h_ucomp_i.of_le (by norm_num)) hz
      have h_diff_const_mul : DifferentiableAt ℝ
          (fun x : Vec3 => u (x, z.2) m * curlComp u i (x, z.2)) z.1 := by
        apply DifferentiableAt.mul
        · exact differentiableAt_spatialSlice ((contDiffOn_component huTop m).of_le (by
          norm_num)) hz
        · exact differentiableAt_spatialSlice ((h_curlComp i).of_le (by norm_num)) hz
      have h_diff_force : DifferentiableAt ℝ
          (fun x : Vec3 => serrinForceFlux f i m (x, z.2)) z.1 := by
        unfold serrinForceFlux
        split
        · -- m = i + 1 case: value is f z (i + 2)
          exact differentiableAt_spatialSlice ((h_fcomp (i + 2)).of_le (by norm_num)) hz
        · split
          · -- m = i + 2 case: value is -f z (i + 1)
            apply DifferentiableAt.neg
            exact differentiableAt_spatialSlice ((h_fcomp (i + 1)).of_le (by norm_num)) hz
          · -- else: value is 0
            simp
      have h_diff_AB : DifferentiableAt ℝ
          (fun x : Vec3 => (curlComp u m (x, z.2) * u (x, z.2) i
            - u (x, z.2) m * curlComp u i (x, z.2))) z.1 :=
        DifferentiableAt.sub h_diff_mul h_diff_const_mul
      rw [spatialPartial_add_of_differentiableAt h_diff_AB h_diff_force]
      rw [spatialPartial_sub_of_differentiableAt h_diff_mul h_diff_const_mul]
      rw [spatialPartial_mul_of_contDiffOn
        ((h_curlComp m).of_le (by norm_num)) h_ucomp_i hz m]
      rw [spatialPartial_mul_of_contDiffOn
        (contDiffOn_component huTop m) ((h_curlComp i).of_le (by norm_num)) hz m]
      rfl
    unfold serrinVortFlux
    simp only [Fin.sum_univ_three]
    rw [h_term 0, h_term 1, h_term 2]
    ring
  have h_div : ∑ m, spatialPartial (fun w => u w m) m z = 0 := hcl.2.2.2.2 z hz
  rw [h_expand, h_sum_curl, h_sum_force, h_div, zero_mul, zero_mul, zero_add, sub_zero]
  -- Goal: timePartial (curlComp u i) z - ∑ m, spatialSecondPartial (curlComp u i) m m z =
  --   ∑ m, curlComp u m z * spatialPartial (fun w => u w i) m z
  --   - ∑ m, u z m * spatialPartial (curlComp u i) m z + curlComp f i z
  -- From h_pde, rearranged:
  linarith only [h_pde]

end CIV
