/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.PotentialVorticity
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Identities.PartialSmooth
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm

/-!
# Force Quotient

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If the force is `C²`-bounded by `M`, then the azimuthal vorticity is bounded by `2M`. -/
theorem abs_azimuthalVorticity_le_of_forceC2Bounded {f : ParabolicPoint → Vec3} {M : ℝ}
    (hM : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ M) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    |azimuthalVorticity f z| ≤ 2 * M := by
  have h0 := hM z hz 0 ![0,0,1] (by decide)
  have h2 := hM z hz 2 ![1,0,0] (by decide)
  have hav : azimuthalVorticity f z
      = multiPartial (fun w => f w 0) ![0,0,1] z
        - multiPartial (fun w => f w 2) ![1,0,0] z := by
    simp [azimuthalVorticity, curlComp_one, multiPartial, Function.iterate_zero]
  rw [hav]
  have habs : |multiPartial (fun w => f w 0) ![0,0,1] z
      - multiPartial (fun w => f w 2) ![1,0,0] z|
      ≤ |multiPartial (fun w => f w 0) ![0,0,1] z|
        + |multiPartial (fun w => f w 2) ![1,0,0] z| :=
    abs_sub _ _
  have hsum : |multiPartial (fun w => f w 0) ![0,0,1] z|
        + |multiPartial (fun w => f w 2) ![1,0,0] z| ≤ 2 * M := by
    linarith only [h0, h2]
  linarith only [habs, hsum]

private lemma spatialPartial_azimuthalVorticity_eq_multiPartial
    {f : ParabolicPoint → Vec3} {z : ParabolicPoint}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hz : z ∈ unitCylinder) :
    spatialPartial (azimuthalVorticity f) 0 z
      = multiPartial (fun w => f w 0) ![1,0,1] z
        - multiPartial (fun w => f w 2) ![2,0,0] z := by
  have hcomp0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z 0) unitCylinder :=
    contDiffOn_componentFun hf 0
  have hcomp2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z 2) unitCylinder :=
    contDiffOn_componentFun hf 2
  have hspatial0_2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => f w 0) 2 z) unitCylinder :=
    contDiffOn_spatialPartial_of_smooth hcomp0 2
  have hspatial2_0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => f w 2) 0 z) unitCylinder :=
    contDiffOn_spatialPartial_of_smooth hcomp2 0
  have hdiff0 : DifferentiableAt ℝ (fun x : Vec3 =>
      spatialPartial (fun w => f w 0) 2 (x, z.2)) z.1 := by
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : Vec3 × ℝ => spatialPartial (fun w => f w 0) 2 z') z :=
      hspatial0_2.contDiffAt (isOpen_unitCylinder_prod.mem_nhds hz)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => (x, z.2)) :=
      (contDiff_id.prodMk contDiff_const)
    exact (hcd.comp z.1 hφ.contDiffAt).differentiableAt (by norm_num)
  have hdiff2 : DifferentiableAt ℝ (fun x : Vec3 =>
      spatialPartial (fun w => f w 2) 0 (x, z.2)) z.1 := by
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : Vec3 × ℝ => spatialPartial (fun w => f w 2) 0 z') z :=
      hspatial2_0.contDiffAt (isOpen_unitCylinder_prod.mem_nhds hz)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => (x, z.2)) :=
      (contDiff_id.prodMk contDiff_const)
    exact (hcd.comp z.1 hφ.contDiffAt).differentiableAt (by norm_num)
  set g := fun w : ParabolicPoint => spatialPartial (fun w' => f w' 0) 2 w with hg_def
  set h := fun w : ParabolicPoint => spatialPartial (fun w' => f w' 2) 0 w with hh_def
  have hav_eq : azimuthalVorticity f = fun w => g w - h w := by
    ext w; simp [azimuthalVorticity, curlComp_one, g, h]
  rw [hav_eq]
  rw [spatialPartial_sub_of_differentiableAt hdiff0 hdiff2]
  simp [multiPartial, Function.iterate_succ, Function.iterate_zero]

/-- If the force is `C²`-bounded by `M` and `C^∞`, then the radial derivative of the azimuthal
vorticity is bounded by `2M`. -/
theorem abs_spatialPartial_azimuthalVorticity_le_of_forceC2Bounded {f : ParabolicPoint → Vec3}
    {M : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hM : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ M) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    |spatialPartial (azimuthalVorticity f) 0 z| ≤ 2 * M := by
  rw [spatialPartial_azimuthalVorticity_eq_multiPartial hf hz]
  have h0 := hM z hz 0 ![1,0,1] (by decide)
  have h2 := hM z hz 2 ![2,0,0] (by decide)
  have habs : |multiPartial (fun w => f w 0) ![1,0,1] z
      - multiPartial (fun w => f w 2) ![2,0,0] z|
      ≤ |multiPartial (fun w => f w 0) ![1,0,1] z|
        + |multiPartial (fun w => f w 2) ![2,0,0] z| :=
    abs_sub _ _
  have hsum : |multiPartial (fun w => f w 0) ![1,0,1] z|
        + |multiPartial (fun w => f w 2) ![2,0,0] z| ≤ 2 * M := by
    linarith only [h0, h2]
  linarith only [habs, hsum]

/-- If the force is `C²`-bounded and `C^∞`, then the potential vorticity of `f` is bounded on
the unit cylinder. -/
theorem abs_potentialVorticity_force_le {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder) (hMf : ForceC2Bounded f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₁ x₃ t : ℝ, (meridional x₁ x₃, t) ∈ unitCylinder →
      |potentialVorticity f (meridional x₁ x₃, t)| ≤ C := by
  rcases hMf with ⟨M, hM⟩
  refine ⟨2 * max M 0, by
    have : 0 ≤ max M 0 := le_max_right _ _
    linarith only [this], ?_⟩
  intro x₁ x₃ t hz
  have hz' : (meridional x₁ x₃, t) ∈ (vec3Ball (0 : Vec3) 1) ×ˢ (Set.Ioo (-1 : ℝ) 0) := hz
  rcases hz' with ⟨hball, ht⟩
  have hball_sq : x₁ ^ 2 + x₃ ^ 2 < 1 := by
    rw [mem_vec3Ball, sub_zero] at hball
    rw [vec3EuclideanNorm_meridional x₁ x₃] at hball
    have hlt := (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).mp hball
    simpa [sq] using hlt
  have hmem_seg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (meridional (s * x₁) x₃, t) ∈ unitCylinder := by
    intro s hs
    have hs_sq : s ^ 2 ≤ 1 := by
      have h_abs : |s| ≤ 1 := abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
      have h := abs_le.mp h_abs
      nlinarith only [h.1, h.2]
    have hx_sq : (s * x₁) ^ 2 + x₃ ^ 2 < 1 := by
      have hx_sq_ineq : (s * x₁) ^ 2 ≤ x₁ ^ 2 := by
        calc
          (s * x₁) ^ 2 = s ^ 2 * x₁ ^ 2 := by ring
          _ ≤ 1 * x₁ ^ 2 := mul_le_mul_of_nonneg_right hs_sq (sq_nonneg x₁)
          _ = x₁ ^ 2 := by simp
      linarith only [hx_sq_ineq, hball_sq]
    have hball' : vec3EuclideanNorm (meridional (s * x₁) x₃) < 1 := by
      rw [vec3EuclideanNorm_meridional (s * x₁) x₃]
      have hsq : (s * x₁) ^ 2 + x₃ ^ 2 < 1 ^ 2 := by simpa [sq] using hx_sq
      have h := (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).mpr hsq
      simpa [Real.sqrt_one] using h
    have hmem : (meridional (s * x₁) x₃, t) ∈
        (vec3Ball (0 : Vec3) 1) ×ˢ (Set.Ioo (-1 : ℝ) 0) := by
      refine ⟨?_, ht⟩
      rwa [mem_vec3Ball, sub_zero]
    -- unitCylinder = spaceTimeSet = (vec3Ball 0 1) ×ˢ Ioo (-1) 0, so hmem is
    -- definitionally the goal
    exact hmem
  have hM_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |spatialPartial (azimuthalVorticity f) 0 (meridional (s * x₁) x₃, t)| ≤ 2 * M := by
    intro s hs
    exact abs_spatialPartial_azimuthalVorticity_le_of_forceC2Bounded hf hM (hmem_seg s hs)
  have h := abs_potentialVorticity_le hfaxi hf hz hM_bound
  have hmax : 2 * M ≤ 2 * max M 0 := by
    gcongr
    exact le_max_left _ _
  linarith only [h, hmax]

end CIV
