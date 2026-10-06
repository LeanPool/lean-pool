/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical
public import LeanPool.CIVAxisymmetric.Identities.PlaneTransfer
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# The symmetry of the curl of the force (`rem:force:symmetry`)

No symmetry of the force is assumed in `thm:main`, but the hypotheses of that theorem imply
one: for every angle `φ`,

`ℛ_φ (curl f) = curl f` on the unit cylinder (`eq:force:symmetry`).

The argument is the one printed after `rem:force:symmetry`. Once `ℛ_φ u = u` is known — this
is the conclusion `u = 𝒫u` of `eq:interior:global:symmetry`, recorded here as
`IsAxisymmetricOn u unitCylinder` — applying `ℛ_φ` to the momentum equation
(`isClassicalSolutionOn_rotField`) produces a second classical solution with the *same*
velocity, so subtracting the two momentum equations exhibits

`ℛ_φ f - f = ∇(π ∘ Q_φ⁻¹ - π)`

as a spatial gradient. Taking the curl kills the gradient, because mixed second spatial
partial derivatives of a jointly smooth scalar commute (`spatialSecondPartial_comm`), and
leaves `curl (ℛ_φ f) = curl f`. The curl is equivariant under the rotations about the axis
for an arbitrary `C¹` field (`curlComp_rotField_eq`), i.e. `curl (ℛ_φ f) = ℛ_φ (curl f)`, and
combining the two identities gives `eq:force:symmetry`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Elementary bridges -/

/-- Pointwise agreement of two scalar fields on the unit cylinder transports the time
partial derivative. -/
private theorem timePartial_congr_cylinder {v w : ParabolicPoint → ℝ}
    (h : ∀ y ∈ unitCylinder, v y = w y) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    timePartial v z = timePartial w z := by
  show fderiv ℝ (fun s : ℝ => v (z.1, s)) z.2 1 = fderiv ℝ (fun s : ℝ => w (z.1, s)) z.2 1
  have hev : (fun s : ℝ => v (z.1, s)) =ᶠ[nhds z.2] (fun s : ℝ => w (z.1, s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz.2] with s hs using h (z.1, s) ⟨hz.1, hs⟩
  rw [hev.fderiv_eq]

/-- Pointwise agreement of two scalar fields on the unit cylinder transports a second spatial
partial derivative. -/
private theorem spatialSecondPartial_congr_cylinder {v w : ParabolicPoint → ℝ}
    (h : ∀ y ∈ unitCylinder, v y = w y) {z : ParabolicPoint} (hz : z ∈ unitCylinder)
    (i j : Fin 3) :
    spatialSecondPartial v i j z = spatialSecondPartial w i j z :=
  spatialPartial_congr_of_eqOn (fun _y hy => spatialPartial_congr_of_eqOn h hy i) hz j

/-! ### The derivative in a rotated coordinate direction -/

/-- A derivative in the direction `Q_{-φ} e₁` is the corresponding combination of the
derivatives in the directions `e₁` and `e₂`. -/
private theorem fderiv_apply_rotZ_neg_basisVec_zero (g : Vec3 → ℝ) (y : Vec3) (φ : ℝ) :
    fderiv ℝ g y (rotZ (-φ) (basisVec 0))
      = Real.cos φ * fderiv ℝ g y (basisVec 0) - Real.sin φ * fderiv ℝ g y (basisVec 1) := by
  have hb : rotZ (-φ) (basisVec 0 : Vec3)
      = Real.cos φ • (basisVec 0 : Vec3) - Real.sin φ • basisVec 1 := by
    ext k
    fin_cases k <;> simp [rotZ, basisVec_apply, Real.cos_neg, Real.sin_neg]
  rw [hb, (fderiv ℝ g y).map_sub, (fderiv ℝ g y).map_smul, (fderiv ℝ g y).map_smul,
    smul_eq_mul, smul_eq_mul]

/-- A derivative in the direction `Q_{-φ} e₂` is the corresponding combination of the
derivatives in the directions `e₁` and `e₂`. -/
private theorem fderiv_apply_rotZ_neg_basisVec_one (g : Vec3 → ℝ) (y : Vec3) (φ : ℝ) :
    fderiv ℝ g y (rotZ (-φ) (basisVec 1))
      = Real.sin φ * fderiv ℝ g y (basisVec 0) + Real.cos φ * fderiv ℝ g y (basisVec 1) := by
  have hb : rotZ (-φ) (basisVec 1 : Vec3)
      = Real.sin φ • (basisVec 0 : Vec3) + Real.cos φ • basisVec 1 := by
    ext k
    fin_cases k <;> simp [rotZ, basisVec_apply, Real.cos_neg, Real.sin_neg]
  rw [hb, (fderiv ℝ g y).map_add, (fderiv ℝ g y).map_smul, (fderiv ℝ g y).map_smul,
    smul_eq_mul, smul_eq_mul]

/-- The axial direction is fixed by the rotations about the axis. -/
private theorem fderiv_apply_rotZ_neg_basisVec_two (g : Vec3 → ℝ) (y : Vec3) (φ : ℝ) :
    fderiv ℝ g y (rotZ (-φ) (basisVec 2)) = fderiv ℝ g y (basisVec 2) := by
  have hb : rotZ (-φ) (basisVec 2 : Vec3) = (basisVec 2 : Vec3) := by
    ext k
    fin_cases k <;> simp [rotZ, basisVec_apply]
  rw [hb]

/-! ### Equivariance of the curl -/

/-- The curl is equivariant under the rotations about the axis: for an arbitrary `C¹` field
`F` on the unit cylinder, `∇ × (ℛ_φ F) = ℛ_φ (∇ × F)`. No symmetry of `F` is assumed; the
identity is the conjugation `Q_φ (∇F) Q_φ⁻¹` of the spatial derivative together with the fact
that `Q_φ` preserves the orientation. -/
theorem curlComp_rotField_eq (φ : ℝ) (F : ParabolicPoint → Vec3)
    (hF : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => F w) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    curlComp (rotField φ F) i z = rotField φ (vorticityField F) z i := by
  have hpyth := Real.cos_sq_add_sin_sq φ
  fin_cases i
  · show spatialPartial (fun w => rotField φ F w 2) 1 z
        - spatialPartial (fun w => rotField φ F w 1) 2 z
      = rotZ φ (vorticityField F (rotZ (-φ) z.1, z.2)) 0
    rw [spatialPartial_rotField_two φ F hF hz 1, spatialPartial_rotField_one φ F hF hz 2,
      rotZ_apply_zero]
    show _ = Real.cos φ * (fderiv ℝ (fun y : Vec3 => F (y, z.2) 2) (rotZ (-φ) z.1) (basisVec 1)
          - fderiv ℝ (fun y : Vec3 => F (y, z.2) 1) (rotZ (-φ) z.1) (basisVec 2))
        - Real.sin φ * (fderiv ℝ (fun y : Vec3 => F (y, z.2) 0) (rotZ (-φ) z.1) (basisVec 2)
          - fderiv ℝ (fun y : Vec3 => F (y, z.2) 2) (rotZ (-φ) z.1) (basisVec 0))
    simp only [fderiv_apply_rotZ_neg_basisVec_one, fderiv_apply_rotZ_neg_basisVec_two]
    ring
  · show spatialPartial (fun w => rotField φ F w 0) 2 z
        - spatialPartial (fun w => rotField φ F w 2) 0 z
      = rotZ φ (vorticityField F (rotZ (-φ) z.1, z.2)) 1
    rw [spatialPartial_rotField_zero φ F hF hz 2, spatialPartial_rotField_two φ F hF hz 0,
      rotZ_apply_one]
    show _ = Real.sin φ * (fderiv ℝ (fun y : Vec3 => F (y, z.2) 2) (rotZ (-φ) z.1) (basisVec 1)
          - fderiv ℝ (fun y : Vec3 => F (y, z.2) 1) (rotZ (-φ) z.1) (basisVec 2))
        + Real.cos φ * (fderiv ℝ (fun y : Vec3 => F (y, z.2) 0) (rotZ (-φ) z.1) (basisVec 2)
          - fderiv ℝ (fun y : Vec3 => F (y, z.2) 2) (rotZ (-φ) z.1) (basisVec 0))
    simp only [fderiv_apply_rotZ_neg_basisVec_zero, fderiv_apply_rotZ_neg_basisVec_two]
    ring
  · show spatialPartial (fun w => rotField φ F w 1) 0 z
        - spatialPartial (fun w => rotField φ F w 0) 1 z
      = rotZ φ (vorticityField F (rotZ (-φ) z.1, z.2)) 2
    rw [spatialPartial_rotField_one φ F hF hz 0, spatialPartial_rotField_zero φ F hF hz 1,
      rotZ_apply_two]
    show _ = fderiv ℝ (fun y : Vec3 => F (y, z.2) 1) (rotZ (-φ) z.1) (basisVec 0)
        - fderiv ℝ (fun y : Vec3 => F (y, z.2) 0) (rotZ (-φ) z.1) (basisVec 1)
    simp only [fderiv_apply_rotZ_neg_basisVec_zero, fderiv_apply_rotZ_neg_basisVec_one]
    linear_combination (fderiv ℝ (fun y : Vec3 => F (y, z.2) 1) (rotZ (-φ) z.1) (basisVec 0)
      - fderiv ℝ (fun y : Vec3 => F (y, z.2) 0) (rotZ (-φ) z.1) (basisVec 1)) * hpyth

/-! ### Two fields differing by a gradient have the same curl -/

/-- If two smooth fields differ by the spatial gradient of a jointly smooth scalar, their
curls agree: the mixed second partial derivatives of the scalar commute. -/
private theorem curlComp_congr_of_grad (F G : ParabolicPoint → Vec3) (a b : ParabolicPoint → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => F w) unitCylinder)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => a w) unitCylinder)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => b w) unitCylinder)
    (hGF : ∀ w ∈ unitCylinder, ∀ k : Fin 3,
      G w k = F w k + spatialPartial a k w - spatialPartial b k w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i : Fin 3) :
    curlComp G i z = curlComp F i z := by
  have hsplit : ∀ k j : Fin 3, spatialPartial (fun w => G w k) j z
      = spatialPartial (fun w => F w k) j z + spatialPartial (spatialPartial a k) j z
        - spatialPartial (spatialPartial b k) j z := by
    intro k j
    have hFk : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => F w k) unitCylinder :=
      (contDiffOn_component hF k).of_le (by norm_num)
    have hak : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial a k w) unitCylinder :=
      (contDiffOn_spatialPartial ha k).of_le (by norm_num)
    have hbk : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial b k w) unitCylinder :=
      (contDiffOn_spatialPartial hb k).of_le (by norm_num)
    have hA : DifferentiableAt ℝ (fun y : Vec3 => F (y, z.2) k) z.1 :=
      differentiableAt_spatialSlice (v := fun w : ParabolicPoint => F w k) hFk hz
    have hB : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial a k (y, z.2)) z.1 :=
      differentiableAt_spatialSlice (v := fun w : ParabolicPoint => spatialPartial a k w) hak hz
    have hC : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial b k (y, z.2)) z.1 :=
      differentiableAt_spatialSlice (v := fun w : ParabolicPoint => spatialPartial b k w) hbk hz
    rw [spatialPartial_congr_of_eqOn (v := fun w => G w k)
        (u := fun w => F w k + spatialPartial a k w - spatialPartial b k w)
        (fun w hw => hGF w hw k) hz j,
      spatialPartial_sub_of_differentiableAt (g := fun w => F w k + spatialPartial a k w)
        (h := spatialPartial b k) (i := j) (hA.add hB) hC,
      spatialPartial_add_of_differentiableAt (g := fun w => F w k) (h := spatialPartial a k)
        (i := j) hA hB]
  have hcomma : spatialPartial (spatialPartial a (i + 2)) (i + 1) z
      = spatialPartial (spatialPartial a (i + 1)) (i + 2) z :=
    spatialSecondPartial_comm ha hz (i + 2) (i + 1)
  have hcommb : spatialPartial (spatialPartial b (i + 2)) (i + 1) z
      = spatialPartial (spatialPartial b (i + 1)) (i + 2) z :=
    spatialSecondPartial_comm hb hz (i + 2) (i + 1)
  show spatialPartial (fun w => G w (i + 2)) (i + 1) z
      - spatialPartial (fun w => G w (i + 1)) (i + 2) z
    = spatialPartial (fun w => F w (i + 2)) (i + 1) z
      - spatialPartial (fun w => F w (i + 1)) (i + 2) z
  rw [hsplit (i + 2) (i + 1), hsplit (i + 1) (i + 2)]
  linarith only [hcomma, hcommb]

/-! ### The rotated force differs from the force by a gradient -/

/-- Applying `ℛ_φ` to the momentum equation of a classical solution whose velocity is
axisymmetric produces a second classical solution with the same velocity, so the two forces
differ by the spatial gradient of the difference of the two pressures:
`ℛ_φ f - f = ∇(π ∘ Q_φ⁻¹ - π)` on the unit cylinder. -/
private theorem rotField_force_sub_eq_grad (φ : ℝ) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) :
    ∀ w ∈ unitCylinder, ∀ k : Fin 3, rotField φ f w k
      = f w k + spatialPartial (fun v : ParabolicPoint => p (rotZ (-φ) v.1, v.2)) k w
        - spatialPartial p k w := by
  intro w hw k
  have hrotsol := isClassicalSolutionOn_rotField φ u p f hsol
  have hmomw := hsol.2.2.2.1 w hw k
  have hmomφ := hrotsol.2.2.2.1 w hw k
  have heq : ∀ y ∈ unitCylinder, rotField φ u y = u y :=
    fun y hy => haxi.rotField_eq (fun ψ _ hy' => rotZ_mem_unitCylinder ψ hy') φ hy
  have hcongr : ∀ y ∈ unitCylinder, rotField φ u y k = u y k :=
    fun y hy => congrFun (heq y hy) k
  simp only [congrFun (heq w hw), spatialPartial_congr_of_eqOn hcongr hw,
    spatialSecondPartial_congr_cylinder hcongr hw] at hmomφ
  rw [timePartial_congr_cylinder hcongr hw] at hmomφ
  linarith only [hmomw, hmomφ]

/-! ### The symmetry of the curl of the force -/

/-- **The symmetry of the curl of the force** (`rem:force:symmetry`, `eq:force:symmetry`).
Let `(u, π, f)` be a classical solution of `eq:nse:forced` on the unit cylinder whose
velocity is axisymmetric there — the conclusion `u = 𝒫u` of `eq:interior:global:symmetry`,
which the hypotheses of `thm:main` provide. Then the curl of the force is fixed by every
rotation about the axis:

`ℛ_φ (∇ × f) = ∇ × f` on the unit cylinder, for every angle `φ`.

No symmetry of `f` itself is assumed. -/
theorem rotField_vorticityField_force_eq (φ : ℝ) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    rotField φ (vorticityField f) z = vorticityField f z := by
  have hrotsol := isClassicalSolutionOn_rotField φ u p f hsol
  have hf1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => f w) unitCylinder :=
    hsol.2.2.1.of_le (by norm_num)
  funext i
  have hequi := curlComp_rotField_eq φ f hf1 hz i
  have hgrad := curlComp_congr_of_grad f (rotField φ f)
    (fun v : ParabolicPoint => p (rotZ (-φ) v.1, v.2)) p hsol.2.2.1 hrotsol.2.1 hsol.2.1
    (rotField_force_sub_eq_grad φ u p f hsol haxi) hz i
  show rotField φ (vorticityField f) z i = curlComp f i z
  rw [← hequi, hgrad]

end CIV
