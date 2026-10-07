/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Rotation
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Rotations about the vertical axis and the angular mean

Basic properties of the rotation `rotZ`, the rotated field `rotField`, and the angular
mean `angularMean` of `eq:interior:average`: the group law of the rotations, their
`2π`-periodicity, preservation of the Euclidean norm and hence of the balls centred on
the axis and of the unit cylinder, linearity and smoothness in the space variable, the
rotation invariance of the angular mean, and the equivalence of `IsAxisymmetricOn` with
pointwise rotation invariance on a rotation-invariant set (Section
`sec:aniso:notation`).

None of the statements needs an integrability hypothesis: the change of variables in
the angular integral is the translation invariance of the interval integral of a
periodic function, and the rotation commutes with the integral because it is a
continuous linear automorphism.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Components and the group law -/

@[simp] theorem rotZ_apply_zero (φ : ℝ) (x : Vec3) :
    rotZ φ x 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := rfl

@[simp] theorem rotZ_apply_one (φ : ℝ) (x : Vec3) :
    rotZ φ x 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := rfl

/-- A rotation about the vertical axis does not move the vertical coordinate. -/
@[simp] theorem rotZ_apply_two (φ : ℝ) (x : Vec3) : rotZ φ x 2 = x 2 := rfl

theorem rotZ_zero_apply (x : Vec3) : rotZ 0 x = x := by
  ext i; fin_cases i <;> simp [rotZ]

theorem rotZ_zero : rotZ 0 = id := funext rotZ_zero_apply

/-- The group law `Q_{φ+ψ} = Q_φ Q_ψ`. -/
theorem rotZ_add (φ ψ : ℝ) (x : Vec3) : rotZ (φ + ψ) x = rotZ φ (rotZ ψ x) := by
  ext i; fin_cases i <;> simp [rotZ, Real.cos_add, Real.sin_add] <;> ring

theorem rotZ_neg_rotZ (φ : ℝ) (x : Vec3) : rotZ (-φ) (rotZ φ x) = x := by
  rw [← rotZ_add, neg_add_cancel, rotZ_zero_apply]

theorem rotZ_rotZ_neg (φ : ℝ) (x : Vec3) : rotZ φ (rotZ (-φ) x) = x := by
  rw [← rotZ_add, add_neg_cancel, rotZ_zero_apply]

theorem rotZ_injective (φ : ℝ) : Function.Injective (rotZ φ) :=
  Function.LeftInverse.injective (rotZ_neg_rotZ φ)

theorem rotZ_surjective (φ : ℝ) : Function.Surjective (rotZ φ) :=
  Function.RightInverse.surjective (rotZ_rotZ_neg φ)

/-- The rotations are `2π`-periodic in the angle. -/
theorem rotZ_periodic : Function.Periodic rotZ (2 * Real.pi) := by
  intro φ
  ext x i
  fin_cases i <;> simp [rotZ, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem rotZ_add_two_pi (φ : ℝ) : rotZ (φ + 2 * Real.pi) = rotZ φ := rotZ_periodic φ

theorem rotZ_sub_two_pi (φ : ℝ) : rotZ (φ - 2 * Real.pi) = rotZ φ := rotZ_periodic.sub_eq φ

/-! ### Linearity, continuity, and smoothness in the space variable -/

theorem rotZ_add_vec (φ : ℝ) (x y : Vec3) : rotZ φ (x + y) = rotZ φ x + rotZ φ y := by
  ext i; fin_cases i <;> simp [rotZ] <;> ring

theorem rotZ_smul (φ c : ℝ) (x : Vec3) : rotZ φ (c • x) = c • rotZ φ x := by
  ext i; fin_cases i <;> simp [rotZ] <;> ring

theorem rotZ_zero_vec (φ : ℝ) : rotZ φ 0 = 0 := by
  ext i; fin_cases i <;> simp [rotZ]

theorem rotZ_neg_vec (φ : ℝ) (x : Vec3) : rotZ φ (-x) = -rotZ φ x := by
  ext i; fin_cases i <;> simp [rotZ] <;> ring

theorem rotZ_sub_vec (φ : ℝ) (x y : Vec3) : rotZ φ (x - y) = rotZ φ x - rotZ φ y := by
  ext i; fin_cases i <;> simp [rotZ] <;> ring

theorem continuous_rotZ (φ : ℝ) : Continuous (rotZ φ) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [rotZ] <;>
    fun_prop

/-- Joint continuity of the rotation in the angle and the point. -/
theorem continuous_rotZ_uncurry : Continuous fun p : ℝ × Vec3 => rotZ p.1 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [rotZ] <;>
    fun_prop

/-- The rotation `rotZ φ` as a continuous linear automorphism of `Vec3`, with inverse
`rotZ (-φ)`. -/
@[expose] def rotZEquiv (φ : ℝ) : Vec3 ≃L[ℝ] Vec3 where
  toFun := rotZ φ
  invFun := rotZ (-φ)
  map_add' := rotZ_add_vec φ
  map_smul' := rotZ_smul φ
  left_inv := rotZ_neg_rotZ φ
  right_inv := rotZ_rotZ_neg φ
  continuous_toFun := continuous_rotZ φ
  continuous_invFun := continuous_rotZ (-φ)

@[simp] theorem rotZEquiv_apply (φ : ℝ) (x : Vec3) : rotZEquiv φ x = rotZ φ x := rfl

@[simp] theorem rotZEquiv_symm_apply (φ : ℝ) (x : Vec3) :
    (rotZEquiv φ).symm x = rotZ (-φ) x := rfl

theorem contDiff_rotZ (φ : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (rotZ φ) :=
  (rotZEquiv φ).contDiff

theorem contDiff_rotZ_smooth (φ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rotZ φ) := contDiff_rotZ φ _

/-! ### The axis and the meridional plane -/

/-- The rotation of a point of the meridional plane `{x₂ = 0}`. -/
theorem rotZ_meridional (φ x₁ x₃ : ℝ) :
    rotZ φ (meridional x₁ x₃) = ![Real.cos φ * x₁, Real.sin φ * x₁, x₃] := by
  ext i; fin_cases i <;> simp [rotZ, meridional]

/-- Every rotation fixes the vertical axis pointwise. -/
theorem rotZ_axis (φ z : ℝ) : rotZ φ ![0, 0, z] = ![0, 0, z] := by
  ext i; fin_cases i <;> simp [rotZ]

/-! ### The Euclidean norm, balls centred on the axis, and the unit cylinder -/

/-- Rotations preserve the Euclidean norm. -/
theorem vec3EuclideanNorm_rotZ (φ : ℝ) (x : Vec3) :
    vec3EuclideanNorm (rotZ φ x) = vec3EuclideanNorm x := by
  unfold vec3EuclideanNorm
  congr 1
  simp only [Fin.sum_univ_three, rotZ_apply_zero, rotZ_apply_one, rotZ_apply_two]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.cos_sq_add_sin_sq φ

theorem rotZ_mem_vec3Ball_zero_iff (φ r : ℝ) (x : Vec3) :
    rotZ φ x ∈ vec3Ball 0 r ↔ x ∈ vec3Ball 0 r := by
  simp only [mem_vec3Ball, sub_zero, vec3EuclideanNorm_rotZ]

theorem rotZ_mem_unitCylinder_iff (φ : ℝ) (x : Vec3) (t : ℝ) :
    (rotZ φ x, t) ∈ unitCylinder ↔ (x, t) ∈ unitCylinder := by
  change (rotZ φ x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1) 0) ↔ (x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1) 0)
  rw [rotZ_mem_vec3Ball_zero_iff]

/-- The unit cylinder is invariant under every rotation about the axis. -/
theorem rotZ_mem_unitCylinder (φ : ℝ) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    (rotZ φ z.1, z.2) ∈ unitCylinder :=
  (rotZ_mem_unitCylinder_iff φ z.1 z.2).2 hz

/-! ### The rotated field -/

theorem rotField_apply (φ : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    rotField φ u z = rotZ φ (u (rotZ (-φ) z.1, z.2)) := rfl

theorem rotField_zero (u : ParabolicPoint → Vec3) : rotField 0 u = u := by
  funext z
  obtain ⟨x, t⟩ := z
  change rotZ 0 (u (rotZ (-0) x, t)) = u (x, t)
  rw [neg_zero, rotZ_zero_apply, rotZ_zero_apply]

/-- The rotated fields compose according to the group law, `ℛ_φ ℛ_ψ = ℛ_{φ+ψ}`. -/
theorem rotField_rotField (φ ψ : ℝ) (u : ParabolicPoint → Vec3) :
    rotField φ (rotField ψ u) = rotField (φ + ψ) u := by
  funext z
  simp only [rotField, ← rotZ_add, neg_add_rev]

theorem rotField_neg_rotField (φ : ℝ) (u : ParabolicPoint → Vec3) :
    rotField (-φ) (rotField φ u) = u := by
  rw [rotField_rotField, neg_add_cancel, rotField_zero]

theorem rotField_rotField_neg (φ : ℝ) (u : ParabolicPoint → Vec3) :
    rotField φ (rotField (-φ) u) = u := by
  rw [rotField_rotField, add_neg_cancel, rotField_zero]

theorem rotField_add_two_pi (φ : ℝ) (u : ParabolicPoint → Vec3) :
    rotField (φ + 2 * Real.pi) u = rotField φ u := by
  have h : rotZ (-(φ + 2 * Real.pi)) = rotZ (-φ) := by
    rw [neg_add, ← sub_eq_add_neg, rotZ_sub_two_pi]
  funext z
  simp only [rotField, rotZ_add_two_pi, h]

/-- At a fixed point, the rotated field is a `2π`-periodic function of the angle. -/
theorem rotField_periodic (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    Function.Periodic (fun φ => rotField φ u z) (2 * Real.pi) :=
  fun φ => congrFun (rotField_add_two_pi φ u) z

/-! ### The angular mean -/

theorem angularMean_apply (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    angularMean u z = (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z := rfl

/-- The integral over a period of a periodic function is translation invariant. -/
theorem intervalIntegral_comp_add_left_of_periodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} {T : ℝ} (hF : Function.Periodic F T) (ψ : ℝ) :
    ∫ φ in (0 : ℝ)..T, F (ψ + φ) = ∫ φ in (0 : ℝ)..T, F φ := by
  rw [intervalIntegral.integral_comp_add_left, add_zero, hF.intervalIntegral_add_eq ψ 0, zero_add]

/-- A rotation commutes with the interval integral of a vector field. -/
theorem rotZ_intervalIntegral (ψ : ℝ) (F : ℝ → Vec3) (a b : ℝ) :
    rotZ ψ (∫ φ in a..b, F φ) = ∫ φ in a..b, rotZ ψ (F φ) := by
  have key : ∀ s : Set ℝ, rotZ ψ (∫ φ in s, F φ) = ∫ φ in s, rotZ ψ (F φ) := fun s =>
    ((rotZEquiv ψ).toContinuousLinearMap.integral_comp_comm' (rotZEquiv ψ).antilipschitz F).symm
  simp only [intervalIntegral, rotZ_sub_vec, key]

/-- A field fixed by every rotation is its own angular mean. -/
theorem isAxisymmetricOn_of_forall_rotField_eq {u : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} (h : ∀ φ, ∀ z ∈ S, rotField φ u z = u z) :
    IsAxisymmetricOn u S := by
  intro z hz
  have hc : (fun φ => rotField φ u z) = fun _ => u z := funext fun φ => h φ z hz
  rw [angularMean_apply, hc, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ Real.two_pi_pos.ne', one_smul]

theorem angularMean_eq_of_forall_rotField_eq {u : ParabolicPoint → Vec3}
    (h : ∀ φ, rotField φ u = u) : angularMean u = u :=
  funext fun z =>
    isAxisymmetricOn_of_forall_rotField_eq (S := univ) (fun φ z _ => congrFun (h φ) z) z
      (mem_univ z)

/-- The angular mean is fixed by every rotation: `ℛ_ψ 𝒫u = 𝒫u`. -/
theorem rotField_angularMean (ψ : ℝ) (u : ParabolicPoint → Vec3) :
    rotField ψ (angularMean u) = angularMean u := by
  funext z
  change rotZ ψ ((2 * Real.pi)⁻¹ •
      ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u (rotZ (-ψ) z.1, z.2)) =
    (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z
  rw [rotZ_smul, rotZ_intervalIntegral]
  congr 1
  calc ∫ φ in (0 : ℝ)..(2 * Real.pi), rotZ ψ (rotField φ u (rotZ (-ψ) z.1, z.2))
      = ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField (ψ + φ) u z := by
        congr 1
        funext φ
        exact congrFun (rotField_rotField ψ φ u) z
    _ = ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z :=
        intervalIntegral_comp_add_left_of_periodic (rotField_periodic u z) ψ

/-- The angular mean of a rotated field is the angular mean of the field: `𝒫 ℛ_ψ u = 𝒫u`. -/
theorem angularMean_rotField (ψ : ℝ) (u : ParabolicPoint → Vec3) :
    angularMean (rotField ψ u) = angularMean u := by
  funext z
  rw [angularMean_apply, angularMean_apply]
  congr 1
  calc ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ (rotField ψ u) z
      = ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField (ψ + φ) u z := by
        congr 1
        funext φ
        rw [congrFun (rotField_rotField φ ψ u) z, add_comm]
    _ = ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z :=
        intervalIntegral_comp_add_left_of_periodic (rotField_periodic u z) ψ

/-- The angular mean is a projection: `𝒫 𝒫u = 𝒫u`. -/
theorem angularMean_angularMean (u : ParabolicPoint → Vec3) :
    angularMean (angularMean u) = angularMean u :=
  angularMean_eq_of_forall_rotField_eq fun ψ => rotField_angularMean ψ u

theorem isAxisymmetricOn_angularMean (u : ParabolicPoint → Vec3) (S : Set ParabolicPoint) :
    IsAxisymmetricOn (angularMean u) S :=
  fun z _ => congrFun (angularMean_angularMean u) z

/-! ### Axisymmetry on a set -/

theorem IsAxisymmetricOn.mono {u : ParabolicPoint → Vec3} {S T : Set ParabolicPoint}
    (h : IsAxisymmetricOn u T) (hST : S ⊆ T) : IsAxisymmetricOn u S :=
  fun z hz => h z (hST hz)

theorem isAxisymmetricOn_univ_iff (u : ParabolicPoint → Vec3) :
    IsAxisymmetricOn u univ ↔ angularMean u = u :=
  ⟨fun h => funext fun z => h z (mem_univ z), fun h z _ => congrFun h z⟩

/-- On a rotation-invariant set, an axisymmetric field is fixed pointwise by every
rotation. -/
theorem IsAxisymmetricOn.rotField_eq {u : ParabolicPoint → Vec3} {S : Set ParabolicPoint}
    (h : IsAxisymmetricOn u S) (hS : ∀ φ, ∀ z ∈ S, (rotZ φ z.1, z.2) ∈ S) (φ : ℝ)
    {z : ParabolicPoint} (hz : z ∈ S) : rotField φ u z = u z := by
  have hz' : (rotZ (-φ) z.1, z.2) ∈ S := hS (-φ) z hz
  calc rotField φ u z = rotZ φ (u (rotZ (-φ) z.1, z.2)) := rfl
    _ = rotZ φ (angularMean u (rotZ (-φ) z.1, z.2)) := by rw [h _ hz']
    _ = rotField φ (angularMean u) z := rfl
    _ = angularMean u z := congrFun (rotField_angularMean φ u) z
    _ = u z := h z hz

/-- On a rotation-invariant set, axisymmetry is pointwise invariance under every
rotation. -/
theorem isAxisymmetricOn_iff {u : ParabolicPoint → Vec3} {S : Set ParabolicPoint}
    (hS : ∀ φ, ∀ z ∈ S, (rotZ φ z.1, z.2) ∈ S) :
    IsAxisymmetricOn u S ↔ ∀ φ, ∀ z ∈ S, rotField φ u z = u z :=
  ⟨fun h φ _ hz => h.rotField_eq hS φ hz, isAxisymmetricOn_of_forall_rotField_eq⟩

/-- Axisymmetry on the unit cylinder is pointwise rotation invariance there. -/
theorem isAxisymmetricOn_unitCylinder_iff (u : ParabolicPoint → Vec3) :
    IsAxisymmetricOn u unitCylinder ↔ ∀ φ, ∀ z ∈ unitCylinder, rotField φ u z = u z :=
  isAxisymmetricOn_iff fun φ _ hz => rotZ_mem_unitCylinder φ hz

end CIV
