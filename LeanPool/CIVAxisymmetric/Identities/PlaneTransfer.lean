/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.GradientIdentity
public import LeanPool.CIVAxisymmetric.Identities.StretchingIdentity
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# From the meridional plane to the whole ball

The identities `gradient_sq_meridional` and `stretching_meridional` are proved on the
meridional plane `{x₂ = 0}`, off the axis. This file supplies the transfer that extends
them to every point of `B(1)`: polar coordinates in the first two components write any
point as `rotZ φ (meridional x₁ x₃)` with `x₁ ≥ 0` (`exists_rotZ_meridional`), and a
rotation-invariant quantity therefore agrees with its meridional-plane value at every
point (`invariant_eq_meridional`).

The Cartesian expressions `spatialPartial (fun w => u w i) j` are **not** themselves
rotation invariant: differentiating in a fixed Cartesian direction at a rotated point is
not the same operation as differentiating at the reference point. What is rotation
invariant is the pair of facts recorded here. First, the *cylindrical* coefficients of an
axisymmetric field, read by undoing the rotation of the field values
(`cylindricalCoeffs_eq_meridional` and its three components), reduce to the values on the
meridional plane; this is design note R7's identification, made precise. Second, the
scalars that actually appear in `eq:aniso:closure:gradient` and
`eq:aniso:closure:stretch` — the Frobenius norm of the full spatial derivative, the
Euclidean norm of the curl, and the vortex-stretching scalar `(ω · ∇u) · ω` — are
genuinely invariant under every rotation about the axis (`gradient_sq_rotZ_invariant`,
`curl_sq_rotZ_invariant`, `stretching_rotZ_invariant`), because `fderiv_comp_rotZ`
intertwines the spatial derivative with the rotations and `rotZ` is an orthogonal map.

Three consequences are recorded here as well. The curl itself is equivariant
(`curlVec_rotZ_eq`), hence so is the azimuthal vorticity, and the vorticity read as a
vector field (`vorticityField`) is axisymmetric (`isAxisymmetricOn_vorticityField`). The
circulation `Γ = r u_θ` is invariant (`circulation_rotZ_invariant`), which makes `swirlCoeffAt u
z = Γ / r` a public
reading of `u_θ` at a general point, equal on the polar representative to the meridional
value (`swirlCoeffAt_rotZ_meridional`). Finally `gradient_sq_ball` and `stretching_ball`
glue `gradient_sq_meridional` and `stretching_meridional` to every off-axis point of `B(1)`.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The polar representative -/

/-- Every point of `Vec3` is the image, under some rotation about the vertical axis, of a
meridional point `(x₁, 0, x₃)` with `x₁ ≥ 0` and the same third coordinate: polar
coordinates in the first two components, taking `x₁` to be the modulus and `φ` the
argument of the complex number formed from them. -/
theorem exists_rotZ_meridional (x : Vec3) :
    ∃ φ x₁ x₃ : ℝ, 0 ≤ x₁ ∧ x = rotZ φ (meridional x₁ x₃) := by
  refine ⟨Complex.arg ⟨x 0, x 1⟩, ‖(⟨x 0, x 1⟩ : ℂ)‖, x 2, norm_nonneg _, ?_⟩
  have hcos : ‖(⟨x 0, x 1⟩ : ℂ)‖ * Real.cos (Complex.arg ⟨x 0, x 1⟩) = x 0 :=
    Complex.norm_mul_cos_arg ⟨x 0, x 1⟩
  have hsin : ‖(⟨x 0, x 1⟩ : ℂ)‖ * Real.sin (Complex.arg ⟨x 0, x 1⟩) = x 1 :=
    Complex.norm_mul_sin_arg ⟨x 0, x 1⟩
  rw [rotZ_meridional]
  funext i
  fin_cases i
  · change x 0 = Real.cos (Complex.arg ⟨x 0, x 1⟩) * ‖(⟨x 0, x 1⟩ : ℂ)‖
    rw [mul_comm]; exact hcos.symm
  · change x 1 = Real.sin (Complex.arg ⟨x 0, x 1⟩) * ‖(⟨x 0, x 1⟩ : ℂ)‖
    rw [mul_comm]; exact hsin.symm
  · rfl

/-- The Euclidean norm of a rotated meridional point is the norm of its meridional
coordinates: `‖rotZ φ (x₁, 0, x₃)‖ = √(x₁² + x₃²)`. -/
theorem vec3EuclideanNorm_eq_of_rotZ_meridional (φ x₁ x₃ : ℝ) :
    vec3EuclideanNorm (rotZ φ (meridional x₁ x₃)) = Real.sqrt (x₁ ^ 2 + x₃ ^ 2) := by
  rw [vec3EuclideanNorm_rotZ]
  unfold vec3EuclideanNorm
  congr 1
  simp only [Fin.sum_univ_three, meridional]
  norm_num

/-! ### The general invariance transfer -/

/-- A scalar fixed by every rotation about the axis, at every point of the unit
cylinder, agrees at each point with its value at some `x₁ ≥ 0` representative of the
meridional plane: the transfer that extends a meridional-plane identity to all of
`B(1)` (design note R7). -/
theorem invariant_eq_meridional {Φ : ParabolicPoint → ℝ}
    (hΦ : ∀ φ : ℝ, ∀ w ∈ unitCylinder, Φ (rotZ φ w.1, w.2) = Φ w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    ∃ x₁ x₃ : ℝ, 0 ≤ x₁ ∧ Φ z = Φ (meridional x₁ x₃, z.2) := by
  obtain ⟨x, t⟩ := z
  obtain ⟨φ, x₁, x₃, hx₁, hxeq⟩ := exists_rotZ_meridional x
  refine ⟨x₁, x₃, hx₁, ?_⟩
  have hw : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder := by
    have hxball : x ∈ vec3Ball (0 : Vec3) 1 := hz.1
    rw [hxeq, rotZ_mem_vec3Ball_zero_iff] at hxball
    exact ⟨hxball, hz.2⟩
  have key := hΦ φ (meridional x₁ x₃, t) hw
  rw [← hxeq] at key
  exact key

/-! ### The cylindrical coefficients are read on the meridional plane -/

/-- At the representative point `x = rotZ φ (meridional x₁ x₃)`, undoing the rotation of
the field value recovers the value on the meridional plane: the cylindrical coefficients
`u_r (x, t) := (rotZ (-φ) (u (x, t))) 0`, `u_θ (x, t) := (rotZ (-φ) (u (x, t))) 1`, and
`u_z (x, t) := u (x, t) 2` all equal the corresponding component of `u (meridional x₁ x₃,
t)` (design note R7). -/
theorem cylindricalCoeffs_eq_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {φ x₁ x₃ t : ℝ}
    (hz : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder) :
    rotZ (-φ) (u (rotZ φ (meridional x₁ x₃), t)) = u (meridional x₁ x₃, t) := by
  have hz' : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ (meridional x₁ x₃) t).1 hz
  have key := h.apply_rotZ (z := (meridional x₁ x₃, t)) φ hz'
  rw [key, rotZ_neg_rotZ]

/-- The radial coefficient `u_r` at the representative point is `u (meridional x₁ x₃,
t) 0`. -/
theorem radialCoeff_eq_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {φ x₁ x₃ t : ℝ}
    (hz : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder) :
    rotZ (-φ) (u (rotZ φ (meridional x₁ x₃), t)) 0 = u (meridional x₁ x₃, t) 0 :=
  congrFun (cylindricalCoeffs_eq_meridional h hz) 0

/-- The swirl coefficient `u_θ` at the representative point is `u (meridional x₁ x₃,
t) 1`. -/
theorem swirlCoeff_eq_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {φ x₁ x₃ t : ℝ}
    (hz : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder) :
    rotZ (-φ) (u (rotZ φ (meridional x₁ x₃), t)) 1 = u (meridional x₁ x₃, t) 1 :=
  congrFun (cylindricalCoeffs_eq_meridional h hz) 1

/-- The vertical coefficient `u_z` at the representative point is `u (meridional x₁ x₃,
t) 2`; unlike the radial and swirl coefficients it needs no undoing of the rotation,
since `rotZ` fixes the vertical component. -/
theorem verticalCoeff_eq_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {φ x₁ x₃ t : ℝ}
    (hz : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder) :
    u (rotZ φ (meridional x₁ x₃), t) 2 = u (meridional x₁ x₃, t) 2 := by
  have hcomp := congrFun (cylindricalCoeffs_eq_meridional h hz) 2
  rwa [rotZ_apply_two] at hcomp

/-! ### The circulation and the swirl coefficient at a general point -/

/-- The circulation `Γ = r u_θ = x₁u₂ − x₂u₁` of an axisymmetric field is invariant under the
rotations about the axis: the position and the field value rotate together, and the two
`cos`/`sin` pairs cancel against each other. -/
theorem circulation_rotZ_invariant {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {z : ParabolicPoint} (hz : z ∈ unitCylinder) (φ : ℝ) :
    circulation u (rotZ φ z.1, z.2) = circulation u z := by
  have hval : u ((rotZ φ z.1 : Vec3), z.2) = rotZ φ (u z) := h.apply_rotZ φ hz
  change (rotZ φ z.1 : Vec3) 0 * u ((rotZ φ z.1 : Vec3), z.2) 1
      - (rotZ φ z.1 : Vec3) 1 * u ((rotZ φ z.1 : Vec3), z.2) 0
    = z.1 0 * u z 1 - z.1 1 * u z 0
  rw [hval, rotZ_apply_zero, rotZ_apply_one, rotZ_apply_zero, rotZ_apply_one]
  have hpyth := Real.cos_sq_add_sin_sq φ
  linear_combination (z.1 0 * u z 1 - z.1 1 * u z 0) * hpyth

/-- The swirl coefficient `u_θ` read at a general point: the circulation `Γ = r u_θ`
divided by the distance `r = √(x₁² + x₂²)` to the axis. This is the public reading of the
azimuthal component of the field in the cylindrical frame. On the axis the quotient is
`0 / 0`, whose value in Lean is `0`; for an axisymmetric field that value is the correct
one, since `apply_axis_one` forces `u_θ = 0` there, so the definition needs no caveat. -/
@[expose] def swirlCoeffAt (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  circulation u z / Real.sqrt ((z.1 0) ^ 2 + (z.1 1) ^ 2)

/-- At the polar representative `x = rotZ φ (meridional x₁ x₃)` with `x₁ > 0`, the swirl
coefficient of an axisymmetric field is the second component of its value on the meridional
plane. Together with `exists_rotZ_meridional` this carries a meridional-plane bound on `u_θ`,
such as the conclusion of `CIV.swirl_bound`, to every point of the ball off the axis. -/
theorem swirlCoeffAt_rotZ_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {φ x₁ x₃ t : ℝ} (hx₁ : 0 < x₁)
    (hz : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder) :
    swirlCoeffAt u (rotZ φ (meridional x₁ x₃), t) = u (meridional x₁ x₃, t) 1 := by
  have hz' : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ (meridional x₁ x₃) t).1 hz
  have hnum : circulation u ((rotZ φ (meridional x₁ x₃) : Vec3), t)
      = x₁ * u (meridional x₁ x₃, t) 1 := by
    have hrot := circulation_rotZ_invariant h (z := ((meridional x₁ x₃ : Vec3), t)) hz' φ
    rw [hrot]
    change (meridional x₁ x₃ : Vec3) 0 * u (meridional x₁ x₃, t) 1
        - (meridional x₁ x₃ : Vec3) 1 * u (meridional x₁ x₃, t) 0
      = x₁ * u (meridional x₁ x₃, t) 1
    simp [meridional]
  have hsq : (rotZ φ (meridional x₁ x₃) : Vec3) 0 ^ 2
      + (rotZ φ (meridional x₁ x₃) : Vec3) 1 ^ 2 = x₁ ^ 2 := by
    rw [rotZ_apply_zero, rotZ_apply_one]
    have hm0 : (meridional x₁ x₃ : Vec3) 0 = x₁ := by simp [meridional]
    have hm1 : (meridional x₁ x₃ : Vec3) 1 = 0 := by simp [meridional]
    rw [hm0, hm1]
    have hpyth := Real.cos_sq_add_sin_sq φ
    linear_combination x₁ ^ 2 * hpyth
  change circulation u ((rotZ φ (meridional x₁ x₃) : Vec3), t)
      / Real.sqrt ((rotZ φ (meridional x₁ x₃) : Vec3) 0 ^ 2
        + (rotZ φ (meridional x₁ x₃) : Vec3) 1 ^ 2)
    = u (meridional x₁ x₃, t) 1
  rw [hnum, hsq, Real.sqrt_sq hx₁.le, mul_comm, mul_div_assoc, div_self hx₁.ne', mul_one]

/-! ### Rotation invariance of the basis vectors under `rotZ` -/

private lemma rotZ_neg_basisVec_zero (φ : ℝ) :
    rotZ (-φ) (basisVec 0 : Vec3)
      = Real.cos φ • (basisVec 0 : Vec3) - Real.sin φ • basisVec 1 := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply, Real.cos_neg, Real.sin_neg]

private lemma rotZ_neg_basisVec_one (φ : ℝ) :
    rotZ (-φ) (basisVec 1 : Vec3)
      = Real.sin φ • (basisVec 0 : Vec3) + Real.cos φ • basisVec 1 := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply, Real.cos_neg, Real.sin_neg]

private lemma rotZ_neg_basisVec_two (φ : ℝ) :
    rotZ (-φ) (basisVec 2 : Vec3) = (basisVec 2 : Vec3) := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply]

/-- The sum of squared norms of a pair of vectors is invariant under the simultaneous
plane rotation `(p, q) ↦ (cos φ • p - sin φ • q, sin φ • p + cos φ • q)`: the Pythagorean
identity behind the invariance of the Frobenius norm of the spatial derivative. -/
private lemma rotate_pair_sumSq (φ : ℝ) (p q : Vec3) :
    vec3EuclideanNorm (Real.cos φ • p - Real.sin φ • q) ^ 2
        + vec3EuclideanNorm (Real.sin φ • p + Real.cos φ • q) ^ 2
      = vec3EuclideanNorm p ^ 2 + vec3EuclideanNorm q ^ 2 := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hpyth := Real.cos_sq_add_sin_sq φ
  linear_combination (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) * hpyth

/-- The dot product of `Vec3` vectors is invariant under `rotZ`, since it is an
orthogonal map. -/
private lemma rotZ_dot_rotZ (φ : ℝ) (v w : Vec3) :
    ∑ i : Fin 3, rotZ φ v i * rotZ φ w i = ∑ i : Fin 3, v i * w i := by
  simp only [Fin.sum_univ_three, rotZ_apply_zero, rotZ_apply_one, rotZ_apply_two]
  have hpyth := Real.cos_sq_add_sin_sq φ
  linear_combination (v 0 * w 0 + v 1 * w 1) * hpyth

/-! ### The spatial derivative at a rotated point, evaluated at a fixed basis vector -/

private lemma fderiv_rotZ_basisVec_zero {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    fderiv ℝ (fun y : Vec3 => u (y, t)) (rotZ φ x) (basisVec 0)
      = rotZ φ (Real.cos φ • fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 0)
          - Real.sin φ • fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 1)) := by
  have key := fderiv_comp_rotZ h hu hz φ (rotZ (-φ) (basisVec 0))
  rw [rotZ_rotZ_neg, rotZ_neg_basisVec_zero,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_sub,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_smul,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_smul] at key
  exact key

private lemma fderiv_rotZ_basisVec_one {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    fderiv ℝ (fun y : Vec3 => u (y, t)) (rotZ φ x) (basisVec 1)
      = rotZ φ (Real.sin φ • fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 0)
          + Real.cos φ • fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 1)) := by
  have key := fderiv_comp_rotZ h hu hz φ (rotZ (-φ) (basisVec 1))
  rw [rotZ_rotZ_neg, rotZ_neg_basisVec_one,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_add,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_smul,
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x).map_smul] at key
  exact key

private lemma fderiv_rotZ_basisVec_two {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    fderiv ℝ (fun y : Vec3 => u (y, t)) (rotZ φ x) (basisVec 2)
      = rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 2)) := by
  have key := fderiv_comp_rotZ h hu hz φ (rotZ (-φ) (basisVec 2))
  rw [rotZ_rotZ_neg, rotZ_neg_basisVec_two] at key
  exact key

/-! ### The gradient-squared is rotation invariant -/

private lemma gradient_sq_eq_sum_basis {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hxt : ((x, t) : ParabolicPoint) ∈ unitCylinder) :
    ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2
      = vec3EuclideanNorm (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 0)) ^ 2
        + vec3EuclideanNorm (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 1)) ^ 2
        + vec3EuclideanNorm (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 2)) ^ 2 := by
  have hstep : ∀ j : Fin 3, ∑ i : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2
      = vec3EuclideanNorm (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec j)) ^ 2 := by
    intro j
    have heq : ∀ i : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2
        = (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec j) i) ^ 2 := fun i => by
      rw [spatialPartial_eq_fderiv_apply hu hxt i j]
    simp only [heq]
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (by positivity)]
  rw [Finset.sum_comm, Fin.sum_univ_three, hstep 0, hstep 1, hstep 2]

/-- The full Cartesian gradient-squared `∑ᵢ ∑ⱼ (∂ⱼ uᵢ)²` of a smooth axisymmetric field —
the Frobenius norm of the spatial derivative — is invariant under the rotations about the
axis. This is the genuinely rotation-invariant scalar behind `gradient_sq_meridional`
(`eq:aniso:closure:gradient`): the Cartesian partial derivatives themselves are not
invariant, but `fderiv_comp_rotZ` intertwines the full derivative with `rotZ`, and the
Frobenius norm is unchanged by conjugation with an orthogonal map. -/
theorem gradient_sq_rotZ_invariant {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j (rotZ φ x, t)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2 := by
  have hz' : ((rotZ φ x, t) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ x t).2 hz
  rw [gradient_sq_eq_sum_basis hu hz', gradient_sq_eq_sum_basis hu hz,
    fderiv_rotZ_basisVec_zero h hu hz φ, fderiv_rotZ_basisVec_one h hu hz φ,
    fderiv_rotZ_basisVec_two h hu hz φ,
    vec3EuclideanNorm_rotZ, vec3EuclideanNorm_rotZ, vec3EuclideanNorm_rotZ]
  have hpair := rotate_pair_sumSq φ (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 0))
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 1))
  linarith only [hpair]

/-! ### The curl-squared is rotation invariant -/

private lemma curlComp_zero_rotZ_eq {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    curlComp u 0 (rotZ φ x, t)
      = Real.cos φ * curlComp u 0 (x, t) - Real.sin φ * curlComp u 1 (x, t) := by
  have hz' : ((rotZ φ x, t) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ x t).2 hz
  change spatialPartial (fun w => u w 2) 1 (rotZ φ x, t)
        - spatialPartial (fun w => u w 1) 2 (rotZ φ x, t)
      = Real.cos φ * (spatialPartial (fun w => u w 2) 1 (x, t)
          - spatialPartial (fun w => u w 1) 2 (x, t))
        - Real.sin φ * (spatialPartial (fun w => u w 0) 2 (x, t)
            - spatialPartial (fun w => u w 2) 0 (x, t))
  rw [spatialPartial_eq_fderiv_apply hu hz' 2 1, spatialPartial_eq_fderiv_apply hu hz' 1 2,
    spatialPartial_eq_fderiv_apply hu hz 2 1, spatialPartial_eq_fderiv_apply hu hz 1 2,
    spatialPartial_eq_fderiv_apply hu hz 0 2, spatialPartial_eq_fderiv_apply hu hz 2 0,
    fderiv_rotZ_basisVec_one h hu hz φ, fderiv_rotZ_basisVec_two h hu hz φ]
  simp only [rotZ_apply_two, rotZ_apply_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma curlComp_one_rotZ_eq {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    curlComp u 1 (rotZ φ x, t)
      = Real.sin φ * curlComp u 0 (x, t) + Real.cos φ * curlComp u 1 (x, t) := by
  have hz' : ((rotZ φ x, t) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ x t).2 hz
  change spatialPartial (fun w => u w 0) 2 (rotZ φ x, t)
        - spatialPartial (fun w => u w 2) 0 (rotZ φ x, t)
      = Real.sin φ * (spatialPartial (fun w => u w 2) 1 (x, t)
          - spatialPartial (fun w => u w 1) 2 (x, t))
        + Real.cos φ * (spatialPartial (fun w => u w 0) 2 (x, t)
            - spatialPartial (fun w => u w 2) 0 (x, t))
  rw [spatialPartial_eq_fderiv_apply hu hz' 0 2, spatialPartial_eq_fderiv_apply hu hz' 2 0,
    spatialPartial_eq_fderiv_apply hu hz 2 1, spatialPartial_eq_fderiv_apply hu hz 1 2,
    spatialPartial_eq_fderiv_apply hu hz 0 2, spatialPartial_eq_fderiv_apply hu hz 2 0,
    fderiv_rotZ_basisVec_zero h hu hz φ, fderiv_rotZ_basisVec_two h hu hz φ]
  simp only [rotZ_apply_two, rotZ_apply_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma curlComp_two_rotZ_eq {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    curlComp u 2 (rotZ φ x, t) = curlComp u 2 (x, t) := by
  have hz' : ((rotZ φ x, t) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ x t).2 hz
  change spatialPartial (fun w => u w 1) 0 (rotZ φ x, t)
        - spatialPartial (fun w => u w 0) 1 (rotZ φ x, t)
      = spatialPartial (fun w => u w 1) 0 (x, t) - spatialPartial (fun w => u w 0) 1 (x, t)
  rw [spatialPartial_eq_fderiv_apply hu hz' 1 0, spatialPartial_eq_fderiv_apply hu hz' 0 1,
    spatialPartial_eq_fderiv_apply hu hz 1 0, spatialPartial_eq_fderiv_apply hu hz 0 1,
    fderiv_rotZ_basisVec_zero h hu hz φ, fderiv_rotZ_basisVec_one h hu hz φ]
  simp only [rotZ_apply_zero, rotZ_apply_one, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  have hpyth := Real.cos_sq_add_sin_sq φ
  set a1 := fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 0) 1
  set b0 := fderiv ℝ (fun y : Vec3 => u (y, t)) x (basisVec 1) 0
  linear_combination (a1 - b0) * hpyth

/-- The curl vector `fun i => curlComp u i` at the rotated point is the rotation of the
curl vector at the reference point: the curl of an axisymmetric field is equivariant
under the rotations about the axis. -/
theorem curlVec_rotZ_eq {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    (fun k : Fin 3 => curlComp u k (rotZ φ x, t))
      = rotZ φ (fun k : Fin 3 => curlComp u k (x, t)) := by
  funext i
  fin_cases i
  · change curlComp u 0 (rotZ φ x, t) = rotZ φ (fun k : Fin 3 => curlComp u k (x, t)) 0
    rw [curlComp_zero_rotZ_eq h hu hz φ, rotZ_apply_zero]
  · change curlComp u 1 (rotZ φ x, t) = rotZ φ (fun k : Fin 3 => curlComp u k (x, t)) 1
    rw [curlComp_one_rotZ_eq h hu hz φ, rotZ_apply_one]
  · change curlComp u 2 (rotZ φ x, t) = rotZ φ (fun k : Fin 3 => curlComp u k (x, t)) 2
    rw [curlComp_two_rotZ_eq h hu hz φ, rotZ_apply_two]

/-! ### The vorticity as a vector field -/

/-- The Cartesian vorticity `ω = ∇ × u`, read as a space-time vector field. -/
@[expose] def vorticityField (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => fun i : Fin 3 => curlComp u i z

/-- The vorticity field of a smooth axisymmetric velocity is fixed by every rotation about
the axis: the curl is equivariant (`curlVec_rotZ_eq`), so rotating the field value undoes
the rotation of the point. -/
theorem rotField_vorticityField_eq {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) (φ : ℝ) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    rotField φ (vorticityField u) z = vorticityField u z := by
  have hz' : (((rotZ (-φ) z.1 : Vec3), z.2) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff (-φ) z.1 z.2).2 hz
  have hkey :
      (fun k : Fin 3 => curlComp u k ((rotZ φ (rotZ (-φ) z.1) : Vec3), z.2))
        = rotZ φ (fun k : Fin 3 => curlComp u k ((rotZ (-φ) z.1 : Vec3), z.2)) :=
    curlVec_rotZ_eq h hu hz' φ
  rw [rotZ_rotZ_neg] at hkey
  exact hkey.symm

/-- The vorticity of a smooth axisymmetric velocity is itself axisymmetric on the unit
cylinder. This is the hypothesis `gradient_sq_ball` needs before it can be applied to
`ω = ∇ × u`. -/
theorem isAxisymmetricOn_vorticityField {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    IsAxisymmetricOn (vorticityField u) unitCylinder :=
  isAxisymmetricOn_of_forall_rotField_eq fun φ _ hz => rotField_vorticityField_eq h hu φ hz

/-- The Cartesian curl-squared `∑ᵢ (curlComp u i)²` of a smooth axisymmetric field — the
Euclidean norm of the curl — is invariant under the rotations about the axis: the curl is
equivariant (`curlVec_rotZ_eq`) and `rotZ` preserves the Euclidean norm. -/
theorem curl_sq_rotZ_invariant {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    ∑ i : Fin 3, (curlComp u i (rotZ φ x, t)) ^ 2 = ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three,
    curlComp_zero_rotZ_eq h hu hz φ, curlComp_one_rotZ_eq h hu hz φ,
    curlComp_two_rotZ_eq h hu hz φ]
  have hpyth := Real.cos_sq_add_sin_sq φ
  linear_combination (curlComp u 0 (x, t) ^ 2 + curlComp u 1 (x, t) ^ 2) * hpyth

/-! ### The vortex-stretching scalar is rotation invariant -/

/-- The vortex-stretching sum `∑ᵢ ∑ⱼ ωⱼ (∂ⱼ uᵢ) ωᵢ` is the dot product `ω · Du(ω)` of the
curl `ω` with its own image under the spatial derivative, reassembled from the basis
expansion `ω = ∑ⱼ ωⱼ eⱼ` and the linearity of `Du`. -/
private lemma stretching_eq_dot {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hxt : ((x, t) : ParabolicPoint) ∈ unitCylinder) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t) * curlComp u i (x, t)
      = ∑ i : Fin 3, curlComp u i (x, t)
          * fderiv ℝ (fun y : Vec3 => u (y, t)) x (fun k => curlComp u k (x, t)) i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∑ j : Fin 3, curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t)
      * curlComp u i (x, t))
      = curlComp u i (x, t)
          * ∑ j : Fin 3, curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t)
      from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)]
  congr 1
  have hpt : (fun k : Fin 3 => curlComp u k (x, t))
      = ∑ j : Fin 3, curlComp u j (x, t) • (basisVec j : Vec3) :=
    (sum_smul_basisVec (fun k : Fin 3 => curlComp u k (x, t))).symm
  rw [hpt, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => by rw [spatialPartial_eq_fderiv_apply hu hxt i j])

/-- The vortex-stretching scalar `(ω · ∇u) · ω` of `eq:aniso:closure:stretch` is invariant
under the rotations about the axis. Reassembled as the dot product `ω · Du(ω)`
(`stretching_eq_dot`), invariance follows from the equivariance of the curl
(`curlVec_rotZ_eq`), the intertwining `fderiv_comp_rotZ`, and the orthogonal invariance
of the dot product (`rotZ_dot_rotZ`). -/
theorem stretching_rotZ_invariant {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (φ : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        curlComp u j (rotZ φ x, t) * spatialPartial (fun w => u w i) j (rotZ φ x, t)
          * curlComp u i (rotZ φ x, t)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t) * curlComp u i (x, t) := by
  have hz' : ((rotZ φ x, t) : ParabolicPoint) ∈ unitCylinder :=
    (rotZ_mem_unitCylinder_iff φ x t).2 hz
  rw [stretching_eq_dot hu hz', stretching_eq_dot hu hz]
  change ∑ i : Fin 3, (fun k : Fin 3 => curlComp u k (rotZ φ x, t)) i
        * fderiv ℝ (fun y : Vec3 => u (y, t)) (rotZ φ x)
            (fun k : Fin 3 => curlComp u k (rotZ φ x, t)) i
      = ∑ i : Fin 3, curlComp u i (x, t)
          * fderiv ℝ (fun y : Vec3 => u (y, t)) x (fun k : Fin 3 => curlComp u k (x, t)) i
  rw [curlVec_rotZ_eq h hu hz φ, fderiv_comp_rotZ h hu hz φ]
  exact rotZ_dot_rotZ φ (fun k : Fin 3 => curlComp u k (x, t))
    (fderiv ℝ (fun y : Vec3 => u (y, t)) x (fun k : Fin 3 => curlComp u k (x, t)))

/-! ### The two meridional identities on the whole ball -/

/-- The gluing of `gradient_sq_meridional` to a general off-axis point of the unit cylinder:
the Frobenius norm of `∇u` there equals the meridional expression at the polar representative
`(x₁, 0, x₃)`, whose radial coordinate is positive because the point is off the axis. -/
theorem gradient_sq_ball {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hoff : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0) :
    ∃ x₁ x₃ : ℝ, 0 < x₁ ∧ ((meridional x₁ x₃ : Vec3), z.2) ∈ unitCylinder ∧
      ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j z) ^ 2 =
        ∑ i : Fin 3, ((spatialPartial (fun w => u w i) 0 (meridional x₁ x₃, z.2)) ^ 2
            + (spatialPartial (fun w => u w i) 2 (meridional x₁ x₃, z.2)) ^ 2)
          + ((u (meridional x₁ x₃, z.2) 0) ^ 2 + (u (meridional x₁ x₃, z.2) 1) ^ 2) / x₁ ^ 2 := by
  obtain ⟨x, t⟩ := z
  obtain ⟨φ, x₁, x₃, hx₁, hxeq⟩ := exists_rotZ_meridional x
  have hx₁pos : 0 < x₁ := by
    rcases hx₁.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hxeq
      rw [rotZ_meridional] at hxeq
      rcases hoff with h0 | h1
      · exact h0 (by rw [hxeq]; simp)
      · exact h1 (by rw [hxeq]; simp)
  have hm : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder := by
    have : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder := by rwa [← hxeq]
    exact (rotZ_mem_unitCylinder_iff φ (meridional x₁ x₃) t).1 this
  refine ⟨x₁, x₃, hx₁pos, hm, ?_⟩
  have hinv : ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => u w i) j ((x : Vec3), t)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3,
        (spatialPartial (fun w => u w i) j ((meridional x₁ x₃ : Vec3), t)) ^ 2 := by
    rw [hxeq]
    exact gradient_sq_rotZ_invariant haxi hu hm φ
  rw [hinv]
  have hplane : ((meridional x₁ x₃ : Vec3), t).1 1 = 0 := by simp [meridional]
  have hr : ((meridional x₁ x₃ : Vec3), t).1 0 ≠ 0 := by
    simpa [meridional] using hx₁pos.ne'
  have hkey := gradient_sq_meridional haxi hu hm hplane hr
  simpa [meridional] using hkey

/-- The gluing of `stretching_meridional` to a general off-axis point of the unit cylinder:
the vortex-stretching scalar `(ω · ∇u) · ω` there equals its value at the polar
representative `(x₁, 0, x₃)`, with `x₁ > 0`. -/
theorem stretching_ball {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hoff : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0) :
    ∃ x₁ x₃ : ℝ, 0 < x₁ ∧ ((meridional x₁ x₃ : Vec3), z.2) ∈ unitCylinder ∧
      ∑ i : Fin 3, ∑ j : Fin 3,
          curlComp u j z * spatialPartial (fun w => u w i) j z * curlComp u i z =
        ∑ i : Fin 3, ∑ j : Fin 3,
          curlComp u j (meridional x₁ x₃, z.2)
            * spatialPartial (fun w => u w i) j (meridional x₁ x₃, z.2)
            * curlComp u i (meridional x₁ x₃, z.2) := by
  obtain ⟨x, t⟩ := z
  obtain ⟨φ, x₁, x₃, hx₁, hxeq⟩ := exists_rotZ_meridional x
  have hx₁pos : 0 < x₁ := by
    rcases hx₁.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hxeq
      rw [rotZ_meridional] at hxeq
      rcases hoff with h0 | h1
      · exact h0 (by rw [hxeq]; simp)
      · exact h1 (by rw [hxeq]; simp)
  have hm : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder := by
    have : ((rotZ φ (meridional x₁ x₃) : Vec3), t) ∈ unitCylinder := by rwa [← hxeq]
    exact (rotZ_mem_unitCylinder_iff φ (meridional x₁ x₃) t).1 this
  refine ⟨x₁, x₃, hx₁pos, hm, ?_⟩
  rw [hxeq]
  exact stretching_rotZ_invariant haxi hu hm φ

end CIV
