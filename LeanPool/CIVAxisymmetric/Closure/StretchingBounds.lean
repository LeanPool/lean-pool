/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalanceTerms
public import LeanPool.CIVAxisymmetric.Identities.GradientIdentity
public import LeanPool.CIVAxisymmetric.Identities.RadialQuotientContinuous
public import LeanPool.CIVAxisymmetric.Statements.MeridionalQuantity

/-!
# The stretching-term bounds of `lem:aniso:closure`

This file proves two of the estimates that go into the tested vortex-stretching term of
`lem:aniso:closure`, from *Regularity of asymptotically axisymmetric solutions to the 3D
Navier–Stokes equations with analytic forcing*, arXiv:2609.20803: the unlabeled prose bound,
right after `eq:aniso:closure:stretch`, of the first three terms and the `∂_z u_r` term by
`C G Y`, and the labeled `eq:aniso:closure:angular:bound`.

## The plane-to-ball transfer

`CIV.Identities.PlaneTransfer` proves the cylindrical identities `stretching_meridional` and
`gradient_sq_meridional` on the meridional plane `{x₂ = 0}`, and transfers *rotation-invariant
scalars* (the Frobenius norm of `∇u`, the Euclidean norm of `curl u`, the vortex-stretching
scalar) to the whole ball via `exists_rotZ_meridional`: every `x` is `rotZ φ (meridional r x₃)`
for a unique `r ≥ 0`. The uniqueness is made explicit here: `r` is forced to be
`polarR x = √(x₀² + x₁²)` and `x₃` is forced to be `x 2` (`polarR_eq_of_rotZ_meridional`), so the
representative point of `x` is the *explicit*, globally continuous map
`x ↦ meridional (polarR x) (x 2)` — continuous everywhere (including on the axis, where it is
the identity), though not differentiable there.

This lets us read the cylindrical quantities of `eq:aniso:closure:stretch` at the representative
of a general point `x`, and bound them there: `stretchGTerm u x t` packages the first three terms
of the stretching sum and the `∂_z u_r` term, and `stretchAngularSwirl u x t` packages the
angular term's swirl factor `u_θ · (ω_r/r)`. Both are built from `radialQuotient`, which is
already known continuous across the axis (`continuousOn_radialQuotient_plane`), so both are
continuous on the whole open unit ball, and the pointwise bounds of `abs_stretchGTerm_le` and
`abs_two_mul_stretchAngularSwirl_mul_curlComp_one_le` integrate directly against `χ²` to the two
inequalities `stretchGTerm_integral_le` and `stretchAngularTerm_integral_abs_le`.

The remaining piece of `eq:aniso:closure:stretch`, the mixed term `(∂_r u_z) ω_r ω_z`, is
bounded by integration by parts in the `z`-direction (`eq:aniso:closure:mixed`,
`CIV.integral_cutoff_sq_stretchMixedTerm_eq`), which needs differentiability off the axis rather
than the continuity of the representative map used here.
`CIV.energy_inequality_of_mixed_term_bound` sums this file's two bounds with the mixed term into
`eq:aniso:closure:energy`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### The explicit meridional representative -/

/-- The distance from `x` to the vertical axis, `√(x₀² + x₁²)`. This is the modulus used by
`exists_rotZ_meridional`, made explicit: continuous on all of `Vec3` (though not differentiable
on the axis). -/
@[expose] def polarR (x : Vec3) : ℝ := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)

theorem polarR_nonneg (x : Vec3) : 0 ≤ polarR x := Real.sqrt_nonneg _

theorem continuous_polarR : Continuous polarR := by
  unfold polarR
  fun_prop

/-- The meridional representative of `x`: `(polarR x, 0, x 2)`, read through `meridional`. On
the axis this is `x` itself. -/
private lemma rep_eq_self_of_axis {x : Vec3} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    meridional (polarR x) (x 2) = x := by
  have hp : polarR x = 0 := by unfold polarR; rw [h0, h1]; simp
  rw [hp]
  ext i
  fin_cases i
  · show (0 : ℝ) = x 0; exact h0.symm
  · show (0 : ℝ) = x 1; exact h1.symm
  · show x 2 = x 2; rfl

/-- Any witness `(φ, r, x₃)` of `exists_rotZ_meridional x` with `r ≥ 0` has `r = polarR x` and
`x₃ = x 2`: the polar radius and height of `x` are forced by the rotated-meridional relation. -/
theorem polarR_eq_of_rotZ_meridional {x : Vec3} {φ r x₃ : ℝ} (hr : 0 ≤ r)
    (hxeq : x = rotZ φ (meridional r x₃)) : polarR x = r ∧ x 2 = x₃ := by
  have h0 : x 0 = Real.cos φ * r := by rw [hxeq, rotZ_apply_zero]; simp [meridional]
  have h1 : x 1 = Real.sin φ * r := by rw [hxeq, rotZ_apply_one]; simp [meridional]
  have h2 : x 2 = x₃ := by rw [hxeq, rotZ_apply_two]; simp [meridional]
  refine ⟨?_, h2⟩
  have hsq : x 0 ^ 2 + x 1 ^ 2 = r ^ 2 := by
    rw [h0, h1]
    have hpyth := Real.cos_sq_add_sin_sq φ
    nlinarith only [hpyth]
  unfold polarR
  rw [hsq, Real.sqrt_sq hr]

/-- Every point is the image, under some rotation about the axis, of its own explicit
meridional representative `meridional (polarR x) (x 2)`. -/
theorem exists_rotZ_polarR (x : Vec3) :
    ∃ φ : ℝ, x = rotZ φ (meridional (polarR x) (x 2)) := by
  obtain ⟨φ, r, x₃, hr, hxeq⟩ := exists_rotZ_meridional x
  obtain ⟨hR, hX3⟩ := polarR_eq_of_rotZ_meridional hr hxeq
  exact ⟨φ, by rw [hR, hX3]; exact hxeq⟩

/-- The meridional representative of `x` has the same Euclidean norm as `x`: a direct algebraic
identity, `polarR x ^ 2 + x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2`, not needing rotation
invariance. -/
theorem vec3EuclideanNorm_polarR_rep (x : Vec3) :
    vec3EuclideanNorm (meridional (polarR x) (x 2)) = vec3EuclideanNorm x := by
  unfold vec3EuclideanNorm
  congr 1
  simp only [Fin.sum_univ_three, meridional, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have hpR : polarR x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    unfold polarR; rw [Real.sq_sqrt (by positivity)]
  rw [hpR]
  ring

/-- The meridional representative of a point of an open ball about the origin is again in that
same ball: the argument is radius-agnostic, since it rests only on
`vec3EuclideanNorm_polarR_rep`. -/
theorem rep_mem_vec3Ball {x : Vec3} {ρ : ℝ} (hx : x ∈ vec3Ball (0 : Vec3) ρ) :
    meridional (polarR x) (x 2) ∈ vec3Ball (0 : Vec3) ρ := by
  rw [mem_vec3Ball, sub_zero, vec3EuclideanNorm_polarR_rep]
  simpa [mem_vec3Ball] using hx

/-- The representative pair `(polarR x, x 2)` lands in the open disk `{y₁² + y₂² < 1}` when `x`
is in the open unit ball. -/
theorem polarRRep_mapsTo :
    Set.MapsTo (fun x : Vec3 => ((polarR x, x 2) : ℝ × ℝ)) (vec3Ball (0 : Vec3) 1)
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 1} := by
  intro x hx
  have hmem := rep_mem_vec3Ball hx
  have hnorm : vec3EuclideanNorm (meridional (polarR x) (x 2)) < 1 := by
    simpa [mem_vec3Ball] using hmem
  have hnn : (0 : ℝ) ≤ vec3EuclideanNorm (meridional (polarR x) (x 2)) := Real.sqrt_nonneg _
  have hsq : vec3EuclideanNorm (meridional (polarR x) (x 2)) ^ 2 < 1 := by
    nlinarith only [hnorm, hnn]
  have heq : vec3EuclideanNorm (meridional (polarR x) (x 2)) ^ 2 = polarR x ^ 2 + (x 2) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_three, meridional, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  show (polarR x, x 2).1 ^ 2 + (polarR x, x 2).2 ^ 2 < 1
  rw [← heq]
  exact hsq

/-! ### The two invariant scalars, read at the explicit representative -/

/-- The Euclidean curl-squared of an axisymmetric field agrees at every point with its value at
the point's explicit meridional representative. -/
theorem curlSq_eq_polarR {v : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn v unitCylinder)
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : (x, t) ∈ unitCylinder) :
    ∑ i : Fin 3, (curlComp v i (x, t)) ^ 2
      = ∑ i : Fin 3, (curlComp v i (meridional (polarR x) (x 2), t)) ^ 2 := by
  by_cases haxis : x 0 = 0 ∧ x 1 = 0
  · rw [rep_eq_self_of_axis haxis.1 haxis.2]
  · have hoff : x 0 ≠ 0 ∨ x 1 ≠ 0 := not_and_or.mp haxis
    obtain ⟨φ, hxeq⟩ := exists_rotZ_polarR x
    have hzrep : (meridional (polarR x) (x 2), t) ∈ unitCylinder := by
      have hrot : ((rotZ φ (meridional (polarR x) (x 2)) : Vec3), t) ∈ unitCylinder := by
        rw [← hxeq]; exact hz
      exact (rotZ_mem_unitCylinder_iff φ (meridional (polarR x) (x 2)) t).1 hrot
    conv_lhs => rw [hxeq]
    exact curl_sq_rotZ_invariant haxi hv hzrep φ

/-- The Frobenius gradient-squared of an axisymmetric field agrees at every point with its value
at the point's explicit meridional representative. -/
theorem gradientSq_eq_polarR {v : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn v unitCylinder)
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : (x, t) ∈ unitCylinder) :
    ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => v w i) j (x, t)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => v w i) j (meridional (polarR x) (x 2), t)) ^ 2 := by
  by_cases haxis : x 0 = 0 ∧ x 1 = 0
  · rw [rep_eq_self_of_axis haxis.1 haxis.2]
  · have hoff : x 0 ≠ 0 ∨ x 1 ≠ 0 := not_and_or.mp haxis
    obtain ⟨φ, hxeq⟩ := exists_rotZ_polarR x
    have hzrep : (meridional (polarR x) (x 2), t) ∈ unitCylinder := by
      have hrot : ((rotZ φ (meridional (polarR x) (x 2)) : Vec3), t) ∈ unitCylinder := by
        rw [← hxeq]; exact hz
      exact (rotZ_mem_unitCylinder_iff φ (meridional (polarR x) (x 2)) t).1 hrot
    conv_lhs => rw [hxeq]
    exact gradient_sq_rotZ_invariant haxi hv hzrep φ

/-! ### Smoothness of the vorticity field -/

/-- The Cartesian vorticity of a smooth velocity is smooth. -/
theorem contDiffOn_vorticityField {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => vorticityField u z) unitCylinder := by
  refine contDiffOn_pi.2 fun i => ?_
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => curlComp u i z) unitCylinder
  exact (contDiffOn_spatialPartial (contDiffOn_component hu (i + 2)) (i + 1)).sub
    (contDiffOn_spatialPartial (contDiffOn_component hu (i + 1)) (i + 2))

/-! ### The four-term part of `eq:aniso:closure:stretch` -/

/-- The first three terms and the `∂_z u_r` term of `eq:aniso:closure:stretch`, read at the
meridional representative of `x`: `(∂_r u_r) ω_r² + (u_r/r) ω_θ² + (∂_z u_z) ω_z² + (∂_z u_r)
ω_r ω_z`, all evaluated at `meridional (polarR x) (x 2)`. On the meridional plane itself
(`x 1 = 0`, `x 0 ≥ 0`) the representative is `x`, and this is literally the manuscript's
expression. -/
@[expose] def stretchGTerm (u : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) : ℝ :=
  spatialPartial (fun w => u w 0) 0 (meridional (polarR x) (x 2), t)
      * (curlComp u 0 (meridional (polarR x) (x 2), t)) ^ 2
    + radialQuotient u (meridional (polarR x) (x 2), t)
        * (curlComp u 1 (meridional (polarR x) (x 2), t)) ^ 2
    + spatialPartial (fun w => u w 2) 2 (meridional (polarR x) (x 2), t)
        * (curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2
    + spatialPartial (fun w => u w 0) 2 (meridional (polarR x) (x 2), t)
        * curlComp u 0 (meridional (polarR x) (x 2), t)
        * curlComp u 2 (meridional (polarR x) (x 2), t)

/-- **The pointwise bound behind `eq:aniso:closure:stretch`'s four-term estimate.**
`stretchGTerm` is bounded, at every point of the ball `B(ρ)` (for `ρ ≤ 1`),
by `2 G` times the local enstrophy density, whenever the four cylindrical quantities of
`meridionalQuantity` are bounded by `G` at every meridional-plane point of `B(ρ)`. Each of
the four coefficients of `stretchGTerm` is one of those four quantities (`meridionalQuantity`'s
definition), and the two mixed products are split by `2|ab| ≤ a² + b²`. -/
theorem abs_stretchGTerm_le {u : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t G ρ : ℝ} (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    (hG : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G)
    (hGnn : 0 ≤ G) {x : Vec3} (hxρ : x ∈ vec3Ball (0 : Vec3) ρ) (ht : t ∈ Ioo (-1 : ℝ) 0) :
    |stretchGTerm u x t| ≤ 2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
  have hz : (x, t) ∈ unitCylinder := ⟨hρ1 hxρ, ht⟩
  set rep : Vec3 := meridional (polarR x) (x 2) with hrep
  have hrepmem : rep ∈ vec3Ball (0 : Vec3) ρ := rep_mem_vec3Ball hxρ
  have hGrep : meridionalQuantity u (rep, t) ≤ G := by
    have hkey := hG (polarR x) (x 2) hrepmem
    rw [hrep]; exact hkey
  have hmq : meridionalQuantity u (rep, t)
      = |spatialPartial (fun w => u w 0) 0 (rep, t)| + |radialQuotient u (rep, t)|
        + |spatialPartial (fun w => u w 2) 2 (rep, t)|
        + |spatialPartial (fun w => u w 0) 2 (rep, t)| := rfl
  have h1 : |spatialPartial (fun w => u w 0) 0 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have := abs_nonneg (radialQuotient u (rep, t))
    have := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    have := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, this, ‹0 ≤ |radialQuotient u (rep, t)|›,
      ‹0 ≤ |spatialPartial (fun w => u w 2) 2 (rep, t)|›]
  have h2 : |radialQuotient u (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb3 := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    have hb4 := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, hb1, hb3, hb4]
  have h3 : |spatialPartial (fun w => u w 2) 2 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb2 := abs_nonneg (radialQuotient u (rep, t))
    have hb4 := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, hb1, hb2, hb4]
  have h4 : |spatialPartial (fun w => u w 0) 2 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb2 := abs_nonneg (radialQuotient u (rep, t))
    have hb3 := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    linarith only [hGrep, hb1, hb2, hb3]
  set a0 := curlComp u 0 (rep, t)
  set a1 := curlComp u 1 (rep, t)
  set a2 := curlComp u 2 (rep, t)
  set c1 := spatialPartial (fun w => u w 0) 0 (rep, t)
  set c2 := radialQuotient u (rep, t)
  set c3 := spatialPartial (fun w => u w 2) 2 (rep, t)
  set c4 := spatialPartial (fun w => u w 0) 2 (rep, t)
  have hbound : |c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2|
      ≤ 2 * G * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) := by
    have hprod : |c4 * a0 * a2| ≤ G * (a0 ^ 2 + a2 ^ 2) := by
      have hsplit : |c4 * a0 * a2| ≤ |c4| * (a0 ^ 2 + a2 ^ 2) / 2 := by
        have hsq : (0 : ℝ) ≤ (|a0| - |a2|) ^ 2 := sq_nonneg _
        have hae : |a0 * a2| ≤ (a0 ^ 2 + a2 ^ 2) / 2 := by
          have habs : |a0 * a2| = |a0| * |a2| := abs_mul a0 a2
          have hsq0 : |a0| ^ 2 = a0 ^ 2 := sq_abs a0
          have hsq2 : |a2| ^ 2 = a2 ^ 2 := sq_abs a2
          nlinarith only [hsq, habs, hsq0, hsq2]
        calc |c4 * a0 * a2| = |c4| * |a0 * a2| := by rw [mul_assoc, abs_mul]
          _ ≤ |c4| * ((a0 ^ 2 + a2 ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hae (abs_nonneg c4)
          _ = |c4| * (a0 ^ 2 + a2 ^ 2) / 2 := by ring
      have hGa : |c4| * (a0 ^ 2 + a2 ^ 2) / 2 ≤ G * (a0 ^ 2 + a2 ^ 2) := by
        have hnn : (0 : ℝ) ≤ a0 ^ 2 + a2 ^ 2 := by positivity
        have hprodle := mul_le_mul_of_nonneg_right h4 hnn
        have hGnn2 : (0 : ℝ) ≤ G * (a0 ^ 2 + a2 ^ 2) := mul_nonneg hGnn hnn
        linarith only [hprodle, hGnn2]
      linarith only [hsplit, hGa]
    have hsum1 : |c1 * a0 ^ 2| ≤ G * a0 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a0)]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg a0)
    have hsum2 : |c2 * a1 ^ 2| ≤ G * a1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a1)]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg a1)
    have hsum3 : |c3 * a2 ^ 2| ≤ G * a2 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a2)]
      exact mul_le_mul_of_nonneg_right h3 (sq_nonneg a2)
    have htri : |c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2|
        ≤ |c1 * a0 ^ 2| + |c2 * a1 ^ 2| + |c3 * a2 ^ 2| + |c4 * a0 * a2| := by
      have e1 := abs_add_le (c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2) (c4 * a0 * a2)
      have e2 := abs_add_le (c1 * a0 ^ 2 + c2 * a1 ^ 2) (c3 * a2 ^ 2)
      have e3 := abs_add_le (c1 * a0 ^ 2) (c2 * a1 ^ 2)
      linarith only [e1, e2, e3]
    have hGa1 : (0 : ℝ) ≤ G * a1 ^ 2 := mul_nonneg hGnn (sq_nonneg a1)
    linarith only [htri, hsum1, hsum2, hsum3, hprod, hGa1]
  have hval : stretchGTerm u x t = c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2 := rfl
  have hcurl : ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := by
    rw [curlSq_eq_polarR haxi (hu.of_le (by exact_mod_cast le_top)) hz]
    simp only [Fin.sum_univ_three]
    rfl
  rw [hval, hcurl]
  exact hbound

/-! ### Continuity, and the integral form of the four-term estimate -/

/-- The four-term stretching part is continuous on the unit ball, since it is built from the
already-continuous slices of `u` and of the curl, composed with the continuous representative
map, plus the one piece built from `radialQuotient`, continuous across the axis by
`continuousOn_radialQuotient_plane`. -/
theorem continuousOn_stretchGTerm {u : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn u
    unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => stretchGTerm u x t) (vec3Ball (0 : Vec3) 1) := by
  have hrepmap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) := by
    have : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
      unfold meridional
      have hc : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
      have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
      fun_prop
    exact this.continuousOn
  have hmaps : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun x hx => rep_mem_vec3Ball hx
  have hd00 : ContinuousOn (fun x : Vec3 => spatialPartial (fun w => u w 0) 0 (x, t))
      (vec3Ball (0 : Vec3) 1) := continuousOn_dvel_slice hu 0 0 ht
  have hd22 : ContinuousOn (fun x : Vec3 => spatialPartial (fun w => u w 2) 2 (x, t))
      (vec3Ball (0 : Vec3) 1) := continuousOn_dvel_slice hu 2 2 ht
  have hd02 : ContinuousOn (fun x : Vec3 => spatialPartial (fun w => u w 0) 2 (x, t))
      (vec3Ball (0 : Vec3) 1) := continuousOn_dvel_slice hu 0 2 ht
  have hc0 : ContinuousOn (fun x : Vec3 => curlComp u 0 (x, t)) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_curl_slice hu 0 ht
  have hc1 : ContinuousOn (fun x : Vec3 => curlComp u 1 (x, t)) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_curl_slice hu 1 ht
  have hc2 : ContinuousOn (fun x : Vec3 => curlComp u 2 (x, t)) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_curl_slice hu 2 ht
  have hrq : ContinuousOn (fun x : Vec3 => radialQuotient u (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) := by
    have hplane := continuousOn_radialQuotient_plane u t (hu.of_le (by exact_mod_cast le_top))
      haxi ht
    have hcompmap : ContinuousOn (fun x : Vec3 => ((polarR x, x 2) : ℝ × ℝ))
        (vec3Ball (0 : Vec3) 1) :=
      (continuous_polarR.prodMk (continuous_apply 2)).continuousOn
    exact hplane.comp' hcompmap polarRRep_mapsTo
  refine ((((hd00.comp' hrepmap hmaps).mul ((hc0.comp' hrepmap hmaps).pow 2)).add
      (hrq.mul ((hc1.comp' hrepmap hmaps).pow 2))).add
    ((hd22.comp' hrepmap hmaps).mul ((hc2.comp' hrepmap hmaps).pow 2))).add
    (((hd02.comp' hrepmap hmaps).mul (hc0.comp' hrepmap hmaps)).mul
      (hc2.comp' hrepmap hmaps))

/-- **The four-term estimate, integrated.** The four-term part of the vortex-stretching
integrand, integrated against `χ²`, is bounded by `2 G` times the cutoff enstrophy `Y t`,
whenever `χ`'s support sits inside a ball `B(ρ) ⊆ B(1)` on which the four cylindrical
quantities of `meridionalQuantity` are bounded by `G`: the radius `MeridionalSmallness ρ`
actually delivers. -/
theorem stretchGTerm_integral_le {u : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn u
    unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t G : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0)
    (hG : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G)
    (hGnn : 0 ≤ G) :
    ∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t ≤ 2 * G * cutoffEnstrophy χ u t := by
  have hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1 := hρU.trans hρ1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hLcont : ContinuousOn (fun x : Vec3 => stretchGTerm u x t) (vec3Ball 0 1) :=
    continuousOn_stretchGTerm haxi hu ht
  have hRcont : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)
      (vec3Ball (0 : Vec3) 1) :=
    continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i ht).pow 2)
  have hLint : Integrable (fun x : Vec3 => χ x ^ 2 * stretchGTerm u x t) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul hLcont)
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hRint : Integrable
      (fun x : Vec3 => χ x ^ 2 * (2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)) := by
    refine integrable_of_cutoff hχs hχU
      ((hsqχ.continuous.continuousOn).mul (continuousOn_const.mul hRcont)) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hpt : ∀ x : Vec3, χ x ^ 2 * stretchGTerm u x t
      ≤ χ x ^ 2 * (2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) ρ
    · have habs := abs_stretchGTerm_le haxi hu hρ1 hG hGnn hxb ht
      have hle := le_abs_self (stretchGTerm u x t)
      have hsq : (0:ℝ) ≤ χ x ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_left (le_trans hle habs) hsq
      linarith only [this]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hρU hm))
      rw [hχ0]; norm_num
  calc ∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t
      ≤ ∫ x : Vec3, χ x ^ 2 * (2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) :=
        integral_mono hLint hRint hpt
    _ = 2 * G * cutoffEnstrophy χ u t := by
        rw [show (fun x : Vec3 => χ x ^ 2 * (2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2))
            = (fun x : Vec3 => (2 * G) * (χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2))
          from by funext x; ring, integral_const_mul]
        rfl

/-! ### The angular term of `eq:aniso:closure:angular:bound` -/

/-- The swirl factor of the angular term `eq:aniso:closure:angular:bound`: `u_θ · (ω_r / r)`,
read at the meridional representative of `x`. -/
@[expose] def stretchAngularSwirl (u : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) : ℝ :=
  u (meridional (polarR x) (x 2), t) 1
    * radialQuotient (vorticityField u) (meridional (polarR x) (x 2), t)

/-- The square of `radialQuotient v` at a meridional-plane point is bounded by the Frobenius
gradient-squared of `v` there: off the axis this is `(v_0/r)² ≤ (v_0² + v_1²)/r² ≤ |∇v|²` via
`gradient_sq_meridional`; on the axis `radialQuotient v` is *defined* to be `∂_0 v_0`, one of the
nonnegative summands of the same double sum. -/
private lemma sq_radialQuotient_le_gradientSq {v : ParabolicPoint → Vec3}
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder)
    (haxi : IsAxisymmetricOn v unitCylinder) {r x₃ t : ℝ} (hr : 0 ≤ r)
    (hmem : (meridional r x₃, t) ∈ unitCylinder) :
    (radialQuotient v (meridional r x₃, t)) ^ 2 ≤
      ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => v w i) j (meridional r x₃, t)) ^ 2 := by
  rcases hr.lt_or_eq with hr0 | hr0
  · have hplane : (meridional r x₃, t).1 1 = 0 := by show meridional r x₃ 1 = 0; simp [meridional]
    have hr0eq : (meridional r x₃, t).1 0 = r := by
      show meridional r x₃ 0 = r; exact meridional_apply_zero r x₃
    have hrr : (meridional r x₃, t).1 0 ≠ 0 := by rw [hr0eq]; exact hr0.ne'
    have hgrad := gradient_sq_meridional haxi hv hmem hplane hrr
    rw [hr0eq] at hgrad
    have hAeq : radialQuotient v (meridional r x₃, t) = v (meridional r x₃, t) 0 / r := by
      unfold radialQuotient
      split_ifs with h
      · exact absurd h hrr
      · rfl
    have hd : (radialQuotient v (meridional r x₃, t)) ^ 2
        = (v (meridional r x₃, t) 0) ^ 2 / r ^ 2 := by rw [hAeq, div_pow]
    rw [hd, hgrad]
    have hsplit2 : ((v (meridional r x₃, t) 0) ^ 2 + (v (meridional r x₃, t) 1) ^ 2) / r ^ 2
        = (v (meridional r x₃, t) 0) ^ 2 / r ^ 2 + (v (meridional r x₃, t) 1) ^ 2 / r ^ 2 := by
      ring
    rw [hsplit2]
    have h1 : (0 : ℝ) ≤ (v (meridional r x₃, t) 1) ^ 2 / r ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ∑ i : Fin 3, ((spatialPartial (fun w => v w i) 0 (meridional r x₃, t)) ^ 2
        + (spatialPartial (fun w => v w i) 2 (meridional r x₃, t)) ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    linarith only [h1, h2]
  · have hzero : (meridional r x₃, t).1 0 = 0 := by
      show meridional r x₃ 0 = 0
      rw [meridional_apply_zero, ← hr0]
    have hAeq : radialQuotient v (meridional r x₃, t)
        = spatialPartial (fun w => v w 0) 0 (meridional r x₃, t) := by
      unfold radialQuotient
      split_ifs with h
      · rfl
      · exact absurd hzero h
    rw [hAeq]
    have hm0 : (0 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)) := Finset.mem_univ 0
    calc (spatialPartial (fun w => v w 0) 0 (meridional r x₃, t)) ^ 2
        ≤ ∑ j : Fin 3, (spatialPartial (fun w => v w 0) j (meridional r x₃, t)) ^ 2 :=
          Finset.single_le_sum (f := fun j : Fin 3 =>
            (spatialPartial (fun w => v w 0) j (meridional r x₃, t)) ^ 2)
            (fun j _ => sq_nonneg _) hm0
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => v w i) j (meridional r x₃, t)) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin 3 =>
            ∑ j : Fin 3, (spatialPartial (fun w => v w i) j (meridional r x₃, t)) ^ 2)
            (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hm0

/-- **The pointwise bound behind `eq:aniso:closure:angular:bound`.** Twice the product of the
angular swirl factor with `ω_θ` is bounded, at every point of the ball `B(ρ)` (for `ρ ≤ 1`), by
a quarter of the local dissipation density plus `4 W²` times the local enstrophy density,
whenever `|u_θ| ≤ W` at every meridional-plane point of `B(ρ)`. The proof is the AM–GM bound
`2 W A B ≤ ¼ A² + 4 W² B²` with `A = ω_r/r`,
`B = ω_θ`, followed by `A² ≤ |∇ω|²` (`sq_radialQuotient_le_gradientSq`, applied to `ω`, dropping
the nonnegative `ω_θ²/r²` summand) and `B² ≤ |ω|²`. -/
theorem abs_two_mul_stretchAngularSwirl_mul_curlComp_one_le
    {u : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t W ρ : ℝ} (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    (hW : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W)
    {x : Vec3} (hxρ : x ∈ vec3Ball (0 : Vec3) ρ) (ht : t ∈ Ioo (-1 : ℝ) 0) :
    |2 * stretchAngularSwirl u x t * curlComp u 1
        (meridional (polarR x) (x 2), t)|
      ≤ (1 / 4) * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
        + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
  have hz : (x, t) ∈ unitCylinder := ⟨hρ1 hxρ, ht⟩
  set rep : Vec3 := meridional (polarR x) (x 2) with hrep
  have hrepmem : rep ∈ vec3Ball (0 : Vec3) ρ := rep_mem_vec3Ball hxρ
  have hzrep : (rep, t) ∈ unitCylinder := ⟨hρ1 hrepmem, hz.2⟩
  have hWrep : |u (rep, t) 1| ≤ W := by
    have hkey := hW (polarR x) (x 2) hrepmem
    rw [hrep]; exact hkey
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hωaxi : IsAxisymmetricOn (vorticityField u) unitCylinder :=
    isAxisymmetricOn_vorticityField haxi hu1
  have hωu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => vorticityField u z) unitCylinder :=
    (contDiffOn_vorticityField hu).of_le (by exact_mod_cast le_top)
  set A := radialQuotient (vorticityField u) (rep, t) with hA
  set B := curlComp u 1 (rep, t) with hB
  have hAM : |2 * W * A * B| ≤ (1/4) * A ^ 2 + 4 * W ^ 2 * B ^ 2 := by
    have hsq1 : (0:ℝ) ≤ (A / 2 - 2 * W * B) ^ 2 := sq_nonneg _
    have hsq2 : (0:ℝ) ≤ (A / 2 + 2 * W * B) ^ 2 := sq_nonneg _
    have hcases : 2 * W * A * B ≤ (1/4) * A ^ 2 + 4 * W ^ 2 * B ^ 2 ∧
        -(2 * W * A * B) ≤ (1/4) * A ^ 2 + 4 * W ^ 2 * B ^ 2 :=
      ⟨by nlinarith only [hsq1], by nlinarith only [hsq2]⟩
    rcases abs_cases (2 * W * A * B) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]; exact hcases.1
    · rw [heq]; exact hcases.2
  have hWA : |2 * stretchAngularSwirl u x t * B| ≤ |2 * W * A * B| := by
    have hval : stretchAngularSwirl u x t = u (rep, t) 1 * A := rfl
    have hWnn : (0:ℝ) ≤ W := le_trans (abs_nonneg _) hWrep
    have heq2 : |2 * stretchAngularSwirl u x t * B| = 2 * |u (rep, t) 1| * |A| * |B| := by
      rw [hval, show (2:ℝ) * (u (rep, t) 1 * A) * B = 2 * u (rep, t) 1 * A * B from by ring,
        abs_mul, abs_mul, abs_mul]
      norm_num
    have heq3 : |2 * W * A * B| = 2 * W * |A| * |B| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hWnn]
      norm_num
    rw [heq2, heq3]
    have hABnn : (0:ℝ) ≤ |A| * |B| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc 2 * |u (rep, t) 1| * |A| * |B| = 2 * (|u (rep, t) 1| * (|A| * |B|)) := by ring
      _ ≤ 2 * (W * (|A| * |B|)) := by
          have hstep := mul_le_mul_of_nonneg_right hWrep hABnn
          linarith only [hstep]
      _ = 2 * W * |A| * |B| := by ring
  have hbound : |2 * stretchAngularSwirl u x t * B| ≤ (1/4) * A ^ 2 + 4 * W ^ 2 * B ^ 2 :=
    le_trans hWA hAM
  have hA2 : A ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (rep, t)) ^ 2 :=
    sq_radialQuotient_le_gradientSq hωu1 hωaxi (polarR_nonneg x) hzrep
  have hB2 : B ^ 2 ≤ ∑ i : Fin 3, (curlComp u i (rep, t)) ^ 2 := by
    have hm1 : (1 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)) := Finset.mem_univ 1
    have hstep := Finset.single_le_sum (f := fun i : Fin 3 => (curlComp u i (rep, t)) ^ 2)
      (fun i _ => sq_nonneg _) hm1
    rw [hB]; exact hstep
  have hgradEq : ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (rep, t)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2 :=
    (gradientSq_eq_polarR hωaxi hωu1 hz).symm
  have hcurlEq : ∑ i : Fin 3, (curlComp u i (rep, t)) ^ 2
      = ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := (curlSq_eq_polarR haxi hu1 hz).symm
  have hWnn2 : (0:ℝ) ≤ 4 * W ^ 2 := by positivity
  have hfinal : (1/4) * A ^ 2 + 4 * W ^ 2 * B ^ 2 ≤ (1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
      + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    rw [← hgradEq, ← hcurlEq]
    have hA2' : (1/4) * A ^ 2 ≤ (1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
        (spatialPartial (fun w => vorticityField u w i) j (rep, t)) ^ 2 := by
      linarith only [hA2]
    have hB2' : 4 * W ^ 2 * B ^ 2 ≤ 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (rep, t)) ^ 2 :=
      mul_le_mul_of_nonneg_left hB2 hWnn2
    linarith only [hA2', hB2']
  linarith only [hbound, hfinal]

/-! ### Continuity, and the integral form of the angular term -/

/-- The angular swirl factor is continuous on the unit ball: it is built from the continuous
slice of `u` and from `radialQuotient (vorticityField u)`, continuous across the axis by
`continuousOn_radialQuotient_plane` applied to the smooth axisymmetric field `vorticityField u`. -/
theorem continuousOn_stretchAngularSwirl {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun x : Vec3 => stretchAngularSwirl u x t) (vec3Ball (0 : Vec3) 1) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hωaxi : IsAxisymmetricOn (vorticityField u) unitCylinder :=
    isAxisymmetricOn_vorticityField haxi hu1
  have hrepmap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) := by
    have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
      unfold meridional
      have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
      have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
      fun_prop
    exact hc.continuousOn
  have hmaps : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun x hx => rep_mem_vec3Ball hx
  have hvel : ContinuousOn (fun x : Vec3 => u (x, t) 1) (vec3Ball (0 : Vec3) 1) :=
    continuousOn_vel_slice hu 1 ht
  have hrq : ContinuousOn
      (fun x : Vec3 => radialQuotient (vorticityField u) (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) := by
    have hplane := continuousOn_radialQuotient_plane (vorticityField u) t
      (contDiffOn_vorticityField hu) hωaxi ht
    have hcompmap : ContinuousOn (fun x : Vec3 => ((polarR x, x 2) : ℝ × ℝ))
        (vec3Ball (0 : Vec3) 1) :=
      (continuous_polarR.prodMk (continuous_apply 2)).continuousOn
    exact hplane.comp' hcompmap polarRRep_mapsTo
  exact (hvel.comp' hrepmap hmaps).mul hrq

/-- **`eq:aniso:closure:angular:bound`, integrated.** Twice the product of the angular swirl
factor with `ω_θ`, integrated against `χ²` in absolute value, is bounded by a quarter of the
cutoff dissipation `M t` plus `4 W²` times the cutoff enstrophy `Y t`, whenever `χ`'s support
sits inside a ball `B(ρ) ⊆ B(1)` on which `|u_θ| ≤ W`: the radius `CIV.swirl_bound_ball`
actually delivers. -/
theorem stretchAngularTerm_integral_abs_le {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t W : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0)
    (hW : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W) :
    |∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
        * curlComp u 1 (meridional (polarR x) (x 2), t))|
      ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t + 4 * W ^ 2 * cutoffEnstrophy χ u t := by
  have hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1 := hρU.trans hρ1
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  have hLcont : ContinuousOn (fun x : Vec3 => 2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t)) (vec3Ball (0 : Vec3) 1) := by
    have hswirl := continuousOn_stretchAngularSwirl haxi hu ht
    have hrepmap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
        (vec3Ball (0 : Vec3) 1) := by
      have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
        unfold meridional
        have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
        have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
        fun_prop
      exact hc.continuousOn
    have hmaps : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
        (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun x hx => rep_mem_vec3Ball hx
    have hc1 : ContinuousOn (fun x : Vec3 => curlComp u 1 (meridional (polarR x) (x 2), t))
        (vec3Ball (0 : Vec3) 1) := (continuousOn_curl_slice hu 1 ht).comp' hrepmap hmaps
    exact (continuousOn_const.mul hswirl).mul hc1
  have hRcont : ContinuousOn (fun x : Vec3 => (1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
      + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) (vec3Ball (0 : Vec3) 1) := by
    have hM : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
        (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2) (vec3Ball (0 : Vec3) 1) :=
      continuousOn_finsetSum Finset.univ (fun i _ =>
        continuousOn_finsetSum Finset.univ (fun j _ =>
          (continuousOn_dvel_slice (contDiffOn_vorticityField hu) i j ht).pow 2))
    have hY : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)
        (vec3Ball (0 : Vec3) 1) :=
      continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i ht).pow 2)
    exact (continuousOn_const.mul hM).add (continuousOn_const.mul hY)
  have hLint : Integrable (fun x : Vec3 => χ x ^ 2 * (2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t))) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul hLcont)
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hRint : Integrable (fun x : Vec3 => χ x ^ 2 * ((1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
      + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul hRcont)
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hpt : ∀ x : Vec3, |χ x ^ 2 * (2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t))|
      ≤ χ x ^ 2 * ((1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
        + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) ρ
    · have habs := abs_two_mul_stretchAngularSwirl_mul_curlComp_one_le haxi hu hρ1 hW hxb ht
      have hsq : (0:ℝ) ≤ χ x ^ 2 := sq_nonneg _
      rw [abs_mul, abs_of_nonneg hsq]
      exact mul_le_mul_of_nonneg_left habs hsq
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hρU hm))
      rw [hχ0]; norm_num
  calc |∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
        * curlComp u 1 (meridional (polarR x) (x 2), t))|
      ≤ ∫ x : Vec3, |χ x ^ 2 * (2 * stretchAngularSwirl u x t
          * curlComp u 1 (meridional (polarR x) (x 2), t))| := abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, χ x ^ 2 * ((1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
        + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) :=
        integral_mono hLint.abs hRint hpt
    _ = (1/4) * cutoffEnstrophyDissipation χ u t + 4 * W ^ 2 * cutoffEnstrophy χ u t := by
        rw [show (fun x : Vec3 => χ x ^ 2 * ((1/4) * ∑ i : Fin 3, ∑ j : Fin 3,
              (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2
            + 4 * W ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2))
            = (fun x : Vec3 => (1/4) * (χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
                (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2)
              + (4 * W ^ 2) * (χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2))
          from by funext x; ring]
        have hM1 : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
            (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2) := by
          refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
            (continuousOn_finsetSum Finset.univ (fun i _ =>
              continuousOn_finsetSum Finset.univ (fun j _ =>
                (continuousOn_dvel_slice (contDiffOn_vorticityField hu) i j ht).pow 2))))
            (fun x hx => ?_)
          rw [image_eq_zero_of_notMem_tsupport hx]; ring
        have hY1 : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2)
          := by
          refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
            (continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i
              ht).pow 2)))
            (fun x hx => ?_)
          rw [image_eq_zero_of_notMem_tsupport hx]; ring
        rw [integral_add (hM1.const_mul _) (hY1.const_mul _), integral_const_mul,
          integral_const_mul]
        rfl

end CIV
