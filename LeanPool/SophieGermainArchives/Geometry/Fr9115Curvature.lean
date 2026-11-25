/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

/-!
# Français 9115: the curvature of surfaces

Adapted from `lean/Germain/Fr9115Curvature.lean` of
https://github.com/Commutator-IO/germain-project
at commit `167c171` (CC0, same author).

The modernised reading `transcripts/fr-9115/fr-9115.modern.tex` reads, in views 3–41, the
« Exposition des principes qui servent de base à la théorie des surfaces élastiques », in
views 43–89 the « Mémoire sur la courbure des surfaces », in view 114 a computation on three
neighbouring normal sections, and in view 650 the « Somme des raisons inverses des deux rayons
de principale courbure » for a sphere. This file proves the statements on normal curvature
those sections make, in current notation: `κ(φ) = κ₁ cos² φ + κ₂ sin² φ` (Euler's formula),
`H = (κ₁ + κ₂)/2`.

* Euler's theorem on normal sections from the second fundamental form `r, s, t` of a surface
  whose tangent plane is horizontal (`euler_principal`), and the irregularity formulas of the
  Exposition, N° 4 (`kq_perp_diff`, `kq_complement_diff`).
* The distribution law of the memoir, N° 3: the sum on perpendicular sections
  (`kappa_add_perp`), `κ(φ) = H + ((κ₁ - κ₂)/2) cos 2φ` (`kappa_harmonic`,
  `amplitude_sq`), the section at 45° (`kappa_pi_div_four`), the antisymmetry about it
  (`kappa_quarter_symm`), when a section has the mean curvature (`kappa_eq_mean_iff`).
* The mean over all directions (memoir, Nos. 5–6): `∫₀^{2π} κ = 2π H` (`integral_kappa`) and
  the equal extent of the « surface des distances » and the « surface des distances
  moyennes » (`distance_surface`); the « ligne de distance » `ρ(1 - cos(s/ρ)) ≈ s²/(2ρ)`
  (`sinus_verse`).
* View 114, three neighbouring sections: the three equations (`three_sections_one`,
  `three_sections_two`, `three_sections_three`), the comparison of the two decreases
  (`decrease_compare`), the rate of change, largest at 45° (`hasDerivAt_kappa`,
  `abs_deriv_kappa_le`), and the counterexample to the leaf's statement on radii
  (`radii_counterexample`).
* View 650: the formula for `1/R + 1/R'` gives `-2/ρ` on the sphere `z = √(ρ² - x² - y²)`
  (`sphere_sum`, with the partial derivatives `sphere_p` … `sphere_t`).

Not formalised: Meusnier's theorem and the geometry of oblique sections, the developments of
the surfaces on a plane, the variational computation of view 483, the comparison with
Fourier's ring, the « Idées à vérifier » on the catenary.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Fr9115Curvature

open Real

/-- Euler's formula: the curvature of the normal section at angle `φ` from the first
principal direction. -/
noncomputable def kappa (k₁ k₂ φ : ℝ) : ℝ := k₁ * cos φ ^ 2 + k₂ * sin φ ^ 2

/-- The normal curvature in direction `A` for a surface `z = ½(r x² + 2 s x y + t y²) + …`
with horizontal tangent plane. -/
noncomputable def kq (r s t A : ℝ) : ℝ := r * cos A ^ 2 + 2 * s * sin A * cos A + t * sin A ^ 2

/-- **Euler's theorem on normal sections.** For every second fundamental form `(r, s, t)`
there are principal curvatures `κ₂ ≤ κ₁` and a principal angle `θ₀` with
`kq(A) = κ₁ cos²(A - θ₀) + κ₂ sin²(A - θ₀)`, `κ₁ + κ₂ = r + t`, `κ₁ κ₂ = r t - s²`. -/
theorem euler_principal (r s t : ℝ) :
    ∃ θ₀ κ₁ κ₂ : ℝ, κ₁ + κ₂ = r + t ∧ κ₁ * κ₂ = r * t - s ^ 2 ∧ κ₂ ≤ κ₁ ∧
      ∀ A, kq r s t A = κ₁ * cos (A - θ₀) ^ 2 + κ₂ * sin (A - θ₀) ^ 2 := by
  set z : ℂ := ⟨(r - t) / 2, s⟩
  set R := ‖z‖
  set φ := Complex.arg z
  have hc : R * cos φ = (r - t) / 2 := Complex.norm_mul_cos_arg z
  have hs : R * sin φ = s := Complex.norm_mul_sin_arg z
  have hR : 0 ≤ R := norm_nonneg z
  refine ⟨φ / 2, (r + t) / 2 + R, (r + t) / 2 - R, by ring, ?_, by linarith, fun A => ?_⟩
  · linear_combination (-(R * cos φ + (r - t) / 2)) * hc - (R * sin φ + s) * hs +
      R ^ 2 * sin_sq_add_cos_sq φ
  · have e4 : cos (2 * (A - φ / 2)) = cos (2 * A) * cos φ + sin (2 * A) * sin φ := by
      rw [show 2 * (A - φ / 2) = 2 * A - φ by ring, cos_sub]
    simp only [kq]
    linear_combination t * sin_sq_add_cos_sq A - ((r + t) / 2 - R) * sin_sq_add_cos_sq (A - φ / 2) +
      R * cos_two_mul (A - φ / 2) - R * e4 - cos (2 * A) * hc - sin (2 * A) * hs -
      (r - t) / 2 * cos_two_mul A - s * sin_two_mul A

/-- Exposition, N° 4: the difference of curvatures of two perpendicular normal sections. -/
theorem kq_perp_diff (r s t A : ℝ) :
    kq r s t A - kq r s t (A + π / 2) = (r - t) * cos (2 * A) + 2 * s * sin (2 * A) := by
  simp only [kq, cos_add_pi_div_two, sin_add_pi_div_two]
  linear_combination (-(r - t)) * sin_sq_add_cos_sq A - (r - t) * cos_two_mul A -
    2 * s * sin_two_mul A

/-- … and for the complementary pair, at angle `π/2 - A`; the sum of the two differences is
`4 s sin 2A`, zero on principal axes (`s = 0`). -/
theorem kq_complement_diff (r s t A : ℝ) :
    kq r s t (π / 2 - A) - kq r s t (π - A) = -(r - t) * cos (2 * A) + 2 * s * sin (2 * A) := by
  simp only [kq, cos_pi_div_two_sub, sin_pi_div_two_sub, cos_pi_sub, sin_pi_sub]
  linear_combination (r - t) * sin_sq_add_cos_sq A + (r - t) * cos_two_mul A -
    2 * s * sin_two_mul A

/-- Memoir, N° 3, first proposition: two perpendicular normal sections have the constant sum
of curvatures `κ₁ + κ₂`. -/
theorem kappa_add_perp (k₁ k₂ φ : ℝ) : kappa k₁ k₂ φ + kappa k₁ k₂ (φ + π / 2) = k₁ + k₂ := by
  simp only [kappa, cos_add_pi_div_two, sin_add_pi_div_two]
  linear_combination (k₁ + k₂) * sin_sq_add_cos_sq φ

/-- The distribution law: a mean value plus a single harmonic of order 2. -/
theorem kappa_harmonic (k₁ k₂ φ : ℝ) :
    kappa k₁ k₂ φ = (k₁ + k₂) / 2 + (k₁ - k₂) / 2 * cos (2 * φ) := by
  simp only [kappa]
  linear_combination k₂ * sin_sq_add_cos_sq φ - (k₁ - k₂) / 2 * cos_two_mul φ

/-- The amplitude of the anisotropic part: `((κ₁ - κ₂)/2)² = H² - K`. -/
theorem amplitude_sq (k₁ k₂ : ℝ) : ((k₁ - k₂) / 2) ^ 2 = ((k₁ + k₂) / 2) ^ 2 - k₁ * k₂ := by
  ring

/-- Second proposition (and the note of the Exposition): the section at 45° of the
principal planes has the mean curvature. -/
theorem kappa_pi_div_four (k₁ k₂ : ℝ) : kappa k₁ k₂ (π / 4) = (k₁ + k₂) / 2 := by
  rw [kappa_harmonic, show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two]; ring

/-- The excess on one side of the 45° section balances the defect on the other. -/
theorem kappa_quarter_symm (k₁ k₂ u : ℝ) :
    kappa k₁ k₂ (π / 4 + u) + kappa k₁ k₂ (π / 4 - u) = k₁ + k₂ := by
  rw [kappa_harmonic, kappa_harmonic, show 2 * (π / 4 + u) = 2 * u + π / 2 by ring,
    show 2 * (π / 4 - u) = π / 2 - 2 * u by ring, cos_add_pi_div_two, cos_pi_div_two_sub]
  ring

/-- Off the umbilics, a normal section has the mean curvature exactly at the two 45°
directions (« Idées à vérifier », view 137). -/
theorem kappa_eq_mean_iff {k₁ k₂ : ℝ} (h : k₁ ≠ k₂) (φ : ℝ) :
    kappa k₁ k₂ φ = (k₁ + k₂) / 2 ↔ cos (2 * φ) = 0 := by
  rw [kappa_harmonic]
  have h' : (k₁ - k₂) / 2 ≠ 0 := by
    intro h0; apply h; linarith
  constructor
  · intro h1
    have : (k₁ - k₂) / 2 * cos (2 * φ) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left h'
  · intro h1; rw [h1]; ring

/-- Third proposition: `κ(φ) = κ(-φ) = κ(π - φ)`. -/
theorem kappa_symm (k₁ k₂ φ : ℝ) :
    kappa k₁ k₂ (-φ) = kappa k₁ k₂ φ ∧ kappa k₁ k₂ (π - φ) = kappa k₁ k₂ φ := by
  constructor <;> simp only [kappa, cos_neg, sin_neg, cos_pi_sub, sin_pi_sub, neg_sq]

/-- Memoir, Nos. 5–6: the mean of the normal curvature over all directions is `H`. -/
theorem integral_kappa (k₁ k₂ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), kappa k₁ k₂ φ = 2 * π * ((k₁ + k₂) / 2) := by
  simp only [kappa]
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun φ => k₁ * cos φ ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun φ => k₂ * sin φ ^ 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_sq, integral_sin_sq]
  simp only [sin_two_pi, sin_zero]
  ring

/-- The surface of distances (lines of distance `½ κ(φ) s²` over the circle of radius `s`)
has the extent of the cylinder of height `½ H s²`. -/
theorem distance_surface (k₁ k₂ s : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), 1 / 2 * kappa k₁ k₂ φ * s ^ 2 * s =
      2 * π * s * (1 / 2 * ((k₁ + k₂) / 2) * s ^ 2) := by
  have : ∀ φ, 1 / 2 * kappa k₁ k₂ φ * s ^ 2 * s = s ^ 3 / 2 * kappa k₁ k₂ φ := fun φ => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_kappa]
  ring

/-- Memoir, N° 4: the line of distance (versed sine) of an arc of angle `x` on a circle of
radius `ρ` is `ρ x²/2` up to `(5/96) ρ x⁴`; with `s = ρ x`, `ρ x²/2 = s²/(2ρ)`. -/
theorem sinus_verse (ρ x : ℝ) (hρ : 0 ≤ ρ) (hx : |x| ≤ 1) :
    |ρ * (1 - cos x) - ρ * x ^ 2 / 2| ≤ 5 / 96 * ρ * |x| ^ 4 := by
  have hb := cos_bound hx
  have e : ρ * (1 - cos x) - ρ * x ^ 2 / 2 = -(ρ * (cos x - (1 - x ^ 2 / 2))) := by ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg hρ]
  calc ρ * |cos x - (1 - x ^ 2 / 2)| ≤ ρ * (|x| ^ 4 * (5 / 96)) :=
        mul_le_mul_of_nonneg_left hb hρ
    _ = 5 / 96 * ρ * |x| ^ 4 := by ring

/-! ## View 114: three neighbouring normal sections -/

/-- Equation (1): the decrease from `A` to `A + a`. -/
theorem three_sections_one (k₁ k₂ A a : ℝ) :
    kappa k₁ k₂ A - kappa k₁ k₂ (A + a) = (k₁ - k₂) * sin a * sin (2 * A + a) := by
  rw [kappa_harmonic, kappa_harmonic]
  have h1 : cos (2 * A) = cos ((2 * A + a) - a) := by ring_nf
  have h2 : cos (2 * (A + a)) = cos ((2 * A + a) + a) := by ring_nf
  rw [h1, h2, cos_sub (2 * A + a) a, cos_add (2 * A + a) a]
  ring

/-- Equation (2): the decrease from `A - a` to `A`. -/
theorem three_sections_two (k₁ k₂ A a : ℝ) :
    kappa k₁ k₂ (A - a) - kappa k₁ k₂ A = (k₁ - k₂) * sin a * sin (2 * A - a) := by
  rw [kappa_harmonic, kappa_harmonic]
  have h1 : cos (2 * (A - a)) = cos ((2 * A - a) - a) := by ring_nf
  have h2 : cos (2 * A) = cos ((2 * A - a) + a) := by ring_nf
  rw [h1, h2, cos_sub (2 * A - a) a, cos_add (2 * A - a) a]
  ring

/-- Equation (3): the second difference; it vanishes for the sphere, for `a = 0` or `π`, and
for `A = 45°`. -/
theorem three_sections_three (k₁ k₂ A a : ℝ) :
    kappa k₁ k₂ (A - a) + kappa k₁ k₂ (A + a) - 2 * kappa k₁ k₂ A =
      -2 * (k₁ - k₂) * sin a ^ 2 * cos (2 * A) := by
  rw [kappa_harmonic, kappa_harmonic, kappa_harmonic,
    show 2 * (A - a) = 2 * A - 2 * a by ring, show 2 * (A + a) = 2 * A + 2 * a by ring,
    cos_sub (2 * A) (2 * a), cos_add (2 * A) (2 * a)]
  have hc : cos (2 * a) = 1 - 2 * sin a ^ 2 := by
    rw [cos_two_mul]; linear_combination 2 * sin_sq_add_cos_sq a
  linear_combination (k₁ - k₂) * cos (2 * A) * hc

/-- The comparison of (1) and (2): between the plane of greatest curvature and 45°, the
decrease from `A - a` to `A` is smaller than from `A` to `A + a`. -/
theorem decrease_compare {k₁ k₂ A a : ℝ} (hk : k₂ < k₁) (hA0 : 0 ≤ A) (hA1 : A < π / 4)
    (ha : sin a ≠ 0) :
    kappa k₁ k₂ (A - a) - kappa k₁ k₂ A < kappa k₁ k₂ A - kappa k₁ k₂ (A + a) := by
  have h3 := three_sections_three k₁ k₂ A a
  have hcos : 0 < cos (2 * A) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hsin : 0 < sin a ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha))
  have : 0 < (k₁ - k₂) * sin a ^ 2 * cos (2 * A) :=
    mul_pos (mul_pos (by linarith) hsin) hcos
  linarith

theorem hasDerivAt_kappa (k₁ k₂ θ : ℝ) :
    HasDerivAt (kappa k₁ k₂) (-(k₁ - k₂) * sin (2 * θ)) θ := by
  have e : kappa k₁ k₂ = fun x => k₁ * (cos x * cos x) + k₂ * (sin x * sin x) := by
    funext x; simp only [kappa]; ring
  rw [e]
  exact ((((hasDerivAt_cos θ).mul (hasDerivAt_cos θ)).const_mul k₁).add
    (((hasDerivAt_sin θ).mul (hasDerivAt_sin θ)).const_mul k₂)).congr_deriv
    (by rw [sin_two_mul]; ring)

/-- The curvature changes fastest at the 45° section, and not at all on the principal
directions: `|κ'(θ)| ≤ |κ₁ - κ₂| = |κ'(π/4)|`. -/
theorem abs_deriv_kappa_le (k₁ k₂ θ : ℝ) :
    |deriv (kappa k₁ k₂) θ| ≤ |deriv (kappa k₁ k₂) (π / 4)| := by
  rw [(hasDerivAt_kappa k₁ k₂ θ).deriv, (hasDerivAt_kappa k₁ k₂ (π / 4)).deriv,
    show 2 * (π / 4) = π / 2 by ring, sin_pi_div_two, abs_mul, abs_mul, abs_one, mul_one]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)

/-- The leaf's conclusion read on the radii is false: for `0 < κ₂ < κ₁`, the two 45° sections
have radii whose sum is not the sum of the principal radii. -/
theorem radii_counterexample {k₁ k₂ : ℝ} (h2 : 0 < k₂) (h12 : k₂ < k₁) :
    1 / kappa k₁ k₂ (π / 4) + 1 / kappa k₁ k₂ (π / 4) ≠ 1 / k₁ + 1 / k₂ := by
  rw [kappa_pi_div_four]
  intro h
  have h1 : 0 < k₁ := by linarith
  have hS : 0 < k₁ + k₂ := by linarith
  have hH : (k₁ + k₂) / 2 ≠ 0 := by positivity
  rw [div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ hH hH,
    div_eq_div_iff (mul_ne_zero hH hH) (mul_ne_zero h1.ne' h2.ne')] at h
  nlinarith [mul_pos hS (pow_pos (sub_pos.mpr h12) 2)]

/-! ## View 650: the sum of curvatures on the sphere -/

/-- The upper hemisphere `z = √(ρ² - x² - y²)`. -/
noncomputable def sphZ (ρ x y : ℝ) : ℝ := √(ρ ^ 2 - x ^ 2 - y ^ 2)

private theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem sphere_p {ρ x y : ℝ} (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    HasDerivAt (fun x => sphZ ρ x y) (-x / sphZ ρ x y) x := by
  have hf : HasDerivAt (fun x => ρ ^ 2 - x ^ 2 - y ^ 2) (-(2 * x)) x :=
    ((hasDerivAt_sq' x).const_sub (ρ ^ 2)).sub_const (y ^ 2)
  exact (hf.sqrt hD.ne').congr_deriv (by simp only [sphZ]; ring)

theorem sphere_q {ρ x y : ℝ} (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    HasDerivAt (fun y => sphZ ρ x y) (-y / sphZ ρ x y) y := by
  have hf : HasDerivAt (fun y => ρ ^ 2 - x ^ 2 - y ^ 2) (-(2 * y)) y :=
    (hasDerivAt_sq' y).const_sub (ρ ^ 2 - x ^ 2)
  exact (hf.sqrt hD.ne').congr_deriv (by simp only [sphZ]; ring)

theorem sphere_r {ρ x y : ℝ} (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    HasDerivAt (fun x => -x / sphZ ρ x y) (-(ρ ^ 2 - y ^ 2) / sphZ ρ x y ^ 3) x := by
  have hZ : 0 < sphZ ρ x y := sqrt_pos.mpr hD
  have hZ2 : sphZ ρ x y ^ 2 = ρ ^ 2 - x ^ 2 - y ^ 2 := sq_sqrt hD.le
  have hZu := mul_inv_cancel₀ hZ.ne'
  exact ((hasDerivAt_id' x).neg.div (sphere_p hD) hZ.ne').congr_deriv
    (by simp only [Pi.neg_apply]
        linear_combination (sphZ ρ x y * (sphZ ρ x y)⁻¹ ^ 2) * hZu - (sphZ ρ x y)⁻¹ ^ 3 * hZ2)

theorem sphere_s {ρ x y : ℝ} (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    HasDerivAt (fun y => -x / sphZ ρ x y) (-(x * y) / sphZ ρ x y ^ 3) y := by
  have hZ : 0 < sphZ ρ x y := sqrt_pos.mpr hD
  exact ((hasDerivAt_const y (-x)).div (sphere_q hD) hZ.ne').congr_deriv (by ring)

theorem sphere_t {ρ x y : ℝ} (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    HasDerivAt (fun y => -y / sphZ ρ x y) (-(ρ ^ 2 - x ^ 2) / sphZ ρ x y ^ 3) y := by
  have hZ : 0 < sphZ ρ x y := sqrt_pos.mpr hD
  have hZ2 : sphZ ρ x y ^ 2 = ρ ^ 2 - x ^ 2 - y ^ 2 := sq_sqrt hD.le
  have hZu := mul_inv_cancel₀ hZ.ne'
  exact ((hasDerivAt_id' y).neg.div (sphere_q hD) hZ.ne').congr_deriv
    (by simp only [Pi.neg_apply]
        linear_combination (sphZ ρ x y * (sphZ ρ x y)⁻¹ ^ 2) * hZu - (sphZ ρ x y)⁻¹ ^ 3 * hZ2)

/-- **View 650.** With `p, q, r, s, t` the partial derivatives of `z = √(ρ² - x² - y²)`
(`sphere_p` … `sphere_t`), the formula
`((1 + q²) r - 2pqs + (1 + p²) t) / (1 + p² + q²)^{3/2}` gives `-2/ρ`, twice the curvature
`1/ρ` with the sign of the downward normal. -/
theorem sphere_sum {ρ x y : ℝ} (hρ : 0 < ρ) (hD : 0 < ρ ^ 2 - x ^ 2 - y ^ 2) :
    ((1 + (-y / sphZ ρ x y) ^ 2) * (-(ρ ^ 2 - y ^ 2) / sphZ ρ x y ^ 3) -
        2 * (-x / sphZ ρ x y) * (-y / sphZ ρ x y) * (-(x * y) / sphZ ρ x y ^ 3) +
        (1 + (-x / sphZ ρ x y) ^ 2) * (-(ρ ^ 2 - x ^ 2) / sphZ ρ x y ^ 3)) /
      √(1 + (-x / sphZ ρ x y) ^ 2 + (-y / sphZ ρ x y) ^ 2) ^ 3 = -2 / ρ := by
  have hZ : 0 < sphZ ρ x y := sqrt_pos.mpr hD
  have hZ2 : sphZ ρ x y ^ 2 = ρ ^ 2 - x ^ 2 - y ^ 2 := sq_sqrt hD.le
  have hu : (ρ ^ 2 - x ^ 2 - y ^ 2) * (sphZ ρ x y)⁻¹ ^ 2 = 1 := by
    rw [← hZ2, ← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
  have h1 : 1 + (-x / sphZ ρ x y) ^ 2 + (-y / sphZ ρ x y) ^ 2 = (ρ * (sphZ ρ x y)⁻¹) ^ 2 := by
    linear_combination (-1 : ℝ) * hu
  have hN : (1 + (-y / sphZ ρ x y) ^ 2) * (-(ρ ^ 2 - y ^ 2) / sphZ ρ x y ^ 3) -
      2 * (-x / sphZ ρ x y) * (-y / sphZ ρ x y) * (-(x * y) / sphZ ρ x y ^ 3) +
      (1 + (-x / sphZ ρ x y) ^ 2) * (-(ρ ^ 2 - x ^ 2) / sphZ ρ x y ^ 3) =
      -2 * ρ ^ 2 * (sphZ ρ x y)⁻¹ ^ 3 := by
    linear_combination (-((sphZ ρ x y)⁻¹ ^ 3) * (x ^ 2 + y ^ 2)) * hu
  have hpos : 0 < ρ * (sphZ ρ x y)⁻¹ := mul_pos hρ (inv_pos.mpr hZ)
  rw [hN, h1, sqrt_sq hpos.le, div_eq_div_iff (pow_ne_zero 3 hpos.ne') hρ.ne']
  ring

end LeanPool.SophieGermainArchives.Fr9115Curvature
