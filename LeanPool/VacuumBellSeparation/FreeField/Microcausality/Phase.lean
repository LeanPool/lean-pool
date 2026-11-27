/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz

/-!
# Microcausality, stages B–D: the complexified boost phase

Stages B, C and D of the microcausality proof.  Notation:
`ω = ω_m(𝐩)`, `p₁ = ⟪𝐞₁, 𝐩⟫`, `w₁ = ⟪𝐞₁, 𝐰⟫` for `w = (w⁰, 𝐰)`.

* `sub_mem_wedge_of_mem_doubleCone` (B): for `x` in the unit double cone at the origin and `y` in
  the unit double cone at `s 𝐞₁`, the difference `w = y - x` satisfies `w₁ - |w⁰| > s - 2`.
* `boostPhase m ζ 𝐩 w` (C): the complexified boost phase
  `ψ(ζ, 𝐩, w) = ω (w⁰ cosh ζ + w₁ sinh ζ) - (p₁ (w⁰ sinh ζ + w₁ cosh ζ) + ⟪𝐩, 𝐰⟫ - p₁ w₁)`;
  `boostPhase_ofReal`: for real `ζ = σ` it is the Minkowski product `⟨(ω, 𝐩), Λ(σ) w⟩`;
  `boostPhase_zero`: `ψ(0, 𝐩, w) = ω w⁰ - ⟪𝐩, 𝐰⟫`;
  `boostPhase_add_ofReal`: the shift identity `ψ(σ + ζ, 𝐩, w) = ψ(ζ, S(-σ) 𝐩, w)`
  (`S = shellBoost m`);
  `boostPhase_im`, `boostPhase_im_ge`, `boostPhase_im_nonneg`:
  `Im ψ(σ + iθ, 𝐩, w) = sin θ (ω' w₁ - p₁' w⁰) ≥ sin θ ω' (w₁ - |w⁰|)` with `(ω', 𝐩') = S(-σ)`
  applied to `𝐩`, nonnegative for `θ ∈ [0, π]` in the right wedge `|w⁰| ≤ w₁`, so
  `|exp(iψ)| ≤ 1` there (`norm_exp_I_mul_boostPhase_le_one`), and
  `|exp(iψ(σ + iθ, 𝐩, y - x))| ≤ exp(-sin θ ω' (s - 2))` for `x`, `y` in the two double cones
  (`norm_exp_I_mul_boostPhase_le_of_mem_doubleCone`);
  `axisReflection`: `𝐩 ↦ 2 p₁ 𝐞₁ - 𝐩`, i.e. `(p₁, p₂, p₃) ↦ (p₁, -p₂, -p₃)`
  (`axisReflection_apply_coord`), a linear isometry;
  `boostPhase_pi_mul_I`, `exp_I_mul_boostPhase_pi_mul_I`: `ψ(iπ, 𝐩, w) = -ψ(0, 𝐩', w)` with the
  reflected momentum `𝐩'`, so `exp(iψ(iπ, 𝐩, w)) = conj exp(iψ(0, 𝐩', w))`.
* `boostPhaseIntegral m F G 𝐩 ζ` (B): `Φ(𝐩, ζ) = ∫∫ exp(iψ(ζ, 𝐩, y - x)) F(x) G(y) dx dy` (over
  the product measure), whose integrand is integrable (`integrable_boostPhaseIntegrand`);
  `conj_oneParticle_mul_oneParticle`: `conj(κF(𝐩)) κG(𝐩) = Φ(𝐩, 0)`;
  `oneParticleInner_eq_integral_boostPhaseIntegral`: `⟨κF, κG⟩ = ∫ Φ(𝐩, 0) dν(𝐩)`.
* `integral_boostPhaseIntegral_add_ofReal` (D): `∫ Φ(𝐩, σ + ζ) dν = ∫ Φ(𝐩, ζ) dν` for real `σ`,
  every complex `ζ` and `m ≠ 0` (the shift identity and the boost invariance of `dν`); the
  instance `ζ = iθ` is `integral_boostPhaseIntegral_add_mul_I`.
* The boundary value at `iπ` (an ingredient of stage G): `boostPhaseIntegral_pi_mul_I`:
  `Φ(𝐩, iπ) = conj Φ(𝐩', 0)`; `integral_boostPhaseIntegral_pi_mul_I`:
  `∫ Φ(𝐩, iπ) dν = conj ⟨κF, κG⟩`; `im_oneParticleInner_eq_zero_of_boundary_eq`: if
  `∫ Φ(𝐩, 0) dν = ∫ Φ(𝐩, iπ) dν` (the content of stages E and F), then `Im ⟨κF, κG⟩ = 0`.

Here `dν(𝐩) = d³p / (2(2π)³ ω_m(𝐩))` is the weight of `oneParticleInner`.  Holomorphy and decay
are proved in `Microcausality/Strip.lean`, `Microcausality/Decay.lean` and
`Microcausality/Edges.lean` (stages E and F).
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-! ### B. The wedge geometry of two separated unit double cones -/

/-- For `x` in the unit double cone at the origin and `y` in the unit double cone at `s 𝐞₁`, the
difference `w = y - x` lies in the right wedge with margin `s - 2`: `⟪𝐞₁, 𝐰⟫ - |w⁰| > s - 2`. -/
theorem sub_mem_wedge_of_mem_doubleCone {s : ℝ} {x y : Spacetime} (hx : x ∈ doubleCone 0 1)
    (hy : y ∈ doubleCone (0, s • e₁) 1) :
    s - 2 < ⟪e₁, (y - x).2⟫_ℝ - |(y - x).1| := by
  have hx' : |x.1 - 0| + ‖x.2 - 0‖ < 1 := hx
  have hy' : |y.1 - 0| + ‖y.2 - s • e₁‖ < 1 := hy
  simp only [sub_zero] at hx' hy'
  have h1 : ⟪e₁, (y - x).2⟫_ℝ = ⟪e₁, y.2 - s • e₁⟫_ℝ + s - ⟪e₁, x.2⟫_ℝ := by
    rw [Prod.snd_sub, inner_sub_right, inner_sub_right, real_inner_smul_right, inner_e₁_self]
    ring
  have h2 : |(y - x).1| ≤ |y.1| + |x.1| := by
    rw [Prod.fst_sub, abs_le]
    constructor <;> linarith [le_abs_self y.1, neg_abs_le y.1, le_abs_self x.1, neg_abs_le x.1]
  have h3 : -‖y.2 - s • e₁‖ ≤ ⟪e₁, y.2 - s • e₁⟫_ℝ := by
    have := abs_inner_e₁_le (y.2 - s • e₁)
    linarith [neg_abs_le ⟪e₁, y.2 - s • e₁⟫_ℝ]
  have h4 : ⟪e₁, x.2⟫_ℝ ≤ ‖x.2‖ := by
    have := abs_inner_e₁_le x.2
    linarith [le_abs_self ⟪e₁, x.2⟫_ℝ]
  linarith

/-- For `s ≥ 2` the difference of points of the two unit double cones lies in the closed right
wedge `|w⁰| ≤ ⟪𝐞₁, 𝐰⟫`. -/
theorem abs_fst_sub_le_of_mem_doubleCone {s : ℝ} (hs : 2 ≤ s) {x y : Spacetime}
    (hx : x ∈ doubleCone 0 1) (hy : y ∈ doubleCone (0, s • e₁) 1) :
    |(y - x).1| ≤ ⟪e₁, (y - x).2⟫_ℝ := by
  have h := sub_mem_wedge_of_mem_doubleCone hx hy
  linarith

/-! ### C. The complexified boost phase -/

/-- The complexified boost phase `ψ_m(ζ, 𝐩, w)` for a complex rapidity `ζ`:
`ω (w⁰ cosh ζ + w₁ sinh ζ) - (p₁ (w⁰ sinh ζ + w₁ cosh ζ) + ⟪𝐩, 𝐰⟫ - p₁ w₁)` with `ω = ω_m(𝐩)`,
`p₁ = ⟪𝐞₁, 𝐩⟫`, `w₁ = ⟪𝐞₁, 𝐰⟫`.  For real `ζ = σ` it is `⟨(ω, 𝐩), Λ(σ) w⟩`
(`boostPhase_ofReal`). -/
noncomputable def boostPhase (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) : ℂ :=
  (dispersion m p : ℂ) * ((w.1 : ℂ) * Complex.cosh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.sinh ζ) -
    ((⟪e₁, p⟫_ℝ : ℂ) * ((w.1 : ℂ) * Complex.sinh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.cosh ζ) +
      (⟪p, w.2⟫_ℝ : ℂ) - (⟪e₁, p⟫_ℝ : ℂ) * (⟪e₁, w.2⟫_ℝ : ℂ))

/-- At `ζ = 0` the phase is the plane-wave phase `ω w⁰ - ⟪𝐩, 𝐰⟫`. -/
theorem boostPhase_zero (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m 0 p w = ((dispersion m p * w.1 - ⟪p, w.2⟫_ℝ : ℝ) : ℂ) := by
  unfold boostPhase
  rw [Complex.cosh_zero, Complex.sinh_zero]
  push_cast
  ring

/-- The Minkowski product `⟨(ω, 𝐩), Λ(σ) w⟩` in coordinates. -/
theorem minkowskiForm_onShell_boost (m σ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    minkowskiForm (onShell m p) (boost σ w) =
      dispersion m p * (w.1 * Real.cosh σ + ⟪e₁, w.2⟫_ℝ * Real.sinh σ) -
        (⟪e₁, p⟫_ℝ * (w.1 * Real.sinh σ + ⟪e₁, w.2⟫_ℝ * Real.cosh σ) + ⟪p, w.2⟫_ℝ -
          ⟪e₁, p⟫_ℝ * ⟪e₁, w.2⟫_ℝ) := by
  obtain ⟨w0, wv⟩ := w
  simp only [minkowskiForm, onShell, boost_apply, boostCLM_apply]
  rw [inner_add_right, real_inner_smul_right, real_inner_comm p e₁]
  ring

/-- For real rapidity `σ` the phase is the Minkowski product of the on-shell momentum with the
boosted point: `ψ(σ, 𝐩, w) = ⟨(ω_m(𝐩), 𝐩), Λ(σ) w⟩`. -/
theorem boostPhase_ofReal (m σ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m (σ : ℂ) p w = ((minkowskiForm (onShell m p) (boost σ w) : ℝ) : ℂ) := by
  rw [minkowskiForm_onShell_boost]
  unfold boostPhase
  push_cast
  ring

/-- **The shift identity**: a real shift of the rapidity is a boost of the momentum,
`ψ(σ + ζ, 𝐩, w) = ψ(ζ, S(-σ) 𝐩, w)` for real `σ` and complex `ζ`, `S = shellBoost m`. -/
theorem boostPhase_add_ofReal (m σ : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m ((σ : ℂ) + ζ) p w = boostPhase m ζ (shellBoost m (-σ) p) w := by
  have hω : dispersion m (shellBoost m (-σ) p) =
      Real.cosh σ * dispersion m p - Real.sinh σ * ⟪e₁, p⟫_ℝ := by
    rw [dispersion_shellBoost, Real.cosh_neg, Real.sinh_neg]
    ring
  have h1 : ⟪e₁, shellBoost m (-σ) p⟫_ℝ =
      Real.cosh σ * ⟪e₁, p⟫_ℝ - Real.sinh σ * dispersion m p := by
    rw [shellBoost, inner_e₁_add_smul, Real.cosh_neg, Real.sinh_neg]
    ring
  have h2 : ⟪shellBoost m (-σ) p, w.2⟫_ℝ = ⟪p, w.2⟫_ℝ +
      (-Real.sinh σ * dispersion m p + (Real.cosh σ - 1) * ⟪e₁, p⟫_ℝ) * ⟪e₁, w.2⟫_ℝ := by
    rw [shellBoost, inner_add_left, real_inner_smul_left, Real.cosh_neg, Real.sinh_neg]
  unfold boostPhase
  rw [hω, h1, h2, Complex.cosh_add, Complex.sinh_add]
  push_cast
  ring

/-- The shift identity on the line `Im ζ = θ`: `ψ(σ + iθ, 𝐩, w) = ψ(iθ, S(-σ) 𝐩, w)`. -/
theorem boostPhase_add_mul_I (m σ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p w =
      boostPhase m ((θ : ℂ) * Complex.I) (shellBoost m (-σ) p) w :=
  boostPhase_add_ofReal m σ _ p w

/-- For real rapidity, `ψ(σ, 𝐩, w) = ψ(0, S(-σ) 𝐩, w)`. -/
theorem boostPhase_ofReal_eq_zero_shellBoost (m σ : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (w : Spacetime) :
    boostPhase m (σ : ℂ) p w = boostPhase m 0 (shellBoost m (-σ) p) w := by
  have h := boostPhase_add_ofReal m σ 0 p w
  rwa [add_zero] at h

/-- The phase on the imaginary axis, split into real and imaginary parts:
`ψ(iθ, 𝐪, w) = ((ω w⁰ - q₁ w₁) cos θ - ⟪𝐪, 𝐰⟫ + q₁ w₁) + i sin θ (ω w₁ - q₁ w⁰)`. -/
theorem boostPhase_ofReal_mul_I (m θ : ℝ) (q : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m ((θ : ℂ) * Complex.I) q w =
      (((dispersion m q * w.1 - ⟪e₁, q⟫_ℝ * ⟪e₁, w.2⟫_ℝ) * Real.cos θ - ⟪q, w.2⟫_ℝ +
          ⟪e₁, q⟫_ℝ * ⟪e₁, w.2⟫_ℝ : ℝ) : ℂ) +
        ((Real.sin θ * (dispersion m q * ⟪e₁, w.2⟫_ℝ - ⟪e₁, q⟫_ℝ * w.1) : ℝ) : ℂ) *
          Complex.I := by
  unfold boostPhase
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

/-- `Im ψ(iθ, 𝐪, w) = sin θ (ω_m(𝐪) w₁ - q₁ w⁰)`. -/
theorem boostPhase_ofReal_mul_I_im (m θ : ℝ) (q : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    (boostPhase m ((θ : ℂ) * Complex.I) q w).im =
      Real.sin θ * (dispersion m q * ⟪e₁, w.2⟫_ℝ - ⟪e₁, q⟫_ℝ * w.1) := by
  rw [boostPhase_ofReal_mul_I, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul,
    Complex.I_im, mul_one, zero_add]

/-- `Re ψ(iθ, 𝐪, w) = (ω_m(𝐪) w⁰ - q₁ w₁) cos θ - ⟪𝐪, 𝐰⟫ + q₁ w₁`. -/
theorem boostPhase_ofReal_mul_I_re (m θ : ℝ) (q : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    (boostPhase m ((θ : ℂ) * Complex.I) q w).re =
      (dispersion m q * w.1 - ⟪e₁, q⟫_ℝ * ⟪e₁, w.2⟫_ℝ) * Real.cos θ - ⟪q, w.2⟫_ℝ +
        ⟪e₁, q⟫_ℝ * ⟪e₁, w.2⟫_ℝ := by
  rw [boostPhase_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    Complex.I_re, mul_zero, add_zero]

/-- **The imaginary part of the phase** in the strip: `Im ψ(σ + iθ, 𝐩, w) = sin θ (ω' w₁ - p₁' w⁰)`
with `𝐩' = S(-σ) 𝐩`, `ω' = ω_m(𝐩')`, `p₁' = ⟪𝐞₁, 𝐩'⟫` the boosted energy and momentum. -/
theorem boostPhase_im (m σ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    (boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p w).im =
      Real.sin θ * (dispersion m (shellBoost m (-σ) p) * ⟪e₁, w.2⟫_ℝ -
        ⟪e₁, shellBoost m (-σ) p⟫_ℝ * w.1) := by
  rw [boostPhase_add_ofReal, boostPhase_ofReal_mul_I_im]

/-- Lower bound of the imaginary part for `θ ∈ [0, π]`:
`Im ψ(σ + iθ, 𝐩, w) ≥ sin θ · ω' · (w₁ - |w⁰|)`, `ω' = ω_m(S(-σ) 𝐩)`. -/
theorem boostPhase_im_ge (m σ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime)
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Real.sin θ * (dispersion m (shellBoost m (-σ) p) * (⟪e₁, w.2⟫_ℝ - |w.1|)) ≤
      (boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p w).im := by
  rw [boostPhase_im]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ hθπ)
  have hq : |⟪e₁, shellBoost m (-σ) p⟫_ℝ| ≤ dispersion m (shellBoost m (-σ) p) :=
    (abs_inner_e₁_le _).trans (norm_le_dispersion m _)
  have h1 : ⟪e₁, shellBoost m (-σ) p⟫_ℝ * w.1 ≤ dispersion m (shellBoost m (-σ) p) * |w.1| :=
    calc ⟪e₁, shellBoost m (-σ) p⟫_ℝ * w.1 ≤ |⟪e₁, shellBoost m (-σ) p⟫_ℝ * w.1| :=
          le_abs_self _
      _ = |⟪e₁, shellBoost m (-σ) p⟫_ℝ| * |w.1| := abs_mul _ _
      _ ≤ dispersion m (shellBoost m (-σ) p) * |w.1| :=
          mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  rw [mul_sub]
  linarith

/-- **Positivity of the imaginary part**: for `θ ∈ [0, π]` and `w` in the closed right wedge
`|w⁰| ≤ w₁`, `Im ψ(σ + iθ, 𝐩, w) ≥ 0`. -/
theorem boostPhase_im_nonneg (m σ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime)
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hw : |w.1| ≤ ⟪e₁, w.2⟫_ℝ) :
    0 ≤ (boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p w).im := by
  refine le_trans ?_ (boostPhase_im_ge m σ θ p w hθ₀ hθπ)
  have hω : 0 ≤ dispersion m (shellBoost m (-σ) p) := Real.sqrt_nonneg _
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ hθπ)
    (mul_nonneg hω (sub_nonneg.mpr hw))

/-- `|exp(iψ(σ + iθ, 𝐩, w))| ≤ 1` for `θ ∈ [0, π]` and `w` in the closed right wedge. -/
theorem norm_exp_I_mul_boostPhase_le_one (m σ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (w : Spacetime) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hw : |w.1| ≤ ⟪e₁, w.2⟫_ℝ) :
    ‖Complex.exp (Complex.I * boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p w)‖ ≤ 1 := by
  rw [Complex.norm_exp, Complex.I_mul_re, Real.exp_le_one_iff, neg_nonpos]
  exact boostPhase_im_nonneg m σ θ p w hθ₀ hθπ hw

/-- Exponential decay on the supports: for `x` in the unit double cone at the origin, `y` in the
unit double cone at `s 𝐞₁` and `θ ∈ [0, π]`,
`|exp(iψ(σ + iθ, 𝐩, y - x))| ≤ exp(-sin θ · ω' · (s - 2))` with `ω' = ω_m(S(-σ) 𝐩)`. -/
theorem norm_exp_I_mul_boostPhase_le_of_mem_doubleCone (m σ θ s : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) {x y : Spacetime} (hx : x ∈ doubleCone 0 1)
    (hy : y ∈ doubleCone (0, s • e₁) 1) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ‖Complex.exp (Complex.I * boostPhase m ((σ : ℂ) + (θ : ℂ) * Complex.I) p (y - x))‖ ≤
      Real.exp (-(Real.sin θ * (dispersion m (shellBoost m (-σ) p) * (s - 2)))) := by
  rw [Complex.norm_exp, Complex.I_mul_re, Real.exp_le_exp, neg_le_neg_iff]
  refine le_trans ?_ (boostPhase_im_ge m σ θ p (y - x) hθ₀ hθπ)
  have hw := sub_mem_wedge_of_mem_doubleCone hx hy
  have hω : 0 ≤ dispersion m (shellBoost m (-σ) p) := Real.sqrt_nonneg _
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ hθπ
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw.le hω) hsin

/-! ### The rotation by `π` about the `𝐞₁` axis -/

/-- `R(R𝐩) = 𝐩` for `R𝐩 = 2 p₁ 𝐞₁ - 𝐩`. -/
theorem axisReflection_aux_involutive (p : EuclideanSpace ℝ (Fin 3)) :
    (2 * ⟪e₁, (2 * ⟪e₁, p⟫_ℝ) • e₁ - p⟫_ℝ) • e₁ - ((2 * ⟪e₁, p⟫_ℝ) • e₁ - p) = p := by
  rw [inner_sub_right, real_inner_smul_right, inner_e₁_self,
    show 2 * (2 * ⟪e₁, p⟫_ℝ * 1 - ⟪e₁, p⟫_ℝ) = 2 * ⟪e₁, p⟫_ℝ by ring]
  exact sub_sub_cancel _ _

/-- `|2 p₁ 𝐞₁ - 𝐩| = |𝐩|`. -/
theorem axisReflection_aux_norm (p : EuclideanSpace ℝ (Fin 3)) :
    ‖(2 * ⟪e₁, p⟫_ℝ) • e₁ - p‖ = ‖p‖ := by
  have h : ‖(2 * ⟪e₁, p⟫_ℝ) • e₁ - p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs, norm_e₁, mul_one,
      sq_abs]
    ring
  rw [← Real.sqrt_sq (norm_nonneg ((2 * ⟪e₁, p⟫_ℝ) • e₁ - p)), h, Real.sqrt_sq (norm_nonneg p)]

/-- The rotation by `π` about the `𝐞₁` axis, `𝐩 ↦ 2 p₁ 𝐞₁ - 𝐩`, that is
`(p₁, p₂, p₃) ↦ (p₁, -p₂, -p₃)`, as a linear isometry of `ℝ³` (it is its own inverse). -/
noncomputable def axisReflection : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun p := (2 * ⟪e₁, p⟫_ℝ) • e₁ - p
  map_add' p q := by
    change (2 * ⟪e₁, p + q⟫_ℝ) • e₁ - (p + q) =
      ((2 * ⟪e₁, p⟫_ℝ) • e₁ - p) + ((2 * ⟪e₁, q⟫_ℝ) • e₁ - q)
    rw [inner_add_right, mul_add, add_smul]
    abel
  map_smul' c p := by
    change (2 * ⟪e₁, c • p⟫_ℝ) • e₁ - c • p = c • ((2 * ⟪e₁, p⟫_ℝ) • e₁ - p)
    rw [real_inner_smul_right, smul_sub, smul_smul, mul_left_comm]
  invFun p := (2 * ⟪e₁, p⟫_ℝ) • e₁ - p
  left_inv p := axisReflection_aux_involutive p
  right_inv p := axisReflection_aux_involutive p
  norm_map' p := axisReflection_aux_norm p

/-- `R𝐩 = 2 p₁ 𝐞₁ - 𝐩`. -/
theorem axisReflection_apply (p : EuclideanSpace ℝ (Fin 3)) :
    axisReflection p = (2 * ⟪e₁, p⟫_ℝ) • e₁ - p :=
  rfl

/-- `⟪𝐞₁, R𝐩⟫ = ⟪𝐞₁, 𝐩⟫`. -/
theorem inner_e₁_axisReflection (p : EuclideanSpace ℝ (Fin 3)) :
    ⟪e₁, axisReflection p⟫_ℝ = ⟪e₁, p⟫_ℝ := by
  rw [axisReflection_apply, inner_sub_right, real_inner_smul_right, inner_e₁_self]
  ring

/-- `⟪R𝐩, 𝐯⟫ = 2 p₁ v₁ - ⟪𝐩, 𝐯⟫`. -/
theorem inner_axisReflection_left (p v : EuclideanSpace ℝ (Fin 3)) :
    ⟪axisReflection p, v⟫_ℝ = 2 * ⟪e₁, p⟫_ℝ * ⟪e₁, v⟫_ℝ - ⟪p, v⟫_ℝ := by
  rw [axisReflection_apply, inner_sub_left, real_inner_smul_left]

/-- In coordinates (index `0` is the `𝐞₁` direction), `R(p₁, p₂, p₃) = (p₁, -p₂, -p₃)`. -/
theorem axisReflection_apply_coord (p : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    axisReflection p i = if i = 0 then p i else -p i := by
  have h1 : ⟪e₁, p⟫_ℝ = p 0 := by
    rw [real_inner_comm]
    exact inner_euclideanSingle_one p 0
  have he : e₁ i = if i = 0 then 1 else 0 := by
    simp [e₁]
  rw [axisReflection_apply, PiLp.sub_apply, PiLp.smul_apply, h1, he, smul_eq_mul]
  split_ifs with hi
  · subst hi
    ring
  · ring

/-- **The phase at `ζ = iπ`**: `ψ(iπ, 𝐩, w) = -ψ(0, R𝐩, w)` with the reflected momentum
`R𝐩 = (p₁, -p₂, -p₃)`. -/
theorem boostPhase_pi_mul_I (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhase m ((Real.pi : ℂ) * Complex.I) p w = -boostPhase m 0 (axisReflection p) w := by
  unfold boostPhase
  rw [dispersion_linearIsometryEquiv, inner_e₁_axisReflection, inner_axisReflection_left,
    Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi, Complex.cosh_zero,
    Complex.sinh_zero]
  push_cast
  ring

/-- `exp(iψ(iπ, 𝐩, w)) = conj exp(iψ(0, R𝐩, w))`. -/
theorem exp_I_mul_boostPhase_pi_mul_I (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    Complex.exp (Complex.I * boostPhase m ((Real.pi : ℂ) * Complex.I) p w) =
      conj (Complex.exp (Complex.I * boostPhase m 0 (axisReflection p) w)) := by
  rw [boostPhase_pi_mul_I, boostPhase_zero, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  congr 1
  ring

/-! ### B. The one-particle inner product as a double integral -/

/-- `Φ_m(F, G; 𝐩, ζ) = ∫∫ exp(iψ_m(ζ, 𝐩, y - x)) F(x) G(y) dx dy`, an integral over the product
measure on `Spacetime × Spacetime`. -/
noncomputable def boostPhaseIntegral (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) : ℂ :=
  ∫ z : Spacetime × Spacetime, Complex.exp (Complex.I * boostPhase m ζ p (z.2 - z.1)) *
    ((F.1 z.1 : ℝ) : ℂ) * ((G.1 z.2 : ℝ) : ℂ) ∂((volume : Measure Spacetime).prod volume)

/-- The phase `w ↦ ψ(ζ, 𝐩, w)` is continuous. -/
theorem continuous_boostPhase (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun w : Spacetime => boostPhase m ζ p w := by
  have h1 : Continuous fun w : Spacetime => ((w.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  have h2 : Continuous fun w : Spacetime => ((⟪e₁, w.2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner continuous_snd)
  have h3 : Continuous fun w : Spacetime => ((⟪p, w.2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner continuous_snd)
  unfold boostPhase
  exact (continuous_const.mul ((h1.mul continuous_const).add (h2.mul continuous_const))).sub
    (((continuous_const.mul ((h1.mul continuous_const).add (h2.mul continuous_const))).add
      h3).sub (continuous_const.mul h2))

/-- The integrand of `Φ(𝐩, ζ)` is integrable for the product measure (it is continuous and
vanishes outside `tsupport F × tsupport G`). -/
theorem integrable_boostPhaseIntegrand (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) :
    Integrable (fun z : Spacetime × Spacetime =>
      Complex.exp (Complex.I * boostPhase m ζ p (z.2 - z.1)) * ((F.1 z.1 : ℝ) : ℂ) *
        ((G.1 z.2 : ℝ) : ℂ)) ((volume : Measure Spacetime).prod volume) := by
  have hc : Continuous fun z : Spacetime × Spacetime =>
      Complex.exp (Complex.I * boostPhase m ζ p (z.2 - z.1)) * ((F.1 z.1 : ℝ) : ℂ) *
        ((G.1 z.2 : ℝ) : ℂ) :=
    ((Complex.continuous_exp.comp (continuous_const.mul
      ((continuous_boostPhase m ζ p).comp (continuous_snd.sub continuous_fst)))).mul
      (Complex.continuous_ofReal.comp ((continuous_testFunction F).comp continuous_fst))).mul
      (Complex.continuous_ofReal.comp ((continuous_testFunction G).comp continuous_snd))
  have hs : HasCompactSupport fun z : Spacetime × Spacetime =>
      Complex.exp (Complex.I * boostPhase m ζ p (z.2 - z.1)) * ((F.1 z.1 : ℝ) : ℂ) *
        ((G.1 z.2 : ℝ) : ℂ) := by
    refine HasCompactSupport.intro (IsCompact.prod F.2.2 G.2.2) fun z hz => ?_
    rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have : (volume : Measure Spacetime).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : IsFiniteMeasureOnCompacts ((volume : Measure Spacetime).prod
    (volume : Measure Spacetime)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  exact hc.integrable_of_hasCompactSupport hs

/-- Pointwise form of `conj(κF) κG = Φ(·, 0)`:
`conj(e^{i(ω x⁰ - ⟪𝐩, 𝐱⟫)} F(x)) e^{i(ω y⁰ - ⟪𝐩, 𝐲⟫)} G(y) = e^{iψ(0, 𝐩, y - x)} F(x) G(y)`. -/
theorem conj_oneParticleIntegrand_mul (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (x y : Spacetime) :
    conj (oneParticleIntegrand m F p x) * oneParticleIntegrand m G p y =
      Complex.exp (Complex.I * boostPhase m 0 p (y - x)) * ((F.1 x : ℝ) : ℂ) *
        ((G.1 y : ℝ) : ℂ) := by
  have hphase : Complex.I * boostPhase m 0 p (y - x) =
      conj (Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ)) +
        Complex.I * ((dispersion m p * y.1 - ⟪p, y.2⟫_ℝ : ℝ) : ℂ) := by
    rw [boostPhase_zero, map_mul, Complex.conj_I, Complex.conj_ofReal, Prod.fst_sub,
      Prod.snd_sub, inner_sub_right]
    push_cast
    ring
  rw [hphase, Complex.exp_add, Complex.exp_conj]
  simp only [oneParticleIntegrand, map_mul, Complex.conj_ofReal]
  ring

/-- **`conj(κ_m F(𝐩)) κ_m G(𝐩) = Φ(𝐩, 0)`** (product of two integrals as an integral over the
product measure; no integrability hypothesis is needed). -/
theorem conj_oneParticle_mul_oneParticle (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    conj (oneParticle m F p) * oneParticle m G p = boostPhaseIntegral m F G p 0 := by
  rw [oneParticle_eq_integral, oneParticle_eq_integral, ← integral_conj, ← integral_prod_mul]
  unfold boostPhaseIntegral
  exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
    conj_oneParticleIntegrand_mul m F G p z.1 z.2)

/-- **The one-particle inner product as an integral of `Φ`**:
`⟨κ_m F, κ_m G⟩ = ∫ Φ(𝐩, 0) d³p / (2(2π)³ ω_m(𝐩))`. -/
theorem oneParticleInner_eq_integral_boostPhaseIntegral (m : ℝ) (F G : RealTestFunction) :
    oneParticleInner m F G = ∫ p, boostPhaseIntegral m F G p 0 *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  unfold oneParticleInner
  congr 1
  funext p
  rw [conj_oneParticle_mul_oneParticle]

/-! ### D. Independence of the real part of the rapidity -/

/-- The shift identity for `Φ`: `Φ(𝐩, σ + ζ) = Φ(S(-σ) 𝐩, ζ)` for real `σ`. -/
theorem boostPhaseIntegral_add_ofReal (m σ : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) :
    boostPhaseIntegral m F G p ((σ : ℂ) + ζ) =
      boostPhaseIntegral m F G (shellBoost m (-σ) p) ζ := by
  unfold boostPhaseIntegral
  simp only [boostPhase_add_ofReal]

/-- **`∫ Φ(𝐩, ζ) dν(𝐩)` does not depend on `Re ζ`**: for `m ≠ 0`, real `σ` and complex `ζ`,
`∫ Φ(𝐩, σ + ζ) dν = ∫ Φ(𝐩, ζ) dν` (the shift identity and the boost invariance of
`dν = d³p / (2(2π)³ ω_m(𝐩))`; no integrability hypothesis is needed). -/
theorem integral_boostPhaseIntegral_add_ofReal {m : ℝ} (hm : m ≠ 0) (σ : ℝ)
    (F G : RealTestFunction) (ζ : ℂ) :
    ∫ p, boostPhaseIntegral m F G p ((σ : ℂ) + ζ) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p ζ *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  simp only [boostPhaseIntegral_add_ofReal]
  exact integral_shellBoost_mul_weight hm (-σ) (fun q => boostPhaseIntegral m F G q ζ)

/-- The constancy on the line `Im ζ = θ`: `∫ Φ(𝐩, σ + iθ) dν = ∫ Φ(𝐩, iθ) dν` (`m ≠ 0`). -/
theorem integral_boostPhaseIntegral_add_mul_I {m : ℝ} (hm : m ≠ 0) (σ θ : ℝ)
    (F G : RealTestFunction) :
    ∫ p, boostPhaseIntegral m F G p ((σ : ℂ) + (θ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) :=
  integral_boostPhaseIntegral_add_ofReal hm σ F G _

/-! ### The boundary value at `ζ = iπ` -/

/-- `Φ(𝐩, iπ) = conj Φ(R𝐩, 0)` (`F`, `G` are real). -/
theorem boostPhaseIntegral_pi_mul_I (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    boostPhaseIntegral m F G p ((Real.pi : ℂ) * Complex.I) =
      conj (boostPhaseIntegral m F G (axisReflection p) 0) := by
  unfold boostPhaseIntegral
  rw [← integral_conj]
  congr 1
  funext z
  rw [exp_I_mul_boostPhase_pi_mul_I]
  simp only [map_mul, Complex.conj_ofReal]

/-- **The boundary value at `iπ` is the conjugate inner product**:
`∫ Φ(𝐩, iπ) dν(𝐩) = conj ⟨κ_m F, κ_m G⟩` (the reflection `𝐩 ↦ R𝐩` preserves `dν`). -/
theorem integral_boostPhaseIntegral_pi_mul_I (m : ℝ) (F G : RealTestFunction) :
    ∫ p, boostPhaseIntegral m F G p ((Real.pi : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      conj (oneParticleInner m F G) := by
  rw [oneParticleInner_eq_integral_boostPhaseIntegral, ← integral_conj]
  simp only [boostPhaseIntegral_pi_mul_I, map_mul, Complex.conj_ofReal]
  have h := axisReflection.measurePreserving.integral_comp
    axisReflection.toHomeomorph.measurableEmbedding
    (fun q => conj (boostPhaseIntegral m F G q 0) *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q) : ℝ) : ℂ))
  simp only [dispersion_linearIsometryEquiv] at h
  exact h

/-- **The last step of stage G**: if the boundary values on the two edges of the strip agree,
`∫ Φ(𝐩, 0) dν = ∫ Φ(𝐩, iπ) dν`, then `⟨κ_m F, κ_m G⟩` is real. -/
theorem im_oneParticleInner_eq_zero_of_boundary_eq (m : ℝ) (F G : RealTestFunction)
    (h : ∫ p, boostPhaseIntegral m F G p 0 *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p ((Real.pi : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) :
    (oneParticleInner m F G).im = 0 := by
  rw [← oneParticleInner_eq_integral_boostPhaseIntegral, integral_boostPhaseIntegral_pi_mul_I] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end VacuumBellSeparation
