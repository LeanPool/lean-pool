/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Phase
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Microcausality, stage E: holomorphy and constancy on the open strip

Stage E of the microcausality proof.  Notation as in
`FreeField/Microcausality/Phase.lean`: `ψ = boostPhase m`, `Φ = boostPhaseIntegral m F G`,
`dν(𝐩) = d³p / (2(2π)³ ω_m(𝐩))`.

* `boostPhaseDeriv`, `hasDerivAt_boostPhase`: `ζ ↦ ψ(ζ, 𝐩, w)` is entire with derivative
  `ω (w⁰ sinh ζ + w₁ cosh ζ) - p₁ (w⁰ cosh ζ + w₁ sinh ζ)`; `norm_boostPhaseDeriv_le`:
  `|∂_ζ ψ| ≤ 2 ω (|w⁰| + |w₁|) M` if `|cosh ζ|, |sinh ζ| ≤ M`.
* `exp_neg_abs_mul_dispersion_le`: `e^{-|σ|} ω_m(𝐩) ≤ ω_m(S(-σ) 𝐩)`;
  `norm_exp_I_mul_boostPhase_le_exp`: for `0 ≤ Im ζ ≤ π` and `x`, `y` in the two double cones,
  `|exp(iψ(ζ, 𝐩, y - x))| ≤ exp(-κ (s - 2) ω_m(𝐩))` whenever `κ ≤ sin(Im ζ) e^{-|Re ζ|}`.
* `integrable_exp_neg_mul_dispersion`, `integrable_stripMajorant`: for `c > 0` the majorant
  `(𝐩, x, y) ↦ e^{-c ω_m(𝐩)} |F(x)| |G(y)|` is integrable on `ℝ³ × (Spacetime × Spacetime)`.
* `stripIntegral m F G ζ = ∫ Φ(𝐩, ζ) dν(𝐩)`; `stripIntegrand`, `stripIntegrandDeriv`: its
  integrand on `ℝ³ × (Spacetime × Spacetime)` and the `ζ`-derivative of that integrand, with the
  bounds `norm_stripIntegrand_le`, `norm_stripIntegrandDeriv_le` (the factor `ω` of `∂_ζ ψ` is
  cancelled by the weight `1 / ω`); `integrable_stripIntegrand`,
  `stripIntegral_eq_integral_prod` (Fubini) for `0 < Im ζ < π`.

Main results, for `m > 0`, `s > 2`, `tsupport F ⊆ doubleCone 0 1`,
`tsupport G ⊆ doubleCone (0, s 𝐞₁) 1`:

* `hasDerivAt_stripIntegral`, `differentiableAt_stripIntegral`: `ζ ↦ ∫ Φ(𝐩, ζ) dν(𝐩)` is complex
  differentiable at every `ζ` with `0 < Im ζ < π` (differentiation under the integral sign,
  dominated by `C e^{-c ω_m(𝐩)} |F(x)| |G(y)|` on a neighbourhood of `ζ`);
* `deriv_stripIntegral_eq_zero`: its derivative vanishes there (it equals the derivative in the
  real direction, and `stripIntegral_add_ofReal`, i.e. stage D, says the function is constant in
  `Re ζ`);
* `stripIntegral_eq_of_mem_strip`: it is constant on the open strip;
  `integral_boostPhaseIntegral_mul_I_eq`, `integral_boostPhaseIntegral_eq_on_strip`: the same on
  the imaginary axis, `∫ Φ(𝐩, iθ) dν = ∫ Φ(𝐩, iπ/2) dν` for `θ ∈ (0, π)`;
* `im_oneParticleInner_eq_zero_of_continuousOn`: if moreover `θ ↦ ∫ Φ(𝐩, iθ) dν` is continuous on
  `[0, π]` (stage F, proved in `Microcausality/Edges.lean`), then `Im ⟨κ_m F, κ_m G⟩ = 0`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Topology
open MeasureTheory Filter

namespace VacuumBellSeparation

/-! ### The derivative of the phase in the rapidity -/

/-- The complex derivative of the boost phase in the rapidity,
`∂_ζ ψ_m(ζ, 𝐩, w) = ω (w⁰ sinh ζ + w₁ cosh ζ) - p₁ (w⁰ cosh ζ + w₁ sinh ζ)` with `ω = ω_m(𝐩)`,
`p₁ = ⟪𝐞₁, 𝐩⟫`, `w₁ = ⟪𝐞₁, 𝐰⟫` (`hasDerivAt_boostPhase`). -/
noncomputable def boostPhaseDeriv (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3))
    (w : Spacetime) : ℂ :=
  (dispersion m p : ℂ) * ((w.1 : ℂ) * Complex.sinh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.cosh ζ) -
    (⟪e₁, p⟫_ℝ : ℂ) * ((w.1 : ℂ) * Complex.cosh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.sinh ζ)

/-- `ζ ↦ ψ_m(ζ, 𝐩, w)` is entire, with derivative `boostPhaseDeriv m ζ 𝐩 w`. -/
theorem hasDerivAt_boostPhase (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) (ζ : ℂ) :
    HasDerivAt (fun ζ => boostPhase m ζ p w) (boostPhaseDeriv m ζ p w) ζ := by
  have hc := Complex.hasDerivAt_cosh ζ
  have hs := Complex.hasDerivAt_sinh ζ
  have h1 := (hc.const_mul (w.1 : ℂ)).add (hs.const_mul (⟪e₁, w.2⟫_ℝ : ℂ))
  have h2 := (hs.const_mul (w.1 : ℂ)).add (hc.const_mul (⟪e₁, w.2⟫_ℝ : ℂ))
  have h3 := (h1.const_mul (dispersion m p : ℂ)).sub
    (((h2.const_mul (⟪e₁, p⟫_ℝ : ℂ)).add_const (⟪p, w.2⟫_ℝ : ℂ)).sub_const
      ((⟪e₁, p⟫_ℝ : ℂ) * (⟪e₁, w.2⟫_ℝ : ℂ)))
  exact h3

/-- Joint continuity of the phase in the momentum and the spacetime point. -/
theorem continuous_boostPhase_comp {α : Type*} [TopologicalSpace α] (m : ℝ) (ζ : ℂ)
    {f : α → EuclideanSpace ℝ (Fin 3)} {g : α → Spacetime} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => boostPhase m ζ (f a) (g a) := by
  have h1 : Continuous fun a => (((g a).1 : ℝ) : ℂ) := Complex.continuous_ofReal.comp hg.fst
  have h2 : Continuous fun a => ((⟪e₁, (g a).2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner hg.snd)
  have h3 : Continuous fun a => ((⟪f a, (g a).2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.inner hg.snd)
  have h4 : Continuous fun a => ((dispersion m (f a) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_dispersion m).comp hf)
  have h5 : Continuous fun a => ((⟪e₁, f a⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner hf)
  unfold boostPhase
  exact (h4.mul ((h1.mul continuous_const).add (h2.mul continuous_const))).sub
    (((h5.mul ((h1.mul continuous_const).add (h2.mul continuous_const))).add h3).sub (h5.mul h2))

/-- Joint continuity of the derivative of the phase in the momentum and the spacetime point. -/
theorem continuous_boostPhaseDeriv_comp {α : Type*} [TopologicalSpace α] (m : ℝ) (ζ : ℂ)
    {f : α → EuclideanSpace ℝ (Fin 3)} {g : α → Spacetime} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => boostPhaseDeriv m ζ (f a) (g a) := by
  have h1 : Continuous fun a => (((g a).1 : ℝ) : ℂ) := Complex.continuous_ofReal.comp hg.fst
  have h2 : Continuous fun a => ((⟪e₁, (g a).2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner hg.snd)
  have h4 : Continuous fun a => ((dispersion m (f a) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_dispersion m).comp hf)
  have h5 : Continuous fun a => ((⟪e₁, f a⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner hf)
  unfold boostPhaseDeriv
  exact (h4.mul ((h1.mul continuous_const).add (h2.mul continuous_const))).sub
    (h5.mul ((h1.mul continuous_const).add (h2.mul continuous_const)))

/-- `|∂_ζ ψ_m(ζ, 𝐩, w)| ≤ 2 ω_m(𝐩) (|w⁰| + |w₁|) M` whenever `|cosh ζ| ≤ M` and `|sinh ζ| ≤ M`. -/
theorem norm_boostPhaseDeriv_le (m : ℝ) {ζ : ℂ} {M : ℝ} (hc : ‖Complex.cosh ζ‖ ≤ M)
    (hs : ‖Complex.sinh ζ‖ ≤ M) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    ‖boostPhaseDeriv m ζ p w‖ ≤ 2 * dispersion m p * (|w.1| + |⟪e₁, w.2⟫_ℝ|) * M := by
  have hω : 0 ≤ dispersion m p := Real.sqrt_nonneg _
  have hp : |⟪e₁, p⟫_ℝ| ≤ dispersion m p := (abs_inner_e₁_le p).trans (norm_le_dispersion m p)
  have hA : ∀ a b : ℂ, ‖a‖ ≤ M → ‖b‖ ≤ M →
      ‖(w.1 : ℂ) * a + (⟪e₁, w.2⟫_ℝ : ℂ) * b‖ ≤ (|w.1| + |⟪e₁, w.2⟫_ℝ|) * M := by
    intro a b ha hb
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
  have h1 := hA _ _ hs hc
  have h2 := hA _ _ hc hs
  unfold boostPhaseDeriv
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hω]
  calc dispersion m p * ‖(w.1 : ℂ) * Complex.sinh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.cosh ζ‖ +
        |⟪e₁, p⟫_ℝ| * ‖(w.1 : ℂ) * Complex.cosh ζ + (⟪e₁, w.2⟫_ℝ : ℂ) * Complex.sinh ζ‖
      ≤ dispersion m p * ((|w.1| + |⟪e₁, w.2⟫_ℝ|) * M) +
        dispersion m p * ((|w.1| + |⟪e₁, w.2⟫_ℝ|) * M) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hω) (mul_le_mul hp h2 (norm_nonneg _) hω)
    _ = 2 * dispersion m p * (|w.1| + |⟪e₁, w.2⟫_ℝ|) * M := by ring

/-! ### Bounds on the supports -/

/-- For `x` in the unit double cone at the origin and `y` in the unit double cone at `s 𝐞₁`
(`s ≥ 0`), the difference `w = y - x` satisfies `|w⁰| + |w₁| ≤ s + 2`. -/
theorem abs_fst_add_abs_inner_le_of_mem_doubleCone {s : ℝ} (hs : 0 ≤ s) {x y : Spacetime}
    (hx : x ∈ doubleCone 0 1) (hy : y ∈ doubleCone (0, s • e₁) 1) :
    |(y - x).1| + |⟪e₁, (y - x).2⟫_ℝ| ≤ s + 2 := by
  have hx' : |x.1 - 0| + ‖x.2 - 0‖ < 1 := hx
  have hy' : |y.1 - 0| + ‖y.2 - s • e₁‖ < 1 := hy
  simp only [sub_zero] at hx' hy'
  have h1 : |(y - x).1| ≤ |y.1| + |x.1| := by
    rw [Prod.fst_sub, abs_le]
    constructor <;> linarith [le_abs_self y.1, neg_abs_le y.1, le_abs_self x.1, neg_abs_le x.1]
  have hs1 : ‖s • e₁‖ = s := by
    rw [norm_smul, norm_e₁, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]
  have h2 : ‖(y - x).2‖ ≤ ‖y.2 - s • e₁‖ + s + ‖x.2‖ := by
    calc ‖(y - x).2‖ = ‖(y.2 - s • e₁) + s • e₁ - x.2‖ := by rw [Prod.snd_sub, sub_add_cancel]
      _ ≤ ‖(y.2 - s • e₁) + s • e₁‖ + ‖x.2‖ := norm_sub_le _ _
      _ ≤ ‖y.2 - s • e₁‖ + ‖s • e₁‖ + ‖x.2‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = ‖y.2 - s • e₁‖ + s + ‖x.2‖ := by rw [hs1]
  have h3 := abs_inner_e₁_le (y - x).2
  linarith [abs_nonneg x.1, abs_nonneg y.1]

/-- The boosted energy is bounded below: `e^{-|σ|} ω_m(𝐩) ≤ ω_m(S(-σ) 𝐩)`. -/
theorem exp_neg_abs_mul_dispersion_le (m σ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    Real.exp (-|σ|) * dispersion m p ≤ dispersion m (shellBoost m (-σ) p) := by
  rw [dispersion_shellBoost, Real.cosh_neg, Real.sinh_neg]
  have hp : |⟪e₁, p⟫_ℝ| ≤ dispersion m p := (abs_inner_e₁_le p).trans (norm_le_dispersion m p)
  have hp1 : ⟪e₁, p⟫_ℝ ≤ dispersion m p := (le_abs_self _).trans hp
  have hp2 : -dispersion m p ≤ ⟪e₁, p⟫_ℝ := by linarith [neg_abs_le ⟪e₁, p⟫_ℝ]
  rcases le_or_gt 0 σ with hσ | hσ
  · rw [abs_of_nonneg hσ, ← Real.cosh_sub_sinh]
    have hsh : 0 ≤ Real.sinh σ := Real.sinh_nonneg_iff.mpr hσ
    nlinarith [mul_le_mul_of_nonneg_left hp1 hsh]
  · rw [abs_of_neg hσ, neg_neg, ← Real.cosh_add_sinh]
    have hsh : Real.sinh σ < 0 := Real.sinh_neg_iff.mpr hσ
    nlinarith [mul_le_mul_of_nonneg_left hp2 (neg_nonneg.mpr hsh.le)]

/-- Decay on the supports with an explicit rate: for `0 ≤ Im ζ ≤ π`, `s ≥ 2`,
`κ ≤ sin(Im ζ) e^{-|Re ζ|}`, `x` in the unit double cone at the origin and `y` in the one at
`s 𝐞₁`, `|exp(iψ(ζ, 𝐩, y - x))| ≤ exp(-κ (s - 2) ω_m(𝐩))`. -/
theorem norm_exp_I_mul_boostPhase_le_exp {m s κ : ℝ} (hs : 2 ≤ s) {ζ : ℂ} (h0 : 0 ≤ ζ.im)
    (hπ : ζ.im ≤ Real.pi) (hκ : κ ≤ Real.sin ζ.im * Real.exp (-|ζ.re|))
    (p : EuclideanSpace ℝ (Fin 3)) {x y : Spacetime} (hx : x ∈ doubleCone 0 1)
    (hy : y ∈ doubleCone (0, s • e₁) 1) :
    ‖Complex.exp (Complex.I * boostPhase m ζ p (y - x))‖ ≤
      Real.exp (-(κ * (s - 2) * dispersion m p)) := by
  have h := norm_exp_I_mul_boostPhase_le_of_mem_doubleCone m ζ.re ζ.im s p hx hy h0 hπ
  rw [Complex.re_add_im] at h
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hω' := exp_neg_abs_mul_dispersion_le m ζ.re p
  have hsin : 0 ≤ Real.sin ζ.im := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
  have hω : 0 ≤ dispersion m p := Real.sqrt_nonneg _
  have hs2 : 0 ≤ s - 2 := by linarith
  calc κ * (s - 2) * dispersion m p
      ≤ Real.sin ζ.im * Real.exp (-|ζ.re|) * (s - 2) * dispersion m p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hs2) hω
    _ = Real.sin ζ.im * (Real.exp (-|ζ.re|) * dispersion m p * (s - 2)) := by ring
    _ ≤ Real.sin ζ.im * (dispersion m (shellBoost m (-ζ.re) p) * (s - 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hω' hs2) hsin

/-- A pointwise bound needs to be checked only on the supports of `F` and `G`:
if `A ≤ B` whenever `x ∈ U` and `y ∈ V`, then `A |F(x)| |G(y)| ≤ B |F(x)| |G(y)|`. -/
theorem mul_abs_mul_abs_le_of_tsupport {F G : RealTestFunction} {U V : Set Spacetime}
    (hF : tsupport F.1 ⊆ U) (hG : tsupport G.1 ⊆ V) {A B : ℝ} {x y : Spacetime}
    (h : x ∈ U → y ∈ V → A ≤ B) : A * (|F.1 x| * |G.1 y|) ≤ B * (|F.1 x| * |G.1 y|) := by
  by_cases hx : x ∈ tsupport F.1
  · by_cases hy : y ∈ tsupport G.1
    · exact mul_le_mul_of_nonneg_right (h (hF hx) (hG hy))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### Integrability of the majorant -/

/-- `1 ≤ 2 (2π)³`. -/
theorem one_le_two_mul_two_pi_pow_three : (1 : ℝ) ≤ 2 * (2 * Real.pi) ^ 3 := by
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h := one_le_pow₀ (n := 3) h2pi
  linarith

/-- `e^{-ct} ≤ 24 e^c c⁻⁴ (1 + t)⁻⁴` for `c > 0` and `t ≥ 0`. -/
theorem exp_neg_mul_le_one_add_rpow {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(c * t)) ≤ 24 * Real.exp c / c ^ 4 * (1 + t) ^ (-(4 : ℝ)) := by
  have h1 : 0 < 1 + t := by linarith
  have hc0 : c ≠ 0 := hc.ne'
  have ht0 : 1 + t ≠ 0 := h1.ne'
  have hx : 0 ≤ c * (1 + t) := by positivity
  have h := Real.pow_div_factorial_le_exp (c * (1 + t)) hx 4
  have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  have hpos : 0 < (c * (1 + t)) ^ 4 / 24 := by positivity
  have h2 : (Real.exp (c * (1 + t)))⁻¹ ≤ ((c * (1 + t)) ^ 4 / 24)⁻¹ := inv_anti₀ hpos h
  have h3 : Real.exp (-(c * t)) = Real.exp c * (Real.exp (c * (1 + t)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h4 : (1 + t) ^ (-(4 : ℝ)) = ((1 + t) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    congr 1
    exact Real.rpow_ofNat (1 + t) 4
  have h5 : Real.exp c * ((c * (1 + t)) ^ 4 / 24)⁻¹ =
      24 * Real.exp c / c ^ 4 * ((1 + t) ^ 4)⁻¹ := by
    field_simp
  rw [h3, h4, ← h5]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le

/-- For `c > 0`, `𝐩 ↦ e^{-c ω_m(𝐩)}` is integrable on `ℝ³`. -/
theorem integrable_exp_neg_mul_dispersion (m : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-(c * dispersion m p))) := by
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine (hint.const_mul (24 * Real.exp c / c ^ 4)).mono'
    (Real.continuous_exp.comp ((continuous_const.mul
      (continuous_dispersion m)).neg)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(c * dispersion m p)) ≤ Real.exp (-(c * ‖p‖)) :=
        Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (norm_le_dispersion m p) hc.le))
    _ ≤ 24 * Real.exp c / c ^ 4 * (1 + ‖p‖) ^ (-(4 : ℝ)) :=
        exp_neg_mul_le_one_add_rpow hc (norm_nonneg p)

/-- `(x, y) ↦ |F(x)| |G(y)|` is integrable on `Spacetime × Spacetime`. -/
theorem integrable_abs_mul_abs_testFunction (F G : RealTestFunction) :
    Integrable (fun z : Spacetime × Spacetime => |F.1 z.1| * |G.1 z.2|)
      ((volume : Measure Spacetime).prod volume) :=
  ((continuous_testFunction F).integrable_of_hasCompactSupport F.2.2).abs.mul_prod
    ((continuous_testFunction G).integrable_of_hasCompactSupport G.2.2).abs

/-- For `c > 0` the majorant `(𝐩, x, y) ↦ e^{-c ω_m(𝐩)} |F(x)| |G(y)|` is integrable on
`ℝ³ × (Spacetime × Spacetime)`. -/
theorem integrable_stripMajorant (m : ℝ) {c : ℝ} (hc : 0 < c) (F G : RealTestFunction) :
    Integrable (fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      Real.exp (-(c * dispersion m q.1)) * (|F.1 q.2.1| * |G.1 q.2.2|))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure Spacetime).prod volume)) :=
  (integrable_exp_neg_mul_dispersion m hc).mul_prod (integrable_abs_mul_abs_testFunction F G)

/-! ### The integrand on `ℝ³ × (Spacetime × Spacetime)` and its derivative -/

/-- The integrand `(𝐩, x, y) ↦ e^{iψ_m(ζ, 𝐩, y - x)} F(x) G(y) / (2(2π)³ ω_m(𝐩))` of
`∫ Φ(𝐩, ζ) dν(𝐩)` on `ℝ³ × (Spacetime × Spacetime)` (`stripIntegral_eq_integral_prod`). -/
noncomputable def stripIntegrand (m : ℝ) (F G : RealTestFunction) (ζ : ℂ)
    (q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime)) : ℂ :=
  Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1)) * ((F.1 q.2.1 : ℝ) : ℂ) *
    ((G.1 q.2.2 : ℝ) : ℂ) * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) : ℝ) : ℂ)

/-- The `ζ`-derivative of `stripIntegrand` (`hasDerivAt_stripIntegrand`):
`(𝐩, x, y) ↦ e^{iψ} (i ∂_ζ ψ) F(x) G(y) / (2(2π)³ ω_m(𝐩))` with `ψ = ψ_m(ζ, 𝐩, y - x)`. -/
noncomputable def stripIntegrandDeriv (m : ℝ) (F G : RealTestFunction) (ζ : ℂ)
    (q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime)) : ℂ :=
  Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1)) *
      (Complex.I * boostPhaseDeriv m ζ q.1 (q.2.2 - q.2.1)) * ((F.1 q.2.1 : ℝ) : ℂ) *
    ((G.1 q.2.2 : ℝ) : ℂ) * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) : ℝ) : ℂ)

/-- `G(ζ) = ∫ Φ(𝐩, ζ) dν(𝐩)` with `dν = d³p / (2(2π)³ ω_m(𝐩))`, the function of the complex
rapidity `ζ` that is holomorphic (`hasDerivAt_stripIntegral`) and constant
(`stripIntegral_eq_of_mem_strip`) on the open strip `0 < Im ζ < π`. -/
noncomputable def stripIntegral (m : ℝ) (F G : RealTestFunction) (ζ : ℂ) : ℂ :=
  ∫ p, boostPhaseIntegral m F G p ζ * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)

/-- The weight `𝐩 ↦ 1 / (2(2π)³ ω_m(𝐩))` is continuous for `m ≠ 0`. -/
theorem continuous_shellWeight {m : ℝ} (hm : m ≠ 0) :
    Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  have hK : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  exact Complex.continuous_ofReal.comp (continuous_const.div
    (continuous_const.mul (continuous_dispersion m))
    fun p => (mul_pos hK (dispersion_pos hm p)).ne')

/-- `stripIntegrand m F G ζ` is continuous (`m ≠ 0`). -/
theorem continuous_stripIntegrand {m : ℝ} (hm : m ≠ 0) (F G : RealTestFunction) (ζ : ℂ) :
    Continuous (stripIntegrand m F G ζ) := by
  have hψ : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      boostPhase m ζ q.1 (q.2.2 - q.2.1) :=
    continuous_boostPhase_comp m ζ continuous_fst (continuous_snd.snd.sub continuous_snd.fst)
  have hF : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((F.1 q.2.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_testFunction F).comp continuous_snd.fst)
  have hG : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((G.1 q.2.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_testFunction G).comp continuous_snd.snd)
  have hw : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) : ℝ) : ℂ) :=
    (continuous_shellWeight hm).comp continuous_fst
  exact (((Complex.continuous_exp.comp (continuous_const.mul hψ)).mul hF).mul hG).mul hw

/-- `stripIntegrandDeriv m F G ζ` is continuous (`m ≠ 0`). -/
theorem continuous_stripIntegrandDeriv {m : ℝ} (hm : m ≠ 0) (F G : RealTestFunction) (ζ : ℂ) :
    Continuous (stripIntegrandDeriv m F G ζ) := by
  have hψ : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      boostPhase m ζ q.1 (q.2.2 - q.2.1) :=
    continuous_boostPhase_comp m ζ continuous_fst (continuous_snd.snd.sub continuous_snd.fst)
  have hψ' : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      boostPhaseDeriv m ζ q.1 (q.2.2 - q.2.1) :=
    continuous_boostPhaseDeriv_comp m ζ continuous_fst
      (continuous_snd.snd.sub continuous_snd.fst)
  have hF : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((F.1 q.2.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_testFunction F).comp continuous_snd.fst)
  have hG : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((G.1 q.2.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_testFunction G).comp continuous_snd.snd)
  have hw : Continuous fun q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime) =>
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) : ℝ) : ℂ) :=
    (continuous_shellWeight hm).comp continuous_fst
  exact ((((Complex.continuous_exp.comp (continuous_const.mul hψ)).mul
    (continuous_const.mul hψ')).mul hF).mul hG).mul hw

/-- `ζ ↦ stripIntegrand m F G ζ q` is entire with derivative `stripIntegrandDeriv m F G ζ q`. -/
theorem hasDerivAt_stripIntegrand (m : ℝ) (F G : RealTestFunction) (ζ : ℂ)
    (q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime)) :
    HasDerivAt (fun ζ => stripIntegrand m F G ζ q) (stripIntegrandDeriv m F G ζ q) ζ :=
  ((((hasDerivAt_boostPhase m q.1 (q.2.2 - q.2.1) ζ).const_mul Complex.I).cexp.mul_const
    ((F.1 q.2.1 : ℝ) : ℂ)).mul_const ((G.1 q.2.2 : ℝ) : ℂ)).mul_const
    (((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) : ℝ) : ℂ))

/-- On the closed strip, with `κ ≤ sin(Im ζ) e^{-|Re ζ|}`:
`|stripIntegrand m F G ζ (𝐩, x, y)| ≤ m⁻¹ e^{-κ (s - 2) ω_m(𝐩)} |F(x)| |G(y)|`. -/
theorem norm_stripIntegrand_le {m s κ : ℝ} (hm : 0 < m) (hs : 2 ≤ s) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    {ζ : ℂ} (h0 : 0 ≤ ζ.im) (hπ : ζ.im ≤ Real.pi)
    (hκ : κ ≤ Real.sin ζ.im * Real.exp (-|ζ.re|))
    (q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime)) :
    ‖stripIntegrand m F G ζ q‖ ≤
      1 / m * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) * (|F.1 q.2.1| * |G.1 q.2.2|)) := by
  have hK : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  have hωpos : 0 < dispersion m q.1 := dispersion_pos hm.ne' q.1
  have hwpos : 0 < 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) :=
    one_div_pos.mpr (mul_pos hK hωpos)
  have hwle : 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) ≤ 1 / m := by
    refine one_div_le_one_div_of_le hm ?_
    calc m ≤ dispersion m q.1 := le_dispersion hm.le q.1
      _ = 1 * dispersion m q.1 := (one_mul _).symm
      _ ≤ 2 * (2 * Real.pi) ^ 3 * dispersion m q.1 :=
          mul_le_mul_of_nonneg_right one_le_two_mul_two_pi_pow_three hωpos.le
  have hE := mul_abs_mul_abs_le_of_tsupport hF hG
    (A := ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖)
    (B := Real.exp (-(κ * (s - 2) * dispersion m q.1))) (x := q.2.1) (y := q.2.2)
    (fun hx hy => norm_exp_I_mul_boostPhase_le_exp (m := m) hs h0 hπ hκ q.1 hx hy)
  have hnorm : ‖stripIntegrand m F G ζ q‖ =
      ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖ *
        (|F.1 q.2.1| * |G.1 q.2.2|) * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1)) := by
    simp only [stripIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
    ring
  rw [hnorm]
  calc ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖ *
        (|F.1 q.2.1| * |G.1 q.2.2|) * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1))
      ≤ Real.exp (-(κ * (s - 2) * dispersion m q.1)) * (|F.1 q.2.1| * |G.1 q.2.2|) * (1 / m) :=
        mul_le_mul hE hwle hwpos.le
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = 1 / m * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) * (|F.1 q.2.1| * |G.1 q.2.2|)) := by
        ring

/-- On the closed strip, with `κ ≤ sin(Im ζ) e^{-|Re ζ|}` and `|cosh ζ|, |sinh ζ| ≤ M`:
`|stripIntegrandDeriv m F G ζ (𝐩, x, y)| ≤ 2 (s + 2) M e^{-κ (s - 2) ω_m(𝐩)} |F(x)| |G(y)|`
(the factor `ω_m(𝐩)` of `∂_ζ ψ` is cancelled by the weight). -/
theorem norm_stripIntegrandDeriv_le {m s κ M : ℝ} (hm : 0 < m) (hs : 2 ≤ s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) {ζ : ℂ} (h0 : 0 ≤ ζ.im)
    (hπ : ζ.im ≤ Real.pi) (hκ : κ ≤ Real.sin ζ.im * Real.exp (-|ζ.re|))
    (hc : ‖Complex.cosh ζ‖ ≤ M) (hsh : ‖Complex.sinh ζ‖ ≤ M)
    (q : EuclideanSpace ℝ (Fin 3) × (Spacetime × Spacetime)) :
    ‖stripIntegrandDeriv m F G ζ q‖ ≤
      2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
        (|F.1 q.2.1| * |G.1 q.2.2|)) := by
  have hK : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  have hωpos : 0 < dispersion m q.1 := dispersion_pos hm.ne' q.1
  have hwpos : 0 < 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1) :=
    one_div_pos.mpr (mul_pos hK hωpos)
  have hM : 0 ≤ M := (norm_nonneg _).trans hc
  have hs0 : 0 ≤ s := by linarith
  have hωw : dispersion m q.1 * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (mul_pos hK hωpos)]
    calc dispersion m q.1 = 1 * dispersion m q.1 := (one_mul _).symm
      _ ≤ 2 * (2 * Real.pi) ^ 3 * dispersion m q.1 :=
          mul_le_mul_of_nonneg_right one_le_two_mul_two_pi_pow_three hωpos.le
  have hE := mul_abs_mul_abs_le_of_tsupport hF hG
    (A := ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖ *
      ‖boostPhaseDeriv m ζ q.1 (q.2.2 - q.2.1)‖)
    (B := Real.exp (-(κ * (s - 2) * dispersion m q.1)) * (2 * dispersion m q.1 * (s + 2) * M))
    (x := q.2.1) (y := q.2.2) (fun hx hy => by
      have h1 := norm_exp_I_mul_boostPhase_le_exp (m := m) hs h0 hπ hκ q.1 hx hy
      have h2 := norm_boostPhaseDeriv_le m hc hsh q.1 (q.2.2 - q.2.1)
      have h3 := abs_fst_add_abs_inner_le_of_mem_doubleCone hs0 hx hy
      have h4 : 2 * dispersion m q.1 * (|(q.2.2 - q.2.1).1| + |⟪e₁, (q.2.2 - q.2.1).2⟫_ℝ|) * M ≤
          2 * dispersion m q.1 * (s + 2) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (mul_pos two_pos hωpos).le) hM
      exact mul_le_mul h1 (h2.trans h4) (norm_nonneg _) (Real.exp_pos _).le)
  have hnorm : ‖stripIntegrandDeriv m F G ζ q‖ =
      ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖ *
        ‖boostPhaseDeriv m ζ q.1 (q.2.2 - q.2.1)‖ * (|F.1 q.2.1| * |G.1 q.2.2|) *
        (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1)) := by
    simp only [stripIntegrandDeriv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hwpos]
    ring
  have hB : 0 ≤ 2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
      (|F.1 q.2.1| * |G.1 q.2.2|)) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (by linarith)) hM)
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  rw [hnorm]
  calc ‖Complex.exp (Complex.I * boostPhase m ζ q.1 (q.2.2 - q.2.1))‖ *
        ‖boostPhaseDeriv m ζ q.1 (q.2.2 - q.2.1)‖ * (|F.1 q.2.1| * |G.1 q.2.2|) *
        (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1))
      ≤ Real.exp (-(κ * (s - 2) * dispersion m q.1)) * (2 * dispersion m q.1 * (s + 2) * M) *
          (|F.1 q.2.1| * |G.1 q.2.2|) * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1)) :=
        mul_le_mul_of_nonneg_right hE hwpos.le
    _ = 2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
          (|F.1 q.2.1| * |G.1 q.2.2|)) *
          (dispersion m q.1 * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q.1))) := by ring
    _ ≤ 2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
          (|F.1 q.2.1| * |G.1 q.2.2|)) * 1 := mul_le_mul_of_nonneg_left hωw hB
    _ = 2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
          (|F.1 q.2.1| * |G.1 q.2.2|)) := mul_one _

/-- For `0 < Im ζ < π`, `stripIntegrand m F G ζ` is integrable on `ℝ³ × (Spacetime × Spacetime)`
(`m > 0`, `s > 2`, supports in the two double cones). -/
theorem integrable_stripIntegrand {m s : ℝ} (hm : 0 < m) (hs : 2 < s) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    {ζ : ℂ} (h0 : 0 < ζ.im) (hπ : ζ.im < Real.pi) :
    Integrable (stripIntegrand m F G ζ)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure Spacetime).prod volume)) := by
  have hκ : 0 < Real.sin ζ.im * Real.exp (-|ζ.re|) :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi h0 hπ) (Real.exp_pos _)
  have hc : 0 < Real.sin ζ.im * Real.exp (-|ζ.re|) * (s - 2) := mul_pos hκ (by linarith)
  refine ((integrable_stripMajorant m hc F G).const_mul (1 / m)).mono'
    (continuous_stripIntegrand hm.ne' F G ζ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  exact norm_stripIntegrand_le hm hs.le hF hG h0.le hπ.le le_rfl q

/-- **Fubini**: for `0 < Im ζ < π`, `G(ζ) = ∫ Φ(𝐩, ζ) dν(𝐩)` is the integral of `stripIntegrand`
over the product measure on `ℝ³ × (Spacetime × Spacetime)`. -/
theorem stripIntegral_eq_integral_prod {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) {ζ : ℂ} (h0 : 0 < ζ.im)
    (hπ : ζ.im < Real.pi) :
    stripIntegral m F G ζ = ∫ q, stripIntegrand m F G ζ q
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure Spacetime).prod volume)) := by
  rw [integral_prod _ (integrable_stripIntegrand hm hs hF hG h0 hπ)]
  unfold stripIntegral
  congr 1
  funext p
  unfold boostPhaseIntegral
  rw [← integral_mul_const]
  rfl

/-! ### E. Holomorphy on the open strip -/

/-- **Holomorphy on the open strip** (differentiation under the integral sign): for `m > 0`,
`s > 2`, `F` supported in the unit double cone at the origin and `G` in the unit double cone at
`s 𝐞₁`, `G(ζ) = ∫ Φ(𝐩, ζ) dν(𝐩)` has a complex derivative at every `ζ₀` with
`0 < Im ζ₀ < π`. -/
theorem hasDerivAt_stripIntegral {m s : ℝ} (hm : 0 < m) (hs : 2 < s) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    {ζ₀ : ℂ} (h0 : 0 < ζ₀.im) (hπ : ζ₀.im < Real.pi) :
    HasDerivAt (stripIntegral m F G)
      (∫ q, stripIntegrandDeriv m F G ζ₀ q
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          ((volume : Measure Spacetime).prod volume))) ζ₀ := by
  have hκ0 : 0 < Real.sin ζ₀.im * Real.exp (-|ζ₀.re|) :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi h0 hπ) (Real.exp_pos _)
  obtain ⟨κ, hκ, hκlt⟩ : ∃ κ : ℝ, 0 < κ ∧ κ < Real.sin ζ₀.im * Real.exp (-|ζ₀.re|) :=
    ⟨Real.sin ζ₀.im * Real.exp (-|ζ₀.re|) / 2, half_pos hκ0, half_lt_self hκ0⟩
  obtain ⟨M, hMc, hMs⟩ : ∃ M : ℝ, ‖Complex.cosh ζ₀‖ < M ∧ ‖Complex.sinh ζ₀‖ < M :=
    ⟨‖Complex.cosh ζ₀‖ + ‖Complex.sinh ζ₀‖ + 1,
      by linarith [norm_nonneg (Complex.sinh ζ₀)], by linarith [norm_nonneg (Complex.cosh ζ₀)]⟩
  have hrate : Continuous fun ζ : ℂ => Real.sin ζ.im * Real.exp (-|ζ.re|) :=
    (Real.continuous_sin.comp Complex.continuous_im).mul
      (Real.continuous_exp.comp (continuous_abs.comp Complex.continuous_re).neg)
  have hopen : IsOpen {ζ : ℂ | κ < Real.sin ζ.im * Real.exp (-|ζ.re|) ∧
      ‖Complex.cosh ζ‖ < M ∧ ‖Complex.sinh ζ‖ < M ∧ 0 < ζ.im ∧ ζ.im < Real.pi} :=
    (isOpen_lt continuous_const hrate).inter
      ((isOpen_lt Complex.continuous_cosh.norm continuous_const).inter
        ((isOpen_lt Complex.continuous_sinh.norm continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const))))
  have hmem : ζ₀ ∈ {ζ : ℂ | κ < Real.sin ζ.im * Real.exp (-|ζ.re|) ∧
      ‖Complex.cosh ζ‖ < M ∧ ‖Complex.sinh ζ‖ < M ∧ 0 < ζ.im ∧ ζ.im < Real.pi} :=
    ⟨hκlt, hMc, hMs, h0, hπ⟩
  have hc : 0 < κ * (s - 2) := mul_pos hκ (by linarith)
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      ((volume : Measure Spacetime).prod volume))
    (F := stripIntegrand m F G) (F' := stripIntegrandDeriv m F G) (x₀ := ζ₀)
    (bound := fun q => 2 * (s + 2) * M * (Real.exp (-(κ * (s - 2) * dispersion m q.1)) *
      (|F.1 q.2.1| * |G.1 q.2.2|)))
    (hopen.mem_nhds hmem)
    (Filter.Eventually.of_forall fun ζ =>
      (continuous_stripIntegrand hm.ne' F G ζ).aestronglyMeasurable)
    (integrable_stripIntegrand hm hs hF hG h0 hπ)
    (continuous_stripIntegrandDeriv hm.ne' F G ζ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q ζ hζ =>
      norm_stripIntegrandDeriv_le hm hs.le hF hG hζ.2.2.2.1.le hζ.2.2.2.2.le hζ.1.le hζ.2.1.le
        hζ.2.2.1.le q)
    ((integrable_stripMajorant m hc F G).const_mul (2 * (s + 2) * M))
    (Filter.Eventually.of_forall fun q ζ _ => hasDerivAt_stripIntegrand m F G ζ q)
  refine hderiv.congr_of_eventuallyEq ?_
  have hstrip : IsOpen {ζ : ℂ | 0 < ζ.im ∧ ζ.im < Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  filter_upwards [hstrip.mem_nhds ⟨h0, hπ⟩] with ζ hζ
  exact stripIntegral_eq_integral_prod hm hs hF hG hζ.1 hζ.2

/-- `G(ζ) = ∫ Φ(𝐩, ζ) dν(𝐩)` is complex differentiable at every point of the open strip
`0 < Im ζ < π` (`m > 0`, `s > 2`, supports in the two double cones). -/
theorem differentiableAt_stripIntegral {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) {ζ : ℂ} (h0 : 0 < ζ.im)
    (hπ : ζ.im < Real.pi) : DifferentiableAt ℂ (stripIntegral m F G) ζ :=
  (hasDerivAt_stripIntegral hm hs hF hG h0 hπ).differentiableAt

/-! ### E. Constancy on the open strip -/

/-- `G(σ + ζ) = G(ζ)` for real `σ` (`m ≠ 0`; stage D). -/
theorem stripIntegral_add_ofReal {m : ℝ} (hm : m ≠ 0) (σ : ℝ) (F G : RealTestFunction)
    (ζ : ℂ) : stripIntegral m F G ((σ : ℂ) + ζ) = stripIntegral m F G ζ :=
  integral_boostPhaseIntegral_add_ofReal hm σ F G ζ

/-- The complex derivative of `G` vanishes on the open strip: it equals the derivative in the real
direction, and `G` is constant in `Re ζ`. -/
theorem deriv_stripIntegral_eq_zero {m s : ℝ} (hm : 0 < m) (hs : 2 < s) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    {ζ₀ : ℂ} (h0 : 0 < ζ₀.im) (hπ : ζ₀.im < Real.pi) :
    deriv (stripIntegral m F G) ζ₀ = 0 := by
  have hd : HasDerivAt (stripIntegral m F G) (deriv (stripIntegral m F G) ζ₀) ζ₀ :=
    (differentiableAt_stripIntegral hm hs hF hG h0 hπ).hasDerivAt
  have h1 : HasDerivAt (fun x : ℂ => stripIntegral m F G (x + ζ₀))
      (deriv (stripIntegral m F G) ζ₀) 0 := by
    refine HasDerivAt.comp_add_const 0 ζ₀ ?_
    rw [zero_add]
    exact hd
  have h2 : HasDerivAt (fun y : ℝ => stripIntegral m F G ((y : ℂ) + ζ₀))
      (deriv (stripIntegral m F G) ζ₀) 0 := by
    refine HasDerivAt.comp_ofReal (e := fun x : ℂ => stripIntegral m F G (x + ζ₀)) ?_
    rw [Complex.ofReal_zero]
    exact h1
  have h3 : (fun y : ℝ => stripIntegral m F G ((y : ℂ) + ζ₀)) =
      fun _ => stripIntegral m F G ζ₀ :=
    funext fun y => stripIntegral_add_ofReal hm.ne' y F G ζ₀
  rw [h3] at h2
  exact h2.unique (hasDerivAt_const 0 _)

/-- **Constancy on the open strip**: for `m > 0`, `s > 2`, `F` supported in the unit double cone
at the origin and `G` in the unit double cone at `s 𝐞₁`, `G(ζ₁) = G(ζ₂)` for all `ζ₁`, `ζ₂` with
`0 < Im ζ₁, Im ζ₂ < π` (`G` is holomorphic with vanishing derivative on the convex open strip). -/
theorem stripIntegral_eq_of_mem_strip {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) {ζ₁ ζ₂ : ℂ} (h₁0 : 0 < ζ₁.im)
    (h₁π : ζ₁.im < Real.pi) (h₂0 : 0 < ζ₂.im) (h₂π : ζ₂.im < Real.pi) :
    stripIntegral m F G ζ₁ = stripIntegral m F G ζ₂ := by
  have hopen : IsOpen (Complex.im ⁻¹' Set.Ioo 0 Real.pi) :=
    isOpen_Ioo.preimage Complex.continuous_im
  have hconv : Convex ℝ (Complex.im ⁻¹' Set.Ioo 0 Real.pi) :=
    (convex_Ioo 0 Real.pi).linear_preimage Complex.imLm
  refine hopen.is_const_of_deriv_eq_zero hconv.isPreconnected ?_ ?_ ⟨h₁0, h₁π⟩ ⟨h₂0, h₂π⟩
  · intro ζ hζ
    exact (differentiableAt_stripIntegral hm hs hF hG hζ.1 hζ.2).differentiableWithinAt
  · intro ζ hζ
    exact deriv_stripIntegral_eq_zero hm hs hF hG hζ.1 hζ.2

/-- **Stage E, on the imaginary axis**: `∫ Φ(𝐩, iθ₁) dν(𝐩) = ∫ Φ(𝐩, iθ₂) dν(𝐩)` for
`θ₁, θ₂ ∈ (0, π)` (`m > 0`, `s > 2`, `F` supported in the unit double cone at the origin, `G` in
the unit double cone at `s 𝐞₁`). -/
theorem integral_boostPhaseIntegral_mul_I_eq {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) {θ₁ θ₂ : ℝ} (h₁0 : 0 < θ₁)
    (h₁π : θ₁ < Real.pi) (h₂0 : 0 < θ₂) (h₂π : θ₂ < Real.pi) :
    ∫ p, boostPhaseIntegral m F G p ((θ₁ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p ((θ₂ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  have him : ∀ θ : ℝ, ((θ : ℂ) * Complex.I).im = θ := fun _ => by
    rw [Complex.mul_I_im, Complex.ofReal_re]
  exact stripIntegral_eq_of_mem_strip hm hs hF hG (ζ₁ := (θ₁ : ℂ) * Complex.I)
    (ζ₂ := (θ₂ : ℂ) * Complex.I) (by rw [him]; exact h₁0) (by rw [him]; exact h₁π)
    (by rw [him]; exact h₂0) (by rw [him]; exact h₂π)

/-- **Stage E** (the form used in stage G): for `θ ∈ (0, π)`,
`∫ Φ(𝐩, iθ) dν(𝐩) = ∫ Φ(𝐩, iπ/2) dν(𝐩)`. -/
theorem integral_boostPhaseIntegral_eq_on_strip {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      ∫ p, boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
          ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
        ∫ p, boostPhaseIntegral m F G p (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
          ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := fun _θ hθ0 hθπ =>
  integral_boostPhaseIntegral_mul_I_eq hm hs hF hG hθ0 hθπ (half_pos Real.pi_pos)
    (half_lt_self Real.pi_pos)

/-- **Stage G, conditional on the edge continuity of stage F**: if
`θ ↦ ∫ Φ(𝐩, iθ) dν(𝐩)` is continuous on `[0, π]`, then its boundary values at `θ = 0` and
`θ = π` agree (it is constant on `(0, π)`), hence `Im ⟨κ_m F, κ_m G⟩ = 0`. -/
theorem im_oneParticleInner_eq_zero_of_continuousOn {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    (hcont : ContinuousOn (fun θ : ℝ => ∫ p, boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) (Set.Icc 0 Real.pi)) :
    (oneParticleInner m F G).im = 0 := by
  have hconst : Set.EqOn (fun θ : ℝ => ∫ p, boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ))
      (fun _ => ∫ p, boostPhaseIntegral m F G p (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) (Set.Ioo 0 Real.pi) :=
    fun θ hθ => integral_boostPhaseIntegral_eq_on_strip hm hs hF hG θ hθ.1 hθ.2
  have hEq := hconst.of_subset_closure hcont continuousOn_const Set.Ioo_subset_Icc_self
    (closure_Ioo Real.pi_pos.ne).symm.subset
  have h0 : ∫ p, boostPhaseIntegral m F G p (((0 : ℝ) : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) :=
    hEq (Set.left_mem_Icc.mpr Real.pi_pos.le)
  have hπ : ∫ p, boostPhaseIntegral m F G p ((Real.pi : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, boostPhaseIntegral m F G p (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) :=
    hEq (Set.right_mem_Icc.mpr Real.pi_pos.le)
  rw [Complex.ofReal_zero, zero_mul] at h0
  exact im_oneParticleInner_eq_zero_of_boundary_eq m F G (h0.trans hπ.symm)

end VacuumBellSeparation
