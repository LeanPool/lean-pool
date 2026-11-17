/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity

/-!
# Generators of inverses and powers

The derivative of `Ring.inverse ∘ G`, the generator of an inverse operator `𝓛(A⁻¹) = −A⁻¹(𝓛A)A⁻¹ +
Σ_k A⁻¹H_kA⁻¹H_kA⁻¹`, and
bounds for generators of powers.
-/

@[expose] public section

noncomputable section



namespace FunctionalInequalities.Probability.Diffusion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

private theorem fderiv_evaluate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : V → E} {x : V}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : V) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

section Inverse

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

private theorem fderiv_product_apply {f g : V → R} {x : V}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : V) :
    fderiv ℝ (fun y => f y * g y) x v =
      f x * fderiv ℝ g x v + fderiv ℝ f x v * g x := by
  rw [fderiv_fun_mul' hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul, op_smul_eq_mul]

variable [CompleteSpace R]

/--
**Derivative of the inverse of an operator-valued function**: `D(A⁻¹)(x)[v] = −A⁻¹ (DA[v]) A⁻¹` at a
point where
`A x` is a unit. -/
theorem fderiv_ringInverse_comp_apply (A : V → R) {x : V} (hA : DifferentiableAt ℝ A x)
    (hu : IsUnit (A x)) (v : V) :
    fderiv ℝ (fun y => Ring.inverse (A y)) x v =
      -(Ring.inverse (A x) * fderiv ℝ A x v * Ring.inverse (A x)) := by
  have hi :
    HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse (A x)) (Ring.inverse (A x))))
      (A x) := by
    simpa only [← Ring.inverse_unit, hu.unit_spec] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
  have hc := (hi.comp x hA.hasFDerivAt).fderiv
  exact congrArg (fun L : V →L[ℝ] R => L v) hc

private theorem inverse_second_diagonal (A : V → R) {x : V}
    (hA : ContDiffAt ℝ 2 A x) (hu : IsUnit (A x)) (v : V) :
    fderiv ℝ (fderiv ℝ (fun y => Ring.inverse (A y))) x v v =
      -(Ring.inverse (A x) * fderiv ℝ (fderiv ℝ A) x v v *
          Ring.inverse (A x)) +
        (2 : ℝ) •
          (Ring.inverse (A x) * fderiv ℝ A x v * Ring.inverse (A x) *
            fderiv ℝ A x v * Ring.inverse (A x)) := by
  have hAd : DifferentiableAt ℝ A x := hA.differentiableAt (by norm_num)
  have hAf : DifferentiableAt ℝ (fderiv ℝ A) x :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi : ContDiffAt ℝ 2 Ring.inverse (A x) := by
    simpa only [hu.unit_spec] using
      (contDiffAt_ringInverse (𝕜 := ℝ) (n := 2) hu.unit)
  have hI : ContDiffAt ℝ 2 (fun y => Ring.inverse (A y)) x :=
    hi.fun_comp x hA
  have hId := hI.differentiableAt (by norm_num)
  have hIf : DifferentiableAt ℝ
      (fderiv ℝ (fun y => Ring.inverse (A y))) x :=
    (hI.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x :=
    hAf.clm_apply (differentiableAt_const v)
  have hue : ∀ᶠ y in nhds x, IsUnit (A y) :=
    hA.continuousAt.eventually (Units.isOpen.mem_nhds hu)
  have he :
      (fun y => fderiv ℝ (fun z => Ring.inverse (A z)) y v) =ᶠ[nhds x]
        (fun y => -(Ring.inverse (A y) * fderiv ℝ A y v * Ring.inverse (A y))) := by
    filter_upwards [hA.eventually (by norm_num), hue] with y hy huy
    exact fderiv_ringInverse_comp_apply A
      (hy.differentiableAt (by norm_num)) huy v
  rw [← fderiv_evaluate hIf v v, he.fderiv_eq, fderiv_fun_neg]
  simp only [neg_apply]
  rw [fderiv_product_apply (hId.fun_mul hDv) hId,
    fderiv_product_apply hId hDv,
    fderiv_ringInverse_comp_apply A hAd hu,
    fderiv_evaluate hAf v v, two_smul ℝ]
  noncomm_ring

/--
**Generator of the inverse** (the drift of `A_t⁻¹` in Itô's formula): for `A` that is `C²` at `x`
with `A x` a unit,
`𝓛(A⁻¹) = −A⁻¹ (𝓛A) A⁻¹ + Σ_k A⁻¹ (DA[σ_k]) A⁻¹ (DA[σ_k]) A⁻¹`, where `𝓛A = DA[b] + ½ Σ_k D²A[σ_k,
σ_k]`. -/
theorem generator_ringInverse_comp (b : V → V) (σ : V → Fin d → V) (A : V → R) {x : V}
    (hA : ContDiffAt ℝ 2 A x) (hu : IsUnit (A x)) :
    fderiv ℝ (fun y => Ring.inverse (A y)) x (b x) +
        (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ (fun y => Ring.inverse (A y))) x (σ x k) (σ x k) =
      -(Ring.inverse (A x) *
              (fderiv ℝ A x (b x) +
                (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ A) x (σ x k) (σ x k)) *
            Ring.inverse (A x)) +
        ∑ k,
          Ring.inverse (A x) * fderiv ℝ A x (σ x k) * Ring.inverse (A x) *
              fderiv ℝ A x (σ x k) *
            Ring.inverse (A x) := by
  rw [fderiv_ringInverse_comp_apply A (hA.differentiableAt (by norm_num)) hu]
  simp only [inverse_second_diagonal A hA hu, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, smul_add, smul_neg, smul_smul]
  norm_num
  abel

end Inverse

private theorem power_first (n : ℕ) (t u : ℝ) :
    fderiv ℝ (fun z : ℝ => z ^ (n + 2)) t u =
      (u * (n + 2 : ℝ)) * t ^ (n + 1) := by
  rw [fderiv_eq_smul_deriv, deriv_pow_field]
  have hn : n + 2 - 1 = n + 1 := by omega
  simp only [hn, smul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem power_second (n : ℕ) (t u : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : ℝ => z ^ (n + 2))) t u u =
      ((n + 2 : ℝ) * (n + 1) * t ^ n) * u ^ 2 := by
  have hp : ContDiff ℝ 2 (fun z : ℝ => z ^ (n + 2)) :=
    contDiff_id.pow (n + 2)
  have hpd : DifferentiableAt ℝ
      (fderiv ℝ (fun z : ℝ => z ^ (n + 2))) t :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) t
  rw [← fderiv_evaluate hpd u u]
  have he :
      (fun z : ℝ => fderiv ℝ (fun a : ℝ => a ^ (n + 2)) z u) =
        (fun z : ℝ => (u * (n + 2 : ℝ)) * z ^ (n + 1)) :=
    funext (fun z => power_first n z u)
  rw [he, fderiv_eq_smul_deriv,
    ((hasDerivAt_pow (n + 1) t).const_mul (u * (n + 2 : ℝ))).deriv]
  simp only [smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/--
**Generator of a power** (Lyapunov calculus): if `F > 0` at `x`, `𝓛F ≤ K₁ F` and the carré du champ
`Σ_k (DF[σ_k])² ≤ K₂ F²` at `x`, then `𝓛(F^q) ≤ (q K₁ + q(q−1)/2 · K₂) F^q` at `x`. -/
theorem diffusionGenerator_pow_le (b : V → V) (σ : V → Fin d → V) {F : V → ℝ}
    (hF : ContDiff ℝ 2 F) {x : V} (hpos : 0 < F x) {K₁ K₂ : ℝ}
    (h1 : diffusionGenerator b σ F x ≤ K₁ * F x)
    (h2 : ∑ k, (fderiv ℝ F x (σ x k)) ^ 2 ≤ K₂ * F x ^ 2) (q : ℕ) :
    diffusionGenerator b σ (fun y => F y ^ q) x ≤
      ((q : ℝ) * K₁ + (q : ℝ) * ((q : ℝ) - 1) / 2 * K₂) * F x ^ q := by
  rcases q with _ | q
  · simp [diffusionGenerator]
  rcases q with _ | n
  · simpa using h1
  change diffusionGenerator b σ (fun y => F y ^ (n + 2)) x ≤ _
  have hp : ContDiff ℝ 2 (fun t : ℝ => t ^ (n + 2)) := contDiff_id.pow (n + 2)
  have hg :
    diffusionGenerator b σ (fun y => F y ^ (n + 2)) x =
      ((n + 2 : ℝ) * F x ^ (n + 1)) * diffusionGenerator b σ F x +
        ((n + 2 : ℝ) * (n + 1) / 2 * F x ^ n) * ∑ k, (fderiv ℝ F x (σ x k)) ^ 2 := by
    change diffusionGenerator b σ ((fun t : ℝ => t ^ (n + 2)) ∘ F) x = _
    rw [diffusionGenerator_comp b σ (fun t : ℝ => t ^ (n + 2)) F x hp hF]
    simp only [power_first, power_second, smul_eq_mul, ← Finset.mul_sum, diffusionGenerator]
    ring
  rw [hg]
  calc
    ((n + 2 : ℝ) * F x ^ (n + 1)) * diffusionGenerator b σ F x +
          ((n + 2 : ℝ) * (n + 1) / 2 * F x ^ n) * ∑ k, (fderiv ℝ F x (σ x k)) ^ 2 ≤
        ((n + 2 : ℝ) * F x ^ (n + 1)) * (K₁ * F x) +
          ((n + 2 : ℝ) * (n + 1) / 2 * F x ^ n) * (K₂ * F x ^ 2) := by
      exact
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by
      simp only [Nat.cast_succ, pow_succ]
      ring

end FunctionalInequalities.Probability.Diffusion
