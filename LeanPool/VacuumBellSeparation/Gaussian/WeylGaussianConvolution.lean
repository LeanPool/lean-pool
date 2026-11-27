/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RelabeledWeylAverage

/-!
# The actual twisted Gaussian convolution for a Weyl sandwich

The two Gaussian weights and literal Weyl phases are integrated with
respect to complex Lebesgue measure. An exact scalar identity reduces
the convolution to the already established integrable exponential-vector
Weyl kernel. This is the scalar ingredient for projection and compressed
Weyl identities of a symplectically relabeled Gaussian average.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

/-- Phase space vacuum weight given by `Complex.exp ((-‖z‖ ^ 2 / 2 : ℝ) : ℂ)`. -/
def phaseSpaceVacuumWeight {m : ℕ} (z : MultiModePhaseSpace m) : ℂ :=
  Complex.exp ((-‖z‖ ^ 2 / 2 : ℝ) : ℂ)

/-- Weyl sandwich convolution. -/
def weylSandwichConvolution {m : ℕ} (a u : MultiModePhaseSpace m) (z : Fin m → ℂ) : ℂ :=
  let v : MultiModePhaseSpace m := WithLp.toLp 2 z
  phaseSpaceVacuumWeight v * phaseSpaceVacuumWeight (u - v - a) *
    weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) v a *
    weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) (v + a) (u - v - a)

theorem weylSandwichConvolution_eq_kernel {m : ℕ} (a u : MultiModePhaseSpace m)
    (z : Fin m → ℂ) :
    weylSandwichConvolution a u z =
      (phaseSpaceVacuumWeight a * phaseSpaceVacuumWeight u) *
        (weylVacuumWeight m z *
          inner ℂ (multiExponentialVector (fun j => u j))
            (multiOscillatorWeyl (WithLp.toLp 2 z) (multiExponentialVector (fun j => a j)))) := by
  let v : MultiModePhaseSpace m := WithLp.toLp 2 z
  have hvu : inner ℂ v u = conj (inner ℂ u v) := (inner_conj_symm v u).symm
  have hau : inner ℂ a u = conj (inner ℂ u a) := (inner_conj_symm a u).symm
  have hav : inner ℂ a v = conj (inner ℂ v a) := (inner_conj_symm a v).symm
  have hvv : (inner ℂ v v).im = 0 := by
    simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) v
  have haa : (inner ℂ a a).im = 0 := by
    simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) a
  rw [multiOscillatorWeyl_exponential_kernel (WithLp.toLp 2 z) u a]
  change phaseSpaceVacuumWeight v * phaseSpaceVacuumWeight (u - v - a) *
      weylPhase id v a * weylPhase id (v + a) (u - v - a) =
    (phaseSpaceVacuumWeight a * phaseSpaceVacuumWeight u) *
      (phaseSpaceVacuumWeight v *
        Complex.exp (((-‖v‖ ^ 2 / 2 : ℝ) : ℂ) - inner ℂ v a + inner ℂ u (v + a)))
  simp only [phaseSpaceVacuumWeight, weylPhase, id_eq, ← Complex.exp_add]
  congr 1
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    hvu, hau, hav]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im,
      Complex.I_re, Complex.I_im, RCLike.re_to_complex, hvv, haa] <;> ring

theorem integrable_weylSandwichConvolution {m : ℕ} (a u : MultiModePhaseSpace m) :
    Integrable (weylSandwichConvolution a u) := by
  apply ((integrable_gaussianWeyl_exponential_kernel (fun j => u j) (fun j => a j)).const_mul
    (phaseSpaceVacuumWeight a * phaseSpaceVacuumWeight u)).congr
  exact Filter.Eventually.of_forall fun z =>
    (weylSandwichConvolution_eq_kernel a u z).symm

/-- The exact π^m normalization and both vacuum factors in the Weyl
sandwich convolution. All integrals in this identity are genuinely integrable. -/
theorem integral_weylSandwichConvolution {m : ℕ} (a u : MultiModePhaseSpace m) :
    (∫ z : Fin m → ℂ, weylSandwichConvolution a u z) =
      (Real.pi : ℂ) ^ m * phaseSpaceVacuumWeight a * phaseSpaceVacuumWeight u := by
  simp_rw [weylSandwichConvolution_eq_kernel]
  rw [integral_const_mul]
  simp only [weylVacuumWeight]
  rw [integral_gaussianWeyl_exponential_kernel]
  ring

end VacuumBellSeparation.Gaussian
