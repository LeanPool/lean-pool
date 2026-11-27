/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeBargmannL2

/-!
# Pointwise realization of the finite-mode Bargmann isometry

The genuine ℓ² inner-product series gives the pointwise coherent formula.
L² convergence over all finite occupation-index subsets and a cofinal
almost-everywhere convergent subsequence identify it with the actual
L² isometry. Countability, not a finite-volume assumption, supplies the
subsequence. The zero-mode index set is handled by the same argument.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Filter Topology
open scoped ComplexConjugate

/-- Multi Bargmann prefactor given by `∏ j, ((Real.exp (-‖z j‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) :
ℂ)`. -/
def multiBargmannPrefactor {m : ℕ} (z : Fin m → ℂ) : ℂ :=
  ∏ j, ((Real.exp (-‖z j‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) : ℂ)

/-- Multi Bargmann function given by `multiBargmannPrefactor z * inner ℂ (multiExponentialVector
(fun j => conj (z j))) x`. -/
def multiBargmannFunction {m : ℕ} (x : MultiModeOscillatorSpace m) (z : Fin m → ℂ) : ℂ :=
  multiBargmannPrefactor z * inner ℂ (multiExponentialVector (fun j => conj (z j))) x

theorem multiBargmannMonomial_eq_coherentCoefficient {m : ℕ}
    (k : Fin m → ℕ) (z : Fin m → ℂ) :
    multiBargmannMonomial k z = multiBargmannPrefactor z * multiCoherentCoefficient z k := by
  simp only [multiBargmannMonomial, bargmannMonomial_eq_coherentCoefficient,
    multiBargmannPrefactor, multiCoherentCoefficient, Finset.prod_mul_distrib]

theorem conj_multiCoherentCoefficient {m : ℕ} (z : Fin m → ℂ) (k : Fin m → ℕ) :
    conj (multiCoherentCoefficient (fun j => conj (z j)) k) = multiCoherentCoefficient z k := by
  simp only [multiCoherentCoefficient, map_prod, coherentCoefficient, map_div₀, map_pow,
    starRingEnd_self_apply, Complex.conj_ofReal]

theorem hasSum_multiBargmannFunction {m : ℕ} (x : MultiModeOscillatorSpace m) (z : Fin m → ℂ) :
    HasSum (fun k => x k * multiBargmannMonomial k z) (multiBargmannFunction x z) := by
  have h := (lp.hasSum_inner (multiExponentialVector (fun j => conj (z j))) x).mul_left
    (multiBargmannPrefactor z)
  change HasSum _ (multiBargmannPrefactor z *
    inner ℂ (multiExponentialVector (fun j => conj (z j))) x)
  apply h.congr_fun
  intro k
  rw [multiBargmannMonomial_eq_coherentCoefficient, multiExponentialVector_apply,
    RCLike.inner_apply', conj_multiCoherentCoefficient]
  ring

theorem multiBargmannL2_ae_eq_function {m : ℕ} (x : MultiModeOscillatorSpace m) :
    (multiBargmannL2 m x : (Fin m → ℂ) → ℂ) =ᵐ[volume] multiBargmannFunction x := by
  classical
  let F : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Fin m → ℂ)) :=
    fun k => x k • multiBargmannBasisVector k
  have hsum : Tendsto (fun s : Finset (Fin m → ℕ) => ∑ k ∈ s, F k)
      atTop (𝓝 (multiBargmannL2 m x)) := hasSum_multiBargmannL2 x
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hsum).exists_seq_tendsto_ae'
  have hterms : ∀ᵐ z ∂(volume : Measure (Fin m → ℂ)), ∀ k,
      F k z = x k * multiBargmannMonomial k z := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (x k) (multiBargmannBasisVector k),
      (memLp_multiBargmannMonomial k).coeFn_toLp] with z hsmul hmono
    change (x k • multiBargmannBasisVector k) z = _
    change multiBargmannBasisVector k z = multiBargmannMonomial k z at hmono
    exact hsmul.trans (congrArg (fun a : ℂ => x k * a) hmono)
  have hsums : ∀ᵐ z ∂(volume : Measure (Fin m → ℂ)), ∀ s : Finset (Fin m → ℕ),
      (∑ k ∈ s, F k) z = ∑ k ∈ s, F k z :=
    ae_all_iff.mpr fun s => Lp.coeFn_fun_finsetSum s F
  filter_upwards [hlim, hterms, hsums] with z hz hterm hpartial
  have hscalar := (hasSum_multiBargmannFunction x z).comp hns
  have hscalar' : Tendsto (fun N => (∑ k ∈ ns N, F k) z)
      atTop (𝓝 (multiBargmannFunction x z)) := by
    have heq : (fun N => (∑ k ∈ ns N, F k) z) =
        (fun s => ∑ k ∈ s, x k * multiBargmannMonomial k z) ∘ ns := by
      funext N
      change (∑ k ∈ ns N, F k) z = ∑ k ∈ ns N, x k * multiBargmannMonomial k z
      rw [hpartial]
      exact Finset.sum_congr rfl fun k _ => hterm k
    rw [heq]
    exact hscalar
  exact tendsto_nhds_unique hz hscalar'

theorem memLp_multiBargmannFunction {m : ℕ} (x : MultiModeOscillatorSpace m) :
    MemLp (multiBargmannFunction x) 2 (volume : Measure (Fin m → ℂ)) :=
  (Lp.memLp (multiBargmannL2 m x)).ae_eq (multiBargmannL2_ae_eq_function x)

theorem integral_inner_multiBargmannFunction {m : ℕ} (x y : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, inner ℂ (multiBargmannFunction x z) (multiBargmannFunction y z)) =
      inner ℂ x y := by
  calc
    _ = inner ℂ (multiBargmannL2 m x) (multiBargmannL2 m y) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [multiBargmannL2_ae_eq_function x,
        multiBargmannL2_ae_eq_function y] with z hx hy
      rw [hx, hy]
    _ = inner ℂ x y := (multiBargmannL2 m).inner_map_map x y

theorem integrable_inner_multiBargmannFunction {m : ℕ} (x y : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ => inner ℂ (multiBargmannFunction x z)
      (multiBargmannFunction y z)) := by
  have h := L2.integrable_inner (𝕜 := ℂ) (multiBargmannL2 m x) (multiBargmannL2 m y)
  apply h.congr
  filter_upwards [multiBargmannL2_ae_eq_function x, multiBargmannL2_ae_eq_function y] with z hx hy
  rw [hx, hy]

end VacuumBellSeparation.Gaussian
