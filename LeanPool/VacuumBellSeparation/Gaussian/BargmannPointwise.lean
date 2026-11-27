/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.BargmannL2

/-!
# Pointwise realization of the Bargmann isometry

The pointwise entire-series expression is identified almost everywhere
with the genuine L² isometry using L² convergence, an almost-everywhere
convergent subsequence, and the convergent scalar coherent series. This
proves an actual integral inner-product identity for arbitrary oscillator
vectors without interchanging an uncontrolled infinite sum and integral.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Filter Topology
open scoped ComplexConjugate

/-- Bargmann function. -/
noncomputable def bargmannFunction (x : OscillatorSpace) (z : ℂ) : ℂ :=
  (Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) *
    inner ℂ (exponentialVector (conj z)) x

theorem bargmannMonomial_eq_coherentCoefficient (n : ℕ) (z : ℂ) :
    bargmannMonomial n z =
      (Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) * coherentCoefficient z n := by
  rw [bargmannMonomial, coherentCoefficient, Real.sqrt_mul Real.pi_pos.le]
  push_cast
  ring

theorem hasSum_bargmannFunction (x : OscillatorSpace) (z : ℂ) :
    HasSum (fun n => x n * bargmannMonomial n z) (bargmannFunction x z) := by
  have h := (lp.hasSum_inner (exponentialVector (conj z)) x).mul_left
    ((Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) : ℂ)
  have he (c a w : ℂ) (n : ℕ) :
      c * (a * coherentCoefficient w n) =
        a * (conj (coherentCoefficient (conj w) n) * c) := by
    simp only [coherentCoefficient, map_div₀, map_pow, starRingEnd_self_apply,
      Complex.conj_ofReal]
    ring
  change HasSum _ (((Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt Real.pi : ℝ) : ℂ) *
    inner ℂ (exponentialVector (conj z)) x)
  apply h.congr_fun
  intro n
  simp only [exponentialVector_apply, RCLike.inner_apply']
  exact ((congrArg (fun a : ℂ => x n * a)
    (bargmannMonomial_eq_coherentCoefficient n z)).trans (he _ _ _ _))

theorem hasSum_bargmannL2 (x : OscillatorSpace) :
    HasSum (fun n => x n • bargmannBasisVector n) (bargmannL2 x) := by
  simpa only [bargmannL2, LinearIsometry.toSpanSingleton_apply] using
    orthonormal_bargmannBasisVector.orthogonalFamily.hasSum_linearIsometry x

theorem bargmannL2_ae_eq_function (x : OscillatorSpace) :
    (bargmannL2 x : ℂ → ℂ) =ᵐ[volume] bargmannFunction x := by
  let F : ℕ → Lp ℂ 2 (volume : Measure ℂ) := fun n => x n • bargmannBasisVector n
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, F n) atTop (𝓝 (bargmannL2 x)) :=
    (hasSum_bargmannL2 x).tendsto_sum_nat
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hsum).exists_seq_tendsto_ae
  have hterms : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      F n z = x n * bargmannMonomial n z := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (x n) (bargmannBasisVector n),
      (memLp_bargmannMonomial n).coeFn_toLp] with z hsmul hmono
    change (x n • bargmannBasisVector n) z = _
    change bargmannBasisVector n z = bargmannMonomial n z at hmono
    exact hsmul.trans (congrArg (fun a : ℂ => x n * a) hmono)
  have hsums : ∀ᵐ z ∂(volume : Measure ℂ), ∀ N,
      (∑ n ∈ Finset.range N, F n) z = ∑ n ∈ Finset.range N, F n z :=
    ae_all_iff.mpr fun N => Lp.coeFn_fun_finsetSum (Finset.range N) F
  filter_upwards [hlim, hterms, hsums] with z hz hterm hpartial
  have hscalar := (hasSum_bargmannFunction x z).tendsto_sum_nat.comp hns.tendsto_atTop
  have hscalar' : Tendsto
      (fun N => (∑ n ∈ Finset.range (ns N), F n) z) atTop (𝓝 (bargmannFunction x z)) := by
    have heq : (fun N => (∑ n ∈ Finset.range (ns N), F n) z) =
        (fun N => ∑ n ∈ Finset.range N, x n * bargmannMonomial n z) ∘ ns := by
      funext N
      change (∑ n ∈ Finset.range (ns N), F n) z =
        ∑ n ∈ Finset.range (ns N), x n * bargmannMonomial n z
      rw [hpartial]
      exact Finset.sum_congr rfl fun n _ => hterm n
    rw [heq]
    exact hscalar
  exact tendsto_nhds_unique hz hscalar'

theorem memLp_bargmannFunction (x : OscillatorSpace) :
    MemLp (bargmannFunction x) 2 (volume : Measure ℂ) :=
  (Lp.memLp (bargmannL2 x)).ae_eq (bargmannL2_ae_eq_function x)

theorem integral_inner_bargmannFunction (x y : OscillatorSpace) :
    (∫ z : ℂ, inner ℂ (bargmannFunction x z) (bargmannFunction y z)) = inner ℂ x y := by
  calc
    (∫ z : ℂ, inner ℂ (bargmannFunction x z) (bargmannFunction y z)) =
        inner ℂ (bargmannL2 x) (bargmannL2 y) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [bargmannL2_ae_eq_function x, bargmannL2_ae_eq_function y] with z hx hy
      rw [hx, hy]
    _ = inner ℂ x y := bargmannL2.inner_map_map x y

theorem integrable_inner_bargmannFunction (x y : OscillatorSpace) :
    Integrable (fun z : ℂ => inner ℂ (bargmannFunction x z) (bargmannFunction y z)) := by
  have h := L2.integrable_inner (𝕜 := ℂ) (bargmannL2 x) (bargmannL2 y)
  apply h.congr
  filter_upwards [bargmannL2_ae_eq_function x, bargmannL2_ae_eq_function y] with z hx hy
  rw [hx, hy]

end VacuumBellSeparation.Gaussian
