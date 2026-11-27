/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeBargmannPointwise
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Actual torus Fourier expansion of coherent coordinates

At fixed complex amplitudes, the nonnegative occupation frequencies form
an actual orthonormal subfamily of Mathlib's torus Fourier basis. The
coherent scalar coordinate is identified with the resulting L² series by
its pointwise Hilbert-space series and an a.e. convergent subsequence.
Angular Parseval follows with no uniform or absolute series assumption.
The torus Haar measure is explicitly normalized to total mass one.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

/-- The normalized Haar probability measure on the unit circle. -/
local instance torusCircleHaarMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Occupation frequency given by `fun j => k j`. -/
def occupationFrequency {m : ℕ} (k : Fin m → ℕ) : Fin m → ℤ := fun j => k j

theorem occupationFrequency_injective (m : ℕ) :
    Function.Injective (occupationFrequency (m := m)) := by
  intro k l h
  funext j
  have hj : (k j : ℤ) = (l j : ℤ) := congrFun h j
  exact_mod_cast hj

/-- Torus occupation basis obtained from `UnitAddTorus.mFourierLp`. -/
def torusOccupationBasis {m : ℕ} (k : Fin m → ℕ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin m))) :=
  UnitAddTorus.mFourierLp 2 (occupationFrequency k)

theorem orthonormal_torusOccupationBasis (m : ℕ) :
    Orthonormal ℂ (torusOccupationBasis (m := m)) :=
  UnitAddTorus.orthonormal_mFourier.comp occupationFrequency (occupationFrequency_injective m)

/-- Occupation torus L². -/
def occupationTorusL2 (m : ℕ) :
    MultiModeOscillatorSpace m →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin m))) :=
  (orthonormal_torusOccupationBasis m).orthogonalFamily.linearIsometry

theorem hasSum_occupationTorusL2 {m : ℕ} (x : MultiModeOscillatorSpace m) :
    HasSum (fun k => x k • torusOccupationBasis k) (occupationTorusL2 m x) := by
  simpa only [occupationTorusL2, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_torusOccupationBasis m).orthogonalFamily.hasSum_linearIsometry x

/-- Torus coherent label given by `fun j => a j * fourier 1 (θ j)`. -/
def torusCoherentLabel {m : ℕ} (a : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) : Fin m → ℂ :=
  fun j => a j * fourier 1 (θ j)

theorem fourier_natCast_eq_pow (n : ℕ) (θ : UnitAddCircle) :
    fourier (n : ℤ) θ = fourier 1 θ ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem multiCoherentCoefficient_torusLabel {m : ℕ}
    (a : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) (k : Fin m → ℕ) :
    multiCoherentCoefficient (torusCoherentLabel a θ) k =
      multiCoherentCoefficient a k * UnitAddTorus.mFourier (occupationFrequency k) θ := by
  simp only [multiCoherentCoefficient, UnitAddTorus.mFourier, occupationFrequency,
    ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [coherentCoefficient, coherentCoefficient, torusCoherentLabel,
    mul_pow, fourier_natCast_eq_pow]
  ring

theorem summable_torusCoherentCoefficients {m : ℕ} (a : Fin m → ℂ)
    (x : MultiModeOscillatorSpace m) :
    Summable fun k => ‖x k * multiCoherentCoefficient a k‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => ?_) ((hasSum_multiCoherent_norm_sq a).summable.mul_left (‖x‖ ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm (by norm_num) x k) 2)
    (sq_nonneg _)

/-- Torus coherent coefficients. -/
def torusCoherentCoefficients {m : ℕ} (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m) :
    MultiModeOscillatorSpace m :=
  ⟨(fun k => x k * multiCoherentCoefficient a k), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa [Real.rpow_two] using summable_torusCoherentCoefficients a x⟩

@[simp] theorem torusCoherentCoefficients_apply {m : ℕ}
    (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m) (k : Fin m → ℕ) :
    torusCoherentCoefficients a x k = x k * multiCoherentCoefficient a k := rfl

/-- Torus coherent function defined as `inner ℂ (multiExponentialVector (fun j => conj
(torusCoherentLabel a θ j))) x`. -/
def torusCoherentFunction {m : ℕ} (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m)
    (θ : UnitAddTorus (Fin m)) : ℂ :=
  inner ℂ (multiExponentialVector (fun j => conj (torusCoherentLabel a θ j))) x

theorem hasSum_torusCoherentFunction {m : ℕ} (a : Fin m → ℂ)
    (x : MultiModeOscillatorSpace m) (θ : UnitAddTorus (Fin m)) :
    HasSum (fun k => torusCoherentCoefficients a x k *
      UnitAddTorus.mFourier (occupationFrequency k) θ) (torusCoherentFunction a x θ) := by
  have h := lp.hasSum_inner (𝕜 := ℂ)
    (multiExponentialVector (fun j => conj (torusCoherentLabel a θ j))) x
  change HasSum _ (inner ℂ
    (multiExponentialVector (fun j => conj (torusCoherentLabel a θ j))) x)
  apply h.congr_fun
  intro k
  rw [multiExponentialVector_apply, RCLike.inner_apply', conj_multiCoherentCoefficient,
    multiCoherentCoefficient_torusLabel, torusCoherentCoefficients_apply]
  ring

theorem occupationTorusL2_ae_eq_coherent {m : ℕ} (a : Fin m → ℂ)
    (x : MultiModeOscillatorSpace m) :
    (occupationTorusL2 m (torusCoherentCoefficients a x) : UnitAddTorus (Fin m) → ℂ) =ᵐ[volume]
      torusCoherentFunction a x := by
  classical
  let v := torusCoherentCoefficients a x
  let F : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin m))) :=
    fun k => v k • torusOccupationBasis k
  have hsum : Tendsto (fun s : Finset (Fin m → ℕ) => ∑ k ∈ s, F k)
      atTop (𝓝 (occupationTorusL2 m v)) := hasSum_occupationTorusL2 v
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hsum).exists_seq_tendsto_ae'
  have hterms : ∀ᵐ θ ∂(volume : Measure (UnitAddTorus (Fin m))), ∀ k,
      F k θ = v k * UnitAddTorus.mFourier (occupationFrequency k) θ := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (v k) (torusOccupationBasis k),
      UnitAddTorus.coeFn_mFourierLp 2 (occupationFrequency k)] with θ hsmul hchar
    change (v k • torusOccupationBasis k) θ = _
    rw [hsmul]
    change v k * (UnitAddTorus.mFourierLp 2 (occupationFrequency k)) θ = _
    rw [hchar]
  have hsums : ∀ᵐ θ ∂(volume : Measure (UnitAddTorus (Fin m))),
      ∀ s : Finset (Fin m → ℕ), (∑ k ∈ s, F k) θ = ∑ k ∈ s, F k θ :=
    ae_all_iff.mpr fun s => Lp.coeFn_fun_finsetSum s F
  filter_upwards [hlim, hterms, hsums] with θ hθ hterm hpartial
  have hscalar := (hasSum_torusCoherentFunction a x θ).comp hns
  have hscalar' : Tendsto (fun N => (∑ k ∈ ns N, F k) θ)
      atTop (𝓝 (torusCoherentFunction a x θ)) := by
    have heq : (fun N => (∑ k ∈ ns N, F k) θ) =
        (fun s => ∑ k ∈ s, torusCoherentCoefficients a x k *
          UnitAddTorus.mFourier (occupationFrequency k) θ) ∘ ns := by
      funext N
      change (∑ k ∈ ns N, F k) θ = ∑ k ∈ ns N,
        torusCoherentCoefficients a x k * UnitAddTorus.mFourier (occupationFrequency k) θ
      rw [hpartial]
      exact Finset.sum_congr rfl fun k _ => hterm k
    rw [heq]
    exact hscalar
  exact tendsto_nhds_unique hθ hscalar'

theorem memLp_torusCoherentFunction {m : ℕ} (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m) :
    MemLp (torusCoherentFunction a x) 2 (volume : Measure (UnitAddTorus (Fin m))) :=
  (Lp.memLp (occupationTorusL2 m (torusCoherentCoefficients a x))).ae_eq
    (occupationTorusL2_ae_eq_coherent a x)

theorem integrable_torusCoherentFunction_norm_sq {m : ℕ}
    (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m) :
    Integrable (fun θ : UnitAddTorus (Fin m) => ‖torusCoherentFunction a x θ‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (memLp_torusCoherentFunction a x).aestronglyMeasurable).mp
    (memLp_torusCoherentFunction a x)

theorem integral_torusCoherentFunction_norm_sq {m : ℕ}
    (a : Fin m → ℂ) (x : MultiModeOscillatorSpace m) :
    (∫ θ : UnitAddTorus (Fin m), ‖torusCoherentFunction a x θ‖ ^ 2) =
      ∑' k, ‖x k‖ ^ 2 * ‖multiCoherentCoefficient a k‖ ^ 2 := by
  let v := torusCoherentCoefficients a x
  let f := occupationTorusL2 m v
  have hinner : (∫ θ : UnitAddTorus (Fin m),
      inner ℂ (torusCoherentFunction a x θ) (torusCoherentFunction a x θ)) = inner ℂ f f := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [occupationTorusL2_ae_eq_coherent a x] with θ hθ
    rw [hθ]
  have hint : Integrable (fun θ : UnitAddTorus (Fin m) =>
      inner ℂ (torusCoherentFunction a x θ) (torusCoherentFunction a x θ)) := by
    apply (L2.integrable_inner (𝕜 := ℂ) f f).congr
    filter_upwards [occupationTorusL2_ae_eq_coherent a x] with θ hθ
    rw [hθ]
  have hreal := congrArg (RCLike.re : ℂ → ℝ) hinner
  rw [← integral_re hint] at hreal
  have hnorm : (∫ θ : UnitAddTorus (Fin m), ‖torusCoherentFunction a x θ‖ ^ 2) = ‖v‖ ^ 2 := by
    simpa only [inner_self_eq_norm_sq, f, (occupationTorusL2 m).norm_map] using hreal
  rw [hnorm]
  have hs := lp.hasSum_norm (p := 2) (by norm_num) v
  simpa [v, torusCoherentCoefficients_apply, norm_mul, mul_pow, Real.rpow_two] using hs.tsum_eq.symm

end VacuumBellSeparation.Gaussian
