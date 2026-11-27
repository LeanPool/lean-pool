/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Basic
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Fourier multipliers as operators on `L^p`

For `1 ≤ p < ∞` and a bounded measurable symbol `m`, `HarmonicAnalysis.multiplierNorm m p` is the
norm of `T_m` as an operator on `L^p (V)`: it is finite if and only if `T_m` extends from Schwartz
functions to a bounded operator on `L^p (V)`, that is, if and only if `m` is an `L^p` Fourier
multiplier; the extension is unique, and its norm is `multiplierNorm m p`.

## Main results

* `HarmonicAnalysis.existsUnique_extension_of_multiplierNorm_ne_top`: if `multiplierNorm m p ≠ ∞`,
  there is exactly one bounded operator `T` on `L^p (V)` with `T f = T_m f` almost everywhere for
  every Schwartz function `f`.
* `HarmonicAnalysis.enorm_eq_multiplierNorm`: the norm of such a `T` is `multiplierNorm m p` (in
  particular, `multiplierNorm m p ≠ ∞` if there is one).

Both are the density of Schwartz functions in `L^p`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `T_m (f + g) = T_m f + T_m g` for Schwartz functions `f`, `g` and a bounded measurable `m`. -/
theorem fourierMultiplier_add {m : V → ℂ} (hm : Measurable m) (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C)
    (f g : 𝓢(V, ℂ)) : fourierMultiplier m (f + g : 𝓢(V, ℂ)) =
      fourierMultiplier m f + fourierMultiplier m g := by
  have hL : Continuous fun p : V × V ↦ (-innerₗ V) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.fourierIntegral_add Real.continuous_fourierChar hL
    (integrable_smul_fourier hm hmb f) (integrable_smul_fourier hm hmb g)
  have hadd : (fun ξ => m ξ • 𝓕 ((f + g : 𝓢(V, ℂ)) : V → ℂ) ξ) =
      (fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ) + fun ξ => m ξ • 𝓕 (g : V → ℂ) ξ := by
    funext ξ
    simp only [Pi.add_apply, ← SchwartzMap.fourier_coe, FourierTransform.fourier_add, add_apply,
      smul_add]
  unfold fourierMultiplier
  rw [hadd]
  exact h

/-- `T_m (a f) = a T_m f` for Schwartz functions `f`. -/
theorem fourierMultiplier_smul (m : V → ℂ) (a : ℂ) (f : 𝓢(V, ℂ)) :
    fourierMultiplier m (a • f : 𝓢(V, ℂ)) = a • fourierMultiplier m f := by
  have hsmul : (fun ξ => m ξ • 𝓕 ((a • f : 𝓢(V, ℂ)) : V → ℂ) ξ) =
      a • fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ := by
    funext ξ
    simp only [Pi.smul_apply, ← SchwartzMap.fourier_coe, FourierTransform.fourier_smul, smul_apply,
      smul_comm a]
  unfold fourierMultiplier
  rw [hsmul]
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- `T_m f ∈ L^p` for every Schwartz function `f` if `multiplierNorm m p` is finite. -/
theorem memLp_fourierMultiplier {m : V → ℂ} {p : ℝ} (hM : multiplierNorm m p ≠ ∞)
    (f : 𝓢(V, ℂ)) : MemLp (fourierMultiplier m f) (ENNReal.ofReal p) volume :=
  (eLpNorm_fourierMultiplier_le m p f).trans_lt
    (ENNReal.mul_lt_top hM.lt_top (f.memLp _).eLpNorm_lt_top)

/-- If `multiplierNorm m p` is finite, then there is exactly one bounded operator `T` on `L^p (V)`
with `T f = T_m f` for every Schwartz function `f` (`m` bounded and measurable, `1 ≤ p < ∞`). -/
theorem existsUnique_extension_of_multiplierNorm_ne_top {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hM : multiplierNorm m p ≠ ∞) :
    ∃! T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure V),
      ∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f := by
  have hmem := memLp_fourierMultiplier hM
  -- `T_m` as a linear map from Schwartz functions to `L^p`.
  let S : 𝓢(V, ℂ) →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure V) :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by rw [fourierMultiplier_add hm hmb f g])
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by rw [fourierMultiplier_smul m a f]) }
  let e : 𝓢(V, ℂ) →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure V) :=
    (SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal p) volume).toLinearMap
  have he : DenseRange e := SchwartzMap.denseRange_toLpCLM ENNReal.ofReal_ne_top
  have hS : ∀ f, ‖S f‖ ≤ (multiplierNorm m p).toReal * ‖e f‖ := fun f => by
    have h1 : ‖S f‖ = (eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume).toReal :=
      Lp.norm_toLp _ (hmem f)
    have h2 : ‖e f‖ = (eLpNorm f (ENNReal.ofReal p) volume).toReal := SchwartzMap.norm_toLp
    rw [h1, h2, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM (f.memLp _).eLpNorm_lt_top.ne)
      (eLpNorm_fourierMultiplier_le m p f)
  refine ⟨S.extendOfNorm e, fun f => ?_, fun T hT => ?_⟩
  · have h : S.extendOfNorm e (f.toLp (ENNReal.ofReal p)) = S f :=
      LinearMap.extendOfNorm_eq he ⟨_, hS⟩ f
    rw [h]
    exact MemLp.coeFn_toLp (hmem f)
  · refine (LinearMap.extendOfNorm_unique he _ hS T (LinearMap.ext fun f => ?_)).symm
    exact Lp.ext ((hT f).trans (MemLp.coeFn_toLp (hmem f)).symm)

/-- A bounded operator `T` on `L^p (V)`, `1 ≤ p < ∞`, with `T f = T_m f` for every Schwartz function
`f` has the norm `multiplierNorm m p`. -/
theorem enorm_eq_multiplierNorm {m : V → ℂ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure V)}
    (hT : ∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f) :
    ‖T‖ₑ = multiplierNorm m p := by
  have hTf : ∀ f : 𝓢(V, ℂ), ‖T (f.toLp (ENNReal.ofReal p))‖ₑ =
      eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume := fun f => by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (hT f)
  have hf : ∀ f : 𝓢(V, ℂ), ‖f.toLp (ENNReal.ofReal p) (volume : Measure V)‖ₑ =
      eLpNorm f (ENNReal.ofReal p) volume := fun f => by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (f.coeFn_toLp _ _)
  refine le_antisymm ?_ (iSup_le fun f => ENNReal.div_le_of_le_mul ?_)
  · rcases eq_or_ne (multiplierNorm m p) ∞ with hM | hM
    · rw [hM]
      exact le_top
    have he : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) (volume : Measure V)) :=
      SchwartzMap.denseRange_toLpCLM ENNReal.ofReal_ne_top
    have hbound : ∀ x, ‖T x‖ ≤ (multiplierNorm m p).toReal * ‖x‖ := by
      intro x
      refine he.induction_on (p := fun x => ‖T x‖ ≤ (multiplierNorm m p).toReal * ‖x‖) x
        (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) fun f => ?_
      rw [SchwartzMap.toLpCLM_apply, ← toReal_eNorm, ← toReal_eNorm, hTf, hf, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM (f.memLp _).eLpNorm_lt_top.ne)
        (eLpNorm_fourierMultiplier_le m p f)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_of_le_toReal (T.opNorm_le_bound ENNReal.toReal_nonneg hbound)
  · rw [← hTf, ← hf]
    exact T.le_opENorm _

end HarmonicAnalysis
