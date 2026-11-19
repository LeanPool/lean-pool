/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticL2KernelIntegral.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2Product
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual Bochner L² kernel integrals and pointwise representatives -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace Pointwise
namespace GinibrePoincare
noncomputable section

/-- Separated compact scalar kernels have genuine compact support on the
whole product plane. -/
theorem separatedPlanarKernel_hasCompactSupport
    (φ ψ : ℂ → ℂ) (hφ : HasCompactSupport φ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x : ℂ × ℂ => φ x.1 * ψ x.2) := by
  have hS : IsCompact ((tsupport φ).prod (tsupport ψ)) := IsCompact.prod hφ hψ
  apply hS.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hS.isClosed
  intro x hx
  exact ⟨subset_closure (fun h => hx (by simp [h])),
    subset_closure (fun h => hx (by simp [h]))⟩

/-- Compact coefficient and compact translated kernel have jointly compact
support in the integration and evaluation variables, in any normed group. -/
theorem finiteTranslatedKernel_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E]
    (f k : E → ℂ) (hf : HasCompactSupport f) (hk : HasCompactSupport k) :
    HasCompactSupport (fun p : E × E => f p.1 * k (p.2 - p.1)) := by
  have hS : IsCompact ((tsupport f).prod (tsupport f + tsupport k)) :=
    IsCompact.prod hf (IsCompact.add hf hk)
  apply hS.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hS.isClosed
  intro p hp
  have hf' : f p.1 ≠ 0 := fun h => hp (by simp [h])
  have hk' : k (p.2 - p.1) ≠ 0 := fun h => hp (by simp [h])
  exact ⟨subset_closure hf', ⟨p.1, subset_closure hf', p.2 - p.1,
    subset_closure hk', by abel_nf⟩⟩

/-- Compact coefficient and compact translated kernel have jointly compact
support in the integration and evaluation variables. -/
theorem translatedProductKernel_hasCompactSupport
    (f k : ℂ × ℂ → ℂ) (hf : HasCompactSupport f) (hk : HasCompactSupport k) :
    HasCompactSupport (fun p : (ℂ × ℂ) × (ℂ × ℂ) => f p.1 * k (p.2 - p.1)) :=
  finiteTranslatedKernel_hasCompactSupport f k hf hk

/-- On a finite-dimensional real normed space with a locally finite σ-finite measure, a
genuine integrable L²-valued compact kernel family has the actual pointwise integral as its
almost-everywhere representative. -/
theorem finiteDimensionalL2_kernel_integral_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [SigmaFinite μ]
    (g : E × E → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (G : E → Lp ℂ 2 μ)
    (hG : Integrable G μ)
    (hcoef : ∀ a, (G a : E → ℂ) =ᵐ[μ] (fun x => g (a, x))) :
    (((∫ a, G a ∂μ) : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ]
      (fun x => ∫ a, g (a, x) ∂μ) := by
  have hgi : Integrable g (μ.prod μ) := hg.integrable_of_hasCompactSupport hc
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (∫ a, G a ∂μ)).locallyIntegrable (by norm_num))
        hgi.integral_prod_right.locallyIntegrable
  intro θ hθ hθc
  have hθm : MemLp (fun x => (θ x : ℂ)) 2 μ :=
    (Complex.continuous_ofReal.comp hθ.continuous).memLp_of_hasCompactSupport
      (hθc.comp_left (by simp))
  let Θ := hθm.toLp (fun x => (θ x : ℂ))
  have hpair (U : Lp ℂ 2 μ) : ⟪Θ, U⟫_ℂ = ∫ x, θ x • U x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hθm.coeFn_toLp] with x hx
    change ⟪(hθm.toLp _) x, U x⟫_ℂ = θ x • U x
    rw [hx]
    simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul]
    exact mul_comm _ _
  have hgm : Integrable (fun p => θ p.2 • g p) (μ.prod μ) :=
    ((hθ.continuous.comp continuous_snd).smul hg).integrable_of_hasCompactSupport hc.smul_left
  calc
    _ = ⟪Θ, ∫ a, G a ∂μ⟫_ℂ := (hpair _).symm
    _ = ∫ a, ⟪Θ, G a⟫_ℂ ∂μ := ((innerSL ℂ Θ).integral_comp_comm hG).symm
    _ = ∫ a, ∫ x, θ x • g (a, x) ∂μ ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro a
      change ⟪Θ, G a⟫_ℂ = ∫ x, θ x • g (a, x) ∂μ
      rw [hpair]
      exact integral_congr_ae ((hcoef a).mono (fun x hx => congrArg (fun z => θ x • z) hx))
    _ = ∫ x, ∫ a, θ x • g (a, x) ∂μ ∂μ := integral_integral_swap hgm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => integral_smul (θ x) (fun a => g (a, x)))

/-- A genuine integrable L²-valued compact kernel family has the actual
pointwise integral as its almost-everywhere representative. -/
theorem productL2_kernel_integral_ae
    (g : (ℂ × ℂ) × (ℂ × ℂ) → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (G : ℂ × ℂ → Lp ℂ 2 ((volume : Measure ℂ).prod volume))
    (hG : Integrable G ((volume : Measure ℂ).prod volume))
    (hcoef : ∀ a, (G a : ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod volume] (fun x => g (a, x))) :
    (((∫ a, G a ∂((volume : Measure ℂ).prod volume)) : Lp ℂ 2 ((volume : Measure ℂ).prod volume)) :
        ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod volume]
      (fun x => ∫ a, g (a, x) ∂((volume : Measure ℂ).prod volume)) :=
  finiteDimensionalL2_kernel_integral_ae _ g hg hc G hG hcoef

/-- The actual weighted average of translated compact kernels is the
weighted scalar convolution, almost everywhere. -/
theorem productL2_weighted_translated_kernel_integral_ae
    (f k b : ℂ × ℂ → ℂ) (hf : Continuous f) (hk : Continuous k) (hb : Continuous b)
    (hfc : HasCompactSupport f) (hkc : HasCompactSupport k)
    (G : ℂ × ℂ → Lp ℂ 2 ((volume : Measure ℂ).prod volume))
    (hG : Integrable G ((volume : Measure ℂ).prod volume))
    (hcoef : ∀ a, (G a : ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod volume]
      (fun x => (f a * k (x - a)) * b x)) :
    (((∫ a, G a ∂((volume : Measure ℂ).prod volume)) :
      Lp ℂ 2 ((volume : Measure ℂ).prod volume)) : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod volume]
      (fun x => (∫ a, f a * k (x - a) ∂((volume : Measure ℂ).prod volume)) * b x) := by
  have hc := (translatedProductKernel_hasCompactSupport f k hfc hkc).mul_right
    (f' := fun p : (ℂ × ℂ) × (ℂ × ℂ) => b p.2)
  have hg : Continuous (fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      (f p.1 * k (p.2 - p.1)) * b p.2) :=
    ((hf.comp continuous_fst).mul (hk.comp (continuous_snd.sub continuous_fst))).mul
      (hb.comp continuous_snd)
  have he := productL2_kernel_integral_ae _ hg hc G hG hcoef
  exact he.mono (fun x hx => hx.trans (integral_mul_const (b x) _))

end
end GinibrePoincare
