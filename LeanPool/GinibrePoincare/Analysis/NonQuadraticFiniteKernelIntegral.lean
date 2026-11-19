/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticFiniteKernelIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2KernelIntegral
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Non quadratic finite kernel integral

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `finiteDimensionalL2_kernel_integral_ae`, `piSeparatedKernel_hasCompactSupport`,
`finiteTranslatedKernel_hasCompactSupport`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace Pointwise
namespace GinibrePoincare
noncomputable section
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

theorem piSeparatedKernel_hasCompactSupport {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hc : ∀ i, HasCompactSupport (φ i)) :
    HasCompactSupport (fun x : Fin d → ℂ => ∏ i, φ i (x i)) := by
  have hs : IsCompact {x : Fin d → ℂ | ∀ i, x i ∈ tsupport (φ i)} :=
    isCompact_pi_infinite hc
  apply hs.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hs.isClosed
  intro x hx i
  apply subset_closure
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

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

end
end GinibrePoincare
