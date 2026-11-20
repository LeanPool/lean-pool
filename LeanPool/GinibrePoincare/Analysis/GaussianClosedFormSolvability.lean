/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianClosedFormSolvability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarDistributionalClosure
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # The Gaussian weak closed-form domain

For Remark 2.4 of arXiv:2608.19358v2, closedness of an L² (0,1)-form is
an actual distributional curl relation. The definition below uses compact C¹
tests and the concrete Gaussian formal adjoint. It does not assume Hermite
coefficient identities or an existing potential. This module establishes the
closed Hilbert subspace needed for the subsequent solution construction;
it does not yet assert the full solvability statement of Remark 2.4.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace GinibrePoincare
noncomputable section

/-- Distributional `dbar`-closedness, expressed using the actual Gaussian
formal adjoint. Components need not have square-integrable derivatives. -/
def IsGaussianWeakClosedForm (n : ℕ)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) : Prop :=
  ∀ (j k : Fin n) (φ : Configuration n → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ),
    inner ℂ (gaussianDbarAdjointTestL2 j φ hφ hc) (α k) =
      inner ℂ (gaussianDbarAdjointTestL2 k φ hφ hc) (α j)

theorem gaussianWeakClosedForm_zero (n : ℕ) :
    IsGaussianWeakClosedForm n 0 := by
  intro j k φ hφ hc
  simp

theorem gaussianWeakClosedForm_add {n : ℕ}
    {α β : Fin n → Lp ℂ 2 (complexGaussianMeasure n)}
    (hα : IsGaussianWeakClosedForm n α) (hβ : IsGaussianWeakClosedForm n β) :
    IsGaussianWeakClosedForm n (α + β) := by
  intro j k φ hφ hc
  simp only [Pi.add_apply, inner_add_right]
  rw [hα j k φ hφ hc, hβ j k φ hφ hc]

theorem gaussianWeakClosedForm_smul {n : ℕ}
    {α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)}
    (hα : IsGaussianWeakClosedForm n α) (c : ℂ) :
    IsGaussianWeakClosedForm n (c • α) := by
  intro j k φ hφ hc
  simp only [Pi.smul_apply, inner_smul_right]
  rw [hα j k φ hφ hc]

/-- The genuine weak closed-form subspace; its membership condition is a
compact-test relation, independently of any proposed solution. -/
def gaussianWeakClosedFormSpace (n : ℕ) :
    Submodule ℂ (Fin n → Lp ℂ 2 (complexGaussianMeasure n)) where
  carrier := {α | IsGaussianWeakClosedForm n α}
  zero_mem' := gaussianWeakClosedForm_zero n
  add_mem' := gaussianWeakClosedForm_add
  smul_mem' := fun c _ hα => gaussianWeakClosedForm_smul hα c

@[simp] theorem mem_gaussianWeakClosedFormSpace {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) :
    α ∈ gaussianWeakClosedFormSpace n ↔ IsGaussianWeakClosedForm n α := Iff.rfl

theorem isClosed_gaussianWeakClosedFormSpace (n : ℕ) :
    IsClosed (gaussianWeakClosedFormSpace n :
      Set (Fin n → Lp ℂ 2 (complexGaussianMeasure n))) := by
  change IsClosed {α | IsGaussianWeakClosedForm n α}
  simp only [IsGaussianWeakClosedForm, Set.ofPred_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_iInter
  intro hc
  exact isClosed_eq
    (continuous_const.inner (continuous_apply k))
    (continuous_const.inner (continuous_apply j))

/-- Distributional closedness is preserved under Gaussian L² convergence. -/
theorem gaussianWeakClosedForm_of_tendsto {n : ℕ} {ι : Type*}
    {l : Filter ι} [NeBot l]
    (α : ι → Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (β : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : ∀ i, IsGaussianWeakClosedForm n (α i))
    (ht : Tendsto α l (𝓝 β)) : IsGaussianWeakClosedForm n β :=
  (isClosed_gaussianWeakClosedFormSpace n).mem_of_tendsto ht
    (Eventually.of_forall hα)

/-- The weak curl identity in plain Gaussian integral form. Conjugating
compact tests removes the Hermitian pairing convention. -/
theorem gaussianWeakClosedForm_integral_identity {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) (j k : Fin n)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z, α k z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
      ∂complexGaussianMeasure n) =
    ∫ z, α j z * ((n : ℂ) * z k * θ z - dbarComponent θ k z)
      ∂complexGaussianMeasure n := by
  let φ := fun z => conj (θ z)
  have hφ : ContDiff ℝ 1 φ := Complex.conjCLE.contDiff.comp hθ
  have hcφ : HasCompactSupport φ := hc.comp_left (by simp)
  have he := hα j k φ hφ hcφ
  have hadjoint (r : Fin n) (u : Lp ℂ 2 (complexGaussianMeasure n)) :
      inner ℂ (gaussianDbarAdjointTestL2 r φ hφ hcφ) u =
        ∫ z, u z * ((n : ℂ) * z r * θ z - dbarComponent θ r z)
          ∂complexGaussianMeasure n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    have ha := (gaussianDbarAdjointTest_memLp r φ hφ hcφ).coeFn_toLp
    filter_upwards [ha] with z hz
    change (gaussianDbarAdjointTestL2 r φ hφ hcφ : Configuration n → ℂ) z = _ at hz
    rw [RCLike.inner_apply, hz]
    simp only [gaussianDbarAdjointTest, map_sub, map_mul, Complex.conj_natCast,
      starRingEnd_self_apply]
    have hcj : (fun w => conj (φ w)) = θ := by funext w; simp [φ]
    rw [hcj]
    simp only [φ, starRingEnd_self_apply]
  rw [hadjoint j (α k), hadjoint k (α j)] at he
  exact he

/-- Converse integral form of compact-test weak closedness. -/
theorem gaussianWeakClosedForm_of_integral_identity {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : ∀ (j k : Fin n) (θ : Configuration n → ℂ),
      ContDiff ℝ 1 θ → HasCompactSupport θ →
      (∫ z, α k z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
        ∂complexGaussianMeasure n) =
      ∫ z, α j z * ((n : ℂ) * z k * θ z - dbarComponent θ k z)
        ∂complexGaussianMeasure n) : IsGaussianWeakClosedForm n α := by
  intro j k φ hφ hc
  have hadjoint (r : Fin n) (u : Lp ℂ 2 (complexGaussianMeasure n)) :
      inner ℂ (gaussianDbarAdjointTestL2 r φ hφ hc) u =
        ∫ z, u z * ((n : ℂ) * z r * conj (φ z) -
          dbarComponent (fun w => conj (φ w)) r z) ∂complexGaussianMeasure n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    have ha := (gaussianDbarAdjointTest_memLp r φ hφ hc).coeFn_toLp
    filter_upwards [ha] with z hz
    change (gaussianDbarAdjointTestL2 r φ hφ hc : Configuration n → ℂ) z = _ at hz
    rw [RCLike.inner_apply, hz]
    simp only [gaussianDbarAdjointTest, map_sub, map_mul, Complex.conj_natCast,
      starRingEnd_self_apply]
  rw [hadjoint j (α k), hadjoint k (α j)]
  exact hα j k (fun z => conj (φ z)) (Complex.conjCLE.contDiff.comp hφ)
    (hc.comp_left (by simp))

/-- A compact-test curl identity extends to L² limits of the actual test
adjoints. This is a closure lemma, not an assumed coefficient certificate. -/
theorem gaussianWeakClosedForm_pairing_limit {n : ℕ}
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) (j k : Fin n)
    (φ : ℕ → Configuration n → ℂ)
    (hφ : ∀ m, ContDiff ℝ 1 (φ m))
    (hc : ∀ m, HasCompactSupport (φ m))
    (A B : Lp ℂ 2 (complexGaussianMeasure n))
    (hA : Tendsto (fun m => gaussianDbarAdjointTestL2 j (φ m) (hφ m) (hc m))
      atTop (𝓝 A))
    (hB : Tendsto (fun m => gaussianDbarAdjointTestL2 k (φ m) (hφ m) (hc m))
      atTop (𝓝 B)) :
    inner ℂ A (α k) = inner ℂ B (α j) := by
  have hleft := hA.inner (𝕜 := ℂ) (tendsto_const_nhds (x := α k))
  have hright := hB.inner (𝕜 := ℂ) (tendsto_const_nhds (x := α j))
  have heq : (fun m => inner ℂ
      (gaussianDbarAdjointTestL2 j (φ m) (hφ m) (hc m)) (α k)) =
      fun m => inner ℂ
        (gaussianDbarAdjointTestL2 k (φ m) (hφ m) (hc m)) (α j) := by
    funext m
    exact hα j k (φ m) (hφ m) (hc m)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- In one complex coordinate every square-integrable (0,1)-form is closed:
there are no distinct pairs of antiholomorphic coordinates. -/
theorem gaussianWeakClosedForm_one
    (α : Fin 1 → Lp ℂ 2 (complexGaussianMeasure 1)) :
    IsGaussianWeakClosedForm 1 α := by
  intro j k φ hφ hc
  have h : j = k := Subsingleton.elim _ _
  subst k
  rfl

end
end GinibrePoincare

