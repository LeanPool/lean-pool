/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticDbarGauge.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarL2

/-! # Removing the potential from the weak ∂bar equation
Exponential conjugation identifies the actual weighted formal adjoint with
the unweighted Cauchy–Riemann operator on compact tests. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- Multiplication by the reciprocal full density. -/
def planarGaugeMultiplier (W : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.exp (W z) : ℂ) * f z

/-- Exact real derivative of an exponentially conjugated function. -/
theorem planarGaugeMultiplier_fderiv (W : ℂ → ℝ) (f : ℂ → ℂ)
    (hW : Differentiable ℝ W) (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (planarGaugeMultiplier W f) z v =
      (Real.exp (W z) : ℂ) * (fderiv ℝ f z v + (planarDerivative v W z : ℂ) * f z) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z (hW z).hasFDerivAt.exp).mul
    (hf z).hasFDerivAt
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h.fderiv
  change fderiv ℝ (planarGaugeMultiplier W f) z v = _ at he
  rw [he]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  dsimp [planarDerivative]
  push_cast
  ring

/-- Exact gauge removal of the weighted formal adjoint. -/
theorem planarDbarAdjoint_gauge (W : ℂ → ℝ) (f : ℂ → ℂ)
    (hW : Differentiable ℝ W) (hf : Differentiable ℝ f) (z : ℂ) :
    planarDbarAdjoint W (planarGaugeMultiplier W f) z =
      (Real.exp (W z) : ℂ) * planarDbarAdjoint (fun _ => 0) f z := by
  unfold planarDbarAdjoint
  rw [planarGaugeMultiplier_fderiv W f hW hf z 1,
    planarGaugeMultiplier_fderiv W f hW hf z Complex.I]
  simp only [planarDerivative, fderiv_const_apply, zero_apply,
    Complex.ofReal_zero, mul_zero, sub_zero, zero_mul]
  unfold planarGaugeMultiplier
  ring

/-- Multiplication by exp(nV) preserves the actual compact C² test space. -/
def planarPotentialGaugeTest (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (f : PlanarCompactTest) : PlanarCompactTest :=
  ⟨planarGaugeMultiplier (fun z => (n : ℝ) * V z) f,
    ⟨(Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul hV))).mul
      f.property.1, f.property.2.mul_left⟩⟩

/-- The gauged weighted adjoint test is the unweighted adjoint divided by
the density's square root. -/
theorem planarWeightedAdjointTestMap_gauge (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (f : PlanarCompactTest) (z : ℂ) :
    planarWeightedAdjointTestMap n V (planarPotentialGaugeTest n V hV f) z =
      planarDbarAdjoint (fun _ => 0) f z * (Real.exp ((n : ℝ) * V z / 2) : ℂ) := by
  change planarDbarAdjoint (fun z => (n : ℝ) * V z)
    (planarGaugeMultiplier (fun z => (n : ℝ) * V z) f) z * planarPotentialHalfWeight n V z = _
  rw [planarDbarAdjoint_gauge _ _ (contDiff_const.mul hV |>.differentiable (by norm_num))
    (f.property.1.differentiable (by norm_num))]
  have he : Real.exp ((n : ℝ) * V z) * Real.exp (-(n : ℝ) * V z / 2) =
      Real.exp ((n : ℝ) * V z / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold planarPotentialHalfWeight
  calc
    _ = planarDbarAdjoint (fun _ => 0) f z *
        ((Real.exp ((n : ℝ) * V z) * Real.exp (-(n : ℝ) * V z / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by rw [he]

/-- The actual weighted function represented by a Lebesgue-L² vector. -/
def planarUngaugedL2Function (n : ℕ) (V : ℂ → ℝ) (u : PlanarLebesgueL2) (z : ℂ) : ℂ :=
  u z * (Real.exp ((n : ℝ) * V z / 2) : ℂ)

private theorem planar_transfer_real_scalar (a b : ℂ) (r : ℝ) :
    ⟪a, b * (r : ℂ)⟫_ℝ = (star (a * (r : ℂ)) * b).re := by
  simp only [Complex.inner, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem planar_gauge_pairing_ae (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (u : PlanarLebesgueL2) (φ : PlanarCompactTest) :
    (fun z => ⟪u z, planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num))
      (planarPotentialGaugeTest n V hV φ) z⟫_ℝ) =ᵐ[volume]
    (fun z => (star (planarUngaugedL2Function n V u z) *
      planarDbarAdjoint (fun _ => 0) φ z).re) := by
  filter_upwards [(planarWeightedAdjointTestMap_memLp n V (hV.of_le (by norm_num))
    (planarPotentialGaugeTest n V hV φ)).coeFn_toLp] with z hz
  change ⟪u z, ((planarWeightedAdjointTestMap_memLp n V (hV.of_le (by norm_num))
    (planarPotentialGaugeTest n V hV φ)).toLp _) z⟫_ℝ = _
  rw [hz, planarWeightedAdjointTestMap_gauge]
  exact planar_transfer_real_scalar (u z) (planarDbarAdjoint (fun _ => 0) φ z)
    (Real.exp ((n : ℝ) * V z / 2))

/-- All unweighted Cauchy–Riemann test pairings are integrable for the actual
weighted L² representative; no global unweighted L² assumption is needed. -/
theorem planarUngaugedL2Function_test_pairing_integrable
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2) (φ : PlanarCompactTest) :
    Integrable (fun z => (star (planarUngaugedL2Function n V u z) *
      planarDbarAdjoint (fun _ => 0) φ z).re) volume :=
  (L2.integrable_inner (𝕜 := ℝ) u (planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num))
    (planarPotentialGaugeTest n V hV φ))).congr (planar_gauge_pairing_ae n V hV u φ)

/-- The actual weighted distributional kernel consists of functions satisfying
the unweighted distributional Cauchy–Riemann zero equation against every
compact C² test. This removes the potential from the holomorphy problem. -/
theorem planarWeakDbarKernel_unweighted_test_equation
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2)
    (hu : u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num))) (φ : PlanarCompactTest) :
    (∫ z, (star (planarUngaugedL2Function n V u z) *
      planarDbarAdjoint (fun _ => 0) φ z).re) = 0 := by
  rw [← integral_congr_ae (planar_gauge_pairing_ae n V hV u φ), ← L2.inner_def]
  exact (mem_planarWeakDbarKernel_iff n V (hV.of_le (by norm_num)) u).mp hu
    (planarPotentialGaugeTest n V hV φ)

/-- The actual weighted representative is locally integrable, as required
for its unweighted distributional Cauchy–Riemann equation. -/
theorem planarUngaugedL2Function_locallyIntegrable
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (u : PlanarLebesgueL2) :
    LocallyIntegrable (planarUngaugedL2Function n V u) volume := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply hu.mul_continuous
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const.mul hV).div_const 2))

/-- Embed any compact real C² test into the complex test space. -/
def planarComplexifiedTest (c : ℂ) (θ : ℂ → ℝ) (hθ : ContDiff ℝ 2 θ)
    (hc : HasCompactSupport θ) : PlanarCompactTest :=
  ⟨(fun z => c * (θ z : ℂ)), ⟨contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hθ),
    (hc.comp_left (g := Complex.ofReal) rfl).mul_left⟩⟩

private theorem planarComplexifiedTest_fderiv (c : ℂ) (θ : ℂ → ℝ) (hθ : ContDiff ℝ 2 θ)
    (hc : HasCompactSupport θ) (z v : ℂ) :
    fderiv ℝ (planarComplexifiedTest c θ hθ hc : ℂ → ℂ) z v =
      c * (planarDerivative v θ z : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z
    (hθ.differentiable (by norm_num) z).hasFDerivAt).const_mul c
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h.fderiv
  change fderiv ℝ (planarComplexifiedTest c θ hθ hc : ℂ → ℂ) z v = _ at he
  rw [he]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rfl

private theorem planarComplexifiedTest_adjoint (c : ℂ) (θ : ℂ → ℝ) (hθ : ContDiff ℝ 2 θ)
    (hc : HasCompactSupport θ) (z : ℂ) :
    planarDbarAdjoint (fun _ => 0) (planarComplexifiedTest c θ hθ hc) z =
      -(1 / 2 : ℂ) * c * ((planarDerivative 1 θ z : ℂ) -
        Complex.I * (planarDerivative Complex.I θ z : ℂ)) := by
  unfold planarDbarAdjoint
  rw [planarComplexifiedTest_fderiv c θ hθ hc z 1,
    planarComplexifiedTest_fderiv c θ hθ hc z Complex.I]
  simp only [planarDerivative, fderiv_const_apply, zero_apply,
    Complex.ofReal_zero, mul_zero, sub_zero, zero_mul, add_zero]
  ring

/-- The exact two real distributional Cauchy–Riemann equations for the
actual locally integrable representative of any weighted ∂bar-kernel vector. -/
theorem planarWeakDbarKernel_cauchyRiemann_test_equations
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2)
    (hu : u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)))
    (θ : ℂ → ℝ) (hθ : ContDiff ℝ 2 θ) (hc : HasCompactSupport θ) :
    (∫ z, (planarUngaugedL2Function n V u z).re * planarDerivative 1 θ z -
      (planarUngaugedL2Function n V u z).im * planarDerivative Complex.I θ z) = 0 ∧
    (∫ z, (planarUngaugedL2Function n V u z).im * planarDerivative 1 θ z +
      (planarUngaugedL2Function n V u z).re * planarDerivative Complex.I θ z) = 0 := by
  have hx := planarWeakDbarKernel_unweighted_test_equation n V hV u hu
    (planarComplexifiedTest 1 θ hθ hc)
  have hy := planarWeakDbarKernel_unweighted_test_equation n V hV u hu
    (planarComplexifiedTest Complex.I θ hθ hc)
  have hpx (z : ℂ) : (star (planarUngaugedL2Function n V u z) *
      planarDbarAdjoint (fun _ => 0) (planarComplexifiedTest 1 θ hθ hc) z).re =
      (-1 / 2 : ℝ) * ((planarUngaugedL2Function n V u z).re * planarDerivative 1 θ z -
        (planarUngaugedL2Function n V u z).im * planarDerivative Complex.I θ z) := by
    rw [planarComplexifiedTest_adjoint]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
      Complex.div_im, Complex.one_re, Complex.one_im]
    norm_num
    ring
  have hpy (z : ℂ) : (star (planarUngaugedL2Function n V u z) *
      planarDbarAdjoint (fun _ => 0) (planarComplexifiedTest Complex.I θ hθ hc) z).re =
      (-1 / 2 : ℝ) * ((planarUngaugedL2Function n V u z).im * planarDerivative 1 θ z +
        (planarUngaugedL2Function n V u z).re * planarDerivative Complex.I θ z) := by
    rw [planarComplexifiedTest_adjoint]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
      Complex.div_im, Complex.one_re, Complex.one_im]
    norm_num
    ring
  simp_rw [hpx] at hx
  simp_rw [hpy] at hy
  rw [integral_const_mul] at hx hy
  constructor <;> linarith

/-- Each component in the distributional CR equations is integrable;
the test equations do not rely on totalized nonintegrable integrals. -/
theorem planarUngaugedL2Function_cartesian_test_integrable
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (u : PlanarLebesgueL2)
    (θ : ℂ → ℝ) (hθ : ContDiff ℝ 2 θ) (hc : HasCompactSupport θ) (v : ℂ) :
    Integrable (fun z => (planarUngaugedL2Function n V u z).re * planarDerivative v θ z) volume ∧
    Integrable (fun z => (planarUngaugedL2Function n V u z).im * planarDerivative v θ z) volume :=
        by
  have hd : Continuous (planarDerivative v θ) :=
    ((hθ.continuous_fderiv (by norm_num))).clm_apply continuous_const
  have hdc : HasCompactSupport (planarDerivative v θ) := hc.fderiv_apply ℝ v
  have hp := (planarUngaugedL2Function_locallyIntegrable n V hV
      u).integrable_smul_left_of_hasCompactSupport hd hdc
  constructor
  · have hr := Complex.reCLM.integrable_comp hp
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, mul_comm] using hr
  · have hi := Complex.imCLM.integrable_comp hp
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, mul_comm] using hi

end
end GinibrePoincare
