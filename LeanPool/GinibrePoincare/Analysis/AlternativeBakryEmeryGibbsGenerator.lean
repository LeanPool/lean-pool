/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryIntegrationByParts
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The literal Euclidean Gibbs generator

The weighted adjoint and compact-core Dirichlet identities below are proved
under the actual density `exp(-W)`, without a stationarity certificate.
Compact-core stationarity does not by itself assert invariance of a stochastic law.
-/

@[expose] public section

open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- The Gibbs weight `exp (-W x)`. -/
def bakryEmeryGibbsWeight (W : E → ℝ) (x : E) : ℝ := Real.exp (-W x)

/-- The directional derivative `fderiv ℝ f x v` of `f` at `x` in the direction `v`. -/
def bakryEmeryGibbsDirectional (f : E → ℝ) (v : E) (x : E) : ℝ :=
  fderiv ℝ f x v

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
private theorem gibbsDirectional_contDiff {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) :
    ContDiff ℝ 1 (bakryEmeryGibbsDirectional f v) := by
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
private theorem gibbsDirectional_continuous {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    Continuous (bakryEmeryGibbsDirectional f v) := by
  exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const

omit [CompleteSpace E] in
/-- Weighted adjoint for every Euclidean direction. Only the test factor
needs compact support; the other factor may be constant or a logarithm. -/
theorem bakryEmeryGibbs_directional_adjoint (W f θ : E → ℝ) (v : E)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ)
    (hθc : HasCompactSupport θ) :
    (∫ x, bakryEmeryGibbsDirectional f v x * θ x * bakryEmeryGibbsWeight W x) =
      ∫ x, f x * (bakryEmeryGibbsDirectional W v x * θ x -
        bakryEmeryGibbsDirectional θ v x) * bakryEmeryGibbsWeight W x := by
  let w := bakryEmeryGibbsWeight W
  have hw : ContDiff ℝ 1 w := Real.contDiff_exp.comp hW.neg
  have hg : ContDiff ℝ 1 (fun x => θ x * w x) := hθ.mul hw
  have hgc : HasCompactSupport (fun x => θ x * w x) := hθc.mul_right
  have hdf := gibbsDirectional_continuous hf v
  have hdθ := gibbsDirectional_continuous hθ v
  have hdW := gibbsDirectional_continuous hW v
  have hdg := gibbsDirectional_continuous hg v
  have hi₁ : Integrable (fun x => fderiv ℝ f x v * (θ x * w x)) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi₂ : Integrable (fun x => f x * fderiv ℝ (fun y => θ y * w y) x v) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun x => f x * (θ x * w x)) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := v) hi₁ hi₂ hi₃
    (fun x _ => (hf.differentiable (by norm_num)) x)
    (fun x _ => (hg.differentiable (by norm_num)) x)
  have hformula (x : E) :
      fderiv ℝ (fun y => θ y * w y) x v =
        (bakryEmeryGibbsDirectional θ v x -
          bakryEmeryGibbsDirectional W v x * θ x) * w x := by
    have hd := ((hθ.differentiable (by norm_num) x).hasFDerivAt).mul
      (((hW.differentiable (by norm_num) x).hasFDerivAt).neg.exp)
    change HasFDerivAt (fun y => θ y * w y) _ x at hd
    rw [hd.fderiv]
    simp [w, bakryEmeryGibbsWeight, bakryEmeryGibbsDirectional]
    ring
  simp_rw [hformula] at hb
  have hl : (∫ x, bakryEmeryGibbsDirectional f v x * θ x * w x) =
      ∫ x, fderiv ℝ f x v * (θ x * w x) := by
    congr 1
    funext x
    dsimp [bakryEmeryGibbsDirectional]
    ring
  have hr : (∫ x, f x * (bakryEmeryGibbsDirectional W v x * θ x -
      bakryEmeryGibbsDirectional θ v x) * w x) =
      -(∫ x, f x * ((bakryEmeryGibbsDirectional θ v x -
        bakryEmeryGibbsDirectional W v x * θ x) * w x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  change (∫ x, bakryEmeryGibbsDirectional f v x * θ x * w x) = _
  rw [hl, hr]
  linarith

variable {ι : Type*} [Fintype ι]

/-- The ordinary unit-diffusion generator in the specified directions.
For an orthonormal basis these are exactly `Δf - ⟪∇W,∇f⟫`. -/
def bakryEmeryGibbsGenerator (W : E → ℝ) (b : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
    bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x)

/-- The carré du champ `Γ(f, g)(x) = ∑ i, ∂_{b i} f(x) * ∂_{b i} g(x)` along the family of
directions `b`. -/
def bakryEmeryGibbsCarré (b : ι → E) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ i, bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional g (b i) x

omit [CompleteSpace E] in
/-- The actual compact-core weighted Dirichlet identity. -/
theorem bakryEmeryGibbs_dirichlet (W f g : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) :
    (∫ x, g x * bakryEmeryGibbsGenerator W b f x * bakryEmeryGibbsWeight W x) =
      -(∫ x, bakryEmeryGibbsCarré b g f x * bakryEmeryGibbsWeight W x) := by
  have hw : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hc (i : ι) : HasCompactSupport (bakryEmeryGibbsDirectional f (b i)) :=
    hfc.fderiv_apply ℝ (b i)
  have hdf (i : ι) := gibbsDirectional_contDiff hf (b i)
  have hLi (i : ι) : Integrable (fun x => g x *
      (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
        bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x) *
          bakryEmeryGibbsWeight W x) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hg.continuous.mul ((gibbsDirectional_continuous (hdf i) (b i)).sub
        ((gibbsDirectional_continuous hW (b i)).mul (hdf i).continuous))).mul hw
    · exact (((hc i).fderiv_apply ℝ (b i)).sub ((hc i).mul_left)).mul_left.mul_right
  have hGi (i : ι) : Integrable (fun x => bakryEmeryGibbsDirectional g (b i) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsWeight W x) :=
    (((gibbsDirectional_continuous hg (b i)).mul (hdf i).continuous).mul
        hw).integrable_of_hasCompactSupport ((hc i).mul_left.mul_right)
  have hid (i : ι) :
      (∫ x, g x * (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i))
        (b i) x - bakryEmeryGibbsDirectional W (b i) x *
          bakryEmeryGibbsDirectional f (b i) x) * bakryEmeryGibbsWeight W x) =
      -(∫ x, bakryEmeryGibbsDirectional g (b i) x *
        bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsWeight W x) := by
    have h := bakryEmeryGibbs_directional_adjoint W g
      (bakryEmeryGibbsDirectional f (b i)) (b i) hW hg (hdf i) (hc i)
    rw [h, ← integral_neg]
    congr 1
    funext x
    ring
  unfold bakryEmeryGibbsGenerator bakryEmeryGibbsCarré
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hGi i)]
  simp_rw [hid]
  rw [Finset.sum_neg_distrib]

omit [CompleteSpace E] in
/-- Gibbs stationarity on the actual compact smooth generator core. -/
theorem bakryEmeryGibbs_core_stationarity (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, bakryEmeryGibbsGenerator W b f x * bakryEmeryGibbsWeight W x) = 0 := by
  have h := bakryEmeryGibbs_dirichlet W f (fun _ => 1) b hW hf contDiff_const hfc
  simpa [bakryEmeryGibbsCarré, bakryEmeryGibbsDirectional] using h

omit [CompleteSpace E] in
/-- Symmetry of the actual Euclidean Gibbs generator on its compact core. -/
theorem bakryEmeryGibbs_core_symmetry (W f g : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, g x * bakryEmeryGibbsGenerator W b f x * bakryEmeryGibbsWeight W x) =
      ∫ x, f x * bakryEmeryGibbsGenerator W b g x * bakryEmeryGibbsWeight W x := by
  rw [bakryEmeryGibbs_dirichlet W f g b hW hf (hg.of_le (by norm_num)) hfc,
    bakryEmeryGibbs_dirichlet W g f b hW hg (hf.of_le (by norm_num)) hgc]
  congr 2
  funext x
  unfold bakryEmeryGibbsCarré
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
/-- The carré du champ in an orthonormal basis is the ordinary gradient
inner product, rather than a separately supplied energy. -/
theorem bakryEmeryGibbsCarré_eq_gradient (b : OrthonormalBasis ι ℝ E)
    (f g : E → ℝ) (x : E) :
    bakryEmeryGibbsCarré b f g x = inner ℝ (gradient f x) (gradient g x) := by
  unfold bakryEmeryGibbsCarré bakryEmeryGibbsDirectional
  simp_rw [← inner_gradient_left]
  rw [← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (b i) (gradient g x)]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
/-- Exact Euclidean squared gradient identification. -/
theorem bakryEmeryGibbsCarré_self (b : OrthonormalBasis ι ℝ E)
    (f : E → ℝ) (x : E) :
    bakryEmeryGibbsCarré b f f x = ‖gradient f x‖ ^ 2 := by
  rw [bakryEmeryGibbsCarré_eq_gradient, real_inner_self_eq_norm_sq]

/-- The actual Euclidean Laplacian in an orthonormal basis. -/
def bakryEmeryGibbsLaplacian (b : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
/-- Identification with the literal ordinary gradient Langevin generator. -/
theorem bakryEmeryGibbsGenerator_eq_laplacian_gradient
    (W f : E → ℝ) (b : OrthonormalBasis ι ℝ E) (x : E) :
    bakryEmeryGibbsGenerator W b f x = bakryEmeryGibbsLaplacian b f x -
      inner ℝ (gradient W x) (gradient f x) := by
  rw [← bakryEmeryGibbsCarré_eq_gradient b W f x]
  unfold bakryEmeryGibbsGenerator bakryEmeryGibbsLaplacian bakryEmeryGibbsCarré
  rw [Finset.sum_sub_distrib]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
/-- Constant backgrounds do not change the actual generator. -/
theorem bakryEmeryGibbsGenerator_const_add (W f : E → ℝ) (b : ι → E) (c : ℝ) :
    bakryEmeryGibbsGenerator W b (fun x => c + f x) = bakryEmeryGibbsGenerator W b f := by
  funext x
  unfold bakryEmeryGibbsGenerator bakryEmeryGibbsDirectional
  simp only [fderiv_const_add]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
/-- The actual logarithmic differential chain rule. -/
theorem bakryEmeryGibbsDirectional_log (F : E → ℝ) (v : E) (x : E)
    (hF : DifferentiableAt ℝ F x) (hpos : 0 < F x) :
    bakryEmeryGibbsDirectional (fun y => Real.log (F y)) v x =
      bakryEmeryGibbsDirectional F v x / F x := by
  unfold bakryEmeryGibbsDirectional
  rw [(hF.hasFDerivAt.log (ne_of_gt hpos)).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

omit [CompleteSpace E] in
/-- Entropy/Fisher dissipation on positive constant-plus-compact test
functions, proved from the actual Gibbs differential adjoint. -/
theorem bakryEmeryGibbs_log_fisher_core (W f : E → ℝ) (b : ι → E) (c : ℝ)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hpos : ∀ x, 0 < c + f x) :
    (∫ x, Real.log (c + f x) * bakryEmeryGibbsGenerator W b f x *
      bakryEmeryGibbsWeight W x) =
      -(∫ x, bakryEmeryGibbsCarré b f f x / (c + f x) * bakryEmeryGibbsWeight W x) := by
  have hF : ContDiff ℝ 1 (fun x => c + f x) :=
    contDiff_const.add (hf.of_le (by norm_num))
  rw [bakryEmeryGibbs_dirichlet W f (fun x => Real.log (c + f x)) b hW hf
    (hF.log (fun x => ne_of_gt (hpos x))) hfc]
  congr 2
  funext x
  congr 1
  unfold bakryEmeryGibbsCarré
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [bakryEmeryGibbsDirectional_log _ _ x (hF.differentiable (by norm_num) x) (hpos x)]
  have he : bakryEmeryGibbsDirectional (fun y => c + f y) (b i) x =
      bakryEmeryGibbsDirectional f (b i) x := by
    unfold bakryEmeryGibbsDirectional
    rw [fderiv_const_add]
  rw [he]
  ring

/-- The same Fisher identity expressed with the ordinary Euclidean
squared gradient and the actual positive function's generator. -/
theorem bakryEmeryGibbs_entropy_fisher_core (W f : E → ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : ℝ)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hpos : ∀ x, 0 < c + f x) :
    (∫ x, Real.log (c + f x) *
      bakryEmeryGibbsGenerator W b (fun y => c + f y) x * bakryEmeryGibbsWeight W x) =
      -(∫ x, ‖gradient f x‖ ^ 2 / (c + f x) * bakryEmeryGibbsWeight W x) := by
  rw [bakryEmeryGibbsGenerator_const_add]
  simpa only [bakryEmeryGibbsCarré_self] using
    bakryEmeryGibbs_log_fisher_core W f b c hW hf hfc hpos

end
end GinibrePoincare
