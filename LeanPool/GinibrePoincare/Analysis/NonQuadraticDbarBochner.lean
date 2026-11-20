/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticDbarBochner.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPotential
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Planar weighted ∂bar Bochner identity
The weighted adjoint is written in real and imaginary components. The
identity proves its coercivity from the actual planar Laplacian bound,
without imposing convexity of the real Hessian.

The proof expands the real and imaginary parts of the two Wirtinger operators.
Their squared-norm difference is one quarter of the Laplacian-of-potential term
plus the divergence of an explicit compactly supported flux `(Hx, Hy)`.
Mixed partials commute because the tests are C². The flux derivatives integrate
to zero, leaving the weighted identity. Compact support also proves integrability
of every term before splitting the integral.

The coercivity theorem discards the nonnegative derivative energy and inserts
the lower bound `4 * κ ≤ planarLaplacian W`. Substituting `W = n * V` yields
the paper's constant `n * ρ / 2`. The final component identities translate this
real-coordinate proof back to the usual complex Wirtinger notation.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- A real directional derivative of a planar scalar function. -/
def planarDerivative (v : ℂ) (f : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ f z v

/-- The actual planar Laplacian. -/
def planarLaplacian (W : ℂ → ℝ) (z : ℂ) : ℝ :=
  planarDerivative 1 (planarDerivative 1 W) z +
    planarDerivative Complex.I (planarDerivative Complex.I W) z

/-- ∂bar of the complex function a+ib, expressed in real components. -/
def planarDbarOfParts (a b : ℂ → ℝ) (z : ℂ) : ℂ :=
  ⟨(planarDerivative 1 a z - planarDerivative Complex.I b z) / 2,
    (planarDerivative 1 b z + planarDerivative Complex.I a z) / 2⟩

/-- The formal weighted ∂bar adjoint under density exp(-W). -/
def planarDbarAdjointOfParts (W a b : ℂ → ℝ) (z : ℂ) : ℂ :=
  ⟨(-planarDerivative 1 a z - planarDerivative Complex.I b z +
      planarDerivative 1 W z * a z + planarDerivative Complex.I W z * b z) / 2,
    (-planarDerivative 1 b z + planarDerivative Complex.I a z +
      planarDerivative 1 W z * b z - planarDerivative Complex.I W z * a z) / 2⟩

private theorem contDiff_planarDerivative (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (v : ℂ) :
    ContDiff ℝ 1 (planarDerivative v f) :=
  (hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply contDiff_const

private theorem planarDerivative_second (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (u v z : ℂ) :
    planarDerivative v (planarDerivative u f) z = fderiv ℝ (fderiv ℝ f) z v u := by
  unfold planarDerivative
  rw [fderiv_clm_apply
    ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiable (by norm_num) z)
    (differentiableAt_const u)]
  simp

private theorem planarDerivative_comm (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (u v z : ℂ) :
    planarDerivative v (planarDerivative u f) z = planarDerivative u (planarDerivative v f) z := by
  rw [planarDerivative_second f hf, planarDerivative_second f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp [])).eq v u

/-- Exact weighted ∂bar Bochner identity for all compact C² complex tests,
represented by their compact real and imaginary parts. -/
theorem planarDbar_bochner_identity (W a b : ℂ → ℝ)
    (hW : ContDiff ℝ 2 W) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    (∫ z, Complex.normSq (planarDbarAdjointOfParts W a b z) * Real.exp (-W z)) =
      (∫ z, Complex.normSq (planarDbarOfParts a b z) * Real.exp (-W z)) +
      (1 / 4 : ℝ) * ∫ z, planarLaplacian W z * (a z ^ 2 + b z ^ 2) * Real.exp (-W z) := by
  let Dx := planarDerivative (1 : ℂ)
  let Dy := planarDerivative Complex.I
  let w := fun z => Real.exp (-W z)
  let S := fun z => a z ^ 2 + b z ^ 2
  let Hx := fun z => ((-1 / 4 : ℝ) * (Dx W z * S z) +
    (1 / 2 : ℝ) * (a z * Dy b z - b z * Dy a z)) * w z
  let Hy := fun z => ((-1 / 4 : ℝ) * (Dy W z * S z) -
    (1 / 2 : ℝ) * (a z * Dx b z - b z * Dx a z)) * w z
  have hWx := contDiff_planarDerivative W hW 1
  have hWy := contDiff_planarDerivative W hW Complex.I
  have hax := contDiff_planarDerivative a ha 1
  have hay := contDiff_planarDerivative a ha Complex.I
  have hbx := contDiff_planarDerivative b hb 1
  have hby := contDiff_planarDerivative b hb Complex.I
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hw : ContDiff ℝ 1 w := Real.contDiff_exp.comp ((hW.of_le (by norm_num)).neg)
  have hS : ContDiff ℝ 1 S := (ha1.pow 2).add (hb1.pow 2)
  have hHx : ContDiff ℝ 1 Hx :=
    (contDiff_const.mul (hWx.mul hS) |>.add (contDiff_const.mul ((ha1.mul hby).sub (hb1.mul
        hay)))).mul hw
  have hHy : ContDiff ℝ 1 Hy :=
    (contDiff_const.mul (hWy.mul hS) |>.sub (contDiff_const.mul ((ha1.mul hbx).sub (hb1.mul
        hax)))).mul hw
  have ha2c : HasCompactSupport (fun z => a z ^ 2) := by
    apply hca.mono
    intro z hz he
    exact hz (by simp [he])
  have hb2c : HasCompactSupport (fun z => b z ^ 2) := by
    apply hcb.mono
    intro z hz he
    exact hz (by simp [he])
  have hSc : HasCompactSupport S := ha2c.add hb2c
  have hHxc : HasCompactSupport Hx :=
    (hSc.mul_left.mul_left.add (hca.mul_right.sub hcb.mul_right).mul_left).mul_right
  have hHyc : HasCompactSupport Hy :=
    (hSc.mul_left.mul_left.sub (hca.mul_right.sub hcb.mul_right).mul_left).mul_right
  have hDx (z : ℂ) : Dx Hx z =
      ((-1 / 4 : ℝ) * (Dx (Dx W) z * S z + Dx W z * (2 * a z * Dx a z + 2 * b z * Dx b z)) +
        (1 / 2 : ℝ) * (Dx a z * Dy b z + a z * Dx (Dy b) z -
          (Dx b z * Dy a z + b z * Dx (Dy a) z))) * w z -
        ((-1 / 4 : ℝ) * (Dx W z * S z) +
          (1 / 2 : ℝ) * (a z * Dy b z - b z * Dy a z)) * Dx W z * w z := by
    have hWz := ((hW.differentiable (by norm_num)) z).hasFDerivAt
    have haz := ((ha.differentiable (by norm_num)) z).hasFDerivAt
    have hbz := ((hb.differentiable (by norm_num)) z).hasFDerivAt
    have hWxz := ((hWx.differentiable (by norm_num)) z).hasFDerivAt
    have hayz := ((hay.differentiable (by norm_num)) z).hasFDerivAt
    have hbyz := ((hby.differentiable (by norm_num)) z).hasFDerivAt
    have h := (((hWxz.mul ((haz.pow 2).add (hbz.pow 2))).const_mul (-1 / 4 : ℝ)).add
      (((haz.mul hbyz).sub (hbz.mul hayz)).const_mul (1 / 2 : ℝ))).mul hWz.neg.exp
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h.fderiv
    change fderiv ℝ Hx z 1 = _ at he
    rw [show Dx Hx z = fderiv ℝ Hx z 1 from rfl, he]
    simp only [add_apply, sub_apply,
      smul_apply, 
      neg_apply, smul_eq_mul]
    dsimp [Dx, Dy, planarDerivative, S, w]
    ring
  have hDy (z : ℂ) : Dy Hy z =
      ((-1 / 4 : ℝ) * (Dy (Dy W) z * S z + Dy W z * (2 * a z * Dy a z + 2 * b z * Dy b z)) -
        (1 / 2 : ℝ) * (Dy a z * Dx b z + a z * Dy (Dx b) z -
          (Dy b z * Dx a z + b z * Dy (Dx a) z))) * w z -
        ((-1 / 4 : ℝ) * (Dy W z * S z) -
          (1 / 2 : ℝ) * (a z * Dx b z - b z * Dx a z)) * Dy W z * w z := by
    have hWz := ((hW.differentiable (by norm_num)) z).hasFDerivAt
    have haz := ((ha.differentiable (by norm_num)) z).hasFDerivAt
    have hbz := ((hb.differentiable (by norm_num)) z).hasFDerivAt
    have hWyz := ((hWy.differentiable (by norm_num)) z).hasFDerivAt
    have haxz := ((hax.differentiable (by norm_num)) z).hasFDerivAt
    have hbxz := ((hbx.differentiable (by norm_num)) z).hasFDerivAt
    have h := (((hWyz.mul ((haz.pow 2).add (hbz.pow 2))).const_mul (-1 / 4 : ℝ)).sub
      (((haz.mul hbxz).sub (hbz.mul haxz)).const_mul (1 / 2 : ℝ))).mul hWz.neg.exp
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) h.fderiv
    change fderiv ℝ Hy z Complex.I = _ at he
    rw [show Dy Hy z = fderiv ℝ Hy z Complex.I from rfl, he]
    simp only [add_apply, sub_apply,
      smul_apply, 
      neg_apply, smul_eq_mul]
    dsimp [Dx, Dy, planarDerivative, S, w]
    ring
  -- The difference of the two energies is curvature plus a divergence.
  have hpoint (z : ℂ) : Complex.normSq (planarDbarAdjointOfParts W a b z) * w z =
      Complex.normSq (planarDbarOfParts a b z) * w z +
        (1 / 4 : ℝ) * (planarLaplacian W z * S z * w z) + Dx Hx z + Dy Hy z := by
    rw [hDx, hDy]
    have hamix := planarDerivative_comm a ha (1 : ℂ) Complex.I z
    have hbmix := planarDerivative_comm b hb (1 : ℂ) Complex.I z
    change Dy (Dx a) z = Dx (Dy a) z at hamix
    change Dy (Dx b) z = Dx (Dy b) z at hbmix
    rw [hamix, hbmix]
    simp only [planarDbarAdjointOfParts, planarDbarOfParts, planarLaplacian,
      Complex.normSq_apply]
    dsimp [Dx, Dy, S]
    ring
  -- Compact support removes the flux terms after integration.
  have hDxInt := integral_fderiv_complex_real_eq_zero Hx hHx hHxc
  have hDyInt := integral_fderiv_complex_imag_eq_zero Hy hHy hHyc
  have hDxI : Integrable (Dx Hx) :=
    ((hHx.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).integrable_of_hasCompactSupport
      (hHxc.fderiv_apply ℝ (1 : ℂ))
  have hDyI : Integrable (Dy Hy) :=
    ((hHy.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).integrable_of_hasCompactSupport
      (hHyc.fderiv_apply ℝ Complex.I)
  have hDb : Continuous (fun z => Complex.normSq (planarDbarOfParts a b z) * w z) := by
    convert
      (((hax.continuous.sub hby.continuous).div_const 2).mul
        ((hax.continuous.sub hby.continuous).div_const 2) |>.add
        (((hbx.continuous.add hay.continuous).div_const 2).mul
        ((hbx.continuous.add hay.continuous).div_const 2))).mul hw.continuous using 1
    funext z
    simp [planarDbarOfParts, Complex.normSq_apply]
  have hDbc : HasCompactSupport (fun z => Complex.normSq (planarDbarOfParts a b z) * w z) := by
    have hre : HasCompactSupport (fun z => (Dx a z - Dy b z) / 2) :=
      by
        convert ((hca.fderiv_apply ℝ 1).sub (hcb.fderiv_apply ℝ Complex.I)).mul_right (f' := fun _
            => (2 : ℝ)⁻¹) using 1
        rfl
    have him : HasCompactSupport (fun z => (Dx b z + Dy a z) / 2) :=
      by
        convert ((hcb.fderiv_apply ℝ 1).add (hca.fderiv_apply ℝ Complex.I)).mul_right (f' := fun _
            => (2 : ℝ)⁻¹) using 1
        rfl
    have hre2 := hre.mul_right (f' := fun z => (Dx a z - Dy b z) / 2)
    have him2 := him.mul_right (f' := fun z => (Dx b z + Dy a z) / 2)
    convert
      (hre2.add him2).mul_right (f' := w) using 1
    rfl
  have hLap : Continuous (planarLaplacian W) :=
    ((hWx.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      ((hWy.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hLapI : Integrable (fun z => planarLaplacian W z * S z * w z) :=
    ((hLap.mul hS.continuous).mul hw.continuous).integrable_of_hasCompactSupport
      (hSc.mul_left.mul_right)
  have hDbI : Integrable (fun z => Complex.normSq (planarDbarOfParts a b z) * w z) :=
      hDb.integrable_of_hasCompactSupport hDbc
  change (∫ z, Complex.normSq (planarDbarAdjointOfParts W a b z) * w z) = _
  simp_rw [hpoint]
  rw [integral_add
    (f := fun z => Complex.normSq (planarDbarOfParts a b z) * w z +
      (1 / 4 : ℝ) * (planarLaplacian W z * S z * w z) + Dx Hx z)
    (g := fun z => Dy Hy z)
    ((hDbI.add (hLapI.const_mul (1 / 4 : ℝ))).add hDxI) hDyI,
    integral_add
    (f := fun z => Complex.normSq (planarDbarOfParts a b z) * w z +
      (1 / 4 : ℝ) * (planarLaplacian W z * S z * w z))
    (g := fun z => Dx Hx z) (hDbI.add (hLapI.const_mul (1 / 4 : ℝ))) hDxI,
    integral_add (f := fun z => Complex.normSq (planarDbarOfParts a b z) * w z)
      (g := fun z => (1 / 4 : ℝ) * (planarLaplacian W z * S z * w z))
      hDbI (hLapI.const_mul (1 / 4 : ℝ)), integral_const_mul]
  change _ + _ + (∫ z, fderiv ℝ Hx z 1) + (∫ z, fderiv ℝ Hy z Complex.I) = _
  rw [hDxInt, hDyInt]
  simp [S, w]

/-- The compact-test weighted Hörmander bound follows from the planar
Laplacian alone. The real Hessian need not be positive. -/
theorem planarDbar_adjoint_coercivity (W a b : ℂ → ℝ) (κ : ℝ)
    (hW : ContDiff ℝ 2 W) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hcur : ∀ z, 4 * κ ≤ planarLaplacian W z) :
    κ * (∫ z, (a z ^ 2 + b z ^ 2) * Real.exp (-W z)) ≤
      ∫ z, Complex.normSq (planarDbarAdjointOfParts W a b z) * Real.exp (-W z) := by
  have hSc : HasCompactSupport (fun z => a z ^ 2 + b z ^ 2) := by
    have hac : HasCompactSupport (fun z => a z ^ 2) := by
      apply hca.mono
      intro z hz
      simpa [Function.mem_support] using hz
    have hbc : HasCompactSupport (fun z => b z ^ 2) := by
      apply hcb.mono
      intro z hz
      simpa [Function.mem_support] using hz
    exact hac.add hbc
  have hS : Continuous (fun z => a z ^ 2 + b z ^ 2) :=
    (ha.continuous.pow 2).add (hb.continuous.pow 2)
  have hw : Continuous (fun z => Real.exp (-W z)) := Real.continuous_exp.comp hW.continuous.neg
  have hL : Continuous (planarLaplacian W) :=
    (((contDiff_planarDerivative W hW 1).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).add
    (((contDiff_planarDerivative W hW Complex.I).continuous_fderiv (by norm_num)).clm_apply
        continuous_const)
  have hiS : Integrable (fun z => (a z ^ 2 + b z ^ 2) * Real.exp (-W z)) :=
    (hS.mul hw).integrable_of_hasCompactSupport hSc.mul_right
  have hiL : Integrable (fun z => planarLaplacian W z * (a z ^ 2 + b z ^ 2) * Real.exp (-W z)) :=
    ((hL.mul hS).mul hw).integrable_of_hasCompactSupport hSc.mul_left.mul_right
  have hle := integral_mono (hiS.const_mul (4 * κ)) hiL (fun z => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcur z) (add_nonneg (sq_nonneg (a z)) (sq_nonneg (b z))))
      (Real.exp_nonneg (-W z)))
  rw [integral_const_mul] at hle
  have hnon : 0 ≤ ∫ z, Complex.normSq (planarDbarOfParts a b z) * Real.exp (-W z) :=
    integral_nonneg (fun z => mul_nonneg (Complex.normSq_nonneg _) (Real.exp_nonneg _))
  rw [planarDbar_bochner_identity W a b hW ha hb hca hcb]
  linarith

/-- In the paper's exact subharmonic normalization, nV yields nρ/2
weighted adjoint coercivity. -/
theorem rhoSubharmonicPotential_adjoint_coercivity (n : ℕ) (V a b : ℂ → ℝ) (ρ : ℝ)
    (hV : ContDiff ℝ 2 V) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hρ : IsRhoSubharmonicPotential ρ V) :
    ((n : ℝ) * ρ / 2) * (∫ z, (a z ^ 2 + b z ^ 2) * Real.exp (-(n : ℝ) * V z)) ≤
      ∫ z, Complex.normSq (planarDbarAdjointOfParts (fun z => (n : ℝ) * V z) a b z) *
        Real.exp (-(n : ℝ) * V z) := by
  have hscale (z : ℂ) : planarLaplacian (fun z => (n : ℝ) * V z) z =
      (n : ℝ) * planarLaplacian V z := by
    have hfirst (v : ℂ) : planarDerivative v (fun z => (n : ℝ) * V z) =
        fun z => (n : ℝ) * planarDerivative v V z := by
      funext w
      unfold planarDerivative
      rw [fderiv_const_mul (hV.differentiable (by norm_num) w) (n : ℝ)]
      simp
    unfold planarLaplacian
    rw [hfirst 1, hfirst Complex.I]
    unfold planarDerivative
    have hx := fderiv_const_mul ((contDiff_planarDerivative V hV 1).differentiable (by norm_num) z)
        (n : ℝ)
    have hy := fderiv_const_mul ((contDiff_planarDerivative V hV Complex.I).differentiable (by
        norm_num) z) (n : ℝ)
    dsimp [planarDerivative] at hx hy
    rw [hx, hy]
    simp only [smul_apply, smul_eq_mul]
    rw [show planarDerivative 1 V = (fun z => fderiv ℝ V z 1) from rfl,
      show planarDerivative Complex.I V = (fun z => fderiv ℝ V z Complex.I) from rfl]
    ring
  have hbound (z : ℂ) : 4 * ((n : ℝ) * ρ / 2) ≤
      planarLaplacian (fun z => (n : ℝ) * V z) z := by
    rw [hscale]
    have hh : 2 * ρ ≤ planarLaplacian V z := hρ z
    have := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  simpa only [neg_mul] using planarDbar_adjoint_coercivity
    (fun z => (n : ℝ) * V z) a b ((n : ℝ) * ρ / 2)
    (contDiff_const.mul hV) ha hb hca hcb hbound

/-- Concrete Wirtinger ∂bar on complex-valued planar functions. -/
def planarDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- Concrete weighted formal adjoint -∂+∂W. -/
def planarDbarAdjoint (W : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) +
    (1 / 2 : ℂ) * ((planarDerivative 1 W z : ℂ) -
      Complex.I * (planarDerivative Complex.I W z : ℂ)) * f z

private theorem planar_component_derivative (T : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (z v : ℂ) :
    planarDerivative v (fun w => T (f w)) z = T (fderiv ℝ f z v) := by
  have h := (T.hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  change fderiv ℝ (T ∘ f) z v = _
  rw [h]
  rfl

/-- The real-component definition is exactly the usual Wirtinger derivative. -/
theorem planarDbarOfParts_eq (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z : ℂ) :
    planarDbarOfParts (fun w => (f w).re) (fun w => (f w).im) z = planarDbar f z := by
  have hr (v : ℂ) : planarDerivative v (fun w => (f w).re) z = (fderiv ℝ f z v).re :=
    planar_component_derivative Complex.reCLM f hf z v
  have hi (v : ℂ) : planarDerivative v (fun w => (f w).im) z = (fderiv ℝ f z v).im :=
    planar_component_derivative Complex.imCLM f hf z v
  apply Complex.ext <;> simp [planarDbarOfParts, planarDbar, hr, hi] <;> ring

/-- The real-component adjoint is exactly -∂+∂W. -/
theorem planarDbarAdjointOfParts_eq (W : ℂ → ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (z : ℂ) :
    planarDbarAdjointOfParts W (fun w => (f w).re) (fun w => (f w).im) z =
      planarDbarAdjoint W f z := by
  have hr (v : ℂ) : planarDerivative v (fun w => (f w).re) z = (fderiv ℝ f z v).re :=
    planar_component_derivative Complex.reCLM f hf z v
  have hi (v : ℂ) : planarDerivative v (fun w => (f w).im) z = (fderiv ℝ f z v).im :=
    planar_component_derivative Complex.imCLM f hf z v
  apply Complex.ext <;> simp [planarDbarAdjointOfParts, planarDbarAdjoint, hr, hi] <;> ring

/-- Actual complex compact-test Hörmander coercivity at the paper's constant. -/
theorem rhoSubharmonicPotential_complex_adjoint_coercivity
    (n : ℕ) (V : ℂ → ℝ) (f : ℂ → ℂ) (ρ : ℝ)
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hρ : IsRhoSubharmonicPotential ρ V) :
    ((n : ℝ) * ρ / 2) * (∫ z, Complex.normSq (f z) * Real.exp (-(n : ℝ) * V z)) ≤
      ∫ z, Complex.normSq (planarDbarAdjoint (fun z => (n : ℝ) * V z) f z) *
        Real.exp (-(n : ℝ) * V z) := by
  have hr : ContDiff ℝ 2 (fun z => (f z).re) := Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ 2 (fun z => (f z).im) := Complex.imCLM.contDiff.comp hf
  have hrc : HasCompactSupport (fun z => (f z).re) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (fun z => (f z).im) := hc.comp_left (g := Complex.im) rfl
  have hh := rhoSubharmonicPotential_adjoint_coercivity n V (fun z => (f z).re)
    (fun z => (f z).im) ρ hV hr hi hrc hic hρ
  simp_rw [planarDbarAdjointOfParts_eq _ f (hf.differentiable (by norm_num))] at hh
  simpa only [Complex.normSq_apply, pow_two] using hh

end
end GinibrePoincare
