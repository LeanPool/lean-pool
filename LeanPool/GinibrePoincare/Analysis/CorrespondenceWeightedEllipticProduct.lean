/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticProduct.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
/-!
# Correspondence weighted elliptic product

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_compact_C1_product`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_compact_C1_product
    (u g : Lp ℝ 2 (volume : Measure E)) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x))
    (q : E→ℝ) (hq : ContDiff ℝ 1 q) (hc : HasCompactSupport q) :
    ∃U G : Lp ℝ 2 (volume : Measure E),
      (U : E→ℝ)=ᵐ[volume](fun x=>q x*u x) ∧
      (G : E→ℝ)=ᵐ[volume](fun x=>q x*g x+fderiv ℝ q x v*u x) ∧
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G x)= -(∫x, fderiv ℝ θ x v*U x) := by
  let d : E→ℝ := fun x=>fderiv ℝ q x v
  have hd : Continuous d := (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ v
  have ht : MemLp q ⊤ (volume : Measure E) := hq.continuous.memLp_top_of_hasCompactSupport hc volume
  have hdt : MemLp d ⊤ (volume : Measure E) := hd.memLp_top_of_hasCompactSupport hdc volume
  have hU : MemLp (fun x=>q x*u x) 2 volume := ht.fun_mul (r:=2) (Lp.memLp u)
  have hG : MemLp (fun x=>q x*g x+d x*u x) 2 volume :=
    (ht.fun_mul (r:=2) (Lp.memLp g)).add (hdt.fun_mul (r:=2) (Lp.memLp u))
  refine ⟨hU.toLp _, hG.toLp _, hU.coeFn_toLp, hG.coeFn_toLp,?_⟩
  intro θ hθ hθc
  have hψ := correspondenceWeightedElliptic_weak_test_C1 u g v hw (q*θ)
    (hq.mul (hθ.of_le (by norm_num))) (hc.mul_right)
  have he (x) : fderiv ℝ (q*θ) x v=d x*θ x+q x*fderiv ℝ θ x v := by
    rw [fderiv_mul (hq.differentiable (by norm_num) x) (hθ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [d]
    ring
  simp_rw [he] at hψ
  have hi1 : Integrable (fun x=>d x*θ x*u x) volume := by
    have hm : MemLp (fun x=>d x*θ x) 2 volume :=
      (hd.mul hθ.continuous).memLp_of_hasCompactSupport (hdc.mul_right)
    exact hm.integrable_mul (Lp.memLp u)
  have hi2 : Integrable (fun x=>q x*fderiv ℝ θ x v*u x) volume := by
    have hm : MemLp (fun x=>q x*fderiv ℝ θ x v) 2 volume :=
      (hq.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply
          continuous_const)).memLp_of_hasCompactSupport (hc.mul_right)
    exact hm.integrable_mul (Lp.memLp u)
  have hi3 : Integrable (fun x=>q x*θ x*g x) volume := by
    have hm : MemLp (fun x=>q x*θ x) 2 volume :=
      (hq.continuous.mul hθ.continuous).memLp_of_hasCompactSupport (hc.mul_right)
    exact hm.integrable_mul (Lp.memLp g)
  have hψ' : (∫x, q x*θ x*g x)= -(∫x, d x*θ x*u x)-(∫x, q x*fderiv ℝ θ x v*u x) := by
    have heq : (fun x=>(d x*θ x+q x*fderiv ℝ θ x v)*u x)=
        (fun x=>d x*θ x*u x)+(fun x=>q x*fderiv ℝ θ x v*u x) := by funext x; dsimp; ring
    rw [heq] at hψ
    change (∫x, q x*θ x*g x)= -(∫x, d x*θ x*u x+q x*fderiv ℝ θ x v*u x) at hψ
    rw [integral_add hi1 hi2] at hψ
    linarith
  have hleft : (∫x, θ x*(hG.toLp _) x)=(∫x, q x*θ x*g x)+(∫x, d x*θ x*u x) := by
    calc
      _ = ∫x, q x*θ x*g x+d x*θ x*u x := by
        apply integral_congr_ae
        filter_upwards [hG.coeFn_toLp] with x hx
        rw [hx]
        ring
      _ = _ := integral_add hi3 hi1
  have hright : (∫x, fderiv ℝ θ x v*(hU.toLp _) x)=∫x, q x*fderiv ℝ θ x v*u x := by
    apply integral_congr_ae
    filter_upwards [hU.coeFn_toLp] with x hx
    rw [hx]
    ring
  rw [hleft, hright]
  linarith
end
end GinibrePoincare
