/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesTensor.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesGaussian

/-!
# Hermite Rodrigues tensor

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dbarComponent_tensor`, `dholComponent_tensor`, `dbarComponent_tensor_iterate`,
`dholComponent_tensor_iterate`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

/-- The holomorphic Wirtinger derivative `∂ f / ∂ z_j = (∂_{x_j} f - I ∂_{y_j} f) / 2` in
coordinate `j`. -/
def dholComponent {m : ℕ} (f : Configuration m → ℂ) (j : Fin m) (z : Configuration m) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z (realCoordinateDirection j)-
    Complex.I*fderiv ℝ f z (imaginaryCoordinateDirection j))

private def tensorWirtingerOne (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z 1+a*fderiv ℝ f z Complex.I)
private def tensorWirtingerComponent {m : ℕ} (a : ℂ) (f : Configuration m → ℂ)
    (j : Fin m) (z : Configuration m) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z (realCoordinateDirection j)+
    a*fderiv ℝ f z (imaginaryCoordinateDirection j))

private theorem tensorWirtinger_coordinateLift {m : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (i j : Fin m) (z : Configuration m) :
    tensorWirtingerComponent a (fun w=>f (w i)) j z=
      if i=j then tensorWirtingerOne a f (z i) else 0 := by
  have he : (fun w : Configuration m=>f (w i))=f∘(ContinuousLinearMap.proj i : Configuration
      m→L[ℝ]ℂ) := rfl
  rw [tensorWirtingerComponent, he, fderiv_comp (𝕜:=ℝ) z (hf (z i))
    (ContinuousLinearMap.proj i).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  unfold tensorWirtingerOne
  by_cases hij : i=j
  · subst j; simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
  · simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection, hij]

private theorem tensorWirtinger_finsetProd {m : ℕ} {ι : Type*} [DecidableEq ι]
    (a : ℂ) (s : Finset ι) (f : ι → Configuration m → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin m) (z : Configuration m) :
    tensorWirtingerComponent a (fun w=>∏i∈s, f i w) j z=
      ∑i∈s, (∏k∈s.erase i, f k z)*tensorWirtingerComponent a (f i) j z := by
  unfold tensorWirtingerComponent
  rw [fderiv_finsetProd (u:=s) (g:=f) (fun i hi=>hf i hi z)]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.mul_sum,← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem tensorWirtinger_tensor {m : ℕ} (a : ℂ) (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (z : Configuration m) :
    tensorWirtingerComponent a (fun w=>∏i, f i (w i)) j z=
      tensorWirtingerOne a (f j) (z j)*∏i∈Finset.univ.erase j, f i (z i) := by
  rw [tensorWirtinger_finsetProd a Finset.univ (fun i w=>f i (w i))
    (fun i _=>(hf i).comp ((ContinuousLinearMap.proj i : Configuration m →L[ℝ] ℂ).differentiable))]
  simp_rw [tensorWirtinger_coordinateLift a _ (hf _)]
  rw [Finset.sum_eq_single j]
  · simp; ring
  · intro i hi hij; simp [hij]
  · simp

theorem dbarComponent_tensor {m : ℕ} (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (z : Configuration m) :
    dbarComponent (fun w=>∏i, f i (w i)) j z=
      dbarOnePublic (f j) (z j)*∏i∈Finset.univ.erase j, f i (z i) :=
  tensorWirtinger_tensor Complex.I f hf j z

theorem dholComponent_tensor {m : ℕ} (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (z : Configuration m) :
    dholComponent (fun w=>∏i, f i (w i)) j z=
      dholOne (f j) (z j)*∏i∈Finset.univ.erase j, f i (z i) := by
  simpa [dholComponent, tensorWirtingerComponent, tensorWirtingerOne, dholOne,
    sub_eq_add_neg] using tensorWirtinger_tensor (-Complex.I) f hf j z

private theorem tensor_update_prod {m : ℕ} (f : Fin m → ℂ → ℂ) (g : ℂ → ℂ)
    (j : Fin m) (z : Configuration m) :
    (∏i, Function.update f j g i (z i))=g (z j)*∏i∈Finset.univ.erase j, f i (z i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

private theorem tensorWirtinger_tensor_iterate {m : ℕ} (a : ℂ) (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (r : ℕ)
    (hiter : ∀ k ≤ r, Differentiable ℝ ((tensorWirtingerOne a)^[k] (f j))) :
    ((fun F : Configuration m→ℂ => fun z=>tensorWirtingerComponent a F j z)^[r]
      (fun z=>∏i, f i (z i)))=
      fun z=>∏i, Function.update f j ((tensorWirtingerOne a)^[r] (f j)) i (z i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hi := ih (fun k hk=>hiter k (by omega))
    rw [Function.iterate_succ_apply', hi]
    funext z
    rw [tensorWirtinger_tensor]
    · rw [tensor_update_prod]
      simp only [Function.update_self, Function.iterate_succ_apply']
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    · intro i
      by_cases hij : i=j
      · subst i; simpa using hiter r (by omega)
      · simpa [Function.update_of_ne hij] using hf i

theorem dbarComponent_tensor_iterate {m : ℕ} (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (r : ℕ)
    (hiter : ∀ k ≤ r, Differentiable ℝ ((dbarOnePublic)^[k] (f j))) :
    ((fun F : Configuration m→ℂ => fun z=>dbarComponent F j z)^[r]
      (fun z=>∏i, f i (z i)))=
      fun z=>(dbarOnePublic^[r] (f j)) (z j)*∏i∈Finset.univ.erase j, f i (z i) := by
  have h := tensorWirtinger_tensor_iterate Complex.I f hf j r hiter
  funext z
  exact (congrFun h z).trans (tensor_update_prod f _ j z)

theorem dholComponent_tensor_iterate {m : ℕ} (f : Fin m → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (r : ℕ)
    (hiter : ∀ k ≤ r, Differentiable ℝ ((dholOne)^[k] (f j))) :
    ((fun F : Configuration m→ℂ => fun z=>dholComponent F j z)^[r]
      (fun z=>∏i, f i (z i)))=
      fun z=>(dholOne^[r] (f j)) (z j)*∏i∈Finset.univ.erase j, f i (z i) := by
  have heOne : tensorWirtingerOne (-Complex.I)=dholOne := by
    funext F z; simp [tensorWirtingerOne, dholOne, sub_eq_add_neg]
  have heComponent : (fun F : Configuration m→ℂ => fun z=>tensorWirtingerComponent (-Complex.I) F j
      z)=
      (fun F : Configuration m→ℂ => fun z=>dholComponent F j z) := by
    funext F z; simp [tensorWirtingerComponent, dholComponent, sub_eq_add_neg]
  have h := tensorWirtinger_tensor_iterate (-Complex.I) f hf j r (by simpa [heOne] using hiter)
  rw [heOne, heComponent] at h
  funext z
  exact (congrFun h z).trans (tensor_update_prod f _ j z)

end
end ComplexHermite
end GinibrePoincare
