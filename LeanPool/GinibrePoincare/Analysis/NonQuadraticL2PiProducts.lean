/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticL2PiProducts.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2PiOperators
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Genuine pure vectors in the whole finite product L² space -/

@[expose] public section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology InnerProductSpace
namespace GinibrePoincare
noncomputable section
variable {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin n → Measure X) [∀ i, SigmaFinite (μ i)]

theorem l2PiProductFunction_memLp (u : ∀ i, Lp ℂ 2 (μ i)) :
    MemLp (fun z : Fin n → X => ∏ i, u i (z i)) 2 (Measure.pi μ) := by
  have hm : AEStronglyMeasurable (fun z : Fin n → X => ∏ i, u i (z i)) (Measure.pi μ) :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ (fun i _ =>
      (Lp.aestronglyMeasurable (u i)).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval μ i))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hu (i : Fin n) : Integrable (fun x => ‖u i x‖ ^ 2) (μ i) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u i))).mp (Lp.memLp (u i))
  simpa only [norm_prod, Finset.prod_pow] using Integrable.fintype_prod hu

/-- The tensor product of a family of `L²` vectors `u i`, as an element of `L²` of the product
measure `Measure.pi μ`. -/
def l2PiProductVector (u : ∀ i, Lp ℂ 2 (μ i)) : Lp ℂ 2 (Measure.pi μ) :=
  (l2PiProductFunction_memLp μ u).toLp _

theorem l2PiProductVector_coeFn (u : ∀ i, Lp ℂ 2 (μ i)) :
    (l2PiProductVector μ u : (Fin n → X) → ℂ) =ᵐ[Measure.pi μ]
      (fun z => ∏ i, u i (z i)) :=
  (l2PiProductFunction_memLp μ u).coeFn_toLp
theorem complexLp_integral_norm_sq {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (u : Lp ℂ 2 ν) : (∫ x, ‖u x‖ ^ 2 ∂ν) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem l2PiProductVector_norm_sq (u : ∀ i, Lp ℂ 2 (μ i)) :
    ‖l2PiProductVector μ u‖ ^ 2 = ∏ i, ‖u i‖ ^ 2 := by
  rw [← complexLp_integral_norm_sq]
  calc
    _ = ∫ z : Fin n → X, ‖∏ i, u i (z i)‖ ^ 2 ∂Measure.pi μ :=
      integral_congr_ae ((l2PiProductVector_coeFn μ u).mono (fun z hz => congrArg (fun c : ℂ => ‖c‖
          ^ 2) hz))
    _ = ∫ z : Fin n → X, ∏ i, ‖u i (z i)‖ ^ 2 ∂Measure.pi μ := by simp only [norm_prod,
                                                                    Finset.prod_pow]
    _ = ∏ i, ∫ x, ‖u i x‖ ^ 2 ∂μ i := integral_fintype_prod_eq_prod (μ := μ) (fun i x => ‖u i x‖ ^
        2)
    _ = _ := by simp only [complexLp_integral_norm_sq]

theorem l2PiProductVector_norm (u : ∀ i, Lp ℂ 2 (μ i)) :
    ‖l2PiProductVector μ u‖ = ∏ i, ‖u i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg (u i)))).mp
  simpa only [Finset.prod_pow] using l2PiProductVector_norm_sq μ u

theorem l2PullbackEquiv_symm_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {ν : Measure A} {η : Measure B} (e : A ≃ᵐ B) (he : MeasurePreserving e ν η)
    (F : Lp ℂ 2 ν) :
    (l2PullbackEquiv e he).symm F = Lp.compMeasurePreserving e.symm (he.symm e) F := by
  apply (l2PullbackEquiv e he).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change F = Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) F)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hi : (e.symm : B → A) ∘ e = id := by funext a; exact e.symm_apply_apply a
  simp only [hi, Lp.compMeasurePreserving_id_apply]

theorem l2PiCoordinateEquiv_coeFn {m : ℕ} (ν : Fin (m + 1) → Measure X)
    [∀ i, SigmaFinite (ν i)] (i : Fin (m + 1)) (F : Lp ℂ 2 (Measure.pi ν)) :
    (l2PiCoordinateEquiv ν i F : X × (Fin m → X) → ℂ)
      =ᵐ[(ν i).prod (Measure.pi (fun j => ν (i.succAbove j)))]
      (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ => X) i).symm p)) := by
  unfold l2PiCoordinateEquiv
  rw [l2PullbackEquiv_symm_apply]
  exact Lp.coeFn_compMeasurePreserving F ((measurePreserving_piFinSuccAbove ν i).symm _)

theorem l2PiProductVector_split {m : ℕ} (ν : Fin (m + 1) → Measure X)
    [∀ i, SigmaFinite (ν i)] (i : Fin (m + 1)) (u : ∀ j, Lp ℂ 2 (ν j)) :
    l2PiCoordinateEquiv ν i (l2PiProductVector ν u) =
      l2ProductVector (u i) (l2PiProductVector (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove
          j))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => X) i
  have he := l2PiCoordinateEquiv_coeFn ν i (l2PiProductVector ν u)
  have hp := ((measurePreserving_piFinSuccAbove ν i).symm e).quasiMeasurePreserving.ae_eq_comp
    (l2PiProductVector_coeFn ν u)
  have hsplit := he.trans hp
  let ut := l2PiProductVector (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove j))
  have ht := (quasiMeasurePreserving_snd (μ := ν i)
    (ν := Measure.pi (fun j => ν (i.succAbove j)))).ae_eq_comp
    (l2PiProductVector_coeFn (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove j)))
  apply Lp.ext
  filter_upwards [hsplit, l2ProductVector_coeFn (u i) ut, ht] with p hs hh ht
  rw [hs, hh]
  change (∏ j, u j ((e.symm p) j)) = u i p.1 * ut p.2
  change ut p.2 = ∏ j, u (i.succAbove j) (p.2 j) at ht
  rw [ht, Fin.prod_univ_succAbove (fun j => u j ((e.symm p) j)) i]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem l2PiCoordinateOperator_pure {m : ℕ} (ν : Fin (m + 1) → Measure X)
    [∀ i, SigmaFinite (ν i)] (i : Fin (m + 1))
    (A : Lp ℂ 2 (ν i) →L[ℂ] Lp ℂ 2 (ν i)) (u : ∀ j, Lp ℂ 2 (ν j)) :
    l2PiCoordinateOperator ν i A (l2PiProductVector ν u) =
      l2PiProductVector ν (Function.update u i (A (u i))) := by
  apply (l2PiCoordinateEquiv ν i).injective
  change l2PiCoordinateEquiv ν i ((l2PiCoordinateEquiv ν i).symm
    (l2ProductLeftOperator A (l2PiCoordinateEquiv ν i (l2PiProductVector ν u)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, l2PiProductVector_split,
    l2ProductLeftOperator_pure, l2PiProductVector_split]
  congr 1
  · simp
  · congr 1
    funext j
    simp []

theorem continuous_l2PiProductVector {X : Type*} [MeasurableSpace X] (d : ℕ)
    (ν : Fin d → Measure X) [∀ i, SigmaFinite (ν i)] :
    Continuous (l2PiProductVector ν) := by
  induction d with
  | zero =>
    have hh : l2PiProductVector ν = fun _ => l2PiProductVector ν (fun i => Fin.elim0 i) := by
      funext u
      congr 1
      exact Subsingleton.elim _ _
    rw [hh]
    exact continuous_const
  | succ d ih =>
    let i : Fin (d+1) := 0
    let E := l2PiCoordinateEquiv ν i
    have ht : Continuous (fun u : ∀ j, Lp ℂ 2 (ν j) =>
        l2PiProductVector (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove j))) :=
      (ih _).comp (continuous_pi (fun j => continuous_apply (i.succAbove j)))
    have hp : Continuous (fun u : ∀ j, Lp ℂ 2 (ν j) =>
        l2ProductVector (u i)
          (l2PiProductVector (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove j)))) :=
      ((l2ProductContinuousBilinear (μ := ν i)
        (ν := Measure.pi (fun j => ν (i.succAbove j)))).continuous.comp
          (continuous_apply i)).clm_apply ht
    have he : l2PiProductVector ν = fun u => E.symm
        (l2ProductVector (u i)
          (l2PiProductVector (fun j => ν (i.succAbove j)) (fun j => u (i.succAbove j)))) := by
      funext u
      apply E.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact l2PiProductVector_split ν i u
    rw [he]
    exact E.symm.continuous.comp hp

end
end GinibrePoincare
