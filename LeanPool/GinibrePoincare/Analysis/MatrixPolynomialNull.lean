/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixPolynomialNull.lean.
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

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Nullity of nonzero complex polynomial zero sets

Finite products of atomless complex measures assign zero mass to every
nonzero multivariate polynomial's zero set. This is proved by induction on
the number of variables and one-dimensional finiteness of polynomial roots.
-/

@[expose] public section
open MeasureTheory MvPolynomial

namespace GinibrePoincare
noncomputable section

theorem complexPolynomial_eval_ne_zero_ae (μ : Measure ℂ) [NullSingletonClass μ]
    (p : Polynomial ℂ) (hp : p ≠ 0) : ∀ᵐ z ∂μ, p.eval z ≠ 0 := by
  rw [ae_iff]
  simpa [Polynomial.IsRoot.def] using (Polynomial.finite_setOfPred_isRoot hp).measure_zero μ

theorem complexMvPolynomial_fin_eval_ne_zero_ae (μ : Measure ℂ)
    [SigmaFinite μ] [NullSingletonClass μ] (d : ℕ)
    (p : MvPolynomial (Fin d) ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin d => μ), MvPolynomial.eval z p ≠ 0 := by
  induction d with
  | zero =>
    filter_upwards with z
    intro hz
    apply hp
    apply MvPolynomial.funext
    intro w
    have hw : w = z := Subsingleton.elim _ _
    simpa [hw] using hz
  | succ d ih =>
    let q := MvPolynomial.finSuccEquiv ℂ d p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.finSuccEquiv ℂ d).injective (by simpa [q] using h)
    obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hq (AddMonoidAlgebra.ext (Finsupp.ext fun k => by simpa using h k))
    have htail : ∀ᵐ y ∂Measure.pi (fun _ : Fin d => μ),
        ∀ᵐ x ∂μ, MvPolynomial.eval (Fin.cons x y) p ≠ 0 := by
      filter_upwards [ih (q.coeff k) hk] with y hy
      have hmap : q.map (MvPolynomial.eval y) ≠ 0 := by
        intro hz
        have hc := congrArg (fun f : Polynomial ℂ => f.coeff k) hz
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy hc
      simpa only [MvPolynomial.eval_eq_eval_mv_eval'] using
        complexPolynomial_eval_ne_zero_ae μ (q.map (MvPolynomial.eval y)) hmap
    have hm : MeasurableSet {z : ℂ × (Fin d → ℂ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} := by
      have hc : Continuous (fun z : ℂ × (Fin d → ℂ) =>
          (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ)) := by
        fun_prop
      exact ((MvPolynomial.continuous_eval p).comp hc).measurable (measurableSet_singleton 0).compl
    have hprod : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : Fin d => μ)),
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr htail)
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => μ) 0
    have he := hpres.quasiMeasurePreserving.ae hprod
    convert he using 1
    ext z
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

/-- Arbitrary finite index version, suitable for matrix-entry polynomials. -/
theorem complexMvPolynomial_eval_ne_zero_ae {ι : Type*} [Fintype ι]
    (μ : Measure ℂ) [SigmaFinite μ] [NullSingletonClass μ]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂Measure.pi (fun _ : ι => μ), MvPolynomial.eval z p ≠ 0 := by
  let e := Fintype.equivFin ι
  let q := MvPolynomial.renameEquiv ℂ e p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.renameEquiv ℂ e).injective (by simpa [q] using h)
  have h := complexMvPolynomial_fin_eval_ne_zero_ae μ (Fintype.card ι) q hq
  have he := (measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => μ)
      e).quasiMeasurePreserving.ae h
  convert he using 1
  ext z
  simp [q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply, Function.comp_def]

end
end GinibrePoincare
