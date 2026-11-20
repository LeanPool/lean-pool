/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryEntropyPiTensorization.lean.
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
public import LeanPool.GinibrePoincare.Analysis.IntegralEntropyTensorization
public import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Alternative Bakry Emery entropy pi tensorization

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEntropyPiCoordinate_measurable`, `bakryEntropyPi_tensorization_bounded`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

theorem bakryEntropy_fiber_integrable_bounded {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α × β → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ p, |f p| ≤ C) :
    Integrable (fun x => squareEntropy ν (fun y => f (x, y))) μ := by
  have hs (p : α × β) : f p^2 ∈ Icc (0 : ℝ) (C^2) := by
    constructor
    · positivity
    · nlinarith [sq_abs (f p), abs_nonneg (f p), hb p]
  have hlog := integrable_mul_log_of_bounded_nonneg (μ.prod ν) _ (hf.pow_const 2) (C^2) hs
  have hAm : Measurable (fiberSquareMoment ν f) :=
    (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hAb (x : α) : fiberSquareMoment ν f x ∈ Icc (0 : ℝ) (C^2) := by
    constructor
    · exact fiberSquareMoment_nonneg ν f x
    · have hi : Integrable (fun y => f (x, y)^2) ν :=
        memLp_one_iff_integrable.mp (memLp_of_bounded
          (Filter.Eventually.of_forall (fun y => hs (x, y)))
          ((hf.pow_const 2).comp measurable_prodMk_left).aestronglyMeasurable 1)
      simpa [fiberSquareMoment] using integral_mono hi (integrable_const (C^2)) (fun y => (hs (x,
          y)).2)
  exact hlog.integral_prod_left.sub
    (integrable_mul_log_of_bounded_nonneg μ _ hAm (C^2) hAb)

theorem bakryEntropy_fiber_measurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hf : Measurable f) :
    Measurable (fun x => squareEntropy ν (fun y => f (x, y))) := by
  have hs : Measurable (fun x => ∫ y, f (x, y)^2 ∂ν) :=
    (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hl : Measurable (fun x => ∫ y, f (x, y)^2 * Real.log (f (x, y)^2) ∂ν) :=
    ((Real.continuous_mul_log.measurable.comp (hf.pow_const
        2))).stronglyMeasurable.integral_prod_right'.measurable
  exact hl.sub (Real.continuous_mul_log.measurable.comp hs)

/-- The `i`-th conditional square entropy of `f` at `x`: the `squareEntropy` with respect to
`μ i` of `f` as a function of the `i`-th coordinate, the other coordinates frozen at `x`. -/
def bakryEntropyPiCoordinate {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [DecidableEq ι] (μ : ∀ i, Measure (α i)) (f : (∀ i, α i) → ℝ) (i : ι)
    (x : ∀ i, α i) : ℝ := squareEntropy (μ i) (fun y => f (Function.update x i y))

theorem bakryEntropyPiCoordinate_measurable {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [DecidableEq ι] (μ : ∀ i, Measure (α i))
    [∀ i, SFinite (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f) (i : ι) :
    Measurable (bakryEntropyPiCoordinate μ f i) :=
  bakryEntropy_fiber_measurable (μ i) (fun p => f (Function.update p.1 i p.2))
    (hf.comp measurable_update')

theorem bakryEntropyPiCoordinate_integrable {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [DecidableEq ι] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (i : ι) :
    Integrable (bakryEntropyPiCoordinate μ f i) (Measure.pi μ) :=
  bakryEntropy_fiber_integrable_bounded (Measure.pi μ) (μ i)
    (fun p => f (Function.update p.1 i p.2)) (hf.comp measurable_update') C hC (fun _ => hb _)

theorem bakryEntropyFin_step (n : ℕ) (α : Fin (n + 1) → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi μ) f ≤
      (∫ a, squareEntropy (Measure.pi (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j)))
        (fun x => f ((0 : Fin (n+1)).insertNth a x)) ∂μ 0) +
      (∫ x, squareEntropy (μ 0) (fun a => f ((0 : Fin (n+1)).insertNth a x))
        ∂Measure.pi (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j))) := by
  let e := MeasurableEquiv.piFinSuccAbove α (0 : Fin (n+1))
  have hp := (measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))).symm e
  have hg : Measurable (fun p => f (e.symm p)) := hf.comp e.symm.measurable
  have he : squareEntropy (Measure.pi μ) f =
      squareEntropy ((μ 0).prod (Measure.pi (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j))))
        (fun p => f (e.symm p)) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ hp.measurable.aemeasurable f
      (hf.pow_const 2).aestronglyMeasurable
      (Real.continuous_mul_log.measurable.comp (hf.pow_const 2)).aestronglyMeasurable
  rw [he]
  exact squareEntropy_prod_tensorization_bounded _ _ _ hg C hC (fun p => hb _)

theorem bakryEntropyFin_coordinate_integral (n : ℕ) (α : Fin (n + 1) → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (i : Fin (n + 1)) :
    (∫ x, bakryEntropyPiCoordinate μ f i x ∂Measure.pi μ) =
      ∫ x, squareEntropy (μ i) (fun a => f (i.insertNth a x))
        ∂Measure.pi (fun j : Fin n => μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove α i
  have hp := (measurePreserving_piFinSuccAbove μ i).symm e
  have hi := hp.integrable_comp_of_integrable (bakryEntropyPiCoordinate_integrable μ f hf C hC hb i)
  rw [← hp.integral_comp e.symm.measurableEmbedding (bakryEntropyPiCoordinate μ f i)]
  rw [integral_prod_symm (fun p => bakryEntropyPiCoordinate μ f i (e.symm p)) hi]
  change (∫ x, (∫ a, squareEntropy (μ i)
    (fun y => f (Function.update (i.insertNth a x) i y)) ∂μ i)
      ∂Measure.pi (fun j : Fin n => μ (i.succAbove j))) = _
  simp_rw [Fin.update_insertNth]
  simp

theorem bakryEntropyFin_tail_coordinate_integral (n : ℕ) (α : Fin (n + 1) → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (j : Fin n) :
    (∫ a, (∫ x, bakryEntropyPiCoordinate (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j))
      (fun x => f ((0 : Fin (n+1)).insertNth a x)) j x
      ∂Measure.pi (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j))) ∂μ 0) =
    ∫ x, bakryEntropyPiCoordinate μ f ((0 : Fin (n+1)).succAbove j) x ∂Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove α (0 : Fin (n+1))
  have hp := (measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))).symm e
  have hi := hp.integrable_comp_of_integrable
    (bakryEntropyPiCoordinate_integrable μ f hf C hC hb ((0 : Fin (n+1)).succAbove j))
  rw [← hp.integral_comp e.symm.measurableEmbedding
    (bakryEntropyPiCoordinate μ f ((0 : Fin (n+1)).succAbove j))]
  rw [integral_prod (fun p => bakryEntropyPiCoordinate μ f ((0 : Fin (n+1)).succAbove j) (e.symm p))
      hi]
  change (∫ a, (∫ x, squareEntropy (μ ((0 : Fin (n+1)).succAbove j))
    (fun y => f ((0 : Fin (n+1)).insertNth a (Function.update x j y))) ∂_) ∂_) =
    ∫ a, (∫ x, squareEntropy (μ ((0 : Fin (n+1)).succAbove j))
      (fun y => f (Function.update ((0 : Fin (n+1)).insertNth a x) ((0 : Fin (n+1)).succAbove j) y))
          ∂_) ∂_
  simp_rw [Fin.insertNth_update]

theorem bakryEntropyFin_tail_coordinate_outer_integrable (n : ℕ) (α : Fin (n + 1) → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (j : Fin n) :
    Integrable (fun a => ∫ x, bakryEntropyPiCoordinate (fun j : Fin n => μ ((0 : Fin
        (n+1)).succAbove j))
      (fun x => f ((0 : Fin (n+1)).insertNth a x)) j x
      ∂Measure.pi (fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j))) (μ 0) := by
  let e := MeasurableEquiv.piFinSuccAbove α (0 : Fin (n+1))
  have hp := (measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))).symm e
  have hi := hp.integrable_comp_of_integrable
    (bakryEntropyPiCoordinate_integrable μ f hf C hC hb ((0 : Fin (n+1)).succAbove j))
  have hh := hi.integral_prod_left
  change Integrable (fun a => ∫ x, squareEntropy (μ ((0 : Fin (n+1)).succAbove j))
    (fun y => f (Function.update ((0 : Fin (n+1)).insertNth a x) ((0 : Fin (n+1)).succAbove j) y))
        ∂_) (μ 0) at hh
  simpa only [bakryEntropyPiCoordinate, Fin.insertNth_update] using hh

theorem bakryEntropyFin_tensorization_bounded : ∀ (n : ℕ) (α : Fin n → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ), Measurable f →
    ∀ (C : ℝ), 0 ≤ C → (∀ x, |f x| ≤ C) →
    squareEntropy (Measure.pi μ) f ≤ ∑ i, ∫ x, bakryEntropyPiCoordinate μ f i x ∂Measure.pi μ := by
  intro n
  induction n with
  | zero =>
    intro α hα μ hμ f hf C hC hb
    have he : ∀ x : (∀ i, α i), f x = f (fun i => Fin.elim0 i) :=
      fun x => congrArg f (Subsingleton.elim _ _)
    simp [squareEntropy, he, Measure.real]
  | succ n ih =>
    intro α hα μ hμ f hf C hC hb
    let e := MeasurableEquiv.piFinSuccAbove α (0 : Fin (n+1))
    let ν := fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j)
    have hg : Measurable (fun p => f (e.symm p)) := hf.comp e.symm.measurable
    have hleft : Integrable (fun a => squareEntropy (Measure.pi ν)
        (fun x => f ((0 : Fin (n+1)).insertNth a x))) (μ 0) :=
      bakryEntropy_fiber_integrable_bounded (μ 0) (Measure.pi ν) _ hg C hC (fun p => hb _)
    have hright : Integrable (fun a => ∑ j : Fin n, ∫ x, bakryEntropyPiCoordinate ν
        (fun x => f ((0 : Fin (n+1)).insertNth a x)) j x ∂Measure.pi ν) (μ 0) := by
      apply MeasureTheory.integrable_finsetSum
      intro j hj
      exact bakryEntropyFin_tail_coordinate_outer_integrable n α μ f hf C hC hb j
    have hineq := integral_mono hleft hright (fun a =>
      ih (fun j => α ((0 : Fin (n+1)).succAbove j)) ν
        (fun x => f ((0 : Fin (n+1)).insertNth a x))
        (hg.comp measurable_prodMk_left) C hC (fun x => hb _))
    rw [integral_finsetSum Finset.univ (fun j hj =>
      bakryEntropyFin_tail_coordinate_outer_integrable n α μ f hf C hC hb j)] at hineq
    simp_rw [bakryEntropyFin_tail_coordinate_integral n α μ f hf C hC hb] at hineq
    have hstep := bakryEntropyFin_step n α μ f hf C hC hb
    rw [← bakryEntropyFin_coordinate_integral n α μ f hf C hC hb (0 : Fin (n+1))] at hstep
    rw [Fin.sum_univ_succAbove _ (0 : Fin (n+1))]
    linarith

theorem bakryEntropyPi_tensorization_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, α i) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi μ) f ≤ ∑ i, ∫ x, bakryEntropyPiCoordinate μ f i x ∂Measure.pi μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T := MeasurableEquiv.piCongrLeft α e
  have hp := measurePreserving_piCongrLeft μ e
  have hT (x : ∀ j, α (e j)) (j : Fin (Fintype.card ι)) (y : α (e j)) :
      T (Function.update x j y) = Function.update (T x) (e j) y := by
    apply T.symm.injective
    rw [T.symm_apply_apply]
    funext k
    change Function.update x j y k = Function.update (T x) (e j) y (e k)
    by_cases h : k = j
    · subst k; simp
    · have hek : e k ≠ e j := fun he => h (e.injective he)
      rw [Function.update_of_ne h, Function.update_of_ne hek]
      exact (Equiv.piCongrLeft_apply_apply α e x k).symm
  have h := bakryEntropyFin_tensorization_bounded (Fintype.card ι) (fun j => α (e j))
    (fun j => μ (e j)) (fun x => f (T x)) (hf.comp T.measurable) C hC (fun x => hb _)
  have hent : squareEntropy (Measure.pi μ) f =
      squareEntropy (Measure.pi (fun j => μ (e j))) (fun x => f (T x)) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.measurable.aemeasurable f
      (hf.pow_const 2).aestronglyMeasurable
      (Real.continuous_mul_log.measurable.comp (hf.pow_const 2)).aestronglyMeasurable
  rw [← hent] at h
  have hcoord (j : Fin (Fintype.card ι)) :
      (∫ x, bakryEntropyPiCoordinate (fun j => μ (e j)) (fun x => f (T x)) j x
        ∂Measure.pi (fun j => μ (e j))) =
      ∫ x, bakryEntropyPiCoordinate μ f (e j) x ∂Measure.pi μ := by
    rw [← hp.integral_comp T.measurableEmbedding (bakryEntropyPiCoordinate μ f (e j))]
    simp only [bakryEntropyPiCoordinate, hT]
    rfl
  simp_rw [hcoord] at h
  rw [e.sum_comp (fun i => ∫ x, bakryEntropyPiCoordinate μ f i x ∂Measure.pi μ)] at h
  exact h

end
end GinibrePoincare
