/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.InftyToQ
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.HomogenizationErrorControl
public import Mathlib.Analysis.MeanInequalities

/-!
# Breakdown

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the localization breakdown `e.mathcal.E.breakdown`

This file is a proved local provider for the display `e.mathcal.E.breakdown` of
ABK26, the first displayed step in the proof of the localization lemma
`l.localization.mathcalE`.  It is a provider endpoint only: the localization lemma
itself additionally needs the comparator normalization, the `λ`-gate, the
`J`-injection, the good-event aggregation and the bad-event factorization, none of
which is in this file.

Applying `e.mathcalE.infty.to.q` with `p = 2ds^{-1}` and `q = 2` and squaring, the
source records

> `𝓔_{s,∞,2}(□_m; a_m, σ_m)^2
>  ≤ c_{2s} Σ_{l=-∞}^m 3^{-s(m-l)}
>  (⨍_{z ∈ 3^l ℤ^d ∩ □_m} max_{|e|=1} J(z+□_l, σ_m^{-1/2}e, σ_m^{1/2}e; a_m)^{d/s})^{s/d}
>  + c_{2s} Σ_{l=-∞}^m 3^{-s(m-l)}
>  (⨍_{z ∈ 3^l ℤ^d ∩ □_m} max_{|e|=1} J(z+□_l, σ_m^{-1/2}e, σ_m^{1/2}e; a_m^t)^{d/s})^{s/d}`,

where `c_{2s} = 1 - 3^{-2s}` is `Homogenization.Book.Ch02.geometricDiscount s 2`.

## Main results

* `homogenizationErrorOnCube_sq_le_breakdown`: the display, pathwise on
  CoarseGraining's literal `𝓔_{s,∞,2}` carrier, for every triadic coefficient
  family and every constant comparator.  The two right-hand terms carry the
  coefficient `(1/2) c_{2s}`: the `1/2` is the weight of the block splitting,
  retained rather than discarded, and it cancels the doubling of the frame-sup
  legs, so that the conclusion is the printed display verbatim under the leg
  identification `legA = 2 · max_{|e|=1} J(·; a)` (see the frame-sup deviation
  below).
* `cutoffHomogenizationError_sq_ae_le_breakdown`: the same display transported to
  the Section 3 observable `Observable.cutoffHomogenizationError M m ⟨s, _⟩` at the
  running diffusivity `σ_m`.
* `breakdownLegA` / `breakdownLegB`, `legScaleAverage`, `breakdownLegSum`: the
  two legs and the two weighted leg sums of the display, with the A
  (`responseJ_le_breakdownLegA`, `breakdownLegA_le_of_forall_frame`,
  `legScaleAverage_smul`, `summable_breakdownLegSum_terms`, and their `B`
  twins) through which the downstream comparator normalization consumes the
  conclusion.
* `breakdownLegAValueSet_isotropic_eq` / `breakdownLegBValueSet_isotropic_eq` and
  `breakdownLegA_le_of_paired_bound` / `breakdownLegB_le_of_paired_bound`: at the
  isotropic comparator `σ Id` — the only comparator on the localization wire — the
  two legs are exactly the manuscript's paired families
  `J(z+□_l, σ^{-1/2}v, σ^{1/2}v; a)` and `J(z+□_l, σ^{-1/2}v, σ^{1/2}v; a^t)` at
  `v = e₁ ∓ e₂`, with `|v|^2 ≤ 2` (`vecNormSq_frameLegAVec_le`,
  `vecNormSq_frameLegBVec_le`).  The loadings are written in the Section 3
  carrier's own spelling `Observable.inverseSqrtLoad` / `Observable.sqrtLoad`.

## Source correspondence and disclosed deviations

* `d.mathcal.E` is built from the *block* functional `𝐉(R, 𝐀_0^{-1/2}e,
  𝐀_0^{1/2}e; a)` with `e` a unit vector of the doubled `2d`-dimensional space;
  the two scalar legs of the printed display arise from it through the
  unconditional block splitting `doubledResponseJ = ½ J(·;a) + ½ J(·;a^t)`
  (`Homogenization.Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum`).
  Accordingly `breakdownLegA` / `breakdownLegB` are the suprema of the scalar
  responses over the *doubled* unit sphere; at the scalar comparator used on
  the localization wire the loading vector `v = e₁ ∓ e₂` has Euclidean length
  up to `√2`, so each leg is **twice** the printed `max_{|e|=1}` object.  This
  file carries the frame-sup form.
  **The doubling and the `1/2` of the splitting cancel here, and the
  cancellation is performed rather than asserted.**  The `1/2` of
  `doubledResponseJ = ½ J(·;a) + ½ J(·;a^t)` is retained in
  `normalizedBlockResponseMax_le_breakdownLegA_add_breakdownLegB` (which is
  therefore a bound by `½ (legA + legB)`, not by `legA + legB`), and it is
  carried through the per-scale power mean by its positive homogeneity
  (`legScaleAverage_smul`) into the constant of both endpoints.
  The paired shape and the size bound `|v|^2 ≤ 2` are *proved* here at the
  isotropic comparator (`breakdownLegAValueSet_isotropic_eq` and its twin), so
  the deviation is exhibited rather than asserted.  What the cancellation
  removes is the *second*, spurious factor `2` — the one that came from the
  discarded splitting weight and had no source warrant at all.
* The gap is an artifact of the printed range, not of the mathematics: what the
  breakdown actually needs from the embedding is its one-scale counting core,
  which carries no window on `s` at all.  This file therefore consumes
  `ErrorComparison.scaleResponseAtScale_infinity_rpow_le_card_mul_finite`
  (binders `0 < p`, `0 < q` only) and performs the outer geometric scale sum
  directly, rather than the packaged display
  `ErrorComparison.homogenizationError_infinity_le_finite`, whose retained
  (and, in that file, unused) binder `s < 1` would exclude the endpoint.  The
  resulting statement holds on all of `s ∈ (0, 1]`, so the recorded source gap
  is refuted in Lean rather than inherited.
* Consequently the inner and outer power-mean exponents are the printed `d/s`
  and `s/d`, and the geometric weight is the printed `3^{-s(m-l)}`.
* No `𝓔_{s,p,∞}` branch and no `n < m` truncation occurs.
* The deterministic statement `homogenizationErrorOnCube_sq_le_breakdown` is
  genuinely pathwise: it holds for every coefficient family and every
  comparator, with no exceptional set.  The Section 3 endpoint is nevertheless
  almost sure, and its null set sits inside the `s` binder, because the
  observable `Observable.cutoffHomogenizationError` is an verified *measurable
  representative* which only almost everywhere equals CoarseGraining's literal
  `𝓔_{s,∞,2}`
  (`Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube`), and
  that identification is itself indexed by `s`.  The a.e. quantifier here is
  therefore forced by the carrier, not by the argument; the `s`-uniform form
  would require an `s`-uniform representative identification, which the
  Observable layer does not supply.

## References

* ABK26, `e.mathcal.E.breakdown`, inside `l.localization.mathcalE`.
* ABK26, `e.mathcalE.infty.to.q` (`d.mathcal.E`).
-/

namespace Algsuperdiff.Section3.Provider.Localization

-- `_root_` is load-bearing: `Algsuperdiff.Section3.Provider.Homogenization` is a
-- live sibling namespace, so a bare `open Homogenization` would resolve to it
-- once any `Provider.Homogenization` module enters this file's import closure.
-- (The closure currently contains none, so the qualification is forward-defensive
-- rather than presently required; the bare-open counterfactual shadows five
-- identifiers as soon as such a module is imported.)
open _root_.HCPolySupport
open _root_.MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Real-power and finite-average bookkeeping -/

/-- `Real.rpow` at the exponent `2` is the square.

This duplicates Mathlib's `Real.rpow_two`, and is proved from it; it exists
only for the spelling.  Mathlib states the identity in the `HPow` notation as
`x ^ (2 : ℝ) = x ^ 2`, whereas this file (like the proved
`Provider/ErrorComparison/InftyToQ.lean` it consumes) writes every real power
as an explicit `Real.rpow` application, and `rw` will not match the notation
against the application. -/
private theorem rpow_two (x : ℝ) : Real.rpow x 2 = x ^ 2 := Real.rpow_two x

/-- A `finsetAverageReal` is monotone in its integrand on the averaging set. -/
private theorem finsetAverageReal_mono {α : Type*} (t : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ t, f x ≤ g x) :
    Book.Ch02.finsetAverageReal t f ≤ Book.Ch02.finsetAverageReal t g := by
  unfold Book.Ch02.finsetAverageReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg) (by positivity)

/-- Minkowski's inequality for the uniform average over a finite set: for `1 ≤ P`
and nonnegative integrands, `(⨍ (f+g)^P)^{1/P} ≤ (⨍ f^P)^{1/P} + (⨍ g^P)^{1/P}`. -/
private theorem finsetAverageReal_rpow_add_le {α : Type*} (t : Finset α) {P : ℝ}
    (hP : 1 ≤ P) (f g : α → ℝ) (hf : ∀ x ∈ t, 0 ≤ f x) (hg : ∀ x ∈ t, 0 ≤ g x) :
    Real.rpow
        (Book.Ch02.finsetAverageReal t (fun x => Real.rpow (f x + g x) P)) (1 / P) ≤
      Real.rpow (Book.Ch02.finsetAverageReal t (fun x => Real.rpow (f x) P)) (1 / P) +
        Real.rpow (Book.Ch02.finsetAverageReal t (fun x => Real.rpow (g x) P))
          (1 / P) := by
  classical
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  set c : ℝ := ((t.card : ℝ))⁻¹ with hc
  have hcnn : (0 : ℝ) ≤ c := by positivity
  have hfac : ∀ h : α → ℝ, (∀ x ∈ t, 0 ≤ h x) →
      Real.rpow (Book.Ch02.finsetAverageReal t h) (1 / P) =
        Real.rpow c (1 / P) * Real.rpow (∑ x ∈ t, h x) (1 / P) := by
    intro h hh
    have hrw : Book.Ch02.finsetAverageReal t h = c * ∑ x ∈ t, h x := rfl
    rw [hrw, ErrorComparison.mul_rpow' hcnn (Finset.sum_nonneg hh) (1 / P)]
  have hsum : ∀ x ∈ t, (0 : ℝ) ≤ Real.rpow (f x + g x) P := fun x hx =>
    Real.rpow_nonneg (add_nonneg (hf x hx) (hg x hx)) _
  have hf' : ∀ x ∈ t, (0 : ℝ) ≤ Real.rpow (f x) P := fun x hx =>
    Real.rpow_nonneg (hf x hx) _
  have hg' : ∀ x ∈ t, (0 : ℝ) ≤ Real.rpow (g x) P := fun x hx =>
    Real.rpow_nonneg (hg x hx) _
  rw [hfac _ hsum, hfac _ hf', hfac _ hg']
  have hmink :
      Real.rpow (∑ x ∈ t, Real.rpow (f x + g x) P) (1 / P) ≤
        Real.rpow (∑ x ∈ t, Real.rpow (f x) P) (1 / P) +
          Real.rpow (∑ x ∈ t, Real.rpow (g x) P) (1 / P) :=
    Real.Lp_add_le_of_nonneg (s := t) (f := f) (g := g) hP hf hg
  calc
    Real.rpow c (1 / P) * Real.rpow (∑ x ∈ t, Real.rpow (f x + g x) P) (1 / P) ≤
        Real.rpow c (1 / P) *
          (Real.rpow (∑ x ∈ t, Real.rpow (f x) P) (1 / P) +
            Real.rpow (∑ x ∈ t, Real.rpow (g x) P) (1 / P)) :=
      mul_le_mul_of_nonneg_left hmink (Real.rpow_nonneg hcnn _)
    _ = _ := by ring

/-! ## The two frame legs of the display -/

section Legs

variable [NeZero d]

/-- The block-normalized loading `𝐀_0^{-1/2} e` of a doubled direction `e`, split
into its two `ℝ^d` halves. -/
def frameLoadInvSqrt (a0 : Mat d) (e : FullBlockVec d) : BlockVec d :=
  ofFullBlockVec (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) e)

/-- The block-normalized loading `𝐀_0^{1/2} e` of a doubled direction `e`, split
into its two `ℝ^d` halves. -/
def frameLoadSqrt (a0 : Mat d) (e : FullBlockVec d) : BlockVec d :=
  ofFullBlockVec (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) e)

/-- The value set of the `a`-leg of `e.mathcal.E.breakdown`: the scalar responses
`J(R, ·, ·; a)` at the primal frame loadings of the doubled unit directions. -/
def breakdownLegAValueSet (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) : Set ℝ :=
  { v | ∃ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 ∧
      v = Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
        ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) }

/-- The value set of the `a^t`-leg of `e.mathcal.E.breakdown`: the scalar responses
`J(R, ·, ·; a^t)` at the adjoint frame loadings of the doubled unit directions. -/
def breakdownLegBValueSet (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) : Set ℝ :=
  { v | ∃ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 ∧
      v = Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
        ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
        ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) }

/-- The `a`-leg of `e.mathcal.E.breakdown`: the frame supremum
`max_{|e|=1} J(R, 𝐀_0^{-1/2}e, 𝐀_0^{1/2}e; a)` over the doubled unit sphere. -/
def breakdownLegA (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) : ℝ :=
  sSup (breakdownLegAValueSet R a a0)

/-- The `a^t`-leg of `e.mathcal.E.breakdown`: the frame supremum
`max_{|e|=1} J(R, 𝐀_0^{-1/2}e, 𝐀_0^{1/2}e; a^t)` over the doubled unit sphere. -/
def breakdownLegB (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) : ℝ :=
  sSup (breakdownLegBValueSet R a a0)

omit [NeZero d] in
/-- The unconditional block splitting of the doubled response at the normalized
frame loadings. -/
private theorem doubledResponseJ_frame_split (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) (e : FullBlockVec d) :
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        (frameLoadInvSqrt a0 e) (frameLoadSqrt a0 e) =
      (1 / 2 : ℝ) * Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
          ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
          ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) +
        (1 / 2 : ℝ) * Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          (a.coeffOn R).transpose
          ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
          ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) :=
  Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum (Book.Ch02.cubeDomain R)
    (a.coeffOn R) (frameLoadInvSqrt a0 e).1 (frameLoadSqrt a0 e).2
    (frameLoadInvSqrt a0 e).2 (frameLoadSqrt a0 e).1

omit [NeZero d] in
/-- Each doubled unit direction contributes to the normalized block-response value
set. -/
private theorem doubledResponseJ_mem_normalizedBlockResponseValueSet
    (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {e : FullBlockVec d} (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        (frameLoadInvSqrt a0 e) (frameLoadSqrt a0 e) ∈
      Book.Ch02.normalizedBlockResponseValueSet R a a0 :=
  ⟨e, he, rfl⟩

omit [NeZero d] in
/-- The `a`-leg is nonnegative. -/
theorem breakdownLegA_nonneg (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ breakdownLegA R a a0 := by
  refine Real.sSup_nonneg ?_
  rintro v ⟨e, -, rfl⟩
  exact Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R) (a.coeffOn R) _ _

omit [NeZero d] in
/-- The `a^t`-leg is nonnegative. -/
theorem breakdownLegB_nonneg (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ breakdownLegB R a a0 := by
  refine Real.sSup_nonneg ?_
  rintro v ⟨e, -, rfl⟩
  exact Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R)
    (a.coeffOn R).transpose _ _

omit [NeZero d] in
/-- Each `a`-leg frame value is bounded by twice the normalized block response of
the same cube. -/
private theorem legA_frame_le_two_mul_normalizedBlockResponseMax
    {Q R : TriadicCube d} {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) {e : FullBlockVec d}
    (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
        ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) ≤
      2 * Book.Ch02.normalizedBlockResponseMax R a a0 := by
  have hsplit := doubledResponseJ_frame_split R a a0 e
  have hdle :
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
          (frameLoadInvSqrt a0 e) (frameLoadSqrt a0 e) ≤
        Book.Ch02.normalizedBlockResponseMax R a a0 :=
    le_csSup
      (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
        a a0 hR)
      (doubledResponseJ_mem_normalizedBlockResponseValueSet R a a0 he)
  have hJb :
      0 ≤ Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
        ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
        ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) :=
    Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose _ _
  linarith

omit [NeZero d] in
/-- Each `a^t`-leg frame value is bounded by twice the normalized block response of
the same cube. -/
private theorem legB_frame_le_two_mul_normalizedBlockResponseMax
    {Q R : TriadicCube d} {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) {e : FullBlockVec d}
    (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
        ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
        ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) ≤
      2 * Book.Ch02.normalizedBlockResponseMax R a a0 := by
  have hsplit := doubledResponseJ_frame_split R a a0 e
  have hdle :
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
          (frameLoadInvSqrt a0 e) (frameLoadSqrt a0 e) ≤
        Book.Ch02.normalizedBlockResponseMax R a a0 :=
    le_csSup
      (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
        a a0 hR)
      (doubledResponseJ_mem_normalizedBlockResponseValueSet R a a0 he)
  have hJa :
      0 ≤ Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
        ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) :=
    Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R) (a.coeffOn R) _ _
  linarith

omit [NeZero d] in
/-- On a descendant cube the `a`-leg value set is bounded above. -/
theorem breakdownLegAValueSet_bddAbove {Q R : TriadicCube d} {k : ℤ}
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    BddAbove (breakdownLegAValueSet R a a0) := by
  refine ⟨2 * Book.Ch02.normalizedBlockResponseMax R a a0, ?_⟩
  rintro v ⟨e, he, rfl⟩
  exact legA_frame_le_two_mul_normalizedBlockResponseMax a a0 hR he

omit [NeZero d] in
/-- On a descendant cube the `a^t`-leg value set is bounded above. -/
theorem breakdownLegBValueSet_bddAbove {Q R : TriadicCube d} {k : ℤ}
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    BddAbove (breakdownLegBValueSet R a a0) := by
  refine ⟨2 * Book.Ch02.normalizedBlockResponseMax R a a0, ?_⟩
  rintro v ⟨e, he, rfl⟩
  exact legB_frame_le_two_mul_normalizedBlockResponseMax a a0 hR he

omit [NeZero d] in
/-- Every `a`-leg frame value of a descendant cube is bounded by the leg. -/
theorem responseJ_le_breakdownLegA {Q R : TriadicCube d} {k : ℤ}
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) {e : FullBlockVec d}
    (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
        ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
        ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) ≤
      breakdownLegA R a a0 :=
  le_csSup (breakdownLegAValueSet_bddAbove a a0 hR) ⟨e, he, rfl⟩

omit [NeZero d] in
/-- Every `a^t`-leg frame value of a descendant cube is bounded by the leg. -/
theorem responseJ_le_breakdownLegB {Q R : TriadicCube d} {k : ℤ}
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) {e : FullBlockVec d}
    (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
        ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
        ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) ≤
      breakdownLegB R a a0 :=
  le_csSup (breakdownLegBValueSet_bddAbove a a0 hR) ⟨e, he, rfl⟩

omit [NeZero d] in
/-- A uniform bound on the `a`-leg frame values bounds the leg.  This is the
entry point through which the downstream comparator normalization converts a
per-frame response estimate into an estimate on the leg. -/
theorem breakdownLegA_le_of_forall_frame (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
          ((frameLoadInvSqrt a0 e).1 - (frameLoadSqrt a0 e).2)
          ((frameLoadSqrt a0 e).1 - (frameLoadInvSqrt a0 e).2) ≤ c) :
    breakdownLegA R a a0 ≤ c := by
  refine Real.sSup_le ?_ hc
  rintro v ⟨e, he, rfl⟩
  exact h e he

omit [NeZero d] in
/-- A uniform bound on the `a^t`-leg frame values bounds the leg. -/
theorem breakdownLegB_le_of_forall_frame (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
          ((frameLoadSqrt a0 e).2 + (frameLoadInvSqrt a0 e).1)
          ((frameLoadSqrt a0 e).1 + (frameLoadInvSqrt a0 e).2) ≤ c) :
    breakdownLegB R a a0 ≤ c := by
  refine Real.sSup_le ?_ hc
  rintro v ⟨e, he, rfl⟩
  exact h e he

omit [NeZero d] in
/-- The `a`-leg of a descendant cube is bounded by twice its normalized block
response. -/
theorem breakdownLegA_le_two_mul_normalizedBlockResponseMax {Q R : TriadicCube d}
    {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    breakdownLegA R a a0 ≤ 2 * Book.Ch02.normalizedBlockResponseMax R a a0 :=
  breakdownLegA_le_of_forall_frame R a a0
    (by linarith [Book.Ch02.normalizedBlockResponseMax_nonneg R a a0])
    fun e he => legA_frame_le_two_mul_normalizedBlockResponseMax a a0 hR he

omit [NeZero d] in
/-- The `a^t`-leg of a descendant cube is bounded by twice its normalized block
response. -/
theorem breakdownLegB_le_two_mul_normalizedBlockResponseMax {Q R : TriadicCube d}
    {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    breakdownLegB R a a0 ≤ 2 * Book.Ch02.normalizedBlockResponseMax R a a0 :=
  breakdownLegB_le_of_forall_frame R a a0
    (by linarith [Book.Ch02.normalizedBlockResponseMax_nonneg R a a0])
    fun e he => legB_frame_le_two_mul_normalizedBlockResponseMax a a0 hR he

omit [NeZero d] in
/-- **The per-cube two-leg split.**  The block functional from which
`𝓔_{s,p,q}` is built is bounded by **half** the sum of the two scalar frame legs,
because the doubled response splits unconditionally into the primal and adjoint
halves *with the weight `1/2` on each*
(`Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum`).

The `1/2` is the arithmetic content of the splitting and is retained here: the
weaker bound by the full sum — obtained by discarding each `1/2` against
`responseJ_nonneg` — would double the constant of `e.mathcal.E.breakdown` against
the printed display.  Retaining the `1/2` uses *strictly fewer* inputs than
discarding it: only the splitting identity and the two frame bounds
`responseJ_le_breakdownLegA` / `responseJ_le_breakdownLegB`, and no
nonnegativity of the individual scalar responses. -/
theorem normalizedBlockResponseMax_le_breakdownLegA_add_breakdownLegB
    {Q R : TriadicCube d} {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    Book.Ch02.normalizedBlockResponseMax R a a0 ≤
      (1 / 2 : ℝ) * (breakdownLegA R a a0 + breakdownLegB R a a0) := by
  refine Real.sSup_le ?_
    (by linarith [breakdownLegA_nonneg R a a0, breakdownLegB_nonneg R a a0])
  rintro x ⟨e, he, rfl⟩
  have hsplit := doubledResponseJ_frame_split R a a0 e
  have hA := responseJ_le_breakdownLegA a a0 hR he
  have hB := responseJ_le_breakdownLegB a a0 hR he
  change Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
      (frameLoadInvSqrt a0 e) (frameLoadSqrt a0 e) ≤ _
  linarith

end Legs

/-! ## The per-scale power mean and the weighted leg sums -/

/-- The per-scale power mean of a leg at the printed exponents of
`e.mathcal.E.breakdown`:
`(⨍_{z ∈ 3^k ℤ^d ∩ Q} leg(z + □_k)^{d/s})^{s/d}`. -/
def legScaleAverage (Q : TriadicCube d) (k : ℤ) (s : ℝ)
    (leg : TriadicCube d → ℝ) : ℝ :=
  Real.rpow
    (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
      (fun R => Real.rpow (leg R) ((d : ℝ) / s)))
    (s / (d : ℝ))

/-- The per-scale power mean of a nonnegative leg is nonnegative. -/
theorem legScaleAverage_nonneg (Q : TriadicCube d) (k : ℤ) (s : ℝ)
    {leg : TriadicCube d → ℝ}
    (hleg : ∀ R ∈ descendantsAtScale Q k, 0 ≤ leg R) :
    0 ≤ legScaleAverage Q k s leg :=
  Real.rpow_nonneg
    (ErrorComparison.finsetAverageReal_nonneg _ fun R hR =>
      Real.rpow_nonneg (hleg R hR) _)
    _

/-- A uniform bound on a nonnegative leg bounds its per-scale power mean. -/
theorem legScaleAverage_le_const (Q : TriadicCube d) (k : ℤ) {s : ℝ} (hs : 0 < s)
    {leg : TriadicCube d → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hleg : ∀ R ∈ descendantsAtScale Q k, 0 ≤ leg R)
    (hle : ∀ R ∈ descendantsAtScale Q k, leg R ≤ D) (hd : d ≠ 0) :
    legScaleAverage Q k s leg ≤ D := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hmul : (d : ℝ) / s * (s / (d : ℝ)) = 1 := by
    field_simp
  have havg :
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (leg R) ((d : ℝ) / s)) ≤
        Real.rpow D ((d : ℝ) / s) :=
    ErrorComparison.finsetAverageReal_le _ (Real.rpow_nonneg hD _) fun R hR =>
      Real.rpow_le_rpow (hleg R hR) (hle R hR) (by positivity)
  calc
    legScaleAverage Q k s leg ≤
        Real.rpow (Real.rpow D ((d : ℝ) / s)) (s / (d : ℝ)) :=
      Real.rpow_le_rpow
        (ErrorComparison.finsetAverageReal_nonneg _ fun R hR =>
          Real.rpow_nonneg (hleg R hR) _)
        havg (by positivity)
    _ = D := ErrorComparison.rpow_rpow_of_mul_eq_one hD hmul

/-- **Positive homogeneity of the per-scale power mean.**  The power mean
`(⨍ leg^{d/s})^{s/d}` is degree-one homogeneous in a nonnegative leg, so a
nonnegative constant factor passes through it unchanged.  This is what carries
the `1/2` of the block splitting
(`normalizedBlockResponseMax_le_breakdownLegA_add_breakdownLegB`) out of the
per-scale average and into the constant of `e.mathcal.E.breakdown`. -/
theorem legScaleAverage_smul (Q : TriadicCube d) (k : ℤ) {s : ℝ} (hs : 0 < s)
    (hd : d ≠ 0) {c : ℝ} (hc : 0 ≤ c) {leg : TriadicCube d → ℝ}
    (hleg : ∀ R ∈ descendantsAtScale Q k, 0 ≤ leg R) :
    legScaleAverage Q k s (fun R => c * leg R) =
      c * legScaleAverage Q k s leg := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hmul : (d : ℝ) / s * (s / (d : ℝ)) = 1 := by
    field_simp
  have hpt : ∀ R ∈ descendantsAtScale Q k,
      Real.rpow (c * leg R) ((d : ℝ) / s) =
        Real.rpow c ((d : ℝ) / s) * Real.rpow (leg R) ((d : ℝ) / s) :=
    fun R hR => ErrorComparison.mul_rpow' hc (hleg R hR) _
  have hsum :
      ∑ R ∈ descendantsAtScale Q k, Real.rpow (c * leg R) ((d : ℝ) / s) =
        Real.rpow c ((d : ℝ) / s) *
          ∑ R ∈ descendantsAtScale Q k, Real.rpow (leg R) ((d : ℝ) / s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hpt
  have hlhs :
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (c * leg R) ((d : ℝ) / s)) =
        ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k, Real.rpow (c * leg R) ((d : ℝ) / s) := rfl
  have hrhs :
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (leg R) ((d : ℝ) / s)) =
        ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k, Real.rpow (leg R) ((d : ℝ) / s) := rfl
  have havg0 :
      0 ≤ Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (leg R) ((d : ℝ) / s)) :=
    ErrorComparison.finsetAverageReal_nonneg _ fun R hR =>
      Real.rpow_nonneg (hleg R hR) _
  have hcp : (0 : ℝ) ≤ Real.rpow c ((d : ℝ) / s) := Real.rpow_nonneg hc _
  have havg :
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (c * leg R) ((d : ℝ) / s)) =
        Real.rpow c ((d : ℝ) / s) *
          Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
            (fun R => Real.rpow (leg R) ((d : ℝ) / s)) := by
    rw [hlhs, hrhs, hsum]
    ring
  change Real.rpow
      (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (c * leg R) ((d : ℝ) / s))) (s / (d : ℝ)) =
    c * Real.rpow
      (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (leg R) ((d : ℝ) / s))) (s / (d : ℝ))
  rw [havg, ErrorComparison.mul_rpow' hcp havg0,
    ErrorComparison.rpow_rpow_of_mul_eq_one hc hmul]

/-- **Minkowski's inequality at one scale.**  For `s ≤ 1 ≤ d` the inner exponent
`d/s` is at least one, so the per-scale power mean is subadditive in the leg. -/
theorem legScaleAverage_le_add (Q : TriadicCube d) (k : ℤ) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hd : d ≠ 0) {leg legA legB : TriadicCube d → ℝ}
    (hA : ∀ R ∈ descendantsAtScale Q k, 0 ≤ legA R)
    (hB : ∀ R ∈ descendantsAtScale Q k, 0 ≤ legB R)
    (hleg : ∀ R ∈ descendantsAtScale Q k, 0 ≤ leg R)
    (hsplit : ∀ R ∈ descendantsAtScale Q k, leg R ≤ legA R + legB R) :
    legScaleAverage Q k s leg ≤
      legScaleAverage Q k s legA + legScaleAverage Q k s legB := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hP : (1 : ℝ) ≤ (d : ℝ) / s := (one_le_div hs).mpr (hs1.trans hd1)
  have hdR : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hexp : 1 / ((d : ℝ) / s) = s / (d : ℝ) := by
    field_simp
  have hstep :
      legScaleAverage Q k s leg ≤
        Real.rpow
          (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
            (fun R => Real.rpow (legA R + legB R) ((d : ℝ) / s)))
          (s / (d : ℝ)) :=
    Real.rpow_le_rpow
      (ErrorComparison.finsetAverageReal_nonneg _ fun R hR =>
        Real.rpow_nonneg (hleg R hR) _)
      (finsetAverageReal_mono _ fun R hR =>
        Real.rpow_le_rpow (hleg R hR) (hsplit R hR) (by positivity))
      (by positivity)
  have hmink :=
    finsetAverageReal_rpow_add_le (descendantsAtScale Q k) hP legA legB hA hB
  rw [hexp] at hmink
  exact hstep.trans hmink

/-- The weighted leg sum of `e.mathcal.E.breakdown`,
`Σ_{l=-∞}^m 3^{-s(m-l)} (⨍_{z ∈ 3^l ℤ^d ∩ □_m} leg(z+□_l)^{d/s})^{s/d}`,
reindexed by the depth `j = m - l ∈ ℕ`. -/
def breakdownLegSum (m : ℤ) (s : ℝ) (leg : TriadicCube d → ℝ) : ℝ :=
  ∑' j : ℕ,
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s leg

section Assembly

variable [NeZero d]

/-- The squared `p = ∞` one-scale response is the per-scale power mean of the
normalized block response, at the manuscript exponent `p = 2ds^{-1}`. -/
private theorem scaleResponseAtScale_infinity_sq_le_legScaleAverage
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    (Book.Ch02.scaleResponseAtScale Q k .infinity a a0) ^ 2 ≤
      Real.rpow ((descendantsAtScale Q k).card : ℝ) (s / (d : ℝ)) *
        legScaleAverage Q k s
          (fun R => Book.Ch02.normalizedBlockResponseMax R a a0) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hs0 : s ≠ 0 := ne_of_gt hs
  set p : ℝ := 2 * (d : ℝ) / s with hpdef
  have hp0 : 0 < p := by
    rw [hpdef]; positivity
  have hhalf : p / 2 = (d : ℝ) / s := by
    rw [hpdef]; field_simp
  have hinv : 2 / p = s / (d : ℝ) := by
    rw [hpdef]; field_simp
  have hinv2 : 1 / p * 2 = s / (d : ℝ) := by
    rw [hpdef]; field_simp
  have hstep :=
    ErrorComparison.scaleResponseAtScale_infinity_rpow_le_card_mul_finite Q hk a a0
      hp0 (by norm_num : (0 : ℝ) < 2)
  have havg0 :
      0 ≤ Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (Book.Ch02.normalizedBlockResponseMax R a a0) (p / 2)) :=
    ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q k a a0 p
  have hfinite :
      Real.rpow (Book.Ch02.scaleResponseAtScale Q k (.finite p) a a0) 2 =
        legScaleAverage Q k s
          (fun R => Book.Ch02.normalizedBlockResponseMax R a a0) := by
    change Real.rpow (Book.Ch02.scaleResponseAtScale Q k (.finite p) a a0) 2 =
      Real.rpow
        (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (Book.Ch02.normalizedBlockResponseMax R a a0)
            ((d : ℝ) / s)))
        (s / (d : ℝ))
    rw [ErrorComparison.scaleResponseAtScale_finite_eq,
      ErrorComparison.rpow_rpow havg0, hhalf, hinv2]
  calc
    (Book.Ch02.scaleResponseAtScale Q k .infinity a a0) ^ 2 =
        Real.rpow (Book.Ch02.scaleResponseAtScale Q k .infinity a a0) 2 :=
      (rpow_two _).symm
    _ ≤ Real.rpow ((descendantsAtScale Q k).card : ℝ) (2 / p) *
          Real.rpow (Book.Ch02.scaleResponseAtScale Q k (.finite p) a a0) 2 := hstep
    _ = Real.rpow ((descendantsAtScale Q k).card : ℝ) (s / (d : ℝ)) *
          legScaleAverage Q k s
            (fun R => Book.Ch02.normalizedBlockResponseMax R a a0) := by
        rw [hinv, hfinite]

/-- The number of descendants at depth `j`, raised to the outer power-mean
exponent `s/d`, is exactly the geometric amplification `3^{sj}` that the outer
weight `3^{-2sj}` of `𝓔_{s,·,2}^2` absorbs into the printed `3^{-s(m-l)}`. -/
private theorem card_descendants_rpow_eq (m : ℤ) (s : ℝ) (j : ℕ) :
    Real.rpow ((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℝ)
        (s / (d : ℝ)) = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hk : m - (j : ℤ) ≤ (originCube d m).scale := by
    change m - (j : ℤ) ≤ m
    omega
  have hdepth : Int.toNat ((originCube d m).scale - (m - (j : ℤ))) = j := by
    have hred : (originCube d m).scale - (m - (j : ℤ)) = (j : ℤ) := by
      change m - (m - (j : ℤ)) = (j : ℤ)
      ring
    rw [hred, Int.toNat_natCast]
  rw [ErrorComparison.card_descendantsAtScale_eq_rpow (originCube d m) hk, hdepth,
    ErrorComparison.rpow_rpow (by norm_num : (0 : ℝ) ≤ 3),
    show (d : ℝ) * ((j : ℕ) : ℝ) * (s / (d : ℝ)) = s * ((j : ℕ) : ℝ) by
      field_simp]

/-- **The per-scale step of `e.mathcal.E.breakdown`.**  One term of the
`𝓔_{s,∞,2}^2` scale series is bounded by the two leg terms of the display at the
same scale, with the printed geometric weight `3^{-s(m-l)}`, the printed constant
`c_{2s}`, and the `1/2` of the block splitting carried out of the per-scale power
mean by `legScaleAverage_smul`.  Since `breakdownLegA` is twice the printed
`max_{|e|=1}` object, `(1/2) * legScaleAverage … breakdownLegA` is exactly the
printed per-scale power mean. -/
private theorem scale_term_le_leg_terms (m : ℤ)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (j : ℕ) :
    Book.Ch02.geometricWeight s 2 j *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
            a a0) 2 ≤
      (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegA R a a0))) +
        (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegB R a a0))) := by
  have hk : m - (j : ℤ) ≤ (originCube d m).scale := by
    change m - (j : ℤ) ≤ m
    omega
  have hweight_nonneg : 0 ≤ Book.Ch02.geometricWeight s 2 j := by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) j (by positivity)
  have hcore :=
    scaleResponseAtScale_infinity_sq_le_legScaleAverage (originCube d m) hk a a0 hs
  rw [card_descendants_rpow_eq m s j] at hcore
  have hminkraw :
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => Book.Ch02.normalizedBlockResponseMax R a a0) ≤
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => (1 / 2 : ℝ) * breakdownLegA R a a0) +
          legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => (1 / 2 : ℝ) * breakdownLegB R a a0) :=
    legScaleAverage_le_add _ _ hs hs1 (NeZero.ne d)
      (fun R _ => by linarith [breakdownLegA_nonneg R a a0])
      (fun R _ => by linarith [breakdownLegB_nonneg R a a0])
      (fun R _ => Book.Ch02.normalizedBlockResponseMax_nonneg R a a0)
      (fun R hR => by
        linarith [normalizedBlockResponseMax_le_breakdownLegA_add_breakdownLegB
          a a0 hR])
  have hsmulA :
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => (1 / 2 : ℝ) * breakdownLegA R a a0) =
        (1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => breakdownLegA R a a0) :=
    legScaleAverage_smul _ _ hs (NeZero.ne d) (by norm_num)
      (fun R _ => breakdownLegA_nonneg R a a0)
  have hsmulB :
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => (1 / 2 : ℝ) * breakdownLegB R a a0) =
        (1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => breakdownLegB R a a0) :=
    legScaleAverage_smul _ _ hs (NeZero.ne d) (by norm_num)
      (fun R _ => breakdownLegB_nonneg R a a0)
  rw [hsmulA, hsmulB] at hminkraw
  have hthree : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcombined :
      (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
          a a0) ^ 2 ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          ((1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegA R a a0) +
            (1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegB R a a0)) :=
    hcore.trans (mul_le_mul_of_nonneg_left hminkraw hthree)
  have hprod :
      Book.Ch02.geometricWeight s 2 j * Real.rpow (3 : ℝ) (s * (j : ℝ)) =
        Book.Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
    have hadd :
        Real.rpow (3 : ℝ) (-s * 2 * ((j : ℕ) : ℝ)) *
            Real.rpow (3 : ℝ) (s * ((j : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (-s * 2 * ((j : ℕ) : ℝ) + s * ((j : ℕ) : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    have hexp : -s * 2 * ((j : ℕ) : ℝ) + s * ((j : ℕ) : ℝ) = -s * ((j : ℕ) : ℝ) := by
      ring
    unfold Book.Ch02.geometricWeight
    rw [mul_assoc, hadd, hexp]
  calc
    Book.Ch02.geometricWeight s 2 j *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
            a a0) 2 =
        Book.Ch02.geometricWeight s 2 j *
          (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
            a a0) ^ 2 := by rw [rpow_two]
    _ ≤ Book.Ch02.geometricWeight s 2 j *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            ((1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
                (fun R => breakdownLegA R a a0) +
              (1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
                (fun R => breakdownLegB R a a0))) :=
      mul_le_mul_of_nonneg_left hcombined hweight_nonneg
    _ = (Book.Ch02.geometricWeight s 2 j * Real.rpow (3 : ℝ) (s * (j : ℝ))) *
          ((1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegA R a a0) +
            (1 / 2 : ℝ) * legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => breakdownLegB R a a0)) := by ring
    _ = _ := by rw [hprod]; ring

/-- **The summability producer.**  The leg series of the display is summable: each
leg is bounded on the descendants by twice CoarseGraining's structural uniform
response bound for the root cube, so the series is dominated by a convergent
geometric series.

This is public because it is the intended producer of the `Summable` side
conditions of the leg series: a consumer discharges them by supplying a uniform
descendant bound `D` on its leg rather than by re-proving the domination
argument. -/
theorem summable_breakdownLegSum_terms (m : ℤ) {s : ℝ} (hs : 0 < s)
    {leg : TriadicCube d → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hleg0 : ∀ R, 0 ≤ leg R)
    (hlegle : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      leg R ≤ D) :
    Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s leg) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs).mul_right D)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (legScaleAverage_nonneg _ _ _ fun R _ => hleg0 R)
  · exact mul_le_mul_of_nonneg_left
      (legScaleAverage_le_const (originCube d m) (m - (j : ℤ)) hs hD
        (fun R _ => hleg0 R) (hlegle j) (NeZero.ne d))
      (Real.rpow_nonneg (by norm_num) _)

/-- **`e.mathcal.E.breakdown`** (ABK26), pathwise on CoarseGraining's literal
`𝓔_{s,∞,2}` carrier.

For every triadic coefficient family `a`, every constant comparator `a0`, every
cube scale `m` and every `s ∈ (0, 1]`,
```
𝓔_{s,∞,2}(□_m; a, a0)^2
  ≤ (1/2) c_{2s} Σ_{l ≤ m} 3^{-s(m-l)}
      (⨍_{z ∈ 3^l ℤ^d ∩ □_m} legA(z+□_l)^{d/s})^{s/d}
  + (1/2) c_{2s} Σ_{l ≤ m} 3^{-s(m-l)}
      (⨍_{z ∈ 3^l ℤ^d ∩ □_m} legB(z+□_l)^{d/s})^{s/d},
```
with `legA`/`legB` the primal and adjoint frame legs and
`c_{2s} = 1 - 3^{-2s} = geometricDiscount s 2`.

**This is the printed display verbatim.**  The exact accounting: `legA` and
`legB` are the frame suprema over the *doubled* unit sphere, and at the scalar
comparator each equals **twice** the printed `max_{|e|=1}` object ([P]).  The
per-scale power mean is degree-one homogeneous (`legScaleAverage_smul`), so
`(1/2) * breakdownLegSum m s legA` is exactly the printed sum `Σ_{l ≤ m}
3^{-s(m-l)} (⨍ max_{|e|=1} J(z+□_l, a0^{-1/2}e, a0^{1/2}e; a)^{d/s})^{s/d}`,
and likewise for `legB` with `a^t`.  Under that identification the two sides of
this inequality are the two sides of `e.mathcal.E.breakdown` with the same
constant `c_{2s}` — the doubling of the legs and the `1/2` of the block
splitting (`normalizedBlockResponseMax_le_breakdownLegA_add_breakdownLegB`)
cancel here, rather than being asserted to cancel later.

The endpoint `s = 1` is included; see the module docstring for the disclosure of
the printed range of `e.mathcalE.infty.to.q` and of the frame-sup
normalization. -/
theorem homogenizationErrorOnCube_sq_le_breakdown (m : ℤ)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) :
    (Book.Ch02.HomogenizationErrorOnCube (originCube d m) s .infinity (.finite 2)
        a a0) ^ 2 ≤
      (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
          breakdownLegSum m s (fun R => breakdownLegA R a a0)) +
        (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
          breakdownLegSum m s (fun R => breakdownLegB R a a0)) := by
  have hroot : m ≤ (originCube d m).scale := le_of_eq rfl
  obtain ⟨R0, hR0⟩ := descendantsAtScale_nonempty (originCube d m) hroot
  have hU0 : 0 ≤ 2 * Book.Ch02.normalizedBlockResponseUniformBound
      (originCube d m) a a0 := by
    have := (Book.Ch02.normalizedBlockResponseMax_nonneg R0 a a0).trans
      (Book.Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := a) (Q := originCube d m) (R := R0) (k := m) a0 hR0)
    linarith
  have hlegbound : ∀ (leg : TriadicCube d → ℝ),
      (∀ {Q R : TriadicCube d} {k : ℤ}, R ∈ descendantsAtScale Q k →
        leg R ≤ 2 * Book.Ch02.normalizedBlockResponseMax R a a0) →
      ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
        leg R ≤ 2 * Book.Ch02.normalizedBlockResponseUniformBound
          (originCube d m) a a0 := by
    intro leg hbound j R hR
    have h1 := hbound hR
    have h2 :=
      Book.Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := a) (Q := originCube d m) (R := R) (k := m - (j : ℤ)) a0 hR
    linarith
  have hsumA :
      Summable (fun j : ℕ =>
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => breakdownLegA R a a0)) :=
    summable_breakdownLegSum_terms m hs hU0 (fun R => breakdownLegA_nonneg R a a0)
      (hlegbound _ fun hR => breakdownLegA_le_two_mul_normalizedBlockResponseMax
        a a0 hR)
  have hsumB :
      Summable (fun j : ℕ =>
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => breakdownLegB R a a0)) :=
    summable_breakdownLegSum_terms m hs hU0 (fun R => breakdownLegB_nonneg R a a0)
      (hlegbound _ fun hR => breakdownLegB_le_two_mul_normalizedBlockResponseMax
        a a0 hR)
  have hterm := scale_term_le_leg_terms m a a0 hs hs1
  have hsumRHS :
      Summable (fun j : ℕ =>
        (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s
                (fun R => breakdownLegA R a a0))) +
          (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
            (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              legScaleAverage (originCube d m) (m - (j : ℤ)) s
                (fun R => breakdownLegB R a a0)))) :=
    ((hsumA.mul_left _).mul_left _).add ((hsumB.mul_left _).mul_left _)
  have hLHSnonneg : ∀ j : ℕ,
      0 ≤ Book.Ch02.geometricWeight s 2 j *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
            a a0) 2 := by
    intro j
    have hk : m - (j : ℤ) ≤ (originCube d m).scale := by
      change m - (j : ℤ) ≤ m
      omega
    refine mul_nonneg ?_ (Real.rpow_nonneg
      (Book.Ch02.scaleResponseAtScale_infinity_nonneg (originCube d m) hk a a0) 2)
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) j (by positivity)
  have hsumLHS := Summable.of_nonneg_of_le hLHSnonneg hterm hsumRHS
  have hEeq :
      Book.Ch02.HomogenizationErrorOnCube (originCube d m) s .infinity (.finite 2)
          a a0 =
        Real.rpow
          (∑' j : ℕ, Book.Ch02.geometricWeight s 2 j *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ))
                .infinity a a0) 2) (1 / 2) :=
    ErrorComparison.homogenizationError_finite_eq_rpow_tsum (originCube d m) m s
      .infinity 2 a a0
  have hEsq :
      (Book.Ch02.HomogenizationErrorOnCube (originCube d m) s .infinity (.finite 2)
          a a0) ^ 2 =
        ∑' j : ℕ, Book.Ch02.geometricWeight s 2 j *
          Real.rpow
            (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
              a a0) 2 := by
    rw [hEeq, ← rpow_two]
    exact ErrorComparison.rpow_rpow_of_mul_eq_one (tsum_nonneg hLHSnonneg)
      (by norm_num)
  rw [hEsq]
  calc
    (∑' j : ℕ, Book.Ch02.geometricWeight s 2 j *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale (originCube d m) (m - (j : ℤ)) .infinity
            a a0) 2) ≤
        ∑' j : ℕ,
          ((1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
              (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                legScaleAverage (originCube d m) (m - (j : ℤ)) s
                  (fun R => breakdownLegA R a a0))) +
            (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount s 2 *
              (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                legScaleAverage (originCube d m) (m - (j : ℤ)) s
                  (fun R => breakdownLegB R a a0)))) :=
      Summable.tsum_le_tsum hterm hsumLHS hsumRHS
    _ = _ := by
        rw [Summable.tsum_add ((hsumA.mul_left _).mul_left _)
            ((hsumB.mul_left _).mul_left _),
          (hsumA.mul_left _).tsum_mul_left, (hsumB.mul_left _).tsum_mul_left,
          hsumA.tsum_mul_left, hsumB.tsum_mul_left]
        rfl

end Assembly

/-! ## The two frame combinations and their size -/

/-- The primal frame combination `e₁ - e₂` of a doubled direction `e`. -/
def frameLegAVec (e : FullBlockVec d) : Vec d :=
  (ofFullBlockVec e).1 - (ofFullBlockVec e).2

/-- The adjoint frame combination `e₁ + e₂` of a doubled direction `e`. -/
def frameLegBVec (e : FullBlockVec d) : Vec d :=
  (ofFullBlockVec e).1 + (ofFullBlockVec e).2

/-- The doubled squared norm splits into the two halves. -/
private theorem fullBlockVecNormSq_eq_add (e : FullBlockVec d) :
    Book.Ch02.fullBlockVecNormSq e =
      vecNormSq (ofFullBlockVec e).1 + vecNormSq (ofFullBlockVec e).2 := by
  simp only [Book.Ch02.fullBlockVecNormSq, vecNormSq, vecDot, ofFullBlockVec]
  rw [Fintype.sum_sum_type]
  simp [pow_two]

/-- The primal loading vector of a doubled unit direction has squared length at
most `2`. -/
theorem vecNormSq_frameLegAVec_le (e : FullBlockVec d)
    (he : Book.Ch02.fullBlockVecNormSq e = 1) : vecNormSq (frameLegAVec e) ≤ 2 := by
  have hsplit := fullBlockVecNormSq_eq_add e
  have hsub := vecNormSq_sub_le (ofFullBlockVec e).1 (ofFullBlockVec e).2
  rw [he] at hsplit
  simpa only [frameLegAVec] using hsub.trans (by linarith)

/-- The adjoint loading vector of a doubled unit direction has squared length at
most `2`. -/
theorem vecNormSq_frameLegBVec_le (e : FullBlockVec d)
    (he : Book.Ch02.fullBlockVecNormSq e = 1) : vecNormSq (frameLegBVec e) ≤ 2 := by
  have hsplit := fullBlockVecNormSq_eq_add e
  have hadd := vecNormSq_add_le (ofFullBlockVec e).1 (ofFullBlockVec e).2
  rw [he] at hsplit
  simpa only [frameLegBVec] using hadd.trans (by linarith)

/-! ## The isotropic comparator acts diagonally on the doubled frame -/

section Diagonal

variable [NeZero d]

omit [NeZero d] in
private theorem frameLoadSqrt_fst (sigma : Observable.PositiveScalar)
    (e : FullBlockVec d) :
    (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 =
      Real.sqrt (sigma : ℝ) • (ofFullBlockVec e).1 := by
  simp only [frameLoadSqrt,
    show Observable.isotropicComparatorMatrix (d := d) sigma =
      scalarMatrix (d := d) (sigma : ℝ) from rfl,
    Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
      (d := d) sigma.2]
  funext i
  simp [ofFullBlockVec, Matrix.mulVec_diagonal,
    Book.Ch05.Section56.scalarFullBlockSqrtDiag]

omit [NeZero d] in
private theorem frameLoadSqrt_snd (sigma : Observable.PositiveScalar)
    (e : FullBlockVec d) :
    (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 =
      (Real.sqrt (sigma : ℝ))⁻¹ • (ofFullBlockVec e).2 := by
  simp only [frameLoadSqrt,
    show Observable.isotropicComparatorMatrix (d := d) sigma =
      scalarMatrix (d := d) (sigma : ℝ) from rfl,
    Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
      (d := d) sigma.2]
  funext i
  simp [ofFullBlockVec, Matrix.mulVec_diagonal,
    Book.Ch05.Section56.scalarFullBlockSqrtDiag]

omit [NeZero d] in
private theorem frameLoadInvSqrt_fst (sigma : Observable.PositiveScalar)
    (e : FullBlockVec d) :
    (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 =
      (Real.sqrt (sigma : ℝ))⁻¹ • (ofFullBlockVec e).1 := by
  simp only [frameLoadInvSqrt,
    show Observable.isotropicComparatorMatrix (d := d) sigma =
      scalarMatrix (d := d) (sigma : ℝ) from rfl,
    Book.Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
      (d := d) sigma.2]
  funext i
  simp [ofFullBlockVec, Matrix.mulVec_diagonal,
    Book.Ch04.scalarFullBlockInvSqrtDiag]

omit [NeZero d] in
private theorem frameLoadInvSqrt_snd (sigma : Observable.PositiveScalar)
    (e : FullBlockVec d) :
    (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 =
      Real.sqrt (sigma : ℝ) • (ofFullBlockVec e).2 := by
  simp only [frameLoadInvSqrt,
    show Observable.isotropicComparatorMatrix (d := d) sigma =
      scalarMatrix (d := d) (sigma : ℝ) from rfl,
    Book.Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
      (d := d) sigma.2]
  funext i
  simp [ofFullBlockVec, Matrix.mulVec_diagonal,
    Book.Ch04.scalarFullBlockInvSqrtDiag]

/-! ## The legs in the manuscript's paired form -/

omit [NeZero d] in
/-- **The primal leg at the isotropic comparator is the manuscript's paired
family.**  Each doubled unit direction `e` contributes exactly
`J(R, σ^{-1/2}v, σ^{1/2}v; a)` at the loading vector `v = e₁ - e₂`. -/
theorem breakdownLegAValueSet_isotropic_eq (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar) :
    breakdownLegAValueSet R a (Observable.isotropicComparatorMatrix sigma) =
      { x : ℝ | ∃ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 ∧
          x = Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
            (Observable.inverseSqrtLoad sigma (frameLegAVec e))
            (Observable.sqrtLoad sigma (frameLegAVec e)) } := by
  have hfirst : ∀ e : FullBlockVec d,
      (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 -
          (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 =
        Observable.inverseSqrtLoad sigma (frameLegAVec e) := by
    intro e
    rw [frameLoadInvSqrt_fst, frameLoadSqrt_snd]
    simp only [Observable.inverseSqrtLoad, frameLegAVec, smul_sub]
  have hsecond : ∀ e : FullBlockVec d,
      (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 -
          (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 =
        Observable.sqrtLoad sigma (frameLegAVec e) := by
    intro e
    rw [frameLoadSqrt_fst, frameLoadInvSqrt_snd]
    simp only [Observable.sqrtLoad, frameLegAVec, smul_sub]
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [hfirst e, hsecond e]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [hfirst e, hsecond e]⟩

omit [NeZero d] in
/-- **The adjoint leg at the isotropic comparator is the manuscript's paired
family.**  Each doubled unit direction `e` contributes exactly
`J(R, σ^{-1/2}v, σ^{1/2}v; a^t)` at the loading vector `v = e₁ + e₂`. -/
theorem breakdownLegBValueSet_isotropic_eq (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar) :
    breakdownLegBValueSet R a (Observable.isotropicComparatorMatrix sigma) =
      { x : ℝ | ∃ e : FullBlockVec d, Book.Ch02.fullBlockVecNormSq e = 1 ∧
          x = Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
            (Observable.inverseSqrtLoad sigma (frameLegBVec e))
            (Observable.sqrtLoad sigma (frameLegBVec e)) } := by
  have hfirst : ∀ e : FullBlockVec d,
      (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 +
          (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 =
        Observable.inverseSqrtLoad sigma (frameLegBVec e) := by
    intro e
    rw [frameLoadSqrt_snd, frameLoadInvSqrt_fst]
    simp only [Observable.inverseSqrtLoad, frameLegBVec, smul_add]
    exact add_comm _ _
  have hsecond : ∀ e : FullBlockVec d,
      (frameLoadSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).1 +
          (frameLoadInvSqrt (Observable.isotropicComparatorMatrix (d := d) sigma) e).2 =
        Observable.sqrtLoad sigma (frameLegBVec e) := by
    intro e
    rw [frameLoadSqrt_fst, frameLoadInvSqrt_snd]
    simp only [Observable.sqrtLoad, frameLegBVec, smul_add]
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [hfirst e, hsecond e]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [hfirst e, hsecond e]⟩

/-! ## The consumption interface -/

omit [NeZero d] in
/-- **The primal leg under a paired-loading bound.**  A bound on the manuscript's
paired response `J(R, σ^{-1/2}v, σ^{1/2}v; a)`, uniform over loading vectors of
squared Euclidean length at most `2`, bounds the leg.  This is the interface
through which the localization proof's per-cube estimates — which are proved at
paired unit loadings — reach the legs of `e.mathcal.E.breakdown`; the excess
length `√2` is exactly the doubling recorded in [P]. -/
theorem breakdownLegA_le_of_paired_bound (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ c) :
    breakdownLegA R a (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  rw [breakdownLegA, breakdownLegAValueSet_isotropic_eq]
  refine Real.sSup_le ?_ hc
  rintro x ⟨e, he, rfl⟩
  exact h (frameLegAVec e) (vecNormSq_frameLegAVec_le e he)

omit [NeZero d] in
/-- **The adjoint leg under a paired-loading bound.** -/
theorem breakdownLegB_le_of_paired_bound (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R).transpose
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ c) :
    breakdownLegB R a (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  rw [breakdownLegB, breakdownLegBValueSet_isotropic_eq]
  refine Real.sSup_le ?_ hc
  rintro x ⟨e, he, rfl⟩
  exact h (frameLegBVec e) (vecNormSq_frameLegBVec_le e he)

end Diagonal

/-! ## The Section 3 carrier -/

/-- The paper-wide dimension assumption `2 ≤ d` stored in the model discharges the
`[NeZero d]` binder carried by the statements of this file.  That binder is
therefore typing data for the block carriers, not an additional mathematical
premise: any caller holding an `ABKModel d` can supply it. -/
theorem neZero_of_abkModel (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

section Carrier

variable [NeZero d]

/-- **`e.mathcal.E.breakdown` on the Section 3 carrier** (ABK26).  For the
measurable Section 3 observable `𝓔_{s,∞,2}(□_m; a_m, σ_m)` at any `s ∈ (0, 1]`,
```
𝓔_{s,∞,2}(□_m; a_m, σ_m)^2
  ≤ (1/2) c_{2s} Σ_{l ≤ m} 3^{-s(m-l)}
      (⨍_{z ∈ 3^l ℤ^d ∩ □_m} legA(z+□_l; a_m, σ_m)^{d/s})^{s/d}
  + (1/2) c_{2s} Σ_{l ≤ m} 3^{-s(m-l)}
      (⨍_{z ∈ 3^l ℤ^d ∩ □_m} legB(z+□_l; a_m, σ_m)^{d/s})^{s/d}
```
almost surely under the cutoff-sample law, with `legA` the primal and `legB` the
adjoint frame leg at the `σ_m`-normalized loadings.

**This is the printed display verbatim**, with the same accounting as
`homogenizationErrorOnCube_sq_le_breakdown`: each leg is twice the printed
`max_{|e|=1}` object, the per-scale power mean is degree-one homogeneous
(`legScaleAverage_smul`), so `(1/2) * breakdownLegSum m s legA` is exactly the
printed sum and the constant is the printed `c_{2s}`.

The inequality itself is deterministic
(`homogenizationErrorOnCube_sq_le_breakdown`); the almost-sure quantifier, and
the fact that its null set sits inside the `s` binder, come only from the
verified measurable representative underlying
`Observable.cutoffHomogenizationError`, whose identification with
CoarseGraining's literal `𝓔_{s,∞,2}` is itself indexed by `s` ([F]). -/
theorem cutoffHomogenizationError_sq_ae_le_breakdown (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (hs1 : (s : ℝ) ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (Observable.cutoffHomogenizationError M m s omega) ^ 2 ≤
        (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount (s : ℝ) 2 *
            breakdownLegSum m (s : ℝ) (fun R =>
              breakdownLegA R (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))) +
          (1 / 2 : ℝ) * (Book.Ch02.geometricDiscount (s : ℝ) 2 *
            breakdownLegSum m (s : ℝ) (fun R =>
              breakdownLegB R (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))) := by
  filter_upwards
    [Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M m s]
    with omega homega
  rw [homega]
  exact homogenizationErrorOnCube_sq_le_breakdown m
    (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) s.2 hs1

end Carrier

end

end Algsuperdiff.Section3.Provider.Localization
