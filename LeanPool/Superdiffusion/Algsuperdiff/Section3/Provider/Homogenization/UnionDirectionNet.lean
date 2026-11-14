/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ResponseCommonDomination

/-!
# UnionDirectionNet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The finite direction net of the Section 3.5 response

This module supplies such a reduction against this repository's carrier: on one
probability-one event, simultaneously for every cutoff scale and every unit
direction, the Section 3.5 response `Observable.cutoffResponseJ` is at most `2
^ d` times the sum of its values at the `d` coordinate directions, hence at
most `2 ^ d * d` times one of them.

The response is a nonnegative quadratic form in the direction: quadratic
homogeneity and the parallelogram identity are Chapter 2 theorems of
CoarseGraining about `responseJ` (`responseJ_smul`, `responseJ_parallelogram`),
and nonnegativity is another (`responseJ_nonneg`).  No convexity A, no
convexity predicate, no bilinear form and no convex hull is constructed.  The
net used here is the `d` coordinate directions and the cost is `2 ^ d`, a
constant depending only on `d`; the source's own net is the `2 ^ d` sign vectors
at cost `d`.  Both are admissible for a source node whose constant scope is
`C(d)`, and the coordinate net is the one for which the decomposition `e =
sum_i e_i E_i` with `sum_i e_i ^ 2 = 1` is available directly.

Two deliberate deviations from the source are recorded here.  First, the net is the
`d` coordinate directions rather than the `2 ^ d` sign vectors.  Second, the
dimensional cost is `2 ^ d` (or `2 ^ d * d` in the existential form) rather
than the printed `d`; the sharper printed constant comes from a genuine convexity
argument over the `l^infinity` box, while the route taken here uses only the
parallelogram identity through `R(x + y) <= 2 R(x) + 2 R(y)`.  Both costs
depend on `d` alone, which is the constant scope recorded for the source node.
The extra factor is absorbed in two places, both inside the printed budget
`k = k1 + k2 <= C(d) |log epsilon|`: on the two fluctuation lanes by enlarging
the separation `k2` (see `exists_gridDecay_mul_le` in
`Provider/Homogenization/UnionAggregation.lean`; the increment is
`2 log(2 ^ d * d) / (d log 3)`, bounded in `d`), and on the deterministic mean
by running the finite-corridor iteration at `epsilon / (2 ^ d * d)`, which
costs `k1` an additive `C(d)`.  Enlarging `k2` alone does not suffice: the
direction net multiplies the mean term as well.

Only one null set is spent: everything below is `filter_upwards` on the single
statement `Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal`,
whose quantifiers over cutoff scales and loads already sit inside the event.
The uncountable direction quantifier likewise stays inside the event, so no
intersection over directions is taken.

Standing data: `M : ABKModel d` (through which `0 < d` is read off
`M.shellPrefix.dimension`, never bound).  Typing data: `d`, `cubeScale`, `e`,
and the section carriers `U`, `a`, `sigma` of the deterministic lemmas.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

section DirectionNet

variable {d : ℕ} {U : Ch02.Domain d} {a : Ch02.CoeffOn U}
  {sigma : Observable.PositiveScalar}

/-- The scalar response as a function of the direction alone, with both loads
normalized by one positive comparator.  This is the object ABK26 maximizes over
the unit sphere. -/
def loadResponse (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (sigma : Observable.PositiveScalar) (x : Vec d) : ℝ :=
  Ch02.responseJ U a (Observable.inverseSqrtLoad sigma x)
    (Observable.sqrtLoad sigma x)

private theorem loadResponse_nonneg (x : Vec d) : 0 ≤ loadResponse U a sigma x :=
  Ch02.responseJ_nonneg U a _ _

private theorem loadResponse_smul (c : ℝ) (x : Vec d) :
    loadResponse U a sigma (c • x) = c ^ 2 * loadResponse U a sigma x := by
  have hp : Observable.inverseSqrtLoad sigma (c • x) =
      c • Observable.inverseSqrtLoad sigma x := by
    simp only [Observable.inverseSqrtLoad]
    exact smul_comm _ _ _
  have hq : Observable.sqrtLoad sigma (c • x) =
      c • Observable.sqrtLoad sigma x := by
    simp only [Observable.sqrtLoad]
    exact smul_comm _ _ _
  simp only [loadResponse, hp, hq]
  exact Ch02.responseJ_smul c _ _

private theorem loadResponse_zero : loadResponse U a sigma (0 : Vec d) = 0 := by
  simpa using loadResponse_smul (U := U) (a := a) (sigma := sigma) 0 0

private theorem loadResponse_add_le (x y : Vec d) :
    loadResponse U a sigma (x + y) ≤
      2 * loadResponse U a sigma x + 2 * loadResponse U a sigma y := by
  have hpadd : Observable.inverseSqrtLoad sigma (x + y) =
      Observable.inverseSqrtLoad sigma x + Observable.inverseSqrtLoad sigma y := by
    simp only [Observable.inverseSqrtLoad, smul_add]
  have hqadd : Observable.sqrtLoad sigma (x + y) =
      Observable.sqrtLoad sigma x + Observable.sqrtLoad sigma y := by
    simp only [Observable.sqrtLoad, smul_add]
  have hpsub : Observable.inverseSqrtLoad sigma (x - y) =
      Observable.inverseSqrtLoad sigma x - Observable.inverseSqrtLoad sigma y := by
    simp only [Observable.inverseSqrtLoad, smul_sub]
  have hqsub : Observable.sqrtLoad sigma (x - y) =
      Observable.sqrtLoad sigma x - Observable.sqrtLoad sigma y := by
    simp only [Observable.sqrtLoad, smul_sub]
  have hpar := Ch02.responseJ_parallelogram (U := U) (a := a)
    (Observable.inverseSqrtLoad sigma x) (Observable.sqrtLoad sigma x)
    (Observable.inverseSqrtLoad sigma y) (Observable.sqrtLoad sigma y)
  have hsubnn : 0 ≤ loadResponse U a sigma (x - y) := loadResponse_nonneg _
  simp only [loadResponse, hpadd, hqadd, hpsub, hqsub] at *
  linarith

private theorem loadResponse_sum_le {iota : Type*} (s : Finset iota)
    (f : iota → Vec d) :
    loadResponse U a sigma (∑ i ∈ s, f i) ≤
      2 ^ s.card * ∑ i ∈ s, loadResponse U a sigma (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [loadResponse_zero]
  · intro x s' hx ih
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      Finset.card_insert_of_notMem hx]
    have hstep := loadResponse_add_le (U := U) (a := a) (sigma := sigma)
      (f x) (∑ i ∈ s', f i)
    have hone : (1 : ℝ) ≤ 2 ^ s'.card := one_le_pow₀ (by norm_num)
    have hfx : 0 ≤ loadResponse U a sigma (f x) := loadResponse_nonneg _
    have hpow : (2 : ℝ) ^ (s'.card + 1) = 2 * 2 ^ s'.card := by ring
    rw [hpow]
    nlinarith [hstep, ih, hone, hfx]

private theorem loadResponse_unit_le {e : Vec d} (he : Ch02.vecNorm e = 1) :
    loadResponse U a sigma e ≤
      2 ^ d * ∑ i : Fin d, loadResponse U a sigma (Pi.single i (1 : ℝ)) := by
  classical
  have hdecomp : e = ∑ i : Fin d, (e i) • (Pi.single i (1 : ℝ) : Vec d) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hnormsq : vecNormSq e = 1 := by
    rw [← Ch02.vecNorm_sq_eq_vecNormSq, he]
    norm_num
  have hcoord : ∀ i : Fin d, (e i) ^ 2 ≤ 1 := by
    intro i
    have hle := sq_apply_le_vecNormSq e i
    rw [hnormsq] at hle
    exact hle
  calc loadResponse U a sigma e
      = loadResponse U a sigma
          (∑ i : Fin d, (e i) • (Pi.single i (1 : ℝ) : Vec d)) := by
        rw [← hdecomp]
    _ ≤ 2 ^ (Finset.univ : Finset (Fin d)).card *
          ∑ i : Fin d, loadResponse U a sigma
            ((e i) • (Pi.single i (1 : ℝ) : Vec d)) :=
        loadResponse_sum_le (U := U) (a := a) (sigma := sigma) Finset.univ
          (fun i : Fin d => (e i) • (Pi.single i (1 : ℝ) : Vec d))
    _ = 2 ^ d * ∑ i : Fin d, (e i) ^ 2 *
          loadResponse U a sigma (Pi.single i (1 : ℝ)) := by
        rw [Finset.card_univ, Fintype.card_fin]
        congr 1
        exact Finset.sum_congr rfl fun i _ => loadResponse_smul _ _
    _ ≤ 2 ^ d * ∑ i : Fin d, loadResponse U a sigma (Pi.single i (1 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_)
          (by positivity)
        nlinarith [loadResponse_nonneg (U := U) (a := a) (sigma := sigma)
          (Pi.single i (1 : ℝ) : Vec d), hcoord i]

/-- The squared Euclidean length of a coordinate direction is one. -/
private theorem vecNormSq_single_one (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply]

/-- Each coordinate direction is an admissible direction for the Section 3.5
family, that is, a Euclidean unit vector. -/
theorem vecNorm_single_one (i : Fin d) :
    Ch02.vecNorm (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  have hsq : Ch02.vecNorm (Pi.single i (1 : ℝ) : Vec d) ^ 2 = 1 := by
    rw [Ch02.vecNorm_sq_eq_vecNormSq, vecNormSq_single_one]
  have hnn : 0 ≤ Ch02.vecNorm (Pi.single i (1 : ℝ) : Vec d) := by
    simp only [Ch02.vecNorm]
    exact norm_nonneg _
  have hfactor : (Ch02.vecNorm (Pi.single i (1 : ℝ) : Vec d) - 1) *
      (Ch02.vecNorm (Pi.single i (1 : ℝ) : Vec d) + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

/-- On one probability-one event, and simultaneously for every cutoff scale and
every direction, the measurable Section 3.5 response is the Chapter 2 response
of CoarseGraining at the two normalized loads.  This is the form in which the
Chapter 2 quadraticity theorems apply to it. -/
theorem ae_forall_cutoffResponseJ_eq_bookResponseJ (M : ABKModel d)
    (cubeScale : ℤ) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (coefficientScale : ℤ) (x : Vec d),
        Observable.cutoffResponseJ M cubeScale coefficientScale x omega =
          Ch02.responseJ (Ch02.cubeDomain (originCube d cubeScale))
            ((coefficientCutoffTriadicCoeffFamily M coefficientScale
              omega).coeffOn (originCube d cubeScale))
            (Observable.inverseSqrtLoad
              (Annealed.sigmaBar M coefficientScale) x)
            (Observable.sqrtLoad (Annealed.sigmaBar M coefficientScale) x) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  filter_upwards
    [Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal M
      cubeScale] with omega hresponse
  intro coefficientScale x
  rw [_root_.HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ]
  simp only [coefficientCutoffTriadicCoeffFamily,
    coefficientCutoffCoeffOn_toCoeffField]
  change Observable.cutoffResponseJ M cubeScale coefficientScale x omega =
    ResponseJ (openCubeSet (originCube d cubeScale))
      (Observable.inverseSqrtLoad (Annealed.sigmaBar M coefficientScale) x)
      (Observable.sqrtLoad (Annealed.sigmaBar M coefficientScale) x)
      (coefficientCutoff M.nu coefficientScale omega).toFun
  rw [← _root_.HCPolySupport.responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
  exact hresponse coefficientScale x

/-- **The finite direction net.**  On one probability-one event, and
simultaneously for every cutoff scale and every Euclidean unit direction, the
Section 3.5 response is bounded by `2 ^ d` times the sum of its values at the
`d` coordinate directions.

The proof uses only the Chapter 2 quadraticity theorems of CoarseGraining ---
exact quadratic homogeneity, the parallelogram identity, and nonnegativity ---
and the decomposition of a unit vector into coordinates with squared
coefficients summing to one.  The uncountable direction quantifier sits inside
the event, so no intersection over directions is taken. -/
theorem ae_forall_cutoffResponseJ_le_coordinateSum (M : ABKModel d)
    (cubeScale : ℤ) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (coefficientScale : ℤ) (e : Vec d), Ch02.vecNorm e = 1 →
        Observable.cutoffResponseJ M cubeScale coefficientScale e omega ≤
          2 ^ d * ∑ i : Fin d,
            Observable.cutoffResponseJ M cubeScale coefficientScale
              (Pi.single i (1 : ℝ)) omega := by
  filter_upwards [ae_forall_cutoffResponseJ_eq_bookResponseJ M cubeScale]
    with omega hbook
  intro coefficientScale e he
  rw [hbook coefficientScale e]
  have hrewrite : ∀ i : Fin d,
      Observable.cutoffResponseJ M cubeScale coefficientScale
          (Pi.single i (1 : ℝ)) omega =
        loadResponse (Ch02.cubeDomain (originCube d cubeScale))
          ((coefficientCutoffTriadicCoeffFamily M coefficientScale
            omega).coeffOn (originCube d cubeScale))
          (Annealed.sigmaBar M coefficientScale) (Pi.single i (1 : ℝ)) :=
    fun i => hbook coefficientScale _
  simp only [hrewrite]
  exact loadResponse_unit_le he

/-- The consumer form of the direction net: every unit direction is dominated,
on the same event, by one member of the `d`-element coordinate family, at the
dimensional cost `2 ^ d * d`.

This is the shape the aggregation consumes: an existential over a finite index
whose quantifier sits inside the almost-sure event. -/
theorem ae_forall_cutoffResponseJ_le_directionNet (M : ABKModel d)
    (cubeScale : ℤ) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (coefficientScale : ℤ) (e : Vec d), Ch02.vecNorm e = 1 →
        ∃ i : Fin d,
          Observable.cutoffResponseJ M cubeScale coefficientScale e omega ≤
            2 ^ d * (d : ℝ) *
              Observable.cutoffResponseJ M cubeScale coefficientScale
                (Pi.single i (1 : ℝ)) omega := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, hd⟩⟩
  filter_upwards [ae_forall_cutoffResponseJ_le_coordinateSum M cubeScale]
    with omega hsum
  intro coefficientScale e he
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin d))
      (fun i : Fin d => Observable.cutoffResponseJ M cubeScale
        coefficientScale (Pi.single i (1 : ℝ)) omega) hne
  refine ⟨i, (hsum coefficientScale e he).trans ?_⟩
  have hbound : ∑ j : Fin d, Observable.cutoffResponseJ M cubeScale
      coefficientScale (Pi.single j (1 : ℝ)) omega ≤
      (d : ℝ) * Observable.cutoffResponseJ M cubeScale coefficientScale
        (Pi.single i (1 : ℝ)) omega := by
    have hcard : ((Finset.univ : Finset (Fin d)).card : ℝ) = (d : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    calc ∑ j : Fin d, Observable.cutoffResponseJ M cubeScale
          coefficientScale (Pi.single j (1 : ℝ)) omega
        ≤ ∑ _j : Fin d, Observable.cutoffResponseJ M cubeScale
            coefficientScale (Pi.single i (1 : ℝ)) omega :=
          Finset.sum_le_sum fun j hj => hi j hj
      _ = (d : ℝ) * Observable.cutoffResponseJ M cubeScale coefficientScale
            (Pi.single i (1 : ℝ)) omega := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hpow : (0 : ℝ) ≤ 2 ^ d := by positivity
  calc 2 ^ d * ∑ j : Fin d, Observable.cutoffResponseJ M cubeScale
        coefficientScale (Pi.single j (1 : ℝ)) omega
      ≤ 2 ^ d * ((d : ℝ) * Observable.cutoffResponseJ M cubeScale
          coefficientScale (Pi.single i (1 : ℝ)) omega) :=
        mul_le_mul_of_nonneg_left hbound hpow
    _ = 2 ^ d * (d : ℝ) * Observable.cutoffResponseJ M cubeScale
          coefficientScale (Pi.single i (1 : ℝ)) omega := by ring

end DirectionNet

end

end Algsuperdiff.Section3.Provider.Homogenization
