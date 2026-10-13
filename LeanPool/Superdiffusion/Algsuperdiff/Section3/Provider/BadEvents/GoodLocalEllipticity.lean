/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.Definitions

/-!
# GoodLocalEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse-ellipticity clause of the good local sensitivity event

ABK26 defines, in `e.good.local.events`, for `m, n` integers and a centre `z`,
the good local sensitivity event

```
Q(m,n,z) := { C_sens sup_{L >= n} 3^{2m} ||grad (k_L - k_n)||_{W^{1,infinity}(z+square_m)}
              <= (1/2) C_{(e.cg.ellip.lower)}^{-1} 3^{-(1/2)(n-m)_+} sigmaBar_{n-1}
              <= 3^{-(1/4)(n-m)_+} lambda_{1/8,2}(z+square_m; a_n) } .
```

The displayed event is a chain of two inequalities.  This module defines and
proves a local version of the **second** one — the comparison of the middle threshold with the coarse-grained
lower ellipticity of the cutoff field `a_n` on the cube — as a measurable event
`goodLocalEllipticity`, and proves the exact identification of its complement
with the second event of the manuscript's own decomposition of `not Q(m,n,0)`
in the proof of `l.bad.event.lemma`,

```
{ lambda^{-1}_{1/8,2}(square_m; a_n) sigmaBar_{n-1} > 2 . 3^{(1/4)(n-m)_+}
    C_{(e.cg.ellip.lower)} } .
```

## Carrier and constant conventions (recorded)

* The centre `z` is carried by a `TriadicCube d`, exactly as for the bad events
  of `Definitions.lean`: `Q.scale = m` is the cube scale and `cubeSet Q = z +
  square_m` with `z` in `3^m Z^d`.  The manuscript writes `z in R^d`; every
  consumer of `e.good.local.events` instantiates `z` in a triadic lattice, and
  this repository has no multiscale ellipticity observable on off-grid
  translates.
* `C_{(e.cg.ellip.lower)}` is carried as an explicit real parameter `Ccg`.  Its
  source is the constant of `e.cg.ellip.lower` in `p.cg.ellipticity.bounds`,
  whose frozen statement
  `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is now proved and
  available to consumers.  This conditional A remains parametrized by `Ccg`;
  downstream assemblies may instantiate it from the frozen export, while every
  statement below that uses it carries `0 < Ccg` explicitly.
* `lambda_{1/8,2}(z+square_m; a_n)` is the measurable representative
  `cubeLowerEllipticity`, defined as the pointwise inverse of the proved
  representative `cubeLowerEllipticityInv` of `lambda^{-1}_{1/8,2}`.  Since
  `Ch02.lambdaSq` is a real number and the literal observable is its inverse,
  the double inverse is the literal `lambda` exactly
  (`cubeLowerEllipticityInvLiteral_inv_eq`).

## Main definitions

* `scaleGapPos`: the manuscript's positive part `(n - m)_+`.
* `cubeLowerEllipticity`: measurable representative of `lambda_{s,q}(Q; a_r)`.
* `goodLocalThreshold`: the middle term
  `(1/2) Ccg^{-1} 3^{-(1/2)(n-m)_+} sigmaBar_{n-1}` of `e.good.local.events`.
* `goodLocalEllipticity`: the second inequality of `e.good.local.events`, as an
  event.

## Main results

* `cubeLowerEllipticityInvLiteral_pos`, `cubeLowerEllipticityInv_pos_ae`.
* `measurable_cubeLowerEllipticity`, `cubeLowerEllipticity_ae_eq_literal`,
  `cubeLowerEllipticityInvLiteral_inv_eq`.
* `measurableSet_goodLocalEllipticity`.
* `notMem_goodLocalEllipticity_iff`: the exact equivalence with the
  manuscript's coarse-ellipticity failure event, at a point where the
  representative of `lambda^{-1}` is positive.
* `compl_goodLocalEllipticity_ae_eq`, `measureReal_compl_goodLocalEllipticity`:
  the same identification almost everywhere, and the resulting equality of
  probabilities — the first reduction in the proof of `l.bad.event.lemma`.

## References

* ABK26, `e.good.local.events`.
* ABK26, `l.bad.event.lemma`.
* ABK26, `p.cg.ellipticity.bounds` (`e.cg.ellip.lower`).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_abkModel (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## The scale gap -/

/-- The manuscript's positive part `(n - m)_+` of the scale gap between the
cutoff scale `n` and the cube scale `m`. -/
def scaleGapPos (m n : ℤ) : ℝ := max ((n : ℝ) - (m : ℝ)) 0

theorem scaleGapPos_nonneg (m n : ℤ) : 0 ≤ scaleGapPos m n := le_max_right _ _

/-- On the branch `n >= m` the positive part is the plain gap. -/
theorem scaleGapPos_of_le {m n : ℤ} (h : m ≤ n) :
    scaleGapPos m n = (n : ℝ) - (m : ℝ) := by
  have : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h
  exact max_eq_left (by linarith)

/-- On the branch `n < m` the positive part vanishes. -/
theorem scaleGapPos_of_lt {m n : ℤ} (h : n < m) : scaleGapPos m n = 0 := by
  have : ((n : ℝ)) < (m : ℝ) := by exact_mod_cast h
  exact max_eq_right (by linarith)

/-! ## Positivity of the lower multiscale ellipticity -/

/-- The literal inverse lower multiscale ellipticity of the cutoff field is
strictly positive: `Ch02.lambdaSq` is positive for every coefficient family, and
the cutoff field is always in the elliptic branch of `Ch04.lambdaSqCoeffField`. -/
theorem cubeLowerEllipticityInvLiteral_pos (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    0 < cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega := by
  let : NeZero d := neZero_of_abkModel M
  obtain ⟨qe, hqe⟩ := q
  unfold cubeLowerEllipticityInvLiteral
  refine inv_pos.mpr ?_
  rw [Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]
  cases qe with
  | finite r =>
      exact Ch02.lambdaSq_finite_pos Q _ hs hqe
  | infinity =>
      exact Ch02.lambdaSq_infinity_pos Q _ hs

/-- The measurable representative of `lambda^{-1}_{s,q}(Q; a_r)` is almost
surely positive. -/
theorem cubeLowerEllipticityInv_pos_ae (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0 < cubeLowerEllipticityInv M Q cutoffScale s hs q omega := by
  filter_upwards [cubeLowerEllipticityInv_ae_eq_literal M Q cutoffScale s hs q]
    with omega homega
  rw [homega]
  exact cubeLowerEllipticityInvLiteral_pos M Q cutoffScale hs q omega

/-! ## The lower multiscale ellipticity observable -/

/-- Measurable representative of `lambda_{s,q}(Q; a_r)` for the actual cutoff on an
arbitrary triadic cube: the pointwise inverse of the proved representative of
`lambda^{-1}_{s,q}(Q; a_r)`. -/
def cubeLowerEllipticity (M : ABKModel d) (Q : TriadicCube d) (cutoffScale : ℤ)
    (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    CutoffSample d → ℝ :=
  fun omega => (cubeLowerEllipticityInv M Q cutoffScale s hs q omega)⁻¹

theorem measurable_cubeLowerEllipticity (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    Measurable (cubeLowerEllipticity M Q cutoffScale s hs q) :=
  (measurable_cubeLowerEllipticityInv M Q cutoffScale s hs q).inv

theorem cubeLowerEllipticity_nonneg (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    0 ≤ cubeLowerEllipticity M Q cutoffScale s hs q omega :=
  inv_nonneg.2 (cubeLowerEllipticityInv_nonneg M Q cutoffScale s hs q omega)

/-- The inverse of the literal inverse lower ellipticity is the literal lower
ellipticity `lambda_{s,q}(Q; a_r)` of the actual cutoff. -/
theorem cubeLowerEllipticityInvLiteral_inv_eq [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    (cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega)⁻¹ =
      Ch04.lambdaSqCoeffField Q s q.1
        (Cutoff.coefficientCutoff M.nu cutoffScale omega) :=
  inv_inv _

/-- The representative of `lambda_{s,q}(Q; a_r)` agrees almost everywhere with
the inverse of the literal observable, hence — by
`cubeLowerEllipticityInvLiteral_inv_eq` — with `lambda_{s,q}(Q; a_r)`. -/
theorem cubeLowerEllipticity_ae_eq_literal (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeLowerEllipticity M Q cutoffScale s hs q
        =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega => (cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega)⁻¹ := by
  filter_upwards [cubeLowerEllipticityInv_ae_eq_literal M Q cutoffScale s hs q]
    with omega homega
  change (cubeLowerEllipticityInv M Q cutoffScale s hs q omega)⁻¹ = _
  rw [homega]

/-! ## The middle threshold of `e.good.local.events` -/

/-- The middle term of the chain `e.good.local.events`:
`(1/2) C_{(e.cg.ellip.lower)}^{-1} 3^{-(1/2)(n-m)_+} sigmaBar_{n-1}`. -/
def goodLocalThreshold (M : ABKModel d) (Ccg : ℝ) (m n : ℤ) : ℝ :=
  (1 / 2 : ℝ) * Ccg⁻¹ * (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos m n) *
    ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))

theorem goodLocalThreshold_pos (M : ABKModel d) {Ccg : ℝ} (hCcg : 0 < Ccg)
    (m n : ℤ) : 0 < goodLocalThreshold M Ccg m n := by
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1)).2
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos m n) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (0 : ℝ) < Ccg⁻¹ := inv_pos.2 hCcg
  unfold goodLocalThreshold
  positivity

/-! ## The coarse-ellipticity clause of `e.good.local.events` -/

/-- The second inequality of `e.good.local.events` (ABK26), as
an event: the middle threshold is below
`3^{-(1/4)(n-m)_+} lambda_{1/8,2}(z+square_m; a_n)`, where `m = Q.scale` and `z`
is the base point of `Q`. -/
def goodLocalEllipticity (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n : ℤ) : Set (CutoffSample d) :=
  {omega | goodLocalThreshold M Ccg Q.scale n ≤
    (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale n) *
      cubeLowerEllipticity M Q n (1 / 8) (by norm_num)
        exponentTwo omega}

theorem measurableSet_goodLocalEllipticity (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    MeasurableSet (goodLocalEllipticity M Ccg Q n) :=
  measurableSet_le measurable_const
    ((measurable_cubeLowerEllipticity M Q n (1 / 8) (by norm_num)
      exponentTwo).const_mul _)

/-- The manuscript's coarse-ellipticity failure event of the decomposition in the
proof of `l.bad.event.lemma` (ABK26): `{ lambda^{-1}_{1/8,2}(z+square_m; a_n)
sigmaBar_{n-1} > 2. 3^{(1/4)(n-m)_+} C_{(e.cg.ellip.lower)} }`. -/
def coarseEllipticityFailure (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n : ℤ) : Set (CutoffSample d) :=
  {omega | 2 * (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) * Ccg <
    cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega *
      ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))}

/-- **The decomposition step of `l.bad.event.lemma`** (ABK26).  Wherever the
representative of `lambda^{-1}_{1/8,2}` is positive, failure of the
coarse-ellipticity clause of `e.good.local.events` is exactly the manuscript's
event `{ lambda^{-1}_{1/8,2} sigmaBar_{n-1} > 2 . 3^{(1/4)(n-m)_+} C }`. -/
theorem notMem_goodLocalEllipticity_iff (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (n : ℤ) {omega : CutoffSample d}
    (hpos : 0 < cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num)
      exponentTwo omega) :
    omega ∉ goodLocalEllipticity M Ccg Q n ↔
      omega ∈ coarseEllipticityFailure M Ccg Q n := by
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1)).2
  set p : ℝ := scaleGapPos Q.scale n with hp
  set X : ℝ := cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num)
    exponentTwo omega with hX
  set sig : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) with hsigdef
  set A : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ) * p) with hA
  have hApos : (0 : ℝ) < A := Real.rpow_pos_of_pos (by norm_num) _
  have hAsq : (3 : ℝ) ^ (-(1 / 2 : ℝ) * p) = A * A := by
    rw [hA, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hAinv : (3 : ℝ) ^ ((1 / 4 : ℝ) * p) = A⁻¹ := by
    rw [hA, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hXne : X ≠ 0 := ne_of_gt hpos
  have hCne : Ccg ≠ 0 := ne_of_gt hCcg
  have hk : (0 : ℝ) < 2 * Ccg * X := by positivity
  -- membership, unfolded
  have hmem : (omega ∉ goodLocalEllipticity M Ccg Q n) ↔
      A * X⁻¹ < (1 / 2 : ℝ) * Ccg⁻¹ * (A * A) * sig := by
    rw [goodLocalEllipticity, Set.mem_ofPred_eq, not_le, goodLocalThreshold,
      cubeLowerEllipticity, ← hp, ← hA, ← hX, ← hsigdef, hAsq]
  have hfail : (omega ∈ coarseEllipticityFailure M Ccg Q n) ↔
      2 * A⁻¹ * Ccg < X * sig := by
    rw [coarseEllipticityFailure, Set.mem_ofPred_eq, ← hp, ← hX, ← hsigdef, hAinv]
  rw [hmem, hfail]
  -- multiply both sides of the first inequality by `2 * Ccg * X > 0`
  have hleft : A * X⁻¹ * (2 * Ccg * X) = 2 * A * Ccg := by
    field_simp
  have hright : (1 / 2 : ℝ) * Ccg⁻¹ * (A * A) * sig * (2 * Ccg * X) =
      A * (A * sig * X) := by
    field_simp
  have hstep1 : (A * X⁻¹ < (1 / 2 : ℝ) * Ccg⁻¹ * (A * A) * sig) ↔
      2 * A * Ccg < A * (A * sig * X) := by
    rw [← mul_lt_mul_iff_of_pos_right hk, hleft, hright]
  -- multiply both sides of the second inequality by `A > 0`
  have hleft' : 2 * A⁻¹ * Ccg * A = 2 * Ccg := by
    field_simp
  have hright' : X * sig * A = A * sig * X := by ring
  have hstep2 : (2 * A⁻¹ * Ccg < X * sig) ↔ 2 * Ccg < A * sig * X := by
    rw [← mul_lt_mul_iff_of_pos_right hApos, hleft', hright']
  rw [hstep1, hstep2, show 2 * A * Ccg = A * (2 * Ccg) by ring]
  exact mul_lt_mul_iff_of_pos_left hApos

/-- The identification of the previous theorem, almost everywhere: the
representative of `lambda^{-1}_{1/8,2}` is almost surely positive. -/
theorem compl_goodLocalEllipticity_ae_eq (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (n : ℤ) :
    (goodLocalEllipticity M Ccg Q n)ᶜ
        =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      coarseEllipticityFailure M Ccg Q n := by
  refine Filter.eventuallyEqSet_iff.mpr ?_
  filter_upwards [cubeLowerEllipticityInv_pos_ae M Q n (1 / 8) (by norm_num)
    exponentTwo] with omega homega
  exact notMem_goodLocalEllipticity_iff M hCcg Q n homega

/-- **The first reduction in the proof of `l.bad.event.lemma`** (ABK26): the
probability that the coarse-ellipticity clause of `e.good.local.events` fails is
the probability of the manuscript's coarse-ellipticity failure event. -/
theorem measureReal_compl_goodLocalEllipticity (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (n : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        (goodLocalEllipticity M Ccg Q n)ᶜ =
      (Cutoff.cutoffSampleLaw M).toMeasure.real
        (coarseEllipticityFailure M Ccg Q n) :=
  measureReal_congr (compl_goodLocalEllipticity_ae_eq M hCcg Q n)

end

end Algsuperdiff.Section3.Provider.BadEvents
