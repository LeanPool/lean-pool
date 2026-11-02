/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.ResponseSubadditivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.NormalizedLoading
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationErrorCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily

/-!
# Bridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From averaged local responses to the squared homogenization error

This module proves the display of ABK26,
  `avsum_{z in 3^{-h} Zd cap cu_0} J(z + cu_{-h}, sigma0^{-1/2} e, sigma0^{1/2} e; a)
     <= 3^{2 t h} mathcal E_{t,2,2}(cu_0; a, sigma0)^2`,

as a named node, for every depth `h in N`, every `t > 0` and every unit vector
`e in R^d`.

## The aggregation identity the bridge is derived from

For `p = q = 2` CoarseGraining's `Ch02.HomogenizationErrorOnCube Q t (.finite
2) (.finite 2)` squares to a *single* geometric aggregate.  Writing `N(R):=
Ch02.normalizedBlockResponseMax a0` for the one-cube quantity `max_{|e| = 1}
bfJ(R, bfA_0^{-1/2} e, bfA_0^{1/2} e; a)` of Definition `d.mathcal.E`, the `p =
2` scale response is the square root of the descendant average of `N`, so
squaring removes every root and leaves
  `mathcal E_{t,2,2}(Q; a, a0)^2
     = sum_{l = 0}^infty c_{t,2} 3^{-2 t l} avsum_{R at depth l} N(R)`,
  `c_{t,2} = 1 - 3^{-2 t}`,

which is `homogenizationErrorOnCube_finite_two_two_sq_eq_tsum` below.  The
weights `c_{t,2} 3^{-2 t l}` form a probability density on `N`, so a *single*
term of this series would only give the constant `c_{t,2}^{-1} 3^{2 t h}`, which
degenerates as `t -> 0`.  The sharp constant `3^{2 t h}` of the source display
comes from using the whole tail `l >= h`, together with the monotonicity in the
depth of the averaged responses, which is exactly the subadditivity patching of
`ResponseSubadditivity.lean`:
  `avsum_h J <= avsum_l J <= avsum_l N`  for every `l >= h`,
  `sum_{l >= h} c_{t,2} 3^{-2 t l} = 3^{-2 t h}`.

## Contents

* `homogenizationErrorOnCube_finite_two_two_sq_eq_tsum` - the aggregation
  identity above (no summability hypothesis: both sides are `0` when the series
  diverges);
* `summable_geometricWeight_mul_descendantsAverage_normalizedBlockResponseMax`
  - the series does converge, by CoarseGraining's uniform descendant bound;
* `descendantsAverage_responseJ_scalarLoading_le_rpow_mul_homogenizationErrorOnCube_sq`
  - the bridge for an arbitrary root cube;
* `descendantsAverage_responseJ_scalarLoading_le_rpow_mul_unitCubeHomogenizationError_sq`
  - the same statement against the frozen unit-cube quantity, reached through
  the frozen characterization theorem (`Classical.choose` is never unfolded).
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

/-- Bridge between CoarseGraining's explicit `Real.rpow` applications and the `^`
notation used by Mathlib's `rpow` lemmas. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## An abstract tail estimate

The arithmetic of the bridge is a statement about one nonnegative weighted
series and is isolated here, away from the multiscale definitions. -/

/-- If the terms `A l` of a nonnegative weighted series dominate a constant `G`
from the index `h` on, then the tail mass of the weights times `G` is below the
total sum. -/
private theorem tail_weight_mul_le_tsum
    {w A : ℕ → ℝ} {G : ℝ} (h : ℕ)
    (hw : ∀ l, 0 ≤ w l) (hA : ∀ l, 0 ≤ A l)
    (hGA : ∀ k : ℕ, G ≤ A (k + h))
    (hsumw : Summable w) (hsum : Summable fun l => w l * A l) :
    (∑' k : ℕ, w (k + h)) * G ≤ ∑' l : ℕ, w l * A l := by
  have hwshift : Summable fun k : ℕ => w (k + h) :=
    (summable_nat_add_iff (f := w) h).mpr hsumw
  have hGshift : Summable fun k : ℕ => w (k + h) * G := hwshift.mul_right G
  have hAshift : Summable fun k : ℕ => w (k + h) * A (k + h) :=
    (summable_nat_add_iff (f := fun l : ℕ => w l * A l) h).mpr hsum
  have hstep1 : ∑' k : ℕ, w (k + h) * G ≤ ∑' k : ℕ, w (k + h) * A (k + h) := by
    refine Summable.tsum_le_tsum ?_ hGshift hAshift
    intro k
    exact mul_le_mul_of_nonneg_left (hGA k) (hw (k + h))
  have hsplit :=
    Summable.sum_add_tsum_nat_add (f := fun l : ℕ => w l * A l) h hsum
  have hrange : 0 ≤ ∑ i ∈ Finset.range h, w i * A i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hA i)
  have hstep2 : ∑' k : ℕ, w (k + h) * A (k + h) ≤ ∑' l : ℕ, w l * A l := by
    linarith [hsplit]
  calc
    (∑' k : ℕ, w (k + h)) * G = ∑' k : ℕ, w (k + h) * G := by
        rw [tsum_mul_right]
    _ ≤ ∑' k : ℕ, w (k + h) * A (k + h) := hstep1
    _ ≤ ∑' l : ℕ, w l * A l := hstep2

/-! ## Elementary facts about the geometric weights -/

variable {d : ℕ}

/-- `Ch02.geometricWeight s 2 l = c_{s,2} r^l` with `r = 3^{-2 s}`. -/
private theorem geometricWeight_two_eq_pow (s : ℝ) (l : ℕ) :
    Ch02.geometricWeight s 2 l =
      Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ l := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hpow : (Real.rpow (3 : ℝ) (-s * 2)) ^ l =
      Real.rpow (3 : ℝ) (-s * 2 * (l : ℝ)) := by
    simp only [rpow_eq_pow]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s * 2)) l, ← Real.rpow_mul h3]
  rw [Ch02.geometricWeight, hpow]

private theorem geometric_ratio_pos (s : ℝ) : 0 < Real.rpow (3 : ℝ) (-s * 2) :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem geometric_ratio_lt_one {s : ℝ} (hs : 0 < s) :
    Real.rpow (3 : ℝ) (-s * 2) < 1 := by
  simp only [rpow_eq_pow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)

private theorem geometricDiscount_two_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Ch02.geometricDiscount s 2 := by
  have hle : Real.rpow (3 : ℝ) (-s * 2) ≤ 1 := by
    simp only [rpow_eq_pow]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  simpa [Ch02.geometricDiscount] using hle

private theorem geometricWeight_two_nonneg {s : ℝ} (hs : 0 ≤ s) (l : ℕ) :
    0 ≤ Ch02.geometricWeight s 2 l := by
  rw [geometricWeight_two_eq_pow]
  exact mul_nonneg (geometricDiscount_two_nonneg hs)
    (pow_nonneg (le_of_lt (geometric_ratio_pos s)) l)

private theorem summable_geometricWeight_two {s : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ => Ch02.geometricWeight s 2 l := by
  have hfun : (fun l : ℕ => Ch02.geometricWeight s 2 l) =
      fun l : ℕ => Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ l := by
    funext l
    exact geometricWeight_two_eq_pow s l
  rw [hfun]
  exact (summable_geometric_of_lt_one (le_of_lt (geometric_ratio_pos s))
    (geometric_ratio_lt_one hs)).mul_left _

/-- The geometric tail mass of the weights from depth `h` on is exactly
`3^{-2 s h}`.  This is what produces the sharp constant of the source display. -/
private theorem tsum_geometricWeight_two_shift {s : ℝ} (hs : 0 < s) (h : ℕ) :
    ∑' k : ℕ, Ch02.geometricWeight s 2 (k + h) =
      (Real.rpow (3 : ℝ) (-s * 2)) ^ h := by
  have hr0 : 0 < Real.rpow (3 : ℝ) (-s * 2) := geometric_ratio_pos s
  have hr1 : Real.rpow (3 : ℝ) (-s * 2) < 1 := geometric_ratio_lt_one hs
  have hne : (1 : ℝ) - Real.rpow (3 : ℝ) (-s * 2) ≠ 0 := by
    have hpos : 0 < (1 : ℝ) - Real.rpow (3 : ℝ) (-s * 2) := by linarith
    exact ne_of_gt hpos
  have hfun :
      (fun k : ℕ => Ch02.geometricWeight s 2 (k + h)) =
        fun k : ℕ =>
          (Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ h) *
            (Real.rpow (3 : ℝ) (-s * 2)) ^ k := by
    funext k
    rw [geometricWeight_two_eq_pow, pow_add]
    ring
  have hcancel :
      (1 - Real.rpow (3 : ℝ) (-s * 2)) * (1 - Real.rpow (3 : ℝ) (-s * 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hne
  rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hr0) hr1]
  have hdisc : Ch02.geometricDiscount s 2 = 1 - Real.rpow (3 : ℝ) (-s * 2) := rfl
  rw [hdisc]
  calc
    (1 - Real.rpow (3 : ℝ) (-s * 2)) * (Real.rpow (3 : ℝ) (-s * 2)) ^ h *
        (1 - Real.rpow (3 : ℝ) (-s * 2))⁻¹
        = ((1 - Real.rpow (3 : ℝ) (-s * 2)) *
            (1 - Real.rpow (3 : ℝ) (-s * 2))⁻¹) *
          (Real.rpow (3 : ℝ) (-s * 2)) ^ h := by ring
    _ = (Real.rpow (3 : ℝ) (-s * 2)) ^ h := by rw [hcancel, one_mul]

/-! ## The `p = q = 2` aggregation identity -/

/-- Descendants at scale `Q.scale - l` are the descendants at depth `l`, so the
finite average appearing in `Ch02.scaleResponseAtScale` is `descendantsAverage`. -/
private theorem finsetAverageReal_descendantsAtScale_eq_descendantsAverage
    (Q : TriadicCube d) (l : ℕ) (f : TriadicCube d → ℝ) :
    finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ))) f =
      descendantsAverage Q l f := by
  have hk : Q.scale - (l : ℤ) ≤ Q.scale := by omega
  have htoNat : Int.toNat (Q.scale - (Q.scale - (l : ℤ))) = l := by omega
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk, htoNat]
  rfl

/-- Membership at depth `l` as membership at scale `Q.scale - l`. -/
private theorem mem_descendantsAtScale_of_mem_descendantsAtDepth
    {Q R : TriadicCube d} {l : ℕ} (hR : R ∈ descendantsAtDepth Q l) :
    R ∈ descendantsAtScale Q (Q.scale - (l : ℤ)) := by
  have hk : Q.scale - (l : ℤ) ≤ Q.scale := by omega
  have htoNat : Int.toNat (Q.scale - (Q.scale - (l : ℤ))) = l := by omega
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk, htoNat]
  exact hR

variable [NeZero d]

omit [NeZero d] in
/-- At `p = 2` the squared scale response is the descendant average of the
one-cube normalized block response. -/
private theorem scaleResponseAtScale_finite_two_sq
    (Q : TriadicCube d) (l : ℕ) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    (Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) (.finite 2) F a0) ^ 2 =
      descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) := by
  have hnonneg :
      0 ≤ descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) :=
    descendantsAverage_nonneg Q l _
      (fun R _hR => normalizedBlockResponseMax_nonneg R F a0)
  have hfun :
      (fun R : TriadicCube d =>
          Real.rpow (Ch02.normalizedBlockResponseMax R F a0) ((2 : ℝ) / 2)) =
        fun R : TriadicCube d => Ch02.normalizedBlockResponseMax R F a0 := by
    funext R
    norm_num
  change (Real.rpow
      (finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) ((2 : ℝ) / 2)))
      (1 / 2)) ^ 2 = _
  rw [hfun, finsetAverageReal_descendantsAtScale_eq_descendantsAverage Q l]
  simp only [rpow_eq_pow]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt hnonneg

omit [NeZero d] in
/-- **The exact `p = q = 2` aggregation identity for `mathcal E`.**  Squaring
the homogenization error at `p = q = 2` produces exactly the geometrically
weighted sum, over all depths, of the descendant averages of the one-cube
normalized block responses. -/
theorem homogenizationErrorOnCube_finite_two_two_sq_eq_tsum
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ}
    (hs : 0 ≤ s) :
    (Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 =
      ∑' l : ℕ,
        Ch02.geometricWeight s 2 l *
          descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) := by
  have hnonneg :
      0 ≤ ∑' l : ℕ,
        Ch02.geometricWeight s 2 l *
          descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) := by
    refine tsum_nonneg fun l => mul_nonneg (geometricWeight_two_nonneg hs l) ?_
    exact descendantsAverage_nonneg Q l _
      (fun R _hR => normalizedBlockResponseMax_nonneg R F a0)
  have hEq :
      Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 =
        Real.rpow
          (∑' l : ℕ,
            Ch02.geometricWeight s 2 l *
              descendantsAverage Q l
                (fun R => Ch02.normalizedBlockResponseMax R F a0)) (1 / 2) := by
    change Ch02.HomogenizationErrorFinite Q Q.scale s (.finite 2) 2 F a0 = _
    unfold Ch02.HomogenizationErrorFinite
    refine congrArg (fun x : ℝ => Real.rpow x (1 / 2)) ?_
    refine tsum_congr fun l => ?_
    rw [rpow_eq_pow, Real.rpow_two, scaleResponseAtScale_finite_two_sq Q l F a0]
  rw [hEq]
  simp only [rpow_eq_pow]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt hnonneg

/-! ## Convergence of the aggregate -/

/-- The descendant average of the one-cube normalized block responses is bounded by
CoarseGraining's uniform descendant bound at the root cube, uniformly in the
depth. -/
private theorem descendantsAverage_normalizedBlockResponseMax_le_uniform
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) (a0 : Mat d) (l : ℕ) :
    descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) ≤
      normalizedBlockResponseUniformBound Q F a0 := by
  have hpt :
      ∀ R ∈ descendantsAtDepth Q l,
        Ch02.normalizedBlockResponseMax R F a0 ≤
          normalizedBlockResponseUniformBound Q F a0 := by
    intro R hR
    exact normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
      (a := F) (Q := Q) (R := R) (k := Q.scale - (l : ℤ)) a0
      (mem_descendantsAtScale_of_mem_descendantsAtDepth hR)
  calc
    descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0)
        ≤ descendantsAverage Q l
            (fun _ => normalizedBlockResponseUniformBound Q F a0) :=
          descendantsAverage_le_descendantsAverage Q l hpt
    _ = normalizedBlockResponseUniformBound Q F a0 :=
          descendantsAverage_const Q l _

/-- The `p = q = 2` aggregate converges for every positive exponent. -/
theorem summable_geometricWeight_mul_descendantsAverage_normalizedBlockResponseMax
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ}
    (hs : 0 < s) :
    Summable (fun l : ℕ =>
      Ch02.geometricWeight s 2 l *
        descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0)) := by
  have hr0 : 0 < Real.rpow (3 : ℝ) (-s * 2) := geometric_ratio_pos s
  have hr1 : Real.rpow (3 : ℝ) (-s * 2) < 1 := geometric_ratio_lt_one hs
  have hdisc : 0 ≤ Ch02.geometricDiscount s 2 :=
    geometricDiscount_two_nonneg (le_of_lt hs)
  have hBnonneg : 0 ≤ normalizedBlockResponseUniformBound Q F a0 :=
    le_trans (descendantsAverage_nonneg Q 0 _
      (fun R _hR => normalizedBlockResponseMax_nonneg R F a0))
      (descendantsAverage_normalizedBlockResponseMax_le_uniform Q F a0 0)
  have hmajor :
      Summable (fun l : ℕ =>
        (Ch02.geometricDiscount s 2 * normalizedBlockResponseUniformBound Q F a0) *
          (Real.rpow (3 : ℝ) (-s * 2)) ^ l) :=
    (summable_geometric_of_lt_one (le_of_lt hr0) hr1).mul_left _
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro l
    refine mul_nonneg (geometricWeight_two_nonneg (le_of_lt hs) l) ?_
    exact descendantsAverage_nonneg Q l _
      (fun R _hR => normalizedBlockResponseMax_nonneg R F a0)
  · intro l
    rw [geometricWeight_two_eq_pow]
    have hstep :
        descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0) ≤
          normalizedBlockResponseUniformBound Q F a0 :=
      descendantsAverage_normalizedBlockResponseMax_le_uniform Q F a0 l
    have hcoef : 0 ≤ Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ l :=
      mul_nonneg hdisc (pow_nonneg (le_of_lt hr0) l)
    calc
      Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ l *
          descendantsAverage Q l (fun R => Ch02.normalizedBlockResponseMax R F a0)
          ≤ Ch02.geometricDiscount s 2 * (Real.rpow (3 : ℝ) (-s * 2)) ^ l *
              normalizedBlockResponseUniformBound Q F a0 :=
            mul_le_mul_of_nonneg_left hstep hcoef
      _ = Ch02.geometricDiscount s 2 * normalizedBlockResponseUniformBound Q F a0 *
            (Real.rpow (3 : ℝ) (-s * 2)) ^ l := by ring

/-! ## The bridge -/

/-- **The homogenization-error bridge.**  For a positive scalar background
`sigma0`, a unit vector `e` in `R^d`, a positive exponent `t` and any depth
`h`, the unweighted average over the depth-`h` descendants of the
`sigma0`-loaded scalar responses is bounded by `3^{2 t h}` times the squared
homogenization error of the root cube.  This is the display of ABK26. -/
theorem descendantsAverage_responseJ_scalarLoading_le_rpow_mul_homogenizationErrorOnCube_sq
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) {t σ0 : ℝ} (ht : 0 < t)
    (hσ0 : 0 < σ0) {e : Vec d} (he : vecNorm e = 1) (h : ℕ) :
    descendantsAverage Q h
        (fun R => responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)) ≤
      Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
        (Ch02.HomogenizationErrorOnCube Q t (.finite 2) (.finite 2) F
          (scalarMatrix (d := d) σ0)) ^ 2 := by
  classical
  have hAnonneg :
      ∀ l : ℕ,
        0 ≤ descendantsAverage Q l
          (fun R => Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0)) := by
    intro l
    exact descendantsAverage_nonneg Q l _
      (fun R _hR => normalizedBlockResponseMax_nonneg R F _)
  have hGA :
      ∀ k : ℕ,
        descendantsAverage Q h
            (fun R => responseJ (cubeDomain R) (F.coeffOn R)
              ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)) ≤
          descendantsAverage Q (k + h)
            (fun R => Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0)) := by
    intro k
    have hmono := descendantsAverage_responseJ_mono F Q (Nat.le_add_left h k)
      ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)
    have hpt :
        ∀ R ∈ descendantsAtDepth Q (k + h),
          responseJ (cubeDomain R) (F.coeffOn R)
              ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) ≤
            Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) := by
      intro R _hR
      exact responseJ_scalarLoading_le_normalizedBlockResponseMax F R hσ0 he
    exact le_trans hmono
      (descendantsAverage_le_descendantsAverage Q (k + h) hpt)
  have htail :=
    tail_weight_mul_le_tsum (w := fun l : ℕ => Ch02.geometricWeight t 2 l)
      (A := fun l : ℕ =>
        descendantsAverage Q l
          (fun R => Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0)))
      (G := descendantsAverage Q h
        (fun R => responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)))
      h (fun l => geometricWeight_two_nonneg (le_of_lt ht) l) hAnonneg hGA
      (summable_geometricWeight_two ht)
      (summable_geometricWeight_mul_descendantsAverage_normalizedBlockResponseMax
        Q F (scalarMatrix (d := d) σ0) ht)
  rw [tsum_geometricWeight_two_shift ht h,
    ← homogenizationErrorOnCube_finite_two_two_sq_eq_tsum Q F
      (scalarMatrix (d := d) σ0) (le_of_lt ht)] at htail
  -- convert the geometric factor and cancel it
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hexp : -t * 2 * (h : ℝ) = -(2 * t * (h : ℝ)) := by ring
  have hpow : (Real.rpow (3 : ℝ) (-t * 2)) ^ h =
      Real.rpow (3 : ℝ) (-(2 * t * (h : ℝ))) := by
    simp only [rpow_eq_pow]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-t * 2)) h, ← Real.rpow_mul h3, hexp]
  have hposFactor : 0 < Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel :
      Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
          Real.rpow (3 : ℝ) (-(2 * t * (h : ℝ))) = 1 := by
    simp only [rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  rw [hpow] at htail
  calc
    descendantsAverage Q h
        (fun R => responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e))
        = Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
            (Real.rpow (3 : ℝ) (-(2 * t * (h : ℝ))) *
              descendantsAverage Q h
                (fun R => responseJ (cubeDomain R) (F.coeffOn R)
                  ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e))) := by
          rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
          (Ch02.HomogenizationErrorOnCube Q t (.finite 2) (.finite 2) F
            (scalarMatrix (d := d) σ0)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hposFactor)
          simpa [mul_comm] using htail

/-- **The bridge against the frozen unit-cube homogenization error.**  Routed
through the frozen characterization theorem; `Classical.choose` is never
unfolded. -/
theorem descendantsAverage_responseJ_scalarLoading_le_rpow_mul_unitCubeHomogenizationError_sq
    (a : CoeffOn (cubeDomain (originCube d 0))) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {t σ0 : ℝ} (ht : 0 < t) (hσ0 : 0 < σ0) {e : Vec d} (he : vecNorm e = 1)
    (h : ℕ) :
    descendantsAverage (originCube d 0) h
        (fun R => responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e)) ≤
      Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
        (Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError t
          (.finite 2) (.finite 2) a (scalarMatrix (d := d) σ0)) ^ 2 := by
  rw [Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
    t (.finite 2) (.finite 2) a (scalarMatrix (d := d) σ0) F hF]
  exact
    descendantsAverage_responseJ_scalarLoading_le_rpow_mul_homogenizationErrorOnCube_sq
      (originCube d 0) F ht hσ0 he h

end

end Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge
