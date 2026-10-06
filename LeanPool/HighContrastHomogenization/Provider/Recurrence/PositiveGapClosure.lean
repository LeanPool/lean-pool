/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# High-contrast homogenization: Provider.Recurrence.PositiveGapClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The positive-gap estimate read at the carriers of the fixed-grid recurrence

`l.fixed.geometry.positive.gap` is proved for abstract random blocks: a positive excess `D`
caught below `Ĝ = P + Y`, a bound `b` on the mean of `tr D`, and the mixed norms
`x = ‖D‖_{L^Q(S_Q)}`, `y = ‖Y‖_{L^Q(S_Q)}`.  Three passages carry it onto the
data of `p.fixed.geometry.parent.child.recurrence`, and they are taken here.

*The expectation identities.*  With `F̂` the response over the parent cell and
`Ĝ` the average of the responses over its aligned children, both normalized by
the parent mean `E_p^q`, the reference proof records `E[D] = B` and
`E[tr D] = b` for `D = Ĝ - F̂` and `B = P_{j,p}^q - I`.  Both are the
interchange of a fixed linear functional with the block-valued Bochner integral:
normalization is a two-sided multiplication by a deterministic matrix and the
trace is a linear functional, so each passes through.  The mean of the
normalized parent response is the identity and the mean of the normalized
average is the relative mean, so `E[D] = P_{j,p}^q - I`.  Since `D` is positive
along every realization, the `L^1` norm of `tr D` is its mean, which is the
fail-closed form the integrated trace-power display takes as its gap hypothesis.

*The finiteness read-back.*  The integrated display is an inequality in
`ℝ≥0∞`.  On the event that the two mixed norms are finite it becomes the
printed quadratic inequality between real numbers, and the two constants it
carries are reconciled into the single constant `C = 2^{Q-2}(2m)^{1-1/Q}` the
absorption step takes, at the cost of `(2m)^{1-1/Q} ≥ 1`.

*The mixed-norm triangle step.*  The closing estimate of `l.fixed.geometry.positive.gap` is
pointwise; the conclusion is between mixed norms.  Passing between them costs
the `L^Q` norm of a constant, which is that constant exactly because the law is
a probability measure — the one place in the chain where the normalization of
the law is genuinely used.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Flattening the block difference and the normalized difference -/

/-- The flattening of a difference of doubled blocks is the difference of the
flattenings. -/
theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  rw [Matrix.sub_apply, toFullBlockMat_blockSub_apply]

/-- The flattening of the `F`-normalized difference, expanded as the difference
of the two congruences. -/
theorem toFullBlockMat_normalizedBlock_blockSub (X Y F : BlockMat d) :
    toFullBlockMat (normalizedBlock (blockSub X Y) F) =
      matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat F)⁻¹ -
        matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat Y * matSqrt (toFullBlockMat F)⁻¹ := by
  rw [toFullBlockMat_normalizedBlock, toFullBlockMat_blockSub, Matrix.mul_sub, Matrix.sub_mul]

/-! ## Entrywise integrability of a block-valued map -/

/-- The identity, read as a continuous linear map from the coordinatewise
(finite-product) presentation of `FullBlockMat d` into the matrix type itself.
Continuity is automatic on a finite-dimensional space; the map exists only to
move Bochner-integral values between the two topologically identical but
differently normed presentations `FullBlockMat d` carries — the Loewner-order
one open in this file and the coordinatewise one the generic product API
uses. -/
@[expose]
public def piToFullBlockMatCLM :
    (BlockCoord d → BlockCoord d → ℝ) →L[ℝ] FullBlockMat d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

private theorem piToFullBlockMatCLM_apply (M : BlockCoord d → BlockCoord d → ℝ) :
    piToFullBlockMatCLM M = M := rfl

/-- A block-valued map is Bochner integrable exactly when every one of its
entries is: `FullBlockMat d` carries its Loewner-order topology, which agrees
with the coordinatewise topology it inherits as a finite product of reals,
and the entrywise reading is the one the generic product API is stated in. -/
private theorem integrable_fullBlockMat_iff {P : Measure (CoeffSpace d)}
    {f : CoeffSpace d → FullBlockMat d} :
    Integrable f P ↔ ∀ i j : BlockCoord d, Integrable (fun a => f a i j) P := by
  constructor
  · intro hf i j
    have h := (hf.eval i).eval j
    convert h using 1
  · intro hf
    refine Integrable.of_eval fun i => Integrable.of_eval fun j => ?_
    have h := hf i j
    convert h using 1

/-- The coordinatewise reading of an integrable block-valued map is itself
integrable for the generic product API. -/
private theorem integrable_pi_of_integrable {P : Measure (CoeffSpace d)}
    {f : CoeffSpace d → FullBlockMat d} (hf : Integrable f P) :
    Integrable (fun a => (f a : BlockCoord d → BlockCoord d → ℝ)) P := by
  convert hf using 1

/-- **The Bochner integral of a block-valued map is computed entrywise.** -/
private theorem integral_fullBlockMat_apply {P : Measure (CoeffSpace d)}
    {f : CoeffSpace d → FullBlockMat d} (hf : Integrable f P) (i j : BlockCoord d) :
    (∫ a, f a ∂P) i j = ∫ a, f a i j ∂P := by
  have hf' := integrable_pi_of_integrable hf
  have heq : ∫ a, f a ∂P =
      piToFullBlockMatCLM (∫ a, (f a : BlockCoord d → BlockCoord d → ℝ) ∂P) :=
    piToFullBlockMatCLM.integral_comp_comm hf'
  rw [heq, piToFullBlockMatCLM_apply, congrFun (eval_integral hf'.eval i) j]
  exact eval_integral (hf'.eval i).eval j

/-- The difference of two block-valued maps that are separately Bochner
integrable is integrable, read entrywise to sidestep the mismatch between the
Loewner-order and coordinatewise topologies on `FullBlockMat d`. -/
private theorem integrable_sub_fullBlockMat {P : Measure (CoeffSpace d)}
    {f g : CoeffSpace d → FullBlockMat d} (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => f a - g a) P := by
  refine integrable_fullBlockMat_iff.mpr fun i j => ?_
  have hfij := integrable_fullBlockMat_iff.mp hf i j
  have hgij := integrable_fullBlockMat_iff.mp hg i j
  exact hfij.sub hgij

/-- The Bochner integral of a difference of block-valued maps is the
difference of the integrals, again read entrywise. -/
private theorem integral_sub_fullBlockMat {P : Measure (CoeffSpace d)}
    {f g : CoeffSpace d → FullBlockMat d} (hf : Integrable f P) (hg : Integrable g P) :
    ∫ a, (f a - g a) ∂P = (∫ a, f a ∂P) - ∫ a, g a ∂P := by
  have hsub := integrable_sub_fullBlockMat hf hg
  ext i j
  have hL : (∫ a, (f a - g a) ∂P) i j = ∫ a, (f a i j - g a i j) ∂P := by
    rw [integral_fullBlockMat_apply hsub i j]
    simp only [Matrix.sub_apply]
  have hR : ((∫ a, f a ∂P) - ∫ a, g a ∂P) i j =
      (∫ a, f a i j ∂P) - ∫ a, g a i j ∂P := by
    rw [Matrix.sub_apply, integral_fullBlockMat_apply hf i j, integral_fullBlockMat_apply hg i j]
  rw [hL, hR,
    integral_sub (integrable_fullBlockMat_iff.mp hf i j) (integrable_fullBlockMat_iff.mp hg i j)]

/-! ## The trace against the block-valued integral -/

/-- **The trace passes through the block-valued Bochner integral**, being a
linear functional on a finite-dimensional space. -/
theorem integral_blockTrace {P : Measure (CoeffSpace d)} {D : CoeffSpace d → BlockMat d}
    (hint : Integrable (fun a => toFullBlockMat (D a)) P) :
    ∫ a, blockTrace (D a) ∂P = Matrix.trace (∫ a, toFullBlockMat (D a) ∂P) := by
  show ∫ a, ∑ i : BlockCoord d, toFullBlockMat (D a) i i ∂P =
    ∑ i : BlockCoord d, (∫ a, toFullBlockMat (D a) ∂P) i i
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_fullBlockMat_iff.mp hint i i)]
  exact Finset.sum_congr rfl fun i _ => (integral_fullBlockMat_apply hint i i).symm

/-- The trace of an integrable block-valued map is integrable. -/
theorem integrable_blockTrace {P : Measure (CoeffSpace d)} {D : CoeffSpace d → BlockMat d}
    (hint : Integrable (fun a => toFullBlockMat (D a)) P) :
    Integrable (fun a => blockTrace (D a)) P := by
  show Integrable (fun a => ∑ i : BlockCoord d, toFullBlockMat (D a) i i) P
  exact integrable_finsetSum Finset.univ (fun i _ => integrable_fullBlockMat_iff.mp hint i i)

/-- **`E[tr D] = b`, fail-closed.**  For a block that is positive along every
realization the `L^1` norm of its trace is the mean of that trace, with no
finiteness hedge: the trace is already nonnegative, so no absolute value is
lost.  This is the form the gap hypothesis of the integrated trace-power display
is stated in. -/
theorem eLpNorm_blockTrace_eq_ofReal {P : Measure (CoeffSpace d)}
    {D : CoeffSpace d → BlockMat d} {c : ℝ}
    (hpos : ∀ a, (toFullBlockMat (D a)).PosSemidef)
    (hint : Integrable (fun a => toFullBlockMat (D a)) P)
    (hmean : ∫ a, blockTrace (D a) ∂P = c) :
    eLpNorm (fun a => blockTrace (D a)) 1 P = ENNReal.ofReal c := by
  have hnorm : ∫ a, ‖blockTrace (D a)‖ ∂P = c := by
    rw [← hmean]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
      Real.norm_of_nonneg (hpos a).trace_nonneg)
  rw [eLpNorm_one_eq_lintegral_enorm (integrable_blockTrace hint).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (integrable_blockTrace hint), hnorm]

/-! ## The expectation identities at the adapted means -/

/-- The normalized excess is Bochner integrable as soon as the two responses
are. -/
theorem integrable_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    {Gh : CoeffSpace d → BlockMat d} (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P) :
    Integrable (fun a => toFullBlockMat (normalizedBlock
      (blockSub (Gh a) (coarseBlock (adaptedCell q p) a)) (adaptedMean P q p))) P := by
  simp only [toFullBlockMat_normalizedBlock_blockSub]
  exact integrable_sub_fullBlockMat (integrable_mul_left_mul_right _ _ hGint)
    (integrable_mul_left_mul_right _ _ (integrable_toFullBlockMat hintp))

/-- **`0 ≤ D`.**  The excess of the aligned average over the response is
positive along every realization, congruence by the inverse square root of the
parent mean preserving the pathwise order. -/
theorem posSemidef_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {p : ℤ} (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef)
    {Gh : CoeffSpace d → BlockMat d}
    (hGle : ∀ a, toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤ toFullBlockMat (Gh a))
    (a : CoeffSpace d) :
    (toFullBlockMat (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
      (adaptedMean P q p))).PosSemidef := by
  have hS : (matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹)ᴴ =
      matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹ :=
    (matSqrt_spec hEp.inv.posSemidef).1.isHermitian
  have hdiff := (Matrix.le_iff.mp (hGle a)).mul_mul_conjTranspose_same
    (matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹)
  rw [hS, Matrix.mul_sub, Matrix.sub_mul] at hdiff
  rwa [toFullBlockMat_normalizedBlock_blockSub]

/-- **`E[D] = B`** (`l.fixed.geometry.positive.gap`, at the carriers of
`p.fixed.geometry.parent.child.recurrence`): the mean of the normalized excess of the aligned
average over the parent response is `P_{j,p}^q - I`.  The parent response
integrates to the parent mean, whose normalization by its own inverse square
root is the identity, and the aligned average integrates to the child mean,
whose normalization is the relative mean. -/
theorem integral_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j)) :
    ∫ a, toFullBlockMat (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
        (adaptedMean P q p)) ∂P =
      toFullBlockMat (relMean P q j p) - 1 := by
  set S : FullBlockMat d := matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹
  have hAint : Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCell q p) a)) P :=
    integrable_toFullBlockMat hintp
  simp only [toFullBlockMat_normalizedBlock_blockSub]
  rw [integral_sub_fullBlockMat (integrable_mul_left_mul_right S S hGint)
      (integrable_mul_left_mul_right S S hAint),
    integral_mul_left_mul_right S S hGint, integral_mul_left_mul_right S S hAint,
    hGmean, ← toFullBlockMat_adaptedMean_eq_integral hintp, toFullBlockMat_relMean,
    matSqrt_inv_conj hEp]

/-- **`E[tr D] = b`** (`l.fixed.geometry.positive.gap`, at the carriers of
`p.fixed.geometry.parent.child.recurrence`): the mean of the trace of the normalized excess
is the trace gap `tr(P_{j,p}^q - I)` of the relative mean. -/
theorem integral_blockTrace_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j)) :
    ∫ a, blockTrace (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
        (adaptedMean P q p)) ∂P =
      blockTrace (relMean P q j p) - 2 * (d : ℝ) := by
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  rw [integral_blockTrace (integrable_toFullBlockMat_normalizedBlock_blockSub hintp hGint),
    integral_toFullBlockMat_normalizedBlock_blockSub hintp hEp hGint hGmean, Matrix.trace_sub,
    Matrix.trace_one, hcard]
  rfl

/-- **The gap hypothesis of the integrated trace-power display, at the adapted
means.**  The `L^1` norm of the trace of the normalized excess is the trace gap
of the relative mean, so any bound on that gap is a bound in the fail-closed
form the display consumes. -/
theorem eLpNorm_blockTrace_normalizedBlock_blockSub_le {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} {b : ℝ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j))
    (hGle : ∀ a, toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤ toFullBlockMat (Gh a))
    (hb : blockTrace (relMean P q j p) - 2 * (d : ℝ) ≤ b) :
    eLpNorm (fun a => blockTrace (normalizedBlock
        (blockSub (Gh a) (coarseBlock (adaptedCell q p) a)) (adaptedMean P q p))) 1 P ≤
      ENNReal.ofReal b := by
  rw [eLpNorm_blockTrace_eq_ofReal
    (posSemidef_toFullBlockMat_normalizedBlock_blockSub hEp hGle)
    (integrable_toFullBlockMat_normalizedBlock_blockSub hintp hGint)
    (integral_blockTrace_normalizedBlock_blockSub hintp hEp hGint hGmean)]
  exact ENNReal.ofReal_le_ofReal hb

/-! ## The finiteness read-back of the quadratic display -/

/-- **The extended-real display, read back on finite mixed norms.**  A bound
`u^Q ≤ αb + β(y^{Q-1}x)` in `ℝ≥0∞` between the images of nonnegative reals is
that bound between the reals themselves, `ENNReal.ofReal` being an order
embedding on the nonnegative axis. -/
theorem rpow_le_add_mul_of_ofReal_le {Q α β b x y : ℝ} (hQ : 2 ≤ Q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ENNReal.ofReal x ^ Q ≤ ENNReal.ofReal (α * b) +
      ENNReal.ofReal β * (ENNReal.ofReal y ^ (Q - 1) * ENNReal.ofReal x)) :
    x ^ Q ≤ α * b + β * (y ^ (Q - 1) * x) := by
  have hrhs : (0 : ℝ) ≤ α * b + β * (y ^ (Q - 1) * x) :=
    add_nonneg (mul_nonneg hα hb) (mul_nonneg hβ (mul_nonneg (Real.rpow_nonneg hy _) hx))
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by linarith only [hQ] : (0 : ℝ) ≤ Q),
    ENNReal.ofReal_rpow_of_nonneg hy (by linarith only [hQ] : (0 : ℝ) ≤ Q - 1),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hy _), ← ENNReal.ofReal_mul hβ,
    ← ENNReal.ofReal_add (mul_nonneg hα hb)
      (mul_nonneg hβ (mul_nonneg (Real.rpow_nonneg hy _) hx))] at h
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp h

/-! ## The closing step in the mixed norm -/

end

end Recurrence
end HighContrast
end HCPolySupport
