/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# High-contrast homogenization: Entry.Setup.SchattenNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schatten Norm

The spectral bound of a doubled block and the Schatten norm the printed statements are stated with.

The spectral norm `|M|` of a symmetric positive semidefinite matrix is the least `t ≥ 0` with
`M ≤ t I`, encoded as `specBound`; `matSqrt` is its positive semidefinite square root.  On top of
these, the deterministic Schatten norm `|M|_{S_N}` and the mixed norm `‖H‖_{L^N(S_N)}` are those
of the display near `e.scale.selection.Q.choice`, and the predicate `SchattenMemLp` carries the
printed "`H` in `L^N(S_N)`" that the hypotheses of `l.fixed.geometry.positive.gap` use.
-/

section
/-!
## The scalar Loewner bound and the positive semidefinite square root

The print writes `|M|` for the spectral norm of a symmetric positive semidefinite matrix and
`m^{1/2}` for the positive square root.  This file proves that the encodings `specBound` and
`matSqrt` are those objects: `specBound M` is the least `t ≥ 0` with `M ≤ t I`, and
`matSqrt M` is *the* positive semidefinite square root, independently of the choice made in
its definition.
-/

open HCPolySupport.HighContrast (lambdaRef matSqrt matSqrt_eq specBound_nonneg)
namespace HCPolySupport.HighContrast

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem matVecMul_smul_one (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, mul_comm]

private theorem vecDot_smul_self (t : ℝ) (x : Vec d) : vecDot x (t • x) = t * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The scalar Loewner bound of `M` by `t` is the pointwise inequality of quadratic forms. -/
theorem matLoewnerLE_smul_one_iff (M : Mat d) (t : ℝ) :
    MatLoewnerLE M (t • (1 : Mat d)) ↔
      ∀ x : Vec d, vecDot x (matVecMul M x) ≤ t * vecNormSq x := by
  simp only [MatLoewnerLE, matVecMul_smul_one, vecDot_smul_self]
  constructor
  · intro h x
    have := h x
    linarith only [this]
  · intro h x
    have := h x
    linarith only [this]

private theorem specBoundSet_isClosed (M : Mat d) :
    IsClosed {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} := by
  have hset : {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} =
      Set.Ici 0 ∩ ⋂ x : Vec d, {t : ℝ | vecDot x (matVecMul M x) ≤ t * vecNormSq x} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter,
      matLoewnerLE_smul_one_iff]
  rw [hset]
  exact isClosed_Ici.inter (isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.mul continuous_const))

/-! ## The positive semidefinite square root -/

/-- On positive semidefinite data `matSqrt` is Mathlib's continuous-functional-calculus square
root, the object `explicitRoundedGrid` is written with. -/
theorem matSqrt_eq_cfc_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) : matSqrt M = CFC.sqrt M :=
  matSqrt_eq hM (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg M)) (CFC.sqrt_mul_sqrt_self M)

/-! ## Junk guards on the contrast constants -/

/-- `λ_0` is nonnegative, junk branch included. -/
theorem lambdaRef_nonneg (E : BlockMat d) : 0 ≤ lambdaRef E :=
  inv_nonneg.2 (specBound_nonneg _)

end

end HCPolySupport.HighContrast
end

section
/-!
## The Schatten norm `|M|_{S_N}` and the mixed norm `‖H‖_{L^N(S_N)}`

Near `e.scale.selection.Q.choice`:

> We write `|M|` for the operator norm of a matrix `M`. For `N ≥ 1` and a deterministic
> symmetric `2d`-by-`2d` matrix `M` with eigenvalues `λ_1(M), …, λ_{2d}(M)`, set
> `|M|_{S_N} := (∑_{j=1}^{2d} |λ_j(M)|^N)^{1/N}`.  For a random symmetric `2d`-by-`2d`
> matrix `H`, set `‖H‖_{L^N(S_N)} := (E[|H|_{S_N}^N])^{1/N}`.

Two renderings of the first display are given, and the reason is recorded here rather than
left for a reader to reconstruct (operating rules, the standing honesty rule).

* `schattenNormEigen` is the display symbol for symbol: the sum runs over the
  index type `BlockCoord d`, which has `2d` elements, and `hM.eigenvalues` is Mathlib's
  eigenvalue family of a Hermitian matrix.  It takes the symmetry of `M` as an argument,
  because Mathlib's eigenvalues of a matrix exist only relative to such a proof.
* `absSchattenNorm` is the same number written without that argument, through the continuous
  functional calculus of `x ↦ |x|^N`, and is the form every later definition uses: the
  fluctuation `V^q_j` whose Schatten norm the profile integrates is a random block, and a
  definition that carried an almost-everywhere symmetry proof could not be composed.

**These two are not proved equal here, and nothing below asserts it.**  `absSchattenNorm N M`
is `(tr |M|^N)^{1/N}`, which on a symmetric `M` is the printed eigenvalue sum and off the
symmetric matrices is `0` by the junk convention of `cfc`.  Discharging
`absSchattenNorm N M = schattenNormEigen hM N` for symmetric `M` is one of the eight equalities
left unproved here.

**The second display is real-valued, and the carrier is the predicate `SchattenMemLp`**.
The expectation `E[|H|_{S_N}^N]` is the Bochner integral of the real
function `a ↦ |H(a)|_{S_N}^N`, and `‖H‖_{L^N(S_N)}` is its `1/N`-th power.  Two consequences
are recorded rather than left to be discovered:

* On an integrand that is not `P`-integrable Mathlib's Bochner integral is `0`, so
  `lqSchattenNorm P N H` is junk there.  This is exactly what the printed "`H` in
  `L^N(S_N)`" excludes, and that phrase is `SchattenMemLp P N H`, carried as a premise where
  the paper carries it — not as an extra hypothesis, since the paper states its propositions
  for such matrices.  The printed occurrence is `l.fixed.geometry.positive.gap`
  (`l.fixed.geometry.positive.gap`): "let `F` and `G` be positive semidefinite random
  `2d`-by-`2d` matrices in `L^N(S_N)` such that `F ≤ G`".  (The old development asserted the
  same finiteness at each use site without naming it; this is the same content with the
  premise named.)
* There is exactly one definition per printed object: the `ℝ≥0∞` rendering of the mixed norm
  (`∫⁻` of `ENNReal.ofReal`, which fails closed at `∞`) and the subtype rendering of the
  carrier are both dropped.

An alternative encoding writes the deterministic Schatten norm with a real exponent as
`(tr ((H²)^{Q/2}))^{1/Q}` and the mixed norm as Mathlib's `eLpNorm`, which is `ℝ≥0∞`-valued;
that encoding has **no** carrier for "in `L^N(S_N)`" at all — finiteness is asserted at each
use site.  This file uses the spectral (functional-calculus) reading of the Schatten norm,
and states the content of "in `L^N(S_N)`" once as a predicate.  It does not use `(H²)^{Q/2}`,
which is the printed `∑|λ_j|^N` only after a squaring identity, in favour of `|x|^N` applied
directly; it does not use `eLpNorm`, whose `‖·‖₊` is a second absolute value the display does
not have; and it does not use the `ℝ≥0∞` value.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The Schatten norm of a deterministic block -/

/-- The Schatten norm `|M|_{S_N} = (∑_{j=1}^{2d} |λ_j(M)|^N)^{1/N}` of a symmetric
`2d`-by-`2d` matrix, as in the display near `e.scale.selection.Q.choice`.
The eigenvalue family is Mathlib's, so the symmetry of `M` is an explicit argument. -/
@[expose]
def schattenNormEigen {M : FullBlockMat d} (hM : M.IsHermitian) (N : ℝ) : ℝ :=
  (∑ j, |hM.eigenvalues j| ^ N) ^ N⁻¹

/-- The Schatten norm `|H|_{S_N}` of a doubled block, written `(tr |H|^N)^{1/N}` with the
continuous functional calculus of `x ↦ |x|^N`, so that it is a function of `H` alone.  On a
symmetric `H` this is the printed `(∑_{j=1}^{2d} |λ_j(H)|^N)^{1/N}`; off the symmetric
blocks the functional calculus is `0`.

The `schattenNorm` of the published `HCPoly` library (`HCPoly/Setup/Moments.lean`) is a
different function of `H`: it is `(tr (H²)^{Q/2})^{1/Q}`, the calculus of `x ↦ x^{Q/2}`
applied to `H²`.  The two agree on symmetric `H`, where the eigenvalues of `H²` are the
squares of those of `H`, but they are not definitionally equal and neither definition
restricts `H` to the symmetric blocks. -/
@[expose]
def absSchattenNorm (N : ℝ) (H : BlockMat d) : ℝ :=
  (Matrix.trace (cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H))) ^ N⁻¹

/-! ## The mixed norm of a random block -/

/-- The mixed norm `‖H‖_{L^N(S_N)} = (E[|H|_{S_N}^N])^{1/N}` of a random doubled block
(near `e.scale.selection.Q.choice`), real-valued: the expectation is the
Bochner integral of `a ↦ |H(a)|_{S_N}^N`.  On an integrand that is not `P`-integrable the
integral is Mathlib's junk `0`; the printed "`H` in `L^N(S_N)`" is `SchattenMemLp P N H`,
carried as a premise where the paper carries it. -/
@[expose]
def lqSchattenNorm (P : Measure (CoeffSpace d)) (N : ℝ) (H : CoeffSpace d → BlockMat d) :
    ℝ :=
  (∫ a, absSchattenNorm N (H a) ^ N ∂P) ^ N⁻¹

/-! ## The carrier: a random symmetric block in `L^N(S_N)` -/

/-- Measurability of a random doubled block for the law `P`, entry by entry; the shape is
the one `HasMeasurableCoarseBlock` of `HCPoly/Setup/Response.lean` already uses for the
coarse response. -/
@[expose]
def HasMeasurableBlock (P : Measure (CoeffSpace d)) (H : CoeffSpace d → BlockMat d) : Prop :=
  ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry (H a) α β) P

/-- "`H` is a random symmetric `2d`-by-`2d` matrix in `L^N(S_N)`" (near
`e.scale.selection.Q.choice`, as used in the hypotheses of the printed lemmas), as a predicate:
`H` is
measurable for the law, almost surely symmetric, and its `N`-th Schatten moment is
`P`-integrable, which under the real-valued reading of `‖·‖_{L^N(S_N)}` is what "in
`L^N(S_N)`" adds. -/
structure SchattenMemLp (P : Measure (CoeffSpace d)) (N : ℝ)
    (H : CoeffSpace d → BlockMat d) : Prop where
  /-- Every entry of `H` is almost surely strongly measurable for the law. -/
  measurable : HasMeasurableBlock P H
  /-- `H` is almost surely a symmetric matrix, as the print's "random symmetric matrix" says. -/
  symmetric : ∀ᵐ a ∂P, IsSymmetricBlockMat (H a)
  /-- The moment `E[|H|_{S_N}^N]` the mixed norm takes is a genuine expectation. -/
  integrable : Integrable (fun a => absSchattenNorm N (H a) ^ N) P

end

end HCPolySupport.HighContrast
end
