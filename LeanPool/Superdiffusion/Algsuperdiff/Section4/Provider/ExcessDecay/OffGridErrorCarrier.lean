/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityCap
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilitySubadditivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Adapters

/-!
# OffGridErrorCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The multiscale error carrier of an **off-grid** cube

The `OffGridStability*.lean` modules deliver the geometry, the countable
subadditivity and the arithmetic of the printed transport
`e.mathcalE.stability.applied` (ABK26).  The composition they feed cannot even
be *stated* with CoarseGraining's carriers: `𝓔_{t,∞,2}` is
`HomogenizationErrorOnCube`, whose shells `descendantsAtScale` are **lattice**
cubes, so there is no CoarseGraining object for `𝓔_{t,∞,2}(x + □_n)` at a real
translate `x`.  This module supplies that object.

## The design: a *set-level* doubled response, so no off-grid `Domain` is needed

CoarseGraining's `Ch02.doubledResponseJ` is indexed by a `Ch02.Domain` together
with a `Ch02.CoeffOn` on it, neither of which a real translate of a triadic
cube carries.  Instead of transporting those structures, this module takes
CoarseGraining's own scalar splitting

```
𝐉(U, (p,q), (q*,p*); a)
  = ½ J(U, p − p*, q* − q; a) + ½ J(U, p* + p, q* + q; aᵗ)
```

(`Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum`) as the **definition** of the
doubled response on an arbitrary measurable set, in terms of CoarseGraining's set-level
`Homogenization.ResponseJ`, which needs no domain structure at all.  The bridge
`setDoubledResponseJ_openCubeSet` proves that on a *grid* cube this definition agrees with
CoarseGraining's `Ch02.doubledResponseJ` on the nose, whenever the triadic family's cube
representative is the ambient field (which is how every CoarseGraining consumer builds it:
`Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField` makes it `rfl`).  Consequently

* `offGridBlockResponseMax 0 R g a0 = Ch02.normalizedBlockResponseMax a0`,
* `offGridErrorFunctional 0 P t g a0 = 𝓔_{t,∞,2}(P; A, a0)`,

so the off-grid carrier is a *conservative extension* of CoarseGraining's, not
a parallel invention: at zero translate it **is** CoarseGraining's quantity.

## The carrier-compatibility binder `hg` (disclosed)

Several statements below carry `hg : (A.coeffOn R).toCoeffField = g` (or its `∀
Q` form).  This is **typing/carrier data**, not a mathematical hypothesis of
any printed statement: it says the abstract `Ch02.TriadicCoeffFamily` and the
ambient `CoeffField` are the same object, which holds by `rfl` for every family
CoarseGraining constructs from an ambient field.  It is never used as a source
premise and never appears in a statement that claims a printed display.

## Main results

* `setDoubledResponseJ`, `setDoubledResponseJ_openCubeSet` — the set-level
  doubled response and its agreement with CoarseGraining's on a grid cube.
* `offGridBlockResponseMax`, `offGridShellMax`, `offGridErrorFunctional` — the
  off-grid carrier, shell by shell.
* `offGridBlockResponseMax_zero_eq`, `offGridErrorFunctional_zero_eq` — the
  conservative-extension theorems.

## References

* ABK26, `e.mathcalE.stability.applied`.
* ABK26, `l.lambdas.stability`; `d.mathcal.E`.
* CoarseGraining,
  `Homogenization/Book/Ch02/Theorems/DeterministicIdentities.lean`
  (`doubledResponseJ_eq_half_responseJ_adjoint_sum`),
  `Homogenization/Internal/Ch02/Adapters.lean` (`book_responseJ_eq_ResponseJ`),
  `Homogenization/Book/Ch02/HomogenizationError.lean` (the shell carriers).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## 1. The adjoint of an elliptic field -/

/-- The adjoint field `aᵗ` is elliptic on the same set with the same constants.
CoarseGraining proves the matrix statement (`isEllipticMatrix_transpose`); only
the measurability clause has to be transposed. -/
theorem isEllipticFieldOn_adjointCoeffField {lam Lam : ℝ} {V : Set (Vec d)}
    {g : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V g) :
    IsEllipticFieldOn lam Lam V (adjointCoeffField g) := by
  classical
  refine ⟨?_, fun x hx => isEllipticMatrix_transpose (hEll.2 x hx)⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have h : Measurable (fun x : Vec d => if x ∈ V then g x j i else 0) :=
    measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 j) i
  exact h

/-! ## 2. The set-level doubled response -/

/-- **The doubled response functional on an arbitrary set.**

This is the right-hand side of CoarseGraining's scalar splitting
`Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum`, written with the
set-level `Homogenization.ResponseJ`, which requires no `Ch02.Domain`
structure.  On a grid cube it agrees with `Ch02.doubledResponseJ`
(`setDoubledResponseJ_openCubeSet`). -/
def setDoubledResponseJ (V : Set (Vec d)) (g : CoeffField d) (P Q : BlockVec d) : ℝ :=
  (1 / 2 : ℝ) * ResponseJ V (P.1 - Q.2) (Q.1 - P.2) g +
    (1 / 2 : ℝ) * ResponseJ V (Q.2 + P.1) (Q.1 + P.2) (adjointCoeffField g)

theorem setDoubledResponseJ_nonneg (V : Set (Vec d)) (g : CoeffField d) (P Q : BlockVec d) :
    0 ≤ setDoubledResponseJ V g P Q := by
  have h1 : 0 ≤ ResponseJ V (P.1 - Q.2) (Q.1 - P.2) g :=
    HCPolySupport.responseJ_nonneg V _ _ g
  have h2 : 0 ≤ ResponseJ V (Q.2 + P.1) (Q.1 + P.2) (adjointCoeffField g) :=
    HCPolySupport.responseJ_nonneg V _ _ (adjointCoeffField g)
  rw [setDoubledResponseJ]
  linarith only [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) h1,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) h2]

/-- Each scalar half of the doubled response is at most twice the whole: the two
summands are nonnegative. -/
theorem responseJ_le_two_mul_setDoubledResponseJ_left (V : Set (Vec d)) (g : CoeffField d)
    (P Q : BlockVec d) :
    ResponseJ V (P.1 - Q.2) (Q.1 - P.2) g ≤ 2 * setDoubledResponseJ V g P Q := by
  have h2 : 0 ≤ ResponseJ V (Q.2 + P.1) (Q.1 + P.2) (adjointCoeffField g) :=
    HCPolySupport.responseJ_nonneg V _ _ (adjointCoeffField g)
  rw [setDoubledResponseJ]
  linarith only [h2]

theorem responseJ_le_two_mul_setDoubledResponseJ_right (V : Set (Vec d)) (g : CoeffField d)
    (P Q : BlockVec d) :
    ResponseJ V (Q.2 + P.1) (Q.1 + P.2) (adjointCoeffField g) ≤
      2 * setDoubledResponseJ V g P Q := by
  have h1 : 0 ≤ ResponseJ V (P.1 - Q.2) (Q.1 - P.2) g :=
    HCPolySupport.responseJ_nonneg V _ _ g
  rw [setDoubledResponseJ]
  linarith only [h1]

/-- **The bridge.**  On the open realization of a grid cube the set-level doubled
response *is* CoarseGraining's `Ch02.doubledResponseJ`, provided the triadic
family's representative on that cube is the ambient field. -/
theorem setDoubledResponseJ_openCubeSet (R : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    (g : CoeffField d) (hg : (A.coeffOn R).toCoeffField = g) (P Q : BlockVec d) :
    setDoubledResponseJ (openCubeSet R) g P Q =
      Ch02.doubledResponseJ (Ch02.cubeDomain R) (A.coeffOn R) P Q := by
  have hsplit := Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum
    (Ch02.cubeDomain R) (A.coeffOn R) P.1 Q.2 P.2 Q.1
  have hP : (P.1, P.2) = P := rfl
  have hQ : (Q.1, Q.2) = Q := rfl
  rw [hP, hQ] at hsplit
  have hbook1 : Ch02.responseJ (Ch02.cubeDomain R) (A.coeffOn R) (P.1 - Q.2) (Q.1 - P.2) =
      ResponseJ (openCubeSet R) (P.1 - Q.2) (Q.1 - P.2) g := by
    rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ, hg]
    rfl
  have htr : ((A.coeffOn R).transpose).toCoeffField = adjointCoeffField g := by
    funext x
    rw [← hg]
    rfl
  have hbook2 : Ch02.responseJ (Ch02.cubeDomain R) ((A.coeffOn R).transpose)
      (Q.2 + P.1) (Q.1 + P.2) =
      ResponseJ (openCubeSet R) (Q.2 + P.1) (Q.1 + P.2) (adjointCoeffField g) := by
    rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ, htr]
    rfl
  rw [hsplit, hbook1, hbook2, setDoubledResponseJ]

/-! ## 3. The off-grid unit-sphere maximum -/

variable [NeZero d]

private theorem exists_unit_fullBlockVec :
    ∃ e : FullBlockVec d, Ch02.fullBlockVecNormSq e = 1 := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨Pi.single (Sum.inl ⟨0, hd⟩ : BlockCoord d) 1, ?_⟩
  rw [Ch02.fullBlockVecNormSq, Fintype.sum_eq_single (Sum.inl ⟨0, hd⟩ : BlockCoord d)]
  · simp
  · intro b hb
    rw [Pi.single_eq_of_ne hb]
    ring

/-- The value set whose supremum is the off-grid normalized block response
maximum: the `A₀`-normalized doubled response of the off-grid cube `w + R` over
the unit sphere of `ℝ^{2d}`.  Compare `Ch02.normalizedBlockResponseValueSet`. -/
def offGridBlockResponseValueSet (w : Vec d) (R : TriadicCube d) (g : CoeffField d)
    (a0 : Mat d) : Set ℝ :=
  {m | ∃ e : FullBlockVec d, Ch02.fullBlockVecNormSq e = 1 ∧
    m = setDoubledResponseJ (offGridCube w R) g
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e))}

/-- **The one-cube quantity at a real translate.**  `max_{|e|=1} 𝐉(w + R, …)`. -/
def offGridBlockResponseMax (w : Vec d) (R : TriadicCube d) (g : CoeffField d)
    (a0 : Mat d) : ℝ :=
  sSup (offGridBlockResponseValueSet w R g a0)

theorem offGridBlockResponseValueSet_nonempty (w : Vec d) (R : TriadicCube d)
    (g : CoeffField d) (a0 : Mat d) :
    (offGridBlockResponseValueSet w R g a0).Nonempty := by
  obtain ⟨e, he⟩ := exists_unit_fullBlockVec (d := d)
  exact ⟨_, ⟨e, he, rfl⟩⟩

theorem offGridBlockResponseMax_nonneg (w : Vec d) (R : TriadicCube d) (g : CoeffField d)
    (a0 : Mat d) : 0 ≤ offGridBlockResponseMax w R g a0 := by
  rw [offGridBlockResponseMax]
  refine Real.sSup_nonneg ?_
  rintro m ⟨e, -, rfl⟩
  exact setDoubledResponseJ_nonneg _ _ _ _

/-- **The unit-sphere maximum is bounded by any uniform bound on its values.**
This is the `csSup_le` interface the covering step consumes. -/
theorem offGridBlockResponseMax_le {w : Vec d} {R : TriadicCube d} {g : CoeffField d}
    {a0 : Mat d} {C : ℝ}
    (h : ∀ e : FullBlockVec d, Ch02.fullBlockVecNormSq e = 1 →
      setDoubledResponseJ (offGridCube w R) g
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) ≤ C) :
    offGridBlockResponseMax w R g a0 ≤ C := by
  rw [offGridBlockResponseMax]
  refine csSup_le (offGridBlockResponseValueSet_nonempty w R g a0) ?_
  rintro m ⟨e, he, rfl⟩
  exact h e he

/-! ## 4. Conservative extension: the zero translate is CoarseGraining's quantity -/

omit [NeZero d] in
@[simp] theorem offGridCube_zero (P : TriadicCube d) :
    offGridCube (0 : Vec d) P = openCubeSet P := by
  rw [offGridCube, translateSet_zero]

/-! ## 5. The shells and the off-grid error functional -/

/-- **The shell maximum of an off-grid cube.**  The `w`-translated lattice: the
grid descendants `R` of the shape cube `P` at scale `k`, each read on the
translated cube `w + R`.  At `w = 0` this is
`Ch02.maxDescendantNormalizedBlockResponseAtScale`. -/
def offGridShellMax (w : Vec d) (P : TriadicCube d) (k : ℤ) (g : CoeffField d)
    (a0 : Mat d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale P k) (fun R => offGridBlockResponseMax w R g a0)

theorem offGridShellMax_nonneg (w : Vec d) (P : TriadicCube d) (k : ℤ) (g : CoeffField d)
    (a0 : Mat d) : 0 ≤ offGridShellMax w P k g a0 :=
  Ch02.finsetSupReal_nonneg _ _ fun R _ => offGridBlockResponseMax_nonneg w R g a0

/-- The shell maximum is bounded by any uniform bound on its cubes. -/
theorem offGridShellMax_le {w : Vec d} {P : TriadicCube d} {k : ℤ} {g : CoeffField d}
    {a0 : Mat d} {C : ℝ} (hk : k ≤ P.scale)
    (h : ∀ R ∈ descendantsAtScale P k, offGridBlockResponseMax w R g a0 ≤ C) :
    offGridShellMax w P k g a0 ≤ C :=
  Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty P hk) h

/-- **The multiscale error of an off-grid cube**, `𝓔_{t,∞,2}(w + P; g, a₀)`.

The shell series of `d.mathcal.E` with CoarseGraining's own geometric weights,
over the `w`-translated lattice.  At `w = 0` it is
`Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2)`
(`offGridErrorFunctional_zero_eq`). -/
def offGridErrorFunctional (w : Vec d) (P : TriadicCube d) (t : ℝ) (g : CoeffField d)
    (a0 : Mat d) : ℝ :=
  Real.sqrt (∑' l : ℕ, Ch02.geometricWeight t 2 l *
    offGridShellMax w P (P.scale - (l : ℤ)) g a0)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
