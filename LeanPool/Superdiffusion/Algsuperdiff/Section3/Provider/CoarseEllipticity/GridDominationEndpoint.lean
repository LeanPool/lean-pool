/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridDomination

/-!
# GridDominationEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `hgrid` at the endpoint `q = infinity`: the direct, pole-free route

The frozen display `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds`
quantifies over every admissible exponent, and its deterministic lower profile
at the endpoint is the bare constant
(`LowerLegProfile.lowerEllipticityProfile_infinity`: `lowerEllipticityProfile C
gamma s infinity = C`) --- **no pole**.  That is not an accident of the print:
at `q = infinity` the coarse-grained ellipticity constant is a *supremum*, not
a series (`e.coarse.grained.ellipticity.infty`),

```
lambda_{s,infinity}(cu_m;a)^{-1} = sup_{n >= 0} 3^{-2 s n} max_{z in 3^{m-n} Zd cap cu_m} |sigma_*^{-1}(z + cu_{m-n}; a)| ,
```

and a supremum of `Cdet + (lane at gap n)` is at most `Cdet + sup_n (lane)`:
the deterministic constant is **not** multiplied by the number of scales.  This
module proves that endpoint at this repository's carriers.

## Why this is not the finite-`q` statement with `q` sent to infinity

`Provider/CoarseEllipticity/GridDomination.lean` (at `q = 2`) and
`.../GridDominationAllQ.lean` (at finite `q >= 2`) both end in the consumers'
series shape `X <= sum_k mass * gridWeight rho k * G k`, whose deterministic slot
is `Cdet * (mass * rho^{-1})`.  Routing the endpoint through that shape is
possible --- the supremum is bounded by the series, since every term of the
series is nonnegative --- but it is *lossy in exactly the wrong place*: it
reintroduces the factor `(2s)^{-1}` that the endpoint profile does not have.
The theorems below therefore do **not** go through `gridWeight` at all.  What
they deliver is the endpoint's own domination

```
lambda_{s,infinity}^{-1}(cu_m; a_L) * scaling <= V(omega)      for every omega, every L >= L0,
```

from a caller-supplied majorant `V` of the *individual* weighted grid maxima.
Fed with `V = Cdet + (summed lane)`, this is precisely the two-slot family
split that `LowerLeg.isLowerIntegerFamilyOrlicz_of_familySplit` consumes, with
the deterministic slot equal to `Cdet` --- the frozen endpoint profile, with no
pole and no fold.

## What is proved here

* `lambdaSqCoeffField_inv_infinity_eq_sSup`,
  `LambdaSqCoeffField_infinity_eq_sSup` --- the endpoint constants at the
  Chapter 4 ambient coefficient field are the source's suprema, non-elliptic
  branch included (there the supremum is that of `{0}`).
* `lambdaSqCoeffField_inv_infinity_le_of_forall` and the two scaled forms
  `lambdaSqCoeffField_inv_infinity_mul_le_of_forall`,
  `LambdaSqCoeffField_infinity_mul_le_of_forall` --- the endpoint domination
  from a majorant of the individual weighted maxima.
* `cutoffLowerEllipticityInvLiteral_infinity_mul_le_of_forall`,
  `cutoffUpperEllipticityLiteral_infinity_mul_le_of_forall` --- the same at the
  Section 3 literal observables.
* `cutoffLowerEllipticityInv_infinity_mul_forall_le`,
  `cutoffUpperEllipticity_infinity_mul_le` --- the same at the **exported**
  observables, at every sample point (the  body swap), in the two legs' own
  shapes: `forall omega, forall L >= L0` for the lower family and `forall
  omega` at the single cutoff index for the upper.

## What is *not* claimed here

No block estimate, no `e.maxy.bound` lift, no base case; nothing below asserts
that either leg's payload is satisfiable.  In particular the majorant `V` is the
caller's: this module does not construct it, and the per-scale split that would
produce it (`p.bfA.multiscalebound` at the endpoint) is untouched.

## References

* ABK26, `e.coarse.grained.ellipticity.infty`, (the endpoint is the supremum,
  and is the `q -> infinity` limit of the finite definition);
  `p.cg.ellipticity.bounds`, statement, proof.
* `Provider/CoarseEllipticity/GridDominationAllQ.lean` (the finite branch
  `2 <= q`), `.../GridDomination.lean` (the ruled `q = 2`),
  `.../LowerLegProfile.lean` (`lowerEllipticityProfile_infinity`),
  `.../LowerLeg.lean` (`isLowerIntegerFamilyOrlicz_of_familySplit`, the
  endpoint's consumer).
* CoarseGraining: `Book.Ch02.lambdaSqInfinity`, `Book.Ch02.LambdaSqInfinity`
  (the source definitions) and
  `Book.Ch02.lambdaSqInfinity_denominator_valueSet_bddAbove` (the boundedness
  that makes the supremum a real number --- not needed by the `csSup_le` route
  below, which needs only nonemptiness).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. A scaled supremum bound -/

/-- A nonnegative multiple of a supremum is bounded by any bound on the scaled
elements.  The `scaling = 0` case is separated because the division route is not
available there. -/
private theorem mul_csSup_le_of_forall {S : Set ℝ} (hS : S.Nonempty) {c B : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∈ S, c * x ≤ B) : c * sSup S ≤ B := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · obtain ⟨x, hx⟩ := hS
    have hxB := h x hx
    rw [← hc0] at hxB ⊢
    rw [zero_mul] at hxB ⊢
    exact hxB
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    have hinv : (0 : ℝ) ≤ c⁻¹ := (inv_pos.mpr hcpos).le
    have hle : sSup S ≤ c⁻¹ * B := by
      refine csSup_le hS fun x hx => ?_
      have h1 : c⁻¹ * (c * x) ≤ c⁻¹ * B := mul_le_mul_of_nonneg_left (h x hx) hinv
      rwa [← mul_assoc, inv_mul_cancel₀ hcne, one_mul] at h1
    calc c * sSup S ≤ c * (c⁻¹ * B) := mul_le_mul_of_nonneg_left hle hc
      _ = B := by rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-! ## 2. The endpoint constants at the Chapter 4 ambient coefficient field -/

/-- **The endpoint lower constant is the source's supremum**, at the Chapter 4
ambient coefficient field, non-elliptic branch included (there both sides are
the supremum of `{0}`, i.e. `0`).  Unconditional in `s`. -/
theorem lambdaSqCoeffField_inv_infinity_eq_sSup [NeZero d] (Q : TriadicCube d)
    (a : RegCoeffField d) (s : ℝ) :
    (Book.Ch04.lambdaSqCoeffField Q s .infinity a)⁻¹
      = sSup {N : ℝ | ∃ n : ℕ, N = Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a} := by
  classical
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · simp only [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, h,
      dite_eq_left]
    simp only [Book.Ch04.lambdaSqCoeffField, h, dite_eq_left, Book.Ch02.lambdaSq_infinity,
      Book.Ch02.lambdaSqInfinity, inv_inv]
  · simp only [Book.Ch04.lambdaSqCoeffField,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, h, dite_eq_right,
      not_false_iff, inv_zero, mul_zero]
    have hset : {N : ℝ | ∃ _n : ℕ, N = 0} = ({0} : Set ℝ) := by
      ext x
      simp
    rw [hset, csSup_singleton]

/-- **The endpoint upper constant is the source's supremum**, at the Chapter 4
ambient coefficient field, non-elliptic branch included. -/
theorem LambdaSqCoeffField_infinity_eq_sSup [NeZero d] (Q : TriadicCube d)
    (a : RegCoeffField d) (s : ℝ) :
    Book.Ch04.LambdaSqCoeffField Q s .infinity a
      = sSup {N : ℝ | ∃ n : ℕ, N = Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a} := by
  classical
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · simp only [Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, h, dite_eq_left]
    simp only [Book.Ch04.LambdaSqCoeffField, h, dite_eq_left, Book.Ch02.LambdaSq_infinity,
      Book.Ch02.LambdaSqInfinity]
  · simp only [Book.Ch04.LambdaSqCoeffField,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, h, dite_eq_right,
      not_false_iff, mul_zero]
    have hset : {N : ℝ | ∃ _n : ℕ, N = 0} = ({0} : Set ℝ) := by
      ext x
      simp
    rw [hset, csSup_singleton]

/-! ## 3. The endpoint domination from a majorant of the individual maxima -/

/-- **The endpoint lower domination.**  Any bound on the individual weighted grid
maxima bounds `lambda_{s,infinity}^{-1}` itself.  No summability, no fold, and no
`s`-pole: the gap-`0` scale is one of the elements of the supremum. -/
theorem lambdaSqCoeffField_inv_infinity_le_of_forall [NeZero d] (Q : TriadicCube d)
    (a : RegCoeffField d) (s : ℝ) {B : ℝ}
    (hB : ∀ n : ℕ, Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a ≤ B) :
    (Book.Ch04.lambdaSqCoeffField Q s .infinity a)⁻¹ ≤ B := by
  rw [lambdaSqCoeffField_inv_infinity_eq_sSup]
  refine csSup_le ⟨_, ⟨0, rfl⟩⟩ ?_
  rintro x ⟨n, rfl⟩
  exact hB n

/-- The scaled form of `lambdaSqCoeffField_inv_infinity_le_of_forall`. -/
theorem lambdaSqCoeffField_inv_infinity_mul_le_of_forall [NeZero d]
    (Q : TriadicCube d) (a : RegCoeffField d) (s : ℝ) {scaling B : ℝ}
    (hscaling : 0 ≤ scaling)
    (hB : ∀ n : ℕ, scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a) ≤ B) :
    (Book.Ch04.lambdaSqCoeffField Q s .infinity a)⁻¹ * scaling ≤ B := by
  rw [lambdaSqCoeffField_inv_infinity_eq_sSup, mul_comm]
  refine mul_csSup_le_of_forall ?_ hscaling ?_
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro x ⟨n, rfl⟩
    exact hB n


/-- The upper endpoint counterpart of
`lambdaSqCoeffField_inv_infinity_mul_le_of_forall`, in the scaled form. -/
theorem LambdaSqCoeffField_infinity_mul_le_of_forall [NeZero d] (Q : TriadicCube d)
    (a : RegCoeffField d) (s : ℝ) {scaling B : ℝ} (hscaling : 0 ≤ scaling)
    (hB : ∀ n : ℕ, scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
        ≤ B) :
    Book.Ch04.LambdaSqCoeffField Q s .infinity a * scaling ≤ B := by
  rw [LambdaSqCoeffField_infinity_eq_sSup, mul_comm]
  refine mul_csSup_le_of_forall ?_ hscaling ?_
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro x ⟨n, rfl⟩
    exact hB n

/-! ## 4. The endpoint at the Section 3 literal observables -/

/-- The endpoint lower domination at the Section 3 literal observable, at the
centered cube. -/
theorem cutoffLowerEllipticityInvLiteral_infinity_mul_le_of_forall [NeZero d]
    (M : ABKModel d) (m L : ℤ) (s : ℝ) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.infinity) {scaling B : ℝ}
    (hscaling : 0 ≤ scaling) (omega : Cutoff.CutoffSample d)
    (hB : ∀ n : ℕ, scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale (originCube d m)
        (m - (n : ℤ)) (Cutoff.coefficientCutoff M.nu L omega)) ≤ B) :
    Observable.cutoffLowerEllipticityInvLiteral M m L s q omega * scaling ≤ B := by
  have hscale : (originCube d m).scale = m := rfl
  rw [cutoffLowerEllipticityInvLiteral_eq_coeffField, hqval]
  exact lambdaSqCoeffField_inv_infinity_mul_le_of_forall (originCube d m)
    (Cutoff.coefficientCutoff M.nu L omega) s hscaling (by rw [hscale]; exact hB)

/-- The endpoint upper domination at the Section 3 literal observable. -/
theorem cutoffUpperEllipticityLiteral_infinity_mul_le_of_forall [NeZero d]
    (M : ABKModel d) (m L : ℤ) (s : ℝ) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.infinity) {scaling B : ℝ}
    (hscaling : 0 ≤ scaling) (omega : Cutoff.CutoffSample d)
    (hB : ∀ n : ℕ, scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m)
        (m - (n : ℤ)) (Cutoff.coefficientCutoff M.nu L omega)) ≤ B) :
    Observable.cutoffUpperEllipticityLiteral M m L s q omega * scaling ≤ B := by
  have hscale : (originCube d m).scale = m := rfl
  rw [cutoffUpperEllipticityLiteral_eq_coeffField, hqval]
  exact LambdaSqCoeffField_infinity_mul_le_of_forall (originCube d m)
    (Cutoff.coefficientCutoff M.nu L omega) s hscaling (by rw [hscale]; exact hB)

/-! ## 5. The endpoint at the exported observables, in the legs' own shapes -/

/-- **The lower leg's endpoint domination.**  Verbatim the `hdom` binder of
`LowerLeg.isLowerIntegerFamilyOrlicz_of_familySplit` at
`X L omega = cutoffLowerEllipticityInv M m L s hs q omega * scaling`, once the
caller takes `V omega = Ydet omega + Y omega`.

The deterministic slot the caller then gets is whatever `V`'s deterministic part
is: at `V = Cdet + (summed lane)` it is `Cdet` itself, which is exactly the
frozen endpoint profile `lowerEllipticityProfile Clow gamma s infinity = Clow`.
No `(2s)^{-1}` appears anywhere, because no series is formed. -/
theorem cutoffLowerEllipticityInv_infinity_mul_forall_le [NeZero d] (M : ABKModel d)
    (m : ℤ) {s : ℝ} (hs : 0 < s) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.infinity) {L0 : ℤ} {scaling : ℝ}
    {V : Cutoff.CutoffSample d → ℝ} (hscaling : 0 ≤ scaling)
    (hV : ∀ (n : ℕ) (omega : Cutoff.CutoffSample d) (L : ℤ), L0 ≤ L →
      scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          (originCube d m) (m - (n : ℤ)) (Cutoff.coefficientCutoff M.nu L omega))
        ≤ V omega) :
    ∀ (omega : Cutoff.CutoffSample d) (L : ℤ), L0 ≤ L →
      Observable.cutoffLowerEllipticityInv M m L s hs q omega * scaling ≤ V omega := by
  intro omega L hL
  rw [congrFun (Observable.cutoffLowerEllipticityInv_eq_literal M m L s hs q) omega]
  exact cutoffLowerEllipticityInvLiteral_infinity_mul_le_of_forall M m L s hqval
    hscaling omega fun n => hV n omega L hL

/-- **The upper leg's endpoint domination**, at the single cutoff index the upper
leg reads its target at.  Verbatim the domination slot of the upper payload once
the caller takes `V omega = Udet omega + Uone omega + Utail omega`. -/
theorem cutoffUpperEllipticity_infinity_mul_le [NeZero d] (M : ABKModel d)
    (m L : ℤ) {s : ℝ} (hs : 0 < s) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.infinity) {scaling : ℝ}
    {V : Cutoff.CutoffSample d → ℝ} (hscaling : 0 ≤ scaling)
    (hV : ∀ (n : ℕ) (omega : Cutoff.CutoffSample d),
      scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m)
          (m - (n : ℤ)) (Cutoff.coefficientCutoff M.nu L omega)) ≤ V omega) :
    ∀ omega : Cutoff.CutoffSample d,
      Observable.cutoffUpperEllipticity M m L s hs q omega * scaling ≤ V omega := by
  intro omega
  rw [congrFun (Observable.cutoffUpperEllipticity_eq_literal M m L s hs q) omega]
  exact cutoffUpperEllipticityLiteral_infinity_mul_le_of_forall M m L s hqval
    hscaling omega fun n => hV n omega

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
