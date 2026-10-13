/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# ExponentMonotonicity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the ordered multiscale ellipticity gauges

This file proves a local version of the display `e.ellipticities.monotone.ordered` of
ABK26:

> For every `m ∈ ℤ`, `q ∈ [1,∞]` and `t, s ∈ (0,∞)` with `t < s`,
> `λ_{t,q}(□_m; a) ≤ λ_{s,q}(□_m; a) ≤ |σ_*^{-1}(□_m; a)|^{-1}
>  ≤ |b(□_m; a)| ≤ Λ_{s,q}(□_m; a) ≤ Λ_{t,q}(□_m; a)`.

The carriers are CoarseGraining's Chapter 2.5 objects: `Book.Ch02.lambdaSq` and
`Book.Ch02.LambdaSq` for the two multiscale gauges (definition
`e.coarse.grained.ellipticity` / `e.coarse.grained.ellipticity.infty`, i.e.
ABK26 (2.22)--(2.23)), and `Book.Ch02.coarseSigmaStarInvMatrixNorm`,
`Book.Ch02.coarseBMatrixNorm` for the two one-cube norms `|σ_*^{-1}(U; a)|` and
`|b(U; a)|` of `e.CG.bounds.1`.

## Scope and carrier notes (implementation record, no manuscript defect)

* The cube is an arbitrary `TriadicCube d`, not only the centered `□_m`.  The
  manuscript's own definition paragraph ends with "We extend these definitions
  to translations `y + □_m` of the cube `□_m` in the obvious way", and the
  consumers of this display instantiate it at off-centre cubes; the centered
  case is `Q = originCube d m`.  This is a strengthening of the quantifier, not
  an added hypothesis.
* `q ∈ [1,∞]` is `Book.Ch02.MultiscaleExponent.IsAdmissible`: `.finite q` with
  `1 ≤ q`, or `.infinity`.
* `[NeZero d]` is typing data for CoarseGraining's Chapter 2.5 layer (the
  paper-wide standing assumption is `2 ≤ d`).

## Proof route

Nothing analytic is reproved.

## Main results

* `ellipticities_monotone_ordered`: the display, as the full five-inequality
  chain.
* `lambdaSq_mono_of_lt`: the consumer-facing corollary, the first inequality of
  the chain read on its own.
* `lambdaSq_le_descendantWeight_mul_lambdaSq`: cube monotonicity of the
  multiscale lower ellipticity, `λ_{s,q}(Q; a) ≤ 3^{2s(Q.scale − k)}
  λ_{s,q}(R; a)` for a descendant `R` of `Q` at scale `k`.

## References

* ABK26, `e.ellipticities.monotone.ordered`, statement and proof, the
  definitions (2.22)--(2.23).
* ABK26, `e.CG.bounds.1` (`e.subadda.nosymm`).
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

variable {d : ℕ}

/-! ## The display -/

/-- **`e.ellipticities.monotone.ordered`** (ABK26).  For every triadic cube,
every admissible exponent `q ∈ [1,∞]` and all `0 < t < s`, the six multiscale
and one-cube ellipticity gauges are ordered:

`λ_{t,q} ≤ λ_{s,q} ≤ |σ_*^{-1}|^{-1} ≤ |b| ≤ Λ_{s,q} ≤ Λ_{t,q}`. -/
theorem ellipticities_monotone_ordered [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t s : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (ht : 0 < t) (hts : t < s)
    (hq : q.IsAdmissible) :
    Book.Ch02.lambdaSq Q t q a ≤ Book.Ch02.lambdaSq Q s q a ∧
      Book.Ch02.lambdaSq Q s q a ≤
          (Book.Ch02.coarseSigmaStarInvMatrixNorm Q a)⁻¹ ∧
        (Book.Ch02.coarseSigmaStarInvMatrixNorm Q a)⁻¹ ≤
            Book.Ch02.coarseBMatrixNorm Q a ∧
          Book.Ch02.coarseBMatrixNorm Q a ≤ Book.Ch02.LambdaSq Q s q a ∧
            Book.Ch02.LambdaSq Q s q a ≤ Book.Ch02.LambdaSq Q t q a := by
  have hs : 0 < s := ht.trans hts
  exact ⟨Book.Ch02.lambdaSq_mono Q a ht hts hq,
    Book.Ch02.lambdaSq_le_oneCube Q a hs hq,
    Book.Ch02.oneCube_sigmaStarInv_le_b Q a,
    Book.Ch02.oneCube_b_le_LambdaSq Q a hs hq,
    Book.Ch02.LambdaSq_antitone Q a ht hts hq⟩

/-! ## Consumer-facing corollaries -/

/-- The first inequality of the display: `λ_{t,q} ≤ λ_{s,q}` for `0 < t < s`. -/
theorem lambdaSq_mono_of_lt [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t s : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (ht : 0 < t) (hts : t < s)
    (hq : q.IsAdmissible) :
    Book.Ch02.lambdaSq Q t q a ≤ Book.Ch02.lambdaSq Q s q a :=
  (ellipticities_monotone_ordered Q a ht hts hq).1

/-! ## Cube monotonicity -/

/-- **Cube monotonicity of the multiscale lower ellipticity.**  If `R` is a
descendant of `Q` at scale `k`, then

`λ_{s,q}(Q; a) ≤ 3^{2s(Q.scale − k)} λ_{s,q}(R; a)`. -/
theorem lambdaSq_le_descendantWeight_mul_lambdaSq [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : Book.Ch02.TriadicCoeffFamily d) {s : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (hR : R ∈ descendantsAtScale Q k)
    (hs : 0 < s) (hq : q.IsAdmissible) :
    Book.Ch02.lambdaSq Q s q a ≤
      Book.Ch02.multiscaleDescendantWeight Q k s * Book.Ch02.lambdaSq R s q a := by
  have hx : 0 < Book.Ch02.lambdaSq R s q a := Book.Ch02.lambdaSq_pos R a hs hq
  have hy : 0 < Book.Ch02.lambdaSq Q s q a := Book.Ch02.lambdaSq_pos Q a hs hq
  have h := Book.Ch02.descendant_lambdaSq_inv_le (Q := Q) (R := R) (k := k) a hR hs hq
  have h3 : Book.Ch02.lambdaSq Q s q a * (Book.Ch02.lambdaSq R s q a)⁻¹ ≤
      Book.Ch02.multiscaleDescendantWeight Q k s := by
    have hmul := mul_le_mul_of_nonneg_left h hy.le
    rwa [show Book.Ch02.lambdaSq Q s q a *
        (Book.Ch02.multiscaleDescendantWeight Q k s *
          (Book.Ch02.lambdaSq Q s q a)⁻¹) =
        Book.Ch02.multiscaleDescendantWeight Q k s by
      field_simp] at hmul
  have h4 := mul_le_mul_of_nonneg_right h3 hx.le
  rwa [inv_mul_cancel_right₀ (ne_of_gt hx)] at h4

end Algsuperdiff.Section3.Provider.ErrorComparison
