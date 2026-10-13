/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# StepSevenLambdaStability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7b, clause (A): `l.lambdas.stability` at `s* = 1/16`

## The target

ABK26 `l.lambdas.stability` (statement, proof):

```text
  There is C(d) < ∞ such that for every p, q ∈ [1,∞], s, t ∈ (0,1/2] with s < t,
  and x ∈ □_0 with x + □_{-1} ⊆ □_0,
      λ_{t,q}^{-1}(x+□_{-1}; a) ≤ C(1-2s)^{-1}(t/(t-s))^{2/q} λ_{s,q}^{-1}(□_0; a) ,
      Λ_{t,q}(x+□_{-1}; a)      ≤ C(1-2s)^{-1}(t/(t-s))^{2/q} Λ_{s,q}(□_0; a) .
```

That is what is delivered here, at the printed prefactor shape
`C/(1-2s*)·(t/(t-s*))^{2/q}` with the explicit constant `C = 2`.

## Carrier scope: what is delivered, and the one restriction

`Ch02.lambdaSq`/`Ch02.LambdaSq` are functions of a `TriadicCube d`, which is a
`scale : ℤ` together with an integer `index : Fin d → ℤ`.  A cube `y + □_{k-1}`
with `y` off the scale-`(k-1)` lattice is therefore **not an object of the
carrier at all**: the printed lemma's hypothesis "`x ∈ □_0` with `x + □_{-1} ⊆
□_0`" ranges over arbitrary real `x`, and for non-lattice `x` the term
`λ_{t,q}(x+□_{-1}; a)` does not type.

What is expressible, and what this module proves, is the printed inequality for
the lattice-aligned configuration: the inner cube is a triadic descendant of the
outer one.  That is exactly the printed configuration when the Step-7a sandwich
centre can be taken to be the window centre itself (`y' = z`, i.e. when `z +
□_{k'-1} ⊆ □_m`, so the clamp is the identity), and the outer/inner pair is `(z +
□_{k'}, z + □_{k'-1})` — a parent and its centre child.  Everything downstream
in §4.4 runs on `originCube d k` with the translation absorbed into the
coefficient family and the solution's argument (see
`StepSevenMean.exists_stepSevenEnd_chain_of_lambda_hmeanFree`), so this is the
configuration the proved chain consumes.

## The proof, and what CoarseGraining supplied

The printed proof builds a Whitney-type family and sums a geometric series.  In
the lattice-aligned configuration none of that is needed: CoarseGraining
already proves the two halves separately and the lemma is their composition.

* index monotonicity on ONE cube — `Ch02.lambdaSq_mono`,
  `Ch02.LambdaSq_antitone` (ABK26 `e.ellipticities.monotone.ordered`):
  `λ_{s,q}^{-1}` and `Λ_{s,q}` are nonincreasing in the index, so passing from
  `t` down to `s*` costs nothing;
* one-scale descent at a fixed index — `Ch02.descendant_lambdaSq_inv_le`,
  `Ch02.descendant_LambdaSq_le` (ABK26 `e.bound.one.cube.by.lambdas`): a
  descendant at scale `k` costs `3^{2s(m-k)}`, here `3^{2s*}`.

So the honest constant of the composition is `3^{2s*} = 3^{1/8} ≤ 2`, and the
printed prefactor — whose smallest possible value at `s* = 1/16` is `C·8/7 ≥
8/7` — dominates it at `C = 2`.  The printed `C(d)` is realized dimension-free
here; that is a strengthening, not a weakening.

## Strengthenings (binders dropped)

* the printed range binder `t ≤ 1/2` is NOT taken: the estimate is proved for
  every `t > s*`;
* the printed `p ∈ [1,∞]` binder is absent because the `p` of the printed lemma
  belongs only to its third display (the `𝓔` twin), which is not built here;
* the constant is dimension-free.

## What is NOT built here

The `𝓔` twin `e.mathcalE.stability`.  §4.4's Step 7b applies only the `λ` and
`Λ` displays (`e.lambda.stability.applied`).

## References

* ABK26, `l.lambdas.stability`; `e.lambda.stability.applied`;
  `e.ellipticities.monotone.ordered`; `e.bound.one.cube.by.lambdas`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The re-specified stability index and the printed prefactor -/

noncomputable def stepSevenStabilityIndex : ℝ := 1 / 16

@[simp] theorem stepSevenStabilityIndex_eq : stepSevenStabilityIndex = 1 / 16 := rfl

theorem stepSevenStabilityIndex_pos : 0 < stepSevenStabilityIndex := by
  rw [stepSevenStabilityIndex_eq]; norm_num

noncomputable def stepSevenStabilityConst : ℝ := 2

@[simp] theorem stepSevenStabilityConst_eq : stepSevenStabilityConst = 2 := rfl

/-- **The printed exponent factor `(t/(t-s))^{2/q}`**, with the `q = ∞` endpoint
value `1` (the limit of the finite-`q` expression). -/
noncomputable def stepSevenStabilityExponentFactor (s t : ℝ) :
    Ch02.MultiscaleExponent → ℝ
  | .finite q => Real.rpow (t / (t - s)) (2 / q)
  | .infinity => 1

@[simp] theorem stepSevenStabilityExponentFactor_finite (s t q : ℝ) :
    stepSevenStabilityExponentFactor s t (.finite q) =
      Real.rpow (t / (t - s)) (2 / q) := rfl

@[simp] theorem stepSevenStabilityExponentFactor_infinity (s t : ℝ) :
    stepSevenStabilityExponentFactor s t .infinity = 1 := rfl

noncomputable def stepSevenStabilityPrefactor (C s t : ℝ)
    (q : Ch02.MultiscaleExponent) : ℝ :=
  C / (1 - 2 * s) * stepSevenStabilityExponentFactor s t q

/-- The exponent factor is at least `1`: `t/(t-s) ≥ 1` and `2/q ≥ 0`. -/
theorem one_le_stepSevenStabilityExponentFactor {s t : ℝ}
    (hs : 0 < s) (hst : s < t) {q : Ch02.MultiscaleExponent}
    (hq : q.IsAdmissible) :
    1 ≤ stepSevenStabilityExponentFactor s t q := by
  cases q with
  | finite q =>
      have hq1 : (1 : ℝ) ≤ q := by simpa using hq
      have hts : 0 < t - s := by linarith only [hst]
      have hbase : (1 : ℝ) ≤ t / (t - s) := by
        rw [le_div_iff₀ hts]; linarith only [hs]
      have hexp : (0 : ℝ) ≤ 2 / q :=
        div_nonneg (by norm_num) (by linarith only [hq1])
      have hmain := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hexp
      rw [Real.one_rpow] at hmain
      rw [stepSevenStabilityExponentFactor_finite]
      exact hmain
  | infinity => rw [stepSevenStabilityExponentFactor_infinity]

/-- `3^{2s*} = 3^{1/8} ≤ 2`: the honest constant of the lattice-aligned
composition. -/
theorem rpow_three_two_mul_stabilityIndex_le_two :
    Real.rpow (3 : ℝ) (2 * stepSevenStabilityIndex) ≤ 2 := by
  have hexp : 2 * stepSevenStabilityIndex = (1 : ℝ) / 8 := by
    rw [stepSevenStabilityIndex_eq]; norm_num
  have h256 : Real.rpow (256 : ℝ) ((1 : ℝ) / 8) = 2 := by
    have hnat : Real.rpow (2 : ℝ) ((8 : ℕ) : ℝ) = (2 : ℝ) ^ (8 : ℕ) :=
      Real.rpow_natCast 2 8
    have hb : (256 : ℝ) = Real.rpow (2 : ℝ) ((8 : ℕ) : ℝ) := by rw [hnat]; norm_num
    have hmul : Real.rpow (2 : ℝ) (((8 : ℕ) : ℝ) * ((1 : ℝ) / 8)) =
        Real.rpow (Real.rpow (2 : ℝ) ((8 : ℕ) : ℝ)) ((1 : ℝ) / 8) :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
    have he : ((8 : ℕ) : ℝ) * ((1 : ℝ) / 8) = 1 := by norm_num
    have hone : Real.rpow (2 : ℝ) (1 : ℝ) = 2 := Real.rpow_one 2
    rw [hb, ← hmul, he, hone]
  calc Real.rpow (3 : ℝ) (2 * stepSevenStabilityIndex)
      = Real.rpow (3 : ℝ) ((1 : ℝ) / 8) := by rw [hexp]
    _ ≤ Real.rpow (256 : ℝ) ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 2 := h256

/-- The honest constant is dominated by the printed prefactor at `s* = 1/16` and `C
= 2`: `3^{1/8} ≤ 2 ≤ (16/7)·(t/(t-s*))^{2/q}`. -/
theorem rpow_three_le_stepSevenStabilityPrefactor {t : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hst : stepSevenStabilityIndex < t) (hq : q.IsAdmissible) :
    Real.rpow (3 : ℝ) (2 * stepSevenStabilityIndex) ≤
      stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
        t q := by
  have hfac :=
    one_le_stepSevenStabilityExponentFactor stepSevenStabilityIndex_pos hst hq
  have hcoef :
      stepSevenStabilityConst / (1 - 2 * stepSevenStabilityIndex) = 16 / 7 := by
    rw [stepSevenStabilityConst_eq, stepSevenStabilityIndex_eq]; norm_num
  rw [stepSevenStabilityPrefactor, hcoef]
  refine le_trans rpow_three_two_mul_stabilityIndex_le_two ?_
  have hmul :
      (16 : ℝ) / 7 * 1 ≤
        16 / 7 * stepSevenStabilityExponentFactor stepSevenStabilityIndex t q :=
    mul_le_mul_of_nonneg_left hfac (by norm_num)
  linarith only [hmul]

/-! ## 2. The two CoarseGraining halves -/

/-- **Index monotonicity of `λ^{-1}` on one cube**
(`e.ellipticities.monotone.ordered`): `λ_{s,q}^{-1}` is nonincreasing in the
index. -/
theorem lambdaSq_inv_le_of_index_le [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {s t : ℝ} {q : Ch02.MultiscaleExponent}
    (hs : 0 < s) (hst : s < t) (hq : q.IsAdmissible) :
    (Ch02.lambdaSq Q t q a)⁻¹ ≤ (Ch02.lambdaSq Q s q a)⁻¹ :=
  inv_anti₀ (Ch02.lambdaSq_pos Q a hs hq) (Ch02.lambdaSq_mono Q a hs hst hq)

/-- **The one-scale descent weight at depth one**: `multiscaleDescendantWeight Q
(Q.scale - 1) s = 3^{2s}`. -/
theorem multiscaleDescendantWeight_pred (Q : TriadicCube d) (s : ℝ) :
    Ch02.multiscaleDescendantWeight Q (Q.scale - 1) s = Real.rpow (3 : ℝ) (2 * s) := by
  have hz : ((Q.scale - (Q.scale - 1) : ℤ) : ℝ) = 1 := by
    rw [show (Q.scale - (Q.scale - 1) : ℤ) = 1 by ring]; norm_num
  rw [Ch02.multiscaleDescendantWeight, hz, mul_one]

/-! ## 3. Clause (A), general depth -/

/-- **Clause (A), lower constant, at a general descendant scale.**  For every
descendant `R` of `Q` at scale `k` and every index pair `s < t`,

```text
  λ_{t,q}^{-1}(R; a) ≤ 3^{2s(Q.scale-k)} · λ_{s,q}^{-1}(Q; a) .
``` -/
theorem lambdaSq_inv_stability_of_descendant [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffFamily d) {s t : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hst : s < t)
    (hq : q.IsAdmissible) :
    (Ch02.lambdaSq R t q a)⁻¹ ≤
      Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s q a)⁻¹ :=
  le_trans (lambdaSq_inv_le_of_index_le R a hs hst hq)
    (Ch02.descendant_lambdaSq_inv_le a hR hs hq)

/-- **Clause (A), upper constant, at a general descendant scale.**

```text
  Λ_{t,q}(R; a) ≤ 3^{2s(Q.scale-k)} · Λ_{s,q}(Q; a) .
``` -/
theorem LambdaSq_stability_of_descendant [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffFamily d) {s t : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hst : s < t)
    (hq : q.IsAdmissible) :
    Ch02.LambdaSq R t q a ≤
      Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s q a :=
  le_trans (Ch02.LambdaSq_antitone R a hs hst hq) (Ch02.descendant_LambdaSq_le a hR hs hq)

/-! ## 4. Clause (A) in the printed shape, at `s* = 1/16` -/

/-- **Clause (A), the printed lower display** `e.lambda.stability` at the
re-specified index, in the lattice-aligned configuration: for every triadic
cube `Q`, every centre child / one-scale descendant `R`, every `t > s*` and
every admissible `q ∈ [1,∞]`,

```text
  λ_{t,q}^{-1}(R; a)
    ≤ C(1-2s*)^{-1}(t/(t-s*))^{2/q} λ_{s*,q}^{-1}(Q; a) ,      C = 2 .
``` -/
theorem stepSevenLambdaStability_lambdaInv [NeZero d]
    {Q R : TriadicCube d} (a : CoeffFamily d) {t : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q (Q.scale - 1))
    (hst : stepSevenStabilityIndex < t) (hq : q.IsAdmissible) :
    (Ch02.lambdaSq R t q a)⁻¹ ≤
      stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
          t q *
        (Ch02.lambdaSq Q stepSevenStabilityIndex q a)⁻¹ := by
  have hcore :=
    lambdaSq_inv_stability_of_descendant a hR stepSevenStabilityIndex_pos hst hq
  rw [multiscaleDescendantWeight_pred] at hcore
  refine hcore.trans (mul_le_mul_of_nonneg_right
    (rpow_three_le_stepSevenStabilityPrefactor hst hq)
    (inv_nonneg.mpr (Ch02.lambdaSq_nonneg Q a stepSevenStabilityIndex_pos hq)))

/-- **Clause (A), the printed upper display** `e.big.Lambda.stability` at the
re-specified index, in the lattice-aligned configuration:

```text
  Λ_{t,q}(R; a) ≤ C(1-2s*)^{-1}(t/(t-s*))^{2/q} Λ_{s*,q}(Q; a) ,      C = 2 .
``` -/
theorem stepSevenLambdaStability_Lambda [NeZero d]
    {Q R : TriadicCube d} (a : CoeffFamily d) {t : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q (Q.scale - 1))
    (hst : stepSevenStabilityIndex < t) (hq : q.IsAdmissible) :
    Ch02.LambdaSq R t q a ≤
      stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
          t q *
        Ch02.LambdaSq Q stepSevenStabilityIndex q a := by
  have hcore :=
    LambdaSq_stability_of_descendant a hR stepSevenStabilityIndex_pos hst hq
  rw [multiscaleDescendantWeight_pred] at hcore
  refine hcore.trans (mul_le_mul_of_nonneg_right
    (rpow_three_le_stepSevenStabilityPrefactor hst hq)
    (Ch02.LambdaSq_nonneg Q a stepSevenStabilityIndex_pos hq))

/-! ## 5. The lattice-aligned Step-7a sandwich pair -/

/-- **The centre child** `□_{k-1} ⊆ □_k`: the lattice-aligned instance of the
Step-7a sandwich, in which the clamp of
`StepSevenSandwich.exists_sandwich_centre` is the identity (`y' = z`) and the
translation is absorbed into the coefficient family. -/
theorem stepSevenCentreChild_mem_descendantsAtScale (d : ℕ) (k : ℤ) :
    originCube d (k - 1) ∈ descendantsAtScale (originCube d k) (k - 1) := by
  have hk : k - 1 ≤ (originCube d k).scale := by
    show k - 1 ≤ k
    omega
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d k) hk]
  have hdepth : Int.toNat ((originCube d k).scale - (k - 1)) = 1 := by
    show Int.toNat (k - (k - 1)) = 1
    omega
  rw [hdepth, descendantsAtDepth_one]
  refine Finset.mem_image.mpr ⟨fun _ => (1 : Fin 3), Finset.mem_univ _, ?_⟩
  have hindex :
      (fun i : Fin d => 3 * (originCube d k).index i + ((1 : Fin 3) : ℤ) - 1) =
        (originCube d (k - 1)).index := by
    funext i
    show 3 * (0 : ℤ) + ((1 : Fin 3) : ℤ) - 1 = 0
    norm_num
  exact congrArg (fun idx => (⟨k - 1, idx⟩ : TriadicCube d)) hindex

/-- **Clause (A) at the Step-7a sandwich pair** `(□_{k-1}, □_k)`, both displays, in
the printed indexing `(k'-1, k')`. -/
theorem stepSevenLambdaStability_centreChild [NeZero d] (k : ℤ)
    (a : CoeffFamily d) {t : ℝ} {q : Ch02.MultiscaleExponent}
    (hst : stepSevenStabilityIndex < t) (hq : q.IsAdmissible) :
    (Ch02.lambdaSq (originCube d (k - 1)) t q a)⁻¹ ≤
        stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
            t q *
          (Ch02.lambdaSq (originCube d k) stepSevenStabilityIndex q a)⁻¹ ∧
      Ch02.LambdaSq (originCube d (k - 1)) t q a ≤
        stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
            t q *
          Ch02.LambdaSq (originCube d k) stepSevenStabilityIndex q a := by
  have hR : originCube d (k - 1) ∈
      descendantsAtScale (originCube d k) ((originCube d k).scale - 1) := by
    have h := stepSevenCentreChild_mem_descendantsAtScale d k
    have hs : (originCube d k).scale = k := rfl
    rwa [hs]
  exact ⟨stepSevenLambdaStability_lambdaInv a hR hst hq,
    stepSevenLambdaStability_Lambda a hR hst hq⟩

end

end Algsuperdiff.Section4.Provider.Regularity
