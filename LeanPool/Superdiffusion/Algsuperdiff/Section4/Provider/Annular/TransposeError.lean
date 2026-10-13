/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.BlockResponse
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.FinalStitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledAdjointEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.AdjointInjection
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq

/-!
# TransposeError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transpose invariance of the `(2,2)` homogenization error at an isotropic comparator

ABK26, Section 4.1: the manuscript runs the ugly estimate
`e.ugly.estimate.for.J` a second time "for the transposed field", and asserts
that the transposed estimate holds with the same right-hand side.

This module supplies the deterministic half of that argument at the `𝓔_{s,2,2}`
slot: the error functional is **pointwise** unchanged when the coefficient
family is replaced by its adjoint, so nothing has to be paid for the transposed
leg's error atom.

## The mechanism

`𝓔` is built from `normalizedBlockResponseMax R a a0`, the supremum of the
*doubled* response `bfJ(R, P, Q; a)` over the normalized `2d`-sphere.
CoarseGraining's unconditional splitting identity
`doubledResponseJ_eq_half_responseJ_adjoint_sum`

```
bfJ(U, (p,q), (q*,p*); a) = ½ J(U, p−p*, q*−q; a) + ½ J(U, p*+p, q*+q; aᵀ)
```

read at `aᵀ` (and back at `aᵀᵀ ≈ a`) says exactly that transposing the field is
the same as flipping the sign of the *flux* half of both block loads:

```
bfJ(U, P, Q; aᵀ) = bfJ(U, ΦP, ΦQ; a) ,      Φ(p,q) = (p, −q) .
```

At an **isotropic** background `a0 = σ Id` the constant block matrix is `diag(σ
Id, σ⁻¹ Id)`, which commutes with `Φ`; and `Φ` preserves the normalization `⟨P,
bfA₀ P⟩`.  So `Φ` permutes the admissible probes and the two suprema coincide.
No matrix square root is ever computed: the whole argument runs through
CoarseGraining's representation-free admission gate
`normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one`.

Composing with the proved `(J3)` carrier identity
`Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint` (`a_m(−ω) = a_m(ω)ᵀ`,
read at the family level by
`Localization.coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq`)
turns this into the sample-level statement that the `𝒢₂` atom `𝓔_{s,2,2}(□_n;
a_{n−2}, σ_{n−2})` is invariant under whole-sequence negation.

## What is proved

* `doubledResponseJ_transpose` — the flip identity for the doubled response.
* `normalizedBlockResponseMax_adjointFamily` — the one-cube invariance.
* `scaleResponseAtScale_adjointFamily`, `homogenizationError_adjointFamily`,
  `homogenizationErrorOnCube_adjointFamily` — the invariance of the whole `𝓔`
  chain, for every pair of exponents.
* `annularErrorAtom_negateCutoffSample`, `annularErrorAtomMax_negateCutoffSample`
  — the sample-level invariance of the `𝒢₂` atom and of the annulus maximum.

## References

* ABK26, (the transposed ugly estimate); (`𝒢₂`).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Localization
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the flux sign flip on doubled block vectors -/

/-- The flux sign flip `Φ(p,q) = (p, −q)` on doubled block vectors. -/
def blockFlip (X : BlockVec d) : BlockVec d := (X.1, -X.2)

@[simp] theorem blockFlip_blockFlip (X : BlockVec d) : blockFlip (blockFlip X) = X := by
  simp [blockFlip]

/-- **Transposing the field is flipping the flux half of both block loads.**

Read off CoarseGraining's unconditional splitting identity
`doubledResponseJ_eq_half_responseJ_adjoint_sum` at `aᵀ` and at `a`, together
with `responseJ U aᵀᵀ = responseJ U a`. -/
theorem doubledResponseJ_transpose (U : Domain d) (a : CoeffOn U) (P Q' : BlockVec d) :
    doubledResponseJ U a.transpose P Q' =
      doubledResponseJ U a (blockFlip P) (blockFlip Q') := by
  have hPQ : P = (P.1, P.2) := rfl
  have hQQ : Q' = (Q'.1, Q'.2) := rfl
  have hL := doubledResponseJ_eq_half_responseJ_adjoint_sum U a.transpose P.1 Q'.2 P.2 Q'.1
  have hR := doubledResponseJ_eq_half_responseJ_adjoint_sum U a P.1 (-Q'.2) (-P.2) Q'.1
  have hTT : responseJ U a.transpose.transpose (Q'.2 + P.1) (Q'.1 + P.2)
      = responseJ U a (Q'.2 + P.1) (Q'.1 + P.2) :=
    responseJ_eq_ofAEEq (CoeffOn.transpose_transpose_aeeq a) _ _
  have hsub : P.1 - -Q'.2 = Q'.2 + P.1 := by rw [sub_neg_eq_add, add_comm]
  have hsub2 : Q'.1 - -P.2 = Q'.1 + P.2 := by rw [sub_neg_eq_add]
  have hadd : -Q'.2 + P.1 = P.1 - Q'.2 := by rw [add_comm, ← sub_eq_add_neg]
  have hadd2 : Q'.1 + -P.2 = Q'.1 - P.2 := by rw [← sub_eq_add_neg]
  rw [hPQ, hQQ] at hL hR ⊢
  change doubledResponseJ U a.transpose (P.1, P.2) (Q'.1, Q'.2) = _
  rw [hL]
  change _ = doubledResponseJ U a (P.1, -P.2) (Q'.1, -Q'.2)
  rw [hR, hsub, hsub2, hadd, hadd2, hTT]
  ring

/-! ## Part B -- the flip is a symmetry of the isotropic normalization -/

private theorem ofFullBlockVec_mulVec' (M : FullBlockMat d) (P : BlockVec d) :
    ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) =
      blockMatVecMul (ofFullBlockMat M) P := by
  have h := toFullBlockVec_blockMatVecMul (ofFullBlockMat M) P
  rw [toFullBlockMat_ofFullBlockMat] at h
  rw [← h, ofFullBlockVec_toFullBlockVec]

/-- **The structure of a normalized block probe.**  Its co-load is the image
under the constant block matrix, and its quadratic normalization is `1`; the
matrix square root never has to be computed.

This is a forced, disclosed re-derivation of the `private` upstream helper
`BlockResponse.blockProbe_of_mem_valueSet`. -/
theorem blockProbe_normalization {a0 : Mat d} {lam Lam : ℝ}
    (ha0 : IsEllipticMatrix lam Lam a0) {e : FullBlockVec d}
    (he : Ch02.fullBlockVecNormSq e = 1) :
    ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e) =
        blockMatVecMul (constantBlockMatrix a0)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)) ∧
      blockVecDot (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (blockMatVecMul (constantBlockMatrix a0)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))) = 1 := by
  classical
  set M : FullBlockMat d := Ch02.constantFullBlockMatrix a0 with hMdef
  set S : FullBlockMat d := Ch02.constantFullBlockMatrixSqrt a0 with hSdef
  have hMpos : M.PosDef := by
    rw [hMdef]
    exact constantFullBlockMatrix_posDef_of_isEllipticMatrix (a0 := a0) ha0
  have hSunit : IsUnit S := by
    rw [hSdef, Ch02.constantFullBlockMatrixSqrt, ← hMdef]
    exact (CFC.isUnit_sqrt_iff M).2 hMpos.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det (A := S)).mp hSunit
  have hSS : S * S = M := by
    have hsq : S ^ 2 = M := by
      rw [hSdef, Ch02.constantFullBlockMatrixSqrt, ← hMdef]
      exact CFC.sq_sqrt M hMpos.posSemidef.nonneg
    rwa [pow_two] at hsq
  set P : BlockVec d :=
    ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e) with hPdef
  have htoP : toFullBlockVec P = Matrix.mulVec S⁻¹ e := by
    rw [hPdef, toFullBlockVec_ofFullBlockVec, Ch02.constantFullBlockMatrixInvSqrt, hSdef]
  have hMS : M * S⁻¹ = S := by
    rw [← hSS, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.mul_one]
  have hSSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hco : blockMatVecMul (constantBlockMatrix a0) P =
      ofFullBlockVec (Matrix.mulVec S e) := by
    have hofM : ofFullBlockMat M = constantBlockMatrix a0 := by
      rw [hMdef, Ch02.constantFullBlockMatrix, ofFullBlockMat_toFullBlockMat]
    calc blockMatVecMul (constantBlockMatrix a0) P
        = ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) := by
          rw [ofFullBlockVec_mulVec', hofM]
      _ = ofFullBlockVec (Matrix.mulVec M (Matrix.mulVec S⁻¹ e)) := by rw [htoP]
      _ = ofFullBlockVec (Matrix.mulVec (M * S⁻¹) e) := by rw [Matrix.mulVec_mulVec]
      _ = ofFullBlockVec (Matrix.mulVec S e) := by rw [hMS]
  refine ⟨hco.symm, ?_⟩
  have hnorm :=
    fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq (a0 := a0) ha0 P
  rw [htoP, ← hSdef, Matrix.mulVec_mulVec, hSSinv] at hnorm
  rw [← hnorm, Matrix.one_mulVec]
  exact he

/-- At an isotropic background the constant block matrix `diag(σ Id, σ⁻¹ Id)`
commutes with the flux sign flip. -/
theorem blockFlip_blockMatVecMul_scalarMatrix {σ0 : ℝ} (hσ0 : 0 < σ0) (P : BlockVec d) :
    blockFlip (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) P) =
      blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) (blockFlip P) := by
  have hz : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x
    funext i
    simp [matVecMul]
  rw [constantBlockMatrix_scalarMatrix hσ0]
  simp only [blockFlip, blockMatVecMul, matVecMul_scalarMatrix, hz, add_zero, zero_add,
    smul_neg]

/-- The flip preserves the isotropic block normalization. -/
theorem blockVecDot_blockFlip_scalarMatrix {σ0 : ℝ} (hσ0 : 0 < σ0) (P : BlockVec d) :
    blockVecDot (blockFlip P)
        (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) (blockFlip P)) =
      blockVecDot P (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ0)) P) := by
  rw [← blockFlip_blockMatVecMul_scalarMatrix hσ0]
  simp [blockFlip, blockVecDot, vecDot]

/-! ## Part C -- the one-cube block maximum is transpose invariant -/

private theorem normalizedBlockResponseMax_le_of_flip
    (F G : TriadicCoeffFamily d) (R : TriadicCube d) {σ0 : ℝ} (hσ0 : 0 < σ0)
    (h : ∀ P Q' : BlockVec d,
      doubledResponseJ (cubeDomain R) (G.coeffOn R) P Q' =
        doubledResponseJ (cubeDomain R) (F.coeffOn R) (blockFlip P) (blockFlip Q')) :
    normalizedBlockResponseMax R G (scalarMatrix (d := d) σ0)
      ≤ normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) := by
  classical
  have ha0 : IsEllipticMatrix σ0 σ0 (scalarMatrix (d := d) σ0) :=
    isEllipticMatrix_scalarMatrix hσ0
  unfold Ch02.normalizedBlockResponseMax
  refine Real.sSup_le ?_ (normalizedBlockResponseMax_nonneg R F _)
  rintro x ⟨e, he, rfl⟩
  obtain ⟨hco, hquad⟩ := blockProbe_normalization (a0 := scalarMatrix (d := d) σ0) ha0 he
  rw [h, hco, blockFlip_blockMatVecMul_scalarMatrix hσ0]
  refine le_csSup
    (normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := F) (Q := R) (R := R) (k := R.scale)
      (scalarMatrix (d := d) σ0) (by simp [descendantsAtScale_self])) ?_
  refine normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one R F ha0 _ ?_
  rw [blockVecDot_blockFlip_scalarMatrix hσ0]
  exact hquad

/-- **The normalized block-response maximum is transpose invariant at an isotropic
comparator.**  This is the inner quantity of `d.mathcal.E`, so it is the whole
content at the `(2,2)` error slot. -/
theorem normalizedBlockResponseMax_adjointFamily
    (F : TriadicCoeffFamily d) (R : TriadicCube d) {σ0 : ℝ} (hσ0 : 0 < σ0) :
    normalizedBlockResponseMax R (adjointFamily F) (scalarMatrix (d  := d) σ0) =
      normalizedBlockResponseMax R F (scalarMatrix (d := d) σ0) := by
  refine le_antisymm ?_ ?_
  · refine normalizedBlockResponseMax_le_of_flip F (adjointFamily F) R hσ0 (fun P Q' => ?_)
    rw [adjointFamily_coeffOn]
    exact doubledResponseJ_transpose (cubeDomain R) (F.coeffOn R) P Q'
  · refine normalizedBlockResponseMax_le_of_flip (adjointFamily F) F R hσ0 (fun P Q' => ?_)
    rw [adjointFamily_coeffOn,
      doubledResponseJ_transpose (cubeDomain R) (F.coeffOn R) (blockFlip P) (blockFlip Q'),
      blockFlip_blockFlip, blockFlip_blockFlip]

/-! ## Part D -- the whole `𝓔` chain -/

theorem maxDescendantNormalizedBlockResponseAtScale_adjointFamily
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) (k : ℤ) {σ0 : ℝ} (hσ0 : 0 < σ0) :
    maxDescendantNormalizedBlockResponseAtScale Q k (adjointFamily F)
        (scalarMatrix (d  := d) σ0) =
      maxDescendantNormalizedBlockResponseAtScale Q k F (scalarMatrix (d := d) σ0) := by
  unfold Ch02.maxDescendantNormalizedBlockResponseAtScale
  exact congrArg _ (funext fun R => normalizedBlockResponseMax_adjointFamily F R hσ0)

theorem scaleResponseAtScale_adjointFamily
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) (k : ℤ) (p : Ch02.MultiscaleExponent)
    {σ0 : ℝ} (hσ0 : 0 < σ0) :
    scaleResponseAtScale Q k p (adjointFamily F) (scalarMatrix (d  := d) σ0) =
      scaleResponseAtScale Q k p F (scalarMatrix (d := d) σ0) := by
  cases p with
  | finite pp =>
      change Real.rpow (Ch02.finsetAverageReal (descendantsAtScale Q k)
            (fun R => Real.rpow (normalizedBlockResponseMax R (adjointFamily F)
              (scalarMatrix (d := d) σ0)) (pp / 2))) (1 / pp)
        = Real.rpow (Ch02.finsetAverageReal (descendantsAtScale Q k)
            (fun R => Real.rpow (normalizedBlockResponseMax R F
              (scalarMatrix (d := d) σ0)) (pp / 2))) (1 / pp)
      congr 2
      exact funext fun R => by rw [normalizedBlockResponseMax_adjointFamily F R hσ0]
  | infinity =>
      change Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k (adjointFamily F)
            (scalarMatrix (d := d) σ0)) (1 / 2)
        = Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k F
            (scalarMatrix (d := d) σ0)) (1 / 2)
      rw [maxDescendantNormalizedBlockResponseAtScale_adjointFamily F Q k hσ0]

theorem homogenizationError_adjointFamily
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (p q : Ch02.MultiscaleExponent) {σ0 : ℝ} (hσ0 : 0 < σ0) :
    HomogenizationError Q n s p q (adjointFamily F) (scalarMatrix (d  := d) σ0) =
      HomogenizationError Q n s p q F (scalarMatrix (d := d) σ0) := by
  cases q with
  | finite qq =>
      have hsum : (∑' l : ℕ, Ch02.geometricWeight s qq l *
            Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p (adjointFamily F)
              (scalarMatrix (d := d) σ0)) qq)
          = ∑' l : ℕ, Ch02.geometricWeight s qq l *
            Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p F
              (scalarMatrix (d := d) σ0)) qq :=
        tsum_congr fun l => by rw [scaleResponseAtScale_adjointFamily F Q _ p hσ0]
      change Ch02.HomogenizationErrorFinite Q n s p qq (adjointFamily F)
          (scalarMatrix (d := d) σ0) = _
      unfold Ch02.HomogenizationErrorFinite
      rw [hsum]
      rfl
  | infinity =>
      have hset : {m : ℝ | ∃ l : ℕ, m = Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p (adjointFamily F)
              (scalarMatrix (d := d) σ0)}
          = {m : ℝ | ∃ l : ℕ, m = Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p F (scalarMatrix (d := d) σ0)} := by
        apply Set.ext
        intro m
        constructor
        · rintro ⟨l, rfl⟩
          exact ⟨l, by rw [scaleResponseAtScale_adjointFamily F Q _ p hσ0]⟩
        · rintro ⟨l, rfl⟩
          exact ⟨l, by rw [scaleResponseAtScale_adjointFamily F Q _ p hσ0]⟩
      change Ch02.HomogenizationErrorInfinity Q n s p (adjointFamily F)
          (scalarMatrix (d := d) σ0) = _
      unfold Ch02.HomogenizationErrorInfinity
      rw [hset]
      rfl

/-- **`𝓔_{s,p,q}(Q; aᵀ, σ Id) = 𝓔_{s,p,q}(Q; a, σ Id)`**, for every pair of
exponents. -/
theorem homogenizationErrorOnCube_adjointFamily
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) (s : ℝ)
    (p q : Ch02.MultiscaleExponent) {σ0 : ℝ} (hσ0 : 0 < σ0) :
    HomogenizationErrorOnCube Q s p q (adjointFamily F) (scalarMatrix (d  := d) σ0) =
      HomogenizationErrorOnCube Q s p q F (scalarMatrix (d := d) σ0) :=
  homogenizationError_adjointFamily F Q Q.scale s p q hσ0

/-! ## Part E -- the sample-level `𝒢₂` atom -/

/-- Whole-sequence negation commutes with real translation on the cutoff
carrier. -/
theorem translateCutoffSample_negateCutoffSample (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    Cutoff.translateCutoffSample z (Cutoff.negateCutoffSample omega) =
      Cutoff.negateCutoffSample (Cutoff.translateCutoffSample z omega) := by
  apply Subtype.ext
  funext k
  exact translate_negate z (omega.1 k)

/-- **The `𝒢₂` atom is invariant under whole-sequence negation.**

`𝓔_{s,2,2}(□_n; a_{n−2}(−ω), σ_{n−2}) = 𝓔_{s,2,2}(□_n; a_{n−2}(ω), σ_{n−2})`,
pointwise in `ω`: the `(J3)` carrier identity `a_m(−ω) = a_m(ω)ᵀ` composed with
`homogenizationErrorOnCube_adjointFamily`. -/
theorem annularErrorAtom_negateCutoffSample (M : ABKModel d) (n : ℤ)
    (s : ℝ) (omega : Cutoff.CutoffSample d) :
    Support.annularErrorAtom M n s (Cutoff.negateCutoffSample omega) =
      Support.annularErrorAtom M n s omega  := by
  have hchar := Support.cutoffHomogenizationErrorRaw22_characterization M (n - 2) n s
    (Annealed.sigmaBar M (n - 2))
  have hpos : (0 : ℝ) < ((Annealed.sigmaBar M (n - 2) : Observable.PositiveScalar) : ℝ) :=
    (Annealed.sigmaBar M (n - 2)).2
  rw [Support.annularErrorAtom_def, Support.annularErrorAtom_def,
    hchar (Cutoff.negateCutoffSample omega), hchar omega,
    Ch02.HomogenizationErrorOnCube_eq_ofAEEq
      (coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq M (n - 2) omega)]
  exact homogenizationErrorOnCube_adjointFamily
    (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) (originCube d n) s
    (.finite 2) (.finite 2) hpos

/-- **The annulus maximum of the `𝒢₂` atoms is invariant under whole-sequence
negation.**  The lattice index set is deterministic and the translations commute
with the negation. -/
theorem annularErrorAtomMax_negateCutoffSample (M : ABKModel d) (s : ℝ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    annularErrorAtomMax M s (Cutoff.negateCutoffSample omega) j n =
      annularErrorAtomMax M s omega j n  := by
  unfold annularErrorAtomMax
  refine congrArg _ (funext fun v => ?_)
  rw [translateCutoffSample_negateCutoffSample, annularErrorAtom_negateCutoffSample]

end

end Algsuperdiff.Section4.Provider.Annular
