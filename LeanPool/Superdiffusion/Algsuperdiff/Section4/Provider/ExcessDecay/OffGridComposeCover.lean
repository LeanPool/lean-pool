/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridErrorCarrier

/-!
# OffGridComposeCover

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The doubled response across the off-grid covering

`OffGridStabilitySubadditivity.lean` proved countable subadditivity for
CoarseGraining's **scalar** `Homogenization.ResponseJ` across the maximal grid
cubes of an arbitrary real translate `w + □_k`.  The printed transport
`e.mathcalE.stability.applied` (ABK26) needs it for the **doubled** response
`𝐉`, and after that for the unit-sphere maximum `max_{|e|=1} 𝐉`.

Two points make the recombination lossless:

* the majorant of each scalar leg is taken to be *that leg's own* value on the
  subcube, so nothing is thrown away before the two legs are added; the required
  summability of each leg is obtained by comparison, using
  `0 ≤ J ≤ 2·𝐉` (both summands of the splitting are nonnegative);
* the summed per-cube value is then, by the bridge
  `setDoubledResponseJ_openCubeSet`, exactly `𝐉(Q)`, which is at most
  `max_{|e|=1} 𝐉(Q)` — so the constant `1`, not `2`, is what the composition
  inherits.

The unit-sphere maximum is then `csSup_le` against the *e-independent*
right-hand side; the boundedness needed to compare a single `e` with the
maximum is CoarseGraining's descendant-indexed
`Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale`,
applied at the enclosing **grid** cube `K` — the maximal cubes of `w + □_k` are
forced to be triadic descendants of `K` by the composition's
`mem_descendantsAtScale_of_cubeSet_subset`, so no off-grid analogue of the
boundedness lemma is needed.

## Main results

* `setDoubledResponseJ_le_tsum_maximalCubes` — the doubled response of the
  off-grid cube across its maximal grid subcubes.
* `offGridBlockResponseMax_le_tsum_maximalCubes` — the same for the unit-sphere
  maximum.

## References

* ABK26, `l.lambdas.stability`, (the subadditivity display).
* ABK26, `e.mathcalE.stability.applied`.
* CoarseGraining,
  `Homogenization/Book/Ch02/Theorems/DeterministicIdentities.lean`,
  `Homogenization/Book/Ch02/Theorems/HomogenizationError/ResponseBounds.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Every maximal grid cube of an off-grid cube contained in a grid cube `K` is
a triadic descendant of `K`.  Recognition only; the analytic content is nil. -/
theorem mem_descendantsAtScale_of_maximalCubeIn {w : Vec d} {R K Q : TriadicCube d}
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale)
    (hQ : MaximalCubeIn (offGridCube w R) Q) :
    Q ∈ descendantsAtScale K Q.scale :=
  mem_descendantsAtScale_of_cubeSet_subset (hQ.1.trans hKsub)
    (le_trans (scale_le_of_maximalCubeIn_offGridCube hQ) hRK)

/-- On a maximal grid subcube, the normalized doubled response of a single unit
vector is at most the cube's unit-sphere maximum. -/
theorem setDoubledResponseJ_openCubeSet_le_normalizedBlockResponseMax
    {w : Vec d} {R K Q : TriadicCube d} {g : CoeffField d} (A : Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale)
    (hQ : MaximalCubeIn (offGridCube w R) Q)
    (e : FullBlockVec d) (he : Ch02.fullBlockVecNormSq e = 1) :
    setDoubledResponseJ (openCubeSet Q) g
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) ≤
      Ch02.normalizedBlockResponseMax Q A a0 := by
  have hdesc : Q ∈ descendantsAtScale K Q.scale :=
    mem_descendantsAtScale_of_maximalCubeIn hKsub hRK hQ
  rw [setDoubledResponseJ_openCubeSet Q A g (hg Q)]
  exact le_csSup
    (Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale A a0 hdesc)
    ⟨e, he, rfl⟩

/-- **The doubled response across the covering.**

For an arbitrary real translate `w + R` contained in the grid cube `K`, the
`A₀`-normalized doubled response of `w + R` at a unit vector `e` is at most the
`|Q|/|w + R|`-weighted sum of any majorant of the unit-sphere maxima of the
maximal grid subcubes.  Proved by two applications of the countable
subadditivity's scalar subadditivity and CoarseGraining's splitting identity; no
new variational analysis. -/
theorem setDoubledResponseJ_le_tsum_maximalCubes
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale)
    (B : TriadicCube d → ℝ)
    (hB : ∀ Q : TriadicCube d, MaximalCubeIn (offGridCube w R) Q →
      Ch02.normalizedBlockResponseMax Q A a0 ≤ B Q)
    (hsummable : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d))
    (e : FullBlockVec d) (he : Ch02.fullBlockVecNormSq e = 1) :
    setDoubledResponseJ (offGridCube w R) g
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) ≤
      (cubeVolume R)⁻¹ * ∑' Q : maximalCubes (offGridCube w R),
        cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) := by
  classical
  set Pv : BlockVec d :=
    ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e) with hPv
  set Qv : BlockVec d :=
    ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e) with hQv
  set p1 : Vec d := Pv.1 - Qv.2 with hp1
  set q1 : Vec d := Qv.1 - Pv.2 with hq1
  set p2 : Vec d := Qv.2 + Pv.1 with hp2
  set q2 : Vec d := Qv.1 + Pv.2 with hq2
  set f1 : maximalCubes (offGridCube w R) → ℝ := fun Q =>
    cubeVolume (Q : TriadicCube d) * ResponseJ (openCubeSet (Q : TriadicCube d)) p1 q1 g
    with hf1
  set f2 : maximalCubes (offGridCube w R) → ℝ := fun Q =>
    cubeVolume (Q : TriadicCube d) *
      ResponseJ (openCubeSet (Q : TriadicCube d)) p2 q2 (adjointCoeffField g) with hf2
  set fB : maximalCubes (offGridCube w R) → ℝ := fun Q =>
    cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) with hfB
  -- the per-cube doubled bound
  have hcube : ∀ Q : maximalCubes (offGridCube w R),
      setDoubledResponseJ (openCubeSet (Q : TriadicCube d)) g Pv Qv ≤ B (Q : TriadicCube d) :=
    fun Q => le_trans
      (setDoubledResponseJ_openCubeSet_le_normalizedBlockResponseMax A a0 hg hKsub hRK Q.2 e he)
      (hB _ Q.2)
  have hvol : ∀ Q : maximalCubes (offGridCube w R), (0 : ℝ) ≤ cubeVolume (Q : TriadicCube d) :=
    fun Q => (cubeVolume_pos _).le
  -- summability of each scalar leg, by comparison with twice the majorant
  have hmaj : Summable fun Q : maximalCubes (offGridCube w R) => 2 * fB Q := hsummable.mul_left 2
  have hsum1 : Summable f1 := by
    refine Summable.of_nonneg_of_le (fun Q => ?_) (fun Q => ?_) hmaj
    · exact mul_nonneg (hvol Q) (HCPolySupport.responseJ_nonneg _ _ _ g)
    · have hle : ResponseJ (openCubeSet (Q : TriadicCube d)) p1 q1 g ≤ 2 * B (Q : TriadicCube d) :=
        le_trans (responseJ_le_two_mul_setDoubledResponseJ_left _ g Pv Qv)
          (by linarith only [hcube Q])
      calc f1 Q ≤ cubeVolume (Q : TriadicCube d) * (2 * B (Q : TriadicCube d)) :=
            mul_le_mul_of_nonneg_left hle (hvol Q)
        _ = 2 * fB Q := by rw [hfB]; ring
  have hsum2 : Summable f2 := by
    refine Summable.of_nonneg_of_le (fun Q => ?_) (fun Q => ?_) hmaj
    · exact mul_nonneg (hvol Q) (HCPolySupport.responseJ_nonneg _ _ _ (adjointCoeffField g))
    · have hle : ResponseJ (openCubeSet (Q : TriadicCube d)) p2 q2 (adjointCoeffField g) ≤
          2 * B (Q : TriadicCube d) :=
        le_trans (responseJ_le_two_mul_setDoubledResponseJ_right _ g Pv Qv)
          (by linarith only [hcube Q])
      calc f2 Q ≤ cubeVolume (Q : TriadicCube d) * (2 * B (Q : TriadicCube d)) :=
            mul_le_mul_of_nonneg_left hle (hvol Q)
        _ = 2 * fB Q := by rw [hfB]; ring
  -- the two scalar legs
  have hJ1 : ResponseJ (offGridCube w R) p1 q1 g ≤ (cubeVolume R)⁻¹ * ∑' Q, f1 Q :=
    responseJ_offGridCube_le_tsum_maximalCubes hEll
      (fun Q => ResponseJ (openCubeSet Q) p1 q1 g) (fun _ => le_rfl) hsum1
  have hJ2 : ResponseJ (offGridCube w R) p2 q2 (adjointCoeffField g) ≤
      (cubeVolume R)⁻¹ * ∑' Q, f2 Q :=
    responseJ_offGridCube_le_tsum_maximalCubes (isEllipticFieldOn_adjointCoeffField hEll)
      (fun Q => ResponseJ (openCubeSet Q) p2 q2 (adjointCoeffField g)) (fun _ => le_rfl) hsum2
  -- recombine the two legs into one series and compare with the majorant
  have hhalf : ∀ Q : maximalCubes (offGridCube w R),
      (1 / 2 : ℝ) * f1 Q + (1 / 2 : ℝ) * f2 Q =
        cubeVolume (Q : TriadicCube d) *
          setDoubledResponseJ (openCubeSet (Q : TriadicCube d)) g Pv Qv := by
    intro Q
    rw [hf1, hf2, setDoubledResponseJ]
    ring
  have hsumD : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) *
        setDoubledResponseJ (openCubeSet (Q : TriadicCube d)) g Pv Qv := by
    refine ((hsum1.mul_left (1 / 2 : ℝ)).add (hsum2.mul_left (1 / 2 : ℝ))).congr ?_
    exact hhalf
  have htsumD : (1 / 2 : ℝ) * ∑' Q, f1 Q + (1 / 2 : ℝ) * ∑' Q, f2 Q =
      ∑' Q : maximalCubes (offGridCube w R), cubeVolume (Q : TriadicCube d) *
        setDoubledResponseJ (openCubeSet (Q : TriadicCube d)) g Pv Qv := by
    rw [← hsum1.tsum_mul_left, ← hsum2.tsum_mul_left,
      ← (hsum1.mul_left (1 / 2 : ℝ)).tsum_add (hsum2.mul_left (1 / 2 : ℝ))]
    exact tsum_congr hhalf
  have hDle : (∑' Q : maximalCubes (offGridCube w R), cubeVolume (Q : TriadicCube d) *
      setDoubledResponseJ (openCubeSet (Q : TriadicCube d)) g Pv Qv) ≤ ∑' Q, fB Q :=
    Summable.tsum_le_tsum (fun Q => mul_le_mul_of_nonneg_left (hcube Q) (hvol Q))
      hsumD hsummable
  have hinv : (0 : ℝ) ≤ (cubeVolume R)⁻¹ := inv_nonneg.2 (cubeVolume_pos R).le
  rw [setDoubledResponseJ, ← hp1, ← hq1, ← hp2, ← hq2]
  have hcomb : (1 / 2 : ℝ) * ResponseJ (offGridCube w R) p1 q1 g +
      (1 / 2 : ℝ) * ResponseJ (offGridCube w R) p2 q2 (adjointCoeffField g) ≤
      (cubeVolume R)⁻¹ * ((1 / 2 : ℝ) * ∑' Q, f1 Q + (1 / 2 : ℝ) * ∑' Q, f2 Q) := by
    have h1 := mul_le_mul_of_nonneg_left hJ1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 := mul_le_mul_of_nonneg_left hJ2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hexp : (cubeVolume R)⁻¹ * ((1 / 2 : ℝ) * ∑' Q, f1 Q + (1 / 2 : ℝ) * ∑' Q, f2 Q) =
        (1 / 2 : ℝ) * ((cubeVolume R)⁻¹ * ∑' Q, f1 Q) +
          (1 / 2 : ℝ) * ((cubeVolume R)⁻¹ * ∑' Q, f2 Q) := by ring
    rw [hexp]
    linarith only [h1, h2]
  refine le_trans hcomb ?_
  rw [htsumD]
  exact mul_le_mul_of_nonneg_left hDle hinv

/-- **The unit-sphere maximum across the covering.**

The `e`-free right-hand side of `setDoubledResponseJ_le_tsum_maximalCubes` bounds
the whole unit-sphere maximum, by `csSup_le`. -/
theorem offGridBlockResponseMax_le_tsum_maximalCubes
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale)
    (B : TriadicCube d → ℝ)
    (hB : ∀ Q : TriadicCube d, MaximalCubeIn (offGridCube w R) Q →
      Ch02.normalizedBlockResponseMax Q A a0 ≤ B Q)
    (hsummable : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d)) :
    offGridBlockResponseMax w R g a0 ≤
      (cubeVolume R)⁻¹ * ∑' Q : maximalCubes (offGridCube w R),
        cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) :=
  offGridBlockResponseMax_le fun e he =>
    setDoubledResponseJ_le_tsum_maximalCubes A a0 hg hEll hKsub hRK B hB hsummable e he

end

end Algsuperdiff.Section4.Provider.ExcessDecay
