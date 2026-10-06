/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.InverseJensen
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ReferenceNormalization
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferHelpers
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AdaptedEuclideanComparison
public import LeanPool.HighContrastHomogenization.Entry.Source.CoarseSubadditivity
public import LeanPool.HighContrastHomogenization.Entry.SourceWhitney
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields

/-!
# High-contrast homogenization: Entry.Response.Core.EccentricityScaleDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale decay and eccentricity bounds for the response kernels

This file proves the support lemmas behind the two kernel inputs of the response transfer,
`adapted_response_kernel` and `persistence_transfer_kernel`, consumed at Steps 3 and 4 of
`p.response.transfer`. It shows a response block satisfies a geometric scale-decay bound whenever
its Loewner order decays across scales, produces an eccentricity gap from a bound on the response
block, and proves the Loewner comparisons for the block-scale difference and for the swapped
conjugate at a bounded canonical imbalance, together with the antitonicity of the swapped-conjugate
inverse under that order. A short adjoining module also restates the Euclidean-versus-adapted
comparisons of `AdaptedEuclideanComparison` with the paper's unused unit-range hypothesis put back,
for direct citation. Nothing else here is specific to either kernel.
-/

section
/-!
## Response inputs — the analytic kernels

* E1/E2: HC Lemma 2.15, re-derived at the rounded grid
  `q = explicitRoundedGrid jStar m` with a `C(d,γ)` and every binder witnessed.  HC's
  `a.CFS` premise is unused by the proof; the fine-grid Euclidean adapter supplies the
  concentration input from the unit-range law.  Consumed at `p.response.transfer`,
  with the source term normalized by `p.response.transfer` (`𝐄 ≤ C(d,γ) Π 𝔢(m) 𝐀hom_{t,q}`, i.e.
  `adaptedMean_refBlock_normalization`) and the HC source factor `(1 + K² 3^{-t})^γ ≤ 2` absorbed
  into
  `Csrc` exactly as `adaptedMean_refBlock_normalization` absorbs it (`⌈Csrc log₃(2K)⌉ ≤ j_*`).
  Here `𝔢(m)² = ‖m‖‖m⁻¹‖`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale blockSub)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

/-- **E1** kernel: Euclidean-by-adapted comparison (HC's `e.Euc.by.tilt`, at the rounded grid;
`p.response.transfer`, first inequality): for `ℓ ≥ 1`,
`𝐀hom_{t+ℓ,Id} ≤ (1 + C Π ‖m‖‖m⁻¹‖ 3^{-ℓ}) 𝐀hom_{t,q}`.
Proof route (HC): use maximal adapted cells
capped at `t` to tile `□_{t+ℓ}` up to a null set. Integer stationarity identifies the cap
with `adaptedMean P q t`. Every lower row has relative volume `≤ C(d) 𝔢(m) 3^{j-(t+ℓ)}`
and is controlled by the source bound. Fine cells are recentered into the source window;
the inverse-norm bound two makes this source estimate independent of eccentricity.
The geometric series and `adaptedMean_refBlock_normalization` then give the result.
This uses only stationarity and dagger; the stated unit-range assumption is unnecessary. -/
theorem euclidean_le_adapted_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (jStar : ℤ) ≤ t →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) t ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              ∀ ℓ : ℕ, 1 ≤ ℓ →
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ)))
                  (blockScale (1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)))
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t)) := by
  obtain ⟨Csrc, C, hCsrc, hC, h⟩ := Adapter.forward_comparison d hd γ hγ
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat _hunit hdag
  exact h P E Ψ K S hstat hdag

/-- **E2** kernel: adapted-by-Euclidean comparison (HC's `e.tilt.by.Euc`, at the rounded grid;
`p.response.transfer`, second inequality): for `ℓ, r ≥ 1`,
`𝐀hom_{t+ℓ+r,q} ≤ 𝐀hom_{t+ℓ,Id} + C Π ‖m‖‖m⁻¹‖ 3^{-r} 𝐀hom_{t,q}`.
Same route with the roles exchanged: tile `⋄^q_{t+ℓ+r}` by standard cells capped at `t+ℓ`.
Use stationarity on the cap and the annealed source bound on every lower row, whose volume
fraction is `≤ 12 d^{3/2} 3^{j-(t+ℓ+r)}`. Normalize at the original generation `t`.
The argument applies at every later generation without enlarging the source window.
The stated unit-range assumption is again unnecessary. -/
theorem adapted_le_euclidean_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (jStar : ℤ) ≤ t →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) t ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              ∀ ℓ r : ℕ, 1 ≤ ℓ → 1 ≤ r →
                BlockMatLoewnerLE
                  (blockSub (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (t + (ℓ : ℤ) + (r : ℤ)))
                    (blockScale (C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)))
                      (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t)))
                  (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ))) := by
  obtain ⟨Csrc, C, hCsrc, hC, h⟩ := Adapter.reverse_comparison d hd γ hγ
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat _hunit hdag
  exact h P E Ψ K S hstat hdag

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Response inputs — support lemmas for K1 `adapted_response_kernel` and K2
`persistence_transfer_kernel`

Decomposition of the K1 `adapted_response_kernel` and K2 `persistence_transfer_kernel` inputs
of the response transfer (Step 3 and Step 4).  This file holds the non-kernel support lemmas;
the analytic kernels are in `HCPoly/Entry/Response/Core/EccentricityScaleDecay.lean`.

Notation. `q := Geometry.explicitRoundedGrid jStar m` is the rounded grid (near
`e.rounded.grid.bounds`), `𝐀hom_{j,q} :=
adaptedMean P q j`, `𝐑 := blockSwap d`, and `𝐑A⁻¹𝐑` is written out as in `adaptedMean_swapConj_le`.
The canonical imbalance is `𝔡(A) = ‖G^{-1/2} A G^{-1/2}‖` with `G = 𝐑A⁻¹𝐑` (`canonicalImbalance`),
so `𝔡(A) ≤ c` is the Loewner bound `A ≤ c 𝐑A⁻¹𝐑`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCell adaptedMean blockScale blockSub)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

/-! ## Part P: adapted persistence (`p.response.transfer`, right half) -/

/-- **P1**. `𝔡(A) ≤ c` unpacks to `A ≤ c·𝐑A⁻¹𝐑`.  `canonicalImbalance A` is the
operator norm of `G^{-1/2} A G^{-1/2}` with `G = 𝐑A⁻¹𝐑` positive definite (near
`e.scale.selection.projective.distance`); a symmetric positive semidefinite matrix with operator
norm `≤ c` is `≤ c·I`, and conjugating
back by `G^{1/2}` gives the claim.  Mirror the route inside `canonical_comparison_kernel` (K3) and
use
`sqrt_form`, `psd_dot_le_opNorm`, `swapConj_posDef` from the helpers. -/
theorem loewner_swapConj_of_canonicalImbalance_le {d : ℕ} (_hd : 2 ≤ d) (A : BlockMat d)
    (hAs : IsSymmetricBlockMat A) (hA : Book.Ch02.BlockPosDef A) {c : ℝ}
    (hc : canonicalImbalance A ≤ c) :
    BlockMatLoewnerLE A
      (blockScale c (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d)))) := by
  intro X
  let B : BlockMat d :=
    blockScale c (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d)))
  have hfull : toFullBlockMat A ≤ toFullBlockMat B := by
    simpa only [B, toFullBlockMat_blockScale, toFullBlockMat_ofFullBlockMat] using
      le_of_imbalance_le (posDef_toFullBlockMat hAs hA) hc
  have hx := (Matrix.le_iff.mp hfull).dotProduct_mulVec_nonneg (toFullBlockVec X)
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hx
  have hAq : toFullBlockVec X ⬝ᵥ toFullBlockMat A *ᵥ toFullBlockVec X =
      blockVecDot X (blockMatVecMul A X) := by
    rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
  have hBq : toFullBlockVec X ⬝ᵥ toFullBlockMat B *ᵥ toFullBlockVec X =
      blockVecDot X (blockMatVecMul B X) := by
    rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
  rw [hAq, hBq] at hx
  change 1 / 2 * blockVecDot X (blockMatVecMul A X) ≤
    1 / 2 * blockVecDot X (blockMatVecMul B X)
  linarith only [hx]

/-- **P2**. Inverse-and-swap reverses the Loewner order: for symmetric
`0 < X ≤ Y`, `𝐑Y⁻¹𝐑 ≤ 𝐑X⁻¹𝐑`.  `inv_le_inv_of_le` (helpers) gives `Y⁻¹ ≤ X⁻¹`; congruence by the
symmetric involution `𝐑` (`toFullBlockMat_blockSwap_mul_self`) preserves the order. -/
theorem swapConj_inv_antitone {d : ℕ} (X Y : BlockMat d)
    (hXs : IsSymmetricBlockMat X) (hX : Book.Ch02.BlockPosDef X)
    (hYs : IsSymmetricBlockMat Y) (hXY : BlockMatLoewnerLE X Y) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat Y)⁻¹ * toFullBlockMat (blockSwap d)))
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat X)⁻¹ * toFullBlockMat (blockSwap d))) := by
  let R := toFullBlockMat (blockSwap d)
  let A := ofFullBlockMat (R * (toFullBlockMat Y)⁻¹ * R)
  let B := ofFullBlockMat (R * (toFullBlockMat X)⁻¹ * R)
  have hXf : Matrix.PosDef (toFullBlockMat X) := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      ((Analysis.toFullBlockMat_isHermitian_iff X).2 hXs) ?_
    intro x hx
    have hn : ofFullBlockVec x ≠ 0 := by
      intro h
      apply hx
      have hz := congrArg toFullBlockVec h
      rw [toFullBlockVec_ofFullBlockVec] at hz
      funext i
      have hi := congrFun hz i
      cases i <;> simpa [toFullBlockVec] using hi
    simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec, star_trivial] using hX (ofFullBlockVec x) hn
  have hYh : (toFullBlockMat Y).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff Y).2 hYs
  have hXYf : toFullBlockMat X ≤ toFullBlockMat Y := by
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hYh.sub hXf.isHermitian) ?_)
    intro x
    have hx := hXY (ofFullBlockVec x)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]
  have hYf : Matrix.PosDef (toFullBlockMat Y) :=
    posDef_of_le hXf hYh hXYf
  have hinv : (toFullBlockMat Y)⁻¹ ≤ (toFullBlockMat X)⁻¹ :=
    inv_le_inv_of_le hXf hYf hXYf
  have hRt : Rᵀ = R := by
    ext (i | i) (j | j) <;>
      simp [R, blockSwap, Book.Ch02.blockR, toFullBlockMat, Matrix.transpose,
        Matrix.one_apply, eq_comm]
  have hconj : R * (toFullBlockMat Y)⁻¹ * R ≤
      R * (toFullBlockMat X)⁻¹ * R := by
    simpa [R, hRt] using Analysis.matrix_congr_le hinv R
  intro v
  have hv := (Matrix.le_iff.mp hconj).dotProduct_mulVec_nonneg (toFullBlockVec v)
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hv
  have hAq : toFullBlockVec v ⬝ᵥ (R * (toFullBlockMat Y)⁻¹ * R) *ᵥ toFullBlockVec v =
      blockVecDot v (blockMatVecMul A v) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_ofFullBlockMat]
  have hBq : toFullBlockVec v ⬝ᵥ (R * (toFullBlockMat X)⁻¹ * R) *ᵥ toFullBlockVec v =
      blockVecDot v (blockMatVecMul B v) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_ofFullBlockMat]
  rw [hAq, hBq] at hv
  change 1 / 2 * blockVecDot v (blockMatVecMul A v) ≤
    1 / 2 * blockVecDot v (blockMatVecMul B v)
  linarith only [hv]

/-- **P3** persistence (`p.response.transfer`, right half; expanded manuscript
`hcp.e.random.persistence.transfer.adapted.persistence`).  For
`u ≥ t ≥ j_*` and `𝔡(𝐀hom_{t,q}) ≤ 1 + δad`: `(1+δad)^{-d} 𝐀hom_{t,q} ≤ 𝐀hom_{u,q}`.
Route (stronger than the paper's determinant route, same conclusion): `𝐀_u ≤ 𝐀_t`
(`adaptedMean_antitone`); `𝐀_t ≤ (1+δad) 𝐑𝐀_t⁻¹𝐑` (P1) `≤ (1+δad) 𝐑𝐀_u⁻¹𝐑` (P2) `≤ (1+δad) 𝐀_u`
(`adaptedMean_swapConj_le` at `u`); finally `(1+δad)^{-d} ≤ (1+δad)^{-1}` and
`blockScale_loewner_mono`
(positivity from `adaptedMean_posDef`, symmetry from `isSymmetricBlockMat_annealedBlock`). -/
theorem adaptedMean_persistence (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (t u : ℤ) (ht : (jStar : ℤ) ≤ t) (htu : t ≤ u) {δad : ℝ} (hδ : 0 ≤ δad)
    (himb : canonicalImbalance (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t) ≤ 1 + δad) :
    BlockMatLoewnerLE
      (blockScale ((1 + δad) ^ (-(d : ℝ))) (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar m) u) := by
  let At := adaptedMean P (Geometry.explicitRoundedGrid jStar m) t
  let Au := adaptedMean P (Geometry.explicitRoundedGrid jStar m) u
  have hscale : ∀ {A B : BlockMat d} {c : ℝ}, 0 ≤ c →
      BlockMatLoewnerLE A B → BlockMatLoewnerLE (blockScale c A) (blockScale c B) := by
    intro A B c hc hAB v
    rw [Source.quadratic_blockScale, Source.quadratic_blockScale]
    have hv := mul_le_mul_of_nonneg_left (hAB v) hc
    nlinarith only [hv]
  have hblockPos : ∀ A : BlockMat d, (toFullBlockMat A).PosDef → Book.Ch02.BlockPosDef A := by
    intro A hA X hX
    have hvec : toFullBlockVec X ≠ 0 := by
      intro h
      apply hX
      have h' := congrArg ofFullBlockVec h
      rw [ofFullBlockVec_toFullBlockVec] at h'
      simpa using! h'
    have hq := hA.dotProduct_mulVec_pos hvec
    have hstar : star (toFullBlockVec X) = toFullBlockVec X := rfl
    rw [hstar, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at hq
    exact hq
  have hAtSym : IsSymmetricBlockMat At := by
    simpa [At, adaptedMean] using
      isSymmetricBlockMat_annealedBlock P
        (adaptedCell (Geometry.explicitRoundedGrid jStar m) t)
  have hAuSym : IsSymmetricBlockMat Au := by
    simpa [Au, adaptedMean] using
      isSymmetricBlockMat_annealedBlock P
        (adaptedCell (Geometry.explicitRoundedGrid jStar m) u)
  have hAtPosFull : (toFullBlockMat At).PosDef := by
    simpa [At] using
      Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm t
  have hAuPosFull : (toFullBlockMat Au).PosDef := by
    simpa [Au] using
      Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm u
  have hAtPos : Book.Ch02.BlockPosDef At := hblockPos At hAtPosFull
  have hAuPos : Book.Ch02.BlockPosDef Au := hblockPos Au hAuPosFull
  have hc0 : 0 ≤ 1 + δad := by linarith only [hδ]
  have hAuAt : BlockMatLoewnerLE Au At := by
    simpa [At, Au] using
      Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hjStar m hm t u ht htu
  have hAtSwap :
      BlockMatLoewnerLE At
        (blockScale (1 + δad) (ofFullBlockMat (toFullBlockMat (blockSwap d) *
          (toFullBlockMat At)⁻¹ * toFullBlockMat (blockSwap d)))) := by
    simpa [At] using
      loewner_swapConj_of_canonicalImbalance_le hd At hAtSym hAtPos himb
  have hSwapMono :
      BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (blockSwap d) *
          (toFullBlockMat At)⁻¹ * toFullBlockMat (blockSwap d)))
        (ofFullBlockMat (toFullBlockMat (blockSwap d) *
          (toFullBlockMat Au)⁻¹ * toFullBlockMat (blockSwap d))) :=
    swapConj_inv_antitone Au At hAuSym hAuPos hAtSym hAuAt
  have hSwapAu :
      BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (blockSwap d) *
          (toFullBlockMat Au)⁻¹ * toFullBlockMat (blockSwap d))) Au := by
    simpa [Au] using
      Analysis.adaptedMean_swapConj_le hd P γ E Ψ K S hstat hdag jStar hjStar m hm u
  have hAtAu : BlockMatLoewnerLE At (blockScale (1 + δad) Au) :=
    hAtSwap.trans ((hscale hc0 hSwapMono).trans (hscale hc0 hSwapAu))
  have hcpos : 0 < 1 + δad := by linarith only [hδ]
  have hcle : 1 ≤ 1 + δad := by linarith only [hδ]
  have hdreal : (1 : ℝ) ≤ d := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hd)
  have hpowInv :
      (1 + δad) ^ (-(d : ℝ)) ≤ (1 + δad)⁻¹ := by
    have hpow :
        (1 + δad) ^ (-(d : ℝ)) ≤ (1 + δad) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hcle (by nlinarith only [hdreal])
    simpa [Real.rpow_neg_one] using hpow
  have hmul : (1 + δad) ^ (-(d : ℝ)) * (1 + δad) ≤ 1 := by
    calc
      (1 + δad) ^ (-(d : ℝ)) * (1 + δad)
          ≤ (1 + δad)⁻¹ * (1 + δad) :=
            mul_le_mul_of_nonneg_right hpowInv hcpos.le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  intro v
  have hmain := hAtAu v
  rw [Source.quadratic_blockScale] at hmain
  rw [Source.quadratic_blockScale]
  have hAuNonneg : 0 ≤ blockVecDot v (blockMatVecMul Au v) := by
    by_cases hv : v = 0
    · simp [hv, blockVecDot, vecDot]
    · exact (hAuPos v hv).le
  have hpowNonneg : 0 ≤ (1 + δad) ^ (-(d : ℝ)) :=
    Real.rpow_nonneg hcpos.le _
  have hq :
      blockVecDot v (blockMatVecMul At v) ≤
        (1 + δad) * blockVecDot v (blockMatVecMul Au v) := by
    nlinarith only [hmain]
  have hqmul :
      (1 + δad) ^ (-(d : ℝ)) * blockVecDot v (blockMatVecMul At v) ≤
        (1 + δad) ^ (-(d : ℝ)) *
          ((1 + δad) * blockVecDot v (blockMatVecMul Au v)) :=
    mul_le_mul_of_nonneg_left hq hpowNonneg
  have hlast :
      (1 + δad) ^ (-(d : ℝ)) *
          ((1 + δad) * blockVecDot v (blockMatVecMul Au v)) ≤
        blockVecDot v (blockMatVecMul Au v) := by
    nlinarith only [hmul, hAuNonneg]
  nlinarith only [hqmul, hlast]

/-! ## Part A: Loewner arithmetic and the gap choice (`p.response.transfer`) -/

/-- **A4** (Loewner arithmetic). From `X - c·A ≤ Y` and `a·A ≤ X` follows `(a - c)·A ≤ Y`
(the lower bound: combine the reverse comparison with persistence at `m_ent + r`).
Unfold `BlockMatLoewnerLE`; `blockSub`/`blockScale` are entrywise, so the quadratic forms are
linear. -/
theorem loewner_scale_sub_of_le {d : ℕ} (X Y A : BlockMat d) {a c : ℝ}
    (h1 : BlockMatLoewnerLE (blockSub X (blockScale c A)) Y)
    (h2 : BlockMatLoewnerLE (blockScale a A) X) :
    BlockMatLoewnerLE (blockScale (a - c) A) Y := by
  intro v
  have hh1 := h1 v
  have hh2 := h2 v
  have hmul : ∀ M N : BlockMat d,
      blockMatVecMul (blockSub M N) v =
        blockMatVecMul M v - blockMatVecMul N v := by
    intro M N
    have h : blockMatVecMul (blockSub M N) v =
        (matVecMul (M.upperLeft - N.upperLeft) v.1 +
            matVecMul (M.upperRight - N.upperRight) v.2,
          matVecMul (M.lowerLeft - N.lowerLeft) v.1 +
            matVecMul (M.lowerRight - N.lowerRight) v.2) := rfl
    rw [h, sub_matVecMul, sub_matVecMul, sub_matVecMul, sub_matVecMul]
    have h' : blockMatVecMul M v - blockMatVecMul N v =
        (matVecMul M.upperLeft v.1 + matVecMul M.upperRight v.2 -
            (matVecMul N.upperLeft v.1 + matVecMul N.upperRight v.2),
          matVecMul M.lowerLeft v.1 + matVecMul M.lowerRight v.2 -
            (matVecMul N.lowerLeft v.1 + matVecMul N.lowerRight v.2)) := rfl
    rw [h', Prod.mk.injEq]
    constructor <;> abel
  have hscale : ∀ b : ℝ,
      blockMatVecMul (blockScale b A) v = b • blockMatVecMul A v := by
    intro b
    ext i <;> simp [blockScale, blockMatVecMul, smul_matVecMul, smul_add]
  rw [hmul, blockVecDot_sub_right, hscale c, blockVecDot_smul_right] at hh1
  rw [hscale a, blockVecDot_smul_right] at hh2
  rw [hscale (a - c), blockVecDot_smul_right]
  nlinarith only [hh1, hh2]

/-- **A2** (real analysis). The gap choice: with the source constant
`C = C(d,γ)`, the eccentricity exponent `Cglob` and a target `η`, there is `Cresp` such that for
every
`Pival ≥ 1` and `e = ‖m‖‖m⁻¹‖ ≥ 1` with `e^{1/2} ≤ (2+Pival)^{Cglob}` (RawOutput `ecc`) some `ℓ ≥
1` has
`C Pival e 3^{-ℓ} ≤ η` and `ℓ ≤ Cresp log₃(2+Pival)`.  Take `ℓ := ⌈log₃(C Pival e / η)⌉₊ + 1`; then
`ℓ ≤ 2 + log₃ C + (1 + 2 Cglob) log₃(2+Pival) + log₃(1/η)` and `log₃(2+Pival) ≥ 1` since `2 +
Pival ≥ 3`. -/
theorem exists_gap_of_eccentricity (C Cglob η : ℝ) (hC : 0 < C) (hCglob : 0 < Cglob)
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ Pival e : ℝ, 1 ≤ Pival → 1 ≤ e → e ^ ((1 : ℝ) / 2) ≤ (2 + Pival) ^ Cglob →
        ∃ ℓ : ℕ, 1 ≤ ℓ ∧ C * Pival * e * (3 : ℝ) ^ (-(ℓ : ℝ)) ≤ η ∧
          (ℓ : ℝ) ≤ Cresp * Real.logb 3 (2 + Pival) := by
  rcases hη with ⟨hηpos, _hηlt⟩
  let D : ℝ := max 1 (Real.logb 3 (C / η))
  let C0 : ℝ := D + 1 + 2 * Cglob
  refine ⟨C0 + 1, ?_, ?_⟩
  · have hDge : 1 ≤ D := le_max_left _ _
    dsimp [C0]
    linarith only [hDge, hCglob]
  · intro Pival e hP he hhalf
    let L : ℝ := Real.logb 3 (2 + Pival)
    let A : ℝ := C0 * L
    let ℓ : ℕ := Nat.ceil A
    refine ⟨ℓ, ?_, ?_, ?_⟩
    · exact (Nat.one_le_ceil_iff).2 (by
        have hDge : 1 ≤ D := le_max_left _ _
        have hL : 1 ≤ L := by
          dsimp [L]
          rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) (by linarith only [hP] : 0 < 2 + Pival)]
          norm_num
          linarith only [hP]
        dsimp [A, C0]
        nlinarith only [hCglob, hDge, hL])
    · have hbase_pos : 0 < 2 + Pival := by linarith only [hP]
      have hbase_nonneg : 0 ≤ 2 + Pival := hbase_pos.le
      have hbase_ge_three : (3 : ℝ) ≤ 2 + Pival := by linarith only [hP]
      have hDge : 1 ≤ D := le_max_left _ _
      have hDnonneg : 0 ≤ D := by linarith only [hDge]
      have hCηpos : 0 < C / η := div_pos hC hηpos
      have hCη_le_threeD : C / η ≤ (3 : ℝ) ^ D := by
        exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3) hCηpos).mp (le_max_right _ _)
      have hthreeD_le_baseD : (3 : ℝ) ^ D ≤ (2 + Pival) ^ D := by
        exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 3) hbase_ge_three hDnonneg
      have hCη_le_baseD : C / η ≤ (2 + Pival) ^ D := hCη_le_threeD.trans hthreeD_le_baseD
      have hP_le_base : Pival ≤ (2 + Pival) := by linarith only [hP]
      have he_nonneg : 0 ≤ e := by linarith only [he]
      have hhalf_nonneg : 0 ≤ e ^ ((1 : ℝ) / 2) := Real.rpow_nonneg he_nonneg _
      have hbaseC_nonneg : 0 ≤ (2 + Pival) ^ Cglob := Real.rpow_nonneg hbase_nonneg _
      have he_le_base2C : e ≤ (2 + Pival) ^ (2 * Cglob) := by
        have hsquares : (e ^ ((1 : ℝ) / 2)) ^ 2 ≤ ((2 + Pival) ^ Cglob) ^ 2 := by
          nlinarith only [hhalf, hhalf_nonneg, hbaseC_nonneg]
        calc
          e = (e ^ ((1 : ℝ) / 2)) ^ 2 := (HCPolySupport.sq_rpow_half_eq_self_of_nonneg he_nonneg).symm
          _ ≤ ((2 + Pival) ^ Cglob) ^ 2 := hsquares
          _ = (2 + Pival) ^ (2 * Cglob) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nonneg]
            congr 1
            norm_num [mul_comm]
      have hCP_le : (C / η) * Pival ≤ (2 + Pival) ^ (D + 1) := by
        calc
          (C / η) * Pival ≤ (2 + Pival) ^ D * (2 + Pival) := by
            exact mul_le_mul hCη_le_baseD hP_le_base (by linarith only [hP]) (Real.rpow_nonneg hbase_nonneg _)
          _ = (2 + Pival) ^ (D + 1) := by
            rw [Real.rpow_add hbase_pos, Real.rpow_one]
      have hX_le_base : C * Pival * e / η ≤ (2 + Pival) ^ C0 := by
        calc
          C * Pival * e / η = (C / η) * Pival * e := by field_simp [hηpos.ne']
          _ ≤ (2 + Pival) ^ (D + 1) * (2 + Pival) ^ (2 * Cglob) := by
            exact mul_le_mul hCP_le he_le_base2C he_nonneg (Real.rpow_nonneg hbase_nonneg _)
          _ = (2 + Pival) ^ C0 := by
            dsimp [C0]
            rw [← Real.rpow_add hbase_pos]
      have hbaseC0_eq : (2 + Pival) ^ C0 = (3 : ℝ) ^ A := by
        calc
          (2 + Pival) ^ C0 = ((3 : ℝ) ^ L) ^ C0 := by
            rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) hbase_pos]
          _ = (3 : ℝ) ^ (L * C0) := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ = (3 : ℝ) ^ A := by
            congr 1
            dsimp [A]
            ring
      have hA_le_ell : A ≤ (ℓ : ℝ) := by
        dsimp [ℓ]
        exact Nat.le_ceil A
      have hX_le_threeell : C * Pival * e / η ≤ (3 : ℝ) ^ (ℓ : ℝ) := by
        calc
          C * Pival * e / η ≤ (2 + Pival) ^ C0 := hX_le_base
          _ = (3 : ℝ) ^ A := hbaseC0_eq
          _ ≤ (3 : ℝ) ^ (ℓ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hA_le_ell
      have hCPe_le : C * Pival * e ≤ η * (3 : ℝ) ^ (ℓ : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left hX_le_threeell hηpos.le
        have heq : η * (C * Pival * e / η) = C * Pival * e := by field_simp [hηpos.ne']
        rwa [heq] at hm
      have hdecay_nonneg : 0 ≤ (3 : ℝ) ^ (-(ℓ : ℝ)) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
      calc
        C * Pival * e * (3 : ℝ) ^ (-(ℓ : ℝ)) ≤ (η * (3 : ℝ) ^ (ℓ : ℝ)) * (3 : ℝ) ^ (-(ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right hCPe_le hdecay_nonneg
        _ = η := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          have : (ℓ : ℝ) + -(ℓ : ℝ) = 0 := by ring
          rw [this]
          norm_num
    · have hL : 1 ≤ L := by
        dsimp [L]
        rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) (by linarith only [hP] : 0 < 2 + Pival)]
        norm_num
        linarith only [hP]
      have hDge : 1 ≤ D := le_max_left _ _
      have hC0_nonneg : 0 ≤ C0 := by
        dsimp [C0]
        nlinarith only [hDge, hCglob]
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        nlinarith only [hC0_nonneg, hL]
      have hceil_lt : (ℓ : ℝ) < A + 1 := by
        dsimp [ℓ]
        exact Nat.ceil_lt_add_one hA_nonneg
      have hA1_le : A + 1 ≤ (C0 + 1) * L := by
        dsimp [A]
        nlinarith only [hL]
      exact (le_of_lt hceil_lt).trans hA1_le

/-! ## Part S: the printed Step-3 bookkeeping (`p.response.transfer`) -/

/-- **S1**. `e.global.selection.scales` (RawOutput `hs_lo`,
`j_* + ⌈B log₃(2+Pival)⌉ ≤ s`) turns `3^{-ρ(s - j_*)}` into `(2+Pival)^{-ρB}` for `ρ ≥ 0`. -/
theorem scale_decay_of_hs_lo (jStar : ℕ) (s : ℤ) (B Pival ρ : ℝ) (hPival : 3 ≤ 2 + Pival) (hρ : 0 ≤ ρ)
    (hs : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + Pival)⌉ ≤ s) :
    (3 : ℝ) ^ (-(ρ * ((s : ℝ) - (jStar : ℝ)))) ≤ (2 + Pival) ^ (-(ρ * B)) := by
  have pos_3 : (0 : ℝ) < 3 := by norm_num
  have pos_P : (0 : ℝ) < 2 + Pival := by linarith only [hPival]
  have one_le_3 : (1 : ℝ) ≤ 3 := by norm_num
  have logb_rpow : (2 + Pival : ℝ) = 3 ^ Real.logb 3 (2 + Pival) :=
    (Real.rpow_logb pos_3 (by norm_num) pos_P).symm

  have key_ineq : B * Real.logb 3 (2 + Pival) ≤ (s : ℝ) - (jStar : ℝ) := by
    have h1 : B * Real.logb 3 (2 + Pival) ≤ (⌈B * Real.logb 3 (2 + Pival)⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈B * Real.logb 3 (2 + Pival)⌉ : ℝ) ≤ (s : ℝ) - (jStar : ℝ) := by
      norm_cast
      omega
    exact le_trans h1 h2

  have exp_ineq : -(ρ * ((s : ℝ) - (jStar : ℝ))) ≤ -(ρ * B * Real.logb 3 (2 + Pival)) := by
    nlinarith only [key_ineq, hρ]

  have eq_rearrange : (-(ρ * B * Real.logb 3 (2 + Pival)) : ℝ) = -(ρ * B) * Real.logb 3 (2 + Pival) := by
    ring

  calc (3 : ℝ) ^ (-(ρ * ((s : ℝ) - (jStar : ℝ))))
      ≤ (3 : ℝ) ^ (-(ρ * B * Real.logb 3 (2 + Pival))) :=
        Real.rpow_le_rpow_of_exponent_le one_le_3 exp_ineq
    _ = ((3 : ℝ) ^ Real.logb 3 (2 + Pival)) ^ (-(ρ * B)) := by
        rw [eq_rearrange, ← Real.rpow_mul pos_3.le]
        congr 1
        ring
    _ = (2 + Pival : ℝ) ^ (-(ρ * B)) := by rw [← logb_rpow]

/-- **S2**. Since `2 + Pival ≥ 3` and the exponent `1 + 2 Cglob` does not depend
on `B`, choosing `Bresp` after `σ` makes `C (2+Pival)^{1 + 2 Cglob - ρ B} ≤ τ` for every `B ≥
Bresp`. -/
theorem exists_Bresp_of_decay (C Cglob ρ τ : ℝ) (hC : 0 < C) (hCglob : 0 < Cglob) (hρ : 0 < ρ)
    (hτ : 0 < τ) :
    ∃ Bresp : ℝ, 1 ≤ Bresp ∧ ∀ B Pival : ℝ, Bresp ≤ B → 3 ≤ 2 + Pival →
      C * (2 + Pival) ^ (1 + 2 * Cglob - ρ * B) ≤ τ := by
  have _hCuse := hCglob
  set L : ℝ := Real.logb 3 (τ / C)
  refine ⟨max (1:ℝ) ((1 + 2 * Cglob - min 0 L) / ρ), le_max_left _ _, ?_⟩
  intro B Pival hB hPival
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hB2 : (1 + 2 * Cglob - min 0 L) / ρ ≤ B := le_trans (le_max_right _ _) hB
  have hdivmul :
      ρ * ((1 + 2 * Cglob - min 0 L) / ρ) = 1 + 2 * Cglob - min 0 L := by
    field_simp
  have hstep : 1 + 2 * Cglob - min 0 L ≤ ρ * B := by
    have h := mul_le_mul_of_nonneg_left hB2 (le_of_lt hρ)
    rw [hdivmul] at h
    exact h
  have he_le_min : 1 + 2 * Cglob - ρ * B ≤ min 0 L := by linarith only [hstep]
  have he_le0 : 1 + 2 * Cglob - ρ * B ≤ 0 := le_trans he_le_min (min_le_left _ _)
  have he_leL : 1 + 2 * Cglob - ρ * B ≤ L := le_trans he_le_min (min_le_right _ _)
  set e : ℝ := 1 + 2 * Cglob - ρ * B
  have hX3 : (3:ℝ) ≤ 2 + Pival := hPival
  have hkey : (2 + Pival) ^ e ≤ (3:ℝ) ^ e := by
    have hxdiv1 : (1:ℝ) ≤ (2 + Pival) / 3 := by
      have h1 : (2 + Pival) / 3 - 1 = (2 + Pival - 3) / 3 := by ring
      have h2 : (0:ℝ) ≤ (2 + Pival - 3) / 3 := div_nonneg (by linarith only [hPival]) (by norm_num)
      linarith only [h1, h2]
    have hxdivnn : (0:ℝ) ≤ (2 + Pival) / 3 := by linarith only [hxdiv1]
    have hle1 : ((2 + Pival) / 3) ^ e ≤ 1 := by
      rcases hxdiv1.lt_or_eq with hlt2 | heq2
      · have h := (Real.rpow_le_rpow_left_iff hlt2).mpr he_le0
        rwa [Real.rpow_zero] at h
      · rw [← heq2]
        exact le_of_eq (Real.one_rpow _)
    have hmuleq : (3 * ((2 + Pival) / 3) : ℝ) ^ e = (3:ℝ) ^ e * ((2 + Pival) / 3) ^ e :=
      Real.mul_rpow (by norm_num) hxdivnn
    have h3xeq : (3:ℝ) * ((2 + Pival) / 3) = 2 + Pival := by field_simp
    rw [h3xeq] at hmuleq
    have h3epos : (0:ℝ) < (3:ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
    calc (2 + Pival) ^ e = (3:ℝ) ^ e * ((2 + Pival) / 3) ^ e := hmuleq
      _ ≤ (3:ℝ) ^ e * 1 := mul_le_mul_of_nonneg_left hle1 (le_of_lt h3epos)
      _ = (3:ℝ) ^ e := by ring
  have h3eL : (3:ℝ) ^ e ≤ (3:ℝ) ^ L := by
    rcases he_leL.eq_or_lt with heq3 | hlt3
    · exact le_of_eq (by rw [heq3])
    · exact le_of_lt ((Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 3)).mpr hlt3)
  have hτCpos : (0:ℝ) < τ / C := div_pos hτ hC
  have h3L : (3:ℝ) ^ L = τ / C :=
    Real.rpow_logb (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1) hτCpos
  have hfinal : (2 + Pival) ^ e ≤ τ / C := by
    calc (2 + Pival) ^ e ≤ (3:ℝ) ^ e := hkey
      _ ≤ (3:ℝ) ^ L := h3eL
      _ = τ / C := h3L
  have hCne : C ≠ 0 := ne_of_gt hC
  have hCdiv : C * (τ / C) = τ := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hfinal (le_of_lt hC)
  rw [hCdiv] at hmul
  exact hmul

end HCPolySupport.HighContrast.Multiscale
end
