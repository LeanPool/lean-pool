/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Transport.WindowBelowStart

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The below-start quantity

The last clause of `e.source.adapted.bound` that a bounded-window estimate
reads is the below-start source maximum `\mathsf S_{t,<j_*}(F)`: the supremum,
over the scales strictly below the alignment and over an arbitrary family of
centers at each such scale, of the `F`-normalized excess of the adapted
response, weighted by `3^{-\rho(t-k)}`.  It obeys a pathwise bound, and the
three consequences drawn from that bound are its first moment, its `L^Q` norm
and its source-tail form.

Everything follows from one weighted cell bound and the fact that the multiplier
is common to every cell of every family.  On a cell of scale `k < j_*` the burn
discount is `3^{g(j_*-k)}`, and the weight `3^{-\rho(t-k)}` absorbs it
completely when `\rho > g`:

`3^{-\rho(t-k)}3^{g(j_*-k)} = 3^{-\rho(t-j_*)}3^{-(\rho-g)(j_*-k)}
  \leq 3^{-\rho(t-j_*)}`,

so no multiplicity in the scale, and none in the centers either, since the same
`Y_P` serves them all on one event of full measure.  The excess is below the
scalar size, a change of reference block costs `Λ(F;𝐄)`, and the cell bound of
the window supplies the rest.  The three consequences are then the expectation,
the `L^Q` norm and the decomposition `Y_P = 1 + (Y_P - 1)` applied to a single
pathwise majorant proportional to `Y_P`.

The countability of the center families, which the printed statement assumes, is
not used: the bound holds term by term, so the supremum inherits it whatever the
index set.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The two elementary steps -/

/-- The size of the positive part of the normalized excess is below the scalar
size of the same pair: both are read off one relative size, and the excess
subtracts one from it before truncating at zero. -/
theorem blockExcess_le_blockSize {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) : blockExcess H F ≤ blockSize H F := by
  rw [blockExcess_eq hH hF hFpd hHps, blockSize_eq_relSize hH hF hFpd hHps]
  exact max_le (by linarith only [relSize_nonneg (toFullBlockMat H) (toFullBlockMat F)])
    (relSize_nonneg _ _)

/-- **The weight absorbs the burn discount.**  Below the alignment scale the
discount is `3^{g(j_*-k)}`, and the weight `3^{-\rho(t-k)}` beats it by
`3^{-(\rho-g)(j_*-k)} \leq 1` exactly because `\rho > g`. -/
theorem rpow_mul_burnDiscount_le {g rho : ℝ} (hrho : g < rho) {jStar k : ℤ}
    (hk : k < jStar) (t : ℤ) :
    (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) * burnDiscount g jStar k ≤
      (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))) := by
  have hkk : (k : ℝ) < (jStar : ℝ) := by exact_mod_cast hk
  rw [burnDiscount, max_eq_left (by linarith only [hkk] : (0 : ℝ) ≤ (jStar : ℝ) - (k : ℝ)),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr ?_
  have hprod : 0 ≤ (rho - g) * ((jStar : ℝ) - (k : ℝ)) :=
    mul_nonneg (by linarith only [hrho]) (by linarith only [hkk])
  linarith only [hprod]

/-! ## The pathwise bound -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The below-start quantity, pathwise**: one event of full measure carries
the bound for every scale below the alignment and every center of every
family. -/
theorem ae_belowStartSup_le (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {rho : ℝ}
    (hrho : g < rho) (t : ℤ) {Z : ℤ → Set (Vec d)}
    (hZ : ∀ k : ℤ, k < jStar → ∀ z ∈ Z k,
      adaptedCellTranslate (roundedGrid jStar nu) k z ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, belowStartSup rho (roundedGrid jStar nu) jStar t Z F a ≤
      ENNReal.ofReal (boundaryConst Cd g nu * Y a * blockSize E F *
        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) := by
  have hlam : 0 ≤ blockSize E F := PortableHistory.blockSize_nonneg hE hF hFpd
  have hB : 0 ≤ boundaryConst Cd g nu := zero_le_boundaryConst hCd hg nu
  filter_upwards [hY.adapted_primal] with a ha
  have hY1 : (0 : ℝ) ≤ Y a := le_trans zero_le_one (hY.one_le a)
  have hcoef : 0 ≤ boundaryConst Cd g nu * Y a * blockSize E F :=
    mul_nonneg (mul_nonneg hB hY1) hlam
  simp only [belowStartSup]
  refine iSup_le fun k => iSup_le fun hk => iSup_le fun z => iSup_le fun hz => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hAsym : IsSymmetricBlockMat
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) k z) a) :=
    isSymmetricBlockMat_coarseBlock _ a
  have hApsd : (toFullBlockMat
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) k z) a)).PosSemidef :=
    (posDef_toFullBlockMat hAsym (blockPosDef_coarseBlock_adaptedCellTranslate
      (Recurrence.posDef_of_isRoundedGrid hq) k z a)).posSemidef
  have hcell : blockSize (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) k z) a) E ≤
      boundaryConst Cd g nu * burnDiscount g jStar k * Y a := by
    refine blockSize_le_of_blockMatLoewnerLE_blockScale hAsym hApsd hE hEpd
      (mul_nonneg (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar k) hY1) ?_
    have h := ha nu hnu k z (hZ k hk z hz)
    rwa [show boundaryConst Cd g nu * Y a * burnDiscount g jStar k =
      boundaryConst Cd g nu * burnDiscount g jStar k * Y a from mul_right_comm _ _ _] at h
  have hexc : blockExcess (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) k z) a) F ≤
      blockSize E F * (boundaryConst Cd g nu * burnDiscount g jStar k * Y a) :=
    (blockExcess_le_blockSize hAsym hApsd hF hFpd).trans
      ((PortableHistory.blockSize_le_mul_blockSize hAsym hE hEpd hF hFpd hlam
        (PortableHistory.blockSize_sandwich hE hF hFpd).1).trans
        (mul_le_mul_of_nonneg_left hcell hlam))
  have hw : (0 : ℝ) < (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
        blockExcess (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) k z) a) F
      ≤ (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
          (blockSize E F * (boundaryConst Cd g nu * burnDiscount g jStar k * Y a)) :=
        mul_le_mul_of_nonneg_left hexc hw.le
    _ = boundaryConst Cd g nu * Y a * blockSize E F *
          ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) * burnDiscount g jStar k) := by ring
    _ ≤ boundaryConst Cd g nu * Y a * blockSize E F *
          (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))) :=
        mul_le_mul_of_nonneg_left (rpow_mul_burnDiscount_le hrho hk t) hcoef

/-! ## The three consequences -/

section Consequences

variable (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
  (hEpd : Book.Ch02.BlockPosDef E)
  (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
  (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
  (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {rho : ℝ}
  (hrho : g < rho) (t : ℤ) {Z : ℤ → Set (Vec d)}
  (hZ : ∀ k : ℤ, k < jStar → ∀ z ∈ Z k,
    adaptedCellTranslate (roundedGrid jStar nu) k z ⊆ centeredCube d M)

include hCd hg hE hEpd hY hnu hq hF hFpd hrho hZ in
/-- The pathwise majorant in the form the three consequences use: a nonnegative
constant times the multiplier. -/
private theorem ae_belowStartSup_le_mul :
    ∀ᵐ a ∂P, belowStartSup rho (roundedGrid jStar nu) jStar t Z F a ≤
      ENNReal.ofReal ((boundaryConst Cd g nu * blockSize E F *
        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) * Y a) := by
  filter_upwards [ae_belowStartSup_le hCd hg hE hEpd hY hnu hq hF hFpd hrho t hZ]
    with a ha
  refine ha.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
  ring

include hCd hg hE hEpd hY hnu hq hF hFpd hrho hZ in
/-- **The `L^Q` norm of the below-start source maximum.**  The supremum is assumed
a.e. strongly measurable, since it runs over an arbitrary family of centers. -/
theorem eLpNorm_belowStartSup_le (Q : ℝ)
    (hS : AEStronglyMeasurable (belowStartSup rho (roundedGrid jStar nu) jStar t Z F) P) :
    eLpNorm (belowStartSup rho (roundedGrid jStar nu) jStar t Z F)
        (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (boundaryConst Cd g nu * blockSize E F *
        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) * lqNorm P Q Y := by
  set c : ℝ := boundaryConst Cd g nu * blockSize E F *
    (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))) with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (mul_nonneg (zero_le_boundaryConst hCd hg nu)
      (PortableHistory.blockSize_nonneg hE hF hFpd)) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hmono : eLpNorm (belowStartSup rho (roundedGrid jStar nu) jStar t Z F)
      (ENNReal.ofReal Q) P ≤ eLpNorm (c • Y) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_enorm_ae hS ?_
    filter_upwards [ae_belowStartSup_le_mul hCd hg hE hEpd hY hnu hq hF hFpd hrho t hZ]
      with a ha
    have hnn : (0 : ℝ) ≤ c * Y a := mul_nonneg hc0 (le_trans zero_le_one (hY.one_le a))
    change belowStartSup rho (roundedGrid jStar nu) jStar t Z F a ≤ ‖c * Y a‖ₑ
    rwa [Real.enorm_eq_ofReal hnn]
  rwa [eLpNorm_const_smul, Real.enorm_eq_ofReal hc0] at hmono

include hCd hg hE hEpd hY hnu hq hF hFpd hrho hZ in
/-- **The source-tail form of the below-start bound.** -/
theorem isShiftedBigOWithTop_belowStartSup :
    IsShiftedBigOWithTop P Ψ (belowStartSup rho (roundedGrid jStar nu) jStar t Z F)
      (boundaryConst Cd g nu * blockSize E F *
        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))))
      (boundaryConst Cd g nu * blockSize E F * sourceRemainderScale d jStar K *
        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) := by
  set c : ℝ := boundaryConst Cd g nu * blockSize E F *
    (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))) with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (mul_nonneg (zero_le_boundaryConst hCd hg nu)
      (PortableHistory.blockSize_nonneg hE hF hFpd)) (Real.rpow_pos_of_pos (by norm_num) _).le
  refine ⟨fun a => c * (Y a - 1),
    fun a => mul_nonneg hc0 (by linarith only [hY.one_le a]), ?_, ?_⟩
  · filter_upwards [ae_belowStartSup_le_mul hCd hg hE hEpd hY hnu hq hF hFpd hrho t hZ]
      with a ha
    exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring)))
  · have h := hY.orlicz.const_mul hc0
    rwa [hcdef, mul_right_comm (boundaryConst Cd g nu * blockSize E F)] at h

end Consequences

end

end Transport
end HighContrast
end HCPolySupport
