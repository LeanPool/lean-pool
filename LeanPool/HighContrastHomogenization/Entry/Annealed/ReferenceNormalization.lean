/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.InverseJensen
public import LeanPool.HighContrastHomogenization.Entry.Analysis.ReferenceComparison
public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapSupport
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Source.AdaptedBound
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# High-contrast homogenization: Entry.Annealed.ReferenceNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed reference normalization

Under the standing stationary dagger law this module proves the annealed
reference order, the two-grid reference normalization of `adaptedMean`, and the
initialization sandwich on the source window. The reference order comes from the
dagger at one sample and a sufficiently large standard cell through the two-sign
characterization, so no standing-law conclusion needs a separate reference-order
premise, and the normalization constants depend only on the dimension and the
coarse exponent. These results serve `p.global.selection`,
`e.two.grid.source.normalization` and `p.initial.fixed.grid.scale`.

The initialization conclusions retain the window restriction `j ≤ 2 * jStar`;
the unrestricted range would require repeating the source construction at the
larger window.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean annealedBlock
  aspectRatio blockMatEntry_blockScale blockScale coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Reference order from the dagger alone (`p.global.selection`).
The probability measure supplies a sample in the coarse-bound event. -/
theorem refBlock_reference_order {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {γ : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : CoarseEllipticityDagger P γ E Ψ K S) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
        toFullBlockMat (blockSwap d))) E := by
  obtain ⟨a, ha⟩ := hdag.coarse_bound.exists
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (S a) (by norm_num : (1 : ℝ) < 3)
  have hbound := ha (n : ℤ) (by simpa using hn.le) (n : ℤ) le_rfl 0 (by
    change (fun i => (3 : ℝ) ^ (n : ℤ) * ((0 : Fin d → ℤ) i : ℝ)) ∈ _
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero]
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    have hpow : (0 : ℝ) < 3 ^ (n : ℤ) := by positivity
    constructor <;> linarith only [hpow])
  have hscale : blockScale 1 E = E := by cases E; simp [blockScale]
  simp only [sub_self, mul_zero, Real.rpow_zero, hscale] at hbound
  let U := HighContrast.adaptedCellTranslate (1 : Mat d) (n : ℤ) 0
  have hs : IsSymmetricBlockMat (coarseBlock U a) :=
    isSymmetricBlockMat_coarseBlockMatrix U (⇑a.1)
  have hp := posDef_toFullBlockMat hs
    (blockPosDef_coarseBlock_adapted (1 : Mat d) isUnit_one (n : ℤ) 0 a)
  have hpath := Analysis.blockMatLoewnerLE_swapConj_coarseBlock
    (1 : Mat d) isUnit_one (n : ℤ) 0 a
  have hsigns := (Analysis.blockMatLoewnerLE_swapConj_inv_iff hs hp).mp hpath
  have hUE : BlockMatLoewnerLE (coarseBlock U a) E := by
    simpa only [U, adaptedCellTranslate_one_zero] using hbound
  exact (Analysis.blockMatLoewnerLE_swapConj_inv_iff hdag.refBlock_isSymm
    (posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef)).mpr
    ⟨hsigns.1.trans hUE, hsigns.2.trans hUE⟩

/-- Standing-dagger corollary of the deterministic reference comparison. -/
theorem refBlock_le_six_aspectRatio_smul_swapConj {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {γ : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : CoarseEllipticityDagger P γ E Ψ K S) :
    BlockMatLoewnerLE E
      (blockScale (6 * aspectRatio E)
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockSwap d)))) :=
  HCPolySupport.HighContrast.Analysis.refBlock_le_six_aspectRatio_smul_swapConj
    hdag.refBlock_isSymm hdag.refBlock_posDef (refBlock_reference_order hdag)

/-- Standing-dagger corollary of the deterministic reference comparison. -/
theorem aspectRatio_pos_and_three_le {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {γ : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : CoarseEllipticityDagger P γ E Ψ K S) :
    0 < aspectRatio E ∧ 3 ≤ 2 + aspectRatio E :=
  HCPolySupport.HighContrast.Analysis.aspectRatio_pos_and_three_le hdag.refBlock_isSymm
    hdag.refBlock_posDef (refBlock_reference_order hdag)

/-- The envelope has expectation at most two on a probability space. -/
theorem source_envelope_integral_le_two (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (X : CoeffSpace d → ℝ) (hX0 : ∀ a, 0 ≤ X a)
    (hlp : MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P)
    (hnorm : eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2) :
    ∫ a, X a ∂P ≤ 2 := by
  have _hd := hd
  have hQ : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (bigQ d γ : ℝ) := by
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (HCPolySupport.HighContrast.Multiscale.bigQ_two_le d γ hγ).trans' (by norm_num)
  have hmono : eLpNorm X (ENNReal.ofReal (1 : ℝ)) P ≤
      eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P :=
    eLpNorm_le_eLpNorm_of_exponent_le hQ
  have hle : (eLpNorm X (ENNReal.ofReal (1 : ℝ)) P).toReal ≤ 2 := by
    have htop : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact (ENNReal.toReal_mono htop (hmono.trans hnorm)).trans_eq
      (ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2))
  have heq : (eLpNorm X (ENNReal.ofReal (1 : ℝ)) P).toReal = ∫ a, X a ∂P := by
    have hnonneg : 0 ≤ᵐ[P] X := ae_of_all P hX0
    simpa using
      (HCPolySupport.HighContrast.Analysis.scalar_eLpNorm_toReal_eq_root
        (μ := P) (N := (1 : ℝ)) (by norm_num) hnonneg
        (hlp.mono_exponent hQ))
  rwa [heq] at hle

private theorem hasIntegrableCoarseBlock_one (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (j : ℤ) :
    HasIntegrableCoarseBlock P (HighContrast.adaptedCell (1 : Mat d) j) := by
  let : NeZero d := ⟨by omega⟩
  have hzero : HighContrast.adaptedCellTranslate (1 : Mat d) j 0 =
      HighContrast.adaptedCell (1 : Mat d) j := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨x, hx, by ext i; simp⟩
  rw [← hzero]
  simpa [Geometry.explicitRoundedGrid_one (d := d) jStar] using
    hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) j 0

private theorem adaptedMean_swapConj_le_one (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (j : ℤ) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (adaptedMean P (1 : Mat d) j))⁻¹ *
          toFullBlockMat (blockSwap d)))
      (adaptedMean P (1 : Mat d) j) := by
  let : NeZero d := ⟨by omega⟩
  exact HCPolySupport.HighContrast.Analysis.adaptedMean_swapConj_le_of_integrable
    (P := P) (q := (1 : Mat d)) (isUnit_one) j
    (hasIntegrableCoarseBlock_one d hd P γ E Ψ K S hstat hdag jStar hjStar j)

private theorem full_scale (c : ℝ) (A : BlockMat d) :
    toFullBlockMat (blockScale c A) = c • toFullBlockMat A := by
  ext (i | i) (j | j) <;> rfl

private theorem scale_one (A : BlockMat d) : blockScale 1 A = A := by
  cases A
  simp [blockScale]

private theorem scale_scale (c b : ℝ) (A : BlockMat d) :
    blockScale c (blockScale b A) = blockScale (c * b) A := by
  cases A
  simp [blockScale, smul_smul]

private theorem scale_mono {A B : BlockMat d} (h : BlockMatLoewnerLE A B)
    {c : ℝ} (hc : 0 ≤ c) : BlockMatLoewnerLE (blockScale c A) (blockScale c B) := by
  intro x
  rw [Source.quadratic_blockScale, Source.quadratic_blockScale]
  exact mul_le_mul_of_nonneg_left (h x) hc

private theorem matrix_congruence_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A ≤ B) (T : Matrix ι ι ℝ) : Tᴴ * A * T ≤ Tᴴ * B * T := by
  apply Matrix.le_iff.mpr
  simpa only [mul_sub, sub_mul] using (Matrix.le_iff.mp h).conjTranspose_mul_mul_same T

private theorem matrix_inv_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (hle : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  apply Matrix.le_iff.mpr
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.inv.isHermitian.sub hB.inv.isHermitian) ?_
  intro x
  obtain ⟨y, hy⟩ := (Analysis.isGreatest_two_inner_sub_quadratic hB x).1
  have hquad := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg y
  have hvar := Analysis.two_inner_sub_quadratic_le hA x y
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hquad ⊢
  rw [hy]
  linarith only [hquad, hvar]

private theorem lower_of_upper {A E : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hE : (toFullBlockMat E).PosDef)
    {c : ℝ} (hc : 0 < c) (hu : BlockMatLoewnerLE A (blockScale c E))
    (ha : BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d))) A) :
    BlockMatLoewnerLE
      (blockScale c⁻¹ (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)))) A := by
  have hscaled : (toFullBlockMat (blockScale c E)).PosDef := by
    rw [full_scale]
    exact hE.smul hc
  have hi := matrix_inv_antitone hA hscaled
    ((fullBlock_le_iff hA.isHermitian hscaled.isHermitian).mpr hu)
  have hR := (Analysis.toFullBlockMat_isHermitian_iff _).mpr
    (Analysis.isSymmetricBlockMat_blockSwap d)
  have hsi : (c • toFullBlockMat E)⁻¹ = c⁻¹ • (toFullBlockMat E)⁻¹ := by
    let : Invertible c := invertibleOfNonzero hc.ne'
    simpa only [invOf_eq_inv] using Matrix.inv_smul (A := toFullBlockMat E) c ((Matrix.isUnit_iff_isUnit_det _).mp hE.isUnit)
  have hh := matrix_congruence_mono hi (toFullBlockMat (blockSwap d))
  have hleft : (toFullBlockMat (blockScale c⁻¹ (ofFullBlockMat
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
        toFullBlockMat (blockSwap d))))).PosDef := by
    rw [full_scale]
    exact (Analysis.swapConj_posDef hE).smul (inv_pos.mpr hc)
  apply BlockMatLoewnerLE.trans _ ha
  apply (fullBlock_le_iff hleft.isHermitian (Analysis.swapConj_posDef hA).isHermitian).mp
  simpa only [hR.eq, full_scale, toFullBlockMat_ofFullBlockMat, hsi,
    Matrix.mul_smul, Matrix.smul_mul] using hh

private theorem annealed_le_scale_integral {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} {X : CoeffSpace d → ℝ} {E : BlockMat d} (c : ℝ)
    (hU : HasIntegrableCoarseBlock P U) (hX : Integrable X P)
    (hb : ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock U a) (blockScale (c * X a) E)) :
    BlockMatLoewnerLE (annealedBlock P U) (blockScale (c * ∫ a, X a ∂P) E) := by
  have hi (α β : BlockCoord d) : Integrable
      (fun a => blockMatEntry (blockScale (c * X a) E) α β) P := by
    simpa only [blockMatEntry_blockScale] using (hX.const_mul c).mul_const (blockMatEntry E α β)
  have h := Analysis.blockMatLoewnerLE_integral hU hi hb
  have he : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (blockScale (c * X a) E) α β ∂P) =
      blockScale (c * ∫ a, X a ∂P) E := by
    rw [← ofFullBlockMat_toFullBlockMat (blockScale (c * ∫ a, X a ∂P) E)]
    congr 1
    ext α β
    simp only [Matrix.of_apply, toFullBlockMat_eq_blockMatEntry,
      blockMatEntry_blockScale, integral_mul_const, integral_const_mul]
  rw [he] at h
  simpa only [Matrix.of_apply, fullBlock_integral_coarseBlock,
    ofFullBlockMat_toFullBlockMat] using! h

/-- The two-grid annealed reference normalization, near `e.two.grid.source.normalization`.
Both constants depend only on dimension and the coarse exponent. -/
theorem adaptedMean_refBlock_normalization (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ s : ℤ, (jStar : ℤ) ≤ s →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) s ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)
                  (blockScale (C * Real.sqrt (‖m‖ * ‖m⁻¹‖)) E) ∧
                BlockMatLoewnerLE E
                  (blockScale (C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖))
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, C, hCsrc, hC, hsource⟩ := Source.source_multiplier_and_adapted_bound d hd γ hγ
  refine ⟨Csrc, 12 * C, hCsrc, mul_pos (by norm_num) hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hjStar hthreshold m hm s hs hcell
  obtain ⟨ell, X, _, _, hform, _, hlp, _, _, hnorm, hbound⟩ :=
    hsource P E Ψ K S hstat hdag jStar hjStar hthreshold
  have hX0 : ∀ a, 0 ≤ X a := fun a => by rw [hform]; positivity
  have hXint := hlp.integrable (ENNReal.one_le_ofReal.mpr (by
    exact_mod_cast (Multiscale.bigQ_two_le d γ hγ).trans' (by norm_num)))
  have hEX := source_envelope_integral_le_two d hd γ hγ P X hX0 hlp hnorm
  have hecc := Source.one_le_source_eccentricity hm
  have hc : 0 < 2 * C * Real.sqrt (‖m‖ * ‖m⁻¹‖) :=
    mul_pos (mul_pos (by norm_num) hC) (lt_of_lt_of_le zero_lt_one hecc)
  have hexp : max ((jStar : ℝ) - (s : ℝ)) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr (by exact_mod_cast hs))
  have hint : HasIntegrableCoarseBlock P
      (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) s) := by
    simpa [adaptedCellTranslate] using hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag jStar hjStar m hm s 0
  have hupper : BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)
      (blockScale (2 * C * Real.sqrt (‖m‖ * ‖m⁻¹‖)) E) := by
    have hb := annealed_le_scale_integral (C * Real.sqrt (‖m‖ * ‖m⁻¹‖)) hint hXint
      (hbound.mono fun a ha => by
        have hh := ha.2 m hm s 0 (by simpa [adaptedCellTranslate] using hcell)
        simpa [adaptedCellTranslate, hexp] using hh)
    apply hb.trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    calc
      _ ≤ (C * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * 2 :=
        mul_le_mul_of_nonneg_left hEX (mul_nonneg hC.le (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hA := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm s
  have hE := posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hlower := lower_of_upper hA hE hc hupper
    (Analysis.adaptedMean_swapConj_le hd P γ E Ψ K S hstat hdag jStar hjStar m hm s)
  have hswap : BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
        toFullBlockMat (blockSwap d)))
      (blockScale (2 * C * Real.sqrt (‖m‖ * ‖m⁻¹‖))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)) := by
    simpa only [scale_scale, mul_inv_cancel₀ hc.ne', scale_one] using scale_mono hlower hc.le
  constructor
  · apply hupper.trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    exact mul_le_mul_of_nonneg_right (by linarith only [hC] : 2 * C ≤ 12 * C)
      (Real.sqrt_nonneg _)
  · have hPi := one_le_aspectRatio_of_coarseEllipticityDagger hdag
    have hcomp := (refBlock_le_six_aspectRatio_smul_swapConj hdag).trans
      (scale_mono hswap (mul_nonneg (by norm_num) (le_trans zero_le_one hPi)))
    simpa only [scale_scale, show 6 * aspectRatio E *
        (2 * C * Real.sqrt (‖m‖ * ‖m⁻¹‖)) =
        12 * C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) by ring] using hcomp

/-- The exact initialization sandwich on the source window,
`p.initial.fixed.grid.scale`. The printed uniform range is restricted
to `j ≤ 2 * jStar`; a larger window requires repeating the multiplier construction. -/
theorem initial_source_bounds (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j → j ≤ 2 * (jStar : ℤ) →
            BlockMatLoewnerLE
                (blockScale (1 / 2)
                  (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                    toFullBlockMat (blockSwap d))))
                (adaptedMean P (1 : Mat d) j) ∧
              BlockMatLoewnerLE (adaptedMean P (1 : Mat d) j) (blockScale 2 E) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, _, hCsrc, _, hsource⟩ := Source.source_multiplier_and_adapted_bound d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hjStar hthreshold j hj hjwindow
  obtain ⟨ell, X, _, _, hform, _, hlp, _, _, hnorm, hbound⟩ :=
    hsource P E Ψ K S hstat hdag jStar hjStar hthreshold
  have hX0 : ∀ a, 0 ≤ X a := fun a => by rw [hform]; positivity
  have hXint := hlp.integrable (ENNReal.one_le_ofReal.mpr (by
    exact_mod_cast (Multiscale.bigQ_two_le d γ hγ).trans' (by norm_num)))
  have hEX := source_envelope_integral_le_two d hd γ hγ P X hX0 hlp hnorm
  have hexp : max ((jStar : ℝ) - (j : ℝ)) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr (by exact_mod_cast hj))
  have hupper : BlockMatLoewnerLE (adaptedMean P (1 : Mat d) j) (blockScale 2 E) := by
    have hb := annealed_le_scale_integral 1
      (hasIntegrableCoarseBlock_one d hd P γ E Ψ K S hstat hdag jStar hjStar j) hXint
      (hbound.mono fun a ha => by
        have hh := ha.1 j 0 (by
          rw [← adaptedCell_one]
          exact adaptedCell_one_subset_centeredCube j hjwindow)
        simpa only [adaptedCell_one, hexp, mul_zero, Real.rpow_zero, mul_one, one_mul] using hh)
    simp only [one_mul] at hb
    exact hb.trans (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef hEX)
  have hA : (toFullBlockMat (adaptedMean P (1 : Mat d) j)).PosDef := by
    simpa only [explicitRoundedGrid_one] using adaptedMean_posDef d hd P γ E Ψ K S
      hstat hdag jStar hjStar (1 : Mat d) (one_posDef d) j
  refine ⟨?_, hupper⟩
  simpa only [one_div] using lower_of_upper hA
    (posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef)
    (by norm_num : (0 : ℝ) < 2) hupper
    (adaptedMean_swapConj_le_one d hd P γ E Ψ K S hstat hdag jStar hjStar j)

end
end HCPolySupport.HighContrast.Annealed
