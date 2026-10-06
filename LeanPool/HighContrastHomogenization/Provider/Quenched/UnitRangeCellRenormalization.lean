/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedBadEvent
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCentring
public import LeanPool.HighContrastHomogenization.Annealed.Integrability
public import LeanPool.HighContrastHomogenization.Annealed.Measurability
public import LeanPool.HighContrastHomogenization.Provider.Entry.StandardCellMean

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCellRenormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The single-cell renormalization estimate

The renormalization of ellipticity cites, for a single cell of a single scale,
one estimate: that the coarse block of that cell exceeds an additive multiple of
the annealed block at the inner generation only with the finite-range Gaussian
probability.  This file proves that estimate from the frozen carriers alone —
stationarity, unit range of dependence, and the coarse-ellipticity datum — and
records it in the form the bad-generation union bounds consume.

The argument is the printed one.  The coarse blocks of the inner cells that
subdivide the parent are read in the coordinates normalized by the reference
block, and cut off at a level the coarse-ellipticity datum makes inactive on the
event that the source has burnt in; the cut-off readouts are bounded, local to
their own cells and centred at their own means, so the concentration estimate of
unit range applies to their average entrywise, and the reassembly turns the
entrywise deviation into a Loewner deviation against the identity.
Un-normalizing returns a deviation against the reference block, and the
comparison of the reference block with the annealed one turns that into the
printed additive multiple.  Subadditivity puts the parent below the average, and
the centring identification puts the block of means below the annealed block, so
the two ends of the chain meet.

Two bookkeeping points of the printed proof are visible here.  The inner cells of
a parent centred in `□_m` are centred in `□_{m+1}`, so the coarse-ellipticity
datum is read one generation higher and the cutoff level carries the factor
`3^g`.  And the reassembly costs the prefactor `(2d)²`, which is absorbed by
evaluating the concentration estimate at the shifted parameter `T + renormShift d`
rather than at `T`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The quadratic form of a difference and of an average -/

/-- The quadratic form of a difference of doubled blocks. -/
theorem blockVecDot_blockMatVecMul_blockSub (A B : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockSub A B) X)
      = blockVecDot X (blockMatVecMul A X) - blockVecDot X (blockMatVecMul B X) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_blockSub, sub_mul, mul_sub,
    Finset.sum_sub_distrib]

private theorem sum_sum_sum_comm {ι : Type*} (Z : Finset ι)
    (F : ι → BlockCoord d → BlockCoord d → ℝ) :
    ∑ α : BlockCoord d, ∑ β : BlockCoord d, ∑ t ∈ Z, F t α β
      = ∑ t ∈ Z, ∑ α : BlockCoord d, ∑ β : BlockCoord d, F t α β := by
  calc ∑ α : BlockCoord d, ∑ β : BlockCoord d, ∑ t ∈ Z, F t α β
      = ∑ α : BlockCoord d, ∑ t ∈ Z, ∑ β : BlockCoord d, F t α β :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t ∈ Z, ∑ α : BlockCoord d, ∑ β : BlockCoord d, F t α β := Finset.sum_comm

/-- The quadratic form of an average of doubled blocks is the average of the
quadratic forms. -/
theorem blockVecDot_blockMatVecMul_avgBlockOf {ι : Type*} (Z : Finset ι)
    (M : ι → BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (avgBlockOf Z M) X)
      = (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, blockVecDot X (blockMatVecMul (M t) X) := by
  classical
  have hL : blockVecDot X (blockMatVecMul (avgBlockOf Z M) X)
      = ∑ α : BlockCoord d, ∑ β : BlockCoord d, ∑ t ∈ Z,
          (Z.card : ℝ)⁻¹ *
            (toFullBlockVec X α * (blockMatEntry (M t) α β * toFullBlockVec X β)) := by
    rw [blockVecDot_blockMatVecMul_eq_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [blockMatEntry_avgBlockOf, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hR : (Z.card : ℝ)⁻¹ * ∑ t ∈ Z, blockVecDot X (blockMatVecMul (M t) X)
      = ∑ t ∈ Z, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          (Z.card : ℝ)⁻¹ *
            (toFullBlockVec X α * (blockMatEntry (M t) α β * toFullBlockVec X β)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
  rw [hL, hR]
  exact sum_sum_sum_comm Z _

/-- An average of doubled blocks agreeing on the index set is unchanged. -/
theorem avgBlockOf_congr {ι : Type*} {Z : Finset ι} {M N : ι → BlockMat d}
    (h : ∀ t ∈ Z, M t = N t) : avgBlockOf Z M = avgBlockOf Z N := by
  refine toFullBlockMat_injective ?_
  rw [toFullBlockMat_avgBlockOf, toFullBlockMat_avgBlockOf]
  exact congrArg _ (Finset.sum_congr rfl fun t ht => by rw [h t ht])

/-- The average of symmetric doubled blocks is symmetric. -/
theorem isSymmetricBlockMat_avgBlockOf {ι : Type*} (Z : Finset ι) {M : ι → BlockMat d}
    (h : ∀ t, IsSymmetricBlockMat (M t)) : IsSymmetricBlockMat (avgBlockOf Z M) := by
  intro α β
  rw [blockMatEntry_avgBlockOf, blockMatEntry_avgBlockOf]
  exact congrArg _ (Finset.sum_congr rfl fun t _ => h t α β)

/-- An average of doubled blocks each below a fixed block is below that block. -/
theorem blockMatLoewnerLE_avgBlockOf_of_forall {ι : Type*} {Z : Finset ι} (hZ : Z.Nonempty)
    {M : ι → BlockMat d} {C : BlockMat d} (h : ∀ t ∈ Z, BlockMatLoewnerLE (M t) C) :
    BlockMatLoewnerLE (avgBlockOf Z M) C := by
  intro X
  rw [blockVecDot_blockMatVecMul_avgBlockOf]
  have hcard : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hZ
  have hsum : ∑ t ∈ Z, blockVecDot X (blockMatVecMul (M t) X) ≤
      ∑ _t ∈ Z, blockVecDot X (blockMatVecMul C X) :=
    Finset.sum_le_sum fun t ht => by
      have := h t ht X
      linarith only [this]
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hcard.le)
  rw [inv_mul_cancel_left₀ (ne_of_gt hcard)] at hmul
  linarith only [hmul]

/-! ## The single-cell estimate, for an abstract family of inner cells -/

/-- **The single-cell renormalization estimate.**  For a finite family of
scale-`l` standard cells whose centres lie in `□_{m+1}` and whose average
dominates the coarse block of the parent, the coarse block of the parent exceeds
the additive multiple `1 + C` of the annealed block at generation `l` — on the
event that the source has burnt in at `m` — with probability at most
`Ψ_fr(T)⁻¹`, as soon as `C` dominates the deviation the concentration estimate
produces at the shifted parameter `T + renormShift d`. -/
theorem measureReal_renormCell_le_of_family [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {Kg : ℝ} {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi Kg S)
    {l m k : ℤ} (hl : 0 ≤ l) (hlm : l ≤ m + 1)
    (hhalf : (Psi ((3 : ℝ) ^ l))⁻¹ ≤ 1 / 2)
    {Zi : Finset (Fin d → ℤ)} (hZi : Zi.Nonempty)
    (hZmem : ∀ u ∈ Zi, standardCellCenter l u ∈ centeredCube d (m + 1))
    (w : Fin d → ℤ)
    (hsubadd : ∀ a : CoeffSpace d,
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (avgBlockOf Zi fun u => coarseBlock (standardCell d l u) a))
    {T C : ℝ} (hT : 1 ≤ T)
    (hC : 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ))) * frThreshold d *
        (T + renormShift d) * (Real.sqrt (Zi.card : ℝ))⁻¹ * kappaRef E ≤ C) :
    P.real {a : CoeffSpace d | S a ≤ (3 : ℝ) ^ m ∧
        ¬ BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale (1 + C) (annealedBlock P (centeredCube d l)))}
      ≤ (frGauge d T)⁻¹ := by
  classical
  have hEsymm : IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast hd
  have hkappa1 : (1 : ℝ) ≤ kappaRef E :=
    Initialization.one_le_kappaRef hEsymm hEpd (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  have hintcube : HasIntegrableCoarseBlock P (centeredCube d l) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag l
  have href : BlockMatLoewnerLE E
      (blockScale (2 * kappaRef E) (annealedBlock P (centeredCube d l))) :=
    blockMatLoewnerLE_blockScale_annealedBlock_reference hdag l hintcube hhalf
  -- the cutoff level, read one generation above the parent
  set Bcut : ℝ := 4 * (d : ℝ) * (3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ))) with hBdef
  have hBpos : (0 : ℝ) < Bcut := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hBdef]
    nlinarith only [hdpos, h3]
  have hB0 : (0 : ℝ) ≤ Bcut := hBpos.le
  have h2B : (0 : ℝ) < 2 * Bcut := by linarith only [hBpos]
  -- the geometry of the inner cells
  have hcellDom : ∀ u : Fin d → ℤ, IsOpenBoundedConvexDomain (standardCell d l u) :=
    fun u => isOpenBoundedConvexDomain_openCubeSet (translateCube u (originCube d l))
  have hcellVol : ∀ u : Fin d → ℤ, 0 < (volume (standardCell d l u)).toReal := by
    intro u
    change 0 < (volume (openCubeSet (translateCube u (originCube d l)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  have hAsymm : ∀ (u : Fin d → ℤ) (a : CoeffSpace d),
      IsSymmetricBlockMat (coarseBlock (standardCell d l u) a) :=
    fun u a => isSymmetricBlockMat_coarseBlock _ a
  have hApd : ∀ (u : Fin d → ℤ) (a : CoeffSpace d),
      Book.Ch02.BlockPosDef (coarseBlock (standardCell d l u) a) :=
    fun u a => Sharp.blockPosDef_coarseBlock_of_volume_pos (hcellDom u) (hcellVol u) a
  have hNsymm : ∀ (u : Fin d → ℤ) (a : CoeffSpace d),
      IsSymmetricBlockMat (normalizedBlock (coarseBlock (standardCell d l u) a) E) :=
    fun u a => isSymmetricBlockMat_normalizedBlock (hAsymm u a)
  have hNpd : ∀ (u : Fin d → ℤ) (a : CoeffSpace d),
      Book.Ch02.BlockPosDef (normalizedBlock (coarseBlock (standardCell d l u) a) E) :=
    fun u a => blockPosDef_normalizedBlock (hAsymm u a) (hApd u a) hEsymm hEpd
  -- the cut-off normalized inner blocks
  set Ncut : (Fin d → ℤ) → CoeffSpace d → BlockMat d := fun u a =>
    blockCutoff Bcut (normalizedBlock (coarseBlock (standardCell d l u) a) E) with hNcutdef
  have habsN : ∀ (u : Fin d → ℤ) (a : CoeffSpace d) (α β : BlockCoord d),
      |blockMatEntry (Ncut u a) α β| ≤ Bcut := by
    intro u a α β
    simp only [hNcutdef]
    exact abs_blockMatEntry_blockCutoff_le hB0 _ α β
  have hlocN : ∀ (α β : BlockCoord d) (u : Fin d → ℤ),
      @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d l u)) _
        (fun a => blockMatEntry (Ncut u a) α β) := by
    intro α β u
    simp only [hNcutdef]
    exact measurable_blockMatEntry_blockCutoff_of_local Bcut
      (fun alpha beta =>
        measurable_blockMatEntry_normalizedBlock_coarseBlock_standardCell E l u alpha beta) α β
  have hmeasN : ∀ (α β : BlockCoord d) (u : Fin d → ℤ),
      Measurable fun a => blockMatEntry (Ncut u a) α β :=
    fun α β u => Recurrence.measurable_of_measurable_coeffSigma (hlocN α β u)
  have hintN : ∀ u : Fin d → ℤ, HasIntegrableBlock P fun a => Ncut u a := by
    intro u α β
    refine ⟨(hmeasN α β u).aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const Bcut).mono ?_
    filter_upwards with a
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB0]
    exact habsN u a α β
  have habsMean : ∀ (u : Fin d → ℤ) (α β : BlockCoord d),
      |blockMatEntry (meanBlock P fun b => Ncut u b) α β| ≤ Bcut := by
    intro u α β
    rw [blockMatEntry_meanBlock]
    have hbd : ∀ᵐ a ∂P, ‖blockMatEntry (Ncut u a) α β‖ ≤ Bcut := by
      filter_upwards with a
      rw [Real.norm_eq_abs]
      exact habsN u a α β
    have hb := norm_integral_le_of_norm_le_const (μ := P) hbd
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at hb
    exact hb
  -- the observable the concentration estimate is applied to
  set Xobs : BlockCoord d → BlockCoord d → (Fin d → ℤ) → CoeffSpace d → ℝ := fun α β u a =>
    (blockMatEntry (Ncut u a) α β - blockMatEntry (meanBlock P fun b => Ncut u b) α β) /
      (2 * Bcut) with hXdef
  have hXloc : ∀ (α β : BlockCoord d) (u : Fin d → ℤ),
      @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d l u)) _ (Xobs α β u) := by
    intro α β u
    let : MeasurableSpace (CoeffSpace d) := coeffSigma d (standardCell d l u)
    simp only [hXdef]
    exact ((hlocN α β u).sub measurable_const).div measurable_const
  have hXbd : ∀ (α β : BlockCoord d) (u : Fin d → ℤ), ∀ᵐ a ∂P, |Xobs α β u a| ≤ 1 := by
    intro α β u
    filter_upwards with a
    simp only [hXdef]
    rw [abs_div, abs_of_pos h2B, div_le_one h2B]
    have h1 := habsN u a α β
    have h2 := habsMean u α β
    refine le_trans (abs_sub _ _) ?_
    linarith only [h1, h2]
  have hXmean : ∀ (α β : BlockCoord d) (u : Fin d → ℤ), ∫ a, Xobs α β u a ∂P = 0 := by
    intro α β u
    simp only [hXdef]
    rw [integral_div, integral_sub (hintN u α β) (integrable_const _), integral_const,
      blockMatEntry_meanBlock]
    simp
  -- the block-valued observable
  set Hobs : CoeffSpace d → BlockMat d := fun a =>
    blockScale (2 * Bcut)⁻¹
      (blockSub (avgBlockOf Zi fun u => Ncut u a)
        (avgBlockOf Zi fun u => meanBlock P fun b => Ncut u b)) with hHdef
  have hHentry : ∀ (a : CoeffSpace d) (α β : BlockCoord d),
      blockMatEntry (Hobs a) α β = (Zi.card : ℝ)⁻¹ * ∑ u ∈ Zi, Xobs α β u a := by
    intro a α β
    simp only [hHdef, hXdef, blockMatEntry_blockScale, blockMatEntry_blockSub,
      blockMatEntry_avgBlockOf]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  have hFid : ∀ Y : BlockVec d,
      ∑ α : BlockCoord d, toFullBlockVec Y α * toFullBlockVec Y α ≤
        blockVecDot Y (blockMatVecMul (scaledBlockIdentity d 1) Y) := by
    intro Y
    rw [blockVecDot_scaledBlockIdentity, one_mul]
  have hT' : (1 : ℝ) ≤ T + renormShift d := by
    have hs := renormShift_nonneg d
    linarith only [hT, hs]
  have hconc := measureReal_not_blockMatLoewnerLE_average_le_frGauge hunit hl hXloc hXbd hXmean
    hZi hHentry hFid hT'
  -- the fluctuation scale and the deviation the estimate produces
  set eta : ℝ := frThreshold d * (T + renormShift d) * (Real.sqrt (Zi.card : ℝ))⁻¹ with hetadef
  have heta0 : (0 : ℝ) ≤ eta := by
    have h1 := (frThreshold_pos d).le
    have h2 : (0 : ℝ) ≤ T + renormShift d := le_trans zero_le_one hT'
    have h3 : (0 : ℝ) ≤ (Real.sqrt (Zi.card : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    rw [hetadef]
    positivity
  set kappa : ℝ := 2 * Bcut * (2 * (d : ℝ) * eta) with hkappadef
  have hkappa0 : (0 : ℝ) ≤ kappa := by
    rw [hkappadef]
    have h1 : (0 : ℝ) ≤ 2 * Bcut := h2B.le
    have h2 : (0 : ℝ) ≤ 2 * (d : ℝ) * eta := by positivity
    exact mul_nonneg h1 h2
  have hkeq : 2 * kappa * kappaRef E
      = 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ))) * frThreshold d *
        (T + renormShift d) * (Real.sqrt (Zi.card : ℝ))⁻¹ * kappaRef E := by
    rw [hkappadef, hBdef, hetadef]
    ring
  -- the centring block of every inner cell sits below the normalized annealed block
  have hmeanle : ∀ u : Fin d → ℤ, BlockMatLoewnerLE (meanBlock P fun b => Ncut u b)
      (normalizedBlock (annealedBlock P (centeredCube d l)) E) := by
    intro u
    have hcellint : HasIntegrableCoarseBlock P (standardCell d l u) :=
      Entry.hasIntegrableCoarseBlock_standardCell_of_stationary hstat hdag l u
    have hIB2 : HasIntegrableBlock P
        fun b => normalizedBlock (coarseBlock (standardCell d l u) b) E := by
      intro α β
      have hrw : (fun b => blockMatEntry
          (normalizedBlock (coarseBlock (standardCell d l u) b) E) α β)
          = fun b => ∑ delta : BlockCoord d, ∑ gamma : BlockCoord d,
              matSqrt (toFullBlockMat E)⁻¹ α gamma *
                (blockMatEntry (coarseBlock (standardCell d l u) b) gamma delta *
                  matSqrt (toFullBlockMat E)⁻¹ delta β) := by
        funext b
        exact blockMatEntry_normalizedBlock_eq_sum _ E α β
      rw [hrw]
      exact integrable_finsetSum _ fun delta _ => integrable_finsetSum _ fun gamma _ =>
        ((hcellint gamma delta).mul_const _).const_mul _
    have hstep := blockMatLoewnerLE_meanBlock (hintN u) hIB2
      (_root_.Filter.Eventually.of_forall fun b => by
        simp only [hNcutdef]
        exact blockMatLoewnerLE_blockCutoff (hNpd u b))
    rw [meanBlock_normalizedBlock E (hasIntegrableBlock_coarseBlock hcellint),
      ← annealedBlock_eq_meanBlock,
      annealedBlock_standardCell_eq_centeredCube hstat hl u
        (hasMeasurableCoarseBlock_centeredCube P l)] at hstep
    exact hstep
  have hMavg : BlockMatLoewnerLE (avgBlockOf Zi fun u => meanBlock P fun b => Ncut u b)
      (normalizedBlock (annealedBlock P (centeredCube d l)) E) :=
    blockMatLoewnerLE_avgBlockOf_of_forall hZi fun u _ => hmeanle u
  -- the measure bound
  refine le_trans ?_ (hconc.trans (prefactor_absorb d hT))
  simp only [Measure.real]
  refine ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae ?_)
  filter_upwards [hdag.coarse_bound] with a hcoarse hmem
  intro hgood
  refine hmem.2 ?_
  -- the cutoff is inactive on the burnt-in event
  have hsrc' : S a ≤ (3 : ℝ) ^ (m + 1) := by
    have h1 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (m + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 := hmem.1
    linarith only [h1, h2]
  have hcutoff : ∀ u ∈ Zi, Ncut u a
      = normalizedBlock (coarseBlock (standardCell d l u) a) E := by
    intro u hu
    have hdagcell := hcoarse (m + 1) hsrc' l hlm u (hZmem u hu)
    have hnormle : BlockMatLoewnerLE
        (normalizedBlock (coarseBlock (standardCell d l u) a) E)
        (scaledBlockIdentity d ((3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ))))) :=
      blockMatLoewnerLE_scaledBlockIdentity_of_blockScale (hAsymm u a) hEsymm hEpd hdagcell
    simp only [hNcutdef]
    refine blockCutoff_eq_self fun α β => ?_
    have hent := abs_blockMatEntry_le_of_blockMatLoewnerLE_scaledBlockIdentity
      (hNsymm u a) (blockVecDot_nonneg_of_blockPosDef (hNpd u a)) hnormle α β
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)] at hent
    rw [hBdef]
    exact hent
  have havg : (avgBlockOf Zi fun u => Ncut u a)
      = normalizedBlock (avgBlockOf Zi fun u => coarseBlock (standardCell d l u) a) E := by
    rw [normalizedBlock_avgBlockOf]
    exact avgBlockOf_congr hcutoff
  -- the normalized deviation is below the scaled identity
  have hD1 : BlockMatLoewnerLE
      (normalizedBlock (blockSub (avgBlockOf Zi fun u => coarseBlock (standardCell d l u) a)
        (annealedBlock P (centeredCube d l))) E) (scaledBlockIdentity d kappa) := by
    intro Y
    rw [normalizedBlock_blockSub, blockVecDot_blockMatVecMul_blockSub,
      blockVecDot_scaledBlockIdentity]
    have hg := hgood Y
    rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_blockMatVecMul_blockScale,
      blockVecDot_scaledBlockIdentity, one_mul, blockVecDot_blockMatVecMul_blockSub,
      havg] at hg
    have hg' : (2 * Bcut)⁻¹ *
        (blockVecDot Y (blockMatVecMul
            (normalizedBlock (avgBlockOf Zi fun u => coarseBlock (standardCell d l u) a) E) Y) -
          blockVecDot Y (blockMatVecMul
            (avgBlockOf Zi fun u => meanBlock P fun b => Ncut u b) Y)) ≤
        2 * (d : ℝ) * eta * ∑ α : BlockCoord d, toFullBlockVec Y α * toFullBlockVec Y α := by
      linarith only [hg]
    have hmul := mul_le_mul_of_nonneg_left hg' h2B.le
    rw [mul_inv_cancel_left₀ (ne_of_gt h2B)] at hmul
    have hring : (2 * Bcut) *
        (2 * (d : ℝ) * eta * ∑ α : BlockCoord d, toFullBlockVec Y α * toFullBlockVec Y α)
        = kappa * ∑ α : BlockCoord d, toFullBlockVec Y α * toFullBlockVec Y α := by
      rw [hkappadef]
      ring
    have hc := hMavg Y
    linarith only [hmul, hring, hc]
  have hD2 : BlockMatLoewnerLE
      (blockSub (avgBlockOf Zi fun u => coarseBlock (standardCell d l u) a)
        (annealedBlock P (centeredCube d l))) (blockScale kappa E) :=
    blockMatLoewnerLE_blockScale_of_normalizedBlock
      (isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_avgBlockOf Zi fun u => isSymmetricBlockMat_coarseBlock _ a)
        (isSymmetricBlockMat_annealedBlock P _)) hEsymm hEpd hD1
  -- the closing chain of quadratic forms
  intro X
  have e1 := hsubadd a X
  have e2 := hD2 X
  have e3 := href X
  rw [blockVecDot_blockMatVecMul_blockSub, blockVecDot_blockMatVecMul_blockScale] at e2
  rw [blockVecDot_blockMatVecMul_blockScale] at e3
  rw [blockVecDot_blockMatVecMul_blockScale]
  set qAhat : ℝ := blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d l)) X)
    with hqAhatdef
  set qE : ℝ := blockVecDot X (blockMatVecMul E X) with hqEdef
  have hqE0 : 0 ≤ qE := by
    rw [hqEdef]
    exact blockVecDot_nonneg_of_blockPosDef hEpd X
  have hqAhat0 : 0 ≤ qAhat := by
    by_contra hcon
    push Not at hcon
    have hneg : 2 * kappaRef E * qAhat < 0 := by nlinarith only [hkappa1, hcon]
    linarith only [e3, hqE0, hneg]
  have hstep : kappa * qE ≤ 2 * kappa * kappaRef E * qAhat := by
    have hle : qE ≤ 2 * kappaRef E * qAhat := by linarith only [e3]
    have hmul := mul_le_mul_of_nonneg_left hle hkappa0
    have hring : kappa * (2 * kappaRef E * qAhat) = 2 * kappa * kappaRef E * qAhat := by ring
    linarith only [hmul, hring]
  have hCmul : 2 * kappa * kappaRef E * qAhat ≤ C * qAhat := by
    have hle : 2 * kappa * kappaRef E ≤ C := by rw [hkeq]; exact hC
    exact mul_le_mul_of_nonneg_right hle hqAhat0
  have hring : (1 + C) * qAhat = qAhat + C * qAhat := by ring
  linarith only [e1, e2, hstep, hCmul, hring]

/-! ## The named input of the renormalization lemma, from the frozen carriers -/

/-- **The single-cell renormalization estimate holds for the frozen carriers.**
Stationarity, unit range of dependence and the coarse-ellipticity datum supply
`HasCellRenormalization` at the annealed block of the inner generation
`l = n - l₀`, with the exponents `γ = g` and `ν = d/2` and the gain

`Gain = 32 d² 3^g C_fr(d) (1 + renormShift d) κ_𝐄`,

a constant of the dimension, of the exponent `g` and of the reference block
alone.  The two arithmetic side conditions are the printed ones: the inner
generation lies below the window (`h ≤ l₀ + 1`), and the source tail at the inner
generation is at most one half. -/
theorem hasCellRenormalization_of_frozen [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {Kg : ℝ} {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi Kg S)
    {n l0 h : ℕ} (hl0n : l0 ≤ n) (hhl0 : h ≤ l0 + 1)
    (hhalf : (Psi ((3 : ℝ) ^ ((n : ℤ) - (l0 : ℤ))))⁻¹ ≤ 1 / 2) :
    HasCellRenormalization P S (annealedBlock P (centeredCube d ((n : ℤ) - (l0 : ℤ))))
      g ((d : ℝ) / 2)
      (32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * (1 + renormShift d) * kappaRef E)
      n l0 h := by
  classical
  set l : ℤ := (n : ℤ) - (l0 : ℤ) with hldef
  have hl : (0 : ℤ) ≤ l := by omega
  have hlcast : ((l : ℤ) : ℝ) = (n : ℝ) - (l0 : ℝ) := by
    rw [hldef]
    push_cast
    ring
  intro m k hnm hwin hkm T hT w hw
  have hlk : l ≤ k := by omega
  refine measureReal_renormCell_le_of_family hstat hunit hdag hl (by omega) hhalf
    (Zi := (centredIndexFinset d l k).image (innerShift k l w))
    ((centredIndexFinset_nonempty d l k).image _) ?_ w (fun a => ?_) hT ?_
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    exact standardCellCenter_innerShift_mem_centeredCube_succ hlk hkm hw
      ((mem_centredIndexFinset_iff hlk).1 ht)
  · exact blockMatLoewnerLE_coarseBlock_avgBlockOf hl hlk w a
  · -- the closing arithmetic
    rw [← hlcast]
    have hkappa0 : (0 : ℝ) ≤ kappaRef E :=
      le_trans zero_le_one
        (Initialization.one_le_kappaRef hdag.refBlock_isSymm hdag.refBlock_posDef
          (Initialization.blockMatLoewnerLE_blockSharp_reference hdag))
    have hCfr0 : (0 : ℝ) ≤ frThreshold d := (frThreshold_pos d).le
    have h3g : (0 : ℝ) < (3 : ℝ) ^ g := Real.rpow_pos_of_pos (by norm_num) _
    have hA : (0 : ℝ) < (3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hD : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hpow : (3 : ℝ) ^ (g * (((m + 1 : ℤ) : ℝ) - (l : ℝ)))
        = (3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) * (3 : ℝ) ^ g := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    have hsqrt : (Real.sqrt ((((centredIndexFinset d l k).image
          (innerShift k l w)).card : ℕ) : ℝ))⁻¹
        = (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))) := by
      rw [card_image_innerShift, sqrt_card_centredIndexFinset d hlk,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have hTs : T + renormShift d ≤ (1 + renormShift d) * T := by
      have hs := renormShift_nonneg d
      nlinarith only [hT, hs]
    have hX0 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * kappaRef E *
        ((3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ)))) := by
      have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g := mul_nonneg h1 h3g.le
      have h3 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d := mul_nonneg h2 hCfr0
      exact mul_nonneg (mul_nonneg h3 hkappa0) (mul_nonneg hA.le hD.le)
    rw [hpow, hsqrt]
    calc 32 * (d : ℝ) ^ 2 *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) * (3 : ℝ) ^ g) * frThreshold d *
          (T + renormShift d) * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))) * kappaRef E
        = (32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * kappaRef E *
            ((3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))))) * (T + renormShift d) := by
          ring
      _ ≤ (32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * kappaRef E *
            ((3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))))) *
            ((1 + renormShift d) * T) := mul_le_mul_of_nonneg_left hTs hX0
      _ = 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * (1 + renormShift d) * kappaRef E *
            (3 : ℝ) ^ (g * ((m : ℝ) - (l : ℝ))) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((k : ℝ) - (l : ℝ))) * T := by ring

end

end Quenched
end HighContrast
end HCPolySupport
