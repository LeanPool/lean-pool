/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitSharpOrder
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledQuenchedMinimalScale
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedMainBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bridge to the inlined quenched-convergence statement

The composed quenched minimal scale is stated with the provider-tier row
`quenched_block_row` and with a single tolerance selected before the law.  The
source-facing statement writes the row out in the vocabulary of the setup layer,
indexes it by an integer generation, and offers every tolerance in `(0,1)`.

Two conversions are recorded.  The first is the meaning identity: above a random
scale that is at least one, the integer generation is nonnegative, and the
provider row at that generation is exactly the weighted sum of largest
normalized coarse-block excesses restricted to the burnt-source branch.  The
second is the tolerance inflation: dilating the random scale by a deterministic
factor trades the ratio's algebraic weight against the row's coefficient and
leaves the tail of the dilated scale unchanged, the dilation being absorbed into
the polynomial length.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The inlined row -/

/-- The weighted row of normalized coarse-block excesses at an integer
generation, written in the vocabulary of the setup layer. -/
@[expose]
public def inlinedRow (rho : ℝ) (Abar : BlockMat d) (S : CoeffSpace d → ℝ)
    (a : CoeffSpace d) (m : ℤ) : ℝ :=
  if S a ≤ (3 : ℝ) ^ m then
    ∑' n : ℕ, (3 : ℝ) ^ (-rho * (n : ℝ)) *
      sSup {r : ℝ | ∃ w : Fin d → ℤ,
        standardCellCenter (m - (n : ℤ)) w ∈ centeredCube d m ∧
        r = blockExcess (coarseBlock (standardCell d (m - (n : ℤ)) w) a) Abar}
  else 0

/-- At a nonnegative generation the provider row is the inlined row. -/
private theorem physical_block_row_at_int_eq_inlinedRow
    (rho : ℝ) (Abar : BlockMat d) (S : CoeffSpace d → ℝ) (a : CoeffSpace d)
    {m : ℤ} (hm : 0 ≤ m) :
    physicalBlockRowAtInteger rho Abar S a m = inlinedRow rho Abar S a m := by
  have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
  have hpow : (3 : ℝ) ^ (m.toNat) = (3 : ℝ) ^ m := by
    rw [← zpow_natCast, hcast]
  simp only [physicalBlockRowAtInteger, quenchedBlockRow, inlinedRow, hpow,
    hcast]

/-! ## The tolerance inflation -/

/-- The deterministic dilation factor that trades the algebraic weight of the
ratio against the coefficient of the row. -/
@[expose]
public def toleranceDilation (kappa delta0 delta : ℝ) : ℝ :=
  max 1 ((delta0 / delta) ^ kappa⁻¹)

private theorem one_le_toleranceDilation (kappa delta0 delta : ℝ) :
    1 ≤ toleranceDilation kappa delta0 delta := le_max_left _ _

/-- The dilation converts the provider's tolerance into any smaller one. -/
private theorem mul_rpow_neg_toleranceDilation_le
    {kappa delta0 delta : ℝ} (hkappa : 0 < kappa) (hdelta0 : 0 < delta0)
    (hdelta : 0 < delta) :
    delta0 * toleranceDilation kappa delta0 delta ^ (-kappa) ≤ delta := by
  set lam := toleranceDilation kappa delta0 delta with hlam
  have hlam1 : 1 ≤ lam := one_le_toleranceDilation kappa delta0 delta
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
  have hratio : 0 < delta0 / delta := div_pos hdelta0 hdelta
  have hbase : (delta0 / delta) ^ kappa⁻¹ ≤ lam := le_max_right _ _
  have hpow : delta0 / delta ≤ lam ^ kappa := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hratio.le _) hbase hkappa.le
    rwa [← Real.rpow_mul hratio.le, inv_mul_cancel₀ (ne_of_gt hkappa),
      Real.rpow_one] at h
  have hlamkappa : 0 < lam ^ kappa := Real.rpow_pos_of_pos hlampos _
  have hinv : lam ^ (-kappa) ≤ delta / delta0 := by
    rw [Real.rpow_neg hlampos.le]
    rw [inv_le_comm₀ hlamkappa (div_pos hdelta hdelta0)]
    rw [inv_div]
    exact hpow
  calc delta0 * lam ^ (-kappa) ≤ delta0 * (delta / delta0) :=
        mul_le_mul_of_nonneg_left hinv hdelta0.le
    _ = delta := by field_simp

/-! ## The annealed sandwich of the rebased limit block -/

/-- **The rebased annealed limit block is pinned by the Euclidean annealed
blocks of the original law at every nonnegative generation.**  Above the rebase
depth this is the covariance identity followed by the limit's two orderings;
below it, the mean order of `p.fixed.geometry.parent.child.recurrence` on the original law
for the lower comparison, and the greatest-lower-bound property of the limit
applied to the annealed primal-adjoint order for the upper one. -/
theorem annealedLimitBlock_sandwich_of_covariance [NeZero d]
    {P Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Pbase]
    {g gBase : ℝ} {E Ebase : BlockMat d} {Psi PsiBase : ℝ → ℝ} {K Kbase : ℝ}
    {S Sbase : CoeffSpace d → ℝ} {nBase : ℕ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hstatBase : HCPoly.Frozen.IsStationaryLaw Pbase)
    (hdagBase : HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase PsiBase
      Kbase Sbase)
    (hcov : ∀ j : ℕ,
      annealedBlock Pbase (centeredCube d (j : ℤ)) =
        annealedBlock P (centeredCube d ((nBase + j : ℕ) : ℤ))) :
    (∀ m : ℕ,
      BlockMatLoewnerLE (annealedLimitBlock Pbase)
        (annealedBlock P (centeredCube d (m : ℤ)))) ∧
      (∀ m : ℕ,
        BlockMatLoewnerLE
          (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
          (annealedLimitBlock Pbase)) := by
  constructor
  · intro m
    rcases le_or_gt nBase m with hm | hm
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [← hcov j]
      exact blockMatLoewnerLE_annealedLimitBlock hstatBase hdagBase
        (Int.natCast_nonneg j)
    · have hzero :
          BlockMatLoewnerLE (annealedLimitBlock Pbase)
            (annealedBlock P (centeredCube d ((nBase : ℕ) : ℤ))) := by
        have h := blockMatLoewnerLE_annealedLimitBlock hstatBase hdagBase
          (m := ((0 : ℕ) : ℤ)) (Int.natCast_nonneg 0)
        rw [hcov 0] at h
        simpa using h
      refine hzero.trans ?_
      exact Entry.annealedBlock_centeredCube_le_of_nonneg hstat hdag
        (Int.natCast_nonneg m) (by exact_mod_cast hm.le)
  · intro m
    refine blockMatLoewnerLE_annealedLimitBlock_of_forall hstatBase hdagBase ?_
    intro n
    rw [hcov n]
    exact blockMatLoewnerLE_blockSharp_annealedBlock hstat hdag
      (Int.natCast_nonneg m) (nBase + n)

/-! ## The bridge -/

/-- **The composed quenched minimal scale gives the inlined quenched
convergence.**  The hypothesis is the conclusion of the coupled step, carrying
in addition the two Loewner comparisons that pin the limit block against the
Euclidean annealed blocks of the law itself. -/
theorem quenched_convergence_of_coupled_providers (d : ℕ) (hd : 2 ≤ d)
    (hprov : ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C cSrc kappa delta : ℝ,
          0 < C ∧ 0 < cSrc ∧ 0 < kappa ∧ delta ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Psi : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            ∃ (Abar : BlockMat d) (Nann : ℕ) (Lpoly : ℝ)
              (Ssrc X : CoeffSpace d → ℝ),
              IsSymmetricBlockMat Abar ∧
              Book.Ch02.BlockPosDef Abar ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE Abar
                  (annealedBlock P (centeredCube d (m : ℤ)))) ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE
                  (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                  Abar) ∧
              (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ Nann)) ∧
              1 ≤ Lpoly ∧
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              Measurable Ssrc ∧
              (∀ a, 1 ≤ Ssrc a) ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                    (Psi (cSrc * t))⁻¹) ∧
              ∃ OmegaEnd : Set (CoeffSpace d),
                MeasurableSet OmegaEnd ∧
                P.real OmegaEnd = 1 ∧
                (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
                ∀ a ∈ OmegaEnd,
                  HasAllLaterPhysicalBlockRow ((1 + 3 * g) / 4) kappa delta Abar
                    S X a) :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C kappa cSrc : ℝ, 1 < C ∧ 0 < kappa ∧ 0 < cSrc ∧
          ∀ delta : ℝ, delta ∈ Set.Ioo (0 : ℝ) 1 →
            ∃ Cdel : ℝ, 1 ≤ Cdel ∧
              ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Psi : ℝ → ℝ)
                (K : ℝ) (S : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                HCPoly.Frozen.IsStationaryLaw P →
                HCPoly.Frozen.IsUnitRangeLaw P →
                HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
                ∃ (Abar : BlockMat d) (Lpoly : ℝ) (X : CoeffSpace d → ℝ),
                  IsSymmetricBlockMat Abar ∧
                  Book.Ch02.BlockPosDef Abar ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE Abar
                      (annealedBlock P (centeredCube d (m : ℤ)))) ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE
                      (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                      Abar) ∧
                  1 ≤ Lpoly ∧
                  Lpoly ≤ (2 + aspectRatio E * K) ^ Cdel ∧
                  Measurable X ∧
                  (∀ a, 1 ≤ X a) ∧
                  (∀ t : ℝ, 1 ≤ t →
                    P.real {a | C * Lpoly * t ≤ X a} ≤
                      Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                        (Psi (cSrc * t))⁻¹) ∧
                  ∃ OmegaEnd : Set (CoeffSpace d),
                    MeasurableSet OmegaEnd ∧
                    P.real OmegaEnd = 1 ∧
                    (∀ z : Fin d → ℤ,
                      translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
                    ∀ a ∈ OmegaEnd, ∀ m : ℤ, X a ≤ (3 : ℝ) ^ m →
                      (if S a ≤ (3 : ℝ) ^ m then
                          ∑' n : ℕ, (3 : ℝ) ^ (-((1 + 3 * g) / 4) * (n : ℝ)) *
                            sSup {r : ℝ | ∃ w : Fin d → ℤ,
                              standardCellCenter (m - (n : ℤ)) w ∈
                                centeredCube d m ∧
                              r = blockExcess
                                (coarseBlock
                                  (standardCell d (m - (n : ℤ)) w) a) Abar}
                        else 0) ≤ delta * ((3 : ℝ) ^ m / X a) ^ (-kappa) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cd, hcd, hprov⟩ := hprov
  refine ⟨cd, hcd, ?_⟩
  intro g hg
  obtain ⟨C0, cSrc, kappa, delta0, hC0, hcSrc, hkappa, hdelta0, hprov⟩ :=
    hprov g hg
  refine ⟨max C0 2, kappa, cSrc, ?_, hkappa, hcSrc, ?_⟩
  · exact lt_of_lt_of_le one_lt_two (le_max_right _ _)
  intro delta hdelta
  set lam := toleranceDilation kappa delta0 delta with hlamdef
  have hlam1 : 1 ≤ lam := one_le_toleranceDilation kappa delta0 delta
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
  have hlogb : 0 ≤ Real.logb 3 lam :=
    Real.logb_nonneg (by norm_num) hlam1
  refine ⟨max C0 2 + Real.logb 3 lam, by
    have : (2 : ℝ) ≤ max C0 2 := le_max_right _ _
    linarith only [this, hlogb], ?_⟩
  intro P E Psi K S hP hstat hunit hdag
  let : IsProbabilityMeasure P := hP
  obtain ⟨Abar, Nann, Lpoly, Ssrc, X, hsymm, hposdef, hlower, hupper, -,
    hLpoly1, hLpolyBound, -, -, hXmeas, hX1, htail, OmegaEnd, hmeas, hfull,
    hinv, hrow⟩ := hprov P E Psi K S hP hstat hunit hdag
  have hAspect : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hB3 : (3 : ℝ) ≤ 2 + aspectRatio E * K := by nlinarith only [hAspect, hK]
  have hBpos : (0 : ℝ) < 2 + aspectRatio E * K := by linarith only [hB3]
  have hC0le : C0 ≤ max C0 2 := le_max_left _ _
  refine ⟨Abar, lam * Lpoly, fun a => lam * X a, hsymm, hposdef, hlower, hupper,
    ?_, ?_, hXmeas.const_mul lam, ?_, ?_, OmegaEnd, hmeas, hfull, hinv, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hlam1 hLpoly1
  · -- the polynomial length absorbs the dilation
    have hstep :
        Lpoly * lam ≤
          (2 + aspectRatio E * K) ^ (max C0 2) * (2 + aspectRatio E * K) ^
            Real.logb 3 lam := by
      have hleft : Lpoly ≤ (2 + aspectRatio E * K) ^ (max C0 2) :=
        hLpolyBound.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith only [hB3]) hC0le)
      have hright : lam ≤ (2 + aspectRatio E * K) ^ Real.logb 3 lam := by
        have h3 : (3 : ℝ) ^ Real.logb 3 lam ≤
            (2 + aspectRatio E * K) ^ Real.logb 3 lam :=
          Real.rpow_le_rpow (by norm_num) hB3 hlogb
        rwa [Real.rpow_logb (by norm_num) (by norm_num) hlampos] at h3
      exact mul_le_mul hleft hright hlampos.le (Real.rpow_nonneg hBpos.le _)
    rw [Real.rpow_add hBpos, mul_comm lam Lpoly]
    exact hstep
  · intro a
    exact one_le_mul_of_one_le_of_one_le hlam1 (hX1 a)
  · -- the tail of the dilated scale
    intro t ht
    refine le_trans (measureReal_mono ?_) (htail t ht)
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hcancel : max C0 2 * Lpoly * t ≤ X a := by
      have := ha
      have hmul : lam * (max C0 2 * Lpoly * t) ≤ lam * X a := by
        calc lam * (max C0 2 * Lpoly * t) = max C0 2 * (lam * Lpoly) * t := by
              ring
          _ ≤ lam * X a := this
      exact le_of_mul_le_mul_left hmul hlampos
    have hLt : 0 ≤ Lpoly * t := mul_nonneg (by linarith only [hLpoly1])
      (by linarith only [ht])
    calc C0 * Lpoly * t = C0 * (Lpoly * t) := by ring
      _ ≤ max C0 2 * (Lpoly * t) := mul_le_mul_of_nonneg_right hC0le hLt
      _ = max C0 2 * Lpoly * t := by ring
      _ ≤ X a := hcancel
  · -- the inlined row at every admissible integer generation
    intro a ha m hm
    have hXa1 : 1 ≤ X a := hX1 a
    have hXapos : 0 < X a := lt_of_lt_of_le zero_lt_one hXa1
    have hdilated : 1 ≤ lam * X a := one_le_mul_of_one_le_of_one_le hlam1 hXa1
    have hdilatedpos : 0 < lam * X a := lt_of_lt_of_le zero_lt_one hdilated
    have hm0 : 0 ≤ m := by
      by_contra hneg
      have hlt : (3 : ℝ) ^ m < 1 :=
        zpow_lt_one_of_neg₀ (by norm_num) (lt_of_not_ge hneg)
      exact (not_lt_of_ge (hdilated.trans hm)) hlt
    have hXm : X a ≤ (3 : ℝ) ^ m :=
      le_trans (le_mul_of_one_le_left hXapos.le hlam1) hm
    have hbase := hrow a ha m hXm
    rw [physical_block_row_at_int_eq_inlinedRow _ _ _ _ hm0] at hbase
    have hupos : 0 ≤ (3 : ℝ) ^ m / (lam * X a) :=
      div_nonneg (zpow_nonneg (by norm_num) m) hdilatedpos.le
    have hsplit : (3 : ℝ) ^ m / X a = lam * ((3 : ℝ) ^ m / (lam * X a)) := by
      field_simp
    have hfactor :
        ((3 : ℝ) ^ m / X a) ^ (-kappa) =
          lam ^ (-kappa) * ((3 : ℝ) ^ m / (lam * X a)) ^ (-kappa) := by
      rw [hsplit, Real.mul_rpow hlampos.le hupos]
    have hcoeff : delta0 * lam ^ (-kappa) ≤ delta :=
      mul_rpow_neg_toleranceDilation_le hkappa hdelta0.1 hdelta.1
    change inlinedRow ((1 + 3 * g) / 4) Abar S a m ≤ _
    calc inlinedRow ((1 + 3 * g) / 4) Abar S a m
        ≤ delta0 * ((3 : ℝ) ^ m / X a) ^ (-kappa) := hbase
      _ = delta0 * lam ^ (-kappa) *
            ((3 : ℝ) ^ m / (lam * X a)) ^ (-kappa) := by
          rw [hfactor]; ring
      _ ≤ delta * ((3 : ℝ) ^ m / (lam * X a)) ^ (-kappa) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hupos _)

end

end HCPolySupport.HighContrast.Quenched
