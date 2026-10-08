/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitSharpOrder

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedEndpointAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed endpoint of the endgame, assembled on the rebased law

The endgame of `t.random.homogenization` rebases the law
once at a generation `n_rb` and then reads the annealed estimates of the rebased
law back through the covariance of the coarse blocks and the contrast under a
dilation of the law, established in `ss.algebraic.convergence`.  This file performs
that reading: it converts the rebased annealed data at the delay `m_0` of
`e.algebraic.entry` into the original indexing
at `N_ann = n_rb + m_0` of `e.algebraic.entry`, and
accounts the polynomial cost
`e.algebraic.entry`.

Three ingredients are supplied here from the standing assumptions alone: the
limit block of the rebased law with its symmetry, its positive definiteness and
its lower Loewner bound; the reindexing of the contrast and of the annealed
block along the covariance; and the additive absorption of the two polynomial
length costs into one exponent.  The upper Loewner comparison and the geometric
contrast decay are the analytic content of the small-contrast endgame and enter
as explicit hypotheses.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## The additive absorption of the polynomial length costs -/

/-- **The two polynomial length costs absorb additively.**  A rebase length
bounded by `base ^ Crebase`, a reference size bounded by the same power, and a
delay bounded by the `Cdelay` power of that reference size together bound the
total length by the `Crebase * (1 + Cdelay)` power of the base.  Requiring only
`Crebase ≤ Cann` and `Cdelay ≤ Cann` separately would not suffice.

At the product exponent the base needs no lower bound beyond nonnegativity: the
rebase clause already forces the intermediate power to be at least one. -/
theorem three_pow_add_le_rpow_of_length_costs {base b : ℝ} {n m : ℕ}
    {Crebase Cdelay : ℝ} (hbase0 : 0 ≤ base) (hb0 : 0 ≤ b)
    (hn : (3 : ℝ) ^ n ≤ base ^ Crebase) (hb : b ≤ base ^ Crebase)
    (hm : (3 : ℝ) ^ m ≤ b ^ Cdelay) (hCdelay : 0 ≤ Cdelay) :
    (3 : ℝ) ^ (n + m) ≤ base ^ (Crebase * (1 + Cdelay)) := by
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hyPos : (0 : ℝ) < base ^ Crebase := lt_of_lt_of_le zero_lt_one (hone.trans hn)
  have hpowm : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
  have hstep : b ^ Cdelay ≤ (base ^ Crebase) ^ Cdelay :=
    Real.rpow_le_rpow hb0 hb hCdelay
  have hsplit : base ^ Crebase * (base ^ Crebase) ^ Cdelay =
      (base ^ Crebase) ^ (1 + Cdelay) := by
    rw [Real.rpow_add hyPos, Real.rpow_one]
  have hcomp : (base ^ Crebase) ^ (1 + Cdelay) = base ^ (Crebase * (1 + Cdelay)) :=
    (Real.rpow_mul hbase0 _ _).symm
  calc (3 : ℝ) ^ (n + m) = (3 : ℝ) ^ n * (3 : ℝ) ^ m := pow_add 3 n m
    _ ≤ base ^ Crebase * b ^ Cdelay := mul_le_mul hn hm hpowm hyPos.le
    _ ≤ base ^ Crebase * (base ^ Crebase) ^ Cdelay :=
        mul_le_mul_of_nonneg_left hstep hyPos.le
    _ = base ^ (Crebase * (1 + Cdelay)) := by rw [hsplit, hcomp]

/-- The length account at an enlarged exponent, which does require the base to
be at least one. -/
theorem three_pow_add_le_rpow_of_length_costs_le {base b : ℝ} {n m : ℕ}
    {Crebase Cdelay Cann : ℝ} (hbase : 1 ≤ base) (hb0 : 0 ≤ b)
    (hn : (3 : ℝ) ^ n ≤ base ^ Crebase) (hb : b ≤ base ^ Crebase)
    (hm : (3 : ℝ) ^ m ≤ b ^ Cdelay) (hCdelay : 0 ≤ Cdelay)
    (hCann : Crebase * (1 + Cdelay) ≤ Cann) :
    (3 : ℝ) ^ (n + m) ≤ base ^ Cann :=
  le_trans
    (three_pow_add_le_rpow_of_length_costs (le_trans zero_le_one hbase) hb0 hn hb hm hCdelay)
    (Real.rpow_le_rpow_of_exponent_le hbase hCann)

/-! ## Reindexing along the scale covariance -/

/-- The rebased contrast at the delayed generation is the original contrast at
the annealed entry generation, read through the covariance of the contrast under
a dilation of the law. -/
theorem annealedContrast_shift_of_covariance {P Pbase : Measure (CoeffSpace d)}
    {nBase m : ℕ}
    (hcov : ∀ j : ℕ,
      annealedContrast Pbase (j : ℤ) = annealedContrast P ((nBase + j : ℕ) : ℤ))
    (j : ℕ) :
    annealedContrast Pbase ((m + j : ℕ) : ℤ) =
      annealedContrast P ((nBase + m + j : ℕ) : ℤ) := by
  have h := hcov (m + j)
  rwa [show nBase + (m + j) = nBase + m + j from (Nat.add_assoc nBase m j).symm] at h

/-- The rebased annealed block at the delayed generation is the original
annealed block at the annealed entry generation. -/
theorem annealedBlock_shift_of_covariance {P Pbase : Measure (CoeffSpace d)}
    {nBase m : ℕ}
    (hcov : ∀ j : ℕ,
      annealedBlock Pbase (centeredCube d (j : ℤ)) =
        annealedBlock P (centeredCube d ((nBase + j : ℕ) : ℤ)))
    (j : ℕ) :
    annealedBlock Pbase (centeredCube d ((m + j : ℕ) : ℤ)) =
      annealedBlock P (centeredCube d ((nBase + m + j : ℕ) : ℤ)) := by
  have h := hcov (m + j)
  rwa [show nBase + (m + j) = nBase + m + j from (Nat.add_assoc nBase m j).symm] at h

/-! ## The assembled endpoint -/

/-- **The annealed endpoint on the original indexing.**  From the standing
assumptions on the rebased law, the two scale covariances and the two polynomial
rebase costs, and the small-contrast conclusions of the endgame on the rebased
law, this produces the endgame's annealed package at
`N_ann = n_rb + m_0`: a symmetric positive definite limit block, the polynomial
bound on `3^{N_ann}`, the geometric contrast decay
`e.algebraic.contrast.decay`, and the two-sided
Loewner comparison
`e.algebraic.block.decay`.

The limit block, its symmetry, its lower Loewner bound, the reindexing and the
length accounting are proved here.  The geometric contrast decay and the upper
Loewner comparison are the hypotheses `hcontrast` and `hupper`. -/
theorem exists_annealed_endpoint_of_rebased_decay [NeZero d]
    {P Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {E Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {K Kbase gBase : ℝ}
    {Sbase : CoeffSpace d → ℝ} {alpha Crebase Cdelay Cann : ℝ} {nBase m0 : ℕ}
    (hstat : HCPoly.Frozen.IsStationaryLaw Pbase)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase Ψbase Kbase Sbase)
    (hcovContrast : ∀ j : ℕ,
      annealedContrast Pbase (j : ℤ) = annealedContrast P ((nBase + j : ℕ) : ℤ))
    (hcovBlock : ∀ j : ℕ,
      annealedBlock Pbase (centeredCube d (j : ℤ)) =
        annealedBlock P (centeredCube d ((nBase + j : ℕ) : ℤ)))
    (hbase : 1 ≤ 2 + aspectRatio E * K)
    (hnBase : (3 : ℝ) ^ nBase ≤ (2 + aspectRatio E * K) ^ Crebase)
    (hrefCost : 2 + aspectRatio Ebase * Kbase ≤ (2 + aspectRatio E * K) ^ Crebase)
    (hCdelay : 0 ≤ Cdelay) (hCann : Crebase * (1 + Cdelay) ≤ Cann)
    (hdelay : (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay)
    (hcontrast : ∀ j : ℕ,
      annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ)))
    (hupper : ∀ j : ℕ,
      BlockMatLoewnerLE (annealedBlock Pbase (centeredCube d ((m0 + j : ℕ) : ℤ)))
        (blockScale (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) (annealedLimitBlock Pbase))) :
    ∃ (Abar : BlockMat d) (Nann : ℕ),
      IsSymmetricBlockMat Abar ∧
      Book.Ch02.BlockPosDef Abar ∧
      (3 : ℝ) ^ Nann ≤ (2 + aspectRatio E * K) ^ Cann ∧
      (∀ j : ℕ,
        annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ))) ∧
      (∀ j : ℕ,
        BlockMatLoewnerLE Abar (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
        BlockMatLoewnerLE (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ)))
          (blockScale (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) ∧
      Abar = annealedLimitBlock Pbase := by
  classical
  refine ⟨annealedLimitBlock Pbase, nBase + m0,
    isSymmetricBlockMat_annealedLimitBlock Pbase, ?_, ?_, ?_, ?_, rfl⟩
  · -- positivity of the limit, from the sharp order alone
    exact blockPosDef_annealedLimitBlock hstat hdag
  · -- the polynomial length account
    have hEbase : 0 ≤ 2 + aspectRatio Ebase * Kbase := by
      have hAR : 1 ≤ aspectRatio Ebase := one_le_aspectRatio_of_coarseEllipticityDagger hdag
      have hK : 1 < Kbase := hdag.one_lt_growthWitness
      nlinarith only [hAR, hK]
    exact three_pow_add_le_rpow_of_length_costs_le hbase hEbase hnBase hrefCost hdelay
      hCdelay hCann
  · -- the contrast decay, reindexed
    intro j
    have hshift := annealedContrast_shift_of_covariance (m := m0) hcovContrast j
    have h := hcontrast j
    rw [hshift] at h
    exact h
  · -- the two Loewner comparisons, reindexed
    intro j
    have hshift := annealedBlock_shift_of_covariance (m := m0) hcovBlock j
    constructor
    · rw [← hshift]
      exact blockMatLoewnerLE_annealedLimitBlock hstat hdag
        (m := ((m0 + j : ℕ) : ℤ)) (Int.natCast_nonneg _)
    · rw [← hshift]
      exact hupper j

end

end Quenched
end HighContrast
end HCPolySupport
