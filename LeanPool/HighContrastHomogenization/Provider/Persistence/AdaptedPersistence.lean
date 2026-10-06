/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity
public import LeanPool.HighContrastHomogenization.Geometry.CanonicalDeterminant
public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects

/-!
# High-contrast homogenization: Provider.Persistence.AdaptedPersistence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted persistence of the annealed means

The persistence of the adapted block above the response scale reads the adapted
means of a rounded grid at every scale above the entry scale in both directions:
the coarser mean lies below the entry mean, and the entry mean lies below
`(1+δ_ad)^d` times the coarser one.  The first half is the annealed mean order of
`p.fixed.geometry.parent.child.recurrence`.  The second is the determinant account.

Write `Ξ(H) = det(H)^{1/d}` for the determinant root of a doubled block.  The
determinant clause for the canonical metric reads, on a block that dominates its
own sharp, as `1 ≤ det(H) ≤ 𝔡(H)^d`, and the annealed primal-adjoint order makes
every adapted mean of the tower dominate its own sharp.  So the coarser mean has
determinant at least one, and the entry mean has determinant at most the `d`-th
power of its imbalance, which the adapted-imbalance hypothesis caps at `1+δ_ad`.
The determinant quotient of the ordered pair is therefore at most `(1+δ_ad)^d`,
and `e.global.selection.metric.loss` turns a determinant quotient bounded by
`r^d` into the Loewner comparison `E ≤ r^d F` for the pair it is read on.

The account is unconditional in the sense that it consumes only the finiteness of
the entry mean: the finiteness of the coarser mean, which both halves need in
order to denote, is supplied by the upward integrability of the companion file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Persistence

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

/-! ## Two order facts about scalar dilations and the imbalance -/

section Scalars

variable {n : Type*}

/-- Dilation of a fixed positive semidefinite matrix is monotone in the
scalar. -/
theorem smul_le_smul_of_le_right {A : Matrix n n ℝ} (hA : A.PosSemidef) {c₁ c₂ : ℝ}
    (h : c₁ ≤ c₂) : c₁ • A ≤ c₂ • A := by
  refine Matrix.le_iff.mpr ?_
  have hrw : c₂ • A - c₁ • A = (c₂ - c₁) • A := (sub_smul c₂ c₁ A).symm
  rw [hrw]
  exact hA.smul (sub_nonneg.mpr h)

end Scalars

variable {d : ℕ}

/-- **The imbalance of a self-dominating positive block is at least one.**  The
determinant clause for the canonical metric puts the determinant between one and
the `d`-th power of the imbalance, so an imbalance below one would leave no
room. -/
theorem one_le_canonImbalance [Nonempty (Fin d)] {E : FullBlockMat d} (hE : E.PosDef)
    (hle : fullBlockSharp E ≤ E) : 1 ≤ canonImbalance E := by
  have hd : 0 < d := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin d)›
  by_contra hlt
  push Not at hlt
  have hpow := pow_lt_one₀ (canonImbalance_pos hE).le hlt hd.ne'
  have hdet := one_le_det_of_fullBlockSharp_le hE hle
  have hupper := det_le_canonImbalance_pow hE hle
  linarith only [hpow, hdet, hupper]

/-- **A determinant quotient bounded by `c` gives the Loewner comparison
`E ≤ cF`.**  This is `e.global.selection.metric.loss` at the printed ratio,
with the ratio's `d`-th power replaced by any upper bound for it. -/
theorem le_smul_of_det_div_le (hd : 2 ≤ d) {E F : FullBlockMat d} (hE : E.PosDef)
    (hF : F.PosDef) (hFE : F ≤ E) {c : ℝ} (hc : E.det / F.det ≤ c) : E ≤ c • F := by
  obtain ⟨-, ⟨-, hle⟩, -, -, -⟩ := canonDeterminantLoss_canonDetRatio hd hE hF hFE
  rw [canonDetRatio_pow (by omega) (div_pos hE.det_pos hF.det_pos).le] at hle
  exact hle.trans (smul_le_smul_of_le_right hF.posSemidef hc)

/-! ## The annealed sharp order at the adapted means -/

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d}

/-- **The adapted mean dominates its own sharp.**  This is the annealed
primal-adjoint order on the adapted cell, which is a nonempty bounded open
convex domain as soon as the grid is positive definite. -/
theorem blockSharp_adaptedMean_le [IsProbabilityMeasure P] (hq : IsRoundedGrid l q)
    (r : ℤ) (hfin : HasFiniteAdaptedMean P q r) :
    BlockMatLoewnerLE (blockSharp (adaptedMean P q r)) (adaptedMean P q r) :=
  Sharp.blockSharp_annealedBlock_le_of_nonempty
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell (Recurrence.posDef_of_isRoundedGrid hq) r)
    (Recurrence.adaptedCell_nonempty q r) hfin

/-- The same, on the flattened carrier the determinant account is read on. -/
theorem fullBlockSharp_toFullBlockMat_adaptedMean_le [IsProbabilityMeasure P]
    (hq : IsRoundedGrid l q) (r : ℤ) (hfin : HasFiniteAdaptedMean P q r) :
    fullBlockSharp (toFullBlockMat (adaptedMean P q r)) ≤
      toFullBlockMat (adaptedMean P q r) :=
  fullBlockSharp_le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P q r)
    (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r hfin)
    (blockSharp_adaptedMean_le hq r hfin)

/-! ## The determinant account of an adapted mean -/

/-- **`1 ≤ det(E_r^q)`**, the lower half of the determinant clause at an adapted
mean. -/
theorem one_le_det_adaptedMean [IsProbabilityMeasure P] (hq : IsRoundedGrid l q)
    (r : ℤ) (hfin : HasFiniteAdaptedMean P q r) :
    1 ≤ (toFullBlockMat (adaptedMean P q r)).det :=
  one_le_det_of_fullBlockSharp_le (Recurrence.posDef_toFullBlockMat_adaptedMean hq r hfin)
    (fullBlockSharp_toFullBlockMat_adaptedMean_le hq r hfin)

/-- **`det(E_r^q) ≤ 𝔡(E_r^q)^d`**, the upper half of the determinant clause at
an adapted mean. -/
theorem det_adaptedMean_le_blockImbalance_pow [Nonempty (Fin d)] [IsProbabilityMeasure P]
    (hq : IsRoundedGrid l q) (r : ℤ) (hfin : HasFiniteAdaptedMean P q r) :
    (toFullBlockMat (adaptedMean P q r)).det ≤ blockImbalance (adaptedMean P q r) ^ d :=
  det_le_canonImbalance_pow (Recurrence.posDef_toFullBlockMat_adaptedMean hq r hfin)
    (fullBlockSharp_toFullBlockMat_adaptedMean_le hq r hfin)

/-- **`1 ≤ 𝔡(E_r^q)`**: the imbalance of an adapted mean is at least one. -/
theorem one_le_blockImbalance_adaptedMean [Nonempty (Fin d)] [IsProbabilityMeasure P]
    (hq : IsRoundedGrid l q) (r : ℤ) (hfin : HasFiniteAdaptedMean P q r) :
    1 ≤ blockImbalance (adaptedMean P q r) :=
  one_le_canonImbalance (Recurrence.posDef_toFullBlockMat_adaptedMean hq r hfin)
    (fullBlockSharp_toFullBlockMat_adaptedMean_le hq r hfin)

/-! ## The persistence clause -/

end

end Persistence
end HighContrast
end HCPolySupport
