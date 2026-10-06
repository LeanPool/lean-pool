/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EccentricityFoldFactor

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.RootInterface.ScaleFactorArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The root-interface length factor

The root's exported homogenization length is the quenched length multiplied by
one common positive factor.  Two independent sources contribute to that factor:

* the **certificate factor**, paid once when the printed-order certificate is
  read at the common affine scale rather than at the raw quenched scale;
* the **provider factor**, paid once by the Dirichlet provider, which is free to
  choose a law-free `g`-dependent amplitude together with an eccentricity power.

Both are of the same shape — a law-free real at least one, times a power of the
homogenized witness eccentricity — so the whole factor is again of that shape.
This module records the arithmetic of such a factor: it is at least one, it is
polynomial in the printed length base, and it transfers every clause of the
frozen statement exactly as the single fold factor of
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.EccentricityFoldFactor` does.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## A law-free amplitude is polynomial in the printed base -/

/-- A real at least one is below any base at least two raised to its binary
logarithm.  This converts a law-free amplitude into a polynomial-length
exponent. -/
theorem le_rpow_logb_two {base L : ℝ} (hbase : (2 : ℝ) ≤ base) (hL : 1 ≤ L) :
    L ≤ base ^ Real.logb 2 L := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hlogb : (0 : ℝ) ≤ Real.logb 2 L :=
    Real.logb_nonneg (by norm_num) hL
  have hrewrite : (2 : ℝ) ^ Real.logb 2 L = L :=
    Real.rpow_logb (by norm_num) (by norm_num) hL0
  calc L = (2 : ℝ) ^ Real.logb 2 L := hrewrite.symm
    _ ≤ base ^ Real.logb 2 L :=
        Real.rpow_le_rpow (by norm_num) hbase hlogb

theorem logb_two_nonneg {L : ℝ} (hL : 1 ≤ L) : (0 : ℝ) ≤ Real.logb 2 L :=
  Real.logb_nonneg (by norm_num) hL

/-! ## The composite root factor -/

/-- The root's length factor: a law-free amplitude times an eccentricity power,
paid once by the certificate and once by the Dirichlet provider. -/
@[expose]
def rootLengthFactor (abar : Mat d) (Lcert pCert Lprov pProv : ℝ) : ℝ :=
  (Lcert * RowSupply.eccentricityFoldFactor abar pCert) *
    (Lprov * RowSupply.eccentricityFoldFactor abar pProv)

theorem one_le_rootLengthFactor {abar : Mat d} {Lcert pCert Lprov pProv : ℝ}
    (hLcert : 1 ≤ Lcert) (hLprov : 1 ≤ Lprov) :
    1 ≤ rootLengthFactor abar Lcert pCert Lprov pProv := by
  have h1 : (1 : ℝ) ≤ Lcert * RowSupply.eccentricityFoldFactor abar pCert :=
    one_le_mul_of_one_le_of_one_le hLcert
      (RowSupply.one_le_eccentricityFoldFactor abar pCert)
  have h2 : (1 : ℝ) ≤ Lprov * RowSupply.eccentricityFoldFactor abar pProv :=
    one_le_mul_of_one_le_of_one_le hLprov
      (RowSupply.one_le_eccentricityFoldFactor abar pProv)
  exact one_le_mul_of_one_le_of_one_le h1 h2

theorem rootLengthFactor_pos {abar : Mat d} {Lcert pCert Lprov pProv : ℝ}
    (hLcert : 1 ≤ Lcert) (hLprov : 1 ≤ Lprov) :
    0 < rootLengthFactor abar Lcert pCert Lprov pProv :=
  lt_of_lt_of_le zero_lt_one (one_le_rootLengthFactor hLcert hLprov)

/-- The composite exponent the polynomial-length clause closes at. -/
@[expose]
def rootLengthExponent (Lcert pCert Lprov pProv : ℝ) : ℝ :=
  Real.logb 2 Lcert + 5 * pCert + (Real.logb 2 Lprov + 5 * pProv)

theorem rootLengthExponent_nonneg {Lcert pCert Lprov pProv : ℝ}
    (hLcert : 1 ≤ Lcert) (hpCert : 0 ≤ pCert)
    (hLprov : 1 ≤ Lprov) (hpProv : 0 ≤ pProv) :
    0 ≤ rootLengthExponent Lcert pCert Lprov pProv := by
  have h1 := logb_two_nonneg hLcert
  have h2 := logb_two_nonneg hLprov
  have h3 : (0 : ℝ) ≤ 5 * pCert := by positivity
  have h4 : (0 : ℝ) ≤ 5 * pProv := by positivity
  unfold rootLengthExponent
  linarith only [h1, h2, h3, h4]

/-- **The root factor is polynomial in the printed length base.**  The law-free
halves are absorbed by their binary logarithms and the eccentricity halves by
the law-level eccentricity bound. -/
theorem rootLengthFactor_le_rpow {abar : Mat d} {base Lcert pCert Lprov pProv : ℝ}
    (hbase : (2 : ℝ) ≤ base) (hLcert : 1 ≤ Lcert) (hpCert : 0 ≤ pCert)
    (hLprov : 1 ≤ Lprov) (hpProv : 0 ≤ pProv)
    (hecc : witnessEccentricity (symmPart abar) ≤ base ^ (5 : ℝ)) :
    rootLengthFactor abar Lcert pCert Lprov pProv ≤
      base ^ rootLengthExponent Lcert pCert Lprov pProv := by
  have hbase1 : (1 : ℝ) ≤ base := le_trans (by norm_num) hbase
  have hbase0 : (0 : ℝ) < base := lt_of_lt_of_le zero_lt_one hbase1
  have hcert : Lcert * RowSupply.eccentricityFoldFactor abar pCert ≤
      base ^ (Real.logb 2 Lcert + 5 * pCert) :=
    RowSupply.mul_le_rpow_add hbase1
      (le_trans zero_le_one (RowSupply.one_le_eccentricityFoldFactor abar pCert))
      (le_rpow_logb_two hbase hLcert)
      (RowSupply.eccentricityFoldFactor_le_rpow hbase1 hpCert hecc)
  have hprov : Lprov * RowSupply.eccentricityFoldFactor abar pProv ≤
      base ^ (Real.logb 2 Lprov + 5 * pProv) :=
    RowSupply.mul_le_rpow_add hbase1
      (le_trans zero_le_one (RowSupply.one_le_eccentricityFoldFactor abar pProv))
      (le_rpow_logb_two hbase hLprov)
      (RowSupply.eccentricityFoldFactor_le_rpow hbase1 hpProv hecc)
  have hnonneg : (0 : ℝ) ≤ Lprov * RowSupply.eccentricityFoldFactor abar pProv :=
    le_trans zero_le_one
      (one_le_mul_of_one_le_of_one_le hLprov
        (RowSupply.one_le_eccentricityFoldFactor abar pProv))
  have hpow : (0 : ℝ) ≤ base ^ (Real.logb 2 Lcert + 5 * pCert) :=
    (Real.rpow_pos_of_pos hbase0 _).le
  unfold rootLengthFactor rootLengthExponent
  calc
    (Lcert * RowSupply.eccentricityFoldFactor abar pCert) *
          (Lprov * RowSupply.eccentricityFoldFactor abar pProv) ≤
        base ^ (Real.logb 2 Lcert + 5 * pCert) *
          base ^ (Real.logb 2 Lprov + 5 * pProv) :=
      mul_le_mul hcert hprov hnonneg hpow
    _ = base ^ (Real.logb 2 Lcert + 5 * pCert +
          (Real.logb 2 Lprov + 5 * pProv)) := (Real.rpow_add hbase0 _ _).symm

/-! ## Generic clause transfers at a common factor -/

theorem le_mul_factor {x F : ℝ} (hx : 0 ≤ x) (hF : 1 ≤ F) : x ≤ x * F :=
  le_mul_of_one_le_right hx hF

theorem one_le_mul_factor {x F : ℝ} (hx : 1 ≤ x) (hF : 1 ≤ F) : 1 ≤ x * F :=
  hx.trans (le_mul_factor (le_trans zero_le_one hx) hF)

theorem measurable_mul_factor {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega → ℝ} {F : ℝ} (hX : Measurable X) :
    Measurable fun a => X a * F :=
  hX.mul_const _

end

end RootInterface
end HighContrast
end HCPolySupport
