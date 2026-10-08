/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Definitions
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.GlobalComparison

/-!
# Coarse-graining support: Support.Book.Ch01.Theorems.CircDomination

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Chapter 1 circ domination

The Chapter 1 public facade consists of the six exact source-regime bounds
below.  The former totalized-real, disjoint-cube comparisons remain available
only as compatibility results in `Book.Ch01.Legacy`.
-/

namespace HCPolySupport
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-- In the exact negative `q = 1` regime, the hatted dual seminorm is bounded
by the exact finite-`q` circ seminorm. All proof obligations are internal. -/
theorem dualNegativeBesovQOneHattedSeminorm_le_circNegativeBesovFiniteSeminorm
    {d : ℕ} (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovQOneHattedSeminorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
        circNegativeBesovFiniteSeminorm P.circParameters Q f
          (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) :=
  HCPolySupport.exactDualQOneHattedSeminorm_le_exactCircFiniteSeminorm P Q f hf

/-- In the exact negative `q = 1` regime, the full dual norm is bounded by the
exact finite-`q` circ seminorm plus the literal root term. All proof obligations
are internal. -/
theorem dualNegativeBesovQOneFullNorm_le_circNegativeBesovFiniteSeminorm_add_root
    {d : ℕ} (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovQOneFullNorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
          circNegativeBesovFiniteSeminorm P.circParameters Q f
            (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        HCPolySupport.exactCircDepthWeight Q P.s 0 *
          ENNReal.ofReal |HCPolySupport.cubeAverage Q f| :=
  HCPolySupport.exactDualQOneFullNorm_le_exactCircFiniteSeminorm_add_root P Q f hf

/-- In the exact finite-interior negative Besov (`1 < q < ∞`) regime, the
hatted dual seminorm is bounded by the exact finite-`q` circ seminorm. All
proof obligations are internal. -/
theorem dualNegativeBesovFiniteHattedSeminorm_le_circNegativeBesovFiniteSeminorm
    {d : ℕ} (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovFiniteHattedSeminorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
        circNegativeBesovFiniteSeminorm P.circParameters Q f
          (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) :=
  HCPolySupport.exactDualFiniteHattedSeminorm_le_exactCircFiniteSeminorm P Q f hf

/-- In the exact finite-interior negative Besov (`1 < q < ∞`) regime, the full
dual norm is bounded by the exact finite-`q` circ seminorm plus the literal
root term. All proof obligations are internal. -/
theorem dualNegativeBesovFiniteFullNorm_le_circNegativeBesovFiniteSeminorm_add_root
    {d : ℕ} (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovFiniteFullNorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
          circNegativeBesovFiniteSeminorm P.circParameters Q f
            (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        HCPolySupport.exactCircDepthWeight Q P.s 0 *
          ENNReal.ofReal |HCPolySupport.cubeAverage Q f| :=
  HCPolySupport.exactDualFiniteFullNorm_le_exactCircFiniteSeminorm_add_root P Q f hf

/-- In the exact negative `q = ∞` regime, the hatted dual seminorm is bounded
by the exact endpoint circ seminorm. All proof obligations are internal. -/
theorem dualNegativeBesovTopHattedSeminorm_le_circNegativeBesovTopSeminorm
    {d : ℕ} (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovTopHattedSeminorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
        circNegativeBesovTopSeminorm P.circParameters Q f
          (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) :=
  HCPolySupport.exactDualTopHattedSeminorm_le_exactCircTopSeminorm P Q f hf

/-- In the exact negative `q = ∞` regime, the full dual norm is bounded by the
exact endpoint circ seminorm plus the literal root term. All proof obligations
are internal. -/
theorem dualNegativeBesovTopFullNorm_le_circNegativeBesovTopSeminorm_add_root
    {d : ℕ} (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (normalizedCubeMeasure Q)) :
    dualNegativeBesovTopFullNorm P Q f hf ≤
      (3 : ENNReal) ^ ((d : ℝ) + P.s) *
          circNegativeBesovTopSeminorm P.circParameters Q f
            (HCPolySupport.exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        HCPolySupport.exactCircDepthWeight Q P.s 0 *
          ENNReal.ofReal |HCPolySupport.cubeAverage Q f| :=
  HCPolySupport.exactDualTopFullNorm_le_exactCircTopSeminorm_add_root P Q f hf

/-! ## Legacy totalized-real and disjoint-cube compatibility -/

namespace Legacy

/-- Compatibility comparison for the totalized-real, disjoint-cube mean-zero
dual Besov seminorm; it is not an exact source-regime theorem. -/
theorem circDominatesMeanZeroDualBesov {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    dualNegativeBesovSeminorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u :=
  HCPolySupport.cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm
    Q s p q u hs hu hp hpTop hpConjTop hq

/-- Compatibility comparison for the totalized-real, disjoint-cube full dual
Besov norm; it is not an exact source-regime theorem. -/
theorem circDominatesFullDualBesov {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    dualNegativeBesovNorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖ :=
  HCPolySupport.cubeBesovDualFullNorm_le_note_rhs
    Q s p q u hs hu hp hpTop hpConjTop hq

/-- Compatibility pairing estimate for totalized-real, disjoint-cube Besov
quantities and unit full-dual positive tests; it is not an exact source pairing
theorem. -/
theorem cubeBesovPairing_le_circNorm_of_fullTest {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u g : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q)
    (hg : CubeBesovDualFullTest Q s p q g) :
    |cubeBesovPairing Q u g| ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u := by
  have hBdd :
      BddAbove (cubeBesovCircNormValueSet Q s p q u) :=
    HCPolySupport.cubeBesovCircNormValueSet_bddAbove_of_memLp
      Q s p q u hs hu hp hpTop hq
  have hpair :
      |cubeBesovPairing Q u g| ≤
        max 1 ((3 : ℝ) ^ s) * circNegativeBesovNorm Q s p q u :=
    HCPolySupport.abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_full_test
      Q s p q u g hBdd hu hp hpTop hpConjTop hq hg
  have hconst :
      max 1 ((3 : ℝ) ^ s) ≤ (3 : ℝ) ^ ((d : ℝ) + s) :=
    HCPolySupport.max_one_three_rpow_le_three_rpow_nat_add d s hs.le
  have hcirc_nonneg :
      0 ≤ circNegativeBesovNorm Q s p q u :=
    HCPolySupport.cubeBesovCircNorm_nonneg Q s p q u hBdd
  exact hpair.trans (mul_le_mul_of_nonneg_right hconst hcirc_nonneg)

end Legacy

end

end Ch01
end Book
end HCPolySupport
