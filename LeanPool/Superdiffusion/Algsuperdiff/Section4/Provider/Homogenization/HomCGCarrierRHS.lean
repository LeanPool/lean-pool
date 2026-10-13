/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierEnergy

/-!
# HomCGCarrierRHS

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The printed right-hand side at both spellings

## What this file supplies

The measurement was that `CoarseGraining`'s `localCoarseGrainingLpRHS` and this
repository's `coarseGrainingFinitePRHS` "match term for term", with the ONE
real issue at the `S`-slot.  `HomCGCarrierEnergy` settles the `S`-slot; this
file performs the remaining, purely bookkeeping half:

```text
  localCoarseGrainingLpRHS C Q n hn 𝐚 σ₀ hσ₀ 𝐠 u s₁ s s₂ p
      ≤ ENNReal.ofReal (coarseGrainingFinitePRHS Ccg s s₂ σ₀ E₁ E₂ D_g S n)
```

as soon as the four abstract slots of this repository's spelling dominate the
four printed carriers of `CoarseGraining`'s:

| repo slot | printed carrier |
| --- | --- |
| `Ccg`  | the produced constant `C(p,d)` |
| `E₁`   | `parentTruncatedHomogenizationErrorInfinityOneScalar … s₁` |
| `E₂`   | `parentTruncatedHomogenizationErrorInfinityTwoScalar … (s₁/2)` |
| `D_g`  | `cubeEuclideanPositiveBesovOverlapESeminorm □_m s₂ p 𝐠` |
| `S`    | `weightedLocalSymmetricEnergyLp` (`HomCGCarrierEnergy`) |

Everything else is an `ℝ≥0∞`/`ℝ` transfer of the printed scalars: `s^{-1}`,
`σ₀^{1/2} = √σ₀`, `s^{-9/2}`, `(s₂-s)^{-1}`, `1 + E₂²` and `3^{s₂n}`.  Every
transfer is an EQUALITY, so no constant is lost here.

## The order slot is NOT transferred here

The display is entered at the order `s′` the carrier comparison forces (see
`HomCGCarrierEnergy`), so the right-hand side below is the printed one READ AT
`s′`: its prefactors are `s′^{-1}`, `s′^{-9/2}` and `(s₂-s′)^{-1}`.  No
transfer back to the data order `s` is attempted, and none is needed: the
Step-4 consumption site takes its own arithmetic side condition at its own
order, exactly as the per-site disposition of the corrected reading.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The right-hand side, transferred -/

/-- **The printed right-hand side, at this repository's real-valued spelling.** -/
theorem localCoarseGrainingLpRHS_le_ofReal
    {Q : TriadicCube d} {n : ℤ} (hn : n ≤ Q.scale)
    {C : ℝ≥0∞} (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) (g : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (s1 s s2 : FractionalOrder) (p : FiniteLpExponent) (hss2 : s.1 < s2.1)
    {Ccg E1 E2 Dg S : ℝ} (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hDg0 : 0 ≤ Dg) (hS0 : 0 ≤ S)
    (hC : C ≤ ENNReal.ofReal Ccg)
    (hE1 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≤ ENNReal.ofReal E1)
    (hE2 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2)
    (hDg : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤ ENNReal.ofReal Dg)
    (hSlot : weightedLocalSymmetricEnergyLp Q n hn a u s1 s p ≤ ENNReal.ofReal S) :
    localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p ≤
      ENNReal.ofReal (coarseGrainingFinitePRHS Ccg s.1 s2.1 sigma0 E1 E2 Dg S n) := by
  have hs0 : 0 < s.1 := s.2.1
  have hdiff : 0 < s2.1 - s.1 := sub_pos.mpr hss2
  have nInv : (0 : ℝ) ≤ s.1⁻¹ := inv_nonneg.mpr hs0.le
  have nSqrt : (0 : ℝ) ≤ Real.sqrt sigma0 := Real.sqrt_nonneg _
  have nPow : (0 : ℝ) ≤ s.1 ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
  have nDinv : (0 : ℝ) ≤ (s2.1 - s.1)⁻¹ := inv_nonneg.mpr hdiff.le
  have nE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE20 2
    linarith only [h]
  have nThree : (0 : ℝ) ≤ (3 : ℝ) ^ (s2.1 * (n : ℝ)) := three_rpow_nonneg _
  /- the two scalar identities of the first summa -/
  have hInv : (ENNReal.ofReal s.1)⁻¹ = ENNReal.ofReal s.1⁻¹ :=
    (ENNReal.ofReal_inv_of_pos hs0).symm
  have hSq : (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt sigma0) := by
    rw [ENNReal.ofReal_rpow_of_pos hsigma0, Real.sqrt_eq_rpow]
  /- the three scalar identities of the second summa -/
  have hPow : (ENNReal.ofReal s.1) ^ (-(9 / 2) : ℝ) =
      ENNReal.ofReal (s.1 ^ (-(9 / 2) : ℝ)) := ENNReal.ofReal_rpow_of_pos hs0
  have hDinv : (ENNReal.ofReal (s2.1 - s.1))⁻¹ = ENNReal.ofReal (s2.1 - s.1)⁻¹ :=
    (ENNReal.ofReal_inv_of_pos hdiff).symm
  have hE2sq : (1 : ℝ≥0∞) +
      (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 (fractionalOrderHalf s1)) ^ 2 ≤ ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) := by
    have hsq : (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 (fractionalOrderHalf s1)) ^ 2 ≤ (ENNReal.ofReal E2) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul' hE2 hE2
    calc (1 : ℝ≥0∞) + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a
            sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2
        ≤ 1 + (ENNReal.ofReal E2) ^ 2 := add_le_add le_rfl hsq
      _ = ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (pow_nonneg hE20 2), ENNReal.ofReal_one,
            ENNReal.ofReal_pow hE20]
  /- the two summands, separate -/
  have hT1 : C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
          hsigma0 s1 *
        weightedLocalSymmetricEnergyLp Q n hn a u s1 s p ≤
      ENNReal.ofReal (Ccg * s.1⁻¹ * Real.sqrt sigma0 * E1 * S) := by
    rw [hInv, hSq,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nInv) nSqrt) hE10),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCcg0 nInv) nSqrt),
      ENNReal.ofReal_mul (mul_nonneg hCcg0 nInv), ENNReal.ofReal_mul hCcg0]
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hC le_rfl) le_rfl) hE1) hSlot
  have hT2 : C * (ENNReal.ofReal s.1) ^ (-(9 / 2) : ℝ) *
        (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
        (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
          hsigma0 (fractionalOrderHalf s1)) ^ 2) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤
      ENNReal.ofReal (Ccg * s.1 ^ (-(9 / 2) : ℝ) * (s2.1 - s.1)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2.1 * (n : ℝ)) * Dg)) := by
    rw [hPow, hDinv,
      show Ccg * s.1 ^ (-(9 / 2) : ℝ) * (s2.1 - s.1)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2.1 * (n : ℝ)) * Dg) =
        Ccg * s.1 ^ (-(9 / 2) : ℝ) * (s2.1 - s.1)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          (3 : ℝ) ^ (s2.1 * (n : ℝ)) * Dg from by ring,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nPow) nDinv)
        nE2sq) nThree),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nPow) nDinv) nE2sq),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCcg0 nPow) nDinv),
      ENNReal.ofReal_mul (mul_nonneg hCcg0 nPow), ENNReal.ofReal_mul hCcg0]
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hC le_rfl) le_rfl)
      hE2sq) le_rfl) hDg
  /- assemb -/
  have hsum1 : (0 : ℝ) ≤ Ccg * s.1⁻¹ * Real.sqrt sigma0 * E1 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nInv) nSqrt) hE10) hS0
  have hsum2 : (0 : ℝ) ≤ Ccg * s.1 ^ (-(9 / 2) : ℝ) * (s2.1 - s.1)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2.1 * (n : ℝ)) * Dg) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nPow) nDinv) nE2sq)
      (mul_nonneg nThree hDg0)
  rw [coarseGrainingFinitePRHS_def, ENNReal.ofReal_add hsum1 hsum2]
  exact add_le_add hT1 hT2

/-! ## 2. Nonnegativity of the transferred right-hand side -/

/-- This repository's spelling of the printed right-hand side is nonnegative on the
printed data. -/
theorem coarseGrainingFinitePRHS_nonneg {Ccg s s2 sigma E1 E2 Dg S : ℝ} {n : ℤ}
    (hCcg0 : 0 ≤ Ccg) (hs0 : 0 < s) (hss2 : s < s2)
    (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2) (hDg0 : 0 ≤ Dg) (hS0 : 0 ≤ S) :
    0 ≤ coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n := by
  have nInv : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have nSqrt : (0 : ℝ) ≤ Real.sqrt sigma := Real.sqrt_nonneg _
  have nPow : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
  have nDinv : (0 : ℝ) ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (by linarith only [hss2])
  have nE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE20 2
    linarith only [h]
  have nThree : (0 : ℝ) ≤ (3 : ℝ) ^ (s2 * (n : ℝ)) := three_rpow_nonneg _
  rw [coarseGrainingFinitePRHS_def]
  have h1 : (0 : ℝ) ≤ Ccg * s⁻¹ * Real.sqrt sigma * E1 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nInv) nSqrt) hE10) hS0
  have h2 : (0 : ℝ) ≤ Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * (n : ℝ)) * Dg) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCcg0 nPow) nDinv) nE2sq)
      (mul_nonneg nThree hDg0)
  linarith only [h1, h2]

/-- The real value of the printed right-hand side, from the transferred bound. -/
theorem localCoarseGrainingLpRHS_toReal_le [NeZero d]
    {Q : TriadicCube d} {n : ℤ} (hn : n ≤ Q.scale)
    {C : ℝ≥0∞} (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) (g : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (s1 s s2 : FractionalOrder) (p : FiniteLpExponent) (hss2 : s.1 < s2.1)
    {Ccg E1 E2 Dg S : ℝ} (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hDg0 : 0 ≤ Dg) (hS0 : 0 ≤ S)
    (hC : C ≤ ENNReal.ofReal Ccg)
    (hE1 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≤ ENNReal.ofReal E1)
    (hE2 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2)
    (hDg : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤ ENNReal.ofReal Dg)
    (hSlot : weightedLocalSymmetricEnergyLp Q n hn a u s1 s p ≤ ENNReal.ofReal S) :
    (localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p).toReal ≤
      coarseGrainingFinitePRHS Ccg s.1 s2.1 sigma0 E1 E2 Dg S n := by
  have hbase := localCoarseGrainingLpRHS_le_ofReal hn a hsigma0 g u s1 s s2 p hss2
    hCcg0 hE10 hE20 hDg0 hS0 hC hE1 hE2 hDg hSlot
  have hnn : 0 ≤ coarseGrainingFinitePRHS Ccg s.1 s2.1 sigma0 E1 E2 Dg S n :=
    coarseGrainingFinitePRHS_nonneg hCcg0 s.2.1 hss2 hE10 hE20 hDg0 hS0
  have hstep := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbase
  rwa [ENNReal.toReal_ofReal hnn] at hstep

/-- The transferred right-hand side is finite. -/
theorem localCoarseGrainingLpRHS_ne_top [NeZero d]
    {Q : TriadicCube d} {n : ℤ} (hn : n ≤ Q.scale)
    {C : ℝ≥0∞} (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) (g : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (s1 s s2 : FractionalOrder) (p : FiniteLpExponent) (hss2 : s.1 < s2.1)
    {Ccg E1 E2 Dg S : ℝ} (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hDg0 : 0 ≤ Dg) (hS0 : 0 ≤ S)
    (hC : C ≤ ENNReal.ofReal Ccg)
    (hE1 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0
        hsigma0 s1 ≤ ENNReal.ofReal E1)
    (hE2 : Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0
        hsigma0 (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2)
    (hDg : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g ≤ ENNReal.ofReal Dg)
    (hSlot : weightedLocalSymmetricEnergyLp Q n hn a u s1 s p ≤ ENNReal.ofReal S) :
    localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (localCoarseGrainingLpRHS_le_ofReal hn a hsigma0 g u s1 s s2 p hss2
      hCcg0 hE10 hE20 hDg0 hS0 hC hE1 hE2 hDg hSlot)

end

end Algsuperdiff.Section4.Provider.Homogenization
