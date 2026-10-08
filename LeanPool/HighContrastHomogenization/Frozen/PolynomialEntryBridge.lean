/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Statements.PolynomialEntry
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Frozen.PolynomialEntryBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From the printed form of `t.polynomial.entry` to the calibrated form

The theorem `t.polynomial.entry` is printed as a statement about *every* scale
beyond the entry scale: for a tolerance `σ ∈ (0, 1]` there is a constant `C` with
`Θ_m ≤ 1 + σ` for every `m ≥ ⌈C log₃(2 + Π K)⌉`.  The consumers of the theorem in
the proofs of `t.algebraic.convergence` and `t.random.homogenization` use it in a
calibrated form instead: a tolerance `c_*` below both members of a calibration
pair `(c_sc, c_end)`, and a single entry generation `m_ent` exhibited as a
natural number, bounded by the printed ceiling and with `3^{m_ent}` polynomial in
`2 + Π K`.

This module derives the second from the first.  Three steps are involved.

* **The tolerance.**  `c_* := min 1 (min c_sc c_end)` is positive, lies below both
  members of the calibration pair, and is admissible as a tolerance in the
  printed statement, which requires `σ ≤ 1`.
* **The entry generation.**  The printed statement quantifies over all scales
  above `⌈C log₃(2 + Π K)⌉`.  That ceiling is positive, because `Π ≥ 0` and
  `K > 1` make `2 + Π K` exceed one and `C` is positive, so
  `m_ent := ⌈C log₃(2 + Π K)⌉` is a natural number and is itself an admissible
  scale.
* **The length bound.**  `⌈x⌉ < x + 1` turns the ceiling into the printed
  polynomial bound: `3^{m_ent} ≤ 3^{x+1} = 3 · 3^{C log₃(2 + Π K)} =
  3 (2 + Π K)^C`.

The assumptions `e.stationarity`, `e.unit.range` and `e.coarse.ellipticity` are
the ones the printed statement carries: `HCPoly.Frozen.IsStationaryLaw`,
`HCPoly.Frozen.IsUnitRangeLaw` and `HCPoly.Frozen.CoarseEllipticityDagger`, read
by the proofs of the propositions under their project-namespace names.  Nothing
is converted here.
-/

namespace HCPoly.Frozen

open HCPolySupport HighContrast MeasureTheory

/-- The positivity of the printed entry scale: `2 + Π K > 1` whenever the
reference aspect ratio is nonnegative and the growth witness exceeds one, so a
positive multiple of its base-three logarithm has a positive ceiling. -/
theorem one_lt_two_add_aspectRatio_mul {d : ℕ} (E : BlockMat d) {K : ℝ}
    (hK : 1 < K) : 1 < 2 + aspectRatio E * K := by
  have haspect : 0 ≤ aspectRatio E := aspectRatio_nonneg E
  have hprod : 0 ≤ aspectRatio E * K := mul_nonneg haspect (by linarith only [hK])
  linarith only [hprod]

/-- The printed entry generation as a natural number, with the two printed
readings of the entry scale: it is the ceiling itself, and its triadic
exponential is bounded by the printed polynomial. -/
theorem exists_entry_generation {C b : ℝ} (hC : 0 < C) (hb : 1 < b) :
    ∃ mEnt : ℕ, (mEnt : ℤ) = ⌈C * Real.logb 3 b⌉ ∧
      (3 : ℝ) ^ (mEnt : ℕ) ≤ 3 * b ^ C := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hlog : 0 < Real.logb 3 b := Real.logb_pos (by norm_num) hb
  have hx : 0 < C * Real.logb 3 b := mul_pos hC hlog
  have hceil : 0 ≤ ⌈C * Real.logb 3 b⌉ := by
    have := Int.ceil_le_ceil (le_of_lt hx)
    rw [Int.ceil_zero] at this
    exact this
  refine ⟨(⌈C * Real.logb 3 b⌉).toNat, Int.toNat_of_nonneg hceil, ?_⟩
  have hcast : (((⌈C * Real.logb 3 b⌉).toNat : ℕ) : ℝ) = ((⌈C * Real.logb 3 b⌉ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hceil)
  have hlt : ((⌈C * Real.logb 3 b⌉ : ℤ) : ℝ) < C * Real.logb 3 b + 1 :=
    Int.ceil_lt_add_one _
  have hmono : (3 : ℝ) ^ (((⌈C * Real.logb 3 b⌉).toNat : ℕ) : ℝ)
      ≤ (3 : ℝ) ^ (C * Real.logb 3 b + 1) := by
    rw [hcast]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr hlt.le
  have hsplit : (3 : ℝ) ^ (C * Real.logb 3 b + 1) = b ^ C * 3 := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one, mul_comm C,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hb0]
  rw [← Real.rpow_natCast 3 ((⌈C * Real.logb 3 b⌉).toNat)]
  rw [hsplit] at hmono
  linarith only [hmono]

/-- **The bridge.**  The calibrated form of `t.polynomial.entry` used by
`ss.algebraic.convergence` and `ss.random.dirichlet`, derived from the printed
form.  The calibration pair `(c_sc, c_end)` is carried by the statement; the
intermediate `δ₀` and the calibration inequality are carried for the consumers
and are not used here. -/
theorem polynomial_entry_random_source_of_printed
    (d : ℕ) (hd : 2 ≤ d)
    (cSc _δ₀ cEnd : ℝ) (hcSc : 0 < cSc) (_hδ₀ : _δ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hcEnd : 0 < cEnd)
    (_hcal : (1 + _δ₀) ^ 2 * (1 + cEnd) ≤ 1 + cSc) :
    ∃ cStar : ℝ, cStar ∈ Set.Ioc 0 (min cSc cEnd) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
            CoarseEllipticityDagger P g E Ψ K S →
            ∃ mEnt : ℕ,
              (mEnt : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
              annealedContrast P (mEnt : ℤ) - 1 ≤ cStar ∧
              (3 : ℝ) ^ (mEnt : ℕ) ≤ 3 * (2 + aspectRatio E * K) ^ C := by
  have hmin : 0 < min cSc cEnd := lt_min hcSc hcEnd
  refine ⟨min 1 (min cSc cEnd), ⟨lt_min zero_lt_one hmin, min_le_right _ _⟩, ?_⟩
  intro g hg
  obtain ⟨C, hC, hbody⟩ :=
    HCPolySupport.HighContrast.polynomial_entry d hd g hg (min 1 (min cSc cEnd))
      ⟨lt_min zero_lt_one hmin, min_le_left _ _⟩
  refine ⟨C, hC, ?_⟩
  intro P E Ψ K S hP hstat hrange hdagger
  have hb : 1 < 2 + aspectRatio E * K :=
    one_lt_two_add_aspectRatio_mul E hdagger.one_lt_growthWitness
  obtain ⟨mEnt, hmEnt, hpow⟩ := exists_entry_generation hC hb
  refine ⟨mEnt, le_of_eq hmEnt, ?_, hpow⟩
  have hcontrast :=
    hbody P E Ψ K S hP hstat hrange hdagger (mEnt : ℤ) (le_of_eq hmEnt.symm)
  linarith only [hcontrast]

end HCPoly.Frozen
