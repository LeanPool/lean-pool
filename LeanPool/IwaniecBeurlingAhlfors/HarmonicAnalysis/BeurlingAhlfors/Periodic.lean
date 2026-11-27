/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Smooth
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Transference

/-!
# The Beurling–Ahlfors transform on smooth periodic functions

On `ℤ²`-periodic functions on `ℝ² ≅ ℂ`, the powers `𝓑^k` of the Beurling–Ahlfors transform are
the Fourier multipliers `UnitAddTorus.periodicMultiplier` with the symbols `m (ν)^k`,
`m (ξ) = (conj ξ) / ξ` (`HarmonicAnalysis.beurlingSymbol`), `ν = n₀ + i n₁`
(`HarmonicAnalysis.latticePoint`):

* the symbols are bounded, hence polynomially bounded
  (`HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow`);
* `𝓑 (∂_zbar g) = ∂g` for every smooth periodic `g`
  (`HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi`), by comparing coefficients:
  `m (ν) πi ν = πi (conj ν)`;
* on trigonometric polynomials, `𝓑^k` is the torus multiplier `HarmonicAnalysis.torusBeurlingPow`
  (`HarmonicAnalysis.periodicMultiplier_trigPoly`).
-/

@[expose] public section

noncomputable section

open Complex
open scoped ComplexConjugate Real ContDiff

namespace HarmonicAnalysis

open UnitAddTorus

/-- The symbols `m (n₀ + i n₁)^k` of `𝓑^k` on `𝕋²` are polynomially bounded (by `1`). -/
theorem isPolyBounded_beurlingSymbol_pow (k : ℕ) :
    IsPolyBounded fun n => beurlingSymbol (latticePoint n) ^ k :=
  isPolyBounded_of_norm_le (C := 1) fun n => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_beurlingSymbol_le _)

/-- `𝓑 (∂_zbar g) = ∂g` for every smooth `ℤ²`-periodic `g : ℝ² → ℂ`. -/
theorem periodicMultiplier_beurlingSymbol_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) :
    periodicMultiplier (fun n => beurlingSymbol (latticePoint n)) (dzbarPi g) = dzPi g := by
  have hβ : IsPolyBounded fun n => beurlingSymbol (latticePoint n) := by
    simpa using isPolyBounded_beurlingSymbol_pow 1
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hd := contDiff_dzbarPi hg
  have hdp := isPeriodic_dzbarPi hper
  refine eq_of_cubeFourierCoeff_eq (contDiff_periodicMultiplier hβ hd hdp)
    (isPeriodic_periodicMultiplier _ _) (contDiff_dzPi hg) (isPeriodic_dzPi hper) fun n => ?_
  rw [cubeFourierCoeff_periodicMultiplier hβ hd hdp, cubeFourierCoeff_dzbarPi hg1 hper,
    cubeFourierCoeff_dzPi hg1 hper]
  -- `m (ν) πi ν = πi (conj ν)`
  rcases eq_or_ne (latticePoint n) 0 with h | h
  · simp [h]
  · rw [beurlingSymbol]
    field_simp

/-- On trigonometric polynomials, `𝓑^k` is the torus multiplier `torusBeurlingPow k`. -/
theorem periodicMultiplier_trigPoly (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) :
    periodicMultiplier (fun n => beurlingSymbol (latticePoint n) ^ k)
        (fun x => trigPoly c (ofPi x)) =
      fun x => torusBeurlingPow k c (ofPi x) := by
  have e : (fun x => trigPoly c (ofPi x)) =
      fun x => ∑ n ∈ c.support, c n * mFourier n (ofPi x) := by
    funext x
    simp [trigPoly, Finsupp.sum]
  rw [e, periodicMultiplier_sum_mFourier]
  funext x
  simp [torusBeurlingPow, torusMultiplier, Finsupp.sum]

end HarmonicAnalysis
