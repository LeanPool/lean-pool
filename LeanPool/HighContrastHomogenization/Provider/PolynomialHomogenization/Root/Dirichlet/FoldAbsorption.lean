/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.OutputFactorEccentricityBound

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.FoldAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two joins, and the eccentricity absorption into `pEcc`

Two joins have to be supplied before the negative-Sobolev Dirichlet error
clause's inhabitant can be assembled.

**Join 1 — the two spellings of the fold factor.**  The energy collapse and
the output-factor bound are stated with `(max 1 ecc) ^ p`, while
`eccentricityFoldFactor abar p` is `max 1 (ecc ^ p)`.  They are
"equal exactly when `1 ≤ ecc`, so the bridge lemma is one `max_eq_right` step".
In fact they are equal for **every** `abar` and every `0 ≤ p`, with no
positive-definiteness hypothesis at all: below one, both sides are `1`.  So the
join costs nothing and carries no side condition.

**Join 2 — absorbing an eccentricity power into `pEcc`.**  One step absorbs a
law-free residual constant `Krest` into the *length* factor `Lg` at the rate
`κ`.  Its eccentricity companion — the move that lets `pEcc` be the **sum** of
the rate-leg and energy-leg exponents, which is the shape the restated hole
demands — is `eccentricity_absorbed_into_fold` below:

```
(C₀ · E ^ p) · (ε (x (Lg · fold p₀))) ^ κ  ≤  C₀ · (ε (x (Lg · fold (p₀ + p/κ)))) ^ κ
```

The `p/κ` is exactly the `κ`-th root that the rate factor takes, and the sum is
performed by the root-interface's `eccentricityFoldFactor_mul_le`.  Note
the shape of the enlarged length is `x * (Lg * fold pEcc)`, not `x * fold pEcc`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Join 1 -/

/-- **Join 1.**  `(max 1 ecc) ^ p` and `eccentricityFoldFactor abar p`
(= `max 1 (ecc ^ p)`) are the same number for every nonnegative exponent — no
positive-definiteness hypothesis is needed. -/
theorem max_one_witnessEccentricity_rpow_eq_fold (abar : Mat d) {p : ℝ}
    (hp : 0 ≤ p) :
    (max 1 (witnessEccentricity (symmPart abar))) ^ p =
      eccentricityFoldFactor abar p := by
  have he0 : (0 : ℝ) ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  rw [eccentricityFoldFactor]
  rcases le_or_gt 1 (witnessEccentricity (symmPart abar)) with h1 | h1
  · rw [max_eq_right h1, max_eq_right (Real.one_le_rpow h1 hp)]
  · rw [max_eq_left h1.le, Real.one_rpow,
      max_eq_left (Real.rpow_le_one he0 h1.le hp)]

/-! ## Join 2 -/

/-- **Join 2 — the eccentricity absorptions into `pEcc`.**  An eccentricity power
standing beside the constant is absorbed into the fold exponent of the enlarged
length, at the cost of `p / κ` added to `pEcc`.  This is that step's
`constant_absorbed_into_length` for the *fold* slot rather than the `Lg` slot. -/
theorem eccentricity_absorbed_into_fold (abar : Mat d)
    {C0 p p0 kappa epsilon x Lg : ℝ}
    (hC0 : 0 ≤ C0) (hkappa : 0 < kappa) (hp : 0 ≤ p) (hp0 : 0 ≤ p0)
    (heps : 0 ≤ epsilon) (hx : 0 ≤ x) (hLg : 0 ≤ Lg) :
    (C0 * (max 1 (witnessEccentricity (symmPart abar))) ^ p) *
        (epsilon * (x * (Lg * eccentricityFoldFactor abar p0))) ^ kappa ≤
      C0 *
        (epsilon * (x * (Lg *
          eccentricityFoldFactor abar (p0 + p / kappa)))) ^ kappa := by
  have hk0 : kappa ≠ 0 := ne_of_gt hkappa
  have hE1 : (1 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_max_left _ _
  have hE0 : (0 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_trans zero_le_one hE1
  have hq0 : (0 : ℝ) ≤ p / kappa := div_nonneg hp hkappa.le
  have hexp : p / kappa * kappa = p := by field_simp
  have hEp : (max 1 (witnessEccentricity (symmPart abar))) ^ p =
      (eccentricityFoldFactor abar (p / kappa)) ^ kappa := by
    rw [← max_one_witnessEccentricity_rpow_eq_fold abar hq0,
      ← Real.rpow_mul hE0, hexp]
  have hfold00 : (0 : ℝ) ≤ eccentricityFoldFactor abar p0 :=
    (eccentricityFoldFactor_pos abar p0).le
  have hfoldq0 : (0 : ℝ) ≤ eccentricityFoldFactor abar (p / kappa) :=
    (eccentricityFoldFactor_pos abar _).le
  have hbase0 : (0 : ℝ) ≤
      epsilon * (x * (Lg * eccentricityFoldFactor abar p0)) :=
    mul_nonneg heps (mul_nonneg hx (mul_nonneg hLg hfold00))
  have hswap : eccentricityFoldFactor abar (p / kappa) *
        (epsilon * (x * (Lg * eccentricityFoldFactor abar p0))) =
      epsilon * (x * (Lg * (eccentricityFoldFactor abar p0 *
        eccentricityFoldFactor abar (p / kappa)))) := by ring
  have hprod0 : (0 : ℝ) ≤ epsilon * (x * (Lg *
      (eccentricityFoldFactor abar p0 *
        eccentricityFoldFactor abar (p / kappa)))) :=
    mul_nonneg heps (mul_nonneg hx (mul_nonneg hLg
      (mul_nonneg hfold00 hfoldq0)))
  have hsum : epsilon * (x * (Lg * (eccentricityFoldFactor abar p0 *
        eccentricityFoldFactor abar (p / kappa)))) ≤
      epsilon * (x * (Lg *
        eccentricityFoldFactor abar (p0 + p / kappa))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (RootInterface.eccentricityFoldFactor_mul_le abar hp0 hq0) hLg) hx) heps
  calc (C0 * (max 1 (witnessEccentricity (symmPart abar))) ^ p) *
        (epsilon * (x * (Lg * eccentricityFoldFactor abar p0))) ^ kappa
      = C0 * ((eccentricityFoldFactor abar (p / kappa)) ^ kappa *
          (epsilon * (x * (Lg * eccentricityFoldFactor abar p0))) ^ kappa) := by
        rw [hEp]; ring
    _ = C0 * ((eccentricityFoldFactor abar (p / kappa) *
          (epsilon * (x * (Lg * eccentricityFoldFactor abar p0)))) ^ kappa) := by
        rw [Real.mul_rpow hfoldq0 hbase0]
    _ = C0 * ((epsilon * (x * (Lg * (eccentricityFoldFactor abar p0 *
          eccentricityFoldFactor abar (p / kappa))))) ^ kappa) := by
        rw [hswap]
    _ ≤ C0 * ((epsilon * (x * (Lg *
          eccentricityFoldFactor abar (p0 + p / kappa)))) ^ kappa) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hprod0 hsum hkappa.le) hC0

end

end RowSupply
end HighContrast
end HCPolySupport
