/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHatDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.CorrectedTiltEndpoint

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHcoreEndpoint

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hcore` endpoint of Proposition 4.2

The last link of the endgame.  `Prop42Scalar.exists_power_bounded_unit_decay_
of_corrected_tilt` turns

* the hatted decay `hhat` at every generation past `2N₀`, and
* the outer transfer `htransfer` over the whole admissible range,

into exactly the inner conclusion of the `hcore` binder of the tree's
`Quenched.exists_annealed_endpoint_telescope_of_contrast_decay`
(the cited theorem):

```
∃ m₀ : ℕ, (3 : ℝ) ^ m₀ ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay ∧
  ∀ j : ℕ, annealedContrast Pbase ((m₀ + j : ℕ) : ℤ) - 1 ≤ 3 ^ (-alpha * (j : ℝ))
```

This file supplies the two shapes that link into it: the `∀ n ≥ 2N₀` form of
the hatted decay (from the delayed recursion), and the composition itself.

A structural confirmation worth recording: the tree's `hcore` binder fixes the
base law's Dagger exponent to `gBase = (1 + g)/2` — which is *exactly*
`contrastRho g` of the corresponding argument.  The exponent pairing `ρ = (1+g)/2`, `α = (1-g)/4`
forced by the weak value's own weights is the one the endpoint already
expects.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The `hcore` inner conclusion of Proposition 4.2.**  From the hatted decay
and the outer transfer — the two shapes the construction now supplies — the annealed
contrast decays geometrically past a `Π`-polynomially bounded entry
generation.  This is exactly the body of the `hcore` binder of
`Quenched.exists_annealed_endpoint_telescope_of_contrast_decay`. -/
theorem exists_annealed_decay_of_hhat_and_transfer
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ : ℕ}
    {Aerr kappa base Centry Cpref : ℝ}
    (hA : 0 ≤ Aerr) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry)
    (hpref : Aerr * (Real.rpow (3 : ℝ) (kappa / 2) + 1) ≤ Real.rpow base Cpref)
    (hhat : ∀ n : ℕ, 2 * N₀ ≤ n →
      (9 / 2 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q (n : ℤ) - 1)) ≤
        Aerr * Real.rpow (3 : ℝ) (-kappa * ((n - 2 * N₀ : ℕ) : ℝ)))
    (htransfer : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          Aerr * Real.rpow (3 : ℝ)
            (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤ Real.rpow base (Centry + (1 + Cpref / (kappa / 2))) ∧
        ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
          Real.rpow (3 : ℝ) (-(kappa / 2) * (j : ℝ)) :=
  Prop42Scalar.exists_power_bounded_unit_decay_of_corrected_tilt
    (F := fun j => annealedContrast P (j : ℤ) - 1)
    (Fhat := fun j =>
      (9 / 2 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q (j : ℤ) - 1)))
    hA hkappa hkappa1 hbase hCpref hentry hpref hhat htransfer

end

end HCPolySupport.HighContrast.Quenched
