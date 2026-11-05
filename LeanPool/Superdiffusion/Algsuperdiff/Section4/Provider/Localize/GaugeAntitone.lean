/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ExponentMonotonicity

/-!
# GaugeAntitone

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Antitonicity of the gauge `λ_{s,q}^{-1}` in the exponent `s`

ABK26, `e.ellipticities.monotone.ordered`, read in the inverted direction.

## Why this file exists

The event side of that trade is free, and this file is the reason: a **larger**
gauge exponent puts **less** weight on the deep scales, so

```
λ_{s,q}^{-1}(Q; a) ≤ λ_{γ,q}^{-1}(Q; a)      whenever  0 < γ ≤ s .
```

Hence every `γ`-gauge upper bound the good event supplies is automatically an
`s`-gauge upper bound, at constant `1`.

## References

* ABK26, `e.ellipticities.monotone.ordered`.
-/

namespace Algsuperdiff.Section4.Provider.Localize

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- **Gauge antitonicity of `λ^{-1}`** (the inverted first inequality of
`e.ellipticities.monotone.ordered`).  For `0 < t ≤ s` and admissible `q`,

```
λ_{s,q}^{-1}(Q; a) ≤ λ_{t,q}^{-1}(Q; a) .
```

A larger gauge exponent discounts the deep scales more heavily, and the
per-depth maxima are nondecreasing in the depth, so raising the exponent can
only decrease the gauge's inverse.  Constant `1`; no cube, field or dimension
enters. -/
theorem inv_lambdaSq_antitone_gauge [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t s : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (ht : 0 < t) (hts : t ≤ s)
    (hq : q.IsAdmissible) :
    (Book.Ch02.lambdaSq Q s q a)⁻¹ ≤ (Book.Ch02.lambdaSq Q t q a)⁻¹ := by
  rcases eq_or_lt_of_le hts with heq | hlt
  · rw [heq]
  · exact inv_anti₀ (Book.Ch02.lambdaSq_pos Q a ht hq)
      (Algsuperdiff.Section3.Provider.ErrorComparison.lambdaSq_mono_of_lt Q a ht
        hlt hq)

/-- **The finite-`q` instance at `q = 2`**, the only exponent §4.1 uses. -/
theorem inv_lambdaSq_two_antitone_gauge [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ ≤
      (Book.Ch02.lambdaSq Q t (.finite 2) a)⁻¹ :=
  inv_lambdaSq_antitone_gauge Q a ht hts (by norm_num)

end

end Algsuperdiff.Section4.Provider.Localize
