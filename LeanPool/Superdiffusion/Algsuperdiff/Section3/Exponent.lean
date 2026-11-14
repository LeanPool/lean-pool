/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity

/-!
# Exponent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3 coarse-ellipticity exponents

This file fixes the admissible finite-or-infinite exponent carrier and the
source window used by the Section 3 coarse-ellipticity statements, together
with the source-corrected deterministic lower-pole amplitude.

## Main definitions

* `CoarseEllipticityExponent`: the admissible subtype of CoarseGraining's
  multiscale exponent carrier.
* `lowerEllipticityProfile`: the source-corrected total deterministic lower
  profile on raw parameters.

## References

* ABK26, Proposition `p.cg.ellipticity.bounds`.
-/

namespace Algsuperdiff.Section3

/-- The exact admissible carrier for the source range `q ∈ [1, infinity]`: finite
CoarseGraining multiscale exponents at least one, together with the infinity
endpoint. -/
def CoarseEllipticityExponent :=
  {q : HCPolySupport.Book.Ch02.MultiscaleExponent // q.IsAdmissible}

namespace CoarseEllipticityExponent

/-- An admissible finite coarse-ellipticity exponent. -/
def finite (q : {q : ℝ // 1 ≤ q}) : CoarseEllipticityExponent :=
  ⟨.finite q, q.property⟩

/-- The admissible infinity endpoint. -/
def infinity : CoarseEllipticityExponent :=
  ⟨.infinity, trivial⟩

end CoarseEllipticityExponent

/-- The total deterministic lower-ellipticity profile in the
supersession-resolved Section 3.3 source. At finite exponents below `2`, the
pole has order `2 / q`; at finite exponents at least `2`, it has order one;
the infinity endpoint is the direct constant bound.

Positivity of `2 * s - gamma` is a theorem-side consequence of the source
window. It is deliberately not stored in this definition's arguments, so a
frozen source statement can quantify the manuscript's raw `s : ℝ` without a
proof-valued carrier or an equality premise. -/
noncomputable def lowerEllipticityProfile (C gamma s : ℝ)
    (q : CoarseEllipticityExponent) : ℝ :=
  match q.1 with
  | .finite q =>
      if q < 2 then
        C * Real.rpow (s / (2 * s - gamma)) (2 / q)
      else
        C * s * (2 * s - gamma)⁻¹
  | .infinity => C

end Algsuperdiff.Section3
