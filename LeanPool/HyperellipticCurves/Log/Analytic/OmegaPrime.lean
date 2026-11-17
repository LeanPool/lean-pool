/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion
public import LeanPool.HyperellipticCurves.Series.FormalGroupLaw.Log
public import LeanPool.HyperellipticCurves.Series.LogIso

import LeanPool.HyperellipticCurves.ForMathlib.MvPowerSeriesPDeriv

/-!
# The pullback of the invariant differential along a formal path (`thm:omega-prime-global`)

For a formal group law `Φ` over `O` and a formal path `z ↦ ζ(z)` (an `ι`-tuple of power
series in `O⟦z⟧` with substitutable, e.g. vanishing, constant terms), the differential
`ω′_i = ∑_j (M⁻¹)_{ij}(ζ(z)) · ζ_j′(z)` (`ChabautyColeman.omegaPrime`) is the pullback
of the `i`-th invariant differential of `Φ` along the path. It is **integral** — defined
over `O`, because the inverse Jacobian `M⁻¹` is — and over a field of characteristic
zero it equals `d/dz Λ_i(ζ(z))` for the formal logarithm `Λ`
(`ChabautyColeman.pderiv_subst_log`, the formal chain rule).

Moreover `Λ_i(ζ(z))` is the **formal integral of `ω′` from the disk center**
(`ChabautyColeman.subst_log_eq_antideriv`): the substitution of the path into the formal
logarithm is the zero-based antiderivative of `ω′` — the formal core of clause (b) of
`thm:omega-prime-global`.

Applied to `ζ = ChabautyColeman.phiZeta` (the disk chart coordinates of `def:phiD`,
substitutable by `ChabautyColeman.constantCoeff_phiZeta`) and `Φ` the translated formal
group law `ChabautyColeman.ftauFoldFGL`, this realizes `ω′` of blueprint
`thm:omega-prime-global` on a residue disk.
-/

@[expose] public section

open MvPowerSeries

namespace ChabautyColeman

section OmegaPrime

open scoped PowerSeries

variable {O O' : Type*} [CommRing O] [CommRing O'] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The pullback of the invariant differential along a formal path** (the `ω′` of
blueprint `thm:omega-prime-global`): for a path `z ↦ ζ(z)` with coordinates in `O⟦z⟧`
and a formal group law `Φ`, the series `ω′_i = ∑_j (M⁻¹)_{ij}(ζ(z)) · ζ_j′(z)`. Over a
field of characteristic zero this is `d/dz Λ_i(ζ(z))`
(`ChabautyColeman.pderiv_subst_log`), but the definition is integral: it lives over
`O`. -/
noncomputable def omegaPrime (Φ : FormalGroupLaw O ι) (ζ : ι → O⟦X⟧) (i : ι) : O⟦X⟧ :=
  ∑ j, MvPowerSeries.subst ζ (Φ.diffMatrix⁻¹ i j) * MvPowerSeries.pderiv () (ζ j)

variable {K : Type*} [Field K] [CharZero K]

/-- **The formal chain rule for the logarithm along a path** (blueprint
`thm:omega-prime-global`, formal core of clause (b)): `d/dz Λ_i(ζ(z)) = ω′_i(z)`. -/
theorem pderiv_subst_log (Φ : FormalGroupLaw K ι) {ζ : ι → K⟦X⟧} (hζ : HasSubst ζ)
    (i : ι) :
    MvPowerSeries.pderiv () (MvPowerSeries.subst ζ (Φ.log i)) = omegaPrime Φ ζ i := by
  rw [omegaPrime, pderiv_subst hζ]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Φ.pderiv_log i j]

end OmegaPrime

section AntiderivCore

open scoped PowerSeries

/-- The partial derivative in the unique variable is the univariate formal derivative. -/
theorem pderiv_unit_eq_derivative {R : Type*} [CommRing R] (g : R⟦X⟧) :
    MvPowerSeries.pderiv () g = PowerSeries.derivative g := by
  ext n
  rw [PowerSeries.coeff_derivative]
  change MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv () g) = _
  rw [coeff_pderiv, Finsupp.single_apply, ite_eq_left rfl, ← Finsupp.single_add]
  rfl

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`Λ(ζ(z))` is the formal integral of `ω′` from the disk center** (blueprint
`thm:omega-prime-global`(b), formal core): the substitution of the path into the formal
logarithm is the antiderivative (with zero constant term) of the pullback `ω′` of the
invariant differential. -/
theorem subst_log_eq_antideriv (Φ : FormalGroupLaw K ι) {ζ : ι → K⟦X⟧}
    (hζ0 : ∀ j, PowerSeries.constantCoeff (ζ j) = 0) (i : ι) :
    MvPowerSeries.subst ζ (Φ.log i) = antideriv (omegaPrime Φ ζ i) := by
  have hζ : HasSubst ζ := hasSubst_of_constantCoeff_zero hζ0
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [← pderiv_unit_eq_derivative, pderiv_subst_log Φ hζ i, derivative_antideriv]
  · rw [constantCoeff_antideriv]
    exact constantCoeff_subst_eq_zero hζ hζ0 (Φ.constantCoeff_log i)

end AntiderivCore

end ChabautyColeman

end
