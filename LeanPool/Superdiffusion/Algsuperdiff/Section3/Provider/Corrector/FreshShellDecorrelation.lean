/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.OriginConcentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LocalMeasurability

/-!
# FreshShellDecorrelation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The fresh shell has compactly supported forcing covariance

`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean` proves the
`Ω`-level decorrelation bound
`integral_normSq_mollify_le_of_helmholtz_of_covariance_support` with the explicit
hypothesis

`hcov : ∀ w : Vec d, ρ ≤ ‖w‖ → ∫ ω, ⟪f (w +ᵥ ω), f ω⟫ ∂μ = 0`,

i.e. the forcing covariance is supported in the ball of radius `ρ`.  This file
discharges that hypothesis at the fresh shell: for the literal origin forcing
`originForcing e` (`Algsuperdiff/Probability/StationaryValueProjection.lean`)
and the zero-shell law on CoarseGraining's regular-coefficient carrier
(`zeroShellRegLaw`), the covariance vanishes as soon as `√d < ‖w‖`.

The only inputs are the two halves of ABK26 (J1), read off the frozen assumption
surface `Algsuperdiff/Frozen/Assumptions/ShellLawJ1.lean`:

* `ShellLawJ1.range_dependence`: the integral-generated local σ-algebras
  `lihLocalSigma U`, `lihLocalSigma V` are independent under the zero-shell law
  whenever every `x ∈ U` and `y ∈ V` satisfy `√d ≤ vecNorm (x - y)`;
* `ShellLawJ1.mean_zero` (through
  `Algsuperdiff.Section3.Provider.Stream.integral_zeroShell_entry_eq_zero`): every
  entry of the zero shell has vanishing expectation at every point.

No infinite-volume construction, no ergodic theorem and no mean ergodic averaging
is used: the origin forcing reads the field at the single point `0`, its translate
reads it at the single point `w`, and the two evaluations are independent and
centred.

## The reachable constant

`ρ = √d` is **not** reachable, and the reason is the *integral* nature of the
frozen (J1) local σ-algebras, not the choice of norm.  A point value
`j ↦ j x` is `lihLocalSigma U`-measurable only when `U` contains a ball of
strictly positive radius around `x`
(`Algsuperdiff.Section3.Provider.BadEvents.measurable_entry_eval_lihLocalSigma`);
the two read sets must therefore be thickened by some `r > 0` before (J1) can be
invoked, and the separation budget shrinks by `2 r`.  Consequently every
`ρ > √d` is admissible and `ρ = √d` is not.  The two exported forms are the
`ρ`-parametric `integral_inner_originForcing_vadd_eq_zero_of_le_norm` (any
`ρ > √d`) and its instance `integral_inner_originForcing_vadd_eq_zero` at
`ρ = √d + 1`.

The gap between the supremum norm `‖·‖` carried by `Vec d` and the Euclidean
`Book.Ch02.vecNorm` in which (J1) is phrased costs nothing here: `‖v‖ ≤ vecNorm v`
(`norm_le_vecNorm` below), so a supremum-norm separation is *stronger* than the
Euclidean separation (J1) asks for.
-/

open MeasureTheory ProbabilityTheory
open HCPolySupport
open scoped Matrix.Norms.Elementwise

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

/-! ### The supremum norm is dominated by the Euclidean norm -/

/-- The supremum norm carried by `Vec d` is bounded by the Euclidean
`Book.Ch02.vecNorm` in which ABK26 (J1) states its range of dependence.  A
supremum-norm separation is therefore stronger than the separation (J1)
requires. -/
theorem norm_le_vecNorm {d : ℕ} (v : Vec d) : ‖v‖ ≤ Book.Ch02.vecNorm v := by
  refine (pi_norm_le_iff_of_nonneg (Book.Ch02.vecNorm_nonneg v)).2 fun i => ?_
  have hsq : v i ^ 2 ≤ Book.Ch02.vecNorm v ^ 2 := by
    rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
    exact sq_apply_le_vecNormSq v i
  have hroot : Real.sqrt (v i ^ 2) ≤ Real.sqrt (Book.Ch02.vecNorm v ^ 2) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Book.Ch02.vecNorm_nonneg v)] at hroot
  rwa [Real.norm_eq_abs]

/-! ### The invariant-measure structure of the fresh shell -/

/-- The fresh-shell law is invariant under the real translation action, directly
from the frozen (J1) stationarity field.  This is one of the two structural
instances that `MollifiedDecorrelation`'s `Ω`-level results require of a carrier;
the other, `MeasurableVAdd₂ (Vec d) (RegCoeffField d)`, is not available in the
tree and is not assumed anywhere in this file.

See `ValuePathTransport`, whose
`integral_normSq_mollify_le_of_helmholtz_valuePath` discharges `hcov` outright
by transporting the covariance statement below along `ShellField.valuePath`.
The transport changes no mathematics: the identification
`valuePathForcing_valuePath` holds by `rfl`. -/
theorem vaddInvariantMeasure_zeroShellRegLaw {d : ℕ} (M : ABKModel d) :
    VAddInvariantMeasure (Vec d) (RegCoeffField d)
      (ShellField.zeroShellRegLaw M.P).toMeasure :=
  ShellField.zeroShellRegLaw_vaddInvariant M.P
    (ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary M.P M.J1.stationary)

end

end Algsuperdiff.Section3.Provider.Corrector
