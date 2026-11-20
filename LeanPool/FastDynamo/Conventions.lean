/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Global conventions

This module freezes the torus, scalar, vector, and complex-inner-product
conventions used throughout the formalisation.
-/

@[expose] public section

namespace FastDynamo

/-- The additive unit `d`-torus `ℝᵈ/ℤᵈ`.  Its `volume` is the Haar probability measure, i.e.
the Lebesgue measure with which the paper equips `T³ = ℝ³/ℤ³`. -/
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)

/-- The axial unit circle used by the paper's `x₃` Fourier modes. -/
abbrev AxialCircle := UnitAddCircle

/-!
## Terminology: `transverse` in Lean, "horizontal" in the paper

The paper calls the `y = (x₁, x₂)` directions **horizontal** and the `x₃` direction axial
(§1.1: "We call the `y`-directions horizontal and the `x₃`-direction axial", "The subscript
`⊥` denotes horizontal components or differential operators acting in the horizontal
variables").  The Lean identifiers of this development say *transverse* for the same
directions:
`TransverseTorus`, `TransverseRealW1Inf`, `IsTransverseDivergenceFree`,
the `FastDynamo/Analysis/Transverse*` modules, the `⊥`-subscripted operators.

The two words denote the same thing: `transverse` in a Lean name means exactly the paper's
"horizontal", and `TransverseTorus` is the paper's horizontal torus `𝕋² = ℝ²/ℤ²`.  The prose
follows the paper and says "horizontal"; the identifiers say `Transverse`.  `Axial` carries
the same meaning in both.

### Growth rates: the paper's symbols and the Lean names

The paper uses several growth rates and they are not interchangeable.  The dictionary,
paper symbol first:

* `γ(u, ε)`, `eq:semigroup-growth-rate` — `FastDynamo.gamma`, the growth bound of the
  semigroup generated on `L²_σ` by `L_{ε,u}` with domain `H² ∩ L²_σ`
  (`FastDynamo.generator_solenoidalInductionSemigroup`), on the product model `T² × T` with an
  axially independent velocity, transported to the literal three-torus.  It is defined as a
  `limsup` and proved to be the paper's limit (`FastDynamo.gamma_eq_lim`) and the spectral
  bound of `L_{ε,u}` (`FastDynamo.gamma_eq_iSup_re_spectrum`).
* `γ(u, ·)` read as a function of `ε` on `(0, ∞)` — `FastDynamo.gammaOf`, the total extension
  (`gamma` carries `0 < ε` as an argument, so a filter limit in `ε` needs one);
  `FastDynamo.gammaOf_eq_gamma` identifies the two.
* `γ_id(u)`, `eq:zero-ideal-growth` (`cor:ideal-growth`) —
  `FastDynamo.HasVanishingIdealOperatorGrowthRate`.
* the per-datum ideal rate (the last sentence of `cor:ideal-growth`) —
  `FastDynamo.HasVanishingIdealGrowthRate`.
* `𝒯₀(t)` (§1.2, before `thm:main`) — the group `T` of `FastDynamo.IsIdealInductionGroup`, the
  unique solution group of the ideal induction equation in the sense of
  `FastDynamo.IsIdealSolutionGroup`; at the theorem's velocity, `FastDynamo.mainIdealGroup`.
* `L²_σ(𝕋³) = {B ∈ L²(𝕋³; ℂ³) : Div B = 0}` (§1.1) —
  `FastDynamo.literalSolenoidalSubspace`, the *transported* Fourier subspace rather than an
  intrinsic `{Div B = 0}`; it is characterised on `Torus 3` by `Div B = 0` tested against the
  characters (see its docstring).
* `Lip(F)` (§1.2) — `FastDynamo.lipConst`, an `sInf` that is not proved to be attained (and
  does not need to be).
* `h_top(F)` (§1.2) — `Dynamics.coverEntropy F Set.univ`, through
  `FastDynamo.HasZeroTopologicalEntropy`.

The model behind the first entry (the product torus and an axially independent velocity) and
the sixth entry are deviations of the formalisation from the paper and are recorded as such in
`DEVIATIONS.md`; the docstrings of `FastDynamo.gamma` and
`FastDynamo.literalSolenoidalSubspace` say precisely what is and is not proved about them.

### The axial wavenumber `N`

The paper carries no axial wavenumber as a parameter: it works at `N = 2π` and writes `4π²`,
`2π i` and `ℓ_n = 1/K_n` out in full (the operator `A_w` of §2.1, `eq:local-generator`, §3.2).
The Lean development keeps the symbol: `FastDynamo.LocalSeedParameters.wavenumber` is `N = 2π k_*`
with `k_*` a positive natural-number field, `FastDynamo.wholePlaneAxialWavenumber K` is `2π K`,
and the concrete inhabitant is taken at `k_* = 1`, hence at `N = 2π`
(`FastDynamo.HorizontalMode.exists_localSeedC2_two_pi`).

So every statement of this development that names `N` is the paper's at `k_* = 1` and is
*more general* otherwise; nothing is weaker.  Keeping `k_*` free costs nothing and is what
makes the scaling lemma `lem:exact-renormalization` a statement about an arbitrary
scale family.  A docstring that writes `N²` or `κ² − N²` where the paper prints `4π²` is
saying the same thing at `k_* = 1`.  The blueprint records the same note under
`def:local:smoothed-velocity`.
-/

/-- The transverse two-torus — the paper's *horizontal* torus `𝕋²` (§1.1). -/
abbrev TransverseTorus := Torus 2

/--
The product model of the three-torus used throughout the development: the
transverse two-torus times the axial circle.  The operator theory and the
induction equation are stated in this model; the measure-preserving
identification with the literal `Torus 3` is built in
`FastDynamo.Analysis.LiteralThreeTorus` and used only to transport the final
magnetic clauses and the velocity.
-/
abbrev ProductTorus3 := TransverseTorus × AxialCircle

/-- Three-dimensional real Euclidean space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Three-dimensional complex Euclidean space. -/
abbrev C3 := EuclideanSpace ℂ (Fin 3)

/-- Raw transverse complex amplitudes used by the theorem specification. -/
abbrev AxialAmplitudeRaw := TransverseTorus → C3

/--
The paper's inner-product convention, linear in the first argument.
Mathlib's `inner` is conjugate-linear in the first argument, so the arguments
are reversed here.
-/
def paperInner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) : ℂ :=
  inner ℂ y x

/--
Evaluating the paper's inner product on a vector against itself returns the squared norm,
coerced to `ℂ`; the reversal of arguments in `paperInner` is invisible on the diagonal.
-/
@[simp] theorem paperInner_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x : E) : paperInner x x = (‖x‖ : ℂ) ^ 2 := by
  simp [paperInner]

/-!
## The `abbrev` reducibility contract of the derived parameter accessors

The parameter chain of `FastDynamo/Global/GlobalParameterChoice.lean` exposes all of its
derived data as `abbrev`s, on both of its records.  On the seed-side interface
`GlobalSeedInterface`: `S.contour`, `S.growthFloor`, `S.imBound`, `S.profileSupportRadius`,
`S.placementRadius`, `S.coercivityConstant`.  On the parameter record
`GlobalParameterChoice` itself: `Theta.placement`, `Theta.scaleFamily`, `Theta.baseIndex`,
`Theta.tau`, `Theta.axialAmplitude`, `Theta.eps0`, `Theta.fourierIndex`.
**The `@[reducible]` attribute an `abbrev` carries is part of the interface.**

The accessors form a chain — `Theta.scaleFamily` is `Theta.placement.scaleFamily`, and
`Theta.placement` is `Theta.jointPlacement.restrictSupportRadius
S.profileSupportRadius_le_placementRadius`, a restriction that leaves the `scaleFamily` field
untouched (`ScaleFamily.TorusCellPlacement.restrictSupportRadius_scaleFamily`,
`FastDynamo/Global/TorusCellPlacement.lean`, proved by `rfl`).  The final proofs use the
accessors as mere abbreviations of the underlying record fields: `Theta.scaleFamily` stands in
binder types such as `ScaleFamily.MatchingCell Theta.scaleFamily epsilon`, and identities of the
derived data are discharged by `rfl` against the unfolded form — for example
`have hR : Theta.scaleFamily.bufferRadius c.index = Real.sqrt (Theta.scaleFamily.ell c.index)`
`:= rfl` in `FastDynamo/Global/GlobalParameterChoiceConcrete.lean`.  `simp`, `rw`, instance
synthesis and the arithmetic tactics are expected to see through the accessors without being
told to unfold them.  Definitional unfolding at default transparency would survive a change to
`def`, but the reducible-transparency matching of `simp` lemmas, `rw` motives, instance
arguments and tactic atoms would not.  The derived accessors of the parameter record are
therefore `abbrev`s; turning one into a `def` affects the proofs of the main parameter chain
(`GlobalParameterChoiceConcrete`, `TorusSelectedWitness`, `GlobalSpectralTransferConcrete`,
`TorusGlobalRieszNonzero`).

## Positivity hypotheses never appear on a `def`

A sign or positivity hypothesis — `0 ≤ tau`, `0 < N`, essential boundedness of a symbol — is a
hypothesis of the **theorems**, never an argument of the **definition** they are about.  When a
definition is only meaningful under such a hypothesis, branch on the proposition itself with the
`dite` device

```lean
def f (t : ℝ) : F :=
  @dite _ (P t) (Classical.propDecidable _) (fun hP ↦ value hP) fun _ ↦ 0

theorem f_eq (hP : P t) : f t = value hP := dite_eq_left hP
```

and state the recovery lemma `f_eq` next to it; every downstream statement then carries the
hypothesis exactly once, as a hypothesis, and the check surface shows a type with no proof
argument in it.

The definitions that follow this rule are `PeriodizedPlaneFlowData.symbolLInf`
(`FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean`), on which the transports `idealTransport`
and `idealTruncatedTransport` are built, and `idealGroup`
(`FastDynamo/Dynamics/Ideal/SolenoidalInvariance.lean`), with recovery lemmas
`symbolLInf_eq_toLp` and `idealGroup_eq_codRestrict`.
-/

end FastDynamo
