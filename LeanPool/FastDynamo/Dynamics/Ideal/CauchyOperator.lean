/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.MeasurePreserving
public import LeanPool.FastDynamo.Dynamics.Flow.FlowDerivative

/-!
# The Cauchy transport operator of the ideal induction equation

The paper defines the ideal induction solution group, in the proof of `cor:ideal-growth`, by
the **Cauchy formula** `eq:ideal-cauchy-formula`

```
  (𝒯₀(t) B)(Φ_t(a)) = DΦ_t(a) B(a)        for almost every a,
```

which, read at `x = Φ_t(a)` rather than at `a`, is the pointwise multiplier

```
  (𝒯₀(t) B)(x) = DΦ_t(Φ_{-t}(x)) · B(Φ_{-t}(x)).
```

`FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean` builds that operator generically over a
`PeriodizedPlaneFlowData`: the **symbol** is the complexified derivative flow read at the
pre-image `Φ_{-t}(x)`, the transport is pointwise multiplication by its `L^∞` class composed with
the measure-preserving substitution `B ↦ B ∘ Φ_{-t}`, and the group law
`𝒯₀(s + t) = 𝒯₀(s) 𝒯₀(t)` is the chain rule of the symbol.  This module reads
those off at `fullFlowData`.

## Contents

* `idealSymbol`, `norm_idealSymbol_le`, `memLp_idealSymbol` — the operator-valued symbol
  `DΦ_t ∘ Φ_{-t}`, its uniform bound and its membership in `L^∞(T³; ℂ³ →L[ℂ] ℂ³)`; the symbol is
  discontinuous at the accumulation circle, so the transport multiplies by its `L^∞` class
  through `operatorMulL2` (`FastDynamo/Analysis/BoundedOperatorMultiplier.lean`).
* `idealTransport` — the transport operator on `LiteralC3L2 = L²(T³; ℂ³)`, with its almost
  everywhere representative `idealTransport_coe_ae`, the per-datum bound
  `norm_idealTransport_apply_le` and the group laws `idealTransport_zero`, `idealTransport_add`.
* `idealTransport_cauchy` — the Cauchy formula in exactly the shape of the `cauchy` clause of
  `IsIdealInductionGroup` (`FastDynamo/Dynamics/ParticleFlow.lean`), stated on the whole of
  `LiteralC3L2`; the solenoidal subspace is imposed later.
* `norm_le_mul_norm_idealTransport` — the per-datum lower bound of `cor:ideal-growth` (proved in
  the last step of its proof).

## The essential boundedness hypothesis

The uniform bound on `DΦ_t` (`norm_flowFDerivC_le`) carries the hypothesis `0 ≤ tau` of the
axial profile, so `MemLp (idealSymbol … t) ∞ volume` is available only under `htau : 0 ≤ tau`.
The operator `idealTransport … t` must nevertheless be a plain function of the time, because
every later module states its results about `idealTransport … t` itself; the generic
`PeriodizedPlaneFlowData.symbolLInf` is therefore defined by a case distinction on that `MemLp`
hypothesis, and the almost everywhere identification — hence `idealTransport_coe_ae`,
`idealTransport_add` and the two bounds — carries `htau`.  Only `idealTransport_zero` has no
hypothesis: at `t = 0` the symbol is the identity, which is essentially bounded for free.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The constant -/

/-- The `L^∞` symbol bound is even in the time, because the derivative bound of
`FastDynamo/Dynamics/Flow/FlowDerivative.lean` is. -/
theorem flowComplexDerivativeBound_neg (t : ℝ) :
    flowComplexDerivativeBound h P angularSpeed axialSpeed tau (-t) =
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t := by
  rw [flowComplexDerivativeBound, flowComplexDerivativeBound, flowDerivativeBound_neg]

/-! ## The symbol of the Cauchy transport -/

/-- **The symbol of the Cauchy transport** (`eq:ideal-cauchy-formula`): the
complexified derivative flow `DΦ_t ⊗ ℂ` read at the pre-image `Φ_{-t}(x)`, so that the Cauchy
formula `(𝒯₀(t)B)(Φ_t a) = DΦ_t(a) B(a)` becomes the pointwise multiplier
`(𝒯₀(t)B)(x) = idealSymbol … t x (B (Φ_{-t} x))`. -/
abbrev idealSymbol (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).symbol t x

/-- The symbol is the complexified derivative flow read at the pre-image. -/
theorem idealSymbol_eq (t : ℝ) (x : Torus 3) :
    idealSymbol h P angularSpeed axialSpeed tau t x =
      flowFDerivC h P angularSpeed axialSpeed tau t
        (literalFlow h P angularSpeed axialSpeed tau (-t) x) := rfl

/-- **The uniform bound on the symbol**: the symbol is bounded by
`flowComplexDerivativeBound … t = 24 (1 + |t| · flowLipschitzSlope …)` at every point. -/
theorem norm_idealSymbol_le (htau : 0 ≤ tau) (t : ℝ) (x : Torus 3) :
    ‖idealSymbol h P angularSpeed axialSpeed tau t x‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t :=
  norm_flowFDerivC_le h P angularSpeed axialSpeed tau htau t _

/-- The symbol is essentially bounded, so it defines a class in `L^∞(T³; ℂ³ →L[ℂ] ℂ³)`. -/
theorem memLp_idealSymbol (htau : 0 ≤ tau) (t : ℝ) :
    MemLp (idealSymbol h P angularSpeed axialSpeed tau t) ∞ (volume : Measure (Torus 3)) :=
  (fullFlowData h P angularSpeed axialSpeed tau).memLp_symbol_of_bound
    (norm_idealSymbol_le h P angularSpeed axialSpeed tau htau t)

/-! ## The transport operator -/

/-- **The Cauchy transport operator `𝒯₀(t)` on `L²(T³; ℂ³)`** (`eq:ideal-cauchy-formula`):
pointwise multiplication by the `L^∞` symbol `DΦ_t(Φ_{-t} ·)`, composed with the
measure-preserving substitution `B ↦ B ∘ Φ_{-t}`.  The restriction to the solenoidal subspace is
imposed by `idealGroup` (`FastDynamo/Dynamics/Ideal/SolenoidalInvariance.lean`). -/
abbrev idealTransport (t : ℝ) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  (fullFlowData h P angularSpeed axialSpeed tau).transport t

/-- **The almost everywhere representative of the Cauchy transport**:
`(𝒯₀(t)B)(x) = DΦ_t(Φ_{-t} x) B(Φ_{-t} x)` for almost every `x`. -/
theorem idealTransport_coe_ae (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    (idealTransport h P angularSpeed axialSpeed tau t B : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ idealSymbol h P angularSpeed axialSpeed tau t x
        ((B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)) :=
  (fullFlowData h P angularSpeed axialSpeed tau).transport_coe_ae
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau t) B

/-- **The per-datum upper bound** `‖𝒯₀(t)B‖₂ ≤ C(1 + |t|) ‖B‖₂` (the display after
`eq:ideal-cauchy-formula`, with `Lip(Φ_t)` bounded by `prop:particle-flow`): Hölder's
estimate for the `L^∞` symbol, together with the isometry of the substitution. -/
theorem norm_idealTransport_apply_le (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    ‖idealTransport h P angularSpeed axialSpeed tau t B‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t * ‖B‖ :=
  (fullFlowData h P angularSpeed axialSpeed tau).norm_transport_apply_le
    (flowComplexDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau t)
    (norm_idealSymbol_le h P angularSpeed axialSpeed tau htau t) B

/-- **The identity at time zero**: `𝒯₀(0) = id`.  No hypothesis on `tau` is needed. -/
theorem idealTransport_zero :
    idealTransport h P angularSpeed axialSpeed tau 0 = ContinuousLinearMap.id ℂ LiteralC3L2 :=
  (fullFlowData h P angularSpeed axialSpeed tau).transport_zero

/-- **The group law** `𝒯₀(s + t) = 𝒯₀(s) 𝒯₀(t)` (the proof of `cor:ideal-growth`), from the
cocycle identity of the symbol and the flow law. -/
theorem idealTransport_add (htau : 0 ≤ tau) (s t : ℝ) :
    idealTransport h P angularSpeed axialSpeed tau (s + t) =
      (idealTransport h P angularSpeed axialSpeed tau s).comp
        (idealTransport h P angularSpeed axialSpeed tau t) :=
  (fullFlowData h P angularSpeed axialSpeed tau).transport_add
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau s)
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau t)
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau (s + t))

/-! ## The Cauchy clause and the per-datum lower bound -/

/-- **The Cauchy formula in the shape of the `cauchy` clause of `IsIdealInductionGroup`**
(`FastDynamo/Dynamics/ParticleFlow.lean`, `eq:ideal-cauchy-formula`): for almost
every `a` and every coordinate `i`,

```
  (𝒯₀(t)B)(Φ_t a)ᵢ = ∑ⱼ (DΦ_t(a) e_j)ᵢ B(a)ⱼ .
```

It is stated on the whole of `LiteralC3L2`; the assembly restricts it to the solenoidal
subspace. -/
theorem idealTransport_cauchy (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    ∀ᵐ a : Torus 3, ∀ i : Fin 3,
      (idealTransport h P angularSpeed axialSpeed tau t B : Torus 3 → C3)
          (literalFlow h P angularSpeed axialSpeed tau t a) i =
        ∑ j : Fin 3, ((flowFDeriv h P angularSpeed axialSpeed tau t a
            (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * (B : Torus 3 → C3) a j :=
  (fullFlowData h P angularSpeed axialSpeed tau).transport_cauchy
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau t) B

/-- **The per-datum lower bound** of `cor:ideal-growth` (proved in the last step of its
proof): `‖B‖₂ = ‖𝒯₀(-t)𝒯₀(t)B‖₂ ≤ C(1 + |t|) ‖𝒯₀(t)B‖₂`. -/
theorem norm_le_mul_norm_idealTransport (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    ‖B‖ ≤ flowComplexDerivativeBound h P angularSpeed axialSpeed tau (-t) *
      ‖idealTransport h P angularSpeed axialSpeed tau t B‖ :=
  (fullFlowData h P angularSpeed axialSpeed tau).norm_le_mul_norm_transport
    (flowComplexDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau (-t))
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau t)
    (memLp_idealSymbol h P angularSpeed axialSpeed tau htau (-t))
    (norm_idealSymbol_le h P angularSpeed axialSpeed tau htau (-t)) B

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
