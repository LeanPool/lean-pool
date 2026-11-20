/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow
public import LeanPool.FastDynamo.Analysis.EntropyCriterion

/-!
# Zero topological entropy of the explicit particle flow

`prop:particle-flow` of the paper (in particular the display `h_top(Φ_t) = 0` of its statement)
asserts that every time map of the particle flow of the fast-dynamo velocity has vanishing
topological entropy.  The last paragraph of its proof applies the power rule and the Lipschitz
entropy bound of [HasselblattKatok02, Section 2.5f(3) and Proposition 2.5.5] to
`eq:linear-flow-lipschitz`:
`m h_top(Φ_s) = h_top(Φ_{m s}) ≤ 3 log (C_L (1 + m |s|))`, which vanishes on dividing by `m`.
The formalisation takes a different, quantitative route — linearly growing Lipschitz constants
of the iterates, then a packing bound `s_m(Φ_t, ρ) ≤ C_ρ (1 + m |t|)³` on `T³`, then "a polynomial
has vanishing exponential growth rate" — which reaches the same conclusion without the power rule
or the bound `h ≤ 3 log Lip`.

This module carries out the last step for the flow built in
`FastDynamo/Dynamics/Flow/TorusFlow.lean`.  The two inputs are

* the iterate law `literalFlow_iterate` together with the Lipschitz descent
  `lipschitzWith_literalFlow` (`FastDynamo/Dynamics/Flow/TorusFlow.lean`) and the growth
  estimate `flowLipschitzBound_natCast_mul_le`
  (`FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`), which together say that the `m`-th iterate
  of `Φ_t` is Lipschitz with constant `C_t (1 + m)` for the explicit
  `C_t = 2 max (1, |t| · flowLipschitzSlope …)`;
* the criterion `coverEntropy_eq_zero_of_lipschitz_iterate`
  (`FastDynamo/Analysis/EntropyCriterion.lean`), which converts exactly that hypothesis into the
  vanishing of the entropy.

## Main declarations

* `flowIterateLipschitzConstant` — the constant `C_t` above, with its `ℝ≥0` form
  `flowIterateLipschitzConstantNN` and `flowIterateLipschitzConstantNN_pos`;
* `lipschitzWith_literalFlow_iterate` — `Lip((Φ_t)^[m]) ≤ C_t (1 + m)`, the hypothesis of
  `coverEntropy_eq_zero_of_lipschitz_iterate`;
* `coverEntropy_literalFlow_eq_zero` — `Dynamics.coverEntropy (Φ_t) Set.univ = 0`;
* `hasZeroTopologicalEntropy_literalFlow` — the same fact through the predicate of
  `FastDynamo/Dynamics/ParticleFlow.lean`;
* `forall_hasZeroTopologicalEntropy_literalFlow` — the entropy clause of
  `FastDynamo.MainLagrangianClauses` (`FastDynamo/Dynamics/ParticleFlow.lean`) verbatim.

## The form of the conclusion

The clause is proved in the **cover-entropy** form: `FastDynamo.HasZeroTopologicalEntropy F`
unfolds to `Dynamics.coverEntropy F Set.univ = 0`, the vanishing of Mathlib's entropy computed from
dynamical *covers*.  The paper fixes no definition of `h_top` of its own (§1.2 refers to
[HasselblattKatok02, Section 2.5e] for the entropy of a continuous self-map of a compact metric
space).  On a compact metric space — and `T³` is one —
cover and separated-set entropy agree,
by Mathlib's
`Dynamics.coverEntropy_eq_iSup_netEntropyEntourage`.  That bridge lives in
`Mathlib/Dynamics/TopologicalEntropy/NetEntropy.lean`, is not needed by any clause of
`FastDynamo.MainLagrangianClauses`, and is **not** carried out in this formalisation: the
packing bound of `FastDynamo/Analysis/EntropyCriterion.lean` bounds covers directly and the
matching lower bound `0 ≤ coverEntropy` is Mathlib's `Dynamics.coverEntropy_nonneg`.  So the
identification of the proved statement with the paper's `h_top(Φ_t) = 0` is a standard but
unformalised step.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped NNReal

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- **The linear growth constant of the iterates of `Φ_t`**, `C_t := 2 max (1, |t| L)` with
`L = flowLipschitzSlope h P angularSpeed axialSpeed tau`
(`FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`).

It is the constant of `flowLipschitzBound_natCast_mul_le`: the Lipschitz constant
`flowLipschitzBound … (m t) = 2 (1 + |m t| L)` of the `m`-th iterate `Φ_{m t}` of `Φ_t` is at most
`C_t (1 + m)`.  The `max` with `1` both absorbs the additive `1` of `flowLipschitzBound` and keeps
the constant positive for every real `t`, with no sign hypothesis on `tau` — this is the shape the
criterion of `FastDynamo/Analysis/EntropyCriterion.lean` consumes (the entropy step of the proof
of `prop:particle-flow`). -/
def flowIterateLipschitzConstant (t : ℝ) : ℝ :=
  2 * max 1 (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau)

/-- **The `ℝ≥0` form of `C_t`**, the constant `LipschitzWith` and the entropy criterion of
`FastDynamo/Analysis/EntropyCriterion.lean` take. -/
def flowIterateLipschitzConstantNN (t : ℝ) : ℝ≥0 :=
  2 * max 1 (‖t‖₊ * flowLipschitzSlopeNN h P angularSpeed axialSpeed tau)

/-- `2 ≤ C_t` in `ℝ≥0`, with no hypothesis on `tau`. -/
theorem two_le_flowIterateLipschitzConstantNN (t : ℝ) :
    2 ≤ flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau t := by
  rw [flowIterateLipschitzConstantNN]
  exact le_mul_of_one_le_right zero_le (le_max_left _ _)

/-- `0 < C_t` in `ℝ≥0`, the positivity hypothesis `hC` of the entropy criterion
`coverEntropy_eq_zero_of_lipschitz_iterate` (`FastDynamo/Analysis/EntropyCriterion.lean`). -/
theorem flowIterateLipschitzConstantNN_pos (t : ℝ) :
    0 < flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau t :=
  lt_of_lt_of_le (by norm_num)
    (two_le_flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau t)

/-- The `ℝ≥0` form coerces to `flowIterateLipschitzConstant`. -/
theorem coe_flowIterateLipschitzConstantNN (htau : 0 ≤ tau) (t : ℝ) :
    ((flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau t : ℝ≥0) : ℝ) =
      flowIterateLipschitzConstant h P angularSpeed axialSpeed tau t := by
  rw [flowIterateLipschitzConstantNN, flowIterateLipschitzConstant, NNReal.coe_mul,
    NNReal.coe_max, NNReal.coe_one,
    coe_nnnorm_mul_flowLipschitzSlopeNN h P angularSpeed axialSpeed tau htau]
  norm_num

/-- The growth estimate of `flowLipschitzBound_natCast_mul_le`
(`FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`) written with the constant `C_t` of
`flowIterateLipschitzConstant`: `Lip(Φ_{m t}) ≤ C_t (1 + m)`, the linear growth of
`eq:linear-flow-lipschitz` along the arithmetic
progression `m ↦ m t`. -/
theorem flowLipschitzBound_natCast_mul_le_flowIterateLipschitzConstant (t : ℝ) (m : ℕ) :
    flowLipschitzBound h P angularSpeed axialSpeed tau ((m : ℝ) * t) ≤
      flowIterateLipschitzConstant h P angularSpeed axialSpeed tau t * (1 + m) := by
  rw [flowIterateLipschitzConstant]
  exact flowLipschitzBound_natCast_mul_le h P angularSpeed axialSpeed tau t m

/-- **Linearly growing Lipschitz constants along the iterates.**  The `m`-th iterate of the time-`t`
map `Φ_t` of `FastDynamo/Dynamics/Flow/TorusFlow.lean` is Lipschitz with constant `C_t (1 + m)`.

This is `prop:particle-flow`'s `eq:linear-flow-lipschitz` evaluated along `Φ_t^m = Φ_{m t}` (as
in the entropy step of the proof of `prop:particle-flow`), and it is exactly the hypothesis
of the entropy criterion of `FastDynamo/Analysis/EntropyCriterion.lean`.  The proof is the
iterate law `literalFlow_iterate`, the Lipschitz descent `lipschitzWith_literalFlow` and
`LipschitzWith.weaken` along `flowLipschitzBound_natCast_mul_le_flowIterateLipschitzConstant`. -/
theorem lipschitzWith_literalFlow_iterate (htau : 0 ≤ tau) (t : ℝ) (m : ℕ) :
    LipschitzWith
      (flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau t * (1 + m))
      ((literalFlow h P angularSpeed axialSpeed tau t)^[m]) := by
  rw [literalFlow_iterate]
  refine (lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau ((m : ℝ) * t)).weaken ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast,
    coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau,
    coe_flowIterateLipschitzConstantNN h P angularSpeed axialSpeed tau htau]
  exact flowLipschitzBound_natCast_mul_le_flowIterateLipschitzConstant h P angularSpeed axialSpeed
    tau t m

/-- **Vanishing cover entropy of every time map** (the entropy clause of
`prop:particle-flow`).

`Dynamics.coverEntropy (Φ_t) Set.univ = 0` for every `t : ℝ`, from
`lipschitzWith_literalFlow_iterate` and `coverEntropy_eq_zero_of_lipschitz_iterate`
(`FastDynamo/Analysis/EntropyCriterion.lean`).  See the module docstring for the relation
between this cover form and the entropy the paper refers to
([HasselblattKatok02, Section 2.5e], cited in §1.2). -/
theorem coverEntropy_literalFlow_eq_zero (htau : 0 ≤ tau) (t : ℝ) :
    Dynamics.coverEntropy (literalFlow h P angularSpeed axialSpeed tau t) Set.univ = 0 :=
  coverEntropy_eq_zero_of_lipschitz_iterate
    (flowIterateLipschitzConstantNN_pos h P angularSpeed axialSpeed tau t)
    (lipschitzWith_literalFlow_iterate h P angularSpeed axialSpeed tau htau t)

/-- **Zero topological entropy of every time map**, in the vocabulary of
`FastDynamo.HasZeroTopologicalEntropy` (`FastDynamo/Dynamics/ParticleFlow.lean`):
`h_top(Φ_t) = 0` of `prop:particle-flow`, proved in the
cover form (see the module docstring for the residue this leaves). -/
theorem hasZeroTopologicalEntropy_literalFlow (htau : 0 ≤ tau) (t : ℝ) :
    HasZeroTopologicalEntropy (literalFlow h P angularSpeed axialSpeed tau t) :=
  coverEntropy_literalFlow_eq_zero h P angularSpeed axialSpeed tau htau t

/-- **The entropy clause of `FastDynamo.MainLagrangianClauses`**
(`FastDynamo/Dynamics/ParticleFlow.lean`), verbatim: `∀ t, HasZeroTopologicalEntropy (Φ t)` at
`Φ = literalFlow h P angularSpeed axialSpeed tau`.

This is the form used in the assembly of the main theorem; it needs `0 ≤ tau`, which the main
parameter choice supplies (`mainParameterChoice.tau_nonneg`). -/
theorem forall_hasZeroTopologicalEntropy_literalFlow (htau : 0 ≤ tau) :
    ∀ t : ℝ, HasZeroTopologicalEntropy (literalFlow h P angularSpeed axialSpeed tau t) :=
  fun t => hasZeroTopologicalEntropy_literalFlow h P angularSpeed axialSpeed tau htau t

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
