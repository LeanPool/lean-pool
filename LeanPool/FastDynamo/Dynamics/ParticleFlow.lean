/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Dynamics.IdealWeakForm
public import LeanPool.FastDynamo.Analysis.LiteralTorusRepresentative
public import LeanPool.FastDynamo.Analysis.LogLinearGrowth
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# The dynamical clauses of Theorem 1.2: particle flow, entropy, ideal induction group

**Statement layer.**  The predicates below are *stated* here and *proved* downstream: the
flow is constructed in `FastDynamo/Dynamics/Flow/*`, the ideal induction group in
`FastDynamo/Dynamics/Ideal/*`, and the two are assembled at the constructed velocity in
`FastDynamo/Dynamics/MainLagrangianClauses.lean` (`mainLagrangianClauses_literalVelocity`,
`mainTheoremLagrangian_holds`, `mainTheoremDynamical_holds`).

The paper states Theorem 1.2 (`thm:main`) with a short dynamical half (its last sentence):

```
  h_top(Φ_t) = 0   (t ∈ ℝ),        lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0 ,
```

where `Φ_t` is the particle flow of `u` and `𝒯₀` the ideal induction solution group on
`L²_σ(T³)` (both fixed in §1.2 just before `thm:main`).  That is `MainTheoremDynamicalClauses`
below.  The paper keeps more than that — a linear Lipschitz bound and two-sided
per-datum bounds on `𝒯₀` — outside the theorem, in `prop:particle-flow` and
`cor:ideal-growth`:

```
  Lip(Φ_t) + Lip(Φ_t⁻¹) ≤ C_L (1 + |t|)          (eq:linear-flow-lipschitz),
  ‖B‖ / (C_L(1 + |t|)) ≤ ‖𝒯₀(t)B‖ ≤ C_L(1 + |t|) ‖B‖      (cor:ideal-growth),
```

together with `h_top(Φ_t) = 0` (`prop:particle-flow`) and the vanishing per-datum rate (the
last sentence of `cor:ideal-growth`).
That larger bundle is `MainLagrangianClauses` below — the blueprint node
`prop:main-lagrangian` — and `MainLagrangianClauses.toMainTheoremDynamicalClauses` projects
it onto the theorem's own two clauses.

Where each clause is discharged:

* `IsParticleFlow` at the constructed velocity — `Dynamics/Flow/ParticleFlowProof.lean`
  (`isParticleFlow_literalFlow`), on the closed-form flow `literalFlow` of
  `Dynamics/Flow/TorusFlow.lean`; no Picard–Lindelöf and no Gronwall is used, the flow is
  written down cell by cell and the ODE is verified.  Uniqueness is separate
  (`Dynamics/Flow/ParticleFlowUniqueness.lean`), so `literalFlow` is the
  paper's unique particle flow `Φ_t` (the display opening §4).
* `HasZeroTopologicalEntropy` of every time map — `Dynamics/Flow/Entropy.lean`
  (`coverEntropy_literalFlow_eq_zero`), from the Lipschitz-iterate criterion
  `coverEntropy_eq_zero_of_lipschitz_iterate` of `Analysis/EntropyCriterion.lean`.
* `IsIdealInductionGroup` — `Dynamics/Ideal/IdealGroup.lean`
  (`isIdealInductionGroup_idealGroup`), on the Cauchy transport operator of
  `Dynamics/Ideal/CauchyOperator.lean` corestricted to `literalSolenoidalSubspace` in
  `Dynamics/Ideal/SolenoidalInvariance.lean`; that it is a solution group of the ideal induction
  equation is `Dynamics/Ideal/WeakSolution.lean`, that it is the only one
  `Dynamics/Ideal/WeakSolutionUniqueness.lean`.
* `MainLagrangianClauses`, `MainTheoremDynamicalClauses` and the two vanishing-rate
  predicates at `mainLiteralVelocity` — `Dynamics/MainLagrangianClauses.lean`.

Two further clauses of `prop:particle-flow` are proved outside this bundle: the explicit
formula `eq:explicit-particle-flow` with the fixed points and the centre speed (the sentences
after it), in `Dynamics/Flow/TorusFlow.lean`, and the optimal-constant limit
`lim_{|t| → ∞} |t|⁻¹ log Lip(Φ_t) = 0`, in
`Dynamics/Flow/LipschitzRate.lean`.

The blueprint carries the three definitions (`def:dynamics:particle-flow`,
`def:dynamics:topological-entropy`, `def:dynamics:ideal-induction-group`) and the proofs
`prop:particle-flow` and `cor:ideal-growth` in `blueprint/src/chapters/particle.tex`.

## Contents

* `IsLiteralTorusLift` — the notion of a periodic lift along the coordinatewise quotient
  `literalTorusPoint : ℝ³ → T³` of `FastDynamo/Analysis/LiteralThreeTorus.lean`, the device the
  paper itself uses to differentiate maps of the torus ("the periodic lift of `u` and the
  corresponding equivariant lift of `Φ_t`", the proof of `cor:ideal-growth`).
* `IsParticleFlow` — the flow of a Lipschitz velocity, `d/dt Φ_t(x) = u(Φ_t(x))`, `Φ_0 = id`
  (§1.2, restated at the opening of §4).
* `HasZeroTopologicalEntropy` — vanishing of Mathlib's `Dynamics.coverEntropy`.
* `IsIdealInductionGroup` — the solution group `𝒯₀` of the ideal induction equation
  (§1.2, `cor:ideal-growth`): a strongly continuous group on `L²_σ`, a solution group in the
  weak sense of `FastDynamo/Dynamics/IdealWeakForm.lean` and the only one, together with the
  Cauchy representation `eq:ideal-cauchy-formula` that ties it to the flow.
* `MainLagrangianClauses` — the bundle of `prop:particle-flow` + `cor:ideal-growth`.
* `MainTheoremDynamicalClauses` — the two dynamical clauses of the theorem itself
  (its last sentence).
* `HasVanishingIdealGrowthRate` — the per-datum rate, the last sentence of `cor:ideal-growth`.
* `HasVanishingIdealOperatorGrowthRate` — the paper's `γ_id(u) = 0`
  (`eq:zero-ideal-growth`), which is also the theorem's second clause.

## The ideal induction equation and the uniqueness of `𝒯₀`

The paper calls `𝒯₀` *the* solution group on `L²_σ(T³)` of the ideal induction equation
(§1.2 and the statement of `cor:ideal-growth`); the proof of `cor:ideal-growth` derives the weak
form `d/dt ⟨𝒯₀(t)B, φ⟩ = ⟨(𝒯₀(t)B · ∇)u, φ⟩ + ⟨𝒯₀(t)B, (u · ∇)φ⟩` from the Cauchy formula and
proves uniqueness among distributional solutions in `C([-T,T]; L²)`.  `IsIdealInductionGroup`
states both: the field `solutionGroup` says that every orbit of `𝒯₀` is a weak solution
(`IsIdealSolutionGroup` of `FastDynamo/Dynamics/IdealWeakForm.lean`: continuous into `L²` on
every `[−T, T]`, and `⟨W(t), φ⟩ − ⟨W(s), φ⟩ = ∫ₛᵗ ⟨(W·∇)u, φ⟩ + ⟨W, (u·∇)φ⟩` for every smooth
periodic test field `φ` and all `s, t ∈ [−T, T]`), and the field `unique` says that no other
group of operators on `L²_σ` has this property.  The weak notion differs from the paper's in the
points recorded in `FastDynamo/Dynamics/IdealWeakForm.lean` (spatial test fields with a
time-integrated identity in place of space–time test functions; `Div B = 0` is not part of the
notion; `∇u` is the pointwise derivative of the lift).

At the constructed velocity — at every admissible parameter tuple, in particular at the velocity
of `thm:main` — existence is `isIdealSolutionGroup_idealGroup`
(`Dynamics/Ideal/WeakSolution.lean`: the Cauchy formula differentiated along the flow with the
variational equation, as in the paper) and uniqueness is `IsIdealSolutionGroup.eq_idealGroup`
(`Dynamics/Ideal/WeakSolutionUniqueness.lean`).  The uniqueness argument deviates from the
paper's: the paper obtains the characteristic identity
`W(t, Φ_t(a)) = ∫₀ᵗ (∇u)(Φ_s(a)) W(s, Φ_s(a)) ds` for a solution with `W(0) = 0` from
Ambrosio–Crippa, Proposition 2.3; here the weak identity is pulled back along the flow — it is
tested against the Lipschitz fields `ψ ∘ Φ_{−s}`, to which it extends by Fourier partial sums
(`Dynamics/Ideal/LipschitzTestFields.lean`) — which gives that identity in tested form, and
Grönwall's inequality forward and backward in time gives `W = 0`, as in the paper.

## What is not stated, and why

None of the items below is part of the *statement* of `prop:particle-flow` or
`cor:ideal-growth`.

1. **The variational equation** `eq:flow-variational-equation`,
   `DΦ_t(a) = id + ∫₀^t (∇u)(Φ_s(a)) DΦ_s(a) ds`, is not a clause of `IsIdealInductionGroup`.
   Its role in the predicate — pinning `DΦ` to the flow — is played by
   `IsIdealInductionGroup.hasFDerivAt`, which says that `DΦ t` is the almost-everywhere Fréchet
   derivative of a periodic lift of `Φ t` (Rademacher, the proof of `cor:ideal-growth`).  At the
   constructed velocity the variational equation is proved, at every point and every time
   (`flowFDeriv_eq_one_add_integral`, `Dynamics/Flow/VariationalEquation.lean`).
2. **Liouville's formula** `det DΦ_t = 1` (the proof of `cor:ideal-growth`) is not stated; its
   consequence, that `Φ t` preserves Lebesgue measure, is, as
   `IsIdealInductionGroup.measurePreserving` — that is what makes the almost-everywhere Cauchy
   identity meaningful for `L²` classes.  The proof of that clause
   (`Dynamics/Flow/MeasurePreserving.lean`) does not go through `Div u = 0` either: the
   transverse Jacobian is computed pointwise from the closed-form flow
   (`det_fderiv_planeTransverseFlow`) and the axial shear is a fibrewise translation, so the
   change of variables and `MeasurePreserving.skew_product` give the clause directly.
3. **`Lip` is the optimal Lipschitz constant** in the paper (§1.2).  In
   `MainLagrangianClauses` the Lipschitz clause is stated with existentially quantified
   admissible constants `L₁, L₂`; since the optimal constant is the least admissible one, the
   two readings of `Lip(Φ_t) + Lip(Φ_t⁻¹) ≤ C_L(1 + |t|)` are equivalent.  The optimal constant
   itself is `lipConst` of `Dynamics/Flow/LipschitzRate.lean`, which the limit clause of
   `prop:particle-flow` needs.
4. **`Φ_t⁻¹ = Φ_{-t}`** (used in the proof of `prop:particle-flow`) is not derived from
   uniqueness for the ODE; it is a clause of `MainLagrangianClauses`, so that `Φ (-t)` in the
   Lipschitz bound is the inverse map.
-/

@[expose] public section
namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Periodic lifts -/

/-- `L` is a periodic lift of the self-map `F` of the literal three-torus: `F ∘ π = π ∘ L` for the
quotient `π = literalTorusPoint`.  This is the device the paper uses to differentiate maps of `T³`
("the periodic lift of `u` and the corresponding equivariant lift of `Φ_t`", the proof of
`cor:ideal-growth`). -/
def IsLiteralTorusLift (F : Torus 3 → Torus 3) (L : R3 → R3) : Prop :=
  ∀ x : R3, F (literalTorusPoint x) = literalTorusPoint (L x)

/-! ## The particle flow -/

/-- **The particle flow of a Lipschitz velocity field on the literal three-torus**
(§1.2, restated at the opening of §4):

```
  d/dt Φ_t(x) = v(Φ_t(x)),        Φ_0(x) = x.
```

`Torus 3` is not a normed space, so the derivative is read on a periodic lift, exactly as the
paper does: for each `x` there is a curve `γ : ℝ → ℝ³` in the universal cover with
`Φ t x = π (γ t)` whose derivative at every time `t` is the velocity at the current position.
The paper infers existence and uniqueness from the global Lipschitz regularity of `u`
(the opening of §4).  Here *existence* is proved instead by exhibiting the flow in closed form
(`ScaleFamily.TorusCellPlacement.isParticleFlow_literalFlow`, on the explicit `literalFlow`);
*uniqueness* is proved separately by Grönwall on the universal cover (`IsParticleFlow.unique`,
`FastDynamo/Dynamics/Flow/ParticleFlowUniqueness.lean`), and identifies `literalFlow` as the
particle flow of the velocity; the inverse law `Φ_{-t} ∘ Φ_t = id` is a separate clause of
`MainLagrangianClauses` rather than a consequence of uniqueness. -/
structure IsParticleFlow (v : Torus 3 → R3) (Φ : ℝ → Torus 3 → Torus 3) : Prop where
  /-- `Φ_0 = id`. -/
  initial : ∀ x : Torus 3, Φ 0 x = x
  /-- `d/dt Φ_t(x) = v(Φ_t(x))`, read along a periodic lift of the trajectory through `x`. -/
  ode : ∀ x : Torus 3, ∃ γ : ℝ → R3,
    (∀ t : ℝ, Φ t x = literalTorusPoint (γ t)) ∧ ∀ t : ℝ, HasDerivAt γ (v (Φ t x)) t

/-! ## Topological entropy -/

/-- **Zero topological entropy of a continuous self-map.**

Mathlib's `Dynamics.coverEntropy F Set.univ` is the supremum over entourages of the exponential
growth rate of the minimal cardinality of a dynamical cover.  The paper fixes no
display for `h_top`: it refers to Hasselblatt–Katok, *Principal structures*, Section 2.5e
(§1.2), the Bowen–Dinaburg invariant of a continuous self-map
of a compact metric space.  On the compact metric space `T³` the proof reduces the cover
entropy, through `Metric.uniformity_basis_dist`, to the growth rate of the minimal
`(m, ρ)`-cover (`coverEntropy_eq_zero_of_lipschitz_iterate`,
`FastDynamo/Analysis/EntropyCriterion.lean`, which is the criterion that supplies the clause),
so the quantity proved to vanish is that invariant in its cover form.

Cover, spanning and separated-set entropy agree on a compact metric space; Mathlib's own
bridge to the separated (net) form, `Dynamics.coverEntropy_eq_iSup_basis_netEntropyEntourage`
(`Mathlib/Dynamics/TopologicalEntropy/NetEntropy.lean`), is available but is not imported here
because no clause needs it. -/
def HasZeroTopologicalEntropy {X : Type*} [UniformSpace X] (F : X → X) : Prop :=
  Dynamics.coverEntropy F Set.univ = 0

/-! ## The ideal induction solution group -/

/-- **The ideal induction solution group `𝒯₀` of a Lipschitz velocity on `L²_σ(T³;ℂ³)`**
(§1.2, `cor:ideal-growth`), for the ideal equation

```
  ∂_t B + (u · ∇)B − (B · ∇)u = 0,        Div B = 0        (statement of `cor:ideal-growth`).
```

The paper defines `𝒯₀` as *the* solution group of this equation on `L²_σ` (§1.2), constructs
it by the Cauchy formula and proves that it solves the equation in the weak sense and that
distributional solutions in `C([-T,T]; L²)` are unique (the proof of `cor:ideal-growth`).  The
predicate says all of this:

* `solutionGroup` and `unique` — `𝒯₀` is a solution group of the equation of `v` in the weak
  sense of `IsIdealSolutionGroup` (`FastDynamo/Dynamics/IdealWeakForm.lean`), and every
  solution group of that equation is `𝒯₀`; with `unique` the group is determined by `v` alone;
* `group_zero`, `group_add`, `strongly_continuous` — the `C₀`-group properties;
* `cauchy` — the paper's formula for `𝒯₀`, `eq:ideal-cauchy-formula`:
  `(𝒯₀(t)B)(Φ_t(a)) = DΦ_t(a) B(a)` for almost every `a`, with the particle flow `Φ` of `v`
  (`particleFlow`), `hasFDerivAt`, which says that `DΦ t` is the almost-everywhere Fréchet
  derivative of a periodic lift of `Φ t` (Rademacher), and `measurePreserving`, the
  consequence `det DΦ_t = 1` of Liouville's formula and `Div u = 0` that makes the
  almost-everywhere identity meaningful between `L²` classes.

The entries of `DΦ t a` are read as `(DΦ t a) e_j` in coordinate `i`, and the real matrix acts
on the complex amplitude coordinatewise.  The weak notion differs from the paper's in the points
recorded in `FastDynamo/Dynamics/IdealWeakForm.lean`; the variational equation
`eq:flow-variational-equation` is not a field (see the module docstring).

The structure is inhabited: `ScaleFamily.TorusCellPlacement.isIdealInductionGroup_idealGroup`
(`FastDynamo/Dynamics/Ideal/IdealGroup.lean`) builds it, at the constructed velocity of every
admissible parameter tuple, from the closed-form flow, its Jacobian `flowFDeriv` and the Cauchy
transport operator corestricted to `literalSolenoidalSubspace`. -/
structure IsIdealInductionGroup (v : Torus 3 → R3) (Φ : ℝ → Torus 3 → Torus 3)
    (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
    (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace) : Prop where
  /-- `Φ` is the particle flow of `v`. -/
  particleFlow : IsParticleFlow v Φ
  /-- `DΦ t` is the almost-everywhere Fréchet derivative of a periodic lift of `Φ t`. -/
  hasFDerivAt : ∀ t : ℝ, ∃ L : R3 → R3, IsLiteralTorusLift (Φ t) L ∧
    ∀ᵐ x : R3, HasFDerivAt L (DΦ t (literalTorusPoint x)) x
  /-- Each time map preserves Lebesgue measure (`det DΦ_t = 1`). -/
  measurePreserving : ∀ t : ℝ, MeasurePreserving (Φ t) volume volume
  /-- `𝒯₀(0) = id`. -/
  group_zero : T 0 = ContinuousLinearMap.id ℂ literalSolenoidalSubspace
  /-- `𝒯₀(s + t) = 𝒯₀(s)𝒯₀(t)`; with `group_zero` this makes `𝒯₀(-t)` the inverse of `𝒯₀(t)`
  (the proof of `cor:ideal-growth`). -/
  group_add : ∀ s t : ℝ, T (s + t) = (T s).comp (T t)
  /-- Strong continuity of the group (the proof of `cor:ideal-growth`). -/
  strongly_continuous : ∀ B : literalSolenoidalSubspace, Continuous fun t : ℝ ↦ T t B
  /-- **The Cauchy formula** `eq:ideal-cauchy-formula`, coordinatewise. -/
  cauchy : ∀ (t : ℝ) (B : literalSolenoidalSubspace), ∀ᵐ a : Torus 3, ∀ i : Fin 3,
    (((T t B : literalSolenoidalSubspace) : LiteralC3L2) : Torus 3 → C3) (Φ t a) i =
      ∑ j : Fin 3, ((DΦ t a (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) *
        (((B : literalSolenoidalSubspace) : LiteralC3L2) : Torus 3 → C3) a j
  /-- `𝒯₀` is a solution group of the ideal induction equation of `v`: every orbit
  `t ↦ 𝒯₀(t)B` is a weak solution in `C([−T, T]; L²)` for every `T` (`IsIdealSolutionGroup`). -/
  solutionGroup : IsIdealSolutionGroup v T
  /-- `𝒯₀` is the only solution group of the ideal induction equation of `v` (the definite
  article of §1.2 and of `cor:ideal-growth`). -/
  unique : ∀ T' : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace,
    IsIdealSolutionGroup v T' → T' = T

/-! ## The dynamical clauses of the main theorem -/

/-- **`prop:particle-flow` and `cor:ideal-growth`, bundled** (the blueprint node
`prop:main-lagrangian`), at a velocity `v` on the literal three-torus:

* the velocity has a particle flow `Φ` with `Φ_t⁻¹ = Φ_{-t}` (§1.2; the inverse law is used in
  the proof of `prop:particle-flow`);
* there is a constant `C_L ≥ 1` with `Lip(Φ_t) + Lip(Φ_{-t}) ≤ C_L(1 + |t|)` for every real `t`
  (`eq:linear-flow-lipschitz`);
* every time map has zero topological entropy, `h_top(Φ_t) = 0` (`prop:particle-flow`);
* `𝒯₀` is the solution group of the ideal induction equation on `L²_σ(T³;ℂ³)` (§1.2,
  `cor:ideal-growth`): a strongly continuous group, a solution group in the weak sense and the
  only one, given by the Cauchy formula (`IsIdealInductionGroup`);
* the two-sided per-datum bounds of `cor:ideal-growth`,

  ```
    ‖B‖ / (C_L(1 + |t|)) ≤ ‖𝒯₀(t)B‖ ≤ C_L(1 + |t|) ‖B‖;
  ```

* every non-zero ideal solution has exponential growth rate zero (the last sentence of
  `cor:ideal-growth`).

This is **more** than Theorem 1.2 states: the theorem has only the entropy
clause and the operator-norm rate (its last sentence), which are
`MainTheoremDynamicalClauses` below, obtained from this bundle by
`MainLagrangianClauses.toMainTheoremDynamicalClauses`.  The Lipschitz bound and the per-datum
bounds are the separate Lagrangian statements, which the name records.

The Lipschitz clause is stated with existentially quantified admissible constants rather than
with the optimal ones; see item 3 of the module docstring.

`MainTheoremLagrangian` (`FastDynamo/MainTheoremStrengthened.lean`) is this predicate at the
constructed velocity, and it is proved: `mainLagrangianClauses_literalVelocity` discharges the
predicate at the general parameters and `mainTheoremLagrangian_holds` instantiates it at the
main parameter choice, both in `FastDynamo/Dynamics/MainLagrangianClauses.lean`. -/
def MainLagrangianClauses (v : Torus 3 → R3) : Prop :=
  ∃ (Φ : ℝ → Torus 3 → Torus 3) (CL : ℝ), 1 ≤ CL ∧ IsParticleFlow v Φ ∧
    (∀ (t : ℝ) (x : Torus 3), Φ (-t) (Φ t x) = x) ∧
    (∀ t : ℝ, ∃ L₁ L₂ : NNReal,
      LipschitzWith L₁ (Φ t) ∧ LipschitzWith L₂ (Φ (-t)) ∧
        (L₁ : ℝ) + (L₂ : ℝ) ≤ CL * (1 + |t|)) ∧
    (∀ t : ℝ, HasZeroTopologicalEntropy (Φ t)) ∧
    ∃ (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
      (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace),
      IsIdealInductionGroup v Φ DΦ T ∧
      (∀ (t : ℝ) (B : literalSolenoidalSubspace),
        ‖B‖ / (CL * (1 + |t|)) ≤ ‖T t B‖ ∧ ‖T t B‖ ≤ CL * (1 + |t|) * ‖B‖) ∧
      (∀ B : literalSolenoidalSubspace, B ≠ 0 →
        Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (‖T t B‖ / ‖B‖))
          Filter.atTop (nhds (0 : ℝ)))

/-! ## The dynamical clauses of Theorem 1.2 -/

/-- **The dynamical clauses of Theorem 1.2** (`thm:main`, its last sentence), at a velocity
`v` on the literal three-torus:

```
  h_top(Φ_t) = 0   (t ∈ ℝ),        lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0 .
```

These are the only two dynamical clauses the theorem carries.  `Φ` is the particle
flow of `v` and `𝒯₀` the ideal induction solution group on `L²_σ(T³)` (§1.2), so a single
existential over `Φ`, `DΦ` and `T` suffices: `IsIdealInductionGroup` already carries
`IsParticleFlow v Φ` as its first field, and both clauses are read at the *same* pair.

**The continuity conjunct `∀ t, Continuous (Φ t)` is part of the entropy clause, not an extra
assertion.**  The paper writes `h_top(F)` for the topological entropy of a *continuous*
self-map of a compact metric space (§1.2), whereas `Dynamics.coverEntropy` — the Mathlib
notion behind `HasZeroTopologicalEntropy` — is defined for an arbitrary self-map of a uniform
space.  Without the conjunct this predicate would assert
`Dynamics.coverEntropy (Φ t) Set.univ = 0` for a `Φ t` it does not force to be continuous,
which is not what `thm:main` says.  At every witness the conjunct is
free: `MainLagrangianClauses` gives Lipschitz time maps, and
`MainLagrangianClauses.toMainTheoremDynamicalClauses` discharges it by
`LipschitzWith.continuous`.

The Lipschitz bound `eq:linear-flow-lipschitz` and the two-sided per-datum
bounds are `prop:particle-flow` and `cor:ideal-growth`, outside the theorem; they are
bundled as `MainLagrangianClauses` above, from which this predicate is obtained by
`MainLagrangianClauses.toMainTheoremDynamicalClauses`.

`‖T t‖` is the operator norm on `literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace`,
which is the paper's `‖·‖_{L²_σ → L²_σ}`; the paper's `lim` and Lean's
`Filter.Tendsto … atTop (𝓝 0)` are the same statement here.

At the constructed velocity this is `MainTheoremDynamical`
(`FastDynamo/MainTheoremStrengthened.lean`), proved by `mainTheoremDynamical_holds`
(`FastDynamo/Dynamics/MainLagrangianClauses.lean`). -/
def MainTheoremDynamicalClauses (v : Torus 3 → R3) : Prop :=
  ∃ (Φ : ℝ → Torus 3 → Torus 3) (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
    (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace),
    IsIdealInductionGroup v Φ DΦ T ∧
      (∀ t : ℝ, Continuous (Φ t)) ∧
      (∀ t : ℝ, HasZeroTopologicalEntropy (Φ t)) ∧
      Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖T t‖) Filter.atTop (nhds (0 : ℝ))

/-- **The per-datum ideal growth rate is zero**: the solution group of the ideal induction
equation of `v` exists (and is unique, by the field `unique` of `IsIdealInductionGroup`), and
every non-zero datum has exponential growth rate exactly zero under it.

This is the last sentence of `cor:ideal-growth` ("In particular, every non-zero ideal solution
has exponential growth rate zero"), and is not part
of `thm:main`.  It
is isolated from `MainLagrangianClauses` so that `ideal_resistive_gap_at_diffusivity`
(`FastDynamo/MainTheoremStrengthened.lean`) can consume it.  The rate is read off the group —
existentially quantified here, and determined by `v` through `IsIdealInductionGroup.unique` —
rather than defined as a `limsup` of a fixed object; at the
constructed velocity the group is `mainIdealGroup`
(`FastDynamo/Dynamics/MainLagrangianClauses.lean`). -/
def HasVanishingIdealGrowthRate (v : Torus 3 → R3) : Prop :=
  ∃ (Φ : ℝ → Torus 3 → Torus 3) (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
    (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace),
    IsIdealInductionGroup v Φ DΦ T ∧
      ∀ B : literalSolenoidalSubspace, B ≠ 0 →
        Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (‖T t B‖ / ‖B‖))
          Filter.atTop (nhds (0 : ℝ))

/-- The Lagrangian bundle contains the vanishing of the per-datum ideal growth rate: this is
the only part of `MainLagrangianClauses` that `ideal_resistive_gap_at_diffusivity` uses. -/
theorem MainLagrangianClauses.hasVanishingIdealGrowthRate {v : Torus 3 → R3}
    (h : MainLagrangianClauses v) : HasVanishingIdealGrowthRate v := by
  obtain ⟨Phi, _CL, -, -, -, -, -, DPhi, T, hgroup, -, hrate⟩ := h
  exact ⟨Phi, DPhi, T, hgroup, hrate⟩

/-! ## The ideal growth rate of the operator norm -/

/-- **The paper's `γ_id(u) = 0` in operator norm** (`eq:zero-ideal-growth`): the solution
group of the ideal induction equation of `v` exists (and is unique, by the field `unique` of
`IsIdealInductionGroup`), and its operator norm grows subexponentially,

```
  lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0 .
```

This is a clause of Theorem 1.2 itself (its last display), not only of
`cor:ideal-growth`; it is the second conjunct of `MainTheoremDynamicalClauses`.  Unlike
`HasVanishingIdealGrowthRate`, which is the *per-datum* sentence of `cor:ideal-growth`, the rate
here
is the one of the evolution **operator**, which is what distinguishes the construction from an
autonomous one; the two are different statements, and
`MainLagrangianClauses.hasVanishingIdealOperatorGrowthRate` derives this one from the
two-sided per-datum bounds by taking the operator norm (the supremum over unit initial data)
and then logarithms, as in the last step of the paper's proof of `cor:ideal-growth`. -/
def HasVanishingIdealOperatorGrowthRate (v : Torus 3 → R3) : Prop :=
  ∃ (Φ : ℝ → Torus 3 → Torus 3) (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
    (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace),
    IsIdealInductionGroup v Φ DΦ T ∧
      Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖T t‖) Filter.atTop (nhds (0 : ℝ))

/-- **The vanishing operator-norm rate from the two-sided per-datum bounds**, isolated from the
dynamics.  This is the last step of the paper's proof of `cor:ideal-growth`: from the
per-datum bounds, "This gives `eq:ideal-group-growth`.  Taking logarithms and dividing by `t`
proves both zero-growth conclusions as `t → ∞`."  (The passage from per-datum to operator-norm
bounds, which the paper leaves implicit, is the supremum over unit initial data.)

The upper bound `‖𝒯₀(t)‖ ≤ C_L(1 + |t|)` is the operator-norm form of the right half of the
per-datum bounds; the lower bound `1/(C_L(1 + |t|)) ≤ ‖𝒯₀(t)‖` is the left half
read at a single non-zero datum.  Between two logarithms of linear functions the rate is
squeezed to zero.  (On a trivial state space both sides degenerate and `‖𝒯₀(t)‖ = 0`, whose
logarithm is `0` by Mathlib's convention, so the conclusion holds there too.)

Both `MainLagrangianClauses.hasVanishingIdealOperatorGrowthRate` and
`MainLagrangianClauses.toMainTheoremDynamicalClauses` — hence the second dynamical clause of
Theorem 1.2 — are this lemma read at the group of the bundle. -/
theorem tendsto_inv_mul_log_opNorm_of_two_sided_bounds
    {T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace} {CL : ℝ}
    (hCL : 1 ≤ CL)
    (hbounds : ∀ (t : ℝ) (B : literalSolenoidalSubspace),
      ‖B‖ / (CL * (1 + |t|)) ≤ ‖T t B‖ ∧ ‖T t B‖ ≤ CL * (1 + |t|) * ‖B‖) :
    Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖T t‖) Filter.atTop (nhds (0 : ℝ)) := by
  have hCL0 : (0 : ℝ) < CL := lt_of_lt_of_le zero_lt_one hCL
  rcases subsingleton_or_nontrivial literalSolenoidalSubspace with hsub | hnt
  · have hzero : (fun t : ℝ ↦ t⁻¹ * Real.log ‖T t‖) = fun _ : ℝ ↦ (0 : ℝ) := by
      funext t
      have ht : T t = 0 := Subsingleton.elim _ _
      simp [ht]
    rw [hzero]
    exact tendsto_const_nhds
  · obtain ⟨B0, hB0⟩ := exists_ne (0 : literalSolenoidalSubspace)
    have hB0n : 0 < ‖B0‖ := norm_pos_iff.2 hB0
    refine squeeze_zero_norm' ?_ (tendsto_inv_mul_log_linear_atTop hCL0)
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hden : (0 : ℝ) < CL * (1 + t) := by positivity
    have habs : |t| = t := abs_of_nonneg ht.le
    have hup : ‖T t‖ ≤ CL * (1 + t) := by
      refine ContinuousLinearMap.opNorm_le_bound _ hden.le fun B ↦ ?_
      have h := (hbounds t B).2
      rwa [habs] at h
    have hlow : 1 / (CL * (1 + t)) ≤ ‖T t‖ := by
      have h1 := (hbounds t B0).1
      rw [habs] at h1
      have hkey : 1 / (CL * (1 + t)) * ‖B0‖ ≤ ‖T t‖ * ‖B0‖ :=
        calc 1 / (CL * (1 + t)) * ‖B0‖ = ‖B0‖ / (CL * (1 + t)) := by ring
          _ ≤ ‖T t B0‖ := h1
          _ ≤ ‖T t‖ * ‖B0‖ := (T t).le_opNorm B0
      exact le_of_mul_le_mul_right hkey hB0n
    have hpos : 0 < ‖T t‖ := lt_of_lt_of_le (by positivity) hlow
    have hlog1 : Real.log ‖T t‖ ≤ Real.log (CL * (1 + t)) := Real.log_le_log hpos hup
    have hlog2 : -Real.log (CL * (1 + t)) ≤ Real.log ‖T t‖ := by
      have h := Real.log_le_log (by positivity) hlow
      rwa [Real.log_div one_ne_zero hden.ne', Real.log_one, zero_sub] at h
    calc ‖t⁻¹ * Real.log ‖T t‖‖ = t⁻¹ * |Real.log ‖T t‖| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 ht.le)]
      _ ≤ t⁻¹ * Real.log (CL * (1 + t)) :=
          mul_le_mul_of_nonneg_left (abs_le.2 ⟨hlog2, hlog1⟩) (inv_nonneg.2 ht.le)

/-- **`γ_id(u) = 0` in operator norm, from the two-sided per-datum bounds**, which is the
last step of the paper's proof of `cor:ideal-growth`:
the per-datum bounds give `eq:ideal-group-growth` (by the supremum over unit initial data),
and the rate follows by taking logarithms.  The
arithmetic is `tendsto_inv_mul_log_opNorm_of_two_sided_bounds`. -/
theorem MainLagrangianClauses.hasVanishingIdealOperatorGrowthRate {v : Torus 3 → R3}
    (h : MainLagrangianClauses v) : HasVanishingIdealOperatorGrowthRate v := by
  obtain ⟨Phi, CL, hCL, -, -, -, -, DPhi, T, hgroup, hbounds, -⟩ := h
  exact ⟨Phi, DPhi, T, hgroup, tendsto_inv_mul_log_opNorm_of_two_sided_bounds hCL hbounds⟩

/-- **Theorem 1.2's dynamical clauses are a projection of the Lagrangian bundle.**

`prop:particle-flow` and `cor:ideal-growth` together — the bundle
`MainLagrangianClauses` — give more than the theorem states.  Its two dynamical
clauses (the last sentence of `thm:main`) are the entropy conjunct of the bundle and the
operator-norm rate obtained from the bundle's two-sided per-datum bounds by
`tendsto_inv_mul_log_opNorm_of_two_sided_bounds`, both read at the bundle's own flow and ideal
group, so no new mathematics is involved.  The continuity conjunct that
`MainTheoremDynamicalClauses` carries alongside the entropy clause — the paper's `h_top`
is defined for continuous self-maps (§1.2) — comes from the bundle's Lipschitz clause by
`LipschitzWith.continuous`. -/
theorem MainLagrangianClauses.toMainTheoremDynamicalClauses {v : Torus 3 → R3}
    (h : MainLagrangianClauses v) : MainTheoremDynamicalClauses v := by
  obtain ⟨Phi, CL, hCL, -, -, hlip, hent, DPhi, T, hgroup, hbounds, -⟩ := h
  have hcont : ∀ t : ℝ, Continuous (Phi t) := by
    intro t
    obtain ⟨_L₁, _L₂, hL₁, -, -⟩ := hlip t
    exact hL₁.continuous
  exact ⟨Phi, DPhi, T, hgroup, hcont, hent,
    tendsto_inv_mul_log_opNorm_of_two_sided_bounds hCL hbounds⟩

end

end FastDynamo
