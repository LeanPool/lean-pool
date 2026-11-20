/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.Realization

/-!
# The Hille–Yosida generation theorem

This module states the theorem the directory was built for.  A *Hille–Yosida ray* for a
domain operator `A : DomainOperator X D` with constant `M` (`ResolventRay.lean`) is a
domain-valued resolvent certificate on a set containing the real ray `(M, ∞)`, together
with the single estimate `‖R(r)‖ ≤ (r - M)⁻¹` there.  If in addition the domain embeds
densely, `A` generates a strongly continuous semigroup with growth bound `M`:

* `exists_stronglyContinuousSemigroup_of_hilleYosidaRay` — the existential form: there is a
  `StronglyContinuousSemigroup X` which realizes `A` in the sense of
  `DomainOperatorSemigroupRealization` and satisfies `‖S t‖ ≤ exp (M t)`.
* `HilleYosidaRay.semigroup_spec` — the same content stated about the *named* objects
  `HilleYosidaRay.semigroup` (`Semigroup.lean`) and `HilleYosidaRay.realization`
  (`Realization.lean`), which are definitions, not existential witnesses.  Consumers that
  need the orbit itself — such as the growth-bound theory — use
  `hy.semigroup hdense`, `hy.realization hdense` and `hy.domainOrbit hdense` directly;
  the existential form above discards exactly that information.
* `re_le_growthBound_of_hilleYosidaRay_of_eigenpair` — the growth-bound sandwich
  `Re λ ≤ S.growthBound ≤ M` for an eigenpair of `A`, which is what the surrounding
  development consumes: the upper bound is `HilleYosidaRay.growthBound_le`
  (`Semigroup.lean`, from `StronglyContinuousSemigroup.growthBound_le_of_norm_le`) and the
  lower bound is `DomainOperatorSemigroupRealization.re_le_growthBound_of_eigenpair`
  (`FastDynamo/Dynamics/GrowthBound.lean`) applied to the realization, under the standing
  hypothesis that forward strong solutions of `A` are unique.
* `HilleYosidaRay.semigroup_unique` — under that same uniqueness hypothesis the generated
  semigroup is *the* semigroup realizing `A`: any strongly continuous semigroup with a
  `DomainOperatorSemigroupRealization` of `A` equals `hy.semigroup hdense`.  In particular
  the construction does not depend on which resolvent certificate the ray carries.

## Scope

This is the abstract generation theorem (the analogue of the Hille–Yosida generation
theorem of Engel–Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Theorem II.3.5, in its quasi-contractive form `‖R(r)‖ ≤ (r - M)⁻¹` and in the repository's
`DomainOperator` formulation).  It is proved by the Yosida route: the
approximants `A_r = r² R(r) - r` are bounded, their exponentials `exp (t A_r)` are uniformly
bounded on compact time intervals, they form a Cauchy family in the strong topology, and
their limit is the semigroup.

**The generator and analyticity** are proved in the neighbouring modules:
`HilleYosidaRay.generator_semigroup` (`GeneratorIdentification.lean`) shows that the generator
of `hy.semigroup hdense`, in the sense of `StronglyContinuousSemigroup.generator`, is `A`, and
`HilleYosidaRay.isAnalyticSemigroup_of_sectorial` (`AnalyticGeneration.lean`) shows that the
semigroup is analytic of angle `π/4` when the numerical range of `A` lies in a sector.
**Uniqueness** among semigroups *realizing* `A` is proved here under the extra hypothesis
`DomainOperator.ForwardStrongSolutionsUnique`: the realization by itself records that `S`
solves the Cauchy problem, not that it is the only family doing so, and it is uniqueness of
forward strong solutions that closes that gap in `HilleYosidaRay.semigroup_unique`.  Among
semigroups with a given *generator*, uniqueness needs no hypothesis
(`StronglyContinuousSemigroup.ext_of_generator_eq`).

This is the generation theorem behind the Lean form of the growth-rate clause of `thm:main`:
the semigroup whose growth bound is `gamma` is `HilleYosidaRay.semigroup` at the product ray
(`FastDynamo/Dynamics/Assembly/ProductSemigroup.lean`), restricted to `L²_σ`, where its
generator is `L_{ε,u}` with domain `H² ∩ L²_σ` (`generator_solenoidalInductionSemigroup`).
The paper generates the semigroup directly on `L²_σ` by perturbing `εΔ`
(`lem:semigroup-spectral-growth`, via Engel–Nagel III.2.10).
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

/--
**Hille–Yosida generation theorem, packaged form.**

The semigroup `hy.semigroup hdense` and the realization `hy.realization hdense` are
definitions, so this statement is about named objects: the generated semigroup realizes
`A`, obeys the exponential bound `‖S t‖ ≤ exp (M t)` with the constant of the
Hille–Yosida hypothesis, and therefore has growth bound at most `M`.
-/
theorem HilleYosidaRay.semigroup_spec {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) :
    Nonempty (DomainOperatorSemigroupRealization (hy.semigroup hdense) A) ∧
      (∀ t : NNReal, ‖(hy.semigroup hdense).operator t‖ ≤ Real.exp (M * (t : ℝ))) ∧
      (hy.semigroup hdense).growthBound ≤ (M : EReal) :=
  ⟨⟨hy.realization hdense⟩, hy.norm_semigroup_le hdense, hy.growthBound_le hdense⟩

/--
**Hille–Yosida generation theorem.**

A domain operator with a Hille–Yosida ray of constant `M` and densely embedded domain
generates a strongly continuous semigroup: there is a `StronglyContinuousSemigroup X`
which realizes `A` — every domain datum evolves along a domain-valued forward strong
solution whose embedding is the semigroup orbit — and which satisfies the exponential
bound `‖S t‖ ≤ exp (M t)` at every nonnegative time.

The witness is `hy.semigroup hdense`, with realization `hy.realization hdense`; use
`HilleYosidaRay.semigroup_spec` when the witnesses themselves are needed, since `Nonempty`
discards the orbit.
-/
theorem exists_stronglyContinuousSemigroup_of_hilleYosidaRay {M : ℝ}
    (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding) :
    ∃ S : StronglyContinuousSemigroup X,
      Nonempty (DomainOperatorSemigroupRealization S A) ∧
        ∀ t : NNReal, ‖S.operator t‖ ≤ Real.exp (M * (t : ℝ)) :=
  ⟨hy.semigroup hdense, ⟨hy.realization hdense⟩, hy.norm_semigroup_le hdense⟩

/--
**The growth-bound sandwich.**  For a domain operator with a Hille–Yosida ray of constant
`M`, densely embedded domain and unique forward strong solutions, every eigenvalue of `A`
has real part below the growth bound of the generated semigroup, which in turn is at most
`M`:

`Re λ ≤ (hy.semigroup hdense).growthBound ≤ M`.

The lower bound is `DomainOperatorSemigroupRealization.re_le_growthBound_of_eigenpair`
applied to `hy.realization hdense`: uniqueness identifies the semigroup orbit of the
eigenvector with the exponential trajectory `e^{λ t} b`, whose norm grows exactly like
`e^{t Re λ}`.  Nonvanishing of the eigenvector in the ambient space is part of
`DomainOperator.IsEigenpair`.  The upper bound is `HilleYosidaRay.growthBound_le`.

This is the form in which the surrounding development uses the generation theorem: it
turns the hypothetical semigroup of `FastDynamo/Dynamics/GrowthBound.lean` into a
constructed one.  The lower inequality is the shape of the paper's `γ(u, ε) ≥ Re λ_ε` (the
proof of `thm:main`); the upper one is the growth ceiling that the paper's formal energy
identity `eq:energy-competition` suggests.
-/
theorem re_le_growthBound_of_hilleYosidaRay_of_eigenpair {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (hunique : A.ForwardStrongSolutionsUnique)
    {eigenvalue : ℂ} {b : D} (hpair : A.IsEigenpair eigenvalue b) :
    (eigenvalue.re : EReal) ≤ (hy.semigroup hdense).growthBound ∧
      (hy.semigroup hdense).growthBound ≤ (M : EReal) :=
  ⟨(hy.realization hdense).re_le_growthBound_of_eigenpair hunique hpair,
    hy.growthBound_le hdense⟩

/--
**The generated semigroup is the only one realizing `A`.**  If forward strong solutions of
`A` are unique and the domain embeds densely, then every strongly continuous semigroup `S`
carrying a `DomainOperatorSemigroupRealization` of `A` equals `hy.semigroup hdense`.

This is `StronglyContinuousSemigroup.eq_of_realization` applied to `hy.realization hdense`.
Two consequences are worth recording.  The definite article in "*the* semigroup generated by
`A`" is earned.  And the construction is independent of the data inside `hy`: two Hille–Yosida
rays for the same `A` — for instance two different choices of resolvent certificate, or two
different constants `M` — generate the same semigroup.
-/
theorem HilleYosidaRay.semigroup_unique {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (hunique : A.ForwardStrongSolutionsUnique)
    {S : StronglyContinuousSemigroup X}
    (R : DomainOperatorSemigroupRealization S A) :
    S = hy.semigroup hdense :=
  StronglyContinuousSemigroup.eq_of_realization R (hy.realization hdense) hunique hdense

end FastDynamo
