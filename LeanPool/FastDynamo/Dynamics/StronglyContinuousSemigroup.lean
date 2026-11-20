/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Finish.GrowingModeEvolution
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Strongly continuous semigroups and eigenmode growth

This module supplies the minimal `C₀`-semigroup interface needed to turn the
project's explicit eigen-trajectories into semigroup orbits.  Time is
the additive monoid `NNReal`, and strong continuity is recorded pointwise on the
ambient complex normed space.

No generation theorem is proved *in this module*.  Instead,
`DomainOperatorSemigroupRealization S A` explicitly stores a domain-valued
forward strong solution representing `S t (A.embedding B)` for every domain
datum `B`.  Identification with the exponential eigen-trajectory additionally
assumes `A.ForwardStrongSolutionsUnique`.

The interface is inhabited.  The abstract Hille–Yosida generation theorem
is proved in `FastDynamo/Dynamics/HilleYosida/`, and
`FastDynamo/Dynamics/Assembly/ProductSemigroup.lean` runs it on the all-frequency
induction operator, producing an inhabitant of both structures above.  That semigroup
is restricted to the solenoidal space `L²_σ(T³)` there and transported to
the literal three-torus in `FastDynamo/Dynamics/Assembly/MainGrowthRate.lean`.
The restricted semigroup is described through its generator rather than by realization
data: `generator_solenoidalInductionSemigroup`
(`FastDynamo/Dynamics/Assembly/SolenoidalGenerator.lean`) identifies its generator with the
*part* of `L_{ε,u}` in `L²_σ(T³)`, with domain `H² ∩ L²_σ`; see the docstring of
`DomainOperatorSemigroupRealization` below.

`StronglyContinuousSemigroup.operator_eq_of_realization` below shows that the
realization data of a densely defined operator with unique forward strong
solutions determines the semigroup, so "the" semigroup of such an operator is
justified.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

universe u v

/-- A semigroup of continuous complex-linear maps over nonnegative real time,
strongly continuous on every ambient vector. -/
structure StronglyContinuousSemigroup (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The bounded evolution operator at a nonnegative time. -/
  operator : NNReal → X →L[ℂ] X
  /-- Evolution at time zero is the identity. -/
  operator_zero' : operator 0 = ContinuousLinearMap.id ℂ X
  /-- The additive time law. -/
  operator_add' : ∀ s t : NNReal,
    operator (s + t) = (operator s).comp (operator t)
  /-- Strong continuity, stated pointwise in the ambient space. -/
  strong_continuous' : ∀ x : X, Continuous fun t : NNReal ↦ operator t x

namespace StronglyContinuousSemigroup

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/--
A `C₀`-semigroup may be applied directly to a time, delegating to its `operator` field, so that
`S t` denotes the evolution operator at time `t`.
-/
instance : CoeFun (StronglyContinuousSemigroup X)
    (fun _ ↦ NNReal → X →L[ℂ] X) :=
  ⟨StronglyContinuousSemigroup.operator⟩

/-- A `C₀`-semigroup is determined by its evolution operators: the three remaining
fields of the structure are propositions, hence equal by proof irrelevance. -/
@[ext] theorem ext {S T : StronglyContinuousSemigroup X}
    (h : ∀ t : NNReal, S.operator t = T.operator t) : S = T := by
  cases S with
  | mk f _ _ _ =>
    cases T with
    | mk g _ _ _ =>
      have hfg : f = g := funext h
      subst hfg
      rfl

/-- Bundled operator equality at time zero. -/
@[simp] theorem operator_zero (S : StronglyContinuousSemigroup X) :
    S 0 = ContinuousLinearMap.id ℂ X :=
  S.operator_zero'

/-- Bundled operator form of the additive semigroup law. -/
theorem operator_add (S : StronglyContinuousSemigroup X) (s t : NNReal) :
    S (s + t) = (S s).comp (S t) :=
  S.operator_add' s t

/-- Evolution fixes every vector at time zero. -/
theorem apply_zero (S : StronglyContinuousSemigroup X) (x : X) :
    S 0 x = x := by
  rw [S.operator_zero]
  rfl

/-- Pointwise form of the additive semigroup law. -/
theorem apply_add (S : StronglyContinuousSemigroup X)
    (s t : NNReal) (x : X) :
    S (s + t) x = S s (S t x) := by
  rw [S.operator_add]
  rfl

/-- Every orbit is continuous on nonnegative real time. -/
theorem orbit_continuous (S : StronglyContinuousSemigroup X) (x : X) :
    Continuous fun t : NNReal ↦ S t x :=
  S.strong_continuous' x

end StronglyContinuousSemigroup

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- A domain-valued curve is a forward strong solution when its embedded
ambient curve has the operator derivative within the nonnegative half-line.
Using `HasDerivWithinAt` gives the correct one-sided statement at time zero. -/
def IsForwardStrongSolution
    (A : DomainOperator X D) (trajectory : ℝ → D) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s : ℝ ↦ A.embedding (trajectory s))
      (A.op (trajectory t)) (Ici 0) t

/-- Uniqueness of forward strong solutions with the same embedded initial
state, as a property of the operator.  It is proved for the reduced induction operator
(`FastDynamo/Dynamics/StrongSolutionUniqueness.lean`), the auxiliary product operator
(`productInductionOperator_forwardStrongSolutionsUnique`) and the curl-form product operator
(`productPhysicalInductionOperator_forwardStrongSolutionsUnique`). -/
def ForwardStrongSolutionsUnique (A : DomainOperator X D) : Prop :=
  ∀ (u v : ℝ → D),
    A.IsForwardStrongSolution u →
    A.IsForwardStrongSolution v →
    A.embedding (u 0) = A.embedding (v 0) →
    ∀ t : ℝ, 0 ≤ t → A.embedding (u t) = A.embedding (v t)

/-- A two-sided strong solution restricts to a forward strong solution. -/
theorem IsStrongSolution.isForwardStrongSolution
    (A : DomainOperator X D) {trajectory : ℝ → D}
    (h : A.IsStrongSolution trajectory) :
    A.IsForwardStrongSolution trajectory := by
  intro t _ht
  exact (h t).hasDerivWithinAt

/-- The explicit trajectory of an eigenpair is also a forward strong
solution. -/
theorem isForwardStrongSolution_eigenTrajectory
    (A : DomainOperator X D) (eigenvalue : ℂ) (B : D)
    (hpair : A.IsEigenpair eigenvalue B) :
    A.IsForwardStrongSolution (A.eigenTrajectory eigenvalue B) :=
  (A.isStrongSolution_eigenTrajectory eigenvalue B hpair).isForwardStrongSolution A

end DomainOperator

/-- Explicit realization data saying that a strongly continuous semigroup
evolves every domain datum along a forward strong solution of `A`.

This module constructs no inhabitant: the structure is assumption-bearing here.
Inhabitants are produced elsewhere — by `HilleYosidaRay.realization`
(`FastDynamo/Dynamics/HilleYosida/Realization.lean`) for any operator with a
Hille–Yosida ray and a densely embedded domain, and by `productInductionRealization`
(`FastDynamo/Dynamics/Assembly/ProductSemigroup.lean`) for the all-frequency
induction operator with domain `H²`.  The semigroup `solenoidalInductionSemigroup` on
`L²_σ`, the restriction of the ambient semigroup to an invariant subspace, is described
through its generator instead: `generator_solenoidalInductionSemigroup`
(`FastDynamo/Dynamics/Assembly/SolenoidalGenerator.lean`) identifies that generator with the
part of `L_{ε,u}` in `L²_σ`, with domain `H² ∩ L²_σ` (Engel–Nagel II.2.3). -/
structure DomainOperatorSemigroupRealization
    {X : Type u} {D : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    (S : StronglyContinuousSemigroup X) (A : DomainOperator X D) where
  /-- A domain-valued representative of the semigroup orbit. -/
  domainOrbit : D → ℝ → D
  /-- The representative starts from the prescribed domain datum. -/
  domainOrbit_zero : ∀ B : D, domainOrbit B 0 = B
  /-- The representative solves the forward strong equation. -/
  domainOrbit_isForwardStrongSolution : ∀ B : D,
    A.IsForwardStrongSolution (domainOrbit B)
  /-- On nonnegative times, its embedding is the actual semigroup orbit. -/
  semigroup_eq_embedding_domainOrbit : ∀ (B : D) (t : ℝ), 0 ≤ t →
    S (Real.toNNReal t) (A.embedding B) = A.embedding (domainOrbit B t)

namespace DomainOperatorSemigroupRealization

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {S : StronglyContinuousSemigroup X} {A : DomainOperator X D}

/-- Under forward uniqueness, the semigroup orbit of an eigenvector is the
embedded exponential eigen-trajectory. -/
theorem apply_embedding_eq_embedding_eigenTrajectory
    (R : DomainOperatorSemigroupRealization S A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (eigenvalue : ℂ) (B : D)
    (hpair : A.IsEigenpair eigenvalue B) (t : NNReal) :
    S t (A.embedding B) =
      A.embedding (A.eigenTrajectory eigenvalue B (t : ℝ)) := by
  have hinitial :
      A.embedding (R.domainOrbit B 0) =
        A.embedding (A.eigenTrajectory eigenvalue B 0) := by
    rw [R.domainOrbit_zero, A.eigenTrajectory_zero]
  have horbits := hunique
    (R.domainOrbit B) (A.eigenTrajectory eigenvalue B)
    (R.domainOrbit_isForwardStrongSolution B)
    (A.isForwardStrongSolution_eigenTrajectory eigenvalue B hpair)
    hinitial (t : ℝ) t.coe_nonneg
  calc
    S t (A.embedding B) =
        S (Real.toNNReal (t : ℝ)) (A.embedding B) := by
          rw [Real.toNNReal_coe]
    _ = A.embedding (R.domainOrbit B (t : ℝ)) :=
      R.semigroup_eq_embedding_domainOrbit B (t : ℝ) t.coe_nonneg
    _ = A.embedding (A.eigenTrajectory eigenvalue B (t : ℝ)) :=
      horbits

/-- Exact exponential norm law for the semigroup orbit of an
eigenvector. -/
theorem norm_apply_embedding_eigenvector
    (R : DomainOperatorSemigroupRealization S A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (eigenvalue : ℂ) (B : D)
    (hpair : A.IsEigenpair eigenvalue B) (t : NNReal) :
    ‖S t (A.embedding B)‖ =
      Real.exp ((t : ℝ) * eigenvalue.re) * ‖A.embedding B‖ := by
  rw [R.apply_embedding_eq_embedding_eigenTrajectory
    hunique eigenvalue B hpair t]
  exact A.norm_embedding_eigenTrajectory eigenvalue B (t : ℝ)

/-- A nonzero eigenvector supplies the standard spectral lower bound on the
semigroup operator norm. -/
theorem exp_re_le_operatorNorm
    (R : DomainOperatorSemigroupRealization S A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (eigenvalue : ℂ) (B : D)
    (hpair : A.IsEigenpair eigenvalue B) (t : NNReal) :
    Real.exp ((t : ℝ) * eigenvalue.re) ≤ ‖S t‖ := by
  have hBnorm : 0 < ‖A.embedding B‖ := norm_pos_iff.mpr hpair.1
  apply le_of_mul_le_mul_right _ hBnorm
  calc
    Real.exp ((t : ℝ) * eigenvalue.re) * ‖A.embedding B‖ =
        ‖S t (A.embedding B)‖ :=
      (R.norm_apply_embedding_eigenvector
        hunique eigenvalue B hpair t).symm
    _ ≤ ‖S t‖ * ‖A.embedding B‖ :=
      ContinuousLinearMap.le_opNorm (S t) (A.embedding B)

/-- Combined statement: an eigenpair orbit is the exponential trajectory,
has the exact exponential norm law, and forces the matching lower bound on
the semigroup norm. -/
theorem eigenpair_orbit_and_growth
    (R : DomainOperatorSemigroupRealization S A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (eigenvalue : ℂ) (B : D)
    (hpair : A.IsEigenpair eigenvalue B) (t : NNReal) :
    S t (A.embedding B) =
        A.embedding (A.eigenTrajectory eigenvalue B (t : ℝ)) ∧
      ‖S t (A.embedding B)‖ =
        Real.exp ((t : ℝ) * eigenvalue.re) * ‖A.embedding B‖ ∧
      Real.exp ((t : ℝ) * eigenvalue.re) ≤ ‖S t‖ := by
  exact ⟨R.apply_embedding_eq_embedding_eigenTrajectory
      hunique eigenvalue B hpair t,
    R.norm_apply_embedding_eigenvector
      hunique eigenvalue B hpair t,
    R.exp_re_le_operatorNorm hunique eigenvalue B hpair t⟩

end DomainOperatorSemigroupRealization

namespace StronglyContinuousSemigroup

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/--
**Uniqueness of a realizing semigroup, operator by operator.**  If two strongly
continuous semigroups both realize the same domain operator `A`, forward strong
solutions of `A` are unique, and the domain embeds densely, then the two
evolution operators agree at every time.

On the range of `A.embedding` the two orbits are forward strong solutions of `A`
with the same initial state, so uniqueness identifies them; density then
propagates the identity from that range to all of `X`, both operators being
continuous.  In particular the semigroup generated by a Hille–Yosida ray does not
depend on the choice of resolvent certificate that produced it.
-/
theorem operator_eq_of_realization
    {A : DomainOperator X D} {S T : StronglyContinuousSemigroup X}
    (R : DomainOperatorSemigroupRealization S A)
    (R' : DomainOperatorSemigroupRealization T A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (hdense : DenseRange A.embedding) (t : NNReal) :
    S.operator t = T.operator t := by
  have key : ∀ d : D, S.operator t (A.embedding d) = T.operator t (A.embedding d) := by
    intro d
    have ht : ((Real.toNNReal (t : ℝ)) : NNReal) = t := Real.toNNReal_coe
    have h1 := R.semigroup_eq_embedding_domainOrbit d (t : ℝ) t.coe_nonneg
    have h2 := R'.semigroup_eq_embedding_domainOrbit d (t : ℝ) t.coe_nonneg
    rw [ht] at h1 h2
    rw [h1, h2]
    exact hunique _ _ (R.domainOrbit_isForwardStrongSolution d)
      (R'.domainOrbit_isForwardStrongSolution d)
      (by rw [R.domainOrbit_zero, R'.domainOrbit_zero]) (t : ℝ) t.coe_nonneg
  have heq := hdense.equalizer (S.operator t).continuous (T.operator t).continuous
    (funext key)
  exact ContinuousLinearMap.ext (congrFun heq)

/--
**Uniqueness of a realizing semigroup, bundled.**  Under the hypotheses of
`StronglyContinuousSemigroup.operator_eq_of_realization` the two semigroups are
equal as structures, by `StronglyContinuousSemigroup.ext`.  This is what justifies
speaking of *the* semigroup realizing such an operator.
-/
theorem eq_of_realization
    {A : DomainOperator X D} {S T : StronglyContinuousSemigroup X}
    (R : DomainOperatorSemigroupRealization S A)
    (R' : DomainOperatorSemigroupRealization T A)
    (hunique : A.ForwardStrongSolutionsUnique)
    (hdense : DenseRange A.embedding) :
    S = T :=
  ext fun t ↦ operator_eq_of_realization R R' hunique hdense t

end StronglyContinuousSemigroup

end

end FastDynamo
