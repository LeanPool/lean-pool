/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import LeanPool.NavierStokesAndEuler.ForMathlib.ElaborationShortcuts

/-!
# Shortcut instances for concrete real normed spaces

Instance resolution on a concrete function space (an `Lp` space, a closed submodule of a product
of `Lp` spaces, a space of continuous linear maps between them) has to rediscover each derived
structure such as `AddCommMonoid`, `Module ℝ` or `TopologicalSpace` by search. On such carriers the
search explores many failing subobject and algebra branches before it succeeds, and it is repeated
in every declaration that mentions the space.

The commands of this file record, for a given carrier `X`, the instances that resolution currently
finds, and register them as instances of `X` itself:

* `normed_group_shortcut_instances p binders : X` records `NormedAddCommGroup X` and the additive,
  metric and topological structures derived from it;
* `normed_space_shortcut_instances p binders : X` records `NormedSpace ℝ X` and the scalar
  structures derived from it;
* `real_normed_space_shortcut_instances p binders : X` does both.

Each instance is named `p.inst` followed by the class name, and unfolds to the instance found by
the search. All of them are elaborated before any is registered, so the recorded instances are
exactly the ones that resolution selects without the shortcuts: terms elaborated with and without
them agree up to unfolding the shortcut. A later query for one of these structures on `X` is
answered by its shortcut, without a search.

The one exception is `SeminormedAddCommGroup X`, which is recorded as the seminormed group
underlying the recorded `NormedAddCommGroup X`. A hypothesis list
`[NormedAddCommGroup E] [NormedSpace ℝ E]` states its second hypothesis over that seminormed
group, so the recorded `NormedSpace ℝ X` then matches such a request without comparing two
seminormed structures field by field.
-/

public section

open Lean in
/-- `normed_group_shortcut_instances p binders : X` registers the instances currently found for
`NormedAddCommGroup X` and for the additive, metric and topological structures of `X` as instances
named `p.inst` followed by the class name. -/
macro "normed_group_shortcut_instances " p:ident bs:bracketedBinder* " : " X:term : command => do
  let nm (s : String) : Ident := mkIdentFrom p (p.getId ++ Name.mkSimple ("inst" ++ s))
  `(@[expose, reducible] def $(nm "NormedAddCommGroup") $bs* : NormedAddCommGroup $X :=
      inferInstance
    @[expose, reducible] def $(nm "SeminormedAddCommGroup") $bs* : SeminormedAddCommGroup $X :=
      @NormedAddCommGroup.toSeminormedAddCommGroup _ inferInstance
    @[expose, reducible] def $(nm "NormedAddGroup") $bs* : NormedAddGroup $X := inferInstance
    @[expose, reducible] def $(nm "SeminormedAddGroup") $bs* : SeminormedAddGroup $X :=
      inferInstance
    @[expose, reducible] def $(nm "AddCommGroup") $bs* : AddCommGroup $X := inferInstance
    @[expose, reducible] def $(nm "AddCommMonoid") $bs* : AddCommMonoid $X := inferInstance
    @[expose, reducible] def $(nm "AddGroup") $bs* : AddGroup $X := inferInstance
    @[expose, reducible] def $(nm "SubNegMonoid") $bs* : SubNegMonoid $X := inferInstance
    @[expose, reducible] def $(nm "AddMonoid") $bs* : AddMonoid $X := inferInstance
    @[expose, reducible] def $(nm "AddZeroClass") $bs* : AddZeroClass $X := inferInstance
    @[expose, reducible] def $(nm "Add") $bs* : Add $X := inferInstance
    @[expose, reducible] def $(nm "Zero") $bs* : Zero $X := inferInstance
    @[expose, reducible] def $(nm "Neg") $bs* : Neg $X := inferInstance
    @[expose, reducible] def $(nm "Sub") $bs* : Sub $X := inferInstance
    @[expose, reducible] def $(nm "Norm") $bs* : Norm $X := inferInstance
    @[expose, reducible] def $(nm "MetricSpace") $bs* : MetricSpace $X := inferInstance
    @[expose, reducible] def $(nm "PseudoMetricSpace") $bs* : PseudoMetricSpace $X :=
      inferInstance
    @[expose, reducible] def $(nm "UniformSpace") $bs* : UniformSpace $X := inferInstance
    @[expose, reducible] def $(nm "TopologicalSpace") $bs* : TopologicalSpace $X :=
      inferInstance
    theorem $(nm "ContinuousAdd") $bs* : ContinuousAdd $X := inferInstance
    theorem $(nm "ContinuousNeg") $bs* : ContinuousNeg $X := inferInstance
    theorem $(nm "ContinuousSub") $bs* : ContinuousSub $X := inferInstance
    theorem $(nm "IsTopologicalAddGroup") $bs* : IsTopologicalAddGroup $X := inferInstance
    theorem $(nm "IsUniformAddGroup") $bs* : IsUniformAddGroup $X := inferInstance
    attribute [instance] $(nm "NormedAddCommGroup") $(nm "SeminormedAddCommGroup")
      $(nm "NormedAddGroup") $(nm "SeminormedAddGroup") $(nm "AddCommGroup")
      $(nm "AddCommMonoid") $(nm "AddGroup") $(nm "SubNegMonoid") $(nm "AddMonoid")
      $(nm "AddZeroClass") $(nm "Add") $(nm "Zero") $(nm "Neg") $(nm "Sub") $(nm "Norm")
      $(nm "MetricSpace") $(nm "PseudoMetricSpace") $(nm "UniformSpace")
      $(nm "TopologicalSpace") $(nm "ContinuousAdd") $(nm "ContinuousNeg")
      $(nm "ContinuousSub") $(nm "IsTopologicalAddGroup") $(nm "IsUniformAddGroup"))

open Lean in
/-- `normed_space_shortcut_instances p binders : X` registers the instances currently found for
`NormedSpace ℝ X` and for the scalar structures of `X` as instances named `p.inst` followed by the
class name. It is meant to follow `normed_group_shortcut_instances p binders : X`. -/
macro "normed_space_shortcut_instances " p:ident bs:bracketedBinder* " : " X:term : command => do
  let nm (s : String) : Ident := mkIdentFrom p (p.getId ++ Name.mkSimple ("inst" ++ s))
  `(@[expose, reducible] def $(nm "NormedSpace") $bs* : NormedSpace ℝ $X := inferInstance
    @[expose, reducible] def $(nm "Module") $bs* : Module ℝ $X := inferInstance
    @[expose, reducible] def $(nm "DistribMulAction") $bs* : DistribMulAction ℝ $X :=
      inferInstance
    @[expose, reducible] def $(nm "MulAction") $bs* : MulAction ℝ $X := inferInstance
    @[expose, reducible] def $(nm "DistribSMul") $bs* : DistribSMul ℝ $X := inferInstance
    @[expose, reducible] def $(nm "SMulZeroClass") $bs* : SMulZeroClass ℝ $X := inferInstance
    @[expose, reducible] def $(nm "MulActionWithZero") $bs* : MulActionWithZero ℝ $X :=
      inferInstance
    @[expose, reducible] def $(nm "SMulWithZero") $bs* : SMulWithZero ℝ $X := inferInstance
    @[expose, reducible] def $(nm "SMul") $bs* : SMul ℝ $X := inferInstance
    theorem $(nm "ContinuousSMul") $bs* : ContinuousSMul ℝ $X := inferInstance
    theorem $(nm "ContinuousConstSMul") $bs* : ContinuousConstSMul ℝ $X := inferInstance
    theorem $(nm "IsBoundedSMul") $bs* : IsBoundedSMul ℝ $X := inferInstance
    theorem $(nm "NormSMulClass") $bs* : NormSMulClass ℝ $X := inferInstance
    attribute [instance] $(nm "NormedSpace") $(nm "Module") $(nm "DistribMulAction")
      $(nm "MulAction") $(nm "DistribSMul") $(nm "SMulZeroClass") $(nm "MulActionWithZero")
      $(nm "SMulWithZero") $(nm "SMul") $(nm "ContinuousSMul") $(nm "ContinuousConstSMul")
      $(nm "IsBoundedSMul") $(nm "NormSMulClass"))

/-- `real_normed_space_shortcut_instances p binders : X` combines
`normed_group_shortcut_instances p binders : X` and
`normed_space_shortcut_instances p binders : X`. -/
macro "real_normed_space_shortcut_instances " p:ident bs:bracketedBinder* " : " X:term :
    command =>
  `(normed_group_shortcut_instances $p $bs* : $X
    normed_space_shortcut_instances $p $bs* : $X)

end
