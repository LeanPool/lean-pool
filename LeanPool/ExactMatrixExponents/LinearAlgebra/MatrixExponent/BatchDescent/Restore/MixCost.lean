/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
import Mathlib.Tactic.Ring

/-! # Shared cost bounds for reset mixers -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template.Mix
open BatchDescent.Phase Coloring

variable {I : Type*} {F : I → Type} {T : (i : I) → Template (F i)}
  {k d n : I → ℕ} {large small height hosts : I → ℕ}
  (largeTwo : ∀ i, 2 ≤ large i) (smallTwo : ∀ i, 2 ≤ small i)
  (smallLeLarge : ∀ i, small i ≤ large i)

local notation "Cost" => MixedCost large small height hosts
local notation "TemplateCost" =>
  MixedCost large small (fun i => Scheme.h (Template.scheme (T i)))
    (fun i => Scheme.m (Template.scheme (T i)))
local notation "TemplateRow" =>
  MixedCost large small (fun i => Scheme.h (Template.scheme (T i))) (fun _ => 0)

include largeTwo smallTwo in
private theorem pair_mixed {A B : I → Format}
    (first : Cost (fun i => (A i).width)) (second : Cost (fun i => (B i).width)) :
    Cost (fun i => ((A i).pair (B i)).width) :=
  (first.add second largeTwo smallTwo).mono fun _ => (Format.width_pair ..).le

include largeTwo smallTwo smallLeLarge

/-- Charge a projection from the two widths it reads. -/
theorem project_mixed {A B : I → Format}
    (first : Cost (fun i => (A i).width)) (second : Cost (fun i => (B i).width)) :
    Cost (fun i => project (A i) (B i)) :=
  (first.add (second.scale 2 smallTwo smallLeLarge) largeTwo smallTwo).scale
    4 smallTwo smallLeLarge

/-- Combine the source projection and the tally work at every host. -/
theorem tallyCost_mixed
    (format : TemplateCost (fun i => (T i).format.width))
    (sources : TemplateCost (fun i => (Sources (T i)).width))
    (digits : TemplateRow (fun i => (Digits (T i) (d i)).width))
    (split : TemplateRow (fun i => (Split (T i) (d i)).width))
    (shortCall : TemplateRow (fun i => 2 ^ (T i).scheme.h * (1 + arity (T i) (k i) (d i))))
    (longCall : TemplateRow (fun i => 1 + arity (T i) (k i) (d i)))
    (batch : TemplateRow (fun i => 2 ^ (T i).scheme.h * (100 + d i) ^ 5))
    (collect : TemplateRow (fun i =>
      Mixing.collectCost (T i).scheme.h (T i).scheme.d (T i).CounterBits)) :
    TemplateCost (fun i => tallyCost (T i) (k i) (d i)) := by
  have projection := project_mixed largeTwo smallTwo smallLeLarge digits split
  have rest := (batch.scale 4 smallTwo smallLeLarge).add longCall largeTwo smallTwo
  have rest := rest.add (collect.scale 4 smallTwo smallLeLarge) largeTwo smallTwo
  have tally := (shortCall.add projection largeTwo smallTwo).add rest largeTwo smallTwo
  exact (project_mixed largeTwo smallTwo smallLeLarge format sources).add
    (tally.hosts fun i => (T i).scheme.m) largeTwo smallTwo

/-- Combine travel, neighborhood, and next-window charges. -/
theorem gatherCost_mixed
    (travel : Cost (fun i => (Travel (T i) (k i)).width))
    (network : Cost (fun i => ((T i).NetworkDepths (k i)).width))
    (near : Cost (fun i => (T i).nearCost (k i)))
    (next : Cost (fun i => ((T i).Next (k i)).width))
    (windows : Cost (fun i => (Windows (T i) (k i)).width)) :
    Cost (fun i => gatherCost (T i) (k i)) := by
  have initial := (travel.scale 24 smallTwo smallLeLarge).add
    (project_mixed largeTwo smallTwo smallLeLarge travel network) largeTwo smallTwo
  have final := project_mixed largeTwo smallTwo smallLeLarge
    (pair_mixed largeTwo smallTwo travel next) windows
  exact (initial.add near largeTwo smallTwo).add final largeTwo smallTwo

/-- Combine the one-time depth projection with the cost of each wave. -/
theorem waveCost_mixed
    (network : TemplateCost (fun i => ((T i).NetworkDepths (k i)).width))
    (depth : TemplateCost (fun i => ((T i).Depths (k i)).width))
    (gather : TemplateCost (fun i => gatherCost (T i) (k i)))
    (call : TemplateRow (fun i => 1 + arity (T i) (k i) (d i)))
    (waves : Poly small n) :
    TemplateCost (fun i => waveCost (T i) (k i) (d i) (n i)) := by
  have each := (network.scale 24 smallTwo smallLeLarge).add gather largeTwo smallTwo
  have each := each.add (call.hosts fun i => (T i).scheme.m) largeTwo smallTwo
  have all := (each.mul waves smallLeLarge).mono
    (fun i => (Nat.mul_comm (n i) _).le)
  exact (project_mixed largeTwo smallTwo smallLeLarge network depth).add
    all largeTwo smallTwo

/-- Combine the two passes over the host records with the final profile projection. -/
theorem profileCost_mixed
    (network : TemplateCost (fun i => ((T i).NetworkDepths (k i)).width))
    (travel : TemplateCost (fun i => (Travel (T i) (k i)).width))
    (gather : TemplateCost (fun i => gatherCost (T i) (k i)))
    (sources : TemplateCost (fun i => (Sources (T i)).width))
    (longCall : TemplateRow (fun i => 1 + arity (T i) (k i) (d i)))
    (shortCall : TemplateRow (fun i => 2 ^ (T i).scheme.h * (1 + arity (T i) (k i) (d i))))
    (sides : TemplateCost (fun i => (Sides (T i) (k i)).width))
    (rows : TemplateCost (fun i => ((T i).profileShape (k i)).width)) :
    TemplateCost (fun i => profileCost (T i) (k i) (d i)) := by
  have survey := project_mixed largeTwo smallTwo smallLeLarge network travel
  have survey := (survey.add gather largeTwo smallTwo).add
    (longCall.hosts fun i => (T i).scheme.m) largeTwo smallTwo
  have collect := (project_mixed largeTwo smallTwo smallLeLarge network sources).add
    (shortCall.hosts fun i => (T i).scheme.m) largeTwo smallTwo
  have start := (network.scale 20 smallTwo smallLeLarge).add survey largeTwo smallTwo
  exact (start.add collect largeTwo smallTwo).add
    (project_mixed largeTwo smallTwo smallLeLarge sides rows) largeTwo smallTwo

/-- Combine the reset mixer charges using the template's first and second record formats. -/
theorem cost_mixed
    (format : TemplateCost (fun i => (T i).format.width))
    (stats : TemplateCost (fun i => (Stats (T i) (k i)).width))
    (depth : TemplateCost (fun i => ((T i).Depths (k i)).width))
    (network : TemplateCost (fun i => ((T i).NetworkDepths (k i)).width))
    (tally : TemplateCost (fun i => tallyCost (T i) (k i) (d i)))
    (wave : TemplateCost (fun i => waveCost (T i) (k i) (d i) (n i)))
    (profile : TemplateCost (fun i => profileCost (T i) (k i) (d i)))
    (extract : TemplateCost (fun i => Mixing.extractionCost (T i).scheme.m (T i).widthCols
      (T i).scheme.h (k i) (T i).profileBits (d i) +
        Mixing.cost ((T i).scheme.m + (T i).widthCols) (T i).scheme.h (k i) (d i))) :
    TemplateCost (fun i => cost (T i) (k i) (d i) (n i)) := by
  have first := pair_mixed largeTwo smallTwo format stats
  have both := pair_mixed largeTwo smallTwo first depth
  have start := (format.scale 48 smallTwo smallLeLarge).add tally largeTwo smallTwo
  have start := start.add (first.scale 24 smallTwo smallLeLarge) largeTwo smallTwo
  have start := start.add (project_mixed largeTwo smallTwo smallLeLarge first network)
    largeTwo smallTwo
  have middle := (start.add wave largeTwo smallTwo).add
    (both.scale 20 smallTwo smallLeLarge) largeTwo smallTwo
  have middle := middle.add (project_mixed largeTwo smallTwo smallLeLarge both network)
    largeTwo smallTwo
  have finish := (middle.add profile largeTwo smallTwo).add extract largeTwo smallTwo
  refine (finish.add (project_mixed largeTwo smallTwo smallLeLarge both stats)
    largeTwo smallTwo).mono fun i => ?_
  unfold cost
  rw [add_assoc _ (Mixing.extractionCost ..)]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template.Mix

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.History.Reset.Child
open BatchDescent.Phase

/-- The four exponential factors in the header builder share one host-indexed budget. -/
theorem buildCost_mixed {I : Type*} {large small height hosts old growth new : I → ℕ}
    (largeTwo : ∀ i, 2 ≤ large i) (hostBound : Poly large hosts)
    (oldBound : Poly large (fun i => 2 ^ old i)) (growthBound : Poly large (fun i => 2 ^ growth i))
    (newBound : Poly large (fun i => 2 ^ new i)) :
    MixedCost large small height hosts
      (fun i => buildCost (hosts i) (old i) (growth i) (new i)) := by
  have head := ((Poly.const largeTwo 1000).mul growthBound).mul newBound
  have tail := ((Poly.const largeTwo 4).add growthBound.of_exp).add hostBound
  refine (MixedCost.long hosts (((head.mul oldBound).mul
    ((Poly.const largeTwo 2).add oldBound.of_exp)).mul tail)).mono fun i => ?_
  unfold buildCost
  rw [pow_add, pow_add, pow_add]
  exact le_of_eq (by ring)

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.History.Reset.Child
