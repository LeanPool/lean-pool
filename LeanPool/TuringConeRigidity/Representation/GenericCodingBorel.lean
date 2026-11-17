/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericCodingBorel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import LeanPool.TuringConeRigidity.Representation.GenericCoding

/-!
# Generic Coding Borel
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericCoding
open Set UniformOracle BinarySeries

theorem query_measurable {X : Type*} [MeasurableSpace X]
    (A : X → Oracle) (q : X → ℕ) (hA : Measurable A) (hq : Measurable q) :
    Measurable (fun x => A x (q x)) := by
  apply measurable_to_countable'
  intro b
  change MeasurableSet {x | A x (q x) = b}
  have he : {x | A x (q x) = b} = ⋃ n : ℕ, {x | q x = n} ∩ {x | A x n = b} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff]
    exact ⟨fun h => ⟨q x,rfl,h⟩,fun ⟨n,hn,h⟩ => by simpa [hn] using h⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurableSet_eq_fun hq measurable_const).inter
    (measurableSet_eq_fun ((measurable_pi_apply n).comp hA) measurable_const))

theorem count_measurable (n : ℕ) : Measurable (fun G : Oracle => count G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hb : Measurable (fun G : Oracle => bit G (2*n+1)) :=
      (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
        (measurable_pi_apply (2*n+1))
    exact (measurable_of_countable (fun z : ℕ × ℕ => z.1+z.2)).comp (ih.prodMk hb)

theorem code_measurable : Measurable (Function.uncurry code) := by
  apply Measurable.of_eval
  intro n
  have hc : Measurable (fun p : Oracle × Oracle => count p.2 n) := (count_measurable n).comp
    measurable_snd
  have ha := query_measurable (fun p : Oracle × Oracle => p.1) (fun p => count p.2 n)
    measurable_fst hc
  have hi : Measurable (fun p : Oracle × Oracle => 2*(n-count p.2 n)) :=
    (measurable_of_countable (fun k : ℕ => 2*(n-k))).comp hc
  have he := query_measurable (fun p : Oracle × Oracle => p.2) _ measurable_snd hi
  have ho : Measurable (fun p : Oracle × Oracle => p.2 (2*n+1)) :=
    (measurable_pi_apply (2*n+1)).comp measurable_snd
  exact (measurable_of_countable (fun z : Bool × Bool × Bool => if z.1 then z.2.1 else z.2.2)).comp
    (ho.prodMk (ha.prodMk he))

end TuringRigidity.GenericCoding

end OAI
