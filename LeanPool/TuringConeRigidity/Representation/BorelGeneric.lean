/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/BorelGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.ProgramSelection

/-!
# Borel Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BorelGeneric
open Set

/-- Decode a finite binary word, with the empty word as the fallback. -/
def word (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []

theorem word_surjective : Function.Surjective word := by
  intro s
  exact ⟨Encodable.encode s,by simp [word]⟩

/-- The second coded word strictly extends the first. -/
def Ext (s t : ℕ) : Prop := word s <+: word t ∧ (word s).length < (word t).length

variable {X : Type*} [MeasurableSpace X]
variable (R : X → ℕ → ℕ → Prop)
variable (hd : ∀ x n s, ∃ t, Ext s t ∧ R x n t)

/-- Choose the least coded strict extension meeting the next requirement for the parameter. -/
noncomputable def next (n : ℕ) (z : X × ℕ) : ℕ :=
  leastSuccess (fun z t => Ext z.2 t ∧ R z.1 n t) (fun z => hd z.1 n z.2) z

omit [MeasurableSpace X] in
theorem next_spec (n : ℕ) (x : X) (s : ℕ) :
    Ext s (next R hd n (x,s)) ∧ R x n (next R hd n (x,s)) :=
  leastSuccess_spec (fun z : X × ℕ => fun t => Ext z.2 t ∧ R z.1 n t)
    (fun z => hd z.1 n z.2) (x,s)

theorem next_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) (n : ℕ) :
    Measurable (next R hd n) := by
  apply leastSuccess_measurable
  intro t
  exact ((Set.to_countable {s : ℕ | Ext s t}).measurableSet.preimage measurable_snd).inter
    ((hR n t).preimage measurable_fst)

/-- The sequence of chosen word codes meeting successive parameterized requirements. -/
noncomputable def stage : ℕ → X → ℕ
  | 0 => fun _ => Encodable.encode ([] : List Bool)
  | n+1 => fun x => next R hd n (x,stage n x)

theorem stage_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    ∀ n, Measurable (stage R hd n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (next_measurable R hd hR n).comp (measurable_id.prodMk ih)

omit [MeasurableSpace X] in
theorem stage_prefix (x : X) (n : ℕ) :
    word (stage R hd n x) <+: word (stage R hd (n+1) x) :=
  (next_spec R hd n x (stage R hd n x)).1.1

omit [MeasurableSpace X] in
theorem stage_length (x : X) (n : ℕ) : n ≤ (word (stage R hd n x)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h := (next_spec R hd n x (stage R hd n x)).1.2
    change n+1 ≤ (word (next R hd n (x,stage R hd n x))).length
    omega

omit [MeasurableSpace X] in
theorem stage_prefix_of_le (x : X) {n m : ℕ} (h : n ≤ m) :
    word (stage R hd n x) <+: word (stage R hd m x) := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m h ih => exact ih.trans (stage_prefix R hd x m)

/-- The oracle obtained from the diagonal bits of the increasing coded-word sequence. -/
noncomputable def generic (x : X) : Oracle :=
  fun i => (word (stage R hd (i+1) x)).getD i false

theorem generic_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    Measurable (generic R hd) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_of_countable (fun k : ℕ => (word k).getD i false)).comp
    (stage_measurable R hd hR (i+1))

/-- The oracle realizes every bit of the coded finite word. -/
def Meets (A : Oracle) (s : ℕ) : Prop :=
  ∀ i, i < (word s).length → A i = (word s).getD i false

private theorem getD_prefix {s t : List Bool} (h : s <+: t) (i : ℕ) (hi : i < s.length) :
    s.getD i false = t.getD i false := by
  obtain ⟨u,rfl⟩ := h
  simp [List.getD, List.getElem?_append, hi]

omit [MeasurableSpace X] in
theorem meets_stage (x : X) (n : ℕ) : Meets (generic R hd x) (stage R hd n x) := by
  intro i hi
  dsimp only [generic]
  rcases le_total n (i+1) with hn | hn
  · exact (getD_prefix (stage_prefix_of_le R hd x hn) i hi).symm
  · exact getD_prefix (stage_prefix_of_le R hd x hn) i (by
      have hl := stage_length R hd x (i+1)
      omega)

include hd in
theorem borel_generic_selection (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ G : X → Oracle, Measurable G ∧ ∀ x n, ∃ t, R x n t ∧ Meets (G x) t := by
  refine ⟨generic R hd,generic_measurable R hd hR,?_⟩
  intro x n
  exact ⟨stage R hd (n+1) x,(next_spec R hd n x (stage R hd n x)).2,
    meets_stage R hd x (n+1)⟩

end TuringRigidity.BorelGeneric

end OAI
