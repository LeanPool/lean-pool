/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonIdealSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdealSearch
public import LeanPool.TuringConeRigidity.Representation.CommonIdealBorel

/-!
# Common Ideal Selection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

def even (G : Oracle) : Oracle := fun n => G (2*n)
def odd (G : Oracle) : Oracle := fun n => G (2*n+1)
def pad (s : List Bool) : Oracle := fun n => s.getD n false

theorem pad_extends (s : List Bool) : Extends (pad s) s := fun _ _ => rfl

theorem extends_of_prefix {G : Oracle} {s t : List Bool} (h : s <+: t)
    (ht : Extends G t) : Extends G s := by
  obtain ⟨u,rfl⟩ := h
  intro i hi
  rw [ht i (by simp; omega)]
  simp [List.getD,List.getElem?_append,hi]

theorem join_columns (G : Oracle) : join (even G) (odd G) = G := by
  funext n
  have hn := Nat.bodd_add_div2 n
  cases hb : n.bodd with
  | false =>
    have he : 2*(n/2) = n := by simpa [hb,Nat.div2_val] using hn
    simp [join,even,hb,he]
  | true =>
    have he : 2*(n/2)+1 = n := by simpa [hb,Nat.div2_val,Nat.add_comm] using hn
    simp [join,odd,hb,he]

def Embeds (r s t : List Bool) : Prop :=
  ∀ G : Oracle, Extends G r → Extends (even G) s ∧ Extends (odd G) t

theorem embeds_initialWord (s t : List Bool) (M : ℕ)
    (hs : 2 * s.length ≤ M) (ht : 2 * t.length ≤ M) :
    Embeds (initialWord (join (pad s) (pad t)) M) s t := by
  intro G hG
  constructor
  · intro i hi
    have hh := hG (2*i) (by simp; omega)
    rw [prefix_getD _ _ _ (by omega),join_even] at hh
    exact hh
  · intro i hi
    have hh := hG (2*i+1) (by simp; omega)
    rw [prefix_getD _ _ _ (by omega),join_odd] at hh
    exact hh

theorem join_extends_input (r u v : List Bool)
    (hu : initialWord (even (pad r)) r.length <+: u)
    (hv : initialWord (odd (pad r)) r.length <+: v) :
    Extends (join (pad u) (pad v)) r := by
  have hU := extends_of_prefix hu (pad_extends u)
  have hV := extends_of_prefix hv (pad_extends v)
  intro n hn
  have hhalf : n/2 < r.length := by omega
  have hU' := hU (n/2) (by simpa using hhalf)
  have hV' := hV (n/2) (by simpa using hhalf)
  rw [prefix_getD _ _ _ hhalf] at hU' hV'
  have heq : join (pad u) (pad v) n = join (even (pad r)) (odd (pad r)) n := by
    unfold join
    split
    · exact hV'
    · exact hU'
  rw [heq,join_columns]
  rfl

def family (A : Oracle) (n c : ℕ) : Prop :=
  ∃ s t : List Bool, Embeds (BorelGeneric.word c) s t ∧
    Requirement A (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2) s t

theorem family_dense (A : Oracle) (n c : ℕ) :
    ∃ d, BorelGeneric.Ext c d ∧ family A n d := by
  let r := BorelGeneric.word c
  obtain ⟨u,v,hu,hv,hR⟩ := requirement_dense A
    (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2)
    (initialWord (even (pad r)) r.length) (initialWord (odd (pad r)) r.length)
  let M := 2*(u.length+v.length+r.length+1)
  let w := initialWord (join (pad u) (pad v)) M
  obtain ⟨d,hd⟩ := BorelGeneric.word_surjective w
  refine ⟨d,?_,?_⟩
  · constructor
    · rw [hd]
      exact prefix_of_extends (join_extends_input r u v hu hv) (by dsimp [M]; omega)
    · rw [hd]
      simp only [w,prefix_length]
      dsimp [M,r]
      omega
  · refine ⟨u,v,?_,hR⟩
    rw [hd]
    exact embeds_initialWord u v M (by dsimp [M]; omega) (by dsimp [M]; omega)

theorem family_measurable (n c : ℕ) : MeasurableSet {A | family A n c} := by
  simp only [family,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro t
  by_cases he : Embeds (BorelGeneric.word c) s t
  · simpa [he] using requirement_measurable
      (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2) s t
  · simp [he]

theorem family_mono {A : Oracle} {n c d : ℕ}
    (hcd : BorelGeneric.word c <+: BorelGeneric.word d) (h : family A n c) :
    family A n d := by
  obtain ⟨s,t,he,hR⟩ := h
  exact ⟨s,t,fun G hG => he G (extends_of_prefix hcd hG),hR⟩

theorem ideal_of_family (A G : Oracle)
    (h : ∀ n, ∃ c, family A n c ∧ BorelGeneric.Meets G c) :
    ∀ b : Degree, b ≤ degree A ↔
      b ≤ degree (join A (even G)) ∧ b ≤ degree (join A (odd G)) := by
  apply ideal_of_meets
  intro p q
  obtain ⟨i,hi⟩ := codeEnumeration_surjective p
  obtain ⟨j,hj⟩ := codeEnumeration_surjective q
  obtain ⟨c,⟨s,t,he,hR⟩,hG⟩ := h (Nat.pair i j)
  have hh := he G hG
  refine ⟨s,t,hh.1,hh.2,?_⟩
  simpa only [Nat.unpair_pair,hi,hj] using hR

theorem borel_selected_common_ideal :
    ∃ G0 G1 : Oracle → Oracle, Measurable G0 ∧ Measurable G1 ∧
      ∀ (A : Oracle) (b : Degree), b ≤ degree A ↔
        b ≤ degree (join A (G0 A)) ∧ b ≤ degree (join A (G1 A)) := by
  obtain ⟨G,hG,hmeet⟩ := BorelGeneric.borel_generic_selection family family_dense family_measurable
  refine ⟨fun A => even (G A),fun A => odd (G A),?_,?_,?_⟩
  · apply Measurable.of_eval
    intro n
    exact (measurable_pi_apply (2*n)).comp hG
  · apply Measurable.of_eval
    intro n
    exact (measurable_pi_apply (2*n+1)).comp hG
  · intro A
    exact ideal_of_family A (G A) (hmeet A)

theorem borel_selected_common_ideal_with
    (S : Oracle → ℕ → ℕ → Prop)
    (hS : ∀ n c, MeasurableSet {A | S A n c})
    (hd : ∀ A n c, ∃ d, BorelGeneric.Ext c d ∧ S A n d) :
    ∃ G : Oracle → Oracle, Measurable G ∧ ∀ A,
      (∀ b : Degree, b ≤ degree A ↔
        b ≤ degree (join A (even (G A))) ∧ b ≤ degree (join A (odd (G A)))) ∧
      (∀ n, ∃ c, S A n c ∧ BorelGeneric.Meets (G A) c) := by
  let R : Oracle → ℕ → ℕ → Prop := fun A n c =>
    if (Nat.unpair n).1 = 0 then family A (Nat.unpair n).2 c else S A (Nat.unpair n).2 c
  have hRd : ∀ A n c, ∃ d, BorelGeneric.Ext c d ∧ R A n d := by
    intro A n c
    dsimp only [R]
    split
    · exact family_dense A _ c
    · exact hd A _ c
  have hRm : ∀ n c, MeasurableSet {A | R A n c} := by
    intro n c
    dsimp only [R]
    split
    · exact family_measurable _ c
    · exact hS _ c
  obtain ⟨G,hG,hm⟩ := BorelGeneric.borel_generic_selection R hRd hRm
  refine ⟨G,hG,fun A => ⟨?_,?_⟩⟩
  · apply ideal_of_family
    intro n
    simpa only [R,Nat.unpair_pair,ite_true] using hm A (Nat.pair 0 n)
  · intro n
    simpa only [R,Nat.unpair_pair,show ¬ (1 : ℕ) = 0 by omega,ite_false] using hm A (Nat.pair 1 n)

end TuringRigidity.CommonIdeal

end OAI
