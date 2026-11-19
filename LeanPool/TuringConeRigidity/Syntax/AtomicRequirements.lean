/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.AtomicForcing
public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing

/-!
# Atomic Requirements
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

/-- A child of the target name has a tag above `p` and is forced equal to the source name at
`p`. -/
def Witness (a : Name P) : Name P → P → Prop
  | .mk _ b t, p => ∃ j, p ≤ t j ∧ EqForces a (b j) p

/-- Every condition extending `p` fails to force membership of the first name in the second. -/
def NegMem (a b : Name P) (p : P) : Prop := ∀ q, q ≤ p → ¬ MemForces a b q

/-- Conditions giving an explicit membership witness or forcing persistent nonmembership. -/
def MemTest (a b : Name P) : Set P := {p | Witness a b p ∨ NegMem a b p}

/-- A child of either name, active at `p`, is persistently absent from the other name below
`p`. -/
def Refute : Name P → Name P → P → Prop
  | .mk _ a s, .mk _ b t, p =>
    (∃ i, p ≤ s i ∧ NegMem (a i) (.mk _ b t) p) ∨
    (∃ j, p ≤ t j ∧ NegMem (b j) (.mk _ a s) p)

/-- Conditions forcing equality or supplying a child refutation of equality. -/
def EqTest (a b : Name P) : Set P := {p | EqForces a b p ∨ Refute a b p}

theorem witness_mono (a b : Name P) {p q : P} (hq : q ≤ p)
    (h : Witness a b p) : Witness a b q := by
  cases b with
  | mk κ b t =>
    obtain ⟨j,hj,he⟩ := h
    exact ⟨j,hq.trans hj,eq_mono _ _ hq he⟩

theorem witness_mem (a b : Name P) (p : P) (h : Witness a b p) : MemForces a b p := by
  cases b with
  | mk κ b t =>
    intro q hq
    exact ⟨q,le_rfl,witness_mono _ _ hq h⟩

theorem memTest_dense (a b : Name P) : Dense (MemTest a b) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Witness a b q
  · obtain ⟨q,hq,hw⟩ := h
    exact ⟨q,hq,Or.inl hw⟩
  · refine ⟨p,le_rfl,Or.inr ?_⟩
    intro q hq hm
    cases b with
    | mk κ b t =>
      obtain ⟨r,hr,hw⟩ := hm q le_rfl
      exact h ⟨r,hr.trans hq,hw⟩

theorem eqTest_dense (a b : Name P) : Dense (EqTest a b) := by
  classical
  cases a with
  | mk ι a s =>
    cases b with
    | mk κ b t =>
      intro p
      by_cases he : EqForces (.mk ι a s) (.mk κ b t) p
      · exact ⟨p,le_rfl,Or.inl he⟩
      · change ¬ ((∀ i, Below p (s i) _) ∧ (∀ j, Below p (t j) _)) at he
        simp only [not_and_or, not_forall, Below] at he
        rcases he with ⟨i,q,hq⟩ | ⟨j,q,hq⟩
        · obtain ⟨hqp,hqs,hn⟩ := hq
          refine ⟨q,hqp,Or.inr (Or.inl ⟨i,hqs,?_⟩)⟩
          intro r hr hm
          obtain ⟨w,hw,k,hk,hf⟩ := hm r le_rfl
          exact hn ⟨w,hw.trans hr,k,hk,hf⟩
        · obtain ⟨hqp,hqt,hn⟩ := hq
          refine ⟨q,hqp,Or.inr (Or.inr ⟨j,hqt,?_⟩)⟩
          intro r hr hm
          obtain ⟨w,hw,i,hi,hf⟩ := hm r le_rfl
          exact hn ⟨w,hw.trans hr,i,hi,eq_symm _ _ _ hf⟩

/-- The filter meets both atomic membership and equality decision families for names in `N`. -/
structure Generic (N : Set (Name P)) (G : GenericFilter P) : Prop where
  memTest : ∀ a ∈ N, ∀ b ∈ N, ∃ p ∈ G.carrier, p ∈ MemTest a b
  eqTest : ∀ a ∈ N, ∀ b ∈ N, ∃ p ∈ G.carrier, p ∈ EqTest a b

theorem generic_witness {N : Set (Name P)} {G : GenericFilter P}
    (hG : Generic N G) {a b : Name P} (ha : a ∈ N) (hb : b ∈ N)
    {p : P} (hp : p ∈ G.carrier) (hm : MemForces a b p) :
    ∃ q ∈ G.carrier, Witness a b q := by
  obtain ⟨q,hq,hw | hn⟩ := hG.memTest a ha b hb
  · exact ⟨q,hq,hw⟩
  · obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact False.elim (hn r hrq (mem_mono _ _ hrp hm))

end TuringRigidity.AtomicForcing

end OAI
