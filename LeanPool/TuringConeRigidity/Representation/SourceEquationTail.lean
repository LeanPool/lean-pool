/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceEquationTail.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenBorelForcing
public import LeanPool.TuringConeRigidity.CohenForcing.ForcingSymmetry

/-!
# Source Equation Tail
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SourceEquationTail
open Set CountableForcing
variable {P Q : Type*} [Preorder P] [Preorder Q]

/-- The product filter consisting of pairs whose two coordinates belong to the corresponding
filters. -/
def productFilter (G : GenericFilter P) (H : GenericFilter Q) : GenericFilter (P × Q) where
  carrier := {p | p.1 ∈ G.carrier ∧ p.2 ∈ H.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    obtain ⟨q,hq⟩ := H.nonempty
    exact ⟨(p,q),hp,hq⟩
  upper := fun hpq hp => ⟨G.upper hpq.1 hp.1,H.upper hpq.2 hp.2⟩
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp.1 hq.1
    obtain ⟨s,hs,hsp,hsq⟩ := H.directed hp.2 hq.2
    exact ⟨(r,s),⟨hr,hs⟩,⟨hrp,hsp⟩,⟨hrq,hsq⟩⟩

theorem truth_liftFirst [OrderTop Q] (a : Sentence P)
    (G : GenericFilter P) (H : GenericFilter Q) :
    Sentence.Truth (productFilter G H) (Sentence.liftFirst a) ↔ Sentence.Truth G a := by
  induction a with
  | ground a => exact Iff.rfl
  | member p =>
    obtain ⟨q,hq⟩ := H.nonempty
    exact ⟨fun h => h.1,fun h => ⟨h,H.upper le_top hq⟩⟩
  | conj a b ha hb => exact and_congr ha hb
  | existsNat a ha => exact exists_congr ha
  | neg a ha => exact not_congr ha

theorem requirements_liftFirst [OrderTop Q] (a : Sentence P) (n : ℕ) (p : P) (q : Q) :
    (p,q) ∈ Sentence.Requirements (Sentence.liftFirst a) n ↔
      p ∈ Sentence.Requirements a n := by
  induction a generalizing n with
  | ground a => exact Iff.rfl
  | member r => exact Iff.rfl
  | conj a b ha hb =>
    simp only [Sentence.liftFirst,Sentence.Requirements]
    split <;> first | exact ha _ | exact hb _
  | existsNat a ha => exact ha _ _
  | neg a ha =>
    simp only [Sentence.liftFirst,Sentence.Requirements]
    split
    · exact or_congr (Sentence.forces_liftFirst a p q) (Sentence.forces_liftFirst (.neg a) p q)
    · exact ha _

theorem generic_product_liftFirst [OrderTop Q] (a : Sentence P)
    (G : GenericFilter P) (H : GenericFilter Q)
    (hG : GenericFor a.Requirements G) :
    GenericFor (Sentence.Requirements (Sentence.liftFirst a)) (productFilter G H) := by
  obtain ⟨q,hq⟩ := H.nonempty
  intro n
  obtain ⟨p,hp,hpn⟩ := hG n
  exact ⟨(p,q),⟨hp,hq⟩,(requirements_liftFirst a n p q).mpr hpn⟩

theorem sourceEquation_tail_invariance (c : OracleCode) (R : Oracle) :
    ∃ a : Sentence CohenBorelForcing.Condition,
      (∀ A, Sentence.Truth (CohenBorelForcing.realFilter A) a ↔
        GenericIdentity.SourceEquation c R (GenericTruth.triple A)) ∧
      (∀ (Q : Type) [Preorder Q] [OrderTop Q]
        (A : Oracle) (H : GenericFilter Q),
        Sentence.Truth (productFilter (CohenBorelForcing.realFilter A) H)
          (Sentence.liftFirst a) ↔ GenericIdentity.SourceEquation c R (GenericTruth.triple A)) ∧
      ∀ (Q : Type) [Preorder Q] [OrderTop Q]
        (p : CohenBorelForcing.Condition) (q : Q),
        Sentence.WeakForces (p,q) (Sentence.liftFirst a) ↔ Sentence.WeakForces p a := by
  obtain ⟨a,ha⟩ := CohenBorelForcing.borel_represented _
    ((GenericIdentity.sourceEquation_measurable c R).preimage GenericTruth.triple_measurable)
  refine ⟨a,ha,?_,?_⟩
  · intro Q _ _ A H
    exact (truth_liftFirst a _ H).trans (ha A)
  · intro Q _ _ p q
    exact Sentence.weak_liftFirst a p q

end TuringRigidity.SourceEquationTail

end OAI
