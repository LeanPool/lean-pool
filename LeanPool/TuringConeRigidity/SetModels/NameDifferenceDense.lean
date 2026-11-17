/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameDifferenceDense.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedMembershipSeparation

/-!
# Name Difference Dense
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

/-- Conditions witnessing a discrepancy between the checked set `S` and the name's membership
on some element of `a`. -/
def NameDifference (a S : ZFSet.{u}) (t : Name (Conditions c)) : Set (Conditions c) :=
  {p | ∃ x ∈ a, (x ∈ S ∧ ∀ q, q ≤ p → ¬ MemForces (Name.check x) t q) ∨
    (x ∉ S ∧ MemForces (Name.check x) t p)}

theorem nameDifference_dense (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (hSa : S ⊆ a) (hSM : S ∉ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) :
    Dense (NameDifference a S t) := by
  classical
  intro p
  by_contra h
  have avoid : ∀ q, q ≤ p → ¬ (q ∈ NameDifference a S t) := by
    simpa only [not_exists,not_and] using h
  obtain ⟨b,hb,hdef⟩ := internal_forced_members M hM hT hc hoM ha ho t ht p
  have hbS : b = S := by
    apply ZFSet.ext
    intro x
    rw [hdef x]
    constructor
    · rintro ⟨hxa,hf⟩
      by_contra hx
      exact avoid p le_rfl ⟨x,hxa,Or.inr ⟨hx,hf⟩⟩
    · intro hx
      refine ⟨hSa hx,mem_of_dense _ _ p ?_⟩
      intro q hqp
      by_contra hn
      have hneg : ∀ r, r ≤ q → ¬ MemForces (Name.check x) t r := by
        simpa only [not_exists,not_and] using hn
      exact avoid q hqp ⟨x,hSa hx,Or.inl ⟨hx,hneg⟩⟩
  exact hSM (hbS ▸ hb)

theorem nameDifference_ne_value (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    {p : Conditions c} (hp : p ∈ G.carrier) (hd : p ∈ NameDifference a S t) :
    t.val G.carrier ≠ S := by
  obtain ⟨x,hxa,hd⟩ := hd
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  have hxM := hM a ha x hxa
  have hcheck := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet hS hR hT.infinity hc hxM
  have htop : ⊤ ∈ G.carrier := G.upper le_top hp
  have truth := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet hS hR hT.infinity
    hc hoM ho G hG (Name.check x) t hcheck ht).2
  rw [Name.val_check G.carrier htop] at truth
  intro hval
  rw [hval] at truth
  rcases hd with ⟨hx,hneg⟩|⟨hx,hpos⟩
  · obtain ⟨q,hq,hf⟩ := truth.mp hx
    obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
    exact hneg r hrp (mem_mono _ _ hrq hf)
  · exact hx (truth.mpr ⟨p,hp,hpos⟩)

end TuringRigidity.FullSetForcing

end OAI
