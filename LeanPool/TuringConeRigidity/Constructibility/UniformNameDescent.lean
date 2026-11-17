/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformNameDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedMembershipSeparation
public import LeanPool.TuringConeRigidity.Representation.CountableGroundGeneric

/-!
# Uniform Name Descent
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

theorem checked_mem_iff_all_outer_generic (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hT : SourceT M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o x : ZFSet.{u}} (hoM : o ∈ M) (hx : x ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) (p : Conditions c) :
    MemForces (Name.check x) t p ↔ ∀ G : GenericFilter (Conditions c),
      GroundGeneric N G → p ∈ G.carrier → x ∈ t.val G.carrier := by
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  have hcheck := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet hS hR hT.infinity hc hx
  have truth (G : GenericFilter (Conditions c)) (hG : GroundGeneric N G) :
      x ∈ t.val G.carrier ↔ ∃ q ∈ G.carrier, MemForces (Name.check x) t q := by
    have hGM : GroundGeneric M G := fun D hD hd => hG D (hMN hD) hd
    obtain ⟨q,hq⟩ := G.nonempty
    have htop : ⊤ ∈ G.carrier := G.upper le_top hq
    have h := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet hS hR hT.infinity
      hc hoM ho G hGM (Name.check x) t hcheck ht).2
    simpa only [Name.val_check G.carrier htop] using h
  constructor
  · intro hf G hG hp
    exact (truth G hG).mpr ⟨p,hp,hf⟩
  · intro h
    apply mem_of_dense
    intro q hqp
    obtain ⟨G,hq,hG⟩ := countable_ground_generic N ⟨c,hMN hc⟩ q
    obtain ⟨r,hr,hrf⟩ := (truth G hG).mp (h G hG (G.upper hqp hq))
    obtain ⟨s,_,hsq,hsr⟩ := G.directed hq hr
    exact ⟨s,hsq,mem_mono _ _ hsr hrf⟩

theorem uniform_value_mem_iff (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hT : SourceT M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o x S : ZFSet.{u}} (hoM : o ∈ M) (hx : x ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) (p : Conditions c)
    (hval : ∀ G : GenericFilter (Conditions c), GroundGeneric N G → p ∈ G.carrier →
      t.val G.carrier = S) :
    MemForces (Name.check x) t p ↔ x ∈ S := by
  rw [checked_mem_iff_all_outer_generic M N hM hT hMN hc hoM hx ho t ht p]
  constructor
  · intro h
    obtain ⟨G,hp,hG⟩ := countable_ground_generic N ⟨c,hMN hc⟩ p
    rw [←hval G hG hp]
    exact h G hG hp
  · intro hxS G hG hp
    rw [hval G hG hp]
    exact hxS

theorem uniform_name_subset_descent (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hT : SourceT M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M) (hSa : S ⊆ a)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) (p : Conditions c)
    (hval : ∀ G : GenericFilter (Conditions c), GroundGeneric N G → p ∈ G.carrier →
      t.val G.carrier = S) : S ∈ M := by
  obtain ⟨b,hb,hdef⟩ := internal_forced_members M hM hT hc hoM ha ho t ht p
  have hSb : S = b := by
    apply ZFSet.ext
    intro x
    rw [hdef x]
    constructor
    · intro hx
      have hxa := hSa hx
      exact ⟨hxa,(uniform_value_mem_iff M N hM hT hMN hc hoM (hM a ha x hxa) ho
        t ht p hval).mpr hx⟩
    · rintro ⟨hxa,hf⟩
      exact (uniform_value_mem_iff M N hM hT hMN hc hoM (hM a ha x hxa) ho
        t ht p hval).mp hf
  exact hSb ▸ hb

end TuringRigidity.FullSetForcing

end OAI
