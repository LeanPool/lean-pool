/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountableNameAvoidance.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameDifferenceDense
public import LeanPool.TuringConeRigidity.Representation.GroundGenericRequirements

/-!
# Countable Name Avoidance
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

omit [Preorder (Conditions c)] [OrderTop (Conditions c)] in
theorem ground_name_sequence (M N : ZFSet.{u}) [Countable (Conditions N)] (hMN : M ⊆ N)
    (t₀ : Name (Conditions c)) (ht₀ : t₀.encode (label c) ∈ M) :
    ∃ ts : ℕ → Name (Conditions c), (∀ n, (ts n).encode (label c) ∈ M) ∧
      ∀ t : Name (Conditions c), t.encode (label c) ∈ M →
        ∃ n, (ts n).encode (label c) = t.encode (label c) := by
  classical
  obtain ⟨m,_⟩ := label_surjective N (hMN ht₀)
  let _ : Nonempty (Conditions N) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions N)
  have pick (n : ℕ) : ∃ s : Name (Conditions c), s.encode (label c) ∈ M ∧
      ∀ t : Name (Conditions c), t.encode (label c) ∈ M →
        t.encode (label c) = label N (e n) → s.encode (label c) = t.encode (label c) := by
    by_cases h : ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧
        t.encode (label c) = label N (e n)
    · obtain ⟨t,ht,heq⟩ := h
      exact ⟨t,ht,fun s _ hs => heq.trans hs.symm⟩
    · exact ⟨t₀,ht₀,fun t ht heq => False.elim (h ⟨t,ht,heq⟩)⟩
  choose ts hts using pick
  refine ⟨ts,fun n => (hts n).1,?_⟩
  intro t ht
  obtain ⟨m,hm⟩ := label_surjective N (hMN ht)
  obtain ⟨n,rfl⟩ := he m
  exact ⟨n,(hts n).2 t ht hm.symm⟩

theorem exists_generic_omitting_subset (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hT : SourceT M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (hSa : S ⊆ a) (hSM : S ∉ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric N G ∧
      S ∉ genericExtensionSet M c G.carrier := by
  have ht₀ := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hc
  obtain ⟨ts,hts,hcover⟩ := ground_name_sequence M N hMN (Name.check c) ht₀
  let E : ℕ → Set (Conditions c) := fun n => NameDifference a S (ts n)
  have hE : ∀ n, Dense (E n) := fun n =>
    nameDifference_dense M hM hT hc hoM ha hSa hSM ho (ts n) (hts n)
  obtain ⟨G,hp,hG,hGE⟩ := ground_generic_with_requirements N ⟨c,hMN hc⟩ E hE p
  refine ⟨G,hp,hG,?_⟩
  intro hSG
  obtain ⟨t,ht,hval⟩ := (mem_extensionSet M c G.carrier S).mp hSG
  obtain ⟨n,hn⟩ := hcover t ht
  obtain ⟨q,hq,hqn⟩ := hGE n
  have hGM : GroundGeneric M G := fun D hD hd => hG D (hMN hD) hd
  have hne := nameDifference_ne_value M hM hT hc hoM ha ho (ts n) (hts n) G hGM hq hqn
  apply hne
  exact (Name.val_eq_of_encode_eq (label c) (label_injective c) G.carrier (ts n) t hn).trans hval

theorem subset_mem_iff_all_generic_extensions (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hT : SourceT M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M) (hSa : S ⊆ a)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    S ∈ M ↔ ∀ G : GenericFilter (Conditions c), GroundGeneric N G → p ∈ G.carrier →
      S ∈ genericExtensionSet M c G.carrier := by
  classical
  constructor
  · intro hSM G _ hp
    exact ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
      G.carrier (G.upper le_top hp) hSM
  · intro h
    by_contra hSM
    obtain ⟨G,hp,hG,hSG⟩ := exists_generic_omitting_subset M N hM hT hMN hc hoM ha hSa hSM ho p
    exact hSG (h G hG hp)

end TuringRigidity.FullSetForcing

end OAI
