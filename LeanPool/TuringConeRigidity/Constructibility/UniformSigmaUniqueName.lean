/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaUniqueName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformExtensionWitnessCover
public import LeanPool.TuringConeRigidity.Constructibility.UniformSigmaSeparationName
public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Uniform Sigma Unique Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u

theorem uniform_sigma_unique_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (F : Set (Conditions c) → ZFSet.{u})
    (hF : ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
      F G.carrier ∈ genericExtensionSet M c G.carrier ∧
      ∀ y ∈ genericExtensionSet M c G.carrier,
        φ.Realize (genericExtensionSet M c G.carrier)
          (cons y (cons (a.val G.carrier) (fun i => (e i).val G.carrier))) ↔ y = F G.carrier) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = F G.carrier := by
  have hp := names_pair_closed M c hM hT.pairing hc ha ha
  obtain ⟨N,hN,hNv⟩ := uniform_extension_witness_cover M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
    hc hoM ho φ e he (Name.pair a a) hp
  have hep (i : ℕ) : (push a e i).encode (label c) ∈ M := by
    cases i
    · exact ha
    · exact he _
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_sigma_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hc hoM ho φ N hN (push a e)
      hep
  let S := N.restrict (label c) B
  have hS : S.encode (label c) ∈ M := by
    dsimp only [S]; rw [Name.encode_restrict _ _ _ hBS]; exact hB
  refine ⟨Name.union S,names_union_closed M c o hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hc hoM ho hS,?_⟩
  intro G hG ht
  obtain ⟨hFm,hFv⟩ := hF G hG ht
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hNE := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have haV : a.val G.carrier ∈ (Name.pair a a).val G.carrier := by
    rw [Name.val_pair G.carrier ht]
    exact ZFSet.mem_pair.mpr (Or.inl rfl)
  obtain ⟨y,hy,hφ⟩ := hNv G hG ht _ haV ⟨_,hFm,(hFv _ hFm).mpr rfl⟩
  have hyF : y = F G.carrier := (hFv y (hE _ hNE y hy)).mp hφ
  have hsval : S.val G.carrier = ({F G.carrier} : ZFSet.{u}) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_singleton]
    have hv := hBv G hG z
    have heval : (fun i => (push a e i).val G.carrier) =
        cons (a.val G.carrier) (fun i => (e i).val G.carrier) := by
      funext i; cases i <;> rfl
    rw [heval] at hv
    rw [hv]
    constructor
    · rintro ⟨hz,hφz⟩; exact (hFv z (hE _ hNE z hz)).mp hφz
    · rintro rfl; exact ⟨hyF ▸ hy,(hFv _ hFm).mpr rfl⟩
  rw [Name.val_union,hsval,ZFSet.sUnion_singleton]

end TuringRigidity.BoundedForcing

end OAI
