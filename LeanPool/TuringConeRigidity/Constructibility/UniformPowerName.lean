/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformPowerName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Uniform Power Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem uniform_power_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ b : Name (Conditions c), b.encode (label c) ∈ M ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ⊤ ∈ G.carrier →
        ∀ x, x ∈ b.val G.carrier ↔
          x ∈ genericExtensionSet M c G.carrier ∧ x ⊆ a.val G.carrier := by
  have hS := hT.separation.finitePrefix.bounded
  have hsupport := support_mem M hM hT.pairing hT.union hT.powerSet hS hc hoM ho a ha
  obtain ⟨W,hW,hWdef⟩ := internal_power M hM hT.powerSet hsupport
  have hWsub : ∀ B ∈ W, B ⊆ a.support (label c) := fun B hB => ((hWdef B).mp hB).2
  have hpower : (powerName a W).encode (label c) ∈ M := by
    rw [encode_powerName a W hWsub]
    exact product_mem M hM hT.pairing hT.union hT.powerSet hS hW
      (singleton_mem M hM hT.pairing (hM c hc _ (label_mem c ⊤)))
  refine ⟨powerName a W,hpower,?_⟩
  intro G hG ht x
  constructor
  · intro hx
    obtain ⟨B,hB,hBx⟩ := (mem_val_powerName a W G.carrier ht x).mp hx
    have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
      rw [Name.encode_restrict _ _ _ (hWsub B hB)]
      exact ((hWdef B).mp hB).1
    exact ⟨(mem_extensionSet M c G.carrier x).mpr ⟨_,hcode,hBx⟩,
      hBx ▸ a.val_restrict_subset (label c) B G⟩
  · rintro ⟨hx,hsub⟩
    obtain ⟨b,hb,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
    obtain ⟨B,hBM,hBS,hBval⟩ := internal_intersection_name M hM hT.pairing hT.union
      hT.powerSet hS hT.replacement.finitePrefix hT.infinity hc hoM ho G hG a b ha hb
    apply (mem_val_powerName a W G.carrier ht _).mpr
    refine ⟨B,(hWdef B).mpr ⟨hBM,hBS⟩,hBval.trans ?_⟩
    apply ZFSet.ext; intro y
    rw [ZFSet.mem_inter]
    exact ⟨And.right,fun hy => ⟨hsub hy,hy⟩⟩

end TuringRigidity.AtomicForcing

end OAI
