/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformProductName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformPowerName
public import LeanPool.TuringConeRigidity.Constructibility.UniformSeparationName

/-!
# Uniform Product Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing BoundedForcing
universe u

theorem uniform_product_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (hb : b.encode (label c) ∈ M) :
    ∃ d : Name (Conditions c), d.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        d.val G.carrier = ZFSet.prod (a.val G.carrier) (b.val G.carrier) := by
  have hS := hT.separation.finitePrefix.bounded
  let U := Name.union (Name.pair a b)
  have hU : U.encode (label c) ∈ M := names_union_closed M c o hM hT.pairing hT.union
    hT.powerSet hS hc hoM ho (names_pair_closed M c hM hT.pairing hc ha hb)
  obtain ⟨P,hP,hPv⟩ := uniform_power_name M hM hT hc hoM ho U hU
  obtain ⟨Q,hQ,hQv⟩ := uniform_power_name M hM hT hc hoM ho P hP
  let e := push a (push b (fun _ => b))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _ | _ | i
    · exact ha
    · exact hb
    · exact hb
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hS hT.replacement.finitePrefix hT.infinity hc hoM ho productFormula Q hQ e he
  refine ⟨Q.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
    have haE : a.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
    have hbE : b.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨b,hb,rfl⟩
    have hUv : U.val G.carrier = a.val G.carrier ∪ b.val G.carrier := by
      rw [Name.val_union,Name.val_pair G.carrier ht,ZFSet.sUnion_pair]
    have hbound : ZFSet.prod (a.val G.carrier) (b.val G.carrier) ⊆ Q.val G.carrier := by
      intro z hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      have hxE := hE _ haE x hx
      have hyE := hE _ hbE y hy
      apply (hQv G hG ht _).mpr
      refine ⟨orderedPair_mem E hE hTE.pairing hxE hyE,?_⟩
      intro t htz
      change t ∈ ({({x} : ZFSet.{u}),({x,y} : ZFSet.{u})} : ZFSet.{u}) at htz
      rcases ZFSet.mem_pair.mp htz with rfl|rfl
      · apply (hPv G hG ht _).mpr
        refine ⟨singleton_mem E hE hTE.pairing hxE,?_⟩
        intro w hw
        obtain rfl := ZFSet.mem_singleton.mp hw
        rw [hUv]; exact ZFSet.mem_union.mpr (Or.inl hx)
      · apply (hPv G hG ht _).mpr
        refine ⟨pair_mem E hE hTE.pairing hxE hyE,?_⟩
        intro w hw
        rw [hUv]
        rcases ZFSet.mem_pair.mp hw with rfl|rfl
        · exact ZFSet.mem_union.mpr (Or.inl hx)
        · exact ZFSet.mem_union.mpr (Or.inr hy)
    apply ZFSet.ext; intro z
    rw [hBv G hG z]
    change (_ ∧ productFormula.Eval (cons z (cons (a.val G.carrier)
      (cons (b.val G.carrier) (fun _ => b.val G.carrier))))) ↔ _
    rw [eval_productFormula]
    exact ⟨And.right,fun hz => ⟨hbound hz,hz⟩⟩

end TuringRigidity.AtomicForcing

end OAI
