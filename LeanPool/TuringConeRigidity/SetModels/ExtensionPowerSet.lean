/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionPowerSet.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IntersectionName

/-!
# Extension Power Set
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def powerName (a : Name (Conditions c)) (W : ZFSet.{u}) : Name (Conditions c) :=
  .mk (Conditions W) (fun s => a.restrict (label c) (label W s)) (fun _ => ⊤)

theorem encode_powerName (a : Name (Conditions c)) (W : ZFSet.{u})
    (hW : ∀ B ∈ W, B ⊆ a.support (label c)) :
    (powerName a W).encode (label c) = ZFSet.prod W ({label c ⊤} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    rw [Name.encode_restrict _ _ _ (hW _ (label_mem W s))] at hs
    exact ZFSet.mem_prod.mpr ⟨_,label_mem W s,_,ZFSet.mem_singleton.mpr rfl,hs.symm⟩
  · intro hz
    obtain ⟨B,hB,t,ht,hz⟩ := ZFSet.mem_prod.mp hz
    obtain rfl := ZFSet.mem_singleton.mp ht
    obtain ⟨s,rfl⟩ := label_surjective W hB
    exact ⟨s,by rw [Name.encode_restrict _ _ _ (hW _ hB)]; exact hz.symm⟩

theorem mem_val_powerName (a : Name (Conditions c)) (W : ZFSet.{u})
    (G : Set (Conditions c)) (hG : ⊤ ∈ G) (x : ZFSet.{u}) :
    x ∈ (powerName a W).val G ↔ ∃ B ∈ W, (a.restrict (label c) B).val G = x := by
  rw [powerName,Name.mem_val]
  constructor
  · rintro ⟨s,_,hs⟩
    exact ⟨_,label_mem W s,hs⟩
  · rintro ⟨B,hB,hx⟩
    obtain ⟨s,rfl⟩ := label_surjective W hB
    exact ⟨s,hG,hx⟩

theorem extension_powerSet (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    PowerSet (genericExtensionSet M c G.carrier) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
  have hsupport := support_mem M hM hP hU hPow hS hc hoM ho a ha
  obtain ⟨W,hW,hWdef⟩ := internal_power M hM hPow hsupport
  have hWsub : ∀ B ∈ W, B ⊆ a.support (label c) := fun B hB => ((hWdef B).mp hB).2
  have hpower : (powerName a W).encode (label c) ∈ M := by
    rw [encode_powerName a W hWsub]
    exact product_mem M hM hP hU hPow hS hW
      (singleton_mem M hM hP (hM c hc _ (label_mem c ⊤)))
  refine ⟨(powerName a W).val G.carrier,(mem_extensionSet M c G.carrier _).mpr
    ⟨_,hpower,rfl⟩,?_⟩
  intro z hz
  constructor
  · intro hzPower y _ hyz
    obtain ⟨B,hB,hBz⟩ := (mem_val_powerName a W G.carrier htop z).mp hzPower
    rw [←hBz] at hyz
    exact a.val_restrict_subset (label c) B G hyz
  · intro hsub
    obtain ⟨b,hb,rfl⟩ := (mem_extensionSet M c G.carrier z).mp hz
    have hba : b.val G.carrier ⊆ a.val G.carrier := fun y hy => hsub y
      (genericExtensionSet_transitive M c hM G.carrier _
        ((mem_extensionSet M c G.carrier _).mpr ⟨b,hb,rfl⟩) y hy) hy
    obtain ⟨B,hBM,hBS,hBval⟩ := internal_intersection_name M hM hP hU hPow hS hR hI hc hoM ho G hG
      a b ha hb
    apply (mem_val_powerName a W G.carrier htop _).mpr
    refine ⟨B,(hWdef B).mpr ⟨hBM,hBS⟩,hBval.trans ?_⟩
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_inter]
    exact ⟨And.right,fun hy => ⟨hba hy,hy⟩⟩

end TuringRigidity.AtomicForcing

end OAI
