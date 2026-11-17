/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundInclusion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalContainer
public import LeanPool.TuringConeRigidity.SetModels.InternalCheckRecursion
public import LeanPool.TuringConeRigidity.SetModels.ExtensionBasicAxioms

/-!
# Ground Inclusion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory CountableForcing
universe u

theorem encoded_check_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    (Name.check x).encode (label p) ∈ M := by
  obtain ⟨d,hdM,hd,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI hx
  exact encoded_check_mem_of_container M p d hM hP hU hPow hS hR hp hdM hd hxd

theorem ground_inclusion (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (M : Set ZFSet.{u}) ⊆ genericExtension M p G :=
  ground_subset M p (fun _ hx => encoded_check_mem M p hM hP hU hPow hS hR hI hp hx) G hG

theorem ground_inclusion_set (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    M ⊆ genericExtensionSet M p G := by
  intro x hx
  have hx' := ground_inclusion M p hM hP hU hPow hS hR hI hp G hG hx
  rw [←genericExtensionSet_coe] at hx'
  exact hx'

theorem infinity_of_omega (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) : Infinity M := by
  refine ⟨ZFSet.omega,hω,⟨∅,hM _ hω _ ZFSet.omega_zero,ZFSet.omega_zero,
    fun z _ => ZFSet.notMem_empty z⟩,?_⟩
  intro x _ hx
  have hs := ZFSet.omega_succ hx
  exact ⟨insert x x,hM _ hω _ hs,hs,fun z _ => ZFSet.mem_insert_iff⟩

theorem extension_infinity (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    Infinity (genericExtensionSet M p G) :=
  infinity_of_omega _ (genericExtensionSet_transitive M p hM G)
    (ground_inclusion_set M p hM hP hU hPow hS hR hI hp G hG (omega_mem M hM hS hI))

theorem ground_bounded_absolute (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.Realize M e ↔ φ.Realize (genericExtensionSet M p G) e :=
  (φ.absolute M hM e he).trans
    (φ.absolute _ (genericExtensionSet_transitive M p hM G) e
      (fun i => ground_inclusion_set M p hM hP hU hPow hS hR hI hp G hG (he i))).symm

theorem extension_six_axioms (M p r : ZFSet.{u})
    [Preorder (Conditions p)] [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (G : GenericFilter (Conditions p)) (hG : ⊤ ∈ G.carrier) :
    let E := genericExtensionSet M p G.carrier
    M ⊆ E ∧ BasicAxioms.Extensionality E ∧ BasicAxioms.EmptySet E ∧ Pairing E ∧
      BoundedSetTheory.Union E ∧ BasicAxioms.Foundation E ∧ Infinity E := by
  have hne : M ≠ ∅ := by intro he; exact ZFSet.notMem_empty p (he ▸ hp)
  obtain ⟨he,hem,hp',hu,hf⟩ := extension_five_axioms M p r hM hne hP hU hPow hS hp hrM hr G hG
  exact ⟨ground_inclusion_set M p hM hP hU hPow hS hR hI hp G.carrier hG,he,hem,hp',hu,hf,
    extension_infinity M p hM hP hU hPow hS hR hI hp G.carrier hG⟩

end TuringRigidity.TransitiveNameModel

end OAI
