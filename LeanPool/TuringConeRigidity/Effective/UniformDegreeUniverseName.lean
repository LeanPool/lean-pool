/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformDegreeUniverseName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformOwnRealsName
public import LeanPool.TuringConeRigidity.Constructibility.UniformSeparationName
public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeUniverse

/-!
# Uniform Degree Universe Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open RecursiveNames TransitiveNameModel AtomicForcing CountableForcing BoundedForcing
open RelativeConstructible
universe u

theorem uniform_degreeUniverse_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ D : Name (Conditions c), D.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        D.val G.carrier = degreeUniverse (groundReals (genericExtensionSet M c G.carrier)) := by
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {x : ZFSet.{u}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  obtain ⟨R,hR,hRv⟩ := uniform_ownReals_name M hM hT hc hoM ho
  obtain ⟨P,hP,hPv⟩ := uniform_power_name M hM hT hc hoM ho R hR
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := push (Name.check ZFSet.omega) (push (Name.check Q) (push (Name.check (natSet 0)) (fun _
    => R)))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|i
    · exact hcheck hω
    · exact hcheck hQM
    · exact hcheck hz
    · exact hR
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hoM ho
    (Formula.degreeUniverseMember φ 1 2 3 4 0) P hP e he
  refine ⟨P.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
    have hr : ∀ w ∈ R.val G.carrier, ∃ A : Oracle, realCode A = w := by
      rw [hRv G hG ht]
      intro w hw
      exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
    have hRE : R.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨R,hR,rfl⟩
    have hbound : degreeUniverse (R.val G.carrier) ⊆ P.val G.carrier := by
      intro D hD
      obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse _ _).mp hD
      exact (hPv G hG ht _).mpr ⟨internal_degreeCode E hE hTE _ hRE hr (hE _ hRE _ hA),
        degreeCode_subset _ A⟩
    have hv : (fun i => (e i).val G.carrier) =
        cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => R.val G.carrier))) := by
      funext i; rcases i with _|_|_|i
      · exact Name.val_check G.carrier ht _
      · exact Name.val_check G.carrier ht _
      · exact Name.val_check G.carrier ht _
      rfl
    rw [←hRv G hG ht]
    apply ZFSet.ext; intro D
    rw [hBv G hG D,hv,Formula.degreeUniverseMember_spec hφ 1 2 3 4 0 _ rfl hQ rfl hr]
    exact ⟨And.right,fun h => ⟨hbound h,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
