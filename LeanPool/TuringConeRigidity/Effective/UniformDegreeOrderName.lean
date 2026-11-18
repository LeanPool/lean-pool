/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformDegreeOrderName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformDegreeUniverseName
public import LeanPool.TuringConeRigidity.Constructibility.UniformProductName
public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeOrder

/-!
# Uniform Degree Order Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open RecursiveNames TransitiveNameModel AtomicForcing CountableForcing BoundedForcing
open RelativeConstructible
universe u

theorem uniform_degreeOrder_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ L : Name (Conditions c), L.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        L.val G.carrier = degreeOrder (groundReals (genericExtensionSet M c G.carrier)) := by
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {x : ZFSet.{u}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc hoM ho
  obtain ⟨P,hP,hPv⟩ := uniform_product_name M hM hT hc hoM ho D D hD hD
  obtain ⟨φ,hφ⟩ := degree_order_bounded.{u}
  let e := push (Name.check ZFSet.omega) (push (Name.check Q) (push (Name.check (natSet 0)) (fun _
    => D)))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|i
    · exact hcheck hω
    · exact hcheck hQM
    · exact hcheck hz
    · exact hD
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hoM ho
    (Formula.degreeOrderMember φ 1 2 3 4 0) P hP e he
  refine ⟨P.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hr : ∀ w ∈ groundReals E, ∃ A : Oracle, realCode A = w := by
      intro w hw
      exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
    have hv : (fun i => (e i).val G.carrier) =
        cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => D.val G.carrier))) := by
      funext i; rcases i with _|_|_|i
      · exact Name.val_check G.carrier ht _
      · exact Name.val_check G.carrier ht _
      · exact Name.val_check G.carrier ht _
      rfl
    apply ZFSet.ext; intro z
    rw [hBv G hG z,hv,Formula.degreeOrderMember_spec hφ 1 2 3 4 0 _ rfl hQ rfl
      (groundReals E) (hDv G hG ht) hr,hPv G hG ht,hDv G hG ht]
    exact ⟨And.right,fun h => ⟨(ZFSet.mem_sep.mp h).1,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
