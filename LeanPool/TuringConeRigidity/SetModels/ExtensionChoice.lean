/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ChoiceFromOrdinalCover
public import LeanPool.TuringConeRigidity.SetModels.NameEvaluationGraph
public import LeanPool.TuringConeRigidity.SetModels.ExtensionSigmaReplacement
public import LeanPool.TuringConeRigidity.SetModels.ExtensionPowerSet

/-!
# Extension Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem extension_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    Choice (genericExtensionSet M c G.carrier) := by
  classical
  let E := genericExtensionSet M c G.carrier
  have hET : Transitive E := genericExtensionSet_transitive M c hM G.carrier
  have hEP : Pairing E := extension_pairing M c hM hP hc G.carrier htop
  have hEU : BoundedSetTheory.Union E := extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G
  have hEPow : PowerSet E := extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop
  have hES : Separation E := (extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G
    hG).bounded
  have hground : M ⊆ E := ground_inclusion_set M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop
  intro X hX hnonempty
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier X).mp hX
  obtain ⟨d,hdM,hd,had⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI ha
  let V := ZFSet.sep (fun x => (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c))) d
  have hV : V ∈ M := sigma_sep_mem M hM hS (NameValidity.Code.valid 1 0) (fun _ => c) (fun _ =>
    hc) hdM
  have valid (x : ZFSet.{u}) (hx : x ∈ M) :
      (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c)) ↔
        ∃ b : Name (Conditions c), b.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS.bounded hR hI _
      (by intro i; cases i <;> assumption) 1 0
  have hvalid (x : ZFSet.{u}) (hx : x ∈ V) : ∃ b : Name (Conditions c), b.encode (label c) = x :=
    (valid x (hM V hV x hx)).mp (ZFSet.mem_sep.mp hx).2
  have code_mem (b : Name (Conditions c)) (hb : b.encode (label c) ∈ d) : b.encode (label c) ∈ V :=
    ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM d hdM _ hb)).mpr ⟨b,rfl⟩⟩
  obtain ⟨δ,hδM,hδ,F,hFM,hF,hsurj,_⟩ :=
    InternalWellOrder.internal_ordinal_enumeration M hM hP hU hPow hS hR hI hAC hV
  obtain ⟨N,hN,hNdef⟩ := internal_name_evaluation_graph M hM hP hU hPow hS.bounded hR hI hc
    hV hvalid G.carrier htop
  have hNE : N.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have hNfun : FiniteTerm.Functional (N.val G.carrier) := by
    intro v x y hx hy
    obtain ⟨v',_,b,hb,he⟩ := (hNdef _).mp hx
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    obtain ⟨v'',_,b',hb',he'⟩ := (hNdef _).mp hy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he'
    exact Name.val_eq_of_encode_eq (label c) (label_injective c) G.carrier _ _ (hb.trans hb'.symm)
  apply InternalWellOrder.internal_choice_of_ordinal_cover E hET hEP hEU hEPow hES
    hX (hground hδM) (hground hV) (hground hFM) hNE hδ hF hNfun
  intro x hx
  obtain ⟨y,hy⟩ := hnonempty x hx
  obtain ⟨b,hbd,hbx⟩ := name_of_value_member d hd a had G.carrier x hx
  have hyb : y ∈ b.val G.carrier := hbx.symm ▸ hy
  obtain ⟨s,hsd,hsy⟩ := name_of_value_member d hd b hbd G.carrier y hyb
  have hsV := code_mem s hsd
  obtain ⟨i,hi,hif⟩ := hsurj _ hsV
  refine ⟨i,hi,s.encode (label c),hsV,y,hy,hif,(hNdef _).mpr ?_⟩
  exact ⟨_,hsV,s,rfl,congrArg (ZFSet.pair (s.encode (label c))) hsy.symm⟩

end TuringRigidity.BoundedForcing

end OAI
