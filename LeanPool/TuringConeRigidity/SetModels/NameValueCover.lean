/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameValueCover.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaSeparationName

/-!
# Name Value Cover
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

/-- Choose the forcing name represented by the selected member of the code set `W`. -/
noncomputable def coverChild (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (i : Conditions W) : Name (Conditions c) := (hW _ (label_mem W i)).choose

theorem coverChild_code (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x) (i : Conditions W) :
    (coverChild W hW i).encode (label c) = label W i := (hW _ (label_mem W i)).choose_spec

/-- The name containing all names coded by `W`, with the same tagging condition `p`. -/
noncomputable def coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (p : Conditions c) : Name (Conditions c) := .mk (Conditions W) (coverChild W hW) (fun _ => p)

theorem encode_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x) (p : Conditions c) :
    (coverName W hW p).encode (label c) = ZFSet.prod W ({label c p} : ZFSet.{u}) := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩
    rw [coverChild_code]
    exact ZFSet.mem_prod.mpr ⟨_,label_mem W i,_,ZFSet.mem_singleton.mpr rfl,rfl⟩
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain rfl := ZFSet.mem_singleton.mp hy
    obtain ⟨i,rfl⟩ := label_surjective W hx
    exact ⟨i,by rw [coverChild_code]⟩

theorem val_mem_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (p : Conditions c) (hp : p ∈ G)
    (b : Name (Conditions c)) (hb : b.encode (label c) ∈ W) :
    b.val G ∈ (coverName W hW p).val G := by
  obtain ⟨i,hi⟩ := label_surjective W hb
  rw [coverName,Name.mem_val]
  refine ⟨i,hp,?_⟩
  exact Name.val_eq_of_encode_eq (label c) (label_injective c) G _ b ((coverChild_code W hW
    i).trans hi)

variable [Preorder (Conditions c)]

theorem internal_name_value_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {W : ZFSet.{u}} (hW : W ∈ M) (G : GenericFilter (Conditions c)) :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ b : Name (Conditions c), b.encode (label c) ∈ W → b.val G.carrier ∈ N.val G.carrier := by
  let V := ZFSet.sep (fun x => (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c))) W
  have hV : V ∈ M := sigma_sep_mem M hM hS (NameValidity.Code.valid 1 0) (fun _ => c) (fun _ =>
    hc) hW
  have valid (x : ZFSet.{u}) (hx : x ∈ M) :
      (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c)) ↔
        ∃ a : Name (Conditions c), a.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS.bounded hR hI _
      (by intro i; cases i <;> assumption) 1 0
  have hvalid (x : ZFSet.{u}) (hx : x ∈ V) : ∃ a : Name (Conditions c), a.encode (label c) = x :=
    (valid x (hM V hV x hx)).mp (ZFSet.mem_sep.mp hx).2
  obtain ⟨p,hp⟩ := G.nonempty
  have hN : (coverName V hvalid p).encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS.bounded hV
      (singleton_mem M hM hP (hM c hc _ (label_mem c p)))
  refine ⟨coverName V hvalid p,hN,?_⟩
  intro b hb
  apply val_mem_coverName V hvalid G.carrier p hp b
  exact ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM W hW _ hb)).mpr ⟨b,rfl⟩⟩

end TuringRigidity.BoundedForcing

end OAI
