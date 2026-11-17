/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformNameValueCover.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameValueCover

/-!
# Uniform Name Value Cover
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}}

theorem uniform_name_value_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {W : ZFSet.{u}} (hW : W ∈ M) [Top (Conditions c)] :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ g : Set (Conditions c), ⊤ ∈ g → ∀ b : Name (Conditions c),
        b.encode (label c) ∈ W → b.val g ∈ N.val g := by
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
  let p : Conditions c := ⊤
  have hN : (coverName V hvalid p).encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS.bounded hV
      (singleton_mem M hM hP (hM c hc _ (label_mem c p)))
  refine ⟨coverName V hvalid p,hN,?_⟩
  intro g ht b hb
  apply val_mem_coverName V hvalid g p ht b
  exact ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM W hW _ hb)).mpr ⟨b,rfl⟩⟩

end TuringRigidity.BoundedForcing

end OAI
