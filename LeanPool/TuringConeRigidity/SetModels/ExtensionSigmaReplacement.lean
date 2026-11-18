/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionSigmaReplacement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionWitnessCover
public import LeanPool.TuringConeRigidity.SetModels.ExtensionSigmaSeparation

/-!
# Extension Sigma Replacement
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

/-- Variable renaming reserving a witness slot for a sigma-defined image. -/
def imageVars : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | i+2 => i+3

/-- A sigma formula defining the image of a relation with its witness restricted to the
designated set. -/
def image (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (andBounded (.member 0 2) (φ.rename imageVars))

theorem realize_image (φ : SigmaFormula) (M a y : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.image.Realize M (cons y (cons a e)) ↔
      ∃ x ∈ M, x ∈ a ∧ φ.Realize M (cons y (cons x e)) := by
  simp only [image,Realize,realize_andBounded,realize_rename,Formula.Realize,cons_zero,cons_succ]
  apply exists_congr; intro x
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  have he : (fun i => cons x (cons y (cons a e)) (imageVars i)) = cons y (cons x e) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with _|i <;> rfl
  rw [he]
end SigmaFormula
end TuringRigidity.BoundedSetTheory

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem extension_sigmaReplacement (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    SigmaReplacement (genericExtensionSet M c G.carrier) := by
  classical
  intro φ env henv X hX htotal
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier X).mp hX
  have names_exist (i) := (mem_extensionSet M c G.carrier (env i)).mp (henv i)
  choose e he hval using names_exist
  have hev : (fun i => (e i).val G.carrier) = env := funext hval
  obtain ⟨N,hN,hcover⟩ := extension_witness_cover M hM hP hU hPow hS hR hI hAC hc hoM ho G hG φ e
    he a ha
  rw [hev] at hcover
  have hNExt := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have hAExt := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
  have hExtT := genericExtensionSet_transitive M c hM G.carrier
  have hcovered : ∀ x ∈ a.val G.carrier, ∃ y ∈ N.val G.carrier,
      φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x env)) := by
    intro x hx
    obtain ⟨y,hy,hφ,_⟩ := htotal x hx
    exact hcover x hx ⟨y,hy,hφ⟩
  have hsep := extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG
  have he' : ∀ i, cons (a.val G.carrier) env i ∈ genericExtensionSet M c G.carrier := by
    intro i; cases i with
    | zero => exact hAExt
    | succ i => exact henv i
  obtain ⟨b,hb,hbdef⟩ := hsep φ.image (cons (a.val G.carrier) env) he' (N.val G.carrier) hNExt
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy,SigmaFormula.realize_image]
  constructor
  · rintro ⟨_,x,_,hx,hφ⟩
    exact ⟨x,hx,hφ⟩
  · rintro ⟨x,hx,hφ⟩
    obtain ⟨z,hz,hφz⟩ := hcovered x hx
    obtain ⟨v,_,_,hu⟩ := htotal x hx
    have hzy : z = y := (hu z (hExtT _ hNExt z hz) hφz).trans (hu y hy hφ).symm
    exact ⟨hzy ▸ hz,x,hExtT _ hAExt x hx,hx,hφ⟩

end TuringRigidity.BoundedForcing

end OAI
