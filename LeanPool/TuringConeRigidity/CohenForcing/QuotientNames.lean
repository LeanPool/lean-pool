/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/QuotientNames.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RecursiveNames
public import LeanPool.TuringConeRigidity.CohenForcing.ForcingProjection

/-!
# Quotient Names
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.QuotientNames
open Set CountableForcing ForcingProjection RecursiveNames
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- Restrict a forcing name to children tagged by conditions whose projections belong to `H`. -/
def restrict (π : Projection P Q) (H : GenericFilter Q) :
    Name P → Name (QuotientConditions π H)
  | .mk ι child tag => .mk {i : ι // π.map (tag i) ∈ H.carrier}
      (fun i => restrict π H (child i.val)) (fun i => ⟨tag i.val,i.property⟩)

theorem tag_mem_iff (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (p : P) :
    p ∈ (liftFilter π H K).carrier ↔
      ∃ hp : π.map p ∈ H.carrier, (⟨p,hp⟩ : QuotientConditions π H) ∈ K.carrier := by
  constructor
  · rintro ⟨r,hr,hrp⟩
    exact ⟨H.upper (π.mono hrp) r.property,K.upper hrp hr⟩
  · rintro ⟨hp,hpK⟩
    exact ⟨⟨p,hp⟩,hpK,le_rfl⟩

theorem val_restrict (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (τ : Name P) :
    (restrict π H τ).val K.carrier = τ.val (liftFilter π H K).carrier := by
  induction τ with
  | mk ι child tag ih =>
    apply ZFSet.ext
    intro x
    refine (Name.mem_val K.carrier {index : ι // π.map (tag index) ∈ H.carrier}
      (fun index => restrict π H (child index.val))
      (fun index => ⟨tag index.val,index.property⟩) x).trans ?_
    rw [Name.mem_val]
    simp only [ih]
    constructor
    · rintro ⟨⟨i,hi⟩,hiK,hx⟩
      exact ⟨i,(tag_mem_iff π H K (tag i)).mpr ⟨hi,hiK⟩,hx⟩
    · rintro ⟨i,hi,hx⟩
      obtain ⟨hiH,hiK⟩ := (tag_mem_iff π H K (tag i)).mp hi
      exact ⟨⟨i,hiH⟩,hiK,hx⟩

theorem original_val_restrict (π : Projection P Q) (G : GenericFilter P) (τ : Name P) :
    (restrict π (imageFilter π G) τ).val (quotientFilter π G).carrier = τ.val G.carrier := by
  rw [val_restrict,lift_quotient_eq]

theorem val_lift_name (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (σ : Name (QuotientConditions π H)) :
    (σ.rename Subtype.val).val (liftFilter π H K).carrier = σ.val K.carrier :=
  Name.val_rename Subtype.val K.carrier (liftFilter π H K).carrier
    (lift_mem_iff π H K) σ

theorem family_values_eq (π : Projection P Q) (G : GenericFilter P) (N : Set (Name P)) :
    {x | ∃ τ ∈ N, (restrict π (imageFilter π G) τ).val (quotientFilter π G).carrier = x} =
      {x | ∃ τ ∈ N, τ.val G.carrier = x} := by
  ext x
  simp only [Set.mem_ofPred_eq,original_val_restrict]

end TuringRigidity.QuotientNames

end OAI
