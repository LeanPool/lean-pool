/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/ForcingProjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing

/-!
# Forcing Projection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ForcingProjection
open Set CountableForcing
universe u v
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

/-- A monotone map of forcing posets with the extension-lifting property. -/
structure Projection (P : Type u) (Q : Type v) [Preorder P] [Preorder Q] where
  /-- The monotone map underlying the forcing projection. -/
  map : P → Q
  mono : Monotone map
  lift : ∀ p q, q ≤ map p → ∃ r, r ≤ p ∧ map r ≤ q

/-- The upward closure of the projected filter. -/
def imageFilter (π : Projection P Q) (G : GenericFilter P) : GenericFilter Q where
  carrier := {q | ∃ p ∈ G.carrier, π.map p ≤ q}
  nonempty := by obtain ⟨p,hp⟩ := G.nonempty; exact ⟨π.map p,p,hp,le_rfl⟩
  upper := by rintro p q hpq ⟨r,hr,hrp⟩; exact ⟨r,hr,hrp.trans hpq⟩
  directed := by
    rintro p q ⟨r,hr,hrp⟩ ⟨s,hs,hsq⟩
    obtain ⟨t,ht,htr,hts⟩ := G.directed hr hs
    exact ⟨π.map t,⟨t,ht,le_rfl⟩,(π.mono htr).trans hrp,(π.mono hts).trans hsq⟩

/-- Conditions whose images extend some member of `D`. -/
def pullDense (π : Projection P Q) (D : Set Q) : Set P :=
  {p | ∃ q ∈ D, π.map p ≤ q}

theorem pullDense_dense (π : Projection P Q) (D : Set Q) (hD : Dense D) :
    Dense (pullDense π D) := by
  intro p
  obtain ⟨q,hq,hqD⟩ := hD (π.map p)
  obtain ⟨r,hr,hrq⟩ := π.lift p q hq
  exact ⟨r,hr,q,hqD,hrq⟩

theorem image_meets (π : Projection P Q) (G : GenericFilter P) (D : Set Q)
    (h : ∃ p ∈ G.carrier, p ∈ pullDense π D) :
    ∃ q ∈ (imageFilter π G).carrier, q ∈ D := by
  obtain ⟨p,hp,q,hq,hpq⟩ := h
  exact ⟨q,⟨p,hp,hpq⟩,hq⟩

theorem image_generic (π : Projection P Q) (G : GenericFilter P) (D : ℕ → Set Q)
    (hG : GenericFor (fun n => pullDense π (D n)) G) :
    GenericFor D (imageFilter π G) := fun n => image_meets π G (D n) (hG n)

/-- Conditions whose projected values belong to the specified filter. -/
def QuotientConditions (π : Projection P Q) (H : GenericFilter Q) :=
  {p : P // π.map p ∈ H.carrier}

instance quotientPreorder (π : Projection P Q) (H : GenericFilter Q) :
    Preorder (QuotientConditions π H) := inferInstanceAs (Preorder {p // π.map p ∈ H.carrier})

/-- The original filter regarded as a filter on the quotient conditions over its image. -/
def quotientFilter (π : Projection P Q) (G : GenericFilter P) :
    GenericFilter (QuotientConditions π (imageFilter π G)) where
  carrier := {p | p.val ∈ G.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨⟨p,p,hp,le_rfl⟩,hp⟩
  upper := fun hpq hp => G.upper hpq hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨⟨r,r,hr,le_rfl⟩,hr,hrp,hrq⟩

/-- Lift a quotient filter back to the original forcing poset. -/
def liftFilter (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) : GenericFilter P where
  carrier := {p | ∃ r ∈ K.carrier, r.val ≤ p}
  nonempty := by obtain ⟨r,hr⟩ := K.nonempty; exact ⟨r.val,r,hr,le_rfl⟩
  upper := by rintro p q hpq ⟨r,hr,hrp⟩; exact ⟨r,hr,hrp.trans hpq⟩
  directed := by
    rintro p q ⟨r,hr,hrp⟩ ⟨s,hs,hsq⟩
    obtain ⟨t,ht,htr,hts⟩ := K.directed hr hs
    exact ⟨t.val,⟨t,ht,le_rfl⟩,(show t.val ≤ r.val from htr).trans hrp,(show t.val ≤ s.val from
      hts).trans hsq⟩

theorem lift_mem_iff (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (p : QuotientConditions π H) :
    p.val ∈ (liftFilter π H K).carrier ↔ p ∈ K.carrier := by
  exact ⟨fun ⟨r,hr,hrp⟩ => K.upper hrp hr,fun hp => ⟨p,hp,le_rfl⟩⟩

theorem lift_quotient_eq (π : Projection P Q) (G : GenericFilter P) :
    (liftFilter π (imageFilter π G) (quotientFilter π G)).carrier = G.carrier := by
  ext p
  exact ⟨fun ⟨r,hr,hrp⟩ => G.upper hrp hr,fun hp => ⟨⟨p,p,hp,le_rfl⟩,hp,le_rfl⟩⟩

theorem image_lift_subset (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) :
    (imageFilter π (liftFilter π H K)).carrier ⊆ H.carrier := by
  rintro q ⟨p,⟨r,_,hrp⟩,hpq⟩
  exact H.upper ((π.mono hrp).trans hpq) r.property

/-- Quotient conditions whose projected values extend `q`. -/
def projectionCone (π : Projection P Q) (H : GenericFilter Q) (q : Q) :
    Set (QuotientConditions π H) := {p | π.map p.val ≤ q}

theorem projectionCone_dense (π : Projection P Q)
    (hexact : ∀ p q, q ≤ π.map p → ∃ r, r ≤ p ∧ π.map r = q)
    (H : GenericFilter Q) (q : Q) (hq : q ∈ H.carrier) :
    Dense (projectionCone π H q) := by
  intro p
  obtain ⟨a,ha,hap,haq⟩ := H.directed p.property hq
  obtain ⟨r,hr,hra⟩ := hexact p.val a hap
  exact ⟨⟨r,hra.symm ▸ ha⟩,hr,by change π.map r ≤ q; rw [hra]; exact haq⟩

theorem image_lift_eq (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H))
    (hK : ∀ q ∈ H.carrier, ∃ p ∈ K.carrier, p ∈ projectionCone π H q) :
    (imageFilter π (liftFilter π H K)).carrier = H.carrier := by
  apply Set.Subset.antisymm (image_lift_subset π H K)
  intro q hq
  obtain ⟨p,hp,hpq⟩ := hK q hq
  exact ⟨p.val,⟨p,hp,le_rfl⟩,hpq⟩

end TuringRigidity.ForcingProjection

end OAI
