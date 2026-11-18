/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenProductFilters.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenCoordinates
public import LeanPool.TuringConeRigidity.Representation.AutomorphismName

/-!
# Cohen Product Filters
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenProductFilters
open Set CountableForcing CohenSymmetry CohenCoordinates AutomorphismName
universe u v
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

/-- Project a filter on a product poset to its first coordinate. -/
def first (K : GenericFilter (P × Q)) : GenericFilter P where
  carrier := {p | ∃ q, (p,q) ∈ K.carrier}
  nonempty := by obtain ⟨p,hp⟩ := K.nonempty; exact ⟨p.1,p.2,hp⟩
  upper := by rintro p q hpq ⟨r,hr⟩; exact ⟨r,K.upper (p := (p,r)) (q := (q,r)) ⟨hpq,le_rfl⟩ hr⟩
  directed := by
    rintro p q ⟨r,hr⟩ ⟨s,hs⟩
    obtain ⟨t,ht,htp,htq⟩ := K.directed hr hs
    exact ⟨t.1,⟨t.2,ht⟩,htp.1,htq.1⟩

/-- Project a filter on a product poset to its second coordinate. -/
def second (K : GenericFilter (P × Q)) : GenericFilter Q where
  carrier := {q | ∃ p, (p,q) ∈ K.carrier}
  nonempty := by obtain ⟨p,hp⟩ := K.nonempty; exact ⟨p.2,p.1,hp⟩
  upper := by rintro p q hpq ⟨r,hr⟩; exact ⟨r,K.upper (p := (r,p)) (q := (r,q)) ⟨le_rfl,hpq⟩ hr⟩
  directed := by
    rintro p q ⟨r,hr⟩ ⟨s,hs⟩
    obtain ⟨t,ht,htp,htq⟩ := K.directed hr hs
    exact ⟨t.2,⟨t.1,ht⟩,htp.2,htq.2⟩

theorem mem_iff (K : GenericFilter (P × Q)) (p : P) (q : Q) :
    (p,q) ∈ K.carrier ↔ p ∈ (first K).carrier ∧ q ∈ (second K).carrier := by
  constructor
  · intro h; exact ⟨⟨q,h⟩,⟨p,h⟩⟩
  · rintro ⟨⟨s,hs⟩,⟨r,hr⟩⟩
    obtain ⟨t,ht,hts,htr⟩ := K.directed hs hr
    exact K.upper ⟨hts.1,htr.2⟩ ht

theorem product_eq (K : GenericFilter (P × Q)) :
    (SourceEquationTail.productFilter (first K) (second K)).carrier = K.carrier := by
  ext p
  exact (mem_iff K p.1 p.2).symm

theorem first_dense (D : Set P) (hD : Dense D) :
    Dense {p : P × Q | p.1 ∈ D} := by
  intro p
  obtain ⟨q,hq,hqD⟩ := hD p.1
  exact ⟨(q,p.2),⟨hq,le_rfl⟩,hqD⟩

theorem first_generic (D : ℕ → Set P) (K : GenericFilter (P × Q))
    (hK : GenericFor (fun n => {p | p.1 ∈ D n}) K) : GenericFor D (first K) := by
  intro n
  obtain ⟨p,hp,hpD⟩ := hK n
  exact ⟨p.1,⟨p.2,hp⟩,hpD⟩

/-- The second-coordinate fiber of `D` over conditions belonging to `G`. -/
def fiber (D : Set (P × Q)) (G : GenericFilter P) : Set Q :=
  {q | ∃ p ∈ G.carrier, (p,q) ∈ D}

/-- First coordinates admitting a pair in `D` below the prescribed second condition. -/
def fiberRequirement (D : Set (P × Q)) (q : Q) : Set P :=
  {p | ∃ r, r ≤ q ∧ (p,r) ∈ D}

theorem fiberRequirement_dense (D : Set (P × Q)) (hD : Dense D) (q : Q) :
    Dense (fiberRequirement D q) := by
  intro p
  obtain ⟨r,hr,hrD⟩ := hD (p,q)
  exact ⟨r.1,hr.1,r.2,hr.2,hrD⟩

theorem fiber_dense (D : Set (P × Q)) (G : GenericFilter P)
    (hG : ∀ q, ∃ p ∈ G.carrier, p ∈ fiberRequirement D q) : Dense (fiber D G) := by
  intro q
  obtain ⟨p,hp,r,hr,hrD⟩ := hG q
  exact ⟨r,hr,p,hp,hrD⟩

theorem generic_product_iff (D : ℕ → Set (P × Q)) (K : GenericFilter (P × Q)) :
    GenericFor D K ↔ GenericFor (fun n => fiber (D n) (first K)) (second K) := by
  constructor
  · intro h n
    obtain ⟨p,hp,hpD⟩ := h n
    exact ⟨p.2,⟨p.1,hp⟩,p.1,⟨p.2,hp⟩,hpD⟩
  · intro h n
    obtain ⟨q,hq,p,hp,hpqD⟩ := h n
    exact ⟨(p,q),(mem_iff K p q).mpr ⟨hp,hq⟩,hpqD⟩

theorem partition_filter {ι : Type u} (S : Set ι)
    (G : GenericFilter (Condition ι)) :
    let K := mapFilter (partitionIso S) G
    K.carrier = (SourceEquationTail.productFilter (first K) (second K)).carrier ∧
      ∀ D : ℕ → Set (Condition S × Condition (Sᶜ : Set ι)),
        GenericFor D K ↔ GenericFor (fun n => fiber (D n) (first K)) (second K) :=
  ⟨(product_eq _).symm,fun D => generic_product_iff D _⟩

end TuringRigidity.CohenProductFilters

end OAI
