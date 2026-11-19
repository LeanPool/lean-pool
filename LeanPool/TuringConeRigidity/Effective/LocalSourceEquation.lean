/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalSourceEquation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.AutomorphismName

/-!
# Local Source Equation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalSourceEquation
open Set PersistentRestrictions AutomorphismUnion AutomorphismName GenericIdentity

instance (I : CountableIdeal) : SemilatticeSup I where
  sup a b := ⟨a.val ⊔ b.val,I.join_mem a.property b.property⟩
  le_sup_left a b := (le_sup_left : a.val ≤ a.val ⊔ b.val)
  le_sup_right a b := (le_sup_right : b.val ≤ a.val ⊔ b.val)
  sup_le a b c h₁ h₂ := (sup_le h₁ h₂ : a.val ⊔ b.val ≤ c.val)

theorem local_map_join (I : CountableIdeal) (σ : I ≃o I) (a b : I) :
    (σ (a ⊔ b)).val = (σ a).val ⊔ (σ b).val :=
  congrArg Subtype.val (σ.map_sup a b)

theorem local_intersection (I : CountableIdeal) (σ : I ≃o I) (a l r : I)
    (h : ∀ b : Degree, b ≤ a.val ↔ b ≤ l.val ∧ b ≤ r.val) :
    ∀ b : Degree, b ≤ (σ a).val ↔ b ≤ (σ l).val ∧ b ≤ (σ r).val := by
  intro b
  constructor
  · intro hb
    have ha := (h a.val).mp le_rfl
    exact ⟨hb.trans (σ.monotone ha.1),hb.trans (σ.monotone ha.2)⟩
  · rintro ⟨hl,hr⟩
    let bI : I := ⟨b,I.lower hl (σ l).property⟩
    have hl' : σ.symm bI ≤ l := by
      apply σ.le_iff_le.mp
      simpa only [σ.apply_symm_apply] using (show bI ≤ σ l from hl)
    have hr' : σ.symm bI ≤ r := by
      apply σ.le_iff_le.mp
      simpa only [σ.apply_symm_apply] using (show bI ≤ σ r from hr)
    have hba : σ.symm bI ≤ a := (h (σ.symm bI).val).mpr ⟨hl',hr'⟩
    have hh := σ.monotone hba
    have hh' : bI ≤ σ a := by simpa only [σ.apply_symm_apply] using hh
    exact hh'

theorem graph_join (G : CountableForcing.GenericFilter Approximation) {a b c d : Degree}
    (hab : Graph G a b) (hcd : Graph G c d) : Graph G (a ⊔ c) (b ⊔ d) := by
  obtain ⟨p,hp,ha,hab⟩ := hab
  obtain ⟨q,hq,hc,hcd⟩ := hcd
  obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
  obtain ⟨ha',hab'⟩ := graph_mono hrp ha hab
  obtain ⟨hc',hcd'⟩ := graph_mono hrq hc hcd
  refine ⟨r,hr,r.ideal.join_mem ha' hc',?_⟩
  exact (local_map_join r.ideal r.map ⟨a,ha'⟩ ⟨c,hc'⟩).trans (congrArg₂ (· ⊔ ·) hab' hcd')

theorem graph_intersection (G : CountableForcing.GenericFilter Approximation)
    {a a' l l' r r' : Degree} (ha : Graph G a a') (hl : Graph G l l') (hr : Graph G r r')
    (h : ∀ b : Degree, b ≤ a ↔ b ≤ l ∧ b ≤ r) :
    ∀ b : Degree, b ≤ a' ↔ b ≤ l' ∧ b ≤ r' := by
  intro b
  constructor
  · intro hb
    have ha₀ := (h a).mp le_rfl
    exact ⟨hb.trans ((graph_order G ha hl).mp ha₀.1),hb.trans ((graph_order G ha hr).mp ha₀.2)⟩
  · rintro ⟨hbl,hbr⟩
    have hbD := domain_lower G hbl (graph_domain hl).2
    obtain ⟨c,hcb⟩ := graph_surjective G hbD
    have hc : c ≤ a := (h c).mpr ⟨(graph_order G hcb hl).mpr hbl,(graph_order G hcb hr).mpr hbr⟩
    exact (graph_order G hcb ha).mp hc

/-- The program is total at `A` and its input-output degree pair belongs to the interpreted
graph name. -/
def Represented (G : CountableForcing.GenericFilter Approximation)
    (p : OracleCode) (P A : Oracle) : Prop :=
  Total p P A ∧ (degree A,degree (GenericIdentity.value p P A)) ∈ interpret graphName G

theorem sourceEquation_of_graph (G : CountableForcing.GenericFilter Approximation)
    (p : OracleCode) (P Y L R : Oracle)
    (hL : GenericCoding.InfiniteOdd L) (hR : GenericCoding.InfiniteOdd R)
    (hideal : ∀ b : Degree, b ≤ degree Y ↔ b ≤ degree (join Y L) ∧ b ≤ degree (join Y R))
    (hY : Represented G p P Y) (hGL : Represented G p P L) (hGR : Represented G p P R)
    (hCL : Represented G p P (GenericCoding.code Y L))
    (hCR : Represented G p P (GenericCoding.code Y R)) : SourceEquation p P (Y,L,R) := by
  refine ⟨hY.1,hGL.1,hGR.1,hCL.1,hCR.1,?_⟩
  have hleft := graph_join G hCL.2 hGL.2
  have hright := graph_join G hCR.2 hGR.2
  change Graph G (degree (join (GenericCoding.code Y L) L))
    (degree (join (GenericIdentity.value p P (GenericCoding.code Y L)) (GenericIdentity.value p P
      L))) at hleft
  change Graph G (degree (join (GenericCoding.code Y R) R))
    (degree (join (GenericIdentity.value p P (GenericCoding.code Y R)) (GenericIdentity.value p P
      R))) at hright
  rw [GenericCoding.join_degree_eq Y L hL] at hleft
  rw [GenericCoding.join_degree_eq Y R hR] at hright
  exact graph_intersection G hY.2 hleft hright hideal

end TuringRigidity.LocalSourceEquation

end OAI
