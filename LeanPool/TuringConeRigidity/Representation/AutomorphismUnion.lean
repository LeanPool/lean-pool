/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/AutomorphismUnion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentRestrictions
public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing

/-!
# Automorphism Union
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AutomorphismUnion
open Set PersistentRestrictions CountableForcing

structure Approximation where
  ideal : CountableIdeal
  map : ideal ≃o ideal

instance : Preorder Approximation where
  le p q := ∃ h : q.ideal.carrier ⊆ p.ideal.carrier, Extends h q.map p.map
  le_refl p := ⟨fun _ h => h, fun _ => rfl⟩
  le_trans p q r hpq hqr := by
    obtain ⟨hpq,epq⟩ := hpq
    obtain ⟨hqr,eqr⟩ := hqr
    refine ⟨fun _ h => hpq (hqr h), fun a => ?_⟩
    exact (epq ⟨a.val,hqr a.property⟩).trans (eqr a)

def Domain (G : GenericFilter Approximation) : Set Degree :=
  {a | ∃ p ∈ G.carrier, a ∈ p.ideal.carrier}

def Graph (G : GenericFilter Approximation) (a b : Degree) : Prop :=
  ∃ p ∈ G.carrier, ∃ ha : a ∈ p.ideal.carrier, (p.map ⟨a,ha⟩).val = b

theorem graph_mono {p q : Approximation} (hpq : p ≤ q)
    {a b : Degree} (ha : a ∈ q.ideal.carrier) (hab : (q.map ⟨a, ha⟩).val = b) :
    ∃ h : a ∈ p.ideal.carrier, (p.map ⟨a,h⟩).val = b := by
  obtain ⟨h,e⟩ := hpq
  exact ⟨h ha,(e ⟨a,ha⟩).trans hab⟩

theorem graph_domain {G : GenericFilter Approximation} {a b : Degree}
    (h : Graph G a b) : a ∈ Domain G ∧ b ∈ Domain G := by
  obtain ⟨p,hp,ha,rfl⟩ := h
  exact ⟨⟨p,hp,ha⟩,⟨p,hp,(p.map ⟨a,ha⟩).property⟩⟩

theorem graph_total (G : GenericFilter Approximation) {a : Degree} (ha : a ∈ Domain G) :
    ∃ b, Graph G a b := by
  obtain ⟨p,hp,ha⟩ := ha
  exact ⟨_,p,hp,ha,rfl⟩

theorem graph_surjective (G : GenericFilter Approximation) {b : Degree} (hb : b ∈ Domain G) :
    ∃ a, Graph G a b := by
  obtain ⟨p,hp,hb⟩ := hb
  refine ⟨(p.map.symm ⟨b,hb⟩).val,p,hp,(p.map.symm ⟨b,hb⟩).property,?_⟩
  exact congrArg Subtype.val (p.map.apply_symm_apply ⟨b,hb⟩)

theorem graph_order (G : GenericFilter Approximation) {a b c d : Degree}
    (hab : Graph G a b) (hcd : Graph G c d) : a ≤ c ↔ b ≤ d := by
  obtain ⟨p,hp,ha,hab⟩ := hab
  obtain ⟨q,hq,hc,hcd⟩ := hcd
  obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
  obtain ⟨ha',hab'⟩ := graph_mono hrp ha hab
  obtain ⟨hc',hcd'⟩ := graph_mono hrq hc hcd
  rw [←hab',←hcd']
  exact (@OrderIso.le_iff_le _ _ _ _ r.map ⟨a,ha'⟩ ⟨c,hc'⟩).symm

theorem graph_unique (G : GenericFilter Approximation) {a b c : Degree}
    (hab : Graph G a b) (hac : Graph G a c) : b = c :=
  le_antisymm ((graph_order G hab hac).mp le_rfl) ((graph_order G hac hab).mp le_rfl)

theorem graph_injective (G : GenericFilter Approximation) {a b c : Degree}
    (hac : Graph G a c) (hbc : Graph G b c) : a = b :=
  le_antisymm ((graph_order G hac hbc).mpr le_rfl) ((graph_order G hbc hac).mpr le_rfl)

noncomputable def value (G : GenericFilter Approximation) (a : Domain G) : Domain G :=
  ⟨Classical.choose (graph_total G a.property),
    (graph_domain (Classical.choose_spec (graph_total G a.property))).2⟩

theorem value_graph (G : GenericFilter Approximation) (a : Domain G) :
    Graph G a.val (value G a).val := Classical.choose_spec (graph_total G a.property)

noncomputable def inverse (G : GenericFilter Approximation) (b : Domain G) : Domain G :=
  ⟨Classical.choose (graph_surjective G b.property),
    (graph_domain (Classical.choose_spec (graph_surjective G b.property))).1⟩

theorem inverse_graph (G : GenericFilter Approximation) (b : Domain G) :
    Graph G (inverse G b).val b.val := Classical.choose_spec (graph_surjective G b.property)

noncomputable def automorphism (G : GenericFilter Approximation) : Domain G ≃o Domain G where
  toFun := value G
  invFun := inverse G
  left_inv a := Subtype.ext (graph_injective G (inverse_graph G (value G a)) (value_graph G a))
  right_inv b := Subtype.ext (graph_unique G (value_graph G (inverse G b)) (inverse_graph G b))
  map_rel_iff' := fun {a b} => (graph_order G (value_graph G a) (value_graph G b)).symm

theorem automorphism_graph (G : GenericFilter Approximation) (a : Domain G) (b : Degree) :
    (automorphism G a).val = b ↔ Graph G a.val b := by
  constructor
  · rintro rfl; exact value_graph G a
  · exact graph_unique G (value_graph G a)

theorem automorphism_extends (G : GenericFilter Approximation) {p : Approximation}
    (hp : p ∈ G.carrier) (a : p.ideal) :
    (automorphism G ⟨a.val,⟨p,hp,a.property⟩⟩).val = (p.map a).val :=
  (automorphism_graph G _ _).mpr ⟨p,hp,a.property,rfl⟩

theorem domain_lower (G : GenericFilter Approximation) {a b : Degree}
    (hab : a ≤ b) (hb : b ∈ Domain G) : a ∈ Domain G := by
  obtain ⟨p,hp,hb⟩ := hb
  exact ⟨p,hp,p.ideal.lower hab hb⟩

theorem domain_join (G : GenericFilter Approximation) {a b : Degree}
    (ha : a ∈ Domain G) (hb : b ∈ Domain G) : a ⊔ b ∈ Domain G := by
  obtain ⟨p,hp,ha⟩ := ha
  obtain ⟨q,hq,hb⟩ := hb
  obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
  exact ⟨r,hr,r.ideal.join_mem (hrp.choose ha) (hrq.choose hb)⟩

end TuringRigidity.AutomorphismUnion

end OAI
