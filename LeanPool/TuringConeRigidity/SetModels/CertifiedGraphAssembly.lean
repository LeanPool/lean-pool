/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Shared from the Apache-2.0 upstream DegreeRigidity proofs in
Constructibility/InternalRankRecursion.lean, SetModels/InternalCheckRecursion.lean,
Constructibility/InternalHierarchyRecursion.lean, and SetModels/InternalRelationCollapse.lean.
Certificate interpretation, graph uniqueness, and recursive value closure remain supplied by
those interfaces; only their replacement, union, and singleton-extension assembly is shared.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Assembly of internally certified graphs

The certificate relation and its semantic membership description are parameters. No graph
recursion, well-foundedness, powerset, infinity, collection, or choice axiom is assumed here.
-/

@[expose] public section

namespace OAI.TuringRigidity.CertifiedGraphAssembly

open TransitiveNameModel BoundedSetTheory

universe u

/-- Collect the unique internally certified witness for each member of an internal set. -/
theorem certified_replacement (M a : ZFSet.{u}) (hM : Transitive M)
    (hR : SigmaReplacement M) (ha : a ∈ M) (p : SigmaFormula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (cert : ∀ y ∈ a, ∀ f ∈ M, p.Realize M (cons f (cons y e)) ↔ P y f)
    (exists_witness : ∀ y ∈ a, ∃ f ∈ M, P y f)
    (unique_witness : ∀ y ∈ a, ∀ f g, P y f → P y g → f = g) :
    ∃ b ∈ M, ∀ f, f ∈ b ↔ ∃ y ∈ a, P y f := by
  obtain ⟨b,hb,hbdef⟩ := hR p e he a ha (by
    intro y hy
    obtain ⟨f,hf,hpf⟩ := exists_witness y hy
    refine ⟨f,hf,(cert y hy f hf).mpr hpf,?_⟩
    intro g hg hcg
    exact unique_witness y hy g f ((cert y hy g hg).mp hcg) hpf)
  refine ⟨b,hb,fun f => ?_⟩
  constructor
  · intro hf
    have hfM := hM b hb f hf
    obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
    exact ⟨y,hy,(cert y hy f hfM).mp hc⟩
  · rintro ⟨y,hy,hpf⟩
    obtain ⟨f',hf',hpf'⟩ := exists_witness y hy
    have hfM : f ∈ M := unique_witness y hy f f' hpf hpf' ▸ hf'
    exact (hbdef f hfM).mpr ⟨y,hy,(cert y hy f hfM).mpr hpf⟩

/-- Union the unique certified graphs, using their supplied semantic membership predicates. -/
theorem certified_union (M a : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hR : SigmaReplacement M) (ha : a ∈ M)
    (p : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (P R : ZFSet.{u} → ZFSet.{u} → Prop)
    (cert : ∀ y ∈ a, ∀ f ∈ M, p.Realize M (cons f (cons y e)) ↔ P y f)
    (exists_witness : ∀ y ∈ a, ∃ f ∈ M, P y f)
    (unique_witness : ∀ y ∈ a, ∀ f g, P y f → P y g → f = g)
    (member : ∀ y ∈ a, ∀ f, P y f → ∀ z, z ∈ f ↔ R y z) :
    ∃ g ∈ M, ∀ z, z ∈ g ↔ ∃ y ∈ a, R y z := by
  obtain ⟨b,hb,hbdef⟩ := certified_replacement M a hM hR ha p e he P
    cert exists_witness unique_witness
  refine ⟨ZFSet.sUnion b,union_mem M hM hU hb,fun z => ?_⟩
  constructor
  · intro hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    obtain ⟨y,hy,hpf⟩ := (hbdef f).mp hf
    exact ⟨y,hy,(member y hy f hpf z).mp hzf⟩
  · rintro ⟨y,hy,hyz⟩
    obtain ⟨f,hf,hpf⟩ := exists_witness y hy
    exact ZFSet.mem_sUnion.mpr ⟨f,(hbdef f).mpr ⟨y,hy,hpf⟩,
      (member y hy f hpf z).mpr hyz⟩

/-- Add the current value to a union of predecessor graphs on a recursively unfolded domain. -/
theorem singleton_graph_extension (a x : ZFSet.{u})
    (D V : ZFSet.{u} → ZFSet.{u}) (H g : ZFSet.{u})
    (domain : ∀ w, w ∈ H ↔ w = x ∨ ∃ y ∈ a, w ∈ D y)
    (member : ∀ z, z ∈ g ↔ ∃ y ∈ a, ∃ w ∈ D y, z = ZFSet.pair w (V w)) :
    ∀ z, z ∈ g ∪ ({ZFSet.pair x (V x)} : ZFSet.{u}) ↔
      ∃ w ∈ H, z = ZFSet.pair w (V w) := by
  intro z
  rw [ZFSet.mem_union,ZFSet.mem_singleton,member]
  constructor
  · rintro (⟨y,hy,w,hw,hz⟩|hz)
    · exact ⟨w,(domain w).mpr (Or.inr ⟨y,hy,hw⟩),hz⟩
    · exact ⟨x,(domain x).mpr (Or.inl rfl),hz⟩
  · rintro ⟨w,hw,hz⟩
    rcases (domain w).mp hw with rfl|⟨y,hy,hw⟩
    · exact Or.inr hz
    · exact Or.inl ⟨y,hy,w,hw,hz⟩

end OAI.TuringRigidity.CertifiedGraphAssembly
