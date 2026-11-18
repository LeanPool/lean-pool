/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularBinaryTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalProjectedGeneric
public import LeanPool.TuringConeRigidity.SetModels.RegularDecisionPartition

/-!
# Regular Binary Tree
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularBinaryTree
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularDecisionPartition RegularCodeSplitting

/-- Select two positive child codes satisfying the splitting relation, with empty codes as the
fallback. -/
noncomputable def children (B T U D : ZFSet.{0}) : Bool → ZFSet.{0} := by
  classical
  exact if h : ∃ f : Bool → ZFSet.{0}, (∀ b, f b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair (f false) (f true)) ∈ T
    then h.choose else fun _ => ∅

theorem children_spec (B T U D : ZFSet.{0})
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hD : D ∈ B) :
    (∀ b, children B T U D b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D)
        (ZFSet.pair (children B T U D false) (children B T U D true)) ∈ T := by
  classical
  obtain ⟨y,hy,hxy,_⟩ := hf.2 (ZFSet.pair U D) (ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩)
  obtain ⟨V,hV,W,hW,rfl⟩ := ZFSet.mem_prod.mp hy
  have hex : ∃ f : Bool → ZFSet.{0}, (∀ b, f b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair (f false) (f true)) ∈ T := by
    refine ⟨(fun b => if b then W else V),?_,hxy⟩
    intro b
    cases b
    · exact hV
    · exact hW
  simp only [children,dite_eq_left hex]
  exact hex.choose_spec

theorem children_unique (B T U D V W : ZFSet.{0})
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hD : D ∈ B)
    (hp : ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T) :
    V = children B T U D false ∧ W = children B T U D true :=
  ZFSet.pair_inj.mp (hf.functional (ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩) hp
    (children_spec B T U D hf hU hD).2)

/-- Follow a finite binary path through the selected regular-code splitting tree. -/
noncomputable def tree (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) : ZFSet.{0} :=
  s.reverseRecOn c (fun t b U => children B T U (E t.length) b)

theorem tree_nil (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : tree c B T E [] = c := by
  simp only [tree,List.reverseRecOn_nil]

theorem tree_append (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) (b : Bool) :
    tree c B T E (s ++ [b]) = children B T (tree c B T E s) (E s.length) b := by
  simp only [tree,List.reverseRecOn_concat]

variable (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0})
variable (hc : c ∈ positive B)
variable (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
variable (hE : ∀ n, E n ∈ B)
variable (hB : ∀ U ∈ B, IsCode c U)
variable (hs : ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
  ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
    V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W)

include hc hf hE

theorem tree_positive (s : List Bool) : tree c B T E s ∈ positive B := by
  induction s using List.reverseRecOn with
  | nil => simpa only [tree_nil] using hc
  | append_singleton s b ih =>
    rw [tree_append]
    exact (children_spec B T _ _ hf ih (hE s.length)).1 b

include hs

theorem tree_refines (s : List Bool) :
    Refines c (tree c B T E s) (E s.length)
      (tree c B T E (s ++ [false])) (tree c B T E (s ++ [true])) := by
  rw [tree_append,tree_append]
  have hp := tree_positive c B T E hc hf hE s
  exact (hs _ hp _ (hE s.length) _ _ (children_spec B T _ _ hf hp (hE s.length)).2).2.2

theorem tree_child_subset (s : List Bool) (b : Bool) :
    tree c B T E (s ++ [b]) ⊆ tree c B T E s := by
  have h := (tree_refines c B T E hc hf hE hs s).1
  cases b
  · exact h.1
  · exact h.2.1

theorem tree_append_subset (s t : List Bool) : tree c B T E (s ++ t) ⊆ tree c B T E s := by
  induction t using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using (show tree c B T E s ⊆ tree c B T E s from fun _ h
    => h)
  | append_singleton t b ih =>
    rw [←List.append_assoc]
    exact fun _ hp => ih (tree_child_subset c B T E hc hf hE hs (s ++ t) b hp)

theorem tree_prefix (s t : List Bool) (hst : s <+: t) : tree c B T E t ⊆ tree c B T E s := by
  obtain ⟨u,rfl⟩ := hst
  exact tree_append_subset c B T E hc hf hE hs s u

theorem tree_incompatible (s u v : List Bool) :
    ∀ p ∈ tree c B T E (s ++ [false] ++ u), p ∉ tree c B T E (s ++ [true] ++ v) := by
  intro p hp hq
  exact (tree_refines c B T E hc hf hE hs s).1.2.2.2.2.1 p
    (tree_append_subset c B T E hc hf hE hs (s ++ [false]) u hp)
    (tree_append_subset c B T E hc hf hE hs (s ++ [true]) v hq)

include hB

theorem level_overlaps (D : ZFSet.{0}) (hD : IsCode c D) (hD0 : D ≠ ∅) (n : ℕ) :
    ∃ s : List Bool, s.length = n ∧ ∃ p ∈ tree c B T E s, p ∈ D := by
  classical
  induction n with
  | zero =>
    obtain he|⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty D
    · exact False.elim (hD0 he)
    · exact ⟨[],rfl,p,by rw [tree_nil]; exact hD.1 hp,hp⟩
  | succ n ih =>
    obtain ⟨s,hlen,p,hp,hpD⟩ := ih
    have hpart := (tree_refines c B T E hc hf hE hs s).1
    obtain ⟨r,hr,hpr,hrL|hrR⟩ := hpart.2.2.2.2.2 p hp
    · have hrC := (hB _ (ZFSet.mem_sep.mp (tree_positive c B T E hc hf hE s)).1).1 hr
      exact ⟨s ++ [false],by simp [hlen],r,hrL,code_lower c D hD p hpD r hrC hpr⟩
    · have hrC := (hB _ (ZFSet.mem_sep.mp (tree_positive c B T E hc hf hE s)).1).1 hr
      exact ⟨s ++ [true],by simp [hlen],r,hrR,code_lower c D hD p hpD r hrC hpr⟩

theorem refines_enumerated (n : ℕ) (hn : E n ≠ ∅) :
    ∃ s : List Bool, s.length = n+1 ∧ tree c B T E s ⊆ E n := by
  obtain ⟨s,hlen,p,hp,hpE⟩ := level_overlaps c B T E hc hf hE hB hs (E n) (hB _ (hE n)) hn (n+1)
  cases s using List.reverseRecOn with
  | nil => simp at hlen
  | append_singleton s b =>
    have hslen : s.length = n := by
      simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hlen
    have hd := tree_refines c B T E hc hf hE hs s
    have hdec : tree c B T E (s ++ [b]) ⊆ E n ∨ tree c B T E (s ++ [b]) ⊆ neg c (E n) := by
      rw [←hslen]
      cases b
      · exact hd.2.1
      · exact hd.2.2
    rcases hdec with h|h
    · exact ⟨s ++ [b],hlen,h⟩
    · exact False.elim ((ZFSet.mem_sep.mp (h hp)).2 p hpE (fun _ h => h))

theorem tree_dense
    (hDense : ∀ D, IsCode c D → D ≠ ∅ → ∃ n, E n ≠ ∅ ∧ E n ⊆ D) :
    ∀ D, IsCode c D → D ≠ ∅ → ∃ s : List Bool, tree c B T E s ⊆ D := by
  intro D hD hD0
  obtain ⟨n,hn,hnD⟩ := hDense D hD hD0
  obtain ⟨s,_,hsD⟩ := refines_enumerated c B T E hc hf hE hB hs n hn
  exact ⟨s,fun _ hp => hnD (hsD hp)⟩

end TuringRigidity.RegularBinaryTree

end OAI
