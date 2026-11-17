/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicRequirements

/-!
# Atomic Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

private theorem mem_truth_step {N : Set (Name P)} {G : GenericFilter P}
    (hG : Generic N G) (a : Name P) (κ : Type u) (b : κ → Name P) (t : κ → P)
    (ha : a ∈ N) (hb : Name.mk κ b t ∈ N)
    (he : ∀ j, Name.val G.carrier a = Name.val G.carrier (b j) ↔
      ∃ p ∈ G.carrier, EqForces a (b j) p) :
    Name.val G.carrier a ∈ Name.val G.carrier (.mk κ b t) ↔
      ∃ p ∈ G.carrier, MemForces a (.mk κ b t) p := by
  constructor
  · intro hm
    obtain ⟨j,hj,hv⟩ := (Name.mem_val _ _ _ _ _).mp hm
    obtain ⟨p,hp,hf⟩ := (he j).mp hv.symm
    obtain ⟨r,hr,hrp,hrj⟩ := G.directed hp hj
    exact ⟨r,hr,witness_mem _ _ _ ⟨j,hrj,eq_mono _ _ hrp hf⟩⟩
  · rintro ⟨p,hp,hm⟩
    obtain ⟨q,hq,j,hj,hf⟩ := generic_witness hG ha hb hp hm
    exact (Name.mem_val _ _ _ _ _).mpr ⟨j,G.upper hj hq,((he j).mpr ⟨q,hq,hf⟩).symm⟩

theorem eq_truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hG : Generic N G) (a b : Name P) (ha : a ∈ N) (hb : b ∈ N) :
    Name.val G.carrier a = Name.val G.carrier b ↔
      ∃ p ∈ G.carrier, EqForces a b p := by
  induction a generalizing b with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      have ha' (i) : a i ∈ N := hN _ ha _ ⟨i,rfl⟩
      have hb' (j) : b j ∈ N := hN _ hb _ ⟨j,rfl⟩
      have left (i) : Name.val G.carrier (a i) ∈ Name.val G.carrier (.mk κ b t) ↔
          ∃ p ∈ G.carrier, MemForces (a i) (.mk κ b t) p :=
        mem_truth_step hG (a i) κ b t (ha' i) hb (fun j => ih i (b j) (ha' i) (hb' j))
      have right (j) : Name.val G.carrier (b j) ∈ Name.val G.carrier (.mk ι a s) ↔
          ∃ p ∈ G.carrier, MemForces (b j) (.mk ι a s) p := by
        apply mem_truth_step hG (b j) ι a s (hb' j) ha
        intro i
        constructor
        · intro he
          obtain ⟨p,hp,hf⟩ := (ih i (b j) (ha' i) (hb' j)).mp he.symm
          exact ⟨p,hp,eq_symm _ _ _ hf⟩
        · rintro ⟨p,hp,hf⟩
          exact ((ih i (b j) (ha' i) (hb' j)).mpr ⟨p,hp,eq_symm _ _ _ hf⟩).symm
      constructor
      · intro hv
        obtain ⟨p,hp,he | hn⟩ := hG.eqTest _ ha _ hb
        · exact ⟨p,hp,he⟩
        · rcases hn with ⟨i,hi,hn⟩ | ⟨j,hj,hn⟩
          · have hm : Name.val G.carrier (a i) ∈ Name.val G.carrier (.mk κ b t) := by
              rw [←hv]
              exact (Name.mem_val _ _ _ _ _).mpr ⟨i,G.upper hi hp,rfl⟩
            obtain ⟨q,hq,hf⟩ := (left i).mp hm
            obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
            exact False.elim (hn r hrp (mem_mono _ _ hrq hf))
          · have hm : Name.val G.carrier (b j) ∈ Name.val G.carrier (.mk ι a s) := by
              rw [hv]
              exact (Name.mem_val _ _ _ _ _).mpr ⟨j,G.upper hj hp,rfl⟩
            obtain ⟨q,hq,hf⟩ := (right j).mp hm
            obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
            exact False.elim (hn r hrp (mem_mono _ _ hrq hf))
      · rintro ⟨p,hp,he⟩
        apply ZFSet.ext
        intro x
        constructor
        · intro hx
          obtain ⟨i,hi,rfl⟩ := (Name.mem_val _ _ _ _ _).mp hx
          obtain ⟨r,hr,hrp,hri⟩ := G.directed hp hi
          exact (left i).mpr ⟨r,hr,fun q hq => he.1 i q (hq.trans hrp) (hq.trans hri)⟩
        · intro hx
          obtain ⟨j,hj,rfl⟩ := (Name.mem_val _ _ _ _ _).mp hx
          obtain ⟨r,hr,hrp,hrj⟩ := G.directed hp hj
          apply (right j).mpr
          refine ⟨r,hr,?_⟩
          intro q hq
          obtain ⟨w,hw,i,hi,hf⟩ := he.2 j q (hq.trans hrp) (hq.trans hrj)
          exact ⟨w,hw,i,hi,eq_symm _ _ _ hf⟩

theorem mem_truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hG : Generic N G) (a b : Name P) (ha : a ∈ N) (hb : b ∈ N) :
    Name.val G.carrier a ∈ Name.val G.carrier b ↔
      ∃ p ∈ G.carrier, MemForces a b p := by
  cases b with
  | mk κ b t =>
    exact mem_truth_step hG a κ b t ha hb
      (fun j => eq_truth hN G hG a (b j) ha (hN _ hb _ ⟨j,rfl⟩))

end TuringRigidity.AtomicForcing

end OAI
