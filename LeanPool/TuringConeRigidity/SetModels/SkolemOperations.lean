/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SkolemOperations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCoverInjection
public import LeanPool.TuringConeRigidity.SetModels.FiniteSkolem

/-!
# Skolem Operations
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

noncomputable def labelGraph (a b g o : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair (ZFSet.pair o x) y ∧ ZFSet.pair x y ∈ g)
    (ZFSet.prod (ZFSet.prod {o} a) b)

theorem labelGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {a b g o : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) (hg : g ∈ M) (ho : o ∈ M) :
    labelGraph a b g o ∈ M := by
  simpa only
    [labelGraph,Formula.Eval,Formula.eval_leftPair,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 3 (.conj (.leftPair 2 5 1 0) (.pairMem 1 0 6))))
      (cons a (cons b (cons o (fun _ => g)))) (by
        intro i
        rcases i with _ | i
        · exact ha
        rcases i with _ | i
        · exact hb
        rcases i with _ | i
        · exact ho
        exact hg)
      (product_mem M hM hP hU hPow hS
        (product_mem M hM hP hU hPow hS (singleton_mem M hM hP ho) ha) hb)

theorem labelGraph_shape {a b g o z : ZFSet.{u}} (hz : z ∈ labelGraph a b g o) :
    ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair (ZFSet.pair o x) y ∧ ZFSet.pair x y ∈ g :=
  (ZFSet.mem_sep.mp hz).2

theorem labelGraph_contains {a b g o x y : ZFSet.{u}} (hg : g ⊆ ZFSet.prod a b)
    (hxy : ZFSet.pair x y ∈ g) : ZFSet.pair (ZFSet.pair o x) y ∈ labelGraph a b g o := by
  obtain ⟨x',hx,y',hy,hp⟩ := ZFSet.mem_prod.mp (hg hxy)
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
  exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_prod.mpr
    ⟨_,ZFSet.mem_prod.mpr ⟨o,ZFSet.mem_singleton.mpr rfl,x,hx,rfl⟩,y,hy,rfl⟩,x,hx,y,hy,rfl,hxy⟩

theorem labelGraph_functional {a b g o : ZFSet.{u}} (hg : Functional g) :
    Functional (labelGraph a b g o) := by
  intro c x y hx hy
  obtain ⟨u,_,v,_,he,huv⟩ := labelGraph_shape hx
  obtain ⟨hcu,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨u',_,v',_,he,huv'⟩ := labelGraph_shape hy
  obtain ⟨hcu',rfl⟩ := ZFSet.pair_inj.mp he
  have huu := (ZFSet.pair_inj.mp (hcu.symm.trans hcu')).2
  subst u'
  exact hg u x y huv huv'

theorem Functional.union {f g : ZFSet.{u}} (hf : Functional f) (hg : Functional g)
    (hdis : ∀ a x y, ZFSet.pair a x ∈ f → ZFSet.pair a y ∈ g → False) : Functional (f ∪ g) := by
  intro a x y hx hy
  rcases ZFSet.mem_union.mp hx with hx|hx <;> rcases ZFSet.mem_union.mp hy with hy|hy
  · exact hf a x y hx hy
  · exact False.elim (hdis a x y hx hy)
  · exact False.elim (hdis a y x hy hx)
  · exact hg a x y hx hy

theorem skolem_functional {d g : ZFSet.{u}} {n : ℕ} {φ : Formula} {e : ℕ → ZFSet.{u}}
    (hg : FiniteTuple.SkolemGraph d n φ e g) : Functional g := by
  intro c x y hx hy
  have hp := (ZFSet.mem_sep.mp (hg.1 hx)).1
  obtain ⟨c',hc,x',_,he⟩ := ZFSet.mem_prod.mp hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨xs,hlen,_,rfl⟩ := (FiniteTuple.mem_space d c n).mp hc
  exact hg.functional xs hlen hx hy

theorem internal_skolem_operations (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (fs : List Formula) (start : ℕ) :
    ∃ O ∈ M, Functional O ∧
      (∀ z ∈ O, ∃ i, start ≤ i ∧ ∃ c v, z = ZFSet.pair (ZFSet.pair (natSet i) c) v) ∧
      ∀ φ ∈ fs, ∃ i : ℕ, ∃ g ∈ M, FiniteTuple.SkolemGraph d n φ (fun _ => d) g ∧
        ∀ c v, ZFSet.pair c v ∈ g → ZFSet.pair (ZFSet.pair (natSet i) c) v ∈ O := by
  have hω := omega_mem M hM hS hI
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have ha := FiniteTuple.space_mem M hM hP hU hPow hS hd n
  induction fs generalizing start with
  | nil => exact ⟨∅,hn 0,by intro a x y hx; exact False.elim (by simp at hx),by simp,by simp⟩
  | cons φ fs ih =>
    obtain ⟨O,hO,hOf,hOs,hOg⟩ := ih (start+1)
    obtain ⟨g,hg,hgs⟩ := FiniteTuple.internal_skolem_graph M hM hP hU hPow hS hR hI hAC hd n φ
      (fun _ => d) (fun _ => hd)
    let f := labelGraph (FiniteTuple.space d n) d g (natSet start)
    have hf : f ∈ M := labelGraph_mem M hM hP hU hPow hS ha hd hg (hn start)
    have hff : Functional f := labelGraph_functional (skolem_functional hgs)
    have hfshape (z : ZFSet.{u}) (hz : z ∈ f) :
        ∃ c v, z = ZFSet.pair (ZFSet.pair (natSet start) c) v := by
      obtain ⟨c,_,v,_,he,_⟩ := labelGraph_shape hz
      exact ⟨c,v,he⟩
    refine ⟨f ∪ O,binary_union_mem M hM hP hU hf hO,hff.union hOf ?_,?_,?_⟩
    · intro a x y hx hy
      obtain ⟨c,v,hc⟩ := hfshape _ hx
      obtain ⟨i,hi,b,w,hb⟩ := hOs _ hy
      have hac := (ZFSet.pair_inj.mp hc).1
      have hab := (ZFSet.pair_inj.mp hb).1
      have he := natSet_injective (ZFSet.pair_inj.mp (hac.symm.trans hab)).1
      omega
    · intro z hz
      rcases ZFSet.mem_union.mp hz with hz|hz
      · obtain ⟨c,v,he⟩ := hfshape z hz
        exact ⟨start,le_refl _,c,v,he⟩
      · obtain ⟨i,hi,c,v,he⟩ := hOs z hz
        exact ⟨i,by omega,c,v,he⟩
    · intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl|hψ
      · refine ⟨start,g,hg,hgs,?_⟩
        intro c v hcv
        exact ZFSet.mem_union.mpr (Or.inl (labelGraph_contains
          (fun z hz => (ZFSet.mem_sep.mp (hgs.1 hz)).1) hcv))
      · obtain ⟨i,v,hv,hvs,hvo⟩ := hOg ψ hψ
        exact ⟨i,v,hv,hvs,fun c x hcx => ZFSet.mem_union.mpr (Or.inr (hvo c x hcx))⟩

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
