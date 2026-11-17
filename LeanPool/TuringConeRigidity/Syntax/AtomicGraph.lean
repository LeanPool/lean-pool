/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicFormula
public import LeanPool.TuringConeRigidity.SetModels.InternalFixedPoint
public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Atomic Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

/-- The graph contains exactly the triples satisfying its recursive atomic equality-forcing
equation. -/
def Graph (d c o f : ZFSet.{u}) : Prop :=
  f ⊆ ZFSet.prod (ZFSet.prod d d) c ∧
    ∀ x ∈ d, ∀ y ∈ d, ∀ q ∈ c,
      ZFSet.pair (ZFSet.pair x y) q ∈ f ↔ Step d c (ZFSet.prod d d) o f x y q

theorem vertex_pair (d c o f x y q : ZFSet.{u}) (hx : x ∈ d) (hy : y ∈ d) (hq : q ∈ c) :
    Vertex d c (ZFSet.prod d d) o f (ZFSet.pair (ZFSet.pair x y) q) ↔
      Step d c (ZFSet.prod d d) o f x y q := by
  constructor
  · rintro ⟨a,ha,b,hb,r,hr,v,hv,hve,hze,hs⟩
    obtain ⟨hp,hq'⟩ := ZFSet.pair_inj.mp hze
    have hab := ZFSet.pair_inj.mp (hp.trans hve)
    rcases hab with ⟨rfl,rfl⟩
    simpa only [hq'] using hs
  · intro hs
    exact ⟨x,hx,y,hy,q,hq,_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl,rfl,hs⟩

theorem internal_atomic_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d c o : ZFSet.{u}} (hd : d ∈ M) (hc : c ∈ M) (ho : o ∈ M) :
    ∃ f ∈ M, Graph d c o f := by
  let k := ZFSet.prod d d
  let a := ZFSet.prod k c
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  have ha : a ∈ M := product_mem M hM hP hU hPow hS hk hc
  let e := cons d (cons c (cons k (cons o (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hk
    rcases i with _ | i
    · exact ho
    exact hd
  let φ := AtomicFormula.vertex 2 3 4 5 1 0
  have hφ (f z : ZFSet.{u}) : φ.Eval (cons z (cons f e)) ↔ Vertex d c k o f z :=
    AtomicFormula.eval_vertex 2 3 4 5 1 0 _
  obtain ⟨f,hf,hfa,hfdef⟩ := internal_fixed_point M hM hU hPow hS φ e he a ha (by
    intro f g _ _ hfg z _ h
    exact (hφ g z).mpr (vertex_mono _ _ _ _ _ _ _ hfg ((hφ f z).mp h)))
  refine ⟨f,hf,hfa,fun x hx y hy q hq => ?_⟩
  have hz : ZFSet.pair (ZFSet.pair x y) q ∈ a :=
    ZFSet.mem_prod.mpr ⟨_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,q,hq,rfl⟩
  exact (hfdef _ hz).trans ((hφ f _).trans (vertex_pair d c o f x y q hx hy hq))

end TuringRigidity.AtomicForcing

end OAI
