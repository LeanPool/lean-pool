/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalProductBijection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Internal Product Bijection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalProductBijection
open TransitiveNameModel BoundedSetTheory

/-- The product relation applying `f` to the first coordinate and fixing the coordinate in
`W`. -/
noncomputable def productGraph (A B W f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (ZFSet.prod A W) (ZFSet.prod B W)).sep (fun z =>
    ∃ u ∈ ZFSet.prod A W, ∃ v ∈ ZFSet.prod B W, z = ZFSet.pair u v ∧
      ∃ x ∈ A, ∃ y ∈ B, ∃ n ∈ W, u = ZFSet.pair x n ∧ v = ZFSet.pair y n ∧ ZFSet.pair x y ∈ f)

theorem pair_productGraph (A B W f u v : ZFSet.{0}) :
    ZFSet.pair u v ∈ productGraph A B W f ↔
      ∃ x ∈ A, ∃ y ∈ B, ∃ n ∈ W, u = ZFSet.pair x n ∧ v = ZFSet.pair y n ∧ ZFSet.pair x y ∈ f := by
  simp only [productGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,u',_,v',_,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact h
  · intro h
    obtain ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩ := h
    have hu := ZFSet.pair_mem_prod.mpr ⟨hx,hn⟩
    have hv := ZFSet.pair_mem_prod.mpr ⟨hy,hn⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hu,hv⟩,_,hu,_,hv,rfl,x,hx,y,hy,n,hn,rfl,rfl,hxy⟩

theorem productGraph_mem (M A B W f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hW : W ∈ M) (hf : f ∈ M) : productGraph A B W f ∈ M := by
  have hAW := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hA hW
  have hBW := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hB hW
  let e := cons (ZFSet.prod A W) (cons (ZFSet.prod B W) (cons A (cons B (cons W (fun _ => f)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hAW
    · exact hBW
    · exact hA
    · exact hB
    · exact hW
    · exact hf
  simpa only [productGraph,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.existsMem 7 (.existsMem 9 (.conj (.orderedPair 4 2 0)
          (.conj (.orderedPair 3 1 0) (.pairMem 2 1 11))))))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hAW hBW)

theorem productGraph_function (A B W f : ZFSet.{0}) (hf : FunctionGraph A B f) :
    FunctionGraph (ZFSet.prod A W) (ZFSet.prod B W) (productGraph A B W f) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro u hu
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hu
    obtain ⟨y,hy,hxy,_⟩ := hf.2 x hx
    refine ⟨ZFSet.pair y n,ZFSet.pair_mem_prod.mpr ⟨hy,hn⟩,
      (pair_productGraph A B W f _ _).mpr ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩,?_⟩
    intro v _ hv
    obtain ⟨x',_,y',_,n',_,he,rfl,hxy'⟩ := (pair_productGraph A B W f _ v).mp hv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    rw [hf.functional hx hxy' hxy]

theorem productGraph_injective (A B W f : ZFSet.{0})
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') :
    ∀ u ∈ ZFSet.prod A W, ∀ u' ∈ ZFSet.prod A W, ∀ v ∈ ZFSet.prod B W,
      ZFSet.pair u v ∈ productGraph A B W f → ZFSet.pair u' v ∈ productGraph A B W f → u = u' := by
  intro u _ u' _ v _ huv hu'v
  obtain ⟨x,hx,y,hy,n,_,rfl,rfl,hxy⟩ := (pair_productGraph A B W f u v).mp huv
  obtain ⟨x',hx',y',_,n',_,rfl,he,hx'y⟩ := (pair_productGraph A B W f u' _).mp hu'v
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  rw [hi x hx x' hx' y hy hxy hx'y]

theorem productGraph_onto (A B W f : ZFSet.{0})
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∀ v ∈ ZFSet.prod B W, ∃ u ∈ ZFSet.prod A W, ZFSet.pair u v ∈ productGraph A B W f := by
  intro v hv
  obtain ⟨y,hy,n,hn,rfl⟩ := ZFSet.mem_prod.mp hv
  obtain ⟨x,hx,hxy⟩ := hs y hy
  exact ⟨ZFSet.pair x n,ZFSet.pair_mem_prod.mpr ⟨hx,hn⟩,
    (pair_productGraph A B W f _ _).mpr ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩⟩

end TuringRigidity.InternalProductBijection

end OAI
