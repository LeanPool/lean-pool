/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRelationSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableFiniteUnion

/-!
# Internal Relation Selection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRelationSelection
open TransitiveNameModel BoundedSetTheory

noncomputable def fiber (Y R x : ZFSet.{0}) : ZFSet.{0} :=
  Y.sep (fun y => ZFSet.pair x y ∈ R)

def fiberFormula (Y R x a : ℕ) : Formula := .conj (.subset a Y)
  (.allMem Y (.iff (.member 0 (a+1)) (.pairMem (x+1) 0 (R+1))))

theorem fiberFormula_spec (Y R x a : ℕ) (e : ℕ → ZFSet.{0}) :
    (fiberFormula Y R x a).Eval e ↔ e a = fiber (e Y) (e R) (e x) := by
  simp only [fiberFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,Formula.Eval,cons_zero,cons_succ]
  constructor
  · rintro ⟨hs,h⟩
    apply ZFSet.ext; intro y
    exact ⟨fun hy => ZFSet.mem_sep.mpr ⟨hs hy,(h y (hs hy)).mp hy⟩,
      fun hy => (h y (ZFSet.mem_sep.mp hy).1).mpr (ZFSet.mem_sep.mp hy).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hy => (ZFSet.mem_sep.mp hy).1,
      fun y hy => ZFSet.mem_sep.trans (and_iff_right hy)⟩

theorem fiber_mem (M Y R x : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hY : Y ∈ M) (hR : R ∈ M) (hx : x ∈ M) : fiber Y R x ∈ M := by
  let e := cons x (fun _ => R)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hx
    · exact hR
  simpa only [fiber,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.pairMem 1 0 2) e he hY

theorem select_relation (M X Y R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hY : Y ∈ M) (hR : R ∈ M)
    (htotal : ∀ x ∈ X, ∃ y ∈ Y, ZFSet.pair x y ∈ R) :
    ∃ T ∈ M, FunctionGraph X Y T ∧ T ⊆ R := by
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet
    hT.separation.finitePrefix.bounded hT.choice hY
  have hf (x : ZFSet.{0}) (hx : x ∈ X) : fiber Y R x ∈ q := by
    apply (hqdef _).mpr
    obtain ⟨y,hy,hxy⟩ := htotal x hx
    exact ⟨fiber_mem M Y R x hM hT hY hR (hM X hX x hx),
      fun _ h => (ZFSet.mem_sep.mp h).1,y,ZFSet.mem_sep.mpr ⟨hy,hxy⟩⟩
  let e := cons X (cons Y (cons R (cons q (fun _ => s))))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 6 (.conj (fiberFormula 5 6 2 0) (.pairMem 0 1 8)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hX
    · exact hY
    · exact hR
    · exact hq
    · exact hsM
  let T := (ZFSet.prod X Y).sep (fun z => φ.Eval (cons z e))
  have hTM : T ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hX hY)
  have hmem (z : ZFSet.{0}) : z ∈ T ↔ ∃ x ∈ X, ∃ y ∈ Y,
      z = ZFSet.pair x y ∧ ZFSet.pair (fiber Y R x) y ∈ s := by
    simp only [T,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_pairMem,fiberFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,hy,hz,a,_,ha,hay⟩
      exact ⟨x,hx,y,hy,hz,ha ▸ hay⟩
    · rintro ⟨x,hx,y,hy,rfl,hay⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,fiber Y R x,hf x hx,rfl,hay⟩
  refine ⟨T,hTM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hs.2 _ (hf x hx)
    have hyY := (ZFSet.mem_sep.mp hy).1
    refine ⟨y,hyY,(hmem _).mpr ⟨x,hx,y,hyY,rfl,hxy⟩,?_⟩
    intro y' _ hxy'
    obtain ⟨x',_,y'',_,hp,hfy⟩ := (hmem _).mp hxy'
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hs.functional hfy hxy
  · intro z hz
    obtain ⟨x,_,y,_,rfl,hfy⟩ := (hmem z).mp hz
    exact (ZFSet.mem_sep.mp (InternalWellOrder.choice_value_mem hs hfy)).2

theorem map_sequence (M X Y T : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hY : Y ∈ M) (hTM : T ∈ M) (hf : FunctionGraph X Y T)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ X) (hB : orbitGraph E ∈ M) :
    ∃ F : ℕ → ZFSet.{0}, orbitGraph F ∈ M ∧
      ∀ n, F n ∈ Y ∧ ZFSet.pair (E n) (F n) ∈ T := by
  choose F hF hp hu using fun n => hf.2 (E n) (hE n)
  let B := orbitGraph E
  let e := cons ZFSet.omega (cons X (cons Y (cons B (fun _ => T))))
  let φ : Formula := .existsMem 1 (.existsMem 4 (.conj (.orderedPair 2 1 0)
    (.existsMem 4 (.conj (.pairMem 2 0 7) (.pairMem 0 1 8)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact sourceT_omega_mem M hM hT
    · exact hX
    · exact hY
    · exact hB
    · exact hTM
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph F := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,y,hy,hz,x,_,hnx,hxy⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hx := (orbitGraph_pair E n x).mp hnx
      have hy' := hf.functional (hE n) (hx ▸ hxy) (hp n)
      exact (mem_orbitGraph F z).mpr ⟨n,by rw [hz,hy']⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph F z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,F n,hF n,rfl,E n,hE n,
        (orbitGraph_pair E n _).mpr rfl,hp n⟩
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (sourceT_omega_mem M hM hT) hY)
  have heq : (ZFSet.prod ZFSet.omega Y).sep (fun z => φ.Eval (cons z e)) = orbitGraph F := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function Y F hF).1 z hz),hz⟩⟩
  exact ⟨F,heq ▸ hh,fun n => ⟨hF n,hp n⟩⟩

end TuringRigidity.InternalRelationSelection

end OAI
