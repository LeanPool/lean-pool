/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/TaggedProductConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableMap
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableProduct

/-!
# Tagged Product Conditions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TaggedProductConditions
open TransitiveNameModel BoundedSetTheory
attribute [local instance] InternalCollapse.order

/-- Code a pair of sets by tagging the first with zero and the second with one. -/
noncomputable def code (p s : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.prod {natSet 0} p ∪ ZFSet.prod {natSet 1} s

theorem mem_code (p s z : ZFSet.{0}) : z ∈ code p s ↔
    (∃ x ∈ p, z = ZFSet.pair (natSet 0) x) ∨
    (∃ x ∈ s, z = ZFSet.pair (natSet 1) x) := by
  simp only [code,ZFSet.mem_union,ZFSet.mem_prod,ZFSet.mem_singleton]
  aesop

theorem left_mem (p s x : ZFSet.{0}) :
    ZFSet.pair (natSet 0) x ∈ code p s ↔ x ∈ p := by
  rw [mem_code]
  simp only [ZFSet.pair_inj,natSet_injective.eq_iff]
  simp

theorem right_mem (p s x : ZFSet.{0}) :
    ZFSet.pair (natSet 1) x ∈ code p s ↔ x ∈ s := by
  rw [mem_code]
  simp only [ZFSet.pair_inj,natSet_injective.eq_iff]
  simp

theorem code_subset (p s p' s' : ZFSet.{0}) :
    code p s ⊆ code p' s' ↔ p ⊆ p' ∧ s ⊆ s' := by
  constructor
  · intro h
    exact ⟨fun x hx => (left_mem p' s' x).mp (h ((left_mem p s x).mpr hx)),
      fun x hx => (right_mem p' s' x).mp (h ((right_mem p s x).mpr hx))⟩
  · rintro ⟨hp,hs⟩ z hz
    rcases (mem_code p s z).mp hz with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
    · exact (left_mem p' s' x).mpr (hp hx)
    · exact (right_mem p' s' x).mpr (hs hx)

theorem code_injective (p s p' s' : ZFSet.{0}) :
    code p s = code p' s' ↔ p = p' ∧ s = s' := by
  constructor
  · intro h
    have h₁ := (code_subset p s p' s').mp (fun _ hx => h ▸ hx)
    have h₂ := (code_subset p' s' p s).mp (fun _ hx => h.symm ▸ hx)
    exact ⟨ZFSet.ext (fun x => ⟨fun hx => h₁.1 hx,fun hx => h₂.1 hx⟩),
      ZFSet.ext (fun x => ⟨fun hx => h₁.2 hx,fun hx => h₂.2 hx⟩)⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem code_mem (M p s : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hp : p ∈ M) (hs : s ∈ M) : code p s ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hT.pairing hT.union
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 0)) hp)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 1)) hs)

/-- Bounded formula characterizing the tagged code of a pair of sets. -/
def codeFormula (p s z z0 z1 : ℕ) : Formula :=
  .conj (.allMem z (.disj
    (.existsMem (p+1) (.orderedPair 1 (z0+2) 0))
    (.existsMem (s+1) (.orderedPair 1 (z1+2) 0))))
    (.conj (.allMem p (.pairMem (z0+1) 0 (z+1)))
      (.allMem s (.pairMem (z1+1) 0 (z+1))))

theorem codeFormula_spec (p s z z0 z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) :
    (codeFormula p s z z0 z1).Eval e ↔ e z = code (e p) (e s) := by
  simp only [codeFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,h0,h1]
  constructor
  · rintro ⟨ha,hb,hc⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => (mem_code _ _ _).mpr (ha x hx),fun hx =>
      ((mem_code _ _ _).mp hx).elim (fun ⟨y,hy,he⟩ => he ▸ hb y hy)
        (fun ⟨y,hy,he⟩ => he ▸ hc y hy)⟩
  · intro h; rw [h]
    exact ⟨fun x hx => (mem_code _ _ _).mp hx,
      fun x hx => (left_mem _ _ _).mpr hx,fun x hx => (right_mem _ _ _).mpr hx⟩

/-- A common superset of the tagged product codes formed from members of `a` and `b`. -/
noncomputable def bound (a b : ZFSet.{0}) : ZFSet.{0} :=
  code (ZFSet.sUnion a) (ZFSet.sUnion b)

theorem code_bounded (a b p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
    code p s ⊆ bound a b :=
  (code_subset _ _ _ _).mpr ⟨fun _ hx => ZFSet.mem_sUnion.mpr ⟨p,hp,hx⟩,
    fun _ hx => ZFSet.mem_sUnion.mpr ⟨s,hs,hx⟩⟩

theorem internal_product (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      ∃ g ∈ M, FunctionGraph (ZFSet.prod a b) c g ∧
        (∀ p ∈ a, ∀ s ∈ b, ∀ z, ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s) ∧
        (∀ z ∈ c, ∃ x ∈ ZFSet.prod a b, ZFSet.pair x z ∈ g) := by
  have hbound := code_mem M _ _ hM hT (union_mem M hM hT.union ha) (union_mem M hM hT.union hb)
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hbound
  have hcode (p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) : code p s ∈ Q :=
    (hQdef _).mpr ⟨code_mem M p s hM hT (hM a ha p hp) (hM b hb s hs),code_bounded a b p s hp hs⟩
  let e := cons a (cons b (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact ha
    · exact hb
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let c := Q.sep (fun z => ∃ p ∈ a, ∃ s ∈ b, z = code p s)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  have hc : c ∈ M := by
    simpa only [c,Formula.Eval,hsepCode,
      cons_zero,cons_succ,e] using
      sep_mem M hM hT.separation.finitePrefix.bounded
        (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hQ
  have hcs (z : ZFSet.{0}) : z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s := by
    change (z ∈ Q.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,s,hs,hz⟩ => ⟨hz ▸ hcode p s hp hs,h⟩⟩
  let v := cons (ZFSet.prod a b) (cons c e)
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded ha hb
  have hv : ∀ i, v i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hprod
    · exact hc
    · exact he i
  have hgraphCode (left right value point entry : ZFSet.{0}) :
      (codeFormula 1 0 2 9 10).Eval
        (cons right (cons left (cons value (cons point (cons entry v))))) ↔
          value = code left right :=
    codeFormula_spec 1 0 2 9 10 _ rfl rfl
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0) (codeFormula 1 0 2 9 10))))))
  let g := (ZFSet.prod (ZFSet.prod a b) c).sep (fun z => φ.Eval (cons z v))
  have hg : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hprod hc)
  have hgs (p s z : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
      ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s := by
    simp only [g,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      hgraphCode,cons_zero,cons_succ,v,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,p',_,s',_,hx,hy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hx
      exact hy
    · intro hz
      have hzc := (hcs z).mpr ⟨p,hp,s,hs,hz⟩
      have hps := ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hps,hzc⟩,_,hps,z,hzc,rfl,p,hp,s,hs,rfl,hz⟩
  refine ⟨c,hc,hcs,g,hg,⟨?_,?_⟩,(fun p hp s hs z => hgs p s z hp hs),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨p,hp,s,hs,rfl⟩ := ZFSet.mem_prod.mp hx
    exact ⟨code p s,(hcs _).mpr ⟨p,hp,s,hs,rfl⟩,(hgs p s _ hp hs).mpr rfl,
      fun y _ hy => (hgs p s y hp hs).mp hy⟩
  · intro z hz
    obtain ⟨p,hp,s,hs,hz⟩ := (hcs z).mp hz
    exact ⟨ZFSet.pair p s,ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩,(hgs p s z hp hs).mpr hz⟩

theorem product_countable (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hca : InternallyCountable M a) (hcb : InternallyCountable M b) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c := by
  obtain ⟨c,hc,hcs,g,hg,hgf,_,hgo⟩ := internal_product M a b hM hT ha hb
  refine ⟨c,hc,hcs,InternalCollapse.orderSet_mem M hM hT hc,?_⟩
  exact InternalCountableMap.countable_of_surjection M _ c g hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)
    hc hg hgf hgo (InternalCountableProduct.product_countable M a b hM hT ha hb hca hcb)

end TuringRigidity.TaggedProductConditions

end OAI
