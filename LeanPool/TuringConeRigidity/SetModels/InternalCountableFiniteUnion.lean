/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableFiniteUnion.lean.
Also incorporates the shared flattening proof from the upstream
OAI/Computability/DegreeRigidity/SetModels/InternalCountableUnion.lean
under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFiniteEnumeration
public import LeanPool.TuringConeRigidity.SetModels.CountableSetReal
public import LeanPool.TuringConeRigidity.SetModels.InternalFunctionOrbit

/-!
# Internal Countable Finite Union
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableFiniteUnion
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteEnumeration

/-- A graph entry at `k`, using `d` as the fallback when no value in `U` is recorded there. -/
def Entry (U g d k x : ZFSet.{0}) : Prop := ZFSet.pair k x ∈ g ∨
  (x = d ∧ ∀ y ∈ U, ¬ ZFSet.pair k y ∈ g)

/-- Bounded formula expressing graph lookup with a designated fallback value. -/
def entryFormula (U g d k x : ℕ) : Formula := .disj (.pairMem k x g)
  (.conj (.equal x d) (.allMem U (.neg (.pairMem (k+1) 0 (g+1)))))

theorem entryFormula_spec (U g d k x : ℕ) (e : ℕ → ZFSet.{0}) :
    (entryFormula U g d k x).Eval e ↔ Entry (e U) (e g) (e d) (e k) (e x) := by
  simp only [entryFormula,Entry,Formula.eval_disj,Formula.eval_allMem,
    Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]

theorem entry_exists_unique (U g d k : ZFSet.{0}) (hg : InternalCollapse.Prefix U g)
    (hd : d ∈ U) : ∃ x ∈ U, Entry U g d k x ∧ ∀ y ∈ U, Entry U g d k y → y = x := by
  classical
  by_cases h : ∃ x ∈ U, ZFSet.pair k x ∈ g
  · obtain ⟨x,hx,hkx⟩ := h
    obtain ⟨n,hg⟩ := hg
    have hk : k ∈ natSet n := by
      obtain ⟨k',hk,x',_,he⟩ := hg.1 _ hkx
      exact (ZFSet.pair_inj.mp he).1 ▸ hk
    refine ⟨x,hx,Or.inl hkx,?_⟩
    intro y _ hy
    rcases hy with hy|⟨_,hy⟩
    · exact hg.functional hk hy hkx
    · exact False.elim (hy x hx hkx)
  · exact ⟨d,hd,Or.inr ⟨rfl,fun y hy hky => h ⟨y,hy,hky⟩⟩,
      fun y hy he => he.elim (fun hky => False.elim (h ⟨y,hy,hky⟩)) And.left⟩

/-- Bounded formula flattening a coded sequence of enumerated finite sets through
natural-number pairing. -/
def flattenFormula (ω Q S C B T U d k x : ℕ) : Formula :=
  .existsMem ω (.existsMem (ω+1) (.conj (Formula.naturalPair (ω+2) (Q+2) 1 0 (k+2))
    (.existsMem (S+2) (.conj (.pairMem 2 0 (B+3))
      (.existsMem (C+3) (.conj (.pairMem 1 0 (T+4))
        (entryFormula (U+4) 0 (d+4) 2 (x+4))))))))

theorem flattenFormula_spec (ω Q S C B T U d k x : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ l, finiteNaturalGraph f l ∈ e Q) (N K : ℕ)
    (hk : e k = natSet (Nat.pair N K)) :
    (flattenFormula ω Q S C B T U d k x).Eval e ↔
      ∃ E ∈ e S, ZFSet.pair (natSet N) E ∈ e B ∧
        ∃ g ∈ e C, ZFSet.pair E g ∈ e T ∧ Entry (e U) g (e d) (natSet K) (e x) := by
  simp only [flattenFormula,Formula.Eval,Formula.eval_pairMem,entryFormula_spec,cons_zero,cons_succ]
  rw [hω]
  exact Formula.naturalPair_exists_payload ω Q k e hω hQ N K hk _

/-- Flatten a coded cover using selected graphs with unique fallback entries and
the specified ranges. Selected graphs may be finite prefixes. -/
theorem internally_countable_union_of_selector (M U S C T : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hS : S ∈ M) (hCM : C ∈ M) (hTM : T ∈ M)
    (hTfun : FunctionGraph S C T)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ S)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (d : ZFSet.{0}) (hd : d ∈ U)
    (hlookup : ∀ H ∈ S, ∀ g ∈ C, ZFSet.pair H g ∈ T →
      ∀ k ∈ ZFSet.omega, ∃ x ∈ U, Entry U g d k x ∧
        ∀ y ∈ U, Entry U g d k y → y = x)
    (hranges : ∀ H ∈ S, ∀ g, ZFSet.pair H g ∈ T → Ranges U H g) :
    InternallyCountable M U := by
  classical
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  let B := orbitGraph E
  have hchoice (n k : ℕ) : ∃ x ∈ U, ∃ g ∈ C,
      ZFSet.pair (E n) g ∈ T ∧ Entry U g d (natSet k) x ∧
        ∀ y ∈ U, Entry U g d (natSet k) y → y = x := by
    obtain ⟨g,hg,hEg,_⟩ := hTfun.2 _ (hE n)
    obtain ⟨x,hx,he,hu⟩ := hlookup (E n) (hE n) g hg hEg
      (natSet k) ((mem_omega _).mpr ⟨k,rfl⟩)
    exact ⟨x,hx,g,hg,hEg,he,hu⟩
  choose v hv g hg hEg hentry huniq using hchoice
  let f : ℕ → ZFSet.{0} := fun i => v (Nat.unpair i).1 (Nat.unpair i).2
  let e := cons ZFSet.omega (cons Q (cons S (cons C (cons B (cons T (cons U (fun _ => d)))))))
  let φ : Formula := .existsMem 1 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (flattenFormula 3 4 5 6 7 8 9 10 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|i
    · exact hω
    · exact hQM
    · exact hS
    · exact hCM
    · exact hB
    · exact hTM
    · exact hU
    · exact hM U hU d hd
  have flat (N K : ℕ) (x : ZFSet.{0}) (hx : x ∈ U) (z : ZFSet.{0}) :
      (flattenFormula 3 4 5 6 7 8 9 10 1 0).Eval
        (cons x (cons (natSet (Nat.pair N K)) (cons z e))) ↔ x = v N K := by
    rw [flattenFormula_spec 3 4 5 6 7 8 9 10 1 0 _ rfl hQ N K rfl]
    change (∃ H ∈ S, ZFSet.pair (natSet N) H ∈ B ∧
      ∃ t ∈ C, ZFSet.pair H t ∈ T ∧ Entry U t d (natSet K) x) ↔ _
    constructor
    · rintro ⟨H,_,hNH,t,_,hHt,ht⟩
      have hH := (orbitGraph_pair E N H).mp hNH
      rw [hH] at hHt
      have ht' := hTfun.functional (hE N) hHt (hEg N K)
      exact huniq N K x hx (ht' ▸ ht)
    · rintro rfl
      exact ⟨E N,hE N,(orbitGraph_pair E N _).mpr rfl,g N K,hg N K,hEg N K,hentry N K⟩
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph f := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨i,hi,x,hx,hz,hflat⟩
      obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
      have hn : natSet i = natSet (Nat.pair (Nat.unpair i).1 (Nat.unpair i).2) := by
        rw [Nat.pair_unpair]
      have hflat' := hflat
      rw [hn] at hflat'
      have hx' := (flat (Nat.unpair i).1 (Nat.unpair i).2 x hx z).mp hflat'
      exact (mem_orbitGraph f z).mpr ⟨i,by rw [hz,hx']⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_orbitGraph f z).mp hz
      refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,f i,hv _ _,rfl,?_⟩
      have hh := (flat (Nat.unpair i).1 (Nat.unpair i).2 (f i) (hv _ _)
        (ZFSet.pair (natSet i) (f i))).mpr rfl
      simpa only [Nat.pair_unpair] using hh
  have hG : orbitGraph f ∈ M := by
    have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hU)
    have heq : (ZFSet.prod ZFSet.omega U).sep (fun z => φ.Eval (cons z e)) = orbitGraph f := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,hφ]
      exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function U f (fun _ => hv _
        _)).1 z hz),hz⟩⟩
    exact heq ▸ hh
  refine ⟨orbitGraph f,hG,orbitGraph_function U f (fun _ => hv _ _),?_⟩
  intro p hp
  obtain ⟨n,hpE⟩ := hcover p hp
  have hr := hranges (E n) (hE n) (g n 0) (hEg n 0)
  obtain ⟨k,hk,hkp⟩ := (hr.2 p hp).mp hpE
  obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
  have heq := hTfun.functional (hE n) (hEg n 0) (hEg n k)
  have hpv := huniq n k p hp (Or.inl (heq ▸ hkp))
  refine ⟨natSet (Nat.pair n k),(mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,?_⟩
  apply (orbitGraph_pair f _ p).mpr
  simpa only [f,Nat.unpair_pair] using hpv

theorem internally_countable_union (M U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ finiteSubsets U)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (hne : ∃ p, p ∈ U) : InternallyCountable M U := by
  obtain ⟨d,hd⟩ := hne
  obtain ⟨C,hCM,hC,T,hTM,hTfun,hTrange⟩ := internal_enumeration_selector M U hM hT hU
  apply internally_countable_union_of_selector M U (finiteSubsets U) C T
    hM hT hU (finiteSubsets_mem M U hM hT hU) hCM hTM hTfun E hE hB hcover d hd
    ?_ hTrange
  intro _ _ g hg _ k _
  exact entry_exists_unique U g d k ((hC g).mp hg) hd

end TuringRigidity.InternalCountableFiniteUnion

end OAI
