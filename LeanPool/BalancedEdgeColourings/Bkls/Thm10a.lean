/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6h
public import LeanPool.BalancedEdgeColourings.Bkls.L9e

/-!
# Balister–Kostochka–Li–Schelp 2004, Theorem 10 (part 2): the construction

`strong_of_three`: from a total `k`-colouring in which every colour set is used at most twice and
every colour set used twice contains three fixed colours `a, b, e`, a strong (vertex-distinguishing)
colouring with `k + 1` colours. The edges of colours `a, b, e` form `G'` (`Gs`); Theorem 6 recolours
them with four colours (`a, b, e` and the new colour `k`) so that vertices with the same colours
outside `{a, b, e}` (the key) get different colour sets in `G'`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T10

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

section Defs

variable (c : PEC G (Fin k)) (S0 : Finset (Fin k))

open Classical in
/-- The edges with colours in `S₀`. -/
def Gs : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∃ θ ∈ S0, c.col u v = some θ
  symm := ⟨fun u v ⟨h, θ, hθ, hc⟩ => ⟨h.symm, θ, hθ, by rw [c.col_symm]; exact hc⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

open Classical in
/-- The colours `a, b` and the rest as `0, 1, 2`. -/
def idx (a b : Fin k) (θ : Fin k) : Fin 3 := if θ = a then 0 else if θ = b then 1 else 2

open Classical in
/-- The 3-colouring of `G'`. -/
def c3 (a b : Fin k) : Sym2 V → Fin 3 :=
  Sym2.lift ⟨fun u v => (c.col u v).elim 0 (idx a b), fun u v => by
    change (c.col u v).elim 0 (idx a b) = (c.col v u).elim 0 (idx a b)
    rw [c.col_symm]⟩

end Defs

variable {c : PEC G (Fin k)} {S0 : Finset (Fin k)}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem gs_inc {v : V} {e : Sym2 V} :
    e ∈ (Gs c S0).incidenceFinset v ↔ ∃ u, e = s(v, u) ∧ G.Adj v u ∧ ∃ θ ∈ S0, c.col v u =
        some θ := by
  classical
  rw [C4.mem_inc]
  constructor
  · rintro ⟨he, hv⟩
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨u, rfl, he⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨h, Sym2.mem_mk_left _ _⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem c3_mk {a b : Fin k} {v u : V} {θ : Fin k} (h : c.col v u = some θ) :
    c3 c a b s(v, u) = idx a b θ := by
  classical
  rw [c3, Sym2.lift_mk]
  change (c.col v u).elim 0 (idx a b) = _
  rw [h]; rfl

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem degree_gs (v : V) : (Gs c S0).degree v = #(colSet c v ∩ S0) := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hθ : ∀ u, (Gs c S0).Adj v u → ∃ θ, c.col v u = some θ ∧ θ ∈ S0 := fun u h =>
    let ⟨_, θ, hθ, hc⟩ := h; ⟨θ, hc, hθ⟩
  refine card_bij (fun u hu => (hθ u ((mem_neighborFinset _ _ _).1 hu)).choose) (fun u hu => ?_)
    (fun u hu u' hu' h => ?_) (fun θ hθ' => ?_)
  · obtain ⟨h1, h2⟩ := (hθ u ((mem_neighborFinset _ _ _).1 hu)).choose_spec
    refine mem_inter.2 ⟨?_, h2⟩
    rw [mem_colSet]; intro hf; exact hf u h1
  · have e1 := (hθ u ((mem_neighborFinset _ _ _).1 hu)).choose_spec.1
    have e2 := (hθ u' ((mem_neighborFinset _ _ _).1 hu')).choose_spec.1
    rw [h] at e1
    exact c.col_proper e1 e2
  · obtain ⟨h1, h2⟩ := mem_inter.1 hθ'
    rw [mem_colSet] at h1
    simp only [IsFree, not_forall, not_not] at h1
    obtain ⟨u, hu⟩ := h1
    have hadj : (Gs c S0).Adj v u := ⟨c.col_adj hu, θ, h2, hu⟩
    refine ⟨u, (mem_neighborFinset _ _ _).2 hadj, ?_⟩
    have h' : some θ = some (hθ u hadj).choose := hu.symm.trans (hθ u hadj).choose_spec.1
    exact (Option.some_injective _ h').symm

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem sc_gs (a b : Fin k) (v : V) :
    T6.Sc (Gs c S0) (c3 c a b) v = (colSet c v ∩ S0).image (idx a b) := by
  classical
  ext i
  simp only [T6.Sc, mem_image, gs_inc, mem_inter, mem_colSet]
  constructor
  · rintro ⟨_, ⟨u, rfl, -, θ, hθ, hc⟩, rfl⟩
    exact ⟨θ, ⟨fun hf => hf u hc, hθ⟩, (c3_mk hc).symm⟩
  · rintro ⟨θ, ⟨hf, hθ⟩, rfl⟩
    simp only [IsFree, not_forall, not_not] at hf
    obtain ⟨u, hu⟩ := hf
    exact ⟨s(v, u), ⟨u, rfl, c.col_adj hu, θ, hθ, hu⟩, c3_mk hu⟩
open Classical in
theorem idx_injOn {a b e : Fin k} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e) :
    Set.InjOn (idx a b) ↑({a, b, e} : Finset (Fin k)) := by
  intro x hx y hy h
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  unfold idx at h
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [Ne.symm hab, Ne.symm hae, Ne.symm hbe]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem properOn_c3 {a b e : Fin k} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e) :
    T6.ProperOn (Gs c {a, b, e}) (c3 c a b) := by
  classical
  intro v x y hx hy hne h
  obtain ⟨u, rfl, -, θ, hθ, hc⟩ := gs_inc.1 hx
  obtain ⟨w, rfl, -, θ', hθ', hc'⟩ := gs_inc.1 hy
  rw [c3_mk hc, c3_mk hc'] at h
  have := idx_injOn hab hae hbe hθ hθ' h
  subst this
  exact hne (by rw [c.col_proper hc hc'])
open Classical in
theorem image_inj {f : Fin k → Fin 3} {S A B : Finset (Fin k)} (hf : Set.InjOn f ↑S) (hA : A ⊆ S)
    (hB : B ⊆ S) (h : A.image f = B.image f) : A = B := by
  ext x
  constructor
  · intro hx
    have : f x ∈ B.image f := h ▸ mem_image_of_mem f hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 this
    rw [← hf (hB hy) (hA hx) hxy]; exact hy
  · intro hx
    have : f x ∈ A.image f := h.symm ▸ mem_image_of_mem f hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 this
    rw [← hf (hA hy) (hB hx) hxy]; exact hy

open Classical in
/-- The four new colours. -/
def phi (a b e : Fin k) (i : Fin 4) : Fin (k + 1) :=
  if i = 0 then a.castSucc else if i = 1 then b.castSucc else if i = 2 then e.castSucc else
      Fin.last k

open Classical in
theorem phi_inj {a b e : Fin k} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e) :
    Function.Injective (phi a b e) := by
  intro i j h
  have cs : ∀ x y : Fin k, x.castSucc = y.castSucc ↔ x = y := fun x y => Fin.castSucc_inj
  unfold phi at h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

open Classical in
theorem phi_mem {a b e : Fin k} (i : Fin 4) :
    phi a b e i = Fin.last k ∨ ∃ θ ∈ ({a, b, e} : Finset (Fin k)), phi a b e i = θ.castSucc := by
  unfold phi
  fin_cases i <;> simp

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The strong colouring.** -/
theorem strong_of_three (htot : Total c) (hn2 : ∀ T, cnt c T ≤ 2) {a b e : Fin k}
    (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e)
    (hall : ∀ T, cnt c T = 2 → a ∈ T ∧ b ∈ T ∧ e ∈ T) :
    ∃ c' : PEC G (Fin (k + 1)), Strong c' := by
  classical
  set S0 : Finset (Fin k) := {a, b, e} with hS0
  have hS0c : #S0 = 3 := by rw [hS0, card_insert_of_notMem, card_pair hbe]; simp [hab, hae]
  set key : V → Finset (Fin k) := fun v => colSet c v \ S0
  have hcol : ∀ v, colSet c v = key v ∪ (colSet c v ∩ S0) := fun v => (sdiff_union_inter _ _).symm
  have hcnt2 : ∀ u v, u ≠ v → colSet c u = colSet c v → cnt c (colSet c u) = 2 := by
    intro u v huv h
    have := hn2 (colSet c u)
    have h2 : 2 ≤ cnt c (colSet c u) := by
      unfold cnt
      have hsub : ({u, v} : Finset V) ⊆ univ.filter fun w => colSet c w = colSet c u := by
        intro w hw
        rcases mem_insert.1 hw with rfl | hw
        · exact mem_filter.2 ⟨mem_univ _, rfl⟩
        · rw [mem_singleton.1 hw]; exact mem_filter.2 ⟨mem_univ _, h.symm⟩
      have := card_le_card hsub
      rwa [card_pair huv] at this
    omega
  have hinj := idx_injOn hab hae hbe
  -- Theorem 6
  obtain ⟨col4, hprop4, hsep⟩ := T6.thm6 (G := Gs c S0) (c := c3 c a b) (key := key)
    (properOn_c3 hab hae hbe)
    (fun u v hk huv hd hS => by
      rw [sc_gs, sc_gs] at hS
      have hS' := image_inj hinj inter_subset_right inter_subset_right hS
      have heq : colSet c u = colSet c v := by rw [hcol u, hcol v, hS', hk]
      have h2 := hall _ (hcnt2 u v huv heq)
      rw [degree_gs]
      have : colSet c u ∩ S0 = S0 := inter_eq_right.2 (by
        intro x hx
        simp only [hS0, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h2.1
        · exact h2.2.1
        · exact h2.2.2)
      rw [this, hS0c])
    (fun u v w huv hvw hu hv hw => by
      rw [degree_gs] at hu hv hw
      have hfull : ∀ x, #(colSet c x ∩ S0) = 3 → colSet c x ∩ S0 = S0 := fun x hx =>
        eq_of_subset_of_card_le inter_subset_right (by rw [hx, hS0c])
      have e1 : colSet c u = colSet c v := by
        rw [hcol u, hcol v, hfull u hu, hfull v hv, huv]
      have e2 : colSet c v = colSet c w := by
        rw [hcol v, hcol w, hfull v hv, hfull w hw, hvw]
      by_contra hne
      push Not at hne
      obtain ⟨h1, h2, h3⟩ := hne
      have := hn2 (colSet c u)
      unfold cnt at this
      have hsub : ({u, v, w} : Finset V) ⊆ univ.filter fun x => colSet c x = colSet c u := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact mem_filter.2 ⟨mem_univ _, rfl⟩
        · exact mem_filter.2 ⟨mem_univ _, e1.symm⟩
        · exact mem_filter.2 ⟨mem_univ _, (e1.trans e2).symm⟩
      have h3' := card_le_card hsub
      rw [card_insert_of_notMem (by simp [h1, h3]), card_pair h2] at h3'
      omega)
  -- the new colouring
  let f : V → V → Fin k → Fin (k + 1) := fun u v θ =>
    if θ ∈ S0 then phi a b e (col4 s(u, v)) else θ.castSucc
  have hf_symm : ∀ u v, f u v = f v u := by
    intro u v; funext θ; simp only [f]; rw [Sym2.eq_swap]
  let c' : PEC G (Fin (k + 1)) :=
    ⟨fun u v => (c.col u v).map (f u v), fun u v => by rw [c.col_symm, hf_symm],
      fun {u v γ} h => by
        obtain ⟨θ, hθ, -⟩ := Option.map_eq_some_iff.1 h
        exact c.col_adj hθ,
      fun {u v w γ} h1 h2 => by
        obtain ⟨θ, hθ, e1⟩ := Option.map_eq_some_iff.1 h1
        obtain ⟨θ', hθ', e2⟩ := Option.map_eq_some_iff.1 h2
        have heq : f u v θ = f u w θ' := e1.trans e2.symm
        simp only [f] at heq
        by_cases h1' : θ ∈ S0 <;> by_cases h2' : θ' ∈ S0
        · rw [ite_eq_left h1', ite_eq_left h2'] at heq
          have := phi_inj hab hae hbe heq
          by_contra hvw
          have hx : s(u, v) ∈ (Gs c S0).incidenceFinset u :=
            gs_inc.2 ⟨v, rfl, c.col_adj hθ, θ, h1', hθ⟩
          have hy : s(u, w) ∈ (Gs c S0).incidenceFinset u :=
            gs_inc.2 ⟨w, rfl, c.col_adj hθ', θ', h2', hθ'⟩
          exact hprop4 u _ _ hx hy (fun e => hvw (Sym2.congr_right.1 e)) this
        · exfalso
          rw [ite_eq_left h1', ite_eq_right h2'] at heq
          rcases phi_mem (a := a) (b := b) (e := e) (col4 s(u, v)) with h | ⟨η, hη, h⟩
          · rw [h] at heq; exact Fin.castSucc_ne_last θ' heq.symm
          · rw [h, Fin.castSucc_inj] at heq; subst heq; exact h2' hη
        · exfalso
          rw [ite_eq_right h1', ite_eq_left h2'] at heq
          rcases phi_mem (a := a) (b := b) (e := e) (col4 s(u, w)) with h | ⟨η, hη, h⟩
          · rw [h] at heq; exact Fin.castSucc_ne_last θ heq
          · rw [h, Fin.castSucc_inj] at heq; subst heq; exact h1' hη
        · rw [ite_eq_right h1', ite_eq_right h2', Fin.castSucc_inj] at heq
          subst heq
          exact c.col_proper hθ hθ'⟩
  have htot' : Total c' := by
    intro u v huv
    change (c.col u v).map (f u v) ≠ none
    rw [ne_eq, Option.map_eq_none_iff]
    exact htot u v huv
  -- colour sets of `c'`
  have hmem : ∀ v γ, γ ∈ colSet c' v ↔ ∃ u θ, c.col v u = some θ ∧ f v u θ = γ := by
    intro v γ
    rw [mem_colSet]
    simp only [IsFree, not_forall, not_not]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨θ, hθ, e⟩ := Option.map_eq_some_iff.1 hu
      exact ⟨u, θ, hθ, e⟩
    · rintro ⟨u, θ, hθ, e⟩
      exact ⟨u, Option.map_eq_some_iff.2 ⟨θ, hθ, e⟩⟩
  have hkey : ∀ v θ, θ ∉ S0 → (θ.castSucc ∈ colSet c' v ↔ θ ∈ colSet c v) := by
    intro v θ hθ
    rw [hmem, mem_colSet]
    simp only [IsFree, not_forall, not_not]
    constructor
    · rintro ⟨u, θ', hθ', e'⟩
      simp only [f] at e'
      by_cases h' : θ' ∈ S0
      · exfalso
        rw [ite_eq_left h'] at e'
        rcases phi_mem (a := a) (b := b) (e := e) (col4 s(v, u)) with h | ⟨η, hη, h⟩
        · rw [h] at e'; exact Fin.castSucc_ne_last θ e'.symm
        · rw [h, Fin.castSucc_inj] at e'; subst e'; exact hθ hη
      · rw [ite_eq_right h', Fin.castSucc_inj] at e'
        subst e'
        exact ⟨u, hθ'⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, θ, hu, by simp only [f, ite_eq_right hθ]⟩
  have hsc : ∀ v i, (phi a b e i ∈ colSet c' v ↔ i ∈ T6.Sc (Gs c S0) col4 v) := by
    intro v i
    rw [hmem]
    simp only [T6.Sc, mem_image, gs_inc]
    constructor
    · rintro ⟨u, θ', hθ', e'⟩
      simp only [f] at e'
      by_cases h' : θ' ∈ S0
      · rw [ite_eq_left h'] at e'
        exact ⟨s(v, u), ⟨u, rfl, c.col_adj hθ', θ', h', hθ'⟩, phi_inj hab hae hbe e'⟩
      · exfalso
        rw [ite_eq_right h'] at e'
        rcases phi_mem (a := a) (b := b) (e := e) i with h | ⟨η, hη, h⟩
        · rw [h] at e'; exact Fin.castSucc_ne_last θ' e'
        · rw [h, Fin.castSucc_inj] at e'; subst e'; exact h' hη
    · rintro ⟨_, ⟨u, rfl, -, θ, hθS, hθ⟩, hi⟩
      exact ⟨u, θ, hθ, by simp only [f, ite_eq_left hθS, hi]⟩
  refine ⟨c', htot', fun u v h => ?_⟩
  by_contra huv
  apply hsep u v huv
  · simp only [key]
    ext θ
    simp only [mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hkey v θ h2).1 (h ▸ (hkey u θ h2).2 h1), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hkey u θ h2).1 (h.symm ▸ (hkey v θ h2).2 h1), h2⟩
  · ext i
    rw [← hsc, ← hsc, h]
end Bkls.T10

end LeanPool.BalancedEdgeColourings
