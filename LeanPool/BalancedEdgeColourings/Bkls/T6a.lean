/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cor4

/-!
# Theorem 6, part (a): the `{0, 1}`-subgraph, bad hexagons and the matching

`G` is properly edge-coloured by `c` with colours `0, 1, 2` (the article's `1, 2, 4`); `key u =
key v`
is the relation `B`. `G01` keeps the edges of colours `0, 1`; it has maximum degree two. A *bad
hexagon* is a `6`-cycle of `G01` whose opposite vertices have the same key and the same degree.
Outside bad hexagons, the vertices with the same key, the same degree and the same `2`-status
(whether colour `2` is present) that could end up with equal colour sets come in pairs
(`partner_unique`), which gives the matching for Corollary 4.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The colour set at `v`. -/
noncomputable def Sc {n : ℕ} (c : Sym2 V → Fin n) (v : V) : Finset (Fin n) :=
  (G.incidenceFinset v).image c

/-- `c` is proper on `G`. -/
def ProperOn {n : ℕ} (c : Sym2 V → Fin n) : Prop :=
  ∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → c e ≠ c e'

/-- The edges of colours `0, 1`. -/
def G01 (c : Sym2 V → Fin 3) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c s(u, v) ≠ 2
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

variable {G}

omit [DecidableEq V] in
theorem card_Sc {n : ℕ} {c : Sym2 V → Fin n} (hc : ProperOn G c) (v : V) :
    #(Sc G c v) = G.degree v := by
  classical
  unfold Sc
  rw [card_image_of_injOn, C4.card_inc]
  intro a ha b hb e
  by_contra hne
  exact hc v a b ha hb hne e

/-- Three colour sets of the same size and the same `2`-status, of size at most two, are not
pairwise distinct. -/
theorem pigeon3 : ∀ A B C : Finset (Fin 3), A.card = B.card → B.card = C.card → A.card ≤ 2 →
    (2 ∈ A ↔ 2 ∈ B) → (2 ∈ B ↔ 2 ∈ C) → A = B ∨ B = C ∨ A = C := by
  decide

variable {c : Sym2 V → Fin 3}

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem G01_adj {u v : V} : (G01 G c).Adj u v ↔ G.Adj u v ∧ c s(u, v) ≠ 2 := by
  classical
  exact Iff.rfl

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem G01_le : G01 G c ≤ G := by
  classical
  exact fun _ _ h => h.1

omit [DecidableEq V] in
/-- **`G01` has maximum degree two.** -/
theorem degree_G01_le [DecidableRel (G01 G c).Adj] (hc : ProperOn G c) (v : V) :
    (G01 G c).degree v ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsub : ((G01 G c).neighborFinset v).image (fun u => c s(v, u)) ⊆ {0, 1} := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hx
    have h := ((mem_neighborFinset _ _ _).1 hu).2
    have : c s(v, u) = 0 ∨ c s(v, u) = 1 := by omega
    rcases this with h' | h' <;> simp [h']
  have hinj : Set.InjOn (fun u => c s(v, u)) ((G01 G c).neighborFinset v : Set V) := by
    intro a ha b hb e
    by_contra hne
    have ha' := ((mem_neighborFinset _ _ _).1 ha).1
    have hb' := ((mem_neighborFinset _ _ _).1 hb).1
    refine hc v s(v, a) s(v, b) ((C4.mem_inc G).2 ⟨ha', Sym2.mem_mk_left _ _⟩)
      ((C4.mem_inc G).2 ⟨hb', Sym2.mem_mk_left _ _⟩) (fun h => hne ?_) e
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · rw [h2] at ha'; exact absurd ha' (G.loopless.irrefl v)
  have := card_le_card hsub
  rw [card_image_of_injOn hinj] at this
  have h2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  omega
variable (G c) in
/-- A bad hexagon. -/
def BadHex {κ : Type*} (key : V → κ) (w : ZMod 6 → V) : Prop :=
  Function.Injective w ∧ (∀ k, (G01 G c).Adj (w k) (w (k + 1))) ∧
    ∀ k, key (w k) = key (w (k + 3)) ∧ G.degree (w k) = G.degree (w (k + 3))

variable (G c) in
/-- `v` lies on a bad hexagon. -/
def IsHex {κ : Type*} (key : V → κ) (v : V) : Prop := ∃ w, BadHex G c key w ∧ ∃ k, w k = v

omit [DecidableEq V] in
/-- The `G01`-neighbours of a hexagon vertex are its two hexagon neighbours. -/
theorem hex_nbr (hc : ProperOn G c) {κ : Type*} {key : V → κ}
    {w : ZMod 6 → V} (hw : BadHex G c key w) (k : ZMod 6) {x : V} (hx : (G01 G c).Adj (w k) x) :
    x = w (k - 1) ∨ x = w (k + 1) := by
  classical
  have h1 : (G01 G c).Adj (w k) (w (k - 1)) := by
    have := hw.2.1 (k - 1); rw [sub_add_cancel] at this; exact this.symm
  have h2 : (G01 G c).Adj (w k) (w (k + 1)) := hw.2.1 k
  have hne : w (k - 1) ≠ w (k + 1) := fun e => by
    have := hw.1 e
    have h' : ∀ a : ZMod 6, a - 1 ≠ a + 1 := by decide
    exact h' k this
  by_contra hc'
  push Not at hc'
  have hsub : ({w (k - 1), w (k + 1), x} : Finset V) ⊆ (G01 G c).neighborFinset (w k) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rw [mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hx
  have := card_le_card hsub
  rw [card_neighborFinset_eq_degree, card_insert_of_notMem (by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hne, hc'.1.symm⟩),
    card_insert_of_notMem (by simp only [mem_singleton]; exact hc'.2.symm), card_singleton] at this
  have := degree_G01_le hc (w k)
  omega
end Bkls.T6

end LeanPool.BalancedEdgeColourings
