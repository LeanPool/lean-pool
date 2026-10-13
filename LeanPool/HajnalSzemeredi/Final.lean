/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Teorema de Hajnal–Szemerédi

* `hajnalSzemeredi_exact`: si `|V| = s (r + 1)` y `Δ(G) ≤ r`, hay una `(r+1)`-coloración propia
  cuyas clases tienen todas exactamente `s` vértices (forma del problema de Erdős #914).
* `hajnalSzemeredi`: si `Δ(G) ≤ r`, hay una `(r+1)`-coloración propia equitativa (los tamaños de
  dos clases cualesquiera difieren en a lo más uno).

La forma general se reduce a la exacta agregando un `K_p` disjunto (`p < r + 1`) para que el
número de vértices sea divisible por `r + 1`; cada clase contiene a lo más un vértice agregado.
-/

@[expose] public section

noncomputable section

open Finset

namespace HajnalSzemeredi

variable {V : Type*} [Fintype V]

open Classical in
/-- Pasar del grado de Mathlib a `DegLe` sobre `univ`. -/
lemma degLe_univ (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (h : ∀ v, G.degree v ≤ r) :
    DegLe G univ r := by
  intro v _
  refine le_trans (card_le_card fun w hw => ?_) ((G.card_neighborFinset_eq_degree v).le.trans (h v))
  rw [SimpleGraph.mem_neighborFinset]
  exact (mem_nbr.mp hw).2

open Classical in
/-- Forma exacta. -/
theorem hajnalSzemeredi_exact (G : SimpleGraph V) [DecidableRel G.Adj] (r s : ℕ)
    (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i, (univ.filter fun v => C v = i).card = s := by
  obtain ⟨c, hc⟩ := core _ G univ (range (r + 1)) r s rfl (card_range _)
    (by rw [card_univ, hcard]) (degLe_univ G h)
  have hlt : ∀ v, c v < r + 1 := fun v => mem_range.mp (hc.into v (mem_univ v))
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨c v, hlt v⟩) fun {u v} huv heq =>
    hc.proper u (mem_univ u) v (mem_univ v) huv (congrArg Fin.val heq), fun i => ?_⟩
  refine Eq.trans ?_ (hc.card i (mem_range.mpr i.isLt))
  congr 1

open Classical in
/-- Adyacencia del grafo con un `K_p` disjunto agregado. -/
def padAdj (G : SimpleGraph V) (p : ℕ) : V ⊕ Fin p → V ⊕ Fin p → Prop
  | .inl u, .inl v => G.Adj u v
  | .inr i, .inr j => i ≠ j
  | _, _ => False

open Classical in
/-- `G ⊔ K_p` (unión disjunta). -/
def pad (G : SimpleGraph V) (p : ℕ) : SimpleGraph (V ⊕ Fin p) where
  Adj := padAdj G p
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [padAdj] at h ⊢
    · exact h.symm
    · exact Ne.symm h⟩
  loopless := ⟨fun a h => by
    cases a <;> simp only [padAdj] at h
    · exact G.loopless.irrefl _ h
    · exact h rfl⟩

open Classical in
lemma card_classes_split {W : Type*} [DecidableEq W] {p : ℕ} (f : V ⊕ Fin p → W) (i : W) :
    (univ.filter fun w => f w = i).card =
      (univ.filter fun v => f (.inl v) = i).card + (univ.filter fun j => f (.inr j) = i).card := by
  simp only [card_filter, Fintype.sum_sum_type]

open Classical in
/-- **Teorema de Hajnal–Szemerédi.** -/
theorem hajnalSzemeredi (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (univ.filter fun v => C v = i).card ≤ (univ.filter fun v => C v = j).card + 1 := by
  -- `n + p = s (r + 1)` con `p ≤ r`
  obtain ⟨s, p, hsp, hp⟩ : ∃ s p : ℕ, Fintype.card V + p = s * (r + 1) ∧ p ≤ r := by
    have e := Nat.div_add_mod (Fintype.card V + r) (r + 1)
    have hm := Nat.mod_lt (Fintype.card V + r) (by omega : 0 < r + 1)
    refine ⟨(Fintype.card V + r) / (r + 1),
      (r + 1) * ((Fintype.card V + r) / (r + 1)) - Fintype.card V, ?_, ?_⟩
    · have e' : (r + 1) * ((Fintype.card V + r) / (r + 1)) =
          (Fintype.card V + r) / (r + 1) * (r + 1) := Nat.mul_comm _ _
      omega
    · omega
  have hdeg : ∀ w, (pad G p).degree w ≤ r := by
    intro w
    rw [← (pad G p).card_neighborFinset_eq_degree]
    cases w with
    | inl u =>
      refine le_trans (card_le_card (t := (G.neighborFinset u).map Function.Embedding.inl)
        fun x hx => ?_) ?_
      · rw [SimpleGraph.mem_neighborFinset] at hx
        cases x with
        | inl v =>
          exact mem_map_of_mem _ ((G.mem_neighborFinset u v).mpr hx)
        | inr j => exact absurd hx (by simp [pad, padAdj])
      · rw [card_map, G.card_neighborFinset_eq_degree]; exact h u
    | inr i =>
      refine le_trans (card_le_card (t := (univ.erase i).map Function.Embedding.inr)
        fun x hx => ?_) ?_
      · rw [SimpleGraph.mem_neighborFinset] at hx
        cases x with
        | inl v => exact absurd hx (by simp [pad, padAdj])
        | inr j =>
          have : i ≠ j := hx
          exact mem_map_of_mem _ (mem_erase.mpr ⟨Ne.symm this, mem_univ _⟩)
      · rw [card_map, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨C', hC'⟩ := hajnalSzemeredi_exact (pad G p) r s
    (by rw [Fintype.card_sum, Fintype.card_fin, hsp]) hdeg
  -- restricción a `V`
  refine ⟨SimpleGraph.Coloring.mk (fun v => C' (.inl v)) fun {u v} huv =>
    C'.valid (show (pad G p).Adj (.inl u) (.inl v) from huv), fun i j => ?_⟩
  -- cada clase tiene a lo más un vértice agregado
  have hb : ∀ i, (univ.filter fun t : Fin p => C' (.inr t) = i).card ≤ 1 := by
    intro i
    refine card_le_one.mpr fun a ha b hb => ?_
    by_contra hab
    have hadj : (pad G p).Adj (.inr a) (.inr b) := hab
    exact C'.valid hadj (by rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2])
  have ai : ∀ i, (univ.filter fun v : V => C' (.inl v) = i).card +
      (univ.filter fun t : Fin p => C' (.inr t) = i).card = s := by
    intro i
    rw [← hC' i]
    convert (card_classes_split C' i).symm
  have key : (univ.filter fun v : V => C' (.inl v) = i).card ≤
      (univ.filter fun v : V => C' (.inl v) = j).card + 1 := by
    have := ai i; have := ai j; have := hb i; have := hb j
    omega
  convert key using 3 <;> rfl

end HajnalSzemeredi
