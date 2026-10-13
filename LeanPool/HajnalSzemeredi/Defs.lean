/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Definiciones para la prueba de Kierstead–Kostochka del teorema de Hajnal–Szemerédi

Trabajamos con un grafo `G` sobre un tipo ambiente `V` y un conjunto finito de vértices
`S : Finset V` (el grafo considerado es el inducido `G[S]`). Una coloración es una función
`c : V → ℕ`; sólo importan sus valores sobre `S`, y la paleta es un `Finset ℕ`.

Esto permite pasar a subgrafos inducidos (`A ∪ {y₁}`, `B \ {y₁}` en el artículo) y cambiar la
paleta sin cambiar de tipo.

Referencia: H. A. Kierstead, A. V. Kostochka, *A short proof of the Hajnal–Szemerédi theorem on
equitable colouring*, Combin. Probab. Comput. 17 (2008) 265–270.
-/

@[expose] public section

noncomputable section

open Finset

namespace HajnalSzemeredi

variable {V : Type*} (G : SimpleGraph V)

open Classical in
/-- La clase de color `i` de `c` dentro de `S`. -/
def cls (S : Finset V) (c : V → ℕ) (i : ℕ) : Finset V := S.filter fun v => c v = i

open Classical in
/-- Vecinos de `v` dentro de `S`. -/
def nbr (S : Finset V) (v : V) : Finset V := S.filter fun w => G.Adj v w

open Classical in
/-- `c` es propia sobre `S`. -/
def Proper (S : Finset V) (c : V → ℕ) : Prop := ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c v ≠ c w

open Classical in
/-- `c` toma valores en la paleta `P` sobre `S`. -/
def Into (S : Finset V) (c : V → ℕ) (P : Finset ℕ) : Prop := ∀ v ∈ S, c v ∈ P

open Classical in
/-- Grado máximo de `G[S]` a lo más `r`. -/
def DegLe (S : Finset V) (r : ℕ) : Prop := ∀ v ∈ S, (nbr G S v).card ≤ r

open Classical in
/-- Número de pares ordenados adyacentes en `S` (el doble del número de aristas de `G[S]`). -/
def edgeCount (S : Finset V) : ℕ := (S.offDiag.filter fun p => G.Adj p.1 p.2).card

open Classical in
/-- Coloración equitativa de `S` con paleta `P`, todas las clases de tamaño exactamente `s`. -/
structure IsEq (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (s : ℕ) : Prop where
  proper : Proper G S c
  into : Into S c P
  card : ∀ i ∈ P, (cls S c i).card = s

open Classical in
/-- Coloración casi equitativa: todas las clases de tamaño `s`, salvo una clase pequeña `lo`
de tamaño `s - 1` y una clase grande `hi` de tamaño `s + 1`. -/
structure IsNear (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (s lo hi : ℕ) : Prop where
  proper : Proper G S c
  into : Into S c P
  lo_mem : lo ∈ P
  hi_mem : hi ∈ P
  lo_ne_hi : lo ≠ hi
  card_lo : (cls S c lo).card + 1 = s
  card_hi : (cls S c hi).card = s + 1
  card : ∀ i ∈ P, i ≠ lo → i ≠ hi → (cls S c i).card = s

open Classical in
/-- `v` es *movible* a la clase `j`: no tiene vecinos en ella. -/
def Movable (S : Finset V) (c : V → ℕ) (v : V) (j : ℕ) : Prop :=
  ∀ w ∈ cls S c j, ¬ G.Adj v w

open Classical in
/-- Arco `i → j` del digrafo auxiliar `H(G, c)`: algún vértice de la clase `i` es movible a `j`. -/
def Mov (S : Finset V) (c : V → ℕ) (i j : ℕ) : Prop := ∃ v ∈ cls S c i, Movable G S c v j

open Classical in
/-- Clases accesibles: las que alcanzan a `lo` en `H(G, c)`. -/
def acc (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (lo : ℕ) : Finset ℕ :=
  P.filter fun i => Relation.ReflTransGen (Mov G S c) i lo

/-! ### Lemas básicos sobre clases -/

variable {G}

open Classical in
@[simp] lemma mem_cls {S : Finset V} {c : V → ℕ} {i : ℕ} {v : V} :
    v ∈ cls S c i ↔ v ∈ S ∧ c v = i := by
  simp [cls]

open Classical in
lemma cls_subset (S : Finset V) (c : V → ℕ) (i : ℕ) : cls S c i ⊆ S := filter_subset _ _

open Classical in
@[simp] lemma mem_nbr {S : Finset V} {v w : V} : w ∈ nbr G S v ↔ w ∈ S ∧ G.Adj v w := by
  simp [nbr]

open Classical in
lemma cls_disjoint {S : Finset V} {c : V → ℕ} {i j : ℕ} (h : i ≠ j) :
    Disjoint (cls S c i) (cls S c j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  rw [mem_cls] at hi hj
  exact h (hi.2.symm.trans hj.2)

open Classical in
/-- Las clases de la paleta particionan `S`: la suma de sus tamaños es `|S|`. -/
lemma sum_card_cls {S : Finset V} {c : V → ℕ} {P : Finset ℕ} (h : Into S c P) :
    ∑ i ∈ P, (cls S c i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext v
    simp only [mem_biUnion, mem_cls]
    exact ⟨fun ⟨_, _, hv, _⟩ => hv, fun hv => ⟨c v, h v hv, hv, rfl⟩⟩
  · intro i _ j _ hij
    exact cls_disjoint hij

/-! ### Mover un vértice a otra clase -/

section Move

variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}

open Classical in
lemma cls_update_self (hv : v ∈ S) :
    cls S (Function.update c v j) j = insert v (cls S c j) := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [hv]
  · simp [hw]

open Classical in
lemma cls_update_old (hv : v ∈ S) (hj : c v ≠ j) :
    cls S (Function.update c v j) (c v) = (cls S c (c v)).erase v := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [Ne.symm hj]
  · simp [hw]

open Classical in
lemma cls_update_other {k : ℕ} (hk : k ≠ j) (hk' : k ≠ c v) :
    cls S (Function.update c v j) k = cls S c k := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [Ne.symm hk, Ne.symm hk']
  · simp [hw]

open Classical in
lemma card_cls_update_self (hv : v ∈ S) (hj : c v ≠ j) :
    (cls S (Function.update c v j) j).card = (cls S c j).card + 1 := by
  rw [cls_update_self hv, card_insert_of_notMem]
  simp [hj]

open Classical in
lemma card_cls_update_old (hv : v ∈ S) (hj : c v ≠ j) :
    (cls S (Function.update c v j) (c v)).card + 1 = (cls S c (c v)).card := by
  rw [cls_update_old hv hj, card_erase_add_one]
  simp [hv]

open Classical in
lemma into_update {P : Finset ℕ} (h : Into S c P) (hj : j ∈ P) :
    Into S (Function.update c v j) P := by
  intro w hw
  by_cases hwv : w = v
  · subst hwv; simpa using hj
  · simpa [hwv] using h w hw

open Classical in
/-- Mover un vértice movible preserva la propiedad. -/
lemma proper_update (h : Proper G S c) (hmov : Movable G S c v j) :
    Proper G S (Function.update c v j) := by
  intro a ha b hb hab
  by_cases hav : a = v
  · subst hav
    have hbv : b ≠ a := fun h => G.loopless.irrefl _ (h ▸ hab)
    simp only [Function.update_self, Function.update_of_ne hbv]
    intro hjb
    exact hmov b (mem_cls.mpr ⟨hb, hjb.symm⟩) hab
  · by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self, Function.update_of_ne hav]
      intro hja
      exact hmov a (mem_cls.mpr ⟨ha, hja⟩) hab.symm
    · simpa [Function.update_of_ne hav, Function.update_of_ne hbv] using h a ha b hb hab

end Move

end HajnalSzemeredi
