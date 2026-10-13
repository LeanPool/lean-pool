/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.Defs

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Definitions for the equitable-colouring counting argument

Abstraemos la situación del artículo en `CountHyp`:

* `PA` (clases accesibles) y `PB` (inaccesibles) son paletas disjuntas que cubren los colores de
  `S`; `A`, `B` son los vértices con color en `PA`, `PB`;
* `TU ⊆ PA` es la familia `𝒜'`, con `t = |TU|` clases, todas de tamaño `s`;
* `q = |PB|`, `|B| = q s + 1`, grado máximo `r` con `r + 1 = |PA| + |PB|`;
* (2.1): todo `y ∈ B` tiene un vecino en cada clase de `PA`;
* (2.2): todo `x` con color en `TU` tiene al menos `|PA| - 1 - t` vecinos en `A`.

Una arista `zy` (`z` con color `W ∈ TU`, `y ∈ B`) es *solo* si `z` es el único vecino de `y` en
la clase `W`. `Sz z` son los vecinos especiales de `z` (en `B`) y `Sy y` los de `y` (en `A'`).
-/

@[expose] public section

noncomputable section

open Finset

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- Vértices de `S` con color en la paleta `Q`. -/
def part (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) : Finset V := S.filter fun v => c v ∈ Q

open Classical in
/-- Vecinos de `y` en la clase `W`. -/
def nIn (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (y : V) (W : ℕ) : Finset V :=
  nbr G S y ∩ cls S c W

open Classical in
/-- `zy` es una arista solo (respecto a la familia `TU` y al conjunto `B`). -/
def IsSolo (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V)
    (z y : V) : Prop :=
  z ∈ S ∧ c z ∈ TU ∧ y ∈ B ∧ nIn G S c y (c z) = {z}

open Classical in
/-- Vecinos especiales de `z`. -/
def Sz (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (z : V) :
    Finset V := B.filter fun y => IsSolo G S c TU B z y

open Classical in
/-- Vecinos especiales de `y`. -/
def Sy (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (y : V) :
    Finset V := S.filter fun z => IsSolo G S c TU B z y

open Classical in
/-- Hipótesis de la parte de conteo. -/
structure CountHyp (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (PA PB TU : Finset ℕ)
    (r s : ℕ) : Prop where
  disj : Disjoint PA PB
  cover : ∀ v ∈ S, c v ∈ PA ∪ PB
  sub : TU ⊆ PA
  ne : TU.Nonempty
  card_r : r + 1 = PA.card + PB.card
  deg : DegLe G S r
  size : ∀ W ∈ TU, (cls S c W).card = s
  card_B : (part S c PB).card = PB.card * s + 1
  /-- (2.1) -/
  h21 : ∀ y ∈ part S c PB, ∀ X ∈ PA, (nIn G S c y X).Nonempty
  /-- (2.2) -/
  h22 : ∀ x ∈ S, c x ∈ TU → PA.card ≤ (nbr G (part S c PA) x).card + TU.card + 1

end HajnalSzemeredi
