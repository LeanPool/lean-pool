/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Logic.Relation

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Lemas genéricos de alcanzabilidad

Dos herramientas sobre `Relation.ReflTransGen` que reemplazan el uso de "caminos simples" en el
argumento de Kierstead–Kostochka:

* `transfer`: si `x` alcanza `z` por `R`, y `R'` contiene todos los arcos de `R` cuyo destino no es
  `x`, entonces `x` alcanza `z` por `R'` (se usa la última visita a `x`).
* `exists_step_avoid`: si `x ≠ z` y `x` alcanza `z`, hay un primer paso `x → j` con `j ≠ x` tal
  que `j` alcanza `z` sin pasar por `x`.
-/

@[expose] public section

namespace HajnalSzemeredi

open Relation

variable {α : Type*}

open Classical in
theorem transfer {R R' : α → α → Prop} {x z : α} (h : ReflTransGen R x z)
    (hR : ∀ a b, R a b → b ≠ x → R' a b) : ReflTransGen R' x z := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hab ih =>
    by_cases hc : c = x
    · subst hc; exact ReflTransGen.refl
    · exact ih.tail (hR _ _ hab hc)

open Classical in
theorem exists_step_avoid {R : α → α → Prop} {x z : α} (h : ReflTransGen R x z) (hxz : x ≠ z) :
    ∃ j, R x j ∧ j ≠ x ∧ ReflTransGen (fun a b => R a b ∧ a ≠ x ∧ b ≠ x) j z := by
  induction h with
  | refl => exact absurd rfl hxz
  | @tail a b hxa hab ih =>
    by_cases ha : a = x
    · subst ha
      exact ⟨b, hab, Ne.symm hxz, ReflTransGen.refl⟩
    · obtain ⟨j, hj, hjx, hjb⟩ := ih (Ne.symm ha)
      exact ⟨j, hj, hjx, hjb.tail ⟨hab, ha, Ne.symm hxz⟩⟩

end HajnalSzemeredi
