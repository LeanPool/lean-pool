/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.Defs
public import LeanPool.HajnalSzemeredi.Reach

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Lema 2.1 de Kierstead–Kostochka

Si la clase grande `hi` de una coloración casi equitativa es accesible (alcanza a la clase
pequeña `lo` en el digrafo auxiliar `H`), moviendo un vértice a lo largo de un camino de `hi` a
`lo` se obtiene una coloración equitativa.

Para evitar caminos simples, inducimos sobre un conjunto `K` de clases permitidas: tras mover un
vértice de `hi` a la siguiente clase `j`, el resto del camino evita `hi`, y basta con `K \ {hi}`.
-/

@[expose] public section

noncomputable section

open Finset Relation

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- Si `j ≠ lo` alcanza a `lo`, la clase `j` es no vacía y por tanto está en la paleta. -/
lemma mem_palette_of_reach {S : Finset V} {P : Finset ℕ} {c : V → ℕ} (hc : Into S c P)
    {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → Mov G S c a b) {j lo : ℕ}
    (h : ReflTransGen R j lo) (hj : j ≠ lo) : j ∈ P := by
  rcases h.cases_head with h | ⟨k, hjk, -⟩
  · exact absurd h hj
  · obtain ⟨v, hv, -⟩ := hR _ _ hjk
    rw [mem_cls] at hv
    exact hv.2 ▸ hc v hv.1

open Classical in
theorem shift {S : Finset V} {P : Finset ℕ} {s lo : ℕ} (K : Finset ℕ) :
    ∀ (c : V → ℕ) (hi : ℕ), IsNear G S P c s lo hi →
      ReflTransGen (fun a b => Mov G S c a b ∧ a ∈ K ∧ b ∈ K) hi lo →
      ∃ c', IsEq G S P c' s := by
  induction K using Finset.strongInduction with
  | H K ih =>
  intro c hi hc hpath
  obtain ⟨j, ⟨⟨v, hv, hmov⟩, hiK, hjK⟩, hjhi, hjpath⟩ :=
    exists_step_avoid hpath (Ne.symm hc.lo_ne_hi)
  rw [mem_cls] at hv
  obtain ⟨hvS, hvc⟩ := hv
  have hcvj : c v ≠ j := hvc ▸ Ne.symm hjhi
  set c' := Function.update c v j with hc'
  have hproper : Proper G S c' := proper_update hc.proper hmov
  -- tamaños tras el movimiento
  have hcard_j : (cls S c' j).card = (cls S c j).card + 1 := card_cls_update_self hvS hcvj
  have hcard_hi : (cls S c' hi).card + 1 = (cls S c hi).card := by
    have := card_cls_update_old (j := j) hvS hcvj
    rwa [hvc] at this
  have hcard_other : ∀ k, k ≠ j → k ≠ hi → (cls S c' k).card = (cls S c k).card := by
    intro k hkj hkhi
    rw [cls_update_other hkj (hvc ▸ hkhi)]
  by_cases hjlo : j = lo
  · -- llegamos a la clase pequeña: la coloración es equitativa
    subst hjlo
    refine ⟨c', hproper, into_update hc.into hc.lo_mem, fun k hk => ?_⟩
    by_cases hkj : k = j
    · subst hkj; rw [hcard_j, hc.card_lo]
    · by_cases hkhi : k = hi
      · subst hkhi; have := hc.card_hi; omega
      · rw [hcard_other k hkj hkhi, hc.card k hk hkj hkhi]
  · -- `j` pasa a ser la clase grande; el camino restante evita `hi`
    have hjP : j ∈ P := mem_palette_of_reach hc.into (fun a b h => h.1.1) hjpath hjlo
    have hlohi : lo ≠ hi := hc.lo_ne_hi
    have hnear : IsNear G S P c' s lo j := by
      refine ⟨hproper, into_update hc.into hjP, hc.lo_mem, hjP, Ne.symm hjlo, ?_, ?_, ?_⟩
      · rw [hcard_other lo (Ne.symm hjlo) hlohi, hc.card_lo]
      · rw [hcard_j, hc.card j hjP hjlo hjhi]
      · intro k hk hklo hkj
        by_cases hkhi : k = hi
        · subst hkhi; have := hc.card_hi; omega
        · rw [hcard_other k hkj hkhi, hc.card k hk hklo hkhi]
    refine ih (K.erase hi) (erase_ssubset hiK) c' j hnear ?_
    refine transfer hjpath fun a b hab hbj => ?_
    obtain ⟨⟨⟨w, hw, hwmov⟩, haK, hbK⟩, hahi, hbhi⟩ := hab
    rw [mem_cls] at hw
    have hwv : w ≠ v := by
      rintro rfl
      exact hahi (hw.2.symm.trans hvc)
    refine ⟨⟨w, ?_, ?_⟩, mem_erase.mpr ⟨hahi, haK⟩, mem_erase.mpr ⟨hbhi, hbK⟩⟩
    · rw [mem_cls, hc', Function.update_of_ne hwv]
      exact hw
    · intro u hu
      rw [cls_update_other hbj (hvc ▸ hbhi)] at hu
      exact hwmov u hu

open Classical in
/-- **Lema 2.1.** Si la clase grande es accesible, hay una coloración equitativa. -/
theorem shift_of_acc {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {s lo hi : ℕ}
    (hc : IsNear G S P c s lo hi) (hacc : ReflTransGen (Mov G S c) hi lo) :
    ∃ c', IsEq G S P c' s := by
  set K : Finset ℕ := insert lo (S.image c)
  have key : ∀ a, ReflTransGen (Mov G S c) a lo →
      a ∈ K ∧ ReflTransGen (fun a b => Mov G S c a b ∧ a ∈ K ∧ b ∈ K) a lo := by
    intro a h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨mem_insert_self _ _, ReflTransGen.refl⟩
    | head hab _ ih =>
      obtain ⟨v, hv, -⟩ := id hab
      rw [mem_cls] at hv
      have haK : _ ∈ K := mem_insert_of_mem (mem_image.mpr ⟨v, hv.1, hv.2⟩)
      exact ⟨haK, ReflTransGen.head ⟨hab, haK, ih.1⟩ ih.2⟩
  exact shift K c hi hc (key hi hacc).2

end HajnalSzemeredi
