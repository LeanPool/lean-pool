/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cor4a

/-!
# Balister–Kostochka–Li–Schelp 2004, Corollary 4 (three colours)

`H` has maximum degree two and a proper edge colouring `χ` with two colours; `m` is a partial
matching of its vertices such that matched vertices with the same colour set under `χ` have degree
two. If no hexagon of `H` has all its opposite vertices matched, there is a proper edge colouring of
`H` with three colours in which matched vertices see different colour sets (`cor4`).

The colouring is `lemma3L` on the graph of edges `LG H m`: matched vertices of degree two give
matched edges of `LG`, matched vertices of degree one are joined in `LG`, and `χ` colours `LG`
properly, so `LG` has no odd cycle.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.C4

open Finset SimpleGraph LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]

/-- A properly two-coloured graph has no odd cycle. -/
theorem no_odd_cycle {E : Type*} {L : SimpleGraph E} (χ : E → Fin 2)
    (hχ : ∀ a b, L.Adj a b → χ a ≠ χ b) {n : ℕ} {p : ℕ → E} (hp : IsPathFn L n p)
    (hend : L.Adj (p 0) (p n)) (hodd : Odd (n + 1)) : False := by
  have key : ∀ i ≤ n, (χ (p i)).val = ((χ (p 0)).val + i) % 2 := by
    intro i hi
    induction i with
    | zero => have := (χ (p 0)).isLt; omega
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 : χ (p i) ≠ χ (p (i + 1)) := hχ _ _ (hp.2 i (by omega))
      have h3 : (χ (p i)).val ≠ (χ (p (i + 1))).val := fun e => h2 (Fin.ext e)
      have := (χ (p (i + 1))).isLt
      have := (χ (p i)).isLt
      omega
  have h := key n le_rfl
  obtain ⟨k, hk⟩ := hodd
  have h2 : χ (p 0) ≠ χ (p n) := hχ _ _ hend
  apply h2
  apply Fin.ext
  have := (χ (p 0)).isLt
  omega

omit [DecidableEq V] in
/-- **Corollary 4 (three colours).** -/
theorem cor4 (hdeg : ∀ v, H.degree v ≤ 2) (χ : Sym2 V → Fin 2)
    (hχ : ∀ v e e', e ∈ H.incidenceFinset v → e' ∈ H.incidenceFinset v → e ≠ e' → χ e ≠ χ e')
    (m : V → Option V)
    (hm : ∀ u v, m u = some v → m v = some u ∧ u ≠ v ∧
      ((H.incidenceFinset u).image χ = (H.incidenceFinset v).image χ → H.degree u = 2))
    (hhex : ∀ w : ZMod 6 → V, (∀ k, H.Adj (w k) (w (k + 1))) → Function.Injective w →
      ¬ ∀ k, m (w k) = some (w (k + 3))) :
    ∃ col : Sym2 V → Fin 3,
      (∀ v e e', e ∈ H.incidenceFinset v → e' ∈ H.incidenceFinset v → e ≠ e' → col e ≠ col e') ∧
      ∀ u v, m u = some v → (H.incidenceFinset u).image col ≠ (H.incidenceFinset v).image col := by
  classical
  have hm' : ∀ u v, m u = some v → m v = some u := fun u v h => (hm u v h).1
  -- the matching of the edges of `LG`
  let P : Sym2 (Sym2 V) → Prop := fun ℓ =>
    ∃ u v, H.degree u = 2 ∧ H.degree v = 2 ∧ m u = some v ∧ Lv H u = ℓ
  let μ : Sym2 (Sym2 V) → Option (Sym2 (Sym2 V)) := fun ℓ =>
    if h : P ℓ then some (Lv H h.choose_spec.choose) else none
  have hμ_eq : ∀ u v, H.degree u = 2 → H.degree v = 2 → m u = some v → μ (Lv H u) = some (Lv H
      v) := by
    intro u v hu hv huv
    have h : P (Lv H u) := ⟨u, v, hu, hv, huv, rfl⟩
    simp only [μ, dite_eq_left h]
    obtain ⟨hu', hv', huv', hL⟩ := h.choose_spec.choose_spec
    have e1 : h.choose = u := Lv_inj hu' hu hL
    have h3 : (some h.choose_spec.choose : Option V) = some v :=
      huv'.symm.trans ((congrArg m e1).trans huv)
    rw [Option.some.inj h3]
  have hμ_inv : ∀ ℓ ℓ', μ ℓ = some ℓ' → ∃ u v, H.degree u = 2 ∧ H.degree v = 2 ∧
      m u = some v ∧ Lv H u = ℓ ∧ Lv H v = ℓ' := by
    intro ℓ ℓ' h
    by_cases hP : P ℓ
    · simp only [μ, dite_eq_left hP] at h
      obtain ⟨hu, hv, huv, hL⟩ := hP.choose_spec.choose_spec
      exact ⟨_, _, hu, hv, huv, hL, Option.some.inj h⟩
    · simp [μ, dite_eq_right hP] at h
  -- `χ` colours `LG` properly
  have hχL : ∀ e e', (LG H m).Adj e e' → χ e ≠ χ e' := by
    intro e e' h
    obtain ⟨hne, he, he', h⟩ := h
    have hmerge : ∀ a b, Merge H m a b → χ a ≠ χ b := by
      rintro a b ⟨u, v, huv, hu1, hv1, ha, hb⟩ hab
      have h1 : (H.incidenceFinset u).image χ = (H.incidenceFinset v).image χ := by
        have ea : H.incidenceFinset u = {a} := by
          rw [← card_inc] at hu1; obtain ⟨x, hx⟩ := card_eq_one.1 hu1
          rw [hx] at ha ⊢; rw [mem_singleton.1 ha]
        have eb : H.incidenceFinset v = {b} := by
          rw [← card_inc] at hv1; obtain ⟨x, hx⟩ := card_eq_one.1 hv1
          rw [hx] at hb ⊢; rw [mem_singleton.1 hb]
        rw [ea, eb, image_singleton, image_singleton, hab]
      have := (hm u v huv).2.2 h1
      omega
    rcases h with ⟨w, hw, hw'⟩ | h | h
    · exact hχ w e e' ((mem_inc H).2 ⟨he, hw⟩) ((mem_inc H).2 ⟨he', hw'⟩) hne
    · exact hmerge e e' h
    · exact fun h' => hmerge e' e h h'.symm
  obtain ⟨g, hg1, hg2⟩ := L3L.lemma3L (L := LG H m) (degree_LG_le hdeg hm') μ
    (fun e e' h => by
      obtain ⟨u, v, hu, hv, huv, rfl, rfl⟩ := hμ_inv e e' h
      refine ⟨hμ_eq v u hv hu (hm' u v huv), Lv_adj hu, Lv_adj hv, fun e => ?_⟩
      exact (hm u v huv).2.1 (Lv_inj hu hv e))
    (fun n p hp _ hend hodd => (no_odd_cycle χ hχL hp hend hodd).elim)
    (fun p hp hend hall => by
      -- the hexagon of vertices of degree two
      have hex : ∀ k : ZMod 6, ∃ u, H.degree u = 2 ∧ Lv H u = s(p (k - 1).val, p k.val) ∧
          ∃ v, H.degree v = 2 ∧ m u = some v ∧ Lv H v = s(p (k + 2).val, p (k + 3).val) := by
        intro k
        obtain ⟨u, v, hu, hv, huv, h1, h2⟩ := hμ_inv _ _ (hall k)
        exact ⟨u, hu, h1, v, hv, huv, h2⟩
      choose w hw2 hwL v hv2 hwm hvL using hex
      have hedge : ∀ a b : ZMod 6,
          s(p (a - 1).val, p a.val) = s(p (b - 1).val, p b.val) → a = b := by
        intro a b h
        have hval : ∀ x : ZMod 6, x.val ≤ 5 := fun x => by have := ZMod.val_lt x; omega
        rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact ZMod.val_injective 6 (hp.1 _ _ (hval a) (hval b) h2)
        · have e1 : a - 1 = b := ZMod.val_injective 6 (hp.1 _ _ (hval _) (hval _) h1)
          have e2 : a = b - 1 := ZMod.val_injective 6 (hp.1 _ _ (hval _) (hval _) h2)
          exfalso
          rw [← e1] at e2
          have : ∀ x : ZMod 6, x ≠ x - 1 - 1 := by decide
          exact this a e2
      have hinj : Function.Injective w := fun a b h => by
        apply hedge
        rw [← hwL a, ← hwL b, h]
      have hvw : ∀ k, v k = w (k + 3) := fun k => by
        apply Lv_inj (hv2 k) (hw2 (k + 3))
        rw [hvL k, hwL (k + 3), show k + 3 - 1 = k + 2 by ring]
      have hmem : ∀ k : ZMod 6, p k.val ∈ H.incidenceFinset (w k) ∧
          p k.val ∈ H.incidenceFinset (w (k + 1)) := by
        intro k
        have h1 : p k.val ∈ Lv H (w k) := by rw [hwL k]; exact Sym2.mem_mk_right _ _
        have h2 : p k.val ∈ Lv H (w (k + 1)) := by
          rw [hwL (k + 1), add_sub_cancel_right]; exact Sym2.mem_mk_left _ _
        exact ⟨Lv_mem (hw2 k) h1, Lv_mem (hw2 (k + 1)) h2⟩
      have hadjw : ∀ k, H.Adj (w k) (w (k + 1)) := by
        intro k
        obtain ⟨h1, h2⟩ := hmem k
        have hne : w k ≠ w (k + 1) := fun h => by
          have := hinj h
          have : ∀ x : ZMod 6, x ≠ x + 1 := by decide
          exact this k ‹_›
        have := edge_eq_of_mem ((mem_inc H).1 h1).1 ((mem_inc H).1 h1).2 ((mem_inc H).1 h2).2 hne
        rw [← mem_edgeSet, ← this]
        exact ((mem_inc H).1 h1).1
      exact hhex w hadjw hinj fun k => by rw [hwm k, hvw k])
  -- the colouring of `H`
  have hprop : ∀ v e e', e ∈ H.incidenceFinset v → e' ∈ H.incidenceFinset v → e ≠ e' →
      g e ≠ g e' := by
    intro v e e' he he' hne
    exact hg1 e e' ⟨hne, ((mem_inc H).1 he).1, ((mem_inc H).1 he').1,
      Or.inl ⟨v, ((mem_inc H).1 he).2, ((mem_inc H).1 he').2⟩⟩
  have hcard : ∀ u, #((H.incidenceFinset u).image g) = H.degree u := by
    intro u
    rw [card_image_of_injOn, card_inc]
    intro a ha b hb e
    by_contra hne
    exact hprop u a b ha hb hne e
  refine ⟨g, hprop, fun u v huv => ?_⟩
  obtain ⟨hvu, hne, hS⟩ := hm u v huv
  by_cases hd : H.degree u = H.degree v
  swap
  · intro e
    apply hd
    rw [← hcard u, ← hcard v, e]
  -- equal degrees
  have hdu := hdeg u
  rcases (show H.degree u = 0 ∨ H.degree u = 1 ∨ H.degree u = 2 by omega) with h0 | h1 | h2
  · exfalso
    have eu : H.incidenceFinset u = ∅ := card_eq_zero.1 (by rw [card_inc]; exact h0)
    have ev : H.incidenceFinset v = ∅ := card_eq_zero.1 (by rw [card_inc]; omega)
    have := hS (by rw [eu, ev])
    omega
  · -- degree one: the two edges are joined in `LG`
    obtain ⟨a, ha⟩ := card_eq_one.1 (show #(H.incidenceFinset u) = 1 by rw [card_inc]; exact h1)
    obtain ⟨b, hb⟩ := card_eq_one.1 (show #(H.incidenceFinset v) = 1 by rw [card_inc]; omega)
    have hab : a ≠ b := by
      intro e
      have := hS (by rw [ha, hb, e])
      omega
    have haL : a ∈ H.edgeSet := ((mem_inc H).1 (by rw [ha]; exact mem_singleton_self a)).1
    have hbL : b ∈ H.edgeSet := ((mem_inc H).1 (by rw [hb]; exact mem_singleton_self b)).1
    have hgab : g a ≠ g b := hg1 a b ⟨hab, haL, hbL, Or.inr (Or.inl ⟨u, v, huv, h1, by omega,
      by rw [ha]; exact mem_singleton_self a, by rw [hb]; exact mem_singleton_self b⟩)⟩
    rw [ha, hb, image_singleton, image_singleton]
    intro e
    exact hgab (singleton_injective e)
  · -- degree two: the matched edges of `LG`
    have hv2 : H.degree v = 2 := by omega
    have hsep := hg2 _ _ (hμ_eq u v h2 hv2 huv)
    have hcs : ∀ x, H.degree x = 2 → L3L.cs g (Lv H x) = (H.incidenceFinset x).image g := by
      intro x hx
      obtain ⟨e1, e2, -, heq, hL⟩ := Lv_spec hx
      rw [hL, L3L.cs_mk, heq, image_insert, image_singleton]
    rw [← hcs u h2, ← hcs v hv2]
    exact hsep
end Bkls.C4

end LeanPool.BalancedEdgeColourings
