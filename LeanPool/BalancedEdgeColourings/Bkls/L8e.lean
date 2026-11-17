/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L8d

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 8

`lemma8`: in an optimal colouring with all `n_T ≤ 2`, for `S₋ ⊆ S₊` and `γ ∈ S₊ \ S₋`, some
`(S₊ \ S₋)`-recolouring has, with `r = |S₊| - |S₋|` and `G_d` the number of 1-piles in
`[S₋, S₊]_d`,
* `r · g_{γ,d} ≤ (d - |S₋|) G_d + r - 1` for all `d` (`g_{γ,d} ≤ ⌈(d - |S₋|) G_d / r⌉`), and
* `r · g_{γ,d₀} ≤ (d₀ - |S₋|) G_{d₀}` for one given `d₀`.

Take the recolouring minimising `Ψ = Σ_d Σ_e g_{e,d}²`, then `Σ_d g_{γ,d}`, then `g_{γ,d₀}`; the
moves of `move8` show `g_{γ,d} ≤ g_{e,d} + 1` and `g_{γ,d₀} ≤ g_{e,d₀}` for every `e`, and
`Σ_e g_{e,d} = (d - |S₋|) G_d`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L8

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm Sp : Finset (Fin k)}

open Classical in
theorem exists_min_nat {α : Type*} (P : α → Prop) (f : α → ℕ) (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → f x ≤ f y := by
  have hex : ∃ m, ∃ x, P x ∧ f x = m := let ⟨x, hx⟩ := h; ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, hfx⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hfx]
  exact Nat.find_min' hex ⟨y, hy, rfl⟩

open Classical in
/-- 1-piles in `[S₋, S₊]_d`. -/
noncomputable def Gd (Sm Sp : Finset (Fin k)) (c : PEC G (Fin k)) (d : ℕ) : ℕ :=
  #(univ.filter fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ #T = d ∧ cnt c T = 1)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem g_zero_of_gt {c : PEC G (Fin k)} {e : Fin k} {d : ℕ} (hd : k < d) : g Sm Sp c e d = 0 := by
  classical
  unfold g
  rw [card_eq_zero, filter_eq_empty_iff]
  intro T _ h
  have := card_le_univ T
  rw [Fintype.card_fin] at this
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Double counting.** -/
theorem sum_g (_ : Sm ⊆ Sp) (c : PEC G (Fin k)) (d : ℕ) :
    ∑ e ∈ Sp \ Sm, g Sm Sp c e d = (d - #Sm) * Gd Sm Sp c d := by
  classical
  unfold g Gd
  simp only [card_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro T _
  by_cases hT : Sm ⊆ T ∧ T ⊆ Sp ∧ #T = d ∧ cnt c T = 1
  · obtain ⟨h1, h2, h3, h4⟩ := hT
    rw [ite_eq_left ⟨h1, h2, h3, h4⟩, mul_one]
    have : ∑ e ∈ Sp \ Sm, (if Sm ⊆ T ∧ T ⊆ Sp ∧ e ∈ T ∧ #T = d ∧ cnt c T = 1 then 1 else 0) =
        ∑ e ∈ Sp \ Sm, (if e ∈ T then 1 else 0) := by
      apply sum_congr rfl
      intro e _
      by_cases he : e ∈ T
      · rw [ite_eq_left ⟨h1, h2, he, h3, h4⟩, ite_eq_left he]
      · rw [ite_eq_right (fun h => he h.2.2.1), ite_eq_right he]
    rw [this, ← card_filter]
    have e1 : (Sp \ Sm).filter (fun e => e ∈ T) = T \ Sm := by
      ext e; simp only [mem_filter, mem_sdiff]
      constructor
      · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨⟨h2 h', h⟩, h'⟩
    rw [e1]
    have := card_sdiff_add_card_eq_card h1
    omega
  · rw [ite_eq_right hT, mul_zero]
    apply sum_eq_zero
    intro e _
    rw [ite_eq_right]
    rintro ⟨h1, h2, -, h3, h4⟩
    exact hT ⟨h1, h2, h3, h4⟩
section Extremal

variable (Sm Sp) in
open Classical in
/-- `Ψ = Σ_d Σ_e g_{e,d}²`. -/
noncomputable def Psi (c : PEC G (Fin k)) : ℕ :=
  ∑ d ∈ range (k + 1), ∑ e ∈ Sp \ Sm, g Sm Sp c e d ^ 2

open Classical in
theorem sum_diff_pt {s : Finset ℕ} {f f' : ℕ → ℤ} {p : ℕ} (hp : p ∈ s)
    (h : ∀ d ∈ s, d ≠ p → f' d = f d) : ∑ d ∈ s, f' d - ∑ d ∈ s, f d = f' p - f p := by
  rw [← sum_erase_add _ _ hp, ← sum_erase_add (f := f) _ hp,
    sum_congr rfl (fun d hd => h d (mem_of_mem_erase hd) (ne_of_mem_erase hd))]
  ring

open Classical in
theorem sum_diff_two {s : Finset ℕ} {f f' : ℕ → ℤ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s)
    (hpq : p ≠ q) (h : ∀ d ∈ s, d ≠ p → d ≠ q → f' d = f d) :
    ∑ d ∈ s, f' d - ∑ d ∈ s, f d = (f' p - f p) + (f' q - f q) := by
  have hq' : q ∈ s.erase p := mem_erase.2 ⟨Ne.symm hpq, hq⟩
  rw [← sum_erase_add _ _ hp, ← sum_erase_add (f := f) _ hp, ← sum_erase_add _ _ hq',
    ← sum_erase_add (f := f) _ hq', sum_congr rfl (fun d hd =>
      h d (mem_of_mem_erase (mem_of_mem_erase hd)) (ne_of_mem_erase (mem_of_mem_erase hd))
        (ne_of_mem_erase hd))]
  ring

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The change of `Ψ` under a move on the colours `a, b`. -/
theorem psi_change (hab : a ≠ b) (ha : a ∈ Sp \ Sm) (hb : b ∈ Sp \ Sm) {c c' : PEC G (Fin k)}
    (h0 : ∀ e, e ≠ a → e ≠ b → ∀ d', g Sm Sp c' e d' = g Sm Sp c e d')
    (h1 : ∀ d', g Sm Sp c' a d' + g Sm Sp c' b d' = g Sm Sp c a d' + g Sm Sp c b d') :
    2 * (Psi Sm Sp c' : ℤ) - 2 * Psi Sm Sp c = ∑ d ∈ range (k + 1),
      (((g Sm Sp c' a d : ℤ) - g Sm Sp c' b d) ^ 2 - ((g Sm Sp c a d : ℤ) - g Sm Sp c b d) ^
          2) := by
  classical
  unfold Psi
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  have hsplit : ∀ c₀ : PEC G (Fin k), ∑ e ∈ Sp \ Sm, ((g Sm Sp c₀ e d : ℕ) : ℤ) ^ 2 =
      (g Sm Sp c₀ a d : ℤ) ^ 2 + (g Sm Sp c₀ b d : ℤ) ^ 2 +
        ∑ e ∈ ((Sp \ Sm).erase a).erase b, ((g Sm Sp c₀ e d : ℕ) : ℤ) ^ 2 := by
    intro c₀
    rw [← sum_erase_add _ _ ha, ← sum_erase_add _ _ (mem_erase.2 ⟨Ne.symm hab, hb⟩)]
    ring
  rw [hsplit c', hsplit c, sum_congr rfl (fun e he => by
    rw [h0 e (ne_of_mem_erase (mem_of_mem_erase he)) (ne_of_mem_erase he)])]
  have := h1 d
  have h' : (g Sm Sp c' a d : ℤ) + g Sm Sp c' b d = g Sm Sp c a d + g Sm Sp c b d := by
    exact_mod_cast this
  have hb' : (g Sm Sp c' b d : ℤ) = g Sm Sp c a d + g Sm Sp c b d - g Sm Sp c' a d := by linarith
  rw [hb']
  ring
end Extremal

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem minimal_move_bound {c c1 c2 cs : PEC G (Fin k)} {γ : Fin k} (d₀ : ℕ)
    (hγ : γ ∈ Sp \ Sm) (hcs : Rec (Sp \ Sm) c cs)
    (hcsΨ : Psi Sm Sp cs = Psi Sm Sp c1)
    (hmin1 : ∀ y, Rec (Sp \ Sm) c y → Psi Sm Sp c1 ≤ Psi Sm Sp y)
    (hmin2 : ∀ y, Rec (Sp \ Sm) c y ∧ Psi Sm Sp y = Psi Sm Sp c1 →
      ∑ d ∈ range (k + 1), g Sm Sp c2 γ d ≤ ∑ d ∈ range (k + 1), g Sm Sp y γ d)
    (hmin3 : ∀ y, (Rec (Sp \ Sm) c y ∧ Psi Sm Sp y = Psi Sm Sp c1) ∧
      ∑ d ∈ range (k + 1), g Sm Sp y γ d = ∑ d ∈ range (k + 1), g Sm Sp c2 γ d →
      g Sm Sp cs γ d₀ ≤ g Sm Sp y γ d₀)
    (hcsS : ∑ d ∈ range (k + 1), g Sm Sp cs γ d = ∑ d ∈ range (k + 1), g Sm Sp c2 γ d)
    (hopts : IsOptimal cs) (hn2s : ∀ T, cnt cs T ≤ 2) :
    ∀ e ∈ Sp \ Sm, e ≠ γ → ∀ d, g Sm Sp cs e d < g Sm Sp cs γ d →
      g Sm Sp cs γ d = g Sm Sp cs e d + 1 ∧ (d = d₀ → False) := by
  classical
  let R := Sp \ Sm
  let F : PEC G (Fin k) → Prop := fun c' => Rec R c c'
  have hγS : γ ∈ Sp := (mem_sdiff.1 hγ).1
  have hγm : γ ∉ Sm := (mem_sdiff.1 hγ).2
  have hcsS' : (∑ d' ∈ range (k + 1), (g Sm Sp cs γ d' : ℤ)) =
      ∑ d' ∈ range (k + 1), (g Sm Sp c2 γ d' : ℤ) := by exact_mod_cast hcsS
  intro e he heγ d hlt
  have heS : e ∈ Sp := (mem_sdiff.1 he).1
  have hem : e ∉ Sm := (mem_sdiff.1 he).2
  have hdk : d ≤ k := by
    by_contra h; push Not at h; rw [g_zero_of_gt h, g_zero_of_gt h] at hlt; omega
  obtain ⟨c', hrec, h0, h1, hcase⟩ := move8 (Sm := Sm) (Sp := Sp) hopts hn2s hγS heS hγm hem
    (Ne.symm heγ) hlt
  have hrecR : Rec R cs c' := Rec.mono hrec (by
    intro x hx; rcases mem_insert.1 hx with rfl | hx
    · exact hγ
    · rw [mem_singleton.1 hx]; exact he)
  have hF : F c' := hcs.trans hrecR
  have hΨ := psi_change (Ne.symm heγ) hγ he h0 h1
  have hΨmin : (Psi Sm Sp c1 : ℤ) ≤ Psi Sm Sp c' := by exact_mod_cast hmin1 c' hF
  rw [hcsΨ] at hΨ
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ, ∀ d', D d' = (g Sm Sp cs γ d' : ℤ) - g Sm Sp cs e d' :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ℕ → ℤ, ∀ d', D' d' = (g Sm Sp c' γ d' : ℤ) - g Sm Sp c' e d' :=
    ⟨_, fun _ => rfl⟩
  have hΨ' : 2 * (Psi Sm Sp c' : ℤ) - 2 * Psi Sm Sp c1 =
      ∑ d' ∈ range (k + 1), D' d' ^ 2 - ∑ d' ∈ range (k + 1), D d' ^ 2 := by
    rw [hΨ, ← sum_sub_distrib]
    exact sum_congr rfl (fun d' _ => by rw [hD, hD'])
  have hDd : 1 ≤ D d := by rw [hD]; omega
  have hmem : d ∈ range (k + 1) := mem_range.2 (by omega)
  have hDk : ∀ d', D d' ≠ 0 → d' ∈ range (k + 1) := by
    intro d' h
    by_contra hd'
    rw [mem_range, not_lt] at hd'
    rw [hD, g_zero_of_gt (show k < d' by omega), g_zero_of_gt (show k < d' by omega)] at h
    exact h rfl
  -- the sum of `γ`-counts
  have hSg : ∀ d', 2 * ((g Sm Sp c' γ d' : ℤ) - g Sm Sp cs γ d') = D' d' - D d' := by
    intro d'
    have := h1 d'
    have h' : (g Sm Sp c' γ d' : ℤ) + g Sm Sp c' e d' = g Sm Sp cs γ d' + g Sm Sp cs e d' := by
      exact_mod_cast this
    rw [hD, hD']
    linarith
  have hSg' : 2 * (∑ d' ∈ range (k + 1), (g Sm Sp c' γ d' : ℤ)) -
      2 * ∑ d' ∈ range (k + 1), (g Sm Sp cs γ d' : ℤ) =
      ∑ d' ∈ range (k + 1), D' d' - ∑ d' ∈ range (k + 1), D d' := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl (fun d' _ => by rw [← hSg d']; ring)
  have hmin2' : ∀ c'', F c'' → Psi Sm Sp c'' = Psi Sm Sp c1 →
      (∑ d' ∈ range (k + 1), (g Sm Sp cs γ d' : ℤ)) ≤
        ∑ d' ∈ range (k + 1), (g Sm Sp c'' γ d' : ℤ) := by
    intro c'' h1' h2'
    have := hmin2 c'' ⟨h1', h2'⟩
    rw [hcsS']
    exact_mod_cast this
  have hΨeq : ∀ x : ℤ, 2 * (Psi Sm Sp c' : ℤ) - 2 * Psi Sm Sp c1 = x → x ≤ 0 →
      Psi Sm Sp c' = Psi Sm Sp c1 := by
    intro x hx hx0
    have : (Psi Sm Sp c' : ℤ) = Psi Sm Sp c1 := by linarith
    exact_mod_cast this
  rcases hcase with hc | ⟨d₁, hd₁, hc⟩ | ⟨d₁, hd₁ne, hd₁, hc⟩
  · -- only `d` changes
    have hc2 : ∀ d', D' d' = D d' - (if d' = d then 2 else 0) := fun d' => by
      rw [hD', hD]; exact hc d'
    have hsum := sum_diff_pt (f := fun d' => D d' ^ 2) (f' := fun d' => D' d' ^ 2) hmem
      (fun d' _ hne => by simp only [hc2 d', ite_eq_right hne, sub_zero])
    have hsum' := sum_diff_pt (f := D) (f' := D') hmem
      (fun d' _ hne => by simp only [hc2 d', ite_eq_right hne, sub_zero])
    have hDd' : D' d = D d - 2 := by rw [hc2 d, ite_eq_left rfl]
    rw [hDd'] at hsum hsum'
    have hq : (D d - 2) ^ 2 - D d ^ 2 = -4 * D d + 4 := by ring
    by_cases h2 : D d = 1
    · have hc'Ψ := hΨeq _ hΨ' (by linarith)
      have := hmin2' c' hF hc'Ψ
      refine ⟨by rw [hD] at h2; omega, fun _ => ?_⟩
      linarith
    · exfalso
      have : 2 ≤ D d := by omega
      linarith
  · have hc2 : ∀ d', D' d' = D d' - (if d' = d then 2 else 0) - (if d' = d₁ then 2 else 0) :=
      fun d' => by rw [hD', hD]; exact hc d'
    rw [← hD] at hd₁
    have hD1nz : D d₁ ≠ 0 := by split_ifs at hd₁ <;> omega
    have hmem1 := hDk d₁ hD1nz
    by_cases hdd : d₁ = d
    · subst hdd
      have hsum := sum_diff_pt (f := fun d' => D d' ^ 2) (f' := fun d' => D' d' ^ 2) hmem
        (fun d' _ hne => by simp only [hc2 d', ite_eq_right hne, sub_zero])
      have hsum' := sum_diff_pt (f := D) (f' := D') hmem
        (fun d' _ hne => by simp only [hc2 d', ite_eq_right hne, sub_zero])
      have hDd' : D' d₁ = D d₁ - 4 := by rw [hc2 d₁, ite_eq_left rfl]; ring
      rw [hDd'] at hsum hsum'
      rw [ite_eq_left rfl] at hd₁
      have hq : (D d₁ - 4) ^ 2 - D d₁ ^ 2 = -8 * D d₁ + 16 := by ring
      have hc'Ψ := hΨeq _ hΨ' (by linarith)
      have := hmin2' c' hF hc'Ψ
      exfalso; linarith
    · rw [ite_eq_right hdd] at hd₁
      have hsum := sum_diff_two (f := fun d' => D d' ^ 2) (f' := fun d' => D' d' ^ 2) hmem
        hmem1 (Ne.symm hdd) (fun d' _ h1 h2 => by
          simp only [hc2 d', ite_eq_right h1, ite_eq_right h2, sub_zero])
      have hsum' := sum_diff_two (f := D) (f' := D') hmem hmem1 (Ne.symm hdd)
        (fun d' _ h1 h2 => by simp only [hc2 d', ite_eq_right h1, ite_eq_right h2, sub_zero])
      have e1 : D' d = D d - 2 := by rw [hc2 d, ite_eq_left rfl, ite_eq_right (Ne.symm hdd)]; ring
      have e2 : D' d₁ = D d₁ - 2 := by rw [hc2 d₁, ite_eq_right hdd, ite_eq_left rfl]; ring
      rw [e1, e2] at hsum hsum'
      have hq1 : (D d - 2) ^ 2 - D d ^ 2 = -4 * D d + 4 := by ring
      have hq2 : (D d₁ - 2) ^ 2 - D d₁ ^ 2 = -4 * D d₁ + 4 := by ring
      have hc'Ψ := hΨeq _ hΨ' (by linarith)
      have := hmin2' c' hF hc'Ψ
      exfalso; linarith
  · have hc2 : ∀ d', D' d' = D d' - (if d' = d then 2 else 0) + (if d' = d₁ then 2 else 0) :=
      fun d' => by rw [hD', hD]; exact hc d'
    rw [← hD] at hd₁
    have hmem1 := hDk d₁ (by omega)
    have hsum := sum_diff_two (f := fun d' => D d' ^ 2) (f' := fun d' => D' d' ^ 2) hmem
      hmem1 (Ne.symm hd₁ne) (fun d' _ h1 h2 => by
        simp only [hc2 d', ite_eq_right h1, ite_eq_right h2, sub_zero, add_zero])
    have hsum' := sum_diff_two (f := D) (f' := D') hmem hmem1 (Ne.symm hd₁ne)
      (fun d' _ h1 h2 => by simp only [hc2 d', ite_eq_right h1, ite_eq_right h2, sub_zero,
          add_zero])
    have e1 : D' d = D d - 2 := by rw [hc2 d, ite_eq_left rfl, ite_eq_right (Ne.symm hd₁ne)]; ring
    have e2 : D' d₁ = D d₁ + 2 := by rw [hc2 d₁, ite_eq_right hd₁ne, ite_eq_left rfl]; ring
    rw [e1, e2] at hsum hsum'
    have hq1 : (D d - 2) ^ 2 - D d ^ 2 = -4 * D d + 4 := by ring
    have hq2 : (D d₁ + 2) ^ 2 - D d₁ ^ 2 = 4 * D d₁ + 4 := by ring
    have hc'Ψ := hΨeq _ hΨ' (by linarith)
    have h2 : D d = 1 := by linarith
    refine ⟨by rw [hD] at h2; omega, fun hd0 => ?_⟩
    subst hd0
    have hS2 : ∑ d' ∈ range (k + 1), g Sm Sp c' γ d' =
        ∑ d' ∈ range (k + 1), g Sm Sp c2 γ d' := by
      have := hmin2' c' hF hc'Ψ
      have h3 : D d₁ = -1 := by linarith
      have : (∑ d' ∈ range (k + 1), (g Sm Sp c' γ d' : ℤ)) =
          ∑ d' ∈ range (k + 1), (g Sm Sp c2 γ d' : ℤ) := by linarith
      exact_mod_cast this
    have := hmin3 c' ⟨⟨hF, hc'Ψ⟩, hS2⟩
    have h4 := hSg d
    rw [e1] at h4
    have : (g Sm Sp cs γ d : ℤ) ≤ g Sm Sp c' γ d := by exact_mod_cast this
    linarith

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 8.** -/
theorem lemma8 {c : PEC G (Fin k)} (hopt : IsOptimal c) (hn2 : ∀ T, cnt c T ≤ 2)
    (hSm : Sm ⊆ Sp) {γ : Fin k} (hγ : γ ∈ Sp \ Sm) (d₀ : ℕ) :
    ∃ c', Rec (Sp \ Sm) c c' ∧
      (∀ d, (#Sp - #Sm) * g Sm Sp c' γ d ≤ (d - #Sm) * Gd Sm Sp c d + (#Sp - #Sm - 1)) ∧
      (#Sp - #Sm) * g Sm Sp c' γ d₀ ≤ (d₀ - #Sm) * Gd Sm Sp c d₀ := by
  classical
  set R := Sp \ Sm with hRdef
  set F : PEC G (Fin k) → Prop := fun c' => Rec R c c'
  obtain ⟨c1, hc1, hmin1⟩ := exists_min_nat F (Psi Sm Sp) ⟨c, Rec.self hopt⟩
  obtain ⟨c2, ⟨hc2, hc2Ψ⟩, hmin2⟩ := exists_min_nat (fun c' => F c' ∧ Psi Sm Sp c' = Psi Sm Sp c1)
    (fun c' => ∑ d ∈ range (k + 1), g Sm Sp c' γ d) ⟨c1, hc1, rfl⟩
  obtain ⟨cs, ⟨⟨hcs, hcsΨ⟩, hcsS⟩, hmin3⟩ := exists_min_nat
    (fun c' => (F c' ∧ Psi Sm Sp c' = Psi Sm Sp c1) ∧
      ∑ d ∈ range (k + 1), g Sm Sp c' γ d = ∑ d ∈ range (k + 1), g Sm Sp c2 γ d)
    (fun c' => g Sm Sp c' γ d₀) ⟨c2, ⟨hc2, hc2Ψ⟩, rfl⟩
  have hopts := hcs.opt
  have hn2s : ∀ T, cnt cs T ≤ 2 := by
    obtain ⟨-, π, -, e⟩ := hcs
    intro T; rw [e]; exact hn2 _
  have hγS : γ ∈ Sp := (mem_sdiff.1 hγ).1
  have hγm : γ ∉ Sm := (mem_sdiff.1 hγ).2
  -- the key consequence of minimality: for every `e`, a move from `γ` to `e` is impossible
  have hkey := minimal_move_bound d₀ hγ hcs hcsΨ hmin1 hmin2 hmin3 hcsS hopts hn2s
  -- the two conclusions
  have hB1 : ∀ e ∈ R, ∀ d, g Sm Sp cs γ d ≤ g Sm Sp cs e d + 1 := by
    intro e he d
    by_cases heγ : e = γ
    · rw [heγ]; omega
    by_contra hlt
    push Not at hlt
    have := (hkey e he heγ d (by omega)).1
    omega
  have hB2 : ∀ e ∈ R, g Sm Sp cs γ d₀ ≤ g Sm Sp cs e d₀ := by
    intro e he
    by_cases heγ : e = γ
    · rw [heγ]
    by_contra hlt
    push Not at hlt
    exact (hkey e he heγ d₀ hlt).2 rfl
  have hG : ∀ d, Gd Sm Sp cs d = Gd Sm Sp c d := by
    intro d
    have := hcs.card_filter (fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ #T = d) (fun T T' hcT h => by
      have hSm' : ∀ z ∈ Sm, z ∉ R := fun z hz h' => (mem_sdiff.1 h').2 hz
      have hSp' : ∀ z, z ∉ Sp → z ∉ R := fun z hz h' => hz (mem_sdiff.1 h').1
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun z hz => (h z (hSm' z hz)).1 (h1 hz), fun z hz => ?_, hcT ▸ h3⟩
        by_contra hzp; exact hzp (h2 ((h z (hSp' z hzp)).2 hz))
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun z hz => (h z (hSm' z hz)).2 (h1 hz), fun z hz => ?_, hcT ▸ h3⟩
        by_contra hzp; exact hzp (h2 ((h z (hSp' z hzp)).1 hz))) 1
    unfold Gd
    convert this using 2 <;> ext T <;> simp only [mem_filter, mem_univ, true_and] <;> tauto
  have hcardR : #R = #Sp - #Sm := card_sdiff_of_subset hSm
  refine ⟨cs, hcs, fun d => ?_, ?_⟩
  · have hsum := sum_g hSm cs d
    rw [hG, ← hRdef] at hsum
    have hlow : ∑ e ∈ R, g Sm Sp cs e d + (#R - 1) ≥ #R * g Sm Sp cs γ d := by
      rw [← sum_erase_add _ _ hγ]
      have : ∀ e ∈ R.erase γ, g Sm Sp cs γ d ≤ g Sm Sp cs e d + 1 := fun e he =>
        hB1 e (mem_of_mem_erase he) d
      have h2 := sum_le_sum this
      simp only [sum_add_distrib, sum_const, card_erase_of_mem hγ, smul_eq_mul, mul_one] at h2
      have : #R = (#R - 1) + 1 := by have := card_pos.2 ⟨γ, hγ⟩; omega
      rw [this, add_mul, one_mul]
      omega
    rw [← hcardR]
    omega
  · have hsum := sum_g hSm cs d₀
    rw [hG, ← hRdef] at hsum
    have : #R * g Sm Sp cs γ d₀ ≤ ∑ e ∈ R, g Sm Sp cs e d₀ := by
      have := sum_le_sum (fun e he => hB2 e he)
      rwa [sum_const, smul_eq_mul] at this
    rw [← hcardR]
    omega
end Bkls.L8

end LeanPool.BalancedEdgeColourings
