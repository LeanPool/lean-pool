/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Thm10a
public import LeanPool.BalancedEdgeColourings.Bkls.SVizing

/-!
# Balister–Kostochka–Li–Schelp 2004, Theorem 10 (part 2)

`thm10_2`: if `k ≥ Δ(G)` (and `k ≥ 3`), `n_0, n_1, n_2 ≤ 1`, `n_3, n_4, n_k ≤ 2`,
`n_{k-1} ≤ k + 1`, and `n_d ≤ (d-4)/(d-3) · min(2 C(k-3, d-3), C(k, d)) - 2` for `5 ≤ d ≤ k - 2`,
then `G` has a strong (vertex-distinguishing proper) edge colouring with `k + 1` colours.

A proper `k`-colouring exists by Vizing's theorem (`k > Δ`) or its strengthened form (`k = Δ`,
`n_Δ ≤ 2`); Lemma 9 gives an optimal one with `0, 1, 2` in every colour set used twice, and
`strong_of_three` recolours the edges of colours `0, 1, 2` by Theorem 6.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T10

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

open Classical in
omit [DecidableEq V] in
/-- A proper `k`-colouring of all edges. -/
theorem exists_total_k (hΔ : G.maxDegree ≤ k) (hkk : L9.nd G k ≤ 2) :
    ∃ c : PEC G (Fin k), Total c := by
  classical
  by_cases hlt : G.maxDegree < k
  · exact exists_total (G := G) (C := Fin k) (by rw [Fintype.card_fin]; exact hlt)
  have heq : G.maxDegree = k := by omega
  obtain ⟨c, hc⟩ := SV.class_one_of_le_two G (by
    have : (univ.filter fun v => G.degree v = G.maxDegree) = univ.filter fun v => G.degree v =
        k := by
      rw [heq]
    rw [this]; exact hkk)
  refine ⟨⟨fun u v => (c.col u v).map (Fin.cast heq), fun u v => by rw [c.col_symm],
    fun {u v γ} h => ?_, fun {u v w γ} h1 h2 => ?_⟩, fun u v huv => ?_⟩
  · obtain ⟨δ, hδ, -⟩ := Option.map_eq_some_iff.1 h
    exact c.col_adj hδ
  · obtain ⟨δ, hδ, e⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨δ', hδ', e'⟩ := Option.map_eq_some_iff.1 h2
    have : δ = δ' := Fin.cast_injective heq (e.trans e'.symm)
    subst this
    exact c.col_proper hδ hδ'
  · change (c.col u v).map _ ≠ none
    rw [ne_eq, Option.map_eq_none_iff]
    exact hc u v huv

open Classical in
omit [DecidableEq V] in
/-- **Theorem 10 (part 2).** -/
theorem thm10_2 (hk3 : 3 ≤ k) (hΔ : G.maxDegree ≤ k)
    (h012 : ∀ d, d ≤ 2 → L9.nd G d ≤ 1) (h3 : L9.nd G 3 ≤ 2) (h4 : L9.nd G 4 ≤ 2)
    (hkk : L9.nd G k ≤ 2) (hk1 : L9.nd G (k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (L9.nd G d : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) - 2) :
    ∃ c : PEC G (Fin (k + 1)), Strong c := by
  classical
  obtain ⟨c0, htot0⟩ := exists_total_k hΔ hkk
  have h0 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨c, hopt, hn2, hall⟩ := L9.lemma9 hk3 (fun v => (G.degree_le_maxDegree v).trans hΔ)
    htot0 h0 h02 h12 h012 h3 h4 hkk hk1 h6
  exact strong_of_three hopt.1 hn2 h0 h02 h12 hall
end Bkls.T10

end LeanPool.BalancedEdgeColourings
