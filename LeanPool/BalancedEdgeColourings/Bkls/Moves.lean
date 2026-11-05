/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Lemma2

/-!
# Lemma 2 with a named partner

For colours `a ≠ b` and a set `S` with `n_{i S} < n_S`, the swap of Lemma 2 starts at the vertex of
`V_S` of rank `n_{i S}` and ends at the other unmatched end of its `J ∪ K` path; `partner S` is the
colour set of that end. `lemma2_one'` is Lemma 2 (difference one) with the other pair equal to
`partner S`, and `partner_inj`: on sets with `n_S = n_{i S} + 1`, `partner` is injective (the end of
a path determines its start).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
/-- The start of the swap: the vertex of `V_S` of rank `n_{i S}`. -/
noncomputable def startV (c : PEC G (Fin k)) (a b : Fin k) {S : Finset (Fin k)}
    (h : cnt c (swapSet a b S) < cnt c S) : V := (exists_rank c h).choose

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem startV_spec {S : Finset (Fin k)} (h : cnt c (swapSet a b S) < cnt c S) :
    colSet c (startV c a b h) = S ∧ rank c (startV c a b h) = cnt c (swapSet a b S) := by
  classical
  exact (exists_rank c h).choose_spec

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem startV_end {S : Finset (Fin k)} (h : cnt c (swapSet a b S) < cnt c S) :
    IsEnd c a b (startV c a b h) := by
  classical
  have hSne : swapSet a b S ≠ S := fun e => by rw [e] at h; exact lt_irrefl _ h
  unfold IsEnd
  rw [(startV_spec h).1]
  by_contra hc
  apply hSne
  apply swapSet_eq_of_iff
  tauto

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem startV_unm {S : Finset (Fin k)} (h : cnt c (swapSet a b S) < cnt c S) :
    ¬ JMatched c a b (startV c a b h) := by
  classical
  unfold JMatched
  rw [(startV_spec h).2, (startV_spec h).1]
  exact lt_irrefl _

open Classical in
/-- The other end. -/
noncomputable def endV (c : PEC G (Fin k)) {a b : Fin k} (hab : a ≠ b) {S : Finset (Fin k)}
    (h : cnt c (swapSet a b S) < cnt c S) : V :=
  (exists_unique_other_end hab (startV_end h) (startV_unm h)).choose

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem endV_spec (hab : a ≠ b) {S : Finset (Fin k)} (h : cnt c (swapSet a b S) < cnt c S) :
    endV c hab h ≠ startV c a b h ∧ (jkGraph c a b).Reachable (startV c a b h) (endV c hab h) ∧
      IsEnd c a b (endV c hab h) ∧ ¬ JMatched c a b (endV c hab h) ∧
      ∀ w, w ≠ startV c a b h → (jkGraph c a b).Reachable (startV c a b h) w →
        ¬ JMatched c a b w → w = endV c hab h := by
  classical
  exact (exists_unique_other_end hab (startV_end h) (startV_unm h)).choose_spec

open Classical in
/-- The partner of `S`: the colour set of the other end. -/
noncomputable def partner (c : PEC G (Fin k)) {a b : Fin k} (hab : a ≠ b) (S : Finset (Fin k)) :
    Finset (Fin k) :=
  if h : cnt c (swapSet a b S) < cnt c S then colSet c (endV c hab h) else S

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem partner_eq (hab : a ≠ b) {S : Finset (Fin k)} (h : cnt c (swapSet a b S) < cnt c S) :
    partner c hab S = colSet c (endV c hab h) := by
  classical
  rw [partner, dite_eq_left h]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The swap of Lemma 2, with the named partner. -/
theorem lemma2_swap' (hab : a ≠ b) (htot : Total c) {S : Finset (Fin k)}
    (hlt : cnt c (swapSet a b S) < cnt c S) :
    cnt c (swapSet a b (partner c hab S)) < cnt c (partner c hab S) ∧
      partner c hab S ≠ swapSet a b S ∧
      (partner c hab S = S → cnt c (swapSet a b S) + 2 ≤ cnt c S) ∧
      ∃ c' : PEC G (Fin k), Total c' ∧ ∀ T,
        cnt c' T + ind S T + ind (partner c hab S) T =
          cnt c T + ind (swapSet a b S) T + ind (swapSet a b (partner c hab S)) T := by
  classical
  have hue := startV_end hlt
  have hm := startV_unm hlt
  obtain ⟨hu, hur⟩ := startV_spec hlt
  obtain ⟨hne, hr, hue', hum, huniq⟩ := endV_spec hab hlt
  obtain ⟨c', htot', hcnt⟩ := exists_swap hab htot hue hm hne hr hum huniq
  rw [partner_eq hab hlt]
  generalize startV c a b hlt = u at *
  generalize endV c hab hlt = u' at *
  have hlt' : cnt c (swapSet a b (colSet c u')) < cnt c (colSet c u') := by
    have := rank_lt_cnt c u'
    unfold JMatched at hum
    omega
  refine ⟨hlt', fun h => ?_, fun h => ?_, c', htot', fun T => ?_⟩
  · rw [h, swapSet_swapSet] at hlt'
    exact lt_asymm hlt hlt'
  · have h1 := rank_lt_cnt c u'
    have h2 : rank c u' ≠ rank c u := fun e => hne (rank_injOn c (h.trans hu.symm) e)
    unfold JMatched at hum
    rw [h] at h1 hum
    omega
  · have := hcnt T; rw [hu] at this; exact this

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, difference one, with the named partner.** -/
theorem lemma2_one' (hopt : IsOptimal c) (hab : a ≠ b) {S : Finset (Fin k)}
    (h : cnt c S = cnt c (swapSet a b S) + 1) :
    partner c hab S ≠ S ∧ partner c hab S ≠ swapSet a b S ∧
      swapSet a b (partner c hab S) ≠ S ∧ swapSet a b (partner c hab S) ≠ swapSet a b S ∧
      cnt c (partner c hab S) = cnt c (swapSet a b (partner c hab S)) + 1 ∧
      ∃ c' : PEC G (Fin k), IsOptimal c' ∧ cnt c' S = cnt c (swapSet a b S) ∧
        cnt c' (swapSet a b S) = cnt c S ∧
        cnt c' (partner c hab S) = cnt c (swapSet a b (partner c hab S)) ∧
        cnt c' (swapSet a b (partner c hab S)) = cnt c (partner c hab S) ∧
        ∀ X, X ≠ S → X ≠ swapSet a b S → X ≠ partner c hab S →
          X ≠ swapSet a b (partner c hab S) → cnt c' X = cnt c X := by
  classical
  have hSne : swapSet a b S ≠ S := fun e => by rw [e] at h; omega
  obtain ⟨hlt', hS'ne, hSS, c', htot', hcnt⟩ := lemma2_swap' hab hopt.1 (S := S) (by omega)
  set S' := partner c hab S
  have hS' : S' ≠ S := fun e => by have := hSS e; omega
  have h1 : S' ≠ swapSet a b S' := fun e => by rw [← e] at hlt'; exact lt_irrefl _ hlt'
  obtain ⟨h2, h3⟩ := four_distinct hSne h1 hS' hS'ne
  obtain ⟨e1, e2, e3, e4, e5⟩ := counts_four hSne h1 hS' hS'ne hcnt
  have hsum := sum_sq_update4 (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
    (Ne.symm hSne) (Ne.symm hS') (Ne.symm h2) (Ne.symm hS'ne) (Ne.symm h3) h1 e1 e2 e3 e4 e5
  have hle := cost_le_of_opt hopt htot'
  have hlt'' : (cnt c (swapSet a b S') : ℤ) + 1 ≤ cnt c S' := by exact_mod_cast hlt'
  have hh : (cnt c S : ℤ) = cnt c (swapSet a b S) + 1 := by exact_mod_cast h
  have hS'1 : (cnt c S' : ℤ) = cnt c (swapSet a b S') + 1 := by linarith
  refine ⟨hS', hS'ne, h2, h3, by exact_mod_cast hS'1, c',
    isOptimal_of_cost_eq hopt htot' (by rw [hsum]; linarith), by omega, by omega, by omega,
    by omega, fun X f1 f2 f3 f4 => by have := e5 X f1 f2 f3 f4; omega⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The partner determines the set.** -/
theorem partner_inj (hopt : IsOptimal c) (hab : a ≠ b) {S T : Finset (Fin k)}
    (hS : cnt c S = cnt c (swapSet a b S) + 1) (hT : cnt c T = cnt c (swapSet a b T) + 1)
    (he : partner c hab S = partner c hab T) : S = T := by
  classical
  have hSl : cnt c (swapSet a b S) < cnt c S := by omega
  have hTl : cnt c (swapSet a b T) < cnt c T := by omega
  obtain ⟨-, -, -, -, hU, -⟩ := lemma2_one' hopt hab hS
  set U := partner c hab S with hUdef
  obtain ⟨hneS, hrS, heS, humS, -⟩ := endV_spec hab hSl
  obtain ⟨hneT, hrT, heT, humT, -⟩ := endV_spec hab hTl
  have hcS : colSet c (endV c hab hSl) = U := (partner_eq hab hSl).symm
  have hcT : colSet c (endV c hab hTl) = U := by rw [he]; exact (partner_eq hab hTl).symm
  -- both ends are the vertex of `V_U` of rank `n_{i U}`
  have hrank : ∀ v, colSet c v = U → ¬ JMatched c a b v → rank c v = cnt c (swapSet a b U) := by
    intro v hv hm
    have := rank_lt_cnt c v
    unfold JMatched at hm
    rw [hv] at this hm
    omega
  have hvv : endV c hab hSl = endV c hab hTl :=
    rank_injOn c (hcS.trans hcT.symm) ((hrank _ hcS humS).trans (hrank _ hcT humT).symm)
  -- the other end from it is unique
  set w := endV c hab hSl
  obtain ⟨w', -, -, -, -, huniq⟩ := exists_unique_other_end hab heS humS
  have h1 : startV c a b hSl = w' := huniq _ (Ne.symm hneS) hrS.symm (startV_unm hSl)
  have h2 : startV c a b hTl = w' := huniq _ (by rw [hvv]; exact Ne.symm hneT)
    (by rw [hvv]; exact hrT.symm) (startV_unm hTl)
  rw [← (startV_spec hSl).1, ← (startV_spec hTl).1, h1, h2]
end Bkls

end LeanPool.BalancedEdgeColourings
