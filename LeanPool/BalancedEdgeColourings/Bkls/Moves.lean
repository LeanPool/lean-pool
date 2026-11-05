/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Lemma2

/-!
# Injectivity of the named partner in Lemma 2

For colours `a ≠ b` and a set `S` with `n_{i S} < n_S`, the swap of Lemma 2 starts at the vertex of
`V_S` of rank `n_{i S}` and ends at the other unmatched end of its `J ∪ K` path; `partner S`,
constructed in `Lemma2`, is
the colour set of that end. `lemma2_one'` is Lemma 2 (difference one) with the other pair equal to
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
