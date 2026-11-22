/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.DeferredAcceptance

/-!
# Optimality of deferred acceptance

* `Market.rankM_deferredAcceptance_le`: every man likes the outcome of men-proposing deferred
  acceptance at least as well as his partner at any stable matching (D. Gale, L. S. Shapley,
  *College admissions and the stability of marriage*, Amer. Math. Monthly 69 (1962),
  Theorem 2; A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and open
  questions*, Internat. J. Game Theory 36 (2008), Theorem 2). The route: no man is ever
  rejected by a woman who is his partner at some stable matching.
* `Market.eq_daMatching_of_forall_rankM_le`: the men-optimal stable matching is unique.
* `Market.rankW_le_of_forall_rankM_le`: the opposition of interests between the two sides:
  if every man likes a stable matching `μ` at least as well as a stable matching `ν`, then
  every woman likes `ν` at least as well as `μ` (Knuth 1976).
* Deferred acceptance with the women proposing is the algorithm of the role swap:
  `Market.exists_isStable_woman_eq_deferredAcceptance_swap`; it is women-optimal and
  men-pessimal (`Market.rankW_deferredAcceptance_swap_le`,
  `Market.rankM_le_swap_daMatching_symm`).
-/

@[expose] public section

noncomputable section

namespace LeanPool.StableMatching

variable {M W : Type*}

namespace Market

variable {P : Market M W} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- No man is ever rejected by his partner at a stable matching. -/
theorem not_mem_rej_of_isStable {ν : M ≃. W} (hν : P.IsStable ν) (k : ℕ) {m : M} {w : W}
    (hmw : ν m = some w) : w ∉ P.rej k m := by
  induction k generalizing m w with
  | zero => simp
  | succ k ih =>
    rw [rej_succ]
    intro hw
    rcases mem_step_iff.1 hw with h | ⟨h1, h2⟩
    · exact ih hmw h
    have hwm : ν.symm w = some m := (PEquiv.eq_some_iff ν).2 hmw
    have hacc : P.rankW w (some m) ≤ P.rankW w none := by
      simpa [hwm] using hν.1.2 w
    have hlt : P.rankW w (P.held (P.proposals (P.rej k)) w) < P.rankW w (some m) :=
      P.rankW_lt_of_le_of_ne (rankW_held_le h1 hacc) h2
    obtain ⟨m', hm'⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le hlt hacc)
    rw [hm'] at hlt h2
    have hprop : P.proposal m' (P.rej k m') = some w :=
      (eq_some_of_held_eq_some hm' : P.proposals (P.rej k) m' = some w)
    have hne : ν m' ≠ some w := by
      intro h'
      have : m' = m := ν.inj h' hmw
      exact h2 (by rw [this])
    have hle : P.rankM m' (some w) ≤ P.rankM m' (ν m') := by
      rw [← hprop]
      cases hν' : ν m' with
      | none => exact rankM_proposal_le_none _ _
      | some w' => exact rankM_proposal_le (ih hν') (by simpa [hν'] using hν.1.1 m')
    exact hν.2 m' w ⟨P.rankM_lt_of_le_of_ne hle hne.symm, by rw [hwm]; exact hlt⟩

/-- **Gale–Shapley.** Every man likes the outcome of deferred acceptance at least as well as
his partner at any stable matching. -/
theorem rankM_deferredAcceptance_le {ν : M ≃. W} (hν : P.IsStable ν) (m : M) :
    P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (ν m) := by
  rw [deferredAcceptance_eq]
  cases hm : ν m with
  | none => exact rankM_proposal_le_none _ _
  | some w =>
    exact rankM_proposal_le (not_mem_rej_of_isStable hν _ hm) (by simpa [hm] using hν.1.1 m)

/-- The men-optimal stable matching is unique: a stable matching that every man likes at least
as well as any stable matching is the outcome of deferred acceptance. -/
theorem eq_daMatching_of_forall_rankM_le {μ : M ≃. W} (hμ : P.IsStable μ)
    (h : ∀ ν : M ≃. W, P.IsStable ν → ∀ m, P.rankM m (μ m) ≤ P.rankM m (ν m)) :
    μ = P.daMatching := by
  ext1 m
  exact P.rankM_injective m (le_antisymm (h _ P.isStable_daMatching m)
    (rankM_deferredAcceptance_le hμ m))

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] in
/-- **Opposition of interests.** If every man likes a matching `μ` at least as well as a stable
matching `ν`, then every woman likes `ν` at least as well as `μ`. -/
theorem rankW_le_of_forall_rankM_le {μ ν : M ≃. W} (hν : P.IsStable ν)
    (h : ∀ m, P.rankM m (μ m) ≤ P.rankM m (ν m)) (w : W) :
    P.rankW w (ν.symm w) ≤ P.rankW w (μ.symm w) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le hlt (hν.1.2 w))
  have hμm : μ m = some w := (PEquiv.eq_some_iff μ).1 hm
  have hne : ν m ≠ some w := fun h' ↦ by
    rw [(PEquiv.eq_some_iff ν).2 h', hm] at hlt
    exact lt_irrefl _ hlt
  have h1 : P.rankM m (some w) < P.rankM m (ν m) :=
    P.rankM_lt_of_le_of_ne (hμm ▸ h m) hne.symm
  exact hν.2 m w ⟨h1, hm ▸ hlt⟩

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] in
/-- The opposition of interests with the roles of the two sides exchanged. -/
theorem rankM_le_of_forall_rankW_le {μ ν : M ≃. W} (hν : P.IsStable ν)
    (h : ∀ w, P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w)) (m : M) :
    P.rankM m (ν m) ≤ P.rankM m (μ m) := by
  have := rankW_le_of_forall_rankM_le (P := P.swap) (μ := μ.symm) (ν := ν.symm)
    (isStable_swap_iff.2 hν) h m
  simpa using this

/-! ### Women proposing -/

/-- Deferred acceptance with the women proposing, the algorithm of the role swap, returns the
women's side of a stable matching. -/
theorem exists_isStable_woman_eq_deferredAcceptance_swap :
    ∃ μ : M ≃. W, ⇑μ.symm = P.swap.deferredAcceptance ∧ P.IsStable μ :=
  ⟨P.swap.daMatching.symm, by simp [coe_daMatching],
    isStable_swap_iff.1 (by simpa using P.swap.isStable_daMatching)⟩

/-- Every woman likes the outcome of women-proposing deferred acceptance at least as well as her
partner at any stable matching. -/
theorem rankW_deferredAcceptance_swap_le {ν : M ≃. W} (hν : P.IsStable ν) (w : W) :
    P.rankW w (P.swap.deferredAcceptance w) ≤ P.rankW w (ν.symm w) :=
  rankM_deferredAcceptance_le (P := P.swap) (isStable_swap_iff.2 hν) w

/-- Every man likes any stable matching at least as well as the outcome of women-proposing
deferred acceptance: it is the least element of the men's order on stable matchings. -/
theorem rankM_le_swap_daMatching_symm {ν : M ≃. W} (hν : P.IsStable ν) (m : M) :
    P.rankM m (ν m) ≤ P.rankM m (P.swap.daMatching.symm m) := by
  refine rankM_le_of_forall_rankW_le hν (fun w ↦ ?_) m
  simpa [coe_daMatching] using rankW_deferredAcceptance_swap_le hν w

end Market

end LeanPool.StableMatching
