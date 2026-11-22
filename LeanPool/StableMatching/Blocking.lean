/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.DeferredAcceptance
public import Mathlib.Data.Finset.Max

/-!
# The blocking lemma, weak Pareto optimality and strategyproofness for the men

* `Market.exists_blocks_of_rankM_lt` (**the blocking lemma** of Gale and Sotomayor): if an
  individually rational matching `μ'` makes some man strictly better off than men-proposing
  deferred acceptance, then some pair `(m, w)` blocks `μ'`, where `m` likes deferred acceptance
  at least as well as `μ'` and `w` is the partner under `μ'` of a man made strictly better off.
  When the men made better off are not mapped by `μ'` into their partners under deferred
  acceptance, the partner under deferred acceptance of a woman outside works. Otherwise we look
  at the last round in which one of these men is rejected: the woman `w` he proposes to next
  rejects, in that round, the man she held, and that man and `w` block `μ'`.
* `Market.not_forall_rankM_lt_deferredAcceptance` (**weak Pareto optimality for the men**): no
  individually rational matching makes every man strictly better off than deferred acceptance
  (A. E. Roth, *The economics of matching: stability and incentives*, Math. Oper. Res. 7 (1982),
  Theorem 6; A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and open
  questions*, Internat. J. Game Theory 36 (2008), Theorem 5).
* `Market.rankM_deferredAcceptance_le_updateMan` (**Dubins–Freedman, Roth**): truth-telling is a
  dominant strategy for the men under men-proposing deferred acceptance (L. E. Dubins,
  D. A. Freedman, *Machiavelli and the Gale–Shapley algorithm*, Amer. Math. Monthly 88 (1981);
  Roth 1982, Theorem 5; Roth 2008, Theorem 8).
-/

@[expose] public section

noncomputable section

namespace LeanPool.StableMatching

variable {M W : Type*}

namespace Market

variable {P : Market M W} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

omit [Fintype M] [DecidableEq M] in
/-- A woman a man strictly prefers to his proposal has rejected him. -/
theorem mem_of_rankM_lt_proposal {m : M} {R : Finset W} {w : W}
    (h : P.rankM m (some w) < P.rankM m (P.proposal m R)) : w ∈ R := by
  by_contra hw
  exact absurd (rankM_proposal_le hw (h.trans_le (rankM_proposal_le_none m R)).le) (not_le.2 h)

/-- The rejection of a woman happens at some round. -/
theorem exists_round_of_mem_rej {k : ℕ} {m : M} {w : W} (h : w ∈ P.rej k m) :
    ∃ j < k, w ∉ P.rej j m ∧ w ∈ P.rej (j + 1) m := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    by_cases hk : w ∈ P.rej k m
    · obtain ⟨j, hj, h1, h2⟩ := ih hk
      exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
    · exact ⟨k, Nat.lt_succ_self k, hk, h⟩

/-- **The blocking lemma, first case.** If a man made better off by `μ'` is matched by `μ'` to a
woman whose partner under deferred acceptance is not made better off, that partner and the woman
block `μ'`. -/
theorem exists_blocks_of_not_mem {μ' : M ≃. W} (hμ' : P.IsIndividuallyRational μ') {m' : M}
    {w : W} (hm' : P.rankM m' (μ' m') < P.rankM m' (P.deferredAcceptance m'))
    (hw : μ' m' = some w)
    (hout : ∀ m, P.deferredAcceptance m = some w →
      P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (μ' m)) :
    ∃ m w, P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (μ' m) ∧ P.Blocks μ' m w ∧
      ∃ m', μ' m' = some w ∧ P.rankM m' (μ' m') < P.rankM m' (P.deferredAcceptance m') := by
  have hlt : P.rankM m' (some w) < P.rankM m' (P.daMatching m') := hw ▸ hm'
  have h1 := P.isStable_daMatching.rankW_lt hlt
  have hw' : μ'.symm w = some m' := (PEquiv.eq_some_iff μ').2 hw
  have hacc : P.rankW w (some m') ≤ P.rankW w none := hw' ▸ hμ'.2 w
  obtain ⟨m₁, hm₁⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le h1 hacc)
  have hμm₁ : P.deferredAcceptance m₁ = some w := (PEquiv.eq_some_iff P.daMatching).1 hm₁
  have hle := hout m₁ hμm₁
  have hne : m₁ ≠ m' := by
    rintro rfl
    exact absurd hle (not_le.2 hm')
  have hne' : μ' m₁ ≠ some w := fun h ↦ hne (μ'.inj h hw)
  refine ⟨m₁, w, hle, ⟨?_, ?_⟩, m', hw, hm'⟩
  · rw [← hμm₁]
    exact P.rankM_lt_of_le_of_ne hle (hμm₁ ▸ hne'.symm)
  · rw [hw']
    rwa [hm₁] at h1

/-- **The blocking lemma, second case.** Suppose every man made better off by `μ'` has received
his last rejection by round `t + 1`, that `m⋆` is made better off and received a rejection in
round `t`, and that his final partner `w` is the partner under `μ'` of a man `m_w` made better
off. The man `w` held in round `t` and `w` block `μ'`. -/
theorem exists_blocks_of_last_round {μ' : M ≃. W} (hμ' : P.IsIndividuallyRational μ')
    {t : ℕ} (hT : ∀ m, P.rankM m (μ' m) < P.rankM m (P.deferredAcceptance m) →
      P.rej (t + 1) m = P.finalRej m)
    {mstar : M} (hstar : P.rankM mstar (μ' mstar) < P.rankM mstar (P.deferredAcceptance mstar))
    (hstar' : P.rej t mstar ≠ P.finalRej mstar) {w : W}
    (hw : P.deferredAcceptance mstar = some w) {mw : M} (hmw : μ' mw = some w)
    (hmw' : P.rankM mw (μ' mw) < P.rankM mw (P.deferredAcceptance mw)) :
    ∃ m w, P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (μ' m) ∧ P.Blocks μ' m w ∧
      ∃ m', μ' m' = some w ∧ P.rankM m' (μ' m') < P.rankM m' (P.deferredAcceptance m') := by
  -- the woman `m⋆` proposes to in round `t` is not `w`
  have hsub : P.rej t mstar ⊆ P.rej (t + 1) mstar := rej_mono (Nat.le_succ t) mstar
  obtain ⟨w', hw'1, hw'2⟩ : ∃ w', w' ∈ P.rej (t + 1) mstar ∧ w' ∉ P.rej t mstar := by
    by_contra h
    push Not at h
    exact hstar' ((Finset.Subset.antisymm hsub h).trans (hT mstar hstar))
  rw [rej_succ] at hw'1
  have hpw' := (mem_step_iff.1 hw'1).resolve_left hw'2 |>.1
  have hww' : w' ≠ w := by
    rintro rfl
    have : w' ∈ P.finalRej mstar := by rw [← hT mstar hstar, rej_succ]; exact hw'1
    exact not_mem_of_proposal_eq_some hw this
  -- the man `w` holds in round `t` is better for her than `m_w`
  have hwm : μ'.symm w = some mw := (PEquiv.eq_some_iff μ').2 hmw
  have hacc : P.rankW w (some mw) ≤ P.rankW w none := hwm ▸ hμ'.2 w
  have hwRf : w ∈ P.rej (t + 1) mw := by
    rw [hT mw hmw']
    exact mem_of_rankM_lt_proposal (hmw ▸ hmw')
  have hheld : P.rankW w (P.held (P.proposals (P.rej t)) w) < P.rankW w (some mw) := by
    by_cases h : w ∈ P.rej t mw
    · exact rankW_held_lt_of_mem_rej h
    · rw [rej_succ] at hwRf
      obtain ⟨h1, h2⟩ := (mem_step_iff.1 hwRf).resolve_left h
      exact P.rankW_lt_of_le_of_ne (rankW_held_le h1 hacc) h2
  obtain ⟨h, hh⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le hheld hacc)
  rw [hh] at hheld
  have hph : P.proposal h (P.rej t h) = some w :=
    (eq_some_of_held_eq_some hh : P.proposals (P.rej t) h = some w)
  have hhne : h ≠ mstar := by
    rintro rfl
    rw [hph, Option.some_injective _ |>.eq_iff] at hpw'
    exact hww' hpw'.symm
  have hph' : P.proposal h (P.rej (t + 1) h) = some w := by
    rw [rej_succ]
    exact proposal_step_of_held hh
  -- `w` eventually rejects the man she holds
  have hwh : w ∈ P.finalRej h := by
    by_contra hn
    have := proposal_eq_of_subset (rej_subset_finalRej (t + 1) h) hph' hn
    exact hhne (P.daMatching.inj (this : P.daMatching h = some w) hw)
  have hnotimp : P.rankM h (P.deferredAcceptance h) ≤ P.rankM h (μ' h) := by
    by_contra himp
    have := hT h (not_le.1 himp)
    rw [this] at hph'
    exact not_mem_of_proposal_eq_some hph' hwh
  refine ⟨h, w, hnotimp, ⟨?_, ?_⟩, mw, hmw, hmw'⟩
  · refine lt_of_lt_of_le ?_ hnotimp
    rw [← hph', deferredAcceptance_eq]
    refine P.rankM_lt_of_le_of_ne (rankM_proposal_mono (rej_subset_finalRej (t + 1) h)) ?_
    rw [hph']
    intro h'
    exact not_mem_of_proposal_eq_some h'.symm hwh
  · rw [hwm]
    exact hheld

/-- **The blocking lemma** (Gale–Sotomayor). If an individually rational matching `μ'` makes
some man strictly better off than deferred acceptance, then some pair `(m, w)` blocks `μ'`,
where `m` likes deferred acceptance at least as well as `μ'`, and `w` is the partner under `μ'`
of a man made strictly better off. -/
theorem exists_blocks_of_rankM_lt {μ' : M ≃. W} (hμ' : P.IsIndividuallyRational μ') {m₀ : M}
    (hm₀ : P.rankM m₀ (μ' m₀) < P.rankM m₀ (P.deferredAcceptance m₀)) :
    ∃ m w, P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (μ' m) ∧ P.Blocks μ' m w ∧
      ∃ m', μ' m' = some w ∧ P.rankM m' (μ' m') < P.rankM m' (P.deferredAcceptance m') := by
  set S := Finset.univ.filter fun m ↦ P.rankM m (μ' m) < P.rankM m (P.deferredAcceptance m)
    with hS
  have hmemS : ∀ m, m ∈ S ↔ P.rankM m (μ' m) < P.rankM m (P.deferredAcceptance m) := by
    simp [hS]
  have himp : ∀ m, m ∈ S → ∃ w, μ' m = some w := fun m hm ↦
    eq_some_of_rankM_lt_none (lt_of_lt_of_le ((hmemS m).1 hm) (rankM_proposal_le_none _ _))
  by_cases hc : ∃ m' w, m' ∈ S ∧ μ' m' = some w ∧
      ∀ m, P.deferredAcceptance m = some w → P.rankM m (P.deferredAcceptance m) ≤ P.rankM m (μ' m)
  · obtain ⟨m', w, hm', hw, hout⟩ := hc
    exact exists_blocks_of_not_mem hμ' ((hmemS m').1 hm') hw hout
  push Not at hc
  -- the men of `S` are mapped by `μ'` onto their partners under deferred acceptance
  set f : M → Option M := fun m ↦ (μ' m).bind P.daMatching.symm with hf
  have hmaps : ∀ m ∈ S, ∃ m'' ∈ S, f m = some m'' := fun m hm ↦ by
    obtain ⟨w, hw⟩ := himp m hm
    obtain ⟨m'', hm'', hle⟩ := hc m w hm hw
    exact ⟨m'', (hmemS m'').2 hle, by
      simp [hf, hw, (PEquiv.eq_some_iff P.daMatching).2 hm'']⟩
  have hinj : ∀ a₁ a₂ b, f a₁ = some b → f a₂ = some b → a₁ = a₂ := fun a₁ a₂ b h₁ h₂ ↦ by
    obtain ⟨w₁, hw₁, hb₁⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨w₂, hw₂, hb₂⟩ := Option.bind_eq_some_iff.1 h₂
    have : w₁ = w₂ := P.daMatching.symm.inj hb₁ hb₂
    subst this
    exact μ'.inj hw₁ hw₂
  have hsurj := exists_eq_some_of_injOn hmaps hinj hmaps hinj
  -- the last round in which a man of `S` is rejected
  have hex : ∀ m : M, ∃ k, P.rej k m = P.finalRej m := fun _ ↦ ⟨_, rfl⟩
  obtain ⟨mstar, hmstar, hmax⟩ :=
    S.exists_max_image (fun m ↦ Nat.find (hex m)) ⟨m₀, (hmemS m₀).2 hm₀⟩
  have hpos : Nat.find (hex mstar) ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec (hex mstar)
    rw [h0, rej_zero] at h1
    obtain ⟨w, hw⟩ := himp mstar hmstar
    have hlt := (hmemS mstar).1 hmstar
    rw [hw, deferredAcceptance_eq] at hlt
    have hmem := mem_of_rankM_lt_proposal hlt
    rw [← h1] at hmem
    simp at hmem
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hT : ∀ m, P.rankM m (μ' m) < P.rankM m (P.deferredAcceptance m) →
      P.rej (t + 1) m = P.finalRej m := by
    intro m hm
    have hle : Nat.find (hex m) ≤ t + 1 := by
      have := hmax m ((hmemS m).2 hm)
      omega
    refine Finset.Subset.antisymm (rej_subset_finalRej _ m) ?_
    rw [← Nat.find_spec (hex m)]
    exact rej_mono hle m
  have hstar' : P.rej t mstar ≠ P.finalRej mstar :=
    Nat.find_min (hex mstar) (by omega)
  obtain ⟨a, ha, hab⟩ := hsurj mstar hmstar
  obtain ⟨w, hw, hwb⟩ := Option.bind_eq_some_iff.1 hab
  exact exists_blocks_of_last_round hμ' hT ((hmemS mstar).1 hmstar) hstar'
    ((PEquiv.eq_some_iff P.daMatching).1 hwb) hw ((hmemS a).1 ha)

/-- **Roth.** If there is at least one man, no individually rational matching makes every man
strictly better off than deferred acceptance. -/
theorem not_forall_rankM_lt_deferredAcceptance [Nonempty M] {ν : M ≃. W}
    (hν : P.IsIndividuallyRational ν) :
    ¬ ∀ m, P.rankM m (ν m) < P.rankM m (P.deferredAcceptance m) := by
  intro h
  obtain ⟨m, -, hle, -⟩ := exists_blocks_of_rankM_lt hν (h (Classical.arbitrary M))
  exact absurd (h m) (not_lt.2 hle)

/-- **Dubins–Freedman, Roth.** No man obtains, by stating other strict preferences, a partner
he truly prefers to the one deferred acceptance gives him. -/
theorem rankM_deferredAcceptance_le_updateMan (m : M) (r : Option W → ℕ)
    (hr : Function.Injective r) :
    P.rankM m (P.deferredAcceptance m) ≤
      P.rankM m ((P.updateMan m r hr).deferredAcceptance m) := by
  set P' := P.updateMan m r hr
  set μ' := P'.daMatching
  have hμ' : P'.IsStable μ' := P'.isStable_daMatching
  by_contra hlt
  rw [not_le] at hlt
  have hIR : P.IsIndividuallyRational μ' := by
    refine ⟨fun m' ↦ ?_, fun w ↦ hμ'.1.2 w⟩
    by_cases hm' : m' = m
    · subst hm'
      exact (lt_of_lt_of_le hlt (rankM_proposal_le_none _ _)).le
    · have := hμ'.1.1 m'
      rwa [updateMan_rankM_of_ne hm'] at this
  obtain ⟨m₁, w₁, hle, hb, -⟩ := exists_blocks_of_rankM_lt hIR hlt
  have hne : m₁ ≠ m := by
    rintro rfl
    exact absurd hlt (not_lt.2 hle)
  refine hμ'.2 m₁ w₁ ⟨?_, hb.2⟩
  rw [updateMan_rankM_of_ne hne]
  exact hb.1

end Market

end LeanPool.StableMatching
