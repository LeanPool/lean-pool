/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.Basic
public import LeanPool.StableMatching.Auxiliary
public import Mathlib.Data.Fintype.EquivFin

/-!
# The lattice of stable matchings

Fix two stable matchings `μ` and `ν`. The men who strictly prefer `μ` to `ν` and the women who
strictly prefer `ν` to `μ` are in bijection both through `μ` and through `ν`
(`Market.exists_eq_some_of_rankW_lt`, `Market.exists_symm_eq_some_of_rankM_lt`): each map sends
the first set into the second injectively, and a counting argument makes it onto. From this we
prove:

* `Market.exists_isStable_manSup` and `Market.exists_isStable_manInf` (**Conway's lattice**):
  giving each man the better (respectively the worse) of his two partners defines a stable
  matching, in which each woman gets the worse (respectively the better) of hers (A. E. Roth,
  *Deferred acceptance algorithms: history, theory, practice, and open questions*, Internat. J.
  Game Theory 36 (2008), Theorem 3, attributed by D. E. Knuth, *Mariages stables* (1976), to
  J. H. Conway);
* `Market.man_eq_none_iff_of_isStable` and `Market.woman_eq_none_iff_of_isStable`
  (**McVitie–Wilson**): the same men and the same women are single at every stable matching
  (D. G. McVitie, L. B. Wilson, *Stable marriage assignment for unequal sets*, BIT 10 (1970);
  Roth 2008, Theorem 4).

Together with `Market.rankM_deferredAcceptance_le` and `Market.rankM_le_swap_daMatching_symm`, the
stable matchings form a lattice for the men's common order, whose greatest element is the
outcome of men-proposing deferred acceptance and whose least element is the outcome of
women-proposing deferred acceptance.
-/

@[expose] public section

namespace LeanPool.StableMatching

variable {M W : Type*}

namespace Market

variable {P : Market M W} {μ ν : M ≃. W}

/-- A man who strictly prefers `μ` to `ν` is matched by `μ` to a woman who strictly prefers `ν`
to `μ`. -/
theorem exists_eq_some_of_rankM_lt (hν : P.IsStable ν) {m : M}
    (hm : P.rankM m (μ m) < P.rankM m (ν m)) :
    ∃ w, μ m = some w ∧ P.rankW w (ν.symm w) < P.rankW w (μ.symm w) := by
  obtain ⟨w, hw⟩ := eq_some_of_rankM_lt_none (lt_of_lt_of_le hm (hν.1.1 m))
  rw [hw] at hm
  refine ⟨w, hw, ?_⟩
  rw [(PEquiv.eq_some_iff μ).2 hw]
  exact hν.rankW_lt hm

/-- A woman who strictly prefers `ν` to `μ` is matched by `ν` to a man who strictly prefers `μ`
to `ν`. -/
theorem exists_symm_eq_some_of_rankW_lt (hμ : P.IsStable μ) {w : W}
    (hw : P.rankW w (ν.symm w) < P.rankW w (μ.symm w)) :
    ∃ m, ν.symm w = some m ∧ P.rankM m (μ m) < P.rankM m (ν m) := by
  obtain ⟨m, hm⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le hw (hμ.1.2 w))
  rw [hm] at hw
  refine ⟨m, hm, ?_⟩
  rw [(PEquiv.eq_some_iff ν).1 hm]
  exact hμ.rankM_lt hw

variable [Finite M] [Finite W]

/-- **The counting step.** A woman who strictly prefers `ν` to `μ` is matched by `μ` to a man
who strictly prefers `μ` to `ν`. -/
theorem exists_eq_some_of_rankW_lt (hμ : P.IsStable μ) (hν : P.IsStable ν) {w : W}
    (hw : P.rankW w (ν.symm w) < P.rankW w (μ.symm w)) :
    ∃ m, μ m = some w ∧ P.rankM m (μ m) < P.rankM m (ν m) := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  obtain ⟨m, hm, hmw⟩ := exists_eq_some_of_injOn
    (s := Finset.univ.filter fun m ↦ P.rankM m (μ m) < P.rankM m (ν m))
    (t := Finset.univ.filter fun w ↦ P.rankW w (ν.symm w) < P.rankW w (μ.symm w))
    (f := μ) (g := ν.symm)
    (fun m hm ↦ by
      obtain ⟨w, hw, h⟩ := exists_eq_some_of_rankM_lt hν (Finset.mem_filter.1 hm).2
      exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ w, h⟩, hw⟩)
    (fun _ _ _ h₁ h₂ ↦ μ.inj h₁ h₂)
    (fun w hw ↦ by
      obtain ⟨m, hm, h⟩ := exists_symm_eq_some_of_rankW_lt hμ (Finset.mem_filter.1 hw).2
      exact ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ m, h⟩, hm⟩)
    (fun _ _ _ h₁ h₂ ↦ ν.symm.inj h₁ h₂) w (Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩)
  exact ⟨m, hmw, (Finset.mem_filter.1 hm).2⟩

/-- **The counting step.** A man who strictly prefers `μ` to `ν` is the partner under `ν` of a
woman who strictly prefers `ν` to `μ`. -/
theorem exists_symm_eq_some_of_rankM_lt (hμ : P.IsStable μ) (hν : P.IsStable ν) {m : M}
    (hm : P.rankM m (μ m) < P.rankM m (ν m)) :
    ∃ w, ν.symm w = some m ∧ P.rankW w (ν.symm w) < P.rankW w (μ.symm w) := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  obtain ⟨w, hw, hwm⟩ := exists_eq_some_of_injOn
    (s := Finset.univ.filter fun w ↦ P.rankW w (ν.symm w) < P.rankW w (μ.symm w))
    (t := Finset.univ.filter fun m ↦ P.rankM m (μ m) < P.rankM m (ν m))
    (f := ν.symm) (g := μ)
    (fun w hw ↦ by
      obtain ⟨m, hm, h⟩ := exists_symm_eq_some_of_rankW_lt hμ (Finset.mem_filter.1 hw).2
      exact ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ m, h⟩, hm⟩)
    (fun _ _ _ h₁ h₂ ↦ ν.symm.inj h₁ h₂)
    (fun m hm ↦ by
      obtain ⟨w, hw, h⟩ := exists_eq_some_of_rankM_lt hν (Finset.mem_filter.1 hm).2
      exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ w, h⟩, hw⟩)
    (fun _ _ _ h₁ h₂ ↦ μ.inj h₁ h₂) m (Finset.mem_filter.2 ⟨Finset.mem_univ m, hm⟩)
  exact ⟨w, hwm, (Finset.mem_filter.1 hw).2⟩

/-! ### Conway's lattice -/

/-- The man-side join is the woman-side meet: the woman a man gets when taking the better of
his two partners is the one who, taking the worse of her two partners, gets him. -/
theorem manSup_eq_some_iff (hμ : P.IsStable μ) (hν : P.IsStable ν) (m : M) (w : W) :
    (if P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w) then ν.symm w else μ.symm w) = some m ↔
      (if P.rankM m (μ m) ≤ P.rankM m (ν m) then μ m else ν m) = some w := by
  constructor
  · intro h
    split_ifs at h with hle
    · have hνm : ν m = some w := (PEquiv.eq_some_iff ν).1 h
      split_ifs with hm
      · by_cases heq : μ m = ν m
        · rw [heq, hνm]
        · obtain ⟨w', hw', hB⟩ :=
            exists_symm_eq_some_of_rankM_lt hμ hν (P.rankM_lt_of_le_of_ne hm heq)
          have : w' = w := by
            have := (PEquiv.eq_some_iff ν).1 hw'
            rw [hνm] at this
            exact (Option.some_injective _ this).symm
          subst this
          exact absurd hle (not_le.2 hB)
      · exact hνm
    · have hμm : μ m = some w := (PEquiv.eq_some_iff μ).1 h
      obtain ⟨m', hm', hA⟩ := exists_eq_some_of_rankW_lt hμ hν (not_le.1 hle)
      have : m' = m := μ.inj hm' hμm
      subst this
      rw [ite_eq_left_of_eq_true _ _ (eq_true hA.le), hμm]
  · intro h
    split_ifs at h with hm
    · have hμw : μ.symm w = some m := (PEquiv.eq_some_iff μ).2 h
      by_cases heq : μ m = ν m
      · have hνw : ν.symm w = some m := (PEquiv.eq_some_iff ν).2 (heq ▸ h)
        split_ifs <;> assumption
      · obtain ⟨w', hw', hB⟩ :=
          exists_eq_some_of_rankM_lt hν (P.rankM_lt_of_le_of_ne hm heq)
        rw [h, Option.some_injective _ |>.eq_iff] at hw'
        subst hw'
        rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.2 hB)), hμw]
    · have hνw : ν.symm w = some m := (PEquiv.eq_some_iff ν).2 h
      split_ifs with hle
      · exact hνw
      · obtain ⟨m', hm', hA⟩ := exists_symm_eq_some_of_rankW_lt hμ (not_le.1 hle)
        rw [hνw, Option.some_injective _ |>.eq_iff] at hm'
        subst hm'
        exact absurd hA.le hm

/-- **Conway's lattice, join (with the women's side).** Letting each man take the better of his
partners at two stable matchings gives a stable matching, in which each woman gets the worse of
her two partners. -/
theorem exists_isStable_manSup_womanInf (hμ : P.IsStable μ) (hν : P.IsStable ν) :
    ∃ ρ : M ≃. W, P.IsStable ρ ∧
      (∀ m, ρ m = if P.rankM m (μ m) ≤ P.rankM m (ν m) then μ m else ν m) ∧
      ∀ w, ρ.symm w = if P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w) then ν.symm w else μ.symm w :=
    by
  let ρ : M ≃. W :=
    { toFun := fun m ↦ if P.rankM m (μ m) ≤ P.rankM m (ν m) then μ m else ν m
      invFun := fun w ↦
        if P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w) then ν.symm w else μ.symm w
      inv := fun m w ↦ manSup_eq_some_iff hμ hν m w }
  refine ⟨ρ, ⟨⟨fun m ↦ ?_, fun w ↦ ?_⟩, fun m w ⟨hm, hw⟩ ↦ ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · change P.rankM m (if _ then _ else _) ≤ _
    split_ifs
    exacts [hμ.1.1 m, hν.1.1 m]
  · change P.rankW w (if _ then _ else _) ≤ _
    split_ifs
    exacts [hν.1.2 w, hμ.1.2 w]
  · change P.rankM m (some w) < P.rankM m (if _ then _ else _) at hm
    change P.rankW w (some m) < P.rankW w (if _ then _ else _) at hw
    have h1 : P.rankM m (some w) < P.rankM m (μ m) ∧ P.rankM m (some w) < P.rankM m (ν m) := by
      split_ifs at hm with h
      · exact ⟨hm, lt_of_lt_of_le hm h⟩
      · exact ⟨lt_trans hm (not_le.1 h), hm⟩
    have h2 := hμ.rankW_lt h1.1
    have h3 := hν.rankW_lt h1.2
    split_ifs at hw
    · exact lt_asymm hw h3
    · exact lt_asymm hw h2

/-- **Conway's lattice, join.** Letting each man take the better of his partners at two stable
matchings gives a stable matching. -/
theorem exists_isStable_manSup (hμ : P.IsStable μ) (hν : P.IsStable ν) :
    ∃ ρ : M ≃. W, P.IsStable ρ ∧ ∀ m, ρ m =
      if P.rankM m (μ m) ≤ P.rankM m (ν m) then μ m else ν m :=
  let ⟨ρ, hρ, hm, _⟩ := exists_isStable_manSup_womanInf hμ hν
  ⟨ρ, hρ, hm⟩

omit [Finite M] [Finite W] in
theorem ite_rankM_le_comm (m : M) :
    (if P.rankM m (μ m) ≤ P.rankM m (ν m) then ν m else μ m) =
      if P.rankM m (ν m) ≤ P.rankM m (μ m) then μ m else ν m := by
  split_ifs with h1 h2 h2
  · exact P.rankM_injective m (le_antisymm h2 h1)
  · rfl
  · rfl
  · exact absurd (le_of_lt (not_le.1 h1)) h2

omit [Finite M] [Finite W] in
theorem ite_rankW_le_comm (w : W) :
    (if P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w) then μ.symm w else ν.symm w) =
      if P.rankW w (ν.symm w) ≤ P.rankW w (μ.symm w) then ν.symm w else μ.symm w := by
  split_ifs with h1 h2 h2
  · exact P.rankW_injective w (le_antisymm h1 h2)
  · rfl
  · rfl
  · exact absurd (le_of_lt (not_le.1 h1)) h2

/-- **Conway's lattice, meet (with the women's side).** Letting each man take the worse of his
partners at two stable matchings gives a stable matching, in which each woman gets the better of
her two partners. Proved by applying the join to the role swap. -/
theorem exists_isStable_manInf_womanSup (hμ : P.IsStable μ) (hν : P.IsStable ν) :
    ∃ ρ : M ≃. W, P.IsStable ρ ∧
      (∀ m, ρ m = if P.rankM m (ν m) ≤ P.rankM m (μ m) then μ m else ν m) ∧
      ∀ w, ρ.symm w = if P.rankW w (μ.symm w) ≤ P.rankW w (ν.symm w) then μ.symm w else ν.symm w :=
    by
  obtain ⟨ρ', hρ', hw, hm⟩ := exists_isStable_manSup_womanInf (P := P.swap)
    (isStable_swap_iff.2 hμ) (isStable_swap_iff.2 hν)
  refine ⟨ρ'.symm, isStable_swap_iff.1 (by simpa using hρ'), fun m ↦ ?_, fun w ↦ ?_⟩
  · rw [hm m]
    exact ite_rankM_le_comm m
  · exact hw w

/-- **Conway's lattice, meet.** Letting each man take the worse of his partners at two stable
matchings gives a stable matching. -/
theorem exists_isStable_manInf (hμ : P.IsStable μ) (hν : P.IsStable ν) :
    ∃ ρ : M ≃. W, P.IsStable ρ ∧ ∀ m, ρ m =
      if P.rankM m (ν m) ≤ P.rankM m (μ m) then μ m else ν m :=
  let ⟨ρ, hρ, hm, _⟩ := exists_isStable_manInf_womanSup hμ hν
  ⟨ρ, hρ, hm⟩

/-! ### McVitie–Wilson -/

theorem eq_none_of_isStable_of_eq_none (hμ : P.IsStable μ) (hν : P.IsStable ν) {m : M}
    (h : μ m = none) : ν m = none := by
  by_contra hne
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
  have hlt : P.rankM m (ν m) < P.rankM m (μ m) := by
    rw [h, hw]
    exact rankM_some_lt_none (hw ▸ hν.1.1 m)
  obtain ⟨w', hw', -⟩ := exists_symm_eq_some_of_rankM_lt hν hμ hlt
  rw [(PEquiv.eq_some_iff μ).1 hw'] at h
  exact Option.some_ne_none _ h

theorem symm_eq_none_of_isStable_of_symm_eq_none (hμ : P.IsStable μ) (hν : P.IsStable ν) {w : W}
    (h : μ.symm w = none) : ν.symm w = none := by
  by_contra hne
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hne
  have hlt : P.rankW w (ν.symm w) < P.rankW w (μ.symm w) := by
    rw [h, hm]
    exact rankW_some_lt_none (hm ▸ hν.1.2 w)
  obtain ⟨m', hm', -⟩ := exists_eq_some_of_rankW_lt hμ hν hlt
  rw [(PEquiv.eq_some_iff μ).2 hm'] at h
  exact Option.some_ne_none _ h

/-- **McVitie–Wilson, men.** The same men are single at every stable matching. -/
theorem man_eq_none_iff_of_isStable (hμ : P.IsStable μ) (hν : P.IsStable ν) (m : M) :
    μ m = none ↔ ν m = none :=
  ⟨eq_none_of_isStable_of_eq_none hμ hν, eq_none_of_isStable_of_eq_none hν hμ⟩

/-- **McVitie–Wilson, women.** The same women are single at every stable matching. -/
theorem woman_eq_none_iff_of_isStable (hμ : P.IsStable μ) (hν : P.IsStable ν) (w : W) :
    μ.symm w = none ↔ ν.symm w = none :=
  ⟨symm_eq_none_of_isStable_of_symm_eq_none hμ hν,
    symm_eq_none_of_isStable_of_symm_eq_none hν hμ⟩

end Market

end LeanPool.StableMatching
