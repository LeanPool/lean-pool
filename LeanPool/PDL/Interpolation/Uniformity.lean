/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.UniformityCore
import all LeanPool.PDL.Interpolation.UniformityCore -- shake: keep
public import LeanPool.PDL.Interpolation.ClusterSatDown

meta import LeanPool.PDL.General.ImportCompatibility

/-! # Uniformity of split tableaux (Section 8.1)

This file defines when a tableau is *uniform*, by the two conditions U1 and U2 of the
paper, and shows that in a uniform tableau every loaded cluster has the property
`LoadedCluster.HasUniformSteps` that the construction of the quasi-tableau needs.

Recall the two conditions from the paper, where `Λ₁(s)` and `Λ₂(s)` are the left and the
right component of the sequent at the node `s`, and where `i ∈ {1,2}`:

* **U1.** If `Λᵢ(s)` is loaded then a local rule is applied to a formula in the unloaded
  component of `s`, unless that component is basic.
* **U2.** If `Λᵢ(s) = Λᵢ(t)` is loaded and not basic, and the unloaded components of both
  `s` and `t` are basic, then at `s` and at `t` the same rule is applied, to the same
  formula in the loaded component of the node.

Both conditions speak about the nodes of the tableau in the sense of the paper, i.e. also
about the nodes *inside* the local tableaux. Hence we state them for `FinePathIn tab`.
Note that in U2 the loaded component is not basic, so the rule applied at `s` and at `t`
must be a *local* rule; we therefore phrase U2 using `FinePathIn.lraOpt`, and "the same rule
applied to the same formula" becomes `LocalRuleApp.SameRuleAs`: the two rule applications
have the same principal formulas (`Lcond`, `Rcond` and `Ocond`) and the same results
(`ress`), and indeed use the same rule (`lr`).

The main result is `LoadedCluster.uniformOfUniTab`. Its proof splits into two cases, and
only the second one uses uniformity:

* If `Δ` is basic then by Lemma 9.7 (e) — here `Uniformity.basicModalStep` — the rule
  applied at a node of `C^R_Δ` is the modal rule `(M)` for the loaded formula of `Δ`, and
  hence the right component of the unique child only depends on `Δ`.
* If `Δ` is not basic then the rule applied at a node of `C^R_Δ` is a local rule acting on
  the right. By U1 the left component of such a node is basic, so U2 applies and says that
  the same rule with the same principal formula is used at all these nodes. Since a local
  rule application only changes the right component by deleting its principal formulas and
  adding the results, the right components of the children agree — this is
  `Uniformity.map_rightOnly_C_eq`.

## Duplicated helper lemmas

The file `Pdl.ClusterInterpolation` imports this file (it uses `Tableau.isUniform` and
`LoadedCluster.uniformOfUniTab`), so we cannot use the lemmas about right rules that are
proved there. The section `Uniformity` below therefore repeats those that are needed here,
under different names.
-/

@[expose] public section

namespace PDL

/-! ## Refutable sequents

To show that the local development of a sequent does not depend on the order in which the
rules are applied we have to deal with *clashes*: one local tableau may close a branch with
a closure rule while another one first decomposes the two clashing formulas. So we need to
know that a clash cannot get lost, i.e. that after applying any local rule to a closed
sequent the resulting sequents can still be closed.

We call a sequent `Refutable` if it has a local tableau without any end nodes. Note that we
only ask for the *existence* of such a local tableau; this is all that is needed below, and
it can be shown by purely syntactic means: the interesting case is when the rule applied is
the box or the diamond unfolding for the two clashing formulas `⌈α⌉ψ` and `~⌈α⌉ψ`. There
the branches of `unfoldBox` and of `unfoldDiamond` clash pairwise, either on a test or on a
formula `⌈⌈δ⌉⌉ψ`, which is `Dset_mem_P_of_tests` below. -/

theorem Dset_mem_P_of_tests (α : Program) (ℓ : TP α) (Fs : List Formula) (δ : List Program)
    (h : (Fs, δ) ∈ Dset α) (hF : ∀ τ ∈ Fs, (~τ) ∉ F α ℓ) : δ ∈ P α ℓ := by
  cases α
  case atom_prog a => simp [Dset] at h; simp [P, h.2]
  case test τ =>
    simp only [Dset, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨hFs, hδ⟩ := h
    subst hFs; subst hδ
    have hℓ : ℓ ⟨τ, by simp [testsOfProgram]⟩ = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      exact hF τ (by simp) (by simp [F, hc])
    simp [P, hℓ]
  case union α β =>
    simp only [Dset, List.mem_union_iff] at h
    simp only [F, List.mem_union_iff] at hF
    rcases h with h | h
    · have := Dset_mem_P_of_tests α _ _ _ h (fun τ hτ hc => hF τ hτ (Or.inl hc))
      simp only [P, List.mem_union_iff]; tauto
    · have := Dset_mem_P_of_tests β _ _ _ h (fun τ hτ hc => hF τ hτ (Or.inr hc))
      simp only [P, List.mem_union_iff]; tauto
  case sequence α β =>
    simp only [Dset, List.mem_flatMap] at h
    simp only [F, List.mem_union_iff] at hF
    obtain ⟨⟨G, γ⟩, hGγ, hmem⟩ := h
    by_cases hγ : γ = []
    · subst hγ
      simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq, and_true,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right'] at hmem
      obtain ⟨H, hHδ, rfl⟩ := hmem
      have hG : [] ∈ P α (ℓ : TP α) := by
        refine Dset_mem_P_of_tests α _ _ _ hGγ (fun τ hτ hc => hF τ ?_ (Or.inl hc))
        simp only [List.mem_union_iff]; tauto
      have hH : δ ∈ P β (ℓ : TP β) := by
        refine Dset_mem_P_of_tests β _ _ _ hHδ (fun τ hτ hc => hF τ ?_ (Or.inr hc))
        simp only [List.mem_union_iff]; tauto
      simp only [P, List.mem_union_iff]
      right
      simp [hG, hH]
    · simp only [ite_eq_right hγ, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      have hG : γ ∈ P α (ℓ : TP α) :=
        Dset_mem_P_of_tests α _ _ _ hGγ (fun τ hτ hc => hF τ hτ (Or.inl hc))
      simp only [P, List.mem_union_iff]
      left
      simp only [List.mem_map, List.mem_filter]
      exact ⟨γ, ⟨hG, by simp [hγ]⟩, rfl⟩
  case star α =>
    simp only [Dset, List.mem_union_iff, List.mem_flatten, List.mem_map] at h
    simp only [F] at hF
    rcases h with h | ⟨l, ⟨⟨G, γ⟩, hGγ, rfl⟩, hin⟩
    · simp at h
      simp [P, h.2]
    · by_cases hγ : γ = []
      · simp [hγ] at hin
      · simp only [ite_eq_right hγ, List.mem_singleton, Prod.mk.injEq] at hin
        obtain ⟨rfl, rfl⟩ := hin
        have hG : γ ∈ P α (ℓ : TP α) := Dset_mem_P_of_tests α _ _ _ hGγ hF
        simp only [P, List.mem_union_iff]
        right
        simp only [List.mem_map, List.mem_filter]
        exact ⟨γ, ⟨hG, by simp [hγ]⟩, rfl⟩

/-! ### Refutable and dominated sequents -/

/-- The sequent `W` is *dominated by* the finite set `Ys` if it has a local tableau all of
whose end nodes occur in `Ys`. -/
def Sequent.DominatedBy (W : Sequent) (Ys : Finset Sequent) : Prop :=
  ∃ lt : LocalTableau W, ∀ Y ∈ endNodesOf lt, Y ∈ Ys

/-- A sequent is *refutable* if it has a local tableau without any end nodes. -/
def Sequent.Refutable (X : Sequent) : Prop := X.DominatedBy ∅

lemma Sequent.refutable_iff {X : Sequent} :
    X.Refutable ↔ ∃ lt : LocalTableau X, endNodesOf lt = ∅ := by
  constructor
  · rintro ⟨lt, h⟩
    exact ⟨lt, Finset.eq_empty_of_forall_notMem (fun Y hY => by simpa using h Y hY)⟩
  · rintro ⟨lt, h⟩
    exact ⟨lt, fun Y hY => absurd (h ▸ hY) (by simp)⟩

lemma Sequent.DominatedBy.mono {W : Sequent} {Ys Zs : Finset Sequent} (h : W.DominatedBy Ys)
    (hsub : Ys ⊆ Zs) : W.DominatedBy Zs := by
  obtain ⟨lt, hlt⟩ := h
  exact ⟨lt, fun Y hY => hsub (hlt Y hY)⟩

lemma Sequent.Refutable.dominatedBy {W : Sequent} (h : W.Refutable) (Ys : Finset Sequent) :
    W.DominatedBy Ys :=
  h.mono (Finset.empty_subset _)

/-- If all children of a rule application are dominated by `Ys` then so is the sequent. -/
lemma Sequent.DominatedBy.byRule {W : Sequent} {Ys : Finset Sequent} {lra : LocalRuleApp}
    (hX : lra.X = W) (h : ∀ V ∈ lra.C, V.DominatedBy Ys) : W.DominatedBy Ys := by
  choose f hf using h
  refine ⟨LocalTableau.byLocalRule lra hX.symm f, ?_⟩
  intro Y hY
  simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
    true_and, Subtype.exists] at hY
  obtain ⟨V, hV, hY⟩ := hY
  exact hf V hV Y hY

/-- A closed sequent is refutable: a closure rule can be applied to it. -/
lemma Sequent.Refutable.of_closed {X : Sequent} (h : X.closed) : X.Refutable := by
  have key : ∃ lra : LocalRuleApp, lra.X = X ∧ lra.C = ∅ := by
    rcases X with ⟨L, R, O⟩
    rcases h with bot_in | ⟨φ, φ_in, not_φ_in⟩
    · simp only [Sequent.mem_def] at bot_in
      cases bot_in
      · exact ⟨⟨L, R, O, {⊥}, ∅, none, ∅, .oneSidedL .bot rfl, ∅, by simp [applyLocalRule],
          by simp_all⟩, by simp, rfl⟩
      · exact ⟨⟨L, R, O, ∅, {⊥}, none, ∅, .oneSidedR .bot rfl, ∅, by simp [applyLocalRule],
          by simp_all⟩, by simp, rfl⟩
    · simp only [Sequent.mem_def] at φ_in not_φ_in
      cases φ_in <;> cases not_φ_in
      · exact ⟨⟨L, R, O, {φ, ~φ}, ∅, none, ∅, .oneSidedL (.not _) rfl, ∅,
          by simp [applyLocalRule], by simp_all [Finset.insert_subset_iff]⟩, by simp, rfl⟩
      · exact ⟨⟨L, R, O, {φ}, {~φ}, none, ∅, LocalRule.LRnegL φ, ∅, by simp [applyLocalRule],
          by simp_all⟩, by simp, rfl⟩
      · exact ⟨⟨L, R, O, {~φ}, {φ}, none, ∅, LocalRule.LRnegR φ, ∅, by simp [applyLocalRule],
          by simp_all⟩, by simp, rfl⟩
      · exact ⟨⟨L, R, O, ∅, {φ, ~φ}, none, ∅, .oneSidedR (.not _) rfl, ∅,
          by simp [applyLocalRule], by simp_all [Finset.insert_subset_iff]⟩, by simp, rfl⟩
  obtain ⟨lra, hX, hC⟩ := key
  exact Sequent.DominatedBy.byRule hX (by simp [hC])

/-! ### Clashes survive the application of a rule

The next lemmas say that a clash in a sequent cannot be lost by applying a local rule:
the results are again refutable. The interesting cases are those where the rule is applied
to one of the two clashing formulas. -/

/-- To show that `X` is refutable it suffices to apply a one-sided rule to a formula `p` of
`X` and to refute all the results. The resulting sequents are only described by two
properties, so that we do not have to care about which of the two components `p` is in:
all formulas of `X` other than `p` are still present, and the result of the rule was added. -/
lemma Sequent.Refutable.byOneSided {X : Sequent} {p : Formula} {ress : Finset (Finset Formula)}
    (orule : OneSidedLocalRule {p} ress) (hp : p ∈ X)
    (h : ∀ res ∈ ress, ∀ W : Sequent,
        (∀ f ∈ X, f ≠ p → f ∈ W) → (∀ φ ∈ res, φ ∈ W) → W.Refutable) :
    X.Refutable := by
  rcases X with ⟨L, R, O⟩
  simp only [Sequent.mem_def, Sequent.L, Sequent.R] at hp
  rcases hp with hp | hp
  · refine Sequent.DominatedBy.byRule (lra := ⟨L, R, O, {p}, ∅, none,
      ress.image (fun res => (res, ∅, none)), .oneSidedL orule rfl, _, rfl,
      ⟨by simpa using hp, Finset.empty_subset _, by simp⟩⟩) rfl ?_
    intro V hV
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hV
    obtain ⟨res, hres, rfl⟩ := hV
    refine h res hres _ ?_ ?_
    · rintro f hf hne
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_singleton] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (Or.inl ⟨hf, hne⟩)
      · exact Or.inr (by simpa using hf)
    · intro φ hφ
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union]
      exact Or.inl (Or.inr hφ)
  · refine Sequent.DominatedBy.byRule (lra := ⟨L, R, O, ∅, {p}, none,
      ress.image (fun res => (∅, res, none)), .oneSidedR orule rfl, _, rfl,
      ⟨Finset.empty_subset _, by simpa using hp, by simp⟩⟩) rfl ?_
    intro V hV
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hV
    obtain ⟨res, hres, rfl⟩ := hV
    refine h res hres _ ?_ ?_
    · rintro f hf hne
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_singleton] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (by simpa using hf)
      · exact Or.inr (Or.inl ⟨hf, hne⟩)
    · intro φ hφ
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union]
      exact Or.inr (Or.inr hφ)

/-- Two formulas of different length are different. -/
lemma Formula.ne_of_length_lt {φ ψ : Formula}
    (h : lengthOfFormula φ < lengthOfFormula ψ) : φ ≠ ψ := by
  rintro rfl
  omega

/-- Two formulas of different length are different. -/
lemma Formula.ne_of_length_ne {φ ψ : Formula}
    (h : lengthOfFormula φ ≠ lengthOfFormula ψ) : φ ≠ ψ := by
  rintro rfl
  exact h rfl

/-- Adding formulas to a closed sequent keeps it closed. -/
lemma Sequent.closed.append {L R Ln Rn : Finset Formula} {O O' : Olf}
    (hX : Sequent.closed (L, R, O)) : Sequent.closed (L ∪ Ln, R ∪ Rn, O') := by
  rcases hX with hbot | ⟨f, hf, hnf⟩
  · left
    simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union] at hbot ⊢
    tauto
  · right
    refine ⟨f, ?_, ?_⟩ <;>
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union]
        at hf hnf ⊢ <;>
      tauto

/-- A one-sided rule that is not a closure rule has exactly one principal formula. -/
lemma OneSidedLocalRule.singleton_precond {pre : Finset Formula} {ress : Finset (Finset Formula)}
    (orule : OneSidedLocalRule pre ress) (h : ress ≠ ∅) : ∃ p, pre = {p} := by
  cases orule <;> simp_all

/-- Tests are shorter than the program they occur in. -/
lemma lengthOfFormula_lt_of_mem_testsOfProgram {α : Program} : ∀ {τ : Formula},
    τ ∈ testsOfProgram α → lengthOfFormula τ < lengthOfProgram α := by
  intro τ hτ
  cases α
  all_goals simp only [testsOfProgram, lengthOfProgram, List.mem_append, List.not_mem_nil,
    List.mem_singleton] at hτ ⊢
  case test φ => subst hτ; omega
  case sequence α β =>
    rcases hτ with h | h
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) h; omega
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := β) h; omega
  case union α β =>
    rcases hτ with h | h
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) h; omega
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := β) h; omega
  case star α => have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) hτ; omega

/-- A list of boxes in front of a short formula is not the negation of a longer one. -/
lemma boxes_ne_neg {δ : List Program} {ψ χ : Formula}
    (h : lengthOfFormula ψ ≤ lengthOfFormula χ) : Formula.boxes δ ψ ≠ (~χ) := by
  cases δ with
  | nil => simp only [Formula.boxes_nil]; exact Formula.ne_of_length_lt (by simp; omega)
  | cons γ δ => simp [Formula.boxes_cons]

/-- A formula in the unfolding of `⌈α⌉ψ` is not `~⌈α⌉ψ`. -/
lemma ne_neg_box_of_mem_Bset {α : Program} {ψ : Formula} {ℓ : TP α} {f : Formula}
    (hf : f ∈ Bset α ℓ ψ) : f ≠ (~⌈α⌉ψ) := by
  simp only [Bset, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨δ, _, rfl⟩
  · exact Formula.ne_of_length_lt (by have := F_goes_down hf; simp; omega)
  · exact boxes_ne_neg (by simp)

/-- A formula in the unfolding of `~⌈α⌉ψ` is neither `⌈α⌉ψ` nor `~~⌈α⌉ψ`. -/
lemma ne_box_of_mem_Yset {α : Program} {ψ : Formula} {Fs : List Formula} {δ : List Program}
    (hFδ : (Fs, δ) ∈ Dset α) {f : Formula} (hf : f ∈ Yset (Fs, δ) ψ) :
    f ≠ (⌈α⌉ψ) ∧ f ≠ (~~⌈α⌉ψ) := by
  simp only [Yset, List.mem_union_iff, List.mem_singleton] at hf
  rcases hf with hf | rfl
  · obtain ⟨τ, hτ, rfl⟩ := Dset_mem_test α f hFδ hf
    have := lengthOfFormula_lt_of_mem_testsOfProgram hτ
    exact ⟨Formula.ne_of_length_lt (by simp; omega), Formula.ne_of_length_lt (by simp; omega)⟩
  · refine ⟨by simp, ?_⟩
    simp only [ne_eq, Formula.neg.injEq]
    exact boxes_ne_neg (by simp)

/-- **The branches of the box unfolding and of the diamond unfolding clash.**
Given a test profile `ℓ` and a pair `(Fs, δ) ∈ Dset α`, the two lists `Bset α ℓ ψ` and
`Yset (Fs, δ) ψ` contain a formula and its negation: either the two disagree about a test,
or `δ ∈ P α ℓ` and then `⌈⌈δ⌉⌉ψ` is in the first and `~⌈⌈δ⌉⌉ψ` is in the second list. -/
lemma Bset_Yset_clash {α : Program} {ψ : Formula} (ℓ : TP α) {Fs : List Formula}
    {δ : List Program} (hFδ : (Fs, δ) ∈ Dset α) :
    ∃ f, (f ∈ Bset α ℓ ψ ∧ (~f) ∈ Yset (Fs, δ) ψ)
       ∨ ((~f) ∈ Bset α ℓ ψ ∧ f ∈ Yset (Fs, δ) ψ) := by
  by_cases hcase : ∀ τ ∈ Fs, (~τ) ∉ F α ℓ
  · have hδ : δ ∈ P α ℓ := Dset_mem_P_of_tests α ℓ _ _ hFδ hcase
    refine ⟨⌈⌈δ⌉⌉ψ, Or.inl ⟨?_, ?_⟩⟩
    · simp only [Bset, List.mem_append, List.mem_map]
      exact Or.inr ⟨δ, hδ, rfl⟩
    · simp [Yset]
  · push Not at hcase
    obtain ⟨τ, hτ, hτF⟩ := hcase
    exact ⟨τ, Or.inr ⟨by simp [Bset, hτF], by simp [Yset]; tauto⟩⟩

lemma refutable_of_negneg {X : Sequent} {χ : Formula} (h1 : χ ∈ X) (h2 : (~(~(~χ))) ∈ X) :
    X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (~χ)) h2 ?_
  rintro res hres W hsurv hmem
  simp only [Finset.mem_singleton] at hres
  subst hres
  refine Sequent.Refutable.of_closed (Or.inr ⟨χ, ?_, hmem _ (by simp)⟩)
  exact hsurv χ h1 (Formula.ne_of_length_ne (by simp; omega))

lemma refutable_of_con_nCo {X : Sequent} {χ ρ : Formula} (h1 : χ ∈ X) (h2 : ρ ∈ X)
    (h3 : (~(χ ⋀ ρ)) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.nCo χ ρ) h3 ?_
  rintro res hres W hsurv hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hres
  rcases hres with rfl | rfl
  · exact Sequent.Refutable.of_closed (Or.inr ⟨χ,
      hsurv χ h1 (Formula.ne_of_length_ne (by simp; omega)), hmem _ (by simp)⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨ρ,
      hsurv ρ h2 (Formula.ne_of_length_ne (by simp; omega)), hmem _ (by simp)⟩)

lemma refutable_of_nCo_con {X : Sequent} {χ ρ : Formula} (h1 : (~χ) ∈ X ∨ (~ρ) ∈ X)
    (h2 : (χ ⋀ ρ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.con χ ρ) h2 ?_
  rintro res hres W hsurv hmem
  simp only [Finset.mem_singleton] at hres
  subst hres
  rcases h1 with h1 | h1
  · exact Sequent.Refutable.of_closed (Or.inr ⟨χ, hmem _ (by simp), hsurv _ h1 (by simp)⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨ρ, hmem _ (by simp), hsurv _ h1 (by simp)⟩)

lemma refutable_of_nCo_negneg {X : Sequent} {χ ρ : Formula} (h1 : (~χ) ∈ X ∨ (~ρ) ∈ X)
    (h2 : (~~(χ ⋀ ρ)) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (χ ⋀ ρ)) h2 ?_
  rintro res hres W hsurv hmem
  simp only [Finset.mem_singleton] at hres
  subst hres
  have k1 : (~χ) ≠ (~~(χ ⋀ ρ)) := Formula.ne_of_length_ne (by simp; omega)
  have k2 : (~ρ) ≠ (~~(χ ⋀ ρ)) := Formula.ne_of_length_ne (by simp; omega)
  refine refutable_of_nCo_con (χ := χ) (ρ := ρ) ?_ (hmem _ (by simp))
  rcases h1 with h1 | h1
  · exact Or.inl (hsurv _ h1 k1)
  · exact Or.inr (hsurv _ h1 k2)

lemma refutable_of_box_dia {X : Sequent} {α : Program} {ψ : Formula} {ℓ : TP α}
    (hna : ¬ α.isAtomic) (hB : ∀ φ ∈ Bset α ℓ ψ, φ ∈ X) (hd : (~⌈α⌉ψ) ∈ X) :
    X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.dia α ψ hna) hd ?_
  rintro res hres W hsurv hmem
  simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
  obtain ⟨Y, hY, rfl⟩ := hres
  simp only [unfoldDiamond, List.mem_map] at hY
  obtain ⟨⟨Fs, δ⟩, hFδ, rfl⟩ := hY
  have hBW : ∀ φ ∈ Bset α ℓ ψ, φ ∈ W :=
    fun φ hφ => hsurv φ (hB φ hφ) (ne_neg_box_of_mem_Bset hφ)
  obtain ⟨f, hf | hf⟩ := Bset_Yset_clash (ψ := ψ) ℓ hFδ
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hBW _ hf.1, hmem _ (by simpa using hf.2)⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hmem _ (by simpa using hf.2), hBW _ hf.1⟩)

lemma refutable_of_dia_box {X : Sequent} {α : Program} {ψ : Formula} {Fs : List Formula}
    {δ : List Program} (hna : ¬ α.isAtomic) (hFδ : (Fs, δ) ∈ Dset α)
    (hY : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ X) (hb : (⌈α⌉ψ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.box α ψ hna) hb ?_
  rintro res hres W hsurv hmem
  simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
  obtain ⟨B, hB, rfl⟩ := hres
  simp only [unfoldBox, List.mem_map] at hB
  obtain ⟨ℓ, _, rfl⟩ := hB
  have hYW : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ W :=
    fun φ hφ => hsurv φ (hY φ hφ) (ne_box_of_mem_Yset hFδ hφ).1
  obtain ⟨f, hf | hf⟩ := Bset_Yset_clash (ψ := ψ) ℓ hFδ
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hmem _ (by simpa using hf.1), hYW _ hf.2⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hYW _ hf.2, hmem _ (by simpa using hf.1)⟩)

lemma refutable_of_dia_negneg {X : Sequent} {α : Program} {ψ : Formula} {Fs : List Formula}
    {δ : List Program} (hna : ¬ α.isAtomic) (hFδ : (Fs, δ) ∈ Dset α)
    (hY : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ X) (hb : (~~⌈α⌉ψ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (⌈α⌉ψ)) hb ?_
  rintro res hres W hsurv hmem
  simp only [Finset.mem_singleton] at hres
  subst hres
  exact refutable_of_dia_box hna hFδ
    (fun φ hφ => hsurv φ (hY φ hφ) (ne_box_of_mem_Yset hFδ hφ).2) (hmem _ (by simp))

/-- **A clash survives a one-sided rule.** If `X` is closed and `W` is obtained from `X` by
removing the principal formula `p` of a one-sided rule and adding one of its results, then
`W` is refutable. -/
lemma Sequent.Refutable.of_oneSided_step {X W : Sequent} (hX : X.closed) {p : Formula}
    {pre : Finset Formula} {ress : Finset (Finset Formula)} (orule : OneSidedLocalRule pre ress)
    (hpre : pre = {p}) {res : Finset Formula}
    (hres : res ∈ ress) (hsurv : ∀ f ∈ X, f ≠ p → f ∈ W) (hmem : ∀ φ ∈ res, φ ∈ W) :
    W.Refutable := by
  have easy : ∀ f, f ∈ X → (~f) ∈ X → f ≠ p → (~f) ≠ p → W.Refutable := fun f h1 h2 h3 h4 =>
    Sequent.Refutable.of_closed (Or.inr ⟨f, hsurv f h1 h3, hsurv _ h2 h4⟩)
  cases orule
  case bot => simp at hres
  case not φ => simp at hres
  case neg φ =>
    rw [Finset.singleton_inj] at hpre
    subst hpre
    simp only [Finset.mem_singleton] at hres
    subst hres
    have hφW : φ ∈ W := hmem _ (by simp)
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~~φ)
      · subst h1
        have hne : (~(~~φ)) ≠ (~~φ) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_negneg (χ := φ) hφW (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~~φ)
        · simp only [Formula.neg.injEq] at h2
          subst h2
          have hne : (~φ) ≠ (~~φ) := Formula.ne_of_length_ne (by simp)
          exact Sequent.Refutable.of_closed (Or.inr ⟨φ, hφW, hsurv _ hf hne⟩)
        · exact easy f hf hnf h1 h2
  case con φ ψ =>
    rw [Finset.singleton_inj] at hpre
    subst hpre
    simp only [Finset.mem_singleton] at hres
    subst hres
    have hφW : φ ∈ W := hmem _ (by simp)
    have hψW : ψ ∈ W := hmem _ (by simp)
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (φ ⋀ ψ)
      · subst h1
        exact refutable_of_con_nCo hφW hψW (hsurv _ hnf (by simp))
      · exact easy f hf hnf h1 (by simp)
  case nCo φ ψ =>
    rw [Finset.singleton_inj] at hpre
    subst hpre
    have hres' : res = {~φ} ∨ res = {~ψ} := by simpa using hres
    have hin : (~φ) ∈ W ∨ (~ψ) ∈ W := by
      rcases hres' with rfl | rfl
      · exact Or.inl (hmem _ (by simp))
      · exact Or.inr (hmem _ (by simp))
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~(φ ⋀ ψ))
      · subst h1
        have hne : (~~(φ ⋀ ψ)) ≠ (~(φ ⋀ ψ)) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_nCo_negneg hin (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~(φ ⋀ ψ))
        · simp only [Formula.neg.injEq] at h2
          subst h2
          exact refutable_of_nCo_con hin (hsurv _ hf (by simp))
        · exact easy f hf hnf h1 h2
  case box α φ hna =>
    rw [Finset.singleton_inj] at hpre
    subst hpre
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
    obtain ⟨B, hB, rfl⟩ := hres
    simp only [unfoldBox, List.mem_map] at hB
    obtain ⟨ℓ, _, rfl⟩ := hB
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (⌈α⌉φ)
      · subst h1
        exact refutable_of_box_dia (ℓ := ℓ) hna (fun x hx => hmem x (by simpa using hx))
          (hsurv _ hnf (by simp))
      · exact easy f hf hnf h1 (by simp)
  case dia α φ hna =>
    rw [Finset.singleton_inj] at hpre
    subst hpre
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
    obtain ⟨Y, hY, rfl⟩ := hres
    simp only [unfoldDiamond, List.mem_map] at hY
    obtain ⟨⟨Fs, δ⟩, hFδ, rfl⟩ := hY
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~⌈α⌉φ)
      · subst h1
        have hne : (~~⌈α⌉φ) ≠ (~⌈α⌉φ) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_dia_negneg hna hFδ (fun x hx => hmem x (by simpa using hx))
          (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~⌈α⌉φ)
        · simp only [Formula.neg.injEq] at h2
          subst h2
          exact refutable_of_dia_box hna hFδ (fun x hx => hmem x (by simpa using hx))
            (hsurv _ hf (by simp))
        · exact easy f hf hnf h1 h2

/-- **A clash survives any local rule:** every child of a rule application to a closed
sequent is refutable. -/
lemma Sequent.Refutable.child_of_closed {X W : Sequent} (hX : X.closed) {lra : LocalRuleApp}
    (hXl : lra.X = X) (hW : W ∈ lra.C) : W.Refutable := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X] at hXl
  subst hXl
  subst hC
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hW
    obtain ⟨res, hres, rfl⟩ := hW
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at hres)
    refine Sequent.Refutable.of_oneSided_step hX orule rfl hres ?_ ?_
    · rintro f hf hne
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_singleton, Finset.sdiff_empty, Finset.union_empty] at hf ⊢
      tauto
    · intro φ hφ
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.sdiff_empty, Finset.union_empty]
      tauto
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hW
    obtain ⟨res, hres, rfl⟩ := hW
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at hres)
    refine Sequent.Refutable.of_oneSided_step hX orule rfl hres ?_ ?_
    · rintro f hf hne
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_singleton, Finset.sdiff_empty, Finset.union_empty] at hf ⊢
      tauto
    · intro φ hφ
      simp only [Sequent.mem_def, Sequent.L, Sequent.R, Finset.mem_union,
        Finset.mem_sdiff, Finset.sdiff_empty, Finset.union_empty]
      tauto
  case LRnegL => simp at hW
  case LRnegR => simp at hW
  case loadedL ress' χ lrule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hW
    obtain ⟨⟨Ln, on⟩, hres, rfl⟩ := hW
    exact Sequent.Refutable.of_closed (by simpa only [Finset.sdiff_empty] using hX.append)
  case loadedR ress' χ lrule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hW
    obtain ⟨⟨Ln, on⟩, hres, rfl⟩ := hW
    exact Sequent.Refutable.of_closed (by simpa only [Finset.sdiff_empty] using hX.append)

/-! ### Closure rules

A local rule has no results if and only if it is one of the closure rules. For the direction
we need here we must know that the box and diamond unfoldings are never empty. -/

/-- The box unfolding is never empty. -/
lemma unfoldBox_ne_nil (a : Program) (phi : Formula) : unfoldBox a phi ≠ [] := by
  intro h
  have hmem : Bset a (fun _ => true) phi ∈ unfoldBox a phi :=
    List.mem_map.mpr ⟨_, allTP_mem _, rfl⟩
  rw [h] at hmem
  simp at hmem

/-- The program unfolding used for diamonds is never empty. -/
theorem Dset_ne_nil : ∀ (a : Program), Dset a ≠ []
  | ·_ => by simp [Dset]
  | ?'_ => by simp [Dset]
  | a ⋓ b => by
      simp only [Dset]
      intro h
      refine Dset_ne_nil a (List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_))
      rw [List.eq_nil_iff_forall_not_mem] at h
      exact h x (by simp [hx])
  | a;' b => by
      simp only [Dset]
      intro h
      rw [List.flatMap_eq_nil_iff] at h
      obtain ⟨⟨F, delta⟩, hmem⟩ := List.exists_mem_of_ne_nil _ (Dset_ne_nil a)
      have hthis := h _ hmem
      by_cases hd : delta = []
      · subst hd
        simp only [ite_true] at hthis
        obtain ⟨⟨G, delta'⟩, hmem2⟩ := List.exists_mem_of_ne_nil _ (Dset_ne_nil b)
        have hh : (F ∪ G, delta') ∈ ((Dset b).map
            (fun x : List Formula × List Program => [(F ∪ x.1, x.2)])).flatten :=
          List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨(G, delta'), hmem2, rfl⟩, by simp⟩
        rw [hthis] at hh
        simp at hh
      · simp [hd] at hthis
  | ∗_ => by simp [Dset]

/-- A local tableau for a basic sequent has that sequent as its only end node. -/
lemma endNodesOf_of_basic {X : Sequent} (bas : X.basic) (lt : LocalTableau X) :
    endNodesOf lt = {X} := by
  cases lt with
  | byLocalRule lra X_def next => exact absurd (X_def ▸ bas) (nonbasic_of_localRuleApp lra)
  | sim => simp only [endNodesOf]

/- DISABLED, use UniTheorem instead!

/-! ### Uniform tableaux

**Warning.** The old proof of `Tableau.exists_isUni` for `List`-based sequents did not survive the
move to `Finset`-based sequents. With `Finset` components a formula that is re-created by a rule is
no longer counted twice, so the end nodes of a local tableau really do depend on the order in which
the rules are applied. Concretely, let `a`, `b`, `c` be atomic and consider the sequent with left
component `L = {~(a⋀b), (~(a⋀b))⋀c}` (empty right component, no loaded formula).

* Applying `con` to `(~(a⋀b))⋀c` first gives the single child `{~(a⋀b), c}`, and applying
  `nCo` there gives the two end nodes `{~a, c}` and `{~b, c}`.
* Applying `nCo` to `~(a⋀b)` first gives the children `{(~(a⋀b))⋀c, ~a}` and
  `{(~(a⋀b))⋀c, ~b}`; unfolding the conjunction re-creates `~(a⋀b)`, which then has to be
  unfolded again, so `{~a, ~b, c}` is an end node of every local tableau below the first
  child.

So `{~a, ~b, c}` is an end node in the second order but not in the first one. (For `List`
components this cannot happen: in the first order the child is `[~(a⋀b), ~(a⋀b), c]`, with
two copies of the formula, and unfolding both of them also produces `[~a, ~b, c]`.)

The statement `Tableau.exists_isUni` itself
is still plausible — the extra formulas of an end node of the canonical local tableau make
it *easier* to refute — but proving it now needs a weakening argument for tableaux instead
of the commutation argument, which is left open here. -/

/-- For every tableau there is one that applies the rules in the canonical order, i.e. that
satisfies `Tableau.IsUni`.

TODO: this needs a new proof for `Finset`-based sequents, see the note above. -/
theorem Tableau.exists_isUni {H : History} {X : Sequent} (tab : Tableau H X) :
    ∃ t : Tableau H X, t.IsUni := by
  induction tab with
  | @loc H X nflprep nbas lt next IH =>
      have hall : ∀ Y ∈ endNodesOf (uniLocalTab X), ∃ t : Tableau (X :: H) Y, t.IsUni := by
        intro Y hY
        -- TRICKY: `lt` and `uniLocalTab` might not have the *same* endNodesOf. But similar-ish?!
        -- Hm, the disjunctions over all endNodes should be equivalent or at least equi-satisfiable?
        -- But note that we can only apply the IH to `lt`.
        have Y_in_end_lt : Y ∈ endNodesOf lt := TODO;-)
        apply IH Y Y_in_end_lt
      choose next uni_next using hall
      exact ⟨.loc nflprep nbas (uniLocalTab X) next, ⟨uniLocalTab_isUni X, uni_next⟩⟩
  | @pdl H X Y nflprep bas r next IH =>
      obtain ⟨t, ht⟩ := IH
      exact ⟨.pdl nflprep bas r t, ht⟩
  | @lrep H X lpr =>
      exact ⟨.lrep lpr, trivial⟩

/-- If there is any tableau, then there is a uniform one. -/
lemma Tableau.toUniform (tab : Tableau .nil X) :
    ∃ u_tab : Tableau .nil X, u_tab.isUniform :=
  let ⟨t, ht⟩ := tab.exists_isUni
  ⟨t, ht.isUniform⟩

-/

namespace Uniformity

/-! ## Helpers

These are copies of results in `Pdl.ClusterInterpolation`, which are not available here
because that file imports this one. -/

/-- The right component of a basic sequent is basic.
Same as `Sequent.basic_rightOnly` in `Pdl.ClusterInterpolation`. -/
private lemma basic_rightOnly_impl {X : Sequent} (h : X.basic) : X.rightOnly.basic := by
  rcases X with ⟨L, R, O⟩
  obtain ⟨hb, hc⟩ := h
  constructor
  · intro f hf
    apply hb
    simp only [Sequent.rightOnly, Sequent.toFinset, Finset.empty_union, Finset.mem_union] at hf ⊢
    tauto
  · intro hcl
    apply hc
    rcases hcl with hbot | ⟨f, hf, hnf⟩
    · left
      revert hbot
      simp only [Sequent.rightOnly, Sequent.mem_def, Sequent.L, Sequent.R,
        Finset.notMem_empty, false_or]
      tauto
    · right
      refine ⟨f, ?_, ?_⟩ <;>
        simp only [Sequent.rightOnly, Sequent.mem_def, Sequent.L, Sequent.R,
          Finset.notMem_empty, false_or] at hf hnf ⊢ <;>
        tauto

-- Keep the established auxiliary signatures independent of the imported simp cache.
section
universe u_1

private theorem basic_rightOnly._simp_1_2 {α : Type u_1} [inst : DecidableEq α]
    {s t : Finset α} {a : α} : (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) :=
  propext Finset.mem_union

private theorem basic_rightOnly._simp_1_3 {φ : Formula} {X : Sequent} :
    (φ ∈ X) = (φ ∈ X.L ∨ φ ∈ X.R) := propext Sequent.mem_def

private theorem basic_rightOnly._simp_1_4 {α : Type u_1} (a : α) :
    (a ∈ (∅ : Finset α)) = False := eq_false (Finset.notMem_empty a)

end

/-- A basic sequent has a basic right component, including its optional loading. -/
lemma basic_rightOnly {X : Sequent} (h : X.basic) : X.rightOnly.basic := by
  exact basic_rightOnly_impl h

/-- A right local rule cannot be applied when the right component of the sequent is basic.
Same as `LocalRuleApp.not_rightOnly_basic_of_isRightRule` in `Pdl.ClusterInterpolation`. -/
lemma not_rightOnly_basic_of_isRightRule (lra : LocalRuleApp)
    (h : lra.isRightRule) : ¬ lra.X.rightOnly.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr
  case oneSidedR ress orule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, Rcond, none, _, LocalRule.oneSidedR orule YS_def, _, rfl,
        ⟨Finset.empty_subset _, pre.2.1, by simp⟩⟩
    simpa [Sequent.rightOnly] using this
  case loadedR χ lrule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, ∅, some (Sum.inr (~'χ)), _, LocalRule.loadedR χ lrule YS_def, _, rfl,
        ⟨Finset.empty_subset _, Finset.empty_subset _, pre.2.2⟩⟩
    simpa [Sequent.rightOnly] using this
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- Where a right rule is applied, it is either a local rule or the node is basic.
Same as `FinePathIn.lra_or_basic_of_usesRightRule` in `Pdl.ClusterInterpolation`. -/
lemma lra_or_basic_of_usesRightRule : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), f.usesRightRule →
      (∃ lra, f.lraOpt = some lra ∧ lra.isRightRule) ∨ f.label.basic
  | _, _, _, .inLoc lp hint, h => by
      simp only [FinePathIn.usesRightRule, FinePathIn.lraOpt] at h ⊢
      rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
      · rw [hlt] at h
        exact Or.inl ⟨lra, rfl, h⟩
      · rw [hlt] at h; simp at h
  | _, _, .pdl _ bas _ _, .pdlHere, _ => Or.inr bas
  | _, _, _, .lrepHere, h => by simp [FinePathIn.usesRightRule] at h
  | _, _, _, .loc Y_in tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lraOpt, FinePathIn.label] using
        lra_or_basic_of_usesRightRule tail h
  | _, _, _, .pdl tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lraOpt, FinePathIn.label] using
        lra_or_basic_of_usesRightRule tail h

/-- The right component of the child obtained by applying the modal rule `(M)` to a sequent
whose loaded formula `~⌊·A⌋ξ` is on the right.
Same as `modRChildRightOnly` in `Pdl.ClusterInterpolation`. -/
def modRChildRight (A : Nat) (ξ : AnyFormula) (R : Finset Formula) : Sequent :=
  match ξ with
  | .normal φ => ⟨∅, {~φ} ∪ R.pdlProjection A, none⟩
  | .loaded χ => ⟨∅, R.pdlProjection A, some (Sum.inr (~'χ))⟩

/-- At a fine node with a *basic* right component where a right rule is applied, that rule
is one of the three `PdlRule`s acting on the right.
Same as `FinePathIn.basicRightStep` in `Pdl.ClusterInterpolation`. -/
lemma basicRightStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesRightRule) (hb : f.label.rightOnly.basic) :
      (f.atBigRoot ∧ f.label.2.2 = none)
      ∨ (∃ g, f.children = {g} ∧ g.atBigRoot ∧ g.label.2.2 = none)
      ∨ (∃ A ξ, f.label.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, f.children = {g} ∧ g.atBigRoot
          ∧ g.label.left = (f.label.left).pdlProjection A
          ∧ g.label.rightOnly = modRChildRight A ξ f.label.2.1) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesRightRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [FinePathIn.label] at hb
      rw [X_def] at hb
      exact absurd hb (not_rightOnly_basic_of_isRightRule lra h)
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label, FinePathIn.children, FinePathIn.atBigRoot]
    cases r with
    | loadR hmem hnb hY => exact Or.inl ⟨trivial, rfl⟩
    | freeR hX hY =>
      exact Or.inr (Or.inl ⟨_, rfl, by simp [FinePathIn.atBigRoot],
        by simp [FinePathIn.label, hY]⟩)
    | @modR Y' L R A X' ξ hX hY =>
      subst hX
      right; right
      refine ⟨A, ξ, rfl, _, rfl, by simp [FinePathIn.atBigRoot], ?_, ?_⟩ <;>
        cases ξ <;> simp_all [modRChildRight, Sequent.rightOnly, FinePathIn.label]
    | _ => simp [PdlRule.isRightRule] at h
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.loc Y_in g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .loc Y_in g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.pdl g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .pdl g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)

/-- A fine node that is a node in the coarse sense has the label of that coarse node.
Same as `FinePathIn.label_eq_nodeAt_base` in `Pdl.ClusterInterpolation`. -/
lemma label_eq_nodeAt_base {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.atBigRoot) : f.label = nodeAt f.base := by
  have := congrArg FinePathIn.label (f.eq_toFine_base_of_atBigRoot h)
  rwa [PathIn.label_toFine] at this

/-- If a child of a local rule application is loaded on the right, then so is its premise.
Same as `LocalRuleApp.isRight_of_mem_C` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_C (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.2.2.isRight → lra.X.2.2.isRight := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  intro Y hY hYR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨res, -, rfl⟩ := hY
    simpa using hYR
  case oneSidedR ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨res, -, rfl⟩ := hY
    simpa using hYR
  case LRnegL => simp [applyLocalRule] at hY
  case LRnegR => simp [applyLocalRule] at hY
  case loadedL χ lrule YS_def =>
    exfalso
    subst YS_def
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨⟨Lnew, Onew⟩, -, rfl⟩ := hY
    rcases Onew with _ | o <;> simp_all [Olf.isRight]
  case loadedR χ lrule YS_def =>
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp [Olf.isRight]

/-- If some end node of a local tableau is loaded on the right, then so is its root.
Same as `LocalTableau.isRight_of_mem_endNodesOf` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_endNodesOf : ∀ {Z : Sequent} (lt : LocalTableau Z),
    ∀ Y ∈ endNodesOf lt, Y.2.2.isRight → Z.2.2.isRight
  | _, .sim _, Y, hY, hYR => by
      simp only [endNodesOf, Finset.mem_singleton] at hY
      exact hY ▸ hYR
  | _, .byLocalRule lra X_def next, Y, hY, hYR => by
      subst X_def
      simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup,
        Finset.mem_attach, true_and, Subtype.exists] at hY
      obtain ⟨W, W_in, hY⟩ := hY
      exact isRight_of_mem_C lra W W_in
        (isRight_of_mem_endNodesOf (next W W_in) Y hY hYR)

/-- The end nodes below a local path are end nodes of the local tableau at that path.
Same as `LocalPathIn.mem_endNodesOf_ltAt` in `Pdl.ClusterInterpolation`. -/
lemma mem_endNodesOf_ltAt {Z : Sequent} {lt : LocalTableau Z} (lp : LocalPathIn lt) :
    ∀ Yh ∈ lp.endNodesBelow, (Yh : Sequent) ∈ endNodesOf lp.ltAt := by
  induction lp with
  | nil => intro Yh _; exact Yh.2
  | cons Y_in tail IH =>
    intro Yh h
    simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h
    obtain ⟨Z, hZ, hmem, rfl⟩ := h
    exact IH ⟨Z, hZ⟩ hmem

/-- A fine node that is not a coarse node and has a coarse child loaded on the right is
itself loaded on the right.
Same as `FinePathIn.isRight_of_mem_coarseChildrenBelow` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      ∀ q ∈ f.coarseChildrenBelow, (nodeAt q).2.2.isRight → f.label.2.2.isRight
  | _, _, _, .inLoc lp _, _, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, hmem, rfl⟩ := hq
      rw [nodeAt_loc_nil] at hqR
      exact isRight_of_mem_endNodesOf lp.ltAt Y (mem_endNodesOf_ltAt lp ⟨Y, Y_in⟩ hmem) hqR
  | _, _, _, .pdlHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_loc] at hqR
      exact isRight_of_mem_coarseChildrenBelow tail
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR
  | _, _, _, .pdl tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_pdl] at hqR
      exact isRight_of_mem_coarseChildrenBelow tail
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR

variable {X : Sequent} {tab : Tableau .nil X}

/-- Lemma 9.4 (a) at the fine level: every fine node of a loaded cluster is loaded on the
right. For a coarse node this is `LoadedCluster.all_right_loaded`, and for a node inside a
local tableau it follows because that node has a coarse child in the cluster. -/
lemma isRight_of_memFine (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : C.memFine f) : f.label.2.2.isRight := by
  by_cases hbr : f.atBigRoot
  · rw [label_eq_nodeAt_base f hbr]
    exact C.all_right_loaded _ hf.1
  · rcases hf.2 with h | ⟨q, hq, hqC⟩
    · exact absurd h hbr
    · exact isRight_of_mem_coarseChildrenBelow f hbr q hq (C.all_right_loaded q hqC)

/-- Lemma 9.7 (e): at a node `t` of `C^R_Δ` with `Δ` basic the rule applied is the modal
rule `(M)` for the loaded formula `~⌊·A⌋ξ` of `Δ`, so that the right component of the
unique child of `t` only depends on `Δ`.
Same as `LoadedCluster.basicModalStepAt` in `Pdl.ClusterInterpolation`. -/
lemma basicModalStep (C : LoadedCluster tab) {Δ : Sequent}
    (hb : Δ.basic) {t : FinePathIn tab} (ht : t ∈ C.nodesWithFineRight Δ) :
    ∃ A ξ, Δ.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, t.children = {g}
      ∧ g.label.rightOnly = modRChildRight A ξ Δ.2.1 := by
  simp only [LoadedCluster.nodesWithFineRight, LoadedCluster.nodesWithFine, List.mem_filter,
    decide_eq_true_eq] at ht
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  have hDl : Δ.2.2 = t.label.2.2 := by rw [← ht_lab]; rfl
  have hDr : Δ.2.1 = t.label.2.1 := by rw [← ht_lab]; rfl
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rcases basicRightStep t ht_right (ht_lab ▸ hb) with
    ⟨hbr, hnone⟩ | ⟨g, hg, hgbr, hgnone⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
  · exfalso
    have hrl := C.all_right_loaded t.base hmf.1
    rw [← label_eq_nodeAt_base t hbr, hnone] at hrl
    simp at hrl
  · exfalso
    simp only [hg, Finset.mem_singleton] at hc
    subst hc
    have hrl := C.all_right_loaded c.base hcmf.1
    rw [← label_eq_nodeAt_base c hgbr, hgnone] at hrl
    simp at hrl
  · exact ⟨A, ξ, by rw [hDl]; exact hA, g, hg, by rw [hDr]; exact hg2⟩

/-- The key computation for condition U2: if the same local rule with the same principal
formulas is applied at two nodes with the same right component, then the right components
of the children agree, including their order. This holds because a local rule application
deletes the principal formulas from, and adds the results to, the given sequent. -/
lemma map_rightOnly_C_eq {lra₁ lra₂ : LocalRuleApp} (hsame : lra₁.SameRuleAs lra₂)
    (hX : lra₁.X.rightOnly = lra₂.X.rightOnly) :
    lra₁.C.image Sequent.rightOnly = lra₂.C.image Sequent.rightOnly := by
  obtain ⟨-, hRcond, hOcond, hress, -⟩ := hsame
  have hR : lra₁.R = lra₂.R := congrArg (fun Y => Y.2.1) hX
  have hO : lra₁.O = lra₂.O := congrArg (fun Y => Y.2.2) hX
  rw [lra₁.hC, lra₂.hC]
  simp only [applyLocalRule, Finset.image_image, Function.comp_def, Sequent.rightOnly]
  rw [hress]
  refine Finset.image_congr ?_
  rintro ⟨Lnew, Rnew, Onew⟩ -
  simp only [hRcond, hOcond, hR, hO]

end Uniformity

/-- In a uniform tableau any loaded cluster has the property `HasUniformSteps` needed for
the construction of the quasi-tableau: any two nodes of the cluster with the same right
component `Δ` at which a right rule is applied have the same right components below them.

The case where `Δ` is basic does not use uniformity: there the rule applied is the modal
rule for the loaded formula of `Δ` (Lemma 9.7 (e)). The case where `Δ` is not basic is
Lemma 9.7 (f), and uses both U1 and U2. -/
theorem LoadedCluster.uniformOfUniTab {tab : Tableau .nil X}
    (C : LoadedCluster tab) (uni_tab : tab.isUniform)
    : C.HasUniformSteps := by
  obtain ⟨u1, u2⟩ := uni_tab.1
  intro Δ f hf g hg
  have hf' := hf
  have hg' := hg
  simp only [LoadedCluster.nodesWithFineRight, LoadedCluster.nodesWithFine, List.mem_filter,
    decide_eq_true_eq] at hf' hg'
  obtain ⟨⟨hf_CL, hf_lab⟩, hf_right⟩ := hf'
  obtain ⟨⟨hg_CL, hg_lab⟩, hg_right⟩ := hg'
  by_cases hb : Δ.basic
  · -- Lemma 9.7 (e): the modal rule is applied at both nodes, to the loaded formula of `Δ`.
    obtain ⟨A, ξ, hAξ, cf, hcf, hcf_right⟩ := Uniformity.basicModalStep C hb hf
    obtain ⟨A', ξ', hAξ', cg, hcg, hcg_right⟩ := Uniformity.basicModalStep C hb hg
    have hAA : A' = A ∧ ξ' = ξ := by
      rw [hAξ] at hAξ'
      simp only [Option.some.injEq, Sum.inr.injEq] at hAξ'
      rcases ξ' with φ | χ <;> rcases ξ with φ' | χ' <;> simp_all
    rw [hAA.1, hAA.2] at hcg_right
    rw [hcf, hcg]
    simp only [Finset.image_singleton, hcf_right, hcg_right]
  · -- Lemma 9.7 (f): the same local rule is applied at both nodes, by U1 and U2.
    have hfb : ¬ f.label.basic := fun h => hb (hf_lab ▸ Uniformity.basic_rightOnly h)
    have hgb : ¬ g.label.basic := fun h => hb (hg_lab ▸ Uniformity.basic_rightOnly h)
    obtain ⟨lraf, hlraf, hfR⟩ :=
      (Uniformity.lra_or_basic_of_usesRightRule f hf_right).resolve_right hfb
    obtain ⟨lrag, hlrag, hgR⟩ :=
      (Uniformity.lra_or_basic_of_usesRightRule g hg_right).resolve_right hgb
    -- Both nodes are loaded on the right, being nodes of the cluster.
    have hfRight : f.label.2.2.isRight :=
      Uniformity.isRight_of_memFine C ((C.mem_fineCL f).mp hf_CL)
    have hgRight : g.label.2.2.isRight :=
      Uniformity.isRight_of_memFine C ((C.mem_fineCL g).mp hg_CL)
    -- By U1 their left components are basic, because a right rule is applied at them.
    have hfleft : f.label.leftFree.basic := by
      by_contra hcon
      exact f.not_left_and_right
        ⟨(u1 f (f.not_isLrep_base_of_usesRightRule hf_right)).1 hfRight hcon, hf_right⟩
    have hgleft : g.label.leftFree.basic := by
      by_contra hcon
      exact g.not_left_and_right
        ⟨(u1 g (g.not_isLrep_base_of_usesRightRule hg_right)).1 hgRight hcon, hg_right⟩
    -- Hence U2 applies.
    have hsame := (u2 f g lraf lrag hlraf hlrag).1 hfRight (hf_lab.trans hg_lab.symm)
      (hf_lab ▸ hb) hfleft hgleft hfR hgR
    obtain ⟨hfX, hfC⟩ := f.lraOpt_spec hlraf
    obtain ⟨hgX, hgC⟩ := g.lraOpt_spec hlrag
    have hXeq : lraf.X.rightOnly = lrag.X.rightOnly := by
      rw [← hfX, ← hgX, hf_lab, hg_lab]
    -- The right components of the children agree *as finite sets*:
    have hCeq : lraf.C.image Sequent.rightOnly = lrag.C.image Sequent.rightOnly :=
      Uniformity.map_rightOnly_C_eq hsame hXeq
    -- Hence so do the right components of the children of the two nodes, because the
    -- labels of the children are exactly the elements of `lraf.C` resp. `lrag.C`.
    calc f.children.image (fun h => h.label.rightOnly)
        = (f.children.image FinePathIn.label).image Sequent.rightOnly := by
          rw [Finset.image_image]; rfl
      _ = lraf.C.image Sequent.rightOnly := by rw [hfC]
      _ = lrag.C.image Sequent.rightOnly := hCeq
      _ = (g.children.image FinePathIn.label).image Sequent.rightOnly := by rw [hgC]
      _ = g.children.image (fun h => h.label.rightOnly) := by
          rw [Finset.image_image]; rfl

end PDL

run_cmd do
  let source := `LeanPool.PDL.Interpolation.UniformityCore
  let target := `LeanPool.PDL.Interpolation.Uniformity
  Lean.Elab.Command.liftCoreM (PDL.ImportCompatibility.retainPrivateDeclarations source target)
