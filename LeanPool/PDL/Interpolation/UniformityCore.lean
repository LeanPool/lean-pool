/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Local.AllLocalTab
public import LeanPool.PDL.Interpolation.FinePath
public import LeanPool.PDL.FlipCore

import Mathlib.Tactic.Bound.Init -- shake: keep

/-! # Canonical uniform local tableaux -/

@[expose] public section

namespace PDL

/-! ## The components of a sequent -/

/-- The left component of a sequent, together with the loaded formula, again as a sequent.
This is `Λ₁` from the paper; compare `Sequent.rightOnly`, which is `Λ₂`. -/
def Sequent.leftOnly (X : Sequent) : Sequent := ⟨X.1, ∅, X.2.2⟩

/-- The left component of a sequent, without any loaded formula. When the loaded formula
is on the right, i.e. in the situation of a `LoadedCluster`, this is the *unloaded*
component `Λ₁` of the node, and `Sequent.leftFree X |>.basic` says that no local rule is
applicable to it. -/
def Sequent.leftFree (X : Sequent) : Sequent := ⟨X.1, ∅, none⟩

/-- The right component of a sequent, without any loaded formula. When the loaded formula
is on the left this is the *unloaded* component `Λ₂` of the node. -/
def Sequent.rightFree (X : Sequent) : Sequent := ⟨∅, X.2.1, none⟩

/-- Two local rule applications use the same rule with the same principal formulas.
The fields `Lcond`, `Rcond` and `Ocond` are the principal formulas and `ress` is the list
of results of the rule, so this says that the *same rule instance* is applied at two nodes,
which may still have different sequents. -/
def LocalRuleApp.SameRuleAs (lra₁ lra₂ : LocalRuleApp) : Prop :=
  lra₁.Lcond = lra₂.Lcond ∧ lra₁.Rcond = lra₂.Rcond ∧ lra₁.Ocond = lra₂.Ocond
    ∧ lra₁.ress = lra₂.ress ∧ HEq lra₁.lr lra₂.lr

/-! ## Uniformity -/

/-- Condition U1: at a node with a loaded component, a rule is applied to the *unloaded*
component unless the latter is basic. Since every rule is a left rule or a right rule but
not both (`FinePathIn.not_left_and_right`), we state this as: a rule on the unloaded side
is applied.

The condition is only about nodes at which a rule is applied at all, i.e. we exclude the
leaves given by a loaded-path repeat, which is what `¬ f.base.isLrep` says. Note that this
exclusion is needed: at a loaded-path repeat the tableau stops, so no rule at all — and in
particular no rule on the unloaded component — is applied there, while the sequent of a
loaded-path repeat may well have a non-basic unloaded component. (For example, the sequent
reached again after a loop may contain a conjunction on the unloaded side; the tableau is
then forced to stop, because `Tableau.loc` and `Tableau.pdl` both require `¬ flprep`.)
Without the exclusion no tableau with such a repeat would be uniform, and `Tableau.toUniform`
would fail. -/
def Tableau.U1 {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  ∀ f : FinePathIn tab, ¬ f.base.isLrep →
      (f.label.2.2.isRight → ¬ f.label.leftFree.basic → f.usesLeftRule)
    ∧ (f.label.2.2.isLeft → ¬ f.label.rightFree.basic → f.usesRightRule)

/-- Condition U2: two nodes whose loaded component is the same and not basic, and whose
unloaded components are both basic, apply the same rule to the same formula of the loaded
component. As the loaded component is not basic the rule must be a local one, so we may
state this for the local rule applications `f.lraOpt` and `g.lraOpt`. -/
def Tableau.U2 {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  ∀ (f g : FinePathIn tab) (lraf lrag : LocalRuleApp),
      f.lraOpt = some lraf → g.lraOpt = some lrag →
      ( (f.label.2.2.isRight → f.label.rightOnly = g.label.rightOnly →
          ¬ f.label.rightOnly.basic → f.label.leftFree.basic → g.label.leftFree.basic →
          lraf.isRightRule → lrag.isRightRule → lraf.SameRuleAs lrag)
      ∧ (f.label.2.2.isLeft → f.label.leftOnly = g.label.leftOnly →
          ¬ f.label.leftOnly.basic → f.label.rightFree.basic → g.label.rightFree.basic →
          lraf.isLeftRule → lrag.isLeftRule → lraf.SameRuleAs lrag) )

/-- The conditions U1 and U2 together. -/
def Tableau.UniCore {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  tab.U1 ∧ tab.U2

/-- A sanity check that U1 and U2 are not contradictory: both conditions only constrain
nodes with a loaded component, so a tableau in which no node is loaded satisfies them. -/
lemma Tableau.uniCore_of_all_free {H : History} {X : Sequent} {tab : Tableau H X}
    (h : ∀ f : FinePathIn tab, f.label.2.2 = none) : tab.UniCore := by
  refine ⟨fun f _ => ⟨?_, ?_⟩, fun f g lraf lrag _ _ => ⟨?_, ?_⟩⟩ <;>
    intro hf <;> rw [h f] at hf <;> simp [Olf.isRight, Olf.isLeft] at hf

/-- A tableau is *uniform* if it satisfies the conditions U1 and U2.

We also demand U1 and U2 for the flipped tableau `tab.flip`, in which the left and the
right components of all sequents are swapped. This is not an extra demand: U1 and U2 are
symmetric in the two components, so `tab.UniCore` and `tab.flip.UniCore` say the same
thing. Asking for both here only spares us the purely technical work of transporting U1
and U2 along `Tableau.flip`, which would need a `flip` operation on `FinePathIn`.
What it buys us is `Tableau.isUniform.flip` below, which is needed because the
interpolation proof flips the tableau when the loaded formula is on the left. -/
def Tableau.isUniform {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  tab.UniCore ∧ tab.flip.UniCore

/-- Transporting `Tableau.UniCore` along an equality of tableaux. -/
lemma Tableau.UniCore.heq_transfer {H₁ X₁ H₂ X₂} {t₁ : Tableau H₁ X₁} {t₂ : Tableau H₂ X₂}
    (hH : H₁ = H₂) (hX : X₁ = X₂) (h : HEq t₁ t₂) (h₁ : t₁.UniCore) : t₂.UniCore := by
  subst hH
  subst hX
  cases eq_of_heq h
  exact h₁

/-- Uniformity is preserved by flipping the tableau. -/
lemma Tableau.isUniform.flip {H : History} {X : Sequent} {tab : Tableau H X}
    (h : tab.isUniform) : tab.flip.isUniform :=
  ⟨h.2, Tableau.UniCore.heq_transfer Hist_flip.symm Sequent.flip_flip.symm
    (HEq.symm (flip_aux_Tableau_flip_flip_heq tab)) h.1⟩

/-! ## Uniform tableaux by construction

To obtain uniform tableaux we follow approach (B): instead of repairing a given tableau we
describe how a uniform one is built, by fixing *which* local rule is applied at each node.
The conditions U1 and U2 only speak about the local rules applied at the nodes, and both are
conditions that can be read off a single rule application together with the sequent it is
applied to. This is what `LocalRuleApp.IsUniChoice` below says:

* the rule is applied to the unloaded component, unless that component is basic (U1); and
* if it is applied to the loaded component (the unloaded one then being basic) then it is
  *the* canonical rule for that component, given by `uniRightChoice` resp. `uniLeftChoice`.

Since the canonical rule only depends on the loaded component `Λᵢ(s)`, any two nodes with
the same loaded component use the same rule, which is U2. A tableau all of whose rule
applications are `IsUniChoice` is called `Tableau.IsUni`, and `Tableau.IsUni.uniCore` shows
that such a tableau indeed satisfies U1 and U2. The construction is symmetric under flipping
(`Tableau.IsUni.flip`), which gives the second half of `Tableau.isUniform`. -/

/-! ### Flipping components, rules and rule applications -/

@[simp]
lemma LocalRuleApp.flip_O (lra : LocalRuleApp) : (lra.flip).O = lra.O.flip := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩; rfl

lemma LocalRuleApp.flip_X (lra : LocalRuleApp) : (lra.flip).X = lra.X.flip := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp [LocalRuleApp.flip, Sequent.flip]

@[simp]
lemma LocalRuleApp.flip_isRightRule (lra : LocalRuleApp) :
    (lra.flip).isRightRule = lra.isLeftRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;> simp [LocalRuleApp.flip, LocalRuleApp.isRightRule, LocalRuleApp.isLeftRule,
      LocalRule.isRightRule, LocalRule.isLeftRule, LocalRule.flip]

@[simp]
lemma LocalRuleApp.flip_isLeftRule (lra : LocalRuleApp) :
    (lra.flip).isLeftRule = lra.isRightRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;> simp [LocalRuleApp.flip, LocalRuleApp.isRightRule, LocalRuleApp.isLeftRule,
      LocalRule.isRightRule, LocalRule.isLeftRule, LocalRule.flip]

@[simp]
lemma Sequent.flip_leftFree {X : Sequent} : X.flip.leftFree = X.rightFree.flip := by
  rcases X with ⟨L, R, O⟩; rfl

@[simp]
lemma Sequent.flip_rightFree {X : Sequent} : X.flip.rightFree = X.leftFree.flip := by
  rcases X with ⟨L, R, O⟩; rfl

@[simp]
lemma Sequent.flip_rightOnly {X : Sequent} : X.flip.rightOnly = X.leftOnly.flip := by
  rcases X with ⟨L, R, O⟩; simp [Sequent.flip, Sequent.rightOnly, Sequent.leftOnly]

@[simp]
lemma Sequent.flip_leftOnly {X : Sequent} : X.flip.leftOnly = X.rightOnly.flip := by
  rcases X with ⟨L, R, O⟩; simp [Sequent.flip, Sequent.rightOnly, Sequent.leftOnly]

/-- Being the same rule is preserved by flipping. -/
lemma LocalRuleApp.SameRuleAs.flip {lra₁ lra₂ : LocalRuleApp} (h : lra₁.SameRuleAs lra₂) :
    lra₁.flip.SameRuleAs lra₂.flip := by
  obtain ⟨hL, hR, hO, hress, hlr⟩ := h
  rcases lra₁ with ⟨L₁, R₁, O₁, Lcond₁, Rcond₁, Ocond₁, ress₁, lr₁, C₁, hC₁, pre₁⟩
  rcases lra₂ with ⟨L₂, R₂, O₂, Lcond₂, Rcond₂, Ocond₂, ress₂, lr₂, C₂, hC₂, pre₂⟩
  simp_all only
  subst hL; subst hR; subst hO; subst hress
  cases eq_of_heq hlr
  exact ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Being the same rule is reflexive. -/
lemma LocalRuleApp.SameRuleAs.refl (lra : LocalRuleApp) : lra.SameRuleAs lra :=
  ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Being the same rule is symmetric. -/
lemma LocalRuleApp.SameRuleAs.symm {lra₁ lra₂ : LocalRuleApp} (h : lra₁.SameRuleAs lra₂) :
    lra₂.SameRuleAs lra₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- Being the same rule is transitive. -/
lemma LocalRuleApp.SameRuleAs.trans {lra₁ lra₂ lra₃ : LocalRuleApp}
    (h : lra₁.SameRuleAs lra₂) (h' : lra₂.SameRuleAs lra₃) : lra₁.SameRuleAs lra₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

/-! ### The canonical rule for a component -/

/-- The canonical local rule to be applied to the right component of a sequent.
We use the first right rule in the list `LocalRuleApp.all` of all applicable rules.
Which rule exactly is picked does not matter for uniformity; all that matters is that
this is a *function* of the sequent — and that it is applied to sequents of the form
`X.rightOnly`, so that it only depends on the right component. -/
def uniRightChoice (Y : Sequent) : Option LocalRuleApp :=
  (LocalRuleApp.all Y).find? (fun lra => lra.isRightRule)

/-- The canonical local rule to be applied to the left component of a sequent.
Defined as the flip of `uniRightChoice`, which makes the whole construction symmetric. -/
def uniLeftChoice (Y : Sequent) : Option LocalRuleApp :=
  (uniRightChoice Y.flip).map LocalRuleApp.flip

lemma uniLeftChoice_flip (Y : Sequent) :
    uniLeftChoice Y.flip = (uniRightChoice Y).map LocalRuleApp.flip := by
  simp [uniLeftChoice]

lemma uniRightChoice_flip (Y : Sequent) :
    uniRightChoice Y.flip = (uniLeftChoice Y).map LocalRuleApp.flip := by
  simp [uniLeftChoice, Option.map_map, Function.comp_def, LocalRuleApp.flip_flip]

/-! ### Uniform rule applications -/

/-- The conditions on a single local rule application in a uniform tableau: the first two
fields are the local form of U1 and the last two are the local form of U2. -/
structure LocalRuleApp.IsUniChoice (lra : LocalRuleApp) : Prop where
  /-- If loaded on the right and the left component is not basic, a left rule is applied. -/
  leftFirst : lra.X.2.2.isRight → ¬ lra.X.leftFree.basic → lra.isLeftRule
  /-- If loaded on the left and the right component is not basic, a right rule is applied. -/
  rightFirst : lra.X.2.2.isLeft → ¬ lra.X.rightFree.basic → lra.isRightRule
  /-- A right rule applied at a node loaded on the right whose left component is basic is
  the canonical rule for the right component. -/
  rightCanon : lra.isRightRule → lra.X.2.2.isRight → lra.X.leftFree.basic →
      ∃ lrb, uniRightChoice lra.X.rightOnly = some lrb ∧ lra.SameRuleAs lrb
  /-- A left rule applied at a node loaded on the left whose right component is basic is
  the canonical rule for the left component. -/
  leftCanon : lra.isLeftRule → lra.X.2.2.isLeft → lra.X.rightFree.basic →
      ∃ lrb, uniLeftChoice lra.X.leftOnly = some lrb ∧ lra.SameRuleAs lrb

/-- The conditions on rule applications are symmetric under flipping. -/
lemma LocalRuleApp.IsUniChoice.flip {lra : LocalRuleApp} (h : lra.IsUniChoice) :
    lra.flip.IsUniChoice := by
  have hXf : lra.flip.X = lra.X.flip := LocalRuleApp.flip_X lra
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have h1' : lra.X.2.2.isLeft := by
      rw [hXf] at h1; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h2' : ¬ lra.X.rightFree.basic := by
      rw [hXf] at h2; simpa using h2
    simpa using h.rightFirst h1' h2'
  · intro h1 h2
    have h1' : lra.X.2.2.isRight := by
      rw [hXf] at h1; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h2' : ¬ lra.X.leftFree.basic := by
      rw [hXf] at h2; simpa using h2
    simpa using h.leftFirst h1' h2'
  · intro h1 h2 h3
    have h1' : lra.isLeftRule := by simpa using h1
    have h2' : lra.X.2.2.isLeft := by
      rw [hXf] at h2; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h3' : lra.X.rightFree.basic := by
      rw [hXf] at h3; simpa using h3
    obtain ⟨lrb, hb, hsame⟩ := h.leftCanon h1' h2' h3'
    refine ⟨lrb.flip, ?_, hsame.flip⟩
    rw [hXf, Sequent.flip_rightOnly, uniRightChoice_flip, hb]
    rfl
  · intro h1 h2 h3
    have h1' : lra.isRightRule := by simpa using h1
    have h2' : lra.X.2.2.isRight := by
      rw [hXf] at h2; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h3' : lra.X.leftFree.basic := by
      rw [hXf] at h3; simpa using h3
    obtain ⟨lrb, hb, hsame⟩ := h.rightCanon h1' h2' h3'
    refine ⟨lrb.flip, ?_, hsame.flip⟩
    rw [hXf, Sequent.flip_leftOnly, uniLeftChoice_flip, hb]
    rfl

/-! ### Basic sequents have basic components -/

lemma Sequent.leftFree_basic_of_basic {X : Sequent} (h : X.basic) : X.leftFree.basic := by
  rcases X with ⟨L, R, o⟩
  rcases h with ⟨hall, hcl⟩
  refine ⟨fun f hf => hall f ?_, ?_⟩
  · simp only [Sequent.leftFree, Sequent.toFinset, Finset.union_empty, Finset.union_assoc,
      Finset.mem_union] at hf ⊢
    tauto
  · rintro (hbot | ⟨f, hf, hnf⟩)
    · exact hcl (Or.inl (by simp_all [Sequent.leftFree, Sequent.mem_def]))
    · exact hcl (Or.inr ⟨f, by simp_all [Sequent.leftFree, Sequent.mem_def]⟩)

lemma Sequent.rightFree_basic_of_basic {X : Sequent} (h : X.basic) : X.rightFree.basic := by
  rcases X with ⟨L, R, o⟩
  rcases h with ⟨hall, hcl⟩
  refine ⟨fun f hf => hall f ?_, ?_⟩
  · simp only [Sequent.rightFree, Sequent.toFinset, Finset.empty_union, Finset.union_assoc,
      Finset.mem_union] at hf ⊢
    tauto
  · rintro (hbot | ⟨f, hf, hnf⟩)
    · exact hcl (Or.inl (by simp_all [Sequent.rightFree, Sequent.mem_def]))
    · exact hcl (Or.inr ⟨f, by simp_all [Sequent.rightFree, Sequent.mem_def]⟩)

/-- All local rule applications inside a local tableau are uniform choices. -/
def LocalTableau.IsUni : {X : Sequent} → LocalTableau X → Prop
  | _, (.sim _) => True
  | _, (.byLocalRule lra _ next) =>
      lra.IsUniChoice ∧ ∀ Y, ∀ h : Y ∈ lra.C, (next Y h).IsUni

/-- All local rule applications inside a tableau are uniform choices. -/
def Tableau.IsUni : {H : History} → {X : Sequent} → Tableau H X → Prop
  | _, _, .loc _ _ lt next => lt.IsUni ∧ ∀ Y, ∀ h : Y ∈ endNodesOf lt, (next Y h).IsUni
  | _, _, .pdl _ _ _ next => next.IsUni
  | _, _, .lrep _ => True

lemma LocalTableau.IsUni.ltAt {X} {lt : LocalTableau X} (h : lt.IsUni) (lp : LocalPathIn lt) :
    (lp.ltAt).IsUni := by
  induction lp
  case nil => exact h
  case cons X lra X_def next Y Y_in tail IH =>
    rw [LocalTableau.IsUni] at h
    exact IH (h.2 Y Y_in)

lemma Tableau.IsUni.lraOpt_isUniChoice {H X} {tab : Tableau H X} (h : tab.IsUni)
    {f : FinePathIn tab} {lra : LocalRuleApp} (hf : f.lraOpt = some lra) : lra.IsUniChoice := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    rw [Tableau.IsUni] at h
    have hlt := h.1.ltAt lp
    simp only [FinePathIn.lraOpt] at hf
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hltAt] at hf hlt
      simp only [Option.some.injEq] at hf
      subst hf
      rw [LocalTableau.IsUni] at hlt
      exact hlt.1
    · rw [hltAt] at hf; simp at hf
  case pdlHere => simp [FinePathIn.lraOpt] at hf
  case lrepHere => simp [FinePathIn.lraOpt] at hf
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    rw [Tableau.IsUni] at h
    exact IH (h.2 Y Y_in) hf
  case pdl IH =>
    rw [Tableau.IsUni] at h
    exact IH h hf

lemma FinePathIn.usesLeftRule_eq_of_lraOpt {H X} {tab : Tableau H X} {f : FinePathIn tab}
    {lra : LocalRuleApp} (hf : f.lraOpt = some lra) : f.usesLeftRule = lra.isLeftRule := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lraOpt, FinePathIn.usesLeftRule] at *
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas <;> simp_all
  case pdlHere => simp [FinePathIn.lraOpt] at hf
  case lrepHere => simp [FinePathIn.lraOpt] at hf
  case loc IH => simpa [FinePathIn.usesLeftRule] using IH (by simpa [FinePathIn.lraOpt] using hf)
  case pdl IH => simpa [FinePathIn.usesLeftRule] using IH (by simpa [FinePathIn.lraOpt] using hf)

lemma FinePathIn.usesRightRule_eq_of_lraOpt {H X} {tab : Tableau H X} {f : FinePathIn tab}
    {lra : LocalRuleApp} (hf : f.lraOpt = some lra) : f.usesRightRule = lra.isRightRule := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lraOpt, FinePathIn.usesRightRule] at *
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas <;> simp_all
  case pdlHere => simp [FinePathIn.lraOpt] at hf
  case lrepHere => simp [FinePathIn.lraOpt] at hf
  case loc IH => simpa [FinePathIn.usesRightRule] using IH (by simpa [FinePathIn.lraOpt] using hf)
  case pdl IH => simpa [FinePathIn.usesRightRule] using IH (by simpa [FinePathIn.lraOpt] using hf)

lemma FinePathIn.isLrep_or_basic_of_lraOpt_eq_none {H X} {tab : Tableau H X} {f : FinePathIn tab}
    (hf : f.lraOpt = none) : f.base.isLrep ∨ f.label.basic := by
  induction f
  case inLoc lp lp_int =>
    exfalso
    simp only [FinePathIn.lraOpt] at hf
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hltAt] at hf; simp at hf
    · exact absurd lp_int (by simp [LocalPathIn.isInternal, hltAt, LocalTableau.hasRule])
  case pdlHere Hist X Y nrep bas r next => exact Or.inr bas
  case lrepHere => exact Or.inl (by simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep])
  case loc IH =>
    rcases IH (by simpa [FinePathIn.lraOpt] using hf) with h | h
    · exact Or.inl (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
    · exact Or.inr (by simpa [FinePathIn.label] using h)
  case pdl IH =>
    rcases IH (by simpa [FinePathIn.lraOpt] using hf) with h | h
    · exact Or.inl (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
    · exact Or.inr (by simpa [FinePathIn.label] using h)

theorem Tableau.IsUni.uniCore {H X} {tab : Tableau H X} (h : tab.IsUni) : tab.UniCore := by
  constructor
  · -- U1
    intro f hnlrep
    rcases hl : f.lraOpt with _ | lra
    · rcases FinePathIn.isLrep_or_basic_of_lraOpt_eq_none hl with hb | hbas
      · exact absurd hb hnlrep
      · exact ⟨fun _ hcon => absurd (Sequent.leftFree_basic_of_basic hbas) hcon,
               fun _ hcon => absurd (Sequent.rightFree_basic_of_basic hbas) hcon⟩
    · have hu := h.lraOpt_isUniChoice hl
      have hX : f.label = lra.X := (f.lraOpt_spec hl).1
      constructor
      · intro h1 h2
        rw [FinePathIn.usesLeftRule_eq_of_lraOpt hl]
        exact hu.leftFirst (hX ▸ h1) (hX ▸ h2)
      · intro h1 h2
        rw [FinePathIn.usesRightRule_eq_of_lraOpt hl]
        exact hu.rightFirst (hX ▸ h1) (hX ▸ h2)
  · -- U2
    intro f g lraf lrag hf hg
    have huf := h.lraOpt_isUniChoice hf
    have hug := h.lraOpt_isUniChoice hg
    have hXf : f.label = lraf.X := (f.lraOpt_spec hf).1
    have hXg : g.label = lrag.X := (g.lraOpt_spec hg).1
    constructor
    · intro hfR hfg _ hfl hgl hfRule hgRule
      have hOeq : f.label.2.2 = g.label.2.2 := congrArg (fun Y => Y.2.2) hfg
      have hgR : g.label.2.2.isRight := hOeq ▸ hfR
      obtain ⟨lrb, hb, hsame⟩ := huf.rightCanon hfRule (hXf ▸ hfR) (hXf ▸ hfl)
      obtain ⟨lrb', hb', hsame'⟩ := hug.rightCanon hgRule (hXg ▸ hgR) (hXg ▸ hgl)
      have : lrb = lrb' := by
        rw [← hXf, hfg] at hb
        rw [← hXg] at hb'
        exact Option.some.inj (hb.symm.trans hb')
      exact hsame.trans (this ▸ hsame'.symm)
    · intro hfL hfg _ hfr hgr hfRule hgRule
      have hOeq : f.label.2.2 = g.label.2.2 := congrArg (fun Y => Y.2.2) hfg
      have hgL : g.label.2.2.isLeft := hOeq ▸ hfL
      obtain ⟨lrb, hb, hsame⟩ := huf.leftCanon hfRule (hXf ▸ hfL) (hXf ▸ hfr)
      obtain ⟨lrb', hb', hsame'⟩ := hug.leftCanon hgRule (hXg ▸ hgL) (hXg ▸ hgr)
      have : lrb = lrb' := by
        rw [← hXf, hfg] at hb
        rw [← hXg] at hb'
        exact Option.some.inj (hb.symm.trans hb')
      exact hsame.trans (this ▸ hsame'.symm)

lemma LocalTableau.IsUni_cast {A B : Sequent} (h : A = B) (t : LocalTableau A) :
    (h ▸ t).IsUni ↔ t.IsUni := by subst h; rfl

lemma Tableau.IsUni_cast {H} {A B : Sequent} (h : A = B) (t : Tableau H A) :
    (h ▸ t).IsUni ↔ t.IsUni := by subst h; rfl

lemma LocalTableau.IsUni.flip {X} {lt : LocalTableau X} (h : lt.IsUni) : (lt.flip).IsUni := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    rw [LocalTableau.IsUni] at h
    rw [LocalTableau.flip, LocalTableau.IsUni]
    refine ⟨h.1.flip, ?_⟩
    intro Y Y_in
    rw [LocalTableau.IsUni_cast]
    exact IH _ (Sequent.flip_mem_of_mem_image_flip Y_in) (h.2 _ _)
  case sim bas => rw [LocalTableau.flip, LocalTableau.IsUni]; trivial

lemma Tableau.IsUni.flip {H X} {tab : Tableau H X} (h : tab.IsUni) : (tab.flip).IsUni := by
  induction tab
  case loc Hist X nrep nbas lt next IH =>
    rw [Tableau.IsUni] at h
    rw [Tableau.flip, Tableau.IsUni]
    refine ⟨h.1.flip, ?_⟩
    intro Y Y_in
    rw [Tableau.IsUni_cast]
    exact IH _ (endNodesOf_flip Y_in) (h.2 _ _)
  case pdl IH =>
    rw [Tableau.IsUni] at h
    rw [Tableau.flip, Tableau.IsUni]
    exact IH h
  case lrep => trivial

/-- A tableau all of whose local rule applications are uniform choices is uniform. -/
theorem Tableau.IsUni.isUniform {X} {tab : Tableau .nil X} (h : tab.IsUni) : tab.isUniform :=
  ⟨h.uniCore, h.flip.uniCore⟩

/-! ## Building a uniform tableau

We now show `Tableau.exists_isUni`: for every tableau there is one that applies the rules in
the canonical order. The construction is deterministic: `uniChoiceAt` picks, at each sequent,
the canonical rule application (first a rule for the unloaded component, and once that is
basic the canonical rule for the loaded component), and `uniLocalTab` iterates this to a
local tableau all of whose rule applications are uniform choices (`uniLocalTab_isUni`).

Given an arbitrary tableau we then re-build it, replacing the local tableau at each `loc`
step by the canonical one. Because the end nodes of the canonical local tableau need not be
literally the same lists as the end nodes of the original one, we prove the statement in the
more flexible form `Tableau.exists_isUni_of_msEq`, allowing the sequent and the history to
change up to `Sequent.multisetEqTo`, i.e. up to permutation of the two lists in a sequent.
That the calculus does not care about such permutations is `PdlRule.exists_of_multisetEqTo`
and `lpr_of_multisetEqTo`.

The only step that is left open is `uniLocalTab_endNode_dominated`. -/

/-- Put a local rule application into a different context, keeping the rule itself. -/
def LocalRuleApp.inContext (lra : LocalRuleApp) (L R : Finset Formula) (O : Olf)
    (hL : lra.Lcond ⊆ L) (hR : lra.Rcond ⊆ R) (hO : lra.Ocond ⊆ O) :
    LocalRuleApp :=
  { L := L, R := R, O := O,
    Lcond := lra.Lcond, Rcond := lra.Rcond, Ocond := lra.Ocond,
    ress := lra.ress, lr := lra.lr,
    C := applyLocalRule lra.lr (L, R, O), hC := rfl,
    preconditionProof := ⟨hL, hR, hO⟩ }

/-- Put a local rule application into the context of the sequent `X`, if possible. -/
def LocalRuleApp.toContext (lra : LocalRuleApp) (X : Sequent) : LocalRuleApp :=
  if h : lra.Lcond ⊆ X.1 ∧ lra.Rcond ⊆ X.2.1 ∧ lra.Ocond ⊆ X.2.2 then
    lra.inContext X.1 X.2.1 X.2.2 h.1 h.2.1 h.2.2
  else lra

lemma LocalRuleApp.toContext_sameRuleAs (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).SameRuleAs lra := by
  unfold LocalRuleApp.toContext
  split
  · exact ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩
  · exact LocalRuleApp.SameRuleAs.refl lra

@[simp]
lemma LocalRuleApp.toContext_isLeftRule (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).isLeftRule = lra.isLeftRule := by
  unfold LocalRuleApp.toContext
  split <;> rfl

@[simp]
lemma LocalRuleApp.toContext_isRightRule (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).isRightRule = lra.isRightRule := by
  unfold LocalRuleApp.toContext
  split <;> rfl

lemma LocalRuleApp.toContext_X (lra : LocalRuleApp) (X : Sequent)
    (h : lra.Lcond ⊆ X.1 ∧ lra.Rcond ⊆ X.2.1 ∧ lra.Ocond ⊆ X.2.2) :
    (lra.toContext X).X = X := by
  unfold LocalRuleApp.toContext
  rw [dite_eq_left h]
  rfl

lemma uniRightChoice_spec {Y : Sequent} {lra : LocalRuleApp} (h : uniRightChoice Y = some lra) :
    lra.X = Y ∧ lra.isRightRule := by
  unfold uniRightChoice at h
  exact ⟨LocalRuleApp.all_X Y lra (List.mem_of_find?_eq_some h), by
    simpa using List.find?_some h⟩

lemma uniRightChoice_isSome {Y : Sequent} {lra : LocalRuleApp} (hX : lra.X = Y)
    (hr : lra.isRightRule) : (uniRightChoice Y).isSome := by
  unfold uniRightChoice
  rcases h : (LocalRuleApp.all Y).find? (fun lra => lra.isRightRule) with _ | lrb
  · exfalso
    rw [List.find?_eq_none] at h
    exact h lra (hX ▸ lra.all_spec) (by simpa using hr)
  · rw [h]; rfl

lemma uniLeftChoice_spec {Y : Sequent} {lra : LocalRuleApp} (h : uniLeftChoice Y = some lra) :
    lra.X = Y ∧ lra.isLeftRule := by
  unfold uniLeftChoice at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨lrb, hb, rfl⟩ := h
  obtain ⟨hX, hr⟩ := uniRightChoice_spec hb
  refine ⟨?_, by simpa using hr⟩
  rw [LocalRuleApp.flip_X, hX, Sequent.flip_flip]

lemma uniLeftChoice_isSome {Y : Sequent} {lra : LocalRuleApp} (hX : lra.X = Y)
    (hl : lra.isLeftRule) : (uniLeftChoice Y).isSome := by
  unfold uniLeftChoice
  have : (uniRightChoice Y.flip).isSome := by
    refine uniRightChoice_isSome (lra := lra.flip) ?_ (by simpa using hl)
    rw [LocalRuleApp.flip_X, hX]
  simpa using this

/-! ### Shapes of left and right rules -/

lemma LocalRuleApp.isLeftRule_shape {lra : LocalRuleApp} (h : lra.isLeftRule) :
    lra.Rcond = ∅ ∧ (lra.Ocond = none ∨ lra.Ocond.isLeft) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp_all [LocalRuleApp.isLeftRule, LocalRule.isLeftRule, Olf.isLeft]

lemma LocalRuleApp.isRightRule_shape {lra : LocalRuleApp} (h : lra.isRightRule) :
    lra.Lcond = ∅ ∧ (lra.Ocond = none ∨ lra.Ocond.isRight) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp_all [LocalRuleApp.isRightRule, LocalRule.isRightRule, Olf.isRight]

/-- Any local rule applicable to a sequent of the shape `(L, ∅, none)` is a left rule. -/
lemma LocalRuleApp.isLeftRule_of_X_eq {lra : LocalRuleApp} {L : Finset Formula}
    (h : lra.X = (L, ∅, none)) : lra.isLeftRule := by
  rcases lra with ⟨L', R', O', Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨preL, preR, preO⟩ := pre
  cases lr
  case oneSidedL => simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule]
  case oneSidedR orule YS_def =>
    exact absurd (Finset.subset_empty.mp preR) (orule.precond_ne_nil)
  case LRnegL φ => simp at preR
  case LRnegR φ => simp at preR
  case loadedL => simp at preO
  case loadedR => simp at preO

/-! ### Moving rules between a sequent and its components -/

lemma LocalRuleApp.toContext_X_of_leftOnly {lra : LocalRuleApp} {X : Sequent}
    (h : lra.X = X.leftOnly) : (lra.toContext X).X = X := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = X.1 := congrArg (fun Y => Y.1) h
  have hR : lra.R = ∅ := congrArg (fun Y => Y.2.1) h
  have hO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) h
  refine lra.toContext_X X ⟨hL ▸ preL, ?_, hO ▸ preO⟩
  rw [hR] at preR
  rw [Finset.subset_empty.mp preR]
  exact Finset.empty_subset _

lemma LocalRuleApp.toContext_X_of_rightOnly {lra : LocalRuleApp} {X : Sequent}
    (h : lra.X = X.rightOnly) : (lra.toContext X).X = X := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = ∅ := congrArg (fun Y => Y.1) h
  have hR : lra.R = X.2.1 := congrArg (fun Y => Y.2.1) h
  have hO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) h
  refine lra.toContext_X X ⟨?_, hR ▸ preR, hO ▸ preO⟩
  rw [hL] at preL
  rw [Finset.subset_empty.mp preL]
  exact Finset.empty_subset _

lemma LocalRuleApp.toContext_rightOnly_X {lra : LocalRuleApp} {X : Sequent}
    (hX : lra.X = X) (hr : lra.isRightRule) : (lra.toContext X.rightOnly).X = X.rightOnly := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  subst hX
  refine lra.toContext_X _ ⟨?_, preR, preO⟩
  rw [(LocalRuleApp.isRightRule_shape hr).1]
  exact Finset.empty_subset _

/-! ### When is the canonical choice available? -/

lemma exists_localRuleApp_of_not_basic {Y : Sequent} (h : ¬ Y.basic) :
    ∃ lra : LocalRuleApp, lra.X = Y := by
  by_contra hcon
  exact h (basic_iff_noLocalRuleApp.mpr hcon)

lemma uniLeftChoice_leftOnly_isSome {X : Sequent} (h : ¬ X.leftFree.basic) :
    (uniLeftChoice X.leftOnly).isSome := by
  obtain ⟨lra, hlra⟩ := exists_localRuleApp_of_not_basic h
  have hl : lra.isLeftRule := LocalRuleApp.isLeftRule_of_X_eq hlra
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = X.1 := congrArg (fun Y => Y.1) hlra
  have hR : lra.R = ∅ := congrArg (fun Y => Y.2.1) hlra
  have hO : lra.O = none := congrArg (fun Y => Y.2.2) hlra
  have hOc : lra.Ocond = none := by
    rw [hO] at preO
    rcases hOcond : lra.Ocond with _|(a|b) <;> simp_all
  refine uniLeftChoice_isSome (lra := lra.toContext X.leftOnly) ?_ (by simpa using hl)
  refine lra.toContext_X X.leftOnly ⟨hL ▸ preL, ?_, by simp [hOc, Sequent.leftOnly]⟩
  rw [(LocalRuleApp.isLeftRule_shape hl).1]
  exact Finset.empty_subset _

lemma uniLeftChoice_leftOnly_eq_none {X : Sequent} (hb : X.leftFree.basic)
    (hO : ¬ X.2.2.isLeft) : uniLeftChoice X.leftOnly = none := by
  rcases hc : uniLeftChoice X.leftOnly with _ | lra
  · rfl
  exfalso
  obtain ⟨hX, hl⟩ := uniLeftChoice_spec hc
  obtain ⟨hRcond, hOcond⟩ := LocalRuleApp.isLeftRule_shape hl
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hLL : lra.L = X.1 := congrArg (fun Y => Y.1) hX
  have hOO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) hX
  have hOc : lra.Ocond = none := by
    rcases hOcond with h' | h'
    · exact h'
    · exfalso
      rw [hOO] at preO
      rcases hOcond' : lra.Ocond with _|(a|b) <;> rcases hX22 : X.2.2 with _|(c|d) <;>
        simp_all [Olf.isLeft]
  have : ∃ lra' : LocalRuleApp, lra'.X = X.leftFree := by
    refine ⟨lra.toContext X.leftFree, ?_⟩
    refine lra.toContext_X X.leftFree ⟨hLL ▸ preL, ?_, by simp [hOc, Sequent.leftFree]⟩
    rw [hRcond]
    exact Finset.empty_subset _
  exact (basic_iff_noLocalRuleApp.mp hb) this

lemma uniRightChoice_rightOnly_isSome {X : Sequent} {lra : LocalRuleApp} (hX : lra.X = X)
    (hr : lra.isRightRule) : (uniRightChoice X.rightOnly).isSome :=
  uniRightChoice_isSome (lra := lra.toContext X.rightOnly)
    (lra.toContext_rightOnly_X hX hr) (by simpa using hr)

/-! ### The canonical rule choice -/

open Classical in
/-- The canonical rule application for a sequent that is free or loaded on the right:
first reduce the left component, then use the canonical rule for the right component. -/
def uniChoiceRL (X : Sequent) : Option LocalRuleApp :=
  match uniLeftChoice X.leftOnly with
  | some lra => some (lra.toContext X)
  | none =>
    match uniRightChoice X.rightOnly with
    | some lra => some (lra.toContext X)
    | none => (LocalRuleApp.all X).head?

lemma uniChoiceRL_X {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceRL X = some lra) :
    lra.X = X := by
  unfold uniChoiceRL at h
  rcases hl : uniLeftChoice X.leftOnly with _ | lrl
  · rcases hr : uniRightChoice X.rightOnly with _ | lrr
    · rw [hl, hr] at h
      simp only at h
      exact LocalRuleApp.all_X X lra (List.mem_of_mem_head? h)
    · rw [hl, hr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact LocalRuleApp.toContext_X_of_rightOnly (uniRightChoice_spec hr).1
  · rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    exact LocalRuleApp.toContext_X_of_leftOnly (uniLeftChoice_spec hl).1

lemma uniChoiceRL_isSome {X : Sequent} (h : ¬ X.basic) : (uniChoiceRL X).isSome := by
  unfold uniChoiceRL
  rcases hl : uniLeftChoice X.leftOnly with _ | lrl
  · rcases hr : uniRightChoice X.rightOnly with _ | lrr
    · simp only [Option.isSome]
      rcases hh : (LocalRuleApp.all X).head? with _ | lra
      · exfalso
        rw [List.head?_eq_none_iff] at hh
        exact LocalRuleApp.all_nonempty_of_nonbasic h hh
      · rfl
    · rfl
  · rfl

lemma uniChoiceRL_isUniChoice {X : Sequent} {lra : LocalRuleApp} (hnl : ¬ X.2.2.isLeft)
    (h : uniChoiceRL X = some lra) : lra.IsUniChoice := by
  have hX : lra.X = X := uniChoiceRL_X h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- leftFirst
    intro _ h2
    have h2' : ¬ X.leftFree.basic := by rwa [hX] at h2
    obtain ⟨lrl, hl⟩ := Option.isSome_iff_exists.mp (uniLeftChoice_leftOnly_isSome h2')
    unfold uniChoiceRL at h
    rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    simpa using (uniLeftChoice_spec hl).2
  · -- rightFirst
    intro h1
    exact absurd (hX ▸ h1) hnl
  · -- rightCanon
    intro hr _ _
    have hnleft : uniLeftChoice X.leftOnly = none := by
      rcases hl : uniLeftChoice X.leftOnly with _ | lrl
      · rfl
      · exfalso
        unfold uniChoiceRL at h
        rw [hl] at h
        simp only [Option.some.injEq] at h
        subst h
        exact LocalRuleApp.not_left_and_right _ ⟨by simpa using (uniLeftChoice_spec hl).2, hr⟩
    rcases hrr : uniRightChoice X.rightOnly with _ | lrr
    · exfalso
      have : (uniRightChoice X.rightOnly).isSome := uniRightChoice_rightOnly_isSome hX hr
      rw [hrr] at this
      exact Bool.false_ne_true this
    · refine ⟨lrr, by rw [hX, hrr], ?_⟩
      unfold uniChoiceRL at h
      rw [hnleft, hrr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact LocalRuleApp.toContext_sameRuleAs lrr X
  · -- leftCanon
    intro _ h2
    exact absurd (hX ▸ h2) hnl

open Classical in
/-- The canonical local rule application at a sequent: when the sequent is loaded on the
left we flip, use `uniChoiceRL` and flip back. -/
def uniChoiceAt (X : Sequent) : Option LocalRuleApp :=
  if X.2.2.isLeft then (uniChoiceRL X.flip).map LocalRuleApp.flip else uniChoiceRL X

lemma uniChoiceAt_X {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra) :
    lra.X = X := by
  unfold uniChoiceAt at h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨lrb, hb, rfl⟩ := h
    rw [LocalRuleApp.flip_X, uniChoiceRL_X hb, Sequent.flip_flip]
  · exact uniChoiceRL_X h

lemma uniChoiceAt_isSome {X : Sequent} (h : ¬ X.basic) : (uniChoiceAt X).isSome := by
  unfold uniChoiceAt
  split
  · simpa using uniChoiceRL_isSome (X := X.flip) (by rwa [basic_flip])
  · exact uniChoiceRL_isSome h

lemma uniChoiceAt_isUniChoice {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra) :
    lra.IsUniChoice := by
  unfold uniChoiceAt at h
  split at h
  · rename_i hleft
    rw [Option.map_eq_some_iff] at h
    obtain ⟨lrb, hb, rfl⟩ := h
    refine LocalRuleApp.IsUniChoice.flip (uniChoiceRL_isUniChoice ?_ hb)
    clear hb
    rcases X with ⟨L, R, O⟩
    rcases O with _ | (a | b) <;> simp_all [Sequent.flip, Olf.flip, Olf.isLeft]
  · rename_i hleft
    exact uniChoiceRL_isUniChoice hleft h

lemma uniChoiceAt_C_lt {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra)
    {Y : Sequent} (hY : Y ∈ lra.C) : ltSequent Y X := by
  have hdec := localRuleApp.decreases_DM lra Y hY
  rwa [uniChoiceAt_X h] at hdec

open Classical in
/-- The canonical local tableau: always apply the canonical rule `uniChoiceAt`. -/
def uniLocalTab : (X : Sequent) → LocalTableau X
  | X =>
    if bas : X.basic then .sim bas
    else
      have hX : ((uniChoiceAt X).get (uniChoiceAt_isSome bas)).X = X :=
        uniChoiceAt_X (Option.some_get (uniChoiceAt_isSome bas)).symm
      .byLocalRule ((uniChoiceAt X).get (uniChoiceAt_isSome bas)) hX.symm
        (fun Y _ => uniLocalTab Y)
termination_by X => X
decreasing_by
  exact uniChoiceAt_C_lt (Option.some_get _).symm (by assumption)

lemma uniLocalTab_isUni (X : Sequent) : (uniLocalTab X).IsUni := by
  rw [uniLocalTab]
  split
  · rw [LocalTableau.IsUni]; trivial
  · rename_i bas
    rw [LocalTableau.IsUni]
    refine ⟨uniChoiceAt_isUniChoice (Option.some_get (uniChoiceAt_isSome bas)).symm, ?_⟩
    intro Y hY
    exact uniLocalTab_isUni Y
termination_by X
decreasing_by
  exact uniChoiceAt_C_lt (Option.some_get _).symm (by assumption)


end PDL
