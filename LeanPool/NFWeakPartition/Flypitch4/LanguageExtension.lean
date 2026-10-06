/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/language_extension.lean -/

public import LeanPool.NFWeakPartition.Flypitch4.Compactness

/-! NF weak partition development: Flypitch4.LanguageExtension.
-/


public section

namespace NFChoice

open NFChoice.Set Function

namespace Fol

universe u

/-! ## Language.Lconstants, Language.sum, Language.symbols -/


namespace Language

/-- Flypitch construction `Lconstants`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def Lconstants (α : Type u) : Language.{u} :=
  ⟨fun n => Nat.rec α (fun _n _ih => PEmpty) n, fun _n => PEmpty⟩

/-- Flypitch construction `sum`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def sum (L L' : Language.{u}) : Language.{u} :=
  ⟨fun n => L.functions n ⊕ L'.functions n, fun n => L.relations n ⊕ L'.relations n⟩

/-- Flypitch construction `symbols`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def symbols (L : Language.{u}) :=
  (Σ l, L.functions l) ⊕ (Σ l, L.relations l)

end Language

variable {L : Language.{u}}

/-! ## symbols_in_term, symbols_in_formula -/


/-- Flypitch construction `symbols_in_term`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def symbolsInTerm : ∀ {l}, preterm L l → Set (Language.symbols L)
  | _, &_ => ∅
  | l, preterm.func f => {Sum.inl ⟨l, f⟩}
  | _, preterm.app t₁ t₂ => symbolsInTerm t₁ ∪ symbolsInTerm t₂

/-- Flypitch construction `symbols_in_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def symbolsInFormula : ∀ {l}, @preformula L l → Set (Language.symbols L)
  | _, preformula.falsum => ∅
  | _, preformula.equal t₁ t₂ => symbolsInTerm t₁ ∪ symbolsInTerm t₂
  | l, preformula.rel R => {Sum.inr ⟨l, R⟩}
  | _, preformula.apprel f t => symbolsInFormula f ∪ symbolsInTerm t
  | _, preformula.imp f₁ f₂ => symbolsInFormula f₁ ∪ symbolsInFormula f₂
  | _, preformula.all f => symbolsInFormula f

@[simp]
lemma symbols_in_term_lift_at (n m : ℕ) :
    ∀ {l} (t : preterm L l), symbolsInTerm (t ↑' n # m) = symbolsInTerm t
  | _, &k => by by_cases h : m ≤ k <;> simp [h]
  | _, preterm.func _ => rfl
  | _, preterm.app t₁ t₂ => by
    simp [symbols_in_term_lift_at n m t₁, symbols_in_term_lift_at n m t₂]

lemma symbols_in_term_lift (n : ℕ) {l} (t : preterm L l) :
    symbolsInTerm (t ↑n) = symbolsInTerm t :=
  symbols_in_term_lift_at n 0 t

lemma symbols_in_term_subst (s : term L) (n : ℕ) :
    ∀ {l} (t : preterm L l),
      symbolsInTerm (substTerm t s n) ⊆ symbolsInTerm t ∪ symbolsInTerm s
  | _, &k => by
    rcases Nat.lt_trichotomy k n with h | h | h
    · simp [subst_term_var_lt s h]
    · subst h; simp [subst_term_var_eq, symbols_in_term_lift_at]
    · simp [subst_term_var_gt s h]
  | _, preterm.func _ => Set.subset_union_left
  | _, preterm.app t₁ t₂ =>
    by
    simp only [subst_term_app, symbolsInTerm]
    intro x hx
    rcases hx with h | h
    · rcases symbols_in_term_subst s n t₁ h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases symbols_in_term_subst s n t₂ h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

lemma symbols_in_formula_subst :
    ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
      symbolsInFormula (substFormula f s n) ⊆ symbolsInFormula f ∪ symbolsInTerm s
  | _, preformula.falsum, _, _ => Set.empty_subset _
  | _, preformula.equal t₁ t₂, s, n =>
    by
    simp only [substFormula, symbolsInFormula]
    intro x hx
    rcases hx with h | h
    · rcases symbols_in_term_subst s n t₁ h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases symbols_in_term_subst s n t₂ h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | _, preformula.rel _, _, _ => Set.subset_union_left
  | _, preformula.apprel f t, s, n =>
    by
    simp only [substFormula, symbolsInFormula]
    intro x hx
    rcases hx with h | h
    · rcases symbols_in_formula_subst f s n h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases symbols_in_term_subst s n t h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | _, preformula.imp f₁ f₂, s, n =>
    by
    simp only [substFormula, symbolsInFormula]
    intro x hx
    rcases hx with h | h
    · rcases symbols_in_formula_subst f₁ s n h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases symbols_in_formula_subst f₂ s n h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | _, preformula.all f, s, n =>
    by
    simp only [substFormula, symbolsInFormula]
    exact symbols_in_formula_subst f s (n + 1)

/-! ## Lhom — language homomorphism -/


/-- Flypitch construction `Lhom`, retained by the first-order soundness and completeness
development.
-/
structure Lhom (L L' : Language.{u}) where
  /-- The `on_function` component of the corresponding first-order structure. -/
  onFunction : ∀ {n}, L.functions n → L'.functions n
  /-- The `on_relation` component of the corresponding first-order structure. -/
  onRelation : ∀ {n}, L.relations n → L'.relations n

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
infix:10 " →ᴸ " => Lhom  -- \^L

namespace Lhom

variable {L' : Language.{u}} (ϕ : L →ᴸ L')

/-- Flypitch construction `id`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def id (L : Language.{u}) : L →ᴸ L :=
  ⟨fun {_} => id, fun {_} => id⟩

/-- Flypitch construction `sum_inl`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def sumInl {L L' : Language.{u}} : L →ᴸ L.sum L' :=
  ⟨fun {_} => Sum.inl, fun {_} => Sum.inl⟩

/-- Flypitch construction `sum_inr`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def sumInr {L L' : Language.{u}} : L' →ᴸ L.sum L' :=
  ⟨fun {_} => Sum.inr, fun {_} => Sum.inr⟩

/-- Flypitch construction `comp`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def comp {L1 L2 L3 : Language.{u}} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
  ⟨fun {n} => g.onFunction ∘ f.onFunction (n := n), fun {n} =>
    g.onRelation ∘ f.onRelation (n := n)⟩

local infixr:60 " ∘ᴸ " => Lhom.comp

lemma Lhom_funext {L1 L2 : Language.{u}} {F G : L1 →ᴸ L2}
    (h_fun : @Lhom.onFunction _ _ F = @Lhom.onFunction _ _ G)
    (h_rel : @Lhom.onRelation _ _ F = @Lhom.onRelation _ _ G) : F = G := by
  cases F;
  cases G; simp only at h_fun h_rel; subst h_fun; subst h_rel; rfl

@[simp]
lemma id_is_left_identity {L1 L2 : Language.{u}} {F : L1 →ᴸ L2} : (Lhom.id L2) ∘ᴸ F = F :=
  by cases F; rfl

@[simp]
lemma id_is_right_identity {L1 L2 : Language.{u}} {F : L1 →ᴸ L2} :
    F ∘ᴸ (Lhom.id L1) = F := by cases F; rfl

/-- Flypitch construction `is_injective`, retained by the first-order soundness and completeness
development.
-/
structure IsInjective : Prop where
  onFunction {n} : Function.Injective (ϕ.onFunction (n := n))
  onRelation {n} : Function.Injective (ϕ.onRelation (n := n))

/-- Flypitch construction `has_decidable_range`, retained by the first-order soundness and
completeness development.
-/
class HasDecidableRange : Type u where
  /-- The `on_function` component of the corresponding first-order structure. -/
  onFunction {n} : DecidablePred (· ∈ Set.range (ϕ.onFunction (n := n)))
  /-- The `on_relation` component of the corresponding first-order structure. -/
  onRelation {n} : DecidablePred (· ∈ Set.range (ϕ.onRelation (n := n)))

instance (priority := 100) instDecFn [h : HasDecidableRange ϕ] {n} :
    DecidablePred (· ∈ Set.range (ϕ.onFunction (n := n))) :=
  h.onFunction

instance (priority := 100) instDecRel [h : HasDecidableRange ϕ] {n} :
    DecidablePred (· ∈ Set.range (ϕ.onRelation (n := n))) :=
  h.onRelation

/-- Flypitch construction `on_symbol`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def onSymbol : Language.symbols L → Language.symbols L'
  | Sum.inl ⟨l, f⟩ => Sum.inl ⟨l, ϕ.onFunction f⟩
  | Sum.inr ⟨l, R⟩ => Sum.inr ⟨l, ϕ.onRelation R⟩

/-- Flypitch construction `on_term`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def onTerm : ∀ {l}, preterm L l → preterm L' l
  | _, &k => &k
  | _, preterm.func f => preterm.func (ϕ.onFunction f)
  | _, preterm.app t₁ t₂ => preterm.app (onTerm t₁) (onTerm t₂)

@[simp]
lemma on_term_lift_at :
    ∀ {l} (t : preterm L l) (n m : ℕ), ϕ.onTerm (t ↑' n # m) = ϕ.onTerm t ↑' n # m
  | _, &k, n, m => by simp [liftTermAt]
  | _, preterm.func _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, m => by simp only [onTerm, liftTermAt, on_term_lift_at]

lemma on_term_lift {l} (n : ℕ) (t : preterm L l) :
    ϕ.onTerm (liftTerm t n) = liftTerm (ϕ.onTerm t) n := by
  simp only [liftTerm, on_term_lift_at]

@[simp]
lemma on_term_subst :
    ∀ {l} (t : preterm L l) (s : term L) (n : ℕ),
      ϕ.onTerm (substTerm t s n) = substTerm (ϕ.onTerm t) (ϕ.onTerm s) n
  | _, &k, s, n => by
    rcases Nat.lt_trichotomy k n with h | h | h
    · simp [subst_term_var_lt _ h]
    · subst h
      simp [subst_term_var_eq, on_term_lift_at]
    · simp [subst_term_var_gt _ h]
  | _, preterm.func _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n => by simp [on_term_subst t₁ s n, on_term_subst t₂ s n]

@[simp]
lemma on_term_apps :
    ∀ {l} (t : preterm L l) (ts : DVec (term L) l),
      ϕ.onTerm (apps t ts) = apps (ϕ.onTerm t) (ts.map ϕ.onTerm)
  | _, _, DVec.nil => rfl
  | _, t, DVec.cons t' ts => by
    simp only [apps, DVec.map]
    exact on_term_apps (preterm.app t t') ts

lemma not_mem_symbols_in_term_on_term {s : Language.symbols L'}
    (hs : s ∉ Set.range (ϕ.onSymbol)) :
    ∀ {l} (t : preterm L l), s ∉ symbolsInTerm (ϕ.onTerm t) :=
  by
  intro l t
  induction t with
  | var k => simp [onTerm, symbolsInTerm]
  | func f => exact fun h' => hs ⟨Sum.inl ⟨_, f⟩, (Set.mem_singleton_iff.mp h').symm⟩
  | app t₁ t₂ ih₁
    ih₂ =>
    simp only [onTerm, symbolsInTerm, Set.mem_union, not_or]
    exact ⟨ih₁, ih₂⟩

/-- Flypitch construction `on_formula`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def onFormula : ∀ {l}, @preformula L l → @preformula L' l
  | _, preformula.falsum => preformula.falsum
  | _, preformula.equal t₁ t₂ => preformula.equal (ϕ.onTerm t₁) (ϕ.onTerm t₂)
  | _, preformula.rel R => preformula.rel (ϕ.onRelation R)
  | _, preformula.apprel f t => preformula.apprel (onFormula f) (ϕ.onTerm t)
  | _, preformula.imp f₁ f₂ => preformula.imp (onFormula f₁) (onFormula f₂)
  | _, preformula.all f => preformula.all (onFormula f)

@[simp]
lemma on_formula_lift_at :
    ∀ {l} (n m : ℕ) (f : @preformula L l),
      ϕ.onFormula (f ↑f' n # m) = ϕ.onFormula f ↑f' n # m
  | _, _, _, preformula.falsum => rfl
  | _, _, _, preformula.equal t₁ t₂ => by simp [on_term_lift_at]
  | _, _, _, preformula.rel _ => rfl
  | _, _, _, preformula.apprel f t => by simp [on_formula_lift_at, on_term_lift_at]
  | _, _, _, preformula.imp f₁ f₂ => by simp [on_formula_lift_at]
  | _, _, _, preformula.all f => by simp [on_formula_lift_at]

lemma on_formula_lift {l} (n : ℕ) (f : @preformula L l) :
    ϕ.onFormula (liftFormula f n) = liftFormula (ϕ.onFormula f) n := by
  simp only [liftFormula, on_formula_lift_at]

@[simp]
lemma on_formula_subst :
    ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
      ϕ.onFormula (f [s // n]f) = (ϕ.onFormula f) [ϕ.onTerm s // n]f
  | _, preformula.falsum, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n => by simp [on_term_subst]
  | _, preformula.rel _, _, _ => rfl
  | _, preformula.apprel f t, s, n => by simp [on_formula_subst f s n, on_term_subst]
  | _, preformula.imp f₁ f₂, s, n => by
    simp [on_formula_subst f₁ s n, on_formula_subst f₂ s n]
  | _, preformula.all f, s, n => by simp [on_formula_subst f s (n + 1)]

@[simp]
lemma on_formula_apps_rel :
    ∀ {l} (f : @preformula L l) (ts : DVec (term L) l),
      ϕ.onFormula (appsRel f ts) = appsRel (ϕ.onFormula f) (ts.map ϕ.onTerm)
  | _, _, DVec.nil => rfl
  | _, f, DVec.cons t' ts => by
    simp only [appsRel, DVec.map]
    exact on_formula_apps_rel (preformula.apprel f t') ts

lemma not_mem_symbols_in_formula_on_formula {s : Language.symbols L'}
    (hs : s ∉ Set.range (ϕ.onSymbol)) :
    ∀ {l} (f : @preformula L l), s ∉ symbolsInFormula (ϕ.onFormula f) :=
  by
  intro l f
  induction f with
  | falsum => simp [onFormula, symbolsInFormula]
  | equal t₁
    t₂ =>
    simp only [onFormula, symbolsInFormula, Set.mem_union, not_or]
    exact
      ⟨ϕ.not_mem_symbols_in_term_on_term hs t₁, ϕ.not_mem_symbols_in_term_on_term hs t₂⟩
  | rel R => exact fun h' => hs ⟨Sum.inr ⟨_, R⟩, (Set.mem_singleton_iff.mp h').symm⟩
  | apprel f t
    ihf =>
    simp only [onFormula, symbolsInFormula, Set.mem_union, not_or]
    exact ⟨ihf, ϕ.not_mem_symbols_in_term_on_term hs t⟩
  | imp f₁ f₂ ihf₁
    ihf₂ =>
    simp only [onFormula, symbolsInFormula, Set.mem_union, not_or]
    exact ⟨ihf₁, ihf₂⟩
  | all f ihf => exact ihf

lemma not_mem_function_in_formula_on_formula {l'} {f' : L'.functions l'}
    (h : f' ∉ Set.range (ϕ.onFunction (n := l'))) {l} (f : @preformula L l) :
    (Sum.inl ⟨l', f'⟩ : Language.symbols L') ∉ symbolsInFormula (ϕ.onFormula f) :=
  by
  apply not_mem_symbols_in_formula_on_formula
  intro ⟨s, hs⟩
  apply h
  match s with
  | Sum.inl ⟨m, g⟩ =>
    simp only [onSymbol] at hs
    have heq : (⟨m, ϕ.onFunction g⟩ : Σ l, L'.functions l) = ⟨l', f'⟩ := Sum.inl.inj hs
    have hm : m = l' := congrArg Sigma.fst heq
    subst hm
    exact ⟨g, eq_of_heq (Sigma.mk.inj heq).2⟩
  | Sum.inr p =>
    simp only [onSymbol] at hs
    exact absurd hs (by simp)

/-! ## on_bounded_term, on_bounded_formula -/


/-- Flypitch construction `on_bounded_term`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def onBoundedTerm {n} : ∀ {l} (_t : BoundedPreterm L n l), BoundedPreterm L' n l
  | _, BoundedPreterm.bd_var k => BoundedPreterm.bd_var k
  | _, BoundedPreterm.bd_func f => BoundedPreterm.bd_func (ϕ.onFunction f)
  | _, BoundedPreterm.bd_app t s =>
    BoundedPreterm.bd_app (onBoundedTerm t) (onBoundedTerm s)

@[simp]
lemma on_bounded_term_fst {n} :
    ∀ {l} (t : BoundedPreterm L n l), (ϕ.onBoundedTerm t).fst = ϕ.onTerm t.fst
  | _, BoundedPreterm.bd_var _ => rfl
  | _, BoundedPreterm.bd_func _ => rfl
  | _, BoundedPreterm.bd_app t s => by
    simp [on_bounded_term_fst t, on_bounded_term_fst s]

/-- Flypitch construction `on_bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def onBoundedFormula :
    ∀ {n l} (_f : BoundedPreformula L n l), BoundedPreformula L' n l
  | _, _, bd_falsum => bd_falsum
  | _, _, bd_equal t₁ t₂ => bd_equal (ϕ.onBoundedTerm t₁) (ϕ.onBoundedTerm t₂)
  | _, _, bd_rel R => bd_rel (ϕ.onRelation R)
  | _, _, bd_apprel f t => bd_apprel (onBoundedFormula f) (ϕ.onBoundedTerm t)
  | _, _, bd_imp f₁ f₂ => bd_imp (onBoundedFormula f₁) (onBoundedFormula f₂)
  | _, _, bd_all f => bd_all (onBoundedFormula f)

@[simp]
lemma on_bounded_formula_fst :
    ∀ {n l} (f : BoundedPreformula L n l),
      (ϕ.onBoundedFormula f).fst = ϕ.onFormula f.fst
  | _, _, bd_falsum => rfl
  | _, _, bd_equal t₁ t₂ => by simp [on_bounded_term_fst]
  | _, _, bd_rel _ => rfl
  | _, _, bd_apprel f t => by simp [on_bounded_formula_fst f, on_bounded_term_fst]
  | _, _, bd_imp f₁ f₂ => by simp [on_bounded_formula_fst f₁, on_bounded_formula_fst f₂]
  | _, _, bd_all f => by simp [on_bounded_formula_fst f]

/-! ## Functoriality lemmas -/


@[simp]
lemma comp_on_term {L1 L2 L3 : Language.{u}} {l : ℕ} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
    @onTerm L1 L3 (g.comp f) l =
      Function.comp (@onTerm L2 L3 g l) (@onTerm L1 L2 f l) :=
  by
  funext x
  induction x with
  | var k => rfl
  | func ff => rfl
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [onTerm, Function.comp]
    exact congrArg₂ preterm.app ih₁ ih₂

@[simp]
lemma comp_on_formula {L1 L2 L3 : Language.{u}} {l : ℕ} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
    @onFormula L1 L3 (g.comp f) l =
      Function.comp (@onFormula L2 L3 g l) (@onFormula L1 L2 f l) :=
  by
  funext x
  induction x with
  | falsum => rfl
  | equal t₁ t₂ => simp [onFormula, comp_on_term]
  | rel R => rfl
  | apprel f t ihf =>
    simp only [onFormula, Function.comp]
    exact congrArg₂ preformula.apprel ihf (by simp [comp_on_term])
  | imp f₁ f₂ ihf₁ ihf₂ =>
    simp only [onFormula, Function.comp]
    exact congrArg₂ preformula.imp ihf₁ ihf₂
  | all f ihf =>
    simp only [onFormula, Function.comp]
    exact congrArg preformula.all ihf

@[simp]
lemma comp_on_bounded_term {L1 L2 L3 : Language.{u}} {n l : ℕ} (g : L2 →ᴸ L3)
    (f : L1 →ᴸ L2) :
    @onBoundedTerm L1 L3 (g.comp f) n l =
      Function.comp (@onBoundedTerm L2 L3 g n l) (@onBoundedTerm L1 L2 f n l) :=
  by
  funext x
  induction x with
  | bd_var k => rfl
  | bd_func ff => rfl
  | bd_app t s iht ihs =>
    simp only [onBoundedTerm, Function.comp]
    exact congrArg₂ BoundedPreterm.bd_app iht ihs

@[simp]
lemma comp_on_bounded_formula {L1 L2 L3 : Language.{u}} {n l : ℕ} (g : L2 →ᴸ L3)
    (f : L1 →ᴸ L2) :
    @onBoundedFormula L1 L3 (g.comp f) n l =
      Function.comp (@onBoundedFormula L2 L3 g n l) (@onBoundedFormula L1 L2 f n l) :=
  by
  funext x
  apply BoundedPreformula.eq
  simp [on_bounded_formula_fst, comp_on_formula]

lemma id_term : ∀ {l} (t : preterm L l), @onTerm L L (Lhom.id L) l t = t
  | _, &_ => rfl
  | _, preterm.func _ => rfl
  | _, preterm.app t₁ t₂ => by simp [onTerm, id_term t₁, id_term t₂]

lemma id_formula : ∀ {l} (f : @preformula L l), @onFormula L L (Lhom.id L) l f = f
  | _, preformula.falsum => rfl
  | _, preformula.equal t₁ t₂ => by simp [onFormula, id_term]
  | _, preformula.rel _ => rfl
  | _, preformula.apprel f t => by simp [onFormula, id_formula f, id_term]
  | _, preformula.imp f₁ f₂ => by simp [onFormula, id_formula f₁, id_formula f₂]
  | _, preformula.all f => by simp [onFormula, id_formula f]

lemma id_bounded_term {n} :
    ∀ {l} (t : BoundedPreterm L n l), @onBoundedTerm L L (Lhom.id L) n l t = t
  | _, BoundedPreterm.bd_var _ => rfl
  | _, BoundedPreterm.bd_func _ => rfl
  | _, BoundedPreterm.bd_app t s => by
    simp [onBoundedTerm, id_bounded_term t, id_bounded_term s]

lemma id_bounded_formula :
    ∀ {n l} (f : BoundedPreformula L n l), @onBoundedFormula L L (Lhom.id L) n l f = f
  | _, _, bd_falsum => rfl
  | _, _, bd_equal t₁ t₂ => by simp [onBoundedFormula, id_bounded_term]
  | _, _, bd_rel _ => rfl
  | _, _, bd_apprel f t => by
    simp [onBoundedFormula, id_bounded_formula f, id_bounded_term]
  | _, _, bd_imp f₁ f₂ => by
    simp [onBoundedFormula, id_bounded_formula f₁, id_bounded_formula f₂]
  | _, _, bd_all f => by simp [onBoundedFormula, id_bounded_formula f]

/-- Flypitch construction `on_closed_term`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def onClosedTerm (t : closedTerm L) : closedTerm L' :=
  ϕ.onBoundedTerm t
/-- Flypitch construction `on_sentence`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def onSentence (f : sentence L) : sentence L' :=
  ϕ.onBoundedFormula f

theorem on_sentence_fst (f : sentence L) : (ϕ.onSentence f).fst = ϕ.onFormula f.fst :=
  ϕ.on_bounded_formula_fst f

/-! ## on_prf — Lhom lifts proofs -/


/-- Flypitch construction `on_prf`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def onPrf {Γ : Set (formula L)} {f : formula L} (h : Γ ⊢ f) :
    ϕ.onFormula '' Γ ⊢ ϕ.onFormula f := by
  induction h with
  | axm hΓ => exact prf.axm (Set.mem_image_of_mem _ hΓ)
  | impI _ ih =>
    apply prf.impI
    rw [← Set.image_insert_eq]
    exact ih
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ ih₁ ih₂
  | falsumE _ ih =>
    apply prf.falsumE
    rw [Set.image_insert_eq] at ih
    exact ih
  | allI _ ih =>
    simp only [onFormula]
    apply prf.allI
    rw [Set.image_image] at ih ⊢
    have key :
      ∀ g : formula L, ϕ.onFormula (liftFormula1 g) = liftFormula1 (ϕ.onFormula g) :=
      fun g => by simp only [liftFormula1, on_formula_lift_at]
    simp_rw [key] at ih
    exact ih
  | allE₂ A t _
    ih =>
    have heq : ϕ.onFormula (A [t // 0]f) = (ϕ.onFormula A) [ϕ.onTerm t // 0]f := by
      simp [on_formula_subst]
    rw [heq]
    exact prf.allE₂ _ _ ih
  | ref _ _ => exact prf.ref _ _
  | subst₂ s t f₁ _ _ ih₁
    ih₂ =>
    have heq1 : ϕ.onFormula (f₁ [s // 0]f) = (ϕ.onFormula f₁) [ϕ.onTerm s // 0]f := by
      simp [on_formula_subst]
    have heq2 : ϕ.onFormula (f₁ [t // 0]f) = (ϕ.onFormula f₁) [ϕ.onTerm t // 0]f := by
      simp [on_formula_subst]
    rw [heq2]
    rw [heq1] at ih₂
    exact prf.subst₂ _ _ _ ih₁ ih₂

/-- Flypitch construction `on_sprf`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def onSprf {Γ : SentTheory L} {f : sentence L} (h : Γ ⊢ₛ f) :
    (ϕ.onSentence '' Γ) ⊢ₛ ϕ.onSentence f :=
  by
  have := ϕ.onPrf h
  simp only [SentTheory.sprf, SentTheory.fst, Set.image_image, on_bounded_formula_fst,
    onSentence] at this ⊢
  exact this

/-! ## reflect_term -/


/-- Flypitch construction `reflect_term`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def reflectTerm [HasDecidableRange ϕ] (t : term L') (m : ℕ) : term L :=
  term.elim (fun k => liftTermAt (&k) 1 m)
    (fun {l} f' _ts' ts => if hf' : f' ∈ Set.range (ϕ.onFunction (n := l)) then
        apps (preterm.func (Classical.choose hf')) ts else &m)
    t

variable {ϕ}

lemma reflect_term_apps_pos [HasDecidableRange ϕ] {l} {f : L'.functions l}
    (hf : f ∈ Set.range (ϕ.onFunction (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflectTerm (apps (preterm.func f) ts) m =
      apps (preterm.func (Classical.choose hf)) (ts.map (fun t => ϕ.reflectTerm t m)) :=
  (term.elim_apps _ _ f ts).trans (by rw [dite_eq_left hf]; rfl)

lemma reflect_term_apps_neg [HasDecidableRange ϕ] {l} {f : L'.functions l}
    (hf : f ∉ Set.range (ϕ.onFunction (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflectTerm (apps (preterm.func f) ts) m = &m :=
  (term.elim_apps _ _ f ts).trans (by rw [dite_eq_right hf])

lemma reflect_term_const_pos [HasDecidableRange ϕ] {c : L'.constants}
    (hf : c ∈ Set.range (ϕ.onFunction (n := 0))) (m : ℕ) :
    ϕ.reflectTerm (preterm.func c) m = preterm.func (Classical.choose hf) :=
  reflect_term_apps_pos hf DVec.nil m

lemma reflect_term_const_neg [HasDecidableRange ϕ] {c : L'.constants}
    (hf : c ∉ Set.range (ϕ.onFunction (n := 0))) (m : ℕ) :
    ϕ.reflectTerm (preterm.func c) m = &m :=
  reflect_term_apps_neg hf DVec.nil m

@[simp]
lemma reflect_term_var [HasDecidableRange ϕ] (k m : ℕ) :
    ϕ.reflectTerm (&k) m = &k ↑' 1 # m :=
  rfl

@[simp]
lemma reflect_term_on_term [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (t : term L)
    (m : ℕ) : ϕ.reflectTerm (ϕ.onTerm t) m = t ↑' 1 # m :=
  by
  refine
    @term.rec L (fun t => ϕ.reflectTerm (ϕ.onTerm t) m = t ↑' 1 # m) (fun k => ?_)
      (fun f ts ih_ts => ?_) t
  · -- var k: reflect_term (&k) m = &k ↑' 1 # m
    simp [reflect_term_var, liftTermAt]
      -- func f applied to ts: reflect_term (on_term (apps (func f)
        -- ts)) m = (apps (func f) ts) ↑' 1 # m
  · have hf : ϕ.onFunction f ∈ Set.range (ϕ.onFunction) := Set.mem_range_self f
    simp only [on_term_apps, onTerm, reflect_term_apps_pos hf, lift_term_at_apps]
    congr 1
    -- preterm.func (Classical.choose hf) = preterm.func f (modulo lift which is identity on func)
    · simp only [liftTermAt]
      exact congrArg preterm.func (hϕ.onFunction (Classical.choose_spec hf))
    -- DVec.map (fun t => reflect_term t m) (DVec.map on_term ts) = DVec.map (· ↑' 1 # m) ts
    · rw [DVec.map_map]
      apply DVec.map_congr_pmem
      intro t hmem
      exact ih_ts t hmem

lemma reflect_term_lift_at [HasDecidableRange ϕ] (_hϕ : IsInjective ϕ) {n m m' : ℕ}
    (h : m ≤ m') (t : term L') :
    ϕ.reflectTerm (t ↑' n # m) (m' + n) = ϕ.reflectTerm t m' ↑' n # m :=
  by
  refine
    @term.rec L'
      (fun t => ϕ.reflectTerm (t ↑' n # m) (m' + n) = ϕ.reflectTerm t m' ↑' n # m)
      (fun k => ?_) (fun f ts ih_ts => ?_) t
  · -- var k: ((&k) ↑' n # m) reflected at (m'+n) = reflected (&k) at m' lifted n at m
    simp only [reflect_term_var, liftTermAt]
    split_ifs <;> simp_all [] <;> omega
  · -- func f applied to ts: by_cases on f ∈ range
    by_cases hf : f ∈ Set.range ϕ.onFunction
    · simp only [lift_term_at_apps, reflect_term_apps_pos hf, liftTermAt, DVec.map_map,
        ]
      congr 1
      apply DVec.map_congr_pmem
      intro t hmem; exact ih_ts t hmem
    · show
        ϕ.reflectTerm ((apps (preterm.func f) ts) ↑' n # m) (m' + n) =
          ϕ.reflectTerm (apps (preterm.func f) ts) m' ↑' n # m
      simp only [lift_term_at_apps, liftTermAt, reflect_term_apps_neg hf, h, ite_true]

lemma reflect_term_lift [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) {n m : ℕ}
    (t : term L') :
    ϕ.reflectTerm (liftTerm t n) (m + n) = liftTerm (ϕ.reflectTerm t m) n :=
  reflect_term_lift_at hϕ (Nat.zero_le m) t

lemma reflect_term_subst [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (n m : ℕ)
    (s t : term L') :
    ϕ.reflectTerm (substTerm t s n) (m + n) =
      substTerm (ϕ.reflectTerm t (m + n + 1)) (ϕ.reflectTerm s m) n :=
  by
  induction t using @term.rec L' with
  | hvar
    k =>
    show
      ϕ.reflectTerm (substTerm (&k) s n) (m + n) =
        substTerm (ϕ.reflectTerm (&k) (m + n + 1)) (ϕ.reflectTerm s m) n
    rcases Nat.lt_trichotomy k n with hk | hk | hk
    · -- k < n
      simp only [subst_term_var_lt s hk, reflect_term_var, liftTermAt,
        ite_eq_right (by omega : ¬(m + n ≤ k)),
        ite_eq_right (by omega : ¬(m + n + 1 ≤ k)), subst_term_var_lt _ hk]
        -- k = n: reflect_term (s ↑' n # 0) (m+n) = subst_term (&n ↑' 1 #
            -- (m+n+1)) (reflect_term s m) n
    · simp only [hk, subst_term_var_eq, reflect_term_var, liftTermAt,
        ite_eq_right (by omega : ¬(m + n + 1 ≤ n)), subst_term_var_eq]
      exact reflect_term_lift hϕ s
    · -- k > n
      have hk1 : 1 ≤ k := Nat.one_le_of_lt hk
      by_cases h₂' : m + n + 1 ≤ k
      · -- k ≥ m+n+1: both sides = &k
        simp only [subst_term_var_gt s hk, reflect_term_var, liftTermAt, h₂', ite_true,
          ite_eq_left (by omega : m + n ≤ k - 1), Nat.sub_add_cancel hk1,
          subst_term_var_gt _ (by omega : n < k + 1), show k + 1 - 1 = k from by omega]
      · -- n < k < m+n+1: both sides = &(k-1)
        simp only [subst_term_var_gt s hk, reflect_term_var, liftTermAt,
          ite_eq_right (by omega : ¬(m + n ≤ k - 1)), ite_eq_right h₂',
          subst_term_var_gt _ hk]
  | hfunc f ts
    ih_ts =>
    show
      ϕ.reflectTerm (substTerm (apps (preterm.func f) ts) s n) (m + n) =
        substTerm (ϕ.reflectTerm (apps (preterm.func f) ts) (m + n + 1))
          (ϕ.reflectTerm s m) n
    have hn : n < m + n + 1 := by omega
    by_cases hf : f ∈ Set.range ϕ.onFunction
    · simp only [subst_term_apps, reflect_term_apps_pos hf, subst_term_func,
        subst_term_apps, DVec.map_map]
      exact
        congrArg (apps (preterm.func _))
          (DVec.map_congr_pmem (fun t hmem => ih_ts t hmem))
    · simp only [subst_term_apps, subst_term_func, reflect_term_apps_neg hf,
        subst_term_var_gt _ hn, show m + n + 1 - 1 = m + n from by omega]

variable (ϕ)

/-! ## reflect_formula -/
-- reflect_formula auxiliary: builds ℕ → formula L from formula
-- L'
-- using C = fun _ => ℕ → formula L in formula.rec


-- reflect_formula auxiliary: builds ℕ → formula L from formula
-- L'
-- using C = fun _ => ℕ → formula L in formula.rec
/-- Flypitch construction `reflect_formula_aux'`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def reflectFormulaAux' [HasDecidableRange ϕ] (f : formula L') :
    ℕ → formula L :=
  (formula.rec (C := fun _ => ℕ → formula L) (fun _ => ⊥')
      (fun t₁ t₂ m' => ϕ.reflectTerm t₁ m' ≃ ϕ.reflectTerm t₂ m') (fun {l} R ts m' =>
        if hR : R ∈ Set.range (ϕ.onRelation (n := l)) then
          appsRel (preformula.rel (Classical.choose hR))
            (DVec.map (fun t => ϕ.reflectTerm t m') ts) else ⊥')
      (fun {_f₁} {_f₂} (ih₁ : ℕ → formula L) (ih₂ : ℕ → formula L) (m' : ℕ) =>
        (ih₁ m') ⟹ (ih₂ m')) (fun {_f} (ih : ℕ → formula L) (m' : ℕ) => ∀'(ih (m' + 1))) f :
    ℕ → formula L)

/-- Flypitch construction `reflect_formula`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def reflectFormula [HasDecidableRange ϕ] (m : ℕ) (f : formula L') :
    formula L :=
  @reflectFormulaAux' L L' ϕ _ f m

variable {ϕ}

lemma reflect_formula_apps_rel_pos [HasDecidableRange ϕ] {l} {R : L'.relations l}
    (hR : R ∈ Set.range (ϕ.onRelation (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflectFormula m (appsRel (preformula.rel R) ts) =
      appsRel (preformula.rel (Classical.choose hR))
        (ts.map (fun t => ϕ.reflectTerm t m)) :=
  by
  simp only [reflectFormula, reflectFormulaAux', formula.rec_apps_rel, dite_eq_left hR]

lemma reflect_formula_apps_rel_neg [HasDecidableRange ϕ] {l} {R : L'.relations l}
    (hR : R ∉ Set.range (ϕ.onRelation (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflectFormula m (appsRel (preformula.rel R) ts) = ⊥' := by
  simp only [reflectFormula, reflectFormulaAux', formula.rec_apps_rel,
    dite_eq_right hR]

@[simp]
lemma reflect_formula_equal [HasDecidableRange ϕ] (t₁ t₂ : term L') (m : ℕ) :
    ϕ.reflectFormula m (t₁ ≃ t₂) = ϕ.reflectTerm t₁ m ≃ ϕ.reflectTerm t₂ m :=
  by
  simp only [reflectFormula]
  rfl

@[simp]
lemma reflect_formula_imp [HasDecidableRange ϕ] (f₁ f₂ : formula L') (m : ℕ) :
    ϕ.reflectFormula m (f₁ ⟹ f₂) = ϕ.reflectFormula m f₁ ⟹ ϕ.reflectFormula m f₂ :=
  by
  simp only [reflectFormula]
  rfl

@[simp]
lemma reflect_formula_all [HasDecidableRange ϕ] (f : formula L') (m : ℕ) :
    ϕ.reflectFormula m (∀'f) = ∀'(ϕ.reflectFormula (m + 1) f) :=
  by
  simp only [reflectFormula]
  rfl

@[simp]
lemma reflect_formula_on_formula [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (m : ℕ)
    (f : formula L) : ϕ.reflectFormula m (ϕ.onFormula f) = f ↑f' 1 # m :=
  by
  refine
    @formula.rec L (fun f => ∀ m, ϕ.reflectFormula m (ϕ.onFormula f) = f ↑f' 1 # m) ?_
      ?_ ?_ ?_ ?_ f m
  · intro m; rfl
  · intro t₁ t₂ m
    simp only [onFormula, reflect_formula_equal, liftFormulaAt,
      reflect_term_on_term hϕ]
  · intro l R ts m
    have hR : ϕ.onRelation R ∈ Set.range ϕ.onRelation := Set.mem_range_self _
    simp only [on_formula_apps_rel, onFormula, reflect_formula_apps_rel_pos hR,
      lift_formula_at_apps_rel]
    congr 1
    · simp only [liftFormulaAt]
      exact congrArg preformula.rel (hϕ.onRelation (Classical.choose_spec hR))
    · rw [DVec.map_map]
      apply DVec.map_congr_pmem
      intro t _
      exact reflect_term_on_term hϕ t m
  · intro f₁ f₂ ih₁ ih₂ m
    simp only [onFormula, reflect_formula_imp, liftFormulaAt, ih₁ m, ih₂ m]
  · intro f ih m
    simp only [onFormula, reflect_formula_all, liftFormulaAt, ih (m + 1)]

lemma reflect_formula_lift_at [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) {n m m' : ℕ}
    (h : m ≤ m') (f : formula L') :
    ϕ.reflectFormula (m' + n) (f ↑f' n # m) = ϕ.reflectFormula m' f ↑f' n # m :=
  by
  refine
    @formula.rec L'
      (fun f => ∀ m m', m ≤ m' →
            ϕ.reflectFormula (m' + n) (f ↑f' n # m) = ϕ.reflectFormula m' f ↑f' n # m)
      ?_ ?_ ?_ ?_ ?_ f m m' h
  · intro m m' _; rfl
  · intro t₁ t₂ m m' h'
    simp only [liftFormulaAt, reflect_formula_equal, reflect_term_lift_at hϕ h']
  · intro l R ts m m' h'
    by_cases hR : R ∈ Set.range (ϕ.onRelation (n := l))
    · show
        ϕ.reflectFormula (m' + n) ((appsRel (preformula.rel R) ts) ↑f' n # m) =
          ϕ.reflectFormula m' (appsRel (preformula.rel R) ts) ↑f' n # m
      simp only [lift_formula_at_apps_rel, liftFormulaAt,
        reflect_formula_apps_rel_pos hR, lift_formula_at_apps_rel, DVec.map_map]
      congr 1
      apply DVec.map_congr_pmem
      intro t _; exact reflect_term_lift_at hϕ h' t
    · show
        ϕ.reflectFormula (m' + n) ((appsRel (preformula.rel R) ts) ↑f' n # m) =
          ϕ.reflectFormula m' (appsRel (preformula.rel R) ts) ↑f' n # m
      simp only [lift_formula_at_apps_rel, liftFormulaAt,
        reflect_formula_apps_rel_neg hR]
  · intro f₁ f₂ ih₁ ih₂ m m' h'
    simp only [liftFormulaAt, reflect_formula_imp, ih₁ m m' h', ih₂ m m' h']
  · intro f ih m m' h'
    simp only [liftFormulaAt, reflect_formula_all]
    rw [show m' + n + 1 = (m' + 1) + n from by omega,
      ih (m + 1) (m' + 1) (Nat.add_le_add_right h' 1)]

lemma reflect_formula_lift [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (n m : ℕ)
    (f : formula L') : ϕ.reflectFormula (m + n) (f ↑f n) = ϕ.reflectFormula m f ↑f n :=
  reflect_formula_lift_at hϕ (Nat.zero_le m) f

lemma reflect_formula_lift1 [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (m : ℕ)
    (f : formula L') : ϕ.reflectFormula (m + 1) (f ↑f 1) = ϕ.reflectFormula m f ↑f 1 :=
  reflect_formula_lift hϕ 1 m f

lemma reflect_formula_subst [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (f : formula L')
    (n m : ℕ) (s : term L') :
    ϕ.reflectFormula (m + n) (f [s // n]f) =
      (ϕ.reflectFormula (m + n + 1) f) [ϕ.reflectTerm s m // n]f :=
  by
  refine
    @formula.rec L'
      (fun f => ∀ n, ϕ.reflectFormula (m + n) (f [s // n]f) =
            (ϕ.reflectFormula (m + n + 1) f) [ϕ.reflectTerm s m // n]f)
      ?_ ?_ ?_ ?_ ?_ f n
  · intro n; rfl
  · intro t₁ t₂ n'
    simp only [substFormula, reflect_formula_equal, reflect_term_subst hϕ]
  · intro l R ts n'
    by_cases hR : R ∈ Set.range (ϕ.onRelation (n := l))
    · show
        ϕ.reflectFormula (m + n') ((appsRel (preformula.rel R) ts) [s // n']f) =
          (ϕ.reflectFormula (m + n' + 1)
              (appsRel (preformula.rel R) ts)) [ϕ.reflectTerm s m //
            n']f
      simp only [subst_formula_apps_rel, substFormula, reflect_formula_apps_rel_pos hR,
        subst_formula_apps_rel, DVec.map_map]
      congr 1
      exact DVec.map_congr_pmem (fun t _ => reflect_term_subst hϕ n' m s t)
    · show
        ϕ.reflectFormula (m + n') ((appsRel (preformula.rel R) ts) [s // n']f) =
          (ϕ.reflectFormula (m + n' + 1)
              (appsRel (preformula.rel R) ts)) [ϕ.reflectTerm s m //
            n']f
      simp only [subst_formula_apps_rel, reflect_formula_apps_rel_neg hR, substFormula]
  · intro f₁ f₂ ih₁ ih₂ n'
    simp only [substFormula, reflect_formula_imp, ih₁ n', ih₂ n']
  · intro f ih n'
    simp only [substFormula, reflect_formula_all]
    rw [show m + n' + 1 = m + (n' + 1) from by omega]
    exact congrArg preformula.all (ih (n' + 1))

@[simp]
lemma reflect_formula_subst0 [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) (m : ℕ)
    (f : formula L') (s : term L') :
    ϕ.reflectFormula m (f [s // 0]f) =
      (ϕ.reflectFormula (m + 1) f) [ϕ.reflectTerm s m // 0]f :=
  reflect_formula_subst hϕ f 0 m s

/-! ## reflect_prf_gen -/


/-- Flypitch construction `reflect_prf_gen`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def reflectPrfGen [HasDecidableRange ϕ] (hϕ : IsInjective ϕ) {Γ}
    {f : formula L'} (m : ℕ) (H : Γ ⊢ f) :
    (fun g => ϕ.reflectFormula m g) '' Γ ⊢ ϕ.reflectFormula m f := by
  induction H generalizing m with
  | axm hΓ => exact prf.axm (Set.mem_image_of_mem _ hΓ)
  | impI _ ih =>
    apply prf.impI
    have h := ih m
    rw [Set.image_insert_eq] at h
    exact h
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ (ih₁ m) (ih₂ m)
  | falsumE _ ih =>
    apply prf.falsumE
    have h := ih m
    rw [Set.image_insert_eq] at h
    exact h
  | allI _ ih =>
    apply prf.allI
    rw [Set.image_image]
    have h := ih (m + 1)
    rw [Set.image_image] at h
    have key :
      ∀ g : formula L',
        ϕ.reflectFormula (m + 1) (liftFormula1 g) =
          liftFormula1 (ϕ.reflectFormula m g) :=
      fun g => reflect_formula_lift1 hϕ m g
    simp_rw [key] at h
    exact h
  | allE₂ A t _ ih =>
    have h := ih m
    rw [reflect_formula_all] at h
    rw [reflect_formula_subst0 hϕ]
    exact prf.allE₂ _ _ h
  | ref _ _ => exact prf.ref _ _
  | subst₂ s t f₁ _ _ ih₁ ih₂ =>
    have h₁ := ih₁ m
    simp only [reflect_formula_equal] at h₁
    have h₂ := ih₂ m
    rw [reflect_formula_subst0 hϕ] at h₂
    rw [reflect_formula_subst0 hϕ]
    exact prf.subst₂ _ _ _ h₁ h₂

/-! ## filter_symbols -/


section

/-- Flypitch construction `filter_symbols`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def filterSymbols (p : Language.symbols L → Prop) : Language.{u} :=
  ⟨fun l => { f // p (Sum.inl ⟨l, f⟩) }, fun l => { R // p (Sum.inr ⟨l, R⟩) }⟩

/-- Flypitch construction `filter_symbols_Lhom`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def filterSymbolsLhom (p : Language.symbols L → Prop) : filterSymbols p →ᴸ L :=
  ⟨fun {_} => Subtype.val, fun {_} => Subtype.val⟩

theorem is_injective_filter_symbols_Lhom (p : Language.symbols L → Prop) :
    IsInjective (filterSymbolsLhom p) :=
  ⟨fun {_} => Subtype.val_injective, fun {_} => Subtype.val_injective⟩

/-- Flypitch construction `find_term_filter_symbols`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def findTermFilterSymbols (p : Language.symbols L → Prop) :
    ∀ {l} (t : preterm L l) (_h : symbolsInTerm t ⊆ {s | p s}),
      { t' : preterm (filterSymbols p) l // (filterSymbolsLhom p).onTerm t' = t }
  | _, &k, _h => ⟨&k, rfl⟩
  | _, preterm.func f, h => ⟨preterm.func ⟨f, h (Set.mem_singleton _)⟩, rfl⟩
  | _, preterm.app t₁ t₂, h =>
    by
    have ih₁ := findTermFilterSymbols p t₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := findTermFilterSymbols p t₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preterm.app ih₁.1 ih₂.1, by
        simp only [onTerm]
        exact congrArg₂ preterm.app ih₁.2 ih₂.2⟩

/-- Flypitch construction `find_formula_filter_symbols`, retained by the first-order soundness
and completeness development.
-/
@[expose]
noncomputable def findFormulaFilterSymbols (p : Language.symbols L → Prop) :
    ∀ {l} (f : @preformula L l) (_h : symbolsInFormula f ⊆ {s | p s}),
      { f' : @preformula (filterSymbols p) l //
        (filterSymbolsLhom p).onFormula f' = f }
  | _, preformula.falsum, _ => ⟨preformula.falsum, rfl⟩
  | _, preformula.equal t₁ t₂, h =>
    by
    have ih₁ := findTermFilterSymbols p t₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := findTermFilterSymbols p t₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.equal ih₁.1 ih₂.1, by
        simp only [onFormula];
        exact congrArg₂ preformula.equal ih₁.2 ih₂.2⟩
  | _, preformula.rel R, h => ⟨preformula.rel ⟨R, h (Set.mem_singleton _)⟩, rfl⟩
  | _, preformula.apprel f t, h =>
    by
    have ih₁ := findFormulaFilterSymbols p f (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := findTermFilterSymbols p t (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.apprel ih₁.1 ih₂.1, by
        simp only [onFormula];
        exact congrArg₂ preformula.apprel ih₁.2 ih₂.2⟩
  | _, preformula.imp f₁ f₂, h =>
    by
    have ih₁ :=
      findFormulaFilterSymbols p f₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ :=
      findFormulaFilterSymbols p f₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.imp ih₁.1 ih₂.1, by
        simp only [onFormula];
        exact congrArg₂ preformula.imp ih₁.2 ih₂.2⟩
  | _, preformula.all f, h =>
    by
    have ih := findFormulaFilterSymbols p f h
    exact
      ⟨preformula.all ih.1, by simp only [onFormula]; exact congrArg preformula.all ih.2⟩

end

/-! ## generalize_constant -/


/-- Flypitch construction `generalize_constant`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def generalizeConstant {Γ : Set (formula L)} (c : L.constants)
    (hΓ : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ ⋃₀ (symbolsInFormula '' Γ))
    {f : formula L} (hf : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ symbolsInFormula f)
    (H : Γ ⊢ f [preterm.func c // 0]f) : Γ ⊢ ∀'f :=
  by
  apply prf.allI
  let p : Language.symbols L → Prop := (· ≠ Sum.inl ⟨0, c⟩)
  let ψ : filterSymbols p →ᴸ L := filterSymbolsLhom p
  have hψ : IsInjective ψ := is_injective_filter_symbols_Lhom p
  haveI : HasDecidableRange ψ :=
    ⟨fun {_} _f => Classical.propDecidable _, fun {_} _R => Classical.propDecidable _⟩
      -- c is not in the range of ψ.on_function (since filter language
        -- excludes it)
  have hc : c ∉ Set.range (ψ.onFunction (n := 0)) :=
    by
    rintro
      ⟨c', hc'⟩
          -- c'.val = c, but c'.2 says Sum.inl ⟨0, c'.val⟩ ≠ Sum.inl ⟨0, c⟩
    exact
      c'.2
        (congrArg (Sum.inl ∘ Sigma.mk 0) hc')
          -- f lifts back to the filtered language
  have hf' : symbolsInFormula f ⊆ {s | p s} := by intro s hs hps; subst hps; exact hf hs
  obtain ⟨f₀, hf₀⟩ := findFormulaFilterSymbols p f hf'
  subst hf₀
  have hΓ_lift : ∀ f' ∈ Γ, ∃ f₁ : formula (filterSymbols p), ψ.onFormula f₁ = f' :=
    by
    intro f' hf'mem
    have hf'sym : symbolsInFormula f' ⊆ {s | p s} := by
      intro s hs hps; subst hps;
      exact hΓ ⟨_, Set.mem_image_of_mem _ hf'mem, hs⟩
    exact
      ⟨(findFormulaFilterSymbols p f' hf'sym).1,
        (findFormulaFilterSymbols p f' hf'sym).2⟩
        -- Build Γ₀ as preimage of Γ under ψ.on_formula
  let Γ₀ := ψ.onFormula ⁻¹' Γ
  have hΓ₀ : ψ.onFormula '' Γ₀ = Γ :=
    image_preimage_eq_of_subset_image (t := Γ₀)
      (fun f' hf' => by
        obtain ⟨f₁, hf₁⟩ := hΓ_lift f' hf'
        exact ⟨f₁, show ψ.onFormula f₁ ∈ Γ by rw [hf₁]; exact hf', hf₁⟩)
        -- Rewrite goal: lift_formula1 '' Γ ⊢ ψ.on_formula f₀
          -- as ψ.on_formula '' (lift_formula1 '' Γ₀) ⊢ ψ.on_formula f₀
  have comm :
    ∀ (g : formula (filterSymbols p)),
      liftFormula1 (ψ.onFormula g) = ψ.onFormula (liftFormula1 g) :=
    fun g => by simp [liftFormula1, on_formula_lift_at]
  conv_lhs => rw [← hΓ₀]
  rw [Set.image_image, Set.image_congr' comm, ← Set.image_image]
    -- Apply ψ.on_prf: suffices lift_formula1 '' Γ₀ ⊢ f₀
  apply ψ.onPrf
  have H' : ψ.onFormula '' Γ₀ ⊢ (ψ.onFormula f₀) [preterm.func c // 0]f := by rwa [hΓ₀]
  have step := reflectPrfGen hψ 0 H'
  rw [Set.image_image] at step
  simp only [reflect_formula_on_formula hψ 0] at step
  rw [reflect_formula_subst0 hψ] at step
  rw [reflect_term_const_neg hc, reflect_formula_on_formula hψ 1,
    lift_subst_formula_cancel] at step
  exact step

/-- Flypitch construction `sgeneralize_constant`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def sgeneralizeConstant {T : SentTheory L} (c : L.constants)
    (hΓ : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ ⋃₀ (symbolsInFormula '' T.fst))
    {f : boundedFormula L 1}
    (hf : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ symbolsInFormula f.fst)
    (H : T ⊢ₛ subst0BoundedFormula f (bdConst c)) : T ⊢ₛ bd_all f :=
  by
  simp only [SentTheory.sprf, SentTheory.fst] at H ⊢
  simp only [subst0_bounded_formula_fst, bdConst] at H
  exact generalizeConstant c hΓ hf H

/-! ## reflect_prf -/


/-- Flypitch construction `reflect_prf`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def reflectPrf {Γ : Set (formula L)} {f : formula L} (hϕ : ϕ.IsInjective)
    (h : ϕ.onFormula '' Γ ⊢ ϕ.onFormula f) : Γ ⊢ f :=
  by
  haveI : HasDecidableRange ϕ :=
    ⟨fun {l} _f => Classical.propDecidable _, fun {l} _R => Classical.propDecidable _⟩
  apply reflectPrfLift1
  have := reflectPrfGen hϕ 0 h
  simp only [Set.image_image, reflect_formula_on_formula hϕ 0] at this
  exact this

/-- Flypitch construction `reflect_sprf`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def reflectSprf {Γ : SentTheory L} {f : sentence L} (hϕ : ϕ.IsInjective)
    (h : (ϕ.onSentence '' Γ) ⊢ₛ ϕ.onSentence f) : Γ ⊢ₛ f :=
  by
  apply reflectPrf hϕ
  simp only [SentTheory.sprf, SentTheory.fst, Set.image_image, on_bounded_formula_fst,
    onSentence] at h ⊢
  exact h

/-! ## Injectivity of on_term / on_formula -/


lemma on_term_inj (h : ϕ.IsInjective) {l} :
    Function.Injective (ϕ.onTerm : preterm L l → preterm L' l) :=
  by
  intro x y hxy
  induction x with
  | var k =>
    cases y with
    | var k' =>
      simp only [onTerm, preterm.var.injEq] at hxy;
      exact congrArg preterm.var hxy
    | func _ => simp [onTerm] at hxy
    | app _ _ => simp [onTerm] at hxy
  | func f =>
    cases y with
    | var _ => simp [onTerm] at hxy
    | func f' =>
      simp only [onTerm, preterm.func.injEq] at hxy;
      exact congrArg preterm.func (h.onFunction hxy)
    | app _ _ => simp [onTerm] at hxy
  | app t₁ t₂ iht₁ iht₂ =>
    cases y with
    | var _ => simp [onTerm] at hxy
    | func _ => simp [onTerm] at hxy
    | app t₁' t₂' =>
      simp only [onTerm, preterm.app.injEq] at hxy
      exact congrArg₂ preterm.app (iht₁ hxy.1) (iht₂ hxy.2)

lemma on_formula_inj (h : ϕ.IsInjective) {l} :
    Function.Injective (ϕ.onFormula : @preformula L l → @preformula L' l) :=
  by
  intro x y hxy
  induction x with
  | falsum => cases y <;> simp [onFormula] at hxy ⊢
  | equal t₁ t₂ =>
    cases y with
    | equal t₁' t₂' =>
      simp only [onFormula, preformula.equal.injEq] at hxy
      exact congrArg₂ preformula.equal (on_term_inj h hxy.1) (on_term_inj h hxy.2)
    | _ => simp [onFormula] at hxy
  | rel R =>
    cases y with
    | rel R' =>
      simp only [onFormula, preformula.rel.injEq] at hxy;
      exact congrArg preformula.rel (h.onRelation hxy)
    | _ => simp [onFormula] at hxy
  | apprel f t ihf =>
    cases y with
    | apprel f' t' =>
      simp only [onFormula, preformula.apprel.injEq] at hxy
      exact congrArg₂ preformula.apprel (ihf hxy.1) (on_term_inj h hxy.2)
    | _ => simp [onFormula] at hxy
  | imp f₁ f₂ ihf₁ ihf₂ =>
    cases y with
    | imp f₁' f₂' =>
      simp only [onFormula, preformula.imp.injEq] at hxy
      exact congrArg₂ preformula.imp (ihf₁ hxy.1) (ihf₂ hxy.2)
    | _ => simp [onFormula] at hxy
  | all f ihf =>
    cases y with
    | all f' =>
      simp only [onFormula, preformula.all.injEq] at hxy;
      exact congrArg preformula.all (ihf hxy)
    | _ => simp [onFormula] at hxy

lemma on_bounded_term_inj (h : ϕ.IsInjective) {n l} :
    Function.Injective
      (ϕ.onBoundedTerm : BoundedPreterm L n l → BoundedPreterm L' n l) :=
  by
  intro x y hxy
  apply BoundedPreterm.eq
  exact
    on_term_inj h (by simpa [on_bounded_term_fst] using congrArg BoundedPreterm.fst hxy)

lemma on_bounded_formula_inj (h : ϕ.IsInjective) {n l} :
    Function.Injective
      (ϕ.onBoundedFormula : BoundedPreformula L n l → BoundedPreformula L' n l) :=
  by
  intro x y hxy
  apply BoundedPreformula.eq
  exact
    on_formula_inj h
      (by simpa [on_bounded_formula_fst] using congrArg BoundedPreformula.fst hxy)

variable (ϕ)

/-! ## reduct — L-structure from L'-structure via ϕ -/


/-- Flypitch construction `reduct`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def reduct (S : Structure L') : Structure L :=
  ⟨S.carrier, fun {_n} f => S.funMap (ϕ.onFunction f), fun {_n} R =>
    S.relMap (ϕ.onRelation R)⟩

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:95 S "[[" ϕ "]]" => Lhom.reduct ϕ S

variable {ϕ}

@[simp]
lemma reduct_coe (S : Structure L') : (reduct ϕ S).carrier = S.carrier :=
  rfl

/-- Flypitch construction `reduct_id`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def reductId {S : Structure L'} : S.carrier → (ϕ.reduct S).carrier :=
  id

@[simp]
lemma reduct_term_eq {S : Structure L'} (hϕ : ϕ.IsInjective) {n} (xs : DVec S n) :
    ∀ {l} (t : BoundedPreterm L n l) (xs' : DVec S l),
      realizeBoundedTerm xs (ϕ.onBoundedTerm t) xs' =
        @realizeBoundedTerm L (ϕ.reduct S) n xs l t xs'
  | _, BoundedPreterm.bd_var k, xs' => rfl
  | _, BoundedPreterm.bd_func f, xs' => rfl
  | _, BoundedPreterm.bd_app t s, xs' =>
    by
    simp only [onBoundedTerm, realizeBoundedTerm]
    rw [reduct_term_eq hϕ xs s DVec.nil]
    exact reduct_term_eq hϕ xs t _

lemma reduct_bounded_formula_iff {S : Structure L'} (hϕ : ϕ.IsInjective) :
    ∀ {n l} (xs : DVec S n) (xs' : DVec S l) (f : BoundedPreformula L n l),
      realizeBoundedFormula xs (ϕ.onBoundedFormula f) xs' ↔
        @realizeBoundedFormula L (ϕ.reduct S) n l xs f xs'
  | _, _, xs, xs', bd_falsum => Iff.rfl
  | _, _, xs, xs', bd_equal t₁ t₂ =>
    by
    simp only [onBoundedFormula, realizeBoundedFormula,
      reduct_term_eq hϕ xs t₁ DVec.nil, reduct_term_eq hϕ xs t₂ DVec.nil]
    exact Iff.rfl
  | _, _, xs, xs', bd_rel _ => Iff.rfl
  | _, _, xs, xs', bd_apprel f t =>
    by
    simp only [onBoundedFormula, realizeBoundedFormula,
      reduct_term_eq hϕ xs t DVec.nil]
    exact reduct_bounded_formula_iff hϕ xs (DVec.cons _ xs') f
  | _, _, xs, xs', bd_imp f₁ f₂ =>
    by
    simp only [onBoundedFormula, realizeBoundedFormula]
    exact
      Iff.imp (reduct_bounded_formula_iff hϕ xs xs' f₁)
        (reduct_bounded_formula_iff hϕ xs xs' f₂)
  | _, _, xs, xs', bd_all f =>
    by
    simp only [onBoundedFormula, realizeBoundedFormula]
    constructor
    · intro h x; exact (reduct_bounded_formula_iff hϕ (DVec.cons x xs) xs' f).mp (h x)
    · intro h x; exact (reduct_bounded_formula_iff hϕ (DVec.cons x xs) xs' f).mpr (h x)

lemma reduct_ssatisfied {S : Structure L'} {f : sentence L} (hϕ : ϕ.IsInjective)
    (h : S ⊨ₘ ϕ.onSentence f) : ϕ.reduct S ⊨ₘ f :=
  (reduct_bounded_formula_iff hϕ DVec.nil DVec.nil f).mp h

lemma reduct_ssatisfied' {S : Structure L'} {f : sentence L} (hϕ : ϕ.IsInjective)
    (h : S ⊨ₘ ϕ.onBoundedFormula f) : ϕ.reduct S ⊨ₘ f :=
  (reduct_bounded_formula_iff hϕ DVec.nil DVec.nil f).mp h

theorem reduct_all_ssatisfied {S : Structure L'} {T : SentTheory L} (hϕ : ϕ.IsInjective)
    (h : allRealizeSentence S (ϕ.onSentence '' T)) :
    allRealizeSentence (reduct ϕ S) T := fun _f hf =>
  reduct_ssatisfied hϕ (h (Set.mem_image_of_mem _ hf))

lemma reduct_nonempty_of_nonempty {S : Structure L'} (H : Nonempty S.carrier) :
    Nonempty (ϕ.reduct S).carrier :=
  H

variable (ϕ)

/-- Flypitch construction `Theory_induced`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def TheoryInduced (T : SentTheory L) : SentTheory L' :=
  ϕ.onSentence '' T

variable {ϕ}

lemma is_consistent_Theory_induced (hϕ : ϕ.IsInjective) {T : SentTheory L}
    (hT : T.isConsistent) : (ϕ.TheoryInduced T).isConsistent :=
  by
  intro H
  apply hT
  exact
    H.map
      (fun h => by
        have := reflectSprf hϕ (f := bd_falsum) h
        exact this)

/-! ## is_consistent_extend (the main compactness argument) -/


lemma is_consistent_finite_witness_extension {T : SentTheory L} (hT : T.isConsistent)
    (hϕ : ϕ.IsInjective) (h : boundedFormula L 1 → boundedFormula L 1)
    (hT' : ∀ (f : boundedFormula L 1), T ⊢ₛ' bdEx (h f))
    (g : boundedFormula L 1 → L'.constants) (hg : Function.Injective g)
    (hg' : ∀ x, g x ∉ Set.range (ϕ.onFunction (n := 0)))
    (s₀ : Finset (boundedFormula L 1)) :
    (ϕ.TheoryInduced T ∪
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          (↑s₀ : Set (boundedFormula L 1))).isConsistent :=
  by
  classical
    induction s₀ using Finset.induction with
  | empty =>
    simp only [Finset.coe_empty, Set.image_empty, Set.union_empty]
    exact is_consistent_Theory_induced hϕ hT
  | insert ψ s hψ ih =>
    intro hs
    apply ih
    rw [Finset.coe_insert, Set.image_insert_eq] at hs
    have hs1 :
      (insert (subst0BoundedFormula (ϕ.onBoundedFormula (h ψ)) (bdConst (g ψ)))
            (ϕ.TheoryInduced T ∪ (fun f =>
                  subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
                (↑s : Set (boundedFormula L 1)))).fst ⊢'
        ⊥' :=
      by
      have heq :
        (ϕ.TheoryInduced T ∪
            insert (subst0BoundedFormula (ϕ.onBoundedFormula (h ψ)) (bdConst (g ψ)))
              ((fun f =>
                  subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
                (↑s : Set (boundedFormula L 1)))) =
          (insert (subst0BoundedFormula (ϕ.onBoundedFormula (h ψ)) (bdConst (g ψ)))
            (ϕ.TheoryInduced T ∪ (fun f =>
                  subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
                (↑s : Set (boundedFormula L 1)))) :=
        by
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto
      rw [heq] at hs; exact hs
    let Γ :=
      ϕ.TheoryInduced T ∪
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          (↑s : Set (boundedFormula L 1))
    let ψ' : sentence L' :=
      subst0BoundedFormula (ϕ.onBoundedFormula (h ψ)) (bdConst (g ψ))
    change
      Γ.fst ⊢'
        ⊥'
          -- hs1 : (insert ψ' Γ).fst ⊢' ⊥'
                -- Get: Γ ⊢ ψ' ⟹ ⊥, ie Γ ⊢ ¬ψ'
    have hneg : Γ.fst ⊢' (∼ψ'.fst) :=
      by
      change Γ.fst ⊢' (ψ'.fst ⟹ ⊥')
      apply impI'
      change insert ψ'.fst Γ.fst ⊢' (⊥' : formula L')
      have himg : insert ψ'.fst Γ.fst = (insert ψ' Γ).fst := by
        simp only [SentTheory.fst, Set.image_insert_eq]
      rw [himg]; exact hs1
    let nhψ : boundedFormula L' 1 :=
      bdNot
        (ϕ.onBoundedFormula (h ψ))
          -- Re-cast hneg as a proof of subst0_bounded_formula nhψ
                -- (bd_const (g ψ))
    have hneg' : Γ ⊢ₛ' subst0BoundedFormula nhψ (bdConst (g ψ)) :=
      by
      change Γ.fst ⊢' (subst0BoundedFormula nhψ (bdConst (g ψ))).fst
      have hfst : (subst0BoundedFormula nhψ (bdConst (g ψ))).fst = ∼ψ'.fst :=
        by
        rw [subst0_bounded_formula_fst]
        change substFormula nhψ.fst (bdConst (g ψ)).fst 0 = _
        change
          substFormula ((ϕ.onBoundedFormula (h ψ)).fst ⟹ ⊥') (bdConst (g ψ)).fst 0 =
            ∼ψ'.fst
        change
          (substFormula (ϕ.onBoundedFormula (h ψ)).fst (bdConst (g ψ)).fst 0) ⟹ ⊥' =
            ∼ψ'.fst
        change _ = ψ'.fst ⟹ ⊥'
        rw [show
            ψ'.fst = substFormula (ϕ.onBoundedFormula (h ψ)).fst (bdConst (g ψ)).fst 0
            from subst0_bounded_formula_fst _ _]
      rw [hfst]; exact hneg
    let c : Language.symbols L' :=
      Sum.inl
        ⟨0, g ψ⟩
          -- Show c ∉ ⋃₀ (symbols_in_formula '' Γ.fst)
    have hΓ_no_c : c ∉ ⋃₀ (symbolsInFormula '' Γ.fst) :=
      by
      rintro ⟨X, hX, hcX⟩
      rcases hX with
        ⟨f', hf', rfl⟩
          -- f' ∈ Γ.fst means f' = (some sentence in Γ).fst
      rcases hf' with ⟨σ, hσ, rfl⟩
      rcases hσ with hσ_T | hσ_img
      · -- σ ∈ Theory_induced T = ϕ.on_sentence '' T
        rcases hσ_T with
          ⟨τ, _hτ, rfl⟩
            -- σ.fst = (ϕ.on_sentence τ).fst = ϕ.on_formula τ.fst
        simp only [on_sentence_fst] at hcX
        exact ϕ.not_mem_function_in_formula_on_formula (hg' ψ) τ.fst hcX
      · -- σ in image
        rcases hσ_img with
          ⟨φ, hφ, rfl⟩
            -- σ = subst0_bounded_formula (ϕ.on_bounded_formula (h φ))
                      -- (bd_const (g φ))
        simp only [subst0_bounded_formula_fst] at hcX
        have hsubset :=
          symbols_in_formula_subst (ϕ.onBoundedFormula (h φ)).fst
            (@bdConst L' 0 (g φ)).fst 0
        have hcX' := hsubset hcX
        simp only [bdConst, BoundedPreterm.fst, symbolsInTerm, Set.mem_union] at hcX'
        rcases hcX' with hL | hR
        · -- c ∈ symbols_in_formula (ϕ.on_bounded_formula (h φ)).fst
                      -- Recall c = Sum.inl ⟨0, g ψ⟩; use hg' ψ
          rw [on_bounded_formula_fst] at hL
          exact ϕ.not_mem_function_in_formula_on_formula (hg' ψ) _ hL
        · -- c = Sum.inl ⟨0, g φ⟩, which means g ψ = g φ, hence ψ = φ
          have : (⟨0, g ψ⟩ : Σ l, L'.functions l) = ⟨0, g φ⟩ := Sum.inl.inj hR
          have hgeq : g ψ = g φ := eq_of_heq (Sigma.mk.inj this).2
          have hpsi : ψ = φ := hg hgeq
          subst hpsi
          exact hψ hφ
    have hnhψ_no_c : c ∉ symbolsInFormula nhψ.fst :=
      by
      simp only [nhψ, bdNot, BoundedPreformula.fst, on_bounded_formula_fst,
        symbolsInFormula, Set.mem_union, Set.mem_empty_iff_false, or_false]
      exact ϕ.not_mem_function_in_formula_on_formula (hg' ψ) (h ψ).fst
    have hgen : Γ ⊢ₛ' bd_all nhψ :=
      hneg'.map
        (fun pf => sgeneralizeConstant (g ψ) hΓ_no_c hnhψ_no_c pf)
          -- Now bd_all nhψ = bd_all (bd_not (ϕ.on_bounded_formula (h ψ)))
                -- = bd_not (bd_ex ...)
                -- which contradicts bd_ex (h ψ) being provable from T (lifted to
                -- ϕ.Theory_induced T ⊆ Γ)
                -- Get ϕ-image of hT' ψ
    have hT'_img : (ϕ.TheoryInduced T) ⊢ₛ' ϕ.onSentence (bdEx (h ψ)) := by
      exact
        hT' ψ |>.map
          (fun pf => ϕ.onSprf pf)
            -- ϕ.on_sentence (bd_ex (h ψ)) = bd_ex (ϕ.on_bounded_formula (h
                  -- ψ))
    have hex_eq : ϕ.onSentence (bdEx (h ψ)) = bdEx (ϕ.onBoundedFormula (h ψ)) :=
      by
      apply BoundedPreformula.eq
      simp only [on_sentence_fst, on_bounded_formula_fst, onFormula, bdEx, bdNot,
        BoundedPreformula.fst]
    rw [hex_eq] at hT'_img
    have hex : Γ ⊢ₛ' bdEx (ϕ.onBoundedFormula (h ψ)) :=
      by
      have hsub : ϕ.TheoryInduced T ⊆ Γ := Set.subset_union_left
      exact
        hT'_img.map
          (fun pf => weakening (Set.image_mono hsub) pf)
            -- bd_ex φ = bd_not (bd_all (bd_not φ)), so:
                  -- bd_ex (ϕ.on_bounded_formula (h ψ)) = bd_not (bd_all nhψ)
    have hex_def : bdEx (ϕ.onBoundedFormula (h ψ)) = bdNot (bd_all nhψ) := rfl
    rw [hex_def] at hex
    change Γ.fst ⊢' (⊥' : formula L')
    have hex_fst : (bdNot (bd_all nhψ)).fst = (bd_all nhψ).fst ⟹ ⊥' := rfl
    change Γ.fst ⊢' (bdNot (bd_all nhψ)).fst at hex
    rw [hex_fst] at hex
    exact impE' _ hex hgen

lemma is_consistent_extend {T : SentTheory L} (hT : T.isConsistent) (hϕ : ϕ.IsInjective)
    (h : boundedFormula L 1 → boundedFormula L 1)
    (hT' : ∀ (f : boundedFormula L 1), T ⊢ₛ' bdEx (h f))
    (g : boundedFormula L 1 → L'.constants) (hg : Function.Injective g)
    (hg' : ∀ x, g x ∉ Set.range (ϕ.onFunction (n := 0))) :
    (ϕ.TheoryInduced T ∪
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          Set.univ).isConsistent :=
  by
  have : DecidableEq (boundedFormula L 1) := fun x y => Classical.propDecidable _
  have : DecidableEq (sentence L') := fun x y =>
    Classical.propDecidable
      _
        -- Auxiliary lemma: consistency for any finite subset of
          -- witnesses.
  have lem := is_consistent_finite_witness_extension hT hϕ h hT' g hg hg'
  intro H
  have H' :
    (ϕ.TheoryInduced T ∪
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          Set.univ) ⊢ₛ'
      (bd_falsum : sentence L') :=
    H
  rcases theory_proof_compactness H' with
    ⟨T₀, h₀, hT₀⟩
      -- Decompose T₀ ⊆ T_ind ∪ image
  have hT₀' :
    (↑T₀ : Set (sentence L')) ⊆
      ϕ.TheoryInduced T ∪
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          Set.univ :=
    hT₀
  obtain ⟨t₀, s₀, hunion, ht₀, hs₀⟩ := Finset.subset_union_elim hT₀'
  have hs₀' :
    (↑s₀ : Set (sentence L')) ⊆
      (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
        Set.univ :=
    hs₀.trans
      (Set.sdiff_subset)
        -- Pull back s₀ through the image map
  rw [show
      ((fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
            Set.univ : Set (sentence L')) =
        (fun f => subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f))) ''
          Set.univ
      from rfl] at hs₀'
  rw [Finset.subset_set_image_iff] at hs₀'
  obtain ⟨s₀', _hs₀'_sub, hs₀'_img⟩ := hs₀'
  apply lem s₀'
  apply h₀.map
  intro pf
  apply weakening _ pf
  intro x hx
  rw [SentTheory.fst] at hx ⊢
  rcases hx with ⟨σ, hσ, rfl⟩
  have : σ ∈ (↑t₀ : Set (sentence L')) ∨ σ ∈ (↑s₀ : Set (sentence L')) :=
    by
    have : σ ∈ (↑(t₀ ∪ s₀) : Set (sentence L')) := by rw [hunion]; exact hσ
    simpa [Finset.coe_union, Set.mem_union] using this
  rcases this with hl | hr
  · refine ⟨σ, Or.inl (ht₀ hl), rfl⟩
  · -- σ ∈ s₀; pull back via hs₀'_img
    have hσ_in :
      σ ∈
        (↑(s₀'.image (fun f =>
                subst0BoundedFormula (ϕ.onBoundedFormula (h f)) (bdConst (g f)))) :
          Set (sentence L')) :=
      by
      rw [Finset.coe_image]
      have : σ ∈ (↑s₀ : Set (sentence L')) := hr
      rw [← hs₀'_img] at this
      simpa [Finset.coe_image] using this
    rw [Finset.coe_image] at hσ_in
    rcases hσ_in with ⟨φ, hφ, hφ_eq⟩
    refine ⟨σ, Or.inr ?_, rfl⟩
    exact ⟨φ, hφ, hφ_eq⟩

end Lhom

end Fol

end NFChoice
