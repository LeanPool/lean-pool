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

@[expose]
def Lconstants (α : Type u) : Language.{u} :=
  ⟨fun n => Nat.rec α (fun _n _ih => PEmpty) n, fun _n => PEmpty⟩

@[expose]
protected def sum (L L' : Language.{u}) : Language.{u} :=
  ⟨fun n => L.functions n ⊕ L'.functions n, fun n => L.relations n ⊕ L'.relations n⟩

@[expose]
def symbols (L : Language.{u}) :=
  (Σ l, L.functions l) ⊕ (Σ l, L.relations l)

end Language

variable {L : Language.{u}}

/-! ## symbols_in_term, symbols_in_formula -/


@[simp, expose]
def symbols_in_term : ∀ {l}, preterm L l → Set (Language.symbols L)
  | _, &_ => ∅
  | l, preterm.func f => {Sum.inl ⟨l, f⟩}
  | _, preterm.app t₁ t₂ => symbols_in_term t₁ ∪ symbols_in_term t₂

@[simp, expose]
def symbols_in_formula : ∀ {l}, @preformula L l → Set (Language.symbols L)
  | _, preformula.falsum => ∅
  | _, preformula.equal t₁ t₂ => symbols_in_term t₁ ∪ symbols_in_term t₂
  | l, preformula.rel R => {Sum.inr ⟨l, R⟩}
  | _, preformula.apprel f t => symbols_in_formula f ∪ symbols_in_term t
  | _, preformula.imp f₁ f₂ => symbols_in_formula f₁ ∪ symbols_in_formula f₂
  | _, preformula.all f => symbols_in_formula f

@[simp]
lemma symbols_in_term_lift_at (n m : ℕ) :
    ∀ {l} (t : preterm L l), symbols_in_term (t ↑' n # m) = symbols_in_term t
  | _, &k => by by_cases h : m ≤ k <;> simp [h]
  | _, preterm.func _ => rfl
  | _, preterm.app t₁ t₂ => by
    simp [symbols_in_term_lift_at n m t₁, symbols_in_term_lift_at n m t₂]

@[simp]
lemma symbols_in_term_lift (n : ℕ) {l} (t : preterm L l) :
    symbols_in_term (t ↑n) = symbols_in_term t :=
  symbols_in_term_lift_at n 0 t

lemma symbols_in_term_subst (s : term L) (n : ℕ) :
    ∀ {l} (t : preterm L l),
      symbols_in_term (subst_term t s n) ⊆ symbols_in_term t ∪ symbols_in_term s
  | _, &k => by
    rcases Nat.lt_trichotomy k n with h | h | h
    · simp [subst_term_var_lt s h]
    · subst h; simp [subst_term_var_eq, symbols_in_term_lift_at]
    · simp [subst_term_var_gt s h]
  | _, preterm.func _ => Set.subset_union_left
  | _, preterm.app t₁ t₂ =>
    by
    simp only [subst_term_app, symbols_in_term]
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
      symbols_in_formula (subst_formula f s n) ⊆ symbols_in_formula f ∪ symbols_in_term s
  | _, preformula.falsum, _, _ => Set.empty_subset _
  | _, preformula.equal t₁ t₂, s, n =>
    by
    simp only [subst_formula, symbols_in_formula]
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
    simp only [subst_formula, symbols_in_formula]
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
    simp only [subst_formula, symbols_in_formula]
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
    simp only [subst_formula, symbols_in_formula]
    exact symbols_in_formula_subst f s (n + 1)

/-! ## Lhom — language homomorphism -/


structure Lhom (L L' : Language.{u}) where
  on_function : ∀ {n}, L.functions n → L'.functions n
  on_relation : ∀ {n}, L.relations n → L'.relations n

infix:10 " →ᴸ " => Lhom  -- \^L

namespace Lhom

variable {L' : Language.{u}} (ϕ : L →ᴸ L')

@[expose]
protected def id (L : Language.{u}) : L →ᴸ L :=
  ⟨fun {_} => id, fun {_} => id⟩

@[expose]
protected def sum_inl {L L' : Language.{u}} : L →ᴸ L.sum L' :=
  ⟨fun {_} => Sum.inl, fun {_} => Sum.inl⟩

@[expose]
protected def sum_inr {L L' : Language.{u}} : L' →ᴸ L.sum L' :=
  ⟨fun {_} => Sum.inr, fun {_} => Sum.inr⟩

@[reducible, expose]
def comp {L1 L2 L3 : Language.{u}} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
  ⟨fun {n} => g.on_function ∘ f.on_function (n := n), fun {n} =>
    g.on_relation ∘ f.on_relation (n := n)⟩

local infixr:60 " ∘ᴸ " => Lhom.comp

lemma Lhom_funext {L1 L2 : Language.{u}} {F G : L1 →ᴸ L2}
    (h_fun : @Lhom.on_function _ _ F = @Lhom.on_function _ _ G)
    (h_rel : @Lhom.on_relation _ _ F = @Lhom.on_relation _ _ G) : F = G := by
  cases F;
  cases G; simp only at h_fun h_rel; subst h_fun; subst h_rel; rfl

@[simp]
lemma id_is_left_identity {L1 L2 : Language.{u}} {F : L1 →ᴸ L2} : (Lhom.id L2) ∘ᴸ F = F :=
  by cases F; rfl

@[simp]
lemma id_is_right_identity {L1 L2 : Language.{u}} {F : L1 →ᴸ L2} :
    F ∘ᴸ (Lhom.id L1) = F := by cases F; rfl

structure is_injective : Prop where
  on_function {n} : Function.Injective (ϕ.on_function (n := n))
  on_relation {n} : Function.Injective (ϕ.on_relation (n := n))

class has_decidable_range : Type u where
  on_function {n} : DecidablePred (· ∈ Set.range (ϕ.on_function (n := n)))
  on_relation {n} : DecidablePred (· ∈ Set.range (ϕ.on_relation (n := n)))

instance (priority := 100) inst_dec_fn [h : has_decidable_range ϕ] {n} :
    DecidablePred (· ∈ Set.range (ϕ.on_function (n := n))) :=
  h.on_function

instance (priority := 100) inst_dec_rel [h : has_decidable_range ϕ] {n} :
    DecidablePred (· ∈ Set.range (ϕ.on_relation (n := n))) :=
  h.on_relation

@[simp, expose]
def on_symbol : Language.symbols L → Language.symbols L'
  | Sum.inl ⟨l, f⟩ => Sum.inl ⟨l, ϕ.on_function f⟩
  | Sum.inr ⟨l, R⟩ => Sum.inr ⟨l, ϕ.on_relation R⟩

@[simp, expose]
def on_term : ∀ {l}, preterm L l → preterm L' l
  | _, &k => &k
  | _, preterm.func f => preterm.func (ϕ.on_function f)
  | _, preterm.app t₁ t₂ => preterm.app (on_term t₁) (on_term t₂)

@[simp]
lemma on_term_lift_at :
    ∀ {l} (t : preterm L l) (n m : ℕ), ϕ.on_term (t ↑' n # m) = ϕ.on_term t ↑' n # m
  | _, &k, n, m => by simp [lift_term_at]
  | _, preterm.func _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, m => by simp only [on_term, lift_term_at, on_term_lift_at]

@[simp]
lemma on_term_lift {l} (n : ℕ) (t : preterm L l) :
    ϕ.on_term (lift_term t n) = lift_term (ϕ.on_term t) n := by
  simp only [lift_term, on_term_lift_at]

@[simp]
lemma on_term_subst :
    ∀ {l} (t : preterm L l) (s : term L) (n : ℕ),
      ϕ.on_term (subst_term t s n) = subst_term (ϕ.on_term t) (ϕ.on_term s) n
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
      ϕ.on_term (apps t ts) = apps (ϕ.on_term t) (ts.map ϕ.on_term)
  | _, _, DVec.nil => rfl
  | _, t, DVec.cons t' ts => by
    simp only [apps, DVec.map]
    exact on_term_apps (preterm.app t t') ts

lemma not_mem_symbols_in_term_on_term {s : Language.symbols L'}
    (hs : s ∉ Set.range (ϕ.on_symbol)) :
    ∀ {l} (t : preterm L l), s ∉ symbols_in_term (ϕ.on_term t) :=
  by
  intro l t
  induction t with
  | var k => simp [on_term, symbols_in_term]
  | func f => exact fun h' => hs ⟨Sum.inl ⟨_, f⟩, (Set.mem_singleton_iff.mp h').symm⟩
  | app t₁ t₂ ih₁
    ih₂ =>
    simp only [on_term, symbols_in_term, Set.mem_union, not_or]
    exact ⟨ih₁, ih₂⟩

@[simp, expose]
def on_formula : ∀ {l}, @preformula L l → @preformula L' l
  | _, preformula.falsum => preformula.falsum
  | _, preformula.equal t₁ t₂ => preformula.equal (ϕ.on_term t₁) (ϕ.on_term t₂)
  | _, preformula.rel R => preformula.rel (ϕ.on_relation R)
  | _, preformula.apprel f t => preformula.apprel (on_formula f) (ϕ.on_term t)
  | _, preformula.imp f₁ f₂ => preformula.imp (on_formula f₁) (on_formula f₂)
  | _, preformula.all f => preformula.all (on_formula f)

@[simp]
lemma on_formula_lift_at :
    ∀ {l} (n m : ℕ) (f : @preformula L l),
      ϕ.on_formula (f ↑f' n # m) = ϕ.on_formula f ↑f' n # m
  | _, _, _, preformula.falsum => rfl
  | _, _, _, preformula.equal t₁ t₂ => by simp [on_term_lift_at]
  | _, _, _, preformula.rel _ => rfl
  | _, _, _, preformula.apprel f t => by simp [on_formula_lift_at, on_term_lift_at]
  | _, _, _, preformula.imp f₁ f₂ => by simp [on_formula_lift_at]
  | _, _, _, preformula.all f => by simp [on_formula_lift_at]

@[simp]
lemma on_formula_lift {l} (n : ℕ) (f : @preformula L l) :
    ϕ.on_formula (lift_formula f n) = lift_formula (ϕ.on_formula f) n := by
  simp only [lift_formula, on_formula_lift_at]

@[simp]
lemma on_formula_subst :
    ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
      ϕ.on_formula (f [s // n]f) = (ϕ.on_formula f) [ϕ.on_term s // n]f
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
      ϕ.on_formula (apps_rel f ts) = apps_rel (ϕ.on_formula f) (ts.map ϕ.on_term)
  | _, _, DVec.nil => rfl
  | _, f, DVec.cons t' ts => by
    simp only [apps_rel, DVec.map]
    exact on_formula_apps_rel (preformula.apprel f t') ts

lemma not_mem_symbols_in_formula_on_formula {s : Language.symbols L'}
    (hs : s ∉ Set.range (ϕ.on_symbol)) :
    ∀ {l} (f : @preformula L l), s ∉ symbols_in_formula (ϕ.on_formula f) :=
  by
  intro l f
  induction f with
  | falsum => simp [on_formula, symbols_in_formula]
  | equal t₁
    t₂ =>
    simp only [on_formula, symbols_in_formula, Set.mem_union, not_or]
    exact
      ⟨ϕ.not_mem_symbols_in_term_on_term hs t₁, ϕ.not_mem_symbols_in_term_on_term hs t₂⟩
  | rel R => exact fun h' => hs ⟨Sum.inr ⟨_, R⟩, (Set.mem_singleton_iff.mp h').symm⟩
  | apprel f t
    ihf =>
    simp only [on_formula, symbols_in_formula, Set.mem_union, not_or]
    exact ⟨ihf, ϕ.not_mem_symbols_in_term_on_term hs t⟩
  | imp f₁ f₂ ihf₁
    ihf₂ =>
    simp only [on_formula, symbols_in_formula, Set.mem_union, not_or]
    exact ⟨ihf₁, ihf₂⟩
  | all f ihf => exact ihf

lemma not_mem_function_in_formula_on_formula {l'} {f' : L'.functions l'}
    (h : f' ∉ Set.range (ϕ.on_function (n := l'))) {l} (f : @preformula L l) :
    (Sum.inl ⟨l', f'⟩ : Language.symbols L') ∉ symbols_in_formula (ϕ.on_formula f) :=
  by
  apply not_mem_symbols_in_formula_on_formula
  intro ⟨s, hs⟩
  apply h
  match s with
  | Sum.inl ⟨m, g⟩ =>
    simp only [on_symbol] at hs
    have heq : (⟨m, ϕ.on_function g⟩ : Σ l, L'.functions l) = ⟨l', f'⟩ := Sum.inl.inj hs
    have hm : m = l' := congrArg Sigma.fst heq
    subst hm
    exact ⟨g, eq_of_heq (Sigma.mk.inj heq).2⟩
  | Sum.inr p =>
    simp only [on_symbol] at hs
    exact absurd hs (by simp)

/-! ## on_bounded_term, on_bounded_formula -/


@[simp, expose]
def on_bounded_term {n} : ∀ {l} (_t : bounded_preterm L n l), bounded_preterm L' n l
  | _, bounded_preterm.bd_var k => bounded_preterm.bd_var k
  | _, bounded_preterm.bd_func f => bounded_preterm.bd_func (ϕ.on_function f)
  | _, bounded_preterm.bd_app t s =>
    bounded_preterm.bd_app (on_bounded_term t) (on_bounded_term s)

@[simp]
lemma on_bounded_term_fst {n} :
    ∀ {l} (t : bounded_preterm L n l), (ϕ.on_bounded_term t).fst = ϕ.on_term t.fst
  | _, bounded_preterm.bd_var _ => rfl
  | _, bounded_preterm.bd_func _ => rfl
  | _, bounded_preterm.bd_app t s => by
    simp [on_bounded_term_fst t, on_bounded_term_fst s]

@[simp, expose]
def on_bounded_formula :
    ∀ {n l} (_f : bounded_preformula L n l), bounded_preformula L' n l
  | _, _, bd_falsum => bd_falsum
  | _, _, bd_equal t₁ t₂ => bd_equal (ϕ.on_bounded_term t₁) (ϕ.on_bounded_term t₂)
  | _, _, bd_rel R => bd_rel (ϕ.on_relation R)
  | _, _, bd_apprel f t => bd_apprel (on_bounded_formula f) (ϕ.on_bounded_term t)
  | _, _, bd_imp f₁ f₂ => bd_imp (on_bounded_formula f₁) (on_bounded_formula f₂)
  | _, _, bd_all f => bd_all (on_bounded_formula f)

@[simp]
lemma on_bounded_formula_fst :
    ∀ {n l} (f : bounded_preformula L n l),
      (ϕ.on_bounded_formula f).fst = ϕ.on_formula f.fst
  | _, _, bd_falsum => rfl
  | _, _, bd_equal t₁ t₂ => by simp [on_bounded_term_fst]
  | _, _, bd_rel _ => rfl
  | _, _, bd_apprel f t => by simp [on_bounded_formula_fst f, on_bounded_term_fst]
  | _, _, bd_imp f₁ f₂ => by simp [on_bounded_formula_fst f₁, on_bounded_formula_fst f₂]
  | _, _, bd_all f => by simp [on_bounded_formula_fst f]

/-! ## Functoriality lemmas -/


@[simp]
lemma comp_on_term {L1 L2 L3 : Language.{u}} {l : ℕ} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
    @on_term L1 L3 (g.comp f) l =
      Function.comp (@on_term L2 L3 g l) (@on_term L1 L2 f l) :=
  by
  funext x
  induction x with
  | var k => rfl
  | func ff => rfl
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [on_term, Function.comp]
    exact congrArg₂ preterm.app ih₁ ih₂

@[simp]
lemma comp_on_formula {L1 L2 L3 : Language.{u}} {l : ℕ} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) :
    @on_formula L1 L3 (g.comp f) l =
      Function.comp (@on_formula L2 L3 g l) (@on_formula L1 L2 f l) :=
  by
  funext x
  induction x with
  | falsum => rfl
  | equal t₁ t₂ => simp [on_formula, comp_on_term]
  | rel R => rfl
  | apprel f t ihf =>
    simp only [on_formula, Function.comp]
    exact congrArg₂ preformula.apprel ihf (by simp [comp_on_term])
  | imp f₁ f₂ ihf₁ ihf₂ =>
    simp only [on_formula, Function.comp]
    exact congrArg₂ preformula.imp ihf₁ ihf₂
  | all f ihf =>
    simp only [on_formula, Function.comp]
    exact congrArg preformula.all ihf

@[simp]
lemma comp_on_bounded_term {L1 L2 L3 : Language.{u}} {n l : ℕ} (g : L2 →ᴸ L3)
    (f : L1 →ᴸ L2) :
    @on_bounded_term L1 L3 (g.comp f) n l =
      Function.comp (@on_bounded_term L2 L3 g n l) (@on_bounded_term L1 L2 f n l) :=
  by
  funext x
  induction x with
  | bd_var k => rfl
  | bd_func ff => rfl
  | bd_app t s iht ihs =>
    simp only [on_bounded_term, Function.comp]
    exact congrArg₂ bounded_preterm.bd_app iht ihs

@[simp]
lemma comp_on_bounded_formula {L1 L2 L3 : Language.{u}} {n l : ℕ} (g : L2 →ᴸ L3)
    (f : L1 →ᴸ L2) :
    @on_bounded_formula L1 L3 (g.comp f) n l =
      Function.comp (@on_bounded_formula L2 L3 g n l) (@on_bounded_formula L1 L2 f n l) :=
  by
  funext x
  apply bounded_preformula.eq
  simp [on_bounded_formula_fst, comp_on_formula]

lemma id_term : ∀ {l} (t : preterm L l), @on_term L L (Lhom.id L) l t = t
  | _, &_ => rfl
  | _, preterm.func _ => rfl
  | _, preterm.app t₁ t₂ => by simp [on_term, id_term t₁, id_term t₂]

lemma id_formula : ∀ {l} (f : @preformula L l), @on_formula L L (Lhom.id L) l f = f
  | _, preformula.falsum => rfl
  | _, preformula.equal t₁ t₂ => by simp [on_formula, id_term]
  | _, preformula.rel _ => rfl
  | _, preformula.apprel f t => by simp [on_formula, id_formula f, id_term]
  | _, preformula.imp f₁ f₂ => by simp [on_formula, id_formula f₁, id_formula f₂]
  | _, preformula.all f => by simp [on_formula, id_formula f]

lemma id_bounded_term {n} :
    ∀ {l} (t : bounded_preterm L n l), @on_bounded_term L L (Lhom.id L) n l t = t
  | _, bounded_preterm.bd_var _ => rfl
  | _, bounded_preterm.bd_func _ => rfl
  | _, bounded_preterm.bd_app t s => by
    simp [on_bounded_term, id_bounded_term t, id_bounded_term s]

lemma id_bounded_formula :
    ∀ {n l} (f : bounded_preformula L n l), @on_bounded_formula L L (Lhom.id L) n l f = f
  | _, _, bd_falsum => rfl
  | _, _, bd_equal t₁ t₂ => by simp [on_bounded_formula, id_bounded_term]
  | _, _, bd_rel _ => rfl
  | _, _, bd_apprel f t => by
    simp [on_bounded_formula, id_bounded_formula f, id_bounded_term]
  | _, _, bd_imp f₁ f₂ => by
    simp [on_bounded_formula, id_bounded_formula f₁, id_bounded_formula f₂]
  | _, _, bd_all f => by simp [on_bounded_formula, id_bounded_formula f]

@[simp, expose]
def on_closed_term (t : closed_term L) : closed_term L' :=
  ϕ.on_bounded_term t
@[simp, expose]
def on_sentence (f : sentence L) : sentence L' :=
  ϕ.on_bounded_formula f

theorem on_sentence_fst (f : sentence L) : (ϕ.on_sentence f).fst = ϕ.on_formula f.fst :=
  ϕ.on_bounded_formula_fst f

/-! ## on_prf — Lhom lifts proofs -/


@[expose]
noncomputable def on_prf {Γ : Set (formula L)} {f : formula L} (h : Γ ⊢ f) :
    ϕ.on_formula '' Γ ⊢ ϕ.on_formula f := by
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
    simp only [on_formula]
    apply prf.allI
    rw [Set.image_image] at ih ⊢
    have key :
      ∀ g : formula L, ϕ.on_formula (lift_formula1 g) = lift_formula1 (ϕ.on_formula g) :=
      fun g => by simp only [lift_formula1, on_formula_lift_at]
    simp_rw [key] at ih
    exact ih
  | allE₂ A t _
    ih =>
    have heq : ϕ.on_formula (A [t // 0]f) = (ϕ.on_formula A) [ϕ.on_term t // 0]f := by
      simp [on_formula_subst]
    rw [heq]
    exact prf.allE₂ _ _ ih
  | ref _ _ => exact prf.ref _ _
  | subst₂ s t f₁ _ _ ih₁
    ih₂ =>
    have heq1 : ϕ.on_formula (f₁ [s // 0]f) = (ϕ.on_formula f₁) [ϕ.on_term s // 0]f := by
      simp [on_formula_subst]
    have heq2 : ϕ.on_formula (f₁ [t // 0]f) = (ϕ.on_formula f₁) [ϕ.on_term t // 0]f := by
      simp [on_formula_subst]
    rw [heq2]
    rw [heq1] at ih₂
    exact prf.subst₂ _ _ _ ih₁ ih₂

@[expose]
noncomputable def on_sprf {Γ : SentTheory L} {f : sentence L} (h : Γ ⊢ₛ f) :
    (ϕ.on_sentence '' Γ) ⊢ₛ ϕ.on_sentence f :=
  by
  have := ϕ.on_prf h
  simp only [SentTheory.sprf, SentTheory.fst, Set.image_image, on_bounded_formula_fst,
    on_sentence] at this ⊢
  exact this

/-! ## reflect_term -/


@[expose]
noncomputable def reflect_term [has_decidable_range ϕ] (t : term L') (m : ℕ) : term L :=
  term.elim (fun k => lift_term_at (&k) 1 m)
    (fun {l} f' _ts' ts => if hf' : f' ∈ Set.range (ϕ.on_function (n := l)) then
        apps (preterm.func (Classical.choose hf')) ts else &m)
    t

variable {ϕ}

lemma reflect_term_apps_pos [has_decidable_range ϕ] {l} {f : L'.functions l}
    (hf : f ∈ Set.range (ϕ.on_function (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflect_term (apps (preterm.func f) ts) m =
      apps (preterm.func (Classical.choose hf)) (ts.map (fun t => ϕ.reflect_term t m)) :=
  (term.elim_apps _ _ f ts).trans (by rw [dite_eq_left hf]; rfl)

lemma reflect_term_apps_neg [has_decidable_range ϕ] {l} {f : L'.functions l}
    (hf : f ∉ Set.range (ϕ.on_function (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflect_term (apps (preterm.func f) ts) m = &m :=
  (term.elim_apps _ _ f ts).trans (by rw [dite_eq_right hf])

lemma reflect_term_const_pos [has_decidable_range ϕ] {c : L'.constants}
    (hf : c ∈ Set.range (ϕ.on_function (n := 0))) (m : ℕ) :
    ϕ.reflect_term (preterm.func c) m = preterm.func (Classical.choose hf) :=
  reflect_term_apps_pos hf DVec.nil m

lemma reflect_term_const_neg [has_decidable_range ϕ] {c : L'.constants}
    (hf : c ∉ Set.range (ϕ.on_function (n := 0))) (m : ℕ) :
    ϕ.reflect_term (preterm.func c) m = &m :=
  reflect_term_apps_neg hf DVec.nil m

@[simp]
lemma reflect_term_var [has_decidable_range ϕ] (k m : ℕ) :
    ϕ.reflect_term (&k) m = &k ↑' 1 # m :=
  rfl

@[simp]
lemma reflect_term_on_term [has_decidable_range ϕ] (hϕ : is_injective ϕ) (t : term L)
    (m : ℕ) : ϕ.reflect_term (ϕ.on_term t) m = t ↑' 1 # m :=
  by
  refine
    @term.rec L (fun t => ϕ.reflect_term (ϕ.on_term t) m = t ↑' 1 # m) (fun k => ?_)
      (fun f ts ih_ts => ?_) t
  · -- var k: reflect_term (&k) m = &k ↑' 1 # m
    simp [reflect_term_var, lift_term_at]
      -- func f applied to ts: reflect_term (on_term (apps (func f)
        -- ts)) m = (apps (func f) ts) ↑' 1 # m
  · have hf : ϕ.on_function f ∈ Set.range (ϕ.on_function) := Set.mem_range_self f
    simp only [on_term_apps, on_term, reflect_term_apps_pos hf, lift_term_at_apps]
    congr 1
    -- preterm.func (Classical.choose hf) = preterm.func f (modulo lift which is identity on func)
    · simp only [lift_term_at]
      exact congrArg preterm.func (hϕ.on_function (Classical.choose_spec hf))
    -- DVec.map (fun t => reflect_term t m) (DVec.map on_term ts) = DVec.map (· ↑' 1 # m) ts
    · rw [DVec.map_map]
      apply DVec.map_congr_pmem
      intro t hmem
      exact ih_ts t hmem

lemma reflect_term_lift_at [has_decidable_range ϕ] (_hϕ : is_injective ϕ) {n m m' : ℕ}
    (h : m ≤ m') (t : term L') :
    ϕ.reflect_term (t ↑' n # m) (m' + n) = ϕ.reflect_term t m' ↑' n # m :=
  by
  refine
    @term.rec L'
      (fun t => ϕ.reflect_term (t ↑' n # m) (m' + n) = ϕ.reflect_term t m' ↑' n # m)
      (fun k => ?_) (fun f ts ih_ts => ?_) t
  · -- var k: ((&k) ↑' n # m) reflected at (m'+n) = reflected (&k) at m' lifted n at m
    simp only [reflect_term_var, lift_term_at]
    split_ifs <;> simp_all [] <;> omega
  · -- func f applied to ts: by_cases on f ∈ range
    by_cases hf : f ∈ Set.range ϕ.on_function
    · simp only [lift_term_at_apps, reflect_term_apps_pos hf, lift_term_at, DVec.map_map,
        ]
      congr 1
      apply DVec.map_congr_pmem
      intro t hmem; exact ih_ts t hmem
    · show
        ϕ.reflect_term ((apps (preterm.func f) ts) ↑' n # m) (m' + n) =
          ϕ.reflect_term (apps (preterm.func f) ts) m' ↑' n # m
      simp only [lift_term_at_apps, lift_term_at, reflect_term_apps_neg hf, h, ite_true]

lemma reflect_term_lift [has_decidable_range ϕ] (hϕ : is_injective ϕ) {n m : ℕ}
    (t : term L') :
    ϕ.reflect_term (lift_term t n) (m + n) = lift_term (ϕ.reflect_term t m) n :=
  reflect_term_lift_at hϕ (Nat.zero_le m) t

lemma reflect_term_subst [has_decidable_range ϕ] (hϕ : is_injective ϕ) (n m : ℕ)
    (s t : term L') :
    ϕ.reflect_term (subst_term t s n) (m + n) =
      subst_term (ϕ.reflect_term t (m + n + 1)) (ϕ.reflect_term s m) n :=
  by
  induction t using @term.rec L' with
  | hvar
    k =>
    show
      ϕ.reflect_term (subst_term (&k) s n) (m + n) =
        subst_term (ϕ.reflect_term (&k) (m + n + 1)) (ϕ.reflect_term s m) n
    rcases Nat.lt_trichotomy k n with hk | hk | hk
    · -- k < n
      simp only [subst_term_var_lt s hk, reflect_term_var, lift_term_at,
        ite_eq_right (by omega : ¬(m + n ≤ k)),
        ite_eq_right (by omega : ¬(m + n + 1 ≤ k)), subst_term_var_lt _ hk]
        -- k = n: reflect_term (s ↑' n # 0) (m+n) = subst_term (&n ↑' 1 #
            -- (m+n+1)) (reflect_term s m) n
    · simp only [hk, subst_term_var_eq, reflect_term_var, lift_term_at,
        ite_eq_right (by omega : ¬(m + n + 1 ≤ n)), subst_term_var_eq]
      exact reflect_term_lift hϕ s
    · -- k > n
      have hk1 : 1 ≤ k := Nat.one_le_of_lt hk
      by_cases h₂' : m + n + 1 ≤ k
      · -- k ≥ m+n+1: both sides = &k
        simp only [subst_term_var_gt s hk, reflect_term_var, lift_term_at, h₂', ite_true,
          ite_eq_left (by omega : m + n ≤ k - 1), Nat.sub_add_cancel hk1,
          subst_term_var_gt _ (by omega : n < k + 1), show k + 1 - 1 = k from by omega]
      · -- n < k < m+n+1: both sides = &(k-1)
        simp only [subst_term_var_gt s hk, reflect_term_var, lift_term_at,
          ite_eq_right (by omega : ¬(m + n ≤ k - 1)), ite_eq_right h₂',
          subst_term_var_gt _ hk]
  | hfunc f ts
    ih_ts =>
    show
      ϕ.reflect_term (subst_term (apps (preterm.func f) ts) s n) (m + n) =
        subst_term (ϕ.reflect_term (apps (preterm.func f) ts) (m + n + 1))
          (ϕ.reflect_term s m) n
    have hn : n < m + n + 1 := by omega
    by_cases hf : f ∈ Set.range ϕ.on_function
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
@[expose]
noncomputable def reflect_formula_aux' [has_decidable_range ϕ] (f : formula L') :
    ℕ → formula L :=
  (formula.rec (C := fun _ => ℕ → formula L) (fun _ => ⊥')
      (fun t₁ t₂ m' => ϕ.reflect_term t₁ m' ≃ ϕ.reflect_term t₂ m') (fun {l} R ts m' =>
        if hR : R ∈ Set.range (ϕ.on_relation (n := l)) then
          apps_rel (preformula.rel (Classical.choose hR))
            (DVec.map (fun t => ϕ.reflect_term t m') ts) else ⊥')
      (fun {_f₁} {_f₂} (ih₁ : ℕ → formula L) (ih₂ : ℕ → formula L) (m' : ℕ) =>
        (ih₁ m') ⟹ (ih₂ m')) (fun {_f} (ih : ℕ → formula L) (m' : ℕ) => ∀'(ih (m' + 1))) f :
    ℕ → formula L)

@[expose]
noncomputable def reflect_formula [has_decidable_range ϕ] (m : ℕ) (f : formula L') :
    formula L :=
  @reflect_formula_aux' L L' ϕ _ f m

variable {ϕ}

lemma reflect_formula_apps_rel_pos [has_decidable_range ϕ] {l} {R : L'.relations l}
    (hR : R ∈ Set.range (ϕ.on_relation (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflect_formula m (apps_rel (preformula.rel R) ts) =
      apps_rel (preformula.rel (Classical.choose hR))
        (ts.map (fun t => ϕ.reflect_term t m)) :=
  by
  simp only [reflect_formula, reflect_formula_aux', formula.rec_apps_rel, dite_eq_left hR]

lemma reflect_formula_apps_rel_neg [has_decidable_range ϕ] {l} {R : L'.relations l}
    (hR : R ∉ Set.range (ϕ.on_relation (n := l))) (ts : DVec (term L') l) (m : ℕ) :
    ϕ.reflect_formula m (apps_rel (preformula.rel R) ts) = ⊥' := by
  simp only [reflect_formula, reflect_formula_aux', formula.rec_apps_rel,
    dite_eq_right hR]

@[simp]
lemma reflect_formula_equal [has_decidable_range ϕ] (t₁ t₂ : term L') (m : ℕ) :
    ϕ.reflect_formula m (t₁ ≃ t₂) = ϕ.reflect_term t₁ m ≃ ϕ.reflect_term t₂ m :=
  by
  simp only [reflect_formula]
  rfl

@[simp]
lemma reflect_formula_imp [has_decidable_range ϕ] (f₁ f₂ : formula L') (m : ℕ) :
    ϕ.reflect_formula m (f₁ ⟹ f₂) = ϕ.reflect_formula m f₁ ⟹ ϕ.reflect_formula m f₂ :=
  by
  simp only [reflect_formula]
  rfl

@[simp]
lemma reflect_formula_all [has_decidable_range ϕ] (f : formula L') (m : ℕ) :
    ϕ.reflect_formula m (∀'f) = ∀'(ϕ.reflect_formula (m + 1) f) :=
  by
  simp only [reflect_formula]
  rfl

@[simp]
lemma reflect_formula_on_formula [has_decidable_range ϕ] (hϕ : is_injective ϕ) (m : ℕ)
    (f : formula L) : ϕ.reflect_formula m (ϕ.on_formula f) = f ↑f' 1 # m :=
  by
  refine
    @formula.rec L (fun f => ∀ m, ϕ.reflect_formula m (ϕ.on_formula f) = f ↑f' 1 # m) ?_
      ?_ ?_ ?_ ?_ f m
  · intro m; rfl
  · intro t₁ t₂ m
    simp only [on_formula, reflect_formula_equal, lift_formula_at,
      reflect_term_on_term hϕ]
  · intro l R ts m
    have hR : ϕ.on_relation R ∈ Set.range ϕ.on_relation := Set.mem_range_self _
    simp only [on_formula_apps_rel, on_formula, reflect_formula_apps_rel_pos hR,
      lift_formula_at_apps_rel]
    congr 1
    · simp only [lift_formula_at]
      exact congrArg preformula.rel (hϕ.on_relation (Classical.choose_spec hR))
    · rw [DVec.map_map]
      apply DVec.map_congr_pmem
      intro t _
      exact reflect_term_on_term hϕ t m
  · intro f₁ f₂ ih₁ ih₂ m
    simp only [on_formula, reflect_formula_imp, lift_formula_at, ih₁ m, ih₂ m]
  · intro f ih m
    simp only [on_formula, reflect_formula_all, lift_formula_at, ih (m + 1)]

lemma reflect_formula_lift_at [has_decidable_range ϕ] (hϕ : is_injective ϕ) {n m m' : ℕ}
    (h : m ≤ m') (f : formula L') :
    ϕ.reflect_formula (m' + n) (f ↑f' n # m) = ϕ.reflect_formula m' f ↑f' n # m :=
  by
  refine
    @formula.rec L'
      (fun f => ∀ m m', m ≤ m' →
            ϕ.reflect_formula (m' + n) (f ↑f' n # m) = ϕ.reflect_formula m' f ↑f' n # m)
      ?_ ?_ ?_ ?_ ?_ f m m' h
  · intro m m' _; rfl
  · intro t₁ t₂ m m' h'
    simp only [lift_formula_at, reflect_formula_equal, reflect_term_lift_at hϕ h']
  · intro l R ts m m' h'
    by_cases hR : R ∈ Set.range (ϕ.on_relation (n := l))
    · show
        ϕ.reflect_formula (m' + n) ((apps_rel (preformula.rel R) ts) ↑f' n # m) =
          ϕ.reflect_formula m' (apps_rel (preformula.rel R) ts) ↑f' n # m
      simp only [lift_formula_at_apps_rel, lift_formula_at,
        reflect_formula_apps_rel_pos hR, lift_formula_at_apps_rel, DVec.map_map]
      congr 1
      apply DVec.map_congr_pmem
      intro t _; exact reflect_term_lift_at hϕ h' t
    · show
        ϕ.reflect_formula (m' + n) ((apps_rel (preformula.rel R) ts) ↑f' n # m) =
          ϕ.reflect_formula m' (apps_rel (preformula.rel R) ts) ↑f' n # m
      simp only [lift_formula_at_apps_rel, lift_formula_at,
        reflect_formula_apps_rel_neg hR]
  · intro f₁ f₂ ih₁ ih₂ m m' h'
    simp only [lift_formula_at, reflect_formula_imp, ih₁ m m' h', ih₂ m m' h']
  · intro f ih m m' h'
    simp only [lift_formula_at, reflect_formula_all]
    rw [show m' + n + 1 = (m' + 1) + n from by omega,
      ih (m + 1) (m' + 1) (Nat.add_le_add_right h' 1)]

lemma reflect_formula_lift [has_decidable_range ϕ] (hϕ : is_injective ϕ) (n m : ℕ)
    (f : formula L') : ϕ.reflect_formula (m + n) (f ↑f n) = ϕ.reflect_formula m f ↑f n :=
  reflect_formula_lift_at hϕ (Nat.zero_le m) f

lemma reflect_formula_lift1 [has_decidable_range ϕ] (hϕ : is_injective ϕ) (m : ℕ)
    (f : formula L') : ϕ.reflect_formula (m + 1) (f ↑f 1) = ϕ.reflect_formula m f ↑f 1 :=
  reflect_formula_lift hϕ 1 m f

lemma reflect_formula_subst [has_decidable_range ϕ] (hϕ : is_injective ϕ) (f : formula L')
    (n m : ℕ) (s : term L') :
    ϕ.reflect_formula (m + n) (f [s // n]f) =
      (ϕ.reflect_formula (m + n + 1) f) [ϕ.reflect_term s m // n]f :=
  by
  refine
    @formula.rec L'
      (fun f => ∀ n, ϕ.reflect_formula (m + n) (f [s // n]f) =
            (ϕ.reflect_formula (m + n + 1) f) [ϕ.reflect_term s m // n]f)
      ?_ ?_ ?_ ?_ ?_ f n
  · intro n; rfl
  · intro t₁ t₂ n'
    simp only [subst_formula, reflect_formula_equal, reflect_term_subst hϕ]
  · intro l R ts n'
    by_cases hR : R ∈ Set.range (ϕ.on_relation (n := l))
    · show
        ϕ.reflect_formula (m + n') ((apps_rel (preformula.rel R) ts) [s // n']f) =
          (ϕ.reflect_formula (m + n' + 1)
              (apps_rel (preformula.rel R) ts)) [ϕ.reflect_term s m //
            n']f
      simp only [subst_formula_apps_rel, subst_formula, reflect_formula_apps_rel_pos hR,
        subst_formula_apps_rel, DVec.map_map]
      congr 1
      exact DVec.map_congr_pmem (fun t _ => reflect_term_subst hϕ n' m s t)
    · show
        ϕ.reflect_formula (m + n') ((apps_rel (preformula.rel R) ts) [s // n']f) =
          (ϕ.reflect_formula (m + n' + 1)
              (apps_rel (preformula.rel R) ts)) [ϕ.reflect_term s m //
            n']f
      simp only [subst_formula_apps_rel, reflect_formula_apps_rel_neg hR, subst_formula]
  · intro f₁ f₂ ih₁ ih₂ n'
    simp only [subst_formula, reflect_formula_imp, ih₁ n', ih₂ n']
  · intro f ih n'
    simp only [subst_formula, reflect_formula_all]
    rw [show m + n' + 1 = m + (n' + 1) from by omega]
    exact congrArg preformula.all (ih (n' + 1))

@[simp]
lemma reflect_formula_subst0 [has_decidable_range ϕ] (hϕ : is_injective ϕ) (m : ℕ)
    (f : formula L') (s : term L') :
    ϕ.reflect_formula m (f [s // 0]f) =
      (ϕ.reflect_formula (m + 1) f) [ϕ.reflect_term s m // 0]f :=
  reflect_formula_subst hϕ f 0 m s

/-! ## reflect_prf_gen -/


@[expose]
noncomputable def reflect_prf_gen [has_decidable_range ϕ] (hϕ : is_injective ϕ) {Γ}
    {f : formula L'} (m : ℕ) (H : Γ ⊢ f) :
    (fun g => ϕ.reflect_formula m g) '' Γ ⊢ ϕ.reflect_formula m f := by
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
        ϕ.reflect_formula (m + 1) (lift_formula1 g) =
          lift_formula1 (ϕ.reflect_formula m g) :=
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

@[reducible, expose]
def filter_symbols (p : Language.symbols L → Prop) : Language.{u} :=
  ⟨fun l => { f // p (Sum.inl ⟨l, f⟩) }, fun l => { R // p (Sum.inr ⟨l, R⟩) }⟩

@[expose]
def filter_symbols_Lhom (p : Language.symbols L → Prop) : filter_symbols p →ᴸ L :=
  ⟨fun {_} => Subtype.val, fun {_} => Subtype.val⟩

theorem is_injective_filter_symbols_Lhom (p : Language.symbols L → Prop) :
    is_injective (filter_symbols_Lhom p) :=
  ⟨fun {_} => Subtype.val_injective, fun {_} => Subtype.val_injective⟩

@[expose]
noncomputable def find_term_filter_symbols (p : Language.symbols L → Prop) :
    ∀ {l} (t : preterm L l) (_h : symbols_in_term t ⊆ {s | p s}),
      { t' : preterm (filter_symbols p) l // (filter_symbols_Lhom p).on_term t' = t }
  | _, &k, _h => ⟨&k, rfl⟩
  | _, preterm.func f, h => ⟨preterm.func ⟨f, h (Set.mem_singleton _)⟩, rfl⟩
  | _, preterm.app t₁ t₂, h =>
    by
    have ih₁ := find_term_filter_symbols p t₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := find_term_filter_symbols p t₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preterm.app ih₁.1 ih₂.1, by
        simp only [on_term]
        exact congrArg₂ preterm.app ih₁.2 ih₂.2⟩

@[expose]
noncomputable def find_formula_filter_symbols (p : Language.symbols L → Prop) :
    ∀ {l} (f : @preformula L l) (_h : symbols_in_formula f ⊆ {s | p s}),
      { f' : @preformula (filter_symbols p) l //
        (filter_symbols_Lhom p).on_formula f' = f }
  | _, preformula.falsum, _ => ⟨preformula.falsum, rfl⟩
  | _, preformula.equal t₁ t₂, h =>
    by
    have ih₁ := find_term_filter_symbols p t₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := find_term_filter_symbols p t₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.equal ih₁.1 ih₂.1, by
        simp only [on_formula];
        exact congrArg₂ preformula.equal ih₁.2 ih₂.2⟩
  | _, preformula.rel R, h => ⟨preformula.rel ⟨R, h (Set.mem_singleton _)⟩, rfl⟩
  | _, preformula.apprel f t, h =>
    by
    have ih₁ := find_formula_filter_symbols p f (Set.Subset.trans Set.subset_union_left h)
    have ih₂ := find_term_filter_symbols p t (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.apprel ih₁.1 ih₂.1, by
        simp only [on_formula];
        exact congrArg₂ preformula.apprel ih₁.2 ih₂.2⟩
  | _, preformula.imp f₁ f₂, h =>
    by
    have ih₁ :=
      find_formula_filter_symbols p f₁ (Set.Subset.trans Set.subset_union_left h)
    have ih₂ :=
      find_formula_filter_symbols p f₂ (Set.Subset.trans Set.subset_union_right h)
    exact
      ⟨preformula.imp ih₁.1 ih₂.1, by
        simp only [on_formula];
        exact congrArg₂ preformula.imp ih₁.2 ih₂.2⟩
  | _, preformula.all f, h =>
    by
    have ih := find_formula_filter_symbols p f h
    exact
      ⟨preformula.all ih.1, by simp only [on_formula]; exact congrArg preformula.all ih.2⟩

end

/-! ## generalize_constant -/


@[expose]
noncomputable def generalize_constant {Γ : Set (formula L)} (c : L.constants)
    (hΓ : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ ⋃₀ (symbols_in_formula '' Γ))
    {f : formula L} (hf : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ symbols_in_formula f)
    (H : Γ ⊢ f [preterm.func c // 0]f) : Γ ⊢ ∀'f :=
  by
  apply prf.allI
  let p : Language.symbols L → Prop := (· ≠ Sum.inl ⟨0, c⟩)
  let ψ : filter_symbols p →ᴸ L := filter_symbols_Lhom p
  have hψ : is_injective ψ := is_injective_filter_symbols_Lhom p
  haveI : has_decidable_range ψ :=
    ⟨fun {_} _f => Classical.propDecidable _, fun {_} _R => Classical.propDecidable _⟩
      -- c is not in the range of ψ.on_function (since filter language
        -- excludes it)
  have hc : c ∉ Set.range (ψ.on_function (n := 0)) :=
    by
    rintro
      ⟨c', hc'⟩
          -- c'.val = c, but c'.2 says Sum.inl ⟨0, c'.val⟩ ≠ Sum.inl ⟨0, c⟩
    exact
      c'.2
        (congrArg (Sum.inl ∘ Sigma.mk 0) hc')
          -- f lifts back to the filtered language
  have hf' : symbols_in_formula f ⊆ {s | p s} := by intro s hs hps; subst hps; exact hf hs
  obtain ⟨f₀, hf₀⟩ := find_formula_filter_symbols p f hf'
  subst hf₀
  have hΓ_lift : ∀ f' ∈ Γ, ∃ f₁ : formula (filter_symbols p), ψ.on_formula f₁ = f' :=
    by
    intro f' hf'mem
    have hf'sym : symbols_in_formula f' ⊆ {s | p s} := by
      intro s hs hps; subst hps;
      exact hΓ ⟨_, Set.mem_image_of_mem _ hf'mem, hs⟩
    exact
      ⟨(find_formula_filter_symbols p f' hf'sym).1,
        (find_formula_filter_symbols p f' hf'sym).2⟩
        -- Build Γ₀ as preimage of Γ under ψ.on_formula
  let Γ₀ := ψ.on_formula ⁻¹' Γ
  have hΓ₀ : ψ.on_formula '' Γ₀ = Γ :=
    image_preimage_eq_of_subset_image (t := Γ₀)
      (fun f' hf' => by
        obtain ⟨f₁, hf₁⟩ := hΓ_lift f' hf'
        exact ⟨f₁, show ψ.on_formula f₁ ∈ Γ by rw [hf₁]; exact hf', hf₁⟩)
        -- Rewrite goal: lift_formula1 '' Γ ⊢ ψ.on_formula f₀
          -- as ψ.on_formula '' (lift_formula1 '' Γ₀) ⊢ ψ.on_formula f₀
  have comm :
    ∀ (g : formula (filter_symbols p)),
      lift_formula1 (ψ.on_formula g) = ψ.on_formula (lift_formula1 g) :=
    fun g => by simp [lift_formula1, on_formula_lift_at]
  conv_lhs => rw [← hΓ₀]
  rw [Set.image_image, Set.image_congr' comm, ← Set.image_image]
    -- Apply ψ.on_prf: suffices lift_formula1 '' Γ₀ ⊢ f₀
  apply ψ.on_prf
  have H' : ψ.on_formula '' Γ₀ ⊢ (ψ.on_formula f₀) [preterm.func c // 0]f := by rwa [hΓ₀]
  have step := reflect_prf_gen hψ 0 H'
  rw [Set.image_image] at step
  simp only [reflect_formula_on_formula hψ 0] at step
  rw [reflect_formula_subst0 hψ] at step
  rw [reflect_term_const_neg hc, reflect_formula_on_formula hψ 1,
    lift_subst_formula_cancel] at step
  exact step

@[expose]
noncomputable def sgeneralize_constant {T : SentTheory L} (c : L.constants)
    (hΓ : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ ⋃₀ (symbols_in_formula '' T.fst))
    {f : bounded_formula L 1}
    (hf : (Sum.inl ⟨0, c⟩ : Language.symbols L) ∉ symbols_in_formula f.fst)
    (H : T ⊢ₛ subst0_bounded_formula f (bd_const c)) : T ⊢ₛ bd_all f :=
  by
  simp only [SentTheory.sprf, SentTheory.fst] at H ⊢
  simp only [subst0_bounded_formula_fst, bd_const] at H
  exact generalize_constant c hΓ hf H

/-! ## reflect_prf -/


@[expose]
noncomputable def reflect_prf {Γ : Set (formula L)} {f : formula L} (hϕ : ϕ.is_injective)
    (h : ϕ.on_formula '' Γ ⊢ ϕ.on_formula f) : Γ ⊢ f :=
  by
  haveI : has_decidable_range ϕ :=
    ⟨fun {l} _f => Classical.propDecidable _, fun {l} _R => Classical.propDecidable _⟩
  apply reflect_prf_lift1
  have := reflect_prf_gen hϕ 0 h
  simp only [Set.image_image, reflect_formula_on_formula hϕ 0] at this
  exact this

@[expose]
noncomputable def reflect_sprf {Γ : SentTheory L} {f : sentence L} (hϕ : ϕ.is_injective)
    (h : (ϕ.on_sentence '' Γ) ⊢ₛ ϕ.on_sentence f) : Γ ⊢ₛ f :=
  by
  apply reflect_prf hϕ
  simp only [SentTheory.sprf, SentTheory.fst, Set.image_image, on_bounded_formula_fst,
    on_sentence] at h ⊢
  exact h

/-! ## Injectivity of on_term / on_formula -/


lemma on_term_inj (h : ϕ.is_injective) {l} :
    Function.Injective (ϕ.on_term : preterm L l → preterm L' l) :=
  by
  intro x y hxy
  induction x with
  | var k =>
    cases y with
    | var k' =>
      simp only [on_term, preterm.var.injEq] at hxy;
      exact congrArg preterm.var hxy
    | func _ => simp [on_term] at hxy
    | app _ _ => simp [on_term] at hxy
  | func f =>
    cases y with
    | var _ => simp [on_term] at hxy
    | func f' =>
      simp only [on_term, preterm.func.injEq] at hxy;
      exact congrArg preterm.func (h.on_function hxy)
    | app _ _ => simp [on_term] at hxy
  | app t₁ t₂ iht₁ iht₂ =>
    cases y with
    | var _ => simp [on_term] at hxy
    | func _ => simp [on_term] at hxy
    | app t₁' t₂' =>
      simp only [on_term, preterm.app.injEq] at hxy
      exact congrArg₂ preterm.app (iht₁ hxy.1) (iht₂ hxy.2)

lemma on_formula_inj (h : ϕ.is_injective) {l} :
    Function.Injective (ϕ.on_formula : @preformula L l → @preformula L' l) :=
  by
  intro x y hxy
  induction x with
  | falsum => cases y <;> simp [on_formula] at hxy ⊢
  | equal t₁ t₂ =>
    cases y with
    | equal t₁' t₂' =>
      simp only [on_formula, preformula.equal.injEq] at hxy
      exact congrArg₂ preformula.equal (on_term_inj h hxy.1) (on_term_inj h hxy.2)
    | _ => simp [on_formula] at hxy
  | rel R =>
    cases y with
    | rel R' =>
      simp only [on_formula, preformula.rel.injEq] at hxy;
      exact congrArg preformula.rel (h.on_relation hxy)
    | _ => simp [on_formula] at hxy
  | apprel f t ihf =>
    cases y with
    | apprel f' t' =>
      simp only [on_formula, preformula.apprel.injEq] at hxy
      exact congrArg₂ preformula.apprel (ihf hxy.1) (on_term_inj h hxy.2)
    | _ => simp [on_formula] at hxy
  | imp f₁ f₂ ihf₁ ihf₂ =>
    cases y with
    | imp f₁' f₂' =>
      simp only [on_formula, preformula.imp.injEq] at hxy
      exact congrArg₂ preformula.imp (ihf₁ hxy.1) (ihf₂ hxy.2)
    | _ => simp [on_formula] at hxy
  | all f ihf =>
    cases y with
    | all f' =>
      simp only [on_formula, preformula.all.injEq] at hxy;
      exact congrArg preformula.all (ihf hxy)
    | _ => simp [on_formula] at hxy

lemma on_bounded_term_inj (h : ϕ.is_injective) {n l} :
    Function.Injective
      (ϕ.on_bounded_term : bounded_preterm L n l → bounded_preterm L' n l) :=
  by
  intro x y hxy
  apply bounded_preterm.eq
  exact
    on_term_inj h (by simpa [on_bounded_term_fst] using congrArg bounded_preterm.fst hxy)

lemma on_bounded_formula_inj (h : ϕ.is_injective) {n l} :
    Function.Injective
      (ϕ.on_bounded_formula : bounded_preformula L n l → bounded_preformula L' n l) :=
  by
  intro x y hxy
  apply bounded_preformula.eq
  exact
    on_formula_inj h
      (by simpa [on_bounded_formula_fst] using congrArg bounded_preformula.fst hxy)

variable (ϕ)

/-! ## reduct — L-structure from L'-structure via ϕ -/


@[expose]
def reduct (S : Structure L') : Structure L :=
  ⟨S.carrier, fun {_n} f => S.fun_map (ϕ.on_function f), fun {_n} R =>
    S.rel_map (ϕ.on_relation R)⟩

notation:95 S "[[" ϕ "]]" => Lhom.reduct ϕ S

variable {ϕ}

@[simp]
lemma reduct_coe (S : Structure L') : (reduct ϕ S).carrier = S.carrier :=
  rfl

@[expose]
def reduct_id {S : Structure L'} : S.carrier → (ϕ.reduct S).carrier :=
  id

@[simp]
lemma reduct_term_eq {S : Structure L'} (hϕ : ϕ.is_injective) {n} (xs : DVec S n) :
    ∀ {l} (t : bounded_preterm L n l) (xs' : DVec S l),
      realize_bounded_term xs (ϕ.on_bounded_term t) xs' =
        @realize_bounded_term L (ϕ.reduct S) n xs l t xs'
  | _, bounded_preterm.bd_var k, xs' => rfl
  | _, bounded_preterm.bd_func f, xs' => rfl
  | _, bounded_preterm.bd_app t s, xs' =>
    by
    simp only [on_bounded_term, realize_bounded_term]
    rw [reduct_term_eq hϕ xs s DVec.nil]
    exact reduct_term_eq hϕ xs t _

lemma reduct_bounded_formula_iff {S : Structure L'} (hϕ : ϕ.is_injective) :
    ∀ {n l} (xs : DVec S n) (xs' : DVec S l) (f : bounded_preformula L n l),
      realize_bounded_formula xs (ϕ.on_bounded_formula f) xs' ↔
        @realize_bounded_formula L (ϕ.reduct S) n l xs f xs'
  | _, _, xs, xs', bd_falsum => Iff.rfl
  | _, _, xs, xs', bd_equal t₁ t₂ =>
    by
    simp only [on_bounded_formula, realize_bounded_formula,
      reduct_term_eq hϕ xs t₁ DVec.nil, reduct_term_eq hϕ xs t₂ DVec.nil]
    exact Iff.rfl
  | _, _, xs, xs', bd_rel _ => Iff.rfl
  | _, _, xs, xs', bd_apprel f t =>
    by
    simp only [on_bounded_formula, realize_bounded_formula,
      reduct_term_eq hϕ xs t DVec.nil]
    exact reduct_bounded_formula_iff hϕ xs (DVec.cons _ xs') f
  | _, _, xs, xs', bd_imp f₁ f₂ =>
    by
    simp only [on_bounded_formula, realize_bounded_formula]
    exact
      Iff.imp (reduct_bounded_formula_iff hϕ xs xs' f₁)
        (reduct_bounded_formula_iff hϕ xs xs' f₂)
  | _, _, xs, xs', bd_all f =>
    by
    simp only [on_bounded_formula, realize_bounded_formula]
    constructor
    · intro h x; exact (reduct_bounded_formula_iff hϕ (DVec.cons x xs) xs' f).mp (h x)
    · intro h x; exact (reduct_bounded_formula_iff hϕ (DVec.cons x xs) xs' f).mpr (h x)

lemma reduct_ssatisfied {S : Structure L'} {f : sentence L} (hϕ : ϕ.is_injective)
    (h : S ⊨ₘ ϕ.on_sentence f) : ϕ.reduct S ⊨ₘ f :=
  (reduct_bounded_formula_iff hϕ DVec.nil DVec.nil f).mp h

lemma reduct_ssatisfied' {S : Structure L'} {f : sentence L} (hϕ : ϕ.is_injective)
    (h : S ⊨ₘ ϕ.on_bounded_formula f) : ϕ.reduct S ⊨ₘ f :=
  (reduct_bounded_formula_iff hϕ DVec.nil DVec.nil f).mp h

theorem reduct_all_ssatisfied {S : Structure L'} {T : SentTheory L} (hϕ : ϕ.is_injective)
    (h : all_realize_sentence S (ϕ.on_sentence '' T)) :
    all_realize_sentence (reduct ϕ S) T := fun _f hf =>
  reduct_ssatisfied hϕ (h (Set.mem_image_of_mem _ hf))

lemma reduct_nonempty_of_nonempty {S : Structure L'} (H : Nonempty S.carrier) :
    Nonempty (ϕ.reduct S).carrier :=
  H

variable (ϕ)

@[reducible, expose]
def Theory_induced (T : SentTheory L) : SentTheory L' :=
  ϕ.on_sentence '' T

variable {ϕ}

lemma is_consistent_Theory_induced (hϕ : ϕ.is_injective) {T : SentTheory L}
    (hT : T.is_consistent) : (ϕ.Theory_induced T).is_consistent :=
  by
  intro H
  apply hT
  exact
    H.map
      (fun h => by
        have := reflect_sprf hϕ (f := bd_falsum) h
        exact this)

/-! ## is_consistent_extend (the main compactness argument) -/


lemma is_consistent_finite_witness_extension {T : SentTheory L} (hT : T.is_consistent)
    (hϕ : ϕ.is_injective) (h : bounded_formula L 1 → bounded_formula L 1)
    (hT' : ∀ (f : bounded_formula L 1), T ⊢ₛ' bd_ex (h f))
    (g : bounded_formula L 1 → L'.constants) (hg : Function.Injective g)
    (hg' : ∀ x, g x ∉ Set.range (ϕ.on_function (n := 0)))
    (s₀ : Finset (bounded_formula L 1)) :
    (ϕ.Theory_induced T ∪
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
          (↑s₀ : Set (bounded_formula L 1))).is_consistent :=
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
      (insert (subst0_bounded_formula (ϕ.on_bounded_formula (h ψ)) (bd_const (g ψ)))
            (ϕ.Theory_induced T ∪ (fun f =>
                  subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
                (↑s : Set (bounded_formula L 1)))).fst ⊢'
        ⊥' :=
      by
      have heq :
        (ϕ.Theory_induced T ∪
            insert (subst0_bounded_formula (ϕ.on_bounded_formula (h ψ)) (bd_const (g ψ)))
              ((fun f =>
                  subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
                (↑s : Set (bounded_formula L 1)))) =
          (insert (subst0_bounded_formula (ϕ.on_bounded_formula (h ψ)) (bd_const (g ψ)))
            (ϕ.Theory_induced T ∪ (fun f =>
                  subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
                (↑s : Set (bounded_formula L 1)))) :=
        by
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto
      rw [heq] at hs; exact hs
    let Γ :=
      ϕ.Theory_induced T ∪
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
          (↑s : Set (bounded_formula L 1))
    let ψ' : sentence L' :=
      subst0_bounded_formula (ϕ.on_bounded_formula (h ψ)) (bd_const (g ψ))
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
    let nhψ : bounded_formula L' 1 :=
      bd_not
        (ϕ.on_bounded_formula (h ψ))
          -- Re-cast hneg as a proof of subst0_bounded_formula nhψ
                -- (bd_const (g ψ))
    have hneg' : Γ ⊢ₛ' subst0_bounded_formula nhψ (bd_const (g ψ)) :=
      by
      change Γ.fst ⊢' (subst0_bounded_formula nhψ (bd_const (g ψ))).fst
      have hfst : (subst0_bounded_formula nhψ (bd_const (g ψ))).fst = ∼ψ'.fst :=
        by
        rw [subst0_bounded_formula_fst]
        change subst_formula nhψ.fst (bd_const (g ψ)).fst 0 = _
        change
          subst_formula ((ϕ.on_bounded_formula (h ψ)).fst ⟹ ⊥') (bd_const (g ψ)).fst 0 =
            ∼ψ'.fst
        change
          (subst_formula (ϕ.on_bounded_formula (h ψ)).fst (bd_const (g ψ)).fst 0) ⟹ ⊥' =
            ∼ψ'.fst
        change _ = ψ'.fst ⟹ ⊥'
        rw [show
            ψ'.fst = subst_formula (ϕ.on_bounded_formula (h ψ)).fst (bd_const (g ψ)).fst 0
            from subst0_bounded_formula_fst _ _]
      rw [hfst]; exact hneg
    let c : Language.symbols L' :=
      Sum.inl
        ⟨0, g ψ⟩
          -- Show c ∉ ⋃₀ (symbols_in_formula '' Γ.fst)
    have hΓ_no_c : c ∉ ⋃₀ (symbols_in_formula '' Γ.fst) :=
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
          symbols_in_formula_subst (ϕ.on_bounded_formula (h φ)).fst
            (@bd_const L' 0 (g φ)).fst 0
        have hcX' := hsubset hcX
        simp only [bd_const, bounded_preterm.fst, symbols_in_term, Set.mem_union] at hcX'
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
    have hnhψ_no_c : c ∉ symbols_in_formula nhψ.fst :=
      by
      simp only [nhψ, bd_not, bounded_preformula.fst, on_bounded_formula_fst,
        symbols_in_formula, Set.mem_union, Set.mem_empty_iff_false, or_false]
      exact ϕ.not_mem_function_in_formula_on_formula (hg' ψ) (h ψ).fst
    have hgen : Γ ⊢ₛ' bd_all nhψ :=
      hneg'.map
        (fun pf => sgeneralize_constant (g ψ) hΓ_no_c hnhψ_no_c pf)
          -- Now bd_all nhψ = bd_all (bd_not (ϕ.on_bounded_formula (h ψ)))
                -- = bd_not (bd_ex ...)
                -- which contradicts bd_ex (h ψ) being provable from T (lifted to
                -- ϕ.Theory_induced T ⊆ Γ)
                -- Get ϕ-image of hT' ψ
    have hT'_img : (ϕ.Theory_induced T) ⊢ₛ' ϕ.on_sentence (bd_ex (h ψ)) := by
      exact
        hT' ψ |>.map
          (fun pf => ϕ.on_sprf pf)
            -- ϕ.on_sentence (bd_ex (h ψ)) = bd_ex (ϕ.on_bounded_formula (h
                  -- ψ))
    have hex_eq : ϕ.on_sentence (bd_ex (h ψ)) = bd_ex (ϕ.on_bounded_formula (h ψ)) :=
      by
      apply bounded_preformula.eq
      simp only [on_sentence_fst, on_bounded_formula_fst, on_formula, bd_ex, bd_not,
        bounded_preformula.fst]
    rw [hex_eq] at hT'_img
    have hex : Γ ⊢ₛ' bd_ex (ϕ.on_bounded_formula (h ψ)) :=
      by
      have hsub : ϕ.Theory_induced T ⊆ Γ := Set.subset_union_left
      exact
        hT'_img.map
          (fun pf => weakening (Set.image_mono hsub) pf)
            -- bd_ex φ = bd_not (bd_all (bd_not φ)), so:
                  -- bd_ex (ϕ.on_bounded_formula (h ψ)) = bd_not (bd_all nhψ)
    have hex_def : bd_ex (ϕ.on_bounded_formula (h ψ)) = bd_not (bd_all nhψ) := rfl
    rw [hex_def] at hex
    change Γ.fst ⊢' (⊥' : formula L')
    have hex_fst : (bd_not (bd_all nhψ)).fst = (bd_all nhψ).fst ⟹ ⊥' := rfl
    change Γ.fst ⊢' (bd_not (bd_all nhψ)).fst at hex
    rw [hex_fst] at hex
    exact impE' _ hex hgen

lemma is_consistent_extend {T : SentTheory L} (hT : T.is_consistent) (hϕ : ϕ.is_injective)
    (h : bounded_formula L 1 → bounded_formula L 1)
    (hT' : ∀ (f : bounded_formula L 1), T ⊢ₛ' bd_ex (h f))
    (g : bounded_formula L 1 → L'.constants) (hg : Function.Injective g)
    (hg' : ∀ x, g x ∉ Set.range (ϕ.on_function (n := 0))) :
    (ϕ.Theory_induced T ∪
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
          Set.univ).is_consistent :=
  by
  have : DecidableEq (bounded_formula L 1) := fun x y => Classical.propDecidable _
  have : DecidableEq (sentence L') := fun x y =>
    Classical.propDecidable
      _
        -- Auxiliary lemma: consistency for any finite subset of
          -- witnesses.
  have lem := is_consistent_finite_witness_extension hT hϕ h hT' g hg hg'
  intro H
  have H' :
    (ϕ.Theory_induced T ∪
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
          Set.univ) ⊢ₛ'
      (bd_falsum : sentence L') :=
    H
  rcases theory_proof_compactness H' with
    ⟨T₀, h₀, hT₀⟩
      -- Decompose T₀ ⊆ T_ind ∪ image
  have hT₀' :
    (↑T₀ : Set (sentence L')) ⊆
      ϕ.Theory_induced T ∪
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
          Set.univ :=
    hT₀
  obtain ⟨t₀, s₀, hunion, ht₀, hs₀⟩ := Finset.subset_union_elim hT₀'
  have hs₀' :
    (↑s₀ : Set (sentence L')) ⊆
      (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
        Set.univ :=
    hs₀.trans
      (Set.sdiff_subset)
        -- Pull back s₀ through the image map
  rw [show
      ((fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
            Set.univ : Set (sentence L')) =
        (fun f => subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f))) ''
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
                subst0_bounded_formula (ϕ.on_bounded_formula (h f)) (bd_const (g f)))) :
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
