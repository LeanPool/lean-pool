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
/- Lean 4 port of src/henkin.lean — Part 1 (lines 1-450).
   Task 16a; Task 16b will continue from line 451. -/

public import LeanPool.NFWeakPartition.Flypitch4.Completion
public import LeanPool.NFWeakPartition.Flypitch4.LanguageExtension
public import LeanPool.NFWeakPartition.Flypitch4.Colimit

/-! NF weak partition development: Flypitch4.Henkin. -/


public section

namespace NFChoice

namespace Fol

open colimit omegaColimit

universe u

/-! ## Directed colimits of languages

These are fieldwise (and then indexwise) colimits of types.
For the Henkin construction, the directed type is always ℕ'
(carrier = ℕ : Type 0),
so we can use a single universe u for the language symbols.
-/


/-- A directed diagram of Languages at universe u indexed by ℕ -/
structure DirectedDiagramLanguage : Type (u + 1) where
  /-- The `obj` component of the corresponding first-order structure. -/
  obj : ℕ → Language.{u}
  /-- The `mor` component of the corresponding first-order structure. -/
  mor : ∀ {x y : ℕ}, x ≤ y → (obj x →ᴸ obj y)
  h_mor :
    ∀ {x y z : ℕ} {f1 : x ≤ y} {f2 : y ≤ z} {f3 : x ≤ z}, mor f3 = (mor f2).comp (mor f1)

/-- Restrict to n-ary function family -/
@[expose]
def diagramFunctions (F : DirectedDiagramLanguage.{u}) (n : ℕ) : DirectedDiagram ℕ'
    where
  obj x := (F.obj x).functions n
  mor h := (F.mor h).onFunction
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact
      congr_fun
        (show (F.mor f3).onFunction = (F.mor f2).onFunction ∘ (F.mor f1).onFunction
          from by rw [key])
        a

/-- Restrict to n-ary relation family -/
@[expose]
def diagramRelations (F : DirectedDiagramLanguage.{u}) (n : ℕ) : DirectedDiagram ℕ'
    where
  obj x := (F.obj x).relations n
  mor h := (F.mor h).onRelation
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact
      congr_fun
        (show (F.mor f3).onRelation = (F.mor f2).onRelation ∘ (F.mor f1).onRelation
          from by rw [key])
        a

/-- The colimit language -/
@[expose]
def colimitLanguage (F : DirectedDiagramLanguage.{u}) : Language.{u} :=
  ⟨fun n => LimitCarrier (diagramFunctions F n), fun n =>
    LimitCarrier (diagramRelations F n)⟩

/-- Canonical map from stage i into the colimit language -/
@[expose]
def canonicalMapLanguage {F : DirectedDiagramLanguage.{u}} (i : ℕ) :
    F.obj i →ᴸ colimitLanguage F :=
  ⟨fun {n} => @canonicalMap _ (diagramFunctions F n) i, fun {n} =>
    @canonicalMap _ (diagramRelations F n) i⟩

/-- A cocone over a directed diagram of languages -/
structure CoconeLanguage (F : DirectedDiagramLanguage.{u}) where
  /-- The `vertex` component of the corresponding first-order structure. -/
  vertex : Language.{u}
  /-- The `map` component of the corresponding first-order structure. -/
  map : ∀ i : ℕ, F.obj i →ᴸ vertex
  h_compat : ∀ {i j : ℕ}, ∀ h : i ≤ j, map i = (map j).comp (F.mor h)

/-- The colimit is itself a cocone -/
@[expose]
def coconeOfColimitLanguage (F : DirectedDiagramLanguage.{u}) : CoconeLanguage F
    where
  vertex := colimitLanguage F
  map := canonicalMapLanguage
  h_compat := by
    intro i j H
    apply Lhom.Lhom_funext
    · funext n; funext f
      simp only [canonicalMapLanguage, Function.comp]
      exact congr_fun ((coconeOfColimit (diagramFunctions F n)).h_compat H) f
    · funext n; funext R
      simp only [canonicalMapLanguage, Function.comp]
      exact congr_fun ((coconeOfColimit (diagramRelations F n)).h_compat H) R

/-! ## The Henkin construction
-/


/-- Inductive type of function symbols for one Henkin step.
    `inc` embeds L-symbols; `wit` introduces witness constants. -/
inductive HenkinLanguageFunctions (L : Language.{u}) : ℕ → Type u
  | inc : ∀ {n}, L.functions n → HenkinLanguageFunctions L n
  | wit : boundedFormula L 1 → HenkinLanguageFunctions L 0

open HenkinLanguageFunctions

/-- One Henkin step on languages -/
@[reducible, expose]
def henkinLanguageStep (L : Language.{u}) : Language.{u} :=
  ⟨HenkinLanguageFunctions L, L.relations⟩

/-- Flypitch construction `wit'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def wit' {L : Language.{u}} : boundedFormula L 1 → (henkinLanguageStep L).constants :=
  wit

/-- Flypitch construction `henkin_language_inclusion`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def henkinLanguageInclusion {L : Language.{u}} : L →ᴸ henkinLanguageStep L :=
  ⟨fun {_} f => inc f, fun {_} => id⟩

lemma henkin_language_inclusion_inj {L : Language.{u}} :
    Lhom.IsInjective (@henkinLanguageInclusion L) :=
  ⟨fun {_} _ _ H => HenkinLanguageFunctions.inc.inj H, fun {_} _ _ H => H⟩

/-! ## wit_property and henkin_theory_step -/


/-- The witnessing sentence: (∃ᵇf) → f[c/0] -/
@[reducible, expose]
def witProperty {L : Language.{u}} (f : boundedFormula L 1) (c : L.constants) :
    sentence L :=
  bd_imp (bdEx f) (subst0BoundedFormula f (bdConst c))

/-- One Henkin step on theories -/
@[expose]
def henkinTheoryStep {L : Language.{u}} (T : SentTheory L) :
    SentTheory (henkinLanguageStep L) :=
  henkinLanguageInclusion.TheoryInduced T ∪
    (fun f : boundedFormula L 1 =>
        witProperty (henkinLanguageInclusion.onBoundedFormula f) (wit' f)) ''
      Set.univ

/-- Auxiliary tautology: `T ⊢ₛ' ∃ x, (∃ y, f y) → f x`. -/
private lemma henkin_witness_tautology {L : Language.{u}} (T : SentTheory L)
    (f : boundedFormula L 1) : T ⊢ₛ' bdEx (bd_imp (bdEx f).cast1 f) :=
  by
  change T.fst ⊢' (bdEx (bd_imp (bdEx f).cast1 f)).fst
  refine
    ⟨?_⟩
      -- Goal: T.fst ⊢ (bd_ex (bd_imp (bd_ex f).cast1 f)).fst
        -- = ∃' ((∃' f.fst) ⟹ f.fst)  (since cast1.fst = .fst)
  change T.fst ⊢ ∃'((bdEx f).cast1.fst ⟹ f.fst)
  apply prf.falsumE
  apply prf.impE (∃'f.fst)
  · -- Goal: insert ¬∃' ... ⊢ (∃' f.fst) ⟹ ⊥'
    apply prf.impI
    apply prf.impE _ axm2
    apply exE axm1
    apply exI &0
    rw [lift_subst_formula_cancel]
      -- Now we need: ⊢ (bd_ex f).cast1.fst ⟹ f.fst
          -- (bd_ex f).cast1.fst = (bd_ex f).fst, so this is (∃' f.fst) ⟹
          -- f.fst
    rw [BoundedPreformula.cast1_fst]
    apply prf.impI
    exact axm2
  · -- Goal: insert (∼∃' ...) T.fst ⊢ ∃' f.fst
    apply prf.falsumE
    apply prf.impE _ axm2
    apply
      exI
        &0
            -- Goal: ... ⊢ ((bd_ex f).cast1.fst ⟹ f.fst)[&0 // 0]f
                -- = (bd_ex f).cast1.fst[&0/0] ⟹ f.fst[&0/0]
    apply prf.impI
    apply exfalso
    apply prf.impE _ axm2
    show _ ⊢ ∃'f.fst
    have key : (bdEx f).cast1.fst [&0 // 0]f = ∃'f.fst := by
      rw [BoundedPreformula.cast1_fst, subst_sentence_irrel]; rfl
    rw [← key]
    exact axm1

/-- The Henkin extension of a consistent theory is consistent -/
lemma is_consistent_henkin_theory_step {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : (henkinTheoryStep T).isConsistent := by
  -- Apply is_consistent_extend with h := λ f, (∃' f).cast1 ⟹ f and
    -- g := wit'.
  have hwit_inj : Function.Injective (@wit' L) :=
    by
    intro f f' h
    exact HenkinLanguageFunctions.wit.inj h
  have hwit_not_in :
    ∀ x : boundedFormula L 1,
      wit' x ∉
        Set.range
          ((@henkinLanguageInclusion L).onFunction :
            L.functions 0 → (henkinLanguageStep L).functions 0) :=
    by
    intro x
      ⟨g, hg⟩
        -- hg : henkin_language_inclusion.on_function g = wit' x
            -- on_function g = inc g, wit' x = wit x — different constructors
    simp [henkinLanguageInclusion, wit'] at hg
  have hext :=
    Lhom.is_consistent_extend hT henkin_language_inclusion_inj
      (fun f => bd_imp (bdEx f).cast1 f) (fun f => henkin_witness_tautology T f) wit'
      hwit_inj hwit_not_in
  have hset :
    henkinTheoryStep T =
      (@henkinLanguageInclusion L).TheoryInduced T ∪
        (fun f => subst0BoundedFormula ((@henkinLanguageInclusion L).onBoundedFormula
                (bd_imp (bdEx f).cast1 f)) (bdConst (wit' f))) ''
          Set.univ :=
    by
    show henkinTheoryStep T = _
    unfold henkinTheoryStep
    congr 1
    apply Set.image_congr'
    intro f
    apply BoundedPreformula.eq
    simp only [witProperty, subst0_bounded_formula_fst, Lhom.onBoundedFormula,
      BoundedPreformula.fst_bd_imp, BoundedPreformula.fst_bd_ex, substFormula]
      -- Now the goal is:
          -- ∃' (incl.on_formula f.fst) ⟹ (incl.on_formula f.fst)[c/0] =
          -- subst (incl.on_formula (∃' f.fst)) c 0 ⟹ (incl.on_formula
          -- f.fst)[c/0]
          -- The RHS first arg equals the LHS first arg because
          -- (incl.on_formula (∃' f.fst))
          -- is a sentence (closed bounded_formula).
    congr 1
      -- Goal: ∃' (incl.on_bf f).fst = (incl.on_bf (cast1 (bd_ex
          -- f))).fst [c // 0]f
          -- RHS: (incl.on_bf (cast1 (bd_ex f))).fst = (cast1 (bd_ex
          -- f)).cast1 ... no wait
          -- (incl.on_bf cast1(X)).fst = on_formula (cast1 X).fst =
          -- on_formula X.fst
          -- So RHS = on_formula (bd_ex f).fst [c//0]f = on_formula (∃'
          -- f.fst) [c//0]f
          --       = (∃' (on_formula f.fst)) [c//0]f
          -- And subst sentence_irrel gives ∃' (on_formula f.fst).
    have hRHS :
      ((@henkinLanguageInclusion L).onBoundedFormula
            (BoundedPreformula.cast1 (bdEx f))).fst =
        ∃'((@henkinLanguageInclusion L).onBoundedFormula f).fst :=
      by
      simp only [Lhom.on_bounded_formula_fst, BoundedPreformula.cast1_fst,
        BoundedPreformula.fst_bd_ex]
      rfl
    rw [hRHS]
      -- Goal: ∃' (incl.on_bf f).fst = (∃' (incl.on_bf f).fst) [c//0]f
          -- ∃' X is closed if X is bounded_formula L 1, so use
          -- subst_sentence_irrel via casting
          -- to a sentence
    have hSent :
      (bdEx ((@henkinLanguageInclusion L).onBoundedFormula f) :
            sentence (henkinLanguageStep L)).fst =
        ∃'((@henkinLanguageInclusion L).onBoundedFormula f).fst :=
      by simp only [BoundedPreformula.fst_bd_ex]
    rw [← hSent, subst_sentence_irrel]
  rw [hset]
  exact hext

/-! ## Henkin language chain -/


/-- Objects of the Henkin language chain -/
@[reducible, expose]
def henkinLanguageChainObjects {L : Language.{u}} : ℕ → Language.{u}
  | 0 => L
  | (n + 1) => henkinLanguageStep (@henkinLanguageChainObjects L n)

lemma obvious {L : Language.{u}} (i : ℕ) :
    HenkinLanguageFunctions (@henkinLanguageChainObjects L i) 0 =
      (@henkinLanguageChainObjects L (i + 1)).constants :=
  by simp only [Language.constants]

/-- Transition maps of the Henkin language chain -/
@[expose]
def henkinLanguageChainMaps (L : Language.{u}) :
    ∀ (x y : ℕ),
      x ≤ y →
        Lhom (@henkinLanguageChainObjects L x) (@henkinLanguageChainObjects L y)
  | _, 0, H => Nat.eq_zero_of_le_zero H ▸ Lhom.id _
  | x, y + 1, H =>
    if hx : x = y + 1 then hx ▸ Lhom.id _
    else
      henkinLanguageInclusion.comp
        (henkinLanguageChainMaps L x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hx)))
          -- Private helper: the zero-zero case gives identity


-- Private helper: the zero-zero case gives identity
private lemma hcm_zero_zero (L : Language.{u}) (H : 0 ≤ 0) :
    henkinLanguageChainMaps L 0 0 H = Lhom.id L :=
  rfl

-- Private helper: the self case gives identity
private lemma hcm_self (L : Language.{u}) (k : ℕ) (H : k ≤ k) :
    henkinLanguageChainMaps L k k H = Lhom.id (@henkinLanguageChainObjects L k) :=
  by
  cases k with
  | zero => exact hcm_zero_zero L H
  | succ n =>
    simp only [henkinLanguageChainMaps]
    rfl
      -- Private helper: the non-equal successor case gives a
      -- composition


-- Private helper: the non-equal successor case gives a
-- composition
private lemma hcm_succ_ne (L : Language.{u}) (x y : ℕ) (H : x ≤ y + 1) (hne : x ≠ y + 1) :
    henkinLanguageChainMaps L x (y + 1) H =
      henkinLanguageInclusion.comp
        (henkinLanguageChainMaps L x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hne))) :=
  by simp only [henkinLanguageChainMaps, dite_eq_right hne]

lemma henkin_language_chain_maps_inj (L : Language.{u}) (i j : ℕ) (h : i ≤ j) :
    Lhom.IsInjective (henkinLanguageChainMaps L i j h) := by
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.eq_zero_of_le_zero h; subst h0
    rw [hcm_zero_zero]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
  | succ n ih =>
    by_cases hx : i = n + 1
    · subst hx
      rw [hcm_self]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
    · have hle : i ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      rw [hcm_succ_ne L i n h hx]
      have ih' := ih hle
      exact
        ⟨fun {m} x y H => ih'.onFunction (henkin_language_inclusion_inj.onFunction H),
          fun {m} x y H => ih'.onRelation (henkin_language_inclusion_inj.onRelation H)⟩

/-- Functoriality of the Henkin language chain maps -/
lemma henkin_language_chain_maps_functorial (L : Language.{u}) :
    ∀ (x y z : ℕ) (f1 : x ≤ y) (f2 : y ≤ z) (f3 : x ≤ z),
      henkinLanguageChainMaps L x z f3 =
        (henkinLanguageChainMaps L y z f2).comp
          (henkinLanguageChainMaps L x y f1) :=
  by
  intro x y z f1 f2 f3
  induction z with
  | zero =>
    have hy0 : y = 0 := Nat.eq_zero_of_le_zero f2
    have hx0 : x = 0 := Nat.le_antisymm (hy0 ▸ f1) (Nat.zero_le _)
    subst hx0; subst hy0
    simp [hcm_zero_zero, Lhom.id_is_left_identity]
  | succ n ih =>
    by_cases hy : y = n + 1
    · subst hy
      by_cases hx : x = n + 1
      · subst hx; simp [hcm_self, Lhom.id_is_left_identity]
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_self, Lhom.id_is_left_identity]
    · have hyn : y ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f2 hy)
      by_cases hx : x = n + 1
      · exfalso; exact absurd (Nat.le_trans f1 hyn) (hx ▸ Nat.not_succ_le_self n)
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_succ_ne L y n f2 hy, ih hyn hxn]
        apply Lhom.Lhom_funext <;> (funext n; simp [Function.comp_assoc])

/-- The Henkin language chain as a directed diagram of languages
-/
@[reducible, expose]
def henkinLanguageChain {L : Language.{u}} : DirectedDiagramLanguage.{u}
    where
  obj := @henkinLanguageChainObjects L
  mor := fun {x y} H => henkinLanguageChainMaps L x y H
  h_mor := fun {x y z f1 f2 f3} => henkin_language_chain_maps_functorial L x y z f1 f2 f3

lemma id_of_self_map (L : Language.{u}) (k : ℕ) :
    henkinLanguageChainMaps L k k (Nat.le_refl k) =
      Lhom.id (@henkinLanguageChainObjects L k) :=
  hcm_self L k (Nat.le_refl k)

lemma henkin_language_inclusion_chain_map {i : ℕ} {L : Language.{u}} :
    @henkinLanguageInclusion (@henkinLanguageChainObjects L i) =
      henkinLanguageChainMaps L i (i + 1) (Nat.le_succ i) :=
  by
  rw [hcm_succ_ne L i i (Nat.le_succ i) (Nat.ne_of_lt (Nat.lt_succ_self i))]
  rw [hcm_self L i (Nat.le_refl i)]
  rw [Lhom.id_is_right_identity]

/-! ## The limit language L_∞ -/


/-- The colimit of the Henkin language chain -/
@[reducible, expose]
def LInfty (L : Language.{u}) : Language.{u} :=
  colimitLanguage (@henkinLanguageChain L)

/-- Canonical inclusion L_m → L_∞ -/
@[reducible, expose]
def henkinLanguageCanonicalMap {L : Language.{u}} (m : ℕ) :
    (@henkinLanguageChain L).obj m →ᴸ LInfty L :=
  canonicalMapLanguage m

@[simp]
lemma henkin_language_canonical_map_inj {L : Language.{u}} (m : ℕ) :
    Lhom.IsInjective (@henkinLanguageCanonicalMap L m) :=
  by
  constructor
  · intro n
    simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).onFunction
  · intro n
    simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).onRelation

/-! ## Directed diagrams of terms and formulas -/


/-- Chain of preterms at level l -/
@[reducible, expose]
def henkinTermChain {L : Language.{u}} (l : ℕ) : DirectedDiagram ℕ'
    where
  obj k := preterm (@henkinLanguageChainObjects L k) l
  mor H := Lhom.onTerm (henkinLanguageChainMaps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    simp only [Lhom.comp_on_term, hcomp]

/-- Chain of preformulas at level l -/
@[reducible, expose]
def henkinFormulaChain {L : Language.{u}} (l : ℕ) : DirectedDiagram ℕ'
    where
  obj k := @preformula (@henkinLanguageChainObjects L k) l
  mor H := Lhom.onFormula (henkinLanguageChainMaps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    funext f
    simp [Lhom.comp_on_formula, hcomp]

/-- Chain of bounded preterms at bound n, level l -/
@[reducible, expose]
def henkinBoundedTermChain {L : Language.{u}} (n l : ℕ) : DirectedDiagram ℕ'
    where
  obj k := BoundedPreterm (@henkinLanguageChainObjects L k) n l
  mor H := Lhom.onBoundedTerm (henkinLanguageChainMaps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_term]

/-- Flypitch construction `henkin_bounded_term_chain'`, retained by the first-order soundness
and completeness development.
-/
@[reducible, expose]
def henkinBoundedTermChain' {L : Language.{u}} : DirectedDiagram ℕ' :=
  @henkinBoundedTermChain L 1 0

/-- Chain of bounded preformulas at bound n, level l -/
@[reducible, expose]
def henkinBoundedFormulaChain {L : Language.{u}} (n l : ℕ) : DirectedDiagram ℕ'
    where
  obj k := BoundedPreformula (@henkinLanguageChainObjects L k) n l
  mor H := Lhom.onBoundedFormula (henkinLanguageChainMaps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_formula]

/-- Flypitch construction `henkin_bounded_formula_chain'`, retained by the first-order soundness
and completeness development.
-/
@[reducible, expose]
def henkinBoundedFormulaChain' {L : Language.{u}} : DirectedDiagram ℕ' :=
  @henkinBoundedFormulaChain L 1 0

/-! ## Cocones with vertex L_∞ -/


/-- L_∞ is a cocone over the diagram of languages -/
@[expose]
def coconeOfLInfty {L : Language.{u}} : CoconeLanguage (@henkinLanguageChain L) :=
  coconeOfColimitLanguage _

/-- Cocone over the preterm chain with vertex preterm (L_∞ L) l
-/
@[expose]
def coconeOfTermLInfty {L : Language.{u}} (l : ℕ) : cocone (@henkinTermChain L l)
    where
  vertex := preterm (LInfty L) l
  map i := Lhom.onTerm (henkinLanguageCanonicalMap i)
  h_compat := by
    intro i j H
    change
      (henkinLanguageCanonicalMap i).onTerm =
        (henkinLanguageCanonicalMap j).onTerm ∘
          (henkinLanguageChainMaps L i j H).onTerm
    rw [← Lhom.comp_on_term]
    exact
      congrArg (fun ϕ : @henkinLanguageChainObjects L i →ᴸ LInfty L => ϕ.onTerm)
        ((@coconeOfLInfty L).h_compat H)

/-- Cocone over the preformula chain with vertex @preformula (L_∞
L) l -/
@[expose]
def coconeOfFormulaLInfty {L : Language.{u}} (l : ℕ) :
    cocone (@henkinFormulaChain L l)
    where
  vertex := @preformula (LInfty L) l
  map i := Lhom.onFormula (henkinLanguageCanonicalMap i)
  h_compat := by
    intro i j H
    have hc :
      henkinLanguageCanonicalMap i =
        (henkinLanguageCanonicalMap j).comp (henkinLanguageChainMaps L i j H) :=
      (@coconeOfLInfty L).h_compat H
    funext f
    simp only [Function.comp]
    have :=
      congr_arg
        (fun ϕ : @henkinLanguageChainObjects L i →ᴸ LInfty L => ϕ.onFormula f) hc
    simpa only [Lhom.comp_on_formula (henkinLanguageCanonicalMap j)
          (henkinLanguageChainMaps L i j H),
      Function.comp_apply] using this

/-- Cocone over the bounded term chain with vertex
bounded_preterm (L_∞ L) n l -/
@[expose]
def coconeOfBoundedTermLInfty {L : Language.{u}} (n l : ℕ) :
    cocone (@henkinBoundedTermChain L n l)
    where
  vertex := BoundedPreterm (LInfty L) n l
  map i := Lhom.onBoundedTerm (henkinLanguageCanonicalMap i)
  h_compat := by
    intro i j H
    have hc :
      henkinLanguageCanonicalMap i =
        (henkinLanguageCanonicalMap j).comp (henkinLanguageChainMaps L i j H) :=
      (@coconeOfLInfty L).h_compat H
    funext t
    simp only [Function.comp]
    have :=
      congr_arg
        (fun ϕ : @henkinLanguageChainObjects L i →ᴸ LInfty L => ϕ.onBoundedTerm t)
        hc
    simpa only [Lhom.comp_on_bounded_term (henkinLanguageCanonicalMap j)
          (henkinLanguageChainMaps L i j H),
      Function.comp_apply] using this

/-! ## Cocone over the bounded formula chain (Task 16b,
src/henkin.lean:452-499) -/


/-- Cocone over the bounded preformula chain with vertex
bounded_preformula (L_∞ L) n l -/
@[expose]
def coconeOfBoundedFormulaLInfty {L : Language.{u}} (n l : ℕ) :
    cocone (@henkinBoundedFormulaChain L n l)
    where
  vertex := BoundedPreformula (LInfty L) n l
  map i := Lhom.onBoundedFormula (henkinLanguageCanonicalMap i)
  h_compat := by
    intro i j H
    have hc :
      henkinLanguageCanonicalMap i =
        (henkinLanguageCanonicalMap j).comp (henkinLanguageChainMaps L i j H) :=
      (@coconeOfLInfty L).h_compat H
    funext f
    simp only [Function.comp]
    have :=
      congr_arg
        (fun ϕ : @henkinLanguageChainObjects L i →ᴸ LInfty L => ϕ.onBoundedFormula f)
        hc
    simpa only [Lhom.comp_on_bounded_formula (henkinLanguageCanonicalMap j)
          (henkinLanguageChainMaps L i j H),
      Function.comp_apply] using this

/-- bounded_formula (L_∞ L) 1 is naturally a cocone over the
diagram of bounded_formulas -/
@[expose]
def coconeOfBoundedFormula'LInfty {L : Language.{u}} :
    cocone (@henkinBoundedFormulaChain' L)
    where
  vertex := boundedFormula (LInfty L) 1
  map i := Lhom.onBoundedFormula (henkinLanguageCanonicalMap i)
  h_compat := by
    intro i j H
    have hc :
      henkinLanguageCanonicalMap i =
        (henkinLanguageCanonicalMap j).comp (henkinLanguageChainMaps L i j H) :=
      (@coconeOfLInfty L).h_compat H
    funext f
    simp only [Function.comp]
    have :=
      congr_arg
        (fun ϕ : @henkinLanguageChainObjects L i →ᴸ LInfty L => ϕ.onBoundedFormula f)
        hc
    simpa only [Lhom.comp_on_bounded_formula (henkinLanguageCanonicalMap j)
          (henkinLanguageChainMaps L i j H),
      Function.comp_apply] using this

/-! ## Comparison maps (universal maps from colimits to L_∞) -/


/-- Flypitch construction `term_comparison`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def term_comparison {L : Language.{u}} (l) :
    LimitCarrier (@henkinTermChain L l) → preterm (LInfty L) l :=
  universalMap (V := coconeOfTermLInfty l)

/-- Flypitch construction `formula_comparison`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def formulaComparison {L : Language.{u}} (l) :
    LimitCarrier (@henkinFormulaChain L l) → @preformula (LInfty L) l :=
  universalMap (V := coconeOfFormulaLInfty l)

/-- Flypitch construction `bounded_term_comparison`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def boundedTermComparison {L : Language.{u}} (n l) :
    LimitCarrier (@henkinBoundedTermChain L n l) → BoundedPreterm (LInfty L) n l :=
  universalMap (V := coconeOfBoundedTermLInfty n l)

/-- Flypitch construction `bounded_term'_comparison`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def boundedTerm'Comparison {L : Language.{u}} :
    LimitCarrier (@henkinBoundedTermChain' L) → boundedTerm (LInfty L) 1 :=
  @boundedTermComparison L 1 0

/-- Flypitch construction `bounded_formula_comparison`, retained by the first-order soundness
and completeness development.
-/
@[expose]
def boundedFormulaComparison {L : Language.{u}} (n l) :
    LimitCarrier (@henkinBoundedFormulaChain L n l) →
      BoundedPreformula (LInfty L) n l :=
  universalMap (V := coconeOfBoundedFormulaLInfty n l)

/-- Flypitch construction `bounded_formula'_comparison`, retained by the first-order soundness
and completeness development.
-/
@[reducible, expose]
def boundedFormula'Comparison {L : Language.{u}} :
    LimitCarrier (@henkinBoundedFormulaChain' L) → boundedFormula (LInfty L) 1 :=
  @boundedFormulaComparison L 1 0

/-! ## Bijectivity of comparison maps (src/henkin.lean:508-655)
-/
-- These are complex structural induction arguments; sorried
-- pending full port.


-- These are complex structural induction arguments; sorried
-- pending full port.

/-- Auxiliary: surjectivity of term_comparison -/
private lemma term_comparison_surj {L : Language.{u}} :
    ∀ {l} (t : preterm (LInfty L) l),
      ∃ x : LimitCarrier (@henkinTermChain L l), term_comparison l x = t :=
  by
  intro l t
  induction t with
  | var k =>
    exact
      ⟨canonicalMap 0 (preterm.var k), by
        simp [term_comparison, universal_map_property, coconeOfTermLInfty]⟩
  | func ff =>
    obtain ⟨⟨i, x⟩, Hx⟩ := germRep ff
    exact
      ⟨canonicalMap i (preterm.func x),
        by
        simp only [term_comparison, universal_map_property, coconeOfTermLInfty,
          Lhom.onTerm]
        simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
        rw [← Hx]; rfl⟩
  | app t s iht ihs =>
    obtain ⟨qt, Hqt⟩ := iht
    obtain ⟨qs, Hqs⟩ := ihs
    obtain ⟨⟨i, xt⟩, Hit⟩ := germRep qt
    obtain ⟨⟨j, xs⟩, Hjs⟩ := germRep qs
    have Hqt' : term_comparison _ (canonicalMap i xt) = t := by
      have : canonicalMap i xt = qt := Hit.symm ▸ rfl; rw [this]; exact Hqt
    have Hqs' : term_comparison 0 (canonicalMap j xs) = s := by
      have : canonicalMap j xs = qs := Hjs.symm ▸ rfl; rw [this]; exact Hqs
    have keyt : term_comparison _ (canonicalMap (i + j) (pushToSumR xt j)) = t := by
      rw [← same_fiber_as_push_to_r]; exact Hqt'
    have keys : term_comparison 0 (canonicalMap (i + j) (pushToSumL xs i)) = s := by
      rw [← same_fiber_as_push_to_l]; exact Hqs'
    refine
      ⟨canonicalMap (i + j) (preterm.app (pushToSumR xt j) (pushToSumL xs i)), ?_⟩
    simp only [term_comparison, universal_map_property, coconeOfTermLInfty,
      Lhom.onTerm]
    exact congrArg₂ preterm.app keyt keys

lemma term_comparison_bijective {L : Language.{u}} (l) :
    Function.Bijective (@term_comparison L l) :=
  ⟨universal_map_inj_of_components_inj
      (fun m => Lhom.on_term_inj (henkin_language_canonical_map_inj m)),
    term_comparison_surj⟩

/-- Auxiliary: surjectivity of formula_comparison -/
private lemma formula_comparison_surj {L : Language.{u}} :
    ∀ {l} (f : @preformula (LInfty L) l),
      ∃ x : LimitCarrier (@henkinFormulaChain L l), formulaComparison l x = f :=
  by
  intro l f
  induction f with
  | falsum =>
    exact
      ⟨canonicalMap 0 preformula.falsum, by
        simp [formulaComparison, universal_map_property, coconeOfFormulaLInfty]⟩
  | equal t₁
    t₂ =>
    obtain ⟨qt₁, Hqt₁⟩ := (term_comparison_bijective 0).right t₁
    obtain ⟨qt₂, Hqt₂⟩ := (term_comparison_bijective 0).right t₂
    obtain ⟨⟨i, xt₁⟩, Hit₁⟩ := germRep qt₁
    obtain ⟨⟨j, xt₂⟩, Hit₂⟩ := germRep qt₂
    have Hbt₁ : term_comparison 0 (canonicalMap i xt₁) = t₁ := by
      have : canonicalMap i xt₁ = qt₁ := Hit₁.symm ▸ rfl; rw [this]; exact Hqt₁
    have Hbt₂ : term_comparison 0 (canonicalMap j xt₂) = t₂ := by
      have : canonicalMap j xt₂ = qt₂ := Hit₂.symm ▸ rfl; rw [this]; exact Hqt₂
    have key₁ : term_comparison 0 (canonicalMap (i + j) (pushToSumR xt₁ j)) = t₁ := by
      rw [← same_fiber_as_push_to_r]; exact Hbt₁
    have key₂ : term_comparison 0 (canonicalMap (i + j) (pushToSumL xt₂ i)) = t₂ := by
      rw [← same_fiber_as_push_to_l]; exact Hbt₂
    refine
      ⟨canonicalMap (i + j)
          (preformula.equal (pushToSumR xt₁ j) (pushToSumL xt₂ i)),
        ?_⟩
    simp only [formulaComparison, universal_map_property, coconeOfFormulaLInfty,
      Lhom.onFormula]
    exact congrArg₂ preformula.equal key₁ key₂
  | rel R =>
    obtain ⟨⟨i, x⟩, Hx⟩ := germRep R
    exact
      ⟨canonicalMap i (preformula.rel x),
        by
        simp only [formulaComparison, universal_map_property, coconeOfFormulaLInfty,
          Lhom.onFormula]
        simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
        rw [← Hx]; rfl⟩
  | apprel f t ihf =>
    obtain ⟨qf, Hqf⟩ := ihf
    obtain ⟨qt, Hqt⟩ := (term_comparison_bijective 0).right t
    obtain ⟨⟨i, xf⟩, Hif⟩ := germRep qf
    obtain ⟨⟨j, xt⟩, Hjt⟩ := germRep qt
    have Hbf : formulaComparison _ (canonicalMap i xf) = f := by
      have : canonicalMap i xf = qf := Hif.symm ▸ rfl; rw [this]; exact Hqf
    have Hbt : term_comparison 0 (canonicalMap j xt) = t := by
      have : canonicalMap j xt = qt := Hjt.symm ▸ rfl; rw [this]; exact Hqt
    have keyf : formulaComparison _ (canonicalMap (i + j) (pushToSumR xf j)) = f :=
      by rw [← same_fiber_as_push_to_r]; exact Hbf
    have keyt : term_comparison 0 (canonicalMap (i + j) (pushToSumL xt i)) = t := by
      rw [← same_fiber_as_push_to_l]; exact Hbt
    refine
      ⟨canonicalMap (i + j)
          (preformula.apprel (pushToSumR xf j) (pushToSumL xt i)),
        ?_⟩
    simp only [formulaComparison, universal_map_property, coconeOfFormulaLInfty,
      Lhom.onFormula]
    exact congrArg₂ preformula.apprel keyf keyt
  | imp f₁ f₂ ihf₁ ihf₂ =>
    obtain ⟨qf₁, Hqf₁⟩ := ihf₁
    obtain ⟨qf₂, Hqf₂⟩ := ihf₂
    obtain ⟨⟨i, xf₁⟩, Hif₁⟩ := germRep qf₁
    obtain ⟨⟨j, xf₂⟩, Hjf₂⟩ := germRep qf₂
    have Hbf₁ : formulaComparison _ (canonicalMap i xf₁) = f₁ := by
      have : canonicalMap i xf₁ = qf₁ := Hif₁.symm ▸ rfl; rw [this]; exact Hqf₁
    have Hbf₂ : formulaComparison _ (canonicalMap j xf₂) = f₂ := by
      have : canonicalMap j xf₂ = qf₂ := Hjf₂.symm ▸ rfl; rw [this]; exact Hqf₂
    have keyf₁ :
      formulaComparison _ (canonicalMap (i + j) (pushToSumR xf₁ j)) = f₁ := by
      rw [← same_fiber_as_push_to_r]; exact Hbf₁
    have keyf₂ :
      formulaComparison _ (canonicalMap (i + j) (pushToSumL xf₂ i)) = f₂ := by
      rw [← same_fiber_as_push_to_l]; exact Hbf₂
    refine
      ⟨canonicalMap (i + j) (preformula.imp (pushToSumR xf₁ j) (pushToSumL xf₂ i)),
        ?_⟩
    simp only [formulaComparison, universal_map_property, coconeOfFormulaLInfty,
      Lhom.onFormula]
    exact congrArg₂ preformula.imp keyf₁ keyf₂
  | all f ihf =>
    obtain ⟨qf, Hqf⟩ := ihf
    obtain ⟨⟨i, xf⟩, Hif⟩ := germRep qf
    have Hbf : formulaComparison _ (canonicalMap i xf) = f := by
      have : canonicalMap i xf = qf := Hif.symm ▸ rfl; rw [this]; exact Hqf
    refine ⟨canonicalMap i (preformula.all xf), ?_⟩
    simp only [formulaComparison, universal_map_property, coconeOfFormulaLInfty,
      Lhom.onFormula]
    exact congrArg preformula.all Hbf

lemma formula_comparison_bijective {L : Language.{u}} (l) :
    Function.Bijective (@formulaComparison L l) :=
  ⟨universal_map_inj_of_components_inj
      (fun m => Lhom.on_formula_inj (henkin_language_canonical_map_inj m)),
    formula_comparison_surj⟩

/-- Auxiliary: surjectivity of bounded_term_comparison by
structural induction -/
private lemma bounded_term_comparison_surj {L : Language.{u}} :
    ∀ {n l} (t : BoundedPreterm (LInfty L) n l),
      ∃ x : LimitCarrier (@henkinBoundedTermChain L n l),
        boundedTermComparison n l x = t :=
  by
  intro n l t
  induction t with
  | bd_var k =>
    exact
      ⟨canonicalMap 0 (bd_var k), by
        apply BoundedPreterm.eq
        simp [boundedTermComparison, universal_map_property,
          coconeOfBoundedTermLInfty]⟩
  | bd_func ff =>
    obtain ⟨⟨i, x⟩, Hx⟩ := germRep ff
    exact
      ⟨canonicalMap i (bd_func x),
        by
        apply BoundedPreterm.eq
        simp only [boundedTermComparison, universal_map_property,
          coconeOfBoundedTermLInfty, Lhom.onBoundedTerm, BoundedPreterm.fst]
        simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
        rw [← Hx]; rfl⟩
  | bd_app t s iht ihs =>
    obtain ⟨qt, Hqt⟩ := iht
    obtain ⟨qs, Hqs⟩ := ihs
    obtain ⟨⟨i, xt⟩, Hit⟩ := germRep qt
    obtain ⟨⟨j, xs⟩, Hjs⟩ := germRep qs
    have Hbt : boundedTermComparison _ _ (canonicalMap i xt) = t := by
      have : canonicalMap i xt = qt := Hit.symm ▸ rfl; rw [this]; exact Hqt
    have Hbs : boundedTermComparison _ 0 (canonicalMap j xs) = s := by
      have : canonicalMap j xs = qs := Hjs.symm ▸ rfl; rw [this]; exact Hqs
    have keyt :
      boundedTermComparison _ _ (canonicalMap (i + j) (pushToSumR xt j)) = t := by
      rw [← same_fiber_as_push_to_r]; exact Hbt
    have keys :
      boundedTermComparison _ 0 (canonicalMap (i + j) (pushToSumL xs i)) = s := by
      rw [← same_fiber_as_push_to_l]; exact Hbs
    refine ⟨canonicalMap (i + j) (bd_app (pushToSumR xt j) (pushToSumL xs i)), ?_⟩
    apply BoundedPreterm.eq
    simp only [boundedTermComparison, universal_map_property,
      coconeOfBoundedTermLInfty, Lhom.onBoundedTerm, BoundedPreterm.fst]
    congr 1
    · have h_eq := congrArg BoundedPreterm.fst keyt
      simp only [boundedTermComparison, universal_map_property,
        coconeOfBoundedTermLInfty] at h_eq
      exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
    · have h_eq := congrArg BoundedPreterm.fst keys
      simp only [boundedTermComparison, universal_map_property,
        coconeOfBoundedTermLInfty] at h_eq
      exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq

@[simp]
lemma bounded_term_comparison_bijective {L : Language.{u}} (n l) :
    Function.Bijective (@boundedTermComparison L n l) :=
  ⟨universal_map_inj_of_components_inj
      (fun m => Lhom.on_bounded_term_inj (henkin_language_canonical_map_inj m)),
    bounded_term_comparison_surj⟩

/-- Auxiliary: surjectivity of bounded_formula_comparison by
structural induction -/
private lemma bounded_formula_comparison_surj {L : Language.{u}} :
    ∀ {n l} (f : BoundedPreformula (LInfty L) n l),
      ∃ x : LimitCarrier (@henkinBoundedFormulaChain L n l),
        boundedFormulaComparison n l x = f :=
  by
  intro n l f
  induction f with
  | bd_falsum =>
    exact
      ⟨canonicalMap 0 bd_falsum, by
        simp [boundedFormulaComparison, universal_map_property,
          coconeOfBoundedFormulaLInfty]⟩
  | bd_equal t₁
    t₂ =>
    obtain ⟨qt₁, Hqt₁⟩ := bounded_term_comparison_bijective _ 0 |>.right t₁
    obtain ⟨qt₂, Hqt₂⟩ := bounded_term_comparison_bijective _ 0 |>.right t₂
    obtain ⟨⟨i, xt₁⟩, Hit₁⟩ := germRep qt₁
    obtain ⟨⟨j, xt₂⟩, Hit₂⟩ := germRep qt₂
    have Hbt₁ : boundedTermComparison _ 0 (canonicalMap i xt₁) = t₁ :=
      by
      have : canonicalMap i xt₁ = qt₁ := Hit₁.symm ▸ rfl
      rw [this]; exact Hqt₁
    have Hbt₂ : boundedTermComparison _ 0 (canonicalMap j xt₂) = t₂ :=
      by
      have : canonicalMap j xt₂ = qt₂ := Hit₂.symm ▸ rfl
      rw [this]; exact Hqt₂
    refine
      ⟨canonicalMap (i + j) (bd_equal (pushToSumR xt₁ j) (pushToSumL xt₂ i)), ?_⟩
        -- bounded_formula_comparison (canonical_map (i+j) (bd_equal
              -- ...)) = bd_equal t₁ t₂
              -- Use the fact that bounded_term_comparison respects same-fiber
    have key₁ :
      boundedTermComparison _ 0 (canonicalMap (i + j) (pushToSumR xt₁ j)) = t₁ := by
      rw [← same_fiber_as_push_to_r]; exact Hbt₁
    have key₂ :
      boundedTermComparison _ 0 (canonicalMap (i + j) (pushToSumL xt₂ i)) = t₂ := by
      rw [← same_fiber_as_push_to_l]; exact Hbt₂
    apply BoundedPreformula.eq
    simp only [boundedFormulaComparison, universal_map_property,
      coconeOfBoundedFormulaLInfty, Lhom.onBoundedFormula, BoundedPreformula.fst]
      -- Goal: preformula.equal (...).fst (...).fst = preformula.equal
            -- t₁.fst t₂.fst
    congr 1
    · -- (on_bounded_term (canonical_map (i+j)) (push_r xt₁ j)).fst = t₁.fst
      have h_eq := congrArg BoundedPreterm.fst key₁
      simp only [boundedTermComparison, universal_map_property,
        coconeOfBoundedTermLInfty] at h_eq
      exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
    · have h_eq := congrArg BoundedPreterm.fst key₂
      simp only [boundedTermComparison, universal_map_property,
        coconeOfBoundedTermLInfty] at h_eq
      exact (Lhom.on_bounded_term_fst _ _) ▸ h_eq
  | bd_rel R =>
    obtain ⟨⟨i, x⟩, Hx⟩ := germRep R
    exact
      ⟨canonicalMap i (bd_rel x),
        by
        apply BoundedPreformula.eq
        simp only [boundedFormulaComparison, universal_map_property,
          coconeOfBoundedFormulaLInfty, Lhom.onBoundedFormula,
          BoundedPreformula.fst]
        simp only [henkinLanguageCanonicalMap, canonicalMapLanguage]
        rw [← Hx]
        rfl⟩
  | bd_apprel f t ihf =>
    obtain ⟨qf, Hqf⟩ := ihf
    obtain ⟨qt, Hqt⟩ := bounded_term_comparison_bijective _ 0 |>.right t
    obtain ⟨⟨i, xf⟩, Hif⟩ := germRep qf
    obtain ⟨⟨j, xt⟩, Hjt⟩ := germRep qt
    have Hbf : boundedFormulaComparison _ _ (canonicalMap i xf) = f :=
      by
      have : canonicalMap i xf = qf := Hif.symm ▸ rfl
      rw [this]; exact Hqf
    have Hbt : boundedTermComparison _ 0 (canonicalMap j xt) = t :=
      by
      have : canonicalMap j xt = qt := Hjt.symm ▸ rfl
      rw [this]; exact Hqt
    have keyf :
      boundedFormulaComparison _ _ (canonicalMap (i + j) (pushToSumR xf j)) = f :=
      by rw [← same_fiber_as_push_to_r]; exact Hbf
    have keyt :
      boundedTermComparison _ 0 (canonicalMap (i + j) (pushToSumL xt i)) = t := by
      rw [← same_fiber_as_push_to_l]; exact Hbt
    refine
      ⟨canonicalMap (i + j) (bd_apprel (pushToSumR xf j) (pushToSumL xt i)), ?_⟩
    apply BoundedPreformula.eq
    simp only [boundedFormulaComparison, universal_map_property,
      coconeOfBoundedFormulaLInfty, Lhom.onBoundedFormula, BoundedPreformula.fst]
    congr 1
    · have hf_eq := congrArg BoundedPreformula.fst keyf
      simp only [boundedFormulaComparison, universal_map_property,
        coconeOfBoundedFormulaLInfty] at hf_eq
      exact (Lhom.on_bounded_formula_fst _ _) ▸ hf_eq
    · have ht_eq := congrArg BoundedPreterm.fst keyt
      simp only [boundedTermComparison, universal_map_property,
        coconeOfBoundedTermLInfty] at ht_eq
      exact (Lhom.on_bounded_term_fst _ _) ▸ ht_eq
  | bd_imp f₁ f₂ ihf₁ ihf₂ =>
    obtain ⟨qf₁, Hqf₁⟩ := ihf₁
    obtain ⟨qf₂, Hqf₂⟩ := ihf₂
    obtain ⟨⟨i, xf₁⟩, Hif₁⟩ := germRep qf₁
    obtain ⟨⟨j, xf₂⟩, Hjf₂⟩ := germRep qf₂
    have Hbf₁ : boundedFormulaComparison _ _ (canonicalMap i xf₁) = f₁ := by
      have : canonicalMap i xf₁ = qf₁ := Hif₁.symm ▸ rfl; rw [this]; exact Hqf₁
    have Hbf₂ : boundedFormulaComparison _ _ (canonicalMap j xf₂) = f₂ := by
      have : canonicalMap j xf₂ = qf₂ := Hjf₂.symm ▸ rfl; rw [this]; exact Hqf₂
    have keyf₁ :
      boundedFormulaComparison _ _ (canonicalMap (i + j) (pushToSumR xf₁ j)) = f₁ :=
      by rw [← same_fiber_as_push_to_r]; exact Hbf₁
    have keyf₂ :
      boundedFormulaComparison _ _ (canonicalMap (i + j) (pushToSumL xf₂ i)) = f₂ :=
      by rw [← same_fiber_as_push_to_l]; exact Hbf₂
    refine
      ⟨canonicalMap (i + j) (bd_imp (pushToSumR xf₁ j) (pushToSumL xf₂ i)), ?_⟩
    apply BoundedPreformula.eq
    simp only [boundedFormulaComparison, universal_map_property,
      coconeOfBoundedFormulaLInfty, Lhom.onBoundedFormula, BoundedPreformula.fst]
    congr 1
    · have h_eq := congrArg BoundedPreformula.fst keyf₁
      simp only [boundedFormulaComparison, universal_map_property,
        coconeOfBoundedFormulaLInfty] at h_eq
      exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq
    · have h_eq := congrArg BoundedPreformula.fst keyf₂
      simp only [boundedFormulaComparison, universal_map_property,
        coconeOfBoundedFormulaLInfty] at h_eq
      exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq
  | bd_all f ihf =>
    obtain ⟨qf, Hqf⟩ := ihf
    obtain ⟨⟨i, xf⟩, Hif⟩ := germRep qf
    have Hbf : boundedFormulaComparison _ _ (canonicalMap i xf) = f := by
      have : canonicalMap i xf = qf := Hif.symm ▸ rfl; rw [this]; exact Hqf
    refine ⟨canonicalMap i (bd_all xf), ?_⟩
    apply BoundedPreformula.eq
    simp only [boundedFormulaComparison, universal_map_property,
      coconeOfBoundedFormulaLInfty, Lhom.onBoundedFormula, BoundedPreformula.fst]
    congr 1
    have h_eq := congrArg BoundedPreformula.fst Hbf
    simp only [boundedFormulaComparison, universal_map_property,
      coconeOfBoundedFormulaLInfty] at h_eq
    exact (Lhom.on_bounded_formula_fst _ _) ▸ h_eq

@[simp]
lemma bounded_formula_comparison_bijective {L : Language.{u}} (n l) :
    Function.Bijective (@boundedFormulaComparison L n l) :=
  ⟨universal_map_inj_of_components_inj
      (fun m => Lhom.on_bounded_formula_inj (henkin_language_canonical_map_inj m)),
    bounded_formula_comparison_surj⟩

lemma bounded_formula'_comparison_bijective {L : Language.{u}} :
    Function.Bijective (@boundedFormula'Comparison L) :=
  bounded_formula_comparison_bijective 1 0

/-- Flypitch construction `equiv_bounded_formula_comparison`, retained by the first-order
soundness and completeness development.
-/
@[expose]
noncomputable def equivBoundedFormulaComparison {L : Language.{u}} :
    Equiv (LimitCarrier (@henkinBoundedFormulaChain' L))
      (boundedFormula (LInfty L) 1) :=
  Equiv.ofBijective boundedFormula'Comparison bounded_formula'_comparison_bijective

/-! ## Henkin theory chain (src/henkin.lean:661-734) -/


/-- The Henkin theory chain: T_n = Henkin^n step applied to T -/
@[expose]
def henkinTheoryChain {L : Language.{u}} (T : SentTheory L) :
    ∀ (n : ℕ), SentTheory ((@henkinLanguageChain L).obj n)
  | 0 => T
  | n + 1 => henkinTheoryStep (henkinTheoryChain T n)

lemma is_consistent_henkin_theory_chain {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) (n : ℕ) : (henkinTheoryChain T n).isConsistent := by
  induction n with
  | zero => exact hT
  | succ n ih => exact is_consistent_henkin_theory_step ih

/-! ## has_enough_constants (from src/fol.lean:2482) -/


/-- A theory has enough constants if every bounded formula has a
Henkin witness -/
@[expose]
def hasEnoughConstants {L : Language.{u}} (T : SentTheory L) : Prop :=
  ∃ (C : ∀ (_f : boundedFormula L 1), L.constants),
    ∀ (f : boundedFormula L 1), T.fst ⊢' (witProperty f (C f)).fst

lemma hasEnoughConstants.intro {L : Language.{u}} (T : SentTheory L)
    (H : ∀ (f : boundedFormula L 1), ∃ c : L.constants, T.fst ⊢' (witProperty f c).fst) :
    hasEnoughConstants T :=
  Classical.axiom_of_choice H

/-! ## ι: pushing T_n into Theory L_∞ -/


/-- Given T_n from henkin_theory_chain, ι T_n is the expansion of
T_n to an L_infty theory -/
@[expose]
def ι {L : Language.{u}} {T : SentTheory L} (m : ℕ) : SentTheory (LInfty L) :=
  Lhom.onSentence (henkinLanguageCanonicalMap m) '' (henkinTheoryChain T m)

@[simp]
lemma in_iota_of_in_step {L : Language.{u}} (i : ℕ) {T : SentTheory L}
    (f : sentence ((@henkinLanguageChain L).obj (i + 1))) :
    f ∈ (henkinTheoryChain T (i + 1)) →
      Lhom.onBoundedFormula (henkinLanguageCanonicalMap (i + 1)) f ∈
        @ι L T (i + 1) :=
  fun H => Set.mem_image_of_mem _ H

@[simp]
lemma is_consistent_iota {L : Language.{u}} {T : SentTheory L} (hT : T.isConsistent)
    (m : ℕ) : (@ι L T m).isConsistent := by
  -- ι m = (henkin_language_canonical_map m).Theory_induced
    -- (henkin_theory_chain T m)
    -- and henkin_language_canonical_map m is injective, and
    -- henkin_theory_chain T m is consistent
  have hm := is_consistent_henkin_theory_chain hT m
  exact Lhom.is_consistent_Theory_induced (henkin_language_canonical_map_inj m) hm

/-! ## Monotonicity: ι is increasing (src/henkin.lean:736-751) -/


lemma henkin_theory_chain_inclusion_step {L : Language.{u}} {T : SentTheory L} {i : ℕ}
    {f : sentence ((@henkinLanguageChain L).obj i)} (hf : f ∈ henkinTheoryChain T i) :
    Lhom.onBoundedFormula (henkinLanguageChainMaps L i (i + 1) (Nat.le_succ i)) f ∈
      henkinTheoryChain T (i + 1) :=
  by
  simp only [henkinTheoryChain, henkinTheoryStep]
  apply Set.mem_union_left
  rw [← henkin_language_inclusion_chain_map]
  exact Set.mem_image_of_mem _ hf

lemma iota_inclusion_of_le {L : Language.{u}} {T : SentTheory L} :
    ∀ {i j : ℕ}, i ≤ j → (@ι L T i) ⊆ (@ι L T j) :=
  by
  intro i j h
  induction j with
  | zero =>
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero h
    subst hi0; exact le_refl _
  | succ n ih =>
    by_cases hx : i = n + 1
    · subst hx; exact le_refl _
    · have hle : i ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      intro ψ hψ
      have hψn : ψ ∈ @ι L T n := ih hle hψ
      obtain ⟨g, hgT, hgψ⟩ := hψn
      have hg_step := henkin_theory_chain_inclusion_step hgT
      refine
        ⟨Lhom.onBoundedFormula (henkinLanguageChainMaps L n (n + 1) (Nat.le_succ n))
            g,
          hg_step, ?_⟩
          -- on_sentence (canonical_map (n+1)) (on_bf (hcm n (n+1)) g)
                -- = on_bf ((canonical_map (n+1)).comp (hcm n (n+1))) g
                -- = on_bf (canonical_map n) g   [by cocone compat]
                -- = ψ
      have hc :
        henkinLanguageCanonicalMap n =
          (henkinLanguageCanonicalMap (n + 1)).comp
            (henkinLanguageChainMaps L n (n + 1) (Nat.le_succ n)) :=
        (@coconeOfLInfty L).h_compat
          (Nat.le_succ n)
            -- The goal is: (canonical_map (n+1)).on_sentence ((hcm n
                  -- (n+1)).on_bounded_formula g) = ψ
                  -- comp_on_bounded_formula: ((f.comp g).on_bounded_formula x) =
                  -- f.on_bounded_formula (g.on_bounded_formula x)
                  -- so lhs = ((canonical_map (n+1)).comp (hcm n
                  -- (n+1))).on_bounded_formula g = (canonical_map
                  -- n).on_bounded_formula g = ψ
      have key :
        (henkinLanguageCanonicalMap (n + 1)).onBoundedFormula
            ((henkinLanguageChainMaps L n (n + 1) (Nat.le_succ n)).onBoundedFormula g) =
          (henkinLanguageCanonicalMap n).onBoundedFormula g :=
        by
        -- comp_on_bounded_formula: (f.comp g).on_bf x = f.on_bf (g.on_bf
                -- x)
                -- hc: canonical_map n = (canonical_map (n+1)).comp (hcm n (n+1))
                -- so (canonical_map n).on_bf g = ((canonical_map (n+1)).comp
                -- (hcm n (n+1))).on_bf g
                --    = (canonical_map (n+1)).on_bf ((hcm n (n+1)).on_bf g)
        calc
          (henkinLanguageCanonicalMap (n + 1)).onBoundedFormula
                ((henkinLanguageChainMaps L n (n + 1) (Nat.le_succ n)).onBoundedFormula
                  g) =
              ((henkinLanguageCanonicalMap (n + 1)).comp
                    (henkinLanguageChainMaps L n (n + 1) (Nat.le_succ n))).onBoundedFormula
                g :=
            (congr_fun (Lhom.comp_on_bounded_formula _ _) g).symm
          _ = (henkinLanguageCanonicalMap n).onBoundedFormula g :=
            congr_arg (fun ϕ : _ →ᴸ _ => ϕ.onBoundedFormula g) hc.symm
      simp only [Lhom.onSentence] at hgψ ⊢
      rw [key]
      exact hgψ

/-! ## T_infty: the henkinization (src/henkin.lean:753-774) -/


/-- T_infty is the henkinization of T; we define it to be the
union ⋃ (n : ℕ), ι(T n). -/
@[reducible, expose]
def TInfty {L : Language.{u}} (T : SentTheory L) : SentTheory (LInfty L) :=
  ⋃ n : ℕ, @ι L T n

/-- Flypitch construction `henkin_language`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def henkinLanguage {L : Language.{u}} {T : SentTheory L} {_hT : T.isConsistent} :
    Language.{u} :=
  LInfty L

/-- Flypitch construction `henkin_language_over`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def henkinLanguageOver {L : Language.{u}} {T : SentTheory L} {_hT : T.isConsistent} :
    L →ᴸ (@henkinLanguage L T _hT) :=
  henkinLanguageCanonicalMap 0

lemma henkin_language_over_injective {L : Language.{u}} {T : SentTheory L}
    {_hT : T.isConsistent} : Lhom.IsInjective (@henkinLanguageOver L T _hT) :=
  henkin_language_canonical_map_inj 0

/-- Flypitch construction `henkinization`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def henkinization {L : Language.{u}} {T : SentTheory L} (hT : T.isConsistent) :
    SentTheory (@henkinLanguage L T hT) :=
  TInfty T

/-! ## wit_infty: find a Henkin witness in henkinization
(src/henkin.lean:778-783) -/


/-- Flypitch construction `wit_infty`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def witInfty {L : Language.{u}} {T : SentTheory L} {hT : T.isConsistent}
    (f : boundedFormula (@henkinLanguage L T hT) 1) :
    Σ c : (@henkinLanguage L T hT).constants,
      Σ (f' : Σ' (x : LimitCarrier (@henkinBoundedFormulaChain' L)),
          boundedFormula'Comparison x = f),
        Σ' (f'' : coproductOfDirectedDiagram (@henkinBoundedFormulaChain' L)),
          ⟦f''⟧ = f'.fst ∧
            c = (henkinLanguageCanonicalMap (f''.1 + 1)).onFunction (wit' f''.2) :=
  by
  have f_lift1 :=
    Classical.psigmaOfExists (bounded_formula'_comparison_bijective.right f)
  have f_lift2 := germRep f_lift1.fst
  exact
    ⟨(henkinLanguageCanonicalMap (f_lift2.fst.1 + 1)).onFunction (wit' f_lift2.fst.2),
      f_lift1, f_lift2.fst, f_lift2.snd, rfl⟩

/-! ## henkinization has enough constants
(src/henkin.lean:785-831) -/
-- Helper: on_bounded_formula commutes with
-- subst0_bounded_formula


-- Helper: on_bounded_formula commutes with
-- subst0_bounded_formula
private lemma on_bounded_formula_subst0 {L L' : Language.{u}} (ϕ : L →ᴸ L') {n l}
    (f : BoundedPreformula L (n + 1) l) (s : boundedTerm L n) :
    ϕ.onBoundedFormula (subst0BoundedFormula f s) =
      subst0BoundedFormula (ϕ.onBoundedFormula f) (ϕ.onBoundedTerm s) :=
  by
  apply BoundedPreformula.eq
  simp only [subst0_bounded_formula_fst, Lhom.on_bounded_formula_fst,
    Lhom.on_bounded_term_fst, Lhom.on_formula_subst]

@[simp]
lemma henkinization_is_henkin {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : hasEnoughConstants (henkinization hT) :=
  by
  apply hasEnoughConstants.intro
  intro f
  have big_sigma := witInfty (hT := hT) f
  obtain ⟨c, ⟨f', Hf'⟩, ⟨i, f''⟩, Heq, Hc⟩ := big_sigma
  let wp_step : sentence ((@henkinLanguageChain L).obj (i + 1)) :=
    witProperty (henkinLanguageInclusion.onBoundedFormula f'')
      (wit' f'')
        -- wp_step ∈ henkin_theory_chain T (i+1) = henkin_theory_step
          -- (henkin_theory_chain T i)
  have hwp_step : wp_step ∈ henkinTheoryChain T (i + 1) :=
    by
    simp only [henkinTheoryChain, henkinTheoryStep]
    right
    exact
      ⟨f'', Set.mem_univ _, rfl⟩
        -- (hcm (i+1)).on_bounded_formula wp_step ∈ ι (i+1)
  have hwp_iota :
    (henkinLanguageCanonicalMap (i + 1)).onBoundedFormula wp_step ∈ @ι L T (i + 1) :=
    in_iota_of_in_step i wp_step hwp_step
  have hf_eq : (henkinLanguageCanonicalMap i).onBoundedFormula f'' = f :=
    by
    have :
      (henkinLanguageCanonicalMap i).onBoundedFormula f'' =
        boundedFormula'Comparison (canonicalMap i f'') :=
      by
      simp only [boundedFormula'Comparison, boundedFormulaComparison,
        universal_map_property, coconeOfBoundedFormulaLInfty]
    simp only [canonicalMap] at this
    rw [this, show (Quotient.mk _ ⟨i, f''⟩ : LimitCarrier _) = f' from Heq, Hf']
      -- Key: (hcm (i+1)).on_bf (inclusion.on_bf f'') = f
        -- via cocone_of_bounded_formula'_L_infty.h_compat at i ≤ i+1:
        -- (hcm i).on_bf = (hcm (i+1)).on_bf ∘ incl.on_bf
  have hinc_eq :
    (henkinLanguageCanonicalMap (i + 1)).onBoundedFormula
        (henkinLanguageInclusion.onBoundedFormula f'') =
      f :=
    by
    -- Use cocone_of_bounded_formula'_L_infty.h_compat to get the key
        -- equality
    have hcompat :=
      (@coconeOfBoundedFormula'LInfty L).h_compat
        (Nat.le_succ i)
          -- hcompat : (hcm i).on_bf = (hcm (i+1)).on_bf ∘ (chain_maps i
              -- (i+1)).on_bf
    have hc_bf := congr_fun hcompat f''
    simp only [Function.comp, henkinBoundedFormulaChain', henkinBoundedFormulaChain,
      coconeOfBoundedFormula'LInfty] at hc_bf
    rw [← henkin_language_inclusion_chain_map] at hc_bf
    rw [← hc_bf, hf_eq]
      -- Key: (hcm (i+1)).on_bounded_formula wp_step = wit_property f c
  have heq :
    (henkinLanguageCanonicalMap (i + 1)).onBoundedFormula wp_step =
      witProperty f c :=
    by
    simp only [wp_step, witProperty, Lhom.onBoundedFormula]
    congr 1
    · -- bd_ex (incl.on_bf f'') maps to bd_ex f
      simp only [bdEx, bdNot, Lhom.onBoundedFormula]
      exact congrArg (fun g => bd_imp (bd_all (bd_imp g bd_falsum)) bd_falsum) hinc_eq
    · -- subst0 (incl.on_bf f'') (bd_const (wit' f'')) maps to subst0 f (bd_const c)
      rw [on_bounded_formula_subst0, hinc_eq]
      congr 1
      simp only [bdConst, Lhom.onBoundedTerm]
      exact congrArg BoundedPreterm.bd_func Hc.symm
  have hmem : witProperty f c ∈ henkinization hT :=
    by
    simp only [henkinization, TInfty, Set.mem_iUnion]
    exact ⟨i + 1, heq ▸ hwp_iota⟩
  exact ⟨c, saxm' hmem⟩

/-! ## Directed union infrastructure (src/henkin.lean:833-874) -/


/-- For every n, T_n as a Theory_over (ι T 0) -/
@[expose]
def henkinTheoryOver {L : Language.{u}} (T : SentTheory L) (hT : T.isConsistent)
    (n : ℕ) : TheoryOver (@ι L T 0) (is_consistent_iota hT 0) :=
  ⟨@ι L T n, iota_inclusion_of_le (Nat.zero_le n), is_consistent_iota hT n⟩

/-- Flypitch construction `henkin_theory_schain`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def henkinTheorySchain {L : Language.{u}} (T : SentTheory L) (hT : T.isConsistent) :
    Set (TheoryOver (@ι L T 0) (is_consistent_iota hT 0)) :=
  {T' | ∃ k : ℕ, @ι L T k = T'.val}

lemma iota_union_rw {L : Language.{u}} (T : SentTheory L) (hT : T.isConsistent) :
    @ι L T 0 ∪ ⋃₀ (Subtype.val '' henkinTheorySchain T hT) = henkinization hT := by
  -- henkinization hT = T_infty T = ⋃ n, ι n
    -- LHS = ι 0 ∪ (⋃ { ι k | k : ℕ })  = ⋃ n, ι n
  apply Set.eq_of_subset_of_subset
  · -- LHS ⊆ henkinization
    apply Set.union_subset
    · exact Set.subset_iUnion (@ι L T) 0
    · intro ψ hψ
      obtain ⟨S, hS, hψS⟩ := hψ
      obtain ⟨To, hTo, hSTo⟩ := hS
      simp only [henkinTheorySchain] at hTo
      obtain ⟨k, hk⟩ := hTo
      simp only [henkinization, TInfty, Set.mem_iUnion]
      exact ⟨k, hk ▸ hSTo ▸ hψS⟩
  · -- henkinization ⊆ LHS
    intro ψ hψ
    simp only [henkinization, TInfty, Set.mem_iUnion] at hψ
    obtain ⟨k, hk⟩ := hψ
    cases k with
    | zero => exact Set.mem_union_left _ hk
    | succ n =>
      apply Set.mem_union_right
      refine
        ⟨@ι L T (n + 1), ?_, hk⟩
          -- Need: ι (n+1) ∈ Subtype.val '' henkin_theory_schain T hT
                -- i.e., ∃ To ∈ henkin_theory_schain T hT, To.val = ι (n+1)
      let To : TheoryOver (@ι L T 0) (is_consistent_iota hT 0) :=
        ⟨@ι L T (n + 1), iota_inclusion_of_le (Nat.zero_le _), is_consistent_iota hT _⟩
      refine ⟨To, ?_, rfl⟩
      simp only [henkinTheorySchain]
      exact ⟨n + 1, rfl⟩

lemma chain_henkin_theory_chain {L : Language.{u}} (T : SentTheory L)
    (hT : T.isConsistent) : IsChain TheoryOverSubset (henkinTheorySchain T hT) :=
  by
  intro T₁ hT₁ T₂ hT₂ hne
  simp only [henkinTheorySchain, Set.mem_ofPred_eq] at hT₁ hT₂
  obtain ⟨i, hi⟩ := hT₁; obtain ⟨j, hj⟩ := hT₂
  by_cases h : i ≤ j
  · left
      -- T₁.val = ι i ⊆ ι j = T₂.val
    intro f hf
    rw [← hj]
    exact iota_inclusion_of_le h (hi ▸ hf)
  · right
      -- T₂.val = ι j ⊆ ι i = T₁.val
    intro f hf
    rw [← hi]
    exact iota_inclusion_of_le (Nat.le_of_lt (Nat.lt_of_not_le h)) (hj ▸ hf)

lemma is_consistent_henkinization {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : (henkinization hT).isConsistent :=
  by
  have key := @consis_limit _ _ _ (henkinTheorySchain T hT)
  rw [iota_union_rw] at key
  exact key (chain_henkin_theory_chain T hT)

/-! ## Completion of henkinization (src/henkin.lean:891-911) -/


/-- The core completion: henkinization extends to a complete
consistent theory -/
@[expose]
noncomputable def completionOfHenkinizationCore {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) :
    Σ' (T' : TheoryOver (henkinization hT) (is_consistent_henkinization hT)),
      T'.val.isComplete :=
  completionOfConsis (henkinization hT) (is_consistent_henkinization hT)

/-- The completed henkinization theory -/
@[expose]
noncomputable def completionOfHenkinization {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : SentTheory (@henkinLanguage L T hT) :=
  (completionOfHenkinizationCore hT).fst.val

/-- The completed theory contains the henkinization -/
lemma completion_of_henkinization_contains {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : henkinization hT ⊆ completionOfHenkinization hT :=
  (completionOfHenkinizationCore hT).fst.property.left

/-- The completed theory is consistent -/
lemma completion_of_henkinization_consistent {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : (completionOfHenkinization hT).isConsistent :=
  (completionOfHenkinizationCore hT).fst.property.right

/-- The completed theory is complete -/
theorem completion_of_henkinization_complete {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : (completionOfHenkinization hT).isComplete :=
  (completionOfHenkinizationCore hT).snd

/-- The completed theory is Henkin -/
@[simp]
lemma completion_of_henkinization_is_henkin {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) : hasEnoughConstants (completionOfHenkinization hT) :=
  by
  apply hasEnoughConstants.intro
  intro f
  obtain ⟨C, HC⟩ := henkinization_is_henkin hT
  refine ⟨C f, ?_⟩
  apply weakening' (Γ := (henkinization hT).fst)
  · exact Set.image_mono (completion_of_henkinization_contains hT)
  · exact HC f

/-! ## Helpers for the term model (ported from
src/fol.lean:2445-2498) -/


/-- If T is complete and T ⊢ₛ' f, then f ∈ T -/
lemma mem_of_sprovable {L : Language.{u}} {T : SentTheory L} (hcomp : T.isComplete)
    {f : sentence L} (hf : T ⊢ₛ' f) : f ∈ T :=
  by
  rcases hcomp.2 f with h | h
  · exact h
  · exfalso;
    apply
      hcomp.1
        -- h : bd_not f ∈ T, hf : T ⊢ₛ' f
            -- T.fst ⊢' f.fst ⟹ ⊥'  (from h), and T.fst ⊢' f.fst (from hf)
    exact impE' _ ⟨prf.axm (Set.mem_image_of_mem _ h)⟩ hf

/-- If T is complete and T ⊬ₛ' f, then T ⊢ₛ' bd_not f -/
lemma notI_of_is_complete {L : Language.{u}} {T : SentTheory L} (hcomp : T.isComplete)
    {f : sentence L} (hf : ¬T ⊢ₛ' f) : T ⊢ₛ' bdNot f :=
  by
  rcases hcomp.2 f with h | h
  · exact absurd ⟨prf.axm (Set.mem_image_of_mem _ h)⟩ hf
  · exact ⟨prf.axm (Set.mem_image_of_mem _ h)⟩

/-- If T is complete, T ⊢ₛ' (bd_imp φ ψ) follows from (T ⊢ₛ' φ →
T ⊢ₛ' ψ) -/
lemma impI_of_is_complete {L : Language.{u}} {T : SentTheory L} (hcomp : T.isComplete)
    {φ ψ : sentence L} (h : SentTheory.sprovable T φ → SentTheory.sprovable T ψ) :
    SentTheory.sprovable T (bd_imp φ ψ) :=
  by
  simp only [SentTheory.sprovable, SentTheory.fst, BoundedPreformula.fst]
  rcases hcomp.2 φ with h₁ | h₁
  · -- φ ∈ T
    exact impI' (weakening1' (h ⟨prf.axm (Set.mem_image_of_mem _ h₁)⟩))
  · -- bd_not φ ∈ T (h₁ : bd_not φ ∈ T)
    apply impI'
    apply falsumE'
    apply weakening1'
    have hmem : BoundedPreformula.fst φ ⟹ ⊥' ∈ BoundedPreformula.fst '' T :=
      Set.mem_image_of_mem _ h₁
    exact impE' _ ⟨prf.axm (Set.mem_insert_of_mem _ hmem)⟩ ⟨axm1⟩

/-- Given a complete Henkin theory, universal failure yields a
counterexample -/
lemma find_counterexample_of_henkin {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) (f : boundedFormula L 1)
    (hf : ¬T ⊢ₛ' bd_all f) :
    ∃ t : closedTerm L, T ⊢ₛ' bdNot (subst0BoundedFormula f t) :=
  by
  obtain ⟨C, hC⟩ := henk
  refine ⟨bdConst (C (bdNot f)), ?_⟩
  have hwit : T.fst ⊢' (witProperty (bdNot f) (C (bdNot f))).fst :=
    hC
      (bdNot f)
        -- hwit : T.fst ⊢' (bd_ex (bd_not f)).fst ⟹ (bd_not f)[c/0].fst
          -- We need T.fst ⊢' (bd_not (subst0_bounded_formula f (bd_const
          -- (C (bd_not f))))).fst
          -- Strategy: use ex_not_of_not_all to get ∃'(∼f), then apply hwit
          -- Get ∼(∀'f) as a prf and apply ex_not_of_not_all:
  have hnotall_prf : T.fst ⊢ ∼(∀'f.fst) := (notI_of_is_complete hcomp hf).some
  have hex : T.fst ⊢' (bdEx (bdNot f)).fst :=
    ⟨exNotOfNotAll hnotall_prf⟩
      -- Apply hwit: T.fst ⊢' (bd_ex (bd_not f)).fst ⟹ (bd_not
        -- (subst0_bf f c)).fst
        -- Result: T.fst ⊢' (bd_not (subst0_bf f c)).fst = (subst0_bf f
        -- c).fst ⟹ ⊥'
        -- which equals T.fst ⊢ₛ' bd_not (subst0_bf f (bd_const (C
        -- (bd_not f))))
  simp only [SentTheory.sprovable, SentTheory.fst]
  simp only [BoundedPreformula.fst, bdNot] at hwit
  exact impE' _ hwit hex

/-! ## Term model construction (src/fol.lean:2500-2559) -/


/-- The term equality relation: t₁ ~ t₂ iff T ⊢ₛ' t₁ ≃ t₂ -/
@[expose]
def term_rel {L : Language.{u}} (T : SentTheory L) (t₁ t₂ : closedTerm L) : Prop :=
  T ⊢ₛ' bd_equal t₁ t₂

/-- The term equality setoid -/
@[expose]
noncomputable def term_setoid {L : Language.{u}} (T : SentTheory L) :
    Setoid (closedTerm L) :=
  { r := term_rel T
    iseqv :=
      { refl := fun t => ⟨prf.ref T.fst t.fst⟩
        symm := fun h => h.map prfSymm
        trans := fun h₁ h₂ => h₁.map2 prfTrans h₂ } }

/-- The carrier of the term model: closed terms modulo provable
equality -/
noncomputable abbrev termModel' {L : Language.{u}} (T : SentTheory L) : Type u :=
  @Quotient (closedTerm L) (term_setoid T)

/-- The function interpretation helper for the term model -/
@[expose]
noncomputable def term_model_fun' {L : Language.{u}} (T : SentTheory L) {l}
    (t : closedPreterm L l) (ts : DVec (closedTerm L) l) : termModel' T :=
  @Quotient.mk'' _ (term_setoid T) (bdApps t ts)

/-- Core congr: given equal_preterms and DVecRel, bd_apps
preserves term_rel -/
private lemma bd_apps_congr_equal_preterms {L : Language.{u}} {T : SentTheory L} {l}
    {t t' : closedPreterm L l} (Ht : equalPreterms T.fst t.fst t'.fst) :
    ∀ {xs xs' : DVec (closedTerm L) l},
      @DVec.DVecRel _ (term_setoid T) _ xs xs' →
        term_rel T (bdApps t xs) (bdApps t' xs') :=
  by
  intro xs xs' hxs
  induction hxs with
  | rnil =>
    simp only [term_rel, SentTheory.sprovable, SentTheory.fst, bdApps]
    exact ⟨Ht DVec.nil⟩
  | rcons hx hxs ih =>
    -- hx : term_rel T x x' = T ⊢ₛ' bd_equal x x'
        -- hxs : DVecRel xs xs'
        -- ih is: equal_preterms T.fst (bd_app t x).fst (bd_app t'
        -- x').fst → ...
        -- No, ih is the claim for bd_app t x, bd_app t' x', hxs
    simp only [term_rel, SentTheory.sprovable, SentTheory.fst,
      bdApps] at *
        -- Need: T.fst ⊢' bd_apps (bd_app t x) xs ≃ bd_apps (bd_app t'
            -- x') xs'
            -- But ih gives us: for (bd_app t x) and (bd_app t' x') vs xs and
            -- xs'
            -- Ht' : equal_preterms T.fst (bd_app t x).fst (bd_app t' x').fst
            -- follows from Ht and hx
    exact ih (equalPretermsApp Ht hx.some)

/-- Helper: term_model_fun' is compatible with term_rel on each
argument -/
lemma term_model_fun'_congr {L : Language.{u}} {T : SentTheory L} {l}
    (t : closedPreterm L l) :
    ∀ {xs xs' : DVec (closedTerm L) l},
      @DVec.DVecRel _ (term_setoid T) _ xs xs' →
        term_model_fun' T t xs = term_model_fun' T t xs' :=
  by
  intro xs xs' hxs
  simp only [term_model_fun']
  apply Quotient.sound
  change term_rel T _ _
  exact bd_apps_congr_equal_preterms (equalPretermsRefl T.fst t.fst) hxs

/-- The function interpretation in the term model, using
quotient_lift -/
@[expose]
noncomputable def term_model_fun {L : Language.{u}} (T : SentTheory L) {l}
    (t : closedPreterm L l) (ts : DVec (termModel' T) l) : termModel' T :=
  @DVec.quotientLift _ _ (term_setoid T) _ (term_model_fun' T t)
    (term_model_fun'_congr t) ts

/-- The relation interpretation helper -/
@[expose]
noncomputable def term_model_rel' {L : Language.{u}} (T : SentTheory L) {l}
    (f : presentence L l) (ts : DVec (closedTerm L) l) : Prop :=
  T ⊢ₛ' bdAppsRel f ts

/-- Core congr: given equiv_preformulae and DVecRel, bd_apps_rel
preserves provability -/
private lemma bd_apps_rel_congr_equiv {L : Language.{u}} {T : SentTheory L} {l}
    {f f' : presentence L l} (Hf : equivPreformulae T.fst f.fst f'.fst) :
    ∀ {xs xs' : DVec (closedTerm L) l},
      @DVec.DVecRel _ (term_setoid T) _ xs xs' →
        (T ⊢ₛ' bdAppsRel f xs) = (T ⊢ₛ' bdAppsRel f' xs') :=
  by
  intro xs xs' hxs
  induction hxs with
  | rnil =>
    simp only [bdAppsRel, SentTheory.sprovable, SentTheory.fst]
    exact propext (iff_of_biimp ⟨Hf DVec.nil⟩)
  | rcons hx hxs ih =>
    simp only [bdAppsRel]
    exact ih (equivPreformulaeApprel Hf hx.some)

/-- Helper: term_model_rel' is compatible with term_rel on each
argument -/
lemma term_model_rel'_congr {L : Language.{u}} {T : SentTheory L} {l}
    (f : presentence L l) :
    ∀ {xs xs' : DVec (closedTerm L) l},
      @DVec.DVecRel _ (term_setoid T) _ xs xs' →
        term_model_rel' T f xs = term_model_rel' T f xs' :=
  by
  intro xs xs' hxs
  simp only [term_model_rel']
  exact bd_apps_rel_congr_equiv (equivPreformulaeRefl T.fst f.fst) hxs

/-- The relation interpretation in the term model -/
@[expose]
noncomputable def term_model_rel {L : Language.{u}} (T : SentTheory L) {l}
    (f : presentence L l) (ts : DVec (termModel' T) l) : Prop :=
  @DVec.quotientLift _ _ (term_setoid T) _ (term_model_rel' T f)
    (term_model_rel'_congr f) ts

/-! ## Term model and main completeness theorem -/


/-- term_model of a complete Henkin theory
(src/fol.lean:2559-2562) -/
@[reducible, expose]
noncomputable def term_model {L : Language.{u}} {T : SentTheory L}
    (_hcomp : T.isComplete) (_henk : hasEnoughConstants T) : Structure L :=
  { carrier := termModel' T
    funMap := fun {_n} f ts => term_model_fun T (bd_func f) ts
    relMap := fun {_n} R ts => term_model_rel T (bd_rel R) ts }

/-- Canonical quotient map from closed terms to the term model -/
@[reducible, expose]
noncomputable def term_mk {L : Language.{u}} (T : SentTheory L) (t : closedTerm L) :
    termModel' T :=
  @Quotient.mk'' _ (term_setoid T) t

/-! ### Realization in the term model (src/fol.lean:2568-2627) -/


/-- Realizing a closed preterm in the term model recovers
`bd_apps`. -/
private lemma realize_closed_preterm_term_model {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) :
    ∀ {l} (ts : DVec (closedTerm L) l) (t : closedPreterm L l),
      realizeBoundedTerm (DVec.nil : DVec (term_model hcomp henk) 0) t
          (ts.map (term_mk T)) =
        term_mk T (bdApps t ts) :=
  by
  intro l ts t
  induction t with
  | bd_var k => exact absurd k.2 (Nat.not_lt_zero k.1)
  | bd_func f =>
    -- realize_bounded_term [] (bd_func f) (ts.map term_mk) =
        -- (term_model).fun_map f (ts.map term_mk)
        --   = term_model_fun T (bd_func f) (ts.map term_mk)
        -- = term_model_fun' T (bd_func f) ts (by quotient_beta) =
        -- ⟦bd_apps (bd_func f) ts⟧ = term_mk ...
    change
      term_model_fun T (bd_func f) (ts.map (term_mk T)) =
        term_mk T (bdApps (bd_func f) ts)
    simp only [term_model_fun]
    rw [show (ts.map (term_mk T)) = DVec.map Quotient.mk'' ts from rfl]
    rw [DVec.quotient_beta]
    rfl
  | bd_app t₁ t₂ ih₁ ih₂ =>
    -- bd_app t₁ t₂ has type closed_preterm L l, t₁ has level (l+1),
        -- t₂ has level 0
    rw [realize_bounded_term_bd_app]
      -- Goal: realize_bounded_term [] t₁ (rbt t₂ DVec.nil :: ts.map
          -- term_mk)
          --     = term_mk T (bd_apps (bd_app t₁ t₂) ts)
    have h2 :
      realizeBoundedTerm (DVec.nil : DVec (term_model hcomp henk) 0) t₂ DVec.nil =
        term_mk T t₂ :=
      by
      have := ih₂ DVec.nil
      simp only [DVec.map, bdApps] at this
      exact this
    rw [h2]
      -- Goal: realize_bounded_term [] t₁ (term_mk T t₂ :: ts.map
          -- term_mk)
          --     = term_mk T (bd_apps (bd_app t₁ t₂) ts)
          -- which equals  term_mk T (bd_apps t₁ (t₂ :: ts))
    have h1 := ih₁ (DVec.cons t₂ ts)
    simp only [DVec.map, bdApps] at h1
    exact h1

/-- Realizing a closed term in the term model is the canonical
quotient map. -/
@[simp]
private lemma realize_closed_term_term_model {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) (t : closedTerm L) :
    realizeClosedTerm (term_model hcomp henk) t = term_mk T t :=
  by
  have :=
    realize_closed_preterm_term_model hcomp henk (DVec.nil : DVec (closedTerm L) 0) t
  simp only [DVec.map, bdApps] at this
  exact this

/-- Substitution commutes with realization for preterms. -/
private lemma realize_subst_preterm {L : Language.{u}} {S : Structure L} {n l}
    (t : BoundedPreterm L (n + 1) l) (xs : DVec S l) (s : closedTerm L) (v : DVec S n) :
    realizeBoundedTerm v (substmaxBoundedTerm t s) xs =
      realizeBoundedTerm (v.concat (realizeClosedTerm S s)) t xs :=
  by
  induction t with
  | bd_var k =>
    cases xs
    by_cases h : k.1 < n
    · rw [substmax_var_lt k s h]
      simp only [realizeBoundedTerm]
      rw [DVec.concat_nth v _ k.1 k.2 h]
    · have h' : k.1 = n := Nat.le_antisymm (Nat.lt_succ_iff.mp k.2) (Nat.le_of_not_lt h)
      rw [substmax_var_eq k s h']
      simp only [realizeBoundedTerm]
      rw [realize_bounded_term_irrel _ s (closedPreterm.cast0_fst (n := n) s)]
      simp [DVec.concat_nth_last, h']
  | bd_func f => rfl
  | bd_app t₁ t₂ ih₁
    ih₂ =>
    simp only [substmax_bounded_term_bd_app, realizeBoundedTerm]
    rw [ih₂ DVec.nil, ih₁]

/-- Substitution commutes with realization for terms. -/
private lemma realize_subst_term {L : Language.{u}} {S : Structure L} {n} (v : DVec S n)
    (s : closedTerm L) (t : boundedTerm L (n + 1)) :
    realizeBoundedTerm v (substmaxBoundedTerm t s) DVec.nil =
      realizeBoundedTerm (v.concat (realizeClosedTerm S s)) t DVec.nil :=
  realize_subst_preterm t DVec.nil s v

/-- Substitution commutes with realization for formulas. -/
private lemma realize_subst_formula {L : Language.{u}} (S : Structure L) {n}
    (f : boundedFormula L (n + 1)) (t : closedTerm L) (v : DVec S n) :
    realizeBoundedFormula v (substmaxBoundedFormula f t) DVec.nil ↔
      realizeBoundedFormula (v.concat (realizeClosedTerm S t)) f DVec.nil :=
  by
  set y := realizeClosedTerm S t with hy_def
  let φ : ℕ → S := fun k => if h : k < n then v.nth k h else y
  rw [realize_bounded_formula_iff (v₁ := v) (v₂ := φ) (fun k hk => by simp [φ, hk])
      (substmaxBoundedFormula f t) DVec.nil]
    -- RHS via realize_bounded_formula_iff with extension
      -- subst_realize φ y n
  rw [realize_bounded_formula_iff (v₁ := v.concat y) (v₂ := substRealize φ y n)
      (fun k hk => by
        by_cases hkn : k < n
        · rw [DVec.concat_nth v _ k hk hkn]
          have hnek : k ≠ n := Nat.ne_of_lt hkn
          have hnotlt : ¬n < k := Nat.not_lt.mpr (Nat.le_of_lt hkn)
          simp only [substRealize, ite_true, hnotlt, ite_false, φ, hkn, dite_eq_left]
        · have hkeq : k = n :=
            Nat.le_antisymm (Nat.lt_succ_iff.mp hk) (Nat.le_of_not_lt hkn)
          subst hkeq
          simp [DVec.concat_nth_last])
      f DVec.nil]
    -- Formula side
  simp only [substmax_bounded_formula_fst]
    -- realize_formula_subst gives:
      -- realize_formula (subst_realize φ (realize_term φ (lift_term
      -- t.fst n) []) n) f.fst []
      --     ↔ realize_formula φ (subst_formula f.fst t.fst n) []
      -- We need: realize_formula (subst_realize φ y n) f.fst [] ↔
      -- realize_formula φ (subst_formula ...) []
  have hreal_t : realizeTerm φ (liftTerm t.fst n) DVec.nil = y :=
    by
    rw [hy_def]
    rw [show
        realizeClosedTerm S t = realizeBoundedTerm (DVec.nil : DVec S 0) t DVec.nil
        from rfl]
      -- realize_term φ (lift_term t.fst n) [] = realize_term φ t.fst
          -- []
          -- (since closed terms ignore the valuation, lifting is
          -- irrelevant)
          -- = realize_bounded_term [] t []
    have hlift :
      realizeTerm φ (liftTerm t.fst n) DVec.nil = realizeTerm φ t.fst DVec.nil :=
      by
      have hfst_eq : (liftTerm t.fst n) = t.fst :=
        lift_bounded_term_irrel t n (Nat.zero_le _)
      rw [hfst_eq]
    rw [hlift]
    exact
      (realize_bounded_term_eq (v₁ := (DVec.nil : DVec S 0)) (v₂ := φ)
          (fun k hk => absurd hk (Nat.not_lt_zero k)) t DVec.nil).symm
  rw [← hreal_t]
  exact (realize_formula_subst φ n f.fst t.fst DVec.nil).symm

/-- Substitution at position 0 commutes with realization. -/
private lemma realize_subst_formula0 {L : Language.{u}} (S : Structure L)
    (f : boundedFormula L 1) (t : closedTerm L) :
    realizeSentence S (subst0BoundedFormula f t) ↔
      realizeBoundedFormula (DVec.cons (realizeClosedTerm S t) DVec.nil) f DVec.nil :=
  by
  rw [show subst0BoundedFormula f t = substmaxBoundedFormula f t from
      substmax_eq_subst0_formula f t]
    -- realize_sentence S g = realize_bounded_formula DVec.nil g
      -- DVec.nil
      -- and (DVec.nil).concat (realize_closed_term S t) = DVec.cons
      -- (...) DVec.nil
  change
    realizeBoundedFormula (DVec.nil : DVec S 0) (substmaxBoundedFormula f t)
        DVec.nil ↔
      _
  rw [realize_subst_formula S f t DVec.nil]
    -- (DVec.nil).concat y = DVec.cons y DVec.nil
  rfl

/-- Substituting in the term model: relate to realization at the
quotient class. -/
private lemma term_model_subst0 {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) (f : boundedFormula L 1)
    (t : closedTerm L) :
    realizeSentence (term_model hcomp henk) (subst0BoundedFormula f t) ↔
      realizeBoundedFormula
        (DVec.cons (term_mk T t : (term_model hcomp henk).carrier)
          (DVec.nil : DVec (term_model hcomp henk).carrier 0))
        f DVec.nil :=
  by
  rw [realize_subst_formula0 (term_model hcomp henk) f t]
  rw [realize_closed_term_term_model hcomp henk t]

/-- The term model is nonempty. -/
private lemma nonempty_term_model {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) :
    Nonempty (term_model hcomp henk).carrier :=
  by
  obtain ⟨C, _⟩ := henk
  exact
    ⟨term_mk T (bdConst (C (bd_equal (bd_var ⟨0, by omega⟩) (bd_var ⟨0, by omega⟩))))⟩

/-- Structural recursion on a `bounded_preformula L 0 l` for the
term-model iff,
    parameterized by an external IH on smaller quantifier-counts.

    Implemented via direct structural pattern matching on `f` to
    avoid issues
    with `induction` on a non-variable index `n = 0`. -/
theorem term_model_ssatisfied_iff_struct {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) (n : ℕ)
    (n_ih : ∀ m, m < n → ∀ {l'} (f' : presentence L l') (ts' : DVec (closedTerm L) l'),
            countQuantifiers f'.fst < m → ((T ⊢ₛ' bdAppsRel f' ts') ↔
                realizeSentence (term_model hcomp henk) (bdAppsRel f' ts'))) :
    ∀ {l} (f : BoundedPreformula L 0 l) (ts : DVec (closedTerm L) l),
      countQuantifiers f.fst < n →
        ((T ⊢ₛ' bdAppsRel f ts) ↔ realizeSentence (term_model hcomp henk) (bdAppsRel f ts))
  | _, bd_falsum, ts, _ => by
    cases ts
    simp only [bdAppsRel]
    refine ⟨fun h => absurd h hcomp.1, fun h => ?_⟩
    exfalso; exact h
  | _, bd_equal t₁ t₂, ts, _ => by
    cases ts
    simp only [bdAppsRel]
    rw [show
        realizeSentence (term_model hcomp henk) (bd_equal t₁ t₂) ↔
          realizeClosedTerm (term_model hcomp henk) t₁ =
            realizeClosedTerm (term_model hcomp henk) t₂
        from realize_sentence_equal t₁ t₂]
    rw [realize_closed_term_term_model hcomp henk t₁,
      realize_closed_term_term_model hcomp henk t₂]
    refine ⟨fun h => Quotient.sound (show term_rel T t₁ t₂ from h), fun h => ?_⟩
    exact (Quotient.exact h : term_rel T t₁ t₂)
  | _, bd_rel R, ts, _ => by
    rw [realize_bd_apps_rel R ts]
    show
      _ ↔
        (term_model hcomp henk).relMap R
          (ts.map (realizeClosedTerm (term_model hcomp henk)))
    have h_eq :
      ts.map (realizeClosedTerm (term_model hcomp henk)) = ts.map (term_mk T) :=
      by
      apply DVec.map_congr
      intro x
      exact realize_closed_term_term_model hcomp henk x
    rw [h_eq]
    change _ ↔ term_model_rel T (bd_rel R) (ts.map (term_mk T))
    simp only [term_model_rel]
    rw [show (ts.map (term_mk T)) = DVec.map Quotient.mk'' ts from rfl]
    rw [DVec.quotient_beta]
    rfl
  | _, bd_apprel f t, ts, hn =>
    by
    have heq : bdAppsRel (bd_apprel f t) ts = bdAppsRel f (DVec.cons t ts) := rfl
    rw [heq]
    have hn' : countQuantifiers f.fst < n :=
      by
      rw [count_quantifiers_succ]
      simp only [BoundedPreformula.fst, countQuantifiers] at hn
      exact hn
    exact term_model_ssatisfied_iff_struct hcomp henk n n_ih f (DVec.cons t ts) hn'
  | _, bd_imp f₁ f₂, ts, hn => by
    cases ts
    simp only [bdAppsRel]
    have hn1 : countQuantifiers f₁.fst < n :=
      by
      simp only [BoundedPreformula.fst, countQuantifiers] at hn
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hn
    have hn2 : countQuantifiers f₂.fst < n :=
      by
      simp only [BoundedPreformula.fst, countQuantifiers] at hn
      exact lt_of_le_of_lt (Nat.le_add_left _ _) hn
    have ih1 := term_model_ssatisfied_iff_struct hcomp henk n n_ih f₁ DVec.nil hn1
    have ih2 := term_model_ssatisfied_iff_struct hcomp henk n n_ih f₂ DVec.nil hn2
    simp only [bdAppsRel] at ih1 ih2
    rw [show
        realizeSentence (term_model hcomp henk) (bd_imp f₁ f₂) ↔
          (realizeSentence (term_model hcomp henk) f₁ →
            realizeSentence (term_model hcomp henk) f₂)
        from realize_sentence_imp]
    refine ⟨fun hp h1 => ?_, fun hsem => ?_⟩
    · apply ih2.mp
      have hp1 : T ⊢ₛ' f₁ := ih1.mpr h1
      exact hp.map2 (prf.impE _) hp1
    · apply impI_of_is_complete hcomp
      intro hf1
      exact ih2.mpr (hsem (ih1.mp hf1))
  | _, bd_all f, ts, hn => by
    cases ts
    simp only [bdAppsRel]
    rw [show
        realizeSentence (term_model hcomp henk) (bd_all f) ↔
          ∀ x : (term_model hcomp henk).carrier,
            realizeBoundedFormula (DVec.cons x DVec.nil) f DVec.nil
        from realize_sentence_all]
    have hm : countQuantifiers f.fst + 1 < n :=
      by
      simp only [BoundedPreformula.fst, countQuantifiers] at hn
      omega
    refine ⟨fun hp x => ?_, fun hsem => ?_⟩
    · induction x using Quotient.ind with
      | _ t =>
        apply (term_model_subst0 hcomp henk f t).mp
        have h :=
          (n_ih (countQuantifiers f.fst + 1) hm (l' := 0) (subst0BoundedFormula f t)
                DVec.nil ?_).mp
            ?_
        · simp only [bdAppsRel] at h
          exact h
        · rw [subst0_bounded_formula_fst]
          rw [count_quantifiers_subst]
          exact Nat.lt_succ_self _
        · simp only [bdAppsRel]
          refine hp.map (fun pall => ?_)
          rw [subst0_bounded_formula_fst]
          exact prf.allE₂ f.fst t.fst pall
    · by_contra H
      obtain ⟨t, ht⟩ := find_counterexample_of_henkin hcomp henk f H
      have hsem_t := hsem (term_mk T t)
      have hsubst :
        realizeSentence (term_model hcomp henk) (subst0BoundedFormula f t) :=
        (term_model_subst0 hcomp henk f t).mpr hsem_t
      have h :=
        (n_ih (countQuantifiers f.fst + 1) hm (l' := 0) (subst0BoundedFormula f t)
              DVec.nil ?_).mpr
          ?_
      · simp only [bdAppsRel] at h
        apply hcomp.1
        exact ht.map2 (fun pn p => prf.impE _ pn p) h
      · rw [subst0_bounded_formula_fst]
        rw [count_quantifiers_subst]
        exact Nat.lt_succ_self _
      · simp only [bdAppsRel]
        exact hsubst

/-- The key term-model satisfaction iff (src/fol.lean:2634-2670).
-/
private lemma term_model_ssatisfied_iff {L : Language.{u}} {T : SentTheory L}
    (hcomp : T.isComplete) (henk : hasEnoughConstants T) {n} :
    ∀ {l} (f : presentence L l) (ts : DVec (closedTerm L) l)
      (_ : countQuantifiers f.fst < n),
      ((T ⊢ₛ' bdAppsRel f ts) ↔
        realizeSentence (term_model hcomp henk) (bdAppsRel f ts)) :=
  by
  induction n using Nat.strong_induction_on with
  | _ n n_ih =>
    intro l f ts hn
    exact term_model_ssatisfied_iff_struct hcomp henk n n_ih f ts hn

/-- The term model satisfies T (src/fol.lean:2672) -/
lemma term_model_ssatisfied {L : Language.{u}} {T : SentTheory L} (hcomp : T.isComplete)
    (henk : hasEnoughConstants T) : allRealizeSentence (term_model hcomp henk) T :=
  by
  intro f hf
  have hprov : T ⊢ₛ' bdAppsRel f (DVec.nil : DVec (closedTerm L) 0) :=
    by
    simp only [bdAppsRel]
    exact ⟨prf.axm (Set.mem_image_of_mem _ hf)⟩
  have h :=
    (term_model_ssatisfied_iff hcomp henk (n := countQuantifiers f.fst + 1) f DVec.nil
          (Nat.lt_succ_self _)).mp
      hprov
  simp only [bdAppsRel] at h
  exact h

/-- The reduct of the term model of the complete henkinization
satisfies T -/
@[simp]
lemma reduct_of_complete_henkinization_models_T {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) :
    Lhom.reduct (@henkinLanguageCanonicalMap L 0)
        (term_model (completion_of_henkinization_complete hT)
          (completion_of_henkinization_is_henkin hT)) ⊨ₜ
      T :=
  by
  apply
    Lhom.reduct_all_ssatisfied
      (henkin_language_canonical_map_inj 0)
        -- Goal: all_realize_sentence (term_model ...) ((hcm
          -- 0).on_sentence '' T)
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  apply term_model_ssatisfied
  apply completion_of_henkinization_contains hT
  simp only [henkinization, TInfty]
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem _ hf₀⟩

/-- Given ψ ∈ T, the term model satisfies ψ -/
@[simp]
lemma reduct_of_complete_henkinization_satisfies {L : Language.{u}} {T : SentTheory L}
    (hT : T.isConsistent) (ψ : sentence L) (hψ : ψ ∈ T) :
    Lhom.reduct (@henkinLanguageCanonicalMap L 0)
        (term_model (completion_of_henkinization_complete hT)
          (completion_of_henkinization_is_henkin hT)) ⊨ₘ
      ψ :=
  reduct_of_complete_henkinization_models_T hT hψ

end Fol

end NFChoice
