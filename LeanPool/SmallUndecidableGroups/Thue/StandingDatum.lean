/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.FixedSeed
public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.PriorityReflection
public import Mathlib.Tactic.FinCases

/-!
The fixed machine-to-Thue seed and Matiyasevich's proved compression theorem
together supply the exact three-relation binary input used by the host-group
construction.
-/

@[expose] public section

namespace Undecidability
namespace Thue

/-- Matiyasevich's fixed-target binary three-relation system, derived from
the fixed universal-machine seed. -/
theorem has_undecidable_three_rule_system :
    Matiyasevich1993.HasUndecidableThreeRuleSystem := by
  obtain ⟨seed⟩ := FixedMachine.exists_finiteFixedTargetSeed
  exact Matiyasevich1993.has_undecidable_three_rule_system_of_compression
    Matiyasevich1993.Compression.compressionTheorem seed

end Thue
end Undecidability

namespace Undecidability

namespace Thue

/-- `η(x) = s₁s₂²s₁` and `η(y) = s₁s₂³s₁`. -/
def etaLetter (a : Fin 2) : List (Fin 2) :=
  if a = 0 then
    [(0 : Fin 2), 1, 1, 0]
  else
    [(0 : Fin 2), 1, 1, 1, 0]

/-- The synchronizing monoid homomorphism, represented on lists. -/
def eta (w : List (Fin 2)) : List (Fin 2) :=
  w.flatMap etaLetter

/-- The left-hand words of the three rules after the standing binary encoding. -/
def encodedF (U₃ : List (Fin 2)) : Fin 3 → List (Fin 2) :=
  fun i => eta (baseF U₃ i)

/-- The right-hand words of the three rules after the standing binary encoding. -/
def encodedE (V₃ : List (Fin 2)) : Fin 3 → List (Fin 2) :=
  fun i => eta (baseE V₃ i)

/-- The three-rule Thue system specified by indexed left-hand and right-hand words. -/
def systemOf
    (F E : Fin 3 → List (Fin 2)) : ThueSystem (Fin 2) :=
  Set.range fun i => (F i, E i)

/-- The standing binary Thue system obtained by encoding the three base rules. -/
def encodedSystem (U₃ V₃ : List (Fin 2)) : ThueSystem (Fin 2) :=
  systemOf (encodedF U₃) (encodedE V₃)

/-- A two-letter positive word contains both alphabet symbols. -/
def ContainsBoth (w : List (Fin 2)) : Prop :=
  (0 : Fin 2) ∈ w ∧ (1 : Fin 2) ∈ w

theorem containsBoth_ne_nil {w : List (Fin 2)} (h : ContainsBoth w) :
    w ≠ [] := by
  intro hw
  subst w
  simp [ContainsBoth] at h

/-- Evaluate a positive two-letter word at two elements of a group. -/
def evalPositive {G : Type*} [Group G]
    (s₁ s₂ : G) (w : List (Fin 2)) : G :=
  (w.map fun i => if i = 0 then s₁ else s₂).prod

/-- The three binary rule pairs and their fixed target word. -/
structure BinaryRuleWords where
  /-- The three left sides of the rewriting rules. -/
  F : Fin 3 → List (Fin 2)
  /-- The corresponding right sides. -/
  E : Fin 3 → List (Fin 2)
  /-- The fixed word whose reachability is tested. -/
  P : List (Fin 2)

/--
The exact Thue-system interface used by the remainder of the construction.
The fields correspond to properties (a), (b), and (c) at the beginning
of Section 2 of the paper.
-/
structure StandingDatum extends BinaryRuleWords where
  F_nonempty : ∀ i, F i ≠ []
  E_nonempty : ∀ i, E i ≠ []
  F_support : ∀ i, ContainsBoth (F i)
  E_support : ∀ i, ContainsBoth (E i)
  P_support : ContainsBoth P
  undecidable :
    ¬ ComputablePred fun Q : List (Fin 2) =>
      ThueEq (systemOf F E) Q P
  kill :
    ∀ {G : Type} [Group G] (s₁ s₂ : G),
      s₂ = s₁⁻¹ →
      evalPositive s₁ s₂ (F 1) = evalPositive s₁ s₂ (E 1) →
      s₁ = 1 ∧ s₂ = 1

/-- The synchronizing code is computable. -/
theorem eta_computable : Computable eta :=
  (Primrec.list_flatMap Primrec.id
    ((Primrec.dom_finite etaLetter).comp₂ Primrec₂.right)).to_comp

@[simp]
theorem eta_cons (a : Fin 2) (w : List (Fin 2)) :
    eta (a :: w) = etaLetter a ++ eta w := by
  simp [eta]

/-- An occurrence of the initial marker `011` cannot start strictly inside a
codeword.  This is the finite check at the heart of synchronization. -/
private theorem eta_boundary_edge
    (a : Fin 2) (l bs tail w : List (Fin 2))
    (hc : etaLetter a = l ++ bs)
    (heq : [(0 : Fin 2), 1, 1] ++ tail = bs ++ eta w) :
    l = [] ∨ bs = [] := by
  fin_cases a
  · rcases l with _ | ⟨x, l⟩
    · simp
    · rcases l with _ | ⟨y, l⟩
      · simp only [etaLetter, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.cons_append,
        List.nil_append, List.cons.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp at heq
      · rcases l with _ | ⟨z, l⟩
        · simp only [etaLetter, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.cons_append,
          List.nil_append, List.cons.injEq] at hc
          rcases hc with ⟨rfl, rfl, rfl⟩
          simp at heq
        · rcases l with _ | ⟨q, l⟩
          · simp only [etaLetter, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.cons_append,
            List.nil_append, List.cons.injEq] at hc
            rcases hc with ⟨rfl, rfl, rfl, rfl⟩
            cases w with
            | nil => simp [eta] at heq
            | cons b w => fin_cases b <;> simp [eta, etaLetter] at heq
          · rcases l with _ | ⟨p, l⟩
            · simp only [etaLetter, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.cons_append,
              List.nil_append, List.cons.injEq, List.nil_eq] at hc
              exact Or.inr hc.2.2.2.2
            · simp [etaLetter] at hc
  · rcases l with _ | ⟨x, l⟩
    · simp
    · rcases l with _ | ⟨y, l⟩
      · simp only [etaLetter, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, zero_add,
        OfNat.ofNat_ne_one, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp at heq
      · rcases l with _ | ⟨z, l⟩
        · simp only [etaLetter, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, zero_add,
          OfNat.ofNat_ne_one, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq]
          at hc
          rcases hc with ⟨rfl, rfl, rfl⟩
          simp at heq
        · rcases l with _ | ⟨q, l⟩
          · simp only [etaLetter, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, zero_add,
            OfNat.ofNat_ne_one, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq]
            at hc
            rcases hc with ⟨rfl, rfl, rfl, rfl⟩
            simp at heq
          · rcases l with _ | ⟨p, l⟩
            · simp only [etaLetter, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, zero_add,
              OfNat.ofNat_ne_one, ↓reduceIte, List.cons_append, List.nil_append,
              List.cons.injEq] at hc
              rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
              cases w with
              | nil => simp [eta] at heq
              | cons b w => fin_cases b <;> simp [eta, etaLetter] at heq
            · rcases l with _ | ⟨r, l⟩
              · simp only [etaLetter, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, zero_add,
                OfNat.ofNat_ne_one, ↓reduceIte, List.cons_append, List.nil_append,
                List.cons.injEq, List.nil_eq] at hc
                exact Or.inr hc.2.2.2.2.2
              · simp [etaLetter] at hc

/-- Every `011` marker in an encoded word lies at a codeword boundary. -/
private theorem eta_marker_boundary {W l tail : List (Fin 2)}
    (h : eta W = l ++ [(0 : Fin 2), 1, 1] ++ tail) :
    ∃ L R, W = L ++ R ∧ l = eta L := by
  induction W generalizing l tail with
  | nil => simp [eta] at h
  | cons a W ih =>
      rw [eta_cons] at h
      have h' : etaLetter a ++ eta W =
          l ++ ([(0 : Fin 2), 1, 1] ++ tail) := by
        simpa only [List.append_assoc] using h
      rcases List.append_eq_append_iff.mp h' with
        ⟨as, hl, hs⟩ | ⟨bs, hc, ht⟩
      · obtain ⟨L, R, hW, has⟩ := ih (by
          simpa only [List.append_assoc] using hs)
        refine ⟨a :: L, R, ?_, ?_⟩
        · simp [hW]
        · simp [hl, has]
      · have hedge : l = [] ∨ bs = [] :=
          eta_boundary_edge a l bs tail W hc ht
        rcases hedge with rfl | rfl
        · exact ⟨[], a :: W, by simp, by simp [eta]⟩
        · exact ⟨[a], W, by simp, by simpa [eta] using hc.symm⟩

/-- The synchronizing code reflects the prefix relation. -/
private theorem eta_prefix {X W r : List (Fin 2)}
    (h : eta W = eta X ++ r) :
    ∃ R, W = X ++ R ∧ r = eta R := by
  induction X generalizing W r with
  | nil => exact ⟨W, by simp, by simpa [eta] using h.symm⟩
  | cons a X ih =>
      cases W with
      | nil =>
          fin_cases a <;> simp [eta, etaLetter] at h
      | cons b W =>
          rw [eta_cons, eta_cons, List.append_assoc] at h
          fin_cases a <;> fin_cases b <;> simp only [etaLetter, Fin.zero_eta, Fin.isValue,
            ↓reduceIte, List.cons_append,
            List.nil_append, List.cons.injEq, true_and, Fin.mk_one, Fin.one_eq_zero_iff,
            zero_add, OfNat.ofNat_ne_one, false_and, and_false, Fin.zero_eq_one_iff] at h
          · obtain ⟨R, hW, hr⟩ := ih h
            exact ⟨R, by simp [hW], hr⟩
          · obtain ⟨R, hW, hr⟩ := ih h
            exact ⟨R, by simp [hW], hr⟩

/-- A nonempty encoded word can occur in another encoded word only at codeword
boundaries, and both surrounding contexts are themselves encoded. -/
private theorem eta_occurrence {W X l r : List (Fin 2)} (hX : X ≠ [])
    (h : eta W = l ++ eta X ++ r) :
    ∃ L R, W = L ++ X ++ R ∧ l = eta L ∧ r = eta R := by
  cases X with
  | nil => contradiction
  | cons a X =>
      rw [eta_cons, ← List.append_assoc] at h
      have hm : eta W = l ++ [(0 : Fin 2), 1, 1] ++
          ((etaLetter a).drop 3 ++ eta X ++ r) := by
        fin_cases a <;> simpa [etaLetter, List.drop] using h
      obtain ⟨L, W', hW, hl⟩ := eta_marker_boundary hm
      subst W
      rw [hl] at h
      have hp : eta W' = eta (a :: X) ++ r := by
        simpa only [eta, List.flatMap_cons, List.flatMap_append,
          List.append_assoc, List.append_cancel_left_eq] using h
      obtain ⟨R, hW', hr⟩ := eta_prefix hp
      exact ⟨L, R, by simp [hW'], hl, hr⟩

private theorem eta_injective : Function.Injective eta := by
  intro X Y h
  obtain ⟨R, hY, hR⟩ :=
    eta_prefix (W := Y) (X := X) (r := []) (by simpa using h.symm)
  have : R = [] := by
    cases R with
    | nil => rfl
    | cons a R => fin_cases a <;> simp [eta, etaLetter] at hR
  subst R
  simpa using hY.symm

theorem baseF_nonempty (U₃ : List (Fin 2)) (hU₃ : U₃ ≠ []) :
    ∀ i, baseF U₃ i ≠ [] := by
  intro i
  fin_cases i <;> simp [baseF, hU₃]

theorem baseE_nonempty (V₃ : List (Fin 2)) (hV₃ : V₃ ≠ []) :
    ∀ i, baseE V₃ i ≠ [] := by
  intro i
  fin_cases i <;> simp [baseE, hV₃]

private theorem thueStep_encode (U₃ V₃ : List (Fin 2))
    {X Y : List (Fin 2)} :
    ThueStep (baseSystem U₃ V₃) X Y →
      ThueStep (encodedSystem U₃ V₃) (eta X) (eta Y) := by
  rintro ⟨l, r, x, y, ⟨i, hxy⟩, h⟩
  injection hxy with hx hy
  subst x
  subst y
  refine ⟨eta l, eta r, eta (baseF U₃ i), eta (baseE V₃ i), ?_, ?_⟩
  · exact ⟨i, rfl⟩
  · rcases h with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · exact Or.inl ⟨by simpa [eta] using congrArg eta hX,
        by simpa [eta] using congrArg eta hY⟩
    · exact Or.inr ⟨by simpa [eta] using congrArg eta hX,
        by simpa [eta] using congrArg eta hY⟩

private theorem thueStep_decode (U₃ V₃ : List (Fin 2))
    (hU₃ : U₃ ≠ []) (hV₃ : V₃ ≠ []) {X W : List (Fin 2)}
    (h : ThueStep (encodedSystem U₃ V₃) (eta X) W) :
    ∃ Y, W = eta Y ∧ ThueStep (baseSystem U₃ V₃) X Y := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, h⟩
  simp only [encodedF, encodedE] at hxy
  injection hxy with hx hy
  subst x
  subst y
  rcases h with ⟨hX, hW⟩ | ⟨hX, hW⟩
  · obtain ⟨L, R, hX', hl, hr⟩ :=
      eta_occurrence (baseF_nonempty U₃ hU₃ i) hX
    refine ⟨L ++ baseE V₃ i ++ R, ?_, ?_⟩
    · calc
        W = l ++ eta (baseE V₃ i) ++ r := hW
        _ = eta (L ++ baseE V₃ i ++ R) := by simp [eta, hl, hr]
    · exact ⟨L, R, baseF U₃ i, baseE V₃ i, ⟨i, rfl⟩,
        Or.inl ⟨hX', rfl⟩⟩
  · obtain ⟨L, R, hX', hl, hr⟩ :=
      eta_occurrence (baseE_nonempty V₃ hV₃ i) hX
    refine ⟨L ++ baseF U₃ i ++ R, ?_, ?_⟩
    · calc
        W = l ++ eta (baseF U₃ i) ++ r := hW
        _ = eta (L ++ baseF U₃ i ++ R) := by simp [eta, hl, hr]
    · exact ⟨L, R, baseF U₃ i, baseE V₃ i, ⟨i, rfl⟩,
        Or.inr ⟨hX', rfl⟩⟩

private theorem thueEq_decode (U₃ V₃ : List (Fin 2))
    (hU₃ : U₃ ≠ []) (hV₃ : V₃ ≠ []) {X W : List (Fin 2)}
    (h : ThueEq (encodedSystem U₃ V₃) (eta X) W) :
    ∃ Y, W = eta Y ∧ ThueEq (baseSystem U₃ V₃) X Y := by
  induction h with
  | refl => exact ⟨X, rfl, Relation.ReflTransGen.refl⟩
  | tail hab hbc ih =>
      obtain ⟨Y, rfl, hXY⟩ := ih
      obtain ⟨Z, rfl, hYZ⟩ := thueStep_decode U₃ V₃ hU₃ hV₃ hbc
      exact ⟨Z, rfl, hXY.tail hYZ⟩

/-- Every rewrite between encoded words uniquely decodes.  The nonemptiness
hypotheses exclude rules with an empty side, which could be applied away from a
codeword boundary. -/
theorem synchronization (U₃ V₃ X Y : List (Fin 2))
    (hU₃ : U₃ ≠ []) (hV₃ : V₃ ≠ []) :
    ThueEq (baseSystem U₃ V₃) X Y ↔
      ThueEq (encodedSystem U₃ V₃) (eta X) (eta Y) := by
  constructor
  · intro h
    exact h.lift eta (fun _ _ hstep => thueStep_encode U₃ V₃ hstep)
  · intro h
    obtain ⟨Z, hYZ, hXZ⟩ := thueEq_decode U₃ V₃ hU₃ hV₃ h
    have : Y = Z := eta_injective hYZ
    simpa [this] using hXZ

/-- A nonempty encoded word contains both `s₁` and `s₂`. -/
theorem eta_containsBoth {w : List (Fin 2)} (hw : w ≠ []) :
    ContainsBoth (eta w) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
      fin_cases a <;> simp [eta, etaLetter, ContainsBoth]

/-- The encoded second rule, together with `s₂ = s₁⁻¹`, kills both letters. -/
theorem encoded_second_rule_kills
    (U₃ V₃ : List (Fin 2))
    {G : Type} [Group G] (s₁ s₂ : G)
    (hinv : s₂ = s₁⁻¹)
    (hrel :
      evalPositive s₁ s₂ (encodedF U₃ 1) =
        evalPositive s₁ s₂ (encodedE V₃ 1)) :
    s₁ = 1 ∧ s₂ = 1 := by
  subst s₂
  simp only [evalPositive, Fin.isValue, encodedF, eta, baseF, Matrix.cons_val_one,
    Matrix.cons_val_zero, List.flatMap_cons, etaLetter, ↓reduceIte, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, inv_mul_cancel,
    mul_inv_cancel_left, mul_inv_cancel, encodedE, baseE, mul_eq_left, inv_eq_one] at hrel
  exact ⟨hrel, by simp [hrel]⟩

/-- Synchronization transfers fixed-target undecidability to the encoded system. -/
theorem encoded_undecidable
    {U₃ V₃ P₀ : List (Fin 2)}
    (hU₃ : U₃ ≠ []) (hV₃ : V₃ ≠ [])
    (h : ¬ ComputablePred fun Q : List (Fin 2) =>
      ThueEq (baseSystem U₃ V₃) Q P₀) :
    ¬ ComputablePred fun Q : List (Fin 2) =>
      ThueEq (encodedSystem U₃ V₃) Q (eta P₀) := by
  apply not_computablePred_of_manyOneReducible h
  exact ⟨eta, eta_computable, fun Q =>
    synchronization U₃ V₃ Q P₀ hU₃ hV₃⟩

/-- Package a nonempty Matiyasevich datum after synchronization. -/
noncomputable def encodedDatum
    (U₃ V₃ P₀ : List (Fin 2))
    (hU₃ : U₃ ≠ []) (hV₃ : V₃ ≠ []) (hP₀ : P₀ ≠ [])
    (hund : ¬ ComputablePred fun Q : List (Fin 2) =>
      ThueEq (baseSystem U₃ V₃) Q P₀) :
    StandingDatum := by
  have hbaseF := baseF_nonempty U₃ hU₃
  have hbaseE := baseE_nonempty V₃ hV₃
  refine
    { F := encodedF U₃
      E := encodedE V₃
      P := eta P₀
      F_nonempty := fun i =>
        containsBoth_ne_nil (by
          simpa [encodedF] using eta_containsBoth (hbaseF i))
      E_nonempty := fun i =>
        containsBoth_ne_nil (by
          simpa [encodedE] using eta_containsBoth (hbaseE i))
      F_support := fun i => by
        simpa [encodedF] using eta_containsBoth (hbaseF i)
      E_support := fun i => by
        simpa [encodedE] using eta_containsBoth (hbaseE i)
      P_support := eta_containsBoth hP₀
      undecidable := by
        simpa [encodedSystem] using encoded_undecidable hU₃ hV₃ hund
      kill := fun s₁ s₂ hinv hrel =>
        encoded_second_rule_kills U₃ V₃ s₁ s₂ hinv hrel }

/-- There is a standing datum satisfying exactly `(Und)`, `(Supp)`, and `(Kill)`. -/
theorem exists_standingDatum : Nonempty StandingDatum := by
  obtain ⟨U₃, V₃, P₀, hU₃, hV₃, hP₀, hund⟩ :=
    has_undecidable_three_rule_system
  exact ⟨encodedDatum U₃ V₃ P₀ hU₃ hV₃ hP₀ hund⟩

end Thue

end Undecidability
