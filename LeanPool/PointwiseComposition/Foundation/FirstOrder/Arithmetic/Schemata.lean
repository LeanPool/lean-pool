/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.TA.Basic

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Induction and least number schemata of Arithmetic

## References

- [HP98, §I.2(a), I.2.3]
-/

@[expose] public section

namespace FFL
namespace FirstOrder
namespace Arithmetic

section axioms

/-! ### Axiom formulas -/

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- The succ Ind construction in `FFL.FirstOrder.Arithmetic`. -/
def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “!φ 0 → (∀ x, !φ x → !φ(x + 1)) → ∀ x, !φ x”

/-- The order Ind construction in `FFL.FirstOrder.Arithmetic`. -/
def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

/-- The least Number construction in `FFL.FirstOrder.Arithmetic`. -/
def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

/-! ### Induction schemata -/

variable (L)

/-- The Induction Scheme construction in `FFL.FirstOrder.Arithmetic`. -/
def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  {ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ)}

/-- The 𝐈𝐎𝐩𝐞𝐧 construction in `𝐈𝐎𝐩𝐞𝐧`. -/
abbrev IOpen : ArithmeticTheory :=
  𝐏𝐀⁻ ∪ InductionScheme ℒₒᵣ Semiformula.Open

/-- The «term𝐈𝐎𝐩𝐞𝐧» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐈𝐎𝐩𝐞𝐧" => IOpen

/-- The Induction On Hierarchy construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev InductionOnHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝐏𝐀⁻ ∪ InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ s)

/-- The «term𝐈𝐍𝐃 » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐈𝐍𝐃 " => InductionOnHierarchy

/-- The ISigma construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev ISigma (s : ℕ) : ArithmeticTheory :=
  𝐈𝐍𝐃 Σ s

/-- The «term𝐈Σ » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐈Σ" => ISigma

/-- The «term𝐈Σ₀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐈Σ₀" => ISigma 0

/-- The IPi construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev IPi (s : ℕ) : ArithmeticTheory :=
  𝐈𝐍𝐃 Π s

/-- The «term𝐈Π » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐈Π" => IPi

/-- The «term𝐈Π₀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐈Π₀" => IPi 0

/-- The «term𝐈Σ₁» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐈Σ₁" => ISigma 1

/-- The «term𝐈Π₁» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐈Π₁" => IPi 1

/-- The 𝐏𝐀 construction in `𝐏𝐀`. -/
abbrev Peano : ArithmeticTheory :=
  𝐏𝐀⁻ ∪ InductionScheme ℒₒᵣ Set.univ

/-- The «term𝐏𝐀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐏𝐀" => Peano

variable {L}

/-! ### Least number schemata -/

/-- The Least Number Scheme construction in `FFL.FirstOrder.Arithmetic`. -/
def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  {ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ)}

/-- The Least Number On Hierarchy construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev LeastNumberOnHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝐏𝐀⁻ ∪ LeastNumberScheme (Arithmetic.Hierarchy Γ s)

/-- The «term𝐋 » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐋 " => LeastNumberOnHierarchy

/-- The LSigma construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev LSigma (s : ℕ) : ArithmeticTheory :=
  𝐋 Σ s

/-- The «term𝐋Σ » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐋Σ" => LSigma

/-- The LPi construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev LPi (s : ℕ) : ArithmeticTheory :=
  𝐋 Π s

/-- The «term𝐋Π » construction in `FFL.FirstOrder.Arithmetic`. -/
prefix:max "𝐋Π" => LPi

/-! ### Induction scheme lemmas -/

section

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma InductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_ofPred_eq, forall_exists_index, and_imp]; rintro
      φ hp rfl; exact ⟨φ, h hp, rfl⟩



lemma mem_InductionScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ C := by simpa [InductionScheme] using ⟨φ, hp, rfl⟩

lemma mem_IOpen_of_qfree {φ : ArithmeticSemiformula ℕ 1} (hp : φ.Open) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ Semiformula.Open := by exact ⟨φ, hp, rfl⟩

lemma ISigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈Σs₁ ⊆ 𝐈Σs₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈Σs₁ ≼ 𝐈Σs₂ :=
  Entailment.WeakerThan.ofSubset (ISigma_subset_mono h)

lemma ISigma_weakerThan_of_le_trans {T : ArithmeticTheory} {s₁ s₂} (h : s₁ ≤ s₂)
    (hT : 𝐈Σs₂ ≼ T) : 𝐈Σs₁ ≼ T :=
  Entailment.WeakerThan.trans (ISigma_weakerThan_of_le h) hT

end

/-! ### Least number scheme lemmas -/

section

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩;

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C :=
  ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐋 Γ s₁ ⊆ 𝐋 Γ s₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐋 Γ s₁ ≼ 𝐋 Γ s₂ :=
  Entailment.WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)

end

/-! ### Relations between the theories -/

instance : 𝐄𝐐 ℒₒᵣ ≼ 𝐈𝐍𝐃 Γ s :=
  have : 𝐄𝐐 ℒₒᵣ ≼ 𝐏𝐀⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝐄𝐐 ℒₒᵣ ≼ 𝐈𝐎𝐩𝐞𝐧 :=
  have : 𝐄𝐐 ℒₒᵣ ≼ 𝐏𝐀⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝐈𝐎𝐩𝐞𝐧 ≼ 𝐈𝐍𝐃 Γ s :=
  Entailment.WeakerThan.ofSubset <|
    Set.union_subset_union_right _ <| InductionScheme_subset Arithmetic.Hierarchy.of_open

instance : 𝐈Σ₀ ≼ 𝐈Σ₁ :=
  ISigma_weakerThan_of_le (by decide)

instance : 𝐈Σs ≼ 𝐏𝐀 :=
  Entailment.WeakerThan.ofSubset <|
    Set.union_subset_union_right _ <| InductionScheme_subset (by intros; trivial)

instance : 𝐏𝐀⁻ ≼ 𝐈𝐎𝐩𝐞𝐧 :=
  inferInstance

instance : 𝐈𝐎𝐩𝐞𝐧 ≼ 𝐈Σ₀ :=
  inferInstance

instance : 𝐈Σ₁ ≼ 𝐏𝐀 :=
  inferInstance

instance : 𝐄𝐐 ℒₒᵣ ≼ 𝐏𝐀 :=
  have : 𝐄𝐐 ℒₒᵣ ≼ 𝐏𝐀⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝐏𝐀⁻ ≼ 𝐋 Γ s :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝐄𝐐 ℒₒᵣ ≼ 𝐋 Γ s :=
  Entailment.WeakerThan.trans (inferInstance : 𝐄𝐐 ℒₒᵣ ≼ 𝐏𝐀⁻) inferInstance

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `𝐄𝐐 ℒₒᵣ ≼ T`, so instance search cannot infer it.
lemma eq_weakerThan_of_ISigma {T : ArithmeticTheory} {s : ℕ} [𝐈Σs ≼ T] : 𝐄𝐐 ℒₒᵣ ≼ T :=
  Entailment.WeakerThan.trans (inferInstance : 𝐄𝐐 ℒₒᵣ ≼ 𝐈Σ₀)
    (ISigma_weakerThan_of_le_trans (by omega) ‹𝐈Σs ≼ T›)

end axioms

section models

variable {V : Type*} [ORingStructure V]

namespace InductionScheme

variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ C]

private lemma induction_eval {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) (v : ℕ → V) :
    φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) → ∀ x, φ.Eval ![x] v :=
  by
  have : V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) :=
    Theory.models (T := InductionScheme _ C) V (by simpa using mem_InductionScheme_of_mem hp)
  revert v
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using this

@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end InductionScheme

namespace InductionOnHierarchy

section

variable (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s]

instance : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy Γ s) :=
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  models_of_subtheory this

lemma succ_induction {P : V → Prop} (hP : Γ-[s].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory this
  InductionScheme.succ_induction (P := P) (C := Hierarchy Γ s) (by
    rcases hP with ⟨φ, hp⟩
    have : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γ-[s].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory this
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using succ_induction
  · exact Γ
  · exact s
  · suffices Γ-[s].DefinablePred fun x ↦ ∀ y < x, P y by exact this
    exact HierarchySymbol.Definable.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => infer_instance

private lemma neg_succ_induction {P : V → Prop} (hP : Γ-[s].DefinablePred P) (nzero : ¬P 0)
    (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x :=
  by
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory this
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using succ_induction
    · exact Γ
    · exact s
    · suffices Γ-[s].DefinablePred fun x ↦ x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Definable.bcomp₁ (by definability)
    case zero => intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact
        (not_imp_not.mp <| nsucc (a - (x + 1)))
          (by
            rw [← Arithmetic.sub_sub, sub_add_self_of_le]
            · exact this
            · exact le_tsub_of_add_le_left hx)
    case inst => infer_instance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

instance models_InductionScheme_alt :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ.alt s) :=
  by
  suffices
    ∀ (φ : ArithmeticSemiformula ℕ 1),
      Hierarchy Γ.alt s φ →
        ∀ (f : ℕ → V),
          φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f
    by
    simp only [InductionScheme]
    refine Semantics.ModelsSet.setOf_iff.mpr ?_
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_rew_q,
      Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton] using this φ hφ
  intro φ hp v
  simpa using
    neg_succ_induction Γ s (P := fun x ↦ ¬φ.Eval ![x] v)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
        (by intro x; simp [← Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))

instance models_alt : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ.alt s :=
  by
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory this
  simp only [InductionOnHierarchy, Semantics.ModelsSet.union_iff];
  constructor <;> infer_instance

lemma least_number {P : V → Prop} (hP : Γ-[s].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  by
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory this
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using succ_induction
    · exact Γ.alt
    · exact s
    · suffices Γ.alt-[s].DefinablePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Definable.ball_blt (by definability)
      apply HierarchySymbol.Definable.not
      apply HierarchySymbol.Definable.bcomp₁ (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => infer_instance
  exact this (x + 1) x (by simp) h

end

section

variable (Γ : SigmaPiDelta) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Σ s]

lemma succ_induction_sigma {P : V → Prop} (hP : Γ-[s].DefinablePred P) (zero : P 0)
    (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | Σ => succ_induction Σ s hP zero succ
  | Π =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Π s := models_alt Σ s
    succ_induction Π s hP zero succ
  | ∆ => succ_induction Σ s hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γ-[s].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | Σ => order_induction Σ s hP ind
  | Π =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Π s := models_alt Σ s
    order_induction Π s hP ind
  | ∆ => order_induction Σ s hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γ-[s].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | Σ => least_number Σ s hP h
  | Π =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Π s := models_alt Σ s
    least_number Π s hP h
  | ∆ => least_number Σ s hP.of_delta h

end

instance [V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Σ s] : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s :=
  by
  rcases Γ
  · infer_instance
  · exact models_alt Σ s

instance [V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Π s] : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s :=
  by
  rcases Γ
  · exact models_alt Π s
  · infer_instance

lemma modISigmaOfLe {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝐈Σs₂] : V↓[ℒₒᵣ] ⊧* 𝐈Σs₁ :=
  models_of_ss inferInstance (ISigma_subset_mono h)

instance [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] : V↓[ℒₒᵣ] ⊧* 𝐈Σ₀ :=
  modISigmaOfLe (show 0 ≤ 1 from by simp)

instance [V↓[ℒₒᵣ] ⊧* 𝐈Σs] : V↓[ℒₒᵣ] ⊧* 𝐈Πs :=
  inferInstance

instance [V↓[ℒₒᵣ] ⊧* 𝐈Πs] : V↓[ℒₒᵣ] ⊧* 𝐈Σs :=
  inferInstance

lemma models_ISigma_iff_models_IPi {s} : V↓[ℒₒᵣ] ⊧* 𝐈Σs ↔ V↓[ℒₒᵣ] ⊧* 𝐈Πs :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V↓[ℒₒᵣ] ⊧* 𝐈Σs] : V↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s :=
  match Γ with
  | Σ => inferInstance
  | Π => inferInstance

end InductionOnHierarchy

@[elab_as_elim]
lemma ISigma0.succ_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₀] {P : V → Prop} (hP : Σ₀.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction Σ 0 hP zero succ

@[elab_as_elim]
lemma ISigma1.sigma1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] {P : V → Prop} (hP : Σ₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction Σ 1 hP zero succ

@[elab_as_elim]
lemma ISigma1.pi1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] {P : V → Prop} (hP : Π₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction Π 1 hP zero succ

@[elab_as_elim]
lemma ISigma0.order_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₀] {P : V → Prop} (hP : Σ₀-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction Σ 0 hP ind

@[elab_as_elim]
lemma ISigma1.sigma1_order_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] {P : V → Prop} (hP : Σ₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction Σ 1 hP ind

@[elab_as_elim]
lemma ISigma1.pi1_order_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] {P : V → Prop} (hP : Π₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction Π 1 hP ind

lemma ISigma0.least_number [V↓[ℒₒᵣ] ⊧* 𝐈Σ₀] {P : V → Prop} (hP : Σ₀-Predicate P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  InductionOnHierarchy.least_number Σ 0 hP h

@[elab_as_elim]
lemma ISigma1.succ_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction_sigma Γ 1 hP zero succ

@[elab_as_elim]
lemma ISigma1.order_induction [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP ind

instance [V↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := inferInstance
  models_of_subtheory this

instance [V↓[ℒₒᵣ] ⊧* 𝐈Σ₀] : V↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 :=
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₀ := inferInstance
  models_of_subtheory this

instance [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] : V↓[ℒₒᵣ] ⊧* 𝐈Σ₀ :=
  inferInstance

/-- The mod ISigma of le construction in `FFL.FirstOrder.Arithmetic`. -/
abbrev modISigmaOfLe {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝐈Σs₂] : V↓[ℒₒᵣ] ⊧* 𝐈Σ s₁ :=
  models_of_ss inferInstance (ISigma_subset_mono h)

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻`, so instance search cannot infer it.
lemma mod_paMinus_of_ISigma {s} [V↓[ℒₒᵣ] ⊧* 𝐈Σs] : V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₀ := modISigmaOfLe (Nat.zero_le s)
  inferInstance

instance [V↓[ℒₒᵣ] ⊧* 𝐏𝐀] : V↓[ℒₒᵣ] ⊧* 𝐈Σs :=
  have : V↓[ℒₒᵣ] ⊧* 𝐏𝐀 := inferInstance
  models_of_subtheory this

end models

lemma models_succInd (φ : ArithmeticSemiformula ℕ 1) : ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl :=
  by
  suffices
    ∀ f : ℕ → ℕ, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f
    by
    simpa [Semiformula.eval_univCl, succInd, models_iff, Matrix.constant_eq_singleton,
      Semiformula.eval_substs]
  intro e hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

instance models_ISigma (Γ s) : ℕ↓[ℒₒᵣ] ⊧* 𝐈𝐍𝐃 Γ s :=
  by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)

instance models_ISigmaZero : ℕ↓[ℒₒᵣ] ⊧* 𝐈Σ₀ :=
  inferInstance

instance models_ISigmaOne : ℕ↓[ℒₒᵣ] ⊧* 𝐈Σ₁ :=
  inferInstance

instance models_Peano : ℕ↓[ℒₒᵣ] ⊧* 𝐏𝐀 :=
  by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Peano, Semantics.ModelsSet.union_iff,
    PeanoMinus.instModelsSetStrucORingSentenceStrNat, true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)

instance sigmaOneSound_ISigmaOne : 𝐈Σ₁.SoundOnHierarchy Σ 1 :=
  inferInstance

instance sigmaOneSound_Peano : 𝐏𝐀.SoundOnHierarchy Σ 1 :=
  inferInstance

instance : Entailment.Consistent (𝐈𝐍𝐃 Γ s) :=
  (𝐈𝐍𝐃 Γ s).consistent_of_sound (Eq ⊥) rfl

instance : Entailment.Consistent 𝐏𝐀 :=
  𝐏𝐀.consistent_of_sound (Eq ⊥) rfl

instance : 𝐏𝐀 ≼ 𝐓𝐀 :=
  inferInstance

instance (T : ArithmeticTheory) [𝐏𝐀⁻ ≼ T] : 𝐑₀ ≼ T :=
  have : 𝐑₀ ≼ 𝐏𝐀⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝐈Σ₀ ≼ T] : 𝐏𝐀⁻ ≼ T :=
  have : 𝐏𝐀⁻ ≼ 𝐈Σ₀ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝐈Σ₁ ≼ T] : 𝐏𝐀⁻ ≼ T :=
  have : 𝐏𝐀⁻ ≼ 𝐈Σ₁ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : 𝐏𝐀⁻ ≼ T :=
  have : 𝐏𝐀⁻ ≼ 𝐏𝐀 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
