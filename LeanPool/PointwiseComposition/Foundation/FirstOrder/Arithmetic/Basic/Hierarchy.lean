/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Classical.Padding
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Basic.Model

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section
namespace FFL
namespace FirstOrder
namespace Arithmetic

variable {L : Language} [L.LT]

/-- The arithmetical hierarchy, starting with bounded formulas at level zero. -/
inductive Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | verum (Γ s n) : Hierarchy Γ s (⊤ : Semiformula L ξ n)
  | falsum (Γ s n) : Hierarchy Γ s (⊥ : Semiformula L ξ n)
  | rel (Γ s) {k} (r : L.Rel k) (v) : Hierarchy Γ s (Semiformula.rel r v)
  | nrel (Γ s) {k} (r : L.Rel k) (v) : Hierarchy Γ s (Semiformula.nrel r v)
  |
  and {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋏ ψ)
  |
  or {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋎ ψ)
  |
  ball {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀¹[“x. x < !!t”] φ)
  |
  bexs {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃¹[“x. x < !!t”] φ)
  | exs {s n} {φ : Semiformula L ξ (n + 1)} : Hierarchy Σ (s + 1) φ → Hierarchy Σ (s + 1) (∃¹ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} : Hierarchy Π (s + 1) φ → Hierarchy Π (s + 1) (∀¹ φ)
  | sigma {s n} {φ : Semiformula L ξ (n + 1)} : Hierarchy Π s φ → Hierarchy Σ (s + 1) (∃¹ φ)
  | pi {s n} {φ : Semiformula L ξ (n + 1)} : Hierarchy Σ s φ → Hierarchy Π (s + 1) (∀¹ φ)
  |
  dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Π (s + 1) φ → Hierarchy Σ (s + 1 + 1) (∀¹ φ)
  |
  dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Σ (s + 1) φ → Hierarchy Π (s + 1 + 1) (∃¹ φ)

/-- The Delta Zero construction in `FFL.FirstOrder.Arithmetic`. -/
def DeltaZero (φ : Semiformula L ξ n) : Prop :=
  Hierarchy Σ 0 φ

attribute [simp] Hierarchy.verum Hierarchy.falsum Hierarchy.rel Hierarchy.nrel

namespace Hierarchy

@[simp]
lemma and_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋏ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  ⟨by
    generalize hr : φ ⋏ ψ = r
    intro H
    induction H <;> try simp only [reduceCtorEq, Semiformula.and_inj, FirstOrder.ball,
      Matrix.vecCons_empty_eq_singleton, FirstOrder.bexs] at hr
    case and =>
      rcases hr with ⟨rfl, rfl⟩
      constructor <;> assumption,
    by rintro ⟨hp, hq⟩; exact Hierarchy.and hp hq⟩

@[simp]
lemma or_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋎ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  ⟨by
    generalize hr : φ ⋎ ψ = r
    intro H
    induction H <;> try simp only [reduceCtorEq, Semiformula.or_inj, FirstOrder.ball,
      Matrix.vecCons_empty_eq_singleton, FirstOrder.bexs] at hr
    case or =>
      rcases hr with ⟨rfl, rfl⟩
      constructor <;> assumption,
    by rintro ⟨hp, hq⟩; exact Hierarchy.or hp hq⟩

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    Hierarchy Γ s (Matrix.conj φ) ↔ ∀ i, Hierarchy Γ s (φ i) := by
  induction m <;> simp only [Matrix.conj, verum, IsEmpty.forall_iff, Matrix.vecTail,
    Nat.succ_eq_add_one, and_iff, Function.comp_apply, *]
  · exact ⟨by rintro ⟨hz, hs⟩ i; cases i using Fin.cases <;> simp [*],
           by intro h; exact ⟨h 0, fun _ => h _⟩⟩

lemma zero_eq_alt {φ : Semiformula L ξ n} : Hierarchy Γ 0 φ → Hierarchy Γ.alt 0 φ :=
  by
  generalize hz : 0 = z
  rw [eq_comm] at hz
  intro h
  induction h <;> try simp only [verum, falsum, rel, nrel, and_iff, or_iff,
    Matrix.vecCons_empty_eq_singleton, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    and_self] at hz ⊢
  case and _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case or _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case ball pos _ ih => exact ball pos (ih hz)
  case bexs pos _ ih => exact bexs pos (ih hz)

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} : Hierarchy Π 0 φ ↔ Hierarchy Σ 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} : Hierarchy Γ 0 φ ↔ Hierarchy Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [Polarity.eq_sigma, Polarity.eq_pi, pi_zero_iff_sigma_zero]

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} : Hierarchy Γ 0 φ ↔ DeltaZero φ := by
  simpa [DeltaZero, pi_zero_iff_sigma_zero] using zero_iff

@[simp]
lemma alt_zero_iff_zero {φ : Semiformula L ξ n} : Hierarchy Γ.alt 0 φ ↔ Hierarchy Γ 0 φ := by
  rcases Γ <;> simp [Polarity.eq_sigma, Polarity.eq_pi, pi_zero_iff_sigma_zero]

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} : Hierarchy Γ s φ → ∀ Γ', Hierarchy Γ' (s + 1) φ
  | verum _ _ _, _ => verum _ _ _
  | falsum _ _ _, _ => falsum _ _ _
  | rel _ _ r v, _ => rel _ _ r v
  | nrel _ _ r v, _ => nrel _ _ r v
  | and hp hq, _ => and (hp.accum _) (hq.accum _)
  | or hp hq, _ => or (hp.accum _) (hq.accum _)
  | ball pos hp, _ => ball pos (hp.accum _)
  | bexs pos hp, _ => bexs pos (hp.accum _)
  | all hp, Γ => by
    cases Γ
    · exact hp.dummy_sigma
    · exact (hp.accum Π).all
  | exs hp, Γ => by
    cases Γ
    · exact (hp.accum Σ).exs
    · exact hp.dummy_pi
  | sigma hp, Γ => by
    cases Γ
    · exact ((hp.accum Σ).accum Σ).exs
    · exact (hp.accum Σ).dummy_pi
  | pi hp, Γ => by
    cases Γ
    · exact (hp.accum Π).dummy_sigma
    · exact ((hp.accum Π).accum Π).all
  | dummy_sigma hp, Γ => by
    cases Γ
    · exact (hp.accum Π).dummy_sigma
    · exact ((hp.accum Π).accum Π).all
  | dummy_pi hp, Γ => by
    cases Γ
    · exact ((hp.accum Σ).accum Σ).exs
    · exact (hp.accum Σ).dummy_pi

lemma strict_mono {Γ s} {φ : Semiformula L ξ n} (hp : Hierarchy Γ s φ) (Γ') {s'} (h : s < s') :
    Hierarchy Γ' s' φ :=
  by
  have : ∀ d, Hierarchy Γ' (s + d + 1) φ := by
    intro d
    induction d with
    | zero => simpa using hp.accum Γ'
    | succ s ih => simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by
        simpa [Nat.succ_add] using Nat.add_sub_of_le h] using
    this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n} (hp : Hierarchy Γ s φ) (h : s ≤ s') :
    Hierarchy Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {b b'} {s : ℕ} {φ : Semiformula L ξ n} (hp : Hierarchy b 0 φ) :
    Hierarchy b' s φ :=
  by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp b' pos

section

variable {L : Language}

@[simp] lemma equal [L.Eq] [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma lt [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two, Semiformula.Operator.LT.sentence_eq]

@[simp] lemma le [L.Eq] [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.LE.sentence_eq]

end

lemma neg {φ : Semiformula L ξ n} : Hierarchy Γ s φ → Hierarchy Γ.alt s (∼φ) :=
  by
  intro h; induction h <;> try simp only [LogicalNeutral.DeMorgan.verum, falsum,
    LogicalNeutral.DeMorgan.falsum, verum, Semiformula.neg_rel, nrel, Semiformula.neg_nrel, rel,
    LogicalConnective.DeMorgan.and, or_iff, and_self, *, LogicalConnective.DeMorgan.or, and_iff,
    Matrix.vecCons_empty_eq_singleton, Semiformula.neg_ball, Semiformula.neg_bexs,
    Polarity.alt_sigma, Semiformula.neg_ex, Polarity.alt_pi, Semiformula.neg_all]
  case bexs pos _ ih => exact ball pos ih
  case ball pos _ ih => exact bexs pos ih
  case exs ih => exact all ih
  case all ih => exact exs ih
  case sigma ih => exact pi ih
  case pi ih => exact sigma ih
  case dummy_pi ih => exact dummy_sigma ih
  case dummy_sigma ih => exact dummy_pi ih

@[simp]
lemma neg_iff {φ : Semiformula L ξ n} : Hierarchy Γ s (∼φ) ↔ Hierarchy Γ.alt s φ :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

@[simp]
lemma imp_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⇒ₗ ψ) ↔ (Hierarchy Γ.alt s φ ∧ Hierarchy Γ s ψ) := by
  simp [Semiformula.imp_eq]

@[simp]
lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) : Hierarchy Γ s (∀¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  ⟨by
    generalize hq : (∀¹[“x. x < !!t”] φ) = ψ
    intro H
    induction H <;> try simp only [FirstOrder.ball, Matrix.vecCons_empty_eq_singleton,
      reduceCtorEq, Semiformula.all_inj, Semiformula.imp_inj,
      Semiformula.Operator.LT.lt_inj, true_and, FirstOrder.bexs] at hq
    case ball φ t pt hp ih =>
      rcases hq with ⟨rfl, rfl⟩
      assumption
    case all hp ih =>
      rcases hq with rfl
      simpa using hp
    case pi s _ _ hp ih =>
      rcases hq with rfl
      exact (show Hierarchy Σ s φ from by simpa using hp).accum _
    case dummy_sigma hp _ =>
      rcases hq with rfl
      simp at hp
      exact hp.accum _,
    by intro hp; exact hp.ball ht⟩

@[simp]
lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) : Hierarchy Γ s (∃¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  ⟨by
    generalize hq : (∃¹[“x. x < !!t”] φ) = ψ
    intro H
    induction H <;> try simp only [FirstOrder.bexs, Matrix.vecCons_empty_eq_singleton,
      reduceCtorEq, FirstOrder.ball, Semiformula.exs_inj, Semiformula.and_inj,
      Semiformula.Operator.LT.lt_inj, true_and] at hq
    case bexs φ t pt hp ih =>
      rcases hq with ⟨rfl, rfl⟩
      assumption
    case exs hp ih =>
      rcases hq with rfl
      simpa using hp
    case sigma s _ _ hp ih =>
      rcases hq with rfl
      exact (show Hierarchy Π s φ from by simpa using hp).accum _
    case dummy_pi hp _ =>
      rcases hq with rfl
      simp at hp
      exact hp.accum _,
    by intro hp; exact hp.bexs ht⟩

@[simp]
lemma ballLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.ballLT t) ↔ Hierarchy Γ s φ := by simp [Semiformula.ballLT]

@[simp]
lemma bexsLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.bexsLT t) ↔ Hierarchy Γ s φ := by simp [Semiformula.bexsLT]

@[simp]
lemma ballLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ n} : Hierarchy Γ s (φ.ballLTSucc t) ↔ Hierarchy Γ s φ := by
  simp [Semiformula.ballLTSucc]

@[simp]
lemma bexsLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ n} : Hierarchy Γ s (φ.bexsLTSucc t) ↔ Hierarchy Γ s φ := by
  simp [Semiformula.bexsLTSucc]

lemma pi_of_pi_all {φ : Semiformula L ξ (n + 1)} : Hierarchy Π s (∀¹ φ) → Hierarchy Π s φ :=
  by
  generalize hr : ∀¹ φ = r
  generalize hb : (Π : Polarity) = Γ
  intro H
  cases H <;> try simp only [reduceCtorEq, FirstOrder.ball,
    Matrix.vecCons_empty_eq_singleton, Semiformula.all_inj, FirstOrder.bexs] at hr
  case ball => rcases hr with rfl; simpa
  case all => rcases hr with rfl; simpa
  case pi hp => rcases hr with rfl; exact hp.accum _
  case dummy_sigma hp => rcases hr with rfl; exact hp.accum _

@[simp]
lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Π (s + 1) (∀¹ φ) ↔ Hierarchy Π (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

@[simp]
lemma allItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy Π (s + 1) (∀¹^[k] φ) ↔ Hierarchy Π (s + 1) φ := by
  induction k <;> simp [allItr_succ, *]

lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Σ s (∃¹ φ) → Hierarchy Σ s φ :=
  by
  generalize hr : ∃¹ φ = r
  generalize hb : (Σ : Polarity) = Γ
  intro H
  cases H <;> try simp only [reduceCtorEq, FirstOrder.ball,
    Matrix.vecCons_empty_eq_singleton, FirstOrder.bexs, Semiformula.exs_inj] at hr
  case bexs => rcases hr with rfl; simpa
  case exs => rcases hr with rfl; simpa
  case sigma hp => rcases hr with rfl; exact hp.accum _
  case dummy_pi hp => rcases hr with rfl; exact hp.accum _

@[simp]
lemma sigma_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Σ (s + 1) (∃¹ φ) ↔ Hierarchy Σ (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

@[simp]
lemma exsItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy Σ (s + 1) (∃¹^[k] φ) ↔ Hierarchy Σ (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *]

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s φ → Hierarchy Γ s (ω ▹ φ) :=
  by
  intro h; induction h generalizing n₂ <;> try simp only [LogicalConnective.HomClass.map_top,
    verum, LogicalConnective.HomClass.map_bot, falsum, Semiformula.rew_rel_eq_comp, rel,
    Semiformula.rew_nrel_eq_comp, nrel, LogicalConnective.HomClass.map_and, and_iff, and_self, *,
    LogicalConnective.HomClass.map_or, or_iff, Matrix.vecCons_empty_eq_singleton,
    Rewriting.smul_ball, Rew.hom_finitary2, Rew.q_bvar_zero, Rew.q_positive_iff, ball_iff,
    Rewriting.smul_bexs, bexs_iff, Rewriting.app_exs, sigma_iff, Rewriting.app_all, all_iff]
  case sigma ih => exact (ih _).accum _
  case pi ih => exact (ih _).accum _
  case dummy_pi ih => exact (ih _).dummy_pi
  case dummy_sigma ih => exact (ih _).dummy_sigma

@[simp]
lemma rew_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s (ω ▹ φ) ↔ Hierarchy Γ s φ :=
  by
  constructor
  · generalize eq : ω ▹ φ = ψ
    intro hq
    induction hq generalizing φ n₁ <;>
      try
        simp only [Semiformula.eq_top_iff, Semiformula.eq_bot_iff, Semiformula.eq_rel_iff,
          Semiformula.eq_nrel_iff, Semiformula.eq_and_iff, exists_and_left,
          Semiformula.eq_or_iff, Matrix.vecCons_empty_eq_singleton, Semiformula.eq_ball_iff,
          Semiformula.eq_bexs_iff, Semiformula.eq_exs_iff, Semiformula.eq_all_iff] at eq
    case verum => rcases eq with rfl; simp
    case falsum => rcases eq with rfl; simp
    case rel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case nrel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case ball pos _
      ih =>
      simp only [Rew.eq_lt_iff, Rew.q_eq_zero_iff, Matrix.vecCons_empty_eq_singleton,
        exists_and_left, exists_eq_left] at eq
      rcases eq with ⟨hp, ⟨u, rfl, s, hs, rfl⟩, φ, rfl, rfl⟩
      simpa [show u.Positive from by simpa using pos] using ih rfl
    case bexs pos _
      ih =>
      simp only [Rew.eq_lt_iff, Rew.q_eq_zero_iff, Matrix.vecCons_empty_eq_singleton,
        exists_and_left, exists_eq_left] at eq
      rcases eq with ⟨hp, ⟨u, rfl, s, hs, rfl⟩, φ, rfl, rfl⟩
      simpa [show u.Positive from by simpa using pos] using ih rfl
    case all ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).all
    case exs ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).exs
    case pi ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).pi
    case sigma ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).sigma
    case dummy_sigma ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).dummy_sigma
    case dummy_pi ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact (ih rfl).dummy_pi
  · exact rew _

lemma exsClosure :
    {n : ℕ} →
      {φ : Semiformula L ξ n} → Hierarchy Σ (s + 1) φ → Hierarchy Σ (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃¹ φ) hp.exs

instance : LogicalConnective.AndOrClosed (Hierarchy Γ s : Semiformula L ξ k → Prop)
    where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicalConnective.Closed (Hierarchy Γ 0 : Semiformula L ξ k → Prop)
    where
  not := by simp [neg_iff]
  imply := by simp [Semiformula.imp_eq, neg_iff]; tauto

lemma of_open {φ : Semiformula L ξ n} : φ.Open → Hierarchy Γ s φ :=
  by
  induction φ using Semiformula.rec' <;> simp only [verum, implies_true, falsum, rel, nrel,
    Semiformula.open_and, and_iff, and_imp, Semiformula.open_or, or_iff, Semiformula.not_open_all,
    IsEmpty.forall_iff, Semiformula.not_open_exs]
  case hand ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩
  case hor ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩

variable {L : Language} [L.ORing]

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy b s (φ ⇔ₗ ψ) ↔
      (Hierarchy b s φ ∧ Hierarchy b.alt s φ ∧ Hierarchy b s ψ ∧ Hierarchy b.alt s ψ) :=
  by simp [Semiformula.iff_eq]; tauto

@[simp]
lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy b 0 (φ ⇔ₗ ψ) ↔ (Hierarchy b 0 φ ∧ Hierarchy b 0 ψ) := by
  simp [Semiformula.iff_eq]; tauto

lemma matrix_conj_iff {b s n} {φ : Fin m → Semiformula L ξ n} :
    Hierarchy b s (Matrix.conj fun j ↦ φ j) ↔ ∀ j, Hierarchy b s (φ j) := by cases m <;> simp

lemma remove_forall {φ : Semiformula L ξ (n + 1)} : Hierarchy b s (∀¹ φ) → Hierarchy b s φ :=
  by
  intro h; rcases h
  case ball => simpa
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists {φ : Semiformula L ξ (n + 1)} : Hierarchy b s (∃¹ φ) → Hierarchy b s φ :=
  by
  intro h; rcases h
  case bexs => simpa
  case exs => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

@[simp]
lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    Hierarchy Γ s (φ.padding k) ↔ Hierarchy Γ s φ :=
  by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp]
  intro h
  induction k <;> simp [List.replicate_succ, *]

@[simp]
lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋀l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ := by
  match l with
  | [] => simp
  | [_] => simp
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)]

@[simp]
lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋁l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ := by
  match l with
  | [] => simp
  | [_] => simp
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)]

@[simp]
lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s ((PointwiseComposition.List.conj' · l) φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) := by
  simp [List.conj']

@[simp]
lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s ((PointwiseComposition.List.disj' · l) φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) := by
  simp [List.disj']

@[simp]
lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s ((PointwiseComposition.Finset.conj' t) φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) := by
  simp [Finset.conj']

@[simp]
lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s ((PointwiseComposition.Finset.disj' t) φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) := by
  simp [Finset.disj']

@[simp]
lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.uconj φ) ↔ ∀ i, Hierarchy Γ s (φ i) := by simp [Finset.uconj]

@[simp]
lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.udisj φ) ↔ ∀ i, Hierarchy Γ s (φ i) := by simp [Finset.udisj]

lemma toPrenex {φ : Semiformula L ξ (n + s)} (h : Hierarchy (Γ.altItr s) j φ) :
    Hierarchy Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    change Hierarchy Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ)
    rw [Polarity.quantItr_succ', (show j + (s + 1) = (j + 1) + s by omega)]
    rcases hΓ : Γ.altItr s with _ | _
    · apply ih
      rw [hΓ] at h ⊢
      exact h.sigma
    · apply ih
      rw [hΓ] at h ⊢
      exact h.pi

end Hierarchy

section LOR

lemma sigma₁_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop} (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥) (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy Σ 1 φ → Hierarchy Σ 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy Σ 1 φ → Hierarchy Σ 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy Σ 1 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy Σ 1 φ → P (n + 1) φ → P n (∃¹ φ)) (n φ) : Hierarchy Σ 1 φ → P n φ
  | Hierarchy.verum _ _ _ => hVerum _
  | Hierarchy.falsum _ _ _ => hFalsum _
  | Hierarchy.rel _ _ Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two] using hEQ _ (v 0) (v 1)
  | Hierarchy.nrel _ _ Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two] using hNEQ _ (v 0) (v 1)
  | Hierarchy.rel _ _ Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two] using hLT _ (v 0) (v 1)
  | Hierarchy.nrel _ _ Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two] using hNLT _ (v 0) (v 1)
  | Hierarchy.and hp hq =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hp)
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hq)
  | Hierarchy.or hp hq =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hp)
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hq)
  | Hierarchy.ball pt hp =>
    by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact
      hBall _ t _ hp
        (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hp)
  | Hierarchy.bexs pt hp => by
    apply hExs
    · simp [hp]
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
      apply
        hAnd _ _ _ (by simp) hp (by simpa [Semiformula.Operator.lt_def] using hLT _ _ _)
          (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hp)
  | Hierarchy.sigma (φ := φ) hp =>
    have : Hierarchy Σ 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ this)
  | Hierarchy.exs hp =>
    hExs _ _ hp (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs _ _ hp)

lemma sigma₁_induction' {n φ} (hp : Hierarchy Σ 1 φ)
    {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop} (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥) (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy Σ 1 φ → Hierarchy Σ 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy Σ 1 φ → Hierarchy Σ 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy Σ 1 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy Σ 1 φ → P (n + 1) φ → P n (∃¹ φ)) : P n φ :=
  sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs n φ hp

end LOR

end Arithmetic

/-- The Sound On Hierarchy construction in `FFL.FirstOrder.ArithmeticTheory`. -/
abbrev ArithmeticTheory.SoundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) :=
  T.SoundOn (Arithmetic.Hierarchy Γ k)

lemma ArithmeticTheory.soundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ)
    [T.SoundOnHierarchy Γ k] : T ⊢ σ → Arithmetic.Hierarchy Γ k σ → ℕ↓[ℒₒᵣ] ⊧ σ :=
  SoundOn.sound

instance (T : ArithmeticTheory) [T.SoundOnHierarchy Σ 1] : Entailment.Consistent T :=
  T.consistent_of_sound (Arithmetic.Hierarchy Σ 1) (by simp)

instance (T : ArithmeticTheory) [T.SoundOnHierarchy Π 2] : Entailment.Consistent T :=
  T.consistent_of_sound (Arithmetic.Hierarchy Π 2) (by simp)

end FirstOrder

end FFL

end

end PointwiseComposition
