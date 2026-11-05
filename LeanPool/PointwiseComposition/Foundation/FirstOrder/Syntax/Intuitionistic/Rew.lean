/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Intuitionistic.Formula
public import LeanPool.PointwiseComposition.Foundation.Syntax.Predicate.Rew

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder

namespace Semiformulaᵢ

/-- The rew Aux construction in `FFL.FirstOrder.Semiformulaᵢ`. -/
def rewAux (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaᵢ L ξ₁ n₁ → Semiformulaᵢ L ξ₂ n₂
  | ⊥ => ⊥
  | rel r v => rel r (ω ∘ v)
  | φ ⋏ ψ => rewAux ω φ ⋏ rewAux ω ψ
  | φ ⋎ ψ => rewAux ω φ ⋎ rewAux ω ψ
  | φ ⇒ₗ ψ => rewAux ω φ ⇒ₗ rewAux ω ψ
  | ∀¹ φ => ∀¹ rewAux ω.q φ
  | ∃¹ φ => ∃¹ rewAux ω.q φ

/-- The rew construction in `FFL.FirstOrder.Semiformulaᵢ`. -/
def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaᵢ L ξ₁ n₁ →ˡᶜ Semiformulaᵢ L ξ₂ n₂
    where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [Semiformulaᵢ.neg_def, rewAux]
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_imply' := fun _ _ ↦ rfl

instance : Rewriting L ξ (Semiformulaᵢ L ξ) ζ (Semiformulaᵢ L ζ)
    where
  app := rew
  app_all (_ _) := rfl
  app_exs (_ _) := rfl

instance : Coe (Semisentenceᵢ L n) (Semipropositionᵢ L n) :=
  ⟨Rewriting.emb (ξ := ℕ)⟩

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ rel r v = rel r fun i ↦ ω (v i) :=
  rfl

lemma rew_rel_eq_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r (ω ∘ v) :=
  rfl

private lemma map_inj {n₁ n₂} {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂} (hb : Function.Injective b)
    (hf : Function.Injective f) :
    Function.Injective fun φ : Semiformulaᵢ L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f ▹ φ
  | ⊥, φ => by cases φ using cases' <;> simp [rew_rel]
  | rel r v, φ => by
    cases φ using cases' <;> simp only [rew_rel, rel.injEq, and_imp,
      LogicalConnective.HomClass.map_bot, reduceCtorEq, imp_self,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_imply, Rewriting.app_all, Rewriting.app_exs]
    case hRel =>
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
  | φ ⋏ ψ, χ => by
    cases χ using cases' <;> simp only [LogicalConnective.HomClass.map_and, rew_rel, reduceCtorEq,
      imp_self, LogicalConnective.HomClass.map_bot, and_inj, and_imp,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_imply, Rewriting.app_all,
      Rewriting.app_exs]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | φ ⋎ ψ, χ => by
    cases χ using cases' <;> simp only [LogicalConnective.HomClass.map_or, rew_rel, reduceCtorEq,
      imp_self, LogicalConnective.HomClass.map_bot, LogicalConnective.HomClass.map_and, or_inj,
      and_imp, LogicalConnective.HomClass.map_imply, Rewriting.app_all, Rewriting.app_exs]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | φ ⇒ₗ ψ, χ => by
    cases χ using cases' <;> simp only [LogicalConnective.HomClass.map_imply, rew_rel,
      reduceCtorEq, imp_self, LogicalConnective.HomClass.map_bot,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or, imp_inj, and_imp,
      Rewriting.app_all, Rewriting.app_exs]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | ∀¹ φ, ψ => by
    cases ψ using cases' <;> simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one,
      rew_rel, reduceCtorEq, imp_self, LogicalConnective.HomClass.map_bot,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_imply, all_inj, Rewriting.app_exs]
    intro h;
    exact
      map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb)
          (fun _ ↦ (Fin.succ_ne_zero _).symm))
        hf h
  | ∃¹ φ, ψ => by
    cases ψ using cases' <;> simp only [Rewriting.app_exs, Rew.q_map, Nat.succ_eq_add_one,
      rew_rel, reduceCtorEq, imp_self, LogicalConnective.HomClass.map_bot,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_imply, Rewriting.app_all, exs_inj]
    intro h;
    exact
      map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb)
          (fun _ ↦ (Fin.succ_ne_zero _).symm))
        hf h

instance : ReflectiveRewriting L ξ (Semiformulaᵢ L ξ) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, *]

instance :
    TransitiveRewriting L ξ₁ (Semiformulaᵢ L ξ₁) ξ₂ (Semiformulaᵢ L ξ₂) ξ₃ (Semiformulaᵢ L ξ₃)
    where
  comp_app
    {n₁ n₂ n₃ ω₁₂ ω₂₃
      φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, Rew.comp_app, Rew.q_comp, *]

instance : InjMapRewriting L ξ (Semiformulaᵢ L ξ) ζ (Semiformulaᵢ L ζ) where
  smul_map_injective := map_inj

instance : LawfulSyntacticRewriting L (Semipropositionᵢ L) where

@[simp]
lemma complexity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaᵢ L ξ₁ n₁) :
    (ω ▹ φ).complexity = φ.complexity := by
  induction φ using rec' generalizing n₂ <;> simp [*, rew_rel]

@[simp]
lemma IsNegative.rew {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    (ω ▹ φ).IsNegative ↔ φ.IsNegative := by
  induction φ using rec' generalizing n₂ <;> simp [rew_rel, *]

end Semiformulaᵢ

end FirstOrder
end FFL

end

end PointwiseComposition
