/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.EquationalTheory

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Bootstrapping theory $\mathsf{PA}^-$, $\mathsf{R_0}$ in $\mathsf{I}\Sigma_1$
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]

lemma lt_add_self_add_one (a b : V) : a < b + a + 1 :=
  lt_succ_iff_le.mpr <| le_add_self

lemma lt_succ_iff_eq_or_succ {a b : V} : a < b + 1 ↔ a = b ∨ a < b := by
  simp [lt_succ_iff_le, le_iff_eq_or_lt]

end Arithmetic
end FirstOrder
end FFL

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping
namespace ObjectArithmetic

open FFL.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

local prefix:max "#'" => Semiterm.bvar (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

local postfix:max "↑ᵗ" => Semiterm.shift

local postfix:max "↑ᶠ" => Semiformula.shift

variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝐏𝐀⁻ ≼ T]

open Entailment Entailment.FiniteContext
  _root_.PointwiseComposition.FFL.FirstOrder.Arithmetic.Bootstrapping.Semiformula

instance : 𝐄𝐐 _ ≼ T :=
  have : 𝐏𝐀⁻ ≼ T := inferInstance
  WeakerThan.trans inferInstance this

lemma term_add_assoc (t₁ t₂ t₃ : Term V ℒₒᵣ) :
    T.internalize V ⊢ t₁ + (t₂ + t₃) ≐ (t₁ + t₂) + t₃ :=
  by
  have : T ⊢ (“∀ x y z, x + (y + z) = (x + y) + z”) :=
    complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
      by
      have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
      simp [models_iff, add_assoc]
  have : T.internalize V ⊢ ∀¹ ∀¹ ∀¹ (#'2 + (#'1 + #'0) ≐ #'2 + #'1 + #'0) := by
    simpa using internal_provable_of_outer_provable (V := V) this
  simpa using TProof.specialize₃Proof this t₃ t₂ t₁

lemma numeral_add (n m : V) : T.internalize V ⊢ (ℕᵗn + ℕᵗm) ≐ ℕᵗ(n + m) :=
  by
  induction m using sigma1_pos_succ_induction
  · simp only [tprovable_iff_provable, val_equals, val_add, val_numeral]
    definability
  case
    zero =>
    have : T.internalize V ⊢ ∀¹ ((#'0 + ℕᵗ0) ≐ #'0) :=
      by
      have : T ⊢ (“∀ x, x + 0 = x”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specializeProof this <| ℕᵗn
  case one =>
    rcases eq_zero_or_pos n with (rfl | pos)
    · have : T.internalize V ⊢ (ℕᵗ0 + ℕᵗ1) ≐ ℕᵗ1 :=
        by
        have : T ⊢ (“0 + 1 = 1”) :=
          complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
            by
            have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
            simp [models_iff]
        simpa using internal_provable_of_outer_provable (V := V) this
      simpa using this
    · simp [numeral_succ_pos' pos]
  case succ m
    ih =>
    suffices T.internalize V ⊢ ℕᵗn + (ℕᵗ(m + 1) + ℕᵗ1) ≐ ℕᵗ(n + m + 1) + ℕᵗ1 by
      simpa [← one_add_one_eq_two, ← add_assoc]
    have e1 : T.internalize V ⊢ ℕᵗn + (ℕᵗ(m + 1) + ℕᵗ1) ≐ (ℕᵗn + ℕᵗ(m + 1)) + ℕᵗ1 :=
      term_add_assoc T _ _ _
    have e2 : T.internalize V ⊢ (ℕᵗn + ℕᵗ(m + 1)) + ℕᵗ1 ≐ ℕᵗ(n + (m + 1)) + ℕᵗ1 :=
      subst_add_eq_add T _ _ _ _⨀ih⨀(eq_refl T (ℕᵗ1))
    simpa [add_assoc] using eq_trans e1 e2

lemma numeral_mul (n m : V) : T.internalize V ⊢ ℕᵗn * ℕᵗm ≐ ℕᵗ(n * m) :=
  by
  induction m using sigma1_pos_succ_induction
  · simp only [tprovable_iff_provable, val_equals, val_mul, val_numeral]
    definability
  case
    zero =>
    have : T.internalize V ⊢ ∀¹ ((#'0 * ℕᵗ0) ≐ ℕᵗ0) :=
      by
      have : T ⊢ (“∀ x, x * 0 = 0”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specializeProof this (ℕᵗn)
  case
    one =>
    have : T.internalize V ⊢ ∀¹ ((#'0 * ℕᵗ1) ≐ #'0) :=
      by
      have : T ⊢ (“∀ x, x * 1 = x”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specializeProof this (ℕᵗn)
  case succ m
    ih =>
    suffices T.internalize V ⊢ ℕᵗn * (ℕᵗ(m + 1) + ℕᵗ1) ≐ ℕᵗ(n * (m + 1) + n) by
      simpa [← one_add_one_eq_two, ← add_assoc, mul_add]
    have e1 : T.internalize V ⊢ ℕᵗn * (ℕᵗ(m + 1) + ℕᵗ1) ≐ ℕᵗn * ℕᵗ(m + 1) + ℕᵗn :=
      by
      have : T ⊢ (“∀ x y, x * (y + 1) = x * y + x”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff, mul_add]
      have := by simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂Proof this ℕᵗ(m + 1) (ℕᵗn)
    have e2 : T.internalize V ⊢ ℕᵗn * ℕᵗ(m + 1) + ℕᵗn ≐ ℕᵗ(n * (m + 1)) + ℕᵗn :=
      subst_add_eq_add T _ _ _ _⨀ih⨀(eq_refl T (ℕᵗn))
    have e3 : T.internalize V ⊢ ℕᵗ(n * (m + 1)) + ℕᵗn ≐ ℕᵗ(n * (m + 1) + n) := numeral_add T _ _
    exact eq_trans (eq_trans e1 e2) e3

lemma numeral_eq {n m : V} : n = m → T.internalize V ⊢ ℕᵗ n ≐ ℕᵗ m := by
  rintro rfl;
  exact eq_refl T (ℕᵗ n)

lemma numeral_lt {n m : V} : n < m → T.internalize V ⊢ ℕᵗn <' ℕᵗm := fun h ↦
  by
  let d := m - (n + 1)
  have hm : m = d + n + 1 := by
    simpa [d, add_assoc] using Eq.symm <| sub_add_self_of_le <| succ_le_iff_lt.mpr h
  suffices T.internalize V ⊢ ℕᵗn <' ℕᵗ(d + n + 1) by simpa [hm]
  have l₁ : T.internalize V ⊢ ℕᵗn <' ℕᵗd + ℕᵗn + ℕᵗ1 :=
    by
    have : T ⊢ (“∀ x y, x < y + x + 1”) :=
      complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
        by
        have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
        simp [models_iff, Arithmetic.lt_add_self_add_one]
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize₂Proof this (ℕᵗd) (ℕᵗn)
  have l₂ : T.internalize V ⊢ ℕᵗd + ℕᵗn + ℕᵗ1 ≐ ℕᵗ(d + n + 1) :=
    by
    have e₁ : T.internalize V ⊢ ℕᵗd + ℕᵗn + ℕᵗ1 ≐ ℕᵗ(d + n) + ℕᵗ1 :=
      subst_add_eq_add T _ _ _ _⨀numeral_add T d n⨀eq_refl T (ℕᵗ1)
    have e₂ : T.internalize V ⊢ ℕᵗ(d + n) + ℕᵗ1 ≐ ℕᵗ(d + n + 1) := numeral_add T (d + n) 1
    exact eq_trans e₁ e₂
  exact subst_lt T (ℕᵗn) (ℕᵗn) (ℕᵗd + ℕᵗn + ℕᵗ1) (ℕᵗ(d + n + 1))⨀eq_refl T (ℕᵗn)⨀l₂⨀l₁

lemma numeral_ne {n m : V} : n ≠ m → T.internalize V ⊢ ℕᵗn ≉ ℕᵗm := fun h ↦
  by
  wlog hnm : n < m
  · have hmn : m < n := by exact lt_of_le_of_ne (by simpa using hnm) (Ne.symm h)
    exact ne_symm T _ _⨀(this T (Ne.symm h) hmn)
  have l₁ : T.internalize V ⊢ ℕᵗn <' ℕᵗm := numeral_lt T hnm
  have l₂ : T.internalize V ⊢ (ℕᵗn <' ℕᵗm) ⇒ₗ (ℕᵗn ≉ ℕᵗm) :=
    by
    have : T ⊢ (“∀ x y, x < y → x ≠ y”) :=
      complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
        by
        have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
        simpa [models_iff] using fun _ _ ↦ ne_of_lt
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize₂Proof this (ℕᵗm) (ℕᵗn)
  exact l₂⨀l₁

lemma numeral_nlt {n m : V} : n ≥ m → T.internalize V ⊢ ℕᵗn ≮' ℕᵗm := fun h ↦
  by
  rcases eq_or_lt_of_le h with (rfl | lt)
  · have : T ⊢ (“∀ x, x ≮ x”) :=
      complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
        by
        have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
        simp [models_iff]
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specializeProof this (ℕᵗm)
  · have l₁ : T.internalize V ⊢ ℕᵗm <' ℕᵗn := numeral_lt T lt
    have l₂ : T.internalize V ⊢ (ℕᵗm <' ℕᵗn) ⇒ₗ (ℕᵗn ≮' ℕᵗm) :=
      by
      have : T ⊢ (“∀ x y, x < y → y ≮ x”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simpa [models_iff] using fun _ _ ↦ le_of_lt
      have := by simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂Proof this (ℕᵗn) (ℕᵗm)
    exact l₂⨀l₁

lemma lt_iff_substItrDisj (t : Term V ℒₒᵣ) (m : V) :
    T.internalize V ⊢ (t <' ℕᵗm) ⇔ₗ substItrDisj ![t] (#'1 ≐ #'0) m :=
  by
  induction m using sigma1_pos_succ_induction
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, tprovable_iff_provable, val_iff,
      val_lessThan, val_numeral, substItrDisj_val, SemitermVec.val_succ, Matrix.head_cons,
      Matrix.tail_cons, SemitermVec.val_nil, val_equals, Semiterm.bvar_val,
      Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one, Nat.zero_mod, Nat.cast_zero]
    definability
  case zero =>
    suffices T.internalize V ⊢ (t <' ℕᵗ0) ⇔ₗ ⊥ by simpa
    have : T.internalize V ⊢ ∀¹ ((#'0 <' ℕᵗ0) ⇔ₗ ⊥) :=
      by
      have : T ⊢ (“∀ x, x < 0 ↔ ⊥”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff]
      simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specializeProof this t
  case one =>
    suffices T.internalize V ⊢ (t <' ℕᵗ1) ⇔ₗ (t ≐ ℕᵗ0) ⋎ ⊥ by simpa
    have : T.internalize V ⊢ ∀¹ ((#'0 <' ℕᵗ1) ⇔ₗ (#'0 ≐ ℕᵗ0) ⋎ ⊥) :=
      by
      have : T ⊢ (“∀ x, x < 1 ↔ x = 0 ∨ ⊥”) :=
        complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
          by
          have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
          simp [models_iff]
      simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specializeProof this t
  case succ m
    ih =>
    suffices
      T.internalize V ⊢
        (t <' ℕᵗ(m + 1) + ℕᵗ1) ⇔ₗ (t ≐ ℕᵗ(m + 1)) ⋎ substItrDisj ![t] (#'1 ≐ #'0) (m + 1)
      by simpa [← one_add_one_eq_two, ← add_assoc]
    have : T.internalize V ⊢ (t <' ℕᵗ(m + 1) + ℕᵗ1) ⇔ₗ (t ≐ ℕᵗ(m + 1)) ⋎ (t <' ℕᵗ(m + 1)) :=
      by
      have : T.internalize V ⊢ ∀¹ ∀¹ ((#'0 <' #'1 + ℕᵗ1) ⇔ₗ (#'0 ≐ #'1) ⋎ (#'0 <' #'1)) :=
        by
        have : T ⊢ (“∀ m x, x < m + 1 ↔ x = m ∨ x < m”) :=
          complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦
            by
            have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory hM
            simp [models_iff, Arithmetic.lt_succ_iff_eq_or_succ]
        simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂Proof this t ℕᵗ(m + 1)
    cl_prover[ih, this]

lemma ball_intro (φ : Semiformula V ℒₒᵣ 1) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢ φ.subst ![ℕᵗi]) : T.internalize V ⊢ φ.ball (ℕᵗn) :=
  by
  apply TProof.allProof
  suffices T.internalize V ⊢ (&'0 <' ℕᵗn) ⇒ₗ φ↑ᶠ.subst ![&'0] by
    simpa [imp_def, Semiformula.free, SemitermVec.q, Semiterm.shift_substs,
      Semiterm.substs_substs]
  suffices T.internalize V ⊢ substItrDisj ![&'0] (#'1 ≐ #'0) n ⇒ₗ φ↑ᶠ.subst ![&'0] from
    C_trans (K_left (lt_iff_substItrDisj T (&'0) n)) this
  apply TProof.substItrDisj_left_intro
  · intro i hi
    suffices T.internalize V ⊢ (&'0 ≐ ℕᵗi) ⇒ₗ φ↑ᶠ.subst ![&'0] by simpa
    have hi : T.internalize V ⊢ φ↑ᶠ.subst ![ℕᵗi] := by
      simpa [Semiformula.shift_substs] using TProof.shiftProof (bs i hi)
    have rl : T.internalize V ⊢ (ℕᵗi ≐ &'0) ⇒ₗ φ↑ᶠ.subst ![ℕᵗi] ⇒ₗ φ↑ᶠ.subst ![&'0] :=
      replace T φ.shift (ℕᵗi) (&'0)
    have ec : T.internalize V ⊢ (&'0 ≐ ℕᵗi) ⇒ₗ (ℕᵗi ≐ &'0) := eq_symm T (Semiterm.fvar 0) (ℕᵗi)
    cl_prover[hi, rl, ec]

lemma bexs_intro (φ : Semiformula V ℒₒᵣ 1) (n : V) {i} (hi : i < n)
    (b : T.internalize V ⊢ φ.subst ![ℕᵗi]) : T.internalize V ⊢ φ.bexs (ℕᵗn) :=
  by
  apply TProof.exsProof (ℕᵗi)
  suffices T.internalize V ⊢ (ℕᵗi <' ℕᵗn) ⋏ φ.subst ![ℕᵗi] by simpa
  apply K_intro
  · exact numeral_lt T hi
  · exact b

lemma ball_replace (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ (t ≐ u) ⇒ₗ φ.ball t ⇒ₗ φ.ball u := by
  simpa [SemitermVec.q, Semiformula.substs_substs] using
    replace T ((φ.subst ![#'0]).ball #'0) t u

lemma bexs_replace (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ (t ≐ u) ⇒ₗ φ.bexs t ⇒ₗ φ.bexs u := by
  simpa [SemitermVec.q, Semiformula.substs_substs] using
    replace T ((φ.subst ![#'0]).bexs #'0) t u

end ObjectArithmetic
end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
