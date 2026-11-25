/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.StronglyPositiveForms

/-!
# Associativity of the exterior product of real forms

`FirstPass.MongeAmpere.coordinateWedge` is the exterior product of continuous real alternating
    forms
on `ℂⁿ`, defined by the normalized shuffle (alternatization) formula.  Mathlib has no associativity
statement for it (nor for `AlternatingMap.domCoprod`).  Here:

* `coordinateWedge_apply_perm` —
    `(A ∧ B)(u) = (p! q!)⁻¹ ∑_{π ∈ S_{p+q}} sgn π A(u ∘ π ∘ ι₁) B(u ∘ π ∘ ι₂)`;
* `sum_perm_sum_alternatization_left` / `_right` — an alternatized factor inside an alternation
  sum can be replaced by the factor itself (the inner permutations are absorbed);
* `coordinateWedge_assoc_apply` / `coordinateWedge_assoc` — `(A ∧ B) ∧ C = A ∧ (B ∧ C)` (up to the
  reindexing `Fin ((p + q) + r) = Fin (p + (q + r))`); both sides are
  `(p! q! r!)⁻¹ ∑_{ρ ∈ S_{p+q+r}} sgn ρ A(v ∘ ρ ∘ ι_A) B(v ∘ ρ ∘ ι_B) C(v ∘ ρ ∘ ι_C)`;
* `coordinateWedge_one_one_apply` — `(α ∧ β)(v₀, v₁) = α(v₀) β(v₁) - α(v₁) β(v₀)` for one-forms;
  `coordinateWedge_comm_one` and `coordinateWedge_self_one` — anticommutation of one-forms:
  `α ∧ β = -β ∧ α`, `α ∧ α = 0`;
* `wedgeFour`, `coordinateWedge_two_two_swap13` / `_swap14` — `(a ∧ b) ∧ (c ∧ d)` changes sign
  when two one-form factors are exchanged;
* `sum_coordinateWedge_wedge_eq_zero` — if `∑ᵢ Qᵢ ∧ Pᵢ = 0` for two-forms, then
  `∑ᵢ (γ ∧ Qᵢ) ∧ Pᵢ = 0` for every `γ` (this is how associativity is used for `d (dd^c S) = 0`).
-/

@[expose] public section

noncomputable section

open Equiv Finset

namespace SGPT.Foundations.Analysis.Pending.CoordinateWedgeAssoc

open FirstPass.MongeAmpere StronglyPositiveForms

variable {n : ℕ}

local notation "E" => FirstPass.ComplexModel n

/-! ### Absorbing inner alternations -/

section Absorb

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- An alternation over `ι ⊕ κ` absorbs an alternation over `ι` of the left factor. -/
theorem sum_perm_sum_alternatization_left (K : (ι → E) → ℝ) (L : (κ → E) → ℝ)
    (w : ι ⊕ κ → E) :
    ∑ σ : Perm (ι ⊕ κ), ((Perm.sign σ : ℤ) : ℝ) *
        ((∑ π : Perm ι, ((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π)) *
          L (w ∘ σ ∘ Sum.inr)) =
      (Fintype.card (Perm ι) : ℝ) * ∑ σ : Perm (ι ⊕ κ), ((Perm.sign σ : ℤ) : ℝ) *
        (K (w ∘ σ ∘ Sum.inl) * L (w ∘ σ ∘ Sum.inr)) := by
  set g : Perm (ι ⊕ κ) → ℝ := fun σ => ((Perm.sign σ : ℤ) : ℝ) *
    (K (w ∘ σ ∘ Sum.inl) * L (w ∘ σ ∘ Sum.inr))
  have hterm : ∀ (σ : Perm (ι ⊕ κ)) (π : Perm ι),
      ((Perm.sign σ : ℤ) : ℝ) * (((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π) *
        L (w ∘ σ ∘ Sum.inr)) = g (σ * Perm.sumCongr π 1) := by
    intro σ π
    simp only [g, Perm.sign_mul, Perm.sign_sumCongr, Perm.sign_one, mul_one, Units.val_mul,
      Int.cast_mul]
    have h1 : w ∘ ⇑(σ * Perm.sumCongr π (1 : Perm κ) : Perm (ι ⊕ κ)) ∘ Sum.inl = w ∘ σ ∘ Sum.inl ∘
      π := by
      funext i
      simp
    have h2 : w ∘ ⇑(σ * Perm.sumCongr π (1 : Perm κ) : Perm (ι ⊕ κ)) ∘ Sum.inr = w ∘ σ ∘ Sum.inr
      := by
      funext i
      simp
    rw [h1, h2]
    ring
  calc _ = ∑ σ : Perm (ι ⊕ κ), ∑ π : Perm ι, ((Perm.sign σ : ℤ) : ℝ) *
        (((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π) * L (w ∘ σ ∘ Sum.inr)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ π : Perm ι, ∑ σ : Perm (ι ⊕ κ), g (σ * Perm.sumCongr π 1) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun σ _ => hterm σ π
    _ = ∑ _π : Perm ι, ∑ σ : Perm (ι ⊕ κ), g σ := by
        refine Finset.sum_congr rfl fun π _ => ?_
        exact Fintype.sum_equiv (Equiv.mulRight (Perm.sumCongr π 1)) _ _ (fun _ => rfl)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- An alternation over `ι ⊕ κ` absorbs an alternation over `κ` of the right factor. -/
theorem sum_perm_sum_alternatization_right (K : (ι → E) → ℝ) (L : (κ → E) → ℝ)
    (w : ι ⊕ κ → E) :
    ∑ σ : Perm (ι ⊕ κ), ((Perm.sign σ : ℤ) : ℝ) *
        (K (w ∘ σ ∘ Sum.inl) *
          ∑ π : Perm κ, ((Perm.sign π : ℤ) : ℝ) * L (w ∘ σ ∘ Sum.inr ∘ π)) =
      (Fintype.card (Perm κ) : ℝ) * ∑ σ : Perm (ι ⊕ κ), ((Perm.sign σ : ℤ) : ℝ) *
        (K (w ∘ σ ∘ Sum.inl) * L (w ∘ σ ∘ Sum.inr)) := by
  let swap := Equiv.sumComm κ ι
  have hleft (σ : Perm (κ ⊕ ι)) :
      (w ∘ swap) ∘ σ ∘ Sum.inl = w ∘ swap.permCongr σ ∘ Sum.inr := by
    funext x
    rfl
  have hright (σ : Perm (κ ⊕ ι)) :
      (w ∘ swap) ∘ σ ∘ Sum.inr = w ∘ swap.permCongr σ ∘ Sum.inl := by
    funext x
    rfl
  have hleft_perm (σ : Perm (κ ⊕ ι)) (π : Perm κ) :
      (w ∘ swap) ∘ σ ∘ Sum.inl ∘ π = w ∘ swap.permCongr σ ∘ Sum.inr ∘ π :=
    congrArg (· ∘ π) (hleft σ)
  have hl := sum_perm_sum_alternatization_left L K (w ∘ swap)
  simp only [hleft_perm, hleft, hright] at hl
  rw [Fintype.sum_equiv swap.permCongr _ (fun σ => ((Perm.sign σ : ℤ) : ℝ) *
        (K (w ∘ σ ∘ Sum.inl) *
          ∑ π : Perm κ, ((Perm.sign π : ℤ) : ℝ) * L (w ∘ σ ∘ Sum.inr ∘ π))) (by
        intro σ
        rw [Perm.sign_permCongr, mul_comm (K (w ∘ _ ∘ Sum.inl))]),
      Fintype.sum_equiv swap.permCongr _ (fun σ => ((Perm.sign σ : ℤ) : ℝ) *
        (K (w ∘ σ ∘ Sum.inl) * L (w ∘ σ ∘ Sum.inr))) (by
        intro σ
        rw [Perm.sign_permCongr, mul_comm (K (w ∘ _ ∘ Sum.inl))])] at hl
  exact hl

end Absorb

/-! ### The exterior product as a sum over permutations of `Fin (p + q)` -/

/-- `(A ∧ B)(u) = (p! q!)⁻¹ ∑_{π ∈ S_{p+q}} sgn π A(u ∘ π ∘ ι₁) B(u ∘ π ∘ ι₂)`, with
`ι₁ = finSumFinEquiv ∘ inl`, `ι₂ = finSumFinEquiv ∘ inr`. -/
theorem coordinateWedge_apply_perm {p q : ℕ} (A : RealForm n p) (B : RealForm n q)
    (u : Fin (p + q) → E) :
    coordinateWedge A B u = ((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ *
      ∑ π : Perm (Fin (p + q)), ((Perm.sign π : ℤ) : ℝ) *
        (A (u ∘ π ∘ finSumFinEquiv ∘ Sum.inl) * B (u ∘ π ∘ finSumFinEquiv ∘ Sum.inr)) := by
  rw [coordinateWedge_apply, coordinateWedgeSum_apply, Nat.cast_mul]
  congr 1
  refine Fintype.sum_equiv (finSumFinEquiv.permCongr) _ _ fun τ => ?_
  rw [Perm.sign_permCongr]
  have h : ∀ i, (u ∘ ⇑finSumFinEquiv) (τ i) =
      u ((finSumFinEquiv.permCongr τ) (finSumFinEquiv i)) := by
    intro i
    simp [Equiv.permCongr_apply]
  congr 2
  · congr 1
    funext i
    exact h (Sum.inl i)
  · congr 1
    funext i
    exact h (Sum.inr i)

/-! ### Associativity -/

section Assoc

variable {p q r : ℕ}

/-- Reindexing a triple alternation sum along an equivalence with `Fin N`. -/
theorem sum_perm_triple_equiv {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ} (γ : X ≃ Fin N)
    (A : RealForm n p) (B : RealForm n q) (C : RealForm n r) (v : Fin N → E)
    (jA : Fin p → X) (jB : Fin q → X) (jC : Fin r → X) :
    ∑ σ : Perm X, ((Perm.sign σ : ℤ) : ℝ) *
        (A (v ∘ γ ∘ σ ∘ jA) * B (v ∘ γ ∘ σ ∘ jB) * C (v ∘ γ ∘ σ ∘ jC)) =
      ∑ ρ : Perm (Fin N), ((Perm.sign ρ : ℤ) : ℝ) *
        (A (v ∘ ρ ∘ γ ∘ jA) * B (v ∘ ρ ∘ γ ∘ jB) * C (v ∘ ρ ∘ γ ∘ jC)) := by
  refine Fintype.sum_equiv (γ.permCongr) _ _ fun σ => ?_
  rw [Perm.sign_permCongr]
  have h : ∀ x, γ (σ x) = (γ.permCongr σ) (γ x) := by
    intro x
    simp [Equiv.permCongr_apply]
  have e : ∀ {k : ℕ} (j : Fin k → X),
      v ∘ γ ∘ σ ∘ j = v ∘ (γ.permCongr σ) ∘ γ ∘ j := fun j => by
    funext i
    exact congrArg v (h (j i))
  rw [e jA, e jB, e jC]

/-- `(A ∧ B) ∧ C` as a triple alternation sum. -/
theorem coordinateWedge_wedge_apply_triple (A : RealForm n p) (B : RealForm n q)
    (C : RealForm n r) (v : Fin (p + q + r) → E) :
    coordinateWedge (coordinateWedge A B) C v =
      ((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹ *
        ∑ ρ : Perm (Fin (p + q + r)), ((Perm.sign ρ : ℤ) : ℝ) *
          (A (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inl) *
            B (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inr) *
            C (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inr)) := by
  set w : Fin (p + q) ⊕ Fin r → E := v ∘ finSumFinEquiv
  set K : (Fin (p + q) → E) → ℝ := fun u =>
    A (u ∘ finSumFinEquiv ∘ Sum.inl) * B (u ∘ finSumFinEquiv ∘ Sum.inr)
  have hAB : ∀ σ : Perm (Fin (p + q) ⊕ Fin r),
      coordinateWedge A B (w ∘ σ ∘ Sum.inl) = ((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ *
        ∑ π : Perm (Fin (p + q)), ((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π) := by
    intro σ
    rw [coordinateWedge_apply_perm]
    rfl
  rw [coordinateWedge_apply, coordinateWedgeSum_apply]
  change ((p + q).factorial * r.factorial : ℝ)⁻¹ * ∑ σ : Perm (Fin (p + q) ⊕ Fin r),
      ((Perm.sign σ : ℤ) : ℝ) * (coordinateWedge A B (w ∘ σ ∘ Sum.inl) * C (w ∘ σ ∘ Sum.inr)) = _
  simp_rw [hAB]
  have hfac : ∀ σ : Perm (Fin (p + q) ⊕ Fin r),
      ((Perm.sign σ : ℤ) : ℝ) * ((((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ *
        ∑ π : Perm (Fin (p + q)), ((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π)) *
          C (w ∘ σ ∘ Sum.inr)) =
      ((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ * (((Perm.sign σ : ℤ) : ℝ) *
        ((∑ π : Perm (Fin (p + q)), ((Perm.sign π : ℤ) : ℝ) * K (w ∘ σ ∘ Sum.inl ∘ π)) *
          C (w ∘ σ ∘ Sum.inr))) := fun σ => by ring
  simp_rw [hfac]
  rw [← Finset.mul_sum, sum_perm_sum_alternatization_left K (fun u => C u) w,
    Fintype.card_perm, Fintype.card_fin]
  have htriple := sum_perm_triple_equiv finSumFinEquiv A B C v
    (Sum.inl ∘ finSumFinEquiv ∘ Sum.inl) (Sum.inl ∘ finSumFinEquiv ∘ Sum.inr) Sum.inr
  have hK : ∑ σ : Perm (Fin (p + q) ⊕ Fin r), ((Perm.sign σ : ℤ) : ℝ) *
      (K (w ∘ σ ∘ Sum.inl) * C (w ∘ σ ∘ Sum.inr)) =
      ∑ σ : Perm (Fin (p + q) ⊕ Fin r), ((Perm.sign σ : ℤ) : ℝ) *
        (A (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inl) *
          B (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inr) *
          C (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inr)) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [K, w, Function.comp_assoc]
  rw [hK, htriple]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hpq : ((p + q).factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul]
  field_simp

/-- `A ∧ (B ∧ C)` as a triple alternation sum. -/
theorem wedge_coordinateWedge_apply_triple (A : RealForm n p) (B : RealForm n q)
    (C : RealForm n r) (v : Fin (p + (q + r)) → E) :
    coordinateWedge A (coordinateWedge B C) v =
      ((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹ *
        ∑ ρ : Perm (Fin (p + (q + r))), ((Perm.sign ρ : ℤ) : ℝ) *
          (A (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inl) *
            B (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inl) *
            C (v ∘ ρ ∘ finSumFinEquiv ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inr)) := by
  set w : Fin p ⊕ Fin (q + r) → E := v ∘ finSumFinEquiv
  set L : (Fin (q + r) → E) → ℝ := fun u =>
    B (u ∘ finSumFinEquiv ∘ Sum.inl) * C (u ∘ finSumFinEquiv ∘ Sum.inr)
  have hBC : ∀ σ : Perm (Fin p ⊕ Fin (q + r)),
      coordinateWedge B C (w ∘ σ ∘ Sum.inr) = ((q.factorial * r.factorial : ℕ) : ℝ)⁻¹ *
        ∑ π : Perm (Fin (q + r)), ((Perm.sign π : ℤ) : ℝ) * L (w ∘ σ ∘ Sum.inr ∘ π) := by
    intro σ
    rw [coordinateWedge_apply_perm]
    rfl
  rw [coordinateWedge_apply, coordinateWedgeSum_apply]
  change (p.factorial * (q + r).factorial : ℝ)⁻¹ * ∑ σ : Perm (Fin p ⊕ Fin (q + r)),
      ((Perm.sign σ : ℤ) : ℝ) * (A (w ∘ σ ∘ Sum.inl) * coordinateWedge B C (w ∘ σ ∘ Sum.inr)) = _
  simp_rw [hBC]
  have hfac : ∀ σ : Perm (Fin p ⊕ Fin (q + r)),
      ((Perm.sign σ : ℤ) : ℝ) * (A (w ∘ σ ∘ Sum.inl) * (((q.factorial * r.factorial : ℕ) : ℝ)⁻¹ *
        ∑ π : Perm (Fin (q + r)), ((Perm.sign π : ℤ) : ℝ) * L (w ∘ σ ∘ Sum.inr ∘ π))) =
      ((q.factorial * r.factorial : ℕ) : ℝ)⁻¹ * (((Perm.sign σ : ℤ) : ℝ) *
        (A (w ∘ σ ∘ Sum.inl) *
          ∑ π : Perm (Fin (q + r)), ((Perm.sign π : ℤ) : ℝ) * L (w ∘ σ ∘ Sum.inr ∘ π))) :=
    fun σ => by ring
  simp_rw [hfac]
  rw [← Finset.mul_sum, sum_perm_sum_alternatization_right (fun u => A u) L w,
    Fintype.card_perm, Fintype.card_fin]
  have htriple := sum_perm_triple_equiv finSumFinEquiv A B C v
    Sum.inl (Sum.inr ∘ finSumFinEquiv ∘ Sum.inl) (Sum.inr ∘ finSumFinEquiv ∘ Sum.inr)
  have hL : ∑ σ : Perm (Fin p ⊕ Fin (q + r)), ((Perm.sign σ : ℤ) : ℝ) *
      (A (w ∘ σ ∘ Sum.inl) * L (w ∘ σ ∘ Sum.inr)) =
      ∑ σ : Perm (Fin p ⊕ Fin (q + r)), ((Perm.sign σ : ℤ) : ℝ) *
        (A (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inl) *
          B (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inl) *
          C (v ∘ finSumFinEquiv ∘ σ ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inr)) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [L, w, Function.comp_assoc]
    ring
  rw [hL, htriple]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hqr : ((q + r).factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul]
  field_simp

/-- **Associativity of the exterior product**, evaluated:
`((A ∧ B) ∧ C)(v) = (A ∧ (B ∧ C))(v ∘ cast)`. -/
theorem coordinateWedge_assoc_apply (A : RealForm n p) (B : RealForm n q) (C : RealForm n r)
    (v : Fin (p + q + r) → E) :
    coordinateWedge (coordinateWedge A B) C v =
      coordinateWedge A (coordinateWedge B C) (v ∘ Fin.cast (Nat.add_assoc p q r).symm) := by
  rw [coordinateWedge_wedge_apply_triple, wedge_coordinateWedge_apply_triple]
  congr 1
  refine Fintype.sum_equiv (finCongr (Nat.add_assoc p q r)).permCongr _ _ fun ρ => ?_
  rw [Perm.sign_permCongr]
  have key : ∀ {k : ℕ} (j : Fin k → Fin (p + q + r)) (j' : Fin k → Fin (p + (q + r))),
      (∀ i, (j i : ℕ) = (j' i : ℕ)) →
        v ∘ ρ ∘ j = (v ∘ Fin.cast (Nat.add_assoc p q r).symm) ∘
          ((finCongr (Nat.add_assoc p q r)).permCongr ρ) ∘ j' := by
    intro k j j' hj
    funext i
    have hi : j i = Fin.cast (Nat.add_assoc p q r).symm (j' i) := Fin.ext (by simp [hj i])
    simp [Equiv.permCongr_apply, hi]
  rw [key (finSumFinEquiv ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl)
      (fun i => by simp),
    key (finSumFinEquiv ∘ Sum.inl ∘ finSumFinEquiv ∘ Sum.inr)
      (finSumFinEquiv ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inl) (fun i => by simp),
    key (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr ∘ finSumFinEquiv ∘ Sum.inr)
      (fun i => by simp [Nat.add_assoc])]

end Assoc

/-! ### One-forms -/

section OneForms

variable (n) in
/-- A real linear form as a real alternating one-form. -/
def oneForm (ℓ : E →L[ℝ] ℝ) : RealForm n 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) ℓ

@[simp] theorem oneForm_apply (ℓ : E →L[ℝ] ℝ) (u : Fin 1 → E) : oneForm n ℓ u = ℓ (u 0) := rfl

/-- The two permutations of `Fin 1 ⊕ Fin 1`. -/
theorem univ_perm_one_one :
    (Finset.univ : Finset (Perm (Fin 1 ⊕ Fin 1))) =
      {1, Equiv.swap (Sum.inl 0) (Sum.inr 0)} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have hcases : ∀ x : Fin 1 ⊕ Fin 1, x = Sum.inl 0 ∨ x = Sum.inr 0 := by
    intro x
    rcases x with i | i
    · exact Or.inl (by rw [Subsingleton.elim i 0])
    · exact Or.inr (by rw [Subsingleton.elim i 0])
  rcases hcases (σ (Sum.inl 0)) with h | h
  · left
    have h' : σ (Sum.inr 0) = Sum.inr 0 := by
      rcases hcases (σ (Sum.inr 0)) with h'' | h''
      · exact absurd (σ.injective (h''.trans h.symm)) (by simp)
      · exact h''
    ext x
    rcases hcases x with rfl | rfl
    · simp [h]
    · simp [h']
  · right
    have h' : σ (Sum.inr 0) = Sum.inl 0 := by
      rcases hcases (σ (Sum.inr 0)) with h'' | h''
      · exact h''
      · exact absurd (σ.injective (h''.trans h.symm)) (by simp)
    ext x
    rcases hcases x with rfl | rfl
    · simp [h]
    · simp [h']

/-- **The exterior product of two one-forms**: `(α ∧ β)(v₀, v₁) = α(v₀) β(v₁) - α(v₁) β(v₀)`. -/
theorem coordinateWedge_one_one_apply (α β : RealForm n 1) (v : Fin (1 + 1) → E) :
    coordinateWedge α β v =
      α (fun _ => v 0) * β (fun _ => v 1) - α (fun _ => v 1) * β (fun _ => v 0) := by
  rw [coordinateWedge_apply, coordinateWedgeSum_apply, univ_perm_one_one,
    Finset.sum_pair (by
      intro h
      have := congrArg (fun σ : Perm (Fin 1 ⊕ Fin 1) => σ (Sum.inl 0)) h
      simp at this)]
  rw [Perm.sign_one, Perm.sign_swap (by simp)]
  have e1 : ∀ i : Fin 1, (v ∘ finSumFinEquiv) ((1 : Perm (Fin 1 ⊕ Fin 1)) (Sum.inl i)) = v 0 := by
    intro i; rw [Subsingleton.elim i 0]; rfl
  have e2 : ∀ i : Fin 1, (v ∘ finSumFinEquiv) ((1 : Perm (Fin 1 ⊕ Fin 1)) (Sum.inr i)) = v 1 := by
    intro i; rw [Subsingleton.elim i 0]; rfl
  have e3 : ∀ i : Fin 1, (v ∘ finSumFinEquiv)
      ((Equiv.swap (Sum.inl 0) (Sum.inr 0) : Perm (Fin 1 ⊕ Fin 1)) (Sum.inl i)) = v 1 := by
    intro i; rw [Subsingleton.elim i 0, Equiv.swap_apply_left]; rfl
  have e4 : ∀ i : Fin 1, (v ∘ finSumFinEquiv)
      ((Equiv.swap (Sum.inl 0) (Sum.inr 0) : Perm (Fin 1 ⊕ Fin 1)) (Sum.inr i)) = v 0 := by
    intro i; rw [Subsingleton.elim i 0, Equiv.swap_apply_right]; rfl
  have f1 : (v ∘ finSumFinEquiv) ∘ ⇑(1 : Perm (Fin 1 ⊕ Fin 1)) ∘ Sum.inl = fun _ => v 0 :=
    funext e1
  have f2 : (v ∘ finSumFinEquiv) ∘ ⇑(1 : Perm (Fin 1 ⊕ Fin 1)) ∘ Sum.inr = fun _ => v 1 :=
    funext e2
  have f3 : (v ∘ finSumFinEquiv) ∘
      ⇑(Equiv.swap (Sum.inl 0) (Sum.inr 0) : Perm (Fin 1 ⊕ Fin 1)) ∘ Sum.inl = fun _ => v 1 :=
    funext e3
  have f4 : (v ∘ finSumFinEquiv) ∘
      ⇑(Equiv.swap (Sum.inl 0) (Sum.inr 0) : Perm (Fin 1 ⊕ Fin 1)) ∘ Sum.inr = fun _ => v 0 :=
    funext e4
  rw [f1, f2, f3, f4]
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, inv_one, one_mul, Units.val_one,
    Int.cast_one, Units.val_neg, Int.cast_neg]
  ring

/-- **Anticommutation of one-forms**: `α ∧ β = -(β ∧ α)`. -/
theorem coordinateWedge_comm_one (α β : RealForm n 1) :
    coordinateWedge α β = -coordinateWedge β α := by
  ext v
  rw [ContinuousAlternatingMap.neg_apply, coordinateWedge_one_one_apply,
    coordinateWedge_one_one_apply]
  ring

theorem coordinateWedge_self_one (α : RealForm n 1) : coordinateWedge α α = 0 := by
  have h := coordinateWedge_comm_one α α
  have : (2 : ℝ) • coordinateWedge α α = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

end OneForms

/-! ### Products of four one-forms -/

section Four

variable {p q : ℕ}

theorem coordinateWedge_neg_left (A : RealForm n p) (B : RealForm n q) :
    coordinateWedge (-A) B = -coordinateWedge A B := by
  ext v
  simp only [coordinateWedge_apply, coordinateWedgeSum_apply, ContinuousAlternatingMap.neg_apply,
    neg_mul, mul_neg, Finset.sum_neg_distrib]

theorem coordinateWedge_neg_right (A : RealForm n p) (B : RealForm n q) :
    coordinateWedge A (-B) = -coordinateWedge A B := by
  ext v
  simp only [coordinateWedge_apply, coordinateWedgeSum_apply, ContinuousAlternatingMap.neg_apply,
    mul_neg, Finset.sum_neg_distrib]

/-- Associativity for a two-form and two one-forms, as an equality of four-forms. -/
theorem coordinateWedge_assoc_two_one_one (A : RealForm n 2) (c d : RealForm n 1) :
    @coordinateWedge n 3 1 (@coordinateWedge n 2 1 A c) d =
      @coordinateWedge n 2 2 A (@coordinateWedge n 1 1 c d) := by
  refine ContinuousAlternatingMap.ext fun v => ?_
  have hcast : (v ∘ Fin.cast (Nat.add_assoc 2 1 1).symm) = v := by
    funext i
    rfl
  conv_rhs => rw [← hcast]
  exact coordinateWedge_assoc_apply (p := 2) (q := 1) (r := 1) A c d v

/-- Associativity for three one-forms, as an equality of three-forms. -/
theorem coordinateWedge_assoc_one_one_one (a b c : RealForm n 1) :
    (coordinateWedge (coordinateWedge a b) c : RealForm n 3) =
      coordinateWedge a (coordinateWedge b c) := by
  apply ContinuousAlternatingMap.ext
  intro v
  exact coordinateWedge_assoc_apply (p := 1) (q := 1) (r := 1) a b c v

/-- The left-nested product `((a ∧ b) ∧ c) ∧ d` of four one-forms. -/
def wedgeFour (a b c d : RealForm n 1) : RealForm n 4 :=
  coordinateWedge (coordinateWedge (coordinateWedge a b) c) d

theorem wedgeFour_eq (a b c d : RealForm n 1) :
    wedgeFour a b c d = coordinateWedge (coordinateWedge a b) (coordinateWedge c d) :=
  coordinateWedge_assoc_two_one_one _ c d

theorem wedgeFour_swap_ab (a b c d : RealForm n 1) :
    wedgeFour a b c d = -wedgeFour b a c d := by
  rw [wedgeFour, wedgeFour, coordinateWedge_comm_one a b, coordinateWedge_neg_left,
    coordinateWedge_neg_left]

theorem wedgeFour_swap_bc (a b c d : RealForm n 1) :
    wedgeFour a b c d = -wedgeFour a c b d := by
  have h : (coordinateWedge (coordinateWedge a b) c : RealForm n 3) =
      -coordinateWedge (coordinateWedge a c) b := by
    rw [coordinateWedge_assoc_one_one_one, coordinateWedge_assoc_one_one_one,
      coordinateWedge_comm_one b c, coordinateWedge_neg_right]
  rw [wedgeFour, wedgeFour, h, coordinateWedge_neg_left]

theorem wedgeFour_swap_cd (a b c d : RealForm n 1) :
    wedgeFour a b c d = -wedgeFour a b d c := by
  rw [wedgeFour_eq, wedgeFour_eq, coordinateWedge_comm_one c d, coordinateWedge_neg_right]

/-- Exchanging the first and third factor of `(a ∧ b) ∧ (c ∧ d)` changes the sign. -/
theorem coordinateWedge_two_two_swap13 (a b c d : RealForm n 1) :
    (coordinateWedge (coordinateWedge a b) (coordinateWedge c d) : RealForm n 4) =
      -coordinateWedge (coordinateWedge c b) (coordinateWedge a d) := by
  rw [← wedgeFour_eq, ← wedgeFour_eq, wedgeFour_swap_bc, wedgeFour_swap_ab, wedgeFour_swap_bc]
  simp

/-- Exchanging the first and fourth factor of `(a ∧ b) ∧ (c ∧ d)` changes the sign. -/
theorem coordinateWedge_two_two_swap14 (a b c d : RealForm n 1) :
    (coordinateWedge (coordinateWedge a b) (coordinateWedge c d) : RealForm n 4) =
      -coordinateWedge (coordinateWedge d b) (coordinateWedge c a) := by
  rw [← wedgeFour_eq, ← wedgeFour_eq, wedgeFour_swap_cd, wedgeFour_swap_bc, wedgeFour_swap_ab,
    wedgeFour_swap_bc, wedgeFour_swap_cd]
  simp

end Four

/-! ### Wedging a vanishing sum of products -/

section Vanishing

variable {p r : ℕ}

variable (n) in
/-- The exterior product with a fixed left factor, as a linear map. -/
def wedgeLeftLM (A : RealForm n p) (r : ℕ) : RealForm n r →ₗ[ℝ] RealForm n (p + r) where
  toFun B := coordinateWedge A B
  map_add' B B' := coordinateWedge_add_right A B B'
  map_smul' c B := coordinateWedge_smul_right c A B

/-- If `∑ᵢ Qᵢ ∧ Pᵢ = 0` for two-forms `Qᵢ, Pᵢ`, then `∑ᵢ (γ ∧ Qᵢ) ∧ Pᵢ = 0` for every form `γ`. -/
theorem sum_coordinateWedge_wedge_eq_zero {ι : Type*} [Fintype ι] (γ : RealForm n p)
    (Q P : ι → RealForm n 2)
    (h : ∑ i, (coordinateWedge (Q i) (P i) : RealForm n (2 + 2)) = 0) :
    ∑ i, coordinateWedge (coordinateWedge γ (Q i)) (P i) = 0 := by
  ext v
  rw [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  simp_rw [coordinateWedge_assoc_apply]
  have hsum : ∑ i, coordinateWedge γ (coordinateWedge (Q i) (P i)) =
      coordinateWedge γ (∑ i, (coordinateWedge (Q i) (P i) : RealForm n (2 + 2))) :=
    (map_sum (wedgeLeftLM n γ (2 + 2)) _ _).symm
  have := congrArg (fun F : RealForm n (p + (2 + 2)) =>
    F (v ∘ Fin.cast (Nat.add_assoc p 2 2).symm)) hsum
  simp only [h, ContinuousAlternatingMap.sum_apply] at this
  rw [this]
  have h0 : coordinateWedge γ (0 : RealForm n (2 + 2)) = 0 :=
    map_zero (wedgeLeftLM n γ (2 + 2))
  rw [h0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

end Vanishing

end SGPT.Foundations.Analysis.Pending.CoordinateWedgeAssoc
