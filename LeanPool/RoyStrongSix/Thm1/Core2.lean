/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.Thm1.Core1

/-!
# The core of Theorem 1, part 2: the interpolation matrix and the dichotomy

* `dichotomy`: a matrix `A : ρ × κ` over a field has either a non-zero kernel vector, or a square
  submatrix `A(sel, ·)` (`sel : κ → ρ`) with non-zero determinant.
* `Mono`: the monomials `X^a Y^b` with `|a| ≤ L₀` and `|b| ≤ L₁` (the columns).
* `Row`: pairs (derivation word of length `< T_J` over the basis `wb`, grid point `s ∈ [0,S]^ℓ`)
(the rows).
* `interpMatrix`: `A(word, s; λ) = eval_{exp_G(Σ sᵢηᵢ)} (D_{word} X^λ)` over `Qbar`.
* `vanishing_of_kernel`: a non-zero kernel vector gives `P ≠ 0` with `BidegLE P L₀ L₁` that vanishes
  along `W_K` to order `T_J` on the grid. These are the hypotheses of `obstruction`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule _root_.MvPolynomial
open StrongSix.Roy

namespace StrongSix.Thm1

/-! ### Linear algebra -/

/-- **Either a kernel vector or a non-zero maximal minor.** -/
theorem dichotomy {F : Type*} [Field F] {ρ κ : Type*} [Finite ρ] [Fintype κ] [DecidableEq κ]
    (A : Matrix ρ κ F) :
    (∃ c : κ → F, c ≠ 0 ∧ A.mulVec c = 0) ∨ ∃ sel : κ → ρ, (A.submatrix sel id).det ≠ 0 := by
  classical
  let : Fintype ρ := Fintype.ofFinite ρ
  by_cases hc : LinearIndependent F (fun j i => A i j)
  · right
    have hrank : finrank F (span F (Set.range A.row)) = Fintype.card κ := by
      rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_cols]
      exact finrank_span_eq_card hc
    obtain ⟨b, hbt, hbspan, hli⟩ := exists_linearIndependent F (Set.range A.row)
    let _ : Fintype b := ((Set.finite_range _).subset hbt).fintype
    have hcard : Fintype.card b = Fintype.card κ := by
      rw [← hrank, ← hbspan, ← finrank_span_eq_card hli, Subtype.range_coe]
    let e : κ ≃ b := (Fintype.equivOfCardEq hcard.symm)
    have hpre : ∀ x : b, ∃ r, A.row r = x := fun x => hbt x.2
    choose sel hsel using hpre
    refine ⟨fun j => sel (e j), ?_⟩
    have hrow : (A.submatrix (fun j => sel (e j)) id).row = fun j => ((e j : b) : κ → F) := by
      funext j
      rw [← hsel (e j)]
      rfl
    have hli' : LinearIndependent F (A.submatrix (fun j => sel (e j)) id).row := by
      rw [hrow]; exact hli.comp e e.injective
    have hu := Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  · left
    obtain ⟨g, hg, j0, hj0⟩ := Fintype.not_linearIndependent_iff.mp hc
    refine ⟨g, fun h => hj0 (congrFun h j0), ?_⟩
    funext i
    have := congrFun hg i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this

/-! ### Index types -/

variable {d0 d1 ℓ t : ℕ}

/-- Monomials `X^a Y^b` with `|a| ≤ L₀` and `|b| ≤ L₁`. -/
def Mono (d0 d1 L0 L1 : ℕ) :=
  {m : (Fin d0 → Fin (L0 + 1)) × (Fin d1 → Fin (L1 + 1)) //
    (∑ i, (m.1 i : ℕ)) ≤ L0 ∧ (∑ j, (m.2 j : ℕ)) ≤ L1}

noncomputable instance (L0 L1 : ℕ) : Fintype (Mono d0 d1 L0 L1) := by
  unfold Mono; infer_instance

instance (L0 L1 : ℕ) : DecidableEq (Mono d0 d1 L0 L1) := by
  unfold Mono; infer_instance

/-- The exponent vector of a monomial. -/
noncomputable def Mono.exps {L0 L1 : ℕ} (m : Mono d0 d1 L0 L1) : Var d0 d1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (m.1.1 i : ℕ)) fun j => (m.1.2 j : ℕ))

theorem Mono.exps_inl {L0 L1 : ℕ} (m : Mono d0 d1 L0 L1) (i : Fin d0) :
    m.exps (Sum.inl i) = m.1.1 i := rfl

theorem Mono.exps_inr {L0 L1 : ℕ} (m : Mono d0 d1 L0 L1) (j : Fin d1) :
    m.exps (Sum.inr j) = m.1.2 j := rfl

theorem Mono.exps_injective {L0 L1 : ℕ} : Function.Injective (Mono.exps (d0 := d0) (d1 := d1)
    (L0 := L0) (L1 := L1)) := by
  intro m m' h
  apply Subtype.ext
  apply Prod.ext
  · funext i; exact Fin.ext (by have := DFunLike.congr_fun h (Sum.inl i); simpa [Mono.exps]
    using this)
  · funext j; exact Fin.ext (by have := DFunLike.congr_fun h (Sum.inr j); simpa [Mono.exps]
    using this)

/-- Rows: a derivation word of length `< T_J` over `Fin t`, and a grid point in `[0,S]^ℓ`. -/
abbrev Row (t ℓ TJ S : ℕ) := (Σ k : Fin TJ, Fin k → Fin t) × (Fin ℓ → Fin (S + 1))

/-- The word of a row. -/
def Row.word {TJ S : ℕ} (r : Row t ℓ TJ S) : List (Fin t) := List.ofFn r.1.2

/-- The grid point of a row. -/
def Row.pt {TJ S : ℕ} (r : Row t ℓ TJ S) : Fin ℓ → ℕ := fun i => r.2 i

/-! ### The interpolation matrix -/

variable {η : Fin ℓ → E d0 d1} (D : ∀ i, PtData d0 d1 (η i)) (wb : Fin t → LieG Qb d0 d1)

/-- `A(row; λ) = eval_{exp_G(Σ sᵢηᵢ)} (D_{word} X^λ)`. -/
noncomputable def interpMatrix (TJ S L0 L1 : ℕ) : Matrix (Row t ℓ TJ S) (Mono d0 d1 L0 L1) Qb :=
  fun r m => eval (gpt D r.pt).coords (invDers (r.word.map wb) (monomial m.exps 1))

theorem invDers_add (l : List (LieG Qb d0 d1)) (P Q : MvPolynomial (Var d0 d1) Qb) :
    invDers l (P + Q) = invDers l P + invDers l Q := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [invDers_cons, invDers_cons, invDers_cons, ih, invDer_add]

theorem invDers_smul (l : List (LieG Qb d0 d1)) (c : Qb) (P : MvPolynomial (Var d0 d1) Qb) :
    invDers l (c • P) = c • invDers l P := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [invDers_cons, invDers_cons, ih, invDer_smul_right]

theorem invDers_sum {ι : Type*} (l : List (LieG Qb d0 d1)) (s : Finset ι)
    (f : ι → MvPolynomial (Var d0 d1) Qb) : invDers l (∑ k ∈ s, f k) = ∑ k ∈ s, invDers l (f k)
      := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    induction l with
    | nil => rfl
    | cons w l ih => rw [invDers_cons, ih]; simp [invDer]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, invDers_add, ih]

/-- **A kernel vector gives the obstruction's polynomial.** -/
theorem vanishing_of_kernel (W : Submodule ℂ (E d0 d1)) (hwb : WK W = span Qb (Set.range wb))
    {TJ S L0 L1 : ℕ} (c : Mono d0 d1 L0 L1 → Qb) (hc0 : c ≠ 0)
    (hc : (interpMatrix D wb TJ S L0 L1).mulVec c = 0) :
    ∃ P : MvPolynomial (Var d0 d1) Qb, P ≠ 0 ∧ BidegLE P L0 L1 ∧
      ∀ s : Fin ℓ → ℕ, (∀ i, s i ≤ S) → VanishesAlong (WK W) P TJ (gpt D s) := by
  classical
  set P : MvPolynomial (Var d0 d1) Qb := ∑ m, monomial m.exps (c m) with hP
  have hcoeff : ∀ m, P.coeff m.exps = c m := by
    intro m
    rw [hP, coeff_sum]
    rw [Finset.sum_eq_single m (fun m' _ hm' => by
        have hne : m'.exps ≠ m.exps := fun h => hm' (Mono.exps_injective h)
        simp [coeff_monomial, hne])
      (fun h => absurd (Finset.mem_univ m) h)]
    simp
  refine ⟨P, fun h => ?_, fun e he => ?_, fun s hs => ?_⟩
  · obtain ⟨m, hm⟩ := Function.ne_iff.mp hc0
    exact hm (by rw [← hcoeff m, h]; simp)
  · -- every monomial of `P` has bounded bidegree
    rw [MvPolynomial.mem_support_iff] at he
    have : ∃ m : Mono d0 d1 L0 L1, m.exps = e := by
      by_contra hno
      push Not at hno
      apply he
      rw [hP, coeff_sum]
      exact Finset.sum_eq_zero fun m _ => by simp [coeff_monomial, hno m]
    obtain ⟨m, rfl⟩ := this
    exact ⟨by simpa [Mono.exps_inl] using m.2.1, by simpa [Mono.exps_inr] using m.2.2⟩
  · refine vanishesAlong_of_words (WK W) wb hwb P TJ _ fun word hlen => ?_
    let r : Row t ℓ TJ S := (⟨⟨word.length, hlen⟩, word.get⟩, fun i => ⟨s i, Nat.lt_succ_of_le
      (hs i)⟩)
    have hrow := congrFun hc r
    have hw : r.word = word := List.ofFn_get word
    have hpt : r.pt = s := rfl
    rw [Pi.zero_apply] at hrow
    simp only [Matrix.mulVec, dotProduct, interpMatrix] at hrow
    rw [hP, invDers_sum, map_sum]
    rw [← hrow, hw, hpt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show monomial m.exps (c m) = c m • monomial m.exps (1 : Qb) by
      rw [smul_monomial, smul_eq_mul, mul_one], invDers_smul, smul_eval, mul_comm]

/-! ### Data -/

/-- **C1: the data.** A `ℚ`-basis `η` of `Y` with its `Qbar`-points, and a `Qbar`-basis of `W_K`. -/
theorem exists_data {Y : Submodule ℚ (E d0 d1)} {W V : Submodule ℂ (E d0 d1)}
    (H : Hyps d0 d1 Y W V) :
    ∃ (ℓ : ℕ) (η : Fin ℓ → E d0 d1), span ℚ (Set.range η) = Y ∧ (∀ i, η i ∈ Y) ∧
      Nonempty (∀ i, PtData d0 d1 (η i)) ∧
      ∃ (t : ℕ) (wb : Fin t → LieG Qb d0 d1), WK W = span Qb (Set.range wb) := by
  have := H.fin
  let b := Module.finBasis ℚ Y
  refine ⟨_, fun i => (b i : E d0 d1), ?_, fun i => (b i).2, ?_, ?_⟩
  · have h := congrArg (Submodule.map Y.subtype) b.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at h
    exact h
  · exact ⟨fun i => (exists_ptData (H.pts _ (b i).2)).some⟩
  · let bw := Module.finBasis Qb (WK W)
    refine ⟨_, fun j => (bw j : LieG Qb d0 d1), ?_⟩
    have h := congrArg (Submodule.map (WK W).subtype) bw.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at h
    exact h.symm

end StrongSix.Thm1

end LeanPool
