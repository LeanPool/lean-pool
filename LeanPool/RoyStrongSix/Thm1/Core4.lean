/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Core2
public import LeanPool.RoyStrongSix.Thm1.Heights

/-!
# The core of Theorem 1, part 4: the number field and the arithmetic of the entries

* `exists_nf`: a number field `K ⊂ Qbar ⊂ ℂ` containing all coordinates of the data `(aᵢ, αᵢ,
wb_j)`.
* `KMatrix`: the interpolation matrix computed in `K`. `KMatrix_map`: its image in `Qbar` is
  `interpMatrix`.
* `KMatrix_integral`, `KMatrix_house`: with a common denominator `δ` and a house bound `Hd` of the
  data,
  * `δ^{T_J} δ^{L₀} (δ^{ℓS})^{L₁} · A` is integral, and
  * `house A ≤ (Hd (L₀+L₁))^{T_J} (1 + ℓ S Hd)^{L₀} (Hd^{ℓS})^{L₁}`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule _root_.MvPolynomial NumberField
open StrongSix.Roy

namespace StrongSix.Thm1

variable {d0 d1 ℓ t : ℕ} {η : Fin ℓ → E d0 d1} (D : ∀ i, PtData d0 d1 (η i))
  (wb : Fin t → LieG Qb d0 d1)

/-- All coordinates of the data, as one finite family in `Qbar`. -/
def dataFam : (Fin ℓ × Fin d0) ⊕ (Fin ℓ × Fin d1) ⊕ (Fin t × Fin d0) ⊕ (Fin t × Fin d1) → Qb :=
  Sum.elim (fun p => (D p.1).a p.2) <| Sum.elim (fun p => ((D p.1).α p.2 : Qb)) <|
    Sum.elim (fun p => (wb p.1).1 p.2) fun p => (wb p.1).2 p.2

/-- **A number field containing the data.** -/
theorem exists_nf : ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ K ≤ Qb ∧
    ∀ x, ((dataFam D wb x : Qb) : ℂ) ∈ K := by
  refine ⟨IntermediateField.adjoin ℚ (Set.range fun x => ((dataFam D wb x : Qb) : ℂ)), ?_, ?_,
    fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩⟩
  · have : Finite (Set.range fun x => ((dataFam D wb x : Qb) : ℂ)) := Set.finite_range _
    |>.to_subtype
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨x, rfl⟩ := hz
    exact (mem_algebraicClosure_iff.mp (dataFam D wb x).2).isIntegral
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact (dataFam D wb x).2

section K

variable (K : IntermediateField ℚ ℂ) (hmem : ∀ x, ((dataFam D wb x : Qb) : ℂ) ∈ K)

/-- The data, as elements of `K`. -/
noncomputable def aK (i : Fin ℓ) (k : Fin d0) : K := ⟨((D i).a k : ℂ), hmem (Sum.inl (i, k))⟩
/-- Multiplicative point coordinates lifted to the chosen number field. -/
noncomputable def αK (i : Fin ℓ) (j : Fin d1) : K := ⟨(((D i).α j : Qb) : ℂ), hmem (Sum.inr
  (Sum.inl (i, j)))⟩
/-- Differentiation directions lifted to the chosen number field. -/
noncomputable def wK (j : Fin t) : LieG K d0 d1 :=
  (fun k => ⟨((wb j).1 k : ℂ), hmem (Sum.inr (Sum.inr (Sum.inl (j, k))))⟩,
    fun k => ⟨((wb j).2 k : ℂ), hmem (Sum.inr (Sum.inr (Sum.inr (j, k))))⟩)

/-- `exp_G(Σ sᵢηᵢ)` as a valuation of the variables in `K`. -/
noncomputable def gvK (s : Fin ℓ → ℕ) : Var d0 d1 → K :=
  Sum.elim (fun k => ∑ i, (s i : K) * aK D wb K hmem i k)
    fun j => ∏ i, αK D wb K hmem i j ^ s i

/-- The interpolation matrix in `K`. -/
noncomputable def KMatrix (TJ S L0 L1 : ℕ) : Matrix (Row t ℓ TJ S) (Mono d0 d1 L0 L1) K :=
  fun r m => eval (gvK D wb K hmem r.pt) (invDers (r.word.map (wK D wb K hmem)) (monomial m.exps 1))

/-- `φ (eval g P) = eval (φ ∘ g) (φ P)` for a ring hom between fields. -/
theorem map_eval_hom {A B : Type*} [Field A] [Field B] (φ : A →+* B) (g : Var d0 d1 → A)
    (P : MvPolynomial (Var d0 d1) A) : φ (eval g P) = eval (fun v => φ (g v)) (map φ P) := by
  rw [eval_map]
  change φ (eval₂ (RingHom.id A) g P) = _
  rw [hom_eval₂, RingHom.comp_id]

variable (hle : K ≤ Qb)

/-- The inclusion `K → Qbar`. -/
noncomputable def ιK : K →+* Qb := (IntermediateField.inclusion hle).toRingHom

theorem ιK_apply (x : K) : ((ιK K hle x : Qb) : ℂ) = (x : ℂ) := rfl

/-- **The `K`-matrix maps to the `Qbar`-matrix.** -/
theorem KMatrix_map {TJ S L0 L1 : ℕ} (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) :
    ιK K hle (KMatrix D wb K hmem TJ S L0 L1 r m) = interpMatrix D wb TJ S L0 L1 r m := by
  unfold KMatrix interpMatrix
  rw [map_eval_hom, map_invDers, map_monomial, map_one]
  have hw : ((r.word.map (wK D wb K hmem)).map fun w =>
      ((fun i => ιK K hle (w.1 i), fun j => ιK K hle (w.2 j)) : LieG Qb d0 d1)) = r.word.map wb
        := by
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact Prod.ext (funext fun k => Subtype.ext rfl) (funext fun k => Subtype.ext rfl)
  have hg : (fun v => ιK K hle (gvK D wb K hmem r.pt v)) = (gpt D r.pt).coords := by
    funext v
    apply Subtype.ext
    cases v with
    | inl k =>
      simp only [gvK, Sum.elim_inl, map_sum, map_mul, map_natCast, GPt.coords, gpt]
      rw [IntermediateField.coe_sum]
      simp [Finset.sum_apply, nsmul_eq_mul, ιK_apply, aK]
    | inr j =>
      simp only [gvK, Sum.elim_inr, map_prod, map_pow, GPt.coords, gpt]
      rw [IntermediateField.coe_prod]
      simp [Finset.prod_apply, Units.coe_prod, ιK_apply, αK, Units.val_pow_eq_pow_val]
  rw [hw, hg]

/-! ### Integrality and houses of the entries -/

theorem Row.word_length {TJ S : ℕ} (r : Row t ℓ TJ S) : r.word.length < TJ := by
  simp [Row.word]

theorem Row.pt_le {TJ S : ℕ} (r : Row t ℓ TJ S) (i : Fin ℓ) : r.pt i ≤ S :=
  Nat.lt_succ_iff.mp (r.2 i).2

/-- **Arithmetic of the entries.** With a common denominator `δ` and a house bound `Hd ≥ 1` of
the data, each entry `A` of the `K`-matrix satisfies:
* `δ^{T_J} δ^{L₀} (δ^{ℓS})^{L₁} A` is integral;
* `house A ≤ (Hd (L₀+L₁))^{T_J} (1 + ℓ S Hd)^{L₀} (Hd^{ℓS})^{L₁}`. -/
theorem KMatrix_bounds [NumberField K] (δ : ℕ) {Hd : ℝ} (hHd : 1 ≤ Hd)
    (hδa : ∀ i k, IsIntegral ℤ ((δ : K) * aK D wb K hmem i k))
    (hδα : ∀ i j, IsIntegral ℤ ((δ : K) * αK D wb K hmem i j))
    (hδw1 : ∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).1 k))
    (hδw2 : ∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).2 k))
    (hHa : ∀ i k, house (aK D wb K hmem i k) ≤ Hd) (hHα : ∀ i j, house (αK D wb K hmem i j) ≤ Hd)
    (hHw1 : ∀ j k, house ((wK D wb K hmem j).1 k) ≤ Hd)
    (hHw2 : ∀ j k, house ((wK D wb K hmem j).2 k) ≤ Hd)
    {TJ S L0 L1 : ℕ} (hL0 : 1 ≤ L0) (r : Row t ℓ TJ S) (m : Mono d0 d1 L0 L1) :
    IsIntegral ℤ (((δ ^ TJ * δ ^ L0 * (δ ^ (ℓ * S)) ^ L1 : ℕ) : K) * KMatrix D wb K hmem TJ S L0
      L1 r m) ∧
    house (KMatrix D wb K hmem TJ S L0 L1 r m) ≤
      (Hd * (L0 + L1)) ^ TJ * (1 + ℓ * S * Hd) ^ L0 * (Hd ^ (ℓ * S)) ^ L1 := by
  set l := r.word.map (wK D wb K hmem) with hl
  have hlen : l.length < TJ := by rw [hl, List.length_map]; exact r.word_length
  have hA : (0 : ℝ) ≤ Hd := by linarith
  have hgood := good_invDers (good_monomial (K := K) m.exps (D0 := L0) (D1 := L1)
      (by simpa [Mono.exps_inl] using m.2.1) (by simpa [Mono.exps_inr] using m.2.2) δ) l hA
    (fun w hw i => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hδw1 j i)
    (fun w hw i => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hδw2 j i)
    (fun w hw i => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hHw1 j i)
    (fun w hw i => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw; exact hHw2 j i)
  rw [zero_add, mul_one] at hgood
  have hsum : ∑ i, r.pt i ≤ ℓ * S := by
    calc ∑ i, r.pt i ≤ ∑ _i : Fin ℓ, S := Finset.sum_le_sum fun i _ => r.pt_le i
      _ = ℓ * S := by simp
  constructor
  · -- integrality
    have hx : ∀ k, IsIntegral ℤ ((δ : K) * gvK D wb K hmem r.pt (Sum.inl k)) := by
      intro k
      simp only [gvK, Sum.elim_inl, Finset.mul_sum]
      refine IsIntegral.sum _ fun i _ => ?_
      rw [show (δ : K) * ((r.pt i : K) * aK D wb K hmem i k) =
        (r.pt i : K) * ((δ : K) * aK D wb K hmem i k) by ring]
      exact (isIntegral_natCast' _).mul (hδa i k)
    have hy : ∀ j, IsIntegral ℤ (((δ ^ (ℓ * S) : ℕ) : K) * gvK D wb K hmem r.pt (Sum.inr j)) := by
      intro j
      simp only [gvK, Sum.elim_inr]
      have : ((δ ^ (ℓ * S) : ℕ) : K) * ∏ i, αK D wb K hmem i j ^ r.pt i =
          (δ : K) ^ (ℓ * S - ∑ i, r.pt i) * ∏ i, ((δ : K) * αK D wb K hmem i j) ^ r.pt i := by
        rw [Finset.prod_congr rfl fun i _ => mul_pow (δ : K) _ _, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hsum]
        push_cast; ring
      rw [this]
      exact ((isIntegral_natCast' _).pow _).mul (IsIntegral.prod _ fun i _ => (hδα i j).pow _)
    have hint := isIntegral_eval hgood (gvK D wb K hmem r.pt) δ (δ ^ (ℓ * S)) hx hy
    have e : (((δ ^ TJ * δ ^ L0 * (δ ^ (ℓ * S)) ^ L1 : ℕ) : K) * KMatrix D wb K hmem TJ S L0 L1
      r m) =
        (δ : K) ^ (TJ - l.length) * ((δ : K) ^ l.length * (δ : K) ^ L0 *
          ((δ ^ (ℓ * S) : ℕ) : K) ^ L1 * eval (gvK D wb K hmem r.pt) (invDers l (monomial m.exps
            1))) := by
      have hpow : (δ : K) ^ TJ = (δ : K) ^ (TJ - l.length) * (δ : K) ^ l.length := by
        rw [← pow_add, Nat.sub_add_cancel hlen.le]
      rw [KMatrix, ← hl]
      push_cast
      rw [hpow]
      ring
    rw [e]
    exact ((isIntegral_natCast' _).pow _).mul hint
  · -- houses
    have hX : ∀ k, house (gvK D wb K hmem r.pt (Sum.inl k)) ≤ 1 + ℓ * S * Hd := by
      intro k
      simp only [gvK, Sum.elim_inl]
      calc house (∑ i, (r.pt i : K) * aK D wb K hmem i k)
          ≤ ∑ i, house ((r.pt i : K) * aK D wb K hmem i k) := house_sum_le_sum_house _ _
        _ ≤ ∑ _i : Fin ℓ, (S : ℝ) * Hd := Finset.sum_le_sum fun i _ => by
            rw [house_nat_mul]
            exact mul_le_mul (by exact_mod_cast r.pt_le i) (hHa i k) (house_nonneg _) (by
              positivity)
        _ = ℓ * S * Hd := by simp; ring
        _ ≤ 1 + ℓ * S * Hd := by linarith
    have hY : ∀ j, house (gvK D wb K hmem r.pt (Sum.inr j)) ≤ Hd ^ (ℓ * S) := by
      intro j
      simp only [gvK, Sum.elim_inr]
      calc house (∏ i, αK D wb K hmem i j ^ r.pt i)
          ≤ ∏ i, house (αK D wb K hmem i j ^ r.pt i) := house_prod_le' _ _
        _ ≤ ∏ i, Hd ^ r.pt i := Finset.prod_le_prod₀ (fun _ _ => house_nonneg _) fun i _ =>
            (house_pow _ _).le.trans (pow_le_pow_left₀ (house_nonneg _) (hHα i j) _)
        _ = Hd ^ (∑ i, r.pt i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ Hd ^ (ℓ * S) := pow_le_pow_right₀ hHd hsum
    have hX1 : (1 : ℝ) ≤ 1 + ℓ * S * Hd := by
      have : (0 : ℝ) ≤ ℓ * S * Hd := by positivity
      linarith
    have hY1 : (1 : ℝ) ≤ Hd ^ (ℓ * S) := one_le_pow₀ hHd
    have h := house_eval_le hgood (gvK D wb K hmem r.pt) hX1 hY1 hX hY
    have hAL : (1 : ℝ) ≤ Hd * (L0 + L1) := by
      have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL0
      nlinarith [Nat.cast_nonneg (α := ℝ) L1]
    calc house (KMatrix D wb K hmem TJ S L0 L1 r m)
        ≤ (Hd * (L0 + L1)) ^ l.length * (1 + ℓ * S * Hd) ^ L0 * (Hd ^ (ℓ * S)) ^ L1 := h
      _ ≤ (Hd * (L0 + L1)) ^ TJ * (1 + ℓ * S * Hd) ^ L0 * (Hd ^ (ℓ * S)) ^ L1 := by
          gcongr

/-- The data as one family in `K`. -/
noncomputable def dataK (x : (Fin ℓ × Fin d0) ⊕ (Fin ℓ × Fin d1) ⊕ (Fin t × Fin d0) ⊕ (Fin t ×
  Fin d1)) :
    K := ⟨dataFam D wb x, hmem x⟩

/-- **A common denominator and a house bound for the data.** -/
theorem exists_den_house [NumberField K] :
    ∃ (δ : ℕ) (Hd : ℝ), 1 ≤ δ ∧ 1 ≤ Hd ∧
      (∀ i k, IsIntegral ℤ ((δ : K) * aK D wb K hmem i k)) ∧
      (∀ i j, IsIntegral ℤ ((δ : K) * αK D wb K hmem i j)) ∧
      (∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).1 k)) ∧
      (∀ j k, IsIntegral ℤ ((δ : K) * (wK D wb K hmem j).2 k)) ∧
      (∀ i k, house (aK D wb K hmem i k) ≤ Hd) ∧ (∀ i j, house (αK D wb K hmem i j) ≤ Hd) ∧
      (∀ j k, house ((wK D wb K hmem j).1 k) ≤ Hd) ∧
      (∀ j k, house ((wK D wb K hmem j).2 k) ≤ Hd) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (dataK D wb K hmem))
  have hint : ∀ x, IsIntegral ℤ ((y.natAbs : K) * dataK D wb K hmem x) := by
    intro x
    have h := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    rcases Int.natAbs_eq y with he | he
    · rw [he, natCast_zsmul, nsmul_eq_mul] at h; exact h
    · rw [he, neg_smul, natCast_zsmul, nsmul_eq_mul] at h; simpa using h.neg
  set Hd : ℝ := 1 + ∑ x, house (dataK D wb K hmem x)
  have hH : ∀ x, house (dataK D wb K hmem x) ≤ Hd := fun x => by
    have := Finset.single_le_sum (fun x _ => house_nonneg (dataK D wb K hmem x)) (Finset.mem_univ x)
    linarith
  refine ⟨y.natAbs, Hd, Int.natAbs_pos.mpr hy0, ?_, fun i k => hint (Sum.inl (i, k)),
    fun i j => hint (Sum.inr (Sum.inl (i, j))), fun j k => hint (Sum.inr (Sum.inr (Sum.inl (j,
      k)))),
    fun j k => hint (Sum.inr (Sum.inr (Sum.inr (j, k)))), fun i k => hH (Sum.inl (i, k)),
    fun i j => hH (Sum.inr (Sum.inl (i, j))), fun j k => hH (Sum.inr (Sum.inr (Sum.inl (j, k)))),
    fun j k => hH (Sum.inr (Sum.inr (Sum.inr (j, k))))⟩
  have := Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => house_nonneg (dataK D wb K hmem x)
  linarith

end K

end StrongSix.Thm1

end LeanPool
