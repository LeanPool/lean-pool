/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.CommutatorExpansion.Identity

/-!
# Norm bounds for the multi-layer commutator expansion

The exact multi-layer commutator expansion of arXiv:1912.08854 is exported here.
Estimating each integral in its remainder gives a bound in terms of nested commutator
norms. For skew-adjoint generators, the conjugating exponentials are unitary.

## Main results

* `TrotterError.norm_commutatorRemainder_le` bounds the remainder for general generators.
* `TrotterError.norm_commutatorRemainder_le_of_le_one` gives the bound for contractive exponentials.
* `TrotterError.norm_commutatorRemainder_le_of_skewAdjoint` gives the skew-adjoint estimate.
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### Norm bounds for `thm:comm_exp_conj` -/

/-- The integral-norm estimation shared by the general and skew-adjoint remainder bounds: given a
nonnegative `C` and a pointwise bound for the smul'd conjugation, the beta integral yields
`C * |τ|^m / D * |τ|^q / q`. -/
lemma norm_integral_smul_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
  apply norm_intervalIntegral_le_of_le_abs_sub_pow _ (mul_nonneg hC (by positivity)) hq
  intro u hu
  exact (hpoint u hu).trans_eq (by ring)

/-- The norm of the `expSMulConj` integral is bounded by `C · |τ|^(q+m) / (q · D)` whenever the
conjugation is pointwise bounded by `C`. Shared by the general and skew-adjoint branches. -/
lemma norm_conj_smul_integral_le_of_norm_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      C * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  calc
    _ ≤ C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
      apply norm_integral_smul_conj_le A X q m D hq hD τ C hC
      intro u hu
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow,
        abs_of_pos hD, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hconj u hu) (by positivity)
    _ = _ := by
      rw [pow_add]
      ring

/-- The norm of the integral in one remainder summand is bounded by `‖X‖ · |τ|^(q+m) / (q · D) ·
e^{2|τ|‖A‖}`. Here the integrand is `((τ-u)^(q-1) · τ^m / D) • (e^{uA} X e^{-uA})`. -/
lemma norm_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C := by
    intro u hu
    refine (norm_expSMulConj_le A X u).trans ?_
    have harg : 2 * |u| * ‖A‖ ≤ 2 * |τ| * ‖A‖ := by
      have habs_u : |u| ≤ |τ| := by
        simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hu)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs_u (by norm_num))
        (norm_nonneg A)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg X)
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * |τ| ^ (q + m) / ((q : ℝ) * D) :=
            norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ C hC hconj
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
            dsimp [C]
            ring_nf

/-- For `0 ≤ τ` and `u ∈ [0, -τ]`, the absorbed conjugation `e^{τA} e^{uA} X e^{-uA}` has norm
at most `‖X‖ · e^{τ‖A‖}`: the two inner exponentials `e^{(τ+u)A}` and `e^{-uA}` telescope to a
single factor of `τ`. -/
lemma norm_exp_mul_expSMulConj_le {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : u ∈ Set.uIcc (0 : ℝ) (-τ)) :
    ‖exp (τ • A) * expSMulConj A X u‖ ≤ ‖X‖ * Real.exp (τ * ‖A‖) := by
  have hu' : u ∈ Set.uIcc (-τ) (0 : ℝ) := by simpa [Set.uIcc_comm] using hu
  have hu'' : u ∈ Set.Icc (-τ) (0 : ℝ) := by
    rwa [Set.uIcc_of_le (neg_nonpos.mpr hτ)] at hu'
  have hge : -τ ≤ u := hu''.1
  have hle0 : u ≤ 0 := hu''.2
  have hτu : 0 ≤ τ + u := by linarith
  have hcomm : Commute (τ • A) (u • A) := (Commute.refl A).smul_left τ |>.smul_right u
  have h_exp : exp (τ • A) * exp (u • A) = exp ((τ + u) • A) := by
    rw [add_smul τ u A]
    exact (exp_add_of_commute hcomm).symm
  have h_prod : exp (τ • A) * expSMulConj A X u = exp ((τ + u) • A) * X * exp (-u • A) := by
    rw [expSMulConj, ← mul_assoc, ← mul_assoc, h_exp]
  have h1 : ‖exp ((τ + u) • A)‖ ≤ Real.exp ((τ + u) * ‖A‖) := by
    have hnorm : ‖(τ + u) • A‖ = (τ + u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτu]
    simpa [hnorm] using FQFP.norm_exp_le ((τ + u) • A)
  have h2 : ‖exp (-u • A)‖ ≤ Real.exp ((-u) * ‖A‖) := by
    have hnorm : ‖u • A‖ = (-u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hle0]
    simpa [hnorm] using FQFP.norm_exp_le (-u • A)
  calc
    ‖exp (τ • A) * expSMulConj A X u‖
        = ‖exp ((τ + u) • A) * X * exp (-u • A)‖ := by rw [h_prod]
    _ ≤ ‖exp ((τ + u) • A)‖ * ‖X‖ * ‖exp (-u • A)‖ := by
            exact (norm_mul_le (exp ((τ + u) • A) * X) (exp (-u • A))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le (exp ((τ + u) • A)) X) (norm_nonneg _))
    _ ≤ Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖) := by
            exact mul_le_mul (mul_le_mul h1 (le_refl ‖X‖) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
    _ = ‖X‖ * Real.exp (τ * ‖A‖) := by
            have harg : (τ + u) * ‖A‖ + (-u) * ‖A‖ = τ * ‖A‖ := by ring
            calc
              Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖)
                  = ‖X‖ * (Real.exp ((τ + u) * ‖A‖) * Real.exp ((-u) * ‖A‖)) := by ring
              _ = ‖X‖ * Real.exp ((τ + u) * ‖A‖ + (-u) * ‖A‖) := by rw [Real.exp_add]
              _ = ‖X‖ * Real.exp (τ * ‖A‖) := by rw [harg]

/-- The norm of the integral of the *absorbed* conjugation `e^{τA} e^{uA} X e^{-uA}` times the
scalar `(-τ-u)^(q-1) (-τ)^m / D` is bounded by `‖X‖ |τ|^(q+m)/(q·D) e^{τ‖A‖}` — one factor of
`τ` instead of the naive `2|τ|`. -/
lemma norm_absorbed_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [NormOneClass 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖) := by
  let C := ‖X‖ * Real.exp (τ * ‖A‖)
  calc
    _ ≤ (C * (|-τ| ^ m / D)) * (|-τ| ^ q / (q : ℝ)) := by
      apply norm_intervalIntegral_le_of_le_abs_sub_pow _ (by dsimp [C]; positivity) hq
      intro u hu
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hD]
      calc
        _ ≤ (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * C :=
          mul_le_mul_of_nonneg_left (norm_exp_mul_expSMulConj_le A X τ u hτ
            (Set.uIoc_subset_uIcc hu)) (by positivity)
        _ = _ := by ring
    _ = _ := by
      dsimp [C]
      rw [abs_neg, pow_add]
      ring

/-- Peeling the last entry off the prefix `(ofFn f).take (j+1)`: its product is the product of
`(ofFn f).take j` times `f j`. -/
lemma ofFn_take_succ_prod {s : ℕ} {𝔸 : Type*} [Monoid 𝔸] (f : Fin s → 𝔸) (j : Fin s) :
    ((List.ofFn f).take ((j : ℕ) + 1)).prod = ((List.ofFn f).take (j : ℕ)).prod * f j := by
  have htake : (List.ofFn f).take ((j : ℕ) + 1) = (List.ofFn f).take (j : ℕ) ++ [f j] := by
    rw [← List.take_concat_get' (List.ofFn f) (j : ℕ) (by simp)]
    simp [List.getElem_ofFn]
  rw [htake, List.prod_append, List.prod_singleton]

/-- The telescoping `(∏_k e^{τA_k}) · (e^{-τA_{s-1}} ⋯ e^{-τA_{j+1}}) = e^{τA_0} ⋯ e^{τA_j}`: the
outer exponential factors beyond layer `j` cancel against the reversed dropped suffix. -/
lemma prod_exp_mul_drop_reverse_telescope {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod
      = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod := by
  let l := List.ofFn (fun k : Fin s => exp (τ • A k))
  have hsplit := congrArg List.prod (List.take_append_drop ((j : ℕ) + 1) l)
  rw [List.prod_append] at hsplit
  rw [← hsplit, mul_assoc]
  have hcancel := prod_mul_rev_eq_one_of_mul_eq_one ((List.ofFn A).drop ((j : ℕ) + 1))
    (fun x ↦ exp (τ • x)) (fun x ↦ exp (-τ • x))
    (fun x ↦ by simpa only [neg_smul] using exp_mul_neg_self (τ • x))
  simpa only [l, List.map_reverse, List.map_drop, List.map_ofFn, Function.comp_def, mul_one] using
    congrArg (fun x ↦ (l.take ((j : ℕ) + 1)).prod * x) hcancel

/-- The product of the norms of exponentials `∏ᵢ ‖exp (tᵢ • Aᵢ)‖` is bounded by
`exp (Σᵢ |tᵢ| · ‖Aᵢ‖)`. -/
lemma norm_prod_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι)
    (A : ι → 𝔸) (t : ι → ℝ) :
    (l.map (fun i => ‖exp (t i • A i)‖)).prod ≤
      Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
  rw [Real.exp_list_sum, List.map_map]
  refine List.prod_map_le_prod_map₀ _ _ (fun i _ ↦ norm_nonneg _) ?_
  intro i _
  simpa only [Function.comp_apply, norm_smul, Real.norm_eq_abs] using FQFP.norm_exp_le (t i • A i)

private lemma norm_list_prod_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) (t : ι → ℝ) :
    ‖(l.map (fun i ↦ exp (t i • A i))).prod‖ ≤ Real.exp ((l.map (fun i ↦ |t i| * ‖A i‖)).sum) := by
  refine (List.norm_prod_le _).trans ?_
  simpa only [List.map_map, Function.comp_def] using norm_prod_exp_smul_le l A t

/-- The norm of the product of `exp (τ • A i)` over a sublist `l` of `Fin s` is bounded by
`exp (|τ| * (l.map ‖A ·‖).sum)`. -/
lemma norm_prod_exp_smul_list_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {s : ℕ} (A : Fin s → 𝔸) (l : List (Fin s)) (τ : ℝ) :
    ‖(l.map (fun i => exp (τ • A i))).prod‖ ≤
      Real.exp (|τ| * (l.map (fun i => ‖A i‖)).sum) := by
  simpa only [List.sum_map_mul_left] using norm_list_prod_exp_smul_le l A (fun _ ↦ τ)

/-- The norm of the outer (left) exponential product of a remainder summand is bounded by
`exp (Σ_{i ≥ k} |τ| · ‖A i‖)`, expressed as a `List` sum over the dropped suffix. -/
lemma norm_ofFn_drop_reverse_prod_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  simpa only [List.map_reverse, List.sum_reverse, List.map_drop, List.map_ofFn, Function.comp_def]
    using norm_list_prod_exp_smul_le ((List.ofFn fun i : Fin s ↦ i).drop k).reverse A (fun _ ↦ τ)

/-- The norms of the strictly-smaller layers, `A j`, and the strictly-larger layers partition the
total norm sum: `(take j).sum + ‖A j‖ + (drop (j+1)).sum = Σ_i ‖A i‖`. -/
lemma sum_norm_take_add_point_add_drop {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸)
    (j : Fin s) :
    ((List.ofFn (fun i : Fin s => ‖A i‖)).take (j : ℕ)).sum + ‖A j‖ +
      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop ((j : ℕ) + 1)).sum = ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hdrop : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := by simp [l])
    rw [← hcons, List.sum_cons]
    simp [l, List.getElem_ofFn]
  calc
    (l.take (j : ℕ)).sum + ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum
        = (l.take (j : ℕ)).sum + (l.drop (j : ℕ)).sum := by rw [hdrop]; ring
    _ = l.sum := by simp
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-- The sum of the norms of `A j` and the strictly-larger layers is at most the total norm sum. -/
lemma norm_point_add_drop_sum_le {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) :
    ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤ ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hlen : (j : ℕ) < l.length := by simp [l]
  have hsplit : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := hlen)
    rw [← hcons, List.sum_cons]
    simp [l]
  calc
    ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum = (l.drop (j : ℕ)).sum := hsplit.symm
    _ ≤ l.sum := by
        have hnonneg : ∀ a ∈ l, (0 : ℝ) ≤ a := by
          intro a ha
          rcases (List.mem_ofFn' (fun i : Fin s => ‖A i‖) a).mp (by simpa [l] using ha) with ⟨i, hi⟩
          rw [← hi]
          exact norm_nonneg (A i)
        exact (List.drop_sublist (j : ℕ) l).sum_le_sum hnonneg
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-! ### Completion: layering the remainder sum into `αCommConj` -/

/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖

/-- Splitting `αCommConj` over `Fin (s + 1)` into the inner `Fin s` part (zero on the last
layer) and the part with nonzero outermost multiplicity. -/
lemma αCommConj_snoc_split {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj A B p = αCommConj (fun i : Fin s => A i.castSucc) B p +
      ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
        (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖ := by
  calc
    αCommConj A B p
        = ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := rfl
    _ = ∑ k ∈ range (p + 1), ∑ q ∈ finAntidiagonal s (p - k),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q k) : ℝ) *
              ‖adSequence A (Fin.snoc q k) B‖ := by
              rw [sum_finAntidiagonal_snoc]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          (∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
              ‖adSequence A (Fin.snoc q 0) B‖) := by
              rw [sum_range_succ', Nat.sub_zero]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          αCommConj (fun i : Fin s => A i.castSucc) B p := by
              rw [show (∑ q ∈ finAntidiagonal s p,
                (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
                  ‖adSequence A (Fin.snoc q 0) B‖) =
                αCommConj (fun i : Fin s => A i.castSucc) B p from by
                simp [αCommConj, adSequence_snoc_zero, multinomial_snoc_zero]]
    _ = αCommConj (fun i : Fin s => A i.castSucc) B p +
          (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖) := by
              rw [add_comm, sum_finAntidiagonal_filter_last_ne_zero]

/-- The layer sum is bounded by `αCommConj`: collapsing each `(j, q)` into the antidiagonal of
`Fin s` by padding with zeros (theory.tex:198-214, the `Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}` step). -/
lemma layerSum_le_αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    layerSum A B p ≤ αCommConj A B p := by
  induction s with
  | zero =>
      simp only [layerSum, αCommConj]
      exact sum_nonneg (fun q _ => mul_nonneg (by positivity) (norm_nonneg _))
  | succ s ih =>
      rw [layerSum, Fin.sum_univ_castSucc]
      have hsplit : (∑ j : Fin s,
          (fun j : Fin (s + 1) =>
            ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
              (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
                ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖) j.castSucc)
          = layerSum (fun i : Fin s => A i.castSucc) B p := rfl
      rw [hsplit, αCommConj_snoc_split A B p]
      exact add_le_add (ih (fun i : Fin s => A i.castSucc)) (le_refl _)

/-- The scalar coefficient in one remainder summand equals `multinomial(q) · |τ|^p / p!`. -/
lemma coeff_eq_multinomial_div_factorial {j p : ℕ} (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hsum : (∑ i : Fin (j + 1), q i) = p) (hlast : 1 ≤ q (Fin.last j)) :
    |τ| ^ p / ((q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
  have hfac : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) =
      (Nat.factorial (q (Fin.last j)) : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred (by lia : q (Fin.last j) ≠ 0)
  have hden : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        (∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      ∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ) := by
    rw [hfac, Fin.prod_univ_castSucc, mul_comm]
  have hms : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) *
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) = (Nat.factorial p : ℝ) := by
    have h' := Nat.multinomial_spec (s := (univ : Finset (Fin (j + 1)))) (f := q)
    rw [hsum] at h'
    exact_mod_cast h'
  rw [hden]
  have hfac_p : (Nat.factorial p : ℝ) ≠ 0 := by positivity
  have hprod : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => by positivity)
  field_simp [hfac_p, hprod]
  rw [← hms]; ring

private lemma remainderTerm_coeff_eq_multinomial {j p : ℕ} {q : Fin (j + 1) → ℕ} (t : ℝ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    |t| ^ (q (Fin.last j) + ∑ i : Fin j, q i.castSucc) /
        ((q (Fin.last j) : ℝ) * ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) =
      (Nat.multinomial univ q : ℝ) * |t| ^ p / (Nat.factorial p : ℝ) := by
  have hsum := mem_finAntidiagonal.mp hq
  rw [add_comm (q (Fin.last j)), ← Fin.sum_univ_castSucc, hsum, ← mul_assoc]
  exact coeff_eq_multinomial_div_factorial q t hsum (by lia)

/-- The telescoped remainder summand (with left context `L`): the norm of
`L · (∏_k e^{τA_k}) · commutatorRemainderTerm A B (-τ) j q` telescopes to a single exponential
`exp(|τ| (C + Σ_k ‖A_k‖))`, with `‖L‖ ≤ exp(|τ| C)`. -/
lemma norm_mul_commutatorRemainderTerm_le {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (A : Fin s → 𝔸) (B : 𝔸) (L : 𝔸) (C : ℝ) (p : ℕ) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0)
    (hL : ‖L‖ ≤ Real.exp (|τ| * C)) :
    ‖L * (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
        commutatorRemainderTerm A B (-τ) j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
        |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  let E : List 𝔸 := List.ofFn (fun k : Fin s => exp (τ • A k))
  let En : List 𝔸 := List.ofFn (fun k : Fin s => exp (-τ • A k))
  let N : List ℝ := List.ofFn (fun k : Fin s => ‖A k‖)
  let m : ℕ := q (Fin.last j)
  let r : ℕ := ∑ i : Fin j, q i.castSucc
  have hlast' : 1 ≤ q (Fin.last j) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have hcont : Continuous (fun u : ℝ => (((-τ - u) ^ (m - 1) *
      (-τ) ^ r / D) : ℝ) • expSMulConj (A j) X u) := by
    fun_prop
  have h_unfold : commutatorRemainderTerm A B (-τ) j q =
      ((En.drop ((j : ℕ) + 1)).reverse.prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • expSMulConj (A j) X u) *
        (E.drop ((j : ℕ) + 1)).prod) := by
    unfold commutatorRemainderTerm
    simp [X, D, E, En, m, r]
  have h_eq : L * E.prod * commutatorRemainderTerm A B (-τ) j q =
      L * (E.take (j : ℕ)).prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
        (E.drop ((j : ℕ) + 1)).prod := by
    rw [h_unfold]
    calc
      L * E.prod * ((En.drop ((j : ℕ) + 1)).reverse.prod *
          (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
              D) : ℝ) • expSMulConj (A j) X u) *
          (E.drop ((j : ℕ) + 1)).prod)
          = L * (E.prod * (En.drop ((j : ℕ) + 1)).reverse.prod) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by ac_rfl
      _ = L * (E.take ((j : ℕ) + 1)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [prod_exp_mul_drop_reverse_telescope A j τ]
      _ = L * (E.take (j : ℕ)).prod * exp (τ • A j) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [ofFn_take_succ_prod (fun k : Fin s => exp (τ • A k)) j]
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (exp (τ • A j) * (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^
              (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              congr 3
              rw [← integral_mul_left (exp (τ • A j))
                (fun u => (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  expSMulConj (A j) X u) hcont 0 (-τ)]
              apply intervalIntegral.integral_congr_uIoo
              intro u _
              change exp (τ • A j) * (((-τ - u) ^ (m - 1) * (-τ) ^
                  (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u =
                (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  (exp (τ • A j) * expSMulConj (A j) X u)
              rw [mul_smul_comm]
  have htake : ‖(E.take (j : ℕ)).prod‖ ≤ Real.exp (|τ| * (N.take (j : ℕ)).sum) := by
    simpa [E, N, List.map_take, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).take (j : ℕ)) τ
  have hdrop : ‖(E.drop ((j : ℕ) + 1)).prod‖ ≤ Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
    simpa [E, N, List.map_drop, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).drop ((j : ℕ) + 1)) τ
  have hint : ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
        D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (τ * ‖A j‖) :=
    norm_absorbed_conj_smul_integral_le (A j) X (q (Fin.last j)) (∑ i : Fin j, q i.castSucc) D
      hlast' hD τ hτ
  have hcomb : Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
        Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) =
      Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, abs_of_nonneg hτ]
    ring_nf
  have hexp_arg : C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum =
      C + ∑ k : Fin s, ‖A k‖ := by
    calc
      C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum
          = C + ((N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum) := by ring
      _ = C + ∑ k : Fin s, ‖A k‖ := by simpa [N] using sum_norm_take_add_point_add_drop A j
  calc
    ‖L * E.prod * commutatorRemainderTerm A B (-τ) j q‖
        = ‖L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod‖ := by rw [h_eq]
    _ ≤ ‖L‖ * ‖(E.take (j : ℕ)).prod‖ *
            ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ *
            ‖(E.drop ((j : ℕ) + 1)).prod‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
                ((q (Fin.last j) : ℝ) * D) * Real.exp (τ * ‖A j‖)) *
            Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
            refine mul_le_mul
              (mul_le_mul (mul_le_mul hL htake (by positivity) (by positivity)) hint
                (by positivity) (by positivity))
              hdrop (by positivity) (by positivity)
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            (Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
              Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum)) := by
            ring_nf
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
            rw [hcomb]
    _ = ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ)) *
            Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            rw [remainderTerm_coeff_eq_multinomial τ hq hlast, hexp_arg]
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            dsimp [X]
            ring

/-- Combining the exponential factors of one remainder summand into the global exponential. -/
lemma exp_bound_combine {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
      Real.exp (2 * |τ| * ‖A j‖) *
        Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) ≤
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  have hS : ((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum =
      |τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum := by
    rw [List.ofFn_comp' (f := fun i : Fin s => ‖A i‖) (g := fun x : ℝ => |τ| * x),
      ← List.map_drop, List.sum_map_mul_left, List.map_id']
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, hS]
  calc
    _ = (2 * |τ|) * (‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_point_add_drop_sum_le A j) (by positivity)

/-- The norm of the outer (right) exponential product is bounded by the same suffix exponential. -/
lemma norm_ofFn_drop_prod_exp_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  simpa only [List.map_drop, List.map_ofFn, Function.comp_def, abs_neg] using
    norm_list_prod_exp_smul_le ((List.ofFn fun i : Fin s ↦ i).drop k) A (fun _ ↦ -τ)

/-- The norm bound of a single remainder summand. -/
lemma norm_commutatorRemainderTerm_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p)
    (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hD : 0 < D := by positivity
  have houterL : ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_reverse_prod_exp_le A (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_prod_exp_le A (j + 1) τ
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (2 * |τ| * ‖A j‖) := by
        simpa [D] using norm_conj_smul_integral_le (A j) X (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D (by lia) hD τ
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
              ((q (Fin.last j) : ℝ) * D) *
              Real.exp (2 * |τ| * ‖A j‖)) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
          (Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            Real.exp (2 * |τ| * ‖A j‖) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)) := by ring
    _ ≤ ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ)) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              rw [remainderTerm_coeff_eq_multinomial τ hq hlast]
              gcongr
              exact exp_bound_combine A j τ
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              dsimp [X]; ring

/-- Shared summation skeleton of the left-multiplied commutator-remainder norm bound: given a
pointwise bound `‖M · commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence … q B‖ · multinomial(q) ·
|τ|^p/p! · F` with nonnegative `F`, the total left-multiplied remainder is bounded by
`αCommConj A B p · |τ|^p/p! · F`. -/
lemma norm_mul_commutatorRemainder_le_of_term_bound {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (M : 𝔸) (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ)
    (hF : 0 ≤ F)
    (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ,
      q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) →
        ‖M * commutatorRemainderTerm A B τ j q‖ ≤
          ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * F) :
    ‖M * commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
  let c := |τ| ^ p / (Nat.factorial p : ℝ) * F
  calc
    _ ≤ layerSum A B p * c := by
      simp only [commutatorRemainder, layerSum, Finset.mul_sum, Finset.sum_mul]
      apply norm_sum_le_of_le
      intro j _
      apply norm_sum_le_of_le
      intro q hq
      simpa only [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hterm j q hq
    _ ≤ αCommConj A B p * c :=
      mul_le_mul_of_nonneg_right (layerSum_le_αCommConj A B p) (by positivity)
    _ = _ := by simp only [c, div_eq_mul_inv, mul_assoc]

/-- The spectral-norm bound of the commutator remainder (theory.tex:238-241, general operators). -/
theorem norm_commutatorRemainder_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  simpa only [one_mul] using norm_mul_commutatorRemainder_le_of_term_bound (1 : 𝔸) A B p τ
    (Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)) (le_of_lt (Real.exp_pos _)) (by
      intro j q hq
      simpa only [one_mul] using
        norm_commutatorRemainderTerm_le A B p τ j q (mem_filter.mp hq).1 (mem_filter.mp hq).2)

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- A finite conjugation remainder term has its exact multinomial weight when
all the exponential factors are contractions in both time directions. -/
theorem norm_commutatorRemainderTerm_le_of_le_one {s : ℕ}
    (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (t : ℝ)
    (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B t j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |t| ^ p /
          (Nat.factorial p : ℝ) := by
  let X := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hlast_le : 1 ≤ q (Fin.last j) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have hint : ‖∫ u in 0..t, (((t - u) ^ (q (Fin.last j) - 1) *
        t ^ (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u‖ ≤
      ‖X‖ * |t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D) := by
    apply norm_conj_smul_integral_le_of_norm_conj_le (A j) X (q (Fin.last j))
      (∑ i : Fin j, q i.castSucc) D hlast_le hD t ‖X‖ (norm_nonneg X)
    intro u _
    exact (norm_expSMulConj_eq_of_le_one (A j) X (hA j) u).le
  have hnorm : ‖commutatorRemainderTerm A B t j q‖ =
      ‖∫ u in 0..t, (((t - u) ^ (q (Fin.last j) - 1) *
        t ^ (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u‖ := by
    unfold commutatorRemainderTerm
    simpa only [List.map_drop, List.map_ofFn, Function.comp_def, X, D] using
      norm_list_exp_conj_eq_of_le_one A hA
        ((List.ofFn (fun i : Fin s ↦ i)).drop (j + 1)) _ t
  rw [hnorm]
  calc
    _ ≤ ‖X‖ * |t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D) := hint
    _ = ‖X‖ * (|t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D)) := by ring
    _ = _ := by
      rw [remainderTerm_coeff_eq_multinomial t hq hlast]
      dsimp only [X]
      ring

/-- **Finite conjugation remainder bound.** The full multinomial commutator
constant is retained, with no exponential growth factor or step restriction. -/
theorem norm_commutatorRemainder_le_of_le_one {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) (t : ℝ) (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) :
    ‖commutatorRemainder A B p t‖ ≤ αCommConj A B p * |t| ^ p /
      (Nat.factorial p : ℝ) := by
  simpa only [one_mul, mul_one] using
    norm_mul_commutatorRemainder_le_of_term_bound (1 : 𝔸) A B p t 1 (by norm_num)
      (fun j q hq ↦ by
        simpa only [one_mul, mul_one] using
          norm_commutatorRemainderTerm_le_of_le_one A B p t hA j q
            (mem_filter.mp hq).1 (mem_filter.mp hq).2)

end

/-- The product of the norms of skew-exponentials `exp (τ • A i)` is at most `1`. -/
lemma norm_ofFn_drop_prod_le_one_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] (A : Fin s → 𝔸) (hskew : ∀ i, star (A i) = -A i)
    (k : ℕ) (τ : ℝ) :
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod ≤ 1 := by
  rw [List.map_drop, List.map_ofFn]
  simp [Function.comp_def, norm_exp_smul_of_skewAdjoint, hskew, List.ofFn_const]

/-- The norm of the integral in one skew-adjoint remainder summand is bounded by
`‖X‖ · |τ|^(q+m) / (q · D)` (no exponential factor). -/
lemma norm_conj_smul_integral_le_of_skew {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] (A X : 𝔸) (hskew : star A = -A) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  refine norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ ‖X‖ (norm_nonneg X) ?_
  intro u _
  exact (norm_expSMulConj_eq_of_skewAdjoint A X hskew u).le

/-- The norm bound of a single remainder summand in the skew-adjoint case. -/
lemma norm_commutatorRemainderTerm_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ)
    (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) :=
  norm_commutatorRemainderTerm_le_of_le_one A B p τ
    (fun i ↦ norm_exp_smul_le_one_of_skewAdjoint (hskew i)) j q hq hlast

/-- The spectral-norm bound of the commutator remainder for anti-Hermitian operators
(theory.tex:242-244). -/
theorem norm_commutatorRemainder_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (hskew : ∀ i, star (A i) = -A i) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) :=
  norm_commutatorRemainder_le_of_le_one A B p τ
    (fun i ↦ norm_exp_smul_le_one_of_skewAdjoint (hskew i))

end TrotterError
