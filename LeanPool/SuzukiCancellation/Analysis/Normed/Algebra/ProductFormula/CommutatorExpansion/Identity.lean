/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialConjugation
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.Commutator

/-!
# Commutator expansion of a multi-layer conjugation

The multi-layer commutator formula of arXiv:1912.08854 expands conjugation by a product of
exponentials into a polynomial in time and an operator-valued integral remainder.

## Main definitions

* `TrotterError.multiConj` conjugates an operator by the ordered exponentials.
* `TrotterError.conjCoeff` is a multinomial-weighted coefficient of the expansion.
* `TrotterError.commutatorRemainder` sums the integral remainders from all layers.

## Main results

* `TrotterError.commutatorExpansion_conj` gives the exact expansion through degrees below `p`.
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### Multi-layer conjugation `thm:comm_exp_conj` -/

/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
noncomputable def multiConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸 :=
  (List.ofFn (fun i : Fin s => exp (τ • A i))).reverse.prod * B *
    (List.ofFn (fun i : Fin s => exp (-τ • A i))).prod

/-- The single `(j, q)` summand of `commutatorRemainder`. -/
@[irreducible]
noncomputable def commutatorRemainderTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸 :=
  ((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod *
    (∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
      expSMulConj (A j) (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u) *
    ((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod

/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

/-- The `τ^j` coefficient of the multi-layer conjugation, as the multinomial-weighted sum
`Σ_{q ∈ finAntidiagonal s j} (∏ i, q_i!⁻¹) • adSequence A q B`. -/
noncomputable def conjCoeff {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸 :=
  ∑ q ∈ finAntidiagonal s j,
    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B

end TrotterError

namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### The expansion theorem `commutatorExpansion_conj` -/

/-- Peeling the outermost layer off `multiConj`:
`multiConj A B τ = e^{τA⟨s⟩} (multiConj (A∘castSucc) B τ) e^{-τA⟨s⟩}`. -/
lemma multiConj_succ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) :
    multiConj A B τ =
      expSMulConj (A (Fin.last s)) (multiConj (fun i : Fin s => A i.castSucc) B τ) τ := by
  unfold multiConj expSMulConj
  have hleft : (List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).reverse.prod =
      exp (τ • A (Fin.last s)) *
        (List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).reverse.prod := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.reverse_concat', List.prod_cons]
  have hright : (List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).prod =
      (List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).prod *
        exp (-τ • A (Fin.last s)) := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.prod_append, List.prod_singleton]
  rw [hleft, hright]
  noncomm_ring

/-- One summand of the `(s+1)`-layer coefficient, rewritten through the outermost `ad` layer. -/
lemma conjCoeff_snoc_summand {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ •
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) =
      ((∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ : ℝ) •
        adSequence A (Fin.snoc q j) B := by
  rw [(adPow (A (Fin.last s)) j).map_smul, ← mul_smul, adSequence_snoc, factorial_inv_snoc]

/-- The `m`-th coefficient of the `(s+1)`-layer expansion is obtained from the inner `s`-layer
coefficients by one further `ad` layer. -/
lemma conjCoeff_succ {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (m : ℕ) :
    conjCoeff A B m = ∑ j ∈ range (m + 1),
      ((Nat.factorial j : ℝ)⁻¹ : ℝ) •
        adPow (A (Fin.last s)) j (conjCoeff (fun i : Fin s => A i.castSucc) B (m - j)) := by
  rw [conjCoeff, sum_finAntidiagonal_snoc s m
    (fun q' => ((∏ i : Fin (s + 1), (Nat.factorial (q' i) : ℝ))⁻¹ : ℝ) • adSequence A q' B)]
  apply sum_congr rfl
  intro j _; rw [conjCoeff]; symm
  have hsum : adPow (A (Fin.last s)) j (∑ q ∈ finAntidiagonal s (m - j),
      (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B) =
      ∑ q ∈ finAntidiagonal s (m - j),
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) :=
    map_sum (adPow (A (Fin.last s)) j).toAddMonoidHom
      (fun q => (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B)
      (finAntidiagonal s (m - j))
  rw [hsum, smul_sum]
  apply sum_congr rfl
  intro q _
  exact conjCoeff_snoc_summand A B q j

/-! ### Auxiliary algebra and reindexing lemmas for `commutatorExpansion_conj` -/

/-- Conjugation commutes with right multiplication by a central scalar:
`expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸)`. -/
lemma expSMulConj_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (r : ℝ) (τ : ℝ) :
    expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸) := by
  rw [← smul_eq_mul_right r X]
  calc
    expSMulConj A (r • X) τ = r • expSMulConj A X τ := (expSMulConjLin A τ).map_smul' r X
    _ = expSMulConj A X τ * (r : 𝔸) := smul_eq_mul_right r (expSMulConj A X τ)

/-- `expSMulConj A · τ` distributes over a finite sum. -/
lemma expSMulConj_map_sum {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : 𝔸) (τ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) :
    expSMulConj A (∑ x ∈ s, f x) τ = ∑ x ∈ s, expSMulConj A (f x) τ := by
  change (expSMulConjLin A τ).toAddMonoidHom (∑ x ∈ s, f x) =
    ∑ x ∈ s, (expSMulConjLin A τ).toAddMonoidHom (f x)
  exact map_sum (expSMulConjLin A τ).toAddMonoidHom f s

/-- Right multiplication by a central scalar `(c : 𝔸)` commutes with the interval integral. -/
lemma integral_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (c : ℝ)
    (τ : ℝ) :
    (∫ u in 0..τ, F u) * (c : 𝔸) = ∫ u in 0..τ, F u * (c : 𝔸) := by
  rw [← smul_eq_mul_right c (∫ u in 0..τ, F u), ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  exact smul_eq_mul_right c (F u)

/-- The single-layer Taylor remainder term, weighted by `d⁻¹` and `τ^j`, rewritten as the
`commutatorRemainderTerm` integrand `((τ-u)^k * τ^j / (k! * d)) • expSMulConj A X u`. -/
lemma expSMulConj_taylor_remainder_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (k j : ℕ) (d : ℝ) (τ : ℝ) :
    (d⁻¹ • (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)))
        * (τ ^ j : 𝔸)
      = ∫ u in 0..τ, ((τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d)) •
          expSMulConj A X u := by
  have hsub : (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)) =
        ∫ u in 0..τ, ((τ - u) ^ k / (Nat.factorial k : ℝ)) • expSMulConj A X u :=
    (integral_smul_eq_integral_mul_sub (fun u => expSMulConj A X u) k τ).symm
  rw [hsub, ← intervalIntegral.integral_smul, ← map_pow (algebraMap ℝ 𝔸) τ j]
  rw [integral_mul_cast (fun u => d⁻¹ • (((τ - u) ^ k / (Nat.factorial k : ℝ)) •
    expSMulConj A X u)) (τ ^ j) τ]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  dsimp
  rw [← mul_smul, smul_mul_cast]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-! ### Structural lemmas for the induction step of `commutatorExpansion_conj` -/

/-- `Fin.castSucc` after `Fin.castLE` at a `Fin s` index agrees with `Fin.castLE` at the lifted
bound: restricting to the first `j + 1` layers coincides whether one first drops to the inner
`Fin s` sequence or works directly on `Fin (s + 1)`. -/
lemma comp_castSucc_castLE {s} {𝔸 : Type*} (A : Fin (s + 1) → 𝔸) (j : Fin s) :
    (fun i : Fin s => A i.castSucc) ∘ Fin.castLE (Nat.succ_le_of_lt j.2)
      = A ∘ Fin.castLE (Nat.succ_le_of_lt j.castSucc.2) := by
  funext i
  simp

/-- Conjugating an inner-layer remainder term by the outermost layer yields the corresponding
outer-layer remainder term at the same (inner) layer index. -/
lemma expSMulConj_commutatorRemainderTerm {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) :
    expSMulConj (A (Fin.last s)) (commutatorRemainderTerm (fun i : Fin s => A i.castSucc) B τ j q) τ
      = commutatorRemainderTerm A B τ j.castSucc q := by
  unfold commutatorRemainderTerm expSMulConj
  let L_inner : 𝔸 :=
    ((List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).drop (j + 1)).reverse.prod
  let I_inner : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence ((fun i : Fin s => A i.castSucc) ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u
  let R_inner : 𝔸 := ((List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).drop (j + 1)).prod
  let L_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop (j.castSucc + 1)).reverse.prod
  let I_outer : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.castSucc.2)) q B) u
  let R_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop (j.castSucc + 1)).prod
  change exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
      = (L_outer * I_outer) * R_outer
  have hL : exp (τ • A (Fin.last s)) * L_inner = L_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [L_inner, L_outer]
    simpa using (ofFn_castSucc_drop_reverse_prod
      (f := fun i : Fin (s + 1) => exp (τ • A i)) (k := j + 1) hk)
  have hR : R_inner * exp (-τ • A (Fin.last s)) = R_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [R_inner, R_outer]
    simpa using (ofFn_castSucc_drop_prod (f := fun i : Fin (s + 1) => exp (-τ • A i))
      (k := j + 1) hk)
  have hI : I_inner = I_outer := by
    dsimp [I_inner, I_outer]
    apply intervalIntegral.integral_congr_uIoo
    intro u _
    simp [comp_castSucc_castLE A j]
  calc
    exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
        = (exp (τ • A (Fin.last s)) * L_inner) * I_inner *
            (R_inner * exp (-τ • A (Fin.last s))) := by
            noncomm_ring
    _ = (L_outer * I_outer) * R_outer := by rw [hL, hI, hR]

/-- Decomposing `commutatorRemainder` over `s + 1` layers into the inner remainder conjugated by the
outermost layer plus the outermost-layer remainder. -/
lemma commutatorRemainder_succ {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    commutatorRemainder A B p τ =
      expSMulConj (A (Fin.last s)) (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  rw [commutatorRemainder, Fin.sum_univ_castSucc]
  congr 1
  · symm
    rw [commutatorRemainder, expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact expSMulConj_commutatorRemainderTerm A B τ j q

/-! ### Reassembly lemmas for the polynomial and remainder parts -/

/-- The polynomial part of the single-layer Taylor expansion reassembles, after reindexing by the
total degree, into `Σ_{m < p} conjCoeff A B m · τ^m`. -/
lemma conjCoeff_sum_of_taylor {s} {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
          (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
      = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
  calc
    (∑ j ∈ range p, (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
        (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ i ∈ range (p - j),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
              (τ ^ (i + j) : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_assoc]
              rw [show (τ ^ i : 𝔸) * (τ ^ j : 𝔸) = (τ ^ (i + j) : 𝔸) by rw [← pow_add]]
    _ = ∑ m ∈ range p, ∑ i ∈ range (m + 1),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B (m - i)))) *
              (τ ^ m : 𝔸) := by
              rw [sum_range_add_antidiagonal p
                (fun i j => ((Nat.factorial i : ℝ)⁻¹ •
                  (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
                    (τ ^ (i + j) : 𝔸))]
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i ≤ m := Nat.le_of_lt_succ (mem_range.mp hi)
              congr 1
              rw [show i + (m - i) = m by lia]
    _ = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
              apply Finset.sum_congr rfl
              intro m _
              rw [← Finset.sum_mul]
              congr 1
              rw [conjCoeff_succ A B m]

/-- The outermost-layer (`j = Fin.last s`) remainder term, written as the smul-integral of the
conjugated `adPow A' (k + 1)` applied to the inner `adSequence`. -/
lemma commutatorRemainderTerm_last {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (q : Fin s → ℕ) (m : ℕ) :
    commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q m) =
      ∫ u in 0..τ, (((τ - u) ^ (m - 1) * τ ^ (∑ i : Fin s, q i) /
          ((Nat.factorial (m - 1) : ℝ) * ∏ i : Fin s, (Nat.factorial (q i) : ℝ)))) •
        expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) m (adSequence (fun i : Fin s => A i.castSucc) q B)) u := by
  unfold commutatorRemainderTerm
  have hL : ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  have hR : ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  rw [hL, hR]
  simp [adSequence_snoc]

/-- The single `j`-th Taylor remainder of the outermost conjugation, expanded over the
`finAntidiagonal s j` fibers and matched against the outermost-layer `commutatorRemainderTerm`s. -/
lemma expSMulConj_taylor_remainder_conjCoeff {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p j : ℕ) (τ : ℝ) :
    (∫ u in 0..τ, expSMulConj (A (Fin.last s))
        (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
      = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
  let A' : 𝔸 := A (Fin.last s)
  let A_inner : Fin s → 𝔸 := fun i => A i.castSucc
  calc
    (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (conjCoeff A_inner B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
        = (∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
            (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
              ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) * (τ ^ j : 𝔸) := by
              congr 1
              have had : adPow A' (p - j) (conjCoeff A_inner B j) =
                  ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B) := by
                rw [conjCoeff]
                have h : adPow A' (p - j) (∑ q ∈ finAntidiagonal s j,
                    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) =
                    ∑ q ∈ finAntidiagonal s j, adPow A' (p - j)
                      (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) :=
                  map_sum (adPow A' (p - j)).toAddMonoidHom
                    (fun q =>
                      ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B)
                    (finAntidiagonal s j)
                rw [h]
                apply Finset.sum_congr rfl
                intro q _
                exact (adPow A' (p - j)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                  (adSequence A_inner q B)
              rw [had]
              have hpoint : ∀ u : ℝ, expSMulConj A' (∑ q ∈ finAntidiagonal s j,
                  ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                  ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)
                  = ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) := by
                intro u
                rw [expSMulConj_map_sum (A := A') (τ := τ - u) (s := finAntidiagonal s j)
                  (f := fun q => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B))]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro q _
                have hsmul : expSMulConj A' (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (adPow A' (p - j) (adSequence A_inner q B))) (τ - u)
                    = ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) :=
                  (expSMulConjLin A' (τ - u)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                    (adPow A' (p - j) (adSequence A_inner q B))
                rw [hsmul, smul_mul_assoc]
              rw [intervalIntegral.integral_congr_uIoo (fun u _ => hpoint u)]
              have hint : ∀ q ∈ finAntidiagonal s j, IntervalIntegrable
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) volume 0 τ := by
                intro q _
                have hc : Continuous
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) := by
                  refine Continuous.smul continuous_const ?_
                  rw [show (fun u : ℝ =>
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))
                        = fun u : ℝ => (u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) •
                          expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) by
                    funext u
                    rw [← smul_eq_mul_right]]
                  refine Continuous.smul (by fun_prop) ?_
                  exact (continuous_expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B))).comp
                    (continuous_const.sub continuous_id)
                exact hc.intervalIntegrable 0 τ
              rw [intervalIntegral.integral_finsetSum hint]
              apply Finset.sum_congr rfl
              intro q _
              rw [intervalIntegral.integral_smul]
    _ = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro q hq
              have hsum : (∑ i : Fin s, q i) = j := mem_finAntidiagonal.mp hq
              rw [expSMulConj_taylor_remainder_smul (A := A')
                (X := adPow A' (p - j) (adSequence A_inner q B))
                (k := p - j - 1) (j := j) (d := ∏ i : Fin s, (Nat.factorial (q i) : ℝ)) (τ := τ)]
              rw [commutatorRemainderTerm_last A B τ q (p - j), hsum]

/-- Summing the single-layer Taylor remainders over `j < p` and reindexing by the antidiagonal
fiber gives the outermost-layer part of `commutatorRemainder`. -/
lemma taylor_remainder_sum {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
      = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j,
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact expSMulConj_taylor_remainder_conjCoeff A B p j τ
    _ = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (k + 1)) := by
              exact sum_range_finAntidiagonal_reflect
                (fun q' => commutatorRemainderTerm A B τ (Fin.last s) q')
    _ = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
              exact (sum_finAntidiagonal_filter_last_ne_zero s p
                (fun q => commutatorRemainderTerm A B τ (Fin.last s) q)).symm

/-- The single-layer Taylor expansion of `expSMulConj A' (Σ_{j<p} C_j · τ^j) τ`, split into the
reassembled polynomial `Σ_{m<p} conjCoeff A B m · τ^m` plus the outermost-layer remainder. -/
lemma expSMulConj_taylor_poly {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    expSMulConj (A (Fin.last s))
        (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
      = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    expSMulConj (A (Fin.last s))
      (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
        = ∑ j ∈ range p, expSMulConj (A (Fin.last s))
            (conjCoeff (fun i : Fin s => A i.castSucc) B j) τ * (τ ^ j : 𝔸) := by
              rw [expSMulConj_map_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [← map_pow (algebraMap ℝ 𝔸) τ j]
              exact expSMulConj_mul_cast (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (τ ^ j) τ
    _ = ∑ j ∈ range p, ((∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) *
              (τ ^ i : 𝔸))
            + ∫ u in 0..τ, expSMulConj (A (Fin.last s))
                (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j))
                  (τ - u) *
                ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hpj : 1 ≤ p - j := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (mem_range.mp hj))
              rw [expSMulConj_taylor (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (p - j) τ hpj]
    _ = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
              simp_rw [add_mul, Finset.sum_add_distrib]
              congr 1
              · exact conjCoeff_sum_of_taylor A B p τ
              · exact taylor_remainder_sum A B p τ

/-- `thm:comm_exp_conj` (theory.tex:222-236): the multi-layer conjugation expands as
`multiConj A B τ = Σ_{j < p} conjCoeff A B j · τ^j + commutatorRemainder A B p τ`,
where the `conjCoeff A B j` are the operators `C_j` independent of `τ`. -/
theorem commutatorExpansion_conj {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    multiConj A B τ =
      (∑ j ∈ Finset.range p, conjCoeff A B j * (τ ^ j : 𝔸)) + commutatorRemainder A B p τ := by
  induction s with
  | zero =>
      have hmulti : multiConj A B τ = B := by simp [multiConj]
      have hc0 : conjCoeff A B 0 = B := by
        rw [conjCoeff]
        rw [Finset.sum_eq_single_of_mem (s := finAntidiagonal 0 0) (a := 0)
          (f := fun q => ((∏ i : Fin 0, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B)]
        · simp [adSequence]
        · rw [mem_finAntidiagonal]
          simp
        · intro b _ hb
          exfalso
          apply hb
          exact Subsingleton.elim _ _
      have hcj : ∀ j, 0 < j → conjCoeff A B j = 0 := by
        intro j hj
        rw [conjCoeff]
        have hempty : finAntidiagonal 0 j = ∅ := by
          ext q
          rw [mem_finAntidiagonal, show (∑ i : Fin 0, q i) = 0 by simp]
          constructor
          · intro h
            exact False.elim ((ne_of_gt hj) h.symm)
          · intro h
            simp at h
        rw [hempty]
        simp
      have hrem : commutatorRemainder A B p τ = 0 := by simp [commutatorRemainder]
      rw [hmulti, hrem, add_zero]
      rw [Finset.sum_eq_single_of_mem (a := 0) (s := Finset.range p)
        (f := fun j => conjCoeff A B j * (τ ^ j : 𝔸))]
      · simp [hc0]
      · rw [Finset.mem_range]
        exact lt_of_lt_of_le zero_lt_one hp
      · intro j _ hj0
        rw [hcj j (Nat.pos_of_ne_zero hj0), zero_mul]
  | succ s ih =>
      rw [multiConj_succ A B τ, ih (fun i : Fin s => A i.castSucc)]
      have hlin : expSMulConj (A (Fin.last s))
          ((∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) +
            commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
          = expSMulConj (A (Fin.last s))
              (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ +
            expSMulConj (A (Fin.last s))
              (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ :=
        (expSMulConjLin (A (Fin.last s)) τ).map_add' _ _
      rw [hlin, expSMulConj_taylor_poly A B p τ, commutatorRemainder_succ A B p τ]
      abel

end TrotterError
