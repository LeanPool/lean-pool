/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145EightAffineFamilies
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
C145: literal physical counting trace on the actual ordinary H2 residue fiber.
Frozen compile-free source: no elaboration, compiler, or axiom audit executed.

Coordinates are z=X 0, x=X 1, y=X 2; Res i j k uses [-rate k,-rate i,-rate j].
The oriented di is product_h!=i (rate h-rate i). All divisions are totalized.
Nonzero overlaps are required in the physical theorems, not in the algebraic
factorization. Full ground is retained until a common-ground difference is proved.
Individual zero rates remain allowed in the exact kernel and corrected moments.
The main kernel imposes BOTH ordinary null response and actual counting trace.
No physical separator, rank, calibration recovery, or graph reconstruction is claimed.
-/

@[expose] public section

noncomputable section
namespace C145.H2
open MvPolynomial C145.ThreePlane
open scoped BigOperators
variable {n : ℕ}

/-- Full counting-metric trace, including the ground summand. -/
def fullCountingTrace (a : Fin (n + 1) → ℝ) (U : Tensor (n + 1))
    (i : Fin (n + 1)) : ℝ := ∑ j, U i j j / a j ^ 2

/-- Trace of a residual tensor in the same calibrated full-mode metric. -/
def residualCountingTrace (a : Fin (n + 1) → ℝ) (E : Tensor n)
    (i : Fin n) : ℝ := ∑ j, E i j j / a j.succ ^ 2

/-- Every weighted counting trace of the residual tensor is zero. -/
def ResidualTraceFree (a : Fin (n + 1) → ℝ) (E : Tensor n) : Prop :=
  ∀ i, residualCountingTrace a E i = 0

/-- Swap actual x into coordinate zero, evaluate z,y, then substitute -X. -/
def traceSlice (R : P3) (b : ℝ) : Polynomial ℝ :=
  (Polynomial.map (MvPolynomial.eval ![-b,-b])
    (finSuccEquiv ℝ 2 (rename (Equiv.swap 0 1) R))).comp (-Polynomial.X)

/-- Concrete physical trace polynomial; no interpolation or chosen node. -/
def tracePolynomial (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (R : P3) : Polynomial ℝ :=
  ∑ j, Polynomial.C (1 / (a j.succ ^ 2 * di rates j ^ 2)) *
    ((Polynomial.X - Polynomial.C (2 * rates j)) * traceSlice R (rates j))

theorem fullCountingTrace_sub (a : Fin (n + 1) → ℝ)
    (U V : Tensor (n + 1)) (i : Fin (n + 1)) :
    fullCountingTrace a (V-U) i = fullCountingTrace a V i - fullCountingTrace a U i := by
  simp only [fullCountingTrace, Pi.sub_apply, sub_div, Finset.sum_sub_distrib]

theorem fullCountingTrace_groundZero_zero (a : Fin (n + 1) → ℝ) (E : Tensor n) :
    fullCountingTrace a (groundZero E) 0 = 0 := by
  simp [fullCountingTrace, groundZero_ground_first]

theorem fullCountingTrace_groundZero_succ (a : Fin (n + 1) → ℝ)
    (E : Tensor n) (i : Fin n) :
    fullCountingTrace a (groundZero E) i.succ = residualCountingTrace a E i := by
  simp [fullCountingTrace, residualCountingTrace, Fin.sum_univ_succ,
    groundZero_ground_second, groundZero_succ]

/-- A constant-size slot product representation of the literal physical sum. -/
private theorem physical_entry_product
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ)
    (w : Fin 3 → Fin (n + 1)) :
    C145PhysicalFrame.T Q a (w 1) (w 2) (w 0) =
      ∑ v, ∏ r : Fin 3, a (w r) * Q v (w r) := by
  simp only [C145PhysicalFrame.T, C145PhysicalFrame.C, Finset.mul_sum,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- Every slot permutation follows from reindexing three factors. -/
theorem physical_fullSym
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) :
    FullSymTensor (C145PhysicalFrame.T Q a) := by
  intro e w
  change C145PhysicalFrame.T Q a ((w ∘ e) 1) ((w ∘ e) 2) ((w ∘ e) 0) =
    C145PhysicalFrame.T Q a (w 1) (w 2) (w 0)
  rw [physical_entry_product, physical_entry_product]
  apply Finset.sum_congr rfl
  intro v hv
  exact _root_.Equiv.prod_comp e (fun r => a (w r) * Q v (w r))

private theorem trace_swap_inputs (U : Tensor (n + 1)) (hU : FullSymTensor U)
    (i j k : Fin (n + 1)) : U i j k = U j i k := by
  have h := hU (Equiv.swap 1 2) ![k,i,j]
  change U ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 1 2) 1))
      ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 1 2) 2))
      ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 1 2) 0)) = U i j k at h
  simpa [Equiv.swap_apply_def] using h.symm

private theorem trace_swap_first_output (U : Tensor (n + 1)) (hU : FullSymTensor U)
    (i j k : Fin (n + 1)) : U i j k = U k j i := by
  have h := hU (Equiv.swap 0 1) ![k,i,j]
  change U ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 0 1) 1))
      ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 0 1) 2))
      ((![k,i,j] : Fin 3 → Fin (n + 1)) ((Equiv.swap 0 1) 0)) = U i j k at h
  simpa [Equiv.swap_apply_def] using h.symm

/-- Common constant ground and orthonormality derive every ground entry. -/
theorem physical_commonGround
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c) :
    CommonGround (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a) := by
  have hfirst (j k : Fin (n + 1)) :
      C145PhysicalFrame.T Q1 a 0 j k = C145PhysicalFrame.T Q0 a 0 j k := by
    rw [C145PhysicalFrame.ground_slice Q1 a c hQ1 hG1,
      C145PhysicalFrame.ground_slice Q0 a c hQ0 hG0]
  intro i j k h
  rcases h with rfl | rfl | rfl
  · exact hfirst j k
  · rw [trace_swap_inputs _ (physical_fullSym Q1 a),
      trace_swap_inputs _ (physical_fullSym Q0 a)]
    exact hfirst i k
  · rw [trace_swap_first_output _ (physical_fullSym Q1 a),
      trace_swap_first_output _ (physical_fullSym Q0 a)]
    exact hfirst j i

/-- A physical member relative to an arbitrary common-ground origin has an
inhomogeneous trace target. The origin is not silently assumed physical. -/
theorem physical_member_commonGround_trace_difference
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (ha : ∀ r, a r ≠ 0)
    (hground : ∀ v, Q v 0 = c) (U0 : Tensor (n + 1))
    (hG : CommonGround U0 (C145PhysicalFrame.T Q a)) (i : Fin n) :
    residualCountingTrace a
      (residual (C145PhysicalFrame.T Q a) - residual U0) i =
        -fullCountingTrace a U0 i.succ := by
  calc
    _ = fullCountingTrace a (C145PhysicalFrame.T Q a - U0) i.succ := by
      rw [commonGround_difference U0 (C145PhysicalFrame.T Q a) hG,
        fullCountingTrace_groundZero_succ]
    _ = -fullCountingTrace a U0 i.succ := by
      rw [fullCountingTrace_sub]
      have hz := C145PhysicalFrame.nonground_counting_trace Q a c hQ ha hground i
      change fullCountingTrace a (C145PhysicalFrame.T Q a) i.succ = 0 at hz
      rw [hz, zero_sub]

/-- Homogeneous trace follows because both endpoints are actual frames. -/
theorem physical_pair_difference_trace_free
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1) (ha : ∀ r, a r ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c) :
    ResidualTraceFree a
      (residual (C145PhysicalFrame.T Q1 a) - residual (C145PhysicalFrame.T Q0 a)) := by
  intro i
  rw [physical_member_commonGround_trace_difference Q1 a c hQ1 ha hG1
    (C145PhysicalFrame.T Q0 a) (physical_commonGround Q0 Q1 a c hQ0 hQ1 hG0 hG1)]
  have hz := C145PhysicalFrame.nonground_counting_trace Q0 a c hQ0 ha hG0 i
  change fullCountingTrace a (C145PhysicalFrame.T Q0 a) i.succ = 0 at hz
  rw [hz, neg_zero]

private theorem traceSlice_eval (R : P3) (b u : ℝ) :
    (traceSlice R b).eval u = MvPolynomial.eval ![-b,-u,-b] R := by
  unfold traceSlice
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X]
  rw [← MvPolynomial.eval_eq_eval_mv_eval', MvPolynomial.eval_rename]
  have hv : (Fin.cons (-u) ![-b,-b] : Fin 3 → ℝ) ∘ Equiv.swap 0 1 =
      ![-b,-u,-b] := by
    funext r
    fin_cases r <;> simp [Equiv.swap_apply_def]
  rw [hv]

private theorem traceSlice_natDegree (R : P3) (b : ℝ) :
    (traceSlice R b).natDegree ≤ degreeOf (1 : Fin 3) R := by
  unfold traceSlice
  calc
    _ ≤ (Polynomial.map (MvPolynomial.eval ![-b,-b])
        (finSuccEquiv ℝ 2 (rename (Equiv.swap 0 1) R))).natDegree *
          (-Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_comp_le
    _ = (Polynomial.map (MvPolynomial.eval ![-b,-b])
        (finSuccEquiv ℝ 2 (rename (Equiv.swap 0 1) R))).natDegree := by simp
    _ ≤ (finSuccEquiv ℝ 2 (rename (Equiv.swap 0 1) R)).natDegree :=
      Polynomial.natDegree_map_le
    _ = degreeOf (0 : Fin 3) (rename (Equiv.swap 0 1) R) := natDegree_finSuccEquiv _
    _ = degreeOf (1 : Fin 3) R := by
      simpa using (degreeOf_rename_of_injective (p := R)
        (Equiv.swap (0 : Fin 3) 1).injective (1 : Fin 3))

/-- Evaluation of P is exactly the metric-weighted repeated-node expression. -/
theorem tracePolynomial_eval (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (R : P3) (u : ℝ) :
    (tracePolynomial a rates R).eval u =
      ∑ j, ((u - 2 * rates j) * MvPolynomial.eval ![-rates j,-u,-rates j] R) /
        (a j.succ ^ 2 * di rates j ^ 2) := by
  classical
  simp only [tracePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, traceSlice_eval]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tracePolynomial_zero (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ) :
    tracePolynomial a rates (0 : P3) = 0 := by
  simp [tracePolynomial, traceSlice]

/-- Coordinate-x degree alone bounds P; symmetry is unnecessary here. -/
theorem tracePolynomial_natDegree (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (hn4 : 4 ≤ n) (R : P3) (hR : QAdmissible n R) :
    (tracePolynomial a rates R).natDegree ≤ n - 3 := by
  classical
  rcases hR with rfl | ⟨_, hDegree⟩
  · rw [tracePolynomial_zero]
    simp
  · unfold tracePolynomial
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ ?_
    intro j hj
    have hlin : (Polynomial.X - Polynomial.C (2 * rates j) : Polynomial ℝ).natDegree ≤ 1 := by
      calc
        _ ≤ max (Polynomial.X : Polynomial ℝ).natDegree
            (Polynomial.C (2 * rates j)).natDegree := Polynomial.natDegree_sub_le _ _
        _ = 1 := by rw [Polynomial.natDegree_X, Polynomial.natDegree_C]; norm_num
    have hSlice : (traceSlice R (rates j)).natDegree ≤ n - 4 :=
      (traceSlice_natDegree R (rates j)).trans (hDegree 1)
    calc
      _ ≤ (Polynomial.C (1 / (a j.succ ^ 2 * di rates j ^ 2))).natDegree +
          ((Polynomial.X - Polynomial.C (2 * rates j)) * traceSlice R (rates j)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + (1 + (n - 4)) :=
        add_le_add (le_of_eq (Polynomial.natDegree_C _))
          (Polynomial.natDegree_mul_le.trans (add_le_add hlin hSlice))
      _ ≤ n - 3 := by omega

/-- The literal repeated Xi factors give lambda_i^2*(lambda_i-2lambda_j).
This is an inverse-product identity, valid even at zero denominators under
totalized real division; no cancellation or physical metric is inferred there. -/
theorem res_counting_trace_factorization (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (R : P3) (i : Fin n) :
    residualCountingTrace a (Res rates R) i =
      (rates i ^ 2 / di rates i) * (tracePolynomial a rates R).eval (rates i) := by
  classical
  rw [tracePolynomial_eval, Finset.mul_sum]
  unfold residualCountingTrace
  apply Finset.sum_congr rfl
  intro j hj
  rw [res_entry, xi_negative_diagonal]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring

/-- An individual zero rate gives a zero trace row; its scalar P(0) is not
cancelled or asserted zero. The all-node kernel argument below retains it. -/
theorem res_counting_trace_at_zero_rate (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (R : P3) (i : Fin n) (hi : rates i = 0) :
    residualCountingTrace a (Res rates R) i = 0 := by
  rw [res_counting_trace_factorization, hi]
  simp

/-- X^2 P has all n roots, including an individual zero rate. No division by
lambda_i^2 occurs in this exact trace-compatible quotient characterization. -/
theorem res_trace_free_iff_tracePolynomial_zero (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (R : P3) (hR : QAdmissible n R) :
    ResidualTraceFree a (Res rates R) ↔ tracePolynomial a rates R = 0 := by
  classical
  rcases hR with rfl | ⟨hn4, hDegree⟩
  · simp [tracePolynomial_zero, res_zero, ResidualTraceFree, residualCountingTrace]
  · constructor
    · intro hTrace
      let P := tracePolynomial a rates R
      let Q : Polynomial ℝ := Polynomial.X ^ 2 * P
      have hP : P.natDegree ≤ n - 3 :=
        tracePolynomial_natDegree a rates hn4 R (Or.inr ⟨hn4, hDegree⟩)
      have hQbound : Q.natDegree ≤ 2 + P.natDegree := by
        calc
          _ ≤ ((Polynomial.X : Polynomial ℝ) ^ 2).natDegree + P.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 2 + P.natDegree := congrArg (fun d : ℕ => d + P.natDegree)
            (Polynomial.natDegree_X_pow (R := ℝ) 2)
      have hQn : Q.natDegree < n := by omega
      have hQdegree : Q.degree < (Finset.univ : Finset (Fin n)).card := by
        have hcast : (Q.natDegree : WithBot ℕ) < (n : WithBot ℕ) :=
          WithBot.coe_lt_coe.mpr hQn
        have hdeg : Q.degree < (n : WithBot ℕ) :=
          (Polynomial.degree_le_natDegree (p := Q)).trans_lt hcast
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot] using hdeg
      have hQzero : Q = 0 := by
        apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
          (s := (Finset.univ : Finset (Fin n))) hRates.injOn hQdegree
        intro i hi
        have ht := hTrace i
        rw [res_counting_trace_factorization] at ht
        field_simp [di_ne_zero rates hRates i] at ht
        simpa only [Q, P, Polynomial.eval_mul, Polynomial.eval_X_pow, mul_zero] using ht
      change (Polynomial.X : Polynomial ℝ) ^ 2 * P = 0 at hQzero
      exact (mul_eq_zero.mp hQzero).resolve_left (pow_ne_zero 2 Polynomial.X_ne_zero)
    · intro hP i
      rw [res_counting_trace_factorization, hP]
      simp

/-- Coefficient extraction at -lambda_i keeps the actual di orientation.
Here the degree is n-3 and p<=1; the older n-4 receiving lemma is not used. -/
private theorem trace_scalar_moment (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hn4 : 4 ≤ n)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n - 3) (p : ℕ) (hp : p ≤ 1) :
    ∑ i, rates i ^ p * P.eval (rates i) / di rates i = 0 := by
  classical
  let Q : Polynomial ℝ := (Polynomial.X ^ p * P).comp (-Polynomial.X)
  have hQbound : Q.natDegree ≤ p + P.natDegree := by
    calc
      _ ≤ (Polynomial.X ^ p * P).natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ = (Polynomial.X ^ p * P).natDegree := by simp
      _ ≤ p + P.natDegree := by
        simpa only [Polynomial.natDegree_X_pow] using
          (Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ) ^ p) (q := P))
  have hQlt : Q.natDegree < n - 1 := by omega
  have hQn : Q.natDegree < n := by omega
  have hQdegree : Q.degree < (Finset.univ : Finset (Fin n)).card := by
    have hcast : (Q.natDegree : WithBot ℕ) < (n : WithBot ℕ) :=
      WithBot.coe_lt_coe.mpr hQn
    have hdeg : Q.degree < (n : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree (p := Q)).trans_lt hcast
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot] using hdeg
  have hNodes : Function.Injective (fun i : Fin n => -rates i) := by
    intro i j hij
    exact hRates (neg_injective hij)
  have hDen (i : Fin n) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ((-rates i) - (-rates j))) = di rates i := by
    unfold di
    apply Finset.prod_congr rfl
    intro j hj
    ring
  have hCoeff := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin n)))
    (v := fun i : Fin n => -rates i) (P := Q) hNodes.injOn hQdegree
  have hZero : Q.coeff (n - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hQlt
  have hh := hCoeff.symm.trans (by
    simpa only [Finset.card_univ, Fintype.card_fin] using hZero)
  simpa only [Finset.card_univ, Fintype.card_fin, hDen, Q,
    Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X_pow,
    Polynomial.eval_neg, Polynomial.eval_X, neg_neg] using hh

/-- The reciprocal-rate row identity remains valid at a zero rate. -/
theorem res_trace_reciprocal_rate_annihilator (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (R : P3) (hR : QAdmissible n R) :
    ∑ i, residualCountingTrace a (Res rates R) i / rates i = 0 := by
  classical
  rcases hR with rfl | ⟨hn4, hDegree⟩
  · simp [res_zero, residualCountingTrace]
  · have hP := tracePolynomial_natDegree a rates hn4 R (Or.inr ⟨hn4, hDegree⟩)
    calc
      _ = ∑ i, rates i ^ 1 * (tracePolynomial a rates R).eval (rates i) / di rates i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [res_counting_trace_factorization]
        by_cases hi0 : rates i = 0
        · simp [hi0]
        · field_simp [hi0, di_ne_zero rates hRates i]
      _ = 0 := trace_scalar_moment rates hRates hn4 _ hP 1 (by omega)

/-- Reciprocal-square cancellation requires every residual rate nonzero. -/
theorem res_trace_reciprocal_square_annihilator (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hNZ : ∀ i, rates i ≠ 0) (R : P3) (hR : QAdmissible n R) :
    ∑ i, residualCountingTrace a (Res rates R) i / rates i ^ 2 = 0 := by
  classical
  rcases hR with rfl | ⟨hn4, hDegree⟩
  · simp [res_zero, residualCountingTrace]
  · have hP := tracePolynomial_natDegree a rates hn4 R (Or.inr ⟨hn4, hDegree⟩)
    calc
      _ = ∑ i, rates i ^ 0 * (tracePolynomial a rates R).eval (rates i) / di rates i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [res_counting_trace_factorization]
        field_simp [hNZ i, di_ne_zero rates hRates i]
      _ = 0 := trace_scalar_moment rates hRates hn4 _ hP 0 (by omega)

/-- Exact missing zero-node contribution, without selecting that node. -/
theorem res_trace_zero_rate_correction (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (R : P3) (hR : QAdmissible n R) :
    (∑ i, residualCountingTrace a (Res rates R) i / rates i ^ 2) +
      (∑ i ∈ (Finset.univ.filter (fun i => rates i = 0)),
        (tracePolynomial a rates R).eval 0 / di rates i) = 0 := by
  classical
  rcases hR with rfl | ⟨hn4, hDegree⟩
  · simp [res_zero, residualCountingTrace, tracePolynomial_zero]
  · have hP := tracePolynomial_natDegree a rates hn4 R (Or.inr ⟨hn4, hDegree⟩)
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      _ = ∑ i, rates i ^ 0 * (tracePolynomial a rates R).eval (rates i) / di rates i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [res_counting_trace_factorization]
        by_cases hi0 : rates i = 0
        · simp [hi0]
        · simp only [hi0, ite_false, add_zero, pow_zero, one_mul]
          field_simp [hi0, di_ne_zero rates hRates i]
      _ = 0 := trace_scalar_moment rates hRates hn4 _ hP 0 (by omega)

theorem res_trace_positive_annihilators (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hPos : ∀ i, 0 < rates i) (R : P3) (hR : QAdmissible n R) :
    (∑ i, residualCountingTrace a (Res rates R) i / rates i ^ 2 = 0) ∧
    (∑ i, residualCountingTrace a (Res rates R) i / rates i = 0) := by
  exact ⟨res_trace_reciprocal_square_annihilator a rates hRates
    (fun i => ne_of_gt (hPos i)) R hR,
    res_trace_reciprocal_rate_annihilator a rates hRates R hR⟩

/-- The imposed trace-free ordinary kernel, not just an appended equivalence.
Its unique quotient has P=0; the desired trace equation is part of the left side. -/
theorem complete_ordinary_H2_counting_trace_kernel (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E) :
    (NullRegular rates E ∧ ResidualTraceFree a E) ↔ ∃! R : P3,
      SymPoly R ∧ QAdmissible n R ∧ E = Res rates R ∧ tracePolynomial a rates R = 0 := by
  constructor
  · rintro ⟨hData, hTrace⟩
    obtain ⟨R, hR, hUnique⟩ := (complete_ordinary_H2_kernel rates hRates E hSym).mp hData
    have hP : tracePolynomial a rates R = 0 := by
      apply (res_trace_free_iff_tracePolynomial_zero a rates hRates R hR.2.1).mp
      rw [← hR.2.2]
      exact hTrace
    refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2, hP⟩, ?_⟩
    intro S hS
    exact hUnique S ⟨hS.1, hS.2.1, hS.2.2.1⟩
  · rintro ⟨R, ⟨hRSym, hAdm, rfl, hP⟩, _⟩
    exact ⟨res_nullRegular rates hRates R hAdm,
      (res_trace_free_iff_tracePolynomial_zero a rates hRates R hAdm).mpr hP⟩

/-- Literal physical two-frame/full-H2 equivalence in common calibrated a,c,rates.
Full symmetry, common ground and trace are all derived inside this theorem.
There is no desired trace, P, rank, reconstruction or calibration-recovery premise. -/
theorem physical_pair_H2_counting_trace_residue
    (μ : ℝ) (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hPos : ∀ i, 0 < rates i)
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1) (ha : ∀ r, a r ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c) :
    SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a) ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧
        C145PhysicalFrame.T Q1 a - C145PhysicalFrame.T Q0 a = groundZero (Res rates R) ∧
        ResidualTraceFree a (Res rates R) ∧ tracePolynomial a rates R = 0 := by
  have hG := physical_commonGround Q0 Q1 a c hQ0 hQ1 hG0 hG1
  have hSym0 := physical_fullSym Q0 a
  have hSym1 := physical_fullSym Q1 a
  have hTrace := physical_pair_difference_trace_free Q0 Q1 a c hQ0 hQ1 ha hG0 hG1
  constructor
  · intro hData
    have hResidual := samePositive_residual_of_commonGround μ rates _ _ hG hData
    obtain ⟨R, hR, hUnique⟩ :=
      (equal_positive_H2_iff_residue_difference rates hRates hPos _ _
        (residual_fullSym _ hSym0) (residual_fullSym _ hSym1)).mp hResidual
    have hFull : C145PhysicalFrame.T Q1 a - C145PhysicalFrame.T Q0 a =
        groundZero (Res rates R) := by
      rw [commonGround_difference _ _ hG, hR.2.2]
    have hTraceR : ResidualTraceFree a (Res rates R) := by
      rw [← hR.2.2]
      exact hTrace
    have hP := (res_trace_free_iff_tracePolynomial_zero a rates hRates R hR.2.1).mp hTraceR
    refine ⟨R, ⟨hR.1, hR.2.1, hFull, hTraceR, hP⟩, ?_⟩
    intro S hS
    apply res_injective_on_admissible rates hRates hS.2.1 hR.2.1
    funext i j k
    have hh := congrArg (fun U : Tensor (n + 1) => U i.succ j.succ k.succ)
      (hS.2.2.1.symm.trans hFull)
    simpa only [groundZero_succ] using hh
  · rintro ⟨R, hR, _⟩ s t hs ht
    have hz := (nullPositive_iff_nullRegular rates hPos (Res rates R)).mpr
      (res_nullRegular rates hRates R hR.2.1) s t hs ht
    have hh : H (fullRates μ rates)
        (C145PhysicalFrame.T Q1 a - C145PhysicalFrame.T Q0 a) s t = 0 := by
      rw [hR.2.2.1, H_groundZero]
      exact hz
    rw [H_sub] at hh
    exact (sub_eq_zero.mp hh).symm

/-- The zero admissible branch precedes saturated natural subtraction. -/
theorem trace_small_quotient (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (hn : n ≤ 3) (R : P3) (hR : QAdmissible n R) :
    R = 0 ∧ tracePolynomial a rates R = 0 ∧ ResidualTraceFree a (Res rates R) := by
  have hzero := (admissible_small_iff_zero hn R).mp hR
  subst R
  simp [tracePolynomial_zero, res_zero, ResidualTraceFree, residualCountingTrace]

/-- Empty residual indices need no selected node, nonzero metric, or admissibility. -/
theorem trace_n0 (a : Fin 1 → ℝ) (rates : Fin 0 → ℝ) (E : Tensor 0) (R : P3) :
    ResidualTraceFree a E ∧ tracePolynomial a rates R = 0 := by
  constructor
  · intro i
    exact Fin.elim0 i
  · simp [tracePolynomial]

end C145.H2

end
