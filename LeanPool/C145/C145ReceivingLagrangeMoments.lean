/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145CompleteOrdinaryH2Kernel

/-!
C145: actual receiving Lagrange moments of the unique admissible H2 quotient.

All accepted definitions and sources are imported unchanged. Coordinates are
z=X 0, x=X 1, y=X 2; gridResidue rates R i j k evaluates R at
![-rates k,-rates i,-rates j]. Only individual-rate injection is used for the
moments. Positivity occurs solely in the positive-data difference corollary.
No desired moment, divisibility, reconstruction, trace or physical premise
is supplied. This file stops before six-product and ground/physical joins.
-/

@[expose] public section

noncomputable section

namespace C145.H2

open MvPolynomial C145.ThreePlane
open scoped BigOperators

variable {n : ℕ}

/-- The three literal finite-sum moments, with the power on the summed slot. -/
def AllSlotMoments (rates : Fin n → ℝ) (T : Tensor n) : Prop :=
  (∀ p : ℕ, p ≤ 2 → ∀ j k : Fin n, ∑ i, rates i ^ p * T i j k = 0) ∧
  (∀ p : ℕ, p ≤ 2 → ∀ i k : Fin n, ∑ j, rates j ^ p * T i j k = 0) ∧
  (∀ p : ℕ, p ≤ 2 → ∀ i j : Fin n, ∑ k, rates k ^ p * T i j k = 0)

/-- Coefficient extraction at the actual negative nodes, with the actual
oriented gaps. The guard n>=4 comes from nonzero admissibility downstream. -/
theorem receiving_scalar_moment (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hn4 : 4 ≤ n)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n - 4)
    (p : ℕ) (hp : p ≤ 2) :
    ∑ i, rates i ^ p * P.eval (-rates i) / di rates i = 0 := by
  classical
  let Q : Polynomial ℝ := Polynomial.X ^ p * P
  have hQbound : Q.natDegree ≤ p + P.natDegree := by
    simpa only [Q, Polynomial.natDegree_X_pow] using
      (Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ) ^ p) (q := P))
  have hQlt : Q.natDegree < n - 1 := by omega
  have hQn : Q.natDegree < n := by omega
  have hcast : (Q.natDegree : WithBot ℕ) < (n : WithBot ℕ) :=
    WithBot.coe_lt_coe.mpr hQn
  have hQdegree : Q.degree < (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Polynomial.degree_le_natDegree (p := Q)).trans_lt hcast
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
  have hCoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin n)))
    (v := fun i : Fin n => -rates i) (P := Q) hNodes.injOn hQdegree
  have hZero : Q.coeff (n - 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hQlt
  have hRaw : ∑ i, (-rates i) ^ p * P.eval (-rates i) / di rates i = 0 := by
    have hh := hCoeff.symm.trans (by
      simpa only [Finset.card_univ, Fintype.card_fin] using hZero)
    simpa only [Finset.card_univ, Fintype.card_fin, hDen, Q,
      Polynomial.eval_mul, Polynomial.eval_X_pow] using hh
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 by omega) with rfl | rfl | rfl
  · simpa only [pow_zero, one_mul] using hRaw
  · calc
      (∑ i, rates i ^ 1 * P.eval (-rates i) / di rates i) =
          -(∑ i, (-rates i) ^ 1 * P.eval (-rates i) / di rates i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hRaw, neg_zero]
  · calc
      (∑ i, rates i ^ 2 * P.eval (-rates i) / di rates i) =
          ∑ i, (-rates i) ^ 2 * P.eval (-rates i) / di rates i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := hRaw

/-- Isolate only the actual output coordinate zero; no generic slice API. -/
private def receivingSlice (R : P3) (v : Fin 2 → ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval v) (finSuccEquiv ℝ 2 R)

private theorem receivingSlice_eval (R : P3) (v : Fin 2 → ℝ) (u : ℝ) :
    (receivingSlice R v).eval u =
      MvPolynomial.eval (Fin.cons u v : Fin 3 → ℝ) R := by
  unfold receivingSlice
  rw [← MvPolynomial.eval_eq_eval_mv_eval']

private theorem receivingSlice_natDegree (R : P3) (v : Fin 2 → ℝ) :
    (receivingSlice R v).natDegree ≤ degreeOf (0 : Fin 3) R := by
  calc
    (receivingSlice R v).natDegree ≤ (finSuccEquiv ℝ 2 R).natDegree :=
      Polynomial.natDegree_map_le
    _ = degreeOf (0 : Fin 3) R := natDegree_finSuccEquiv _

/-- The literal quotient-residue output moments follow from admissibility.
The zero branch precedes every use of n-4, retaining all small dimensions. -/
theorem gridResidue_output_moment (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (R : P3) (hR : QAdmissible n R)
    (p : ℕ) (hp : p ≤ 2) (i j : Fin n) :
    ∑ k, rates k ^ p * gridResidue rates R i j k = 0 := by
  classical
  rcases hR with rfl | ⟨hn4, hDegree⟩
  · simp [gridResidue]
  · have hSlice : (receivingSlice R ![-rates i, -rates j]).natDegree ≤ n - 4 :=
      (receivingSlice_natDegree R ![-rates i, -rates j]).trans (hDegree 0)
    have hm := receiving_scalar_moment rates hRates hn4
      (receivingSlice R ![-rates i, -rates j]) hSlice p hp
    have hm' :
        (∑ k, rates k ^ p *
          MvPolynomial.eval ![-rates k, -rates i, -rates j] R / di rates k) = 0 := by
      have hv (k : Fin n) :
          (Fin.cons (-rates k) ![-rates i, -rates j] : Fin 3 → ℝ) =
            ![-rates k, -rates i, -rates j] := by
        funext r
        fin_cases r <;> rfl
      simpa only [receivingSlice_eval, hv] using hm
    calc
      (∑ k, rates k ^ p * gridResidue rates R i j k) =
          (∑ k, rates k ^ p *
            MvPolynomial.eval ![-rates k, -rates i, -rates j] R / di rates k) /
              (di rates i * di rates j) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        unfold gridResidue
        field_simp [di_ne_zero rates hRates i, di_ne_zero rates hRates j,
          di_ne_zero rates hRates k]
      _ = 0 := by rw [hm']; exact zero_div _

private theorem receiving_swap_first_output (T : Tensor n)
    (hT : FullSymTensor T) (i j k : Fin n) : T i j k = T k j i := by
  have h := hT (Equiv.swap 0 1) ![k, i, j]
  change T ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 1) 1))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 1) 2))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 1) 0)) = T i j k at h
  simpa [Equiv.swap_apply_def] using h.symm

private theorem receiving_swap_second_output (T : Tensor n)
    (hT : FullSymTensor T) (i j k : Fin n) : T i j k = T i k j := by
  have h := hT (Equiv.swap 0 2) ![k, i, j]
  change T ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 2) 1))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 2) 2))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 0 2) 0)) = T i j k at h
  simpa [Equiv.swap_apply_def] using h.symm

/-- Full symmetry and all three moments are derived from the actual accepted
symmetric admissible quotient, for every n and every p=0,1,2. -/
theorem gridResidue_receiving_moments (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (R : P3)
    (hSym : SymPoly R) (hR : QAdmissible n R) :
    FullSymTensor (gridResidue rates R) ∧
      AllSlotMoments rates (gridResidue rates R) := by
  have hT := gridResidue_symmetric rates R hSym
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro p hp j k
    calc
      (∑ i, rates i ^ p * gridResidue rates R i j k) =
          ∑ i, rates i ^ p * gridResidue rates R k j i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [receiving_swap_first_output (gridResidue rates R) hT i j k]
      _ = 0 := gridResidue_output_moment rates hRates R hR p hp k j
  · intro p hp i k
    calc
      (∑ j, rates j ^ p * gridResidue rates R i j k) =
          ∑ j, rates j ^ p * gridResidue rates R i k j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [receiving_swap_second_output (gridResidue rates R) hT i j k]
      _ = 0 := gridResidue_output_moment rates hRates R hR p hp i k
  · intro p hp i j
    exact gridResidue_output_moment rates hRates R hR p hp i j

/-- Actual ordinary data equivalence, strengthened by derived receiving
moments of the unique quotient. The desired moments are never a premise. -/
theorem complete_ordinary_H2_receiving_kernel (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (hSym : FullSymTensor E) :
    NullRegular rates E ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ E = Res rates R ∧
        AllSlotMoments rates (gridResidue rates R) := by
  constructor
  · intro hData
    obtain ⟨R, hR, hUnique⟩ :=
      (complete_ordinary_H2_kernel rates hRates E hSym).mp hData
    refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2,
      (gridResidue_receiving_moments rates hRates R hR.1 hR.2.1).2⟩, ?_⟩
    intro S hS
    exact hUnique S ⟨hS.1, hS.2.1, hS.2.2.1⟩
  · rintro ⟨R, hR, _⟩
    rw [hR.2.2.1]
    exact res_nullRegular rates hRates R hR.2.1

/-- Equality of actual positive ordinary H2 data yields the unique literal
S2-S1 residue difference and its derived all-slot quotient moments. -/
theorem equal_positive_H2_iff_receiving_residue_difference (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (S1 S2 : Tensor n) (hS1 : FullSymTensor S1) (hS2 : FullSymTensor S2) :
    SamePositive rates S1 S2 ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ S2 - S1 = Res rates R ∧
        AllSlotMoments rates (gridResidue rates R) := by
  constructor
  · intro hData
    obtain ⟨R, hR, hUnique⟩ :=
      (equal_positive_H2_iff_residue_difference rates hRates hPos S1 S2 hS1 hS2).mp hData
    refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2,
      (gridResidue_receiving_moments rates hRates R hR.1 hR.2.1).2⟩, ?_⟩
    intro S hS
    exact hUnique S ⟨hS.1, hS.2.1, hS.2.2.1⟩
  · rintro ⟨R, hR, hUnique⟩
    apply (equal_positive_H2_iff_residue_difference rates hRates hPos S1 S2 hS1 hS2).mpr
    refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2.1⟩, ?_⟩
    intro S hS
    exact hUnique S ⟨hS.1, hS.2.1, hS.2.2,
      (gridResidue_receiving_moments rates hRates S hS.1 hS.2.1).2⟩

/-- Literal zero quotient, without injectivity or a selected grid point. -/
theorem receiving_gridResidue_zero (rates : Fin n → ℝ) :
    gridResidue rates (0 : P3) = 0 := by
  funext i j k
  simp [gridResidue]

/-- Small n forces the actual quotient to vanish; the moments then follow
without rates, positivity or symmetry assumptions beyond admissibility. -/
theorem receiving_small_quotient (rates : Fin n → ℝ) (hn : n ≤ 3)
    (R : P3) (hR : QAdmissible n R) :
    gridResidue rates R = 0 ∧ AllSlotMoments rates (gridResidue rates R) := by
  have hZero := (admissible_small_iff_zero hn R).mp hR
  rw [hZero, receiving_gridResidue_zero]
  simp [AllSlotMoments]

/-- The empty residual index has vacuous slot moments for every tensor;
no node, nonzero gap, or finite element is selected at n=0. -/
theorem receiving_n0 (rates : Fin 0 → ℝ) (T : Tensor 0) :
    AllSlotMoments rates T := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j
    exact Fin.elim0 j
  · intro p hp i
    exact Fin.elim0 i
  · intro p hp i
    exact Fin.elim0 i


end C145.H2

end
