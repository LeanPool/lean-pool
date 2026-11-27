/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145ReceivingLagrangeMoments

/-!
DRE6 Lemma 3.1 on the actual complete ordinary residual H2 kernel.
The receiving moments are those of V = gridResidue rates R, never Res rates R.
Only rate injectivity is used in the actual kernel joins. Positivity occurs
solely in the positive-data corollaries. Ground extension is literally zero
on every ground-containing entry and retains all n+1 output coordinates.
-/

@[expose] public section

noncomputable section
namespace C145.H2
open MvPolynomial C145.ThreePlane
open scoped BigOperators
variable {n : ℕ}

/-- Two non-ground power inputs and one residual output. Wpq is this same
contraction applied to the auxiliary tensor V. -/
def powerContract (rates : Fin n → ℝ) (T : Tensor n) (p q : ℕ) (k : Fin n) : ℝ :=
  ∑ i, ∑ j, rates i ^ p * rates j ^ q * T i j k

/-- Source notation Wpq for the same actual contraction of the auxiliary V. -/
abbrev Wpq (rates : Fin n → ℝ) (V : Tensor n) (p q : ℕ) (k : Fin n) : ℝ :=
  powerContract rates V p q k

/-- Literal Xi at the negative nodes, multiplied by the auxiliary V. -/
def xiWeighted (rates : Fin n → ℝ) (V : Tensor n) : Tensor n :=
  fun i j k => MvPolynomial.eval ![-rates k, -rates i, -rates j] Xi * V i j k

/-- Six literal vector identities, stated pointwise on every output. -/
def SixNull (rates : Fin n → ℝ) (T : Tensor n) : Prop :=
  ∀ k : Fin n,
    powerContract rates T 0 0 k = 0 ∧ powerContract rates T 0 1 k = 0 ∧
    powerContract rates T 0 2 k = 0 ∧ powerContract rates T 1 1 k = 0 ∧
    powerContract rates T 0 3 k + powerContract rates T 1 2 k = 0 ∧
    powerContract rates T 2 2 k + 2 * powerContract rates T 0 4 k +
      2 * powerContract rates T 1 3 k = 0

/-- The first auxiliary moment kills every contraction of first degree <=2. -/
theorem powerContract_moment_left (rates : Fin n → ℝ) (V : Tensor n)
    (hMom : AllSlotMoments rates V) (p q : ℕ) (hp : p ≤ 2) (k : Fin n) :
    powerContract rates V p q k = 0 := by
  classical
  calc
    powerContract rates V p q k =
        ∑ j, rates j ^ q * (∑ i, rates i ^ p * V i j k) := by
      unfold powerContract
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by simp only [hMom.1 p hp, mul_zero, Finset.sum_const_zero]

/-- The second auxiliary moment kills every contraction of second degree <=2. -/
theorem powerContract_moment_right (rates : Fin n → ℝ) (V : Tensor n)
    (hMom : AllSlotMoments rates V) (p q : ℕ) (hq : q ≤ 2) (k : Fin n) :
    powerContract rates V p q k = 0 := by
  classical
  calc
    powerContract rates V p q k =
        ∑ i, rates i ^ p * (∑ j, rates j ^ q * V i j k) := by
      unfold powerContract
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 0 := by simp only [hMom.2.1 q hq, mul_zero, Finset.sum_const_zero]

/-- Only the symmetry of the two contracted slots is needed for Wpq=Wqp. -/
theorem powerContract_swap (rates : Fin n → ℝ) (V : Tensor n)
    (hInput : ∀ i j k, V i j k = V j i k) (p q : ℕ) (k : Fin n) :
    powerContract rates V p q k = powerContract rates V q p k := by
  classical
  unfold powerContract
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hInput i j k]
  ring

/-- The entire ten-term Xi cubic contraction, before any moments or symmetry.
This explicitly retains W(p+3,q), W(p,q+3), and all output-rate terms. -/
theorem powerContract_xiWeighted (rates : Fin n → ℝ) (V : Tensor n)
    (p q : ℕ) (k : Fin n) :
    powerContract rates (xiWeighted rates V) p q k =
      powerContract rates V (p + 3) q k + powerContract rates V p (q + 3) k +
      rates k ^ 3 * powerContract rates V p q k -
      powerContract rates V (p + 2) (q + 1) k -
      rates k * powerContract rates V (p + 2) q k -
      powerContract rates V (p + 1) (q + 2) k -
      rates k * powerContract rates V p (q + 2) k -
      rates k ^ 2 * powerContract rates V (p + 1) q k -
      rates k ^ 2 * powerContract rates V p (q + 1) k +
      2 * rates k * powerContract rates V (p + 1) (q + 1) k := by
  classical
  calc
    powerContract rates (xiWeighted rates V) p q k =
        ∑ i, ∑ j,
          (rates i ^ (p + 3) * rates j ^ q * V i j k +
           rates i ^ p * rates j ^ (q + 3) * V i j k +
           rates k ^ 3 * (rates i ^ p * rates j ^ q * V i j k) -
           rates i ^ (p + 2) * rates j ^ (q + 1) * V i j k -
           rates k * (rates i ^ (p + 2) * rates j ^ q * V i j k) -
           rates i ^ (p + 1) * rates j ^ (q + 2) * V i j k -
           rates k * (rates i ^ p * rates j ^ (q + 2) * V i j k) -
           rates k ^ 2 * (rates i ^ (p + 1) * rates j ^ q * V i j k) -
           rates k ^ 2 * (rates i ^ p * rates j ^ (q + 1) * V i j k) +
           (2 * rates k) * (rates i ^ (p + 1) * rates j ^ (q + 1) * V i j k)) := by
      unfold powerContract xiWeighted
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [xi_negative_node_expansion]
      simp only [pow_add]
      ring
    _ = _ := by
      simp only [powerContract, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]

/-- Before input symmetry, P13 has W43-W34 as well as -rate(k)*W33.
Neither W43 nor W34 is individually eliminated by the receiving moments. -/
theorem p13_before_input_swap (rates : Fin n → ℝ) (V : Tensor n)
    (hMom : AllSlotMoments rates V) (k : Fin n) :
    powerContract rates (xiWeighted rates V) 1 3 k =
      powerContract rates V 4 3 k - powerContract rates V 3 4 k -
        rates k * powerContract rates V 3 3 k := by
  have hL := powerContract_moment_left rates V hMom
  have hR := powerContract_moment_right rates V hMom
  simpa [hL, hR] using powerContract_xiWeighted rates V 1 3 k

/-- All nine relevant contractions. The last two use exactly W43=W34,
proved from input symmetry; no output-rate restriction or positivity occurs. -/
theorem nine_xi_contractions (rates : Fin n → ℝ) (V : Tensor n)
    (hInput : ∀ i j k, V i j k = V j i k) (hMom : AllSlotMoments rates V)
    (k : Fin n) :
    powerContract rates (xiWeighted rates V) 0 0 k = 0 ∧
    powerContract rates (xiWeighted rates V) 0 1 k = 0 ∧
    powerContract rates (xiWeighted rates V) 0 2 k = 0 ∧
    powerContract rates (xiWeighted rates V) 1 1 k = 0 ∧
    powerContract rates (xiWeighted rates V) 0 3 k = powerContract rates V 3 3 k ∧
    powerContract rates (xiWeighted rates V) 1 2 k = -powerContract rates V 3 3 k ∧
    powerContract rates (xiWeighted rates V) 0 4 k = powerContract rates V 3 4 k ∧
    powerContract rates (xiWeighted rates V) 1 3 k =
      -rates k * powerContract rates V 3 3 k ∧
    powerContract rates (xiWeighted rates V) 2 2 k =
      -2 * powerContract rates V 3 4 k + 2 * rates k * powerContract rates V 3 3 k := by
  have hL := powerContract_moment_left rates V hMom
  have hR := powerContract_moment_right rates V hMom
  have h43 := powerContract_swap rates V hInput 4 3 k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hL, hR] using powerContract_xiWeighted rates V 0 0 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 0 1 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 0 2 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 1 1 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 0 3 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 1 2 k
  · simpa [hL, hR] using powerContract_xiWeighted rates V 0 4 k
  · rw [p13_before_input_swap rates V hMom k, h43]
    ring
  · have h := powerContract_xiWeighted rates V 2 2 k
    simp only [Nat.reduceAdd] at h
    simp only [Std.le_refl, hR, hL, add_zero, mul_zero, h43, zero_sub, sub_zero] at h
    rw [h]
    ring

/-- Abstract finite algebra helper. Its moment and symmetry hypotheses are
fully discharged by the actual quotient in res_six_fixed_products below. -/
theorem six_fixed_products_of_moment_null (rates : Fin n → ℝ) (V : Tensor n)
    (hInput : ∀ i j k, V i j k = V j i k) (hMom : AllSlotMoments rates V) :
    SixNull rates (xiWeighted rates V) := by
  intro k
  obtain ⟨h00, h01, h02, h11, h03, h12, h04, h13, h22⟩ :=
    nine_xi_contractions rates V hInput hMom k
  refine ⟨h00, h01, h02, h11, ?_, ?_⟩
  · rw [h03, h12]
    ring
  · rw [h22, h04, h13]
    ring

private theorem fixed_input_symmetry (V : Tensor n) (hV : FullSymTensor V)
    (i j k : Fin n) : V i j k = V j i k := by
  have h := hV (Equiv.swap 1 2) ![k, i, j]
  change V ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 1 2) 1))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 1 2) 2))
      ((![k, i, j] : Fin 3 → Fin n) ((Equiv.swap 1 2) 0)) = V i j k at h
  simpa [Equiv.swap_apply_def] using h.symm

/-- Actual quotient identity, with no moment claim about Res itself. -/
theorem res_eq_xiWeighted_gridResidue (rates : Fin n → ℝ) (R : P3) :
    Res rates R = xiWeighted rates (gridResidue rates R) := by
  funext i j k
  rw [res_entry]
  simp only [xiWeighted, gridResidue, div_eq_mul_inv]
  ring

/-- DRE6 Lemma 3.1 for every actual symmetric admissible quotient, all n.
The accepted receiving theorem supplies all moments from degree bounds. -/
theorem res_six_fixed_products (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (R : P3)
    (hSym : SymPoly R) (hR : QAdmissible n R) : SixNull rates (Res rates R) := by
  obtain ⟨hV, hMom⟩ := gridResidue_receiving_moments rates hRates R hSym hR
  rw [res_eq_xiWeighted_gridResidue]
  exact six_fixed_products_of_moment_null rates (gridResidue rates R)
    (fixed_input_symmetry (gridResidue rates R) hV) hMom

/-- Every fully symmetric actual ordinary residual kernel element has the six
identities. No desired moment, product, quotient or physical premise occurs. -/
theorem ordinary_H2_six_fixed_products (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n)
    (hSym : FullSymTensor E) (hData : NullRegular rates E) : SixNull rates E := by
  obtain ⟨R, hR, _⟩ := (complete_ordinary_H2_kernel rates hRates E hSym).mp hData
  rw [hR.2.2]
  exact res_six_fixed_products rates hRates R hR.1 hR.2.1

/-- Literal zero extension: any ground input or output gives zero. -/
def groundZero (E : Tensor n) : Tensor (n + 1) :=
  Fin.cases (fun _ _ => 0)
    (fun i => Fin.cases (fun _ => 0) (fun j => Fin.cases 0 (fun k => E i j k)))

/-- Input sums remain on Fin n; output k ranges over all Fin(n+1). -/
def fullPower (rates : Fin n → ℝ) (S : Tensor (n + 1)) (p q : ℕ)
    (k : Fin (n + 1)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, rates i ^ p * rates j ^ q * S i.succ j.succ k

/-- The same six null combinations with the ground output retained. -/
def FullSixNull (rates : Fin n → ℝ) (S : Tensor (n + 1)) : Prop :=
  ∀ k : Fin (n + 1),
    fullPower rates S 0 0 k = 0 ∧ fullPower rates S 0 1 k = 0 ∧
    fullPower rates S 0 2 k = 0 ∧ fullPower rates S 1 1 k = 0 ∧
    fullPower rates S 0 3 k + fullPower rates S 1 2 k = 0 ∧
    fullPower rates S 2 2 k + 2 * fullPower rates S 0 4 k +
      2 * fullPower rates S 1 3 k = 0

theorem groundZero_ground_first (E : Tensor n) (j k : Fin (n + 1)) :
    groundZero E 0 j k = 0 := rfl

theorem groundZero_ground_second (E : Tensor n) (i k : Fin (n + 1)) :
    groundZero E i 0 k = 0 := by
  refine Fin.cases ?_ (fun a => ?_) i <;> rfl

theorem groundZero_ground_output (E : Tensor n) (i j : Fin (n + 1)) :
    groundZero E i j 0 = 0 := by
  refine Fin.cases ?_ (fun a => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun b => ?_) j <;> rfl

theorem groundZero_succ (E : Tensor n) (i j k : Fin n) :
    groundZero E i.succ j.succ k.succ = E i j k := rfl

theorem fullPower_groundZero_zero (rates : Fin n → ℝ) (E : Tensor n) (p q : ℕ) :
    fullPower rates (groundZero E) p q 0 = 0 := by
  simp [fullPower, groundZero_ground_output]

theorem fullPower_groundZero_succ (rates : Fin n → ℝ) (E : Tensor n)
    (p q : ℕ) (k : Fin n) :
    fullPower rates (groundZero E) p q k.succ = powerContract rates E p q k := rfl

/-- Honest all-output join, including n=0: ground plus every successor output. -/
theorem full_six_groundZero_iff (rates : Fin n → ℝ) (E : Tensor n) :
    FullSixNull rates (groundZero E) ↔ SixNull rates E := by
  constructor
  · intro h k
    simpa only [fullPower_groundZero_succ] using h k.succ
  · intro h k
    refine Fin.cases ?_ (fun a => ?_) k
    · simp [fullPower_groundZero_zero]
    · simpa only [fullPower_groundZero_succ] using h a

/-- Complete actual kernel, strengthened by DERIVED auxiliary moments and six
full-output null products. These extra conclusions are never hypotheses. -/
theorem complete_ordinary_H2_six_fixed_kernel (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (hSym : FullSymTensor E) :
    NullRegular rates E ↔ ∃! R : P3,
      SymPoly R ∧ QAdmissible n R ∧ E = Res rates R ∧
      AllSlotMoments rates (gridResidue rates R) ∧ FullSixNull rates (groundZero E) := by
  constructor
  · intro hData
    obtain ⟨R, hR, hUnique⟩ :=
      (complete_ordinary_H2_receiving_kernel rates hRates E hSym).mp hData
    refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2, ?_⟩, ?_⟩
    · exact (full_six_groundZero_iff rates E).mpr
        (ordinary_H2_six_fixed_products rates hRates E hSym hData)
    · intro S hS
      exact hUnique S ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  · rintro ⟨R, hR, _⟩
    rw [hR.2.2.1]
    exact res_nullRegular rates hRates R hR.2.1

/-- Equality means all six literal vector values agree, at every output. -/
def SameFullSix (rates : Fin n → ℝ) (S1 S2 : Tensor (n + 1)) : Prop :=
  ∀ k : Fin (n + 1),
    fullPower rates S2 0 0 k = fullPower rates S1 0 0 k ∧
    fullPower rates S2 0 1 k = fullPower rates S1 0 1 k ∧
    fullPower rates S2 0 2 k = fullPower rates S1 0 2 k ∧
    fullPower rates S2 1 1 k = fullPower rates S1 1 1 k ∧
    fullPower rates S2 0 3 k + fullPower rates S2 1 2 k =
      fullPower rates S1 0 3 k + fullPower rates S1 1 2 k ∧
    fullPower rates S2 2 2 k + 2 * fullPower rates S2 0 4 k +
      2 * fullPower rates S2 1 3 k =
      fullPower rates S1 2 2 k + 2 * fullPower rates S1 0 4 k +
      2 * fullPower rates S1 1 3 k

theorem fullPower_sub (rates : Fin n → ℝ) (S1 S2 : Tensor (n + 1))
    (p q : ℕ) (k : Fin (n + 1)) :
    fullPower rates (S2 - S1) p q k = fullPower rates S2 p q k -
      fullPower rates S1 p q k := by
  simp only [fullPower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Linearity of precisely the six displayed combinations. -/
theorem sameFullSix_iff_difference (rates : Fin n → ℝ) (S1 S2 : Tensor (n + 1)) :
    SameFullSix rates S1 S2 ↔ FullSixNull rates (S2 - S1) := by
  constructor
  · intro h k
    obtain ⟨h00, h01, h02, h11, h0312, h220413⟩ := h k
    simp only [fullPower_sub]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro h k
    obtain ⟨h00, h01, h02, h11, h0312, h220413⟩ := h k
    simp only [fullPower_sub] at h00 h01 h02 h11 h0312 h220413
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Actual residual-data invariance for full tensors whose difference is the
literal zero-ground extension. The common ground entries are explicit in hDiff. -/
theorem ordinary_H2_full_six_fixed (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates E) (S1 S2 : Tensor (n + 1))
    (hDiff : S2 - S1 = groundZero E) : SameFullSix rates S1 S2 := by
  apply (sameFullSix_iff_difference rates S1 S2).mpr
  rw [hDiff]
  exact (full_six_groundZero_iff rates E).mpr
    (ordinary_H2_six_fixed_products rates hRates E hSym hData)

/-- Positive-data S2-S1 join. Positivity is needed only to pass from actual
all-positive response equality to the accepted ordinary residue description. -/
theorem positive_H2_difference_six_fixed (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (S1 S2 : Tensor n) (hS1 : FullSymTensor S1) (hS2 : FullSymTensor S2)
    (hData : SamePositive rates S1 S2) :
    FullSixNull rates (groundZero (S2 - S1)) := by
  obtain ⟨R, hR, _⟩ :=
    (equal_positive_H2_iff_receiving_residue_difference rates hRates hPos S1 S2 hS1 hS2).mp hData
  apply (full_six_groundZero_iff rates (S2 - S1)).mpr
  rw [hR.2.2.1]
  exact res_six_fixed_products rates hRates R hR.1 hR.2.1

/-- Positive-data equality, with the complete unique quotient retained and
its six full-output identities derived on the right side of the equivalence. -/
theorem equal_positive_H2_iff_six_fixed_difference (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (S1 S2 : Tensor n) (hS1 : FullSymTensor S1) (hS2 : FullSymTensor S2) :
    SamePositive rates S1 S2 ↔
      (∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ S2 - S1 = Res rates R ∧
        AllSlotMoments rates (gridResidue rates R)) ∧
      FullSixNull rates (groundZero (S2 - S1)) := by
  constructor
  · intro hData
    exact ⟨(equal_positive_H2_iff_receiving_residue_difference
        rates hRates hPos S1 S2 hS1 hS2).mp hData,
      positive_H2_difference_six_fixed rates hRates hPos S1 S2 hS1 hS2 hData⟩
  · intro h
    exact (equal_positive_H2_iff_receiving_residue_difference
      rates hRates hPos S1 S2 hS1 hS2).mpr h.1

/-- The six vectors agree on full tensors with the displayed residual
positive-H2 difference. No physical calibration or response inference is claimed. -/
theorem positive_H2_full_six_fixed (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (S1 S2 : Tensor n) (hS1 : FullSymTensor S1) (hS2 : FullSymTensor S2)
    (hData : SamePositive rates S1 S2) (U1 U2 : Tensor (n + 1))
    (hDiff : U2 - U1 = groundZero (S2 - S1)) : SameFullSix rates U1 U2 := by
  apply (sameFullSix_iff_difference rates U1 U2).mpr
  rw [hDiff]
  exact positive_H2_difference_six_fixed rates hRates hPos S1 S2 hS1 hS2 hData

end C145.H2

end
