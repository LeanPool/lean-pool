/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145H2GridResidueInverse

/-!
C145: complete ordinary, unshifted, fully symmetric residual H2 kernel.
Compile-free source proposal; no elaboration or verification verdict.

The imported actual numerator, Box, regular response, grid inverse and
three-plane factorization are used unchanged. Coordinates are z=X 0,
x=X 1, y=X 2. Individual real rates need only be injective. Positivity is
assumed only in the named all-positive-data corollaries. No additive
nonresonance, supplied divisibility/reconstruction or rank premise occurs.
-/

@[expose] public section

noncomputable section

namespace C145.H2

open MvPolynomial C145.ThreePlane

variable {n : ℕ}

/-- Literal source coordinate bound, retaining negative-bound meaning at n<4. -/
def QAdmissible (n : ℕ) (R : P3) : Prop :=
  R = 0 ∨ (4 ≤ n ∧ ∀ r : Fin 3, degreeOf r R ≤ n - 4)

/-- Actual XiR negative-node residues, with x-input/y-input/z-output order.
Only individual oriented gap products occur in the denominator. -/
def Res (rates : Fin n → ℝ) (R : P3) : Tensor n :=
  fun i j k => MvPolynomial.eval ![-rates k, -rates i, -rates j] (Xi * R) /
    (di rates i * di rates j * di rates k)

theorem res_eq_gridResidue (rates : Fin n → ℝ) (R : P3) :
    Res rates R = gridResidue rates (Xi * R) := rfl

/-- The literal quotient formula with the product evaluation split explicitly. -/
theorem res_entry (rates : Fin n → ℝ) (R : P3) (i j k : Fin n) :
    Res rates R i j k =
      (MvPolynomial.eval ![-rates k, -rates i, -rates j] Xi *
        MvPolynomial.eval ![-rates k, -rates i, -rates j] R) /
        (di rates i * di rates j * di rates k) := by
  simp only [Res, map_mul]

/-- Source signs at negative rates; the three factors introduce one minus sign. -/
theorem xi_negative_node_factors (a b c : ℝ) :
    MvPolynomial.eval ![-c, -a, -b] Xi =
      -((a + b - c) * (a + c - b) * (b + c - a)) := by
  simp [Xi, Lz, Ly, Lx, x, y, z]; ring

/-- Exactly the XiMinus cubic used by DRE6's receiving moment calculation. -/
theorem xi_negative_node_expansion (a b c : ℝ) :
    MvPolynomial.eval ![-c, -a, -b] Xi =
      a ^ 3 + b ^ 3 + c ^ 3 - a ^ 2 * b - a ^ 2 * c - b ^ 2 * a -
        b ^ 2 * c - c ^ 2 * a - c ^ 2 * b + 2 * a * b * c := by
  rw [xi_negative_node_factors]
  ring

/-- In particular, the repeated-node sign matches CRITIC1's trace boundary. -/
theorem xi_negative_diagonal (a b : ℝ) :
    MvPolynomial.eval ![-b, -a, -b] Xi = a ^ 2 * (a - 2 * b) := by
  rw [xi_negative_node_factors]
  ring

/-- Exact nonzero product degrees and the actual support Box derive the
quotient bound. Symmetry and plane vanishing are not additional premises here. -/
theorem quotient_admissible {F R : P3} (hBox : Box n F) (hF : F = Xi * R) :
    QAdmissible n R := by
  by_cases hR : R = 0
  · exact Or.inl hR
  · have hFne : F ≠ 0 := by
      rw [hF]
      exact mul_ne_zero xi_ne hR
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      exact hFne ((box_zero_iff F).mp hBox)
    have hdegree : ∀ r : Fin 3, 3 + degreeOf r R < n := by
      intro r
      have hd := factor_degree hF hFne r
      have hb := (box_iff_degree_lt hn F).mp hBox r
      omega
    have hn4 : 4 ≤ n := by
      have hd := hdegree 0
      omega
    refine Or.inr ⟨hn4, fun r => ?_⟩
    have hd := hdegree r
    omega

/-- Upper degree bounds suffice in the converse, even when R is zero. -/
theorem box_xi_mul_of_admissible {R : P3} (hR : QAdmissible n R) :
    Box n (Xi * R) := by
  rcases hR with rfl | ⟨hn4, hdegree⟩
  · simp [Box]
  · apply (box_iff_degree_lt (by omega) (Xi * R)).mpr
    intro r
    have hd : degreeOf r (Xi * R) ≤ 3 + degreeOf r R := by
      simpa only [xi_degree] using (degreeOf_mul_le r Xi R)
    have hbound := hdegree r
    omega

/-- The actual support condition on XiR is exactly the literal admissibility. -/
theorem box_xi_mul_iff_admissible (R : P3) :
    Box n (Xi * R) ↔ QAdmissible n R :=
  ⟨fun h => quotient_admissible h rfl, box_xi_mul_of_admissible⟩

theorem xi_mul_symmetric {R : P3} (hR : SymPoly R) : SymPoly (Xi * R) := by
  intro e
  rw [map_mul, xi_symmetric e, hR e]

theorem rhoZ_xi_mul (R : P3) : rhoZ (Xi * R) = 0 := by
  simp only [Xi, map_mul, rhoZ_Lz, zero_mul]

/-- Full polynomial kernel: the unique symmetric admissible quotient is
obtained from symmetry and the actual plane identity, not assumed. -/
theorem complete_polynomial_kernel (F : P3) (hSym : SymPoly F) (hBox : Box n F) :
    rhoZ F = 0 ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ F = Xi * R := by
  constructor
  · intro hz
    obtain ⟨R, hR, _⟩ := symmetric_three_plane_factor hSym hz
    refine ⟨R, ⟨hR.2.1, quotient_admissible hBox hR.1, hR.1⟩, ?_⟩
    intro S hS
    exact quotient_unique hS.2.2 hR.1
  · rintro ⟨R, hR, _⟩
    rw [hR.2.2]
    exact rhoZ_xi_mul R

/-- The accepted actual grid inverse identifies the quotient with its literal
residues. Admissibility derives the required Box; reconstruction is a conclusion. -/
theorem numerator_eq_xi_iff_res (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (R : P3)
    (hR : QAdmissible n R) :
    numerator rates E = Xi * R ↔ E = Res rates R := by
  rw [res_eq_gridResidue]
  exact numerator_eq_iff_gridResidue rates hRates E (Xi * R)
    (box_xi_mul_of_admissible hR)

theorem numerator_res (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (R : P3) (hR : QAdmissible n R) :
    numerator rates (Res rates R) = Xi * R :=
  (numerator_eq_xi_iff_res rates hRates (Res rates R) R hR).mpr rfl

/-- Every symmetric admissible quotient really gives a fully symmetric tensor. -/
theorem res_symmetric (rates : Fin n → ℝ) (R : P3) (hR : SymPoly R) :
    FullSymTensor (Res rates R) := by
  rw [res_eq_gridResidue]
  exact gridResidue_symmetric rates (Xi * R) (xi_mul_symmetric hR)

/-- Every admissible quotient really gives zero actual ordinary response on
regular positive points; the converse does not require quotient symmetry. -/
theorem res_nullRegular (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (R : P3) (hR : QAdmissible n R) : NullRegular rates (Res rates R) := by
  apply (ordinary_data_iff_plane rates (Res rates R)).mpr
  rw [numerator_res rates hRates R hR]
  exact rhoZ_xi_mul R

/-- Admissible parameters have distinct actual residues, including n=0. -/
theorem res_injective_on_admissible (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) {R S : P3}
    (hR : QAdmissible n R) (hS : QAdmissible n S)
    (h : Res rates R = Res rates S) : R = S := by
  apply mul_left_cancel₀ xi_ne
  calc
    Xi * R = numerator rates (Res rates R) := (numerator_res rates hRates R hR).symm
    _ = numerator rates (Res rates S) := congrArg (numerator rates) h
    _ = Xi * S := numerator_res rates hRates S hS

/-- Complete all-n ordinary H2 kernel from the literal response. Only individual
rate injectivity is assumed. All three tensor slots are symmetric. -/
theorem complete_ordinary_H2_kernel (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (hSym : FullSymTensor E) :
    NullRegular rates E ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ E = Res rates R := by
  constructor
  · intro hdata
    obtain ⟨R, hR, hUnique⟩ :=
      (complete_polynomial_kernel (numerator rates E)
        (numerator_symmetric rates E hSym) (numerator_box rates E)).mp
        ((ordinary_data_iff_plane rates E).mp hdata)
    refine ⟨R, ⟨hR.1, hR.2.1,
      (numerator_eq_xi_iff_res rates hRates E R hR.2.1).mp hR.2.2⟩, ?_⟩
    intro S hS
    exact hUnique S ⟨hS.1, hS.2.1,
      (numerator_eq_xi_iff_res rates hRates E S hS.2.1).mpr hS.2.2⟩
  · rintro ⟨R, hR, _⟩
    rw [hR.2.2]
    exact res_nullRegular rates hRates R hR.2.1

/-- Exact physical positive-rate corollary, with all positive data points. -/
theorem complete_positive_H2_kernel (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (E : Tensor n) (hSym : FullSymTensor E) :
    NullPositive rates E ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ E = Res rates R := by
  rw [nullPositive_iff_nullRegular rates hPos E]
  exact complete_ordinary_H2_kernel rates hRates E hSym

/-- Equality of two ordinary positive H2 responses is exactly the unique
admissible residue difference S2-S1, with the source direction explicit. -/
theorem equal_positive_H2_iff_residue_difference (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (S1 S2 : Tensor n) (hS1 : FullSymTensor S1) (hS2 : FullSymTensor S2) :
    SamePositive rates S1 S2 ↔
      ∃! R : P3, SymPoly R ∧ QAdmissible n R ∧ S2 - S1 = Res rates R := by
  have hd : SamePositive rates S1 S2 ↔ NullPositive rates (S2 - S1) := by
    constructor
    · intro h s t hs ht
      rw [H_sub, h s t hs ht, sub_self]
    · intro h s t hs ht
      have hh := h s t hs ht
      rw [H_sub] at hh
      exact (sub_eq_zero.mp hh).symm
  rw [hd]
  exact complete_positive_H2_kernel rates hRates hPos (S2 - S1)
    (fullSymTensor_sub S2 S1 hS2 hS1)

/-- At n<=3 admissibility forces the zero polynomial, avoiding saturated
natural-degree bounds that would incorrectly allow constants at small n. -/
theorem admissible_small_iff_zero (hn : n ≤ 3) (R : P3) :
    QAdmissible n R ↔ R = 0 := by
  constructor
  · rintro (h | ⟨hn4, _⟩)
    · exact h
    · omega
  · exact Or.inl

theorem res_zero (rates : Fin n → ℝ) : Res rates (0 : P3) = 0 := by
  funext i j k
  simp [Res]

/-- The complete characterization retains the accepted small-n injectivity. -/
theorem small_n_kernel_iff_zero (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hn : n ≤ 3)
    (E : Tensor n) (hSym : FullSymTensor E) :
    NullRegular rates E ↔ E = 0 := by
  constructor
  · intro h
    obtain ⟨R, hR, _⟩ := (complete_ordinary_H2_kernel rates hRates E hSym).mp h
    rw [(admissible_small_iff_zero hn R).mp hR.2.1, res_zero] at hR
    exact hR.2.2
  · rintro rfl
    intro s t hs ht hreg
    simp [H]

theorem small_n_positive_kernel_iff_zero (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i) (hn : n ≤ 3)
    (E : Tensor n) (hSym : FullSymTensor E) :
    NullPositive rates E ↔ E = 0 := by
  rw [nullPositive_iff_nullRegular rates hPos E]
  exact small_n_kernel_iff_zero rates hRates hn E hSym

/-- Empty residual index set: the actual ordinary sum vanishes with no chosen
node, rate, or denominator, independently of the quotient presentation. -/
theorem n0_nullRegular (rates : Fin 0 → ℝ) (E : Tensor 0) : NullRegular rates E := by
  intro s t hs ht hreg
  simp [H]


end C145.H2

end
