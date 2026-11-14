/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/FiniteProjection.lean`,
by Jeroen Zuiddam, 2026: the Fourier projection takes a period `L` with `(L : K) ≠ 0`, `L >
3(M-1)` and a primitive `L`-th root of unity, instead of `L = 5M` and `exp(2πi/5M)` in ℂ; `ℂ`
replaced by a field `K`; no declaration here needs `K` algebraically closed; unused hypothesis
renamed `_hM`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Fourier
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.NoWrap
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.SquareWeights
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Exact finite Fourier projection and square filtering

The `L`-term Fourier average (the paper: `L = 5 * M`) is applied to an arbitrary branch coefficient.
The label bounds eliminate modular wrap. The weights on the three tensor legs
then give a nonnegative square degree on every surviving branch. Taking the
constant coefficient retains exactly the branches with `g = h` and `u = v`.

The finite-family statements permit arbitrary coefficients and arbitrary
repetitions of labels; they use only linearity of the Fourier projection and
coefficient extraction, without assumptions on an ambient tensor.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- A normalized finite Fourier average of one branch coefficient. -/
noncomputable def finiteFourierCoefficient (ζ : K) (L : ℕ) (e : ℤ) (c : K) : K :=
  (L : K)⁻¹ * ∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e) * c

/-- The Fourier average is a scalar support indicator, for every coefficient. -/
theorem finiteFourierCoefficient_eq_ite {ζ : K} {L : ℕ}
    (hL : (L : K) ≠ 0) (hζ : IsPrimitiveRoot ζ L) (e : ℤ) (c : K) :
    finiteFourierCoefficient ζ L e c = if (L : ℤ) ∣ e then c else 0 := by
  unfold finiteFourierCoefficient
  rw [← Finset.sum_mul, ← mul_assoc, normalized_sum_zpow_primitive_root hL hζ]
  split_ifs <;> simp

/-- Averaging a finite family of branches agrees with averaging each branch. -/
theorem finiteFourierCoefficient_sum {ι : Type*} (s : Finset ι)
    (ζ : K) (L : ℕ) (e : ι → ℤ) (c : ι → K) :
    (L : K)⁻¹ * (∑ r ∈ Finset.range L, ∑ i ∈ s, ζ ^ ((r : ℤ) * e i) * c i) =
      ∑ i ∈ s, finiteFourierCoefficient ζ L (e i) (c i) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  rfl

/-- Exactly `L` phases select the integer support equation, for any period
`L > 3 * (M - 1)` that is nonzero in `K` (the paper uses `L = 5 * M`). -/
theorem fiveMFourierCoefficient_eq_ite {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (_hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    finiteFourierCoefficient ζ L (phase g h u v) c =
      if phase g h u v = 0 then c else 0 := by
  rw [finiteFourierCoefficient_eq_ite hL hζ]
  have hnoWrap := fourierPhase_dvd_iff_eq_zero_of_lt (M := (M : ℤ)) (L := (L : ℤ))
    (by omega) hh hg hu hv
  simp only [phase, hnoWrap]
  rfl

/-- A projected branch, recorded as an ordinary polynomial after Fourier averaging. -/
noncomputable def projectedBranchPolynomial (ζ : K) (L : ℕ)
    (g h u v : ℤ) (c : K) : Polynomial K :=
  Polynomial.monomial (totalDegree g h u v)
    (finiteFourierCoefficient ζ L (phase g h u v) c)

/-- The surviving polynomial weight is the square `(g - h)^2`. -/
theorem projectedBranchPolynomial_eq_ite {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    projectedBranchPolynomial ζ L g h u v c =
      if phase g h u v = 0 then Polynomial.monomial ((g - h) ^ 2).toNat c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hL hLM hζ hg hh hu hv]
  split_ifs with hp
  · rw [totalDegree, totalWeight_eq_sq_of_phase_eq_zero hp]
  · simp

/-- A coefficient occurs exactly on the Fourier support at its integer total weight. -/
theorem projectedBranchPolynomial_coeff {ζ : K} {M L n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff n =
      if phase g h u v = 0 ∧ totalWeight g h u v = (n : ℤ) then c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hL hLM hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · have hd : totalDegree g h u v = n ↔ totalWeight g h u v = (n : ℤ) := by
      have hcast := totalDegree_cast_of_phase_eq_zero hp
      omega
    simp only [hp, ↓reduceIte, Polynomial.coeff_monomial, hd, true_and]
  · simp [hp]

/-- Each projected branch has no polynomial coefficient above `(M - 1)^2`. -/
theorem projectedBranchPolynomial_coeff_eq_zero_of_lt
    {ζ : K} {M L n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (hn : (M - 1) ^ 2 < n) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff n = 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hL hLM hζ hg hh hu hv]
  split_ifs with hp
  · have hd := totalDegree_le_of_labels hg hh hp
    exact Polynomial.coeff_monomial_of_ne c (by omega)
  · simp

/-- Constant coefficient extraction is the exact square filter, with no restriction
on the original coefficient. -/
theorem projectedBranchPolynomial_coeff_zero {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff 0 =
      if g = h ∧ u = v then c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hL hLM hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · simp only [hp, ↓reduceIte, Polynomial.coeff_monomial,
      totalDegree_eq_zero_iff_of_phase_eq_zero hp]
  · have hlabels : ¬ (g = h ∧ u = v) := by
      rintro ⟨rfl, rfl⟩
      exact hp (by simp [phase])
    simp [hp, hlabels]

/-- Apply the finite Fourier projection and square weights branch by branch. -/
noncomputable def projectedPolynomial {ι : Type*} (s : Finset ι)
    (ζ : K) (L : ℕ) (g h u v : ι → ℤ) (c : ι → K) : Polynomial K :=
  ∑ i ∈ s, projectedBranchPolynomial ζ L (g i) (h i) (u i) (v i) (c i)

/-- Every coefficient of the projected polynomial has the exact integer support. -/
theorem projectedPolynomial_coeff {ι : Type*} (s : Finset ι)
    {ζ : K} {M L n : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).coeff n =
      ∑ i ∈ s, if phase (g i) (h i) (u i) (v i) = 0 ∧
        totalWeight (g i) (h i) (u i) (v i) = (n : ℤ) then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff hM hL hLM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- Exact finite filtering for an arbitrary finite family of branch coefficients. -/
theorem projectedPolynomial_coeff_zero {ι : Type*} (s : Finset ι)
    {ζ : K} {M L : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).coeff 0 =
      ∑ i ∈ s, if g i = h i ∧ u i = v i then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff_zero hM hL hLM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- The finite projected polynomial has support only in degrees at most `(M - 1)^2`. -/
theorem projectedPolynomial_coeff_eq_zero_of_lt {ι : Type*} (s : Finset ι)
    {ζ : K} {M L n : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M)
    (hn : (M - 1) ^ 2 < n) :
    (projectedPolynomial s ζ L g h u v c).coeff n = 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hL hLM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) hn (c i)

/-- The degree bound is independent of the number or values of the coefficients. -/
theorem projectedPolynomial_natDegree_le {ι : Type*} (s : Finset ι)
    {ζ : K} {M L : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).natDegree ≤ (M - 1) ^ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact projectedPolynomial_coeff_eq_zero_of_lt s g h u v c hM hL hLM hζ hg hh hu hv hn

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
