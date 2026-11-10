/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.DiagonalPerturbation
public import LeanPool.EhrhardGaussian.Ehrhard.CompactDerivativeBounds

/-! # Uniform PSD perturbation on compact quantile boxes with a strict gap -/

@[expose] public noncomputable section

open Set
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The triple linear form subtracts the scaled output from the weighted inputs. -/
def tripleLinearForm (p q σ : ℝ) (u : Fin 3 → ℝ) : ℝ := p * u 0 + q * u 1 - σ * u 2

/-- The base diagonal perturbation matrix contains the weighted quantile coordinates and the
negative cubic output scale. -/
def tripleD0 (p q σ : ℝ) (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![p * u 0, q * u 1, -σ ^ 3 * u 2]

/-- The perturbation coefficients normalize the two input weights and the output scale by one plus
the inverse scale. -/
def tripleEcoeff (p q σ : ℝ) (i : Fin 3) : ℝ := ![p, q, σ] i / (1 + σ⁻¹)

/-- The perturbation weight matrix is diagonal with the normalized triple coefficients. -/
def tripleE (p q σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (tripleEcoeff p q σ)

/-- The perturbed diagonal subtracts the scaled triple linear form times each perturbation
coefficient. -/
def triplePerturbationDiagonal (p q σ c : ℝ) (u : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ![p * u 0, q * u 1, -σ ^ 3 * u 2] i - c * tripleLinearForm p q σ u * tripleEcoeff p q σ i

/-- Nonnegative input weights and positive output scale make the perturbation weight matrix positive
semidefinite. -/
theorem tripleE_posSemidef {p q σ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hσ : 0 < σ) :
    (tripleE p q σ).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  have hden : 0 ≤ 1 + σ⁻¹ := by positivity
  fin_cases i
  · exact div_nonneg hp hden
  · exact div_nonneg hq hden
  · exact div_nonneg hσ.le hden

/-- The perturbation weight quadratic form on the Hessian kernel vector has the stated
normalization. -/
theorem tripleE_kernel (p q : ℝ) {σ : ℝ} (hsum : p + q = 1) (hσ : 0 < σ) :
    σ ^ 2 * tripleEcoeff p q σ 0 + σ ^ 2 * tripleEcoeff p q σ 1 + tripleEcoeff p q σ 2 = σ ^ 2 := by
  have hq : q = 1 - p := by linarith only [hsum]
  subst q
  dsimp only [tripleEcoeff]
  norm_num
  field_simp
  ring

/-- The perturbed diagonal quadratic form on the Hessian kernel vector equals the scaled linear gap.
-/
theorem triplePerturbationDiagonal_kernel (p q : ℝ) {σ : ℝ}
    (hsum : p + q = 1) (hσ : 0 < σ) (c : ℝ) (u : Fin 3 → ℝ) :
    σ ^ 2 * triplePerturbationDiagonal p q σ c u 0 +
      σ ^ 2 * triplePerturbationDiagonal p q σ c u 1 +
        triplePerturbationDiagonal p q σ c u 2 = σ ^ 2 * (1 - c) * tripleLinearForm p q σ u := by
  have hE := tripleE_kernel p q hsum hσ
  simp only [triplePerturbationDiagonal]
  norm_num
  calc
    _ = σ ^ 2 * tripleLinearForm p q σ u - c * tripleLinearForm p q σ u *
        (σ ^ 2 * tripleEcoeff p q σ 0 + σ ^ 2 * tripleEcoeff p q σ 1 + tripleEcoeff p q σ 2) := by
      dsimp only [tripleLinearForm]
      ring
    _ = _ := by rw [hE]; ring

/-- The perturbed diagonal matrix equals the base diagonal minus the weighted linear form
perturbation. -/
theorem triplePerturbationDiagonal_eq (p q σ c : ℝ) (u : Fin 3 → ℝ) :
    Matrix.diagonal (triplePerturbationDiagonal p q σ c u) =
      tripleD0 p q σ u - (c * tripleLinearForm p q σ u) • tripleE p q σ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tripleD0, tripleE, triplePerturbationDiagonal]
  · simp [tripleD0, tripleE, hij]

/-- Bounded quantile coordinates give a uniform bound on every perturbed diagonal entry. -/
theorem exists_bound_triplePerturbationDiagonal (p q σ c L : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Fin 3 → ℝ, (∀ i, |u i| ≤ L) →
      ∀ i, |triplePerturbationDiagonal p q σ c u i| ≤ M := by
  have hcont : Continuous (triplePerturbationDiagonal p q σ c) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [triplePerturbationDiagonal, tripleLinearForm] <;> fun_prop
  obtain ⟨C, hC⟩ := (isCompact_probabilitySubbox (k := 3) (-L) L).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu i
  have hi := norm_le_pi_norm (triplePerturbationDiagonal p q σ c u) i
  exact hi.trans ((hC u (fun j => abs_le.mp (hu j))).trans (le_max_left _ _))

/-- A uniform coefficient suffices on any fixed compact quantile box and
strictly negative linear sublevel. Range and gap are independent parameters. -/
theorem exists_triplePerturbation_posSemidef {p q ρ σ δ κ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ) (L : ℝ) :
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ u : Fin 3 → ℝ,
      (∀ i, |u i| ≤ L) → tripleLinearForm p q σ u ≤ -κ →
      (tripleD0 p q σ u + S • tripleHessianMatrix p q ρ σ -
        ((1 + δ) * tripleLinearForm p q σ u) • tripleE p q σ).PosSemidef := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_triplePerturbationDiagonal p q σ (1 + δ) L
  let K := σ ^ 2 * δ * κ
  let m := (1 - |ρ|) * min (p ^ 2) (q ^ 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hm : 0 < m := tripleHessianMatrix_gap_pos hp.ne' hq.ne' hρ
  let S₀ := (K * M + 2 * σ ^ 2 * M ^ 2) / (K * m)
  have hS₀ : 0 ≤ S₀ := by dsimp only [S₀]; positivity
  refine ⟨S₀, hS₀, ?_⟩
  intro S hS u hu hgap
  have hcoeff : K * M + 2 * σ ^ 2 * M ^ 2 ≤ K * (S * m) := by
    have h := (div_le_iff₀ (mul_pos hK hm)).mp hS
    dsimp only [S₀] at hS
    nlinarith only [h]
  have hk : K ≤ σ ^ 2 * triplePerturbationDiagonal p q σ (1 + δ) u 0 +
      σ ^ 2 * triplePerturbationDiagonal p q σ (1 + δ) u 1 +
        triplePerturbationDiagonal p q σ (1 + δ) u 2 := by
    rw [triplePerturbationDiagonal_kernel p q hsum hσ]
    have h := mul_le_mul_of_nonneg_left hgap (mul_nonneg (sq_nonneg σ) hδ.le)
    dsimp only [K]
    nlinarith only [h]
  have h := diagonal_add_smul_posSemidef (tripleHessianMatrix_isHermitian p q ρ σ)
    (tripleHessianMatrix_quadratic_lower_bound p q σ hρ.le)
    (hS₀.trans hS) hK hM (hbound u hu 0) (hbound u hu 1) hk hcoeff
  rw [triplePerturbationDiagonal_eq] at h
  convert h using 1; abel

/-- Increasing the time-correction coefficient only adds a PSD matrix on the
negative sublevel. Thus no upper bound on that coefficient is required. -/
theorem exists_triplePerturbation_posSemidef_of_ge {p q ρ σ δ κ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ) (L : ℝ) :
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ c : ℝ, 1 + δ ≤ c → ∀ u : Fin 3 → ℝ,
      (∀ i, |u i| ≤ L) → tripleLinearForm p q σ u ≤ -κ →
      (tripleD0 p q σ u + S • tripleHessianMatrix p q ρ σ -
        (c * tripleLinearForm p q σ u) • tripleE p q σ).PosSemidef := by
  obtain ⟨S₀, hS₀, hbase⟩ := exists_triplePerturbation_posSemidef hp hq hsum hρ hσ hδ hκ L
  refine ⟨S₀, hS₀, ?_⟩
  intro S hS c hc u hu hgap
  have hscalar : 0 ≤ -((c - (1 + δ)) * tripleLinearForm p q σ u) := by
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (hgap.trans (neg_nonpos.mpr hκ.le))
  have h := (hbase S hS u hu hgap).add ((tripleE_posSemidef hp.le hq.le hσ).smul hscalar)
  convert h using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The middle matrix from the covariance-Hessian computation is PSD for a sufficiently large
squared functional parameter. -/
theorem exists_tripleHessian_posSemidef {p q ρ σ δ κ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ) (L : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ r c : ℝ, Q ≤ r ^ 2 → 1 + δ ≤ c → ∀ u : Fin 3 → ℝ,
      (∀ i, |u i| ≤ L) → tripleLinearForm p q σ u ≤ -κ →
      (tripleD0 p q σ u - (r ^ 2 * tripleLinearForm p q σ u) • tripleHessianMatrix p q ρ σ -
        (c * tripleLinearForm p q σ u) • tripleE p q σ).PosSemidef := by
  obtain ⟨S₀, hS₀, hbase⟩ := exists_triplePerturbation_posSemidef_of_ge hp hq hsum hρ hσ hδ hκ L
  refine ⟨S₀ / κ, div_nonneg hS₀ hκ.le, ?_⟩
  intro r c hr hc u hu hgap
  have hcoef : S₀ ≤ -(r ^ 2 * tripleLinearForm p q σ u) := by
    have h₁ := (div_le_iff₀ hκ).mp hr
    have h₂ := mul_le_mul_of_nonneg_left hgap (sq_nonneg r)
    nlinarith only [h₁, h₂]
  have h := hbase (-(r ^ 2 * tripleLinearForm p q σ u)) hcoef c hc u hu hgap
  simpa only [neg_smul, sub_eq_add_neg] using h

end EhrhardGaussian.Ehrhard

end
