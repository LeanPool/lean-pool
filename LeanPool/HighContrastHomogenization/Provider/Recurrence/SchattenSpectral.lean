/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.DetOrder

/-!
# High-contrast homogenization: Provider.Recurrence.SchattenSpectral

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The spectral form of the Schatten trace

The mixed norm `‖·‖_{L^Q(S_Q)}` of the fixed-grid section is built on the
Schatten size `|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}`, whose inner power is taken by
the continuous functional calculus.  Every estimate the section makes on that
size passes through one identity: the trace of a function of a symmetric matrix
is that function summed over the eigenvalues.  The identity is the spectral
theorem plus the invariance of the trace under conjugation by the eigenvector
unitary, and it is proved here.

Two consequences are recorded because the fixed-grid proofs use them directly.
The first is that the Schatten size is a nonnegative real, so it may be compared
with the extended-real moments without a case split.  The second is the opening
display of the positive-gap estimate `l.fixed.geometry.positive.gap`: for a positive
semidefinite `D` bounded above by `t` in the Loewner order,
`tr(D^Q) ≤ t^{Q-1} tr D`, since every eigenvalue lies in `[0, t]` and the scalar
inequality `μ^Q ≤ t^{Q-1} μ` holds there.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The trace of a function of a symmetric matrix -/

/-- **The trace of a continuous function of a symmetric matrix is the function
summed over the eigenvalues.**  The functional calculus is realized as the
conjugation of a diagonal matrix by the eigenvector unitary, and the trace does
not see that conjugation. -/
theorem trace_cfc_eq_sum_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (cfc f A) = ∑ i, f (hA.eigenvalues i) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ *
      (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hform : cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
    rw [hA.cfc_eq f]
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def]
  rw [hform, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.trace_diagonal]

/-! ## Eigenvalue bounds from the Loewner order -/

/-- A Loewner bound above is a bound on every eigenvalue: the quadratic form of
`t I - A` at the `i`-th unit eigenvector is `t - eigenvalues A i`. -/
theorem eigenvalues_le_of_le_smul_one {A : Matrix n n ℝ} (hA : A.IsHermitian) {t : ℝ}
    (h : A ≤ t • (1 : Matrix n n ℝ)) (i : n) : hA.eigenvalues i ≤ t := by
  have hPS : (t • (1 : Matrix n n ℝ) - A).PosSemidef := Matrix.le_iff.mp h
  have hq := hPS.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : n → ℝ)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul,
    HCPolySupport.HighContrast.dotProduct_eigenvectorBasis_self hA i] at hq
  have hval : hA.eigenvalues i
      = star (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) := by
    simpa using hA.eigenvalues_eq i
  rw [hval]
  simp only [smul_eq_mul, mul_one] at hq
  linarith only [hq]

/-- A positive semidefinite matrix is bounded above by its own trace: every
eigenvalue is at most the sum of them all. -/
theorem le_trace_smul_one {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n ℝ) := by
  have hsum : A.trace = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  refine HCPolySupport.HighContrast.le_smul_one_of_eigenvalues_le
    hA.isHermitian fun i => ?_
  rw [hsum]
  exact Finset.single_le_sum (f := hA.isHermitian.eigenvalues)
    (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-! ## Nonnegativity of the Schatten trace -/

/-- The Schatten trace of a symmetric matrix at a nonnegative exponent is
nonnegative: the eigenvalues of `A²` are nonnegative and the real power of a
nonnegative real is nonnegative. -/
theorem zero_le_trace_cfc_rpow {A : Matrix n n ℝ} (hA : A.PosSemidef) (Q : ℝ) :
    0 ≤ Matrix.trace (cfc (fun x : ℝ => x ^ Q) A) := by
  rw [trace_cfc_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hA.eigenvalues_nonneg i) Q

/-! ## The trace-power estimate of the positive-gap lemma -/

/-- **The opening display of `l.fixed.geometry.positive.gap`.**  A positive semidefinite `D`
bounded above by `t` in the Loewner order satisfies `tr(D^Q) ≤ t^{Q-1} tr D`:
every eigenvalue lies in `[0, t]`, and there `μ^Q = μ^{Q-1} μ ≤ t^{Q-1} μ`. -/
theorem trace_cfc_rpow_le_mul_trace {A : Matrix n n ℝ} (hA : A.PosSemidef) {t Q : ℝ}
    (h : A ≤ t • (1 : Matrix n n ℝ)) (hQ : 1 ≤ Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ Q) A) ≤ t ^ (Q - 1) * A.trace := by
  have hQ1 : (0 : ℝ) ≤ Q - 1 := by linarith only [hQ]
  have hsum : A.trace = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  rw [trace_cfc_eq_sum_eigenvalues hA.isHermitian, hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlow : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
  have hhigh : hA.isHermitian.eigenvalues i ≤ t := eigenvalues_le_of_le_smul_one _ h i
  by_cases hzero : hA.isHermitian.eigenvalues i = 0
  · rw [hzero, mul_zero, Real.zero_rpow (by linarith only [hQ] : Q ≠ 0)]
  · have hpos : 0 < hA.isHermitian.eigenvalues i := lt_of_le_of_ne hlow (Ne.symm hzero)
    have hsplit : hA.isHermitian.eigenvalues i ^ Q
        = hA.isHermitian.eigenvalues i ^ (Q - 1) * hA.isHermitian.eigenvalues i := by
      have hadd : hA.isHermitian.eigenvalues i ^ (Q - 1 + 1)
          = hA.isHermitian.eigenvalues i ^ (Q - 1) * hA.isHermitian.eigenvalues i ^ (1 : ℝ) :=
        Real.rpow_add hpos _ _
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hlow hhigh hQ1) hlow

/-! ## The Schatten argument in the exponent of the reference text -/

/-- The Schatten size squares the matrix before taking the power `Q/2`.  On
positive semidefinite data the two operations collapse: the spectrum is
nonnegative, so `(x²)^{Q/2} = x^Q` there, and the functional calculus composes.
This is what identifies the Schatten trace of `D` with `tr(D^Q)`. -/
theorem trace_cfc_rpow_mul_self {A : Matrix n n ℝ} (hA : A.PosSemidef) {Q : ℝ} (hQ : 0 < Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ (Q / 2)) (A * A))
      = Matrix.trace (cfc (fun x : ℝ => x ^ Q) A) := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hspec : ∀ x ∈ spectrum ℝ A, 0 ≤ x := fun _ hx =>
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hA).2 hx
  have hsq : cfc (fun x : ℝ => x ^ (2 : ℕ)) A = A * A := by
    have h1 := cfc_pow (R := ℝ) (fun x : ℝ => x) 2 A
    rw [cfc_id' ℝ A hsa] at h1
    rw [h1, pow_two]
  have hcont : ContinuousOn (fun x : ℝ => x ^ (Q / 2))
      ((fun x : ℝ => x ^ (2 : ℕ)) '' spectrum ℝ A) := fun x _ =>
    (Real.continuousAt_rpow_const x (Q / 2) (Or.inr (by linarith only [hQ]))).continuousWithinAt
  have hcomp : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => x ^ (Q / 2)) (A * A) := by
    rw [cfc_comp (R := ℝ) (fun x : ℝ => x ^ (Q / 2)) (fun x : ℝ => x ^ (2 : ℕ)) A hsa hcont, hsq]
  have hcongr : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => x ^ Q) A := by
    refine cfc_congr (R := ℝ) fun x hx => ?_
    have hx0 : 0 ≤ x := hspec x hx
    have hnat : (x ^ (2 : ℕ) : ℝ) = x ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast x 2]
      norm_num
    have hexp : (2 : ℝ) * (Q / 2) = Q := by ring
    simp only [Function.comp_apply, hnat]
    rw [← Real.rpow_mul hx0, hexp]
  rw [← hcomp, hcongr]

/-- **The trace-power estimate in the Schatten dialect of the fixed-grid
section.**  This is `tr(D^Q) ≤ |G_hat|^{Q-1} tr D` with the left side written as the
Schatten trace of the squared matrix, the form in which the mixed norm reads
it. -/
theorem trace_cfc_rpow_mul_self_le {A : Matrix n n ℝ} (hA : A.PosSemidef) {t Q : ℝ}
    (h : A ≤ t • (1 : Matrix n n ℝ)) (hQ : 1 ≤ Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ (Q / 2)) (A * A)) ≤ t ^ (Q - 1) * A.trace := by
  rw [trace_cfc_rpow_mul_self hA (lt_of_lt_of_le zero_lt_one hQ)]
  exact trace_cfc_rpow_le_mul_trace hA h hQ

/-! ## The Schatten size of a doubled block -/

section Block

variable {d : ℕ}

/-- The Schatten trace of a symmetric doubled block is nonnegative, so its
Schatten size is a nonnegative real. -/
theorem zero_le_schattenNorm {H : BlockMat d} (hH : IsSymmetricBlockMat H) (Q : ℝ) :
    0 ≤ schattenNorm Q H := by
  have hsq : (toFullBlockMat H * toFullBlockMat H).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (toFullBlockMat H)
    rwa [(isHermitian_toFullBlockMat hH : (toFullBlockMat H).IsHermitian)] at this
  exact Real.rpow_nonneg (zero_le_trace_cfc_rpow hsq (Q / 2)) _

/-- The Schatten size raised to the power `Q` recovers the Schatten trace: the
definition takes the `Q`-th root of a nonnegative real. -/
theorem schattenNorm_rpow {H : BlockMat d} (hH : IsSymmetricBlockMat H) {Q : ℝ} (hQ : 0 < Q) :
    schattenNorm Q H ^ Q =
      Matrix.trace (cfc (fun x : ℝ => x ^ (Q / 2))
        (toFullBlockMat H * toFullBlockMat H)) := by
  have hsq : (toFullBlockMat H * toFullBlockMat H).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (toFullBlockMat H)
    rwa [(isHermitian_toFullBlockMat hH : (toFullBlockMat H).IsHermitian)] at this
  have htr := zero_le_trace_cfc_rpow hsq (Q / 2)
  simp only [schattenNorm]
  rw [← Real.rpow_mul htr, inv_mul_cancel₀ (ne_of_gt hQ), Real.rpow_one]

/-- **The opening display of `l.fixed.geometry.positive.gap` in the doubled block
dialect.**  For a positive doubled block bounded above by `t` in the Loewner
order, the Schatten trace `tr(D^Q)` is at most `t^{Q-1}` times the block
trace. -/
theorem schattenNorm_rpow_le_of_le_smul_one {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hpos : (toFullBlockMat H).PosSemidef) {t Q : ℝ}
    (h : toFullBlockMat H ≤ t • (1 : FullBlockMat d)) (hQ : 1 ≤ Q) :
    schattenNorm Q H ^ Q ≤ t ^ (Q - 1) * blockTrace H := by
  rw [schattenNorm_rpow hH (lt_of_lt_of_le zero_lt_one hQ)]
  simpa only [blockTrace] using trace_cfc_rpow_mul_self_le hpos h hQ

/-- **The trace bound on the Schatten size of a positive block**, the step
`|B|_{S_Q} ≤ tr B` of `l.fixed.geometry.positive.gap`.  Applying the trace-power estimate
at `t = tr B` gives `|B|_{S_Q}^Q ≤ (tr B)^Q`, and the `Q`-th root is monotone. -/
theorem schattenNorm_le_blockTrace {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hpos : (toFullBlockMat H).PosSemidef) {Q : ℝ} (hQ : 1 ≤ Q) :
    schattenNorm Q H ≤ blockTrace H := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have htr : (0 : ℝ) ≤ blockTrace H := hpos.trace_nonneg
  have hpow : schattenNorm Q H ^ Q ≤ blockTrace H ^ (Q - 1) * blockTrace H :=
    schattenNorm_rpow_le_of_le_smul_one hH hpos (le_trace_smul_one hpos) hQ
  have hsplit : blockTrace H ^ (Q - 1) * blockTrace H = blockTrace H ^ Q := by
    rcases eq_or_lt_of_le htr with hzero | hposT
    · rw [← hzero, mul_zero, Real.zero_rpow (by linarith only [hQ] : Q ≠ 0)]
    · have hadd : blockTrace H ^ (Q - 1 + 1)
          = blockTrace H ^ (Q - 1) * blockTrace H ^ (1 : ℝ) := Real.rpow_add hposT _ _
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      norm_num
  rw [hsplit] at hpow
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_schattenNorm hH Q) Q) hpow
    (inv_nonneg.mpr hQ0.le)
  rwa [← Real.rpow_mul (zero_le_schattenNorm hH Q), ← Real.rpow_mul htr,
    mul_inv_cancel₀ (ne_of_gt hQ0), Real.rpow_one, Real.rpow_one] at hroot

end Block

end

end Recurrence
end HighContrast
end HCPolySupport
