/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coordinate
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Multilinear

/-!
# Coefficient arrays of multilinear maps

The bridge between real multilinear maps on a finite-dimensional real inner product space and the
coordinate tensors of `Analysis/Tensor/Coordinate.lean` (Bizeul–Klartag–Lehec, arXiv:2610.05474v1,
Section 2): in an orthonormal basis `b`, a real `k`-linear map `Φ` has the coefficient array
`coordTensor b Φ = (Φ (b i₁, …, b i_k))_i ∈ Coord n k`, whose norm is the Hilbert–Schmidt norm of
the source. Permuting arguments permutes index positions, `symmetrizeML` is `S_k`, `appendInner`
places the original index after the Taylor indices, and the operator norm is at most the
Hilbert–Schmidt norm.
-/

@[expose] public section

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Tensor

/-- Sum a function of two chosen coordinates as an iterated sum over those coordinates. -/
theorem sum_finTwo_arrow {ι E : Type*} [Fintype ι] (b : ι → E) (f : (Fin 2 → E) → ℝ) :
    ∑ J : Fin 2 → ι, f (fun k => b (J k)) = ∑ i, ∑ j, f ![b i, b j] := by
  calc
    ∑ J : Fin 2 → ι, f (fun k => b (J k)) =
        ∑ q : ι × ι, f (fun k => b ((finTwoArrowEquiv ι).symm q k)) :=
      ((finTwoArrowEquiv ι).symm.sum_comp (fun J => f (fun k => b (J k)))).symm
    _ = ∑ q : ι × ι, f ![b q.1, b q.2] := by
      apply Finset.sum_congr rfl
      intro q _
      have hvec : (fun k => b ((finTwoArrowEquiv ι).symm q k)) = ![b q.1, b q.2] := by
        funext i
        fin_cases i <;> rfl
      rw [hvec]
    _ = ∑ i, ∑ j, f ![b i, b j] := Fintype.sum_prod_type _

/-- Sum over two coordinates after adjoining a fixed first coordinate. -/
theorem sum_finTwo_arrow_cons {ι E : Type*} [Fintype ι] (b : ι → E) (u : E)
    (f : (Fin 3 → E) → ℝ) :
    ∑ J : Fin 2 → ι, f (Fin.cons u fun k => b (J k)) = ∑ i, ∑ j, f ![u, b i, b j] := by
  rw [sum_finTwo_arrow b (fun v => f (Fin.cons u v))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hvec : Fin.cons u ![b i, b j] = ![u, b i, b j] := by
    funext k
    fin_cases k <;> rfl
  rw [hvec]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coefficient array `(Φ (b i₁, …, b i_k))_i` of a real `k`-linear map in an orthonormal
basis `b`. -/
def coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) : Coord n k :=
  WithLp.toLp 2 fun i => Φ (fun j => b (i j))

theorem coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl

/-- Permuting the arguments permutes the index positions. -/
theorem coordTensor_domDomCongr {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (σ : Equiv.Perm (Fin k)) :
    coordTensor b (Φ.domDomCongr σ) = slotPerm n k σ (coordTensor b Φ) := by
    ext i
    rw [slotPerm_apply]
    simp [coordTensor, ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

/-- Every permutation of `Fin k` fixes every point outside `univ`. -/
theorem fixingOutside_univ (k : ℕ) :
    fixingOutside (univ : Finset (Fin k)) = (univ : Finset (Equiv.Perm (Fin k))) := by
    ext σ
    simp [fixingOutside]

theorem slots_zero_self (k : ℕ) : slots k 0 k = univ := by
  ext p
  simp [slots]

private lemma coordTensor_smul {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (c : ℝ) (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    coordTensor b (c • Φ) = c • coordTensor b Φ := by
  ext i
  simp [coordTensor_apply]

private lemma coordTensor_sum {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Finset (Equiv.Perm (Fin k)))
    (Φ : Equiv.Perm (Fin k) → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    coordTensor b (∑ σ ∈ s, Φ σ) = ∑ σ ∈ s, coordTensor b (Φ σ) := by
  ext i
  simp [coordTensor_apply]

/-- The full symmetrization of a multilinear map is `S_k` of its coefficient array. -/
theorem coordTensor_symmetrizeML {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    coordTensor b (symmetrizeML Φ) = symmetrize n k k (coordTensor b Φ) := by
    unfold symmetrizeML
    rw [coordTensor_smul, coordTensor_sum]
    unfold symmetrize blockAverage
    rw [slots_zero_self k, fixingOutside_univ k]
    simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    congr 1

/--
In coordinates, `appendInner Ψ` is the array whose last index is the coordinate of the vector
`Ψ (b i₁, …, b i_d)`: the original index comes after the `d` Taylor indices. -/
theorem coordTensor_appendInner {n d : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E) (i : Fin (d + 1) → Fin n) :
    coordTensor b (appendInner Ψ) i =
      ⟪Ψ (fun j => b (i (Fin.castSucc j))), b (i (Fin.last d))⟫ := by
  rw [coordTensor_apply]
  simp only [appendInner, ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  have h :
    Fin.init (fun j : Fin (d + 1) => b (i j)) = (fun j : Fin d => b (i (Fin.castSucc j))) := by
    funext j
    rfl
  rw [h]
  exact
    innerSL_apply_apply (𝕜 := ℝ) (Ψ (fun j : Fin d => b (i (Fin.castSucc j))))
      (b (i (Fin.last d)))

private lemma multilinear_basis_expand {n k : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (c : Fin k → Fin n → ℝ) :
    Φ (fun j => ∑ l, c j l • b l) =
      ∑ i : Fin k → Fin n, (∏ j, c j (i j)) • Φ (fun j => b (i j)) := by
  classical
  rw [Φ.map_sum]
  simp_rw [Φ.map_smul_univ]

/-- Expansion of a multilinear map in an orthonormal basis. -/
theorem apply_eq_sum_coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (h : Fin k → E) :
    Φ h = ∑ i : Fin k → Fin n, coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by
    classical
    have hh :
        h = (fun j => ∑ l : Fin n, ⟪b l, h j⟫ • b l) := by
      funext j
      symm
      exact b.sum_repr' (h j)
    calc
      Φ h = Φ (fun j => ∑ l : Fin n, ⟪b l, h j⟫ • b l) := by
        exact congrArg (fun x => Φ x) hh
      _ = ∑ i : Fin k → Fin n,
          (∏ j, ⟪b (i j), h j⟫) • Φ (fun j => b (i j)) := by
        exact multilinear_basis_expand b Φ (fun j l => ⟪b l, h j⟫)
      _ = ∑ i : Fin k → Fin n,
          coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by
        simp [coordTensor_apply, smul_eq_mul, mul_comm]

private lemma coordTensor_coeff_norm_le
    {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (h : Fin k → E) :
    ‖WithLp.toLp 2 (fun i : Fin k → Fin n => ∏ j, ⟪b (i j), h j⟫)‖
      ≤ ∏ j, ‖h j‖ := by
  have hparseval (j : Fin k) :
      ∑ l : Fin n, (⟪b l, h j⟫) ^ 2 = ‖h j‖ ^ 2 := by
    simpa [pow_two, real_inner_comm, real_inner_self_eq_norm_sq] using
      (b.sum_inner_mul_inner (h j) (h j))
  have hsum :
      (∑ i : Fin k → Fin n, (∏ j, ⟪b (i j), h j⟫) ^ 2)
        = (∏ j : Fin k, ‖h j‖) ^ 2 := by
    calc
      ∑ i : Fin k → Fin n, (∏ j, ⟪b (i j), h j⟫) ^ 2
          = ∑ i : Fin k → Fin n, ∏ j, (⟪b (i j), h j⟫) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.prod_pow]
      _ = ∏ j : Fin k, ∑ l : Fin n, (⟪b l, h j⟫) ^ 2 := by
            rw [Fintype.prod_sum]
      _ = ∏ j : Fin k, ‖h j‖ ^ 2 := by
            simp [hparseval]
      _ = (∏ j : Fin k, ‖h j‖) ^ 2 := by
            rw [Finset.prod_pow]
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [hsum, Real.sqrt_sq_eq_abs]
  exact le_of_eq
    (abs_of_nonneg (Finset.prod_nonneg fun j _ => norm_nonneg (h j)))

/-- The operator norm is at most the Hilbert–Schmidt norm of the coefficient array. -/
theorem norm_le_norm_coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖Φ‖ ≤ ‖coordTensor b Φ‖ := by
    refine Φ.opNorm_le_bound (norm_nonneg _) ?_
    intro h
    let c : Coord n k :=
      WithLp.toLp 2 (fun i : Fin k → Fin n => ∏ j, ⟪b (i j), h j⟫)
    have hc : ‖c‖ ≤ ∏ j, ‖h j‖ := by
      exact coordTensor_coeff_norm_le b h
    have hsum : Φ h = ⟪coordTensor b Φ, c⟫ := by
      rw [apply_eq_sum_coordTensor b Φ h]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, c]
      apply Finset.sum_congr rfl
      intro x hx
      rw [mul_comm]
    calc
      ‖Φ h‖ = |⟪coordTensor b Φ, c⟫| := by
        rw [hsum, Real.norm_eq_abs]
      _ ≤ ‖coordTensor b Φ‖ * ‖c‖ :=
        abs_real_inner_le_norm (coordTensor b Φ) c
      _ ≤ ‖coordTensor b Φ‖ * ∏ j, ‖h j‖ := by
        exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)

/-- `‖coordTensor b Φ‖ ≤ (√n)^k ‖Φ‖`. -/
theorem norm_coordTensor_le {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ ≤ Real.sqrt n ^ k * ‖Φ‖ := by
    have hbound : ∀ i : Fin k → Fin n, ‖Φ (fun j => b (i j))‖ ≤ ‖Φ‖ := by
      intro i
      calc
        ‖Φ (fun j => b (i j))‖ ≤ ‖Φ‖ * ∏ j, ‖b (i j)‖ := Φ.le_opNorm _
        _ = ‖Φ‖ := by
          simp [OrthonormalBasis.norm_eq_one]
    have hsqrt : ∀ m : ℕ, Real.sqrt ((n : ℝ) ^ m) = Real.sqrt n ^ m := by
      intro m
      induction m with
      | zero =>
          simp
      | succ m ih =>
          rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
    calc
      ‖coordTensor b Φ‖ =
          Real.sqrt (∑ i : Fin k → Fin n, ‖Φ (fun j => b (i j))‖ ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        simp [coordTensor_apply]
      _ ≤ Real.sqrt (∑ i : Fin k → Fin n, ‖Φ‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i hi
        have hi' := hbound i
        nlinarith [norm_nonneg (Φ (fun j => b (i j))), norm_nonneg Φ]
      _ = Real.sqrt n ^ k * ‖Φ‖ := by
        rw [show (∑ i : Fin k → Fin n, ‖Φ‖ ^ 2) =
            (n : ℝ) ^ k * ‖Φ‖ ^ 2 by
          simp [Finset.sum_const]]
        rw [Real.sqrt_mul (by positivity), hsqrt]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg Φ)]

end FunctionalInequalities.Analysis.Tensor
