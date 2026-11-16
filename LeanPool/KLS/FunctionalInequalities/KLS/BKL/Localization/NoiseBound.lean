/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Standardization
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
/-!
# The conjugated noise matrices of the covariance

`cumulantEnergy_succ_eq` reindexes `E_{r+2}` (BKL arXiv:2610.05474v1, (90)); `conjugatedNoiseMatrix
μ hc p i` has entries
`κ₃(μ_p)(σ e_a, σ e_b, σ e_i)`, `σ = A(p)^{-1/2}` (BKL (85), `Htilde_i = P H_i P`), and the bound
(79)
in conjugated form,
`Σ_i |Htilde_i v|² ≤ 8|v|²`, follows from `CumulantBoundCompact 2 8` for symmetric positive
semidefinite
`Q`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL

variable {n : ℕ}

private lemma cumulant_middle_sum
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ) (b : Fin n → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w = ∑ j, v j • b j) :
    ∑ j, T ![x, b j, z] * v j = T ![x, w, z] := by
  classical
  let m : Fin 3 → EuclideanSpace ℝ (Fin n) := ![x, 0, z]
  have hm : Function.update m 1 (∑ j, v j • b j) = ![x, ∑ j, v j • b j, z] := by
    funext i
    fin_cases i <;> simp [m]
  have hsum : T ![x, ∑ j, v j • b j, z] = ∑ j, T ![x, v j • b j, z] := by
    have h := (T.toMultilinearMap).map_update_sum Finset.univ 1 (fun j => v j • b j) m
    calc
      T ![x, ∑ j, v j • b j, z] = T (Function.update m 1 (∑ j, v j • b j)) := by rw [hm]
      _ = ∑ j, T (Function.update m 1 (v j • b j)) := h
      _ = ∑ j, T ![x, v j • b j, z] := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : Function.update m 1 (v j • b j) = ![x, v j • b j, z] := by
          funext i
          fin_cases i <;> simp [m]
        rw [hj]
  calc
    ∑ j, T ![x, b j, z] * v j = ∑ j, v j * T ![x, b j, z] := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, T ![x, v j • b j, z] := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : Function.update m 1 (b j) = ![x, b j, z] := by
        funext i
        fin_cases i <;> simp [m]
      have hj' : Function.update m 1 (v j • b j) = ![x, v j • b j, z] := by
        funext i
        fin_cases i <;> simp [m]
      have hsmul := (T.toMultilinearMap).map_update_smul m 1 (v j) (b j)
      calc
        v j * T ![x, b j, z] = v j • T ![x, b j, z] := by simp [smul_eq_mul]
        _ = v j • T (Function.update m 1 (b j)) := by rw [hj]
        _ = T (Function.update m 1 (v j • b j)) := hsmul.symm
        _ = T ![x, v j • b j, z] := by rw [hj']
    _ = T ![x, w, z] := by
      rw [hw]
      exact hsum.symm

private lemma fin_snoc_comp
    {r n : ℕ} {α : Type*} (g : Fin n → α)
    (p : Fin r → Fin n) (x : Fin n) :
    (fun k : Fin (r + 1) =>
        g ((Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) p x) k)) =
      Fin.snoc (α := fun _ : Fin (r + 1) => α)
        (fun s => g (p s)) (g x) := by
  funext i
  refine Fin.lastCases ?_ (fun s => ?_) i
  · simp
  · simp [Fin.snoc_castSucc]

/--
**The cumulant energy of the next order, reindexed** (BKL (90), `Σ_i |W_i|² = E_{m+1}`): splitting
the last
slot, `E_{r+2}(u) = Σ_K Σ_k κ_{r+3}(u, σ e_{K_1}, …, σ e_{r}, σ e_k)²`. -/
theorem cumulantEnergy_succ_eq (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy ν (r + 1) u =
      ∑ K : Fin r → Fin n,
        ∑ k : Fin n,
          cumulant ν (r + 1 + 1)
              (Fin.cons u
                (Fin.snoc
                  (fun s =>
                    inverseSqrt (Covariance.operator ν)
                      (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
                  (inverseSqrt (Covariance.operator ν)
                    (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^
            2 := by
  classical
  unfold cumulantEnergy
  let reindex : (Fin r → Fin n) × Fin n ≃ (Fin (r + 1) → Fin n) :=
    { toFun := fun q => Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) q.1 q.2
      invFun := fun J => (fun s => J s.castSucc, J (Fin.last r))
      left_inv := by
        intro q
        simp
      right_inv := by
        intro J
        funext i
        refine Fin.lastCases ?_ (fun s => ?_) i
        · simp
        · simp }
  let g : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have harg (q : (Fin r → Fin n) × Fin n) :
    Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u
        (fun k =>
          inverseSqrt (Covariance.operator ν)
            (EuclideanSpace.basisFun (Fin n) ℝ ((reindex q) k))) =
      Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u
        (Fin.snoc (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
          (fun s =>
            inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
          (inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ q.2))) := by
    have hs := fin_snoc_comp g q.1 q.2
    have h :=
      congrArg
        (fun f : Fin (r + 1) → EuclideanSpace ℝ (Fin n) =>
          Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u f)
        hs
    simpa [reindex, g] using h
  calc
    ∑ J : Fin (r + 1) → Fin n,
          cumulant ν (r + 1 + 1)
              (Fin.cons u
                (fun k =>
                  inverseSqrt (Covariance.operator ν)
                    (EuclideanSpace.basisFun (Fin n) ℝ (J k)))) ^
            2 =
        ∑ q : (Fin r → Fin n) × Fin n,
          cumulant ν (r + 1 + 1)
              (Fin.cons u
                (Fin.snoc (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
                  (fun s =>
                    inverseSqrt (Covariance.operator ν)
                      (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
                  (inverseSqrt (Covariance.operator ν)
                    (EuclideanSpace.basisFun (Fin n) ℝ q.2)))) ^
            2 := by
      refine
        (Fintype.sum_equiv reindex
            (fun q : (Fin r → Fin n) × Fin n =>
              cumulant ν (r + 1 + 1)
                  (Fin.cons u
                    (Fin.snoc (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
                      (fun s =>
                        inverseSqrt (Covariance.operator ν)
                          (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
                      (inverseSqrt (Covariance.operator ν)
                        (EuclideanSpace.basisFun (Fin n) ℝ q.2)))) ^
                2)
            (fun J : Fin (r + 1) → Fin n =>
              cumulant ν (r + 1 + 1)
                  (Fin.cons u
                    (fun k =>
                      inverseSqrt (Covariance.operator ν)
                        (EuclideanSpace.basisFun (Fin n) ℝ (J k)))) ^
                2)
            ?_).symm
      intro q
      exact
        congrArg
          (fun z : Fin (r + 1 + 1) → EuclideanSpace ℝ (Fin n) => cumulant ν (r + 1 + 1) z ^ 2)
          (harg q).symm
    _ =
        ∑ K : Fin r → Fin n,
          ∑ k : Fin n,
            cumulant ν (r + 1 + 1)
                (Fin.cons u
                  (Fin.snoc
                    (fun s =>
                      inverseSqrt (Covariance.operator ν)
                        (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
                    (inverseSqrt (Covariance.operator ν)
                      (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^
              2 := by
      rw [Fintype.sum_prod_type]

namespace Localization

variable (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- The conjugated noise matrices `Htilde_i = A^{-1/2} H_i A^{-1/2}` of BKL (85): entries
`κ₃(μ_p)(σ e_a, σ e_b, σ e_i)` with `σ = A(p)^{-1/2}`. -/
def conjugatedNoiseMatrix (p : Param n) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 3
      ![inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ a),
        inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ b),
        inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i)]

/--
**BKL (79) in conjugated form** (`Σ_i Htilde_i² ≤ 8 Id`, p. 24): for a compactly supported isotropic
log-concave
prior, symmetric positive semidefinite `Q` and the third-order bound `CumulantBoundCompact 2 8`,
`Σ_i |Htilde_i v|² ≤ 8 |v|²` for every coordinate vector `v`. -/
theorem sum_sq_conjugatedNoiseMatrix_mulVec_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) (v : Fin n → ℝ) :
    ∑ i, ∑ a, (∑ b, conjugatedNoiseMatrix μ hc p i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2 := by
  classical
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := compactPosterior μ hc p.1 p.2
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := cov μ hc p
  let σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := inverseSqrt A
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let w : EuclideanSpace ℝ (Fin n) := ∑ a, v a • e a
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ :=
    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) 3
  have hνcompact : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    rw [compactPosterior_support μ hc p.1 p.2]
    exact hc
  have hpos : A.IsPositive := by
    simpa [A, cov] using Isotropic.compactPosterior_covariance_isPositive μ hc hiso p.1 p.2
  have hunit : IsUnit A := by
    simpa [A, cov] using Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hself : IsSelfAdjoint σ := by
    simpa [σ, A, cov] using (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hroot : (σ.comp A).comp σ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change σ (A (σ x)) = x
    simpa [σ] using
      congrArg (fun S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => S x)
        (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  have hσw : σ w = ∑ b, v b • σ (e b) := by simp only [w, map_sum, map_smul]
  have hcontract (i a : Fin n) :
    ∑ b, conjugatedNoiseMatrix μ hc p i a b * v b = T ![σ (e a), σ w, σ (e i)] := by
    simpa [conjugatedNoiseMatrix, ν, A, σ, e, T] using
      (cumulant_middle_sum T (σ (e a)) (σ (e i)) v (fun b => σ (e b)) (σ w) hσw)
  have hswap (a i : Fin n) : T ![σ (e a), σ w, σ (e i)] = T ![σ w, σ (e a), σ (e i)] := by
    let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have h :=
      cumulant_comp_perm_of_compact ν hνcompact τ
        (![σ w, σ (e a), σ (e i)] : Fin 3 → EuclideanSpace ℝ (Fin n))
    have hv :
      ((![σ w, σ (e a), σ (e i)] : Fin 3 → EuclideanSpace ℝ (Fin n)) ∘ τ) =
        (![σ (e a), σ w, σ (e i)] : Fin 3 → EuclideanSpace ℝ (Fin n)) := by
      funext j
      fin_cases j <;> rfl
    rw [← hv]
    exact h
  have hindex :
    ∑ J : Fin 2 → Fin n, T (Fin.cons (σ w) (fun k => σ (e (J k)))) ^ 2 =
      ∑ a : Fin n, ∑ i : Fin n, T ![σ w, σ (e a), σ (e i)] ^ 2 := by
    have hreindex :=
      (finTwoArrowEquiv (Fin n)).symm.sum_comp
        (fun J : Fin 2 → Fin n => T (Fin.cons (σ w) (fun k => σ (e (J k)))) ^ 2)
    calc
      ∑ J : Fin 2 → Fin n, T (Fin.cons (σ w) (fun k => σ (e (J k)))) ^ 2 =
          ∑ q : Fin n × Fin n,
            T (Fin.cons (σ w) (fun k => σ (e (((finTwoArrowEquiv (Fin n)).symm q) k)))) ^ 2 :=
        hreindex.symm
      _ = ∑ q : Fin n × Fin n, T ![σ w, σ (e q.1), σ (e q.2)] ^ 2 := by
        apply Finset.sum_congr rfl
        intro q _
        congr 2
        ext k
        fin_cases k <;> rfl
      _ = ∑ a : Fin n, ∑ i : Fin n, T ![σ w, σ (e a), σ (e i)] ^ 2 := Fintype.sum_prod_type _
  have hbound :
    ∑ J : Fin 2 → Fin n, T (Fin.cons (σ w) (fun k => σ (e (J k)))) ^ 2 ≤ 8 * ⟪A (σ w), σ w⟫ := by
    simpa [T, ν, A, cov, σ, e] using
      (compactPosterior_cumulant_bound μ hc hiso hLC p.1 p.2 hSym hQ (d := 2) (by norm_num) h8
        (σ w))
  have hsym : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪σ x, y⟫ = ⟪x, σ y⟫ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have hinner : ⟪A (σ w), σ w⟫ = ‖w‖ ^ 2 := by
    have hrootw : σ (A (σ w)) = w := by
      have h :=
        congrArg (fun S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => S w) hroot
      simpa [ContinuousLinearMap.comp_apply] using h
    calc
      ⟪A (σ w), σ w⟫ = ⟪σ (A (σ w)), w⟫ := (hsym _ _).symm
      _ = ⟪w, w⟫ := by rw [hrootw]
      _ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hwcoord (i : Fin n) : w.ofLp i = v i := by
    have hdelta : ∑ x : Fin n, v x * ((Pi.single x (1 : ℝ) : Fin n → ℝ) i) = v i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi
        simp [hbi]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    simpa [w, e, EuclideanSpace.basisFun_apply, smul_eq_mul] using hdelta
  have hnorm : ‖w‖ ^ 2 = ∑ a, v a ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a _
    rw [hwcoord]
    simp [Real.norm_eq_abs, sq_abs]
  calc
    ∑ i, ∑ a, (∑ b, conjugatedNoiseMatrix μ hc p i a b * v b) ^ 2 =
        ∑ i, ∑ a, T ![σ (e a), σ w, σ (e i)] ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [hcontract]
    _ = ∑ i, ∑ a, T ![σ w, σ (e a), σ (e i)] ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [hswap]
    _ = ∑ a, ∑ i, T ![σ w, σ (e a), σ (e i)] ^ 2 := by rw [Finset.sum_comm]
    _ = ∑ J : Fin 2 → Fin n, T (Fin.cons (σ w) (fun k => σ (e (J k)))) ^ 2 := hindex.symm
    _ ≤ 8 * ⟪A (σ w), σ w⟫ := hbound
    _ = 8 * ∑ a, v a ^ 2 := by rw [hinner, hnorm]

end Localization

end FunctionalInequalities.KLS.BKL
