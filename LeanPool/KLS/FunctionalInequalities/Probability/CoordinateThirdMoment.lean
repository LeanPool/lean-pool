/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Moments
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates

/-!
# Coordinate third moments under a self-adjoint operator

For a finite measure `ν` on `EuclideanSpace ℝ (Fin n)` a.e. supported in a ball `‖x − a‖ ≤ R` and a
self-adjoint `T` with
matrix `P` in the standard basis `e`: `V_s V_t (T V)_i` (`V = x − a`) is integrable, and the
sandwich of the computed slices
`H_i(j', k') = ∫ V_j' V_k' ⟪T e_i, V⟫ dν` by `P` is the third-moment matrix of `T V`:
`(P H_i P) j k = ∫ (T V)_j (T V)_k (T V)_i dν` — the deterministic entry identity behind BKL
arXiv:2610.05474v1 (69).
-/

@[expose] public section

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability

/--
Integrability of `V_s V_t (T V)_i` for `V = x − a` under a finite measure a.e. supported in a ball.
-/
theorem integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le {n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure ν] (a : EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : ∀ᵐ x ∂ν, ‖x - a‖ ≤ R)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (s t i : Fin n) :
    Integrable (fun x => (x - a) s * (x - a) t * (T (x - a)) i) ν := by
  have hsum :
    (fun x => (x - a) s * (x - a) t * (T (x - a)) i) = fun x =>
      ∑ u : Fin n,
        operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T i u *
          ((x - a) s * (x - a) t * (x - a) u) := by
    funext x
    rw [euclidean_clm_apply_eq_sum_operatorMatrix T (x - a) i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsum]
  exact
    integrable_finsetSum _ fun u _ =>
      (integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le a R hR s t u).const_mul _

/--
Generic (69) entry identity: `(P H_i P) j k = ∫ (T V)_j (T V)_k (T V)_i dν` for self-adjoint `T`. -/
theorem operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le {n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure ν] (a : EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : ∀ᵐ x ∂ν, ‖x - a‖ ≤ R)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hT : IsSelfAdjoint T)
    (i j k : Fin n) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T *
            (Matrix.of fun j' k' : Fin n =>
              ∫ x,
                (x - a) j' * (x - a) k' * ⟪T (EuclideanSpace.basisFun (Fin n) ℝ i), x - a⟫ ∂ν) *
          operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T)
        j k =
      ∫ x, (T (x - a)) j * (T (x - a)) k * (T (x - a)) i ∂ν := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let P := operatorMatrix e T
  have hP : ∀ r s, P r s = P s r := by
    intro r s
    simp only [P, operatorMatrix_apply_eq_operatorEntry, operatorEntry]
    calc
      ⟪e r, T (e s)⟫ = ⟪T (e s), e r⟫ := real_inner_comm _ _
      _ = ⟪e s, T (e r)⟫ := hT.isSymmetric _ _
  have hpair : ∀ x : EuclideanSpace ℝ (Fin n), ⟪T (e i), x - a⟫ = (T (x - a)) i := by
    intro x
    exact euclidean_inner_selfAdjoint_basisFun T hT (x - a) i
  change
    (P * (Matrix.of fun j' k' : Fin n => ∫ x, (x - a) j' * (x - a) k' * ⟪T (e i), x - a⟫ ∂ν) *
          P)
        j k =
      ∫ x, (T (x - a)) j * (T (x - a)) k * (T (x - a)) i ∂ν
  have hM :
    (Matrix.of fun j' k' : Fin n => ∫ x, (x - a) j' * (x - a) k' * ⟪T (e i), x - a⟫ ∂ν) =
      (Matrix.of fun j' k' : Fin n => ∫ x, (x - a) j' * (x - a) k' * (T (x - a)) i ∂ν) := by
    ext j' k'
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hpair x]
  rw [hM]
  calc
    (P * (Matrix.of fun j' k' : Fin n => ∫ x, (x - a) j' * (x - a) k' * (T (x - a)) i ∂ν) * P) j
          k =
        ∑ s : Fin n,
          ∑ t : Fin n, P j s * P t k * ∫ x, (x - a) s * (x - a) t * (T (x - a)) i ∂ν := by
      rw [Matrix.mul_apply]
      simp_rw [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ =
        ∫ x,
          ∑ s : Fin n,
            ∑ t : Fin n, P j s * P t k * ((x - a) s * (x - a) t * (T (x - a)) i) ∂ν := by
      symm
      simpa using
        (integral_sum_sum_const_mul (ν := ν) Finset.univ Finset.univ
          (fun s t : Fin n => P j s * P t k)
          (fun s t x => (x - a) s * (x - a) t * (T (x - a)) i)
          (fun s t =>
            integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le a R hR T s t i))
    _ = ∫ x, (T (x - a)) j * (T (x - a)) k * (T (x - a)) i ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [euclidean_clm_apply_eq_sum_operatorMatrix T (x - a) j,
        euclidean_clm_apply_eq_sum_operatorMatrix T (x - a) k]
      change
        ∑ s : Fin n, ∑ t : Fin n, P j s * P t k * ((x - a) s * (x - a) t * (T (x - a)) i) =
          (∑ s : Fin n, P j s * (x - a) s) * (∑ t : Fin n, P k t * (x - a) t) * (T (x - a)) i
      calc
        ∑ s : Fin n, ∑ t : Fin n, P j s * P t k * ((x - a) s * (x - a) t * (T (x - a)) i) =
            ∑ s : Fin n, ∑ t : Fin n, P j s * ((x - a) s * (x - a) t * (T (x - a)) i) * P t k := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ =
            (∑ s : Fin n, P j s * (x - a) s) * (∑ t : Fin n, P k t * (x - a) t) *
              (T (x - a)) i :=
          sum_sum_mul_mul_mul_mul_eq_of_symm P hP (fun r => (x - a) r) ((T (x - a)) i) j k

end FunctionalInequalities.Probability
