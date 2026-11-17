/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.EnergyForm
/-!
# Cumulant energies as energy forms

`E_{r+1}(u) = F(PAP, P^{⊗r} κ_{r+1}(u, ·))` for the standard-coordinate cumulant tensor (BKL (83),
(85)): the reduction of
Lemma 5.1 to `A = Id`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

end FunctionalInequalities.Analysis.CoordinateTensor

namespace FunctionalInequalities.KLS.BKL

open FunctionalInequalities.Analysis.CoordinateTensor

variable {n : ℕ}

private lemma energy_inverse_conjugate
    {M : Type*} [MonoidWithZero M] (A P : M)
    (hA : IsUnit A) (hP : IsUnit P) :
    Ring.inverse (P * A * P) =
      Ring.inverse P * Ring.inverse A * Ring.inverse P := by
  rcases hA with ⟨a, rfl⟩
  rcases hP with ⟨p, rfl⟩
  change Ring.inverse (↑(p * a * p) : M) =
    Ring.inverse (↑p : M) * Ring.inverse (↑a : M) * Ring.inverse (↑p : M)
  rw [Ring.inverse_unit (p * a * p), Ring.inverse_unit p, Ring.inverse_unit a]
  simp only [mul_inv_rev, Units.val_mul, mul_assoc]

private lemma energy_coordinate_gram
    (R S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hR : IsSelfAdjoint R) (hS : IsSelfAdjoint S)
    (x y : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin n,
      ⟪x, R (S (EuclideanSpace.basisFun (Fin n) ℝ j))⟫ *
        ⟪y, R (S (EuclideanSpace.basisFun (Fin n) ℝ j))⟫) =
      ⟪x, (R * S * S * R) y⟫ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hm (v w : EuclideanSpace ℝ (Fin n)) :
      ⟪v, R (S w)⟫ = ⟪S (R v), w⟫ := by
    rw [← R.adjoint_inner_left (S w) v, hR.adjoint_eq,
      ← S.adjoint_inner_left w (R v), hS.adjoint_eq]
  change (∑ j, ⟪x, R (S (b j))⟫ * ⟪y, R (S (b j))⟫) = _
  simp only [hm]
  have hf (j : Fin n) : ⟪S (R y), b j⟫ = ⟪b j, S (R y)⟫ :=
    real_inner_comm _ _
  simp only [hf]
  rw [b.sum_inner_mul_inner]
  rw [← S.adjoint_inner_right (R x) (S (R y)), hS.adjoint_eq,
    ← R.adjoint_inner_right x (S (S (R y))), hR.adjoint_eq]
  rfl

private lemma energy_tensor_square (r : ℕ)
    (c : Fin n → Fin n → ℝ) (T : (Fin r → Fin n) → ℝ) :
    (∑ J : Fin r → Fin n,
      (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2) =
      ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
        T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) := by
  classical
  calc
    (∑ J : Fin r → Fin n,
        (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2) =
        ∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
          ∑ L : Fin r → Fin n,
            T K * T L * ∏ s, (c (J s) (K s) * c (J s) (L s)) := by
      simp only [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro K _
      apply Finset.sum_congr rfl
      intro L _
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
          ∑ J : Fin r → Fin n,
            T K * T L * ∏ s, (c (J s) (K s) * c (J s) (L s)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro K _
      rw [Finset.sum_comm]
    _ = ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
          T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) := by
      apply Finset.sum_congr rfl
      intro K _
      apply Finset.sum_congr rfl
      intro L _
      rw [Fintype.prod_sum
        (fun (s : Fin r) (j : Fin n) => c j (K s) * c j (L s)),
        Finset.mul_sum]

/--
**The cumulant energy as the energy form in conjugated coordinates** (BKL (83) and (85)): for a law
`ν` with
positive invertible covariance `A` and any self-adjoint invertible `P`,
`E_{r+1}(u) = |κ_{r+1}(u)|²_A = F(P A P, P^{⊗r} κ_{r+1}(u))`, where `(P^{⊗r} κ_{r+1}(u))_K =
κ_{r+1}(u, P e_{K_1}, …, P e_{K_r})`. -/
theorem cumulantEnergy_eq_energyForm (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hpos : (Covariance.operator ν).IsPositive) (hunit : IsUnit (Covariance.operator ν))
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsSelfAdjoint P)
    (hPu : IsUnit P) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy ν r u =
      energyForm (P * Covariance.operator ν * P)
        (fun K : Fin r → Fin n =>
          cumulant ν (r + 1)
            (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))) := by
  classical
  let A := Covariance.operator ν
  let S := inverseSqrt A
  let R := Ring.inverse P
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f := (cumulant ν (r + 1)).curryLeft u
  let c := fun j k : Fin n => ⟪b k, R (S (b j))⟫
  let T := fun K : Fin r → Fin n => f (fun s => P (b (K s)))
  have hspec := inverseSqrt_spec A hpos hunit
  have hi : Ring.inverse (P * A * P) = R * Ring.inverse A * R :=
    energy_inverse_conjugate A P hunit hPu
  have hoperator : R * S * S * R = Ring.inverse (P * A * P) := by
    rw [mul_assoc R S S, hspec.2.2.1]
    exact hi.symm
  have he (x : EuclideanSpace ℝ (Fin n)) : (∑ k, ⟪b k, R x⟫ • P (b k)) = x := by
    simpa only [map_sum, map_smul, ← mul_apply_eq_comp, Ring.mul_inverse_cancel P hPu,
      one_apply_eq_self] using congrArg P (b.sum_repr' (Ring.inverse P x))
  have hex (J : Fin r → Fin n) :
    f (fun s => S (b (J s))) = ∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K := by
    have hv : (fun s : Fin r => S (b (J s))) = (fun s => ∑ k, c (J s) k • P (b k)) := by
      funext s
      exact (he _).symm
    rw [hv]
    simp only [ContinuousMultilinearMap.map_sum, ContinuousMultilinearMap.map_smul_univ,
      smul_eq_mul]
    rfl
  have hc (k l : Fin n) :
    (∑ j : Fin n, c j k * c j l) = ⟪b k, Ring.inverse (P * A * P) (b l)⟫ := by
    change (∑ j : Fin n, ⟪b k, R (S (b j))⟫ * ⟪b l, R (S (b j))⟫) = _
    rw [energy_coordinate_gram R S hP.ringInverse hspec.2.1, hoperator]
  calc
    cumulantEnergy ν r u =
        ∑ J : Fin r → Fin n, (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2 := by
      unfold cumulantEnergy
      apply Finset.sum_congr rfl
      intro J _
      exact congrArg (fun t : ℝ => t ^ 2) (hex J)
    _ =
        ∑ K : Fin r → Fin n,
          ∑ L : Fin r → Fin n, T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) :=
      energy_tensor_square r c T
    _ =
        energyForm (P * Covariance.operator ν * P)
          (fun K : Fin r → Fin n =>
            cumulant ν (r + 1)
              (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))) := by
      simp only [hc]
      rfl

end FunctionalInequalities.KLS.BKL
