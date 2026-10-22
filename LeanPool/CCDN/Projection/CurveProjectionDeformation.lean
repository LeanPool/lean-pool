/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import LeanPool.CCDN.Plane.LinearDeformation
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.CCDN.Algebra.PolynomialFamilyRelations
import LeanPool.CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad

/-! Construct a polynomial family of plane relations for linear
projections of a prime affine curve. The relation has degree at most the
curve's Hilbert degree and remains nonzero at parameter zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma planeLinearDeformation_eval_quotient {K τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (l : MvPolynomial τ K) (t : K) (f : MvPolynomial (Fin 2) K) :
    (planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
      ((Ideal.Quotient.mk I) l) f).eval (algebraMap K (MvPolynomial τ K ⧸ I) t) =
      projectionCoordinateMap I (![a 0, a 1 + t • l]) f := by
  let E : Polynomial (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial τ K ⧸ I) :=
    (Polynomial.aeval (algebraMap K (MvPolynomial τ K ⧸ I) t)).restrictScalars K
  have he : E.comp (planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
      ((Ideal.Quotient.mk I) l)) = projectionCoordinateMap I (![a 0, a 1 + t • l]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [E, planeLinearDeformation, projectionCoordinateMap, Algebra.smul_def]
    · have hC : (Ideal.Quotient.mk I) (C t) =
          algebraMap K (MvPolynomial τ K ⧸ I) t := (Ideal.Quotient.mkₐ K I).commutes t
      simpa [E, planeLinearDeformation, projectionCoordinateMap, Algebra.smul_def, hC] using
        mul_comm ((Ideal.Quotient.mk I) l) (algebraMap K (MvPolynomial τ K ⧸ I) t)
  exact congrArg (fun ψ => ψ f) he

/-- Every bounded-degree linear displacement has a nonzero plane relation.
The relations can be chosen polynomially in the displacement parameter and
with a nonzero specialization at zero. -/
theorem exists_curve_projection_relation_family {K τ : Type*}
    [Field K] [CharZero K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (l : MvPolynomial τ K) (hl : l.totalDegree ≤ 1) :
    let V := restrictTotalDegree (Fin 2) K d
    let b := Module.finBasis K V
    ∃ v : Fin (Module.finrank K V) → Polynomial K,
      (∑ j, (v j).map (algebraMap K (MvPolynomial τ K ⧸ I)) *
        planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
          ((Ideal.Quotient.mk I) l) (b j).val) = 0 ∧
      ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  let := Fintype.ofFinite τ
  let V := restrictTotalDegree (Fin 2) K d
  let b := Module.finBasis K V
  let ψ := planeLinearDeformation (K := K) (fun i => (Ideal.Quotient.mk I) (a i)) 1
    ((Ideal.Quotient.mk I) l)
  let g := fun j => ψ (b j).val
  apply polynomial_family_relation_nonzero_at_zero g
  intro k
  let aT : Fin 2 → MvPolynomial τ K := ![a 0, a 1 + (k : K) • l]
  have hat (i : Fin 2) : (aT i).totalDegree ≤ 1 := by
    fin_cases i
    · exact ha 0
    · change (a 1 + (k : K) • l).totalDegree ≤ 1
      apply (totalDegree_add _ _).trans
      apply max_le (ha 1)
      exact (totalDegree_smul_le _ _).trans hl
  obtain ⟨p, hp, _, hpd, hkernel⟩ := exists_plane_projection_equation_degree_le
    I aT hat d hdegree 0 hu
  have hpzero : projectionCoordinateMap I aT p = 0 := by
    change (Ideal.Quotient.mk I) (aeval aT p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hkernel p).mpr (dvd_refl p))
  let pV : V := ⟨p, (mem_restrictTotalDegree _ _ _).mpr hpd⟩
  let c := fun j => b.repr pV j
  have hc : c ≠ 0 := by
    intro hzero
    have hpV : pV = 0 := by
      apply b.repr.injective
      ext j
      simpa only [map_zero, Finsupp.zero_apply, Pi.zero_apply] using congrFun hzero j
    exact hp.ne_zero (congrArg Subtype.val hpV)
  have hs : ∑ j, c j • (b j).val = p := by
    have hh := congrArg Subtype.val (b.sum_repr pV)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hh
  refine ⟨c, hc, ?_⟩
  have hev (j : Fin (Module.finrank K V)) : (g j).eval (k : MvPolynomial τ K ⧸ I) =
      projectionCoordinateMap I aT (b j).val := by
    simpa only [map_natCast] using planeLinearDeformation_eval_quotient I a l (k : K) (b j).val
  simp only [hev]
  simp_rw [← map_smul]
  rw [← map_sum, hs, hpzero]

end
end CCDN
