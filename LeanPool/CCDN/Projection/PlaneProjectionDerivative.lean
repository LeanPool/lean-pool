/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import LeanPool.CCDN.Determinant.PlaneSingularities
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative
import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! In characteristic zero, a plane relation with a transcendental first
coordinate has a nonzero derivative in the second coordinate. That derivative
is a proper section of degree at most d-1 of the source curve. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero relation cannot omit the coordinate complementary to a
transcendental coordinate. -/
private theorem plane_relation_pderiv_ne_zero {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [Algebra K A] (ψ : MvPolynomial (Fin 2) K →ₐ[K] A)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (hjk : j ≠ k) (hj : Transcendental K (ψ (X j))) :
    pderiv k f ≠ 0 := by
  classical
  intro hz
  have hk := notMem_vars_of_pderiv_eq_zero hz fun n hn _ ↦ Nat.cast_ne_zero.mpr hn.ne'
  have hvars : (f.vars : Set (Fin 2)) ⊆ Set.range (fun _ : Unit => j) := by
    intro t ht
    have htk : t ≠ k := fun h => hk (h ▸ ht)
    have htj : t = j := by omega
    exact ⟨(), htj.symm⟩
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range f (fun _ : Unit => j)
    (Function.injective_of_subsingleton _) hvars
  have he : ψ.comp (rename (fun _ : Unit => j)) = aeval (fun _ : Unit => ψ (X j)) := by
    apply MvPolynomial.algHom_ext
    intro t
    simp
  have hi : Function.Injective (aeval (R := K) (fun _ : Unit => ψ (X j))) :=
    (algebraicIndependent_unique_type_iff (R := K) (x := fun _ : Unit => ψ (X j))).mpr hj
  have hz : aeval (fun _ : Unit => ψ (X j)) g = 0 := by
    rw [← he]
    change ψ (rename (fun _ : Unit => j) g) = 0
    rwa [hg]
  have hg0 : g = 0 := hi (by simpa only [map_zero] using hz)
  exact hf (by rw [← hg, hg0, map_zero])

/-- The derivative is a proper degree-(d-1) section when f generates the
projection kernel. This is the proposed common reconstruction cut. -/
theorem projection_derivative_proper {K τ : Type*} [Field K] [CharZero K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (j k : Fin 2) (hjk : j ≠ k)
    (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    aeval a (pderiv k f) ∉ I ∧
      (aeval a (pderiv k f)).totalDegree ≤ f.totalDegree - 1 := by
  classical
  let := Fintype.ofFinite τ
  let ψ := projectionCoordinateMap I a
  have hz : ψ f = 0 := by
    change (Ideal.Quotient.mk I) (aeval a f) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker f).mpr (dvd_refl f))
  have ht : Transcendental K (ψ (X j)) := by
    change Transcendental K ((Ideal.Quotient.mk I) (aeval a (X j)))
    rwa [aeval_X]
  have hp := plane_relation_pderiv_ne_zero ψ f hf hz j k hjk ht
  refine ⟨fun hbad => not_dvd_pderiv_of_pderiv_ne_zero hf hp ((hker _).mp hbad),
    (aeval_totalDegree_le a ha _).trans ?_⟩
  simpa only [one_mul] using pderiv_totalDegree_le f k

end
end CCDN
