/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
public import LeanPool.CCDN.Projection.CurvePrimitivePair
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.CCDN.Algebra.ParameterRecurrenceGrowth
import LeanPool.CCDN.Height.BoundedPrimitiveElement
import LeanPool.CCDN.Hilbert.CurveFunctionField
import LeanPool.CCDN.Projection.FieldDegree
import LeanPool.CCDN.Projection.PlaneProjectionKernel

/-!
Once a linear parameter generates the degree filtration, a bounded moment
coordinate produces a degree-preserving plane equation. This combines
full function-field degree with the quantitative primitive-element theorem.

Eventual generation of the affine degree filtration by a linear parameter
forces the function-field extension to have the full Hilbert degree.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- A linear parameter generating the filtration in large degrees gives a
function-field extension of degree exactly d. -/
private theorem curve_parameter_full_degree_of_recurrence {K F σ : Type*}
    [Field K] [Field F] [Finite σ] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (he : algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) l) =
      algebraMap (RatFunc K) F RatFunc.X)
    (N : ℕ) (hrec : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) =
      filteredCoordinateSpace I n ⊔ (filteredCoordinateSpace I n).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    Module.Finite (RatFunc K) F ∧ Module.finrank (RatFunc K) F = d := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨hfinite, hupper⟩ := curve_functionField_finite_rank_le I d hdegree l hl
    RatFunc.X RatFunc.transcendental_X he
  let : Module.Finite (RatFunc K) F := hfinite
  let φ := IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F
  have hcomm (x : MvPolynomial σ K ⧸ I) :
      φ.toLinearMap ((LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) x) =
        algebraMap (RatFunc K) F RatFunc.X * φ.toLinearMap x := by
    change φ (((Ideal.Quotient.mk I) l) * x) = _
    rw [map_mul]
    exact congrArg (fun y => y * φ x) he
  have hlower := parameter_recurrence_slope_le (filteredCoordinateSpace I)
    (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) φ.toLinearMap
    (IsFractionRing.injective _ _) hcomm N hrec d hdegree
  exact ⟨hfinite, Nat.le_antisymm hupper hlower⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Build the bounded second projection coordinate and a plane equation of
exactly degree d from a parameter satisfying eventual filtered generation. -/
theorem exists_full_degree_primitive_projection {K F : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (l : MvPolynomial (Fin n) K) (hl : l.totalDegree ≤ 1)
    (he : algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l) =
      algebraMap (RatFunc K) F RatFunc.X)
    (N : ℕ) (hrec : ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      Irreducible f ∧ f.totalDegree = d ∧
      ∀ g, aeval (![l, momentCoordinate K n k]) g ∈ I ↔ f ∣ g := by
  obtain ⟨hfinite, hfull⟩ := curve_parameter_full_degree_of_recurrence I d hdegree l hl he N hrec
  let : Module.Finite (RatFunc K) F := hfinite
  let φ := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F
  have hu : Transcendental K ((Ideal.Quotient.mk I) l) := by
    intro h
    have hh := (isAlgebraic_algHom_iff φ (IsFractionRing.injective _ _)).mpr h
    change IsAlgebraic K (algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l)) at hh
    rw [he] at hh
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (RatFunc K) F) (algebraMap (RatFunc K) F).injective).mp hh)
  obtain ⟨k, hk, hprim⟩ := exists_bounded_curve_primitive_element (R := RatFunc K) (F := F) I
  let a : Fin 2 → MvPolynomial (Fin n) K := ![l, momentCoordinate K n k]
  have ha (i : Fin 2) : (a i).totalDegree ≤ 1 := by
    fin_cases i
    · exact hl
    · exact momentCoordinate_degree K n k
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree 0 hu
  have hp : IntermediateField.adjoin (RatFunc K) {φ ((Ideal.Quotient.mk I) (a 1))} = ⊤ := by
    change IntermediateField.adjoin (RatFunc K)
      {algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤
    rwa [momentCoordinate_fraction]
  have hfd := plane_projection_degree_eq_of_full_parameter I a ha d hdegree φ f hf.ne_zero hker
    0 1 RatFunc.X RatFunc.transcendental_X he hp hfull
  refine ⟨k, f, by simpa only [hfull] using hk, hf, hfd, ?_⟩
  intro g
  have hg : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) := by
    change _ ↔ (Ideal.Quotient.mk I) (aeval a g) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hg, hker, Ideal.mem_span_singleton]

end
end CCDN
