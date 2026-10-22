/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ParameterPowerSpan
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.CCDN.Hilbert.AffineCurveDegree

/-!
If a filtration is eventually generated one step at a time by a parameter,
its linear growth has slope at most the function-field degree over K(t).
Common denominators affect only the fixed additive offset in the bound.

Any finite family in a finite extension of K(t) fits in a bounded power
block after multiplication by one nonzero rational-function denominator.
-/

@[expose] public section
namespace CCDN
noncomputable section

private lemma ratFunc_polynomial_eval {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    (p : Polynomial K) :
    algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p) =
      Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) p := by
  let φ := (IsScalarTower.toAlgHom K (RatFunc K) F).comp
    (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
  have he : φ = Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) := by
    apply Polynomial.algHom_ext
    simp [φ, RatFunc.algebraMap_X]
  exact congrArg (fun f => f p) he

/-- A common parameter denominator makes every supplied vector a bounded
polynomial combination of a fixed function-field basis. -/
private theorem finite_family_parameter_power_span {K F ι : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F] [Finite ι]
    (w : ι → F) :
    ∃ q : F, q ≠ 0 ∧ ∃ D : ℕ, ∀ j,
      q * w j ∈ parameterPowerSpan K (algebraMap (RatFunc K) F RatFunc.X)
        (Module.finBasis (RatFunc K) F) D := by
  classical
  let := Fintype.ofFinite ι
  let b := Module.finBasis (RatFunc K) F
  let r := Module.finrank (RatFunc K) F
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : ι × Fin r => b.repr (w t.1) t.2)
  choose p hp using hq
  let D := Finset.univ.sup (fun t : ι × Fin r => (p t).natDegree)
  let qF := algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) q.val)
  have hqn : q.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp q.property
  have hqF : qF ≠ 0 := (map_ne_zero_iff (algebraMap (RatFunc K) F)
    (algebraMap (RatFunc K) F).injective).mpr (RatFunc.algebraMap_ne_zero hqn)
  refine ⟨qF, hqF, D, ?_⟩
  intro j
  rw [← b.sum_repr (w j), Finset.mul_sum]
  apply (parameterPowerSpan K (algebraMap (RatFunc K) F RatFunc.X) b D).sum_mem
  intro i _
  have he : qF * (b.repr (w j) i • b i) =
      Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) (p (j,i)) * b i := by
    have hp' : algebraMap (Polynomial K) (RatFunc K) (p (j,i)) =
        algebraMap (Polynomial K) (RatFunc K) q.val * b.repr (w j) i :=
      (hp (j,i)).trans (Algebra.smul_def _ _)
    rw [Algebra.smul_def, ← mul_assoc]
    change (algebraMap (RatFunc K) F _ * algebraMap (RatFunc K) F _) * _ = _
    rw [← map_mul, ← hp', ratFunc_polynomial_eval]
  rw [he]
  exact polynomial_parameter_mul_mem _ b i (p (j,i)) D
    (Finset.le_sup (f := fun t : ι × Fin r => (p t).natDegree) (Finset.mem_univ (j,i)))

end
end CCDN

namespace CCDN
noncomputable section

/-- Eventual generation by the parameter bounds filtered dimensions with
slope equal to the rank over its rational-function field. -/
private theorem parameter_recurrence_growth_bound {K A F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F]
    (V : ℕ → Submodule K A) [∀ n, Module.Finite K (V n)]
    (L : A →ₗ[K] A) (φ : A →ₗ[K] F) (hφ : Function.Injective φ)
    (hL : ∀ x, φ (L x) = algebraMap (RatFunc K) F RatFunc.X * φ x)
    (N : ℕ) (hrec : ∀ n ≥ N, V (n + 1) = V n ⊔ (V n).map L) :
    ∃ D : ℕ, ∀ m, Module.finrank K (V (N + m)) ≤
      Module.finrank (RatFunc K) F * (D + m + 1) := by
  classical
  let b := Module.finBasis K (V N)
  let u := algebraMap (RatFunc K) F RatFunc.X
  let v := Module.finBasis (RatFunc K) F
  obtain ⟨q, hq, D, hD⟩ := finite_family_parameter_power_span (K := K) (fun i => φ (b i).val)
  let T := (LinearMap.mulLeft K q).comp φ
  have hT (x : A) : T x = q * φ x := rfl
  have hTi : Function.Injective T := fun x y h => hφ (mul_left_cancel₀ hq h)
  have hTL (x : A) : T (L x) = u * T x := by rw [hT, hL, hT]; ring
  have hbase {x : A} (hx : x ∈ V N) : T x ∈ parameterPowerSpan K u v D := by
    have he : T x = ∑ i, b.repr ⟨x, hx⟩ i • (q * φ (b i).val) := by
      have hh := congrArg (fun z : V N => T z.val) (b.sum_repr ⟨x, hx⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hT, Finset.mul_sum,
        mul_smul_comm] using hh.symm
    rw [he]
    apply (parameterPowerSpan K u v D).sum_mem
    intro i _
    exact (parameterPowerSpan K u v D).smul_mem _ (hD i)
  have hbound (m : ℕ) : ∀ x ∈ V (N + m), T x ∈ parameterPowerSpan K u v (D + m) := by
    induction m with
    | zero =>
      intro x hx
      exact hbase hx
    | succ m ih =>
      intro x hx
      rw [show N + (m + 1) = (N + m) + 1 by omega, hrec (N + m) (by omega)] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨z, hz, rfl⟩ := hz
      rw [map_add, hTL]
      apply (parameterPowerSpan K u v (D + (m + 1))).add_mem
      · exact parameterPowerSpan_mono u v (by omega) (ih y hy)
      · simpa only [Nat.add_assoc] using parameterPowerSpan_mul_mem u v (D + m) (ih z hz)
  refine ⟨D, ?_⟩
  intro m
  let Tm : V (N + m) →ₗ[K] parameterPowerSpan K u v (D + m) :=
    (T.comp (V (N + m)).subtype).codRestrict _ (fun x => hbound m x.val x.property)
  have hi : Function.Injective Tm := by
    intro x y h
    apply Subtype.ext
    apply hTi
    exact congrArg Subtype.val h
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  exact hd.trans (by simpa only [Fintype.card_fin, Nat.add_assoc] using
    parameterPowerSpan_finrank_le u v (D + m))

/-- The Hilbert slope is at most the parameter extension degree whenever the
coordinate filtration has the parameter-generation recurrence. -/
theorem parameter_recurrence_slope_le {K A F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F]
    (V : ℕ → Submodule K A) [∀ n, Module.Finite K (V n)]
    (L : A →ₗ[K] A) (φ : A →ₗ[K] F) (hφ : Function.Injective φ)
    (hL : ∀ x, φ (L x) = algebraMap (RatFunc K) F RatFunc.X * φ x)
    (N : ℕ) (hrec : ∀ n ≥ N, V (n + 1) = V n ⊔ (V n).map L)
    (d : ℕ) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank K (V n) : ℤ) = (d : ℤ) * n + c) :
    d ≤ Module.finrank (RatFunc K) F := by
  obtain ⟨D, hD⟩ := parameter_recurrence_growth_bound V L φ hφ hL N hrec
  obtain ⟨M, c, hc⟩ := hdegree
  apply eventual_linear_slope_le
    (fun m => Module.finrank K (V (N + m)))
    (fun m => Module.finrank (RatFunc K) F * (D + m + 1)) d (Module.finrank (RatFunc K) F)
  · refine ⟨M, (d : ℤ) * N + c, ?_⟩
    intro m hm
    rw [hc (N + m) (by omega)]
    push_cast
    ring
  · refine ⟨0, (Module.finrank (RatFunc K) F : ℤ) * (D + 1), ?_⟩
    intro m _
    push_cast
    ring
  · exact hD

end
end CCDN
