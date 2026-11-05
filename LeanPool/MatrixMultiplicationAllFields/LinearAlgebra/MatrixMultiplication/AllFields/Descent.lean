/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
module

/-
Copyright 2026 Jeroen Zuiddam. Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatMul
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Free

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Descent of exact tensor decompositions to a smaller field

Let `E / P` be a finite field extension of degree `m`.  A decomposition of
`T ⊗_P E` into `R` simple tensors over `E` gives one of `T` into `m³ R` simple
tensors over `P`: expand every coefficient in a `P`-basis of `E` and apply a
`P`-linear functional `π : E → P` with `π 1 = 1`.

A decomposition over an algebraic extension `K / P` only uses finitely many
coefficients, which generate a finite subextension; this reduces the general
algebraic case to the finite one.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AllFields

section MatMul

/-- The matrix multiplication tensor is defined over the prime ring: ring
homomorphisms map it to itself. -/
theorem matMul_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (a b c : ℕ) :
    (fun x y z => f (Tensor.matMul R a b c x y z)) = Tensor.matMul S a b c := by
  funext x y z
  simp only [Tensor.matMul]
  split_ifs <;> simp

/-- Tensor powers of `⟨u,u,u⟩` are `⟨u^j,u^j,u^j⟩`, so rank is submultiplicative
along powers, over any coefficient semiring. -/
theorem rankAtMost_matMul_pow {R : Type*} [CommSemiring R] {u r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matMul R u u u) r) (j : ℕ) :
    Tensor.RankAtMost (Tensor.matMul R (u ^ j) (u ^ j) (u ^ j)) (r ^ j) := by
  classical
  let e : Fin (u ^ j) ≃ (Fin j → Fin u) := Fintype.equivOfCardEq (by simp)
  let f : Fin (u ^ j) × Fin (u ^ j) → Fin j → Fin u × Fin u :=
    fun x i => (e x.1 i, e x.2 i)
  have hp := (h.power j).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power (Tensor.matMul R u u u) j) =
      Tensor.matMul R (u ^ j) (u ^ j) (u ^ j) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, Tensor.matMul, f,
      Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]
  rwa [heq] at hp

end MatMul

section Descent

variable {P E : Type*} [Field P] [Field E] [Algebra P E]

/-- A `P`-linear functional on `E` that is the identity on `P`. -/
theorem exists_functional_one :
    ∃ π : E →ₗ[P] P, π 1 = 1 := by
  classical
  let b := Module.Free.chooseBasis P E
  have hne : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.injective (h.trans (map_zero b.repr).symm))
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
  refine ⟨(b.repr 1 s)⁻¹ • b.coord s, ?_⟩
  simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  exact inv_mul_cancel₀ (by simpa using hs)

/-- A trilinear expansion of `π (e₁ e₂ e₃)` in a basis. -/
theorem functional_mul_mul_eq_sum {ι : Type*} [Fintype ι] (bs : Module.Basis ι P E)
    (π : E →ₗ[P] P) (e₁ e₂ e₃ : E) :
    π (e₁ * e₂ * e₃) = ∑ w, ∑ t, ∑ s,
      bs.repr e₁ s * bs.repr e₂ t * bs.repr e₃ w * π (bs s * bs t * bs w) := by
  conv_lhs => rw [← bs.sum_repr e₁, ← bs.sum_repr e₂, ← bs.sum_repr e₃]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc, mul_smul_comm,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- **Descent.** If `T` has coefficients in `P` and `T ⊗ E` has rank at most `R`
over a finite extension `E / P` of degree `m`, then `T` has rank at most
`m³ R` over `P`. -/
theorem rankAtMost_of_map [FiniteDimensional P E] {X Y Z : Type*}
    {T : Tensor P X Y Z} {R : ℕ}
    (h : Tensor.RankAtMost (fun x y z => algebraMap P E (T x y z)) R) :
    Tensor.RankAtMost T (Module.finrank P E ^ 3 * R) := by
  classical
  obtain ⟨a, b, c, hT⟩ := h
  obtain ⟨π, hπ⟩ := exists_functional_one (P := P) (E := E)
  let m := Module.finrank P E
  let bs : Module.Basis (Fin m) P E := Module.finBasis P E
  let A : Fin R × Fin m × Fin m × Fin m → X → P :=
    fun q x => bs.repr (a q.1 x) q.2.2.2
  let B : Fin R × Fin m × Fin m × Fin m → Y → P :=
    fun q y => bs.repr (b q.1 y) q.2.2.1
  let C : Fin R × Fin m × Fin m × Fin m → Z → P :=
    fun q z => bs.repr (c q.1 z) q.2.1 * π (bs q.2.2.2 * bs q.2.2.1 * bs q.2.1)
  have hentry : T = fun x y z => ∑ q, Tensor.rankOne (A q) (B q) (C q) x y z := by
    funext x y z
    have h1 : T x y z = π (algebraMap P E (T x y z)) := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
    rw [h1, congrFun (congrFun (congrFun hT x) y) z, map_sum]
    simp only [Tensor.rankOne, Fintype.sum_prod_type, A, B, C]
    apply Finset.sum_congr rfl
    intro l _
    rw [functional_mul_mul_eq_sum bs π]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hentry]
  convert Tensor.rankAtMost_sum_rankOne A B C using 1
  simp only [Fintype.card_prod, Fintype.card_fin, m]
  ring

end Descent

section Algebraic

variable {P K : Type*} [Field P] [Field K] [Algebra P K] [Algebra.IsAlgebraic P K]

/-- A decomposition over an algebraic extension `K / P` uses finitely many
coefficients; they generate a finite-dimensional intermediate field `E`, over
which the same decomposition already exists. -/
theorem exists_finiteDimensional_rankAtMost {X Y Z : Type*}
    [Finite X] [Finite Y] [Finite Z] {T : Tensor P X Y Z} {R : ℕ}
    (h : Tensor.RankAtMost (fun x y z => algebraMap P K (T x y z)) R) :
    ∃ E : IntermediateField P K, FiniteDimensional P E ∧
      Tensor.RankAtMost (fun x y z => algebraMap P E (T x y z)) R := by
  classical
  obtain ⟨a, b, c, hT⟩ := h
  let S : Set K := (Set.range (fun q : Fin R × X => a q.1 q.2) ∪
    Set.range (fun q : Fin R × Y => b q.1 q.2)) ∪ Set.range (fun q : Fin R × Z => c q.1 q.2)
  have hSfin : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  have : Finite S := hSfin.to_subtype
  let E := IntermediateField.adjoin P S
  have hfd : FiniteDimensional P E :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := P) x).isIntegral)
  have ha : ∀ l x, a l x ∈ E := fun l x =>
    IntermediateField.subset_adjoin P S (Or.inl (Or.inl ⟨(l, x), rfl⟩))
  have hb : ∀ l y, b l y ∈ E := fun l y =>
    IntermediateField.subset_adjoin P S (Or.inl (Or.inr ⟨(l, y), rfl⟩))
  have hc : ∀ l z, c l z ∈ E := fun l z =>
    IntermediateField.subset_adjoin P S (Or.inr ⟨(l, z), rfl⟩)
  refine ⟨E, hfd, fun l x => ⟨a l x, ha l x⟩, fun l y => ⟨b l y, hb l y⟩,
    fun l z => ⟨c l z, hc l z⟩, ?_⟩
  funext x y z
  apply Subtype.ext
  have hxyz := congrFun (congrFun (congrFun hT x) y) z
  simp only [Tensor.rankOne] at hxyz ⊢
  rw [IntermediateField.coe_sum]
  simpa [IntermediateField.algebraMap_apply] using hxyz

end Algebraic

end MatrixMultiplication.AllFields

end

end MatrixMultiplicationAllFields
