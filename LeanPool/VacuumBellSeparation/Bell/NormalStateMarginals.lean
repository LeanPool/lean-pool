/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.VectorFunctionalNormal

/-!
Restrictions to concrete unital VNA subalgebras are states and preserve order
normality. The latter uses arbitrary directed positive suprema and the actual
strong operator limit, not a sequential or finite-dimensional surrogate.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The two concrete algebras embed in their actual joint double commutant. -/
theorem union_subset_jointAlgebra (A B : VonNeumannAlgebra H) :
    (A : Set (H →L[ℂ] H)) ∪ (B : Set (H →L[ℂ] H)) ⊆ jointAlgebra A B := by
  intro X hX
  exact StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ hX)

/-- The left unital star-algebra inclusion into the joint algebra. -/
def jointLeft (A B : VonNeumannAlgebra H) :
    A.toStarSubalgebra →⋆ₐ[ℂ] (jointAlgebra A B).toStarSubalgebra :=
  StarSubalgebra.inclusion fun _ hX =>
    union_subset_jointAlgebra A B (Set.mem_union_left _ hX)

/-- The right unital star-algebra inclusion into the joint algebra. -/
def jointRight (A B : VonNeumannAlgebra H) :
    B.toStarSubalgebra →⋆ₐ[ℂ] (jointAlgebra A B).toStarSubalgebra :=
  StarSubalgebra.inclusion fun _ hX =>
    union_subset_jointAlgebra A B (Set.mem_union_right _ hX)

/-- Inclusion is positive for the inherited operator order. -/
def vnaInclusionPositive {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra) :
    M.toStarSubalgebra →ₚ[ℂ] N.toStarSubalgebra where
  toLinearMap := (StarSubalgebra.inclusion h).toLinearMap
  monotone' := fun _ _ hXY => hXY

/-- A state has the literal unit normalization as a function. -/
theorem IsStateFunctional.apply_one {M : VonNeumannAlgebra H}
    {f : M.toStarSubalgebra → ℂ} (hf : IsStateFunctional M f) : f 1 = 1 := by
  obtain ⟨φ, hφ, he⟩ := hf
  exact (he 1).symm.trans hφ

/-- Positive unital restriction, without any extension to the ambient B(H). -/
theorem IsStateFunctional.restrict {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    {f : N.toStarSubalgebra → ℂ} (hf : IsStateFunctional N f) :
    IsStateFunctional M (fun X => f (StarSubalgebra.inclusion h X)) := by
  obtain ⟨φ, hφ, he⟩ := hf
  refine ⟨φ.comp (vnaInclusionPositive h), ?_, ?_⟩
  · change φ (StarSubalgebra.inclusion h 1) = 1
    simpa only [map_one] using hφ
  · intro X
    exact he (StarSubalgebra.inclusion h X)

/-- An internal positive directed supremum is preserved by concrete inclusion. -/
theorem isLUB_inclusion_image_positive {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ X ∈ s, 0 ≤ X) {X : M.toStarSubalgebra} (hX : IsLUB s X) :
    IsLUB ((StarSubalgebra.inclusion h) '' s) (StarSubalgebra.inclusion h X) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact hX.1 hY
  · intro Y hY
    change (X : H →L[ℂ] H) ≤ (Y : H →L[ℂ] H)
    exact Gaussian.operator_le_of_strong_tendsto
      (strong_tendsto_of_isLUB_positive M hs hdir hpos hX)
      (fun _ => tendsto_const_nhds)
      (Filter.Eventually.of_forall fun i : s =>
        (show (i.1 : H →L[ℂ] H) ≤ (Y : H →L[ℂ] H) from
          hY ⟨i.1, i.2, rfl⟩))

/-- Arbitrary directed-set normality passes to a concrete VNA restriction. -/
theorem IsNormalFunctional.restrict {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    {f : N.toStarSubalgebra → ℂ} (hf : IsNormalFunctional N f) :
    IsNormalFunctional M (fun X => f (StarSubalgebra.inclusion h X)) := by
  intro s hs hdir hpos X hX
  let i := StarSubalgebra.inclusion h
  have hdir' : DirectedOn (· ≤ ·) (i '' s) := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨Z, hZ, rfl⟩
    obtain ⟨W, hW, hYW, hZW⟩ := hdir Y hY Z hZ
    exact ⟨i W, ⟨W, hW, rfl⟩, hYW, hZW⟩
  have hpos' : ∀ Y ∈ i '' s, 0 ≤ Y := by
    rintro _ ⟨Y, hY, rfl⟩
    exact hpos Y hY
  have h := hf (i '' s) (hs.image i) hdir' hpos' (i X)
    (isLUB_inclusion_image_positive h hs hdir hpos hX)
  simpa only [Set.image_image] using h

/-- No normality field is added to the definition; this is its restriction proof. -/
theorem IsNormalStateFunctional.restrict {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    {f : N.toStarSubalgebra → ℂ} (hf : IsNormalStateFunctional N f) :
    IsNormalStateFunctional M (fun X => f (StarSubalgebra.inclusion h X)) :=
  ⟨hf.1.restrict h, hf.2.restrict h⟩

/-- Own-marginal factorization can be checked on the two bundled inclusions. -/
theorem hasProductFactorization_iff_bundled (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) :
    HasProductFactorization A B f ↔
      ∀ X : A.toStarSubalgebra, ∀ Y : B.toStarSubalgebra,
        f (jointLeft A B X * jointRight A B Y) =
          f (jointLeft A B X) * f (jointRight A B Y) := by
  constructor
  · intro h X Y
    exact h _ _ X.2 Y.2
  · intro h X Y hX hY
    exact h (⟨X.1, hX⟩ : A.toStarSubalgebra) (⟨Y.1, hY⟩ : B.toStarSubalgebra)

/-- Any normalized factor states must equal the actual marginal restrictions. -/
theorem product_marginals_unique (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ)
    (fA : A.toStarSubalgebra → ℂ) (fB : B.toStarSubalgebra → ℂ)
    (hA : fA 1 = 1) (hB : fB 1 = 1)
    (hprod : ∀ X Y, f (jointLeft A B X * jointRight A B Y) = fA X * fB Y) :
    (∀ X, f (jointLeft A B X) = fA X) ∧
      (∀ Y, f (jointRight A B Y) = fB Y) := by
  constructor
  · intro X
    simpa only [map_one, mul_one, hB] using hprod X 1
  · intro Y
    simpa only [map_one, one_mul, hA] using hprod 1 Y

/-- Literal existential normal marginal states, equivalent to own marginals
for a normal joint state. No split/tensor-product or independence premise. -/
theorem hasProductFactorization_iff_exists_normal_marginals
    (A B : VonNeumannAlgebra H)
    {f : (jointAlgebra A B).toStarSubalgebra → ℂ}
    (hf : IsNormalStateFunctional (jointAlgebra A B) f) :
    HasProductFactorization A B f ↔
      ∃ fA : A.toStarSubalgebra → ℂ, ∃ fB : B.toStarSubalgebra → ℂ,
        IsNormalStateFunctional A fA ∧ IsNormalStateFunctional B fB ∧
          ∀ X Y, f (jointLeft A B X * jointRight A B Y) = fA X * fB Y := by
  constructor
  · intro hp
    refine ⟨fun X => f (jointLeft A B X), fun Y => f (jointRight A B Y),
      ?_, ?_, (hasProductFactorization_iff_bundled A B f).mp hp⟩
    · exact hf.restrict (fun _ hX => union_subset_jointAlgebra A B (Set.mem_union_left _ hX))
    · exact hf.restrict (fun _ hY => union_subset_jointAlgebra A B (Set.mem_union_right _ hY))
  · rintro ⟨fA, fB, hA, hB, hp⟩
    obtain ⟨hleft, hright⟩ := product_marginals_unique A B f fA fB
      hA.1.apply_one hB.1.apply_one hp
    apply (hasProductFactorization_iff_bundled A B f).mpr
    intro X Y
    rw [hp, hleft, hright]

/-- The entire normal-product predicate in existential marginal form. -/
theorem isNormalProductState_iff_exists_normal_marginals
    (A B : VonNeumannAlgebra H) (f : (jointAlgebra A B).toStarSubalgebra → ℂ) :
    IsNormalProductState A B f ↔
      IsNormalStateFunctional (jointAlgebra A B) f ∧
        ∃ fA : A.toStarSubalgebra → ℂ, ∃ fB : B.toStarSubalgebra → ℂ,
          IsNormalStateFunctional A fA ∧ IsNormalStateFunctional B fB ∧
            ∀ X Y, f (jointLeft A B X * jointRight A B Y) = fA X * fB Y := by
  constructor
  · intro hf
    exact ⟨hf.1, (hasProductFactorization_iff_exists_normal_marginals A B hf.1).mp hf.2⟩
  · rintro ⟨hf, hmarginals⟩
    exact ⟨hf, (hasProductFactorization_iff_exists_normal_marginals A B hf).mpr hmarginals⟩

end VacuumBellSeparation.Bipartite
