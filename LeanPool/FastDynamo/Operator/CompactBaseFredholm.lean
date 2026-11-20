/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.CompactAtkinsonIndexZero

/-!
# Ambient compact-base Fredholm and index-zero bridge

Atkinson's theorem and its index computation are available here only on a
Hilbert space.  A factorization of the affine pencil through an
identity-minus-compact endomorphism **of the graph domain** would therefore
demand `InnerProductSpace ℂ D`; the torus graph domains are closed submodules
of sup-normed products and carry no such instance.

The paper's own argument (proof of `lem:torus-sector-basic`) is
ambient-sided: `z - A` differs from the isomorphism `id - ε Δ⊥ : H² → L²` by
an operator bounded `H¹ → L²`, hence compact `H² → L²`.  This file records the corresponding
base-point factorization on the ambient side,

`pencil z = (1 + (z - z₀) • stateResolvent z₀) ∘ pencil z₀`,

whose first factor is an identity-minus-compact endomorphism of `X`.  Only
`InnerProductSpace ℂ X` is then needed, and the ambient space of the torus
problem, `TransverseC3L2 = Lp C3 2 transverseMeasure`, is a Hilbert space.

The setwise package is exposed as `PencilFredholmIndexZeroOn`, stated under
weak `NormedSpace` typeclass assumptions.

No left parametrix, no orthogonal projection on `D`, and no cokernel
identification is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set
open scoped LinearMap.FiniteRangeSetoid

namespace CompactBaseFredholm

universe u v w

/-! ## The setwise Fredholm/index-zero interface -/

section Interface

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The two non-quantitative facts that upgrade a small right inverse of the
affine pencil to an inverse.  Neither field asserts invertibility, surjectivity,
injectivity, or nonvanishing. -/
structure PencilFredholmIndexZeroOn (A : DomainOperator X D) (S : Set ℂ) :
    Prop where
  isFredholm : ∀ z ∈ S, ContinuousLinearMap.IsFredholm (A.pencil z)
  index_eq_zero : ∀ z ∈ S, (A.pencil z).toLinearMap.index = 0

end Interface

/-! ## Ambient base-point factorization -/

section AmbientHilbert

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The ambient correction in the base-point factorization.  It is the
`DomainOperator.resolventCorrection` of the base state resolvent, written out
here so that this module depends only on the compact Atkinson chain. -/
def ambientBaseCorrection (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀}) (z : ℂ) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X + (z - z₀) • h₀.stateResolvent z₀

omit [CompleteSpace X] in
/-- Exact ambient base-point factorization of every value of the affine
pencil.  The correction acts on the ambient space, after the base pencil. -/
theorem ambientBaseCorrection_comp_pencil
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀}) (z : ℂ) :
    (ambientBaseCorrection A h₀ z).comp (A.pencil z₀) = A.pencil z := by
  apply ContinuousLinearMap.ext
  intro d
  have hleft := DFunLike.congr_fun (h₀.left_inv z₀ (by simp)) d
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hleft
  have hp := DFunLike.congr_fun (A.pencil_sub_pencil z z₀) d
  simp only [sub_apply, smul_apply] at hp
  simp only [ambientBaseCorrection, HasResolventOn.stateResolvent,
    ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, hleft]
  exact ((eq_add_of_sub_eq hp).trans (add_comm _ _)).symm

/-- The ambient correction is identity minus a compact endomorphism of the
ambient space. -/
theorem isFredholm_ambientBaseCorrection
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀)) (z : ℂ) :
    ContinuousLinearMap.IsFredholm (ambientBaseCorrection A h₀ z) := by
  let K : X →L[ℂ] X := -(z - z₀) • h₀.stateResolvent z₀
  have hK : IsCompactOperator K := hcompact.smul (-(z - z₀))
  have hcorr : ambientBaseCorrection A h₀ z =
      ContinuousLinearMap.id ℂ X - K := by
    ext x
    simp [ambientBaseCorrection, K]
  rw [hcorr]
  exact CompactAtkinson.isFredholm_id_sub_of_isCompact hK

/-- The ambient correction has algebraic Fredholm index zero. -/
theorem index_ambientBaseCorrection_eq_zero
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀)) (z : ℂ) :
    (ambientBaseCorrection A h₀ z).toLinearMap.index = 0 := by
  let K : X →L[ℂ] X := -(z - z₀) • h₀.stateResolvent z₀
  have hK : IsCompactOperator K := hcompact.smul (-(z - z₀))
  have hcorr : ambientBaseCorrection A h₀ z =
      ContinuousLinearMap.id ℂ X - K := by
    ext x
    simp [ambientBaseCorrection, K]
  rw [hcorr]
  exact CompactAtkinsonIndexZero.index_id_sub_of_isCompact hK

/-! ## Transport through the invertible base pencil -/

omit [CompleteSpace X] in
/-- Right composition with an invertible map preserves Fredholmness.  The
quasi-inverse formulation avoids choosing complements. -/
theorem isFredholm_comp_of_isInvertible_right
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : D →L[ℂ] X} {T : X →L[ℂ] E}
    (hU : U.IsInvertible) (hT : ContinuousLinearMap.IsFredholm T) :
    ContinuousLinearMap.IsFredholm (T.comp U) := by
  obtain ⟨q, hq⟩ := hT.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
    (v := U.inverse.comp q)
  have hUq : U.inverse.IsQuasiInverse U := by
    constructor
    · change U.inverse.toLinearMap.comp U.toLinearMap ≈ LinearMap.id
      rw [← ContinuousLinearMap.toLinearMap_comp, hU.inverse_comp_self]
      exact Setoid.refl _
    · change U.toLinearMap.comp U.inverse.toLinearMap ≈ LinearMap.id
      rw [← ContinuousLinearMap.toLinearMap_comp, hU.self_comp_inverse]
      exact Setoid.refl _
  simpa only [ContinuousLinearMap.toLinearMap_comp] using hUq.comp hq

omit [CompleteSpace X] in
/-- The base pencil is invertible as a bounded map from the graph domain. -/
theorem isInvertible_pencil_base
    (A : DomainOperator X D) {z₀ : ℂ} (h₀ : HasResolventOn A {z₀}) :
    (A.pencil z₀).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (h₀.right_inv z₀ (by simp)) (h₀.left_inv z₀ (by simp))

/-- Compactness of one ambient base state resolvent makes every pencil value
Fredholm.  Only the ambient space is assumed Hilbert. -/
theorem pencil_isFredholm_of_compact_ambient_base_stateResolvent
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀)) (z : ℂ) :
    ContinuousLinearMap.IsFredholm (A.pencil z) := by
  rw [← ambientBaseCorrection_comp_pencil A h₀ z]
  exact isFredholm_comp_of_isInvertible_right (isInvertible_pencil_base A h₀)
    (isFredholm_ambientBaseCorrection A h₀ hcompact z)

/-- Compactness of one ambient base state resolvent makes every pencil value
have algebraic Fredholm index zero. -/
theorem pencil_index_eq_zero_of_compact_ambient_base_stateResolvent
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀)) (z : ℂ) :
    (A.pencil z).toLinearMap.index = 0 := by
  let C : X →L[ℂ] X := ambientBaseCorrection A h₀ z
  let U : D →L[ℂ] X := A.pencil z₀
  have hU : U.IsInvertible := isInvertible_pencil_base A h₀
  have hCFred : ContinuousLinearMap.IsFredholm C :=
    isFredholm_ambientBaseCorrection A h₀ hcompact z
  have hUFred : ContinuousLinearMap.IsFredholm U :=
    FredholmIsolation.IsInvertible.isFredholm hU
  let : FiniteDimensional ℂ C.ker := hCFred.finite_ker
  let : FiniteDimensional ℂ (X ⧸ C.range) := hCFred.finite_coker
  let : FiniteDimensional ℂ U.ker := hUFred.finite_ker
  let : FiniteDimensional ℂ (X ⧸ U.range) := hUFred.finite_coker
  have hfactor : C.comp U = A.pencil z :=
    ambientBaseCorrection_comp_pencil A h₀ z
  rw [← hfactor]
  change (C.toLinearMap.comp U.toLinearMap).index = 0
  rw [LinearMap.index_comp]
  have hUindex : U.toLinearMap.index = 0 := by
    rcases hU with ⟨e, he⟩
    rw [← he]
    exact e.toLinearEquiv.index_eq_zero
  rw [hUindex, index_ambientBaseCorrection_eq_zero A h₀ hcompact z]
  simp

/-- Setwise packaging of the two Fredholm inputs, as a pair of universally
quantified statements. -/
theorem pencil_fredholm_index_zero_on_of_compact_ambient_base_stateResolvent
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀)) (S : Set ℂ) :
    (∀ z ∈ S, ContinuousLinearMap.IsFredholm (A.pencil z)) ∧
      ∀ z ∈ S, (A.pencil z).toLinearMap.index = 0 := by
  constructor
  · intro z _hz
    exact pencil_isFredholm_of_compact_ambient_base_stateResolvent
      A h₀ hcompact z
  · intro z _hz
    exact pencil_index_eq_zero_of_compact_ambient_base_stateResolvent
      A h₀ hcompact z

/-- A compact state resolvent at one base point constructs the setwise
Fredholm/index-zero package, with the Hilbert assumption on the **ambient**
space only.  A graph-domain Hilbert structure is not available at the
two-component fibre, which is why this is the constructor the route uses. -/
theorem PencilFredholmIndexZeroOn.ofCompactAmbientBase
    (A : DomainOperator X D) {z₀ : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀))
    (S : Set ℂ) : PencilFredholmIndexZeroOn A S := by
  obtain ⟨hFredholm, hindex⟩ :=
    pencil_fredholm_index_zero_on_of_compact_ambient_base_stateResolvent
      A h₀ hcompact S
  exact ⟨hFredholm, hindex⟩

end AmbientHilbert

end CompactBaseFredholm

end

end FastDynamo
