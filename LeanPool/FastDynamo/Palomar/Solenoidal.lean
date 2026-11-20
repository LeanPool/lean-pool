/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Palomar.FourierDictionary
public import LeanPool.FastDynamo.Dynamics.Ideal.SolenoidalInvariance
public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate

/-!
# The solenoidal subspace of the Challenge statement

The Challenge statement defines `L²_σ(𝕋³)` as the orthogonal complement `L2σ` of the gradients of
the Fourier characters in `L2`.  The library's solenoidal subspace on the literal three-torus,
`literalSolenoidalSubspace`, is the image of the Fourier-defined product subspace
`productSolenoidalSubspace` under the isometric transport `toLiteralC3L2`.  Since `L2` and
`LiteralC3L2` are the same type, the two are submodules of one space, and they are equal
(`L2σ_eq_literalSolenoidalSubspace`): both are cut out by `∑ᵢ mᵢ B̂ᵢ(m) = 0` for every `m ∈ ℤ³`.

## Contents

* `L2σ_eq_literalSolenoidalSubspace`, `mem_literalSolenoidalSubspace_iff`,
  `toLiteralC3L2_mem_L2σ_iff`, `L2σ_eq_map_productSolenoidalSubspace` — the subspaces.
* `literalSolenoidalEquivL2σ : literalSolenoidalSubspace ≃ₗᵢ[ℂ] L2σ` and
  `productSolenoidalEquivL2σ : productSolenoidalSubspace ≃ₗᵢ[ℂ] L2σ`, with simp lemmas for the
  coercions to `L2` and `ProductC3L2`.
* `conjOp e : (X →L[ℂ] X) ≃ₗᵢ[ℂ] (Y →L[ℂ] Y)` — conjugation of operators by a surjective linear
  isometry `e : X ≃ₗᵢ[ℂ] Y`; it preserves operator norms, identities and composition, so it carries
  semigroups and groups of operators on the library's spaces to `L2σ` and back
  (`StronglyContinuousSemigroup.congr_operator_eq_conjOp`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus

/-! ## The subspaces -/

/-- The library's literal solenoidal subspace in the Challenge's Fourier form. -/
theorem mem_literalSolenoidalSubspace_iff (B : L2) :
    B ∈ literalSolenoidalSubspace ↔
      ∀ m : Fin 3 → ℤ, ∑ i, (m i : ℂ) * mFourierCoeff (fun x ↦ B x i) m = 0 := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ m : Fin 3 → ℤ, (∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
      inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B)) =
        2 * Real.pi * Complex.I * ∑ i, (m i : ℂ) * mFourierCoeff (fun x ↦ B x i) m := by
    intro m
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mFourierCoeff_coe_eq_inner, mFourierCoeff_literalCoordL2, mul_assoc]
  constructor
  · intro hB m
    have h := sum_inner_flatTorus3FourierBasis_eq_zero hB m
    rw [key] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  · intro h
    refine mem_literalSolenoidalSubspace_of_sum_inner_eq_zero fun m ↦ ?_
    rw [key, h m, mul_zero]

/-- **S0.**  The Challenge's `L²_σ` is the library's solenoidal subspace of the literal
three-torus, as submodules of the one space `L2 = LiteralC3L2`. -/
theorem L2σ_eq_literalSolenoidalSubspace : L2σ = literalSolenoidalSubspace := by
  ext B
  rw [mem_L2σ_iff, mem_literalSolenoidalSubspace_iff]

/-- `L2σ` is the image of the library's product solenoidal subspace under the transport
`toLiteralC3L2`. -/
theorem L2σ_eq_map_productSolenoidalSubspace :
    L2σ = productSolenoidalSubspace.map (toLiteralC3L2 : ProductC3L2 →ₗ[ℂ] LiteralC3L2) :=
  L2σ_eq_literalSolenoidalSubspace

/-- Membership in the library's literal solenoidal subspace is membership in `L2σ`. -/
theorem mem_literalSolenoidalSubspace_iff_mem_L2σ (B : L2) :
    B ∈ literalSolenoidalSubspace ↔ B ∈ L2σ := by
  rw [L2σ_eq_literalSolenoidalSubspace]

/-- A transported product field lies in `L2σ` exactly when it is solenoidal in the product
model. -/
@[simp] theorem toLiteralC3L2_mem_L2σ_iff (V : ProductC3L2) :
    toLiteralC3L2 V ∈ L2σ ↔ V ∈ productSolenoidalSubspace := by
  rw [L2σ_eq_map_productSolenoidalSubspace]
  constructor
  · rintro ⟨W, hW, hWV⟩
    have : W = V := toLiteralC3L2.injective hWV
    exact this ▸ hW
  · intro hV
    exact ⟨V, hV, rfl⟩

/-- A field of `L2` lies in `L2σ` exactly when its product-model preimage is solenoidal. -/
theorem mem_L2σ_iff_toLiteralC3L2_symm_mem (B : L2) :
    B ∈ L2σ ↔ toLiteralC3L2.symm B ∈ productSolenoidalSubspace := by
  rw [← toLiteralC3L2_mem_L2σ_iff, LinearIsometryEquiv.apply_symm_apply]

/-- `L2σ` is closed in `L2`. -/
theorem isClosed_L2σ : IsClosed (L2σ : Set L2) :=
  Submodule.isClosed_orthogonal _

/-- `L2σ` is a Hilbert space in its own right. -/
instance : CompleteSpace L2σ :=
  isClosed_L2σ.completeSpace_coe

/-! ## The isometric identifications -/

/-- The identity of `L2`, read as an isometric equivalence from the library's literal solenoidal
subspace onto `L2σ`. -/
def literalSolenoidalEquivL2σ : literalSolenoidalSubspace ≃ₗᵢ[ℂ] L2σ :=
  LinearIsometryEquiv.ofEq _ _ L2σ_eq_literalSolenoidalSubspace.symm

/-- `literalSolenoidalEquivL2σ` does not change the underlying field. -/
@[simp] theorem coe_literalSolenoidalEquivL2σ (B : literalSolenoidalSubspace) :
    ((literalSolenoidalEquivL2σ B : L2σ) : L2) = (B : LiteralC3L2) :=
  rfl

/-- The inverse of `literalSolenoidalEquivL2σ` does not change the underlying field. -/
@[simp] theorem coe_literalSolenoidalEquivL2σ_symm (B : L2σ) :
    ((literalSolenoidalEquivL2σ.symm B : literalSolenoidalSubspace) : LiteralC3L2) =
      (B : L2) :=
  rfl

/-- The library's isometric transport of the product solenoidal subspace onto `L2σ`. -/
def productSolenoidalEquivL2σ : productSolenoidalSubspace ≃ₗᵢ[ℂ] L2σ :=
  solenoidalToLiteral.trans literalSolenoidalEquivL2σ

/-- `productSolenoidalEquivL2σ` is the transport `toLiteralC3L2` on the underlying fields. -/
@[simp] theorem coe_productSolenoidalEquivL2σ (V : productSolenoidalSubspace) :
    ((productSolenoidalEquivL2σ V : L2σ) : L2) = toLiteralC3L2 (V : ProductC3L2) :=
  rfl

/-- The inverse of `productSolenoidalEquivL2σ` is `toLiteralC3L2.symm` on the underlying
fields. -/
@[simp] theorem coe_productSolenoidalEquivL2σ_symm (B : L2σ) :
    ((productSolenoidalEquivL2σ.symm B : productSolenoidalSubspace) : ProductC3L2) =
      toLiteralC3L2.symm (B : L2) := by
  apply toLiteralC3L2.injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← coe_productSolenoidalEquivL2σ,
    LinearIsometryEquiv.apply_symm_apply]

/-- `literalSolenoidalEquivL2σ` composed with the library's transport `solenoidalToLiteral` is
`productSolenoidalEquivL2σ`. -/
theorem solenoidalToLiteral_trans_literalSolenoidalEquivL2σ :
    solenoidalToLiteral.trans literalSolenoidalEquivL2σ = productSolenoidalEquivL2σ :=
  rfl

/-! ## Conjugation of operators -/

section Conj

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y]

/-- Conjugation of bounded operators by a surjective linear isometry `e : X ≃ₗᵢ[ℂ] Y`:
`T ↦ e ∘ T ∘ e⁻¹`.  It is itself a linear isometry, so it preserves operator norms. -/
def conjOp (e : X ≃ₗᵢ[ℂ] Y) : (X →L[ℂ] X) ≃ₗᵢ[ℂ] (Y →L[ℂ] Y) where
  toFun T := (e.toContinuousLinearEquiv : X →L[ℂ] Y).comp
    (T.comp (e.symm.toContinuousLinearEquiv : Y →L[ℂ] X))
  invFun T := (e.symm.toContinuousLinearEquiv : Y →L[ℂ] X).comp
    (T.comp (e.toContinuousLinearEquiv : X →L[ℂ] Y))
  map_add' S T := by ext; simp
  map_smul' c T := by ext; simp
  left_inv T := by ext; simp
  right_inv T := by ext; simp
  norm_map' T := by
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_)
      (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
    · simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
      calc ‖T (e.symm y)‖ ≤ ‖T‖ * ‖e.symm y‖ := T.le_opNorm _
        _ = ‖T‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]
    · set U : Y →L[ℂ] Y := (e.toContinuousLinearEquiv : X →L[ℂ] Y).comp
        (T.comp (e.symm.toContinuousLinearEquiv : Y →L[ℂ] X))
      have hx : T x = e.symm (U (e x)) := by simp [U]
      rw [hx, LinearIsometryEquiv.norm_map]
      calc ‖U (e x)‖ ≤ ‖U‖ * ‖e x‖ := U.le_opNorm _
        _ = ‖U‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Evaluation of a conjugated operator. -/
@[simp] theorem conjOp_apply (e : X ≃ₗᵢ[ℂ] Y) (T : X →L[ℂ] X) (y : Y) :
    conjOp e T y = e (T (e.symm y)) :=
  rfl

/-- Evaluation of an operator conjugated back. -/
@[simp] theorem conjOp_symm_apply (e : X ≃ₗᵢ[ℂ] Y) (T : Y →L[ℂ] Y) (x : X) :
    (conjOp e).symm T x = e.symm (T (e x)) :=
  rfl

/-- Conjugation preserves operator norms. -/
theorem norm_conjOp (e : X ≃ₗᵢ[ℂ] Y) (T : X →L[ℂ] X) : ‖conjOp e T‖ = ‖T‖ :=
  (conjOp e).norm_map T

/-- Conjugation maps the identity to the identity. -/
@[simp] theorem conjOp_id (e : X ≃ₗᵢ[ℂ] Y) :
    conjOp e (ContinuousLinearMap.id ℂ X) = ContinuousLinearMap.id ℂ Y := by
  ext; simp

/-- Conjugation is multiplicative. -/
theorem conjOp_comp (e : X ≃ₗᵢ[ℂ] Y) (S T : X →L[ℂ] X) :
    conjOp e (S.comp T) = (conjOp e S).comp (conjOp e T) := by
  ext; simp

/-- The library's transport of a strongly continuous semigroup along an isometry is conjugation
of its operators. -/
theorem StronglyContinuousSemigroup.congr_operator_eq_conjOp
    (S : StronglyContinuousSemigroup X) (e : X ≃ₗᵢ[ℂ] Y) (t : NNReal) :
    (S.congr e).operator t = conjOp e (S.operator t) :=
  rfl

/-- Conjugating back maps the identity to the identity. -/
theorem conjOp_symm_id (e : X ≃ₗᵢ[ℂ] Y) :
    (conjOp e).symm (ContinuousLinearMap.id ℂ Y) = ContinuousLinearMap.id ℂ X := by
  ext; simp

/-- Conjugating back is multiplicative. -/
theorem conjOp_symm_comp (e : X ≃ₗᵢ[ℂ] Y) (S T : Y →L[ℂ] Y) :
    (conjOp e).symm (S.comp T) = ((conjOp e).symm S).comp ((conjOp e).symm T) := by
  ext; simp

end Conj

end

end FastDynamo
