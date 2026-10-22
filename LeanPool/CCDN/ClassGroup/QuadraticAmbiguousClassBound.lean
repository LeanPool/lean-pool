/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.QuadraticInvolution
public import LeanPool.CCDN.ClassGroup.QuadraticObstructionFibers
import LeanPool.CCDN.ClassGroup.AmbiguousIdealRelativeNorm
import LeanPool.CCDN.ClassGroup.FractionalIdealConjugation
import LeanPool.CCDN.ClassGroup.QuadraticNormConjugation

/-! A cardinal bound for fixed two-torsion classes in terms of
strongly ambiguous classes and the unit-norm quotient. This is
the obstruction-fiber part of genus theory; the ramified-ideal estimate
for the strongly ambiguous subgroup is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField nonZeroDivisors

private theorem card_le_subgroup_mul_obstruction
    {G Q : Type*} [CommGroup G] [Finite G] [Finite Q]
    (S : Subgroup G) (o : G → Q)
    (ho : ∀ x y, o x = o y → x / y ∈ S) :
    Nat.card G ≤ Nat.card S * Nat.card Q := by
  let r : G ⧸ S → G := fun x => Classical.choose (QuotientGroup.mk_surjective x)
  have hr : ∀ x : G ⧸ S, QuotientGroup.mk (r x) = x :=
    fun x => Classical.choose_spec (QuotientGroup.mk_surjective x)
  have hinj : Function.Injective (fun x : G ⧸ S => o (r x)) := by
    intro x y h
    rw [← hr x, ← hr y]
    apply div_eq_one.mp
    rw [← QuotientGroup.mk_div]
    exact (QuotientGroup.eq_one_iff _).mpr (ho _ _ h)
  have hc := Nat.card_le_card_of_injective _ hinj
  calc
    Nat.card G = Nat.card S * S.index := S.card_mul_index.symm
    _ ≤ Nat.card S * Nat.card Q := Nat.mul_le_mul_left _ hc

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K]

/-- Witness data for an ambiguous ideal class `c` (one fixed by `σ`): an invertible fractional
ideal representing `c`, a scalar comparing it with its conjugate, and a base unit equal to the
relative norm of that scalar. -/
structure AmbiguousClassWitness (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) where
  /-- An invertible fractional ideal representing the class. -/
  ideal : (FractionalIdeal (𝓞 K)⁰ K)ˣ
  /-- The scalar comparing the conjugate of `ideal` with `ideal`. -/
  scalar : Kˣ
  /-- A unit of `𝓞 F` equal to the relative norm of `scalar`. -/
  baseUnit : (𝓞 F)ˣ
  /-- The fractional ideal `ideal` represents the class `c`. -/
  class_eq : ClassGroup.mk K ideal = c
  /-- The conjugate of `ideal` under `σ` is the principal ideal of `scalar` times `ideal`. -/
  scalar_eq : fractionalIdealUnitAction (K := K)
    (RingOfIntegers.mapAlgEquiv σ).toRingEquiv ideal =
      toPrincipalIdeal (𝓞 K) K scalar * ideal
  /-- The relative norm of `scalar` is the base unit `baseUnit`. -/
  norm_eq : Algebra.norm F (scalar : K) = ((baseUnit : 𝓞 F) : F)

private theorem nonempty_ambiguousClassWitness (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K))
    (hc : ClassGroup.mulEquiv (RingOfIntegers.mapAlgEquiv σ).toRingEquiv c = c) :
    Nonempty (AmbiguousClassWitness F K σ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨x, y, u, hx, hy, hxy, hu⟩ :=
    ambiguous_numberField_ideal_norm_unit F K σ I hc
  let a : Kˣ := Units.mk0 (x : K) (RingOfIntegers.coe_ne_zero_iff.mpr hx)
  let b : Kˣ := Units.mk0 (y : K) (RingOfIntegers.coe_ne_zero_iff.mpr hy)
  refine ⟨⟨FractionalIdeal.mk0 K I, b / a, u,
    ClassGroup.mk_mk0 K I, ?_, ?_⟩⟩
  · exact integral_ideal_scalar_fractional_comparison
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I x y hx hy hxy
  · simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    change Algebra.norm F ((y : K) * (x : K)⁻¹) = ((u : 𝓞 F) : F)
    simpa only [div_eq_mul_inv] using hu

private def chosenAmbiguousClassWitness (σ : K ≃ₐ[F] K)
    (c : fixedClassGroupTwoTorsion K σ.toRingEquiv) :
    AmbiguousClassWitness F K σ c.val.val :=
  Classical.choice (nonempty_ambiguousClassWitness F K σ c.val.val
    ((mem_fixedClassGroupTwoTorsion K σ.toRingEquiv c.val).mp c.property))

/-- A fixed choice of the unit-norm obstruction on fixed
two-torsion classes. The cardinal argument only uses equality of values. -/
private def fixedClassUnitObstruction (σ : K ≃ₐ[F] K) :
    fixedClassGroupTwoTorsion K σ.toRingEquiv → quadraticUnitNormQuotient F K :=
  fun c => QuotientGroup.mk (chosenAmbiguousClassWitness F K σ c).baseUnit

private theorem fixedClassUnitObstruction_eq_implies
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (c e : fixedClassGroupTwoTorsion K σ.toRingEquiv)
    (hce : fixedClassUnitObstruction F K σ c = fixedClassUnitObstruction F K σ e) :
    c.val.val / e.val.val ∈ stronglyAmbiguousClassGroup F K σ := by
  let w := chosenAmbiguousClassWitness F K σ c
  let z := chosenAmbiguousClassWitness F K σ e
  rw [← w.class_eq, ← z.class_eq]
  exact equal_unit_obstructions_stronglyAmbiguous F K hd σ hσ
    w.ideal z.ideal w.scalar z.scalar w.baseUnit z.baseUnit
    w.scalar_eq z.scalar_eq w.norm_eq z.norm_eq hce

/-- The two-torsion subgroup of the strongly ambiguous subgroup. -/
abbrev stronglyAmbiguousTwoTorsion (σ : K ≃ₐ[F] K) :=
  (powMonoidHom 2 : stronglyAmbiguousClassGroup F K σ →*
    stronglyAmbiguousClassGroup F K σ).ker

private theorem fixedClassGroupTwoTorsion_card_le
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    Nat.card (fixedClassGroupTwoTorsion K σ.toRingEquiv) ≤
      Nat.card (stronglyAmbiguousTwoTorsion F K σ) *
        Nat.card (quadraticUnitNormQuotient F K) := by
  let emb : fixedClassGroupTwoTorsion K σ.toRingEquiv →* ClassGroup (𝓞 K) :=
    (classGroupTwoTorsion K).subtype.comp (fixedClassGroupTwoTorsion K σ.toRingEquiv).subtype
  let S := (stronglyAmbiguousClassGroup F K σ).comap emb
  let := quadraticUnitNormQuotient_finite F K hd
  have hc := card_le_subgroup_mul_obstruction S (fixedClassUnitObstruction F K σ)
    (fun c e h => fixedClassUnitObstruction_eq_implies F K hd σ hσ c e h)
  let incl : S → stronglyAmbiguousTwoTorsion F K σ := fun c =>
    ⟨⟨c.val.val.val, c.property⟩, by
      apply Subtype.ext
      exact c.val.val.property⟩
  have hincl : Function.Injective incl := by
    intro c e h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : stronglyAmbiguousTwoTorsion F K σ => x.val.val) h
  exact hc.trans (Nat.mul_le_mul_right _
    (Nat.card_le_card_of_injective incl hincl))

/-- The unit contribution to quadratic genus theory is bounded by the
degree of the base field, with the strongly ambiguous term left explicit. -/
private theorem fixedClassGroupTwoTorsion_card_le_degree
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    Nat.card (fixedClassGroupTwoTorsion K σ.toRingEquiv) ≤
      Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F :=
  (fixedClassGroupTwoTorsion_card_le F K hd σ hσ).trans
    (Nat.mul_le_mul_left _ (quadraticUnitNormQuotient_card_le_degree F K hd))

/-- The quadratic two-torsion count is reduced to the strongly
ambiguous subgroup, with a proved degree-only unit factor. -/
theorem classGroupTwoTorsionCard_le_stronglyAmbiguous
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    classGroupTwoTorsionCard K ≤
      (Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F) ^ 2 := by
  exact (classGroupTwoTorsionCard_le_fixed_square K σ.toRingEquiv
    (quadratic_automorphism_involutive F K hd σ)).trans
      (Nat.pow_le_pow_left (fixedClassGroupTwoTorsion_card_le_degree F K hd σ hσ) 2)

end
end CCDN
