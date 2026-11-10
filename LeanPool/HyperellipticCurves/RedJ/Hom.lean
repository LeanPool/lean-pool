/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.RedJ.Def
public import LeanPool.HyperellipticCurves.RedJ.Stability

/-!
# The reduction map on the Jacobian is a well-defined homomorphism (`thm:redJ-hom`)

We prove that the reduction relation `ChabautyColeman.IsRedJPair` is single-valued
(`ChabautyColeman.isRedJPair_unique`): two split-supported representatives of the same class
are compared over a common finite extension splitting the connecting principal divisors,
where the reductions of the principal parts are principal
(`ChabautyColeman.isPrincipal_redIdealBar_span`, the content of `thm:spec`) and the
reductions of the representatives are unchanged
(`ChabautyColeman.redIdealBar_map_of_splitSupported`). Consequently `ChabautyColeman.redJ`
is a well-defined group homomorphism (`ChabautyColeman.redJ_mul`,
`ChabautyColeman.redJHom`), and it reduces Abel–Jacobi classes of integral points to the
Abel–Jacobi classes of their reductions (`ChabautyColeman.redJ_aj`), sending points that
reduce to `∞_bar` to the identity (`ChabautyColeman.redJ_aj_of_not_isIntegral`).
-/

@[expose] public section

open Polynomial IsLocalRing nonZeroDivisors

namespace ChabautyColeman

/-- Killing a principal factor under `ClassGroup.mk0`. -/
theorem mk0_mul_left_of_isPrincipal {R : Type*} [CommRing R]
    [IsDedekindDomain R] {X Y : Ideal R} (hX : X ∈ (Ideal R)⁰) (hY : Y ∈ (Ideal R)⁰)
    (hXp : X.IsPrincipal) :
    ClassGroup.mk0 ⟨X * Y, mul_mem hX hY⟩ = ClassGroup.mk0 ⟨Y, hY⟩ := by
  rw [← Submonoid.mk_mul_mk _ X Y hX hY, map_mul,
    (ClassGroup.mk0_eq_one_iff hX).mpr hXp, one_mul]

/-- Two ideals whose products with principal ideals agree have the same class. -/
theorem mk0_eq_mk0_of_isPrincipal_mul_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {X₁ X₂ Y₁ Y₂ : Ideal R} (hX₁ : X₁ ∈ (Ideal R)⁰) (hY₁ : Y₁ ∈ (Ideal R)⁰)
    (hX₂ : X₂ ∈ (Ideal R)⁰) (hY₂ : Y₂ ∈ (Ideal R)⁰) (hp₁ : X₁.IsPrincipal)
    (hp₂ : X₂.IsPrincipal) (heq : X₁ * Y₁ = X₂ * Y₂) :
    ClassGroup.mk0 ⟨Y₁, hY₁⟩ = ClassGroup.mk0 ⟨Y₂, hY₂⟩ := by
  rw [← mk0_mul_left_of_isPrincipal hX₁ hY₁ hp₁, ← mk0_mul_left_of_isPrincipal hX₂ hY₂ hp₂]
  congr 1
  exact Subtype.ext heq

section RedJExtend

universe u

variable {O : Type u} [CommRing O] {K : Type u} [Field K] [Algebra O K]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]

/-- The extension of a nonzero ideal of the coordinate ring along an inclusion of
intermediate fields, as an element of the nonzero-divisor monoid. -/
noncomputable def extendNZ (L L' : IntermediateField K (AlgebraicClosure K)) [Algebra L L']
    [IsScalarTower K L L']
    (I : (Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))))⁰) :
    (Ideal (HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L'))))⁰ :=
  ⟨I.1.map (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L')),
    mem_nonZeroDivisors_of_ne_zero
      (map_baseChangeTo_ne_zero _ _ (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩

@[simp] theorem extendNZ_coe (L L' : IntermediateField K (AlgebraicClosure K)) [Algebra L L']
    [IsScalarTower K L L']
    (I : (Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))))⁰) :
    (extendNZ L L' I).1 = I.1.map (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L')) :=
  rfl

theorem extendNZ_ne_zero (L L' : IntermediateField K (AlgebraicClosure K)) [Algebra L L']
    [IsScalarTower K L L']
    (I : (Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))))⁰) :
    (extendNZ L L' I).1 ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp (extendNZ L L' I).2

variable [CharZero K] [Fact (Squarefree (f.map (algebraMap O K)))]

/-- The base-changed class of a represented class is represented by the extended ideal. -/
theorem hypJacMap_eq_mk0_extendNZ {L L' : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra L L'] [IsScalarTower K L L']
    {c : HypJac K (f.map (algebraMap O K))}
    {I : (Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))))⁰}
    (hc : HypJac.map (f.map (algebraMap O K)) c = ClassGroup.mk0 I) :
    HypJac.map (K' := L') (f.map (algebraMap O K)) c
      = ClassGroup.mk0 (extendNZ L L' I) := by
  let : Algebra (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))
      (HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L'))) :=
    (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L')).toAlgebra
  have htf : Module.IsTorsionFree
      (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))
      (HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L'))) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (HypRing.baseChangeTo_injective _ _)
  have htower : IsScalarTower (HypRing K (f.map (algebraMap O K)))
      (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))
      (HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L'))) := by
    refine IsScalarTower.of_algebraMap_eq fun z ↦ ?_
    refine QuadraticAlgebra.ext ?_ ?_
    · change z.re.map (algebraMap K L')
        = (z.re.map (algebraMap K L)).map (algebraMap L L')
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    · change z.im.map (algebraMap K L')
        = (z.im.map (algebraMap K L)).map (algebraMap L L')
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  calc HypJac.map (K' := L') (f.map (algebraMap O K)) c
      = ClassGroup.extendedHom _ _ (HypJac.map (K' := L) (f.map (algebraMap O K)) c) :=
        (ClassGroup.extendedHom_comp_apply _ _ _ c).symm
    _ = ClassGroup.mk0 (ClassGroup.extendedIdeal _ _ I) := by
        rw [hc]
        exact ClassGroup.extendedHom_mk0 _ _ I
    _ = ClassGroup.mk0 (extendNZ L L' I) := by
        congr 1

omit [CharZero K] [Fact (Squarefree (f.map (algebraMap O K)))] in
/-- Extension of ideals along the tower is transitive. -/
theorem extendNZ_map_baseChangeTo (L₁ L₃ L₄ : IntermediateField K (AlgebraicClosure K))
    [Algebra L₁ L₃] [IsScalarTower K L₁ L₃] [Algebra L₃ L₄] [IsScalarTower K L₃ L₄]
    [Algebra L₁ L₄] [IsScalarTower K L₁ L₄] [IsScalarTower L₁ L₃ L₄]
    (I₁ : (Ideal (HypRing L₁ ((f.map (algebraMap O K)).map (algebraMap K L₁))))⁰) :
    (extendNZ (f := f) L₁ L₃ I₁).1.map
        (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L₃ L₄))
      = (extendNZ (f := f) L₁ L₄ I₁).1 := by
  rw [extendNZ_coe, extendNZ_coe, Ideal.map_map]
  congr 1
  refine RingHom.ext fun z ↦ ?_
  refine QuadraticAlgebra.ext ?_ ?_
  · change ((z.re.map (algebraMap L₁ L₃)).map (algebraMap L₃ L₄))
      = z.re.map (algebraMap L₁ L₄)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  · change ((z.im.map (algebraMap L₁ L₃)).map (algebraMap L₃ L₄))
      = z.im.map (algebraMap L₁ L₄)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- The base change to `Lb` of the Abel–Jacobi class of a point is the class of the point ideal
of the base-changed coordinates. -/
theorem hypJacMap_aj_eq_mk0_pointIdeal
    (Lb : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K Lb] (x y : K) :
    HypJac.map (K' := Lb) (f.map (algebraMap O K)) (aj (f.map (algebraMap O K)) x y)
      = ClassGroup.mk0 ⟨pointIdeal ((f.map (algebraMap O K)).map (algebraMap K Lb))
          (algebraMap K Lb x) (algebraMap K Lb y),
          pointIdeal_mem_nonZeroDivisors _ _ _⟩ := by
  rw [aj, HypJac.map_mk0]
  congr 1
  ext : 1
  exact pointIdeal_map (f.map (algebraMap O K)) _ _

end RedJExtend

section BaseChangeSpan

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K] {f : O[X]}

/-- The span of a nonzero base-changed generator is a nonzero ideal (base change is
injective). -/
theorem span_singleton_baseChangeTo_ne_zero
    {L L' : IntermediateField K (AlgebraicClosure K)} [Algebra L L'] [IsScalarTower K L L']
    {z : HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))} (hz : z ≠ 0) :
    Ideal.span {HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L') z}
      ≠ (0 : Ideal (HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L')))) := by
  simp only [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact fun h0 ↦ hz (HypRing.baseChangeTo_injective _ _ (h0.trans (map_zero _).symm))

end BaseChangeSpan

section RedJHom

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- Multiplicativity of the reduced classes over a common extension. -/
theorem mk0_redIdealBar_extendNZ_mul
    (L₁ L₂ L₃ : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [FiniteDimensional K L₃]
    [Algebra L₁ L₃] [IsScalarTower K L₁ L₃] [Algebra L₂ L₃] [IsScalarTower K L₂ L₃]
    (I₁ : (Ideal (HypRing L₁ ((f.map (algebraMap O K)).map (algebraMap K L₁))))⁰)
    (I₂ : (Ideal (HypRing L₂ ((f.map (algebraMap O K)).map (algebraMap K L₂))))⁰)
    (hs₁ : SplitSupported I₁.1) (hs₂ : SplitSupported I₂.1) :
    ClassGroup.mk0 ⟨redIdealBar f L₃
        (extendNZ (f := f) L₁ L₃ I₁ * extendNZ (f := f) L₂ L₃ I₂ :
          (Ideal (HypRing L₃ ((f.map (algebraMap O K)).map (algebraMap K L₃))))⁰).1,
      mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₃ _)⟩
    = ClassGroup.mk0 ⟨redIdealBar f L₁ I₁.1,
        mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₁ _)⟩
      * ClassGroup.mk0 ⟨redIdealBar f L₂ I₂.1,
        mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₂ _)⟩ := by
  have hst₁ : redIdealBar f L₃ (I₁.1.map (HypRing.baseChangeTo _
      (map_map_algebraMap_eq f L₁ L₃))) = redIdealBar f L₁ I₁.1 :=
    redIdealBar_map_of_splitSupported f L₁ L₃
      (mem_nonZeroDivisors_iff_ne_zero.mp I₁.2) hs₁
  have hst₂ : redIdealBar f L₃ (I₂.1.map (HypRing.baseChangeTo _
      (map_map_algebraMap_eq f L₂ L₃))) = redIdealBar f L₂ I₂.1 :=
    redIdealBar_map_of_splitSupported f L₂ L₃
      (mem_nonZeroDivisors_iff_ne_zero.mp I₂.2) hs₂
  have hval : redIdealBar f L₃
      ((extendNZ (f := f) L₁ L₃ I₁).1 * (extendNZ (f := f) L₂ L₃ I₂).1)
      = redIdealBar f L₁ I₁.1 * redIdealBar f L₂ I₂.1 := by
    rw [redIdealBar_mul f L₃ (extendNZ_ne_zero L₁ L₃ I₁) (extendNZ_ne_zero L₂ L₃ I₂)]
    exact congrArg₂ (· * ·) hst₁ hst₂
  exact (congrArg ClassGroup.mk0 (Subtype.ext ((congrArg (redIdealBar f L₃)
      (Submonoid.coe_mul _ _ _)).trans hval))).trans
    (MonoidHom.map_mul ClassGroup.mk0 _ _)

/-- The reductions of the connecting principal factors are principal. -/
theorem isPrincipal_redIdealBar_span_baseChangeTo
    (L₃ L₄ : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L₃]
    [FiniteDimensional K L₄] [Algebra L₃ L₄] [IsScalarTower K L₃ L₄]
    (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {N : Polynomial L₃} (hN0 : N ≠ 0) (hsplitN : (N.map (algebraMap L₃ L₄)).Splits)
    (hsqN : ∀ x : L₄, (N.map (algebraMap L₃ L₄)).eval x = 0 →
      ∃ b : L₄, b ^ 2 = (((f.map (algebraMap O K)).map (algebraMap K L₃)).map
        (algebraMap L₃ L₄)).eval x)
    (z : HypRing L₃ ((f.map (algebraMap O K)).map (algebraMap K L₃))) (hz : z ≠ 0)
    (hzdvd : (z.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * z.im ^ 2) ∣ N) :
    (redIdealBar f L₄
      (Ideal.span {HypRing.baseChangeTo _ (map_map_algebraMap_eq f L₃ L₄) z})).IsPrincipal := by
  set B₃₄ := HypRing.baseChangeTo _ (map_map_algebraMap_eq f L₃ L₄) with hB₃₄def
  have hnorm : (B₃₄ z).re ^ 2
        - (f.map (algebraMap O K)).map (algebraMap K L₄) * (B₃₄ z).im ^ 2
      = (z.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * z.im ^ 2).map
          (algebraMap L₃ L₄) := by
    rw [hB₃₄def, HypRing.re_baseChangeTo, HypRing.im_baseChangeTo, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
      map_map_algebraMap_eq f L₃ L₄]
  have hz4 : B₃₄ z ≠ 0 := (map_ne_zero_iff _ (HypRing.baseChangeTo_injective _ _)).mpr hz
  refine isPrincipal_redIdealBar_span hf hdeg L₄ hz4 ?_ ?_
  · rw [hnorm]
    refine Polynomial.Splits.of_dvd hsplitN ?_ (Polynomial.map_dvd _ hzdvd)
    simpa [Polynomial.map_eq_zero_iff (algebraMap (↥L₃) (↥L₄)).injective] using hN0
  · intro x _ h0
    rw [hnorm] at h0
    have hxN : (N.map (algebraMap L₃ L₄)).eval x = 0 := by
      obtain ⟨w, hw⟩ := hzdvd
      rw [hw, Polynomial.map_mul, eval_mul, h0, zero_mul]
    obtain ⟨b, hb⟩ := hsqN x hxN
    exact ⟨b, by rwa [map_map_algebraMap_eq f L₃ L₄] at hb⟩

/-- The core comparison for well-definedness: two split-supported representatives whose
extensions to `L₄` differ by principal factors with principal reductions have the same
reduced class. -/
theorem mk0_redIdealBar_eq_of_span_mul_extendNZ
    (L₁ L₂ L₄ : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [FiniteDimensional K L₄]
    [Algebra L₁ L₄] [IsScalarTower K L₁ L₄] [Algebra L₂ L₄] [IsScalarTower K L₂ L₄]
    (I₁ : (Ideal (HypRing L₁ ((f.map (algebraMap O K)).map (algebraMap K L₁))))⁰)
    (I₂ : (Ideal (HypRing L₂ ((f.map (algebraMap O K)).map (algebraMap K L₂))))⁰)
    (hs₁ : SplitSupported I₁.1) (hs₂ : SplitSupported I₂.1)
    {X₁ X₂ : Ideal (HypRing L₄ ((f.map (algebraMap O K)).map (algebraMap K L₄)))}
    (hX₁ : X₁ ≠ 0) (hX₂ : X₂ ≠ 0)
    (hp₁ : (redIdealBar f L₄ X₁).IsPrincipal) (hp₂ : (redIdealBar f L₄ X₂).IsPrincipal)
    (hspan : X₁ * (extendNZ (f := f) L₁ L₄ I₁).1 = X₂ * (extendNZ (f := f) L₂ L₄ I₂).1) :
    ClassGroup.mk0 ⟨redIdealBar f L₁ I₁.1,
        mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₁ _)⟩
      = ClassGroup.mk0 ⟨redIdealBar f L₂ I₂.1,
        mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₂ _)⟩ := by
  have hext₁0 := extendNZ_ne_zero (f := f) L₁ L₄ I₁
  have hext₂0 := extendNZ_ne_zero (f := f) L₂ L₄ I₂
  have hmul₁ : redIdealBar f L₄ (X₁ * (extendNZ (f := f) L₁ L₄ I₁).1)
      = redIdealBar f L₄ X₁ * redIdealBar f L₄ (extendNZ (f := f) L₁ L₄ I₁).1 :=
    redIdealBar_mul f L₄ hX₁ hext₁0
  have hmul₂ : redIdealBar f L₄ (X₂ * (extendNZ (f := f) L₂ L₄ I₂).1)
      = redIdealBar f L₄ X₂ * redIdealBar f L₄ (extendNZ (f := f) L₂ L₄ I₂).1 :=
    redIdealBar_mul f L₄ hX₂ hext₂0
  have hred' : redIdealBar f L₄ X₁ * redIdealBar f L₄ (extendNZ (f := f) L₁ L₄ I₁).1
      = redIdealBar f L₄ X₂ * redIdealBar f L₄ (extendNZ (f := f) L₂ L₄ I₂).1 :=
    hmul₁.symm.trans ((congrArg (redIdealBar f L₄) hspan).trans hmul₂)
  have hmk := mk0_eq_mk0_of_isPrincipal_mul_eq
    (mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₄ _))
    (mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₄ _))
    (mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₄ _))
    (mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L₄ _)) hp₁ hp₂ hred'
  have hstab₁ : redIdealBar f L₄ (extendNZ (f := f) L₁ L₄ I₁).1 = redIdealBar f L₁ I₁.1 :=
    redIdealBar_map_of_splitSupported f L₁ L₄
      (mem_nonZeroDivisors_iff_ne_zero.mp I₁.2) hs₁
  have hstab₂ : redIdealBar f L₄ (extendNZ (f := f) L₂ L₄ I₂).1 = redIdealBar f L₂ I₂.1 :=
    redIdealBar_map_of_splitSupported f L₂ L₄
      (mem_nonZeroDivisors_iff_ne_zero.mp I₂.2) hs₂
  exact (congrArg ClassGroup.mk0 (Subtype.ext hstab₁.symm)).trans
    (hmk.trans (congrArg ClassGroup.mk0 (Subtype.ext hstab₂)))

/-- **Well-definedness of the reduction** (`thm:redJ-hom`): the reduction relation is
single-valued — any two split-supported representatives of the same class have the same
reduced class. -/
theorem isRedJPair_unique (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {c : HypJac K (f.map (algebraMap O K))}
    {r₁ r₂ : HypJac (ResidueField O) (f.map (residue O))}
    (h₁ : IsRedJPair c r₁) (h₂ : IsRedJPair c r₂) : r₁ = r₂ := by
  classical
  obtain ⟨L₁, hL₁, I₁, hs₁, hc₁, rfl⟩ := h₁
  obtain ⟨L₂, hL₂, I₂, hs₂, hc₂, rfl⟩ := h₂
  -- pass to the compositum L₃ and a splitting extension L₄
  set L₃ := L₁ ⊔ L₂
  let : Algebra L₁ L₃ :=
    (IntermediateField.inclusion (le_sup_left : L₁ ≤ L₃)).toRingHom.toAlgebra
  have : IsScalarTower K L₁ L₃ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_sup_left : L₁ ≤ L₃))
  let : Algebra L₂ L₃ :=
    (IntermediateField.inclusion (le_sup_right : L₂ ≤ L₃)).toRingHom.toAlgebra
  have : IsScalarTower K L₂ L₃ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_sup_right : L₂ ≤ L₃))
  have hc₁' := hypJacMap_eq_mk0_extendNZ (L' := L₃) hc₁
  have hc₂' := hypJacMap_eq_mk0_extendNZ (L' := L₃) hc₂
  obtain ⟨h, k, hh0, hk0, hspan⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hc₁'.symm.trans hc₂')
  have hN0 : (h.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * h.im ^ 2)
      * (k.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * k.im ^ 2) ≠ 0 :=
    mul_ne_zero
      (sq_sub_mul_sq_ne_zero (Fact.out : Odd ((f.map (algebraMap O K)).map
        (algebraMap K L₃)).natDegree) (QuadraticAlgebra.not_re_eq_zero_and_im_eq_zero hh0))
      (sq_sub_mul_sq_ne_zero (Fact.out : Odd ((f.map (algebraMap O K)).map
        (algebraMap K L₃)).natDegree) (QuadraticAlgebra.not_re_eq_zero_and_im_eq_zero hk0))
  obtain ⟨L₄, hle₃₄, hfin₄, hsplitN, hsqN⟩ := exists_intermediateField_splits
    ((h.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * h.im ^ 2)
      * (k.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L₃) * k.im ^ 2))
    ((f.map (algebraMap O K)).map (algebraMap K L₃)) hN0
  let : Algebra L₃ L₄ := (IntermediateField.inclusion hle₃₄).toRingHom.toAlgebra
  have : IsScalarTower K L₃ L₄ := IsScalarTower.of_algHom (IntermediateField.inclusion hle₃₄)
  let : Algebra L₁ L₄ :=
    (IntermediateField.inclusion ((le_sup_left : L₁ ≤ L₃).trans hle₃₄)).toRingHom.toAlgebra
  have : IsScalarTower K L₁ L₄ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion ((le_sup_left : L₁ ≤ L₃).trans hle₃₄))
  let : Algebra L₂ L₄ :=
    (IntermediateField.inclusion ((le_sup_right : L₂ ≤ L₃).trans hle₃₄)).toRingHom.toAlgebra
  have : IsScalarTower K L₂ L₄ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion ((le_sup_right : L₂ ≤ L₃).trans hle₃₄))
  have : IsScalarTower L₁ L₃ L₄ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower L₂ L₃ L₄ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- extend the connecting equation to L₄
  have hspan₄ := congrArg
    (Ideal.map (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L₃ L₄))) hspan
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton, Ideal.map_span,
    Set.image_singleton, extendNZ_map_baseChangeTo L₁ L₃ L₄ I₁,
    extendNZ_map_baseChangeTo L₂ L₃ L₄ I₂] at hspan₄
  -- the principal parts have principal reductions
  have hkh := isPrincipal_redIdealBar_span_baseChangeTo L₃ L₄ hf hdeg hN0 hsplitN hsqN h
    hh0 (dvd_mul_right _ _)
  have hkk := isPrincipal_redIdealBar_span_baseChangeTo L₃ L₄ hf hdeg hN0 hsplitN hsqN k
    hk0 (dvd_mul_left _ _)
  have hspan_h := span_singleton_baseChangeTo_ne_zero (L' := L₄) hh0
  have hspan_k := span_singleton_baseChangeTo_ne_zero (L' := L₄) hk0
  exact mk0_redIdealBar_eq_of_span_mul_extendNZ L₁ L₂ L₄ I₁ I₂ hs₁ hs₂ hspan_h hspan_k
    hkh hkk hspan₄

/-- The reduction map returns the second member of a reduction pair: `IsRedJPair` is a graph
description of `redJ`. -/
theorem IsRedJPair.redJ_eq (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {c : HypJac K (f.map (algebraMap O K))}
    {r : HypJac (ResidueField O) (f.map (residue O))} (h : IsRedJPair c r) : redJ c = r :=
  isRedJPair_unique hf hdeg (isRedJPair_redJ c) h

/-- **The reduction is multiplicative** (`thm:redJ-hom`). -/
theorem redJ_mul (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (c₁ c₂ : HypJac K (f.map (algebraMap O K))) :
    redJ (c₁ * c₂) = redJ c₁ * redJ c₂ := by
  classical
  obtain ⟨L₁, hL₁, I₁, hs₁, hc₁, hr₁⟩ := isRedJPair_redJ c₁
  obtain ⟨L₂, hL₂, I₂, hs₂, hc₂, hr₂⟩ := isRedJPair_redJ c₂
  set L₃ := L₁ ⊔ L₂
  let : Algebra L₁ L₃ :=
    (IntermediateField.inclusion (le_sup_left : L₁ ≤ L₃)).toRingHom.toAlgebra
  have ht₁ : IsScalarTower K L₁ L₃ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_sup_left : L₁ ≤ L₃))
  let : Algebra L₂ L₃ :=
    (IntermediateField.inclusion (le_sup_right : L₂ ≤ L₃)).toRingHom.toAlgebra
  have ht₂ : IsScalarTower K L₂ L₃ :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_sup_right : L₂ ≤ L₃))
  have hfd₁ : FiniteDimensional L₁ L₃ := Module.Finite.right K L₁ L₃
  have hfd₂ : FiniteDimensional L₂ L₃ := Module.Finite.right K L₂ L₃
  have hs₁' : SplitSupported (extendNZ (f := f) L₁ L₃ I₁).1 :=
    hs₁.map_baseChangeTo _
  have hs₂' : SplitSupported (extendNZ (f := f) L₂ L₃ I₂).1 :=
    hs₂.map_baseChangeTo _
  refine (IsRedJPair.redJ_eq hf hdeg ⟨L₃, inferInstance,
    extendNZ L₁ L₃ I₁ * extendNZ L₂ L₃ I₂, ?_, ?_, ?_⟩)
  · exact hs₁'.mul hs₂'
  · rw [map_mul, hypJacMap_eq_mk0_extendNZ (L' := L₃) hc₁,
      hypJacMap_eq_mk0_extendNZ (L' := L₃) hc₂, ← MonoidHom.map_mul ClassGroup.mk0]
  · rw [hr₁, hr₂]
    exact (mk0_redIdealBar_extendNZ_mul L₁ L₂ L₃ I₁ I₂ hs₁ hs₂).symm

/-- **The reduction homomorphism on the Jacobian** (`def:redJ`, `thm:redJ-hom`). -/
noncomputable def redJHom (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    HypJac K (f.map (algebraMap O K)) →* HypJac (ResidueField O) (f.map (residue O)) :=
  MonoidHom.mk' redJ (redJ_mul hf hdeg)

/-- **Reduction is compatible with Abel–Jacobi** (`thm:redJ-hom`): the reduction of the
class of an integral point is the class of the reduced point. -/
theorem redJ_aj (hf : f.Monic) (hdeg : 0 < f.natDegree) {a b : O}
    (hab : algebraMap O K b ^ 2 = (f.map (algebraMap O K)).eval (algebraMap O K a)) :
    redJ (aj (f.map (algebraMap O K)) (algebraMap O K a) (algebraMap O K b))
      = aj (f.map (residue O)) (residue O a) (residue O b) := by
  set Lb : IntermediateField K (AlgebraicClosure K) := ⊥
  set x : Lb := algebraMap K Lb (algebraMap O K a) with hx
  set y : Lb := algebraMap K Lb (algebraMap O K b) with hy
  have hxy : y ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K Lb)).eval x := by
    rw [hx, hy, ← map_pow, hab, eval_map_apply]
    conv_rhs => rw [eval_map_apply, eval_map_apply]
  have hxint : IsIntegral O x := by
    rw [hx, ← IsScalarTower.algebraMap_apply O K Lb]
    exact isIntegral_algebraMap
  refine IsRedJPair.redJ_eq hf hdeg ⟨Lb, inferInstance,
    ⟨pointIdeal ((f.map (algebraMap O K)).map (algebraMap K Lb)) x y,
      pointIdeal_mem_nonZeroDivisors _ x y⟩,
    splitSupported_pointIdeal hxy, ?_, ?_⟩
  · exact hypJacMap_aj_eq_mk0_pointIdeal Lb (algebraMap O K a) (algebraMap O K b)
  · rw [aj]
    congr 1
    refine Subtype.ext ?_
    change pointIdeal (f.map (residue O)) (residue O a) (residue O b)
      = redIdealBar f Lb (pointIdeal ((f.map (algebraMap O K)).map (algebraMap K Lb)) x y)
    rw [redIdealBar_pointIdeal f Lb hxy hxint]
    have hxred : redres O Lb x = residue O a := by
      rw [hx, ← IsScalarTower.algebraMap_apply O K Lb, redres_algebraMap]
    have hyred : redres O Lb y = residue O b := by
      rw [hy, ← IsScalarTower.algebraMap_apply O K Lb, redres_algebraMap]
    rw [hxred, hyred]

/-- A point reducing to `∞_bar` has trivial reduced class. -/
theorem redJ_aj_of_not_isIntegral (hf : f.Monic) (hdeg : 0 < f.natDegree) {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x) (hx : ¬IsIntegral O x) :
    redJ (aj (f.map (algebraMap O K)) x y) = 1 := by
  set Lb : IntermediateField K (AlgebraicClosure K) := ⊥
  set x' : Lb := algebraMap K Lb x with hx'
  set y' : Lb := algebraMap K Lb y with hy'
  have hxy' : y' ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K Lb)).eval x' := by
    rw [hx', hy', ← map_pow, hxy]
    conv_rhs => rw [eval_map_apply]
  have hxint : ¬IsIntegral O x' := fun hc ↦
    hx ((isIntegral_algHom_iff (IsScalarTower.toAlgHom O K Lb)
      (algebraMap K Lb).injective).mp hc)
  refine IsRedJPair.redJ_eq hf hdeg ⟨Lb, inferInstance,
    ⟨pointIdeal ((f.map (algebraMap O K)).map (algebraMap K Lb)) x' y',
      pointIdeal_mem_nonZeroDivisors _ x' y'⟩,
    splitSupported_pointIdeal hxy', ?_, ?_⟩
  · exact hypJacMap_aj_eq_mk0_pointIdeal Lb x y
  · refine ((ClassGroup.mk0_eq_one_iff _).mpr ?_).symm
    change (redIdealBar f Lb (pointIdeal ((f.map (algebraMap O K)).map
      (algebraMap K Lb)) x' y')).IsPrincipal
    rw [redIdealBar_pointIdeal_of_not_isIntegral f Lb hxy' hxint]
    exact ⟨1, (Ideal.span_singleton_one).symm⟩

end RedJHom

end ChabautyColeman

end
