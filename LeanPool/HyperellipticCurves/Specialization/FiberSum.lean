/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.Charts
public import LeanPool.HyperellipticCurves.Specialization.Pointwise

import LeanPool.HyperellipticCurves.ForMathlib.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Fiber counts: total multiplicity of an ideal over a residue disk

For an ideal `I` of the coordinate ring `A_K` of `y² = f(x)` over the fraction field of a
DVR `O`, and a point `P_bar` of the residue curve, `ChabautyColeman.fiberCount f I P_bar` is the
total intrinsic multiplicity `∑_{red P = P_bar} emult(m_P, I)` of `I` at the points of the
residue disk of `P_bar`.

The main result (`ChabautyColeman.fiberCount_span`) is `thm:spec` in this bookkeeping-free
form: for a coordinate-ring element with coprime primitive split data, the fiber count of
the principal ideal at *every* affine residue point equals the intrinsic multiplicity of the
reduced function there — obtained from the per-disk point sums by reindexing along the disk
parametrizations `ChabautyColeman.diskParamGeneric` / `diskParamWeierstrass`.

We also record the formal properties feeding the reduction map on the Jacobian
(`def:redJ`): additivity in `I` (`ChabautyColeman.fiberCount_mul`), finite support, and the
values on point ideals (`ChabautyColeman.fiberCount_pointIdeal_of_redPoint_eq` / `_ne`) and
on the unit ideal.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- The total intrinsic multiplicity of the ideal `I` at the points of the residue disk of
`P_bar`: the number of zeros of `I` reducing to `P_bar`, counted with multiplicity. (Meaningful for
affine `P_bar`, whose disk consists of integral affine points.) -/
noncomputable def fiberCount (f : O[X]) (I : Ideal (HypRing K (f.map (algebraMap O K))))
    (Pb : CurvePoint (ResidueField O) (f.map (residue O))) : ℕ :=
  ∑ᶠ P : ResidueDisk (K := K) Pb,
    (emultiplicity (pointIdeal (f.map (algebraMap O K)) P.1.xCoord P.1.yCoord) I).toNat

/-- A point of the residue disk of an affine residue point is an integral affine point with
the corresponding coordinate reductions. -/
theorem exists_eq_affine_of_redPoint_eq_affine {f : O[X]} {ab bb : ResidueField O}
    {hb : bb ^ 2 = (f.map (residue O)).eval ab} {P : CurvePoint K (f.map (algebraMap O K))}
    (hP : redPoint P = .affine ab bb hb) :
    ∃ (x y : K) (h : y ^ 2 = (f.map (algebraMap O K)).eval x),
      P = .affine x y h ∧ 𝓋 x ≤ 1 ∧ 𝓋 y ≤ 1 ∧ redK x = ab ∧ redK y = bb := by
  cases P with
  | infinity => rw [redPoint_infinity] at hP; exact absurd hP (by simp)
  | affine x y h =>
    by_cases hx : 𝓋 x ≤ 1
    · by_cases hy : 𝓋 y ≤ 1
      · rw [redPoint_affine h hx hy] at hP
        simp only [CurvePoint.affine.injEq] at hP
        exact ⟨x, y, h, rfl, hx, hy, hP.1, hP.2⟩
      · rw [redPoint_eq_infinity_of_not_le h hx hy] at hP
        exact absurd hP (by simp)
    · rw [redPoint_eq_infinity_of_lt h (not_le.mp hx)] at hP
      exact absurd hP (by simp)

variable {f : O[X]} [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]

/-- The summands of a fiber count of a nonzero ideal have finite support (each nonzero term
singles out a prime divisor of `I`, and the point ideal determines the point). -/
theorem finite_support_fiberCount {ab bb : ResidueField O}
    (hb : bb ^ 2 = (f.map (residue O)).eval ab)
    {I : Ideal (HypRing K (f.map (algebraMap O K)))} (hI : I ≠ 0) :
    (Function.support fun P : ResidueDisk (K := K) (CurvePoint.affine ab bb hb) ↦
      (emultiplicity (pointIdeal (f.map (algebraMap O K)) P.1.xCoord P.1.yCoord)
        I).toNat).Finite := by
  refine Set.Finite.of_finite_image (f := fun P : ResidueDisk (K := K)
      (CurvePoint.affine ab bb hb) ↦
    pointIdeal (f.map (algebraMap O K)) P.1.xCoord P.1.yCoord) ?_ ?_
  · refine Set.Finite.subset (Set.Finite.image IsDedekindDomain.HeightOneSpectrum.asIdeal
      (Ideal.finite_factors hI)) ?_
    rintro J ⟨⟨P₀, hP₀⟩, hPmem, rfl⟩
    obtain ⟨x, y, h, rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
    simp only [Function.mem_support, CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
      at hPmem
    have hdvd : pointIdeal (f.map (algebraMap O K)) x y ∣ I := by
      by_contra hnd
      exact hPmem (by rw [emultiplicity_eq_zero.mpr hnd]; rfl)
    exact ⟨pointSpectrum h, hdvd, rfl⟩
  · rintro ⟨P₀, hP₀⟩ - ⟨Q₀, hQ₀⟩ - hPQ
    obtain ⟨x, y, h, rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
    obtain ⟨x', y', h', rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hQ₀
    simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine] at hPQ
    obtain ⟨rfl, rfl⟩ := (pointIdeal_eq_pointIdeal_iff h).mp hPQ
    rfl

/-- Fiber counts are additive in the ideal. -/
theorem fiberCount_mul {ab bb : ResidueField O} (hb : bb ^ 2 = (f.map (residue O)).eval ab)
    {I J : Ideal (HypRing K (f.map (algebraMap O K)))} (hI : I ≠ 0) (hJ : J ≠ 0) :
    fiberCount f (I * J) (.affine ab bb hb)
      = fiberCount f I (.affine ab bb hb) + fiberCount f J (.affine ab bb hb) := by
  rw [fiberCount, fiberCount, fiberCount,
    ← finsum_add_distrib (finite_support_fiberCount hb hI) (finite_support_fiberCount hb hJ)]
  refine finsum_congr fun P ↦ ?_
  obtain ⟨P₀, hP₀⟩ := P
  obtain ⟨x, y, h, rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
  simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
  have hprime : Prime (pointIdeal (f.map (algebraMap O K)) x y) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot _ x y) (pointIdeal_isPrime h)
  rw [emultiplicity_mul hprime, ENat.toNat_add
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp
      (FiniteMultiplicity.of_prime_left hprime hI))
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp
      (FiniteMultiplicity.of_prime_left hprime hJ))]

/-- The fiber count of the maximal ideal of an integral point at its own reduction is `1`. -/
theorem fiberCount_pointIdeal_of_redPoint_eq {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x) {ab bb : ResidueField O}
    {hb : bb ^ 2 = (f.map (residue O)).eval ab}
    (hred : redPoint (.affine x y hxy) = .affine ab bb hb) :
    fiberCount f (pointIdeal (f.map (algebraMap O K)) x y) (.affine ab bb hb) = 1 := by
  rw [fiberCount]
  rw [finsum_eq_single _ (⟨.affine x y hxy, hred⟩ :
    ResidueDisk (K := K) (CurvePoint.affine ab bb hb)) ?_]
  · simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
    rw [Ideal.emultiplicity_self_of_ne_top (pointIdeal_isMaximal hxy).ne_top
      (pointIdeal_ne_bot _ x y)]
    rfl
  · rintro ⟨Q₀, hQ₀⟩ hne
    obtain ⟨x', y', h', rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hQ₀
    simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
    have hne' : pointIdeal (f.map (algebraMap O K)) x y
        ≠ pointIdeal (f.map (algebraMap O K)) x' y' := by
      intro heq
      obtain ⟨rfl, rfl⟩ := (pointIdeal_eq_pointIdeal_iff hxy).mp heq
      exact hne rfl
    rw [Ideal.emultiplicity_eq_zero_of_isMaximal_of_ne (pointIdeal_isMaximal h')
      (pointIdeal_isMaximal hxy) hne']
    rfl

/-- The fiber count of the maximal ideal of an integral point vanishes at every other
residue point. -/
theorem fiberCount_pointIdeal_of_redPoint_ne {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x) {ab bb : ResidueField O}
    {hb : bb ^ 2 = (f.map (residue O)).eval ab}
    (hred : redPoint (.affine x y hxy) ≠ .affine ab bb hb) :
    fiberCount f (pointIdeal (f.map (algebraMap O K)) x y) (.affine ab bb hb) = 0 := by
  rw [fiberCount]
  refine finsum_eq_zero_of_forall_eq_zero fun P ↦ ?_
  obtain ⟨P₀, hP₀⟩ := P
  obtain ⟨x', y', h', rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
  simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
  by_cases heq : pointIdeal (f.map (algebraMap O K)) x' y'
      = pointIdeal (f.map (algebraMap O K)) x y
  · obtain ⟨rfl, rfl⟩ := (pointIdeal_eq_pointIdeal_iff h').mp heq
    exact absurd hP₀ hred
  · rw [Ideal.emultiplicity_eq_zero_of_isMaximal_of_ne (pointIdeal_isMaximal h')
      (pointIdeal_isMaximal hxy) fun h ↦ heq h.symm]
    rfl

/-- The fiber count of the unit ideal vanishes. -/
theorem fiberCount_top {ab bb : ResidueField O}
    (hb : bb ^ 2 = (f.map (residue O)).eval ab) :
    fiberCount f (⊤ : Ideal (HypRing K (f.map (algebraMap O K)))) (.affine ab bb hb)
      = 0 := by
  rw [fiberCount]
  refine finsum_eq_zero_of_forall_eq_zero fun P ↦ ?_
  obtain ⟨P₀, hP₀⟩ := P
  obtain ⟨x, y, h, rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
  simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
  rw [← Ideal.one_eq_top,
    emultiplicity_eq_zero.mpr
      (Ideal.prime_of_isPrime (pointIdeal_ne_bot _ x y) (pointIdeal_isPrime h)).not_dvd_one,
    ENat.toNat_zero]

/-- The fiber count of `(x - a)` vanishes everywhere when `a` is not integral (the points of
an affine residue disk have integral coordinates). -/
theorem fiberCount_span_X_sub_C_of_not_isIntegral {a : K} (ha : ¬IsIntegral O a)
    {ab bb : ResidueField O} (hb : bb ^ 2 = (f.map (residue O)).eval ab) :
    fiberCount f
      (Ideal.span {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (X - C a)})
      (.affine ab bb hb) = 0 := by
  rw [fiberCount]
  refine finsum_eq_zero_of_forall_eq_zero fun P ↦ ?_
  obtain ⟨P₀, hP₀⟩ := P
  obtain ⟨x, y, h, rfl, hx, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
  simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
  rw [emultiplicity_pointIdeal_eq_zero h ?_]
  · rfl
  · simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    refine ha ?_
    rw [← ht]
    exact isIntegral_algebraMap

end Count

/-! ### `thm:spec` as a fiber count -/

section Engine

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {f P Q : O[X]}
  [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
  [Fact (Squarefree (f.map (residue O)))]

/-- **`thm:spec` as a fiber count, Weierstrass residue point**. -/
theorem fiberCount_span_of_eq_zero [PerfectField (ResidueField O)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hsq : ∀ (ω : O), f.eval ω = 0 → ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits)
    {ab : ResidueField O} (hroot : (f.map (residue O)).eval ab = 0) :
    fiberCount f (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
        HypRing K (f.map (algebraMap O K)))})
      (.affine ab 0 (by rw [zero_pow two_ne_zero, hroot]))
      = (emultiplicity (pointIdeal (f.map (residue O)) ab 0)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  obtain ⟨ω, hωeval, hu, hωres, hsum⟩ :=
    exists_center_finsum_emultiplicity_weierstrass (K := K) hf hdeg h2 hN hsq hsplit hroot
  subst hωres
  refine .trans ?_ hsum
  rw [fiberCount, ← finsum_comp (⇑(diskParamWeierstrass (K := K) hf hdeg hωeval hu))
    (Equiv.bijective _)]
  refine finsum_congr fun z ↦ ?_
  simp only [diskParamWeierstrass, Equiv.ofBijective_apply, diskPointWeierstrass,
    CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]

variable [IsTopologicalRing O]

/-- **`thm:spec` as a fiber count, generic residue point**: reindexing the per-disk point sum
along the disk parametrization. -/
theorem fiberCount_span_of_ne_zero (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits)
    {ab bb : ResidueField O} (hb : bb ^ 2 = (f.map (residue O)).eval ab) (hb0 : bb ≠ 0) :
    fiberCount f (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
        HypRing K (f.map (algebraMap O K)))}) (.affine ab bb hb)
      = (emultiplicity (pointIdeal (f.map (residue O)) ab bb)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  obtain ⟨a, b, ha, hbres, hab, hfa, hsum⟩ :=
    exists_center_finsum_emultiplicity_generic (K := K) h2 hN hcop hsplit hb hb0
  subst ha hbres
  refine .trans ?_ hsum
  rw [fiberCount, ← finsum_comp (⇑(diskParamGeneric (K := K) hab hfa h2))
    (Equiv.bijective _)]
  refine finsum_congr fun z ↦ ?_
  simp only [diskParamGeneric, Equiv.ofBijective_apply, diskPointGeneric,
    CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]

/-- **`thm:spec` as a fiber count**: for a coordinate-ring element with coprime primitive
split data, the fiber count of the principal ideal at *every* affine residue point equals
the intrinsic multiplicity of the reduced function there. -/
theorem fiberCount_span [PerfectField (ResidueField O)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    (hsq : ∀ (ω : O), f.eval ω = 0 → ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits)
    {ab bb : ResidueField O} (hb : bb ^ 2 = (f.map (residue O)).eval ab) :
    fiberCount f (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
        HypRing K (f.map (algebraMap O K)))}) (.affine ab bb hb)
      = (emultiplicity (pointIdeal (f.map (residue O)) ab bb)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  by_cases hb0 : bb = 0
  · subst hb0
    exact fiberCount_span_of_eq_zero hf hdeg h2 hN hsq hsplit
      (by rw [← hb, zero_pow two_ne_zero])
  · exact fiberCount_span_of_ne_zero h2 hN hcop hsplit hb hb0

end Engine

end ChabautyColeman

end
