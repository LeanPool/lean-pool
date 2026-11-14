/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Specialization.DiskPointSum

import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
import Mathlib.FieldTheory.Perfect

/-!
# `thm:spec` in pointwise form over the whole residue curve

Center-lifting (`exists_generic_center`, `exists_weierstrass_center`: every affine point of the
reduced curve lifts to a disk center by Hensel's lemma) combined with the per-disk point sums
(`LeanPool.HyperellipticCurves.Specialization.DiskPointSum`) gives the specialization theorem in its
final
pointwise form: for
*every* affine point `P_bar` of the reduced curve,
`∑_{P : red P = P_bar} ord_P(h) = ord_P_bar(h_bar)`
(`exists_center_finsum_emultiplicity_generic` / `..._weierstrass`), for data split over the
fraction field `K`.

Together with `LeanPool.HyperellipticCurves.Curve.PointFactorization` (every nonzero prime over an
algebraically closed residue field is a point ideal; principal ideals factor with `emultiplicity`
exponents), this identifies the divisor of the reduced function `h_bar` with the pointwise reduction
of
the divisor of `h` — the well-definedness engine of the reduction homomorphism `thm:redJ-hom`: the
reduction of a principal divisor is principal.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

section CenterLift

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]

/-- Every generic point of the residue curve lifts to a disk center: `a` is any lift of `ā`,
and the `y`-coordinate is a Hensel square root of `f(a)`. -/
theorem exists_generic_center {f : O[X]} (h2 : IsUnit (2 : O)) {ab bb : ResidueField O}
    (hb : bb ^ 2 = (f.map (residue O)).eval ab) (hb0 : bb ≠ 0) :
    ∃ a b : O, residue O a = ab ∧ residue O b = bb ∧ b ^ 2 = f.eval a ∧ IsUnit (f.eval a) := by
  obtain ⟨a, ha⟩ := residue_surjective ab
  obtain ⟨b₀, hb₀⟩ := residue_surjective bb
  have hfa : IsUnit (f.eval a) := (residue_ne_zero_iff_isUnit _).mp fun h0 ↦ by
    rw [← eval_map_apply, ha] at h0
    exact hb0 ((pow_eq_zero_iff (n := 2) two_ne_zero).mp (by rw [hb, h0]))
  have hb₀u : IsUnit b₀ := (residue_ne_zero_iff_isUnit _).mp (by rwa [hb₀])
  have h0 : (Polynomial.X ^ 2 - Polynomial.C (f.eval a)).eval b₀ ∈ maximalIdeal O := by
    have hval : residue O ((Polynomial.X ^ 2 - Polynomial.C (f.eval a)).eval b₀) = 0 := by
      rw [eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, hb₀,
        ← eval_map_apply, ha, ← hb, sub_self]
    exact (residue_eq_zero_iff _).mp hval
  have hderiv : IsUnit ((Polynomial.X ^ 2 - Polynomial.C (f.eval a)).derivative.eval b₀) := by
    rw [derivative_sub, Polynomial.derivative_C, sub_zero, derivative_X_pow]
    simpa using h2.mul hb₀u
  obtain ⟨b, hbeval, hbsub⟩ := exists_smooth_root h0 hderiv
  rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hbeval
  refine ⟨a, b, ha, ?_, hbeval, hfa⟩
  rw [residue_eq_of_sub_mem hbsub, hb₀]

/-- Every Weierstrass point of the residue curve lifts to a Weierstrass disk center (a Hensel
root of `f`; simple because the reduction is squarefree over the residue field). -/
theorem exists_weierstrass_center {f : O[X]} [PerfectField (ResidueField O)]
    [Fact (Squarefree (f.map (residue O)))]
    {ab : ResidueField O} (hroot : (f.map (residue O)).eval ab = 0) :
    ∃ ω : O, residue O ω = ab ∧ f.eval ω = 0 ∧ IsUnit (f.derivative.eval ω) := by
  obtain ⟨ω₀, hω₀⟩ := residue_surjective ab
  have hsep : (f.map (residue O)).Separable :=
    PerfectField.separable_iff_squarefree.mpr Fact.out
  have hder : (f.map (residue O)).derivative.eval ab ≠ 0 := fun h0 ↦
    Polynomial.not_isUnit_X_sub_C ab (hsep.isUnit_of_dvd'
      (dvd_iff_isRoot.mpr hroot) (dvd_iff_isRoot.mpr h0))
  have h0 : f.eval ω₀ ∈ maximalIdeal O := by
    have hval : residue O (f.eval ω₀) = 0 := by rw [← eval_map_apply, hω₀, hroot]
    exact (residue_eq_zero_iff _).mp hval
  have hu : IsUnit (f.derivative.eval ω₀) := (residue_ne_zero_iff_isUnit _).mp fun hmem ↦
    hder (by rwa [derivative_map, ← hω₀, eval_map_apply])
  obtain ⟨ω, hωeval, hωsub⟩ := exists_smooth_root h0 hu
  refine ⟨ω, ?_, hωeval, isUnit_eval_of_sub_mem hu hωsub⟩
  rw [residue_eq_of_sub_mem hωsub, hω₀]

end CenterLift

/-! ### `thm:spec`, pointwise assembled over the residue curve -/

section Pointwise

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **`thm:spec` in pointwise form, generic residue point**: every generic point `(ā, b_bar)` of the
reduced curve has a disk center `(a, b)` above it for which the total intrinsic multiplicity of
`P + Q·y` over the residue disk equals the intrinsic order of the reduced function at `(ā, b_bar)`:
`∑_{red P = P_bar} ord_P(h) = ord_P_bar(h_bar)`. -/
theorem exists_center_finsum_emultiplicity_generic {f P Q : O[X]} [IsTopologicalRing O]
    [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
    [Fact (Squarefree (f.map (algebraMap O K)))]
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (h2 : IsUnit (2 : O)) (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits)
    {ab bb : ResidueField O} (hb : bb ^ 2 = (f.map (residue O)).eval ab) (hb0 : bb ≠ 0) :
    ∃ a b : O, residue O a = ab ∧ residue O b = bb ∧ b ^ 2 = f.eval a ∧ IsUnit (f.eval a) ∧
      ∑ᶠ z : maximalIdeal O,
        (emultiplicity
          (pointIdeal (f.map (algebraMap O K)) (algebraMap O K (a + z.1))
            (algebraMap O K (b * PSeries.eval z.1 (diskSeriesGeneric f a))))
          (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))})).toNat
      = (emultiplicity (pointIdeal (f.map (residue O)) ab bb)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  obtain ⟨a, b, ha, hbres, hab, hfa⟩ := exists_generic_center h2 hb hb0
  refine ⟨a, b, ha, hbres, hab, hfa, ?_⟩
  have h := finsum_emultiplicity_diskPointGeneric (K := K) hab hfa h2 hN hcop hsplit
  rwa [ha, hbres] at h

/-- **`thm:spec` in pointwise form, Weierstrass residue point**: every Weierstrass point
`(ā, 0)` of the reduced curve has a Weierstrass disk center `ω` above it for which the total
intrinsic multiplicity of `P + Q·y` over the residue disk equals the intrinsic order of the
reduced function at `(ā, 0)`. -/
theorem exists_center_finsum_emultiplicity_weierstrass {f P Q : O[X]}
    [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
    [Fact (Squarefree (f.map (algebraMap O K)))]
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))] [PerfectField (ResidueField O)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hsq : ∀ (ω : O), f.eval ω = 0 → ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits)
    {ab : ResidueField O} (hroot : (f.map (residue O)).eval ab = 0) :
    ∃ (ω : O) (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)),
      residue O ω = ab ∧
      ∑ᶠ z : maximalIdeal O,
        (emultiplicity
          (pointIdeal (f.map (algebraMap O K))
            (algebraMap O K (weierstrassRoot hf hdeg hω hu z.2)) (algebraMap O K z.1))
          (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))})).toNat
      = (emultiplicity (pointIdeal (f.map (residue O)) ab 0)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  obtain ⟨ω, hωres, hωeval, hu⟩ := exists_weierstrass_center hroot
  refine ⟨ω, hωeval, hu, hωres, ?_⟩
  have h := finsum_emultiplicity_diskPointWeierstrass (K := K) hf hdeg hωeval hu h2 hN
    (hsq ω hωeval) hsplit
  rwa [hωres] at h

end Pointwise

end ChabautyColeman
