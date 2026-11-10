/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.WeierstrassOrder
public import LeanPool.HyperellipticCurves.Disks.Charts
public import LeanPool.HyperellipticCurves.Disks.OrdMatchElement
public import LeanPool.HyperellipticCurves.Series.PolyZeroCount

import LeanPool.HyperellipticCurves.ForMathlib.ENat
import LeanPool.HyperellipticCurves.ForMathlib.Finprod
import LeanPool.HyperellipticCurves.ForMathlib.Multiplicity
import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import LeanPool.HyperellipticCurves.ForMathlib.WeierstrassPreparation
import LeanPool.HyperellipticCurves.Specialization.CpZeros

/-!
# The per-disk point sums (generic and Weierstrass disks)

`thm:spec` in point form on a generic residue disk: the total intrinsic multiplicity of a
function `h = P + Q·y` at the points of the disk of `(ā, b_bar)` equals the intrinsic order of the
reduced function at the reduced point
(`ChabautyColeman.finsum_emultiplicity_diskPointGeneric`):
`∑_{P : red P = P_bar} ord_P(h) = ord_P_bar(h_bar)`.

The disk points are the parametrized points `(a + z, b·η(z))`, `z ∈ 𝔪` (`diskPointGeneric`
coordinates), over a complete DVR `O` whose fraction field `K` *splits the data*: the norm
polynomial `P² - f·Q²` splits over `K` and `P, Q` are coprime over `K` (in the redJ assembly,
`O = O_L` for the splitting field `L`, provided by `LeanPool.HyperellipticCurves.RedJ.DVRExtension`;
the
coprimality is arranged by splitting off the `K[x]`-gcd, whose divisor reduces trivially).

Per point (`emult_diskPointGeneric_eq_rootMultiplicity`): the multiplicity of `h` at the point
of parameter `z` is the root multiplicity at `z` of the distinguished factor `W` of the disk
expansion. Evaluating the Weierstrass factorization at `z` (the project's `PSeries.eval`, a ring
homomorphism) shows `h` vanishes at the point iff `W(z) = 0`; coprimality excludes simultaneous
vanishing with the conjugate; and the multiplicity is pinned by the norm decomposition
`emult(h) + emult(h*) = rootMult(N)` against the polynomial factorization
`taylor a N = W·W'·q` (`polynomial_cofactor`, `q` unit-constant). Summing with
`finsum_rootMultiplicity_maximalIdeal` gives `deg W`, which is the reduced order
(`natDegree_eq_toNat_order_map`), identified with the intrinsic reduced order by the
unconditional element order match (`order_funcExpansionGeneric_eq_emultiplicity`).

The Weierstrass disk (`finsum_emultiplicity_diskPointWeierstrass`) is self-conjugate (the
involution `z ↦ -z` on the parameter is the hyperelliptic involution on the disk), and its
count is purely algebraic: the conjugate-pair identity at each point, the two-to-one fold of
the parameter onto the `x`-fiber (`finsum_comp_two_to_one`), and the split zero count of
`taylor ω (P² - f·Q²)`. The squareness hypothesis `hsq` supplies the `y`-coordinates of the
potential zeros (automatic over a field splitting `y² - f(xᵢ)` for the roots `xᵢ` of the norm).
No point of the infinity disk is ever needed for the reduction homomorphism: such points
reduce to `∞_bar`, which contributes trivially to the affine class group.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

/-- Evaluating the generic disk expansion at a parameter value gives the value of the function
`P + Q·y` at the parametrized point `(a + z, b·η(z))`. -/
theorem eval_funcExpansionGeneric {O : Type*} [CommRing O] [IsLocalRing O]
    [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
    [T2Space O] [IsTopologicalRing O] (f P Q : O[X]) (a b : O) {z : O}
    (hz : z ∈ maximalIdeal O) :
    PSeries.eval z (funcExpansionGeneric f P Q a b)
      = P.eval (a + z) + Q.eval (a + z) * (b * PSeries.eval z (diskSeriesGeneric f a)) := by
  rw [funcExpansionGeneric, PSeries.eval_add hz, PSeries.eval_mul hz, PSeries.eval_mul hz,
    PSeries.eval_coe, PSeries.eval_coe, PSeries.eval_C, taylor_eval, taylor_eval, add_comm z a]
  ring

section

variable {K : Type*} [Field K] {f : K[X]} [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- Norm decomposition of the intrinsic order at a generic point: the orders of an element and
its conjugate sum to the root multiplicity of the norm polynomial. -/
theorem emultiplicity_pointIdeal_element_add_star {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀)
    (hy : y₀ ≠ 0) {z : HypRing K f} (hN : z.re ^ 2 - f * z.im ^ 2 ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {z})
        + emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {star z})
      = rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) := by
  have hP : Prime (pointIdeal f x₀ y₀) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ y₀) (pointIdeal_isPrime hb)
  rw [← emultiplicity_mul hP, Ideal.span_singleton_mul_span_singleton,
    HypRing.mul_star_eq_norm, HypRing.norm_eq,
    emultiplicity_pointIdeal_generic hb hy hN]

/-- Pointwise conjugate pair-sum as naturals away from the Weierstrass points: the intrinsic
orders of an element `w` and its conjugate at `(x₀, y₀)`, `y₀ ≠ 0`, sum to the norm root
multiplicity. -/
theorem toNat_emult_add_star_pointIdeal {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) (hy : y₀ ≠ 0)
    {w : HypRing K f} (hN : w.re ^ 2 - f * w.im ^ 2 ≠ 0) :
    (emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {w})).toNat
        + (emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {star w})).toNat
      = rootMultiplicity x₀ (w.re ^ 2 - f * w.im ^ 2) :=
  ENat.toNat_add_toNat_of_add_eq_natCast (emultiplicity_pointIdeal_element_add_star hb hy hN)

/-- Pointwise conjugate pair-sum as naturals at a Weierstrass point: there the element and its
conjugate have the same order, so the sum is *twice* the norm root multiplicity. -/
theorem toNat_emult_add_star_pointIdeal_weierstrass {x₀ : K} (hb : (0 : K) ^ 2 = f.eval x₀)
    {w : HypRing K f} (hN : w.re ^ 2 - f * w.im ^ 2 ≠ 0) :
    (emultiplicity (pointIdeal f x₀ 0) (Ideal.span {w})).toNat
        + (emultiplicity (pointIdeal f x₀ 0) (Ideal.span {star w})).toNat
      = 2 * rootMultiplicity x₀ (w.re ^ 2 - f * w.im ^ 2) := by
  refine ENat.toNat_add_toNat_of_add_eq_natCast ?_
  rw [emultiplicity_pointIdeal_element_weierstrass hb hN, nsmul_eq_mul]
  push_cast
  ring

end

/-- Evaluating the element `P + Q·y` at the parametrized point of `z ∈ 𝔪` (as a value in `K`):
by the Weierstrass factorization of the disk expansion it equals `W(z)` times a unit series value,
mapped into `K`. -/
private theorem evalHom_pair_eq {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
    [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
    [IsTopologicalRing O] {K : Type*} [Field K] [Algebra O K]
    {f P Q : O[X]} {a b : O} {W : O[X]} {u : O⟦X⟧}
    (hfacW : (funcExpansionGeneric f P Q a b).IsWeierstrassFactorization W u)
    {z : O} (hz : z ∈ maximalIdeal O)
    (hbK : (algebraMap O K (b * PSeries.eval z (diskSeriesGeneric f a))) ^ 2
      = (f.map (algebraMap O K)).eval (algebraMap O K (a + z))) :
    evalHom hbK (⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
        HypRing K (f.map (algebraMap O K)))
      = algebraMap O K (W.eval z * PSeries.eval z u) := by
  set ι := algebraMap O K
  rw [evalHom_apply]
  change (P.map ι).eval (ι (a + z)) + (Q.map ι).eval (ι (a + z)) * _ = _
  rw [eval_map_apply, eval_map_apply, ← map_mul, ← map_add,
    ← eval_funcExpansionGeneric f P Q a b hz]
  nth_rw 1 [hfacW.eq_mul]
  rw [PSeries.eval_mul hz, PSeries.eval_coe]

/-- Through a factorization `taylor a N = W·W'·q` with `q` a unit at `0` and `W'` not vanishing
at `z ∈ 𝔪`, the root multiplicity of `N` (mapped to `K`) at `a + z` is carried by the factor
`W` alone. -/
private theorem rootMultiplicity_map_eq_of_taylor_factor {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {N W W' q : O[X]} {a z : O}
    (hz : z ∈ maximalIdeal O) (hNfac : taylor a N = W * W' * q) (hq : IsUnit (q.coeff 0))
    (hN0 : N.map (algebraMap O K) ≠ 0) (hW'0 : W'.eval z ≠ 0) :
    (N.map (algebraMap O K)).rootMultiplicity (algebraMap O K (a + z))
      = (W.map (algebraMap O K)).rootMultiplicity (algebraMap O K z) := by
  set ι := algebraMap O K
  have hιinj : Function.Injective ι := IsFractionRing.injective O K
  rw [show ι (a + z) = ι z + ι a by rw [map_add, add_comm], ← rootMultiplicity_taylor,
    ← map_taylor, hNfac, Polynomial.map_mul, Polynomial.map_mul]
  have hprod0 : (W.map ι) * (W'.map ι) * (q.map ι) ≠ 0 := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← hNfac, map_taylor]
    exact fun h0 ↦ hN0 ((taylor_eq_zero _ _).mp h0)
  have hrW' : (W'.map ι).rootMultiplicity (ι z) = 0 :=
    rootMultiplicity_eq_zero fun hroot ↦ hW'0 (hroot.of_map hιinj)
  have hrq : (q.map ι).rootMultiplicity (ι z) = 0 :=
    rootMultiplicity_eq_zero fun hroot ↦
      (isUnit_eval_of_isUnit_coeff_zero hq hz).ne_zero (hroot.of_map hιinj)
  rw [rootMultiplicity_mul hprod0, rootMultiplicity_mul (left_ne_zero_of_mul hprod0),
    hrW', hrq, add_zero, add_zero]

/-- A monic factor `W` of `taylor a N` inherits splitting over `K` from `N`: since `N` splits,
so does `taylor a N`, and `W` divides it. -/
private theorem splits_weierstrassFactor {O : Type*} [CommRing O] [IsDomain O]
    {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K] {N W W' q : O[X]} {a : O}
    (hN0 : N ≠ 0) (hsplit : (N.map (algebraMap O K)).Splits)
    (hNfac : taylor a N = W * W' * q) : (W.map (algebraMap O K)).Splits := by
  set ι := algebraMap O K
  have hTsplit : ((taylor a N).map ι).Splits := by rw [map_taylor]; exact hsplit.taylor _
  have hTKne : (taylor a N).map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective O K)).mpr fun h0 ↦
      hN0 ((taylor_eq_zero _ _).mp h0)
  exact hTsplit.of_dvd hTKne ⟨(W' * q).map ι, by rw [← Polynomial.map_mul, ← mul_assoc, ← hNfac]⟩

section DiskSum

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- Per-point multiplicity on the generic disk: at the parametrized point of `z ∈ 𝔪`, the
intrinsic order of `P + Q·y` equals the root multiplicity at `z` of the distinguished factor `W`
of the disk expansion. -/
private theorem emult_diskPointGeneric_eq_rootMultiplicity {f P Q : O[X]} {a b : O}
    [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
    [Fact (Squarefree (f.map (algebraMap O K)))]
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    {W W' q : O[X]} {u u' : O⟦X⟧}
    (hfacW : (funcExpansionGeneric f P Q a b).IsWeierstrassFactorization W u)
    (hfacW' : (funcExpansionGeneric f P (-Q) a b).IsWeierstrassFactorization W' u')
    (hNfac : taylor a (P ^ 2 - f * Q ^ 2) = W * W' * q) (hq : IsUnit (q.coeff 0))
    {z : O} (hz : z ∈ maximalIdeal O) :
    (emultiplicity
        (pointIdeal (f.map (algebraMap O K)) (algebraMap O K (a + z))
          (algebraMap O K (b * PSeries.eval z (diskSeriesGeneric f a))))
        (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
          HypRing K (f.map (algebraMap O K)))})).toNat
      = (W.map (algebraMap O K)).rootMultiplicity (algebraMap O K z) := by
  set ι := algebraMap O K
  have hιinj : Function.Injective ι := IsFractionRing.injective O K
  have hbK : (ι (b * PSeries.eval z (diskSeriesGeneric f a))) ^ 2
      = (f.map ι).eval (ι (a + z)) := by
    rw [← map_pow, generic_onCurve f hb hfa h2 hz, eval_map_apply]
  have hηu : IsUnit (PSeries.eval z (diskSeriesGeneric f a)) := by
    refine isUnit_of_sub_mem isUnit_one ?_
    simpa [constantCoeff_diskSeriesGeneric]
      using PSeries.eval_sub_constantCoeff_mem hz (diskSeriesGeneric f a)
  have hyu : IsUnit (b * PSeries.eval z (diskSeriesGeneric f a)) := (isUnit_b hb hfa).mul hηu
  have hyK : ι (b * PSeries.eval z (diskSeriesGeneric f a)) ≠ 0 := fun h0 ↦
    hyu.ne_zero (hιinj (by rw [h0, map_zero]))
  -- the values of the function and its conjugate at the parametrized point
  have hval : evalHom hbK (⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι))
      = ι (W.eval z * PSeries.eval z u) := evalHom_pair_eq hfacW hz hbK
  have hstar : evalHom hbK (star (⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)))
      = ι (W'.eval z * PSeries.eval z u') := by
    rw [HypRing.star_mk, ← Polynomial.map_neg]
    exact evalHom_pair_eq hfacW' hz hbK
  have huv : IsUnit (PSeries.eval z u) :=
    isUnit_of_sub_mem (isUnit_iff_constantCoeff.mp hfacW.isUnit)
      (PSeries.eval_sub_constantCoeff_mem hz u)
  have huv' : IsUnit (PSeries.eval z u') :=
    isUnit_of_sub_mem (isUnit_iff_constantCoeff.mp hfacW'.isUnit)
      (PSeries.eval_sub_constantCoeff_mem hz u')
  rcases eq_or_ne (W.eval z) 0 with hW0 | hW0
  · -- the function vanishes at the point; the conjugate must not (coprimality)
    have hW'0 : W'.eval z ≠ 0 := by
      intro h'
      have h1 : (P.map ι).eval (ι (a + z))
          + (Q.map ι).eval (ι (a + z)) * ι (b * PSeries.eval z (diskSeriesGeneric f a)) = 0 := by
        have := hval
        rw [evalHom_apply] at this
        dsimp only at this
        rw [this, hW0, zero_mul, map_zero]
      have h2' : (P.map ι).eval (ι (a + z))
          - (Q.map ι).eval (ι (a + z)) * ι (b * PSeries.eval z (diskSeriesGeneric f a)) = 0 := by
        have := hstar
        rwa [evalHom_star, h', zero_mul, map_zero] at this
      exact isCoprime_not_both_eval_add hcop hyK h1 h2'
    -- norm decomposition at the point
    have hnormK : ((⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)).re) ^ 2
        - (f.map ι) * ((⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)).im) ^ 2
          = (P ^ 2 - f * Q ^ 2).map ι :=
      map_norm_poly ι f P Q
    have hN0 : (P ^ 2 - f * Q ^ 2).map ι ≠ 0 := by
      refine (Polynomial.map_ne_zero_iff hιinj).mpr fun hN' ↦ ?_
      rw [hN', map_zero] at hNfac
      have := hNfac.symm
      rcases mul_eq_zero.mp this with hWW' | hq0
      · rcases mul_eq_zero.mp hWW' with hW | hW'
        · exact hfacW.isDistinguishedAt.monic.ne_zero hW
        · exact hfacW'.isDistinguishedAt.monic.ne_zero hW'
      · exact hq.ne_zero (by rw [hq0, coeff_zero])
    have hpair := emultiplicity_pointIdeal_element_add_star hbK hyK
      (z := (⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι))) (by rwa [hnormK])
    have hstar0 : emultiplicity (pointIdeal (f.map ι) (ι (a + z))
          (ι (b * PSeries.eval z (diskSeriesGeneric f a))))
        (Ideal.span {star (⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι))}) = 0 :=
      emultiplicity_pointIdeal_element_eq_zero hbK (by
        rw [hstar]
        exact fun h0 ↦ (mul_ne_zero hW'0 huv'.ne_zero) (hιinj (by rw [h0, map_zero])))
    rw [hstar0, add_zero, hnormK] at hpair
    -- root multiplicity of the norm through the cofactor factorization
    rw [hpair, rootMultiplicity_map_eq_of_taylor_factor hz hNfac hq hN0 hW'0]
    exact ENat.toNat_natCast _
  · -- the function does not vanish: both sides are zero
    have hev : evalHom hbK (⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)) ≠ 0 := by
      rw [hval]
      exact fun h0 ↦ (mul_ne_zero hW0 huv.ne_zero) (hιinj (by rw [h0, map_zero]))
    rw [emultiplicity_pointIdeal_element_eq_zero hbK hev, ENat.toNat_zero]
    exact (rootMultiplicity_eq_zero fun hroot ↦ hW0 (hroot.of_map hιinj)).symm

/-- **Per-disk point sum, generic disk (`thm:spec` in point form).** The total intrinsic
multiplicity of the function `P + Q·y` at the parametrized points of the generic residue disk of
`(ā, b_bar)` equals the intrinsic order of the reduced function at the reduced point. Requires the
data to be split over `K`: the norm polynomial splits and `P, Q` are coprime over `K`. -/
theorem finsum_emultiplicity_diskPointGeneric {f P Q : O[X]} {a b : O}
    [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
    [Fact (Squarefree (f.map (algebraMap O K)))]
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits) :
    ∑ᶠ z : maximalIdeal O,
        (emultiplicity
          (pointIdeal (f.map (algebraMap O K)) (algebraMap O K (a + z.1))
            (algebraMap O K (b * PSeries.eval z.1 (diskSeriesGeneric f a))))
          (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))})).toNat
      = (emultiplicity (pointIdeal (f.map (residue O)) (residue O a) (residue O b))
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  classical
  set ρ := residue O
  have hN0 : P ^ 2 - f * Q ^ 2 ≠ 0 := fun h ↦ hN (by rw [h, Polynomial.map_zero])
  -- Weierstrass preparation of the expansion and its conjugate
  have hprod : (funcExpansionGeneric f P Q a b).map ρ
      * (funcExpansionGeneric f P (-Q) a b).map ρ
        = ((taylor (ρ a) ((P ^ 2 - f * Q ^ 2).map ρ) : (ResidueField O)[X])
            : (ResidueField O)⟦X⟧) := by
    rw [← map_mul, funcExpansionGeneric_mul_conj P Q hb hfa h2, ← polynomial_map_coe, map_taylor]
  have hTne : ((taylor (ρ a) ((P ^ 2 - f * Q ^ 2).map ρ) : (ResidueField O)[X])
      : (ResidueField O)⟦X⟧) ≠ 0 := by
    rw [ne_eq, Polynomial.coe_eq_zero_iff]
    exact fun h0 ↦ hN ((taylor_eq_zero _ _).mp h0)
  have hne : (funcExpansionGeneric f P Q a b).map ρ ≠ 0 :=
    left_ne_zero_of_mul (hprod ▸ hTne)
  have hne' : (funcExpansionGeneric f P (-Q) a b).map ρ ≠ 0 :=
    right_ne_zero_of_mul (hprod ▸ hTne)
  have hfacW := (funcExpansionGeneric f P Q a b
    ).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hne
  have hfacW' := (funcExpansionGeneric f P (-Q) a b
    ).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hne'
  set W := (funcExpansionGeneric f P Q a b).weierstrassDistinguished hne
  set W' := (funcExpansionGeneric f P (-Q) a b).weierstrassDistinguished hne'
  -- the polynomial cofactor of taylor a N = (W·W')·q
  have hfacN : ((taylor a (P ^ 2 - f * Q ^ 2) : O[X]) : O⟦X⟧).IsWeierstrassFactorization
      (W * W') ((funcExpansionGeneric f P Q a b).weierstrassUnit hne
        * (funcExpansionGeneric f P (-Q) a b).weierstrassUnit hne') :=
    funcExpansionGeneric_mul_conj P Q hb hfa h2 ▸ hfacW.mul hfacW'
  obtain ⟨hNfacpoly, hqunit, -⟩ := hfacN.polynomial_cofactor
  -- pointwise: only the distinguished factor of this disk contributes
  have hpt : ∀ z : maximalIdeal O,
      (emultiplicity
          (pointIdeal (f.map (algebraMap O K)) (algebraMap O K (a + z.1))
            (algebraMap O K (b * PSeries.eval z.1 (diskSeriesGeneric f a))))
          (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))})).toNat
        = (W.map (algebraMap O K)).rootMultiplicity (algebraMap O K z.1) := fun z ↦
    emult_diskPointGeneric_eq_rootMultiplicity hb hfa h2 hcop hfacW hfacW' hNfacpoly hqunit z.2
  rw [finsum_congr hpt]
  -- the disk count of the distinguished factor
  have hWred : W.map ρ ≠ 0 := (hfacW.isDistinguishedAt.monic.map ρ).ne_zero
  have hWsplit : (W.map (algebraMap O K)).Splits :=
    splits_weierstrassFactor hN0 hsplit hNfacpoly
  rw [finsum_rootMultiplicity_maximalIdeal hWred hWsplit,
    show (W.map ρ).rootMultiplicity 0 = W.natDegree by
      rw [show W.map ρ = Polynomial.X ^ W.natDegree from hfacW.isDistinguishedAt.map_eq_X_pow,
        rootMultiplicity_eq_natTrailingDegree', natTrailingDegree_X_pow]]
  -- identify with the reduced intrinsic order
  have hbρ : (ρ b) ^ 2 = (f.map ρ).eval (ρ a) := onCurve_map _ hb
  have hyρ : ρ b ≠ 0 := fun h0 ↦ (hfa.map ρ).ne_zero (by
    rw [← eval_map_apply, ← hbρ, h0]; ring)
  have hNρ : (P.map ρ) ^ 2 - (f.map ρ) * (Q.map ρ) ^ 2 ≠ 0 := map_norm_poly ρ f P Q ▸ hN
  have hordred := order_funcExpansionGeneric_eq_emultiplicity (P.map ρ) (Q.map ρ) hbρ hyρ hNρ
  rw [hfacW.natDegree_eq_toNat_order_map, map_funcExpansionGeneric ρ f P Q a b hfa h2, hordred]

end DiskSum

/-! ### Star transport for point ideals -/

section starTransport

variable {K : Type*} [Field K] {f : K[X]}

/-- The `star` involution carries the point ideal of `(x₀, y₀)` to that of `(x₀, -y₀)`. -/
theorem map_star_pointIdeal (x₀ y₀ : K) :
    Ideal.map (QuadraticAlgebra.starAlgEquiv (S := K) (R := K[X]) (a := f) (b := 0)).toRingEquiv
        (pointIdeal f x₀ y₀) = pointIdeal f x₀ (-y₀) := by
  simp only [pointIdeal, Ideal.map_span, Set.image_pair, AlgEquiv.coe_toRingEquiv,
    QuadraticAlgebra.starAlgEquiv_apply, star_sub, HypRing.star_y, HypRing.algebraMap_eq_C,
    QuadraticAlgebra.star_algebraMap]
  rw [show -HypRing.y f - algebraMap K[X] (HypRing K f) (Polynomial.C y₀)
      = -(HypRing.y f + algebraMap K[X] (HypRing K f) (Polynomial.C y₀)) by ring,
    map_neg Polynomial.C y₀, map_neg, sub_neg_eq_add]
  exact Ideal.span_pair_neg _ _

/-- The intrinsic order at the conjugate point is the intrinsic order of the conjugate
element. -/
theorem emultiplicity_pointIdeal_neg (x₀ y₀ : K) (z : HypRing K f) :
    emultiplicity (pointIdeal f x₀ (-y₀)) (Ideal.span {z})
      = emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {star z}) := by
  have hspan : Ideal.map
      (QuadraticAlgebra.starAlgEquiv (S := K) (R := K[X]) (a := f) (b := 0)).toRingEquiv
        (Ideal.span {star z}) = Ideal.span {z} := by
    rw [Ideal.map_span, Set.image_singleton, AlgEquiv.coe_toRingEquiv,
      QuadraticAlgebra.starAlgEquiv_apply, star_star]
  conv_lhs => rw [← map_star_pointIdeal, ← hspan]
  exact Ideal.emultiplicity_map_ringEquiv _ _ _

end starTransport

/-! ### The per-disk point sum (Weierstrass disk) -/

/-- The Weierstrass-disk root is even in the `y`-parameter:
`weierstrassRoot(-y) = weierstrassRoot(y)`, since `(-y)² = y²` and the root is unique by
Hensel. -/
private theorem weierstrassRoot_neg {O : Type*} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O}
    (hy : y ∈ maximalIdeal O) :
    weierstrassRoot hf hdeg hω hu (neg_mem hy) = weierstrassRoot hf hdeg hω hu hy := by
  refine hensel_unique ?_ (isUnit_eval_of_sub_mem hu (weierstrassRoot_sub hf hdeg hω hu hy)) ?_
  · simpa using sub_mem (weierstrassRoot_sub hf hdeg hω hu (neg_mem hy))
      (weierstrassRoot_sub hf hdeg hω hu hy)
  · rw [weierstrassRoot_eval hf hdeg hω hu (neg_mem hy),
      weierstrassRoot_eval hf hdeg hω hu hy, neg_sq]

/-- Negation is a bijection of the maximal ideal (as a subtype). -/
private theorem neg_bijective_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O] :
    Function.Bijective (fun z : maximalIdeal O ↦ (⟨-z.1, neg_mem z.2⟩ : maximalIdeal O)) :=
  ⟨fun _ _ hab ↦ Subtype.ext (neg_injective (congrArg Subtype.val hab)),
    fun b ↦ ⟨⟨-b.1, neg_mem b.2⟩, Subtype.ext (neg_neg b.1)⟩⟩

/-- The only fixed point of negation on the maximal ideal is `0` (when `2` is a unit). -/
private theorem neg_eq_self_iff_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O]
    (h2 : IsUnit (2 : O)) (z : maximalIdeal O) :
    (⟨-z.1, neg_mem z.2⟩ : maximalIdeal O) = z ↔ z = ⟨0, Submodule.zero_mem _⟩ := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ Subtype.ext (h ▸ neg_zero)⟩
  have h2z : (2 : O) * z.1 = 0 := by linear_combination -congrArg Subtype.val h
  rwa [h2.mul_right_eq_zero] at h2z

/-- Support-finiteness for the `x`-fiber count: if `s z` is a curve point over `z.1` (i.e.
`(ι z.1)² = f(s z)`), then `z ↦ rootMult_{s z}(p)` has finite support — its nonzero locus injects
via `z ↦ ι z.1` into the roots of `∏_{r ∈ p.roots} (X² - C f(r))`. -/
private theorem finite_support_rootMultiplicity_onCurve {O : Type*} [CommRing O] [IsDomain O]
    [IsLocalRing O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {f : O[X]} {p : K[X]} (hp : p ≠ 0)
    {s : maximalIdeal O → K}
    (hs : ∀ z : maximalIdeal O, (algebraMap O K z.1) ^ 2 = (f.map (algebraMap O K)).eval (s z)) :
    (Function.support fun z : maximalIdeal O ↦ p.rootMultiplicity (s z)).Finite := by
  classical
  set ι := algebraMap O K
  have hDne : ((p.roots).map
      (fun r ↦ Polynomial.X ^ 2 - Polynomial.C ((f.map ι).eval r))).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 ↦ by
      obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp h0
      exact (monic_X_pow_sub_C ((f.map ι).eval r) two_ne_zero).ne_zero hr
  have hinjz : Function.Injective (fun z : maximalIdeal O ↦ ι z.1) :=
    fun a b hab ↦ Subtype.ext (IsFractionRing.injective O K hab)
  refine Set.Finite.of_finite_image (Set.Finite.subset (Finset.finite_toSet
    (((p.roots).map
      (fun r ↦ Polynomial.X ^ 2 - Polynomial.C ((f.map ι).eval r))).prod.roots.toFinset)) ?_)
    hinjz.injOn
  rintro x ⟨z, hz, rfl⟩
  rw [Function.mem_support] at hz
  have hroot : p.IsRoot (s z) := by
    by_contra hr
    exact hz (rootMultiplicity_eq_zero hr)
  simp only [Finset.mem_coe]
  rw [Multiset.mem_toFinset, mem_roots hDne, IsRoot, Polynomial.eval_multiset_prod]
  refine Multiset.prod_eq_zero ?_
  rw [Multiset.map_map]
  refine Multiset.mem_map.mpr ⟨s z, (mem_roots hp).mpr hroot, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_pow, eval_X, eval_C]
  rw [← hs z, sub_self]

section WeierstrassDiskSum

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type*} [Field K] [Algebra O K]

/-- **Every `x`-parameter with a root of the norm is hit by the disk parametrization**: if
the norm polynomial vanishes at `ω + b`, the squareness hypothesis produces a `y ∈ 𝔪` whose
Hensel root is `ω + b`. -/
private theorem exists_param_of_isRoot {f P Q : O[X]} {ω : O} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    (hsq : ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (b : maximalIdeal O)
    (hroot : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + b.1)) = 0) :
    ∃ z : maximalIdeal O,
      (⟨weierstrassRoot hf hdeg hω hu z.2 - ω,
          weierstrassRoot_sub hf hdeg hω hu z.2⟩ : maximalIdeal O)
        = b := by
  obtain ⟨y, hy, hysq⟩ := hsq b hroot
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  change weierstrassRoot hf hdeg hω hu hy - ω = b.1
  rw [weierstrassRoot_eq_of_eval_sq hf hdeg hω hu hy (by simp [b.2]) hysq.symm,
    add_sub_cancel_left]

variable [IsFractionRing O K]

/-- The `x`-fiber sum of a shifted root multiplicity over the maximal ideal collapses to a single
root multiplicity of the reduction: `∑_{w ∈ 𝔪} rootMult_{ι(c+w)}(N) = rootMult_{ρ c}(N_bar)`, by the
split zero count of `taylor c N`. -/
private theorem finsum_rootMultiplicity_shift {N : O[X]} {c : O} (hNρ : N.map (residue O) ≠ 0)
    (hsplit : (N.map (algebraMap O K)).Splits) :
    (∑ᶠ w : maximalIdeal O,
        ((N.map (algebraMap O K)).rootMultiplicity (algebraMap O K (c + w.1))))
      = (N.map (residue O)).rootMultiplicity (residue O c) := by
  set ι := algebraMap O K
  set ρ := residue O
  have hGred : (taylor c N).map ρ ≠ 0 := by
    rw [map_taylor]
    exact fun h0 ↦ hNρ ((taylor_eq_zero _ _).mp h0)
  have hGsplit : ((taylor c N).map ι).Splits := by rw [map_taylor]; exact hsplit.taylor _
  have hP3 := finsum_rootMultiplicity_maximalIdeal (K := K) (G := taylor c N) hGred hGsplit
  calc (∑ᶠ w : maximalIdeal O, ((N.map ι).rootMultiplicity (ι (c + w.1))))
      = ∑ᶠ w : maximalIdeal O, ((taylor c N).map ι).rootMultiplicity (ι w.1) := by
        refine finsum_congr fun w ↦ ?_
        rw [show ι (c + w.1) = ι w.1 + ι c by rw [map_add, add_comm], map_taylor,
          rootMultiplicity_taylor]
    _ = ((taylor c N).map ρ).rootMultiplicity 0 := hP3
    _ = (N.map ρ).rootMultiplicity (ρ c) := by rw [map_taylor, rootMultiplicity_taylor, zero_add]

/-- **Per-disk point sum, Weierstrass disk.** The total intrinsic multiplicity of `P + Q·y` at
the points of the Weierstrass residue disk of `(ω_bar, 0)` (parametrized by the `y`-coordinate
`z ∈ 𝔪`, with `x`-coordinate the Hensel root) equals the intrinsic order of the reduced
function at the reduced Weierstrass point. Requires the data to be split over `K` and the
squareness hypothesis `hsq`: `f`-values at the roots of the norm polynomial in the `x`-disk
are squares (automatic over the splitting field of the relevant data). -/
theorem finsum_emultiplicity_diskPointWeierstrass {f P Q : O[X]} {ω : O}
    [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
    [Fact (Squarefree (f.map (algebraMap O K)))]
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hu : IsUnit (f.derivative.eval ω)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hsq : ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits) :
    ∑ᶠ z : maximalIdeal O,
        (emultiplicity
          (pointIdeal (f.map (algebraMap O K))
            (algebraMap O K (weierstrassRoot hf hdeg hω hu z.2)) (algebraMap O K z.1))
          (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))})).toNat
      = (emultiplicity (pointIdeal (f.map (residue O)) (residue O ω) 0)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat := by
  classical
  set ι := algebraMap O K
  have hιinj : Function.Injective ι := IsFractionRing.injective O K
  set ρ := residue O
  have hN0 : P ^ 2 - f * Q ^ 2 ≠ 0 := fun h ↦ hN (by rw [h, Polynomial.map_zero])
  have hNK : (P ^ 2 - f * Q ^ 2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hN0
  have hnormK : ((⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)).re) ^ 2
      - (f.map ι) * ((⟨P.map ι, Q.map ι⟩ : HypRing K (f.map ι)).im) ^ 2
        = (P ^ 2 - f * Q ^ 2).map ι :=
    map_norm_poly ι f P Q
  have hbK (z : maximalIdeal O) :
      (ι z.1) ^ 2 = (f.map ι).eval (ι (weierstrassRoot hf hdeg hω hu z.2)) := by
    rw [← map_pow, ← weierstrassRoot_eval hf hdeg hω hu z.2, eval_map_apply]
  have hxneg (z : maximalIdeal O) :
      weierstrassRoot hf hdeg hω hu (neg_mem z.2) = weierstrassRoot hf hdeg hω hu z.2 :=
    weierstrassRoot_neg hf hdeg hω hu z.2
  -- abbreviations
  set hK : HypRing K (f.map ι) := ⟨P.map ι, Q.map ι⟩
  set E : maximalIdeal O → ℕ := fun z ↦ (emultiplicity
    (pointIdeal (f.map ι) (ι (weierstrassRoot hf hdeg hω hu z.2)) (ι z.1))
    (Ideal.span {hK})).toNat with hE
  set E' : maximalIdeal O → ℕ := fun z ↦ (emultiplicity
    (pointIdeal (f.map ι) (ι (weierstrassRoot hf hdeg hω hu z.2)) (ι z.1))
    (Ideal.span {star hK})).toNat with hE'
  set g : maximalIdeal O → ℕ := fun w ↦
    (((P ^ 2 - f * Q ^ 2).map ι).rootMultiplicity (ι (ω + w.1))) with hg
  have hgζ : ∀ z : maximalIdeal O,
      g ⟨weierstrassRoot hf hdeg hω hu z.2 - ω, weierstrassRoot_sub hf hdeg hω hu z.2⟩
        = ((P ^ 2 - f * Q ^ 2).map ι).rootMultiplicity
            (ι (weierstrassRoot hf hdeg hω hu z.2)) := fun z ↦ by
    rw [hg]
    simp only [add_sub_cancel]
  set z₀ : maximalIdeal O := ⟨0, Submodule.zero_mem _⟩ with hz₀
  set ζ : maximalIdeal O → maximalIdeal O := fun z ↦
    ⟨weierstrassRoot hf hdeg hω hu z.2 - ω, weierstrassRoot_sub hf hdeg hω hu z.2⟩ with hζ
  -- the pair identity at each parameter value
  have hpair (z : maximalIdeal O) : E z + E' z
      = if z = z₀ then 2 * g (ζ z) else g (ζ z) := by
    simp only [hE, hE', hζ, hgζ z]
    by_cases hz0 : z = z₀
    · have hz : ι z.1 = 0 := by rw [hz₀] at hz0; rw [hz0, map_zero]
      rw [ite_eq_left hz0, hz,
        toNat_emult_add_star_pointIdeal_weierstrass (hz ▸ hbK z) (hnormK ▸ hNK), hnormK]
    · rw [ite_eq_right hz0, toNat_emult_add_star_pointIdeal (hbK z)
        (fun h ↦ hz0 (Subtype.ext (hιinj (by rw [h, map_zero])))) (hnormK ▸ hNK), hnormK]
  -- the conjugate parameter gives the conjugate element
  have hEe (z : maximalIdeal O) : E ⟨-z.1, neg_mem z.2⟩ = E' z := by
    simp only [hE, hE', hxneg z, show ι (-z.1 : O) = -(ι z.1) from map_neg ι z.1,
      emultiplicity_pointIdeal_neg]
  -- the parametrization is two-to-one onto the `x`-fibers, with `g` as the base count
  have hgζsupp : (Function.support fun z : maximalIdeal O ↦ g (ζ z)).Finite := by
    rw [show (fun z : maximalIdeal O ↦ g (ζ z))
      = fun z ↦ ((P ^ 2 - f * Q ^ 2).map ι).rootMultiplicity
          (ι (weierstrassRoot hf hdeg hω hu z.2)) from funext hgζ]
    exact finite_support_rootMultiplicity_onCurve hNK hbK
  have hS : (∑ᶠ z, E z) = ∑ᶠ w : maximalIdeal O, g w := by
    refine finsum_eq_of_conj_pair_two_to_one (ζ := ζ) (e := fun z ↦ ⟨-z.1, neg_mem z.2⟩)
      (z₀ := z₀) (fun z ↦ Subtype.ext (by simpa [hζ] using hxneg z)) ?_
      (fun _ ↦ neg_eq_self_iff_maximalIdeal h2 _) ?_ hgζsupp neg_bijective_maximalIdeal
      hEe hpair
    · -- the fibers of the parametrization are the conjugate pairs
      intro z z' hzz
      have hx : weierstrassRoot hf hdeg hω hu z'.2 = weierstrassRoot hf hdeg hω hu z.2 := by
        simpa [hζ, sub_left_inj] using congrArg Subtype.val hzz
      have hsq' : z'.1 ^ 2 = z.1 ^ 2 := by
        rw [← weierstrassRoot_eval hf hdeg hω hu z'.2, ← weierstrassRoot_eval hf hdeg hω hu z.2, hx]
      have hprod : (z'.1 - z.1) * (z'.1 + z.1) = 0 := by linear_combination hsq'
      rcases mul_eq_zero.mp hprod with h | h
      · exact Or.inl (Subtype.ext (sub_eq_zero.mp h))
      · exact Or.inr (Subtype.ext (by simpa using add_eq_zero_iff_eq_neg.mp h))
    · -- a parameter value off the image carries no root
      intro b hb
      by_contra hgb
      exact hb (Set.mem_range.mpr (exists_param_of_isRoot hf hdeg hω hu hsq b (by
        by_contra hr
        rw [hg] at hgb
        exact hgb (rootMultiplicity_eq_zero hr))))
  -- the x-fiber sum via the split zero count
  have hT : (∑ᶠ w : maximalIdeal O, g w)
      = ((P ^ 2 - f * Q ^ 2).map ρ).rootMultiplicity (ρ ω) :=
    finsum_rootMultiplicity_shift hN hsplit
  -- identify with the intrinsic reduced order at the Weierstrass point
  have hbρ : (0 : ResidueField O) ^ 2 = (f.map ρ).eval (ρ ω) := by simp [eval_map_apply, hω]
  have hnormρ : ((⟨P.map ρ, Q.map ρ⟩ : HypRing (ResidueField O) (f.map ρ)).re) ^ 2
      - (f.map ρ) * ((⟨P.map ρ, Q.map ρ⟩ : HypRing (ResidueField O) (f.map ρ)).im) ^ 2
        = (P ^ 2 - f * Q ^ 2).map ρ :=
    map_norm_poly ρ f P Q
  rw [hS, hT, emultiplicity_pointIdeal_element_weierstrass_eq hbρ
    (z := (⟨P.map ρ, Q.map ρ⟩ : HypRing (ResidueField O) (f.map ρ)))
    (by rw [hnormρ]; exact hN), hnormρ, ENat.toNat_natCast]

end WeierstrassDiskSum

end ChabautyColeman
