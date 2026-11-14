/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.NumberField

import LeanPool.HyperellipticCurves.ForMathlib.Squarefree

/-!
# The classical arithmetic case: `ℚ` coefficients and a prime `p`

The theorems over `ℚ` are the case `A = ℤ`, `K = ℚ`, `v = (p)` of the theorems of
`LeanPool.HyperellipticCurves.Count.NumberField`: the residue field of `(p)` is `ZMod p` and the
ramification index is `1` (it is at most `[ℚ : ℚ] = 1`), so the prime condition
`p > 2r + e + 1` reads `p > 2r + 2`. A polynomial `f : ℚ[X]` is `p`-integral when `d·f` has
integer coefficients for some `d` prime to `p`; its reduction mod `p` is then
`d_bar⁻¹·(d·f)‾`, and the reduced curve is the model `d·y² = (d·f)(x)` over `𝔽_p`. This file
performs that specialization: the point counts transport along the residue field
`ℤ_(p) ⧸ (p) ≃+* ZMod p` (`ChabautyColeman.NumberFieldBase.encard_solutionPairs_map`), and
squarefreeness along the induced polynomial-ring isomorphism (`Squarefree.map`). The
finiteness of the rational solution set is not restated here: it is the instantiation
`A = ℤ` of `ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField`.

## Main statements

* `ChabautyColeman.main_affine_rat_of_rank_le` (blueprint `thm:main`): for an odd-degree
  hyperelliptic curve `C : y² = f(x)` over `ℚ` (`HyperellipticCurve ℚ`), `p`-integral with
  squarefree reduction mod a prime `p`, if `rk Cl(ℚ[x][y]/(y² - f)) ≤ r` with `r < g` and
  `p > 2r + 2`, then `#{(x,y) ∈ ℚ² : y² = f(x)} + 1 ≤ #{(x,y) ∈ 𝔽_p² : d_bar·y² = (d·f)‾(x)} + 1 +
  2r`.
* `ChabautyColeman.separable_of_squarefree_twist`: squarefree reduction of `d·f` makes `f`
  separable, so a monic odd-degree `f` with good reduction at `p` is a curve
  (`HyperellipticCurve.ofMonicOdd`); this is how the comparator builds the curve.
* `ChabautyColeman.main_affine_int_of_rank_le`: the case `d = 1` of an integer polynomial
  `f : ℤ[X]`, with the reduced curve `y² = f_bar(x)`.
* `ChabautyColeman.main_affine_int`: its `r = g - 1` case, Coleman's bound `2g - 2` for a
  prime `p ≥ deg f`.
-/

@[expose] public section

open Polynomial IsLocalRing IsDedekindDomain

open scoped TensorProduct

namespace ChabautyColeman

open NumberFieldBase

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The prime `(p)` of `ℤ` as a point of the height-one spectrum of `ℤ`. -/
def intPrime : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

@[simp]
theorem intPrime_asIdeal : (intPrime p).asIdeal = Ideal.span {(p : ℤ)} := rfl

variable (p) in
/-- The residue field of the ring of `p`-integral rational numbers is `ZMod p`. -/
noncomputable def residueFieldEquivZMod :
    ResidueField ((intPrime p).valuationSubringAtPrime ℚ) ≃+* ZMod p :=
  (residueFieldEquiv ℚ (intPrime p)).symm.trans (Int.quotientSpanNatEquivZMod p)

variable (p) in
theorem residueFieldEquivZMod_comp :
    (residueFieldEquivZMod p : ResidueField _ →+* ZMod p).comp
      ((residue _).comp (algebraMap ℤ ((intPrime p).valuationSubringAtPrime ℚ)))
      = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

variable {F : ℤ[X]} {d : ℤ}

theorem notMem_intPrime_of_not_dvd (hd : ¬ (p : ℤ) ∣ d) : d ∉ (intPrime p).asIdeal :=
  fun h ↦ hd (Ideal.mem_span_singleton.mp h)

/-- **The reduction of the `p`-integral model of `f = d⁻¹·F`**, transported to `ZMod p`: it is
`d_bar⁻¹·F_bar`. -/
theorem integralModel_map_residue_map_equiv (hd : ¬ (p : ℤ) ∣ d) :
    ((integralModel ℚ F (notMem_intPrime_of_not_dvd hd)).map (residue _)).map
        (residueFieldEquivZMod p : ResidueField ((intPrime p).valuationSubringAtPrime ℚ) →+* ZMod p)
      = Polynomial.C (d : ZMod p)⁻¹ * F.map (Int.castRingHom (ZMod p)) := by
  have hed : (residueFieldEquivZMod p : ResidueField _ →+* ZMod p)
      (residue _ (algebraMap ℤ ((intPrime p).valuationSubringAtPrime ℚ) d)) = d :=
    RingHom.congr_fun (residueFieldEquivZMod_comp p) d
  rw [integralModel_map_residue, Polynomial.map_mul, map_C, map_inv₀, map_map,
    residueFieldEquivZMod_comp, hed]

/-- **Squarefree reduction of the twisted model** `d_bar·y² = F_bar(x)` is squarefree reduction of
the
`p`-integral model of `f = d⁻¹·F`. -/
theorem squarefree_integralModel_map_residue (hd : ¬ (p : ℤ) ∣ d)
    (hsq : Squarefree (F.map (Int.castRingHom (ZMod p)))) :
    Squarefree ((integralModel ℚ F (notMem_intPrime_of_not_dvd hd)).map (residue _)) := by
  have hd0 : (d : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine (MulEquiv.squarefree_iff (Polynomial.mapEquiv (residueFieldEquivZMod p))).mp ?_
  change Squarefree (((integralModel ℚ F _).map (residue _)).map
    (residueFieldEquivZMod p : ResidueField ((intPrime p).valuationSubringAtPrime ℚ) →+* ZMod p))
  rw [integralModel_map_residue_map_equiv hd]
  exact ((associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (inv_ne_zero hd0)))).squarefree_iff).mpr hsq

/-- **Good reduction at `p` makes `f` separable**: a monic `f : ℚ[X]` with `d·f = F ∈ ℤ[X]`,
`p ∤ d` and squarefree `F_bar` is separable, hence defines a curve over `ℚ`
(`HyperellipticCurve.ofMonicOdd`). -/
theorem separable_of_squarefree_twist {f : ℚ[X]} (hf : f.Monic) (hd : ¬ (p : ℤ) ∣ d)
    (hF : F.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f)
    (hsq : Squarefree (F.map (Int.castRingHom (ZMod p)))) : f.Separable := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · rw [hf.natDegree_eq_zero.mp h0]
    exact separable_one
  exact separable_of_squarefree_map_residue hf h0
    (integralModel_map_algebraMap (notMem_intPrime_of_not_dvd hd) hF)
    (squarefree_integralModel_map_residue hd hsq)

/-- **The Chabauty–Coleman bound over `ℚ`** (blueprint `thm:main`): for an odd-degree
hyperelliptic curve `C : y² = f(x)` over `ℚ` that is `p`-integral — `d·f = F` with `F : ℤ[X]` and
`p ∤ d` — with squarefree reduction mod the prime `p`, if the `ℚ`-rank of the Jacobian
`Cl(ℚ[x][y]/(y² - f))` is at most `r < g` and `p > 2r + 2`, then the number of affine rational
points of `C`, plus one for the point at infinity, is at most the number of affine points of the
reduced model `d_bar·y² = F_bar(x)` over `𝔽_p`, plus one, plus `2r`.

The reduction of `f` mod `p` is `d_bar⁻¹·F_bar`, so the reduced model is the curve `y² = f_bar(x)`;
the rank is `ChabautyColeman.HypJac.rank` of the curve over `ℚ`. -/
theorem main_affine_rat_of_rank_le (C : HyperellipticCurve ℚ) [C.IsOdd] (hd : ¬ (p : ℤ) ∣ d)
    (hF : F.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * C.f)
    (hsq : Squarefree (F.map (Int.castRingHom (ZMod p)))) {r : ℕ} (hpr : 2 * r + 2 < p)
    (hrk : HypJac.rank ℚ C.f ≤ r) (hrg : r < C.genus) :
    {q : ℚ × ℚ | q.2 ^ 2 = C.f.eval q.1}.encard + 1
      ≤ ({q : ZMod p × ZMod p
            | (d : ZMod p) * q.2 ^ 2 = (F.map (Int.castRingHom (ZMod p))).eval q.1}.encard + 1)
        + 2 * r := by
  set v := intPrime p
  have hp𝔭 : ((p : ℕ) : ℤ) ∈ v.asIdeal := Ideal.mem_span_singleton_self _
  have hd' : d ∉ v.asIdeal := notMem_intPrime_of_not_dvd hd
  -- the residue characteristic of `v` is `p`
  have hchar : CharP (ℤ ⧸ v.asIdeal) p :=
    charP_quotient p (Ideal.IsMaximal.ne_top inferInstance) hp𝔭
  have hring : ringChar (ℤ ⧸ v.asIdeal) = p := ringChar.eq _ p
  have hd0 : (d : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- the prime condition: the ramification index is at most `[ℚ : ℚ] = 1`
  have hpr' : 2 * r + Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal + 1
      < ringChar (ResidueField (v.valuationSubringAtPrime ℚ)) := by
    rw [ringChar_residueField, hring, under_eq_span_ringChar v.asIdeal, hring]
    have := ramificationIdx'_le_finrank p v.asIdeal hp𝔭
    rw [Module.finrank_self] at this
    lia
  have h := main_affine_numberField C (integralModel_map_algebraMap hd' hF)
    (squarefree_integralModel_map_residue hd hsq) hpr' hrk hrg
  rw [← encard_solutionPairs_map (φ := (residueFieldEquivZMod p : ResidueField _ →+* ZMod p))
    (residueFieldEquivZMod p).bijective, integralModel_map_residue_map_equiv hd] at h
  have hset : {q : ZMod p × ZMod p
      | q.2 ^ 2 = (Polynomial.C (d : ZMod p)⁻¹ * F.map (Int.castRingHom (ZMod p))).eval q.1}
      = {q | (d : ZMod p) * q.2 ^ 2 = (F.map (Int.castRingHom (ZMod p))).eval q.1} :=
    Set.ext fun q ↦ by simp [eval_mul, eq_inv_mul_iff_mul_eq₀ hd0]
  rwa [hset] at h

/-- **The Chabauty–Coleman bound over `ℤ`** (blueprint `thm:main`): for a monic `f : ℤ[X]` of
odd degree whose reduction mod a prime `p` is squarefree, if the `ℚ`-rank of the Jacobian
`Cl(ℚ[x][y]/(y² - f))` is at most `r < ⌊deg f / 2⌋` and `p > 2r + 2`, then the number of
affine rational points of `y² = f(x)`, plus one for the point at infinity, is at most the
corresponding count over `𝔽_p` plus `2r`: the case `d = 1` of
`ChabautyColeman.main_affine_rat_of_rank_le`.

This is the improvement of `ChabautyColeman.main_affine_int` (which is the case `r = g - 1`):
the bound is governed by the rank, not by the genus, and the prime only has to exceed
`2r + 2` rather than `deg f`. -/
theorem main_affine_int_of_rank_le {f : ℤ[X]} (hf : f.Monic) [Fact (Odd f.natDegree)]
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) {r : ℕ} (hpr : 2 * r + 2 < p)
    (hrk : HypJac.rank ℚ (f.map (algebraMap ℤ ℚ)) ≤ r) (hrg : r < genus f) :
    {q : ℚ × ℚ | q.2 ^ 2 = (f.map (Int.castRingHom ℚ)).eval q.1}.encard + 1
      ≤ ({q : ZMod p × ZMod p
            | q.2 ^ 2 = (f.map (Int.castRingHom (ZMod p))).eval q.1}.encard + 1)
        + 2 * r := by
  have hd : ¬ (p : ℤ) ∣ (1 : ℤ) := mod_cast (Fact.out : p.Prime).not_dvd_one
  have hF : f.map (Int.castRingHom ℚ) = Polynomial.C ((1 : ℤ) : ℚ) * f.map (algebraMap ℤ ℚ) := by
    simp
  have hodd : Odd (f.map (algebraMap ℤ ℚ)).natDegree := by rw [hf.natDegree_map]; exact Fact.out
  have hrg' : r < ((f.map (algebraMap ℤ ℚ)).natDegree / 2 : ℕ) := by rwa [hf.natDegree_map]
  have h := main_affine_rat_of_rank_le
    (.ofMonicOdd (hf.map _) hodd (separable_of_squarefree_twist (hf.map _) hd hF hsq)) hd hF hsq
    hpr hrk hrg'
  simpa using h

/-- **The Chabauty–Coleman bound over `ℤ`, Coleman's form** (blueprint `thm:main`): for a
monic `f : ℤ[X]` of odd degree whose reduction mod a prime `p ≥ deg f` is squarefree, if the
`ℚ`-rank of the Jacobian `Cl(ℚ[x][y]/(y² - f))` is less than the genus `⌊deg f / 2⌋`, then the
number of affine rational points of `y² = f(x)`, plus one for the point at infinity, is at
most the corresponding count over `𝔽_p` plus `2·genus - 2`.

This is `ChabautyColeman.main_affine_int_of_rank_le` at the largest admissible rank
`r = g - 1`, which is why the prime condition `p ≥ deg f = 2g + 1` appears. -/
theorem main_affine_int {f : ℤ[X]} (hf : f.Monic) [Fact (Odd f.natDegree)]
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) (hdegp : f.natDegree ≤ p)
    (hrk : HypJac.rank ℚ (f.map (algebraMap ℤ ℚ)) < genus f) :
    {q : ℚ × ℚ | q.2 ^ 2 = (f.map (Int.castRingHom ℚ)).eval q.1}.encard + 1
      ≤ ({q : ZMod p × ZMod p
            | q.2 ^ 2 = (f.map (Int.castRingHom (ZMod p))).eval q.1}.encard + 1)
        + (2 * genus f - 2 : ℕ) := by
  -- a cardinal below a natural number is a natural number: the rank is at most some `r < g`
  obtain ⟨m, hm⟩ := id (Fact.out : Odd f.natDegree)
  have hg : genus f = m := genus_eq_of_natDegree hm
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp (hrk.trans Cardinal.natCast_lt_aleph0)
  rw [hr, Nat.cast_lt] at hrk
  refine (main_affine_int_of_rank_le hf hsq (by lia) hr.le hrk).trans ?_
  gcongr
  exact_mod_cast (by lia : 2 * r ≤ 2 * genus f - 2)

end ChabautyColeman

end
