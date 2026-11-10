/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.Lam
public import LeanPool.HyperellipticCurves.Log.Analytic.OmegaPrime
public import LeanPool.HyperellipticCurves.Series.ScaledLogEval

import LeanPool.HyperellipticCurves.ForMathlib.PadicValNat
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Coleman integral value of the logarithm (numerical clause (b))

The abelian logarithm `ChabautyColeman.Lam` of a kernel class `c` is defined over the DVR
`O` via the integral `π`-scaled logarithm. This file realizes it as the `p`-adic
convergent value of the formal logarithm over the valued fraction field `K = FractionRing O`
(`LeanPool.HyperellipticCurves.Series.FractionTopology`), the first step toward the numerical form
of clause
(b) of `thm:omega-prime-global`.

`ChabautyColeman.hasSum_algebraMap_Lam` transports `Lam` to `K`: the image of `Lam c i` is
the convergent sum of the honest logarithm series of `F_τ` at the chart coordinates of
`c + τ`. Combined with the substitution identity `ChabautyColeman.subst_log_eq_antideriv`
(the antiderivative of `ω′` is `Λ(ζ(z))`) and the disk-point identification of the chart
coordinates with `ChabautyColeman.phiZeta` evaluated at `z₀`, this expresses `Lam` as the
Coleman integral of `ω′` from the disk center.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries Filter Topology
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries WithZero

namespace ChabautyColeman

section SumOfCoeff

variable {R ι : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Fintype ι]

/-- A finite linear combination of power series whose coefficient series converge at `z`
converges at `z` to the same combination of the values. -/
theorem hasSum_sum_mul_coeff {F : ι → PowerSeries R} {L : ι → R} {z : R} (cs : ι → R)
    (h : ∀ i, HasSum (fun k ↦ PowerSeries.coeff k (F i) * z ^ k) (L i)) :
    HasSum (fun k : ℕ ↦ (∑ i, cs i * PowerSeries.coeff k (F i)) * z ^ k) (∑ i, cs i * L i) := by
  simpa only [Finset.sum_mul, mul_assoc] using
    hasSum_sum (s := Finset.univ) (f := fun i k ↦ cs i * (PowerSeries.coeff k (F i) * z ^ k))
      fun i _ ↦ (h i).mul_left (cs i)

end SumOfCoeff

section PowerSeriesProd

/-- Coefficients of a `Finsupp.prod` of powers commute with `PowerSeries.map`: pushing a ring
map `φ` through the product turns each coefficient into the `φ`-image of the corresponding
coefficient over the base ring. -/
theorem coeff_finsuppProd_map {R S ι : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (ζ : ι → R⟦X⟧) (d : ι →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (d.prod fun s j ↦ (PowerSeries.map φ (ζ s)) ^ j)
      = φ (PowerSeries.coeff k (d.prod fun s j ↦ ζ s ^ j)) := by
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_finsuppProd]
  exact Finsupp.prod_congr fun s _ ↦ (map_pow _ _ _).symm

/-- If every `ζ s` has vanishing constant term, then `X ^ d.degree` divides the `Finsupp.prod`
`∏ s, ζ s ^ d s`, so all its coefficients below `d.degree` vanish. -/
theorem coeff_finsuppProd_eq_zero_of_lt_degree {R ι : Type*} [CommSemiring R] [Finite ι]
    {ζ : ι → R⟦X⟧} (hζ0 : ∀ s, PowerSeries.constantCoeff (ζ s) = 0) (d : ι →₀ ℕ) {k : ℕ}
    (hk : k < d.degree) : PowerSeries.coeff k (d.prod fun s j ↦ ζ s ^ j) = 0 := by
  have := Fintype.ofFinite ι
  have hprodf : (d.prod fun s j ↦ ζ s ^ j) = ∏ s, ζ s ^ (d s) :=
    Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)
  have hdvd : (PowerSeries.X : R⟦X⟧) ^ d.degree ∣ d.prod fun s j ↦ ζ s ^ j := by
    rw [hprodf, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ ↦
      pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (hζ0 s)) _
  exact PowerSeries.X_pow_dvd_iff.mp hdvd k hk

end PowerSeriesProd

section Summability

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O] [CharZero (FractionRing O)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {π : O} {p e : ℕ}

/-- **Joint summability of the Coleman-integral double family** over `K = FractionRing O`.
For a formal group law `Φ`, an integral path `ζ` (vanishing constant term), and a disk point
`z₀ ∈ 𝔪 = (π)`, the family `(d,k) ↦ Λ_d · coeff_k(ζ_K^d) · (f z₀)^k` (with `Λ = (Φ.map f).log`)
is summable in `K`. The `p`-denominators of `Λ_d` cancel against `(f z₀)^{deg d}` (since
`z₀ ∈ (π)`), making each term the image of an `O`-element in `𝔪^{k - e·v_p(deg d)}`; the
exponent tends to `∞` cofinitely, so the family tends to `0` cofinitely and is summable. -/
theorem summable_logSubstFamily (Φ : FormalGroupLaw O ι) (hram : IsUniformizer π p e)
    (hpe : e + 1 < p) {ζ : ι → O⟦X⟧}
    (hζ0 : ∀ s, PowerSeries.constantCoeff (ζ s) = 0) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (i : ι) :
    Summable (fun dk : (ι →₀ ℕ) × ℕ ↦
      coeff dk.1 ((Φ.map (algebraMap O (FractionRing O))).log i)
        * PowerSeries.coeff dk.2
            (dk.1.prod fun s j ↦ (PowerSeries.map (algebraMap O (FractionRing O)) (ζ s)) ^ j)
        * (algebraMap O (FractionRing O) z₀) ^ dk.2) := by
  set f := algebraMap O (FractionRing O)
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective O (FractionRing O)
  have hfp : f (p : O) ≠ 0 := algebraMap_natCast_prime_ne_zero hram.prime
  obtain ⟨w, hw⟩ : π ∣ z₀ := hram.mem_iff.mp hz₀
  set ηd : (ι →₀ ℕ) → O⟦X⟧ := fun d ↦ d.prod fun s j ↦ ζ s ^ j
  have hcoeffK (d : ι →₀ ℕ) (k : ℕ) :
      PowerSeries.coeff k (d.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j)
        = f (PowerSeries.coeff k (ηd d)) := coeff_finsuppProd_map f ζ d k
  have hord (d : ι →₀ ℕ) {k : ℕ} (hk : k < d.degree) : PowerSeries.coeff k (ηd d) = 0 :=
    coeff_finsuppProd_eq_zero_of_lt_degree hζ0 d hk
  set g : (ι →₀ ℕ) × ℕ → O := fun dk ↦
    coeff dk.1 (Φ.scaledLog hram hpe f hfp i) * PowerSeries.coeff dk.2 (ηd dk.1)
      * w ^ dk.2 * π ^ (dk.2 - dk.1.degree) with hg
  have hbfg : (fun dk ↦ coeff dk.1 ((Φ.map f).log i)
        * PowerSeries.coeff dk.2
            (dk.1.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j) * f z₀ ^ dk.2)
      = fun dk ↦ f (g dk) := by
    funext ⟨d, k⟩
    simp only [hg, hcoeffK]
    by_cases hk : d.degree ≤ k
    · rw [map_mul, map_mul, map_mul, map_pow, map_pow, Φ.coeff_scaledLog_map hram hpe hfp i d,
        hw, map_mul, mul_pow, ← pow_mul_pow_sub (f π) hk]
      ring
    · simp [hord d (not_le.mp hk)]
  rw [hbfg]
  have hmem_scaledLog (d : ι →₀ ℕ) :
      coeff d (Φ.scaledLog hram hpe f hfp i)
        ∈ maximalIdeal O ^ (d.degree - e * padicValNat p d.degree) := by
    obtain ⟨c, hcmem, hc⟩ := Φ.coeff_log_map_scale hram hpe f hfp i d
    rwa [hfinj ((Φ.coeff_scaledLog_map hram hpe hfp i d).trans hc)]
  set ex : (ι →₀ ℕ) × ℕ → ℕ :=
    fun dk ↦ max dk.2 dk.1.degree - e * padicValNat p dk.1.degree with hex
  have hgmem : ∀ dk, g dk ∈ maximalIdeal O ^ ex dk := by
    intro ⟨d, k⟩
    by_cases hk : d.degree ≤ k
    · have hvle := Nat.mul_padicValNat_le hpe d.degree
      have h1 : coeff d (Φ.scaledLog hram hpe f hfp i)
          * PowerSeries.coeff k (ηd d) * w ^ k
          ∈ maximalIdeal O ^ (d.degree - e * padicValNat p d.degree) :=
        Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hmem_scaledLog d))
      have h2 : π ^ (k - d.degree) ∈ maximalIdeal O ^ (k - d.degree) :=
        hram.mem_pow_iff.mpr dvd_rfl
      have h3 := Ideal.mul_mem_mul h1 h2
      rw [← pow_add] at h3
      simp only [hex, max_eq_left hk]
      exact Ideal.pow_le_pow_right (by lia) h3
    · have hz : g (d, k) = 0 := by
        simp only [hg, hord d (not_le.mp hk), mul_zero, zero_mul]
      rw [hz]
      exact Submodule.zero_mem _
  have hetendsto : Tendsto ex cofinite atTop := by
    rw [tendsto_atTop]
    intro N
    have hsub : Tendsto (fun d : ι →₀ ℕ ↦ d.degree - e * padicValNat p d.degree) cofinite atTop :=
      (Nat.tendsto_sub_mul_padicValNat_atTop hpe).comp Finsupp.tendsto_degree_cofinite
    have hDa : {d : ι →₀ ℕ | d.degree - e * padicValNat p d.degree < N}.Finite := by
      have h := hsub.eventually_ge_atTop N
      rw [Filter.eventually_cofinite] at h
      simpa only [not_le] using h
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset
      (hDa.toFinset ×ˢ Finset.range (N + hDa.toFinset.sup fun d ↦ d.degree)).finite_toSet ?_
    intro ⟨d, k⟩ hdk
    simp only [Set.mem_ofPred_eq, not_le, hex] at hdk
    have hvle := Nat.mul_padicValNat_le hpe d.degree
    have hdD : d ∈ hDa.toFinset := by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; lia
    have hdeg_le : d.degree ≤ hDa.toFinset.sup fun d ↦ d.degree := Finset.le_sup hdD
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨hdD, by lia⟩
  have htg : Tendsto g cofinite (𝓝 (0 : O)) :=
    (Fact.out : IsAdic (maximalIdeal O)).tendsto_zero_of_mem_pow hgmem hetendsto
  have htb : Tendsto (fun dk ↦ f (g dk)) cofinite (𝓝 (0 : FractionRing O)) := by
    have hc := (continuous_algebraMap (O := O)).continuousAt (x := (0 : O))
    rw [ContinuousAt, map_zero] at hc
    exact hc.comp htg
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htb

/-- **Fubini reindexing of the Coleman double family** (numerical clause (b) of
`thm:omega-prime-global`): given the multi-index convergence `hmulti` of the honest logarithm
series at the endpoint `ζ(z₀)`, the single-index series `∑_k coeff_k(subst ζ_K Λ_K) · (f z₀)^k`
converges to the *same* value `L`. This is the eval-of-substitution identity
`eval_{z₀}(subst ζ Λ) = eval_{ζ(z₀)}Λ` over `K = FractionRing O`, obtained by summing the
jointly-summable double family (`ChabautyColeman.summable_logSubstFamily`) in the two orders:
summing the fibre `k` first recovers the endpoint value (`hmulti`), summing the fibre `d`
first recovers the substitution coefficients. Since `subst ζ_K Λ_K` is the antiderivative of
`ω′` (`ChabautyColeman.subst_log_eq_antideriv`), this expresses `L` as the `p`-adic Coleman
integral of `ω′` from the disk center. -/
theorem hasSum_coeff_subst_log (Φ : FormalGroupLaw O ι) (hram : IsUniformizer π p e)
    (hpe : e + 1 < p) {ζ : ι → O⟦X⟧}
    (hζ0 : ∀ s, PowerSeries.constantCoeff (ζ s) = 0) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    {L : FractionRing O} (i : ι)
    (hmulti : HasSum (fun d : ι →₀ ℕ ↦
        coeff d ((Φ.map (algebraMap O (FractionRing O))).log i)
          * d.prod fun s j ↦ algebraMap O (FractionRing O) (PSeries.eval z₀ (ζ s)) ^ j) L) :
    HasSum (fun k : ℕ ↦ PowerSeries.coeff k
        (MvPowerSeries.subst (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (ζ s))
          ((Φ.map (algebraMap O (FractionRing O))).log i))
        * algebraMap O (FractionRing O) z₀ ^ k) L := by
  set f := algebraMap O (FractionRing O)
  set Λ := (Φ.map f).log i
  set b : (ι →₀ ℕ) × ℕ → FractionRing O := fun dk ↦
    coeff dk.1 Λ
      * PowerSeries.coeff dk.2 (dk.1.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j)
      * f z₀ ^ dk.2 with hb
  have hsummable : Summable b := summable_logSubstFamily Φ hram hpe hζ0 hz₀ i
  have hbsum : HasSum b (∑' x, b x) := hsummable.hasSum
  have hsubst : HasSubst (fun s ↦ PowerSeries.map f (ζ s)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by
      change PowerSeries.constantCoeff (PowerSeries.map f (ζ s)) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hζ0 s, map_zero]
  -- per-`d` fibre: sum over `k` recovers the honest-log summand at the endpoint `ζ(z₀)`
  have hIII (d : ι →₀ ℕ) : HasSum (fun k ↦ b (d, k))
      (coeff d Λ * d.prod fun s j ↦ f (PSeries.eval z₀ (ζ s)) ^ j) := by
    have hval : f (PSeries.eval z₀ (d.prod fun s j ↦ (ζ s) ^ j))
        = d.prod fun s j ↦ f (PSeries.eval z₀ (ζ s)) ^ j := by
      have key : (f.comp (PSeries.evalRingHom hz₀)) (d.prod fun s j ↦ (ζ s) ^ j)
          = d.prod fun s j ↦ (f.comp (PSeries.evalRingHom hz₀)) (ζ s) ^ j := by
        rw [map_finsuppProd]; exact Finsupp.prod_congr fun s _ ↦ map_pow _ _ _
      simpa only [RingHom.comp_apply, PSeries.evalRingHom_apply] using key
    rw [← hval]
    have hO' : HasSum
        (fun k ↦ PowerSeries.coeff k (d.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j) * f z₀ ^ k)
        (f (PSeries.eval z₀ (d.prod fun s j ↦ (ζ s) ^ j))) :=
      ((PSeries.hasSum_eval hz₀ (d.prod fun s j ↦ (ζ s) ^ j)).map f continuous_algebraMap).congr_fun
        fun k ↦ by rw [Function.comp_apply, map_mul, map_pow, coeff_finsuppProd_map f ζ]
    refine (hO'.mul_left (coeff d Λ)).congr_fun fun k ↦ ?_
    simp only [hb, mul_assoc]
  have hgd : HasSum (fun d ↦ coeff d Λ * d.prod fun s j ↦ f (PSeries.eval z₀ (ζ s)) ^ j)
      (∑' x, b x) := hbsum.prod_fiberwise hIII
  have hLeq : (∑' x, b x) = L := hgd.unique hmulti
  -- per-`k` fibre: sum over `d` recovers the substitution coefficient (finite support)
  have hIV (k : ℕ) : HasSum (fun d ↦ b (d, k))
      (PowerSeries.coeff k (MvPowerSeries.subst (fun s ↦ PowerSeries.map f (ζ s)) Λ)
        * f z₀ ^ k) := by
    have hfin := coeff_subst_finite hsubst Λ (Finsupp.single () k)
    have hasum : HasSum
        (fun d ↦ coeff d Λ • MvPowerSeries.coeff (Finsupp.single () k)
          (d.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j))
        (MvPowerSeries.coeff (Finsupp.single () k)
          (MvPowerSeries.subst (fun s ↦ PowerSeries.map f (ζ s)) Λ)) := by
      have hs : Summable (fun d ↦ coeff d Λ • MvPowerSeries.coeff (Finsupp.single () k)
          (d.prod fun s j ↦ (PowerSeries.map f (ζ s)) ^ j)) := summable_of_hasFiniteSupport hfin
      have h := hs.hasSum
      rwa [tsum_eq_finsum hfin, ← coeff_subst hsubst Λ (Finsupp.single () k)] at h
    refine (hasum.mul_right (f z₀ ^ k)).congr_fun fun d ↦ ?_
    simp only [hb, mul_assoc, smul_eq_mul, PowerSeries.coeff_coeToMvPowerSeries]
  have hswap : HasSum (b ∘ Equiv.prodComm ℕ (ι →₀ ℕ)) (∑' x, b x) :=
    (Equiv.prodComm ℕ (ι →₀ ℕ)).hasSum_iff.mpr hbsum
  have hfinal := hswap.prod_fiberwise hIV
  rwa [hLeq] at hfinal

end Summability

section LamTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ}

/-- **The logarithm value transports to the fraction field** (toward `thm:omega-prime-global`,
numerical clause (b)): the image of `Lam c i` in `K = FractionRing O` is the convergent
`p`-adic sum of the honest logarithm series of `F_τ` at the chart coordinates
`(J1_equiv_polydisk c).1` of `c + τ`. This is the pushforward of the integral `O`-level
value along the continuous inclusion `O ↪ K`. -/
theorem hasSum_algebraMap_Lam (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) (i : Fin n) :
    HasSum (fun d' : Fin n →₀ ℕ ↦
        coeff d' ((ftauFoldFGLFrac hu hne hv hw hbez hf hfdeg hroot hcc ha hbv hd hram
            hsplit hunit).log i)
          * d'.prod fun s j ↦ algebraMap O (FractionRing O)
              ((J1_equiv_polydisk hu hne hv hw hbez hf hdeg hfdeg hsq c).1 s) ^ j)
      (algebraMap O (FractionRing O)
        (Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c i)) := by
  have hfp : algebraMap O (FractionRing O) (p : O) ≠ 0 :=
    algebraMap_natCast_prime_ne_zero hram.prime
  have H := hasSum_algebraMap_evalT_scaledLog
    (ftauFoldFGL hu hne hv hw hbez hf
      ((hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg) hroot hcc ha hbv
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing hsplit hunit) hram hpe hfp
    (kerScaledCoords hu hne hv hw hbez hf hdeg hfdeg hsq hram c) i
  simp only [kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram c] at H
  exact H

end LamTransport

end ChabautyColeman

end
