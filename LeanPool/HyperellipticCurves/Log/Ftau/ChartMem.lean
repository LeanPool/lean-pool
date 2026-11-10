/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.ReduceCommutes
public import LeanPool.HyperellipticCurves.Log.Fold.FtauFoldBasic
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauAssoc

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Chart membership: the polydisk parametrizes the kernel of the reduction
(blueprint `thm:chart-mem`)

For a `τ`-datum `(u, v)` in good position (with certificate pack, as provided by
`ChabautyColeman.TauData`), the map sending a polydisk point `z ∈ 𝔪ⁿ` to the chart class
at `z` translated by `-τ` is a bijection onto the kernel of the reduction homomorphism
`ChabautyColeman.redJHom` (`ChabautyColeman.polydiskToKer_bijective`,
`ChabautyColeman.J1_equiv_polydisk`), and transports the formal group law `F_τ` to the
multiplication of the Jacobian (`ChabautyColeman.polydiskToKer_eval_FtauFold`).

Forward direction (`ChabautyColeman.exists_chartClass_eq`): a class with trivial
reduction, translated by `τ`, reduces to the reduced `τ`-datum
(`ChabautyColeman.redJ_tauClass`, via `ChabautyColeman.redJ_mk0_mumford`), so
`ChabautyColeman.red_reducedRep_eq` descends its reduced representative integrally; the
descended datum is the evaluated chart datum at explicit coordinates — the `u`-part by
the shape of `chartU` (`ChabautyColeman.exists_chartU_map_evalRingHom_eq`), the `v`-part
by uniqueness of the square root (`ChabautyColeman.chartV_map_evalRingHom_eq`, with a
Bézout certificate lifted from the `τ`-datum's). Conversely every chart class reduces to
the reduced `τ`-datum (`ChabautyColeman.redJ_chartClass`), so its `-τ`-translate lies in
the kernel, and injectivity is uniqueness of reduced Mumford representatives.

The restriction to Frobenius-fixed points (the `J¹(ℚ_p)`-clause of `thm:chart-mem`) is
deferred to the counting chapter, alongside the instantiation of `thm:J1-index`.
-/

@[expose] public section

open Polynomial nonZeroDivisors IsLocalRing

namespace ChabautyColeman

section Tau

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O] {f u v w : O[X]}
  (hu : u.Monic) (hw : v ^ 2 - f = u * w)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- The class of the `τ`-datum over the fraction field. -/
noncomputable def tauClass :
    ClassGroup (HypRing (FractionRing O) (f.map (algebraMap O (FractionRing O)))) :=
  ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
      (u.map (algebraMap O (FractionRing O))) (v.map (algebraMap O (FractionRing O))),
    mumfordIdeal_mem_nonZeroDivisors (f.map (algebraMap O (FractionRing O)))
      (hu.map (algebraMap O (FractionRing O))).ne_zero
      (v.map (algebraMap O (FractionRing O)))⟩

include hw in
/-- The negated `τ`-datum class is the inverse of the `τ`-datum class. -/
theorem tauClass_mul_tauClassNeg :
    tauClass (f := f) (v := v) hu * tauClassNeg (f := f) (v := v) hu = 1 := by
  classical
  set K := FractionRing O
  set fK := f.map (algebraMap O K)
  have hsf : Squarefree fK := Fact.out
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have hdvdK : u.map (algebraMap O K) ∣ (v.map (algebraMap O K)) ^ 2 - fK := by
    have h := Polynomial.map_dvd (algebraMap O K) (⟨w, hw⟩ : u ∣ v ^ 2 - f)
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  rw [tauClass, tauClassNeg, ← MonoidHom.map_mul ClassGroup.mk0]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  change (mumfordIdeal fK (u.map (algebraMap O K)) (v.map (algebraMap O K))
    * mumfordIdeal fK (u.map (algebraMap O K)) (-(v.map (algebraMap O K)))).IsPrincipal
  rw [← map_star_mumfordIdeal, mumfordIdeal_mul_map_star fK hsf h2 hdvdK]
  exact ⟨_, rfl⟩

include hw in
/-- The negated `τ`-datum class is the inverse of the `τ`-datum class, inverse form. -/
theorem tauClassNeg_eq_inv :
    tauClassNeg (f := f) (v := v) hu = (tauClass (f := f) (v := v) hu)⁻¹ :=
  eq_inv_of_mul_eq_one_right (tauClass_mul_tauClassNeg hu hw)

end Tau

section Eval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- The evaluated chart `u`-polynomial is the `τ`-datum `u` displaced by the
coordinates. -/
theorem chartU_map_evalRingHom {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    (chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
      = u + ∑ j : Fin n, Polynomial.C (z j) * Polynomial.X ^ (j : ℕ) := by
  rw [chartU, Polynomial.map_add, Polynomial.map_map, MvPSeries.evalRingHom_comp_C,
    Polynomial.map_id, Polynomial.map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    MvPSeries.evalRingHom_apply, MvPSeries.eval_X]

/-- The evaluated chart datum satisfies the Mumford divisibility over `O`. -/
theorem chartU_map_evalRingHom_dvd {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    (chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
      ∣ ((chartV hu hne.ge hv hw hbez).map
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))) ^ 2 - f := by
  have h := Polynomial.map_dvd (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
    (chartU_dvd_chartV_sq_sub hu hne.ge hv hw hbez)
  rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_map,
    MvPSeries.evalRingHom_comp_C, Polynomial.map_id] at h

include hu hne in
theorem chartU_map_evalRingHom_monic {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).Monic :=
  (chartU_monic hu hne.ge).map _

include hu hne in
theorem chartU_map_evalRingHom_degree {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).degree
      = u.degree := by
  rw [(chartU_monic hu hne.ge).degree_map, chartU_degree hu hne.ge]

include hu hne in
theorem chartU_map_evalRingHom_natDegree {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).natDegree = n := by
  rw [natDegree_eq_of_degree_eq (chartU_map_evalRingHom_degree hu hne hz), hne]

theorem chartU_map_evalRingHom_map_residue {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).map (residue O)
      = u.map (residue O) := by
  rw [map_residue_eval_eq hz, chartU_map_constantCoeff]

theorem chartV_map_evalRingHom_degree_lt {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartV hu hne.ge hv hw hbez).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).degree
      < ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).degree := by
  rw [chartU_map_evalRingHom_degree hu hne hz]
  exact Polynomial.degree_map_le.trans_lt (chartV_degree_lt hu hne.ge hv hw hbez)

theorem chartV_map_evalRingHom_map_residue {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ((chartV hu hne.ge hv hw hbez).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).map (residue O)
      = v.map (residue O) := by
  rw [map_residue_eval_eq hz, chartV_map_constantCoeff]

/-- **The evaluated chart `v`-part is the unique square root**: any square root of `f`
modulo the evaluated `u`-part that stays below it in degree and reduces to `v_bar` equals
it. -/
theorem chartV_map_evalRingHom_eq {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O)
    {V : O[X]}
    (hdvd : (chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
      ∣ V ^ 2 - f)
    (hdeg : V.degree
      < ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).degree)
    (hres : V.map (residue O) = v.map (residue O)) :
    (chartV hu hne.ge hv hw hbez).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
      = V :=
  eq_of_dvd_sq_sub_of_residue_bezout (chartU_map_evalRingHom_monic hu hne hz)
    (chartU_map_evalRingHom_dvd hu hne hv hw hbez hz) hdvd
    (chartV_map_evalRingHom_degree_lt hu hne hv hw hbez hz) hdeg
    (by rw [chartU_map_evalRingHom_map_residue hz]; exact map_bezout (residue O) hbez)
    (chartV_map_evalRingHom_map_residue hu hne hv hw hbez hz) hres

include hu hne in
/-- A monic polynomial of degree `n` reducing to `ū` is the evaluated chart `u`-part, at the
coordinates read off from its coefficients. -/
theorem exists_chartU_map_evalRingHom_eq {U : O[X]} (hUm : U.Monic) (hUn : U.natDegree = n)
    (hUres : U.map (residue O) = u.map (residue O)) :
    ∃ (z : Fin n → O) (hz : ∀ j, z j ∈ maximalIdeal O),
      (chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz)) = U := by
  have hz (j : Fin n) : (U - u).coeff j ∈ maximalIdeal O := by
    have h0 : residue O ((U - u).coeff j) = 0 := by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, hUres, sub_self, Polynomial.coeff_zero]
    exact (residue_eq_zero_iff _).mp h0
  refine ⟨_, hz, ?_⟩
  rw [chartU_map_evalRingHom hz]
  exact (Polynomial.Monic.eq_add_sum_coeff_sub hUm hu hUn hne).symm

variable [IsDomain O] [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The chart class at a fold-`F_τ` sum is the product of the chart classes and `-τ`**
(`mk0_chart_eval_fold` in polydisk coordinates). -/
theorem chartClass_eval_FtauFold {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O}
    {a b : Fin n → O} (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {z₁ z₂ : Fin n → O} (hz₁ : ∀ j, z₁ j ∈ maximalIdeal O)
    (hz₂ : ∀ j, z₂ j ∈ maximalIdeal O) {e : Fin n → O}
    (hedef : e = fun j ↦ MvPSeries.eval (Sum.elim z₁ z₂)
      (FtauFold A a b hu hne hv hw hbez d j))
    (he : ∀ j, e j ∈ maximalIdeal O) :
    chartClass hu hne hv hw hbez he
      = chartClass hu hne hv hw hbez hz₁ * chartClass hu hne hv hw hbez hz₂
        * tauClassNeg (f := f) (v := v) hu := by
  have hx : ∀ s, Sum.elim z₁ z₂ s ∈ maximalIdeal O := fun s ↦ by
    cases s with
    | inl s => exact hz₁ s
    | inr s => exact hz₂ s
  rw [mk0_chart_eval_fold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit hx
      hedef he,
    chartClass_congr hu hne hv hw hbez (Sum.elim_comp_inl z₁ z₂) _ hz₁,
    chartClass_congr hu hne hv hw hbez (Sum.elim_comp_inr z₁ z₂) _ hz₂]

end Eval

section Red

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [NeZero (2 : ResidueField O)] {f u v : O[X]} (hu : u.Monic)
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

variable (f u v) in
/-- The class of the reduced `τ`-datum over the residue field. -/
noncomputable def tauClassBar (hu : u.Monic) :
    ClassGroup (HypRing (ResidueField O) (f.map (residue O))) :=
  ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) (u.map (residue O))
      (v.map (residue O)),
    mumfordIdeal_mem_nonZeroDivisors (f.map (residue O)) (hu.map (residue O)).ne_zero
      (v.map (residue O))⟩

/-- The reduced `τ`-datum class in the `mk0` spelling, with the presentation of the two
parts supplied as arguments (as in `ChabautyColeman.chartClass_eq`). -/
theorem tauClassBar_eq {U V : (ResidueField O)[X]} (hU : u.map (residue O) = U)
    (hV : v.map (residue O) = V) (hUne : U ≠ 0) :
    tauClassBar f u v hu
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) U V,
        mumfordIdeal_mem_nonZeroDivisors _ hUne V⟩ := by subst hU hV; rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : FractionRing O)]
  {w : O[X]} (hw : v ^ 2 - f = u * w)
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

include hw in
/-- The reduction of the `τ`-datum class is the reduced `τ`-datum class. -/
theorem redJ_tauClass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsq : Squarefree (u.map (residue O))) :
    redJ (tauClass (f := f) (v := v) hu) = tauClassBar f u v hu :=
  redJ_mk0_mumford hf hdeg hu ⟨w, hw⟩ hsq

end Red

section Main

universe u'

variable {O : Type u'} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The chart parametrization is injective**: equal chart classes have equal
coordinates, by uniqueness of reduced Mumford representatives. -/
theorem chartClass_injective
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    {z z' : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O)
    (hz' : ∀ j, z' j ∈ maximalIdeal O)
    (h : chartClass hu hne hv hw hbez hz = chartClass hu hne hv hw hbez hz') :
    z = z' := by
  set K := FractionRing O
  set ε := MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz)
  set ε' := MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz')
  -- the two evaluated data are reduced Mumford data over `K`
  have hm₁ := (chartU_map_evalRingHom_monic hu hne hz).map (algebraMap O K)
  have hm₂ := (chartU_map_evalRingHom_monic hu hne hz').map (algebraMap O K)
  have hnat₁ : (((chartU u n).map ε).map (algebraMap O K)).natDegree = n := by
    rw [(chartU_map_evalRingHom_monic hu hne hz).natDegree_map,
      chartU_map_evalRingHom_natDegree hu hne hz]
  have hnat₂ : (((chartU u n).map ε').map (algebraMap O K)).natDegree = n := by
    rw [(chartU_map_evalRingHom_monic hu hne hz').natDegree_map,
      chartU_map_evalRingHom_natDegree hu hne hz']
  -- uniqueness of reduced representatives identifies the `u`-parts
  rw [chartClass_eq hu hne hv hw hbez hz rfl rfl hm₁.ne_zero,
    chartClass_eq hu hne hv hw hbez hz' rfl rfl hm₂.ne_zero] at h
  obtain ⟨hUeq, -⟩ := mumfordIdeal_reduced_unique _ hm₁ hm₂
    ((chartU_map_evalRingHom_monic hu hne hz).degree_map_lt_degree_map _
      (chartV_map_evalRingHom_degree_lt hu hne hv hw hbez hz))
    ((chartU_map_evalRingHom_monic hu hne hz').degree_map_lt_degree_map _
      (chartV_map_evalRingHom_degree_lt hu hne hv hw hbez hz'))
    (by lia) (by lia)
    (map_dvd_sq_sub _ (chartU_map_evalRingHom_dvd hu hne hv hw hbez hz))
    (map_dvd_sq_sub _ (chartU_map_evalRingHom_dvd hu hne hv hw hbez hz')) h
  -- extract the coordinates
  have hUeqO : (chartU u n).map ε = (chartU u n).map ε' :=
    Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective O K) hUeq
  rw [chartU_map_evalRingHom hz, chartU_map_evalRingHom hz'] at hUeqO
  funext j
  rw [← Polynomial.coeff_sum_C_mul_X_pow z j, ← Polynomial.coeff_sum_C_mul_X_pow z' j,
    add_left_cancel hUeqO]

variable [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The reduction of a chart class is the reduced `τ`-datum class**: the evaluated
chart datum is integral with reduction `(ū, v_bar)`. -/
theorem redJ_chartClass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsq : Squarefree (u.map (residue O)))
    {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    redJ (chartClass hu hne hv hw hbez hz) = tauClassBar f u v hu := by
  rw [chartClass_eq hu hne hv hw hbez hz rfl rfl
      ((chartU_map_evalRingHom_monic hu hne hz).map _).ne_zero,
    redJ_mk0_mumford hf hdeg (chartU_map_evalRingHom_monic hu hne hz)
      (chartU_map_evalRingHom_dvd hu hne hv hw hbez hz)
      (by rw [chartU_map_evalRingHom_map_residue hz]; exact hsq),
    tauClassBar_eq hu (chartU_map_evalRingHom_map_residue hz).symm
      (chartV_map_evalRingHom_map_residue hu hne hv hw hbez hz).symm
      ((chartU_map_evalRingHom_monic hu hne hz).map _).ne_zero]

/-- **Chart membership** (forward direction of `thm:chart-mem`): a class with trivial
reduction, translated by the `τ`-class, is a chart class at polydisk coordinates. -/
theorem exists_chartClass_eq (hf : f.Monic)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O)))
    {c : ClassGroup (HypRing (FractionRing O) (f.map (algebraMap O (FractionRing O))))}
    (hc : redJ c = 1) :
    ∃ (z : Fin n → O) (hz : ∀ j, z j ∈ maximalIdeal O),
      c * tauClass (f := f) (v := v) hu = chartClass hu hne hv hw hbez hz := by
  set K := FractionRing O
  have hinjOK : Function.Injective (algebraMap O K) :=
    FaithfulSMul.algebraMap_injective O K
  have hKnat : (f.map (algebraMap O K)).natDegree = f.natDegree := hf.natDegree_map _
  have hresnat : (f.map (residue O)).natDegree = f.natDegree := hf.natDegree_map _
  have huresnat : (u.map (residue O)).natDegree = n := by rw [hu.natDegree_map, hne]
  have hdeg : 0 < f.natDegree := by lia
  obtain ⟨u', v', hm', hv', hg', hdvd', heq'⟩ :=
    exists_mk0_mumfordIdeal_reduced (f.map (algebraMap O K))
      (c * tauClass (f := f) (v := v) hu)
  -- the reduction of the translated class is the reduced `τ`-datum class
  have hredmul : redJ (ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K)) u' v',
        mumfordIdeal_mem_nonZeroDivisors _ hm'.ne_zero v'⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) (u.map (residue O))
          (v.map (residue O)),
        mumfordIdeal_mem_nonZeroDivisors _ (hu.map (residue O)).ne_zero _⟩ := by
    rw [← heq', redJ_mul hf hdeg, hc, one_mul, redJ_tauClass hu hw hf hdeg hsq,
      tauClassBar_eq hu rfl rfl (hu.map (residue O)).ne_zero]
  -- descend the reduced representative integrally
  obtain ⟨uO, vO, huOK, hvOK, huOres, hvOres⟩ := red_reducedRep_eq hf hdeg hm' hv' hdvd'
    (hu.map (residue O)) (hu.degree_map_lt_degree_map (residue O) hv) (by lia)
    (map_dvd_sq_sub _ ⟨w, hw⟩) hsq (by lia) hredmul
  -- the descended datum is monic of degree `n`, so it is an evaluated chart `u`-part
  have huOm : uO.Monic := hinjOK.monic_map_iff.mpr (huOK ▸ hm')
  have huOnat : uO.natDegree = n := by rw [← huOm.natDegree_map (residue O), huOres, huresnat]
  obtain ⟨z, hz, hUOz⟩ := exists_chartU_map_evalRingHom_eq hu hne huOm huOnat huOres
  -- the evaluated chart `v`-part is the descended `v`, by square-root uniqueness
  have hVdvd : uO ∣ vO ^ 2 - f := (Polynomial.map_dvd_map _ hinjOK huOm).mp
    (by rw [Polynomial.map_sub, Polynomial.map_pow, huOK, hvOK]; exact hdvd')
  have hVdeg : vO.degree < uO.degree := by
    rw [← Polynomial.degree_map_eq_of_injective hinjOK vO,
      ← Polynomial.degree_map_eq_of_injective hinjOK uO, huOK, hvOK]
    exact hv'
  have hVeq := chartV_map_evalRingHom_eq hu hne hv hw hbez hz (V := vO)
    (by rw [hUOz]; exact hVdvd) (by rw [hUOz]; exact hVdeg) hvOres
  exact ⟨z, hz, heq'.trans (chartClass_eq hu hne hv hw hbez hz
    (by rw [hUOz, huOK]) (by rw [hVeq, hvOK]) hm'.ne_zero).symm⟩

/-- **Chart classes translated by `-τ` lie in the kernel of the reduction.** -/
theorem redJ_chartClass_mul_inv (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsq : Squarefree (u.map (residue O)))
    {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    redJ (chartClass hu hne hv hw hbez hz * (tauClass (f := f) (v := v) hu)⁻¹) = 1 := by
  change (redJHom hf hdeg) (chartClass hu hne hv hw hbez hz
    * (tauClass (f := f) (v := v) hu)⁻¹) = 1
  rw [map_mul, map_inv]
  change redJ (chartClass hu hne hv hw hbez hz)
    * (redJ (tauClass (f := f) (v := v) hu))⁻¹ = 1
  rw [redJ_chartClass hu hne hv hw hbez hf hdeg hsq hz, redJ_tauClass hu hw hf hdeg hsq,
    mul_inv_cancel]

/-- The parametrization of the kernel of the reduction by the polydisk: the coordinate
`z` maps to the chart class at `z`, translated by `-τ`. -/
noncomputable def polydiskToKer (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsq : Squarefree (u.map (residue O)))
    (z : {z : Fin n → O // ∀ j, z j ∈ maximalIdeal O}) :
    (redJHom (K := FractionRing O) (f := f) hf hdeg).ker :=
  ⟨chartClass hu hne hv hw hbez z.2 * (tauClass (f := f) (v := v) hu)⁻¹,
    MonoidHom.mem_ker.mpr
      (redJ_chartClass_mul_inv hu hne hv hw hbez hf hdeg hsq z.2)⟩

@[simp] theorem polydiskToKer_coe (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsq : Squarefree (u.map (residue O)))
    (z : {z : Fin n → O // ∀ j, z j ∈ maximalIdeal O}) :
    (polydiskToKer hu hne hv hw hbez hf hdeg hsq z : HypJac (FractionRing O) _)
      = chartClass hu hne hv hw hbez z.2 * (tauClass (f := f) (v := v) hu)⁻¹ :=
  rfl

/-- **The polydisk parametrizes the kernel of the reduction bijectively** (blueprint
`thm:chart-mem`). -/
theorem polydiskToKer_bijective (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) :
    Function.Bijective (polydiskToKer hu hne hv hw hbez hf hdeg hsq) := by
  constructor
  · intro z z' h
    have h1 := congrArg Subtype.val h
    rw [polydiskToKer_coe, polydiskToKer_coe] at h1
    exact Subtype.ext (chartClass_injective hu hne hv hw hbez hfdeg z.2 z'.2
      (mul_right_cancel h1))
  · intro c
    have hc : redJ c.1 = 1 := MonoidHom.mem_ker.mp c.2
    obtain ⟨z, hz, heq⟩ := exists_chartClass_eq hu hne hv hw hbez hf hfdeg hsq hc
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    rw [polydiskToKer_coe, ← heq, mul_inv_cancel_right]

/-- **The chart coordinates of `c + τ` identify the kernel of the reduction with the
polydisk** (blueprint `thm:chart-mem`): the inverse of the parametrization
`ChabautyColeman.polydiskToKer`. The group compatibility (transport of multiplication to
`+_{F_τ}`) is `ChabautyColeman.polydiskToKer_eval_FtauFold`. -/
noncomputable def J1_equiv_polydisk (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) :
    (redJHom (K := FractionRing O) (f := f) hf hdeg).ker
      ≃ {z : Fin n → O // ∀ j, z j ∈ maximalIdeal O} :=
  (Equiv.ofBijective _
    (polydiskToKer_bijective hu hne hv hw hbez hf hdeg hfdeg hsq)).symm

/-- **The parametrization is a group homomorphism onto the kernel** for the fold form of
the translated law (blueprint `thm:chart-mem`, group clause). -/
theorem polydiskToKer_eval_FtauFold (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : f.natDegree = 2 * n + 1) (hsq : Squarefree (u.map (residue O)))
    {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {z₁ z₂ : Fin n → O} (hz₁ : ∀ j, z₁ j ∈ maximalIdeal O)
    (hz₂ : ∀ j, z₂ j ∈ maximalIdeal O) {e : Fin n → O}
    (hedef : e = fun j ↦ MvPSeries.eval (Sum.elim z₁ z₂)
      (FtauFold A a b hu hne hv hw hbez d j))
    (he : ∀ j, e j ∈ maximalIdeal O) :
    polydiskToKer hu hne hv hw hbez hf hdeg hsq ⟨e, he⟩
      = polydiskToKer hu hne hv hw hbez hf hdeg hsq ⟨z₁, hz₁⟩
        * polydiskToKer hu hne hv hw hbez hf hdeg hsq ⟨z₂, hz₂⟩ := by
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, polydiskToKer_coe, polydiskToKer_coe, polydiskToKer_coe,
    chartClass_eval_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit
      hz₁ hz₂ hedef he,
    tauClassNeg_eq_inv hu hw, mul_assoc]
  exact (mul_mul_mul_comm _ _ _ _).symm

end Main

end ChabautyColeman

end
