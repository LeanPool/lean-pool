/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.ZeroCount
public import Mathlib.Algebra.Polynomial.Taylor

import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Strassmann's theorem

A power series `h ∈ O⟦X⟧` whose coefficients tend to `0` can be evaluated at *every*
point of `O` (`ChabautyColeman.PSeries.evalT`, the sum of the defining series; junk
where it does not converge). **Strassmann's theorem**
(`ChabautyColeman.PSeries.strassmann`, with finiteness
`ChabautyColeman.PSeries.strassmann_finite`): if moreover the coefficient of index `N`
is a unit and all later coefficients lie in the maximal ideal, then `h` has at most `N`
zeros in `O`.

The proof decomposes the zero set by residue classes: the reduction of `h` is a
polynomial `q` of degree at most `N` (`ChabautyColeman.PSeries.exists_coe_eq_map`),
zeros of `h` lie over roots of `q`
(`ChabautyColeman.PSeries.setOf_evalT_eq_zero_eq_biUnion`), and over a root `y` with
lift `c` the zeros of `h` are zeros of the recentered series
`ChabautyColeman.PSeries.recenter c h = h(c + X)` on the maximal ideal
(`ChabautyColeman.PSeries.evalT_add_eq`, an exchange of summation). The reduction of
the recentered series is the Taylor shift of `q`
(`ChabautyColeman.PSeries.map_recenter`), whose vanishing order is the root
multiplicity of `q` at `y` (`ChabautyColeman.PSeries.order_coe_taylor`), so the zero
count in each class is bounded by `cor:wprep-count` and the total by
`∑ rootMultiplicity ≤ deg q ≤ N`.

The hypothesis that the coefficients tend to zero is necessary: without it the defining series does
not converge outside the maximal ideal, and finiteness of the number of unit coefficients alone
does not suffice.

Blueprint node: `thm:strassmann`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial Filter Topology

namespace ChabautyColeman

namespace PSeries

section residueField

variable {κ : Type*} [Field κ]

/-- The order of a Taylor-shifted polynomial, as a power series, is the root
multiplicity at the center. -/
theorem order_coe_taylor {q : κ[X]} (hq0 : q ≠ 0) (c : κ) :
    (↑(q.taylor c) : κ⟦X⟧).order = q.rootMultiplicity c := by
  set m := q.rootMultiplicity c
  set r := q /ₘ (Polynomial.X - Polynomial.C c) ^ m
  have hfac := q.pow_mul_divByMonic_rootMultiplicity_eq c
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hq0
  have htaylor : q.taylor c = Polynomial.X ^ m * r.taylor c := by
    rw [← hfac, taylor_mul, taylor_pow]
    congr 2
    rw [map_sub, taylor_X, taylor_C]
    ring
  have horder : (↑(r.taylor c) : κ⟦X⟧).order = 0 := by
    by_contra hne
    have h0 := order_ne_zero_iff_constCoeff_eq_zero.mp hne
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe,
      taylor_coeff_zero] at h0
    exact hr h0
  rw [htaylor]
  push_cast
  rw [order_mul, order_X_pow, horder, add_zero]

end residueField

section reduction

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The reduction of a power series whose coefficients beyond `N` lie in the maximal
ideal is (the coercion of) a polynomial of degree at most `N`. -/
theorem exists_coe_eq_map {h : O⟦X⟧} {N : ℕ}
    (hN : ∀ k, N < k → coeff k h ∈ maximalIdeal O) :
    ∃ q : (ResidueField O)[X], (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)
      ∧ q.natDegree ≤ N := by
  classical
  refine ⟨∑ k ∈ Finset.range (N + 1),
    Polynomial.C (residue O (coeff k h)) * Polynomial.X ^ k, ?_, ?_⟩
  · ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range (N + 1)) m]
    by_cases hm : m ≤ N
    · simp [hm]
    · rw [ite_eq_right (by simpa [Nat.lt_succ_iff] using hm)]
      exact ((residue_eq_zero_iff _).mpr (hN m (by lia))).symm
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    simpa [Polynomial.natDegree_X_pow] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

-- The reduction is nonzero: its degree-`N` coefficient is the residue of the unit `coeff N h`.
private lemma reduction_ne_zero {h : O⟦X⟧} {N : ℕ} (hNu : IsUnit (coeff N h))
    {q : (ResidueField O)[X]} (hq : (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)) : q ≠ 0 := by
  have hqN : q.coeff N ≠ 0 := by
    have h1 := congrArg (PowerSeries.coeff N) hq
    rw [Polynomial.coeff_coe, PowerSeries.coeff_map] at h1
    rw [h1]
    exact (residue_ne_zero_iff_isUnit _).mpr hNu
  exact fun h0 ↦ hqN (by simp [h0])

end reduction

variable {O : Type*} [CommRing O] [UniformSpace O]

/-- Evaluation of a power series with decaying coefficients at an arbitrary point of
`O` (junk if the defining series does not converge). -/
noncomputable def evalT (z : O) (h : O⟦X⟧) : O := ∑' k, coeff k h * z ^ k

theorem evalT_eq_tsum (z : O) (h : O⟦X⟧) : evalT z h = ∑' k, coeff k h * z ^ k := rfl

/-- The recentered power series `h(c + X)`; its coefficients are given by convergent
series when the coefficients of `h` decay (junk coefficients otherwise). -/
noncomputable def recenter (c : O) (h : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑' j, ((n + j).choose n : O) * coeff (n + j) h * c ^ j

@[simp]
theorem coeff_recenter (c : O) (h : O⟦X⟧) (n : ℕ) :
    coeff n (recenter c h) = ∑' j, ((n + j).choose n : O) * coeff (n + j) h * c ^ j :=
  coeff_mk _ _

theorem constantCoeff_recenter (c : O) (h : O⟦X⟧) :
    constantCoeff (recenter c h) = evalT c h := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [evalT_eq_tsum]

-- the doubly indexed family of binomial terms underlying `h(c + w)`
private noncomputable def binomFamily (c w : O) (h : O⟦X⟧) : ℕ × ℕ → O := fun p ↦
  if p.2 ≤ p.1 then coeff p.1 h * (w ^ p.2 * c ^ (p.1 - p.2) * (p.1.choose p.2 : O))
  else 0

private lemma hasSum_binomFamily_row {h : O⟦X⟧} (c w : O) (k : ℕ) :
    HasSum (fun n ↦ binomFamily c w h (k, n)) (coeff k h * (c + w) ^ k) := by
  have hsupp : ∀ n ∉ Finset.range (k + 1), binomFamily c w h (k, n) = 0 := by
    intro n hn
    have hn' : ¬ n ≤ k := by simpa [Nat.lt_succ_iff] using hn
    simp [binomFamily, hn']
  have hsum : HasSum (fun n ↦ binomFamily c w h (k, n))
      (∑ n ∈ Finset.range (k + 1), binomFamily c w h (k, n)) :=
    hasSum_sum_of_ne_finset_zero hsupp
  have heq : ∑ n ∈ Finset.range (k + 1), binomFamily c w h (k, n)
      = coeff k h * (c + w) ^ k := by
    rw [add_comm c w, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' : n ≤ k := by simpa [Nat.lt_succ_iff] using hn
    simp [binomFamily, hn']
  rwa [heq] at hsum

variable [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]

variable [IsUniformAddGroup O] [CompleteSpace O]

theorem summable_mul_of_tendsto_zero {f g : ℕ → O} (hf : Tendsto f atTop (𝓝 0)) :
    Summable fun k ↦ f k * g k :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (by rw [Nat.cofinite_eq_atTop]; exact tendsto_mul_zero_of_tendsto_zero hf)

section summability

variable {h : O⟦X⟧} (hc : Tendsto (fun k ↦ coeff k h) atTop (𝓝 0))

include hc

/-- Subtracting a constant from the series subtracts it from every value. -/
theorem evalT_sub_C [T2Space O] (c z : O) : evalT z (h - PowerSeries.C c) = evalT z h - c := by
  have h1 : HasSum (fun k ↦ coeff k h * z ^ k) (evalT z h) :=
    (summable_mul_of_tendsto_zero hc).hasSum
  have h2 : HasSum (fun k ↦ coeff k (PowerSeries.C c : O⟦X⟧) * z ^ k) c := by
    simpa using hasSum_single (f := fun k ↦ coeff k (PowerSeries.C c : O⟦X⟧) * z ^ k) 0
      fun k hk ↦ by simp [PowerSeries.coeff_C, hk]
  rw [evalT_eq_tsum]
  exact ((h1.sub h2).congr_fun fun k ↦ by rw [map_sub, sub_mul]).tsum_eq

theorem summable_recenter_coeff (c : O) (n : ℕ) :
    Summable fun j ↦ ((n + j).choose n : O) * coeff (n + j) h * c ^ j := by
  have h1 : Tendsto (fun j ↦ coeff (n + j) h) atTop (𝓝 0) := by
    refine hc.comp ?_
    simpa [add_comm] using tendsto_add_atTop_nat n
  exact (summable_mul_of_tendsto_zero (g := fun j ↦ ((n + j).choose n : O) * c ^ j) h1).congr
    fun j ↦ by ring

private lemma summable_binomFamily (c : O) {w : O} (hw : w ∈ maximalIdeal O) :
    Summable (binomFamily c w h) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  have h1 : ∀ᶠ k in atTop, coeff k h ∈ I := by
    simpa using IsLinearTopology.hasBasis_ideal.tendsto_right_iff.mp hc I hI
  have h2 : ∀ᶠ m in atTop, w ^ m ∈ I := by
    simpa using IsLinearTopology.hasBasis_ideal.tendsto_right_iff.mp (hasEval_of_mem hw) I hI
  obtain ⟨K, hK⟩ := eventually_atTop.mp h1
  obtain ⟨M, hM⟩ := eventually_atTop.mp h2
  rw [eventually_cofinite]
  refine Set.Finite.subset ((Set.finite_Iio K).prod (Set.finite_Iio M)) fun p hp ↦ ?_
  simp only [Set.mem_ofPred_eq] at hp
  by_contra hmem
  simp only [Set.mem_prod, Set.mem_Iio, not_and_or, not_lt] at hmem
  refine hp ?_
  by_cases hle : p.2 ≤ p.1
  · simp only [binomFamily, ite_eq_left hle]
    rcases hmem with hk | hm
    · exact I.mul_mem_right _ (hK _ hk)
    · exact I.mul_mem_left _ (I.mul_mem_right _ (I.mul_mem_right _ (hM _ hm)))
  · simp [binomFamily, hle]

private lemma hasSum_binomFamily_col (c w : O) (n : ℕ) :
    HasSum (fun k ↦ binomFamily c w h (k, n)) (coeff n (recenter c h) * w ^ n) := by
  rw [coeff_recenter]
  have hinj := add_right_injective n
  have hzero : ∀ k ∉ Set.range (n + ·), binomFamily c w h (k, n) = 0 := by
    intro k hk
    have hlt : ¬ n ≤ k := fun hle ↦ hk ⟨k - n, by lia⟩
    simp [binomFamily, hlt]
  have hs := ((summable_recenter_coeff hc c n).hasSum).mul_right (w ^ n)
  have heq : (fun j ↦ ((n + j).choose n : O) * coeff (n + j) h * c ^ j * w ^ n)
      = (fun k ↦ binomFamily c w h (k, n)) ∘ (n + ·) := by
    funext j
    have hle : n ≤ n + j := by lia
    simp only [binomFamily, Function.comp_apply, ite_eq_left hle, Nat.add_sub_cancel_left]
    ring
  exact (hinj.hasSum_iff hzero).mp (heq ▸ hs)

end summability

variable [IsTopologicalRing O] [T2Space O]

theorem evalT_eq_eval {z : O} (hz : z ∈ maximalIdeal O) (h : O⟦X⟧) : evalT z h = eval z h :=
  (eval_eq_tsum hz h).symm

section restricted

variable {h : O⟦X⟧} (hc : Tendsto (fun k ↦ coeff k h) atTop (𝓝 0))

include hc

/-- Evaluation at `c + w` is evaluation of the recentered series at `w`
(exchange of summation). -/
theorem evalT_add_eq (c : O) {w : O} (hw : w ∈ maximalIdeal O) :
    evalT (c + w) h = eval w (recenter c h) := by
  have htot := (summable_binomFamily hc c hw).hasSum
  have h1 : HasSum (fun k ↦ coeff k h * (c + w) ^ k) (∑' p, binomFamily c w h p) :=
    htot.prod_fiberwise (hasSum_binomFamily_row c w)
  have h2 : HasSum (fun q : ℕ × ℕ ↦ binomFamily c w h (q.2, q.1))
      (∑' p, binomFamily c w h p) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff (f := binomFamily c w h)).mpr htot
  have h3 : HasSum (fun n ↦ coeff n (recenter c h) * w ^ n) (∑' p, binomFamily c w h p) :=
    h2.prod_fiberwise (hasSum_binomFamily_col hc c w)
  rw [evalT_eq_tsum, h1.tsum_eq]
  exact h3.unique (hasSum_eval hw (recenter c h))

/-- The reduction of the recentered series is the Taylor shift of the reduction. -/
theorem map_recenter {q : (ResidueField O)[X]}
    (hq : (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)) (c : O) :
    (recenter c h).map (residue O) = ↑(q.taylor (residue O c)) := by
  ext n
  have hcoeff (m : ℕ) : residue O (coeff m h) = q.coeff m := by
    have := congrArg (PowerSeries.coeff m) hq
    simpa [PowerSeries.coeff_map, Polynomial.coeff_coe] using this.symm
  have hmem (m : ℕ) (hm : q.natDegree < m) : coeff m h ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    have := hcoeff m
    rwa [coeff_eq_zero_of_natDegree_lt hm] at this
  set B := q.natDegree + 1
  rw [PowerSeries.coeff_map, coeff_recenter]
  set f : ℕ → O := fun j ↦ ((n + j).choose n : O) * coeff (n + j) h * c ^ j with hf
  have hshift : Summable fun j ↦ f (j + B) :=
    (summable_recenter_coeff hc c n).comp_injective (add_left_injective B)
  rw [← Summable.sum_add_tsum_nat_add' hshift]
  have htail : (∑' j, f (j + B)) ∈ maximalIdeal O := by
    refine tsum_mem isClosed_maximalIdeal fun j ↦ ?_
    rw [hf]
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ _ (hmem _ (by lia)))
  have hres : residue O (∑' j, f (j + B)) = 0 := (residue_eq_zero_iff _).mpr htail
  rw [map_add, hres, add_zero, map_sum, Polynomial.coeff_coe, taylor_coeff]
  rw [eval_eq_sum_range' (n := B) (by
    exact lt_of_le_of_lt (natDegree_hasseDeriv_le q n) (by lia))]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [hf, hasseDeriv_coeff]
  push_cast
  rw [map_mul, map_mul, map_pow, hcoeff, map_natCast, add_comm j n]

/-- The residue of a value of `evalT` is the value of the reduction. -/
theorem residue_evalT {q : (ResidueField O)[X]}
    (hq : (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)) (z : O) :
    residue O (evalT z h) = q.eval (residue O z) := by
  have h1 := congrArg (PowerSeries.coeff 0) (map_recenter hc hq z)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_recenter] at h1
  rwa [Polynomial.coeff_coe, taylor_coeff_zero] at h1

/-- The zeros of `h` in `O` decompose according to the roots of the reduction. -/
theorem setOf_evalT_eq_zero_eq_biUnion {q : (ResidueField O)[X]}
    (hq : (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)) :
    {z : O | evalT z h = 0}
      = ⋃ y ∈ {y | q.IsRoot y}, {z : O | evalT z h = 0 ∧ residue O z = y} := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨fun hz ↦ ⟨residue O z, by rw [IsRoot, ← residue_evalT hc hq z, hz, map_zero], hz, rfl⟩,
    fun ⟨_, _, hz, _⟩ ↦ hz⟩

variable [IsDomain O]

-- the zeros of `h` above a fixed root of the reduction inject into the zeros of a
-- recentered series on the maximal ideal, which `cor:wprep-count` counts
private lemma class_zeros {q : (ResidueField O)[X]}
    (hq : (↑q : (ResidueField O)⟦X⟧) = h.map (residue O)) (hq0 : q ≠ 0)
    (y : ResidueField O) :
    {z : O | evalT z h = 0 ∧ residue O z = y}.Finite ∧
      {z : O | evalT z h = 0 ∧ residue O z = y}.ncard ≤ q.rootMultiplicity y := by
  obtain ⟨c, hcen⟩ : ∃ c : O, residue O c = y := Ideal.Quotient.mk_surjective y
  have hne : (recenter c h).map (residue O) ≠ 0 := by
    rw [map_recenter hc hq c]
    simp only [ne_eq, Polynomial.coe_eq_zero_iff, Polynomial.taylor_eq_zero]
    exact hq0
  have hmapsto : Set.MapsTo (fun z ↦ z - c) {z : O | evalT z h = 0 ∧ residue O z = y}
      {w ∈ maximalIdeal O | eval w (recenter c h) = 0} := by
    intro z ⟨hz0, hzc⟩
    have hmem : z - c ∈ maximalIdeal O := by
      have : residue O (z - c) = 0 := by rw [map_sub, hcen, hzc, sub_self]
      exact (residue_eq_zero_iff _).mp this
    refine ⟨hmem, ?_⟩
    have hkey := evalT_add_eq hc c hmem
    rw [add_sub_cancel] at hkey
    rw [← hkey, hz0]
  have hinj : Set.InjOn (fun z ↦ z - c) {z : O | evalT z h = 0 ∧ residue O z = y} :=
    fun a _ b _ hab ↦ by simpa using congrArg (· + c) hab
  have hTfin := finite_setOf_eval_eq_zero hne
  refine ⟨Set.Finite.of_finite_image (hTfin.subset hmapsto.image_subset) hinj, ?_⟩
  calc {z : O | evalT z h = 0 ∧ residue O z = y}.ncard
      ≤ {w ∈ maximalIdeal O | eval w (recenter c h) = 0}.ncard :=
        Set.ncard_le_ncard_of_injOn _ hmapsto hinj hTfin
    _ ≤ ((recenter c h).map (residue O)).order.toNat := zeros_le_ord hne
    _ = q.rootMultiplicity y := by
        rw [map_recenter hc hq c, hcen, order_coe_taylor hq0]
        exact ENat.toNat_natCast _

/-- Strassmann: the zero set of a power series with decaying coefficients and unit
content is finite. -/
theorem strassmann_finite {N : ℕ} (hNu : IsUnit (coeff N h))
    (hN : ∀ k, N < k → coeff k h ∈ maximalIdeal O) :
    {z : O | evalT z h = 0}.Finite := by
  obtain ⟨q, hq, -⟩ := exists_coe_eq_map hN
  have hq0 : q ≠ 0 := reduction_ne_zero hNu hq
  rw [setOf_evalT_eq_zero_eq_biUnion hc hq]
  exact Set.Finite.biUnion (finite_setOfPred_isRoot hq0) fun y _ ↦ (class_zeros hc hq hq0 y).1

/-- **Strassmann's theorem**: a power series over `O` with decaying coefficients whose
last unit coefficient sits in degree `N` has at most `N` zeros in `O`. -/
theorem strassmann {N : ℕ} (hNu : IsUnit (coeff N h))
    (hN : ∀ k, N < k → coeff k h ∈ maximalIdeal O) :
    {z : O | evalT z h = 0}.ncard ≤ N := by
  classical
  obtain ⟨q, hq, hqle⟩ := exists_coe_eq_map hN
  have hq0 : q ≠ 0 := reduction_ne_zero hNu hq
  have hroots : {y : ResidueField O | q.IsRoot y}.Finite := finite_setOfPred_isRoot hq0
  have htofin : hroots.toFinset = q.roots.toFinset := by
    ext y
    simp [Set.Finite.mem_toFinset, Multiset.mem_toFinset, mem_roots hq0]
  have hun : (⋃ y ∈ {y : ResidueField O | q.IsRoot y},
        {z : O | evalT z h = 0 ∧ residue O z = y})
      = ⋃ y ∈ hroots.toFinset, {z : O | evalT z h = 0 ∧ residue O z = y} := by
    ext z
    simp [Set.Finite.mem_toFinset]
  calc {z : O | evalT z h = 0}.ncard
      = (⋃ y ∈ hroots.toFinset, {z : O | evalT z h = 0 ∧ residue O z = y}).ncard := by
        rw [setOf_evalT_eq_zero_eq_biUnion hc hq, hun]
    _ ≤ ∑ y ∈ hroots.toFinset, {z : O | evalT z h = 0 ∧ residue O z = y}.ncard :=
        Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ y ∈ hroots.toFinset, q.rootMultiplicity y :=
        Finset.sum_le_sum fun y _ ↦ (class_zeros hc hq hq0 y).2
    _ = Multiset.card q.roots := by
        rw [htofin, ← Multiset.toFinset_sum_count_eq q.roots]
        exact Finset.sum_congr rfl fun y _ ↦ q.count_roots.symm
    _ ≤ q.natDegree := q.card_roots'
    _ ≤ N := hqle

end restricted

end PSeries

end ChabautyColeman

end
