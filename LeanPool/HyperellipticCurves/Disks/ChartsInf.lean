/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.Charts
public import LeanPool.HyperellipticCurves.Series.HenselRoot
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Disk parametrizations: the infinity chart

The residue disk of the point at infinity `∞_bar` collects the point `∞` and the infinite-type
affine points (those with `𝓋 x > 1`, which reduce to `∞_bar`). It is parametrized by `t ∈ 𝔪` via
`t ↦ (1/u, 1/(uᵍ·t))` (and `t = 0 ↦ ∞`), where `u = 1/x ∈ 𝔪` solves the **non-monic** equation
`u = t²·(reverse f)(u)` — obtained by rewriting `t² = x²ᵍ/f(x)` in `u = 1/x` using
`f(x) = x^{2g+1}·(reverse f)(1/x)`. The root `u` exists by the smooth Hensel lemma
`ChabautyColeman.exists_smooth_root` (the equation is non-monic, so the monic Henselian lemma
does not apply).

The parametrization `t ↦ (1/u, 1/(uᵍt))` (with `0 ↦ ∞`) is a bijection `𝔪 ≃ D_∞_bar`
(`ChabautyColeman.diskParamInf`): it reduces to `∞_bar` (so lands in the disk), is injective (its
`tParam` recovers `t`), and surjective — an infinite-type point `(x, y)` comes from the unique
`u = 1/x`, whose defining equation follows from `y² = f(x)` via the reverse relation and whose
uniqueness is `hensel_unique`.

## Main definitions

* `ChabautyColeman.infRoot`: the root `u ∈ 𝔪` of `u = t²·(reverse f)(u)`.
* `ChabautyColeman.diskPointInf`: the infinity-chart curve point at parameter `t ∈ 𝔪`.
* `ChabautyColeman.diskParamInf`: the bijection `𝔪 ≃ D_∞_bar`.

## Main statements

* `ChabautyColeman.eval_map_inv_mul_pow`: `f(1/x)·xⁿ = (reverse f)(x)`.
* `ChabautyColeman.infRoot_onCurve`: `(1/(uᵍt))² = f(1/u)`.
* `ChabautyColeman.redPoint_diskPointInf`: the parametrized point reduces to `∞_bar`.

Blueprint node: `lem:disk-param` (infinity chart).
-/

@[expose] public section

open IsLocalRing Polynomial IsDedekindDomain

namespace ChabautyColeman

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K]

variable [IsFractionRing O K]

/-- Reverse-polynomial relation over `K`: `f(1/x)·xⁿ = (reverse f)(x)` (as `φ`-images), the
key to the on-curve identity of the infinity chart. -/
theorem eval_map_inv_mul_pow (f : O[X]) {u : O} (hu : u ≠ 0) :
    (f.map (algebraMap O K)).eval (algebraMap O K u)⁻¹ * (algebraMap O K u) ^ f.natDegree
      = algebraMap O K ((reverse f).eval u) := by
  have hφu : algebraMap O K u ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hu
  let : Invertible ((algebraMap O K u)⁻¹) :=
    ⟨algebraMap O K u, mul_inv_cancel₀ hφu, inv_mul_cancel₀ hφu⟩
  have h := eval₂_reverse_mul_pow (algebraMap O K) ((algebraMap O K u)⁻¹) f
  rw [show (⅟((algebraMap O K u)⁻¹)) = algebraMap O K u from rfl, eval₂_at_apply, ← eval_map] at h
  rw [← h, mul_assoc, ← mul_pow, inv_mul_cancel₀ hφu, one_pow, mul_one]

section lift

variable [IsDomain O] [IsDiscreteValuationRing O]

/-- Lift of an element of the fraction field of valuation `< 1`: it comes from an element of the
maximal ideal, nonzero if the element is. Packages the two lift-and-membership setups (for
`u₀ = 1/x` and `t₀ = xᵍ/y`) in the infinity surjectivity proof. -/
private theorem exists_lift_mem_ne_zero {c : K}
    (hc : (IsDiscreteValuationRing.maximalIdeal O).valuation K c < 1) (hc0 : c ≠ 0) :
    ∃ c₀ : O, algebraMap O K c₀ = c ∧ c₀ ∈ maximalIdeal O ∧ c₀ ≠ 0 := by
  obtain ⟨c₀, hc₀eq⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hc.le
  refine ⟨c₀, hc₀eq, ?_, ?_⟩
  · exact ((IsDiscreteValuationRing.maximalIdeal O).valuation_lt_one_iff_mem (K := K) c₀).mp
      (by change (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K c₀) < 1
          rw [hc₀eq]; exact hc)
  · rintro rfl; rw [map_zero] at hc₀eq; exact hc0 hc₀eq.symm

end lift

section inf

variable [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]

/-- For `t ∈ 𝔪`, the non-monic equation `u = t²·(reverse f)(u)` has a solution `u ∈ 𝔪`
(smooth Hensel). -/
theorem exists_infRoot (f : O[X]) (hf : f.Monic) {t : O} (ht : t ∈ maximalIdeal O) :
    ∃ u, u = t ^ 2 * (reverse f).eval u ∧ u ∈ maximalIdeal O := by
  have ht2 : t ^ 2 ∈ maximalIdeal O := (maximalIdeal O).pow_mem_of_mem ht 2 two_pos
  obtain ⟨u, hu0, humem⟩ := exists_smooth_root (g := X - C (t ^ 2) * reverse f) (a₀ := 0)
    (by rw [eval_sub, eval_X, eval_mul, eval_C, ← coeff_zero_eq_eval_zero, coeff_zero_reverse,
          hf.leadingCoeff, mul_one, zero_sub]
        exact neg_mem ht2)
    (by rw [derivative_sub, derivative_X, derivative_C_mul, eval_sub, eval_one, eval_mul, eval_C]
        exact isUnit_of_sub_mem isUnit_one
          (by rw [show 1 - t ^ 2 * (derivative (reverse f)).eval 0 - 1
                = -(t ^ 2 * (derivative (reverse f)).eval 0) by ring]
              exact neg_mem (Ideal.mul_mem_right _ _ ht2)))
  refine ⟨u, ?_, by simpa using humem⟩
  rw [eval_sub, eval_X, eval_mul, eval_C] at hu0
  exact sub_eq_zero.mp hu0

/-- The infinity-chart root: the `u ∈ 𝔪` with `u = t²·(reverse f)(u)`. -/
noncomputable def infRoot (f : O[X]) (hf : f.Monic) {t : O} (ht : t ∈ maximalIdeal O) : O :=
  (exists_infRoot f hf ht).choose

theorem infRoot_eq (f : O[X]) (hf : f.Monic) {t : O} (ht : t ∈ maximalIdeal O) :
    infRoot f hf ht = t ^ 2 * (reverse f).eval (infRoot f hf ht) :=
  (exists_infRoot f hf ht).choose_spec.1

theorem infRoot_mem (f : O[X]) (hf : f.Monic) {t : O} (ht : t ∈ maximalIdeal O) :
    infRoot f hf ht ∈ maximalIdeal O :=
  (exists_infRoot f hf ht).choose_spec.2

theorem infRoot_ne_zero (f : O[X]) (hf : f.Monic) {t : O} (ht : t ∈ maximalIdeal O)
    (ht0 : t ≠ 0) : infRoot f hf ht ≠ 0 := by
  have hru : IsUnit ((reverse f).eval (infRoot f hf ht)) :=
    isUnit_of_sub_mem isUnit_one (by
      obtain ⟨q, hq⟩ := sub_dvd_eval_sub (infRoot f hf ht) 0 (reverse f)
      rw [sub_zero, ← coeff_zero_eq_eval_zero, coeff_zero_reverse, hf.leadingCoeff] at hq
      rw [hq]; exact Ideal.mul_mem_right q _ (infRoot_mem f hf ht))
  rw [infRoot_eq]
  exact mul_ne_zero (pow_ne_zero 2 ht0) hru.ne_zero

/-- The infinity-chart on-curve identity: `(1/(uᵍ·t))² = f(1/u)`. -/
theorem infRoot_onCurve (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) {t : O}
    (ht : t ∈ maximalIdeal O) (ht0 : t ≠ 0) :
    (((algebraMap O K (infRoot f hf ht)) ^ genus f * algebraMap O K t)⁻¹) ^ 2
      = (f.map (algebraMap O K)).eval ((algebraMap O K (infRoot f hf ht))⁻¹) := by
  set u := infRoot f hf ht
  have hu_ne : u ≠ 0 := infRoot_ne_zero f hf ht ht0
  have hφu : algebraMap O K u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hu_ne
  have hφt : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr ht0
  have key := eval_map_inv_mul_pow (K := K) f hu_ne
  have hru : algebraMap O K u
      = (algebraMap O K t) ^ 2 * algebraMap O K ((reverse f).eval u) := by
    rw [← map_pow, ← map_mul]; exact congrArg (algebraMap O K) (infRoot_eq f hf ht)
  have hn : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one hodd).symm
  rw [hn] at key
  have h1 : (f.map (algebraMap O K)).eval ((algebraMap O K u)⁻¹)
      = algebraMap O K ((reverse f).eval u) / (algebraMap O K u) ^ (2 * genus f + 1) :=
    (eq_div_iff (pow_ne_zero _ hφu)).mpr key
  rw [h1]
  field_simp
  linear_combination (algebraMap O K u) ^ (2 * genus f) * hru

open scoped Classical in
/-- The infinity-chart parametrized point at `t ∈ 𝔪`: `∞` at `t = 0`, else `(1/u, 1/(uᵍt))`. -/
noncomputable def diskPointInf (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) {t : O}
    (ht : t ∈ maximalIdeal O) : CurvePoint K (f.map (algebraMap O K)) :=
  if ht0 : t = 0 then .infinity
  else .affine ((algebraMap O K (infRoot f hf ht))⁻¹)
    ((algebraMap O K (infRoot f hf ht) ^ genus f * algebraMap O K t)⁻¹)
    (infRoot_onCurve f hf hodd ht ht0)

@[simp] theorem diskPointInf_zero (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) :
    diskPointInf (K := K) f hf hodd (zero_mem (maximalIdeal O)) = .infinity :=
  dite_eq_left rfl

theorem diskPointInf_of_ne_zero (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) {t : O}
    (ht : t ∈ maximalIdeal O) (ht0 : t ≠ 0) :
    diskPointInf (K := K) f hf hodd ht
      = .affine ((algebraMap O K (infRoot f hf ht))⁻¹)
        ((algebraMap O K (infRoot f hf ht) ^ genus f * algebraMap O K t)⁻¹)
        (infRoot_onCurve f hf hodd ht ht0) :=
  dite_eq_right ht0

/-- The infinity-chart parametrized point depends only on the parameter. -/
theorem diskPointInf_congr {f : O[X]} (hf : f.Monic) (hodd : Odd f.natDegree) {t t' : O}
    (ht : t ∈ maximalIdeal O) (ht' : t' ∈ maximalIdeal O) (h : t = t') :
    diskPointInf (K := K) f hf hodd ht = diskPointInf f hf hodd ht' := by
  subst h; rfl

/-- Every infinity-chart point reduces to `∞_bar` (it is either `∞` or of infinite type). -/
theorem redPoint_diskPointInf (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) {t : O}
    (ht : t ∈ maximalIdeal O) :
    redPoint (diskPointInf (K := K) f hf hodd ht) = .infinity := by
  classical
  rw [diskPointInf]
  split_ifs with ht0
  · rfl
  · apply redPoint_eq_infinity_of_lt
    rw [map_inv₀]
    refine (one_lt_inv₀ ?_).mpr ?_
    · refine zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (infRoot_ne_zero f hf ht ht0)
    · rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact infRoot_mem f hf ht

/-- The forward parameter: `tParam` recovers `t` from the infinity-chart point. -/
theorem tParam_diskPointInf (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) {t : O}
    (ht : t ∈ maximalIdeal O) :
    (diskPointInf (K := K) f hf hodd ht).tParam = algebraMap O K t := by
  classical
  rw [diskPointInf]
  split_ifs with ht0
  · simp [ht0]
  · rw [CurvePoint.tParam_affine, genus_map hf]
    have hφu : algebraMap O K (infRoot f hf ht) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (infRoot_ne_zero f hf ht ht0)
    have hφt : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr ht0
    rw [inv_pow]
    field_simp

/-- The infinity parametrization is injective. -/
theorem diskPointInf_injective (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) :
    Function.Injective fun t : maximalIdeal O ↦ diskPointInf (K := K) f hf hodd t.2 := by
  intro t₁ t₂ h
  have := congrArg CurvePoint.tParam h
  rw [tParam_diskPointInf, tParam_diskPointInf] at this
  exact Subtype.ext (IsFractionRing.injective O K this)

/-- The lifted infinity coordinate `u₀` is the Hensel root `infRoot`: both solve the smooth
equation `u = t²·(reverse f)(u)` in `𝔪`, whose root is unique (`hensel_unique`). -/
theorem eq_infRoot_of_solve {f : O[X]} (hf : f.Monic) {t₀ u₀ : O}
    (hu₀mem : u₀ ∈ maximalIdeal O) (ht₀mem : t₀ ∈ maximalIdeal O)
    (hu₀solve : u₀ = t₀ ^ 2 * (reverse f).eval u₀) :
    u₀ = infRoot f hf ht₀mem := by
  have ht₀2 : t₀ ^ 2 ∈ maximalIdeal O := by rw [sq]; exact Ideal.mul_mem_left _ _ ht₀mem
  refine hensel_unique (f := X - C (t₀ ^ 2) * reverse f) ?_ ?_ ?_
  · exact Ideal.sub_mem _ hu₀mem (infRoot_mem f hf ht₀mem)
  · rw [derivative_sub, derivative_X, derivative_C_mul, eval_sub, eval_one, eval_mul, eval_C]
    exact isUnit_of_sub_mem isUnit_one (by
      rw [show 1 - t₀ ^ 2 * (derivative (reverse f)).eval (infRoot f hf ht₀mem) - 1
          = -(t₀ ^ 2 * (derivative (reverse f)).eval (infRoot f hf ht₀mem)) by ring]
      exact neg_mem (Ideal.mul_mem_right _ _ ht₀2))
  · rw [eval_sub, eval_sub, eval_X, eval_X, eval_mul, eval_mul, eval_C, eval_C,
      ← hu₀solve, ← infRoot_eq]; ring

/-- The infinity parametrization is surjective onto the residue disk of `∞_bar`. -/
theorem diskPointInf_surjective (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree)
    {P : CurvePoint K (f.map (algebraMap O K))} (hP : redPoint P = .infinity) :
    ∃ t : maximalIdeal O, diskPointInf f hf hodd t.2 = P := by
  have : Fact (Odd f.natDegree) := ⟨hodd⟩
  cases P with
  | infinity => exact ⟨⟨0, zero_mem _⟩, diskPointInf_zero f hf hodd⟩
  | affine x y h =>
    have hx1 : 1 < (IsDiscreteValuationRing.maximalIdeal O).valuation K x :=
      (redPoint_eq_infinity_iff hf h).mp hP
    obtain ⟨-, hy1, htlt⟩ := (point_int_or_inf hf h).resolve_left
      (fun hl ↦ absurd hl.1 (not_le.mpr hx1))
    have hx0 : x ≠ 0 := fun hx ↦ by simp [hx] at hx1
    have hy0 : y ≠ 0 := fun hy ↦ by simp [hy] at hy1
    have hxinv : (IsDiscreteValuationRing.maximalIdeal O).valuation K x⁻¹ < 1 := by
      rw [map_inv₀]; exact (inv_lt_one₀ (zero_lt_one.trans hx1)).mpr hx1
    obtain ⟨u₀, hu₀eq, hu₀mem, hu₀0⟩ := exists_lift_mem_ne_zero hxinv (inv_ne_zero hx0)
    obtain ⟨t₀, ht₀eq, ht₀mem, ht₀0⟩ :=
      exists_lift_mem_ne_zero htlt (div_ne_zero (pow_ne_zero _ hx0) hy0)
    have hrev := eval_map_inv_mul_pow (K := K) f hu₀0
    rw [hu₀eq, inv_inv] at hrev
    have hn : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one hodd).symm
    have hu₀solve : u₀ = t₀ ^ 2 * (reverse f).eval u₀ := by
      apply IsFractionRing.injective O K
      rw [map_mul, map_pow, hu₀eq, ht₀eq, ← hrev, ← h, hn]
      field_simp
      rw [one_div, inv_pow, ← pow_mul, ← pow_succ',
        show genus f * 2 + 1 = 2 * genus f + 1 by ring,
        mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hueq : u₀ = infRoot f hf ht₀mem := eq_infRoot_of_solve hf hu₀mem ht₀mem hu₀solve
    refine ⟨⟨t₀, ht₀mem⟩, ?_⟩
    rw [diskPointInf_of_ne_zero _ _ _ _ ht₀0]
    have hcx : (algebraMap O K (infRoot f hf ht₀mem))⁻¹ = x := by rw [← hueq, hu₀eq, inv_inv]
    have hcy : (algebraMap O K (infRoot f hf ht₀mem) ^ genus f * algebraMap O K t₀)⁻¹ = y := by
      rw [← hueq, hu₀eq, ht₀eq]; field_simp
      rw [one_div, ← mul_pow, inv_mul_cancel₀ hx0, one_pow]
    simp only [hcx, hcy]

/-- **Infinity disk parametrization**. The residue disk of `∞_bar` is in bijection with the maximal
ideal, via `t ↦ (1/u, 1/(uᵍt))` (and `0 ↦ ∞`). -/
noncomputable def diskParamInf (f : O[X]) (hf : f.Monic) (hodd : Odd f.natDegree) :
    (maximalIdeal O) ≃ ResidueDisk (K := K)
        (CurvePoint.infinity : CurvePoint (ResidueField O) (f.map (residue O))) :=
  Equiv.ofBijective
    (fun t ↦ ⟨diskPointInf f hf hodd t.2,
      mem_residueDisk.mpr (redPoint_diskPointInf f hf hodd t.2)⟩)
    ⟨fun _ _ h ↦ diskPointInf_injective f hf hodd (congrArg Subtype.val h),
     fun ⟨_, hP⟩ ↦
      let ⟨t, ht⟩ := diskPointInf_surjective f hf hodd (mem_residueDisk.mp hP)
      ⟨t, Subtype.ext ht⟩⟩

end inf

end ChabautyColeman

end
