/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.Reduction
public import LeanPool.HyperellipticCurves.Series.HenselRoot
public import LeanPool.HyperellipticCurves.Series.PSeries
public import LeanPool.HyperellipticCurves.Series.SqrtSeries

import LeanPool.HyperellipticCurves.ForMathlib.LocalRing

/-!
# Disk parametrizations: the generic and Weierstrass charts

For a generic residue point `P_bar = (ā, b_bar)` with `b_bar ≠ 0` on the residue curve, the residue
disk
`D_P_bar` is parametrized by `𝔪` via `z ↦ (a + z, b · η(z))`, where `(a, b)` is an integral lift
(`b² = f(a)`, with `f(a)` a unit since `b_bar ≠ 0`) and `η := ` the square-root series of
`f(a+z)/f(a)` (`ChabautyColeman.diskSeriesGeneric`). The parametrization `z ↦ (a+z, b·η(z))` is
a bijection `𝔪 ≃ D_P_bar` (`ChabautyColeman.diskParamGeneric`): every point reduces to `P_bar` (so
lies
in `D_P_bar`), the map is injective (its `x`-coordinate is `a+z`), and surjective — the square-root
sign of the `y`-coordinate is pinned down by the common nonzero reduction `b_bar`.

The **Weierstrass chart** at a point `(ω_bar, 0)` (with `f(ω) = 0`, `f'(ω)` a unit) is parametrized
by `y ↦ (x, y)`, where `x ≡ ω` is the Hensel root of `f = y²`
(`ChabautyColeman.diskParamWeierstrass`, via `ChabautyColeman.exists_weierstrass_root` and
`ChabautyColeman.hensel_unique`); no power series in the parameter is needed for the bijection.
The infinity chart is developed separately.

## Main definitions

* `ChabautyColeman.diskSeriesGeneric`: the parametrizing series `η` with `η² = f(a+z)/f(a)`.
* `ChabautyColeman.diskPointGeneric` / `diskPointWeierstrass`: the curve point at parameter.
* `ChabautyColeman.diskParamGeneric` / `diskParamWeierstrass`: the bijections `𝔪 ≃ D_P_bar`.

## Main statements

* `ChabautyColeman.generic_onCurve`: `(b · η(z))² = f(a + z)`.
* `ChabautyColeman.redPoint_diskPointGeneric` / `redPoint_diskPointWeierstrass`: the parametrized
  point reduces to `P_bar`.
* `ChabautyColeman.eq_of_sq_eq_of_residue_eq`: a square root is determined by its reduction.

Blueprint node: `lem:disk-param` (generic and Weierstrass charts).
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial IsDedekindDomain

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-- The generic-disk parametrizing series `η` with `η² = f(a+z)/f(a)` and `η(0) = 1`. -/
noncomputable def diskSeriesGeneric (f : O[X]) (a : O) : O⟦X⟧ :=
  sqrtSeries ((taylor a f : O⟦X⟧) * PowerSeries.C (Ring.inverse (f.eval a))) 1 (Ring.inverse 2)

@[simp] theorem constantCoeff_diskSeriesGeneric (f : O[X]) (a : O) :
    constantCoeff (diskSeriesGeneric f a) = 1 := constantCoeff_sqrtSeries _ _ _

/-- If `b² = f(a)` is a unit then so is `b`; this encodes genericity (`b_bar ≠ 0`). -/
theorem isUnit_b {f : O[X]} {a b : O} (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) :
    IsUnit b :=
  (isUnit_pow_iff two_ne_zero).mp (hb ▸ hfa)

section localRing

variable [IsLocalRing O]

/-- In a local ring with `2` a unit, an element is determined by its square and its (nonzero)
reduction: the two square roots have distinct reductions. -/
theorem eq_of_sq_eq_of_residue_eq (h2 : IsUnit (2 : O)) {w w' : O} (hsq : w ^ 2 = w' ^ 2)
    (hres : residue O w = residue O w') (hne : residue O w ≠ 0) : w = w' := by
  have hne0 : residue O (w + w') ≠ 0 := by
    rw [map_add, hres, ← two_mul]
    refine mul_ne_zero ?_ (hres ▸ hne)
    exact (map_ofNat (residue O) 2 : residue O (2 : O) = (2 : ResidueField O)) ▸
      (h2.map (residue O)).ne_zero
  have hunit : IsUnit (w + w') := (residue_ne_zero_iff_isUnit _).mp hne0
  have hz : (w - w') * (w + w') = 0 := by linear_combination hsq
  linear_combination (IsUnit.mul_left_eq_zero hunit).mp hz

/-- An element congruent to a unit modulo `𝔪` is a unit. -/
theorem isUnit_of_sub_mem {a b : O} (hu : IsUnit a) (h : b - a ∈ maximalIdeal O) : IsUnit b :=
  notMem_maximalIdeal.mp fun hb ↦ (notMem_maximalIdeal.mpr hu) (by simpa using sub_mem hb h)

/-- A polynomial with unit value at `ω` has unit value at every point congruent to `ω`
modulo `𝔪`. -/
theorem isUnit_eval_of_sub_mem {g : O[X]} {x ω : O} (hu : IsUnit (g.eval ω))
    (h : x - ω ∈ maximalIdeal O) : IsUnit (g.eval x) :=
  isUnit_of_sub_mem hu <| by
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub x ω g; rw [hc]; exact Ideal.mul_mem_right c _ h

end localRing

/-! ### The Weierstrass-disk root -/

section hensel

variable [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]

/-- The Weierstrass-disk root of `f = y²` near `ω` (Hensel; `exists_weierstrass_root`). -/
noncomputable def weierstrassRoot {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O}
    (hy : y ∈ maximalIdeal O) : O :=
  (exists_weierstrass_root hf hdeg hω hu hy).choose

theorem weierstrassRoot_eval {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O) :
    f.eval (weierstrassRoot hf hdeg hω hu hy) = y ^ 2 :=
  (exists_weierstrass_root hf hdeg hω hu hy).choose_spec.1

theorem weierstrassRoot_sub {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O) :
    weierstrassRoot hf hdeg hω hu hy - ω ∈ maximalIdeal O :=
  (exists_weierstrass_root hf hdeg hω hu hy).choose_spec.2

/-- **The Weierstrass-disk root is the only square root parameter in the disk**: any `x ≡ ω`
with `f(x) = y²` is it (Hensel uniqueness at the simple root `ω`). -/
theorem weierstrassRoot_eq_of_eval_sq {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O)
    {x : O} (hx : x - ω ∈ maximalIdeal O) (hsq : f.eval x = y ^ 2) :
    weierstrassRoot hf hdeg hω hu hy = x :=
  hensel_unique (by simpa using sub_mem (weierstrassRoot_sub hf hdeg hω hu hy) hx)
    (isUnit_eval_of_sub_mem hu hx)
    ((weierstrassRoot_eval hf hdeg hω hu hy).trans hsq.symm)

end hensel

section eval

variable [UniformSpace O] [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- The defining identity of the generic parametrization: `(b · η(z))² = f(a + z)` for
`z ∈ 𝔪`, where `b² = f(a)` and `f(a)` is a unit. -/
theorem generic_onCurve (f : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z : O} (hz : z ∈ maximalIdeal O) :
    (b * PSeries.eval z (diskSeriesGeneric f a)) ^ 2 = f.eval (a + z) := by
  set c := (taylor a f : O⟦X⟧) * PowerSeries.C (Ring.inverse (f.eval a)) with hc
  have hcc : constantCoeff c = 1 := by
    rw [hc, map_mul, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, taylor_coeff_zero,
      constantCoeff_C, Ring.mul_inverse_cancel _ hfa]
  have hηc : diskSeriesGeneric f a ^ 2 = c :=
    sqrtSeries_sq c (by rw [one_pow, hcc]) (by rw [mul_one]; exact Ring.mul_inverse_cancel _ h2)
  have e2 : PSeries.eval z c = f.eval (a + z) * Ring.inverse (f.eval a) := by
    rw [hc, PSeries.eval_mul hz, PSeries.eval_C, PSeries.eval_coe, taylor_apply, eval_comp,
      eval_add, eval_X, eval_C, add_comm z a]
  rw [mul_pow, ← PSeries.eval_pow hz, hηc, e2, hb]
  linear_combination f.eval (a + z) * Ring.mul_inverse_cancel (f.eval a) hfa

/-- The `y`-coordinate `b · η(z)` of the parametrized point reduces to `b_bar` (since `η(0) = 1`).
-/
theorem residue_b_mul_eval {f : O[X]} (a b : O) {z : O} (hz : z ∈ maximalIdeal O) :
    residue O (b * PSeries.eval z (diskSeriesGeneric f a)) = residue O b := by
  have hmem : PSeries.eval z (diskSeriesGeneric f a) - 1 ∈ maximalIdeal O := by
    have := PSeries.eval_sub_constantCoeff_mem hz (diskSeriesGeneric f a)
    rwa [constantCoeff_diskSeriesGeneric] at this
  rw [map_mul, show residue O (PSeries.eval z (diskSeriesGeneric f a)) = 1 from ?_, mul_one]
  exact (residue_eq_of_sub_mem hmem).trans (map_one _)

end eval

section dvr

variable [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {K : Type*} [Field K] [Algebra O K]

/-- The generic-disk parametrized point of the curve over `K` at parameter `z ∈ 𝔪`:
`(a + z, b · η(z))` in integral coordinates. -/
noncomputable def diskPointGeneric (f : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z : O} (hz : z ∈ maximalIdeal O) :
    CurvePoint K (f.map (algebraMap O K)) :=
  .affine (algebraMap O K (a + z))
    (algebraMap O K (b * PSeries.eval z (diskSeriesGeneric f a)))
    (onCurve_map _ (generic_onCurve f hb hfa h2 hz))

@[simp] theorem xCoord_diskPointGeneric (f : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z : O} (hz : z ∈ maximalIdeal O) :
    (diskPointGeneric (K := K) f hb hfa h2 hz).xCoord = algebraMap O K (a + z) :=
  rfl

@[simp] theorem yCoord_diskPointGeneric (f : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z : O} (hz : z ∈ maximalIdeal O) :
    (diskPointGeneric (K := K) f hb hfa h2 hz).yCoord
      = algebraMap O K (b * PSeries.eval z (diskSeriesGeneric f a)) :=
  rfl

/-- The parametrized point of a generic disk depends only on the parameter (the membership
proof is irrelevant). -/
theorem diskPointGeneric_congr {f : O[X]} {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z z' : O} (hz : z ∈ maximalIdeal O)
    (hz' : z' ∈ maximalIdeal O) (h : z = z') :
    diskPointGeneric (K := K) f hb hfa h2 hz = diskPointGeneric f hb hfa h2 hz' := by
  subst h; rfl

variable [IsFractionRing O K]

/-- The generic-disk parametrized point reduces to the residue point `(ā, b_bar)`; hence it lies in
the residue disk `D_(ā, b_bar)`. -/
theorem redPoint_diskPointGeneric (f : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) {z : O} (hz : z ∈ maximalIdeal O) :
    redPoint (diskPointGeneric (K := K) f hb hfa h2 hz)
      = .affine (residue O a) (residue O b)
          (onCurve_map _ hb) := by
  have hX : residue O (a + z) = residue O a := by
    rw [map_add, show residue O z = 0 from (residue_eq_zero_iff z).mpr hz, add_zero]
  have hY := residue_b_mul_eval (f := f) a b hz
  rw [diskPointGeneric,
    redPoint_affine _ ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _)
      ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _)]
  simp only [redK_algebraMap, hX, hY]

/-- The parametrization `z ↦ (a + z, b · η(z))` is injective (its `x`-coordinate is `a + z`). -/
theorem diskPointGeneric_injective {f : O[X]} {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    Function.Injective fun z : maximalIdeal O ↦ diskPointGeneric (K := K) f hb hfa h2 z.2 := by
  intro z₁ z₂ h
  have hx := congrArg CurvePoint.xCoord h
  simp only [xCoord_diskPointGeneric] at hx
  exact Subtype.ext (add_left_cancel (IsFractionRing.injective O K hx))

/-- Every point of the residue disk `D_(ā, b_bar)` is `(a + z, b · η(z))` for a unique `z ∈ 𝔪`:
the parametrization is surjective onto the disk. The square-root sign is pinned down by the
common reduction `b_bar ≠ 0` (`eq_of_sq_eq_of_residue_eq`). -/
theorem diskPointGeneric_surjective {f : O[X]} {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    {P : CurvePoint K (f.map (algebraMap O K))}
    (hP : redPoint P = .affine (residue O a) (residue O b)
            (onCurve_map _ hb)) :
    ∃ z : maximalIdeal O, diskPointGeneric f hb hfa h2 z.2 = P := by
  obtain ⟨x₀, y₀, hyO, hxr, hyr, hPeq⟩ := exists_lift_of_redPoint_affine hP
  have hzmem : x₀ - a ∈ maximalIdeal O := by rw [← residue_eq_zero_iff, map_sub, hxr, sub_self]
  have hw' : b * PSeries.eval (x₀ - a) (diskSeriesGeneric f a) = y₀ := by
    refine eq_of_sq_eq_of_residue_eq h2 ?_ ?_ ?_
    · rw [generic_onCurve f hb hfa h2 hzmem, hyO, add_sub_cancel a x₀]
    · rw [residue_b_mul_eval a b hzmem]; exact hyr.symm
    · rw [residue_b_mul_eval a b hzmem]
      exact ((isUnit_b hb hfa).map (residue O)).ne_zero
  refine ⟨⟨x₀ - a, hzmem⟩, ?_⟩
  rw [hPeq (onCurve_map _ hyO)]
  simp only [diskPointGeneric, add_sub_cancel a x₀, hw']

/-- **Generic disk parametrization**. The residue disk of a generic point `(ā, b_bar)` (with `b_bar
≠ 0`,
encoded by `f(a)` a unit) is in bijection with the maximal ideal, via `z ↦ (a + z, b · η(z))`. -/
noncomputable def diskParamGeneric {f : O[X]} {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    (maximalIdeal O) ≃ ResidueDisk (K := K)
        (.affine (residue O a) (residue O b)
          (onCurve_map _ hb) :
          CurvePoint (ResidueField O) (f.map (residue O))) :=
  Equiv.ofBijective
    (fun z ↦ ⟨diskPointGeneric f hb hfa h2 z.2,
      mem_residueDisk.mpr (redPoint_diskPointGeneric f hb hfa h2 z.2)⟩)
    ⟨fun _ _ h ↦ diskPointGeneric_injective hb hfa h2 (congrArg Subtype.val h),
     fun ⟨_, hP⟩ ↦
      let ⟨z, hz⟩ := diskPointGeneric_surjective hb hfa h2 (mem_residueDisk.mp hP)
      ⟨z, Subtype.ext hz⟩⟩

end dvr

/-! ### The Weierstrass chart -/

section weierstrass

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
  {K : Type*} [Field K] [Algebra O K]

/-- The Weierstrass-disk parametrized point at parameter `y ∈ 𝔪`: `(x, y)` with `x` the Hensel
root of `f = y²` near `ω`. -/
noncomputable def diskPointWeierstrass {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O) :
    CurvePoint K (f.map (algebraMap O K)) :=
  .affine (algebraMap O K (weierstrassRoot hf hdeg hω hu hy)) (algebraMap O K y)
    (onCurve_map _ (weierstrassRoot_eval hf hdeg hω hu hy).symm)

@[simp] theorem xCoord_diskPointWeierstrass {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O}
    (hy : y ∈ maximalIdeal O) :
    (diskPointWeierstrass (K := K) hf hdeg hω hu hy).xCoord
      = algebraMap O K (weierstrassRoot hf hdeg hω hu hy) :=
  rfl

@[simp] theorem yCoord_diskPointWeierstrass {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O}
    (hy : y ∈ maximalIdeal O) :
    (diskPointWeierstrass (K := K) hf hdeg hω hu hy).yCoord = algebraMap O K y :=
  rfl

/-- The Weierstrass-disk parametrized point depends only on the parameter. -/
theorem diskPointWeierstrass_congr {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y y' : O}
    (hy : y ∈ maximalIdeal O) (hy' : y' ∈ maximalIdeal O) (h : y = y') :
    diskPointWeierstrass (K := K) hf hdeg hω hu hy
      = diskPointWeierstrass hf hdeg hω hu hy' := by
  subst h; rfl

variable [IsFractionRing O K]

/-- The Weierstrass-disk parametrized point reduces to `(ω_bar, 0)`; hence it lies in the residue
disk `D_(ω_bar, 0)`. -/
theorem redPoint_diskPointWeierstrass {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O) :
    redPoint (diskPointWeierstrass (K := K) hf hdeg hω hu hy)
      = .affine (residue O ω) 0
          (onCurve_map_of_root _ hω) := by
  have hX : residue O (weierstrassRoot hf hdeg hω hu hy) = residue O ω :=
    residue_eq_of_sub_mem (weierstrassRoot_sub hf hdeg hω hu hy)
  have hY : residue O y = 0 := (residue_eq_zero_iff y).mpr hy
  rw [diskPointWeierstrass,
    redPoint_affine _ ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _)
      ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _)]
  simp only [redK_algebraMap, hX, hY]

/-- The Weierstrass parametrization `y ↦ (x, y)` is injective (its `y`-coordinate is `y`). -/
theorem diskPointWeierstrass_injective {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    Function.Injective fun y : maximalIdeal O ↦
      diskPointWeierstrass (K := K) hf hdeg hω hu y.2 := by
  intro y₁ y₂ h
  have hy := congrArg CurvePoint.yCoord h
  simp only [yCoord_diskPointWeierstrass] at hy
  exact Subtype.ext (IsFractionRing.injective O K hy)

/-- Every point of `D_(ω_bar, 0)` is `(x, y)` for a unique `y ∈ 𝔪`, with `x` the Hensel root: the
parametrization is surjective onto the disk (uniqueness of the root is `hensel_unique`). -/
theorem diskPointWeierstrass_surjective {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    {P : CurvePoint K (f.map (algebraMap O K))}
    (hP : redPoint P = .affine (residue O ω) 0
            (onCurve_map_of_root _ hω)) :
    ∃ y : maximalIdeal O, diskPointWeierstrass hf hdeg hω hu y.2 = P := by
  obtain ⟨x₀, y₀, hyO, hxr, hyr, hPeq⟩ := exists_lift_of_redPoint_affine hP
  have hymem : y₀ ∈ maximalIdeal O := (residue_eq_zero_iff _).mp hyr
  have hxwr : x₀ = weierstrassRoot hf hdeg hω hu hymem :=
    (weierstrassRoot_eq_of_eval_sq hf hdeg hω hu hymem
      ((residue_eq_zero_iff _).mp (by rw [map_sub, hxr, sub_self])) hyO.symm).symm
  refine ⟨⟨y₀, hymem⟩, ?_⟩
  rw [hPeq (onCurve_map _ hyO)]
  simp only [diskPointWeierstrass, ← hxwr]

/-- **Weierstrass disk parametrization**. The residue disk of a Weierstrass point `(ω_bar, 0)` (with
`f(ω) = 0` and `f'(ω)` a unit) is in bijection with the maximal ideal, via `y ↦ (x, y)` where
`x ≡ ω` is the Hensel root of `f = y²`. -/
noncomputable def diskParamWeierstrass {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    (maximalIdeal O) ≃ ResidueDisk (K := K)
        (.affine (residue O ω) 0
          (onCurve_map_of_root _ hω) :
          CurvePoint (ResidueField O) (f.map (residue O))) :=
  Equiv.ofBijective
    (fun y ↦ ⟨diskPointWeierstrass hf hdeg hω hu y.2,
      mem_residueDisk.mpr (redPoint_diskPointWeierstrass hf hdeg hω hu y.2)⟩)
    ⟨fun _ _ h ↦ diskPointWeierstrass_injective hf hdeg hω hu (congrArg Subtype.val h),
     fun ⟨_, hP⟩ ↦
      let ⟨y, hy⟩ := diskPointWeierstrass_surjective hf hdeg hω hu (mem_residueDisk.mp hP)
      ⟨y, Subtype.ext hy⟩⟩

end weierstrass

end ChabautyColeman

end
