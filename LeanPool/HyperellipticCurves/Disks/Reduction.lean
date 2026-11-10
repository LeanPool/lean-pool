/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.CurvePoint
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Reduction and residue disks

Over the fraction field `K` of a discrete valuation ring `O` with residue field `κ`, we reduce
points of the hyperelliptic curve `y² = f(x)` (`f : O[X]` monic) to the residue curve
`y_bar² = f_bar(x_bar)` over `κ`.

`ChabautyColeman.redK : K → κ` reduces an integral element (unique lift to `O`, then
`IsLocalRing.residue`; junk value `0` outside the valuation ring).
`ChabautyColeman.redPoint` sends a finite-type (integral) affine point to its coordinatewise
reduction and every other point to `∞_bar`; `ChabautyColeman.ResidueDisk P_bar` is the fiber of the
reduction over `P_bar`.

## Main definitions

* `ChabautyColeman.redK`: reduction `K → κ` of an integral element.
* `ChabautyColeman.redPoint`: reduction of a curve point to the residue curve.
* `ChabautyColeman.ResidueDisk`: the residue disk (fiber of `redPoint`) of a residue point.

## Main statements

* `ChabautyColeman.redEqn`: the reduced coordinates of an integral affine point satisfy the
  residue curve equation.
* `ChabautyColeman.redPoint_eq_infinity_iff`: an affine point reduces to `∞_bar` iff it is of
  infinite type (`𝓋 x > 1`) — the reduction half of `lem:two-charts`.

Blueprint node: `def:disk`.
-/

@[expose] public section

open Polynomial IsDedekindDomain IsLocalRing

namespace ChabautyColeman

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- Reduction of an integral element of `K` to the residue field of `O`; junk value `0`
outside the valuation ring. The lift to `O` is unique, so this is well defined. -/
noncomputable def redK (x : K) : ResidueField O :=
  if hx : 𝓋 x ≤ 1 then residue O (IsDiscreteValuationRing.exists_lift_of_le_one hx).choose
  else 0

@[simp] theorem redK_algebraMap (a : O) : redK (algebraMap O K a) = residue O a := by
  have hle : 𝓋 (algebraMap O K a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal O).valuation_le_one a
  rw [redK, dite_eq_left hle]
  congr 1
  exact IsFractionRing.injective O K
    ((IsDiscreteValuationRing.exists_lift_of_le_one hle).choose_spec.trans rfl)

/-- The reduction of the curve equation: if `(x, y)` is an integral affine point of the curve
`y² = f(x)` over `K`, its reduction `(x_bar, y_bar)` lies on the residue curve `y_bar² =
f_bar(x_bar)`. -/
theorem redEqn {f : O[X]} {x y : K} (he : y ^ 2 = (f.map (algebraMap O K)).eval x)
    (hx : 𝓋 x ≤ 1) (hy : 𝓋 y ≤ 1) :
    redK y ^ 2 = (f.map (residue O)).eval (redK x) := by
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
  obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hy
  rw [eval_map_apply, ← map_pow] at he
  rw [redK_algebraMap, redK_algebraMap, ← map_pow, IsFractionRing.injective O K he, eval_map_apply]

/-- Reduction of a point: a finite-type (integral) affine point reduces coordinatewise to the
residue curve; every other point reduces to the point at infinity. -/
noncomputable def redPoint {f : O[X]} :
    CurvePoint K (f.map (algebraMap O K)) → CurvePoint (ResidueField O) (f.map (residue O))
  | .affine x y he =>
      if hx : 𝓋 x ≤ 1 then
        if hy : 𝓋 y ≤ 1 then .affine (redK x) (redK y) (redEqn he hx hy) else .infinity
      else .infinity
  | .infinity => .infinity

@[simp] theorem redPoint_infinity {f : O[X]} :
    redPoint (.infinity : CurvePoint K (f.map (algebraMap O K))) = .infinity := rfl

theorem redPoint_affine {f : O[X]} {x y : K} (he : y ^ 2 = (f.map (algebraMap O K)).eval x)
    (hx : 𝓋 x ≤ 1) (hy : 𝓋 y ≤ 1) :
    redPoint (.affine x y he : CurvePoint K (f.map (algebraMap O K)))
      = .affine (redK x) (redK y) (redEqn he hx hy) := by
  simp only [redPoint, dite_eq_left hx, dite_eq_left hy]

theorem redPoint_eq_infinity_of_lt {f : O[X]} {x y : K}
    (he : y ^ 2 = (f.map (algebraMap O K)).eval x) (hx : 1 < 𝓋 x) :
    redPoint (.affine x y he) = .infinity := by
  simp only [redPoint, dite_eq_right (not_le.mpr hx)]

theorem redPoint_eq_infinity_of_not_le {f : O[X]} {x y : K}
    (he : y ^ 2 = (f.map (algebraMap O K)).eval x) (hx : 𝓋 x ≤ 1) (hy : ¬𝓋 y ≤ 1) :
    redPoint (.affine x y he) = .infinity := by
  simp only [redPoint, dite_eq_left hx, dite_eq_right hy]

/-- An affine point reduces to the point at infinity exactly when it is of infinite type
(`𝓋 x > 1`); this is the reduction half of `lem:two-charts`. -/
theorem redPoint_eq_infinity_iff {f : O[X]} (hf : f.Monic) [Fact (Odd f.natDegree)]
    {x y : K} (he : y ^ 2 = (f.map (algebraMap O K)).eval x) :
    redPoint (.affine x y he) = .infinity ↔ 1 < 𝓋 x := by
  refine ⟨fun h ↦ ?_, redPoint_eq_infinity_of_lt he⟩
  by_contra! hx
  have hy := ((point_int_or_inf hf he).resolve_right fun hh ↦ absurd hx (not_le.mpr hh.1)).2
  rw [redPoint_affine he hx hy] at h
  exact nomatch h

/-- A curve point that reduces to an affine residue point is itself an integral affine point:
both coordinates lift from `O`, with the prescribed residues, and satisfy the curve equation over
`O`. This packages the case split (the point is neither `∞` nor of infinite type) shared by the
generic and Weierstrass chart surjectivity proofs. -/
theorem exists_lift_of_redPoint_affine {f : O[X]}
    {P : CurvePoint K (f.map (algebraMap O K))} {xr yr : ResidueField O}
    {he : yr ^ 2 = (f.map (residue O)).eval xr} (hP : redPoint P = .affine xr yr he) :
    ∃ x₀ y₀ : O, y₀ ^ 2 = f.eval x₀ ∧ residue O x₀ = xr ∧ residue O y₀ = yr ∧
      ∀ hxy : algebraMap O K y₀ ^ 2 = (f.map (algebraMap O K)).eval (algebraMap O K x₀),
        P = .affine (algebraMap O K x₀) (algebraMap O K y₀) hxy := by
  cases P with
  | infinity => simp only [redPoint_infinity, reduceCtorEq] at hP
  | affine x y hxy =>
    by_cases hx : 𝓋 x ≤ 1
    · by_cases hy : 𝓋 y ≤ 1
      · obtain ⟨x₀, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
        obtain ⟨y₀, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hy
        rw [redPoint_affine hxy hx hy] at hP
        simp only [redK_algebraMap] at hP
        refine ⟨x₀, y₀, ?_, ?_, ?_, fun _ ↦ rfl⟩
        · have h' := hxy
          rw [← map_pow, eval_map_apply] at h'
          exact IsFractionRing.injective O K h'
        · simpa using congrArg CurvePoint.xCoord hP
        · simpa using congrArg CurvePoint.yCoord hP
      · rw [redPoint_eq_infinity_of_not_le hxy hx hy] at hP
        simp only [reduceCtorEq] at hP
    · rw [redPoint_eq_infinity_of_lt hxy (not_le.mp hx)] at hP
      simp only [reduceCtorEq] at hP

/-- The residue disk of `P_bar`: the fiber of the reduction map over `P_bar`. -/
def ResidueDisk {f : O[X]} (P : CurvePoint (ResidueField O) (f.map (residue O))) :
    Set (CurvePoint K (f.map (algebraMap O K))) := redPoint ⁻¹' {P}

theorem mem_residueDisk {f : O[X]} {P : CurvePoint (ResidueField O) (f.map (residue O))}
    {Q : CurvePoint K (f.map (algebraMap O K))} : Q ∈ ResidueDisk P ↔ redPoint Q = P := Iff.rfl

theorem infinity_notMem_residueDisk_affine {f : O[X]} {x y : ResidueField O}
    {he : y ^ 2 = (f.map (residue O)).eval x} :
    (.infinity : CurvePoint K (f.map (algebraMap O K))) ∉ ResidueDisk (.affine x y he) := by
  simp [mem_residueDisk]

end ChabautyColeman

end
