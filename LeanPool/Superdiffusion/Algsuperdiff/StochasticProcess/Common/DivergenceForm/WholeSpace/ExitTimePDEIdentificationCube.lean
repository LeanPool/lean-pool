/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxGeneralDomainCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationLimit

/-!
# ExitTimePDEIdentificationCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exit-time function of a translated triadic cube

The limit of the Dirichlet resolvents of the constant datum on `y + □_n` as the
shift decreases to zero is identified here with any bounded continuous
representative of the zero-trace solution of
  `-div (a grad w) = 1` in `y + □_n`,  `w = 0` on the boundary,

at every point of the cube.  The identification on the centred exhaustion cubes
is the same argument at the special centre and scale; nothing here refers to
that case, and the solution is *supplied* rather than constructed, so no
existence or sup-norm estimate is repeated.

The argument is the shift-uniform sandwich.  A zero-trace solution of the
constant forcing solves the shifted problem with datum `1 + lam w`, so it is
the shifted resolvent of that datum, and by linearity the difference between it
and the shifted resolvent of the constant datum is `lam` times the shifted
resolvent of itself.  Positivity of the shifted resolvent applied at a small
shift gives that the solution is nonnegative; applied again it gives that the
shifted resolvent of the constant datum stays below the solution; and order
preservation against the uniform bound gives that the gap is at most the shift
times the square of that bound.  Both sides of the sandwich are continuous on
the open cube, so the almost-everywhere statement is pointwise there, and the
supremum along the shifts `1 / (k + 1)` is squeezed to the value of the
representative.

## Main definitions

* `cubeSetAtOneL2` — the `L²` class of the constant datum of `y + □_n`.

## Main results

* `toScalarL2_eq_alphaShiftedResolvent_add_smul` — the resolvent identity
  `w = R_lam (1 + lam w)` for a zero-trace solution of the constant forcing.
* `alphaShiftedResolvent_le_of_isScalarForcedWeakSolution`,
  `sub_alphaShiftedResolvent_le_of_isScalarForcedWeakSolution` — the two halves
  of the shift-uniform sandwich, on an arbitrary open bounded convex domain.
* `cubeSetAtExitFunction_coe_eq_of_isScalarForcedWeakSolution` — the exit-time
  function of `y + □_n` is the continuous representative of the solution at
  every point of the cube.

## References

* ABK26, the localized exit-time problem of Section 5.2.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The shift-uniform sandwich on an open bounded convex domain -/

section Generic

omit [NeZero d] in
/-- **A zero-trace solution of the constant forcing is the shifted resolvent of
the shifted datum.**  This is the identity `w = R_lam (1 + lam w)`. -/
theorem toScalarL2_eq_alphaShiftedResolvent_add_smul
    (a : CoeffField d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu Lam : ℝ} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam U a)
    (w : H10Function U)
    (hw : IsScalarForcedWeakSolution a U (fun _ => (1 : ℝ)) w.toH1Function)
    (one : ScalarL2 U) (hone : ∀ᵐ x ∂volumeMeasureOn U, one x = 1)
    (lam : PositiveShift) :
    w.toH1Function.toScalarL2 =
      alphaShiftedResolvent a lam.property hnu hEll
        (one + (lam : ℝ) • w.toH1Function.toScalarL2) := by
  have hG : ∀ᵐ x ∂volumeMeasureOn U,
      (one + (lam : ℝ) • w.toH1Function.toScalarL2) x =
        (fun _ : Vec d => (1 : ℝ)) x + (lam : ℝ) * w.toH1Function.toFun x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add one
        ((lam : ℝ) • w.toH1Function.toScalarL2),
      MeasureTheory.Lp.coeFn_smul (lam : ℝ) w.toH1Function.toScalarL2,
      hone, w.toH1Function.coeFn_toScalarL2] with x hadd hsmul h1 hw2
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, h1, hw2]
  have hweak := isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution hU
    (alpha := (lam : ℝ)) w hw _ hG
  have heq := (isAlphaShiftedWeakSolution_iff_eq a lam.property hnu hEll _ _).1 hweak
  have hval := congrArg ZeroTraceSobolev.toL2 heq
  rw [ZeroTraceSobolev.toL2_ofH10Function] at hval
  exact hval

omit [NeZero d] in
/-- The gap between the solution and the shifted resolvent of the constant
datum is the shift times the shifted resolvent of the solution. -/
theorem toScalarL2_sub_alphaShiftedResolvent
    (a : CoeffField d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu Lam : ℝ} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam U a)
    (w : H10Function U)
    (hw : IsScalarForcedWeakSolution a U (fun _ => (1 : ℝ)) w.toH1Function)
    (one : ScalarL2 U) (hone : ∀ᵐ x ∂volumeMeasureOn U, one x = 1)
    (lam : PositiveShift) :
    w.toH1Function.toScalarL2 - alphaShiftedResolvent a lam.property hnu hEll one =
      (lam : ℝ) • alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2 := by
  conv_lhs =>
    rw [toScalarL2_eq_alphaShiftedResolvent_add_smul a hU hnu hEll w hw one hone lam]
  rw [map_add, map_smul, add_sub_cancel_left]

omit [NeZero d] in
/-- **A bounded zero-trace solution of the constant forcing is nonnegative.**
At a shift small enough that `1 + lam w` stays nonnegative, the solution is the
shifted resolvent of a nonnegative datum. -/
theorem toScalarL2_nonneg_of_isScalarForcedWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu Lam : ℝ} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam U a)
    (w : H10Function U) {Mb : ℝ}
    (hw : IsScalarForcedWeakSolution a U (fun _ => (1 : ℝ)) w.toH1Function)
    (one : ScalarL2 U) (hone : ∀ᵐ x ∂volumeMeasureOn U, one x = 1)
    (hMb : 0 ≤ Mb)
    (hwb : ∀ᵐ x ∂volumeMeasureOn U, |w.toH1Function.toFun x| ≤ Mb) :
    ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ w.toH1Function.toScalarL2 x := by
  set c : ℝ := (Mb + 1)⁻¹ with hc
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hcM : c * Mb < 1 := by
    rw [hc, inv_mul_eq_div, div_lt_one (by linarith only [hMb])]
    linarith only []
  set lam : PositiveShift := ⟨c, Set.mem_Ioi.mpr hcpos⟩ with hlam
  have hGnn : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ (one + (lam : ℝ) • w.toH1Function.toScalarL2) x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add one
        ((lam : ℝ) • w.toH1Function.toScalarL2),
      MeasureTheory.Lp.coeFn_smul (lam : ℝ) w.toH1Function.toScalarL2,
      hone, w.toH1Function.coeFn_toScalarL2, hwb] with x hadd hsmul h1 hw2 habs
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, h1, hw2]
    have hlow : -Mb ≤ w.toH1Function.toFun x := (abs_le.mp habs).1
    have hstep : -(c * Mb) ≤ c * w.toH1Function.toFun x := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left hlow hcpos.le
    change (0 : ℝ) ≤ 1 + c * w.toH1Function.toFun x
    linarith only [hstep, hcM]
  have hres := alphaShiftedResolvent_nonneg_ae a hU lam.property hnu hEll
    (one + (lam : ℝ) • w.toH1Function.toScalarL2) hGnn
  rw [← toScalarL2_eq_alphaShiftedResolvent_add_smul a hU hnu hEll w hw one hone lam]
    at hres
  exact hres

omit [NeZero d] in
/-- **The lower half of the sandwich.**  The shifted resolvent of the constant
datum never exceeds a bounded zero-trace solution of the constant forcing. -/
theorem alphaShiftedResolvent_le_of_isScalarForcedWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu Lam : ℝ} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam U a)
    (w : H10Function U) {Mb : ℝ}
    (hw : IsScalarForcedWeakSolution a U (fun _ => (1 : ℝ)) w.toH1Function)
    (one : ScalarL2 U) (hone : ∀ᵐ x ∂volumeMeasureOn U, one x = 1)
    (hMb : 0 ≤ Mb)
    (hwb : ∀ᵐ x ∂volumeMeasureOn U, |w.toH1Function.toFun x| ≤ Mb)
    (lam : PositiveShift) :
    ∀ᵐ x ∂volumeMeasureOn U,
      alphaShiftedResolvent a lam.property hnu hEll one x ≤
        w.toH1Function.toScalarL2 x := by
  have hpos := alphaShiftedResolvent_nonneg_ae a hU lam.property hnu hEll
    w.toH1Function.toScalarL2
    (toScalarL2_nonneg_of_isScalarForcedWeakSolution a hU hnu hEll w hw one hone
      hMb hwb)
  have hdiff := toScalarL2_sub_alphaShiftedResolvent a hU hnu hEll w hw one hone lam
  filter_upwards [hpos,
    MeasureTheory.Lp.coeFn_sub w.toH1Function.toScalarL2
      (alphaShiftedResolvent a lam.property hnu hEll one),
    MeasureTheory.Lp.coeFn_smul (lam : ℝ)
      (alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2)] with x hx hsub hsmul
  have hval : w.toH1Function.toScalarL2 x -
      alphaShiftedResolvent a lam.property hnu hEll one x =
      (lam : ℝ) * alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2 x := by
    rw [← Pi.sub_apply, ← hsub, hdiff, hsmul, Pi.smul_apply, smul_eq_mul]
  have hnn : 0 ≤ (lam : ℝ) * alphaShiftedResolvent a lam.property hnu hEll
      w.toH1Function.toScalarL2 x := mul_nonneg lam.property.le hx
  linarith only [hval, hnn]

omit [NeZero d] in
/-- **The upper half of the sandwich.**  The gap between a bounded zero-trace
solution of the constant forcing and the shifted resolvent of the constant
datum is at most the shift times the square of the uniform bound. -/
theorem sub_alphaShiftedResolvent_le_of_isScalarForcedWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu Lam : ℝ} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam U a)
    (w : H10Function U) {Mb : ℝ}
    (hw : IsScalarForcedWeakSolution a U (fun _ => (1 : ℝ)) w.toH1Function)
    (one : ScalarL2 U) (hone : ∀ᵐ x ∂volumeMeasureOn U, one x = 1)
    (hMb : 0 ≤ Mb)
    (hwb : ∀ᵐ x ∂volumeMeasureOn U, |w.toH1Function.toFun x| ≤ Mb)
    (lam : PositiveShift) :
    ∀ᵐ x ∂volumeMeasureOn U,
      w.toH1Function.toScalarL2 x -
          alphaShiftedResolvent a lam.property hnu hEll one x ≤
        (lam : ℝ) * (Mb * Mb) := by
  have hdiff := toScalarL2_sub_alphaShiftedResolvent a hU hnu hEll w hw one hone lam
  have hle : ∀ᵐ x ∂volumeMeasureOn U,
      w.toH1Function.toScalarL2 x ≤ (Mb • one) x := by
    filter_upwards [w.toH1Function.coeFn_toScalarL2, hwb, hone,
      MeasureTheory.Lp.coeFn_smul Mb one] with x hw2 habs h1 hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, h1, mul_one, hw2]
    exact (abs_le.mp habs).2
  have hmono := alphaShiftedResolvent_mono_ae a hU lam.property hnu hEll
    w.toH1Function.toScalarL2 (Mb • one) hle
  have hres : ∀ᵐ x ∂volumeMeasureOn U,
      alphaShiftedResolvent a lam.property hnu hEll w.toH1Function.toScalarL2 x ≤
        Mb * alphaShiftedResolvent a lam.property hnu hEll one x := by
    filter_upwards [hmono, MeasureTheory.Lp.coeFn_smul Mb
      (alphaShiftedResolvent a lam.property hnu hEll one)] with x hx hsmul
    rw [map_smul] at hx
    rw [hsmul, Pi.smul_apply, smul_eq_mul] at hx
    exact hx
  have hup : ∀ᵐ x ∂volumeMeasureOn U, w.toH1Function.toScalarL2 x ≤ Mb := by
    filter_upwards [w.toH1Function.coeFn_toScalarL2, hwb] with x hw2 habs
    rw [hw2]
    exact (abs_le.mp habs).2
  filter_upwards [hres,
    alphaShiftedResolvent_le_of_isScalarForcedWeakSolution a hU hnu hEll w hw one
      hone hMb hwb lam,
    hup,
    MeasureTheory.Lp.coeFn_sub w.toH1Function.toScalarL2
      (alphaShiftedResolvent a lam.property hnu hEll one),
    MeasureTheory.Lp.coeFn_smul (lam : ℝ)
      (alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2)] with x hresx hlowx hupx hsub hsmul
  have hval : w.toH1Function.toScalarL2 x -
      alphaShiftedResolvent a lam.property hnu hEll one x =
      (lam : ℝ) * alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2 x := by
    rw [← Pi.sub_apply, ← hsub, hdiff, hsmul, Pi.smul_apply, smul_eq_mul]
  have hFM : alphaShiftedResolvent a lam.property hnu hEll one x ≤ Mb :=
    le_trans hlowx hupx
  have hstep : Mb * alphaShiftedResolvent a lam.property hnu hEll one x ≤ Mb * Mb :=
    mul_le_mul_of_nonneg_left hFM hMb
  have hfinal : (lam : ℝ) * alphaShiftedResolvent a lam.property hnu hEll
        w.toH1Function.toScalarL2 x ≤ (lam : ℝ) * (Mb * Mb) :=
    mul_le_mul_of_nonneg_left (le_trans hresx hstep) lam.property.le
  rw [hval]
  exact hfinal

end Generic

/-! ## 2. The constant datum of a translated triadic cube as an `L²` class -/

/-- The `L²` class of the constant datum of `y + □_n`: the class the barrier
data of the exit-time problem on that cube is built from. -/
def cubeSetAtOneL2 (y : Vec d) (n : ℤ) : ScalarL2 (cubeSetAt y n) :=
  partDatumL2 (isOpenBoundedConvexDomain_cubeSetAt y n)
    (measurable_cubeSetAtOneDatum y n) (abs_cubeSetAtOneDatum_le y n)

omit [NeZero d] in
theorem cubeSetAtOneL2_ae (y : Vec d) (n : ℤ) :
    ∀ᵐ x ∂volumeMeasureOn (cubeSetAt y n), cubeSetAtOneL2 y n x = 1 := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn
      (isOpenBoundedConvexDomain_cubeSetAt y n)
      ((measurable_cubeSetAtOneDatum y n).comp measurable_subtype_coe)
      (fun z => abs_cubeSetAtOneDatum_le y n z),
    ae_restrict_mem (isOpen_cubeSetAt y n).measurableSet] with x hx hmem
  rw [cubeSetAtOneL2, partDatumL2, hx, domainExtension_of_mem hmem]
  exact cubeSetAtOneDatum_of_mem hmem

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The continuous zero extension of the Dirichlet resolvent of the constant
datum agrees almost everywhere on the cube with the `L²` shifted resolvent of
the constant class. -/
theorem cubeSetAtOneResolvent_ae_alphaShiftedResolvent (y : Vec d) (n : ℤ)
    (lam : PositiveShift) :
    A.cubeSetAtOneResolvent y n lam =ᵐ[volumeMeasureOn (cubeSetAt y n)]
      fun x => alphaShiftedResolvent A.a lam.property A.hnu
        (partEllipticity A (isOpenBoundedConvexDomain_cubeSetAt y n))
        (cubeSetAtOneL2 y n) x :=
  A.cubeSetAtOneResolvent_ae y n lam

/-! ## 3. The exit-time function of a translated triadic cube -/

/-- The value of the exit-time function of `y + □_n` at a point of the live
space is the supremum along the shifts `1 / (k + 1)` of the Dirichlet
resolvents of the constant datum. -/
theorem cubeSetAtExitFunction_coe (y : Vec d) (n : ℤ) (x : Vec d) :
    A.cubeSetAtExitFunction y n (x : OnePoint (Vec d)) =
      ⨆ k : ℕ, ENNReal.ofReal (A.cubeSetAtOneResolvent y n
        ⟨((k : ℝ) + 1)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩ x) := by
  rw [cubeSetAtExitFunction]
  refine iSup_congr fun k => ?_
  exact A.cubeSetAtExitResolvent_coe y n (by positivity) x

/-- **The exit-time function of a translated triadic cube is the continuous
representative of the solution of the constant forcing.**  The solution is
supplied, together with a representative continuous on the cube and a uniform
bound for it there; the identification then holds at every point of the open
cube. -/
theorem cubeSetAtExitFunction_coe_eq_of_isScalarForcedWeakSolution (y : Vec d) (n : ℤ)
    (w : H10Function (cubeSetAt y n))
    (hw : IsScalarForcedWeakSolution A.a (cubeSetAt y n) (fun _ => (1 : ℝ))
      w.toH1Function)
    {wRep : Vec d → ℝ}
    (hae : wRep =ᵐ[volumeMeasureOn (cubeSetAt y n)] w.toH1Function.toFun)
    (hcont : ContinuousOn wRep (cubeSetAt y n))
    {Mb : ℝ} (hMb : 0 ≤ Mb) (hb : ∀ z ∈ cubeSetAt y n, |wRep z| ≤ Mb)
    {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    A.cubeSetAtExitFunction y n (x : OnePoint (Vec d)) = ENNReal.ofReal (wRep x) := by
  set hU : IsOpenBoundedConvexDomain (cubeSetAt y n) :=
    isOpenBoundedConvexDomain_cubeSetAt y n with hUdef
  set hEll : IsEllipticFieldOn A.nu
      (A.cubeEllipticityUpper (partCubeIndex hU)) (cubeSetAt y n) A.a :=
    partEllipticity A hU with hElldef
  have hwb : ∀ᵐ z ∂volumeMeasureOn (cubeSetAt y n),
      |w.toH1Function.toFun z| ≤ Mb := by
    filter_upwards [hae, ae_restrict_mem (isOpen_cubeSetAt y n).measurableSet]
      with z hz hmem
    rw [← hz]
    exact hb z hmem
  have hcontRes : ∀ lam : PositiveShift,
      ContinuousOn (A.cubeSetAtOneResolvent y n lam) (cubeSetAt y n) :=
    fun lam => (A.continuous_cubeSetAtOneResolvent y n lam).continuousOn
  -- the lower half, pointwise on the open cube
  have hlow : ∀ lam : PositiveShift, ∀ z ∈ cubeSetAt y n,
      A.cubeSetAtOneResolvent y n lam z ≤ wRep z := by
    intro lam
    refine le_of_ae_le_of_continuousOn (isOpen_cubeSetAt y n) (hcontRes lam) hcont ?_
    filter_upwards [A.cubeSetAtOneResolvent_ae_alphaShiftedResolvent y n lam,
      alphaShiftedResolvent_le_of_isScalarForcedWeakSolution A.a hU A.hnu hEll w hw
        (cubeSetAtOneL2 y n) (cubeSetAtOneL2_ae y n) hMb hwb lam,
      w.toH1Function.coeFn_toScalarL2, hae] with z hres hcompare hcoe hrep
    rw [hres, hrep, ← hcoe]
    exact hcompare
  -- the upper half, pointwise on the open cube
  have hup : ∀ lam : PositiveShift, ∀ z ∈ cubeSetAt y n,
      wRep z - A.cubeSetAtOneResolvent y n lam z ≤ (lam : ℝ) * (Mb * Mb) := by
    intro lam
    refine le_of_ae_le_of_continuousOn (isOpen_cubeSetAt y n)
      (hcont.sub (hcontRes lam)) continuousOn_const ?_
    filter_upwards [A.cubeSetAtOneResolvent_ae_alphaShiftedResolvent y n lam,
      sub_alphaShiftedResolvent_le_of_isScalarForcedWeakSolution A.a hU A.hnu hEll w
        hw (cubeSetAtOneL2 y n) (cubeSetAtOneL2_ae y n) hMb hwb lam,
      w.toH1Function.coeFn_toScalarL2, hae] with z hres hcompare hcoe hrep
    rw [hres, hrep, ← hcoe]
    exact hcompare
  rw [A.cubeSetAtExitFunction_coe y n x]
  refine iSup_ofReal_eq_of_squeeze (e := Mb * Mb) (fun k => hlow _ x hx) fun k => ?_
  exact hup ⟨((k : ℝ) + 1)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩ x hx

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
