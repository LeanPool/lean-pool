/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# GammaTenStripMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A **cell-uniform** envelope for the realized upper ellipticity constant

ABK26, Step 2 of `l.approximate.recurrence.formula`, `e.CG.bounds.2`.

## The gap this module fills

```
  Lam_R(omega) = Cutoff.coefficientCutoffCubeEllipticityUpper M m omega R
```

at a **fixed** cube `R`, but its majorant carries the local control
`cutoffLocalControl (cubeOriginCoverScale R) m omega`, whose scale is the
canonical origin cover of `R` and therefore moves with `R`.  A grid estimate
over a mesh of cells needs one envelope valid at **every** cell of the mesh at
once.

That envelope is supplied here.  It is *not* a transport: `Lam_R` depends on the
cell only through the integer `cubeOriginCoverScale R`, so there is nothing to
translate --- the mesh-uniform reading is obtained by **monotonicity in the
cover scale**, which is the honest cost of the crude elliptic bound and is
recorded as such below.

## What is proved

* `localCubeControl_mono`, `cutoffLocalControl_mono` --- the deterministic local
  control and its lower-tail series are monotone in the cube scale: a larger
  origin cube can only have a larger sup.
* `cubeOriginCoverScale_mono` --- the canonical origin cover is monotone under
  inclusion of open cubes.  This is minimality of `Nat.find`, not geometry.
* `stripEllipticityEnvelope` --- `Kmaj (1 + u_{cover Q})^2` at the cover scale
  of the **enclosing** cube `Q`, and
  `coefficientCutoffCubeEllipticityUpper_le_stripEllipticityEnvelope`, the
  envelope property at every cube `R` with `openCubeSet R subset openCubeSet Q`.
* `stripEllipticityWeight` --- the combination `Lam + 2 nu^{-1} Lam^2` in which
  the Step-2 majorant reads the ellipticity constant, at the envelope;
  `ellipticityUpper_weight_le_stripEllipticityWeight` is its envelope property.
* `integrable_sq_stripEllipticityWeight` and `stripLambdaMoment` --- the
  **second moment of the weight**, i.e. the fourth moment of the envelope, as a
  finite explicit number.  Its finiteness is the binomial expansion of
  `(1+u)^{2k}` against `Cutoff.P4UpperMoments.integrable_one_add_cutoffLocalControl_pow`.

## The scale of the envelope, stated plainly

`stripLambdaMoment M m Q` is a number attached to the **enclosing cube** `Q`.
When `Q = cu_{Kc}` is the localization cube, that number depends on `Kc`: the
local control at scale `cubeOriginCoverScale (originCube d Kc)` is a supremum of
the shell field over a cube of side `~3^{Kc}`, and the lower-tail law makes its
moments grow with the scale.  No claim of `Kc`-independence is made anywhere
below, and none is used.

## Binders

`stripEllipticityEnvelope`'s envelope property is conditional on the single
geometric containment `openCubeSet R subset openCubeSet Q` and on nothing else:
no smallness, no measurability, no moment and no model gate occurs.  The moment
statements are unconditional.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.CG.bounds.2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Set
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of the deterministic local control -/

/-- The local control at scale `ell` bounds the matrix operator norm of the
shell at every point of the open origin cube at that scale.  This is the step of
`Cutoff.abs_entry_le_localCubeControl` before the entry is extracted. -/
private theorem matrixOperatorNorm_le_localCubeControl (ell : ℤ) (j : ShellField d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    matrixOperatorNorm (j x) ≤ localCubeControl ell j := by
  let r : ℝ := cubeScaleFactor (originCube d ell)
  have hr_pos : 0 < r := by
    simpa [r, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) ell)
  have hx_scaled : r⁻¹ • x ∈ openCubeSet (originCube d 0) := by
    have hx' : x ∈ cubeScaleFactor (originCube d ell) •
        openCubeSet (originCube d 0) := by
      rw [← openCubeSet_originCube_eq_smul_originCube_zero (d := d) ell]
      exact hx
    change x ∈ r • openCubeSet (originCube d 0) at hx'
    rw [Set.mem_smul_set] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [← hxy, smul_smul, inv_mul_cancel₀ (ne_of_gt hr_pos), one_smul]
    exact hy
  let y : ShellField.UnitOpenCubePoint d := ⟨r⁻¹ • x, hx_scaled⟩
  calc matrixOperatorNorm (j x)
      = matrixOperatorNorm ((ShellField.spatialScale r j) y.1) := by
        rw [ShellField.spatialScale_apply]
        congr 2
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    _ ≤ ShellField.unitCubeValueNorm (ShellField.spatialScale r j) :=
        ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm _ y
    _ = localCubeControl ell j := rfl

/-- Open origin cubes are nested in the scale. -/
private theorem openCubeSet_originCube_subset_of_le {q q' : ℤ} (hq : q ≤ q') :
    openCubeSet (originCube d q) ⊆ openCubeSet (originCube d q') := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ q' := zpow_le_zpow_right₀ (by norm_num) hq
  rcases hx i with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- **The local control is monotone in the cube scale.**  Unconditional. -/
theorem localCubeControl_mono {q q' : ℤ} (hq : q ≤ q') (j : ShellField d) :
    localCubeControl q j ≤ localCubeControl q' j := by
  have hr_pos : (0 : ℝ) < cubeScaleFactor (originCube d q) := by
    simpa [cubeScaleFactor] using! (zpow_pos (show (0 : ℝ) < 3 by norm_num) q)
  unfold localCubeControl ShellField.unitCubeValueNorm
  apply csSup_le
  · exact ⟨0, none, rfl⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact localCubeControl_nonneg q' j
  | some x =>
    have hmem : cubeScaleFactor (originCube d q) • x.1 ∈
        openCubeSet (originCube d q) := by
      rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) q, Set.mem_smul_set]
      exact ⟨x.1, x.2, rfl⟩
    have hmem' : cubeScaleFactor (originCube d q) • x.1 ∈
        openCubeSet (originCube d q') :=
      openCubeSet_originCube_subset_of_le hq hmem
    have hstep := matrixOperatorNorm_le_localCubeControl q' j hmem'
    change matrixOperatorNorm
      ((ShellField.spatialScale (cubeScaleFactor (originCube d q)) j) x.1) ≤ _
    rwa [ShellField.spatialScale_apply]

/-- **The lower-tail local-control series is monotone in the cube scale.**
Unconditional; both series are summable on the public cutoff carrier. -/
theorem cutoffLocalControl_mono {ell ell' : ℤ} (hell : ell ≤ ell') (m : ℤ)
    (omega : CutoffSample d) :
    cutoffLocalControl ell m omega ≤ cutoffLocalControl ell' m omega := by
  refine Summable.tsum_le_tsum (fun r => localCubeControl_mono hell _)
    (summable_cutoffLocalControl ell m omega) (summable_cutoffLocalControl ell' m omega)

/-! ## Monotonicity of the canonical origin cover -/

/-- **The canonical origin cover scale is monotone under inclusion of open
cubes.**  This is minimality of the cover depth, not geometry: the enclosing
cube's own cover already covers the closure of the smaller open cube.

only on `hsub`. -/
theorem cubeOriginCoverScale_mono {Q R : TriadicCube d}
    (hsub : openCubeSet R ⊆ openCubeSet Q) :
    cubeOriginCoverScale R ≤ cubeOriginCoverScale Q := by
  have hcl : closure (openCubeSet R) ⊆
      openCubeSet (originCube d ((cubeOriginCoverDepth Q : ℕ) : ℤ)) :=
    (closure_mono hsub).trans (closure_subset_originCover Q)
  have hle : cubeOriginCoverDepth R ≤ cubeOriginCoverDepth Q :=
    cubeOriginCoverDepth_le R (cubeOriginCoverDepth Q) hcl
  have hcast : ((cubeOriginCoverDepth R : ℕ) : ℤ) ≤ ((cubeOriginCoverDepth Q : ℕ) : ℤ) := by
    exact_mod_cast hle
  exact hcast

/-! ## The cell-uniform envelope -/

/-- **The cell-uniform envelope of the realized upper ellipticity constant.**

`Kmaj (1 + u_{cover Q})^2`, with `Kmaj = Cutoff.cutoffUpperEllipticityMajorant M` the
dimensional constant of `Cutoff.P4UpperMoments` and `u_{cover Q}` the lower-tail local
control read at the canonical origin cover of the **enclosing** cube `Q`.  It does not
mention the cell. -/
def stripEllipticityEnvelope (M : ABKModel d) (m : ℤ) (Q : TriadicCube d)
    (omega : CutoffSample d) : ℝ :=
  cutoffUpperEllipticityMajorant M *
    (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2

/-- The realized upper ellipticity constant is nonnegative: it is a quotient of two
nonnegative reals.  Unconditional; the same three lines as in `Cutoff.P4UpperMoments`,
repeated here rather than importing a whole Step-2 layer for them. -/
private theorem ellipticityUpper_nonneg (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (R : TriadicCube d) :
    0 ≤ coefficientCutoffCubeEllipticityUpper M m omega R := by
  unfold coefficientCutoffCubeEllipticityUpper
  refine div_nonneg ?_ M.nu_pos.le
  positivity

theorem cutoffUpperEllipticityMajorant_nonneg (M : ABKModel d) :
    0 ≤ cutoffUpperEllipticityMajorant M := by
  unfold cutoffUpperEllipticityMajorant
  refine div_nonneg ?_ M.nu_pos.le
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  positivity

theorem stripEllipticityEnvelope_nonneg (M : ABKModel d) (m : ℤ) (Q : TriadicCube d)
    (omega : CutoffSample d) : 0 ≤ stripEllipticityEnvelope M m Q omega := by
  have hu : (0 : ℝ) ≤ cutoffLocalControl (cubeOriginCoverScale Q) m omega :=
    cutoffLocalControl_nonneg _ _ _
  refine mul_nonneg (cutoffUpperEllipticityMajorant_nonneg M) ?_
  positivity

/-- **The envelope property.**  At every cube whose open cube sits inside the
enclosing cube's open cube, the realized upper ellipticity constant is below the
envelope of the enclosing cube.

only on the geometric containment `hsub`. -/
theorem coefficientCutoffCubeEllipticityUpper_le_stripEllipticityEnvelope
    (M : ABKModel d) (m : ℤ) {Q R : TriadicCube d}
    (hsub : openCubeSet R ⊆ openCubeSet Q) (omega : CutoffSample d) :
    coefficientCutoffCubeEllipticityUpper M m omega R ≤
      stripEllipticityEnvelope M m Q omega := by
  have hu0 : (0 : ℝ) ≤ cutoffLocalControl (cubeOriginCoverScale R) m omega :=
    cutoffLocalControl_nonneg _ _ _
  have hu : cutoffLocalControl (cubeOriginCoverScale R) m omega ≤
      cutoffLocalControl (cubeOriginCoverScale Q) m omega :=
    cutoffLocalControl_mono (cubeOriginCoverScale_mono hsub) m omega
  refine (coefficientCutoffCubeEllipticityUpper_le_majorant M m omega R).trans ?_
  have hsq : (1 + cutoffLocalControl (cubeOriginCoverScale R) m omega) ^ 2 ≤
      (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact mul_le_mul_of_nonneg_left hsq (cutoffUpperEllipticityMajorant_nonneg M)

/-! ## The weight in which the Step-2 majorant reads the constant -/

/-- **The Step-2 ellipticity weight at the envelope**: `E + 2 nu^{-1} E^2`, the
combination in which `Closure.GammaTenStripCell.stripCellMajorant` multiplies the
potential cell energy. -/
def stripEllipticityWeight (M : ABKModel d) (m : ℤ) (Q : TriadicCube d)
    (omega : CutoffSample d) : ℝ :=
  stripEllipticityEnvelope M m Q omega +
    2 * M.nu⁻¹ * stripEllipticityEnvelope M m Q omega ^ 2

theorem stripEllipticityWeight_nonneg (M : ABKModel d) (m : ℤ) (Q : TriadicCube d)
    (omega : CutoffSample d) : 0 ≤ stripEllipticityWeight M m Q omega := by
  have hE : (0 : ℝ) ≤ stripEllipticityEnvelope M m Q omega :=
    stripEllipticityEnvelope_nonneg M m Q omega
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  unfold stripEllipticityWeight
  positivity

/-- **The envelope property of the weight.**  Monotonicity of
`t |-> t + 2 nu^{-1} t^2` on the nonnegative half line.

only on the geometric containment `hsub`. -/
theorem ellipticityUpper_weight_le_stripEllipticityWeight
    (M : ABKModel d) (m : ℤ) {Q R : TriadicCube d}
    (hsub : openCubeSet R ⊆ openCubeSet Q) (omega : CutoffSample d) :
    coefficientCutoffCubeEllipticityUpper M m omega R +
        2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M m omega R ^ 2 ≤
      stripEllipticityWeight M m Q omega := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hL0 : (0 : ℝ) ≤ coefficientCutoffCubeEllipticityUpper M m omega R :=
    ellipticityUpper_nonneg M m omega R
  have hle := coefficientCutoffCubeEllipticityUpper_le_stripEllipticityEnvelope
    M m hsub omega
  have hsq : coefficientCutoffCubeEllipticityUpper M m omega R ^ 2 ≤
      stripEllipticityEnvelope M m Q omega ^ 2 := pow_le_pow_left₀ hL0 hle 2
  have hinv : (0 : ℝ) ≤ 2 * M.nu⁻¹ := by positivity
  have hmul : 2 * M.nu⁻¹ * coefficientCutoffCubeEllipticityUpper M m omega R ^ 2 ≤
      2 * M.nu⁻¹ * stripEllipticityEnvelope M m Q omega ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hinv
  unfold stripEllipticityWeight
  linarith

/-- The envelope is a measurable function of the sample: it is a polynomial in
the measurable local control.  Unconditional. -/
theorem measurable_stripEllipticityEnvelope (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Measurable (fun omega : CutoffSample d => stripEllipticityEnvelope M m Q omega) := by
  unfold stripEllipticityEnvelope
  exact measurable_const.mul
    ((measurable_const.add (measurable_cutoffLocalControl (cubeOriginCoverScale Q) m)).pow_const 2)

/-- The weight is a measurable function of the sample.  Unconditional. -/
theorem measurable_stripEllipticityWeight (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Measurable (fun omega : CutoffSample d => stripEllipticityWeight M m Q omega) := by
  unfold stripEllipticityWeight
  exact (measurable_stripEllipticityEnvelope M m Q).add
    (measurable_const.mul ((measurable_stripEllipticityEnvelope M m Q).pow_const 2))

/-! ## The second moment of the weight -/

/-- **The weight has a finite second moment.**  Expanding the square, the integrand
is a fixed nonnegative combination of `(1 + u)^4`, `(1 + u)^6` and `(1 + u)^8`,
each integrable by `Cutoff.P4UpperMoments.integrable_one_add_cutoffLocalControl_pow`.
Unconditional. -/
theorem integrable_sq_stripEllipticityWeight (M : ABKModel d) (m : ℤ)
    (Q : TriadicCube d) :
    Integrable (fun omega : CutoffSample d => stripEllipticityWeight M m Q omega ^ 2)
      (cutoffSampleLaw M).toMeasure := by
  have h4 := integrable_one_add_cutoffLocalControl_pow M (cubeOriginCoverScale Q) m 4
  have h6 := integrable_one_add_cutoffLocalControl_pow M (cubeOriginCoverScale Q) m 6
  have h8 := integrable_one_add_cutoffLocalControl_pow M (cubeOriginCoverScale Q) m 8
  have hsum : Integrable (fun omega : CutoffSample d =>
      cutoffUpperEllipticityMajorant M ^ 2 *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 4 +
        (4 * M.nu⁻¹ * cutoffUpperEllipticityMajorant M ^ 3 *
            (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 6 +
          4 * M.nu⁻¹ ^ 2 * cutoffUpperEllipticityMajorant M ^ 4 *
            (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 8))
      (cutoffSampleLaw M).toMeasure :=
    ((h4.const_mul _).add ((h6.const_mul _).add (h8.const_mul _)))
  have hEq : (fun omega : CutoffSample d => stripEllipticityWeight M m Q omega ^ 2) =
      fun omega : CutoffSample d =>
        cutoffUpperEllipticityMajorant M ^ 2 *
            (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 4 +
          (4 * M.nu⁻¹ * cutoffUpperEllipticityMajorant M ^ 3 *
              (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 6 +
            4 * M.nu⁻¹ ^ 2 * cutoffUpperEllipticityMajorant M ^ 4 *
              (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 8) := by
    funext omega
    unfold stripEllipticityWeight stripEllipticityEnvelope
    ring
  rw [hEq]
  exact hsum

/-- **The mesh-uniform ellipticity moment**, as an explicit finite number: the
second sample moment of the Step-2 ellipticity weight at the envelope of the
enclosing cube.  It is the only place where the crude elliptic bound pays for
the coefficient, and it is attached to `Q`, not to a cell. -/
def stripLambdaMoment (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) : ℝ :=
  ∫ omega, stripEllipticityWeight M m Q omega ^ 2 ∂(cutoffSampleLaw M).toMeasure

theorem stripLambdaMoment_nonneg (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    0 ≤ stripLambdaMoment M m Q :=
  integral_nonneg fun _ => sq_nonneg _

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
