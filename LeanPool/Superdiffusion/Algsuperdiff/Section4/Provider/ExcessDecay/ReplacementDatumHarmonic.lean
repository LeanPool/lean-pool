/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReplacementDatum

/-!
# ReplacementDatumHarmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The passage `v_g → v`: the interior `L²` estimate against the harmonic replacement

## What is proved

`ReplacementDatum.lean` bounds `σ 3^{-n} ‖u − v_g‖_{L²}` against the
auxiliary *forced* replacement `v_g`.  ABK26's display
`e.homogenization.L2.interior` is stated against the *harmonic* replacement
`v`, the two being reconciled by "the triangle inequality" applied to the
forcing correction.  This module performs that passage:

```text
  σ 3^{-n} ‖u − v‖_{L²(Q)}
      ≤ σ 3^{-n} ‖u − v_g‖_{L²(Q)}          (`ReplacementDatum`, datum discharged)
      + σ 3^{-n} ‖v_g − v‖_{L²(Q)} ,
```

and bounds the second summand by

```text
  σ 3^{-n} ‖v_g − v‖_{L²(Q)}
      ≤ 2 C_neg(d) [∇v_g − ∇v]_{B^{-s/2}(Q)}          (negative norm to L²)
      ≤ 2 C_neg(d) K_s^{1/2} σ ‖∇v_g − ∇v‖_{L²(Q)}    (negative ≤ L²)
      ≤ 2 C_neg(d) K_s^{1/2} sqrt d · 3^{s n} [g]_{B^s_{2,2}(Q)}   (forcing correction)
```

where `K_s = (1 − 3^{-s})^{-1}`.

## The `s`-envelope of the correction (reported, not hidden)

`K_s^{1/2} = (1 − 3^{-s})^{-1/2}` behaves like `(3/(2s))^{1/2}` as `s ↓ 0`
(concavity of `s ↦ 1 − 3^{-s}` on `[0,1]` gives `1 − 3^{-s} ≥ 2s/3` there), so
the correction term's honest envelope is `s^{-1/2}`.  It is *not* bounded by a
constant, and it is *not* simplified here: the closed form `Real.sqrt
((geometricDiscount (s/2) 2)⁻¹)` is carried verbatim in the statement.

The manuscript prints no separate correction term at all: its display
`e.homogenization.L2.interior` has the same shape before and after the
triangle step, because both corrections sit inside the same
`C s^{-11/2} (1 + 𝓔) 3^{sn} [g]` summand.  The statement below therefore keeps
the two summands **separate**, which is strictly more informative.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {Q : TriadicCube d}

/-! ## 1. Scalar `L²` plumbing on the cube -/

omit [NeZero d] in
/-- Scalar `L²` membership against the normalized cube measure. -/
theorem memLp_scalar_normalizedCubeMeasure {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f 2 (volumeMeasureOn (openCubeSet Q))) :
    MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q) := by
  have h2 : MeasureTheory.MemLp f 2 (volumeMeasureOn (cubeSet Q)) := by
    rw [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hf
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure] using
    h2.smul_measure ENNReal.ofReal_ne_top

omit [NeZero d] in
/-- Triangle inequality for the normalized scalar `L²` norm, subtractive form. -/
theorem cubeLpNorm_two_sub_le (Q : TriadicCube d) {f g h : Vec d → ℝ}
    (hfgh : ∀ x, f x = g x - h x)
    (hg : MeasureTheory.MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MeasureTheory.MemLp h 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f ≤
      cubeLpNorm Q (2 : ℝ≥0∞) g + cubeLpNorm Q (2 : ℝ≥0∞) h := by
  have hfun : f = g - h := by
    funext x
    simpa using hfgh x
  have hle : MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≤
      MeasureTheory.eLpNorm g 2 (normalizedCubeMeasure Q) +
        MeasureTheory.eLpNorm h 2 (normalizedCubeMeasure Q) := by
    rw [hfun]
    exact MeasureTheory.eLpNorm_sub_le
      (by norm_num)
  have hfin : MeasureTheory.eLpNorm g 2 (normalizedCubeMeasure Q) +
      MeasureTheory.eLpNorm h 2 (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩
  have htoReal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add hg.eLpNorm_ne_top hh.eLpNorm_ne_top] at htoReal
  exact htoReal

/-! ## 2. The harmonic corrector and the difference -/

/-- The chosen corrector of the **harmonic** replacement: `u − v`. -/
def harmonicCorrector (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) : H10Function (openCubeSet Q) :=
  dirichletCorrector a0 u
    (MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q))
      (p := (2 : ENNReal)) (0 : Vec d))

/-- The difference of the two correctors, `ρ_g − ρ_0 = v − v_g`. -/
def replacementCorrection (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H10Function (openCubeSet Q) :=
  dirichletCorrector a0 u hg - harmonicCorrector a0 u

theorem replacementCorrection_grad (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementCorrection a0 u hg).toH1Function.grad x =
      (dirichletCorrector a0 u hg).toH1Function.grad x -
        (harmonicCorrector a0 u).toH1Function.grad x := by
  change ((dirichletCorrector a0 u hg).toH1Function -
    (harmonicCorrector a0 u).toH1Function).grad x = _
  exact congrArg (fun f => f x) (H1Function.sub_grad _ _)

theorem replacementCorrection_toFun (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementCorrection a0 u hg).toH1Function.toFun x =
      (dirichletCorrector a0 u hg).toH1Function.toFun x -
        (harmonicCorrector a0 u).toH1Function.toFun x := by
  change ((dirichletCorrector a0 u hg).toH1Function -
    (harmonicCorrector a0 u).toH1Function).toFun x = _
  exact congrArg (fun f => f x) (H1Function.sub_toFun _ _)

/-- **The difference solves the zero-trace problem with force `−g`.**

This is the equation behind the forcing correction: subtracting the two
constant-coefficient problems removes the datum's own flux `a₀∇u` and leaves the
printed force. -/
theorem isZeroTraceDirichletRhsWeakSolution_replacementCorrection
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) (replacementCorrection a0 u hg) (fun x => -g x) := by
  intro φ
  have hzero : MemVectorL2 (openCubeSet Q) (0 : Vec d → Vec d) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q))
      (p := (2 : ENNReal)) (0 : Vec d)
  have hfluxG : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix ((dirichletCorrector a0 u hg).toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
      (dirichletCorrector a0 u hg).toH1Function.grad_memVectorL2
  have hflux0 : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix ((harmonicCorrector a0 u).toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
      (harmonicCorrector a0 u).toH1Function.grad_memVectorL2
  have hsplit := integral_vecDot_sub_left_split (U := openCubeSet Q) hfluxG hflux0
    (H := fun x =>
      matVecMul a0.matrix ((replacementCorrection a0 u hg).toH1Function.grad x))
    (fun x => by
      show matVecMul a0.matrix
        ((replacementCorrection a0 u hg).toH1Function.grad x) = _
      rw [replacementCorrection_grad, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
        ← sub_eq_add_neg]) φ
  have hforce := integral_vecDot_sub_left_split (U := openCubeSet Q)
    (memVectorL2_correctorForce a0 u hg) (memVectorL2_correctorForce a0 u hzero)
    (H := fun x => -g x)
    (fun x => by
      show -g x = correctorForce a0 u g x - correctorForce a0 u (0 : Vec d → Vec d) x
      rw [correctorForce_apply, correctorForce_apply]
      show -g x = matVecMul a0.matrix (u.grad x) - g x -
        (matVecMul a0.matrix (u.grad x) - (0 : Vec d → Vec d) x)
      funext i
      change -g x i = _
      simp) φ
  have hharmWeak : IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) (harmonicCorrector a0 u)
      (correctorForce a0 u (0 : Vec d → Vec d)) :=
    dirichletCorrector_weakSolution a0 u hzero
  rw [hsplit, dirichletCorrector_weakSolution a0 u hg, hharmWeak φ, ← hforce]

/-! ## 3. The correction bound -/

/-- The `s`-dependent analytic factor of the correction: `(1 − 3^{-s})^{-1/2}`,
carried in closed form.  See the module docstring. -/
def negativeToL2Factor (s : ℝ) : ℝ :=
  Real.sqrt ((geometricDiscount (s / 2) 2)⁻¹)

theorem negativeToL2Factor_nonneg (s : ℝ) : 0 ≤ negativeToL2Factor s :=
  Real.sqrt_nonneg _

omit [NeZero d] in
/-- **The negative seminorm is dominated by the normalized Euclidean `L²`
norm**, with the closed-form geometric factor. -/
theorem cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    {s : ℝ} (hs : 0 < s) {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    cubeBesovNegativeVectorSeminormTwo Q (s / 2) F ≤
      negativeToL2Factor s * normalizedEuclideanL2 Q F := by
  have hFcube : MemVectorL2 (cubeSet Q) F := memVectorL2_cubeSet_of_openCubeSet hF
  have hmem : MeasureTheory.MemLp F (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hFcube
  have hbase := sq_cubeBesovNegativeVectorSeminormTwo_le_l2Average_of_memLp Q
    (s := s / 2) (by linarith only [hs]) F hmem
  rw [← normalizedEuclideanL2_sq hFcube] at hbase
  have hdisc : 0 < geometricDiscount (s / 2) 2 :=
    geometricDiscount_pos (by linarith only [hs])
  have hK : (0 : ℝ) ≤ (geometricDiscount (s / 2) 2)⁻¹ := (inv_pos.mpr hdisc).le
  have hrhs : (0 : ℝ) ≤ negativeToL2Factor s * normalizedEuclideanL2 Q F :=
    mul_nonneg (negativeToL2Factor_nonneg s) (normalizedEuclideanL2_nonneg Q F)
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hrhs ?_
  rw [mul_pow, negativeToL2Factor, Real.sq_sqrt hK]
  exact hbase

/-- **The correction term of the triangle step.**

```text
  σ 3^{-scale(Q)} ‖v_g − v‖_{L²(Q)}
      ≤ 2 C_neg(d) K_s^{1/2} sqrt d · 3^{s·scale(Q)} [g]_{B^s_{2,2}(Q)} .
```
-/
theorem replacementCorrection_l2_le {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hgL2 : MemVectorL2 (openCubeSet Q) g) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hg : Ch03.ForceBesovRegularity Q s g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
          (replacementCorrection (scalarComparator hsigma0) u hgL2).toH1Function.toFun
            x) ≤
      2 * negNormBaseConst d * negativeToL2Factor s *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
  set a0 : Ch03.ConstantCoeffMatrix d := scalarComparator hsigma0 with ha0
  set w : H10Function (openCubeSet Q) := replacementCorrection a0 u hgL2 with hwdef
  set N : ℝ := normalizedEuclideanL2 Q fun x => w.toH1Function.grad x with hNdef
  -- the negative-norm step
  have hneg := cubeLpNorm_h10_le_negativeBesov_quarter Q w.toCubeSet hs hs1
  rw [H10Function.toCubeSet_toH1Function_toFun,
    H10Function.toCubeSet_toH1Function_grad] at hneg
  -- negative seminorm against the Euclidean L²
  have hdom := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    (Q := Q) (s := s) hs (F := fun x => w.toH1Function.grad x)
    w.toH1Function.grad_memVectorL2
  have hCpos : (0 : ℝ) ≤ 2 * negNormBaseConst d := by
    have := negNormBaseConst_pos d
    linarith only [this]
  have hstep : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => w.toH1Function.toFun x) ≤
      2 * negNormBaseConst d * (negativeToL2Factor s * N) :=
    hneg.trans (mul_le_mul_of_nonneg_left hdom hCpos)
  -- the forcing correction
  have hEll : IsEllipticFieldOn a0.lam a0.Lam (openCubeSet Q)
      (constantCoeffField a0.matrix) := isEllipticFieldOn_openCubeSet Q a0
  have hlam : a0.lam = sigma0 := rfl
  have hforce := forcingCorrection_le (Q := Q)
    (a := constantCoeffField a0.matrix) (lam := a0.lam) (Lam := a0.Lam) (s := s)
    (g := g) w (isZeroTraceDirichletRhsWeakSolution_replacementCorrection a0 u hgL2)
    hEll hgL2 hg
  rw [hlam] at hforce
  -- assemble
  have hfacnonneg : (0 : ℝ) ≤ 2 * negNormBaseConst d * negativeToL2Factor s :=
    mul_nonneg hCpos (negativeToL2Factor_nonneg s)
  calc sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) fun x => w.toH1Function.toFun x)
      ≤ sigma0 * (2 * negNormBaseConst d * (negativeToL2Factor s * N)) :=
        mul_le_mul_of_nonneg_left hstep hsigma0.le
    _ = 2 * negNormBaseConst d * negativeToL2Factor s * (sigma0 * N) := by ring
    _ ≤ 2 * negNormBaseConst d * negativeToL2Factor s *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) :=
        mul_le_mul_of_nonneg_left hforce hfacnonneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
