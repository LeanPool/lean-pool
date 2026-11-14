/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicReplacement
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Basic

/-!
# ForcingCorrection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The forcing correction: the two inequalities

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The printed display

```text
  σ_{n+2} ‖∇v − ∇v_g‖_{L²(x+□_n)}
      ≤ ‖g − (g)_{x+□_n}‖_{L²(x+□_n)}
      ≤ C 3^{sn} [g]_{H^s(x+□_n)} .
```

This module proves both.

## First inequality: the energy comparison

Stated here in the general form it actually has, for *any* zero-trace weak
solution of `−∇·a∇w = ∇·G` on the cube:

```text
  λ ‖∇w‖_{L²(Q)}  ≤  ‖G − (G)_Q‖_{L²(Q)} .
```

The proof is the printed one: test the equation with `w` itself, subtract the
mean of `G` for free because `∫_Q ∇w = 0` for `w ∈ H¹₀(Q)`, and use ellipticity
on the left — all three steps packaged in CoarseGraining's
`IsZeroTraceDirichletRhsWeakSolution.energy_le_sub_const_rhs_pairing_of_isEllipticFieldOn`
— and then absorb the right-hand pairing by the **sharp** pointwise Young
inequality `|vecDot x y| ≤ λ⁻¹|x|²/2 + λ|y|²/2` (CoarseGraining's
`abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq` at the weights `(λ^{-1/2},
λ^{1/2})`), which returns the constant `1` exactly.

Applied to `w = v_g − v` and `G = −g` — the difference of the two replacements
of `HarmonicReplacement.lean` — and to the scalar background `a₀ = σ Id`, where
`λ = σ`, this is the printed first inequality with the printed constant `1`.

## Second inequality: the fractional Poincaré, at constant `1`

```text
  cubeBesovPositiveVectorDepthSeminorm Q s g 0
      = 3^{s·0} · sqrt(descendantsAverage Q 0 (R ↦ ‖g − (g)_R‖²_{L²(R)}))
      = ‖g − (g)_Q‖_{L²(Q)} ,
```

and every depth term is bounded by the partial seminorm, which is bounded by
`cubeBesovPositiveVectorSeminormTwo Q s g = 3^{s·scale} [g]_{B^s_{2,2}(Q)}`.
No fractional-Poincaré constant is needed: `C = 1`.

## Carriers, and the one dimensional constant (disclosed)

The manuscript's `‖·‖_{L²}` for a **vector** field is the normalized
*Euclidean* `L²` norm, `normalizedEuclideanL2` below.  CoarseGraining's
`cubeLpNorm` measures the ambient `Vec d = Fin d → ℝ` **sup** norm instead, so
passing from the Euclidean carrier (in which the energy comparison lives) to
the Besov carrier (in which the seminorm lives) costs the factor `sqrt d`, and
nothing else — `Ch03.cubeAverage_vecNormSq_le_card_mul_cubeLpNorm_two_sq`.
Consequently the composed statement `forcingCorrection_le` carries `sqrt d`
where the manuscript writes `C(d)`; this is the *only* constant in the display,
and it is `d`-only, as printed.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The normalized Euclidean `L²` carrier -/

/-- The manuscript's `‖F‖_{L²(Q)}` for a vector field: the normalized `L²`
norm taken with the **Euclidean** norm on `ℝ^d`. -/
def normalizedEuclideanL2 (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ :=
  cubeLpNorm Q (2 : ℝ≥0∞) fun x => HilbertVec.ofVec (F x)

theorem normalizedEuclideanL2_nonneg (Q : TriadicCube d) (F : Vec d → Vec d) :
    0 ≤ normalizedEuclideanL2 Q F :=
  cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _

/-- Transport of vector `L²` membership between the two cube realizations. -/
theorem memVectorL2_cubeSet_of_openCubeSet {Q : TriadicCube d} {F : Vec d → Vec d}
    (h : MemVectorL2 (openCubeSet Q) F) : MemVectorL2 (cubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact h

/-- Transport of vector `L²` membership between the two cube realizations. -/
theorem memVectorL2_openCubeSet_of_cubeSet {Q : TriadicCube d} {F : Vec d → Vec d}
    (h : MemVectorL2 (cubeSet Q) F) : MemVectorL2 (openCubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact h

/-- The manuscript's clause (iv) already gives `g ∈ L²` on the window. -/
theorem memVectorL2_openCubeSet_of_forceBesovRegularity {Q : TriadicCube d} {s : ℝ}
    {g : Vec d → Vec d} (hg : Ch03.ForceBesovRegularity Q s g) :
    MemVectorL2 (openCubeSet Q) g :=
  memVectorL2_openCubeSet_of_cubeSet
    (Ch03.memVectorL2_cubeSet_of_forceBesovRegularity hg)

/-- Hilbertified `L²` membership against the normalized cube measure. -/
theorem memLp_hilbert_normalizedCubeMeasure {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F) :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (normalizedCubeMeasure Q) := by
  have hHilbert : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (volumeMeasureOn (cubeSet Q)) := memHilbertVectorL2_hilbertifyVecField hF
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure] using
    hHilbert.smul_measure ENNReal.ofReal_ne_top

/-- The square of the normalized Euclidean `L²` norm is the Euclidean square
average. -/
theorem normalizedEuclideanL2_sq {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F) :
    (normalizedEuclideanL2 Q F) ^ (2 : ℕ) = cubeAverage Q fun x => vecNormSq (F x) := by
  have hmem := memLp_hilbert_normalizedCubeMeasure hF
  have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := (2 : ℝ≥0∞))
    (f := fun x => HilbertVec.ofVec (F x)) (by norm_num) (by norm_num) hmem
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
  simp only [Real.rpow_natCast] at hbase
  rw [normalizedEuclideanL2, hbase]
  refine congrArg (cubeAverage Q) ?_
  funext x
  rw [HilbertVec.norm_sq_ofVec]
  rfl

/-- Euclidean against sup: the only dimensional constant of this module. -/
theorem normalizedEuclideanL2_le_sqrt_card_mul {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F) :
    normalizedEuclideanL2 Q F ≤
      Real.sqrt (Fintype.card (Fin d) : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) F := by
  have hmem : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
  have hsq := Ch03.cubeAverage_vecNormSq_le_card_mul_cubeLpNorm_two_sq
    (Q := Q) (F := F) hmem
  rw [← normalizedEuclideanL2_sq hF] at hsq
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) := by positivity
  have hlp : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) F := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hrhs : (0 : ℝ) ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) F :=
    mul_nonneg (Real.sqrt_nonneg _) hlp
  have hrhs_sq :
      (Real.sqrt (Fintype.card (Fin d) : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℕ) =
        (Fintype.card (Fin d) : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hcard]
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hrhs ?_
  rw [hrhs_sq]
  exact hsq

/-! ## 2. The sharp weighted Young inequality -/

/-- The sharp weighted Young inequality on `ℝ^d`, at the elliptic weight. -/
theorem vecDot_le_inv_mul_add_mul {lam : ℝ} (hlam : 0 < lam) (x y : Vec d) :
    vecDot x y ≤ lam⁻¹ * vecNormSq x / 2 + lam * vecNormSq y / 2 := by
  have hinv : (0 : ℝ) ≤ lam⁻¹ := (inv_pos.mpr hlam).le
  have hprod : Real.sqrt lam⁻¹ * Real.sqrt lam = 1 := by
    rw [← Real.sqrt_mul hinv, inv_mul_cancel₀ hlam.ne', Real.sqrt_one]
  have hbase := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (Real.sqrt lam⁻¹) (Real.sqrt lam) x y
  rw [hprod, one_mul, Real.sq_sqrt hinv, Real.sq_sqrt hlam.le] at hbase
  exact (le_abs_self _).trans hbase

/-! ## 3. The energy comparison -/

/-- **The first inequality of the forcing correction, in its general form.**

For a zero-trace weak solution of `−∇·a∇w = ∇·G` on the open cube `Q`,

```text
  λ ‖∇w‖_{L²(Q)}  ≤  ‖G − (G)_Q‖_{L²(Q)} ,
```

with constant `1`.  The mean subtraction is free (`∫_Q ∇w = 0`). -/
theorem zeroTraceEnergy_le_normalizedEuclideanL2_fluctuation {Q : TriadicCube d}
    {a : CoeffField d} {lam Lam : ℝ} {G : Vec d → Vec d}
    (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q) w G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    lam * normalizedEuclideanL2 Q (fun x => w.toH1Function.grad x) ≤
      normalizedEuclideanL2 Q (cubeFluctuationVec Q G) := by
  obtain ⟨x0, hx0⟩ := Ch02.openCubeSet_nonempty Q
  have hlam : 0 < lam := (hEll.2 x0 hx0).1
  have hfluctOpen : MemVectorL2 (openCubeSet Q) (cubeFluctuationVec Q G) :=
    hG.sub (MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q))
      (p := (2 : ℝ≥0∞)) (cubeAverageVec Q G))
  have hgradCube : MemVectorL2 (cubeSet Q) fun x => w.toH1Function.grad x :=
    memVectorL2_cubeSet_of_openCubeSet w.toH1Function.grad_memVectorL2
  have hfluctCube : MemVectorL2 (cubeSet Q) (cubeFluctuationVec Q G) :=
    memVectorL2_cubeSet_of_openCubeSet hfluctOpen
  -- the two square integrals
  have hgradSqInt : MeasureTheory.IntegrableOn
      (fun x => vecNormSq (w.toH1Function.grad x)) (openCubeSet Q) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2
      w.toH1Function.grad_memVectorL2 w.toH1Function.grad_memVectorL2
  have hfluctSqInt : MeasureTheory.IntegrableOn
      (fun x => vecNormSq (cubeFluctuationVec Q G x)) (openCubeSet Q) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hfluctOpen hfluctOpen
  have hpairInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (cubeFluctuationVec Q G x) (w.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hfluctOpen w.toH1Function.grad_memVectorL2
  -- the elliptic energy identity with the mean subtracted
  have hbase := hw.energy_le_sub_const_rhs_pairing_of_isEllipticFieldOn hEll hG
    (cubeAverageVec Q G)
  -- the Young absorption
  have hyoung : ∫ x in openCubeSet Q,
        vecDot (cubeFluctuationVec Q G x) (w.toH1Function.grad x)
          ∂MeasureTheory.volume ≤
      ∫ x in openCubeSet Q,
        (lam⁻¹ * vecNormSq (cubeFluctuationVec Q G x) / 2 +
          lam * vecNormSq (w.toH1Function.grad x) / 2) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_mono_ae hpairInt ?_ ?_
    · exact ((hfluctSqInt.const_mul lam⁻¹).div_const 2).add
        ((hgradSqInt.const_mul lam).div_const 2)
    · exact Filter.Eventually.of_forall fun x =>
        vecDot_le_inv_mul_add_mul hlam _ _
  have hsplit : ∫ x in openCubeSet Q,
        (lam⁻¹ * vecNormSq (cubeFluctuationVec Q G x) / 2 +
          lam * vecNormSq (w.toH1Function.grad x) / 2) ∂MeasureTheory.volume =
      lam⁻¹ / 2 * (∫ x in openCubeSet Q,
          vecNormSq (cubeFluctuationVec Q G x) ∂MeasureTheory.volume) +
        lam / 2 * ∫ x in openCubeSet Q,
          vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add ((hfluctSqInt.const_mul lam⁻¹).div_const 2)
      ((hgradSqInt.const_mul lam).div_const 2)]
    rw [show (fun x => lam⁻¹ * vecNormSq (cubeFluctuationVec Q G x) / 2) =
        fun x => (lam⁻¹ / 2) * vecNormSq (cubeFluctuationVec Q G x) by
      funext x; ring]
    rw [show (fun x => lam * vecNormSq (w.toH1Function.grad x) / 2) =
        fun x => (lam / 2) * vecNormSq (w.toH1Function.grad x) by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- absorb
  set A : ℝ := ∫ x in openCubeSet Q,
    vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume with hAdef
  set B : ℝ := ∫ x in openCubeSet Q,
    vecNormSq (cubeFluctuationVec Q G x) ∂MeasureTheory.volume with hBdef
  have hchain : lam * A ≤ lam⁻¹ / 2 * B + lam / 2 * A := by
    rw [← hsplit]
    exact hbase.trans hyoung
  have hlaminv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
  have habsorb : lam ^ (2 : ℕ) * A ≤ B := by
    have hmul : (2 * lam) * (lam * A) ≤ (2 * lam) * (lam⁻¹ / 2 * B + lam / 2 * A) :=
      mul_le_mul_of_nonneg_left hchain (by positivity)
    have hexp : (2 * lam) * (lam⁻¹ / 2 * B + lam / 2 * A) =
        (lam * lam⁻¹) * B + lam ^ (2 : ℕ) * A := by ring
    rw [hexp, hlaminv, one_mul] at hmul
    have hleft : (2 * lam) * (lam * A) = lam ^ (2 : ℕ) * A + lam ^ (2 : ℕ) * A := by ring
    rw [hleft] at hmul
    linarith only [hmul]
  -- normalize
  have hvolnonneg : (0 : ℝ) ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg Q)
  have hAcube : cubeAverage Q (fun x => vecNormSq (w.toH1Function.grad x)) =
      (cubeVolume Q)⁻¹ * A := by
    rw [cubeAverage, hAdef]
    exact congrArg (fun t => (cubeVolume Q)⁻¹ * t)
      setIntegral_cubeSet_eq_setIntegral_openCubeSet
  have hBcube : cubeAverage Q (fun x => vecNormSq (cubeFluctuationVec Q G x)) =
      (cubeVolume Q)⁻¹ * B := by
    rw [cubeAverage, hBdef]
    exact congrArg (fun t => (cubeVolume Q)⁻¹ * t)
      setIntegral_cubeSet_eq_setIntegral_openCubeSet
  have hnormsq : (lam * normalizedEuclideanL2 Q fun x => w.toH1Function.grad x) ^ (2 : ℕ) ≤
      (normalizedEuclideanL2 Q (cubeFluctuationVec Q G)) ^ (2 : ℕ) := by
    rw [mul_pow, normalizedEuclideanL2_sq hgradCube, normalizedEuclideanL2_sq hfluctCube,
      hAcube, hBcube]
    have hstep : (cubeVolume Q)⁻¹ * (lam ^ (2 : ℕ) * A) ≤ (cubeVolume Q)⁻¹ * B :=
      mul_le_mul_of_nonneg_left habsorb hvolnonneg
    calc lam ^ (2 : ℕ) * ((cubeVolume Q)⁻¹ * A)
        = (cubeVolume Q)⁻¹ * (lam ^ (2 : ℕ) * A) := by ring
      _ ≤ (cubeVolume Q)⁻¹ * B := hstep
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num)
    (normalizedEuclideanL2_nonneg Q _) hnormsq

/-! ## 4. The fractional Poincaré at constant `1` -/

/-- The depth-`0` Besov term **is** the normalized oscillation. -/
theorem cubeBesovPositiveVectorDepthSeminorm_zero_eq (Q : TriadicCube d) (s : ℝ)
    (g : Vec d → Vec d) :
    cubeBesovPositiveVectorDepthSeminorm Q s g 0 =
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q g) := by
  have havg : cubeBesovPositiveVectorDepthAverage Q g 0 =
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q g)) ^ (2 : ℕ) := by
    rw [cubeBesovPositiveVectorDepthAverage, descendantsAverage]
    simp [descendantsAtDepth_zero]
  rw [cubeBesovPositiveVectorDepthSeminorm, havg,
    Real.sqrt_sq (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _)]
  norm_num

/-- **The second inequality of the forcing correction, at constant `1`.**

```text
  ‖g − (g)_Q‖_{L²(Q)}  ≤  3^{s·scale(Q)} [g]_{B^s_{2,2}(Q)} .
```

In the manuscript's normalization the right-hand side is written `C 3^{sn}
[g]_{H^s}`; CoarseGraining's seminorm already carries the factor `3^{sn}`, and
the constant is `1`. -/
theorem cubeLpNorm_fluctuation_le_besovSeminorm (Q : TriadicCube d) {s : ℝ}
    {g : Vec d → Vec d} (hg : Ch03.ForceBesovRegularity Q s g) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q g) ≤
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  have hpartial := cubeBesovPositiveVectorDepthSeminorm_le_partialSeminormTwo Q s g 0 0
    (by simp)
  rw [cubeBesovPositiveVectorDepthSeminorm_zero_eq Q s g] at hpartial
  exact hpartial.trans (cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
    Q s g hg.partialSeminorms_bddAbove 0)

/-! ## 5. The composed display -/

/-- The fluctuation of `−g` is the negative of the fluctuation of `g`. -/
theorem cubeFluctuationVec_neg (Q : TriadicCube d) (g : Vec d → Vec d) :
    cubeFluctuationVec Q (fun x => -g x) = fun x => -(cubeFluctuationVec Q g x) := by
  funext x
  funext i
  have haverage : cubeAverageVec Q (fun y => -g y) i = -cubeAverageVec Q g i := by
    rw [cubeAverageVec, cubeAverageVec, cubeAverage, cubeAverage]
    simp [MeasureTheory.integral_neg]
  change (-g x) i - cubeAverageVec Q (fun y => -g y) i = -(g x i - cubeAverageVec Q g i)
  rw [haverage]
  simp only [Pi.neg_apply]
  ring

/-- **The forcing correction, composed.**

For a zero-trace weak solution of `−∇·a∇w = ∇·(−g)` (the difference of the
forced and the harmonic replacement, `w = v_g − v`):

```text
  λ ‖∇w‖_{L²(Q)} ≤ ‖g − (g)_Q‖_{L²(Q)}
                  ≤ sqrt d · 3^{s·scale(Q)} [g]_{B^s_{2,2}(Q)} .
```

The `sqrt d` is the Euclidean-vs-sup carrier conversion documented in the module
docstring; the manuscript writes `C(d)`. -/
theorem forcingCorrection_le {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {s : ℝ} {g : Vec d → Vec d} (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q) w (fun x => -g x))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hgL2 : MemVectorL2 (openCubeSet Q) g)
    (hg : Ch03.ForceBesovRegularity Q s g) :
    lam * normalizedEuclideanL2 Q (fun x => w.toH1Function.grad x) ≤
      Real.sqrt (Fintype.card (Fin d) : ℝ) *
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  have hnegL2 : MemVectorL2 (openCubeSet Q) fun x => -g x := hgL2.neg
  have henergy := zeroTraceEnergy_le_normalizedEuclideanL2_fluctuation
    (Q := Q) (a := a) (lam := lam) (Lam := Lam) w hw hEll hnegL2
  have hgCube : MemVectorL2 (cubeSet Q) g := memVectorL2_cubeSet_of_openCubeSet hgL2
  have hfluctCube : MemVectorL2 (cubeSet Q) (cubeFluctuationVec Q g) :=
    hgCube.sub (MeasureTheory.memLp_const (μ := volumeMeasureOn (cubeSet Q))
      (p := (2 : ℝ≥0∞)) (cubeAverageVec Q g))
  have hofneg : ∀ v : Vec d, HilbertVec.ofVec (-v) = -HilbertVec.ofVec v := by
    intro v
    apply HilbertVec.ext
    intro i
    simp
  have hsymm : normalizedEuclideanL2 Q (cubeFluctuationVec Q fun x => -g x) =
      normalizedEuclideanL2 Q (cubeFluctuationVec Q g) := by
    rw [cubeFluctuationVec_neg, normalizedEuclideanL2, normalizedEuclideanL2, cubeLpNorm,
      cubeLpNorm]
    refine congrArg ENNReal.toReal ?_
    rw [show (fun x => HilbertVec.ofVec (-(cubeFluctuationVec Q g x))) =
        fun x => -HilbertVec.ofVec (cubeFluctuationVec Q g x) by
      funext x
      exact hofneg _]
    exact MeasureTheory.eLpNorm_neg
      (f := fun x => HilbertVec.ofVec (cubeFluctuationVec Q g x))
      (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure Q)
  rw [hsymm] at henergy
  refine henergy.trans ((normalizedEuclideanL2_le_sqrt_card_mul hfluctCube).trans ?_)
  exact mul_le_mul_of_nonneg_left (cubeLpNorm_fluctuation_le_besovSeminorm Q hg)
    (Real.sqrt_nonneg _)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
