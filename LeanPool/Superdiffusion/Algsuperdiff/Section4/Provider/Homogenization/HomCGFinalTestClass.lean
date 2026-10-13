/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalFullNorm
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalSmoothTest

/-!
# HomCGFinalTestClass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The test-class conversion, at the two orders `s′ < s`

## What this file supplies

The domination of the Hölder test gauge by `CoarseGraining`'s smooth
`W^{s,p′}` dual is the ONE gap between that dual and the repository's
`WeakNegDualBoundOn`, and it is FALSE at equal orders (the
Gagliardo integrand of a `C^{0,s}` field is logarithmically divergent).  This
file gives the honest, order-losing form as a THEOREM:

```text
  SmoothDualDominatesHolderTestsAt Q s′ s p (cgTestConst d Q s s′ p′)
```

for every pair `s′ < s` in the admissible window `0 < (s-s′)p′ < d`.  The
constant is `HomCGFinalFullNorm`'s, i.e. `d·3^{m(s-s′)}·(1 + C(d,β)^{1/p′})`,
and the two orders enter ONLY through that single factor.

## The route, in one line

A merely Hölder test `φ` is not admissible against the smooth dual, which is a
supremum over **globally `C^∞`** unit tests.  Normalize `φ` by the gauge
(`ψ = φ / (K_test · gauge)`), extend it by McShane and mollify it
(`HomCGFinalSmoothTest`): the resulting fields are globally smooth, carry the
SAME two constants, and hence sit in the unit ball of `cubeEuclideanWspFullENorm`
by `HomCGFinalFullNorm.cubeEuclideanWspFullENorm_le_gauge`.  Each therefore pairs
against `F` below the dual norm `D`.  They converge to `ψ` pointwise on the open
cube, and `F ∈ L²` of a probability measure dominates the pairing integrand
uniformly, so dominated convergence transports the bound to `ψ` itself, i.e. to
`|⟨F, φ⟩| ≤ D · K_test · gauge`.

## What it costs, and why it is free at the level

Nothing is paid at the level: `cgTestConst` carries `3^{m(s-s′)}` and the
smooth-dual display at order `s′` carries `3^{s′m}`, so the product is `3^{sm}`,
the level the Step-4 consumer wants.  The order loss is paid only inside the
printed right-hand side, whose `s^{-1}`, `s^{-9/2}` and `(s₂-s)^{-1}` are read
at `s′`; the spine's bundle quantifies all of those existentially.
-/

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube pairing as an integral against the normalized cube measure -/

/-- The normalized cube measure, realized on the OPEN cube. -/
theorem normalizedCubeMeasure_eq_smul_restrict_openCubeSet (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      (volume (openCubeSet Q))⁻¹ • volume.restrict (openCubeSet Q) := by
  rw [← Support.normalizedVolumeMeasureOn_cubeSet Q, Support.normalizedVolumeMeasureOn_def,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    volume_openCubeSet_eq_volume_cubeSet]

/-- **`⨍_□ F·φ` IS `CoarseGraining`'s normalized pairing.** -/
theorem cubePairing_eq_integral (Q : TriadicCube d) (F psi : Vec d → Vec d) :
    cubePairing Q F psi = ∫ x, vecDot (F x) (psi x) ∂normalizedCubeMeasure Q := by
  rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul]
  rfl

/-- Almost every point of the normalized cube measure lies in the open cube. -/
theorem ae_mem_openCubeSet (Q : TriadicCube d) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q), x ∈ openCubeSet Q := by
  rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet]
  exact Measure.ae_smul_measure (ae_restrict_mem (isOpen_openCubeSet Q).measurableSet) _

/-- The pairing is homogeneous in the test field. -/
theorem cubePairing_const_smul_right (Q : TriadicCube d) (F psi : Vec d → Vec d) (c : ℝ) :
    cubePairing Q F (fun x => c • psi x) = c * cubePairing Q F psi := by
  rw [cubePairing_eq_integral, cubePairing_eq_integral]
  have hpt : ∀ x, vecDot (F x) (c • psi x) = c * vecDot (F x) (psi x) := fun x =>
    vecDot_smul_right (F x) (psi x) c
  simp_rw [hpt]
  exact integral_const_mul c _

/-! ## 2. The pairing integrand, dominated -/

/-- `|F·φ| ≤ d · |F|_eucl · ‖φ‖` in the ambient supremum metric. -/
private theorem abs_vecDot_le_of_bound {u v : Vec d} {B : ℝ} (hv : ‖v‖ ≤ B) :
    |vecDot u v| ≤ (d : ℝ) * (euclideanNorm u * B) := by
  have h1 : |vecDot u v| ≤ ∑ i, |u i * v i| := by
    rw [vecDot]
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i ∈ Finset.univ, |u i * v i| ≤ euclideanNorm u * B := by
    intro i _
    rw [abs_mul]
    have hu : |u i| ≤ euclideanNorm u := abs_coordinate_le_euclideanNorm u i
    have hvi : |v i| ≤ B := by
      have h := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at h
      exact h.trans hv
    exact mul_le_mul hu hvi (abs_nonneg _) (euclideanNorm_nonneg u)
  refine h1.trans ((Finset.sum_le_sum h2).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The Euclidean norm of an `L²` cube field is integrable. -/
private theorem integrable_euclideanNorm_lpField {Q : TriadicCube d}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    Integrable (fun x => euclideanNorm (F.toField x)) (normalizedCubeMeasure Q) := by
  have h2 : MemLp (fun x => HilbertVec.ofVec (F.toField x)) 2
      (normalizedCubeMeasure Q) := by
    simpa using F.euclideanMemLp
  have hi : Integrable (fun x => HilbertVec.ofVec (F.toField x))
      (normalizedCubeMeasure Q) := h2.integrable (by norm_num)
  have hn := hi.norm
  simpa only [euclideanNorm_eq_norm_ofVec] using hn

/-! ## 3. The dominated-convergence transport of the pairing -/

/-- **The pairing passes to a uniformly bounded pointwise limit of test fields.** -/
theorem tendsto_cubePairing {Q : TriadicCube d}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    {psi : ℕ → Vec d → Vec d} {psiLim : Vec d → Vec d} {B : ℝ}
    (hint : ∀ k, Integrable (fun x => vecDot (F.toField x) (psi k x))
      (normalizedCubeMeasure Q))
    (hbound : ∀ k, ∀ x, ‖psi k x‖ ≤ B)
    (hlim : ∀ x ∈ openCubeSet Q,
      Filter.Tendsto (fun k => psi k x) Filter.atTop (nhds (psiLim x))) :
    Filter.Tendsto (fun k => cubePairing Q F.toField (psi k)) Filter.atTop
      (nhds (cubePairing Q F.toField psiLim)) := by
  simp only [cubePairing_eq_integral]
  have hFint := integrable_euclideanNorm_lpField F
  have hbnd : Integrable
      (fun x => (d : ℝ) * (euclideanNorm (F.toField x) * B))
      (normalizedCubeMeasure Q) := (hFint.mul_const B).const_mul _
  refine tendsto_integral_of_dominated_convergence
    (fun x => (d : ℝ) * (euclideanNorm (F.toField x) * B))
    (fun k => (hint k).1) hbnd (fun k => ?_) ?_
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_vecDot_le_of_bound (hbound k x)
  · filter_upwards [ae_mem_openCubeSet Q] with x hx
    have h := hlim x hx
    have hcomp : ∀ i : Fin d,
        Filter.Tendsto (fun k => psi k x i) Filter.atTop (nhds (psiLim x i)) :=
      fun i => ((continuous_apply i).tendsto (psiLim x)).comp h
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun i _ => (hcomp i).const_mul (F.toField x i))
    simpa only [vecDot] using hsum

/-! ## 4. A smooth unit test pairs below the dual norm -/

/-- **Every smooth field in the unit ball pairs below the smooth dual norm.** -/
theorem ofReal_abs_cubePairing_le_dual {Q : TriadicCube d} {s' : FractionalOrder}
    {p : FiniteLpExponent} (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s' p.conjugate)
    (hle : cubeEuclideanWspFullENorm Q s' p.conjugate h.toField ≤ 1) :
    ENNReal.ofReal |cubePairing Q F.toField h.toField| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s' p F := by
  have hpair : cubePairing Q F.toField h.toField =
      cubeEuclideanNormalizedSmoothPairing F h := cubePairing_eq_integral Q _ _
  rw [hpair]
  exact le_iSup (fun g : CubeEuclideanWspSmoothUnitTest Q s' p.conjugate =>
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F g.1|) ⟨h, hle⟩

/-! ## 5. The open cube is nonempty -/

/-- The centre of a triadic cube lies in its open realization. -/
theorem cubeCenter_mem_openCubeSet (Q : TriadicCube d) : cubeCenter Q ∈ openCubeSet Q := by
  intro i
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) * cubeScaleFactor Q :=
    mul_pos (by norm_num) hR
  have hlo : ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q <
      (Q.index i : ℝ) * cubeScaleFactor Q := by
    have hexp : ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q =
        (Q.index i : ℝ) * cubeScaleFactor Q - (1 / 2 : ℝ) * cubeScaleFactor Q := by ring
    rw [hexp]
    linarith only [hhalf]
  have hhi : (Q.index i : ℝ) * cubeScaleFactor Q <
      ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    have hexp : ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q =
        (Q.index i : ℝ) * cubeScaleFactor Q + (1 / 2 : ℝ) * cubeScaleFactor Q := by ring
    rw [hexp]
    linarith only [hhalf]
  exact ⟨hlo, hhi⟩

theorem openCubeSet_nonempty (Q : TriadicCube d) : (openCubeSet Q).Nonempty :=
  ⟨cubeCenter Q, cubeCenter_mem_openCubeSet Q⟩

/-! ## 6. The two-order test-class comparison -/

/-- **The test-class comparison at the two orders `s′` (dual) and `s` (data).**

This is the smooth-dual/Hölder test domination with the `CoarseGraining` side
read at the strictly smaller order `s′`, which is the only reading that can be
true. -/
def SmoothDualDominatesHolderTestsAt (Q : TriadicCube d) (s' s : FractionalOrder)
    (p : FiniteLpExponent) (Ktest : ℝ) : Prop :=
  ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (phi : Vec d → Vec d)
    (Ksup KHol : ℝ), 0 ≤ Ksup → 0 ≤ KHol →
    (∀ x ∈ openCubeSet Q, ‖phi x‖ ≤ Ksup) →
    HolderSeminormBoundOn (openCubeSet Q) s.1 KHol phi →
    ENNReal.ofReal |cubePairing Q F.toField phi| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s' p F *
        ENNReal.ofReal (Ktest * wsInftyGauge Q s.1 Ksup KHol)

/-- The test constant is strictly positive in the admissible window. -/
theorem cgTestConst_pos (Q : TriadicCube d) {alpha s' t : ℝ}
    (hlo : 0 < (alpha - s') * t) (hhi : (alpha - s') * t < (d : ℝ)) :
    0 < cgTestConst d Q alpha s' t := by
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_trans hlo hhi
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hP : (0 : ℝ) < cubeScaleFactor Q ^ (alpha - s') := Real.rpow_pos_of_pos hR _
  have hblt : cgGagliardoBeta d alpha s' t < (d : ℝ) := cgGagliardoBeta_lt hlo
  have hCc : (0 : ℝ) ≤
      Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹ :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  rw [cgTestConst_def]
  exact mul_pos (mul_pos hdpos hP) (by linarith only [hCc])

/-- **THE TEST-CLASS COMPARISON, LANDED.** -/
theorem smoothDualDominatesHolderTestsAt (Q : TriadicCube d) (s' s : FractionalOrder)
    (p : FiniteLpExponent)
    (hlo : 0 < (s.1 - s'.1) * p.conjugate.exponent.toReal)
    (hhi : (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ)) :
    SmoothDualDominatesHolderTestsAt Q s' s p
      (cgTestConst d Q s.1 s'.1 p.conjugate.exponent.toReal) := by
  intro F phi Ksup KHol hKsup hKHol hb hH
  have hKt : 0 < cgTestConst d Q s.1 s'.1 p.conjugate.exponent.toReal :=
    cgTestConst_pos Q hlo hhi
  have hgnn : 0 ≤ wsInftyGauge Q s.1 Ksup KHol := wsInftyGauge_nonneg hKsup hKHol
  have hs0 : 0 < s.1 := s.2.1
  have hs1 : s.1 ≤ 1 := le_of_lt s.2.2
  have hA : (openCubeSet Q).Nonempty := openCubeSet_nonempty Q
  rcases eq_or_lt_of_le (mul_nonneg hKt.le hgnn) with hzero | hpos
  · /- degenerate gauge: the data forces `φ = 0` on the cu -/
    have hg0 : wsInftyGauge Q s.1 Ksup KHol = 0 := by
      rcases mul_eq_zero.mp hzero.symm with h | h
      · exact absurd h (ne_of_gt hKt)
      · exact h
    have hthree : (0 : ℝ) < Real.rpow 3 (-(s.1 * ((Q.scale : ℤ) : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hKsup0 : Ksup = 0 := by
      rw [wsInftyGauge_def] at hg0
      have hmul : Real.rpow 3 (-(s.1 * ((Q.scale : ℤ) : ℝ))) * Ksup = 0 := by
        linarith only [hg0, hKHol, mul_nonneg hthree.le hKsup]
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h (ne_of_gt hthree)
      · exact h
    have hzeroPairing : cubePairing Q F.toField phi = 0 := by
      rw [cubePairing_eq_integral]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_mem_openCubeSet Q] with x hx
      have hphi : phi x = 0 := by
        have h := hb x hx
        rw [hKsup0] at h
        exact norm_le_zero_iff.mp h
      simp [hphi, vecDot]
    rw [hzeroPairing, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  · /- the generic ca -/
    set Kt := cgTestConst d Q s.1 s'.1 p.conjugate.exponent.toReal with hKtdef
    set G : ℝ := Kt * wsInftyGauge Q s.1 Ksup KHol with hGdef
    have hGpos : 0 < G := hpos
    have hGi : 0 < G⁻¹ := inv_pos.mpr hGpos
    have hgpos : 0 < wsInftyGauge Q s.1 Ksup KHol := by
      rcases lt_or_eq_of_le hgnn with h | h
      · exact h
      · exfalso
        rw [hGdef, ← h, mul_zero] at hGpos
        exact lt_irrefl 0 hGpos
    have hgne : wsInftyGauge Q s.1 Ksup KHol ≠ 0 := ne_of_gt hgpos
    have hsupPsi : ∀ x ∈ openCubeSet Q, ‖G⁻¹ • phi x‖ ≤ G⁻¹ * Ksup := by
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hGi.le]
      exact mul_le_mul_of_nonneg_left (hb x hx) hGi.le
    have hHPsi : HolderSeminormBoundOn (openCubeSet Q) s.1 (G⁻¹ * KHol)
        (fun x => G⁻¹ • phi x) := by
      intro x hx y hy
      have hstep : ‖G⁻¹ • phi x - G⁻¹ • phi y‖ = G⁻¹ * ‖phi x - phi y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hGi.le]
      rw [hstep]
      calc G⁻¹ * ‖phi x - phi y‖ ≤ G⁻¹ * (KHol * ‖x - y‖ ^ s.1) :=
            mul_le_mul_of_nonneg_left (hH x hx y hy) hGi.le
        _ = G⁻¹ * KHol * ‖x - y‖ ^ s.1 := by ring
    /- the smooth approximan -/
    set psiK : ℕ → Vec d → Vec d := fun k =>
      cgSmoothApprox (openCubeSet Q) (G⁻¹ * Ksup) (G⁻¹ * KHol) s.1
        (fun x => G⁻¹ • phi x) k with hpsiK
    have hsmooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (psiK k) := fun k =>
      contDiff_cgSmoothApprox (mul_nonneg hGi.le hKHol) hs0 hs1 hA hsupPsi k
    have hnormK : ∀ k, ∀ x, ‖psiK k x‖ ≤ G⁻¹ * Ksup := fun k x =>
      norm_cgSmoothApprox_le (mul_nonneg hGi.le hKsup) (mul_nonneg hGi.le hKHol)
        hs0 hs1 hA hsupPsi k x
    have hholK : ∀ k, HolderSeminormBoundOn Set.univ s.1 (G⁻¹ * KHol) (psiK k) := fun k =>
      holderSeminormBoundOn_univ_cgSmoothApprox (mul_nonneg hGi.le hKHol) hs0 hs1 hA
        hsupPsi k
    have hunit : ∀ k,
        cubeEuclideanWspFullENorm Q s' p.conjugate (psiK k) ≤ 1 := by
      intro k
      have hgauge : wsInftyGauge Q s.1 (G⁻¹ * Ksup) (G⁻¹ * KHol) =
          G⁻¹ * wsInftyGauge Q s.1 Ksup KHol := by
        rw [wsInftyGauge_def, wsInftyGauge_def]
        ring
      have hbound := cubeEuclideanWspFullENorm_le_gauge (Q := Q) (s' := s')
        (q := p.conjugate) (phi := psiK k) (alpha := s.1)
        (Ksup := G⁻¹ * Ksup) (KHol := G⁻¹ * KHol)
        (mul_nonneg hGi.le hKsup) (mul_nonneg hGi.le hKHol) hlo hhi (hnormK k)
        ((hholK k).mono_set (Set.subset_univ _))
      refine hbound.trans (le_of_eq ?_)
      rw [hgauge, ← hKtdef]
      have hinvg : G⁻¹ * wsInftyGauge Q s.1 Ksup KHol = Kt⁻¹ := by
        rw [hGdef, mul_inv, mul_assoc, inv_mul_cancel₀ hgne, mul_one]
      rw [hinvg, mul_inv_cancel₀ (ne_of_gt hKt), ENNReal.ofReal_one]
    have hdual : ∀ k, ENNReal.ofReal |cubePairing Q F.toField (psiK k)| ≤
        cubeEuclideanNegativeWspSmoothDualENorm Q s' p F := by
      intro k
      exact ofReal_abs_cubePairing_le_dual F
        ({ toField := psiK k, contDiff := hsmooth k } :
          CubeEuclideanWspSmoothTest Q s' p.conjugate) (hunit k)
    /- the lim -/
    have hlimPt : ∀ x ∈ openCubeSet Q,
        Filter.Tendsto (fun k => psiK k x) Filter.atTop (nhds (G⁻¹ • phi x)) := by
      intro x hx
      exact tendsto_cgSmoothApprox (mul_nonneg hGi.le hKHol) hs0 hs1 hA hsupPsi hHPsi hx
    have hintK : ∀ k, Integrable (fun x => vecDot (F.toField x) (psiK k x))
        (normalizedCubeMeasure Q) := by
      intro k
      exact cubeEuclideanNormalizedSmoothPairing_integrable F
        ({ toField := psiK k, contDiff := hsmooth k } :
          CubeEuclideanWspSmoothTest Q s' p.conjugate)
    have htend := tendsto_cubePairing F (psiLim := fun x => G⁻¹ • phi x)
      (B := G⁻¹ * Ksup) hintK hnormK hlimPt
    rw [cubePairing_const_smul_right] at htend
    /- transport the uniform bound through the lim -/
    rcases eq_or_lt_of_le (le_top (α := ℝ≥0∞)
      (a := cubeEuclideanNegativeWspSmoothDualENorm Q s' p F)) with htop | hfin
    · rw [htop, ENNReal.top_mul (ENNReal.ofReal_pos.mpr hGpos).ne']
      exact le_top
    · have hDreal : 0 ≤ (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal :=
        ENNReal.toReal_nonneg
      have hstep : ∀ k, |cubePairing Q F.toField (psiK k)| ≤
          (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal := by
        intro k
        have h := hdual k
        rwa [← ENNReal.ofReal_toReal hfin.ne, ENNReal.ofReal_le_ofReal_iff hDreal] at h
      have habs : Filter.Tendsto (fun k => |cubePairing Q F.toField (psiK k)|)
          Filter.atTop (nhds |G⁻¹ * cubePairing Q F.toField phi|) := htend.abs
      have hlimBound : |G⁻¹ * cubePairing Q F.toField phi| ≤
          (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal :=
        le_of_tendsto habs (Filter.Eventually.of_forall hstep)
      have hfinal : |cubePairing Q F.toField phi| ≤
          G * (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal := by
        have hexpand : |G⁻¹ * cubePairing Q F.toField phi| =
            G⁻¹ * |cubePairing Q F.toField phi| := by
          rw [abs_mul, abs_of_nonneg hGi.le]
        rw [hexpand] at hlimBound
        have hmul := mul_le_mul_of_nonneg_left hlimBound hGpos.le
        rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hGpos), one_mul] at hmul
      calc ENNReal.ofReal |cubePairing Q F.toField phi|
          ≤ ENNReal.ofReal
              (G * (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal) :=
            ENNReal.ofReal_le_ofReal hfinal
        _ = ENNReal.ofReal G *
              ENNReal.ofReal
                (cubeEuclideanNegativeWspSmoothDualENorm Q s' p F).toReal :=
            ENNReal.ofReal_mul hGpos.le
        _ = ENNReal.ofReal G * cubeEuclideanNegativeWspSmoothDualENorm Q s' p F := by
            rw [ENNReal.ofReal_toReal hfin.ne]
        _ = cubeEuclideanNegativeWspSmoothDualENorm Q s' p F * ENNReal.ofReal G := by
            rw [mul_comm]

/-! ## 7. The `WeakNegDualBoundOn` conversion at the two orders -/

/-- **The Step-4 carrier, produced from the smooth-dual level at order `s′`.**

The conversion of a smooth-dual level into the Step-4 carrier, with the
`CoarseGraining` side read at `s′ < s`. The output level is the data order `s`, which is what the bundle's
duality clauses use. -/
theorem weakNegDualBoundOn_of_smoothDualAt {Q : TriadicCube d} {s' s : FractionalOrder}
    {p : FiniteLpExponent} {Ktest : ℝ} (hK : 0 ≤ Ktest)
    (hclass : SmoothDualDominatesHolderTestsAt Q s' s p Ktest)
    {F : CubeEuclideanLpField Q FiniteLpExponent.two} {D : ℝ} (hD : 0 ≤ D)
    (hF : cubeEuclideanNegativeWspSmoothDualENorm Q s' p F ≤ ENNReal.ofReal D) :
    WeakNegDualBoundOn Q s.1 (Ktest * D) F.toField := by
  intro phi Ksup KHol hsup hhol hbd hHol
  have hgauge : 0 ≤ wsInftyGauge Q s.1 Ksup KHol := wsInftyGauge_nonneg hsup hhol
  have hstep := hclass F phi Ksup KHol hsup hhol hbd hHol
  have hchain : ENNReal.ofReal |cubePairing Q F.toField phi| ≤
      ENNReal.ofReal (Ktest * D * wsInftyGauge Q s.1 Ksup KHol) := by
    calc ENNReal.ofReal |cubePairing Q F.toField phi|
        ≤ cubeEuclideanNegativeWspSmoothDualENorm Q s' p F *
            ENNReal.ofReal (Ktest * wsInftyGauge Q s.1 Ksup KHol) := hstep
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal (Ktest * wsInftyGauge Q s.1 Ksup KHol) := by
          gcongr
      _ = ENNReal.ofReal (D * (Ktest * wsInftyGauge Q s.1 Ksup KHol)) :=
          (ENNReal.ofReal_mul hD).symm
      _ = ENNReal.ofReal (Ktest * D * wsInftyGauge Q s.1 Ksup KHol) := by
          rw [show D * (Ktest * wsInftyGauge Q s.1 Ksup KHol) =
            Ktest * D * wsInftyGauge Q s.1 Ksup KHol by ring]
  have hrhs : 0 ≤ Ktest * D * wsInftyGauge Q s.1 Ksup KHol :=
    mul_nonneg (mul_nonneg hK hD) hgauge
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hchain

end

end Algsuperdiff.Section4.Provider.Homogenization
