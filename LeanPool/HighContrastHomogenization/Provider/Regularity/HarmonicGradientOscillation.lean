/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicHessianNormalized
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.StandardOverlapComparison
public import LeanPool.HighContrastHomogenization.Support.Multiscale.OverlapLp
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareW1p.OverlapCubeVectorNormalized
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.CubeVector

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicGradientOscillation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

/-- The finite exponent `2 * d * p` used to control restriction to depth `2 * p * t`. -/
@[expose]
public noncomputable def depthTargetExponent (d p : ℕ) [NeZero d] (hp : 0 < p) :
    FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * (d : ℝ) * (p : ℝ))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hd : (1 : ℝ) ≤ d := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith only [hd, hp']
  lt_top := ENNReal.ofReal_lt_top

@[simp] private theorem depthTargetExponent_toReal (d p : ℕ) [NeZero d]
    (hp : 0 < p) :
    (depthTargetExponent d p hp).exponent.toReal =
      2 * (d : ℝ) * (p : ℝ) := by
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) * (p : ℝ) := by positivity
  simp [depthTargetExponent]

private theorem depthRestrictionFactor_eq (d p t : ℕ) [NeZero d]
    (hp : 0 < p) :
    ENNReal.ofReal ((((3 ^ d) ^ (2 * p * t) : ℕ) : ℝ)) ^
        (1 / (depthTargetExponent d p hp).exponent).toReal =
      (3 : ℝ≥0∞) ^ t := by
  rw [ENNReal.ofReal_natCast]
  have hpow : (((3 ^ d) ^ (2 * p * t) : ℕ) : ℝ≥0∞) =
      (3 : ℝ≥0∞) ^ (d * (2 * p * t)) := by
    norm_cast
    simp only [← pow_mul]
  rw [hpow]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hexp : ((d * (2 * p * t) : ℕ) : ℝ) *
      (1 / (depthTargetExponent d p hp).exponent).toReal = (t : ℝ) := by
    simp only [one_div, ENNReal.toReal_inv, depthTargetExponent_toReal]
    push_cast
    field_simp [hdpos.ne', hppos.ne']
  rw [hexp, ENNReal.rpow_natCast]

private theorem depthScale_mul_restrictionFactor_eq {d : ℕ}
    (Q : TriadicCube d) (p t : ℕ) (hp : 0 < p) :
    ENNReal.ofReal (cubeScaleFactor (centralDescendant Q (2 * p * t))) *
        (3 : ℝ≥0∞) ^ t =
      ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
        ENNReal.ofReal (cubeScaleFactor Q) := by
  have hthreepow : (0 : ℝ) < (3 : ℝ) ^ (2 * p * t) := by positivity
  rw [centralDescendant_cubeScaleFactor,
    ENNReal.ofReal_div_of_pos hthreepow]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  have hpow : 2 * p * t = (2 * p - 1) * t + t := by
    calc
      2 * p * t = ((2 * p - 1) + 1) * t := by
        apply congrArg (fun n : ℕ ↦ n * t)
        omega
      _ = (2 * p - 1) * t + t := by rw [Nat.add_mul, one_mul]
  rw [hpow, pow_add]
  let a : ℝ≥0∞ := (3⁻¹ : ℝ≥0∞) ^ t
  have ha0 : a ≠ 0 := pow_ne_zero t (by norm_num)
  have hatop : a ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  change (((3⁻¹ : ℝ≥0∞) ^ ((2 * p - 1) * t) * a) *
      ENNReal.ofReal (cubeScaleFactor Q)) * (3 : ℝ≥0∞) ^ t = _
  have hcancel : a * (3 : ℝ≥0∞) ^ t = 1 := by
    dsimp [a]
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel]
    · exact pow_ne_zero t (by norm_num)
    · exact ENNReal.pow_ne_top (by norm_num)
  calc
    (((3⁻¹ : ℝ≥0∞) ^ ((2 * p - 1) * t) * a) *
        ENNReal.ofReal (cubeScaleFactor Q)) * (3 : ℝ≥0∞) ^ t =
      (3⁻¹ : ℝ≥0∞) ^ ((2 * p - 1) * t) *
        ENNReal.ofReal (cubeScaleFactor Q) *
          (a * (3 : ℝ≥0∞) ^ t) := by ring
    _ = _ := by rw [hcancel, mul_one]

private theorem depthCentralDescendant_scaleFactor_le {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    ENNReal.ofReal (cubeScaleFactor (centralDescendant Q n)) ≤
      ENNReal.ofReal (cubeScaleFactor Q) := by
  rw [centralDescendant_cubeScaleFactor]
  apply ENNReal.ofReal_le_ofReal
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  exact div_le_self hscale.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

private theorem depthELpNorm_centralDescendant_two_mul_le
    {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (p t : ℕ) (hp : 0 < p)
    (f : Vec d → E) :
    MeasureTheory.eLpNorm f (depthTargetExponent d p hp).exponent
        (normalizedCubeMeasure (centralDescendant Q (2 * p * t))) ≤
      (3 : ℝ≥0∞) ^ t *
        MeasureTheory.eLpNorm f (depthTargetExponent d p hp).exponent
          (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_centralDescendant_eq_smul_restrict]
  have hfactor : ENNReal.ofReal ((((3 ^ d) ^ (2 * p * t) : ℕ) : ℝ)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero hfactor]
  calc
    ENNReal.ofReal ((((3 ^ d) ^ (2 * p * t) : ℕ) : ℝ)) ^
          (1 / (depthTargetExponent d p hp).exponent).toReal *
        MeasureTheory.eLpNorm f (depthTargetExponent d p hp).exponent
          ((normalizedCubeMeasure Q).restrict
            (cubeSet (centralDescendant Q (2 * p * t)))) ≤
      ENNReal.ofReal ((((3 ^ d) ^ (2 * p * t) : ℕ) : ℝ)) ^
          (1 / (depthTargetExponent d p hp).exponent).toReal *
        MeasureTheory.eLpNorm f (depthTargetExponent d p hp).exponent
          (normalizedCubeMeasure Q) := by
      exact mul_le_mul_right (MeasureTheory.eLpNorm_mono_measure f
        MeasureTheory.Measure.restrict_le_self) _
    _ = (3 : ℝ≥0∞) ^ t *
        MeasureTheory.eLpNorm f (depthTargetExponent d p hp).exponent
          (normalizedCubeMeasure Q) := by rw [depthRestrictionFactor_eq d p t hp]

private theorem descendantVectorOscillation_decay_and_memLp
    {d : ℕ} [NeZero d] (p t : ℕ) (hp : 0 < p)
    (D : TriadicCube d)
    (V : CubeVectorW1pFunction D (depthTargetExponent d p hp))
    (CP bound : ℝ≥0∞)
    (hCP : ∀ (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d),
      S ∈ ScalarOverlap.centersAtDepth Q j →
      ∀ V : CubeVectorW1pFunction Q (depthTargetExponent d p hp),
        MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec
            (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
          (depthTargetExponent d p hp).exponent
          (ScalarOverlap.normalizedCubeMeasure S) ≤
        CP * ENNReal.ofReal (overlapCubeScaleFactor S) *
          MeasureTheory.eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
            (depthTargetExponent d p hp).exponent
            (ScalarOverlap.normalizedCubeMeasure S))
    (hscaledJacD : ENNReal.ofReal (cubeScaleFactor D) *
      MeasureTheory.eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
        (depthTargetExponent d p hp).exponent (normalizedCubeMeasure D) ≤ bound) :
    MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec
          (V.toField x - cubeAverageVec (centralDescendant D (2 * p * t)) V.toField))
        (depthTargetExponent d p hp).exponent
        (normalizedCubeMeasure (centralDescendant D (2 * p * t))) ≤
      CP * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) * bound ∧
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec
        (V.toField x - cubeAverageVec (centralDescendant D (2 * p * t)) V.toField))
      (depthTargetExponent d p hp).exponent
      (normalizedCubeMeasure (centralDescendant D (2 * p * t))) := by
  let q : FiniteLpExponent := depthTargetExponent d p hp
  let R : TriadicCube d := centralDescendant D (2 * p * t)
  let S : TriadicCube d := ScalarOverlap.middleChildCube R
  have hScenter : S ∈ ScalarOverlap.centersAtDepth D (2 * p * t) := by
    exact ScalarOverlap.middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth
      (centralDescendant_mem_descendantsAtDepth D (2 * p * t))
  have hmean : ScalarOverlap.cubeAverageVec S V.toField =
      cubeAverageVec R V.toField := by
    funext i
    simp only [ScalarOverlap.cubeAverageVec, cubeAverageVec]
    rw [ScalarOverlap.cubeAverage_middleChildCube]
  have hpoincare := hCP D (2 * p * t) S hScenter V
  have hmeasureS : ScalarOverlap.normalizedCubeMeasure S =
      normalizedCubeMeasure R := by
    simp [S]
  have hscaleS : overlapCubeScaleFactor S = cubeScaleFactor R := by
    change ScalarOverlap.scaleFactor S = cubeScaleFactor R
    simp [S]
  have hpoincareR : MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec
          (V.toField x - cubeAverageVec R V.toField))
        q.exponent (normalizedCubeMeasure R) ≤
      CP * ENNReal.ofReal (cubeScaleFactor R) *
        MeasureTheory.eLpNorm
          (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
          (normalizedCubeMeasure R) := by
    rw [hmean, hmeasureS, hscaleS] at hpoincare
    exact hpoincare
  have hjacR : MeasureTheory.eLpNorm
        (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
        (normalizedCubeMeasure R) ≤
      (3 : ℝ≥0∞) ^ t * MeasureTheory.eLpNorm
        (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
        (normalizedCubeMeasure D) := by
    simpa [q, R] using depthELpNorm_centralDescendant_two_mul_le D p t hp
      (fun x => HilbertMat.ofMat (V.jacobian x))
  have hq : MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec
          (V.toField x - cubeAverageVec R V.toField)) q.exponent
        (normalizedCubeMeasure R) ≤
      CP * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) * bound := by
    calc
      _ ≤ CP * ENNReal.ofReal (cubeScaleFactor R) *
          MeasureTheory.eLpNorm
            (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
            (normalizedCubeMeasure R) := hpoincareR
      _ ≤ CP * ENNReal.ofReal (cubeScaleFactor R) *
          ((3 : ℝ≥0∞) ^ t * MeasureTheory.eLpNorm
            (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
            (normalizedCubeMeasure D)) := by gcongr
      _ = CP * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
          (ENNReal.ofReal (cubeScaleFactor D) *
            MeasureTheory.eLpNorm
              (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
              (normalizedCubeMeasure D)) := by
        rw [show R = centralDescendant D (2 * p * t) from rfl]
        calc
          CP * ENNReal.ofReal
                (cubeScaleFactor (centralDescendant D (2 * p * t))) *
                ((3 : ℝ≥0∞) ^ t * MeasureTheory.eLpNorm
                  (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
                  (normalizedCubeMeasure D)) =
              CP * (ENNReal.ofReal
                (cubeScaleFactor (centralDescendant D (2 * p * t))) *
                (3 : ℝ≥0∞) ^ t) * MeasureTheory.eLpNorm
                  (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
                  (normalizedCubeMeasure D) := by ring
          _ = CP * (((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
                ENNReal.ofReal (cubeScaleFactor D)) *
              MeasureTheory.eLpNorm
                (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
                (normalizedCubeMeasure D) := by
            rw [depthScale_mul_restrictionFactor_eq D p t hp]
          _ = _ := by ring
      _ ≤ CP * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
          bound := by gcongr
      _ = _ := by ring
  have hresMem : MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec
        (V.toField x - cubeAverageVec R V.toField)) q.exponent
      (normalizedCubeMeasure R) := by
    have hresMemS : MeasureTheory.MemLp
        (fun x => HilbertVec.ofVec
          (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
        q.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
      rw [MeasureTheory.memLp_piLp_iff]
      intro i
      have hVmem := V.euclideanMemLp
      rw [MeasureTheory.memLp_piLp_iff] at hVmem
      have hcoord :=
        ScalarOverlap.memLp_sub_cubeAverage_of_mem_centersAtDepth_of_memLp
          hScenter (hVmem i)
      simpa only [Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply,
        V.toField_apply, Pi.sub_apply, ScalarOverlap.cubeAverageVec] using hcoord
    rw [hmean, hmeasureS] at hresMemS
    exact hresMemS
  exact ⟨hq, hresMem⟩

private theorem coordinateOscillationBound_to_vectorL2
    {d : ℕ} (Q R : TriadicCube d) (gradient : Vec d → Vec d)
    (q : FiniteLpExponent) (htwoq : (2 : ℝ≥0∞) ≤ q.exponent) (factor : ℝ≥0∞)
    (hbound : MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (gradient x - cubeAverageVec R gradient))
      q.exponent (normalizedCubeMeasure R) ≤
      factor * ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => gradient x j) 2 (normalizedCubeMeasure Q)) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (gradient x - cubeAverageVec R gradient))
      2 (normalizedCubeMeasure R) ≤
      factor * (d : ℝ≥0∞) * MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (gradient x)) 2 (normalizedCubeMeasure Q) := by
  let _ : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  have htwo : MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (gradient x - cubeAverageVec R gradient))
      2 (normalizedCubeMeasure R) ≤ MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (gradient x - cubeAverageVec R gradient))
      q.exponent (normalizedCubeMeasure R) :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le htwoq
  have hsum : ∑ j : Fin d,
      MeasureTheory.eLpNorm (fun x => gradient x j) 2 (normalizedCubeMeasure Q) ≤
      (d : ℝ≥0∞) * MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (gradient x)) 2 (normalizedCubeMeasure Q) := by
    calc
      _ ≤ ∑ _j : Fin d, MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (gradient x)) 2 (normalizedCubeMeasure Q) :=
        Finset.sum_le_sum fun j _ => coordinate_eLpNorm_le_euclidean
          (normalizedCubeMeasure Q) FiniteLpExponent.two gradient j
      _ = _ := by simp
  calc
    _ ≤ factor * ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => gradient x j) 2 (normalizedCubeMeasure Q) :=
      htwo.trans hbound
    _ ≤ factor * ((d : ℝ≥0∞) * MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (gradient x)) 2 (normalizedCubeMeasure Q)) :=
      mul_le_mul_right hsum _
    _ = _ := by ring

/-- A harmonic gradient becomes geometrically close in normalized `L²` to
its average on sufficiently deep central descendants.  Both the gain depth
and the prefactor are dimension-only construction data. -/
theorem exists_harmonic_gradient_oscillation_decay_at_integer_rate
    (d p : ℕ) [NeZero d] (hp : 0 < p) :
    ∃ (depth : ℕ) (C : ℝ≥0∞), C ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∀ t : ℕ,
            let R := centralDescendant
              (centralDescendant (centralChild Q) depth) (2 * p * t)
            MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec
                  (u.grad x - cubeAverageVec R u.grad)) 2
                (normalizedCubeMeasure R) ≤
              C * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
                MeasureTheory.eLpNorm
                  (fun x => HilbertVec.ofVec (u.grad x)) 2
                  (normalizedCubeMeasure Q) := by
  let q : FiniteLpExponent := depthTargetExponent d p hp
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨⟨depth, G⟩⟩ :=
    INTERNAL.nonempty_harmonicEuclideanGradientGain_finiteTarget_of_pos
      d hd q
  obtain ⟨A, hApos, hAtop, hA⟩ :=
    exists_harmonic_centralChild_normalized_hessian_energy_bound
      (d := d)
  obtain ⟨CP, hCPtop, hCP⟩ :=
    exists_overlapCubeVector_normalized_poincare_constant (d := d) q
  let C : ℝ≥0∞ := 1 + CP * G.constantValue * A * (d : ℝ≥0∞)
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hCPtop G.constant_ne_top) hAtop)
        (ENNReal.natCast_ne_top d)⟩
  refine ⟨depth, C, hCtop, ?_⟩
  intro Q u hu t
  let P : TriadicCube d := centralChild Q
  let D : TriadicCube d := centralDescendant P depth
  let R : TriadicCube d := centralDescendant D (2 * p * t)
  have hSopen : IsOpen (scaledOpenCubeSet Q (1 / 2 : ℝ)) :=
    isOpen_scaledOpenCubeSet Q _
  have hSQ : scaledOpenCubeSet Q (1 / 2 : ℝ) ⊆ openCubeSet Q := by
    exact (scaledOpenCubeSet_subset_scaledClosedCubeSet Q _).trans
      (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
        (by norm_num) (by norm_num))
  have hPopen : IsOpen (openCubeSet P) := isOpen_openCubeSet P
  have hPS : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet P).trans (by simpa [P] using
      centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
  have hDopen : IsOpen (openCubeSet D) := isOpen_openCubeSet D
  have hDP : openCubeSet D ⊆ openCubeSet P := by
    exact centralDescendant_openCubeSet_subset P depth
  obtain ⟨uS, huval, hugrad, H, henergy⟩ := hA Q u hu
  have huS : uS = u.restrict hSopen hSQ := by
    apply H1Function.ext
    · simpa [H1Function.restrict] using huval
    · simpa [H1Function.restrict] using hugrad
  subst uS
  let HP := H.restrict hPopen hPS
  let v : Fin d → H1Function (openCubeSet P) :=
    fun i => HP.gradCoordH1Function i
  have hS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
      (u.restrict hSopen hSQ) (fun _ => 0) := hu.restrict hSopen hSQ
  have hv : ∀ i : Fin d,
      WeakPoissonEquationOn (openCubeSet P) (v i) (fun _ => 0) := by
    intro i
    have hvS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
        (H.gradCoordH1Function i) (fun _ => 0) :=
      hS.gradCoordH1Function_harmonic hSopen H i
    have hv_eq : v i =
        (H.gradCoordH1Function i).restrict hPopen hPS := by
      apply H1Function.ext <;> rfl
    rw [hv_eq]
    exact hvS.restrict hPopen hPS
  let HD := HP.restrict hDopen hDP
  have hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x => HilbertVec.ofVec (fun j => HD.hess i j x))
        q.exponent (normalizedCubeMeasure D) := by
    intro i
    simpa [D, HD, v] using! G.memLp P (v i) (hv i)
  have hrowBound : ∀ i : Fin d,
      MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (fun j => HD.hess i j x))
          q.exponent (normalizedCubeMeasure D) ≤
        G.constantValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
            (normalizedCubeMeasure P) := by
    intro i
    simpa [D, HD, v] using! G.bound P (v i) (hv i)
  let V : CubeVectorW1pFunction D q :=
    CubeVectorW1pFunction.ofWeakHessian HD hrows
  have hVfield : V.toField = u.grad := by
    rw [show V = CubeVectorW1pFunction.ofWeakHessian HD hrows from rfl,
      CubeVectorW1pFunction.ofWeakHessian_toField]
    rfl
  have hjacD :
      MeasureTheory.eLpNorm
          (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
          (normalizedCubeMeasure D) ≤
        G.constantValue * ∑ i : Fin d, ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
            (normalizedCubeMeasure P) := by
    calc
      _ ≤ ∑ i : Fin d, MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (fun j => HD.hess i j x))
          q.exponent (normalizedCubeMeasure D) := by
        simpa [V] using
          CubeVectorW1pFunction.ofWeakHessian_eLpNorm_jacobianHilbert_le_sum_rows
            HD hrows
      _ ≤ ∑ i : Fin d, G.constantValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
            (normalizedCubeMeasure P) :=
        Finset.sum_le_sum fun i _ => hrowBound i
      _ = G.constantValue * ∑ i : Fin d, ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
            (normalizedCubeMeasure P) := by rw [Finset.mul_sum]
  have henergy' : ENNReal.ofReal (cubeScaleFactor P) *
      ∑ i : Fin d, ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
          (normalizedCubeMeasure P) ≤
      A * ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x j) 2
          (normalizedCubeMeasure Q) := by
    simpa [P, HP] using! henergy
  have hscaleDP : ENNReal.ofReal (cubeScaleFactor D) ≤
      ENNReal.ofReal (cubeScaleFactor P) := by
    simpa [D] using depthCentralDescendant_scaleFactor_le P depth
  have hscaledJacD : ENNReal.ofReal (cubeScaleFactor D) *
      MeasureTheory.eLpNorm
        (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
        (normalizedCubeMeasure D) ≤
      G.constantValue * A * ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x j) 2
          (normalizedCubeMeasure Q) := by
    calc
      _ ≤ ENNReal.ofReal (cubeScaleFactor D) *
          (G.constantValue * ∑ i : Fin d, ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
              (normalizedCubeMeasure P)) := mul_le_mul_right hjacD _
      _ = G.constantValue * (ENNReal.ofReal (cubeScaleFactor D) *
          ∑ i : Fin d, ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
              (normalizedCubeMeasure P)) := by ring
      _ ≤ G.constantValue * (ENNReal.ofReal (cubeScaleFactor P) *
          ∑ i : Fin d, ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => HP.hess i j x) 2
              (normalizedCubeMeasure P)) := by gcongr
      _ ≤ G.constantValue * (A * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2
            (normalizedCubeMeasure Q)) := mul_le_mul_right henergy' _
      _ = _ := by ring
  obtain ⟨hqRaw, hresMemRaw⟩ :=
    descendantVectorOscillation_decay_and_memLp p t hp D V CP
      (G.constantValue * A * ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q))
      hCP hscaledJacD
  have hq : MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec
          (u.grad x - cubeAverageVec R u.grad)) q.exponent
        (normalizedCubeMeasure R) ≤
      CP * G.constantValue * A * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
        ∑ j : Fin d, MeasureTheory.eLpNorm (fun x => u.grad x j) 2
          (normalizedCubeMeasure Q) := by
    rw [hVfield] at hqRaw
    convert hqRaw using 1; ring
  have hresMem : MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec (u.grad x - cubeAverageVec R u.grad)) q.exponent
      (normalizedCubeMeasure R) := by
    simpa only [hVfield] using hresMemRaw
  have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
    dsimp [q, depthTargetExponent]
    rw [← ENNReal.ofReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    have hdp : 1 ≤ d * p := Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (NeZero.ne d) (Nat.ne_of_gt hp))
    have hdp' : (1 : ℝ) ≤ (d : ℝ) * (p : ℝ) := by exact_mod_cast hdp
    nlinarith only [hdp']
  have hvector := coordinateOscillationBound_to_vectorL2 Q R u.grad q htwoq
    (CP * G.constantValue * A * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t)) hq
  calc
    _ ≤ (CP * G.constantValue * A * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t)) *
        (d : ℝ≥0∞) * MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (u.grad x)) 2 (normalizedCubeMeasure Q) := hvector
    _ = (CP * G.constantValue * A * (d : ℝ≥0∞)) *
        ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) * MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (u.grad x)) 2 (normalizedCubeMeasure Q) := by ring
    _ ≤ C * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) * MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (u.grad x)) 2 (normalizedCubeMeasure Q) := by
      have hconstant : CP * G.constantValue * A * (d : ℝ≥0∞) ≤ C :=
        le_add_of_nonneg_left (by norm_num)
      exact mul_le_mul_left (mul_le_mul_left hconstant _) _

/-- The effective per-scale exponents of the integer-rate family approach
one from below. -/
theorem exists_pos_nat_harmonic_integer_rate_gt {eta : ℝ} (heta : eta < 1) :
    ∃ p : ℕ, 0 < p ∧ eta < 1 - 1 / (2 * (p : ℝ)) := by
  have hgap : 0 < 1 - eta := sub_pos.mpr heta
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap
  let p : ℕ := n + 1
  have hp : 0 < p := by dsimp [p]; omega
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hhalf : 1 / (2 * (p : ℝ)) ≤ 1 / (p : ℝ) := by
    apply one_div_le_one_div_of_le hpReal
    linarith only [hpReal]
  refine ⟨p, hp, ?_⟩
  have hone : 1 / (p : ℝ) < 1 - eta := by simpa [p] using hn
  linarith only [hhalf, hone]

end CubeCalderonZygmund

end

end HCPolySupport
