/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTopology
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCoerciveH1
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.H1Graph.Graph

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLocalLimit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized local limits of finite-volume corrector parts

Finite-volume `H¹` functions are normalized by subtracting their average on
the fixed unit cube. A componentwise Cauchy hypothesis on their normalized
local gradients then produces a unique projective local value-gradient limit.
The limit contains only compatible almost-everywhere `L²` classes.
-/

open scoped ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

private instance localGradientCubeFiniteMeasure (d n : ℕ) :
    IsFiniteMeasure (volumeMeasureOn (localGradientCube d n)) := by
  simpa [localGradientCube, volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d (n : ℤ))).isFiniteMeasure_restrict_volume

/-! ## Projective scalar-value classes -/

/-- Scalar `L²` values on one member of the centered cube exhaustion. -/
abbrev LocalValueL2 (d n : ℕ) :=
  ScalarL2 (localGradientCube d n)

@[expose]
public noncomputable def localValueRestrictLinear {d m n : ℕ} (hmn : m ≤ n) :
    LocalValueL2 d n →ₗ[ℝ] LocalValueL2 d m where
  toFun f :=
    ((Lp.memLp f).mono_measure
      (Measure.restrict_mono_set volume (localGradientCube_mono hmn))).toLp f
  map_add' f g := by
    let hmu : volumeMeasureOn (localGradientCube d m) ≤
        volumeMeasureOn (localGradientCube d n) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hmn)
    change
      ((Lp.memLp (f + g)).mono_measure hmu).toLp (f + g) =
        ((Lp.memLp f).mono_measure hmu).toLp f +
          ((Lp.memLp g).mono_measure hmu).toLp g
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (f + g)).mono_measure hmu)
        (((Lp.memLp f).mono_measure hmu).add ((Lp.memLp g).mono_measure hmu))
        ((Lp.coeFn_add f g).filter_mono (ae_mono hmu))).trans
      (MemLp.toLp_add
        ((Lp.memLp f).mono_measure hmu) ((Lp.memLp g).mono_measure hmu))
  map_smul' c f := by
    let hmu : volumeMeasureOn (localGradientCube d m) ≤
        volumeMeasureOn (localGradientCube d n) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hmn)
    change
      ((Lp.memLp (c • f)).mono_measure hmu).toLp (c • f) =
        c • ((Lp.memLp f).mono_measure hmu).toLp f
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (c • f)).mono_measure hmu)
        (((Lp.memLp f).mono_measure hmu).const_smul c)
        ((Lp.coeFn_smul c f).filter_mono (ae_mono hmu))).trans
      (MemLp.toLp_const_smul c ((Lp.memLp f).mono_measure hmu))

private theorem localValueRestrictLinear_norm_le {d m n : ℕ} (hmn : m ≤ n)
    (f : LocalValueL2 d n) :
    ‖localValueRestrictLinear hmn f‖ ≤ ‖f‖ := by
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  change ‖((Lp.memLp f).mono_measure hmu).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure f hmu)

/-- Restriction of a scalar `L²` class to a smaller exhaustion cube. -/
@[expose]
noncomputable def localValueRestrict {d m n : ℕ} (hmn : m ≤ n) :
    LocalValueL2 d n →L[ℝ] LocalValueL2 d m :=
  LinearMap.mkContinuous (localValueRestrictLinear hmn) 1 fun f => by
    simpa only [one_mul] using localValueRestrictLinear_norm_le hmn f

/-- Restriction agrees almost everywhere with the same scalar representative. -/
theorem localValueRestrict_coeFn_ae {d m n : ℕ} (hmn : m ≤ n)
    (f : LocalValueL2 d n) :
    localValueRestrict hmn f =ᵐ[volumeMeasureOn (localGradientCube d m)] f := by
  exact MemLp.coeFn_toLp
    ((Lp.memLp f).mono_measure
      (Measure.restrict_mono_set volume (localGradientCube_mono hmn)))

/-- Scalar restriction does not increase the `L²` norm. -/
theorem norm_localValueRestrict_le {d m n : ℕ} (hmn : m ≤ n)
    (f : LocalValueL2 d n) :
    ‖localValueRestrict hmn f‖ ≤ ‖f‖ :=
  localValueRestrictLinear_norm_le hmn f

/-- Compatible scalar local classes form the projective value submodule. -/
@[expose]
noncomputable def localValueProjectiveSubmodule (d : ℕ) :
    Submodule ℝ ((n : ℕ) → LocalValueL2 d n) where
  carrier := {f | ∀ m n (hmn : m ≤ n), localValueRestrict hmn (f n) = f m}
  zero_mem' := by
    intro m n hmn
    exact (localValueRestrict hmn).map_zero
  add_mem' := by
    intro f g hf hg m n hmn
    change localValueRestrict hmn (f n + g n) = f m + g m
    rw [(localValueRestrict hmn).map_add, hf m n hmn, hg m n hmn]
  smul_mem' := by
    intro c f hf m n hmn
    change localValueRestrict hmn (c • f n) = c • f m
    rw [(localValueRestrict hmn).map_smul, hf m n hmn]

/-- The countable projective carrier for local scalar-value classes. -/
noncomputable abbrev LocalValueCarrier (d : ℕ) :=
  localValueProjectiveSubmodule d

namespace LocalValueCarrier

/-- The scalar `L²` class on one exhaustion cube. -/
@[expose]
def component {d : ℕ} (f : LocalValueCarrier d) (n : ℕ) :
    LocalValueL2 d n :=
  f.1 n

/-- Projective scalar components agree under restriction. -/
theorem restrict_component {d : ℕ} (f : LocalValueCarrier d)
    {m n : ℕ} (hmn : m ≤ n) :
    localValueRestrict hmn (component f n) = component f m :=
  f.2 m n hmn

/-- A projective scalar value is determined by its local components. -/
@[ext] theorem ext {d : ℕ} {f g : LocalValueCarrier d}
    (h : ∀ n, component f n = component g n) :
    f = g := by
  apply Subtype.ext
  funext n
  exact h n

end LocalValueCarrier

/-! ## Fixed-unit normalization -/

/-- Restriction of an `H¹` function to a smaller exhaustion cube. -/
@[expose]
def restrictLocalH1 {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    H1Function (localGradientCube d m) :=
  u.restrict (isOpen_openCubeSet (originCube d (m : ℤ)))
    (localGradientCube_mono hmn)

/-- Normalize an `H¹` function by subtracting its average on cube zero. -/
@[expose]
noncomputable def normalizeOnUnitCube {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    H1Function (localGradientCube d n) :=
  u.addConst
    (-integralAverage (localGradientCube d 0)
      (restrictLocalH1 (Nat.zero_le n) u))

/-- Fixed-unit normalization restricts on cube zero to ordinary mean
subtraction there. -/
theorem restrictLocalH1_normalizeOnUnitCube_zero {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    restrictLocalH1 (Nat.zero_le n) (normalizeOnUnitCube u) =
      (restrictLocalH1 (Nat.zero_le n) u).subAverage := by
  apply H1Function.ext
  · rfl
  · funext x
    change (normalizeOnUnitCube u).grad x =
      (restrictLocalH1 (Nat.zero_le n) u).subAverage.grad x
    rw [normalizeOnUnitCube, H1Function.grad_addConst,
      H1Function.grad_subAverage]
    rfl

/-- Fixed-unit normalization has zero average on the fixed unit cube. -/
theorem normalizeOnUnitCube_meanZero {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    MeanZeroOn (localGradientCube d 0)
      (restrictLocalH1 (Nat.zero_le n) (normalizeOnUnitCube u)).toFun := by
  rw [restrictLocalH1_normalizeOnUnitCube_zero]
  exact (restrictLocalH1 (Nat.zero_le n) u).meanZeroOn_subAverage

/-- Fixed-unit normalization leaves the weak gradient unchanged. -/
theorem normalizeOnUnitCube_grad {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    (normalizeOnUnitCube u).grad = u.grad := by
  funext x
  rw [normalizeOnUnitCube, H1Function.grad_addConst]

/-- The normalized restriction of the `(n+k)`th finite-volume function to
the `n`th exhaustion cube. -/
@[expose]
noncomputable def normalizedLocalH1 {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k : ℕ) :
    H1Function (localGradientCube d n) :=
  restrictLocalH1 (Nat.le_add_right n k) (normalizeOnUnitCube (u (n + k)))

/-- Every normalized local restriction has zero average on cube zero. -/
theorem normalizedLocalH1_meanZero {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k : ℕ) :
    MeanZeroOn (localGradientCube d 0)
      (restrictLocalH1 (Nat.zero_le n) (normalizedLocalH1 u n k)).toFun := by
  have hrestrict :
      restrictLocalH1 (Nat.zero_le n) (normalizedLocalH1 u n k) =
        restrictLocalH1 (Nat.zero_le (n + k))
          (normalizeOnUnitCube (u (n + k))) := by
    apply H1Function.ext <;> rfl
  rw [hrestrict]
  exact normalizeOnUnitCube_meanZero (u (n + k))

/-- Restricting a normalized tail to a smaller cube is a shifted normalized
tail of the smaller local sequence. -/
theorem restrictLocalH1_normalizedLocalH1 {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    restrictLocalH1 hmn (normalizedLocalH1 u n k) =
      normalizedLocalH1 u m (k + (n - m)) := by
  have hindex : m + (k + (n - m)) = n + k := by omega
  apply H1Function.ext
  · change (normalizeOnUnitCube (u (n + k))).toFun =
      (normalizeOnUnitCube (u (m + (k + (n - m))))).toFun
    rw [hindex]
  · change (normalizeOnUnitCube (u (n + k))).grad =
      (normalizeOnUnitCube (u (m + (k + (n - m))))).grad
    rw [hindex]

/-! ## The fixed-anchor Poincare bridge -/

private theorem localValueRestrict_toScalarL2 {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    localValueRestrict hmn u.toScalarL2 =
      (restrictLocalH1 hmn u).toScalarL2 := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localValueRestrict_coeFn_ae hmn u.toScalarL2).trans
    ((u.coeFn_toScalarL2.filter_mono (ae_mono hmu)).trans
      (restrictLocalH1 hmn u).coeFn_toScalarL2.symm)

private theorem localGradientRestrict_gradToHilbertVectorL2
    {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    localGradientRestrict hmn u.gradToHilbertVectorL2 =
      (restrictLocalH1 hmn u).gradToHilbertVectorL2 := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localGradientRestrict_coeFn_ae hmn u.gradToHilbertVectorL2).trans
    ((u.coeFn_gradToHilbertVectorL2.filter_mono (ae_mono hmu)).trans
      (restrictLocalH1 hmn u).coeFn_gradToHilbertVectorL2.symm)

private theorem localValueRestrict_oneScalarL2 {d m n : ℕ} (hmn : m ≤ n) :
    localValueRestrict hmn (oneScalarL2 (U := localGradientCube d n)) =
      oneScalarL2 (U := localGradientCube d m) := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localValueRestrict_coeFn_ae hmn
      (oneScalarL2 (U := localGradientCube d n))).trans
    (((coeFn_oneScalarL2 (U := localGradientCube d n)).filter_mono
      (ae_mono hmu)).trans
      (coeFn_oneScalarL2 (U := localGradientCube d m)).symm)

private theorem integralAverageCLM_one_localGradientCube (d n : ℕ) :
    integralAverageCLM (U := localGradientCube d n)
      (oneScalarL2 (U := localGradientCube d n)) = 1 := by
  rw [integralAverageCLM_apply]
  have hone :
      ∫ x in localGradientCube d n,
          oneScalarL2 (U := localGradientCube d n) x ∂volume =
        (volume (localGradientCube d n)).toReal := by
    calc
      ∫ x in localGradientCube d n,
          oneScalarL2 (U := localGradientCube d n) x ∂volume =
          ∫ _x in localGradientCube d n, (1 : ℝ) ∂volume := by
            exact integral_congr_ae
              (coeFn_oneScalarL2 (U := localGradientCube d n))
      _ = (volume (localGradientCube d n)).toReal := by
        simp [MeasureTheory.measureReal_def]
  rw [hone]
  have hvol : 0 < (volume (localGradientCube d n)).toReal := by
    simpa [localGradientCube, volume_openCubeSet_toReal] using
      cubeVolume_pos (originCube d (n : ℤ))
  exact inv_mul_cancel₀ hvol.ne'

/-- A positive cube-dependent constant for Poincare with the additive gauge
fixed by zero average on cube zero. -/
@[expose]
noncomputable def anchoredLocalPoincareConstant (d n : ℕ) : ℝ :=
  1 +
    (1 + ‖oneScalarL2 (U := localGradientCube d n)‖ *
      ‖integralAverageCLM (U := localGradientCube d 0)‖) *
      (originCubeMeanZeroH1CoerciveEstimate d (n : ℤ)).constantValue

/-- The fixed-anchor Poincare constant is strictly positive. -/
theorem anchoredLocalPoincareConstant_pos (d n : ℕ) :
    0 < anchoredLocalPoincareConstant d n := by
  unfold anchoredLocalPoincareConstant
  have hC :=
    (originCubeMeanZeroH1CoerciveEstimate d (n : ℤ)).constant_nonneg
  positivity

/-- Poincare on an outer exhaustion cube, with its additive constant fixed by
zero average on cube zero. -/
theorem norm_toScalarL2_le_anchoredLocalPoincareConstant_mul_grad
    {d n : ℕ} (w : H1Function (localGradientCube d n))
    (hmean : MeanZeroOn (localGradientCube d 0)
      (restrictLocalH1 (Nat.zero_le n) w).toFun) :
    ‖w.toScalarL2‖ ≤
      anchoredLocalPoincareConstant d n * ‖w.gradToHilbertVectorL2‖ := by
  let a : ℝ := integralAverage (localGradientCube d n) w
  let C : ℝ :=
    (originCubeMeanZeroH1CoerciveEstimate d (n : ℤ)).constantValue
  let A : ℝ := ‖integralAverageCLM (U := localGradientCube d 0)‖
  let s : ℝ := ‖oneScalarL2 (U := localGradientCube d n)‖
  have hmeanCLM :
      integralAverageCLM (U := localGradientCube d 0)
          (restrictLocalH1 (Nat.zero_le n) w).toScalarL2 = 0 := by
    rw [← H1Function.integralAverage_eq_integralAverageCLM_toScalarL2]
    change (volume (localGradientCube d 0)).toReal⁻¹ *
      ∫ x in localGradientCube d 0,
        (restrictLocalH1 (Nat.zero_le n) w).toFun x ∂volume = 0
    rw [hmean, mul_zero]
  have havgSub :
      integralAverageCLM (U := localGradientCube d 0)
          (restrictLocalH1 (Nat.zero_le n) w.subAverage).toScalarL2 = -a := by
    rw [← localValueRestrict_toScalarL2]
    rw [H1Function.toScalarL2_subAverage_eq_subAverageValueCLM,
      subAverageValueCLM_apply, map_sub, map_smul,
      localValueRestrict_toScalarL2, localValueRestrict_oneScalarL2,
      map_sub, map_smul, hmeanCLM,
      integralAverageCLM_one_localGradientCube]
    simp only [smul_eq_mul, mul_one, zero_sub, a]
    rw [H1Function.integralAverage_eq_integralAverageCLM_toScalarL2]
  have hinnerNorm :
      ‖(restrictLocalH1 (Nat.zero_le n) w.subAverage).toScalarL2‖ ≤
        ‖w.subAverage.toScalarL2‖ := by
    rw [← localValueRestrict_toScalarL2]
    exact norm_localValueRestrict_le (Nat.zero_le n) w.subAverage.toScalarL2
  have ha : |a| ≤ A * ‖w.subAverage.toScalarL2‖ := by
    calc
      |a| = ‖-a‖ := by simp [Real.norm_eq_abs]
      _ = ‖integralAverageCLM (U := localGradientCube d 0)
          (restrictLocalH1 (Nat.zero_le n) w.subAverage).toScalarL2‖ := by
            rw [havgSub]
      _ ≤ A * ‖(restrictLocalH1 (Nat.zero_le n) w.subAverage).toScalarL2‖ := by
            exact (integralAverageCLM (U := localGradientCube d 0)).le_opNorm _
      _ ≤ A * ‖w.subAverage.toScalarL2‖ := by
            exact mul_le_mul_of_nonneg_left hinnerNorm (norm_nonneg _)
  have hp :
      ‖w.subAverage.toScalarL2‖ ≤ C * ‖w.gradToHilbertVectorL2‖ := by
    let :
        IsFiniteMeasure
          (volumeMeasureOn (openCubeSet (originCube d (n : ℤ)))) := by
      simpa [localGradientCube] using
        (inferInstance :
          IsFiniteMeasure (volumeMeasureOn (localGradientCube d n)))
    have hbase :=
      (originCubeMeanZeroH1CoerciveEstimate d (n : ℤ)).bound_subAverage w
    calc
      ‖w.subAverage.toScalarL2‖ ≤ C * ‖w.gradToVectorL2‖ := by
        simpa [C, H1MeanZeroFunction.valueL2Norm] using! hbase
      _ ≤ C * ‖w.gradToHilbertVectorL2‖ := by
        exact mul_le_mul_of_nonneg_left
          w.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
          (originCubeMeanZeroH1CoerciveEstimate d (n : ℤ)).constant_nonneg
  have hsplit :
      w.toScalarL2 = w.subAverage.toScalarL2 +
        a • oneScalarL2 (U := localGradientCube d n) := by
    have hsub :
        w.subAverage.toScalarL2 = w.toScalarL2 -
          a • oneScalarL2 (U := localGradientCube d n) := by
      rw [H1Function.toScalarL2_subAverage_eq_subAverageValueCLM,
        subAverageValueCLM_apply]
      simp only [a]
      rw [H1Function.integralAverage_eq_integralAverageCLM_toScalarL2]
    rw [hsub]
    abel
  have hcenter :
      ‖w.toScalarL2‖ ≤ (1 + s * A) * ‖w.subAverage.toScalarL2‖ := by
    calc
      ‖w.toScalarL2‖ ≤ ‖w.subAverage.toScalarL2‖ +
          ‖a • oneScalarL2 (U := localGradientCube d n)‖ := by
            rw [hsplit]
            exact norm_add_le _ _
      _ = ‖w.subAverage.toScalarL2‖ + |a| * s := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖w.subAverage.toScalarL2‖ +
          (A * ‖w.subAverage.toScalarL2‖) * s := by
            have has : |a| * s ≤ (A * ‖w.subAverage.toScalarL2‖) * s :=
              mul_le_mul_of_nonneg_right ha (by dsimp only [s]; positivity)
            exact add_le_add_right has _
      _ = (1 + s * A) * ‖w.subAverage.toScalarL2‖ := by ring
  calc
    ‖w.toScalarL2‖ ≤ (1 + s * A) * ‖w.subAverage.toScalarL2‖ := hcenter
    _ ≤ (1 + s * A) * (C * ‖w.gradToHilbertVectorL2‖) := by
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ anchoredLocalPoincareConstant d n *
        ‖w.gradToHilbertVectorL2‖ := by
      unfold anchoredLocalPoincareConstant
      dsimp only [A, C, s]
      linarith only [norm_nonneg w.gradToHilbertVectorL2]

private theorem toScalarL2_sub {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).toScalarL2 = u.toScalarL2 - v.toScalarL2 := by
  rw [sub_eq_add_neg, H1Function.toScalarL2_add]
  have hneg := H1Function.toScalarL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

private theorem gradToHilbertVectorL2_sub {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  rw [sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add]
  have hneg := H1Function.gradToHilbertVectorL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

/-- Normalized finite-volume gradients are Cauchy on every fixed exhaustion
cube. -/
@[expose]
def NormalizedLocalGradientCauchy {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) : Prop :=
  ∀ n, CauchySeq (fun k => (normalizedLocalH1 u n k).gradToHilbertVectorL2)

private theorem normalizedLocalH1_sub_meanZero {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k l : ℕ) :
    MeanZeroOn (localGradientCube d 0)
      (restrictLocalH1 (Nat.zero_le n)
        (normalizedLocalH1 u n k - normalizedLocalH1 u n l)).toFun := by
  let wk : H1MeanZeroFunction (localGradientCube d 0) :=
    ⟨restrictLocalH1 (Nat.zero_le n) (normalizedLocalH1 u n k),
      normalizedLocalH1_meanZero u n k⟩
  let wl : H1MeanZeroFunction (localGradientCube d 0) :=
    ⟨restrictLocalH1 (Nat.zero_le n) (normalizedLocalH1 u n l),
      normalizedLocalH1_meanZero u n l⟩
  change MeanZeroOn (localGradientCube d 0) (wk - wl).toH1Function.toFun
  exact (wk - wl).meanZero

/-- The fixed-anchor Poincare estimate upgrades local gradient Cauchy to local
scalar-value Cauchy. -/
theorem normalizedLocalValue_cauchy {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) (n : ℕ) :
    CauchySeq (fun k => (normalizedLocalH1 u n k).toScalarL2) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let C : ℝ := anchoredLocalPoincareConstant d n
  have hC : 0 < C := anchoredLocalPoincareConstant_pos d n
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff.mp (hgrad n) (ε / C) (div_pos hε hC))
  refine ⟨N, ?_⟩
  intro k hk l hl
  let w := normalizedLocalH1 u n k - normalizedLocalH1 u n l
  have hP :=
    norm_toScalarL2_le_anchoredLocalPoincareConstant_mul_grad w
      (normalizedLocalH1_sub_meanZero u n k l)
  calc
    dist (normalizedLocalH1 u n k).toScalarL2
        (normalizedLocalH1 u n l).toScalarL2 =
        ‖w.toScalarL2‖ := by
          rw [dist_eq_norm, toScalarL2_sub]
    _ ≤ C * ‖w.gradToHilbertVectorL2‖ := by simpa [C] using hP
    _ = C * dist (normalizedLocalH1 u n k).gradToHilbertVectorL2
        (normalizedLocalH1 u n l).gradToHilbertVectorL2 := by
          rw [dist_eq_norm, gradToHilbertVectorL2_sub]
    _ < C * (ε / C) := mul_lt_mul_of_pos_left (hN k hk l hl) hC
    _ = ε := by field_simp

/-- The normalized local value-gradient pair on one fixed cube. -/
@[expose]
noncomputable def normalizedLocalPair {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k : ℕ) :
    LocalValueL2 d n × LocalGradientL2 d n :=
  ((normalizedLocalH1 u n k).toScalarL2,
    (normalizedLocalH1 u n k).gradToHilbertVectorL2)

/-- Normalized local value-gradient pairs are Cauchy under the explicit
gradient Cauchy premise. -/
theorem normalizedLocalPair_cauchy {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) (n : ℕ) :
    CauchySeq (normalizedLocalPair u n) :=
  (normalizedLocalValue_cauchy u hgrad n).prodMk (hgrad n)

/-! ## Projective local-limit assembly -/

/-- The unique limit of the normalized value-gradient sequence on one fixed
cube. -/
@[expose]
public noncomputable def normalizedLocalPairLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) (n : ℕ) :
    LocalValueL2 d n × LocalGradientL2 d n :=
  Classical.choose
    (cauchySeq_tendsto_of_complete (normalizedLocalPair_cauchy u hgrad n))

/-- Characterization of the chosen local pair limit. -/
private theorem tendsto_normalizedLocalPairLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) (n : ℕ) :
    _root_.Filter.Tendsto (normalizedLocalPair u n) _root_.Filter.atTop
      (nhds (normalizedLocalPairLimit u hgrad n)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete (normalizedLocalPair_cauchy u hgrad n))

private theorem localValueRestrict_normalizedLocalPair {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    localValueRestrict hmn (normalizedLocalPair u n k).1 =
      (normalizedLocalPair u m (k + (n - m))).1 := by
  rw [normalizedLocalPair, normalizedLocalPair,
    localValueRestrict_toScalarL2,
    restrictLocalH1_normalizedLocalH1]

private theorem localGradientRestrict_normalizedLocalPair {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    localGradientRestrict hmn (normalizedLocalPair u n k).2 =
      (normalizedLocalPair u m (k + (n - m))).2 := by
  rw [normalizedLocalPair, normalizedLocalPair,
    localGradientRestrict_gradToHilbertVectorL2,
    restrictLocalH1_normalizedLocalH1]

private theorem localValueRestrict_normalizedLocalPairLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u)
    {m n : ℕ} (hmn : m ≤ n) :
    localValueRestrict hmn (normalizedLocalPairLimit u hgrad n).1 =
      (normalizedLocalPairLimit u hgrad m).1 := by
  have hn :
      _root_.Filter.Tendsto (fun k => (normalizedLocalPair u n k).1) _root_.Filter.atTop
        (nhds (normalizedLocalPairLimit u hgrad n).1) :=
    (tendsto_normalizedLocalPairLimit u hgrad n).fst_nhds
  have hm :
      _root_.Filter.Tendsto (fun k => (normalizedLocalPair u m k).1) _root_.Filter.atTop
        (nhds (normalizedLocalPairLimit u hgrad m).1) :=
    (tendsto_normalizedLocalPairLimit u hgrad m).fst_nhds
  have hleft :
      _root_.Filter.Tendsto
        (fun k => localValueRestrict hmn (normalizedLocalPair u n k).1)
        _root_.Filter.atTop
        (nhds (localValueRestrict hmn
          (normalizedLocalPairLimit u hgrad n).1)) :=
    ((localValueRestrict hmn).continuous.tendsto
      (normalizedLocalPairLimit u hgrad n).1).comp hn
  have hshift :
      _root_.Filter.Tendsto
        (fun k => (normalizedLocalPair u m (k + (n - m))).1)
        _root_.Filter.atTop (nhds (normalizedLocalPairLimit u hgrad m).1) :=
    (_root_.Filter.tendsto_add_atTop_iff_nat (n - m)).mpr hm
  have hright :
      _root_.Filter.Tendsto
        (fun k => localValueRestrict hmn (normalizedLocalPair u n k).1)
        _root_.Filter.atTop (nhds (normalizedLocalPairLimit u hgrad m).1) := by
    simpa only [localValueRestrict_normalizedLocalPair] using hshift
  exact tendsto_nhds_unique hleft hright

private theorem localGradientRestrict_normalizedLocalPairLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u)
    {m n : ℕ} (hmn : m ≤ n) :
    localGradientRestrict hmn (normalizedLocalPairLimit u hgrad n).2 =
      (normalizedLocalPairLimit u hgrad m).2 := by
  have hn :
      _root_.Filter.Tendsto (fun k => (normalizedLocalPair u n k).2) _root_.Filter.atTop
        (nhds (normalizedLocalPairLimit u hgrad n).2) :=
    (tendsto_normalizedLocalPairLimit u hgrad n).snd_nhds
  have hm :
      _root_.Filter.Tendsto (fun k => (normalizedLocalPair u m k).2) _root_.Filter.atTop
        (nhds (normalizedLocalPairLimit u hgrad m).2) :=
    (tendsto_normalizedLocalPairLimit u hgrad m).snd_nhds
  have hleft :
      _root_.Filter.Tendsto
        (fun k => localGradientRestrict hmn (normalizedLocalPair u n k).2)
        _root_.Filter.atTop
        (nhds (localGradientRestrict hmn
          (normalizedLocalPairLimit u hgrad n).2)) :=
    ((localGradientRestrict hmn).continuous.tendsto
      (normalizedLocalPairLimit u hgrad n).2).comp hn
  have hshift :
      _root_.Filter.Tendsto
        (fun k => (normalizedLocalPair u m (k + (n - m))).2)
        _root_.Filter.atTop (nhds (normalizedLocalPairLimit u hgrad m).2) :=
    (_root_.Filter.tendsto_add_atTop_iff_nat (n - m)).mpr hm
  have hright :
      _root_.Filter.Tendsto
        (fun k => localGradientRestrict hmn (normalizedLocalPair u n k).2)
        _root_.Filter.atTop (nhds (normalizedLocalPairLimit u hgrad m).2) := by
    simpa only [localGradientRestrict_normalizedLocalPair] using hshift
  exact tendsto_nhds_unique hleft hright

@[expose]
public noncomputable def normalizedLocalValueLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    LocalValueCarrier d :=
  ⟨fun n => (normalizedLocalPairLimit u hgrad n).1,
    fun _m _n hmn => localValueRestrict_normalizedLocalPairLimit u hgrad hmn⟩

@[expose]
public noncomputable def normalizedLocalGradientLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    LocalGradientCarrier d :=
  ⟨fun n => (normalizedLocalPairLimit u hgrad n).2,
    fun _m _n hmn => localGradientRestrict_normalizedLocalPairLimit u hgrad hmn⟩

/-- A normalized local `H¹` carrier consists only of compatible local `L²`
value and gradient classes, the closed weak-gradient relation on each cube,
and the fixed-unit zero-average condition. -/
structure NormalizedLocalH1Carrier (d : ℕ) where
  value : LocalValueCarrier d
  gradient : LocalGradientCarrier d
  graph : ∀ n,
    (LocalValueCarrier.component value n,
        LocalGradientCarrier.component gradient n) ∈
      h1GraphClosedSubmodule (U := localGradientCube d n)
  unitMeanZero :
    scalarIntegralCLM (U := localGradientCube d 0)
      (LocalValueCarrier.component value 0) = 0

namespace NormalizedLocalH1Carrier

/-- The scalar local component on the `n`th cube. -/
@[expose]
def valueComponent {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    LocalValueL2 d n :=
  LocalValueCarrier.component z.value n

/-- The weak-gradient local component on the `n`th cube. -/
@[expose]
def gradientComponent {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    LocalGradientL2 d n :=
  LocalGradientCarrier.component z.gradient n

/-- Normalized local carriers are determined by their value and gradient
components. -/
@[ext] theorem ext {d : ℕ} {z w : NormalizedLocalH1Carrier d}
    (hvalue : ∀ n, valueComponent z n = valueComponent w n)
    (hgradient : ∀ n, gradientComponent z n = gradientComponent w n) :
    z = w := by
  cases z with
  | mk zv zg zgraph zmean =>
    cases w with
    | mk wv wg wgraph wmean =>
      have hv : zv = wv := LocalValueCarrier.ext hvalue
      have hg : zg = wg := LocalGradientCarrier.ext hgradient
      cases hv
      cases hg
      rfl

end NormalizedLocalH1Carrier

private theorem normalizedLocalPairLimit_mem_h1Graph {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) (n : ℕ) :
    normalizedLocalPairLimit u hgrad n ∈
      h1GraphClosedSubmodule (U := localGradientCube d n) := by
  apply mem_h1GraphClosedSubmodule_of_tendsto_h1Function
    (l := _root_.Filter.atTop) (w := normalizedLocalH1 u n)
  · exact (tendsto_normalizedLocalPairLimit u hgrad n).fst_nhds
  · exact (tendsto_normalizedLocalPairLimit u hgrad n).snd_nhds

private theorem scalarIntegral_normalizedLocalPair_zero {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (k : ℕ) :
    scalarIntegralCLM (U := localGradientCube d 0)
      (normalizedLocalPair u 0 k).1 = 0 := by
  have hmean := normalizedLocalH1_meanZero u 0 k
  change MeanZeroOn (localGradientCube d 0)
    (normalizedLocalH1 u 0 k).toFun at hmean
  rw [normalizedLocalPair, scalarIntegralCLM_apply]
  exact
    (integral_congr_ae (normalizedLocalH1 u 0 k).coeFn_toScalarL2).trans hmean

private theorem normalizedLocalPairLimit_unitMeanZero {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    scalarIntegralCLM (U := localGradientCube d 0)
      (normalizedLocalPairLimit u hgrad 0).1 = 0 := by
  have hvalue :
      _root_.Filter.Tendsto (fun k => (normalizedLocalPair u 0 k).1) _root_.Filter.atTop
        (nhds (normalizedLocalPairLimit u hgrad 0).1) :=
    (tendsto_normalizedLocalPairLimit u hgrad 0).fst_nhds
  have hleft :
      _root_.Filter.Tendsto
        (fun k => scalarIntegralCLM (U := localGradientCube d 0)
          (normalizedLocalPair u 0 k).1)
        _root_.Filter.atTop
        (nhds (scalarIntegralCLM (U := localGradientCube d 0)
          (normalizedLocalPairLimit u hgrad 0).1)) :=
    ((scalarIntegralCLM (U := localGradientCube d 0)).continuous.tendsto
      (normalizedLocalPairLimit u hgrad 0).1).comp hvalue
  have hright :
      _root_.Filter.Tendsto
        (fun k => scalarIntegralCLM (U := localGradientCube d 0)
          (normalizedLocalPair u 0 k).1)
        _root_.Filter.atTop (nhds 0) := by
    simpa only [scalarIntegral_normalizedLocalPair_zero] using
      (tendsto_const_nhds :
        _root_.Filter.Tendsto (fun _k : ℕ => (0 : ℝ)) _root_.Filter.atTop (nhds 0))
  exact tendsto_nhds_unique hleft hright

@[expose]
public noncomputable def assembledNormalizedLocalH1Carrier {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    NormalizedLocalH1Carrier d where
  value := normalizedLocalValueLimit u hgrad
  gradient := normalizedLocalGradientLimit u hgrad
  graph n := normalizedLocalPairLimit_mem_h1Graph u hgrad n
  unitMeanZero := normalizedLocalPairLimit_unitMeanZero u hgrad

/-- Literal characterization of a normalized local limit: convergence of the
value-gradient pair on every fixed exhaustion cube. -/
@[expose]
def IsNormalizedLocalLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (z : NormalizedLocalH1Carrier d) : Prop :=
  ∀ n,
    _root_.Filter.Tendsto (normalizedLocalPair u n) _root_.Filter.atTop
      (nhds (z.valueComponent n, z.gradientComponent n))

private theorem assembledNormalizedLocalH1Carrier_isLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    IsNormalizedLocalLimit u (assembledNormalizedLocalH1Carrier u hgrad) := by
  intro n
  simpa [assembledNormalizedLocalH1Carrier,
    NormalizedLocalH1Carrier.valueComponent,
    NormalizedLocalH1Carrier.gradientComponent,
    normalizedLocalValueLimit, normalizedLocalGradientLimit,
    LocalValueCarrier.component, LocalGradientCarrier.component] using
    tendsto_normalizedLocalPairLimit u hgrad n

/-- Under the explicit local gradient-Cauchy premise, the normalized local
limit exists and is unique. -/
theorem existsUnique_normalizedLocalLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    ∃! z : NormalizedLocalH1Carrier d, IsNormalizedLocalLimit u z := by
  refine ⟨assembledNormalizedLocalH1Carrier u hgrad,
    assembledNormalizedLocalH1Carrier_isLimit u hgrad, ?_⟩
  intro z hz
  apply NormalizedLocalH1Carrier.ext
  · intro n
    have hp := tendsto_nhds_unique (hz n)
      (assembledNormalizedLocalH1Carrier_isLimit u hgrad n)
    exact congrArg Prod.fst hp
  · intro n
    have hp := tendsto_nhds_unique (hz n)
      (assembledNormalizedLocalH1Carrier_isLimit u hgrad n)
    exact congrArg Prod.snd hp

/-- The normalized projective local limit selected from its unique
characterization. -/
@[expose]
noncomputable def normalizedCorrectorLocalLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    NormalizedLocalH1Carrier d :=
  Classical.choose (existsUnique_normalizedLocalLimit u hgrad)

/-- The selected local limit satisfies the literal componentwise
characterization. -/
theorem normalizedCorrectorLocalLimit_isLimit {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u) :
    IsNormalizedLocalLimit u (normalizedCorrectorLocalLimit u hgrad) :=
  (Classical.choose_spec (existsUnique_normalizedLocalLimit u hgrad)).1

/-- The literal convergence characterization identifies exactly the selected
normalized local limit. -/
theorem isNormalizedLocalLimit_iff_eq {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q))
    (hgrad : NormalizedLocalGradientCauchy u)
    (z : NormalizedLocalH1Carrier d) :
    IsNormalizedLocalLimit u z ↔ z = normalizedCorrectorLocalLimit u hgrad := by
  constructor
  · intro hz
    exact (Classical.choose_spec (existsUnique_normalizedLocalLimit u hgrad)).2 z hz
  · rintro rfl
    exact normalizedCorrectorLocalLimit_isLimit u hgrad

end

end HighContrast
end HCPolySupport
