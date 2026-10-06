/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorClassEnergy
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CoefficientEnergySeminorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The local coefficient-energy seminorm

The symmetric coefficient operator is positive on every positive-volume
domain.  Its quadratic form therefore defines a seminorm.  This is the
Minkowski step needed to telescope finite-corrector increments without
introducing the lower ellipticity constant into the quantitative constant.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

private theorem hilbertSymmCoeffOperator_isSymmetric
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    (hilbertSymmCoeffOperator hEll).IsSymmetric := by
  intro F G
  let fL2 : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F
  let gL2 : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) G
  let f : Vec d → Vec d := fun x ↦ fL2 x
  let g : Vec d → Vec d := fun x ↦ gL2 x
  let hf : MemVectorL2 U f := MeasureTheory.Lp.memLp fL2
  let hg : MemVectorL2 U g := MeasureTheory.Lp.memLp gL2
  have hF : toHilbertVectorL2OfVecField hf = F := by
    calc
      toHilbertVectorL2OfVecField hf =
          vectorL2ToHilbertVectorL2 (U := U) (toVectorL2 hf) := by
        exact (vectorL2ToHilbertVectorL2_toVectorL2 hf).symm
      _ = vectorL2ToHilbertVectorL2 (U := U) fL2 := by
        apply congrArg (vectorL2ToHilbertVectorL2 (U := U))
        change hf.toLp (fun x ↦ fL2 x) = fL2
        exact MeasureTheory.Lp.toLp_coeFn fL2 hf
      _ = F := by
        simpa only [fL2] using
          vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 F
  have hG : toHilbertVectorL2OfVecField hg = G := by
    calc
      toHilbertVectorL2OfVecField hg =
          vectorL2ToHilbertVectorL2 (U := U) (toVectorL2 hg) := by
        exact (vectorL2ToHilbertVectorL2_toVectorL2 hg).symm
      _ = vectorL2ToHilbertVectorL2 (U := U) gL2 := by
        apply congrArg (vectorL2ToHilbertVectorL2 (U := U))
        change hg.toLp (fun x ↦ gL2 x) = gL2
        exact MeasureTheory.Lp.toLp_coeFn gL2 hg
      _ = G := by
        simpa only [gL2] using
          vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 G
  rw [← hF, ← hG]
  change
    inner ℝ
        (hilbertSymmCoeffOperator hEll (toHilbertVectorL2OfVecField hf))
        (toHilbertVectorL2OfVecField hg) =
      inner ℝ (toHilbertVectorL2OfVecField hf)
        (hilbertSymmCoeffOperator hEll (toHilbertVectorL2OfVecField hg))
  rw [hilbertSymmCoeffOperator_toHilbertVectorL2OfVecField,
    hilbertSymmCoeffOperator_toHilbertVectorL2OfVecField,
    inner_toHilbertVectorL2OfVecField_eq_integral,
    inner_toHilbertVectorL2OfVecField_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  have hsymm : (symmPart (a x)).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [symmPart]
    ring
  calc
    vecDot (matVecMul (symmPart (a x)) (f x)) (g x) =
        vecDot (g x) (matVecMul (symmPart (a x)) (f x)) :=
      vecDot_comm _ _
    _ = vecDot (f x) (matVecMul (symmPart (a x)) (g x)) :=
      (vecDot_matVecMul_comm_of_isSymm hsymm (f x) (g x)).symm

/-- The local symmetric coefficient operator is positive on a domain of
positive volume. -/
theorem hilbertSymmCoeffOperator_isPositive
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < volume U) (hvoltop : volume U ≠ ⊤) :
    (hilbertSymmCoeffOperator hEll).IsPositive := by
  refine ⟨hilbertSymmCoeffOperator_isSymmetric hEll, ?_⟩
  intro F
  have hE := normalizedLocalSymmetricEnergy_nonneg hEll F
  have hvolReal : 0 < (volume U).toReal := ENNReal.toReal_pos hvol.ne' hvoltop
  unfold normalizedLocalSymmetricEnergy at hE
  dsimp [ContinuousLinearMap.reApplyInnerSelf]
  exact nonneg_of_mul_nonneg_right hE (inv_pos.mpr hvolReal)

private theorem sq_inner_apply_le_mul_inner_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) (x y : E) :
    inner ℝ (T x) y ^ 2 ≤
      inner ℝ (T x) x * inner ℝ (T y) y := by
  have hy : 0 ≤ inner ℝ (T y) y := hT.inner_nonneg_left y
  refine sq_le_mul_of_quadratic_nonneg hy ?_
  intro t
  have hnonneg := hT.inner_nonneg_left (x - t • y)
  have hsymm : inner ℝ (T y) x = inner ℝ (T x) y := by
    calc
      inner ℝ (T y) x = inner ℝ y (T x) :=
        hT.inner_left_eq_inner_right y x
      _ = inner ℝ (T x) y := real_inner_comm _ _
  have hquad :
      inner ℝ (T (x - t • y)) (x - t • y) =
        inner ℝ (T x) x - 2 * t * inner ℝ (T x) y +
          t ^ 2 * inner ℝ (T y) y := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hsymm]
    ring
  rw [hquad] at hnonneg
  exact hnonneg

/-- The square root of a positive operator's quadratic form satisfies the
triangle inequality. -/
theorem sqrt_inner_apply_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) (x y : E) :
    Real.sqrt (inner ℝ (T (x + y)) (x + y)) ≤
      Real.sqrt (inner ℝ (T x) x) + Real.sqrt (inner ℝ (T y) y) := by
  let qx : ℝ := inner ℝ (T x) x
  let qy : ℝ := inner ℝ (T y) y
  let c : ℝ := inner ℝ (T x) y
  have hqx : 0 ≤ qx := hT.inner_nonneg_left x
  have hqy : 0 ≤ qy := hT.inner_nonneg_left y
  have hcSq : c ^ 2 ≤ qx * qy := by
    simpa only [c, qx, qy] using sq_inner_apply_le_mul_inner_apply T hT x y
  have hc : c ≤ Real.sqrt qx * Real.sqrt qy := by
    have hprod : 0 ≤ Real.sqrt qx * Real.sqrt qy :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply le_of_sq_le_sq
    · simpa [Real.sq_sqrt hqx, Real.sq_sqrt hqy, mul_pow] using hcSq
    · exact hprod
  have hsymm : inner ℝ (T y) x = inner ℝ (T x) y := by
    calc
      inner ℝ (T y) x = inner ℝ y (T x) :=
        hT.inner_left_eq_inner_right y x
      _ = inner ℝ (T x) y := real_inner_comm _ _
  have hquad : inner ℝ (T (x + y)) (x + y) = qx + 2 * c + qy := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsymm]
    dsimp only [qx, qy, c]
    ring
  have hnonneg : 0 ≤ inner ℝ (T (x + y)) (x + y) :=
    hT.inner_nonneg_left (x + y)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · rw [hquad]
    rw [add_sq, Real.sq_sqrt hqx, Real.sq_sqrt hqy]
    nlinarith only [hc]

/-- The square root of normalized local symmetric energy is subadditive. -/
theorem sqrt_normalizedLocalSymmetricEnergy_add_le
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (hvol : 0 < volume U)
    (hvoltop : volume U ≠ ⊤)
    (F G : HilbertVectorL2 U) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (F + G)) ≤
      Real.sqrt (normalizedLocalSymmetricEnergy hEll F) +
        Real.sqrt (normalizedLocalSymmetricEnergy hEll G) := by
  let c : ℝ := (volume U).toReal⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hpos := hilbertSymmCoeffOperator_isPositive hEll hvol hvoltop
  let T : HilbertVectorL2 U →L[ℝ] HilbertVectorL2 U :=
    c • hilbertSymmCoeffOperator hEll
  have hT : T.IsPositive := hpos.smul_of_nonneg hc
  simpa only [normalizedLocalSymmetricEnergy, T, c,
    smul_apply, real_inner_smul_left] using
    sqrt_inner_apply_add_le T hT F G

/-- A finite coefficient-energy telescope is bounded by the sum of its
successive coefficient-energy increments. -/
theorem sqrt_normalizedLocalSymmetricEnergy_sub_le_sum_Ico
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (hvol : 0 < volume U)
    (hvoltop : volume U ≠ ⊤)
    (g : ℕ → HilbertVectorL2 U) (k m : ℕ) (hkm : k ≤ m) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (g m - g k)) ≤
      ∑ j ∈ Finset.Ico k m,
        Real.sqrt
          (normalizedLocalSymmetricEnergy hEll (g (j + 1) - g j)) := by
  induction m, hkm using Nat.le_induction with
  | base => simp [normalizedLocalSymmetricEnergy]
  | succ m hkm ih =>
      have hsplit : g (m + 1) - g k =
          (g (m + 1) - g m) + (g m - g k) := by abel
      rw [hsplit]
      calc
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
            ((g (m + 1) - g m) + (g m - g k))) ≤
            Real.sqrt (normalizedLocalSymmetricEnergy hEll (g (m + 1) - g m)) +
              Real.sqrt (normalizedLocalSymmetricEnergy hEll (g m - g k)) :=
          sqrt_normalizedLocalSymmetricEnergy_add_le
            hEll hvol hvoltop _ _
        _ ≤ Real.sqrt
              (normalizedLocalSymmetricEnergy hEll (g (m + 1) - g m)) +
            ∑ j ∈ Finset.Ico k m,
              Real.sqrt
                (normalizedLocalSymmetricEnergy hEll (g (j + 1) - g j)) := by
          exact add_le_add le_rfl ih
        _ = ∑ j ∈ Finset.Ico k (m + 1),
              Real.sqrt
                (normalizedLocalSymmetricEnergy hEll (g (j + 1) - g j)) := by
          rw [Finset.sum_Ico_succ_top hkm]
          ac_rfl

/-- A uniform coefficient-energy tail passes to a local Hilbert limit. -/
theorem sqrt_normalizedLocalSymmetricEnergy_limit_sub_le_of_uniform_tail
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (g : ℕ → HilbertVectorL2 U) (L : HilbertVectorL2 U) (B : ℝ)
    (hlim : Filter.Tendsto g Filter.atTop (nhds L))
    (k : ℕ)
    (htail : ∀ m : ℕ, k ≤ m →
      Real.sqrt (normalizedLocalSymmetricEnergy hEll (g m - g k)) ≤ B) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (L - g k)) ≤ B := by
  have henergy : Filter.Tendsto
      (fun m ↦ normalizedLocalSymmetricEnergy hEll (g m - g k))
      Filter.atTop
      (nhds (normalizedLocalSymmetricEnergy hEll (L - g k))) :=
    (continuous_normalizedLocalSymmetricEnergy hEll).continuousAt.tendsto.comp
      (hlim.sub tendsto_const_nhds)
  have hsqrt : Filter.Tendsto
      (fun m ↦ Real.sqrt
        (normalizedLocalSymmetricEnergy hEll (g m - g k)))
      Filter.atTop
      (nhds (Real.sqrt
        (normalizedLocalSymmetricEnergy hEll (L - g k)))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp henergy
  exact le_of_tendsto hsqrt
    ((Filter.eventually_ge_atTop k).mono fun m hm ↦ htail m hm)

end

end HighContrast
end HCPolySupport
