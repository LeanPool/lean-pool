/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakTransport
public import LeanPool.HighContrastHomogenization.Provider.Response.LinearOscillationDuality
public import LeanPool.HighContrastHomogenization.Provider.Response.ReferenceWeakBridge
public import LeanPool.HighContrastHomogenization.Support.Besov.Poincare.Descendants
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.Averages
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise

/-!
# High-contrast homogenization: Provider.Response.AdaptedWeakChild

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weak seminorm control on one aligned child

The normalized first-power cell-average sum is bounded by its square-average
counterpart.  On a fixed descendant the latter costs only the square root of
the number of siblings when compared with the parent cube.  These two facts
turn the terminal adapted weak seminorm into a uniform bound for every finite
child-cube scalar seminorm.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The endpoint inner `L¹` descendant average is bounded by the normalized
`L²` descendant average at every finite collection of depths. -/
theorem cubeBesovCircPartialNorm_one_one_le_two_one
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (G : Vec d → ℝ) :
    cubeBesovCircPartialNorm Q s 1 1 N G ≤
      cubeBesovCircPartialNorm Q s 2 1 N G := by
  rw [cubeBesovCircPartialNorm_one_one_eq_sum]
  rw [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
  apply Finset.sum_le_sum
  intro j hj
  have havg : descendantsAverage Q j
      (fun R ↦ Real.sqrt (‖cubeAverage R G‖ ^ 2)) ≤
      Real.sqrt (descendantsAverage Q j
        (fun R ↦ ‖cubeAverage R G‖ ^ 2)) :=
    descendantsAverage_sqrt_le_sqrt_descendantsAverage_of_nonneg
      Q j (fun R ↦ ‖cubeAverage R G‖ ^ 2) (fun R hR ↦ sq_nonneg _)
  have habs : descendantsAverage Q j
      (fun R ↦ Real.sqrt (‖cubeAverage R G‖ ^ 2)) =
      descendantsAverage Q j (fun R ↦ ‖cubeAverage R G‖) := by
    congr 1
    funext R
    exact Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (norm_nonneg _))
  rw [habs] at havg
  have hweight := cubeBesovCircDepthWeight_nonneg Q s j
  simpa [cubeBesovCircDepthSeminorm, cubeBesovCircDepthAverage,
    Real.rpow_one, Real.sqrt_eq_rpow] using
      mul_le_mul_of_nonneg_left havg hweight

/-- One selected descendant average is bounded by the parent average times the
number of descendants at the selected depth. -/
theorem descendantsAverage_le_card_mul_parentAverage
    {Q R : TriadicCube d} {H : ℕ} (hR : R ∈ descendantsAtDepth Q H)
    (j : ℕ) {F : TriadicCube d → ℝ}
    (hF : ∀ S ∈ descendantsAtDepth Q (H + j), 0 ≤ F S) :
    descendantsAverage R j F ≤
      ((descendantsAtDepth Q H).card : ℝ) *
        descendantsAverage Q (H + j) F := by
  classical
  have hnonneg : ∀ U ∈ descendantsAtDepth Q H,
      0 ≤ descendantsAverage U j F := by
    intro U hU
    apply descendantsAverage_nonneg
    intro S hS
    exact hF S (mem_descendantsAtDepth_add hU hS)
  have hsingle : descendantsAverage R j F ≤
      ∑ U ∈ descendantsAtDepth Q H, descendantsAverage U j F :=
    Finset.single_le_sum hnonneg hR
  rw [descendantsAverage_add_eq_descendantsAverage_descendantsAverage]
  unfold descendantsAverage
  have hcard : (((descendantsAtDepth Q H).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q H)
  calc
    descendantsAverage R j F ≤
        ∑ U ∈ descendantsAtDepth Q H, descendantsAverage U j F := hsingle
    _ = ((descendantsAtDepth Q H).card : ℝ) *
          (((descendantsAtDepth Q H).card : ℝ)⁻¹ *
            ∑ U ∈ descendantsAtDepth Q H, descendantsAverage U j F) := by
      field_simp [hcard]

/-- A fixed depth-`H` descendant has at most the square-root cardinality loss
against the parent's finite scalar circ norm. -/
theorem cubeBesovCircPartialNorm_child_le_sqrt_card_mul_parent
    {Q R : TriadicCube d} {H : ℕ} (hR : R ∈ descendantsAtDepth Q H)
    (s : ℝ) (N : ℕ) (G : Vec d → ℝ) :
    cubeBesovCircPartialNorm R s 1 1 N G ≤
      Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
        cubeBesovCircPartialNorm Q s 2 1 (H + N) G := by
  calc
    cubeBesovCircPartialNorm R s 1 1 N G ≤
        cubeBesovCircPartialNorm R s 2 1 N G :=
      cubeBesovCircPartialNorm_one_one_le_two_one R s N G
    _ ≤ Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
        cubeBesovCircPartialNorm Q s 2 1 (H + N) G := by
      simp only [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm,
        ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
      have hdepth : ∀ j : ℕ,
          cubeBesovCircDepthSeminorm R s 2 G j ≤
            Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
              cubeBesovCircDepthSeminorm Q s 2 G (H + j) := by
        intro j
        have havg := descendantsAverage_le_card_mul_parentAverage hR j
          (F := fun S ↦ ‖cubeAverage S G‖ ^ 2)
          (fun S hS ↦ sq_nonneg _)
        have hcard0 : 0 ≤ ((descendantsAtDepth Q H).card : ℝ) := by positivity
        have hglobal : 0 ≤ cubeBesovCircDepthAverage Q 2 G (H + j) :=
          cubeBesovCircDepthAverage_nonneg Q 2 G (H + j)
        have hsqrt : Real.sqrt (cubeBesovCircDepthAverage R 2 G j) ≤
            Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
              Real.sqrt (cubeBesovCircDepthAverage Q 2 G (H + j)) := by
          calc
            Real.sqrt (cubeBesovCircDepthAverage R 2 G j) ≤
                Real.sqrt (((descendantsAtDepth Q H).card : ℝ) *
                  cubeBesovCircDepthAverage Q 2 G (H + j)) :=
              Real.sqrt_le_sqrt (by simpa [cubeBesovCircDepthAverage] using havg)
            _ = _ := Real.sqrt_mul hcard0 _
        have hw := cubeBesovCircDepthWeight_nonneg R s j
        simpa [cubeBesovCircDepthSeminorm, Real.sqrt_eq_rpow,
          cubeBesovCircDepthWeight_eq_of_mem_descendantsAtDepth hR,
          mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hsqrt hw
      calc
        (∑ j ∈ Finset.range (N + 1),
            cubeBesovCircDepthSeminorm R s 2 G j) ≤
            ∑ j ∈ Finset.range (N + 1),
              Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
                cubeBesovCircDepthSeminorm Q s 2 G (H + j) :=
          Finset.sum_le_sum fun j hj ↦ hdepth j
        _ = Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
            ∑ j ∈ Finset.range (N + 1),
              cubeBesovCircDepthSeminorm Q s 2 G (H + j) := by
          rw [Finset.mul_sum]
        _ ≤ Real.sqrt ((descendantsAtDepth Q H).card : ℝ) *
            ∑ j ∈ Finset.range (H + N + 1),
              cubeBesovCircDepthSeminorm Q s 2 G j := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          have hadd := Finset.sum_range_add
            (fun j ↦ cubeBesovCircDepthSeminorm Q s 2 G j) H (N + 1)
          calc
            (∑ j ∈ Finset.range (N + 1),
                cubeBesovCircDepthSeminorm Q s 2 G (H + j)) ≤
                (∑ j ∈ Finset.range H,
                  cubeBesovCircDepthSeminorm Q s 2 G j) +
                  ∑ j ∈ Finset.range (N + 1),
                    cubeBesovCircDepthSeminorm Q s 2 G (H + j) :=
              le_add_of_nonneg_left
                (Finset.sum_nonneg fun j hj ↦
                  cubeBesovCircDepthSeminorm_nonneg Q s 2 G j)
            _ = ∑ j ∈ Finset.range (H + (N + 1)),
                cubeBesovCircDepthSeminorm Q s 2 G j := hadd.symm
            _ = ∑ j ∈ Finset.range (H + N + 1),
                cubeBesovCircDepthSeminorm Q s 2 G j := by
              simp [Nat.add_assoc]

/-- The scalar component of a raw affine pullback is bounded by the terminal
metric weak seminorm, with the finite descendant and metric distortions kept
explicit. -/
theorem ofReal_cubeBesovCircPartialNorm_child_rawPullback_le
    {q S : Mat d} (hq : q.PosDef) (hS : S.PosDef)
    {t : ℤ} {Q R : TriadicCube d} {H : ℕ} (hQ : Q = originCube d t)
    (hR : R ∈ descendantsAtDepth Q H) (N : ℕ)
    (F : Vec d → BlockVec d) (alpha : BlockCoord d)
    (hF₁ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S⁻¹ (F x).2)) :
    ENNReal.ofReal (cubeBesovCircPartialNorm R (1 / 2) 1 1 N
        (fun y ↦ toFullBlockVec (F (matVecMul q y)) alpha)) ≤
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth Q H).card : ℝ)) *
        ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) Q) *
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        ENNReal.ofReal (Real.sqrt (max
          (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
        adaptedWeakSeminorm q t (1 / 2) (fun x ↦
          ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)) := by
  subst Q
  let G : Vec d → BlockVec d := fun y ↦ F (matVecMul q y)
  have hchild := cubeBesovCircPartialNorm_child_le_sqrt_card_mul_parent
    hR (1 / 2) N (fun y ↦ toFullBlockVec (G y) alpha)
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have htransport := adaptedWeakSeminorm_affinePullback_le hq S⁻¹ S t (1 / 2)
    (fun x ↦ ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d))
    hF₁ hF₂
  have hleft : S⁻¹ * S = (1 : Mat d) := Matrix.nonsing_inv_mul S hSdet
  have hright : S * S⁻¹ = (1 : Mat d) := Matrix.mul_nonsing_inv S hSdet
  have htransport' : adaptedWeakSeminorm (1 : Mat d) t (1 / 2) G ≤
      ENNReal.ofReal (Real.sqrt (max
        (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
        adaptedWeakSeminorm q t (1 / 2) (fun x ↦
          ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)) := by
    simpa [G, matVecMul_mul, hleft, hright, matVecMul_one] using htransport
  apply (ENNReal.ofReal_le_ofReal hchild).trans
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [show ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t) H).card : ℝ)) *
        ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        ENNReal.ofReal (Real.sqrt (max
          (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
        adaptedWeakSeminorm q t (1 / 2) (fun x ↦
          ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)) =
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t) H).card : ℝ)) *
        (ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          ENNReal.ofReal (Real.sqrt (max
            (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
          adaptedWeakSeminorm q t (1 / 2) (fun x ↦
            ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d))) by
        ac_rfl]
  apply mul_le_mul_right
  cases alpha with
  | inl i =>
      have hcomp :=
        cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
          (originCube d t) (1 / 2) (fun y ↦ (G y).1) i (H + N)
      calc
        ENNReal.ofReal (cubeBesovCircPartialNorm (originCube d t) (1 / 2) 2 1
            (H + N) (fun y ↦ (G y).1 i)) ≤
            ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
              (originCube d t)) *
              ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
                (originCube d t) (1 / 2) (H + N) (fun y ↦ (G y).1)) := by
          rw [← ENNReal.ofReal_mul
            (cubeBesovScaleWeight_nonneg (-(1 / 2 : ℝ)) (originCube d t))]
          exact ENNReal.ofReal_le_ofReal hcomp
        _ ≤ ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
              (originCube d t)) *
            (ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
              adaptedWeakSeminorm (1 : Mat d) t (1 / 2) G) :=
          mul_le_mul_right
            (ofReal_partialSeminorm_fst_le_normalized_adaptedWeakSeminorm
              t (1 / 2) (H + N) G) _
        _ ≤ _ := by
          simpa only [mul_assoc] using
            (mul_le_mul_right (mul_le_mul_right htransport' _) _)
  | inr i =>
      have hcomp :=
        cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
          (originCube d t) (1 / 2) (fun y ↦ (G y).2) i (H + N)
      calc
        ENNReal.ofReal (cubeBesovCircPartialNorm (originCube d t) (1 / 2) 2 1
            (H + N) (fun y ↦ (G y).2 i)) ≤
            ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
              (originCube d t)) *
              ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
                (originCube d t) (1 / 2) (H + N) (fun y ↦ (G y).2)) := by
          rw [← ENNReal.ofReal_mul
            (cubeBesovScaleWeight_nonneg (-(1 / 2 : ℝ)) (originCube d t))]
          exact ENNReal.ofReal_le_ofReal hcomp
        _ ≤ ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
              (originCube d t)) *
            (ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
              adaptedWeakSeminorm (1 : Mat d) t (1 / 2) G) :=
          mul_le_mul_right
            (ofReal_partialSeminorm_snd_le_normalized_adaptedWeakSeminorm
              t (1 / 2) (H + N) G) _
        _ ≤ _ := by
          simpa only [mul_assoc] using
            (mul_le_mul_right (mul_le_mul_right htransport' _) _)

end

end HCPolySupport.HighContrast.Response
