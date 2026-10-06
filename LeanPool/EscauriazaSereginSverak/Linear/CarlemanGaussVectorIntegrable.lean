/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussIntegrated

/-!
# Integrability of the Gaussian vector energy

Compact support inside the positive-time cylinder makes the original
weighted energy integrable despite the singular expression at time zero.
-/

public section


open CKN CKN.Foundation.Parabolic Set MeasureTheory

noncomputable section

namespace ESS

local instance gaussVectorIntegrableMeasureSpace : MeasureSpace ParabolicPoint :=
  Measure.prod.measureSpace

local instance gaussVectorIntegrableNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance gaussVectorIntegrableNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The squared norm of a smooth compactly supported vector field is smooth
and supported where the field is supported. -/
theorem gauss_vector_norm_sq_smooth_support
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) ∧
    HasCompactSupport
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) ∧
    tsupport (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) ⊆
      tsupport w := by
  let B : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by
    have heq : B = fun z : ParabolicPoint => ∑ i : Fin 3, (w z i) ^ 2 := by
      funext z
      exact gauss_vec3EuclideanNorm_sq (w z)
    rw [heq]
    exact ContDiff.sum (fun i _ => (by fun_prop :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : ParabolicPoint => w z i)).pow 2)
  have hBs : tsupport B ⊆ tsupport w := by
    apply closure_minimal _ (isClosed_tsupport w)
    intro z hz
    by_contra hnot
    have hw0 : w z = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact hz (by simp [B, hw0, vec3EuclideanNorm_zero])
  exact ⟨hB, hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) hBs, hBs⟩

/-- The squared spatial gradient of a smooth compactly supported vector
field has the same support property. -/
theorem gauss_vector_gradient_sq_smooth_support
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => spatialGradientSq w (spatialGradient w) z) ∧
    HasCompactSupport
      (fun z : ParabolicPoint => spatialGradientSq w (spatialGradient w) z) ∧
    tsupport (fun z : ParabolicPoint =>
      spatialGradientSq w (spatialGradient w) z) ⊆ tsupport w := by
  let G : ParabolicPoint → ℝ := fun z => spatialGradientSq w (spatialGradient w) z
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    have heq : G = fun z : ParabolicPoint =>
        ∑ i : Fin 3, ∑ j : Fin 3, spatialPartial (fun y => w y i) j z ^ 2 := by
      funext z
      unfold G spatialGradientSq spatialGradient
      rfl
    rw [heq]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun y : ParabolicPoint => w y i) := by
      fun_prop
    exact (CKN.spatialPartial_contDiff hwi j).pow 2
  have hGs : tsupport G ⊆ tsupport w := by
    apply closure_minimal _ (isClosed_tsupport w)
    intro z hz
    by_contra hnot
    have hgrad : G z = 0 := by
      unfold G spatialGradientSq spatialGradient
      simp [fun i j => (gauss_component_zero_outside w z hnot i).2.2 j |>.1]
    exact hz (by simp [hgrad])
  exact ⟨hG, hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) hGs, hGs⟩

/-- The original weighted energy in `prop:carleman-gauss` is integrable. -/
theorem gauss_original_energy_integrable (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ =>
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
            spatialGradientSq w (spatialGradient w) z)) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have ht : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2) U := by fun_prop
  have htne : ∀ z ∈ U, (z.2 : ℝ) ≠ 0 := by
    intro z hz
    exact ne_of_gt hz.2.1
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => a / z.2) U :=
    contDiffOn_const.div ht htne
  have hcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2)) U := by
    have hwgt : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint =>
          gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) U :=
      gauss_original_weight_contDiffOn a
    exact hwgt.mul hdiv
  obtain ⟨hB, hBc, hBs⟩ := gauss_vector_norm_sq_smooth_support w hw hwc
  obtain ⟨hG, hGc, hGs⟩ := gauss_vector_gradient_sq_smooth_support w hw hwc
  have hM : Integrable (fun z : Vec3 × ℝ =>
      ((gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2)) * vec3EuclideanNorm (w z) ^ 2) volume :=
    integrable_mul_of_tsupport hU hcoeff hB hBc (hBs.trans hwU)
  have hGrad : Integrable (fun z : Vec3 × ℝ =>
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        spatialGradientSq w (spatialGradient w) z) volume :=
    integrable_mul_of_tsupport hU (gauss_original_weight_contDiffOn a)
      hG hGc (hGs.trans hwU)
  have heq : (fun z : Vec3 × ℝ =>
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
            spatialGradientSq w (spatialGradient w) z)) =
      fun z =>
        ((gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2)) * vec3EuclideanNorm (w z) ^ 2 +
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          spatialGradientSq w (spatialGradient w) z := by
    funext z
    ring
  rw [heq]
  exact hM.add hGrad

/-- Each exponentially conjugated component is smooth, compactly supported,
and supported inside the positive-time cylinder. -/
theorem gauss_conjugated_component_properties (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => Real.exp (gaussCarlemanPhase q z) * w z i) ∧
    HasCompactSupport
      (fun z => Real.exp (gaussCarlemanPhase q z) * w z i) ∧
    tsupport (fun z => Real.exp (gaussCarlemanPhase q z) * w z i) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2) := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun z : ParabolicPoint => w z i) := by
    fun_prop
  have hsuppWi : tsupport (fun z : ParabolicPoint => w z i) ⊆ tsupport w :=
    tsupport_comp_subset (g := fun x : Vec3 => x i) rfl w
  have hwic : HasCompactSupport (fun z : ParabolicPoint => w z i) :=
    hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) hsuppWi
  exact ⟨contDiff_exp_mul_of_tsupport hU hφ hwi (hsuppWi.trans hwU),
    hasCompactSupport_exp_mul _ _ hwic,
    (tsupport_exp_mul_subset _ _).trans (hsuppWi.trans hwU)⟩

/-- The vector expression produced by the Gaussian gradient comparison is
integrable, and its integral splits into scalar component energies. -/
theorem gauss_vector_upper_integral_eq_sum (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z : Vec3 × ℝ,
      q * z.2 *
          vec3EuclideanNorm
            (fun i => Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 +
        2 * z.2 ^ 2 *
          ((∑ i : Fin 3, scalarGradSq
              (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z) +
            vec3EuclideanNorm
              (fun i => Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
              scalarGradSq (gaussCarlemanPhase q) z) ∂volume) =
      ∑ i : Fin 3,
        (q * (∫ z : Vec3 × ℝ, z.2 *
            (Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 ∂volume) +
          2 * ((∫ z : Vec3 × ℝ, z.2 ^ 2 * scalarGradSq
              (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ∂volume) +
            (∫ z : Vec3 × ℝ, z.2 ^ 2 *
              (Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
              scalarGradSq (gaussCarlemanPhase q) z ∂volume))) := by
  let v (i : Fin 3) : ParabolicPoint → ℝ := fun z =>
    Real.exp (gaussCarlemanPhase q z) * w z i
  let φ := gaussCarlemanPhase q
  have hM (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => z.2 * v i z ^ 2) volume := by
    obtain ⟨hvi, hvic, _⟩ := gauss_conjugated_component_properties q w hw hwc hwU i
    have hraw := gauss_mass_integrable 3 (v i) hvi hvic
    convert hraw using 1
    funext z
    ring
  have hG (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => z.2 ^ 2 * scalarGradSq (v i) z) volume := by
    obtain ⟨hvi, hvic, _⟩ := gauss_conjugated_component_properties q w hw hwc hwU i
    exact gauss_scalar_gradient_integrable (v i) hvi hvic
  have hH (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z) volume := by
    obtain ⟨hvi, hvic, hviU⟩ :=
      gauss_conjugated_component_properties q w hw hwc hwU i
    exact gauss_phase_gradient_mass_integrable q (v i) hvi hvic hviU
  have hFi (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      q * z.2 * v i z ^ 2 +
        2 * (z.2 ^ 2 * scalarGradSq (v i) z +
          z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z)) volume := by
    convert ((hM i).const_mul q).add (((hG i).add (hH i)).const_mul 2) using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  have hpoint (z : Vec3 × ℝ) :
      q * z.2 * vec3EuclideanNorm (fun i => v i z) ^ 2 +
        2 * z.2 ^ 2 *
          ((∑ i : Fin 3, scalarGradSq (v i) z) +
            vec3EuclideanNorm (fun i => v i z) ^ 2 * scalarGradSq φ z) =
        ∑ i : Fin 3, (q * z.2 * v i z ^ 2 +
          2 * (z.2 ^ 2 * scalarGradSq (v i) z +
            z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z)) := by
    rw [gauss_vec3EuclideanNorm_sq]
    calc
      _ = q * z.2 * (∑ i : Fin 3, v i z ^ 2) +
          2 * z.2 ^ 2 *
            (∑ i : Fin 3,
              (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z)) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = (∑ i : Fin 3, q * z.2 * v i z ^ 2) +
          ∑ i : Fin 3,
            (2 * z.2 ^ 2) *
              (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z) := by
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i : Fin 3,
          (q * z.2 * v i z ^ 2 +
            (2 * z.2 ^ 2) *
              (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z)) := by
            rw [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    _ = ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, (q * z.2 * v i z ^ 2 +
          2 * (z.2 ^ 2 * scalarGradSq (v i) z +
            z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact hpoint z
    _ = ∑ i : Fin 3, ∫ z : Vec3 × ℝ,
        (q * z.2 * v i z ^ 2 +
          2 * (z.2 ^ 2 * scalarGradSq (v i) z +
            z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z)) ∂volume := by
          exact integral_finsetSum _ (fun i _ => hFi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change (∫ z : ParabolicPoint,
          q * z.2 * v i z ^ 2 +
            2 * (z.2 ^ 2 * scalarGradSq (v i) z +
              z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z) ∂volume) =
          q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) +
            2 * ((∫ z : ParabolicPoint,
              z.2 ^ 2 * scalarGradSq (v i) z ∂volume) +
              (∫ z : ParabolicPoint,
                z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z ∂volume))
      calc
        _ = ∫ z : ParabolicPoint,
            q * (z.2 * v i z ^ 2) +
              2 * (z.2 ^ 2 * scalarGradSq (v i) z +
                z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with z
              ring
        _ = (∫ z : ParabolicPoint, q * (z.2 * v i z ^ 2) ∂volume) +
            (∫ z : ParabolicPoint,
              2 * (z.2 ^ 2 * scalarGradSq (v i) z +
                z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z) ∂volume) := by
              exact integral_add ((hM i).const_mul q)
                (((hG i).add (hH i)).const_mul 2)
        _ = _ := by
          have hsum :
              (∫ z : ParabolicPoint,
                z.2 ^ 2 * scalarGradSq (v i) z +
                  z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z ∂volume) =
                (∫ z : ParabolicPoint,
                  z.2 ^ 2 * scalarGradSq (v i) z ∂volume) +
                  (∫ z : ParabolicPoint,
                    z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z ∂volume) := by
            exact integral_add (hG i) (hH i)
          calc
            _ = q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) +
                2 * (∫ z : ParabolicPoint,
                  z.2 ^ 2 * scalarGradSq (v i) z +
                    z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z ∂volume) := by
                  rw [integral_const_mul, integral_const_mul]
            _ = _ := congrArg (fun x : ℝ =>
              q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) + 2 * x) hsum

/-- The vector energy after exponential conjugation is integrable. -/
theorem gauss_vector_upper_integrable (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ =>
      q * z.2 *
          vec3EuclideanNorm
            (fun i => Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 +
        2 * z.2 ^ 2 *
          ((∑ i : Fin 3, scalarGradSq
              (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z) +
            vec3EuclideanNorm
              (fun i => Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
              scalarGradSq (gaussCarlemanPhase q) z)) volume := by
  let v (i : Fin 3) : ParabolicPoint → ℝ := fun z =>
    Real.exp (gaussCarlemanPhase q z) * w z i
  let φ := gaussCarlemanPhase q
  have hcomp (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      q * z.2 * v i z ^ 2 +
        2 * (z.2 ^ 2 * scalarGradSq (v i) z +
          z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z)) volume := by
    obtain ⟨hvi, hvic, hviU⟩ :=
      gauss_conjugated_component_properties q w hw hwc hwU i
    have hM : Integrable (fun z : Vec3 × ℝ => z.2 * v i z ^ 2) volume := by
      convert gauss_mass_integrable 3 (v i) hvi hvic using 1
      funext z
      ring
    have hG := gauss_scalar_gradient_integrable (v i) hvi hvic
    have hH := gauss_phase_gradient_mass_integrable q (v i) hvi hvic hviU
    convert ((hM.const_mul q).add ((hG.add hH).const_mul 2)) using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  have hsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3,
        (q * z.2 * v i z ^ 2 +
          2 * (z.2 ^ 2 * scalarGradSq (v i) z +
            z.2 ^ 2 * v i z ^ 2 * scalarGradSq φ z))) volume :=
    integrable_finsetSum _ (fun i _ => hcomp i)
  convert hsum using 1
  funext z
  rw [gauss_vec3EuclideanNorm_sq]
  calc
    _ = q * z.2 * (∑ i : Fin 3, v i z ^ 2) +
        2 * z.2 ^ 2 *
          (∑ i : Fin 3,
            (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z)) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ i : Fin 3, q * z.2 * v i z ^ 2) +
        ∑ i : Fin 3,
          (2 * z.2 ^ 2) *
            (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i : Fin 3,
        (q * z.2 * v i z ^ 2 +
          (2 * z.2 ^ 2) *
            (scalarGradSq (v i) z + v i z ^ 2 * scalarGradSq φ z)) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The conjugated vector heat integral splits into the three scalar heat
integrals. -/
theorem gauss_vector_conjugated_heat_integral_eq_sum (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z : ParabolicPoint,
      z.2 ^ 2 * (∑ i : Fin 3,
        carlemanConj (gaussCarlemanPhase q)
          (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) ∂volume) =
      ∑ i : Fin 3, ∫ z : ParabolicPoint,
        z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q)
          (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2 ∂volume := by
  have hPi (i : Fin 3) : Integrable (fun z : ParabolicPoint =>
      z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q)
        (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) volume :=
    gauss_component_conjugated_heat_integrable q w hw hwc hwU i
  calc
    _ = ∫ z : ParabolicPoint,
        ∑ i : Fin 3, z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q)
          (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2 ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [Finset.mul_sum]
    _ = _ := integral_finsetSum _ (fun i _ => hPi i)

end ESS
