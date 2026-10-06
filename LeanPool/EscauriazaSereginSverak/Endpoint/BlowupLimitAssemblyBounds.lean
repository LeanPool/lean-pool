/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyHypotheses

/-!
# Uniform bounds for the cutoff blow-up sequence

Slice integrability, the local gradient bound, and the pairing modulus of
`lem:compactness` of the CKN manuscript for the modified sequence of `prop:blowup-limit`, derived
from stagewise bounds of the original fields.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem blowupLimitAssembly_measurable_spatialGradientSq
    (g : ParabolicPoint → Vec3) (Dg : ParabolicPoint → Fin 3 → Vec3)
    (hDg : Measurable Dg) :
    Measurable (fun z : ParabolicPoint => spatialGradientSq g Dg z) := by
  unfold spatialGradientSq
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hDg)).pow_const 2

/-- A uniform compact slice bound and a finite local gradient energy make
the velocity slices and, for almost every time, the gradient slices
integrable on a ball. -/
theorem blowupLimitAssembly_slice_integrability
    (g : ParabolicPoint → Vec3) (Dg : ParabolicPoint → Fin 3 → Vec3)
    (hg : Measurable g) (hDg : Measurable Dg) {R : ℝ} (hR : 0 < R)
    (a b : ℝ)
    (hslice : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t,
      (∫⁻ x in closure (vec3Ball (0 : Vec3) R),
        ENNReal.ofReal (vec3EuclideanNorm (g (x, t))) ^ (2 : ℝ)) ≤ M)
    (G : ℝ≥0∞) (hG : G < ⊤)
    (hgrad : (∫⁻ t in Icc a b, ∫⁻ x in vec3Ball (0 : Vec3) R,
      ENNReal.ofReal (spatialGradientSq g Dg (x, t))) ≤ G) :
    (∀ t, ∀ i : Fin 3, IntegrableOn (fun x => g (x, t) i)
      (vec3Ball (0 : Vec3) R)) ∧
    (∀ᵐ t ∂(volume.restrict (Icc a b)), ∀ i j : Fin 3,
      IntegrableOn (fun x => Dg (x, t) i j) (vec3Ball (0 : Vec3) R)) := by
  set B : Set Vec3 := vec3Ball (0 : Vec3) R
  have hBvol : volume B < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure)
      (measure_closure_vec3Ball_lt_top hR)
  obtain ⟨M, hM, hMb⟩ := hslice
  constructor
  · intro t i
    have hmeas : Measurable (fun x : Vec3 => g (x, t) i) :=
      (measurable_pi_apply i).comp (hg.comp measurable_prodMk_right)
    apply blowupLimitAssembly_integrableOn_of_le_one_add hBvol
      hmeas.aestronglyMeasurable
      (F := fun x => ENNReal.ofReal (vec3EuclideanNorm (g (x, t))) ^ (2 : ℝ))
    · intro x
      exact blowupLimitAssembly_ofReal_abs_component_le (g (x, t)) i
    · calc
        (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (g (x, t))) ^ (2 : ℝ)) ≤
            ∫⁻ x in closure B,
              ENNReal.ofReal (vec3EuclideanNorm (g (x, t))) ^ (2 : ℝ) :=
          lintegral_mono_set subset_closure
        _ ≤ M := hMb t
        _ < ⊤ := hM
  · have hSGS := blowupLimitAssembly_measurable_spatialGradientSq g Dg hDg
    have hinner : Measurable (fun t : ℝ => ∫⁻ x in B,
        ENNReal.ofReal (spatialGradientSq g Dg (x, t))) := by
      have hjoint : Measurable (fun p : Vec3 × ℝ =>
          ENNReal.ofReal (spatialGradientSq g Dg p)) :=
        ENNReal.measurable_ofReal.comp hSGS
      exact hjoint.lintegral_prod_left'
    have hfin : ∀ᵐ t ∂(volume.restrict (Icc a b)),
        (∫⁻ x in B, ENNReal.ofReal (spatialGradientSq g Dg (x, t))) < ⊤ :=
      ae_lt_top' hinner.aemeasurable (ne_of_lt (lt_of_le_of_lt hgrad hG))
    filter_upwards [hfin] with t ht i j
    have hmeas : Measurable (fun x : Vec3 => Dg (x, t) i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (hDg.comp measurable_prodMk_right))
    exact blowupLimitAssembly_integrableOn_of_le_one_add hBvol
      hmeas.aestronglyMeasurable
      (F := fun x => ENNReal.ofReal (spatialGradientSq g Dg (x, t)))
      (fun x => blowupLimitAssembly_ofReal_abs_gradient_le g Dg (x, t) i j) ht

/-- The local gradient energy of one modified field is finite on every
compact set and every past time interval. -/
theorem blowupLimitAssemblyCutoff_gradient_bound_single
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (k : ℕ)
    (hf : ∀ n, Measurable (f n)) (hDf : ∀ n, Measurable (Df n))
    (hslice : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t,
      (∫⁻ x in closure (vec3Ball (0 : Vec3) ((k : ℝ) + 1)),
        ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ)) ≤ M)
    (G : ℝ≥0∞) (hG : G < ⊤)
    (hgrad : (∫⁻ t in Icc (-((k : ℝ) + 1)) 0,
      ∫⁻ x in vec3Ball (0 : Vec3) ((k : ℝ) + 1),
        ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) ≤ G)
    (C : Set Vec3) (a b : ℝ) (hb : b ≤ 0) :
    ∃ Bd : ℝ≥0∞, Bd < ⊤ ∧
      (∫⁻ t in Icc a b, ∫⁻ x in C,
        ENNReal.ofReal (spatialGradientSq (blowupLimitAssemblyCutoffField f ν k)
          (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t))) ≤ Bd := by
  obtain ⟨M, hM, hMb⟩ := hslice
  set B : Set Vec3 := vec3Ball (0 : Vec3) ((k : ℝ) + 1)
  set J : Set ℝ := Icc (-((k : ℝ) + 1)) 0
  have hBmeas : MeasurableSet B := (isOpen_vec3Ball _ _).measurableSet
  have hJmeas : MeasurableSet J := measurableSet_Icc
  let H : Vec3 → ℝ → ℝ≥0∞ := fun x t =>
    2 * ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t)) +
      2 * 64 ^ 2 * ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ)
  have hpoint : ∀ x t, t ≤ 0 → ENNReal.ofReal (spatialGradientSq
      (blowupLimitAssemblyCutoffField f ν k)
      (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t)) ≤
      J.indicator (fun t => B.indicator (fun x => H x t) x) t := by
    intro x t ht0
    by_cases hzero : x ∉ B ∨ t ≤ -((k : ℝ) + 1)
    · have hD := blowupLimitAssemblyCutoffGradient_eq_zero f Df ν k (x, t) hzero
      have hS : spatialGradientSq (blowupLimitAssemblyCutoffField f ν k)
          (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t) = 0 := by
        simp [spatialGradientSq, hD]
      rw [hS, ENNReal.ofReal_zero]
      exact zero_le
    · rw [not_or, not_not, not_le] at hzero
      obtain ⟨hxB, htk⟩ := hzero
      have htJ : t ∈ J := ⟨htk.le, ht0⟩
      rw [indicator_of_mem htJ, indicator_of_mem hxB]
      have hle := blowupLimitAssemblyCutoffGradient_sq_le f Df ν k (x, t)
      have hnn := vec3EuclideanNorm_nonneg (f (ν k) (x, t))
      have hsgs : 0 ≤ spatialGradientSq (f (ν k)) (Df (ν k)) (x, t) := by
        unfold spatialGradientSq
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      calc
        ENNReal.ofReal (spatialGradientSq (blowupLimitAssemblyCutoffField f ν k)
            (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t)) ≤
            ENNReal.ofReal (2 * spatialGradientSq (f (ν k)) (Df (ν k)) (x, t) +
              2 * 64 ^ 2 * vec3EuclideanNorm (f (ν k) (x, t)) ^ 2) :=
          ENNReal.ofReal_le_ofReal hle
        _ = H x t := by
          simp only [H]
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
          norm_num
  have hinner : ∀ t ∈ Icc a b,
      (∫⁻ x in C, ENNReal.ofReal (spatialGradientSq
        (blowupLimitAssemblyCutoffField f ν k)
        (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t))) ≤
      J.indicator (fun t => ∫⁻ x in B, H x t) t := by
    intro t ht
    have ht0 : t ≤ 0 := ht.2.trans hb
    calc
      (∫⁻ x in C, ENNReal.ofReal (spatialGradientSq
          (blowupLimitAssemblyCutoffField f ν k)
          (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t))) ≤
          ∫⁻ x in C, J.indicator (fun t => B.indicator (fun x => H x t) x) t :=
        lintegral_mono fun x => hpoint x t ht0
      _ ≤ J.indicator (fun t => ∫⁻ x in B, H x t) t := by
        by_cases htJ : t ∈ J
        · simp only [indicator_of_mem htJ]
          calc
            (∫⁻ x in C, B.indicator (fun x => H x t) x) ≤
                ∫⁻ x, B.indicator (fun x => H x t) x :=
              setLIntegral_le_lintegral _ _
            _ = ∫⁻ x in B, H x t := lintegral_indicator hBmeas _
        · simp [indicator_of_notMem htJ]
  have hmeasX : Measurable (fun p : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) p)) :=
    ENNReal.measurable_ofReal.comp
      (blowupLimitAssembly_measurable_spatialGradientSq _ _ (hDf (ν k)))
  have hmeasY : Measurable (fun p : Vec3 × ℝ =>
      ENNReal.ofReal (vec3EuclideanNorm (f (ν k) p)) ^ (2 : ℝ)) :=
    (ENNReal.measurable_ofReal.comp
      (continuous_vec3EuclideanNorm.measurable.comp (hf (ν k)))).pow_const _
  have hsplit : ∀ t, (∫⁻ x in B, H x t) =
      2 * (∫⁻ x in B, ENNReal.ofReal
        (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) +
      2 * 64 ^ 2 * ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ) := by
    intro t
    have hm1 : Measurable (fun x : Vec3 => 2 * ENNReal.ofReal
        (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) :=
      (hmeasX.comp measurable_prodMk_right).const_mul 2
    simp only [H]
    rw [lintegral_add_left hm1,
      lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  have hI1 : Measurable (fun t : ℝ => ∫⁻ x in B, ENNReal.ofReal
      (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) :=
    hmeasX.lintegral_prod_left'
  have hYbound : ∀ t, (∫⁻ x in B,
      ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ)) ≤ M :=
    fun t => (lintegral_mono_set subset_closure).trans (hMb t)
  refine ⟨2 * G + 2 * 64 ^ 2 * (M * volume J), ?_, ?_⟩
  · have hJ : volume J < ⊤ := by
      simp only [J, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have h64 : (2 : ℝ≥0∞) * 64 ^ 2 < ⊤ := by norm_num
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hG,
      ENNReal.mul_lt_top h64 (ENNReal.mul_lt_top hM hJ)⟩
  calc
    (∫⁻ t in Icc a b, ∫⁻ x in C,
        ENNReal.ofReal (spatialGradientSq (blowupLimitAssemblyCutoffField f ν k)
          (blowupLimitAssemblyCutoffGradient f Df ν k) (x, t))) ≤
        ∫⁻ t in Icc a b, J.indicator (fun t => ∫⁻ x in B, H x t) t :=
      setLIntegral_mono' measurableSet_Icc hinner
    _ ≤ ∫⁻ t, J.indicator (fun t => ∫⁻ x in B, H x t) t :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in J, ∫⁻ x in B, H x t := lintegral_indicator hJmeas _
    _ = 2 * (∫⁻ t in J, ∫⁻ x in B, ENNReal.ofReal
          (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) +
        2 * 64 ^ 2 * ∫⁻ t in J, ∫⁻ x in B,
          ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ) := by
      have hm2 : Measurable (fun t : ℝ => 2 * ∫⁻ x in B, ENNReal.ofReal
          (spatialGradientSq (f (ν k)) (Df (ν k)) (x, t))) := hI1.const_mul 2
      simp only [hsplit]
      rw [lintegral_add_left hm2,
        lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * G + 2 * 64 ^ 2 * (M * volume J) := by
      gcongr
      calc
        (∫⁻ t in J, ∫⁻ x in B,
            ENNReal.ofReal (vec3EuclideanNorm (f (ν k) (x, t))) ^ (2 : ℝ)) ≤
            ∫⁻ _t in J, M := lintegral_mono hYbound
        _ = M * volume J := by
          rw [lintegral_const, Measure.restrict_apply_univ]

/-- The pairing of a modified field with a test factors through the time
ramp and the spatially cut-off test. -/
theorem blowupLimitAssemblyCutoffField_pairing
    (f : ℕ → ParabolicPoint → Vec3) (ν : ℕ → ℕ) (k : ℕ)
    (w : Vec3 → L2Vec3) (t : ℝ) :
    (∫ x : Vec3, ∑ i : Fin 3,
        blowupLimitAssemblyCutoffField f ν k (x, t) i * w x i) =
      blowupLimitAssemblyTimeRamp k t *
        ∫ x : Vec3, ∑ i : Fin 3, f (ν k) (x, t) i *
          (blowupLimitAssemblySpaceCutoff k x • w x) i := by
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [blowupLimitAssemblyCutoffField, Pi.smul_apply, smul_eq_mul,
    PiLp.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One modified field has a pairing modulus on every past time interval,
from the modulus of the original field at its stage. -/
theorem blowupLimitAssemblyCutoff_modulus_single
    (f : ℕ → ParabolicPoint → Vec3) (ν : ℕ → ℕ) (k Nk : ℕ)
    (hNk : Nk ≤ ν k)
    (hmod : ∀ C : Set Vec3, IsCompact C →
      C ⊆ vec3Ball (0 : Vec3) ((k : ℝ) + 1) →
      ∀ a b : ℝ, Icc a b ⊆ Icc (-((k : ℝ) + 1)) 0 →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n, Nk ≤ n → ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, f n (x, t) i * w x i) -
            (∫ x : Vec3, ∑ i : Fin 3, f n (x, s) i * w x i)| ≤
            A * dist t s + B * (dist t s) ^ θ)
    (a b : ℝ) (hb : b ≤ 0) (w : Vec3 → L2Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
        |(∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitAssemblyCutoffField f ν k (x, t) i * w x i) -
          (∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitAssemblyCutoffField f ν k (x, s) i * w x i)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
  by_cases hab : a ≤ b
  swap
  · refine ⟨0, 0, 1, le_rfl, le_rfl, one_pos, ?_⟩
    intro s t hs _
    exact absurd (hs.1.trans hs.2) hab
  set κ : ℝ := -((k : ℝ) + 1)
  have hκ : κ ≤ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [κ]
    linarith only [this]
  let c : ℝ → ℝ := fun t => max t κ
  set a' : ℝ := c a
  set b' : ℝ := c b
  have hab' : a' ≤ b' := max_le_max hab le_rfl
  have hsub : Icc a' b' ⊆ Icc κ 0 := by
    intro t ht
    exact ⟨(le_max_right a κ).trans ht.1, ht.2.trans (max_le hb hκ)⟩
  have hcmem : ∀ t ∈ Icc a b, c t ∈ Icc a' b' := fun t ht =>
    ⟨max_le_max ht.1 le_rfl, max_le_max ht.2 le_rfl⟩
  have hcdist : ∀ s t, dist (c t) (c s) ≤ dist t s := by
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_max_sub_max_le_abs _ _ _
  set S : Vec3 → ℝ := blowupLimitAssemblySpaceCutoff k
  let w' : Vec3 → L2Vec3 := fun x => S x • w x
  have hw' : ContDiff ℝ (⊤ : ℕ∞) w' :=
    (blowupLimitAssemblySpaceCutoff_contDiff k).smul hw
  have hSc : HasCompactSupport S := blowupLimitAssemblySpaceCutoff_hasCompactSupport k
  have hw'c : HasCompactSupport w' := hSc.smul_right
  have hw'supp : tsupport w' ⊆ tsupport S := tsupport_smul_subset_left _ _
  obtain ⟨A', B', θ', hA', hB', hθ', h'⟩ := hmod (tsupport S) hSc.isCompact
    (blowupLimitAssemblySpaceCutoff_tsupport_subset k) a' b' hsub w' hw' hw'c
    hw'supp
  let X : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, f (ν k) (x, t) i * w' x i
  have hX : ∀ s t, s ∈ Icc a' b' → t ∈ Icc a' b' →
      |X t - X s| ≤ A' * dist t s + B' * (dist t s) ^ θ' :=
    fun s t hs ht => h' (ν k) hNk s t hs ht
  set T : ℝ → ℝ := blowupLimitAssemblyTimeRamp k
  have hg : ∀ t, (∫ x : Vec3, ∑ i : Fin 3,
      blowupLimitAssemblyCutoffField f ν k (x, t) i * w x i) = T (c t) * X (c t) := by
    intro t
    rw [blowupLimitAssemblyCutoffField_pairing]
    rcases le_total t κ with htk | htk
    · have hct : c t = κ := max_eq_right htk
      rw [hct]
      simp only [T]
      rw [blowupLimitAssemblyTimeRamp_eq_zero htk,
        blowupLimitAssemblyTimeRamp_eq_zero le_rfl, zero_mul, zero_mul]
    · have hct : c t = t := max_eq_left htk
      rw [hct]
  set L : ℝ := b' - a'
  have hL : 0 ≤ L := sub_nonneg.mpr hab'
  set K : ℝ := |X b'| + A' * L + B' * L ^ θ'
  have hK : 0 ≤ K := by
    have := Real.rpow_nonneg hL θ'
    positivity
  have hb'mem : b' ∈ Icc a' b' := ⟨hab', le_rfl⟩
  have hXbound : ∀ s ∈ Icc a' b', |X s| ≤ K := by
    intro s hs
    have hdist : dist s b' ≤ L := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith only [hs.1, hs.2]
    have hdiff := hX b' s hb'mem hs
    have hpow : (dist s b') ^ θ' ≤ L ^ θ' :=
      Real.rpow_le_rpow dist_nonneg hdist hθ'.le
    calc
      |X s| = |X b' + (X s - X b')| := by ring_nf
      _ ≤ |X b'| + |X s - X b'| := abs_add_le _ _
      _ ≤ |X b'| + (A' * dist s b' + B' * (dist s b') ^ θ') := by
        linarith only [hdiff]
      _ ≤ K := by
        have h1 : A' * dist s b' ≤ A' * L := mul_le_mul_of_nonneg_left hdist hA'
        have h2 : B' * (dist s b') ^ θ' ≤ B' * L ^ θ' :=
          mul_le_mul_of_nonneg_left hpow hB'
        simp only [K]
        linarith only [h1, h2]
  refine ⟨K + A', B', θ', add_nonneg hK hA', hB', hθ', ?_⟩
  intro s t hs ht
  rw [hg t, hg s]
  have hs' := hcmem s hs
  have ht' := hcmem t ht
  have hd := hcdist s t
  have hd0 : 0 ≤ dist (c t) (c s) := dist_nonneg
  have hTlip := blowupLimitAssemblyTimeRamp_lipschitz k (c s) (c t)
  have hT0 := blowupLimitAssemblyTimeRamp_nonneg k (c s)
  have hT1 := blowupLimitAssemblyTimeRamp_le_one k (c s)
  have hXt := hXbound (c t) ht'
  have hXdiff := hX (c s) (c t) hs' ht'
  have hpow : (dist (c t) (c s)) ^ θ' ≤ (dist t s) ^ θ' :=
    Real.rpow_le_rpow hd0 hd hθ'.le
  calc
    |T (c t) * X (c t) - T (c s) * X (c s)| =
        |(T (c t) - T (c s)) * X (c t) + T (c s) * (X (c t) - X (c s))| := by
      ring_nf
    _ ≤ |T (c t) - T (c s)| * |X (c t)| + T (c s) * |X (c t) - X (c s)| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hT0]
    _ ≤ dist (c t) (c s) * K + 1 * (A' * dist (c t) (c s) +
          B' * (dist (c t) (c s)) ^ θ') := by
      gcongr
    _ ≤ (K + A') * dist t s + B' * (dist t s) ^ θ' := by
      have h1 : dist (c t) (c s) * K ≤ dist t s * K :=
        mul_le_mul_of_nonneg_right hd hK
      have h2 : A' * dist (c t) (c s) ≤ A' * dist t s :=
        mul_le_mul_of_nonneg_left hd hA'
      have h3 : B' * (dist (c t) (c s)) ^ θ' ≤ B' * (dist t s) ^ θ' :=
        mul_le_mul_of_nonneg_left hpow hB'
      nlinarith only [h1, h2, h3]

/-- The modified sequence has one pairing modulus for all indices on every
compact set and past time interval, as required by `lem:compactness` of the CKN manuscript. -/
theorem blowupLimitAssemblyCutoff_modulus
    (f : ℕ → ParabolicPoint → Vec3) (N : ℕ → ℕ)
    (hmod : ∀ m : ℕ, ∀ C : Set Vec3, IsCompact C →
      C ⊆ vec3Ball (0 : Vec3) ((m : ℝ) + 1) →
      ∀ a b : ℝ, Icc a b ⊆ Icc (-((m : ℝ) + 1)) 0 →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n, N m ≤ n → ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, f n (x, t) i * w x i) -
            (∫ x : Vec3, ∑ i : Fin 3, f n (x, s) i * w x i)| ≤
            A * dist t s + B * (dist t s) ^ θ)
    (C : Set Vec3) (hC : IsCompact C) (a b : ℝ) (hab : Icc a b ⊆ Iio 0)
    (w : Vec3 → L2Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwC : tsupport w ⊆ C) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ k s t, s ∈ Icc a b → t ∈ Icc a b →
        |(∫ x : Vec3, ∑ i : Fin 3, blowupLimitAssemblyCutoffField f
            (blowupLimitAssemblyIndex N) k (x, t) i * w x i) -
          (∫ x : Vec3, ∑ i : Fin 3, blowupLimitAssemblyCutoffField f
            (blowupLimitAssemblyIndex N) k (x, s) i * w x i)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
  set ν := blowupLimitAssemblyIndex N
  by_cases hab' : a ≤ b
  swap
  · refine ⟨0, 0, 1, le_rfl, le_rfl, one_pos, ?_⟩
    intro k s t hs _
    exact absurd (hs.1.trans hs.2) hab'
  have hb : b < 0 := hab ⟨hab', le_rfl⟩
  obtain ⟨ρ, hρ⟩ := hC.exists_bound_of_continuousOn
    continuous_vec3EuclideanNorm.continuousOn
  obtain ⟨j, hj⟩ := exists_nat_gt (max ρ (-a))
  have hjρ : ρ < j := (le_max_left _ _).trans_lt hj
  have hja : -a < j := (le_max_right _ _).trans_lt hj
  have hCj : ∀ x ∈ C, vec3EuclideanNorm x < j := by
    intro x hx
    have h := hρ x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg x)] at h
    exact h.trans_lt hjρ
  let g : ℕ → ℝ → ℝ := fun k t => ∫ x : Vec3, ∑ i : Fin 3,
    blowupLimitAssemblyCutoffField f ν k (x, t) i * w x i
  have htail : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ k s t, j ≤ k → s ∈ Icc a b → t ∈ Icc a b →
        |g k t - g k s| ≤ A * dist t s + B * (dist t s) ^ θ := by
    have hCsub : C ⊆ vec3Ball (0 : Vec3) ((j : ℝ) + 1) := by
      intro x hx
      rw [mem_vec3Ball, sub_zero]
      linarith only [hCj x hx]
    have hIsub : Icc a b ⊆ Icc (-((j : ℝ) + 1)) 0 := by
      intro t ht
      exact ⟨by linarith only [ht.1, hja], ht.2.trans hb.le⟩
    obtain ⟨A, B, θ, hA, hB, hθ, h⟩ := hmod j C hC hCsub a b hIsub w hw hwc hwC
    refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
    intro k s t hjk hs ht
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have hpair : ∀ τ ∈ Icc a b, g k τ =
        ∫ x : Vec3, ∑ i : Fin 3, f (ν k) (x, τ) i * w x i := by
      intro τ hτ
      simp only [g]
      congr 1
      funext x
      by_cases hx : x ∈ C
      · have hxk : (x, τ).1 ∈ vec3Ball (0 : Vec3) (k : ℝ) := by
          rw [mem_vec3Ball, sub_zero]
          exact (hCj x hx).trans_le hjk'
        have hτk : -(k : ℝ) ≤ (x, τ).2 := by
          change -(k : ℝ) ≤ τ
          linarith only [hτ.1, hja, hjk']
        rw [(blowupLimitAssemblyCutoff_eq_of_mem f (fun _ _ _ => 0) ν hxk hτk).1]
      · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (hwC h))
        simp [hw0]
    rw [hpair t ht, hpair s hs]
    exact h (ν k) (le_blowupLimitAssemblyIndex N hjk) s t hs ht
  have hsingle : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ k s t, k ≤ j → s ∈ Icc a b → t ∈ Icc a b →
        |g k t - g k s| ≤ A * dist t s + B * (dist t s) ^ θ :=
    blowupLimitAssembly_modulus_le g a b (fun k =>
      blowupLimitAssemblyCutoff_modulus_single f ν k (N k)
        (le_blowupLimitAssemblyIndex N le_rfl) (hmod k) a b hb.le w hw) j
  obtain ⟨A, B, θ, hA, hB, hθ, h⟩ :=
    blowupLimitAssembly_modulus_or g a b (fun k => k ≤ j) (fun k => j ≤ k)
      hsingle htail
  exact ⟨A, B, θ, hA, hB, hθ, fun k s t hs ht => h k s t (le_total k j) hs ht⟩

end ESS

end
