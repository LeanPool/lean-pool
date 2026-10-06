/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongCompactness
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Trace
public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# All-time spatial slices of the local strong limit

The regularized H¹ traces and weak slice convergence provide spatial H¹
representatives for the limit at each positive time.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The `L²` norm of a vector-valued function is at most the sum of the `L²` norms of its
coordinates. -/
theorem lps_eLpNorm_vec3_le_sum_coordinates
    {f : Vec3 → Vec3} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 volume := by
  let S : Vec3 → ℝ := fun x => ∑ i : Fin 3, |f x i|
  have hSnonneg (x : Vec3) : 0 ≤ S x :=
    Finset.sum_nonneg fun i _ => abs_nonneg (f x i)
  have hpoint (x : Vec3) : ‖f x‖ ≤ S x := by
    apply (pi_norm_le_iff_of_nonneg (hSnonneg x)).2
    intro i
    dsimp [S]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (f x j))
      (Finset.mem_univ i)
  have hvector : eLpNorm f 2 volume ≤ eLpNorm S 2 volume :=
    eLpNorm_mono_ae_real hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hsum : eLpNorm S 2 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |f x i|) 2 volume := by
    dsimp [S]
    exact eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
      (f := fun i x => |f x i|) (s := Finset.univ) (by norm_num)
  have hcoord (i : Fin 3) :
      eLpNorm (fun x => |f x i|) 2 volume =
        eLpNorm (fun x => f x i) 2 volume := by
    let hi : MemLp (fun x => f x i) 2 volume := (memLp_pi_iff.mp hf) i
    apply eLpNorm_congr_norm_ae
    · exact hi.abs.aestronglyMeasurable
    · exact hi.aestronglyMeasurable
    · filter_upwards [] with x
      simp
  calc
    eLpNorm f 2 volume ≤ eLpNorm S 2 volume := hvector
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |f x i|) 2 volume := hsum
    _ = _ := by simp_rw [hcoord]

/-- The `L²` norm of a matrix-valued function is at most the sum of the `L²` norms of its
coordinates. -/
theorem lps_eLpNorm_matrix_le_sum_coordinates
    {f : Vec3 → Fin 3 → Vec3} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (fun x => f x i j) 2 volume := by
  let S : Vec3 → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, |f x i j|
  have hSnonneg (x : Vec3) : 0 ≤ S x :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (f x i j)
  have hpoint (x : Vec3) : ‖f x‖ ≤ S x := by
    apply (pi_norm_le_iff_of_nonneg (hSnonneg x)).2
    intro i
    have hrowNonneg : 0 ≤ ∑ j : Fin 3, |f x i j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg (f x i j)
    have hrow : ‖f x i‖ ≤ ∑ j : Fin 3, |f x i j| := by
      apply (pi_norm_le_iff_of_nonneg hrowNonneg).2
      intro j
      exact Finset.single_le_sum (fun k _ => abs_nonneg (f x i k))
        (Finset.mem_univ j)
    calc
      ‖f x i‖ ≤ ∑ j : Fin 3, |f x i j| := hrow
      _ ≤ S x := by
        dsimp [S]
        exact Finset.single_le_sum
          (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (f x k j))
          (Finset.mem_univ i)
  have hvector : eLpNorm f 2 volume ≤ eLpNorm S 2 volume :=
    eLpNorm_mono_ae_real hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hsum : eLpNorm S 2 volume ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (fun x => |f x i j|) 2 volume := by
    dsimp [S]
    calc
      eLpNorm (fun x => ∑ i : Fin 3, ∑ j : Fin 3, |f x i j|) 2 volume ≤
          ∑ i : Fin 3, eLpNorm (fun x => ∑ j : Fin 3, |f x i j|) 2 volume :=
        eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
          (f := fun i x => ∑ j : Fin 3, |f x i j|)
          (s := Finset.univ) (by norm_num)
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
          (f := fun j x => |f x i j|) (s := Finset.univ) (by norm_num)
  have hcoord (i j : Fin 3) :
      eLpNorm (fun x => |f x i j|) 2 volume =
        eLpNorm (fun x => f x i j) 2 volume := by
    let hi : MemLp (fun x => f x i) 2 volume := (memLp_pi_iff.mp hf) i
    let hij : MemLp (fun x => f x i j) 2 volume := (memLp_pi_iff.mp hi) j
    apply eLpNorm_congr_norm_ae
    · exact hij.abs.aestronglyMeasurable
    · exact hij.aestronglyMeasurable
    · filter_upwards [] with x
      simp
  calc
    eLpNorm f 2 volume ≤ eLpNorm S 2 volume := hvector
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun x => |f x i j|) 2 volume := hsum
    _ = _ := by simp_rw [hcoord]

private theorem lps_vec3_norm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i : Fin 3, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · simp only [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

private theorem lps_scalar_eLpNorm_bound_of_toLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {f : α → E}
    (hf : MemLp f p μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ‖hf.toLp f‖ ≤ C) :
    eLpNorm f p μ ≤ ENNReal.ofReal C := by
  have hreal : (eLpNorm f p μ).toReal ≤ C := by
    simpa only [Lp.norm_toLp] using hbound
  have hreal' : (eLpNorm f p μ).toReal ≤ (ENNReal.ofReal C).toReal := by
    simpa only [ENNReal.toReal_ofReal hC] using hreal
  exact (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.ofReal_ne_top).1 hreal'

section ProductDifferentiability

local instance : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
local instance : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
local instance : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

private theorem lps_regularized_c1_slice_weak_gradient
    (f : ParabolicPoint → ℝ)
    (hf : ContDiffOn ℝ 1 f
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (t : ℝ) (ht : 0 < t) :
    HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => f (x, t)) (fun x j => spatialPartial f j (x, t)) := by
  have hslice : ContDiffOn ℝ 1 (fun x : Vec3 => f (x, t)) Set.univ := by
    exact hf.comp (by fun_prop) (by
      intro x hx
      exact ⟨Set.mem_univ _, ht⟩)
  have hdiff := contDiffOn_univ.mp hslice
  exact HasWeakGradientOn.of_contDiff
    (U := Set.univ) (f := fun x : Vec3 => f (x, t)) hdiff

end ProductDifferentiability

private theorem lps_l2class_norm_le_scalar_sum
    {f : Vec3 → Vec3} (hf : MemLp f 2 volume) :
    eLpNorm (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) 2 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 volume := by
  let V : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (f x)
  have hV : MemLp V 2 volume := by
    have hV0 := hf.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp (fun x : Vec3 => (WithLp.toLp 2 (f x) : L2Vec3)) 2 volume
    exact hV0
  have hcoord (i : Fin 3) : MemLp (fun x => f x i) 2 volume :=
    (memLp_pi_iff.mp hf) i
  have hpoint (x : Vec3) : ‖V x‖ ≤ ∑ i : Fin 3, |f x i| := by
    change ‖WithLp.toLp 2 (f x)‖ ≤ _
    rw [← vec3EuclideanNorm_eq_l2]
    exact lps_vec3_norm_le_sum_abs (f x)
  have hnorm : eLpNorm V 2 volume ≤ eLpNorm (fun x => ∑ i : Fin 3, |f x i|) 2 volume :=
    eLpNorm_mono_ae_real hV.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hsum : eLpNorm (fun x => ∑ i : Fin 3, |f x i|) 2 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |f x i|) 2 volume :=
    eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
      (f := fun i x => |f x i|) (s := Finset.univ) (by norm_num)
  have hcoordAbs (i : Fin 3) :
      eLpNorm (fun x => |f x i|) 2 volume = eLpNorm (fun x => f x i) 2 volume := by
    apply eLpNorm_congr_norm_ae
    · exact (hcoord i).abs.aestronglyMeasurable
    · exact (hcoord i).aestronglyMeasurable
    · filter_upwards [] with x
      simp
  exact hnorm.trans (hsum.trans_eq (by simp_rw [hcoordAbs]))

private theorem lps_regR12_slice_providers
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ t : ℝ, 0 ≤ t → MemLp
      (fun x : Vec3 => CKN.Leray.regR12Uε ρ b hb ε (x, t)) 2 volume) ∧
    (∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2
      (fun x : Vec3 => CKN.Leray.regR12Uε ρ b hb ε (x, t))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i : Fin 3, ContDiffOn ℝ 1
       (fun z : ParabolicPoint => CKN.Leray.regR12Uε ρ b hb ε z i)
       (spaceTimeSet Set.univ (Ioi 0))) := by
  obtain ⟨⟨hSlice, _hcontinuous, _hinitial, hdiv⟩,
      _hUcontinuous, _hDcontinuous, _hDDcontinuous, _hDtcontinuous,
      _hpcontinuous, _hDpcontinuous, hC1, _hDdiff, _hpDiff,
      _hstrip, _hslab, _hequation, _henergy, _hregularity⟩ :=
    CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  exact ⟨hSlice, hdiv, hC1⟩

theorem lps_regR12_slice_memLp_bounds
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b)
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hUniformBounds :
      ∀ (ε : ℝ) (hε : 0 < ε),
        let U : ParabolicPoint → Vec3 := CKN.Leray.regR12Velocity ρ ε hε b hb
        let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => U y i) j z
        let D2 : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j =>
          fun k => spatialPartial
            (fun y => spatialPartial (fun x => U x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
              spatialGradientSq U D (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2 z i j) ^ (2 : ℕ) ≤ M)
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc 0 T) :
    MemLp (fun x : Vec3 => CKN.Leray.regR12Velocity ρ ε hε b hb (x, t))
        2 volume ∧
    MemLp (fun x : Vec3 => fun i j => spatialPartial
      (fun y => CKN.Leray.regR12Velocity ρ ε hε b hb y i) j (x, t))
        2 volume ∧
    (∀ i : Fin 3, ∃ hi : MemLp (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε b hb (x, t) i) 2 volume,
      ‖hi.toLp (fun x => CKN.Leray.regR12Velocity ρ ε hε b hb (x, t) i)‖ ≤
        Real.sqrt M) ∧
    (∀ i j : Fin 3, ∃ hij : MemLp (fun x : Vec3 => spatialPartial
      (fun y => CKN.Leray.regR12Velocity ρ ε hε b hb y i) j (x, t)) 2 volume,
      ‖hij.toLp (fun x => spatialPartial
        (fun y => CKN.Leray.regR12Velocity ρ ε hε b hb y i) j (x, t))‖ ≤
        Real.sqrt M) := by
  classical
  let U : ParabolicPoint → Vec3 := CKN.Leray.regR12Velocity ρ ε hε b hb
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => U y i) j z
  obtain ⟨Utrace, DUtrace, hUae, hDUae⟩ :=
    lps_regularised_h1_trace ρ ε hε b hb T hT
  let s : CKN.Leray.RegularizedMildTimeInterval T := ⟨t, ht⟩
  have hUmem : MemLp (fun x : Vec3 => U (x, t)) 2 volume := by
    apply (memLp_congr_ae (hUae s)).2
    exact CKN.Leray.realVectorL2Representative_memLp_two (Utrace s)
  have hDscalar (i j : Fin 3) :
      MemLp (fun x : Vec3 => D (x, t) i j) 2 volume := by
    have hrep := (memLp_pi_iff.mp
      (CKN.Leray.realVectorL2Representative_memLp_two (DUtrace j s))) i
    have hmem := (memLp_congr_ae (hDUae s i j)).2 hrep
    simpa only [D, U] using hmem
  have hDmem : MemLp (fun x : Vec3 => D (x, t)) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    simpa only [D, U] using hDscalar i j
  have hUscalar (i : Fin 3) :
      MemLp (fun x : Vec3 => U (x, t) i) 2 volume :=
    (memLp_pi_iff.mp hUmem) i
  have hUenergyInt : Integrable
      (fun x : Vec3 => ∑ i : Fin 3, (U (x, t) i) ^ (2 : ℕ)) volume := by
    apply integrable_finsetSum
    intro i hi
    exact (hUscalar i).integrable_sq
  have hDenergyInt : Integrable
      (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
        (D (x, t) i j) ^ (2 : ℕ)) volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (hDscalar i j).integrable_sq
  have hEnergyEq : (fun x : Vec3 =>
      vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
        spatialGradientSq U D (x, t)) =
      fun x => (∑ i : Fin 3, (U (x, t) i) ^ (2 : ℕ)) +
        ∑ i : Fin 3, ∑ j : Fin 3, (D (x, t) i j) ^ (2 : ℕ) := by
    funext x
    simp only [lps_vec3EuclideanNorm_sq_eq_sum_sq, spatialGradientSq, D]
  have hEnergyInt : Integrable (fun x : Vec3 =>
      vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
        spatialGradientSq U D (x, t)) volume := by
    rw [hEnergyEq]
    exact hUenergyInt.add hDenergyInt
  have hEnergyBound :
      ∫ x : Vec3, vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
        spatialGradientSq U D (x, t) ≤ M := by
    have h := hUniformBounds ε hε
    have ht' := h.1 t ht
    simpa only [U, D] using ht'
  have hUle (i : Fin 3) (x : Vec3) :
      (U (x, t) i) ^ (2 : ℕ) ≤
        vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
          spatialGradientSq U D (x, t) := by
    have hsingle : (U (x, t) i) ^ (2 : ℕ) ≤
        ∑ j : Fin 3, (U (x, t) j) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (U (x, t) j))
        (Finset.mem_univ i)
    rw [lps_vec3EuclideanNorm_sq_eq_sum_sq]
    exact hsingle.trans (le_add_of_nonneg_right (by
      unfold spatialGradientSq
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg (D (x, t) j k)))
  have hDle (i j : Fin 3) (x : Vec3) :
      (D (x, t) i j) ^ (2 : ℕ) ≤
        vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
          spatialGradientSq U D (x, t) := by
    have hrow : (D (x, t) i j) ^ (2 : ℕ) ≤
        ∑ l : Fin 3, (D (x, t) i l) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun l _ => sq_nonneg (D (x, t) i l))
        (Finset.mem_univ j)
    have htotal : (∑ l : Fin 3, (D (x, t) i l) ^ (2 : ℕ)) ≤
        ∑ k : Fin 3, ∑ l : Fin 3, (D (x, t) k l) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        sq_nonneg (D (x, t) k l)) (Finset.mem_univ i)
    calc
      (D (x, t) i j) ^ (2 : ℕ) ≤
          ∑ l : Fin 3, (D (x, t) i l) ^ (2 : ℕ) := hrow
      _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, (D (x, t) k l) ^ (2 : ℕ) := htotal
      _ = spatialGradientSq U D (x, t) := by rfl
      _ ≤ vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ) +
          spatialGradientSq U D (x, t) :=
        le_add_of_nonneg_left (sq_nonneg (vec3EuclideanNorm (U (x, t))))
  have hUbound (i : Fin 3) :
      ‖(hUscalar i).toLp (fun x => U (x, t) i)‖ ≤ Real.sqrt M := by
    exact lps_hessian_component_norm_le hM (hUscalar i)
      ((hUscalar i).integrable_sq) hEnergyInt (hUle i) hEnergyBound
  have hDbound (i j : Fin 3) :
      ‖(hDscalar i j).toLp (fun x => D (x, t) i j)‖ ≤ Real.sqrt M := by
    exact lps_hessian_component_norm_le hM (hDscalar i j)
      ((hDscalar i j).integrable_sq) hEnergyInt (hDle i j) hEnergyBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [U] using hUmem
  · simpa only [D, U] using hDmem
  · intro i
    exact ⟨hUscalar i, hUbound i⟩
  · intro i j
    exact ⟨hDscalar i j, hDbound i j⟩

private lemma lps_vector_weak_slice_scalar
    {v : ℕ → Vec3 → Vec3} {U : Vec3 → Vec3}
    (hweak : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, v n x i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, U x i * w x i)))
    (i : Fin 3) (w : Vec3 → ℝ) (hw : MemLp w 2 volume) :
    Tendsto (fun n => ∫ x : Vec3, v n x i * w x) atTop
      (nhds (∫ x : Vec3, U x i * w x)) := by
  let W : Vec3 → Vec3 := fun x k => if k = i then w x else 0
  have hW : MemLp W 2 volume := by
    apply memLp_pi_iff.mpr
    intro k
    by_cases hk : k = i
    · subst k
      simpa [W] using hw
    · simp [W, hk]
  have hconv := hweak W hW
  have hsource (n : ℕ) :
      (∫ x : Vec3, ∑ k : Fin 3,
        v n x k * W x k) =
        ∫ x : Vec3, v n x i * w x := by
    congr 1
    funext x
    simp [W]
  have htarget : (∫ x : Vec3, ∑ k : Fin 3, U x k * W x k) =
      ∫ x : Vec3, U x i * w x := by
    congr 1
    funext x
    simp [W]
  simpa only [hsource, htarget] using hconv

private lemma lps_weak_vector_limit_eLpNorm_bound
    {v : ℕ → Vec3 → Vec3} {U : Vec3 → Vec3} (M : ℝ)
    (hv : ∀ n, MemLp (v n) 2 volume) (hU : MemLp U 2 volume)
    (hbound : ∀ n,
      ‖(CKN.Leray.lerayHopfLimit_toLp_memLp (hv n)).toLp
        (fun x => (WithLp.toLp 2 (v n x) : L2Vec3))‖ ≤ 3 * Real.sqrt M)
    (hweak : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, v n x i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, U x i * w x i))) :
    eLpNorm U 2 volume ≤ (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
  let V : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (U x)
  have hVmem : MemLp V 2 volume := by
    have h := hU.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp (fun x : Vec3 => (WithLp.toLp 2 (U x) : L2Vec3)) 2 volume
    exact h
  let Vlp := (CKN.Leray.lerayHopfLimit_toLp_memLp hU).toLp V
  have hVbound : ‖Vlp‖ ≤ 3 * Real.sqrt M := by
    simpa only [V, Vlp] using
      CKN.Leray.norm_le_of_weak_tendsto_of_uniform_bound
        (by positivity) hbound (by
          intro y
          let w : Vec3 → Vec3 := fun x => WithLp.ofLp (y x)
          have hw : MemLp w 2 volume := (Lp.memLp y).continuousLinearMap_comp
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
          have hyeq :
              (CKN.Leray.lerayHopfLimit_toLp_memLp hw).toLp
                (fun x => (WithLp.toLp 2 (w x) : L2Vec3)) = y := by
            refine Lp.ext ?_
            filter_upwards [
              (CKN.Leray.lerayHopfLimit_toLp_memLp hw).coeFn_toLp] with x hx
            rw [hx]
          have htarget := CKN.Leray.lerayHopfLimit_inner_toLp_eq hU hw
          have hsource (n : ℕ) :=
            CKN.Leray.lerayHopfLimit_inner_toLp_eq (hv n) hw
          have hpair : ∀ n, inner ℝ
              ((CKN.Leray.lerayHopfLimit_toLp_memLp (hv n)).toLp
                (fun x => (WithLp.toLp 2 (v n x) : L2Vec3))) y =
              ∫ x : Vec3, ∑ i : Fin 3, v n x i * w x i := by
            intro n
            rw [← hyeq]
            exact hsource n
          have hpairLimit : inner ℝ
              ((CKN.Leray.lerayHopfLimit_toLp_memLp hU).toLp
                (fun x => (WithLp.toLp 2 (U x) : L2Vec3))) y =
              ∫ x : Vec3, ∑ i : Fin 3, U x i * w x i := by
            rw [← hyeq]
            exact htarget
          have hpairEq :
              (fun n => inner ℝ
                ((CKN.Leray.lerayHopfLimit_toLp_memLp (hv n)).toLp
                  (fun x => (WithLp.toLp 2 (v n x) : L2Vec3))) y) =
              (fun n => ∫ x : Vec3,
                ∑ i : Fin 3, v n x i * w x i) := by
            funext n
            exact hpair n
          simpa only [hpairEq, hpairLimit] using hweak w hw)
  have hVboundENN : eLpNorm V 2 volume ≤
      ENNReal.ofReal (3 * Real.sqrt M) := by
    exact lps_scalar_eLpNorm_bound_of_toLp hVmem (by positivity) hVbound
  have hpoint (x : Vec3) : ‖U x‖ ≤ ‖V x‖ := by
    change ‖U x‖ ≤ ‖WithLp.toLp 2 (U x)‖
    rw [← vec3EuclideanNorm_eq_l2]
    exact norm_le_vec3EuclideanNorm _
  have hpi : eLpNorm (fun x : Vec3 => U x) 2 volume ≤
      eLpNorm (fun x : Vec3 => ‖V x‖) 2 volume :=
    eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞)) hU.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hVnorm : eLpNorm (fun x : Vec3 => ‖V x‖) 2 volume =
      eLpNorm V 2 volume := eLpNorm_norm V hVmem.aestronglyMeasurable
  calc
    eLpNorm (fun x : Vec3 => U x) 2 volume ≤
        eLpNorm (fun x : Vec3 => ‖V x‖) 2 volume := hpi
    _ = eLpNorm V 2 volume := hVnorm
    _ ≤ ENNReal.ofReal (3 * Real.sqrt M) := hVboundENN
    _ ≤ (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ))]
      gcongr
      norm_num

private lemma lps_vector_h1_weak_limit
    (v : ℕ → Vec3 → Vec3) (D : ℕ → Vec3 → Fin 3 → Vec3)
    (U : Vec3 → Vec3) (B : ℝ) (hB : 0 ≤ B)
    (hmem : ∀ n i j, MemLp (fun x => D n x i j) 2 volume)
    (hbound : ∀ n i j, ‖(hmem n i j).toLp (fun x => D n x i j)‖ ≤ B)
    (hweak : ∀ i w, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, v n x i * w x) atTop
        (nhds (∫ x : Vec3, U x i * w x)))
    (hgradient : ∀ n i, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => v n x i) (fun x => D n x i)) :
    ∃ G : Fin 3 → Vec3 → Vec3,
      ∀ i : Fin 3, ∃ hG : MemLp (G i) 2 volume,
        HasWeakGradientOn (Set.univ : Set Vec3) (fun x => U x i) (G i) ∧
        ∀ j : Fin 3,
          ‖((memLp_pi_iff.mp hG) j).toLp (fun x => G i x j)‖ ≤ B := by
  have hcomponent (i : Fin 3) : ∃ G : Vec3 → Vec3, ∃ hG : MemLp G 2 volume,
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => U x i) G ∧
      ∀ j : Fin 3, ‖((memLp_pi_iff.mp hG) j).toLp (fun x => G x j)‖ ≤ B :=
    lps_h1_scalar_weak_limit (fun n x => v n x i) (fun n x => D n x i)
      (fun x => U x i) B hB (fun n j => hmem n i j)
      (fun n j => hbound n i j) (hweak i) (fun n => hgradient n i)
  choose G hGmem hGweak hGbound using hcomponent
  exact ⟨G, fun i => ⟨hGmem i, hGweak i, hGbound i⟩⟩

private lemma lps_weak_gradient_h1_matrix_bound
    {U : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3} {G : Fin 3 → Vec3 → Vec3}
    (M : ℝ) (hU : MemLp U 2 volume)
    (hGdata : ∀ i : Fin 3, ∃ hG : MemLp (G i) 2 volume,
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => U x i) (G i) ∧
      ∀ j : Fin 3,
        ‖((memLp_pi_iff.mp hG) j).toLp (fun x => G i x j)‖ ≤ Real.sqrt M)
    (hEq : ∀ x i j, D x i j = G i x j) :
    (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => U x i) ∧ h.grad = (fun x : Vec3 => D x i)) ∧
    MemLp D 2 volume ∧ eLpNorm D 2 volume ≤
      (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
  have hDsliceMem : MemLp (fun x : Vec3 => D x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    rcases hGdata i with ⟨hmem, _hweak, _hbound⟩
    have hcoord := (memLp_pi_iff.mp hmem) j
    have hDsliceAt (x : Vec3) : D x i j = G i x j := hEq x i j
    simpa only [hDsliceAt] using hcoord
  have hDsliceBound : eLpNorm (fun x : Vec3 => D x) 2 volume ≤
      (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
    have hsum := lps_eLpNorm_matrix_le_sum_coordinates hDsliceMem
    have hcoord (i j : Fin 3) :
        eLpNorm (fun x : Vec3 => D x i j) 2 volume ≤
          ENNReal.ofReal (Real.sqrt M) := by
      rcases hGdata i with ⟨hGmem, _hweak, hbound⟩
      have hmem : MemLp (fun x : Vec3 => D x i j) 2 volume :=
        (memLp_pi_iff.mp (memLp_pi_iff.mp hDsliceMem i)) j
      have hGcoord : MemLp (fun x : Vec3 => G i x j) 2 volume :=
        (memLp_pi_iff.mp hGmem) j
      have hnorm : ‖hGcoord.toLp (fun x => G i x j)‖ ≤ Real.sqrt M :=
        hbound j
      have hscalar := lps_scalar_eLpNorm_bound_of_toLp hGcoord
        (Real.sqrt_nonneg M) hnorm
      have hDsliceAt (x : Vec3) : D x i j = G i x j := hEq x i j
      simpa only [hDsliceAt] using hscalar
    calc
      eLpNorm (fun x : Vec3 => D x) 2 volume ≤
          ∑ i : Fin 3, ∑ j : Fin 3,
            eLpNorm (fun x : Vec3 => D x i j) 2 volume := hsum
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ENNReal.ofReal (Real.sqrt M) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hcoord i j
      _ = (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc]
        norm_num
  have hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => U x i) ∧
      h.grad = (fun x : Vec3 => D x i) := by
    intro i
    rcases hGdata i with ⟨hGi, hGweak, _hGbound⟩
    let hi : H1Function (Set.univ : Set Vec3) := {
      toFun := fun x => U x i
      grad := G i
      memL2 := by
        have hcomp := (memLp_pi_iff.mp hU) i
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hcomp
      gradMemL2 := by
        intro j
        have hcomp := (memLp_pi_iff.mp hGi) j
        simpa [CKN.GradMemLpOn, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hcomp
      hasWeakGradient := hGweak
    }
    refine ⟨hi, rfl, ?_⟩
    funext x j
    exact (hEq x i j).symm
  exact ⟨hH1, hDsliceMem, hDsliceBound⟩

/-- Uniform regularized `H¹` bounds pass to every positive-time slice of the
selected Leray limit. The slices belong to `H¹ ∩ J`, and the same bounds give
the finite-slab `L²` control used for the velocity tensor. -/
theorem lps_strong_limit_all_time_h1_slices
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧ IsInJ b)
    (T M : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hUniformBounds :
      ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hb.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => Uε y i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j =>
          fun k => spatialPartial
            (fun y => spatialPartial (fun x => Uε x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    {u : ParabolicPoint → Vec3}
    (hweakSlice : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
      MemLp w 2 volume →
      Tendsto
        (fun n => ∫ x : Vec3, ∑ i : Fin 3,
          CKN.Leray.regR12Uε ρ b hb.2
            (1 / ((σ n : ℝ) + 1)) (x, t) i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)))
    (hrep : ∀ z : Vec3 × ℝ, 0 < z.2 →
      u (parabolicHomeomorph.symm z) =
        CKN.Leray.compactnessMollifiedLimit
          (fun n => fun y => CKN.Leray.regR12Uε ρ b hb.2
            (1 / ((σ n : ℝ) + 1)) (parabolicHomeomorph.symm y)) σ z) :
    ∃ Dslice : ParabolicPoint → Fin 3 → Vec3,
      ∀ t : ℝ, t ∈ Ioc 0 T →
        IsLpsGoodTime u Dslice t ∧
        eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤
          (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) ∧
        eLpNorm (fun x : Vec3 => Dslice (x, t)) 2 volume ≤
          (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) := by
  classical
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let Useq : ℕ → Vec3 × ℝ → Vec3 := fun n y =>
    CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) (parabolicHomeomorph.symm y)
  have hεpos (n : ℕ) : 0 < εseq (σ n) := by positivity
  have hσtop : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hregSlice (n : ℕ) : ∀ t : ℝ, 0 ≤ t → MemLp
      (fun x : Vec3 => CKN.Leray.regR12Uε ρ b hb.2
        (εseq (σ n)) (x, t)) 2 volume :=
    (lps_regR12_slice_providers ρ b hb.2 (εseq (σ n)) (hεpos n)).1
  have hregDiv (n : ℕ) : ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2
      (fun x : Vec3 => CKN.Leray.regR12Uε ρ b hb.2
        (εseq (σ n)) (x, t)) :=
    (lps_regR12_slice_providers ρ b hb.2 (εseq (σ n)) (hεpos n)).2.1
  have hregC1 (n : ℕ) :=
    (lps_regR12_slice_providers ρ b hb.2 (εseq (σ n)) (hεpos n)).2.2
  have hregBounds (t : ℝ) (ht : t ∈ Icc 0 T) (n : ℕ) :=
    lps_regR12_slice_memLp_bounds ρ b hb.2 T M hT.le hM hUniformBounds
      (εseq (σ n)) (hεpos n) t ht
  have hUeq (n : ℕ) :
      CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) =
        CKN.Leray.regR12Velocity ρ (εseq (σ n)) (hεpos n) b hb.2 := by
    simp only [CKN.Leray.regR12Uε, hεpos, ↓reduceDIte]
  have hweakScalar (t : ℝ) (ht : 0 < t) (i : Fin 3) :
      ∀ w : Vec3 → ℝ, MemLp w 2 volume →
        Tendsto (fun n => ∫ x : Vec3,
          CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) (x, t) i * w x)
          atTop (nhds (∫ x : Vec3, u (x, t) i * w x)) :=
    lps_vector_weak_slice_scalar (hweakSlice t ht) i
  have hregWeakGradient (t : ℝ) (ht : 0 < t) (i : Fin 3) (n : ℕ) :
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) (x, t) i)
        (fun x j => spatialPartial
          (fun y => CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) y i)
          j (x, t)) := by
    exact lps_regularized_c1_slice_weak_gradient
      (fun z => CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) z i)
      (hregC1 n i) t ht
  have hgradAll (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ∃ G : Fin 3 → Vec3 → Vec3,
        ∀ i : Fin 3, ∃ hG : MemLp (G i) 2 volume,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x => u (x, t) i) (G i) ∧
          ∀ j : Fin 3,
            ‖((memLp_pi_iff.mp hG) j).toLp
              (fun x => G i x j)‖ ≤ Real.sqrt M := by
    refine lps_vector_h1_weak_limit
      (fun n x => CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) (x, t))
      (fun n x i j => spatialPartial
        (fun y => CKN.Leray.regR12Uε ρ b hb.2 (εseq (σ n)) y i) j (x, t))
      (fun x => u (x, t)) (Real.sqrt M) (Real.sqrt_nonneg M) ?_ ?_ ?_ ?_
    · intro n i j
      simpa only [hUeq] using
        (memLp_pi_iff.mp (memLp_pi_iff.mp (hregBounds t ⟨ht.1.le, ht.2⟩ n).2.1 i)) j
    · intro n i j
      rcases (hregBounds t ⟨ht.1.le, ht.2⟩ n).2.2.2 i j with ⟨hmem, hnorm⟩
      simpa only [hUeq] using hnorm
    · exact hweakScalar t ht.1
    · intro n i
      exact hregWeakGradient t ht.1 i n
  let Dslice : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    if ht : z.2 ∈ Ioc 0 T then (Classical.choose (hgradAll z.2 ht)) i z.1 j
    else 0
  refine ⟨Dslice, ?_⟩
  intro t ht
  let G : Fin 3 → Vec3 → Vec3 := Classical.choose (hgradAll t ht)
  have hGdata : ∀ i : Fin 3, ∃ hG : MemLp (G i) 2 volume,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, t) i) (G i) ∧
      ∀ j : Fin 3,
        ‖((memLp_pi_iff.mp hG) j).toLp (fun x => G i x j)‖ ≤ Real.sqrt M := by
    dsimp only [G]
    exact Classical.choose_spec (hgradAll t ht)
  have hsliceSeq (n : ℕ) : MemLp (fun x : Vec3 => Useq n (x, t)) 2 volume := by
    have h := hregSlice n t ht.1.le
    simpa only [Useq, parabolicHomeomorph_symm_apply] using h
  have hsequenceClassBound (n : ℕ) :
      ‖(CKN.Leray.lerayHopfLimit_toLp_memLp (hsliceSeq n)).toLp
        (fun x => (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3))‖ ≤
          3 * Real.sqrt M := by
    rw [Lp.norm_toLp]
    have hsum := lps_l2class_norm_le_scalar_sum (hsliceSeq n)
    have hcomponent (i : Fin 3) :
        eLpNorm (fun x : Vec3 => Useq n (x, t) i) 2 volume ≤
          ENNReal.ofReal (Real.sqrt M) := by
      rcases (hregBounds t ⟨ht.1.le, ht.2⟩ n).2.2.1 i with ⟨hi, hbound⟩
      have h := lps_scalar_eLpNorm_bound_of_toLp hi (Real.sqrt_nonneg M) hbound
      simpa only [Useq, εseq, parabolicHomeomorph_symm_apply, hUeq] using h
    have hsum' : eLpNorm (fun x => (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3))
        2 volume ≤ 3 * ENNReal.ofReal (Real.sqrt M) := by
      calc
        _ ≤ ∑ i : Fin 3, eLpNorm (fun x => Useq n (x, t) i) 2 volume := hsum
        _ ≤ ∑ _i : Fin 3, ENNReal.ofReal (Real.sqrt M) :=
          Finset.sum_le_sum fun i hi => hcomponent i
        _ = 3 * ENNReal.ofReal (Real.sqrt M) := by simp
    have hVmem : MemLp (fun x : Vec3 =>
        (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3)) 2 volume := by
      have h := (hsliceSeq n).continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
      change MemLp (fun x : Vec3 =>
        (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3)) 2 volume
      exact h
    have hreal' : (eLpNorm (fun x =>
        (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3)) 2 volume).toReal ≤
          3 * Real.sqrt M := by
      have hboundTop : (3 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
      have hreal := ENNReal.toReal_mono hboundTop hsum'
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (Real.sqrt_nonneg M)] using hreal
    exact hreal'
  have hrepSlice (x : Vec3) : u (x, t) =
      CKN.Leray.compactnessMollifiedLimit Useq σ (x, t) := by
    simpa only [parabolicHomeomorph_symm_apply, Useq, εseq] using hrep (x, t) ht.1
  have hweakVector : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
        Useq n (x, t) i * w x i) atTop
        (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)) := by
    intro w hw
    simpa only [Useq, εseq, parabolicHomeomorph_symm_apply] using hweakSlice t ht.1 w hw
  have huSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    CKN.Leray.lerayHopfLimit_slice_memLp_of_representative
      Useq σ hσtop u t hrepSlice hsliceSeq (3 * Real.sqrt M)
      (by positivity) hsequenceClassBound hweakVector
  have hdivSlice : ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ.partialDeriv i x = 0 :=
    CKN.Leray.lerayHopfLimit_divergence_of_weakSlice
      (fun n x => Useq n (x, t)) (fun x => u (x, t))
      (fun n => by
        simpa only [Useq, εseq, parabolicHomeomorph_symm_apply] using
          hregDiv n t ht.1.le)
      hweakVector
  have hJ : IsInJ (fun x : Vec3 => u (x, t)) :=
    CKN.weakDivFreeL2_isInJ ⟨huSlice, hdivSlice⟩
  obtain ⟨hH1, hDsliceMem, hDsliceBound⟩ :=
    lps_weak_gradient_h1_matrix_bound M huSlice hGdata (D := fun x => Dslice (x, t)) (by
      intro x i j
      dsimp only [Dslice]
      simp only [dite_eq_left ht]
      change (Classical.choose (hgradAll t ht)) i x j = G i x j
      rfl)
  have hValueBound : eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤
      (9 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt M) :=
    lps_weak_vector_limit_eLpNorm_bound M hsliceSeq huSlice hsequenceClassBound hweakVector
  refine ⟨⟨hH1, hJ⟩, hValueBound, hDsliceBound⟩

/-- The initial trace and the datum's `H¹ ∩ J` representative fill in the
zero-time slice, while the positive-time extraction includes the final time.
This gives selected `H¹ ∩ J` representatives on the whole closed interval. -/
theorem lps_strong_limit_h1_slices_closed
    {b : Vec3 → Vec3} {Db : Vec3 → Fin 3 → Vec3}
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧ IsInJ b)
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (htrace : ∀ x : Vec3, u (x, 0) = b x)
    (B : ℝ≥0∞)
    (Dpositive : ParabolicPoint → Fin 3 → Vec3)
    (hpositive : ∀ t : ℝ, t ∈ Ioc 0 T →
      IsLpsGoodTime u Dpositive t ∧
        eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤ B ∧
        eLpNorm (fun x : Vec3 => Dpositive (x, t)) 2 volume ≤ B) :
    ∃ Dslice : ParabolicPoint → Fin 3 → Vec3,
      (∀ t : ℝ, t ∈ Icc 0 T → IsLpsGoodTime u Dslice t) ∧
      (∀ t : ℝ, t ∈ Ioc 0 T →
        eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤ B ∧
          eLpNorm (fun x : Vec3 => Dslice (x, t)) 2 volume ≤ B) := by
  classical
  let Dslice : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    if z.2 = 0 then Db z.1 i j else Dpositive z i j
  refine ⟨Dslice, ?_, ?_⟩
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hvalue : (fun x : Vec3 => u (x, 0)) = b := by
        funext x
        exact htrace x
      constructor
      · intro i
        rcases hb.1 i with ⟨h, hfun, hgrad⟩
        refine ⟨h, ?_, ?_⟩
        · calc
            h.toFun = (fun x : Vec3 => b x i) := hfun
            _ = (fun x : Vec3 => u (x, 0) i) := by
              funext x
              exact congrArg (fun v : Vec3 => v i) (htrace x).symm
        · simpa [Dslice] using hgrad
      · rw [hvalue]
        exact hb.2
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htIoc : t ∈ Ioc 0 T := ⟨htpos, ht.2⟩
      have hDsliceEq : (fun x : Vec3 => Dslice (x, t)) =
          fun x => Dpositive (x, t) := by
        funext x i j
        simp [Dslice, ht0]
      rcases (hpositive t htIoc).1 with ⟨hH1, hJ⟩
      constructor
      · intro i
        rcases hH1 i with ⟨h, hfun, hgrad⟩
        refine ⟨h, hfun, ?_⟩
        calc
          h.grad = (fun x => Dpositive (x, t) i) := hgrad
          _ = (fun x => Dslice (x, t) i) := by
            funext x
            exact congrFun (congrFun hDsliceEq x).symm i
      · exact hJ
  · intro t ht
    rcases hpositive t ht with ⟨hgood, hu, hD⟩
    refine ⟨hu, ?_⟩
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    simpa [Dslice, ht0] using hD


end ESS.LPS

end
