/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDirectRoute
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpaceTimeHilbert
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformContracts
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsFinal
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Compactness data for the local strong solution

This file starts the compactness step of `prop:lps-local-strong` from the exact uniform spatial
`H¹` and `H²` bounds. The Leray limit supplies its canonical trace, weak
gradient convergence, and strong velocity convergence (`prop:leray-limit` of the CKN manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The squared Euclidean norm of a vector is the sum of its squared coordinates. -/
theorem lps_vec3EuclideanNorm_sq_eq_sum_sq (v : Vec3) :
    vec3EuclideanNorm v ^ (2 : ℕ) = ∑ i : Fin 3, v i ^ (2 : ℕ) := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-- The ordered second spatial derivatives of one regularized velocity are in
space-time `L²` on the full open slab, including times arbitrarily close to
zero. The Bessel path controls the Fourier multiplier at the initial endpoint;
the pointwise derivative is identified with that path on positive times. -/
theorem lps_regR12_second_memLp_open_slab
    (ρ : CKN.Leray.RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (b : Vec3 → Vec3) (hb : IsInJ b)
    (T : ℝ) (hT : 0 < T) (i j k : Fin 3) :
    MemLp (fun z : ParabolicPoint =>
      spatialPartial
        (fun y => spatialPartial
          (fun x => CKN.Leray.regR12Velocity ρ ε hε b hb x i) j y) k z)
      2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hPath := fun S hS =>
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε b hb 2 S hS
  obtain ⟨v, hv⟩ := hPath T hT.le
  have hGB : ∀ t ∈ Ioo 0 T,
      ‖CKN.Leray.regR12LiftFreq T hT.le v t‖ ≤ ‖v‖ := by
    intro t ht
    exact CKN.Leray.regR12LiftFreq_norm_le T hT.le v t
  let M : L2Vec3 → ℂ := fun ξ =>
    CKN.Leray.regR12CoordSymbol k ξ *
      (CKN.Leray.regR12CoordSymbol j ξ * 1)
  have hM : AEStronglyMeasurable M := by
    have hContM : Continuous M := by
      change Continuous (CKN.Leray.regR12CoordSymbol k *
        (CKN.Leray.regR12CoordSymbol j * fun _ : L2Vec3 => (1 : ℂ)))
      exact (CKN.Leray.regR12CoordSymbol_continuous k).mul
        ((CKN.Leray.regR12CoordSymbol_continuous j).mul continuous_const)
    exact hContM.aestronglyMeasurable
  have hmodel := CKN.Leray.regR12SpaceTimeField_memLp_slab
    (CKN.Leray.regR12CoordCLM i) M hM
    ((2 * Real.pi) ^ 2) (by positivity)
    (CKN.Leray.regR12_second_norm_le j k)
    (CKN.Leray.regR12LiftFreq T hT.le v)
    (CKN.Leray.regR12LiftFreq_continuous T hT.le v)
    0 T ‖v‖ hGB
  have hslab : MeasurableSet
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  apply (memLp_congr_ae ?_).2 hmodel
  filter_upwards [ae_restrict_mem hslab] with z hz
  exact CKN.Leray.regR12Velocity_DD_eq_model
    ρ ε hε b hb T hT.le v hv z ⟨hz.2.1.le, hz.2.2.le⟩ i j k

/-- A square-integrable scalar component controlled pointwise by an
integrable nonnegative energy density inherits its global `L²` bound. -/
theorem lps_hessian_component_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f S : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hmem : MemLp f 2 μ)
    (hfsq : Integrable (fun z => (f z) ^ (2 : ℕ)) μ)
    (hSint : Integrable S μ)
    (hle : ∀ z, (f z) ^ (2 : ℕ) ≤ S z)
    (henergy : (∫ z, S z ∂μ) ≤ M) :
    ‖hmem.toLp f‖ ≤ Real.sqrt M := by
  have hpoint (z : α) :
      ‖f z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f z) ^ (2 : ℕ)) := by
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f z)) (by norm_num)]
    norm_num [Real.norm_eq_abs, sq_abs]
  have hlintegral :
      (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ) =
        ENNReal.ofReal (∫ z, (f z) ^ (2 : ℕ) ∂μ) := by
    calc
      (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ) =
          ∫⁻ z, ENNReal.ofReal ((f z) ^ (2 : ℕ)) ∂μ :=
        lintegral_congr fun z => hpoint z
      _ = ENNReal.ofReal (∫ z, (f z) ^ (2 : ℕ) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hfsq
          (Eventually.of_forall fun z => sq_nonneg (f z))).symm
  have hreal : (∫ z, (f z) ^ (2 : ℕ) ∂μ) ≤ M :=
    (integral_mono hfsq hSint hle).trans henergy
  have hpower : eLpNorm f 2 μ ^ (2 : ℝ) ≤ ENNReal.ofReal M := by
    rw [CKN.Leray.lerayLimit_eLpNorm_two_sq_eq_lintegral hmem.aestronglyMeasurable,
      hlintegral]
    exact ENNReal.ofReal_le_ofReal hreal
  have hrootPower :
      (ENNReal.ofReal M ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ENNReal.ofReal M := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hroot : eLpNorm f 2 μ ≤ ENNReal.ofReal M ^ (1 / 2 : ℝ) :=
    (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
      (hpower.trans_eq hrootPower.symm)
  rw [Lp.norm_toLp]
  calc
    (eLpNorm f 2 μ).toReal ≤
        (ENNReal.ofReal M ^ (1 / 2 : ℝ)).toReal :=
      ENNReal.toReal_mono
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne hroot
    _ = Real.sqrt M := by
      rw [ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)]
      rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]

/-- The inner product of an `L²` class with a class represented by a function. -/
theorem lps_scalar_lp_inner_left_eq_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : Lp ℝ 2 μ}
    {g : α → ℝ} (hg : MemLp g 2 μ) :
    inner ℝ F (hg.toLp g) = ∫ z, (F z) * g z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z h
  rw [h]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A weakly convergent `L²` scalar sequence with uniformly bounded weak
gradients has a weak gradient limit with the same coordinate bounds. -/
theorem lps_h1_scalar_weak_limit
    (fseq : ℕ → Vec3 → ℝ) (gseq : ℕ → Vec3 → Vec3)
    (f : Vec3 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hgseq : ∀ n j, MemLp (fun x => gseq n x j) 2 volume)
    (hbound : ∀ n j,
      ‖(hgseq n j).toLp (fun x => gseq n x j)‖ ≤ C)
    (hweakf : ∀ w : Vec3 → ℝ, MemLp w 2 volume →
      Tendsto (fun n => ∫ x, fseq n x * w x ∂volume) atTop
        (nhds (∫ x, f x * w x ∂volume)))
    (hweakD : ∀ n, HasWeakGradientOn (Set.univ : Set Vec3)
      (fseq n) (gseq n)) :
    ∃ G : Vec3 → Vec3, ∃ hG : MemLp G 2 volume,
      HasWeakGradientOn (Set.univ : Set Vec3) f G ∧
      ∀ j : Fin 3,
        ‖((memLp_pi_iff.mp hG) j).toLp (fun x => G x j)‖ ≤ C := by
  classical
  let F : ℕ → ∀ j : Fin 3, Lp ℝ 2 volume := fun n j =>
    (hgseq n j).toLp (fun x => gseq n x j)
  have hFbound (n : ℕ) (j : Fin 3) : ‖F n j‖ ≤ C := hbound n j
  let : IsSeparable (volume : Measure Vec3) := inferInstance
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace
      (Lp ℝ (2 : ℝ≥0∞) (volume : Measure Vec3)) := by
    exact TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨τ, hτ, H, hHweak⟩ :=
    CKN.Leray.exists_common_subsequence_weak_limit_of_bounded
      F (fun _ : Fin 3 => C) (fun _ => hC) hFbound
  let G : Vec3 → Vec3 := fun x j => H j x
  have hGmem : MemLp G 2 volume := by
    apply memLp_pi_iff.mpr
    intro j
    simpa only [G] using Lp.memLp (H j)
  have hGcoord (j : Fin 3) : MemLp (fun x => G x j) 2 volume :=
    (memLp_pi_iff.mp hGmem) j
  have hGbound (j : Fin 3) :
    ‖(hGcoord j).toLp (fun x => G x j)‖ ≤ C := by
    have hlim := CKN.Leray.norm_le_of_weak_tendsto_of_uniform_bound
      hC (fun n => hFbound (τ n) j) (hHweak j)
    have heq : (hGcoord j).toLp (fun x => G x j) = H j := by
      apply Lp.ext
      filter_upwards [(hGcoord j).coeFn_toLp] with x hx
      exact hx
    rw [heq]
    exact hlim
  have hweakGrad : HasWeakGradientOn (Set.univ : Set Vec3) f G := by
    intro j φ hφ hφc hφsub
    have hφcont : Continuous φ := hφ.continuous
    have hφderivCont : Continuous
        (fun x : Vec3 => (fderiv ℝ φ x) (basisVec j)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hφderivCompact : HasCompactSupport
        (fun x : Vec3 => (fderiv ℝ φ x) (basisVec j)) :=
      hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
    have hφmem : MemLp φ 2 volume := hφcont.memLp_of_hasCompactSupport hφc
    have hφderivMem : MemLp
        (fun x : Vec3 => (fderiv ℝ φ x) (basisVec j)) 2 volume :=
      hφderivCont.memLp_of_hasCompactSupport hφderivCompact
    have hvalue :=
      (hweakf (fun x => (fderiv ℝ φ x) (basisVec j)) hφderivMem).comp
        hτ.tendsto_atTop
    have hgradientInner := hHweak j (hφmem.toLp φ)
    have hgradient : Tendsto
        (fun n => ∫ x, gseq (τ n) x j * φ x ∂volume) atTop
        (nhds (∫ x, G x j * φ x ∂volume)) := by
      have hInnerEq (n : ℕ) :
          inner ℝ (F (τ n) j) (hφmem.toLp φ) =
            ∫ x, gseq (τ n) x j * φ x ∂volume := by
        simpa only [F] using
          lps_scalar_lp_inner_integral_generic (hgseq (τ n) j) hφmem
      have hLimitEq :
          inner ℝ (H j) (hφmem.toLp φ) = ∫ x, G x j * φ x ∂volume := by
        simpa only [G] using
          lps_scalar_lp_inner_left_eq_integral (F := H j) hφmem
      simpa only [hInnerEq, hLimitEq] using hgradientInner
    have hnegative := hgradient.neg
    have hIBP (n : ℕ) :
        ∫ x, fseq (τ n) x * (fderiv ℝ φ x) (basisVec j) ∂volume =
          -(∫ x, gseq (τ n) x j * φ x ∂volume) := by
      have h := hweakD (τ n) j φ hφ hφc
        (fun x hx => Set.mem_univ x)
      simpa only [Measure.restrict_univ] using h
    have hvalueNeg : Tendsto
        (fun n => -(∫ x, gseq (τ n) x j * φ x ∂volume)) atTop
        (nhds (∫ x, f x * (fderiv ℝ φ x) (basisVec j) ∂volume)) := by
      exact hvalue.congr fun n => hIBP n
    have heq := tendsto_nhds_unique hvalueNeg hnegative
    simpa only [G, Measure.restrict_univ] using heq
  exact ⟨G, hGmem, hweakGrad, hGbound⟩

/-- The canonical Leray limit, together with the inherited uniform second
derivative bound, for the sequence `εₙ = 1 / (n + 1)`. -/
theorem lps_strong_limit_compactness_base
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧
      IsInJ b)
    (T M : ℝ) (hT : 0 < T)
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
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ u : ParabolicPoint → Vec3, ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        (∀ x : Vec3, u (x, 0) = b x) ∧
        IsLerayHopfSolution T b u Du ∧
        MemLp u 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp Du 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        Tendsto
          (fun n => eLpNorm
            (CKN.Leray.regR12Uε ρ b hb.2
              ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) - u)
            2 (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0) ∧
        (∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
          MemLp w 2
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
          Tendsto
            (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              spatialPartial
                (fun y => CKN.Leray.regR12Uε ρ b hb.2
                  ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) y i) j z * w z)
            atTop
            (nhds (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              Du z i j * w z))) ∧
        (∀ n : ℕ,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            ∑ i : Fin 3, ∑ j : Fin 3,
              vec3EuclideanNorm
                (fun k => spatialPartial
                  (fun y => spatialPartial
                    (fun x => CKN.Leray.regR12Velocity ρ
                      ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n))
                      (by positivity) b hb.2 x i) j y)
                  k z) ^ (2 : ℕ) ≤ M) ∧
        (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
          MemLp w 2 volume →
          Tendsto
            (fun n => ∫ x : Vec3, ∑ i : Fin 3,
              CKN.Leray.regR12Uε ρ b hb.2
                ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) (x, t) i * w x i)
            atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y => CKN.Leray.regR12Uε ρ b hb.2
                ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n))
                (parabolicHomeomorph.symm y)) σ z) := by
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hseq : ∀ n : ℕ, 0 < εseq n ∧ εseq n ≤ 1 := by
    intro n
    dsimp [εseq]
    constructor
    · positivity
    · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith only [hn0]
      calc
        1 / ((n : ℝ) + 1) ≤ 1 / 1 :=
          one_div_le_one_div_of_le (by norm_num) hn
        _ = 1 := by norm_num
  have hεseq : Tendsto εseq atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let uε := CKN.Leray.regR12Uε ρ
  let pε := CKN.Leray.regR12Pε ρ
  have hregularised := CKN.Leray.regR12_regularised_unconditional ρ
  have htails := CKN.Leray.regTails_of_regularised ρ uε pε hregularised
  have hlimit := CKN.Leray.lerayLimit_prop_of_regularised_tails
    ρ uε pε hregularised htails
  have hregMomentum := CKN.Leray.regMomentum_of_regularised
    ρ uε pε hregularised
  let hlim := hlimit b hb.2 εseq hseq hεseq
  let σ := Classical.choose hlim
  let hlim1 := Classical.choose_spec hlim
  let u := Classical.choose hlim1
  let hlim2 := Classical.choose_spec hlim1
  let Du := Classical.choose hlim2
  obtain ⟨hσ, hσtop, _hεsub, htrace, hslabs, hrep⟩ :=
    Classical.choose_spec hlim2
  have hhopf := CKN.Leray.lerayHopfLimit
    ρ uε pε hregularised hregMomentum hlimit b hb.2 εseq hseq hεseq
  have hLH : IsLerayHopfSolution T b u Du := by
    exact hhopf T hT
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  have hslab := hslabs T hT
  rcases hslab with
    ⟨_huMeas, _hDuMeas, huMem, hDuMem, hUconv, hDweak,
      _hsubcritical, _hU3, _hJ3, _hu3, _hJconv, hweakSlice, _hgrad⟩
  have hH2 (n : ℕ) :
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, ∑ j : Fin 3,
          vec3EuclideanNorm
            (fun k => spatialPartial
              (fun y => spatialPartial
                (fun x => CKN.Leray.regR12Velocity ρ (εseq (σ n))
                  (hseq (σ n)).1 b hb.2 x i)
                j y) k z) ^ (2 : ℕ) ≤ M := by
    have h := hUniformBounds (εseq (σ n)) (hseq (σ n)).1
    simpa [εseq] using h.2
  refine ⟨σ, hσ, u, Du, htrace, hLH, huMem, hDuMem, ?_, ?_, hH2, ?_, ?_⟩
  · simpa only [μ, εseq, uε, σ, u] using hUconv
  · intro i j w hw
    simpa only [μ, εseq, uε, σ, u] using hDweak i j w hw
  · intro t ht w hw
    simpa only [uε, σ, εseq, u] using hweakSlice t ht w hw
  · intro z hz
    exact hrep z hz

/-- On a finite slab, the regularized ordered Hessians have one global
space-time weak `L²` limit along a further subsequence of the Leray limit. -/
theorem lps_strong_limit_hessian_weak_compactness
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
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ u : ParabolicPoint → Vec3, ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        (∀ x : Vec3, u (x, 0) = b x) ∧
        IsLerayHopfSolution T b u Du ∧
        MemLp u 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp Du 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        Tendsto
          (fun n => eLpNorm
            (CKN.Leray.regR12Uε ρ b hb.2
              ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) - u)
            2 (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0) ∧
        (∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
          MemLp w 2
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
          Tendsto
            (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              spatialPartial
                (fun y => CKN.Leray.regR12Uε ρ b hb.2
                  ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) y i) j z * w z)
            atTop
            (nhds (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              Du z i j * w z))) ∧
        ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
          MemLp D2u 2
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
          (∀ i j k : Fin 3, ∀ w : ParabolicPoint → ℝ,
            MemLp w 2 (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
            Tendsto
              (fun n => ∫ z,
                spatialPartial
                  (fun y => spatialPartial
                    (fun x => CKN.Leray.regR12Velocity ρ
                      (1 / ((σ n : ℝ) + 1)) (by positivity) b hb.2 x i)
                    j y) k z * w z
                ∂(volume.restrict
                  (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
              atTop (nhds (∫ z, D2u z i j k * w z
                ∂(volume.restrict
                  (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))) ) ∧
        ∃ σ₀ : ℕ → ℕ, StrictMono σ₀ ∧
          (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
            MemLp w 2 volume →
            Tendsto
              (fun n => ∫ x : Vec3, ∑ i : Fin 3,
                CKN.Leray.regR12Uε ρ b hb.2
                  (1 / ((σ₀ n : ℝ) + 1)) (x, t) i * w x i)
              atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
          (∀ z : Vec3 × ℝ, 0 < z.2 →
            u (parabolicHomeomorph.symm z) =
              CKN.Leray.compactnessMollifiedLimit
                (fun n => fun y => CKN.Leray.regR12Uε ρ b hb.2
                  (1 / ((σ₀ n : ℝ) + 1)) (parabolicHomeomorph.symm y)) σ₀ z) := by
  classical
  obtain ⟨σ, hσ, u, Du, htrace, hLH, huMem, hDuMem, hUconv, hDweak, hH2,
    hweakSlice, hrep⟩ :=
    lps_strong_limit_compactness_base ρ b Db hb T M hT hUniformBounds
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let D2seq : ℕ → ParabolicPoint → Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun n z i j k => spatialPartial
      (fun y => spatialPartial
        (fun x => CKN.Leray.regR12Velocity ρ (εseq (σ n)) (by positivity)
          b hb.2 x i) j y) k z
  let energy : ℕ → ParabolicPoint → ℝ := fun n z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      vec3EuclideanNorm (fun k => D2seq n z i j k) ^ (2 : ℕ)
  have hD2coord (n : ℕ) (i j k : Fin 3) :
      MemLp (fun z => D2seq n z i j k) 2 μ := by
    have hv := lps_regR12_second_memLp_open_slab
      ρ (εseq (σ n)) (by positivity) b hb.2 T hT i j
    simpa only [D2seq, μ, εseq] using hv k
  have henergyEq (n : ℕ) :
      energy n = fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (D2seq n z i j k) ^ (2 : ℕ) := by
    funext z
    simp only [energy, lps_vec3EuclideanNorm_sq_eq_sum_sq]
  have hsumIntegrable (n : ℕ) :
      Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (D2seq n z i j k) ^ (2 : ℕ)) μ := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    apply integrable_finsetSum
    intro k hk
    simpa [Real.norm_eq_abs, sq_abs] using
      (hD2coord n i j k).integrable_sq
  have henergyInt (n : ℕ) : Integrable (energy n) μ := by
    rw [henergyEq n]
    exact hsumIntegrable n
  have henergyBound (n : ℕ) : (∫ z, energy n z ∂μ) ≤ M := by
    have h := hH2 n
    simpa only [μ, energy, D2seq, εseq] using h
  have hcomponentLe (n : ℕ) (i j k : Fin 3) (z : ParabolicPoint) :
      (D2seq n z i j k) ^ (2 : ℕ) ≤ energy n z := by
    have hrow : (D2seq n z i j k) ^ (2 : ℕ) ≤
        ∑ l : Fin 3, (D2seq n z i j l) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun l _ => sq_nonneg (D2seq n z i j l))
        (Finset.mem_univ k)
    have hrowEq :
        ∑ l : Fin 3, (D2seq n z i j l) ^ (2 : ℕ) =
          vec3EuclideanNorm (fun l => D2seq n z i j l) ^ (2 : ℕ) :=
      (lps_vec3EuclideanNorm_sq_eq_sum_sq _).symm
    have hcol : vec3EuclideanNorm (fun l => D2seq n z i j l) ^ (2 : ℕ) ≤
        ∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z i q l) ^ (2 : ℕ) :=
      Finset.single_le_sum
        (f := fun q => vec3EuclideanNorm (fun l => D2seq n z i q l) ^ (2 : ℕ))
        (fun q _ => sq_nonneg
          (vec3EuclideanNorm (fun l => D2seq n z i q l)))
        (Finset.mem_univ j)
    have hrowAll :
        (∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z i q l) ^ (2 : ℕ)) ≤
        energy n z := by
      change (∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z i q l) ^ (2 : ℕ)) ≤
        ∑ p : Fin 3, ∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z p q l) ^ (2 : ℕ)
      exact Finset.single_le_sum
        (f := fun p => ∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z p q l) ^ (2 : ℕ))
        (fun p _ => Finset.sum_nonneg fun q _ =>
          sq_nonneg (vec3EuclideanNorm (fun l => D2seq n z p q l)))
        (Finset.mem_univ i)
    calc
      _ ≤ ∑ l : Fin 3, (D2seq n z i j l) ^ (2 : ℕ) := hrow
      _ = vec3EuclideanNorm (fun l => D2seq n z i j l) ^ (2 : ℕ) := hrowEq
      _ ≤ ∑ q : Fin 3,
          vec3EuclideanNorm (fun l => D2seq n z i q l) ^ (2 : ℕ) := hcol
      _ ≤ energy n z := hrowAll
  have hD2bound (n : ℕ) (i j k : Fin 3) :
      ‖(hD2coord n i j k).toLp (fun z => D2seq n z i j k)‖ ≤ Real.sqrt M :=
    lps_hessian_component_norm_le hM (hD2coord n i j k)
      ((hD2coord n i j k).integrable_sq) (henergyInt n)
      (hcomponentLe n i j k) (henergyBound n)
  let ι := Fin 3 × Fin 3 × Fin 3
  let F : ℕ → ∀ q : ι, Lp ℝ 2 μ := fun n q =>
    (hD2coord n q.1 q.2.1 q.2.2).toLp
      (fun z => D2seq n z q.1 q.2.1 q.2.2)
  have hweakBound (n : ℕ) (q : ι) : ‖F n q‖ ≤ Real.sqrt M := by
    exact hD2bound n q.1 q.2.1 q.2.2
  let : IsSeparable μ := inferInstance
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := by
    exact TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨τ, hτ, H, hHweak⟩ :=
    CKN.Leray.exists_common_subsequence_weak_limit_of_bounded
      F (fun _ : ι => Real.sqrt M) (fun _ => Real.sqrt_nonneg M) hweakBound
  let σ' : ℕ → ℕ := fun n => σ (τ n)
  have hσ' : StrictMono σ' := hσ.comp hτ
  let D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
    H (i, j, k) z
  have hD2u : MemLp D2u 2 μ := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    apply memLp_pi_iff.mpr
    intro k
    simpa only [D2u] using Lp.memLp (H (i, j, k))
  have hUconv' := hUconv.comp hτ.tendsto_atTop
  have hDweak' : ∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 μ →
      Tendsto
        (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          spatialPartial (fun y => CKN.Leray.regR12Uε ρ b hb.2
            (εseq (σ' n)) y i) j z * w z)
        atTop (nhds (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          Du z i j * w z)) := by
    intro i j w hw
    simpa only [μ, εseq, σ', Function.comp_def] using
      (hDweak i j w hw).comp hτ.tendsto_atTop
  refine ⟨σ', hσ', u, Du, htrace, hLH, huMem, hDuMem, ?_, ?_, D2u, hD2u, ?_⟩
  · simpa only [μ, εseq, σ', Function.comp_def] using hUconv'
  · exact hDweak'
  · constructor
    · intro i j k w hw
      have hweak := hHweak (i, j, k) (hw.toLp w)
      have hsequence :
          (fun n => ∫ z, D2seq (τ n) z i j k * w z ∂μ) =
            fun n => inner ℝ (F (τ n) (i, j, k)) (hw.toLp w) := by
        funext n
        symm
        exact lps_scalar_lp_inner_integral_generic
          (hD2coord (τ n) i j k) hw
      have hlimit :
          inner ℝ (H (i, j, k)) (hw.toLp w) =
            ∫ z, D2u z i j k * w z ∂μ := by
        simpa only [D2u] using
          (lps_scalar_lp_inner_left_eq_integral (F := H (i, j, k)) hw)
      rw [show (fun n => ∫ z,
          spatialPartial (fun y => spatialPartial
            (fun x => CKN.Leray.regR12Velocity ρ
              (1 / ((σ' n : ℝ) + 1)) (by positivity) b hb.2 x i) j y) k z * w z
          ∂μ) = (fun n => ∫ z, D2seq (τ n) z i j k * w z ∂μ) by
            funext n
            congr 1
            ]
      rw [hsequence, ← hlimit]
      exact hweak
    · exact ⟨σ, hσ, hweakSlice, hrep⟩


end ESS.LPS

end
