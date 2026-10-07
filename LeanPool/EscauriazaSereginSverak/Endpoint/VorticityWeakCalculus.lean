/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityDivCurlEngine
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Calculus of weak spatial derivatives for the vorticity bootstrap

Differentiating a weak heat equation, the product rule for square-integrable fields with
square-integrable weak derivatives, uniqueness of weak derivatives, almost-everywhere convergent
subsequences and Fatou bounds, and the linearity and locality of backward mollification. These are
the weak-level steps of the bootstrap of `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Finitely many `L²`-convergent sequences have a common subsequence converging almost
everywhere. -/
theorem vorticity_exists_subseq_ae {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Finite ι] {f : ι → ℕ → α → ℝ} {F : ι → α → ℝ}
    (hf : ∀ i n, MemLp (f i n) 2 μ) (hF : ∀ i, MemLp (F i) 2 μ)
    (h : ∀ i, Tendsto (fun n => eLpNorm (f i n - F i) 2 μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f i (φ n) x) atTop (𝓝 (F i x)) := by
  let := Fintype.ofFinite ι
  let S : ℕ → α → ℝ := fun n x => ∑ i, |f i n x - F i x|
  have hSmem : ∀ i n, MemLp (fun x => |f i n x - F i x|) 2 μ := fun i n =>
    ((hf i n).sub (hF i)).abs
  have hS : Tendsto (fun n => eLpNorm (S n - 0) 2 μ) atTop (𝓝 0) := by
    have hbound : ∀ n, eLpNorm (S n - 0) 2 μ ≤ ∑ i, eLpNorm (f i n - F i) 2 μ := by
      intro n
      rw [sub_zero]
      calc
        eLpNorm (S n) 2 μ = eLpNorm (∑ i, fun x => |f i n x - F i x|) 2 μ := by
          congr 1
          funext x
          simp [S]
        _ ≤ ∑ i, eLpNorm (fun x => |f i n x - F i x|) 2 μ :=
          eLpNorm_sum_le (by norm_num)
        _ = ∑ i, eLpNorm (f i n - F i) 2 μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h := eLpNorm_norm (p := 2) (μ := μ) (f i n - F i)
            ((hf i n).sub (hF i)).aestronglyMeasurable
          simpa [Real.norm_eq_abs] using h
    have hsum : Tendsto (fun n => ∑ i, eLpNorm (f i n - F i) 2 μ) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => h i
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) hbound
  obtain ⟨φ, hφ, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hS).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with x hx i
  have hle : ∀ n, |f i (φ n) x - F i x| ≤ S (φ n) x := fun n =>
    Finset.single_le_sum (f := fun i => |f i (φ n) x - F i x|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
    simpa [Real.norm_eq_abs] using hle n) (by simpa using hx)

/-- Fatou's lemma for nonnegative integrands converging almost everywhere. -/
theorem vorticity_integral_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ} {G : α → ℝ} (hg0 : ∀ n x, 0 ≤ g n x) (hgi : ∀ n, Integrable (g n) μ)
    (hGm : AEStronglyMeasurable G μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    {K : ℝ} (hK : ∀ n, ∫ x, g n x ∂μ ≤ K) :
    Integrable G μ ∧ ∫ x, G x ∂μ ≤ K := by
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ G x := by
    filter_upwards [hlim] with x hx
    exact ge_of_tendsto' hx fun n => hg0 n x
  have hlin : ∫⁻ x, ENNReal.ofReal (G x) ∂μ ≤ ENNReal.ofReal K := by
    calc
      ∫⁻ x, ENNReal.ofReal (G x) ∂μ =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact (((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop :=
        lintegral_liminf_le' fun n => (hgi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal K := by
        refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn⟩ := hb.exists
        refine hn.trans ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hgi n)
          (Eventually.of_forall fun x => hg0 n x)]
        exact ENNReal.ofReal_le_ofReal (hK n)
  have hint : Integrable G μ := by
    refine ⟨hGm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hG0]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h := ofReal_integral_eq_lintegral_ofReal hint hG0
  have hK0 : 0 ≤ K := le_trans (integral_nonneg fun x => hg0 0 x) (hK 0)
  rw [← ENNReal.ofReal_le_ofReal_iff hK0, h]
  exact hlin

/-- Weak derivatives of the same function on an open set agree almost everywhere there. -/
theorem vorticity_weakPartial_unique {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {f g₁ g₂ : Vec3 × ℝ → ℝ} {j : Fin 3} (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, g₂ y * ψ y) :
    ∀ᵐ y ∂(volume.restrict W), g₁ y = g₂ y := by
  have hloc : LocallyIntegrableOn (fun y => g₁ y - g₂ y) W :=
    (hg₁.sub hg₂).locallyIntegrableOn
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hψc hψW => by
    have e₁ := h₁ ψ hψ hψc hψW
    have e₂ := h₂ ψ hψ hψc hψW
    have hi₁ : Integrable (fun y => g₁ y * ψ y) (volume.restrict W) := by
      obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
      exact Integrable.mul_bdd hg₁ hψ.continuous.aestronglyMeasurable.restrict
        (Eventually.of_forall hC)
    have hi₂ : Integrable (fun y => g₂ y * ψ y) (volume.restrict W) := by
      obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
      exact Integrable.mul_bdd hg₂ hψ.continuous.aestronglyMeasurable.restrict
        (Eventually.of_forall hC)
    have hdiff : ∫ y in W, (g₁ y - g₂ y) * ψ y = 0 := by
      have : (fun y => (g₁ y - g₂ y) * ψ y) = fun y => g₁ y * ψ y - g₂ y * ψ y := by
        funext y; ring
      rw [this, integral_sub hi₁ hi₂]
      linarith only [e₁, e₂]
    have hsupp : ∫ y, ψ y • (g₁ y - g₂ y) = ∫ y in W, (g₁ y - g₂ y) * ψ y := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1
        funext y
        rw [smul_eq_mul, mul_comm]
      · intro y hy
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψW h)), mul_zero]
    rw [hsupp, hdiff])
  rw [ae_restrict_iff' hW.measurableSet]
  filter_upwards [hzero] with y hy hyW
  exact sub_eq_zero.mp (hy hyW)

/-- The product of a square-integrable function with a bounded continuous function is square
integrable. -/
theorem vorticity_memLp_mul_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace α] [OpensMeasurableSpace α]
    {g φ : α → ℝ} (hg : MemLp g 2 μ) (hφ : Continuous φ) (hφb : ∃ C, ∀ x, ‖φ x‖ ≤ C) :
    MemLp (fun x => g x * φ x) 2 μ := by
  obtain ⟨C, hC⟩ := hφb
  have hφtop : MemLp φ ⊤ μ :=
    memLp_top_of_bound hφ.aestronglyMeasurable C (Eventually.of_forall hC)
  exact hg.mul hφtop

/-- The spatial derivative of a negated smooth function. -/
theorem vorticity_spatialPartial_neg {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun y : Vec3 × ℝ => -f y) j z = -spatialPartial f j z := by
  rw [spatialPartial_eq_product_fderiv (hf.neg.differentiable (by simp) z),
    spatialPartial_eq_product_fderiv (hf.differentiable (by simp) z), fderiv_fun_neg]
  rfl

/-- The spatial derivative of the heat operator applied to a smooth test is the heat operator
applied to the spatial derivative of the test. -/
theorem vorticity_spatialPartial_heatOperator {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (m : Fin 3) (y : Vec3 × ℝ) :
    spatialPartial (fun y : Vec3 × ℝ => -timePartial ψ y -
        ∑ j : Fin 3, spatialSecondPartial ψ j j y) m y =
      -timePartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) y -
        ∑ j : Fin 3, spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j j y := by
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => timePartial ψ y) :=
    CKN.contDiff_timePartial hψ
  have hS : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y) := fun j =>
    CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hψ j) j
  have hsumS : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 × ℝ => ∑ j : Fin 3, spatialSecondPartial ψ j j y) :=
    ContDiff.sum fun j _ => hS j
  have e1 : spatialPartial (fun y : Vec3 × ℝ => -timePartial ψ y -
        ∑ j : Fin 3, spatialSecondPartial ψ j j y) m y =
      spatialPartial (fun y : Vec3 × ℝ => -timePartial ψ y) m y -
        spatialPartial (fun y : Vec3 × ℝ => ∑ j : Fin 3, spatialSecondPartial ψ j j y) m y :=
    vorticity_spatialPartial_sub hT.neg hsumS m y
  have e2 : spatialPartial (fun y : Vec3 × ℝ => -timePartial ψ y) m y =
      -spatialPartial (fun y : Vec3 × ℝ => timePartial ψ y) m y :=
    vorticity_spatialPartial_neg hT m y
  have e3 : spatialPartial (fun y : Vec3 × ℝ => ∑ j : Fin 3, spatialSecondPartial ψ j j y) m y =
      ∑ j : Fin 3, spatialPartial (fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y) m y :=
    spatialPartial_finsetSum_at Finset.univ
      (fun j => fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y)
      (fun j _ => (hS j).differentiable (by simp) y) m
  have e4 : timePartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) y =
      spatialPartial (fun y : Vec3 × ℝ => timePartial ψ y) m y :=
    timePartial_spatialPartial_comm hψ y m
  have e5 : ∀ j : Fin 3,
      spatialPartial (fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y) m y =
        spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j j y := by
    intro j
    have h1 : spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ j y) j m y =
        spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ j y) m j y :=
      spatialSecondPartial_comm (CKN.spatialPartial_contDiff hψ j) y j m
    have h2 : (fun w : ParabolicPoint =>
        spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ j y) m w) =
        fun w : ParabolicPoint =>
          spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j w := by
      funext w
      exact spatialSecondPartial_comm hψ w j m
    have h3 : spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ j y) m j y =
        spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j j y := by
      unfold spatialSecondPartial
      exact congrArg (fun g : ParabolicPoint → ℝ => spatialPartial g j y) h2
    exact h1.trans h3
  rw [e1, e2, e3, e4, Finset.sum_congr rfl fun j _ => e5 j]

/-- Products of an integrable function with a smooth compactly supported function are
integrable. -/
theorem vorticity_integrableOn_mul_smooth {W : Set (Vec3 × ℝ)} {f φ : Vec3 × ℝ → ℝ}
    (hf : IntegrableOn f W) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun y => f y * φ y) W := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  exact Integrable.mul_bdd hf hφ.aestronglyMeasurable.restrict (Eventually.of_forall hC)

/-- Differentiating a weak heat equation in a spatial direction: if the solution and the source
have weak derivatives in that direction, the derivatives solve the weak heat equation with the
differentiated source. -/
theorem vorticityHeat_weak_deriv {W : Set (Vec3 × ℝ)} {w w' : Vec3 × ℝ → ℝ}
    {F F' : Fin 3 → Vec3 × ℝ → ℝ} {m : Fin 3}
    (hFi : ∀ j, IntegrableOn (F j) W) (hF'i : ∀ j, IntegrableOn (F' j) W)
    (heq : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y)
    (hw : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, w y * spatialPartial ψ m y = -∫ y in W, w' y * ψ y)
    (hF : ∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, F j y * spatialPartial ψ m y = -∫ y in W, F' j y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, w' y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W, ∑ j : Fin 3, F' j y * spatialPartial ψ j y := by
  intro ψ hψ hψc hψW
  -- the heat operator of the test
  set φ : Vec3 × ℝ → ℝ := fun y => -timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y
    with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (CKN.contDiff_timePartial hψ).neg.sub (ContDiff.sum fun j _ =>
      CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hψ j) j)
  have hφsupp : tsupport φ ⊆ tsupport ψ := by
    refine closure_minimal ?_ (isClosed_tsupport ψ)
    intro y hy
    by_contra hyψ
    apply hy
    have ht : timePartial ψ y = 0 := by
      by_contra h
      exact hyψ (CKN.tsupport_timePartial_subset ψ (subset_tsupport _ h))
    have hs : ∀ j : Fin 3, spatialSecondPartial ψ j j y = 0 := fun j =>
      CKN.spatialSecondPartial_eq_zero_off_tsupport hyψ j j
    simp only [φ, ht, hs, neg_zero, Finset.sum_const_zero, sub_zero]
  have hφc : HasCompactSupport φ :=
    hψc.isCompact.of_isClosed_subset (isClosed_tsupport _) hφsupp
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.spatialPartial_contDiff hψ m
  have hχc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.hasCompactSupport_spatialPartial hψc m
  have hχW : tsupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) ⊆ W :=
    (CKN.tsupport_spatialPartial_subset m).trans hψW
  -- step 1: move the derivative from w' to w
  have s1 : ∫ y in W, w' y * φ y = -∫ y in W, w y * spatialPartial φ m y := by
    have h := hw φ hφ hφc (hφsupp.trans hψW)
    linarith only [h]
  -- step 2: the heat operator commutes with the spatial derivative
  have s2 : ∫ y in W, w y * spatialPartial φ m y =
      ∫ y in W, w y * (-timePartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) y -
        ∑ j : Fin 3, spatialSecondPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j j y) := by
    congr 1
    funext y
    rw [show spatialPartial φ m y = _ from vorticity_spatialPartial_heatOperator hψ m y]
  -- step 3: the equation for the differentiated test
  have s3 := heq _ hχ hχc hχW
  -- step 4: commute the derivatives of the test in the source term
  have hpair : ∀ j : Fin 3, IntegrableOn
      (fun y => F j y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j y) W :=
    fun j => vorticity_integrableOn_mul_smooth (hFi j)
      (CKN.spatialPartial_contDiff hχ j).continuous (CKN.hasCompactSupport_spatialPartial hχc j)
  have hpair' : ∀ j : Fin 3, IntegrableOn (fun y => F' j y * spatialPartial ψ j y) W :=
    fun j => vorticity_integrableOn_mul_smooth (hF'i j)
      (CKN.spatialPartial_contDiff hψ j).continuous (CKN.hasCompactSupport_spatialPartial hψc j)
  have s4 : ∀ j : Fin 3,
      ∫ y in W, F j y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j y =
        -∫ y in W, F' j y * spatialPartial ψ j y := by
    intro j
    have hcomm : (fun y => F j y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j y) =
        fun y => F j y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ j y) m y := by
      funext y
      congr 1
      exact spatialSecondPartial_comm hψ y m j
    rw [hcomm]
    exact hF j _ (CKN.spatialPartial_contDiff hψ j) (CKN.hasCompactSupport_spatialPartial hψc j)
      ((CKN.tsupport_spatialPartial_subset j).trans hψW)
  have s5 : ∫ y in W, ∑ j : Fin 3,
      F j y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) j y =
        -∫ y in W, ∑ j : Fin 3, F' j y * spatialPartial ψ j y := by
    rw [integral_finsetSum _ fun j _ => hpair j, integral_finsetSum _ fun j _ => hpair' j,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => s4 j
  change ∫ y in W, w' y * φ y = _
  rw [s1, s2, s3, s5]
  ring

/-- The backward kernel balls of the points of a compact set lie in any fixed closed thickening
once the radius is small. -/
theorem vorticityBackBall_subset_cthickening {K : Set (Vec3 × ℝ)} {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : 6 * ε ≤ δ) {z : Vec3 × ℝ} (hz : z ∈ K) :
    Metric.closedBall (z - vorticityBackShift ε) ε ⊆ Metric.cthickening δ K := by
  intro y hy
  apply Metric.mem_cthickening_of_dist_le y z δ K hz
  have hshift : dist (z - vorticityBackShift ε) z = 5 * ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    simp only [vorticityBackShift, Prod.norm_def, norm_zero, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith only [hε])]
    exact max_eq_right (by linarith only [hε])
  have htri := dist_triangle y (z - vorticityBackShift ε) z
  rw [Metric.mem_closedBall] at hy
  linarith only [htri, hy, hshift, hεδ]

/-- The product rule for a spatial derivative of smooth space-time functions. -/
theorem vorticity_spatialPartial_mul {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun y : Vec3 × ℝ => f y * g y) j z =
      spatialPartial f j z * g z + f z * spatialPartial g j z := by
  rw [spatialPartial_eq_product_fderiv ((hf.mul hg).differentiable (by simp) z),
    spatialPartial_eq_product_fderiv (hf.differentiable (by simp) z),
    spatialPartial_eq_product_fderiv (hg.differentiable (by simp) z),
    fderiv_fun_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The product rule for weak spatial derivatives of square-integrable functions with
square-integrable weak derivatives on a bounded open set. -/
theorem vorticity_weakPartial_mul {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) {f g f' g' : Vec3 × ℝ → ℝ} {j : Fin 3}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W))
    (hf' : MemLp f' 2 (volume.restrict W)) (hg' : MemLp g' 2 (volume.restrict W))
    (hdf : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, f' y * ψ y)
    (hdg : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, g y * spatialPartial ψ j y = -∫ y in W, g' y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, f y * g y * spatialPartial ψ j y =
        -∫ y in W, (f' y * g y + f y * g' y) * ψ y := by
  intro ψ hψ hψc hψW
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWfin : volume W < ∞ := hWb.measure_lt_top
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWfin.ne
  have hfi : IntegrableOn f W := hf.integrable (by norm_num)
  have hf'i : IntegrableOn f' W := hf'.integrable (by norm_num)
  have hfloc : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hWm).2 hfi).locallyIntegrable
  have hf'loc : LocallyIntegrable (W.indicator f') (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hWm).2 hf'i).locallyIntegrable
  obtain ⟨δ, hδ, hδW⟩ := hψc.isCompact.exists_cthickening_subset_open hWo hψW
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii (show 0 < δ / 6 by positivity)
  set fn : ℕ → Vec3 × ℝ → ℝ := fun n => vorticityBackMollify W f (ε n) (hεpos n) with hfndef
  set gn : ℕ → Vec3 × ℝ → ℝ := fun n => vorticityBackMollify W f' (ε n) (hεpos n)
    with hgndef
  have hfn : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fn n) := fun n =>
    vorticityBackMollify_contDiff (hεpos n) hfloc
  have hgn : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gn n) := fun n =>
    vorticityBackMollify_contDiff (hεpos n) hf'loc
  have hcomm : ∀ n, ∀ z ∈ tsupport ψ, spatialPartial (fn n) j z = gn n z := by
    intro n z hz
    exact vorticityBackMollify_spatialPartial_of_weak hWo hfi hdf (hεpos n)
      ((vorticityBackBall_subset_cthickening (hεpos n)
        (by have := hεle n; linarith only [this]) hz).trans hδW)
  -- bounded smooth functions
  have hbdd : ∀ φ : Vec3 × ℝ → ℝ, Continuous φ → HasCompactSupport φ → ∃ C, ∀ x, ‖φ x‖ ≤ C :=
    fun φ hφ hφc => hφ.bounded_above_of_compact_support hφc
  have hdψ : Continuous (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    (CKN.spatialPartial_contDiff hψ j).continuous
  have hdψc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    CKN.hasCompactSupport_spatialPartial hψc j
  -- the identity for each approximation
  have hstep : ∀ n, ∫ y in W, fn n y * (g y * spatialPartial ψ j y) =
      -(∫ y in W, fn n y * (g' y * ψ y)) - ∫ y in W, gn n y * (g y * ψ y) := by
    intro n
    have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun y => fn n y * ψ y) := (hfn n).mul hψ
    have hprodc : HasCompactSupport (fun y => fn n y * ψ y) := hψc.mul_left
    have hprodW : tsupport (fun y => fn n y * ψ y) ⊆ W :=
      (tsupport_mul_subset_right).trans hψW
    have h := hdg (fun y : Vec3 × ℝ => fn n y * ψ y) hprod hprodc hprodW
    have hexp : ∀ y, g y * spatialPartial (fun y : Vec3 × ℝ => fn n y * ψ y) j y =
        gn n y * (g y * ψ y) + fn n y * (g y * spatialPartial ψ j y) := by
      intro y
      rw [vorticity_spatialPartial_mul (hfn n) hψ j y]
      by_cases hy : y ∈ tsupport ψ
      · rw [hcomm n y hy]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hy]
        ring
    have hi1 : IntegrableOn (fun y => gn n y * (g y * ψ y)) W := by
      have : IntegrableOn (fun y => g y * (gn n y * ψ y)) W :=
        vorticity_integrableOn_mul_smooth (hg.integrable (by norm_num))
          ((hgn n).continuous.mul hψ.continuous) hψc.mul_left
      refine this.congr_fun (fun y _ => by ring) hWm
    have hi2 : IntegrableOn (fun y => fn n y * (g y * spatialPartial ψ j y)) W := by
      have : IntegrableOn (fun y => g y * (fn n y * spatialPartial ψ j y)) W :=
        vorticity_integrableOn_mul_smooth (hg.integrable (by norm_num))
          ((hfn n).continuous.mul hdψ) hdψc.mul_left
      refine this.congr_fun (fun y _ => by ring) hWm
    have hsplit : ∫ y in W, g y * spatialPartial (fun y : Vec3 × ℝ => fn n y * ψ y) j y =
        (∫ y in W, gn n y * (g y * ψ y)) + ∫ y in W, fn n y * (g y * spatialPartial ψ j y) :=
      (integral_congr_ae (Eventually.of_forall hexp)).trans (integral_add hi1 hi2)
    have hrhs : ∫ y in W, g' y * (fn n y * ψ y) = ∫ y in W, fn n y * (g' y * ψ y) := by
      congr 1
      funext y
      ring
    rw [hsplit, hrhs] at h
    linarith only [h]
  -- pass to the limit
  have hfnL2 : ∀ n, MemLp (fn n) 2 (volume.restrict W) := fun n =>
    vorticity_memLp_two_of_continuous_bounded (hfn n).continuous hWb
  have hgnL2 : ∀ n, MemLp (gn n) 2 (volume.restrict W) := fun n =>
    vorticity_memLp_two_of_continuous_bounded (hgn n).continuous hWb
  have hfconv := vorticityBackMollify_tendsto_restrict hWm hWm subset_rfl hf hεlim hεpos
  have hgconv := vorticityBackMollify_tendsto_restrict hWm hWm subset_rfl hf' hεlim hεpos
  have hL := vorticity_tendsto_integral_mul hfnL2 hf
    (vorticity_memLp_mul_bounded hg hdψ (hbdd _ hdψ hdψc)) hfconv
  have hR1 := vorticity_tendsto_integral_mul hfnL2 hf
    (vorticity_memLp_mul_bounded hg' hψ.continuous (hbdd _ hψ.continuous hψc)) hfconv
  have hR2 := vorticity_tendsto_integral_mul hgnL2 hf'
    (vorticity_memLp_mul_bounded hg hψ.continuous (hbdd _ hψ.continuous hψc)) hgconv
  have hlim := tendsto_nhds_unique hL ((hR1.neg.sub hR2).congr fun n => (hstep n).symm)
  have hi3 : IntegrableOn (fun y => f' y * g y * ψ y) W := by
    have : IntegrableOn (fun y => (f' y * g y) * ψ y) W :=
      vorticity_integrableOn_mul_smooth (hf'.integrable_mul hg) hψ.continuous hψc
    exact this
  have hi4 : IntegrableOn (fun y => f y * g' y * ψ y) W := by
    have : IntegrableOn (fun y => (f y * g' y) * ψ y) W :=
      vorticity_integrableOn_mul_smooth (hf.integrable_mul hg') hψ.continuous hψc
    exact this
  calc
    ∫ y in W, f y * g y * spatialPartial ψ j y =
        ∫ y in W, f y * (g y * spatialPartial ψ j y) := by
      congr 1
      funext y
      ring
    _ = -(∫ y in W, f y * (g' y * ψ y)) - ∫ y in W, f' y * (g y * ψ y) := hlim
    _ = -∫ y in W, (f' y * g y + f y * g' y) * ψ y := by
      have e : (fun y => (f' y * g y + f y * g' y) * ψ y) =
          fun y => f' y * g y * ψ y + f y * g' y * ψ y := by
        funext y
        ring
      rw [e, integral_add hi3 hi4]
      have e1 : ∫ y in W, f y * (g' y * ψ y) = ∫ y in W, f y * g' y * ψ y := by
        congr 1
        funext y
        ring
      have e2 : ∫ y in W, f' y * (g y * ψ y) = ∫ y in W, f' y * g y * ψ y := by
        congr 1
        funext y
        ring
      rw [e1, e2]
      ring

end ESS
