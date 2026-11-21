/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Radial
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Remark 4.3: projections of uniform laws on spheres

All computations go through polar coordinates (`Sphere.lintegral_polar`, from Mathlib's
`measurePreserving_homeomorphUnitSphereProd`) and the Gaussian representation of the uniform law
(`Sphere.lintegral_sphereUniform_one`): `∫ g dσ = ∫ g(x/|x|) γ(dx)`. The projection and the
stereographic projection are then computed by splitting `ℝ^{n+k} = ℝⁿ × ℝᵏ`
(`Sphere.lintegral_append`), one-dimensional substitutions, Tonelli and scaling.

The interface statement `sphereUniform_map_projFirst'` is false for `d = n + 2` (the density
`C (max (R² - |y|²) 0) ^ 0` equals `C` everywhere, see
`Sphere.sphereUniform_map_projFirst_counterexample`); the corrected statement, with the density
restricted to the ball, is `Sphere.sphereUniform_map_projFirst_ball`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

namespace Sphere

open Set ProbabilityTheory

/-- Polar coordinates: integral of `G(x/|x|) φ(|x|)`. -/
theorem lintegral_polar {d : ℕ} (hd : 1 ≤ d) (G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hG : Measurable G) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, G (‖x‖⁻¹ • x) * φ ‖x‖ =
      (∫⁻ ω, G ω ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * φ r := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x ↦ G (‖x‖⁻¹ • x) * φ ‖x‖
  have hmp :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).measurePreserving_homeomorphUnitSphereProd
  calc ∫⁻ x, F x = ∫⁻ x in {(0 : EuclideanSpace ℝ (Fin d))}ᶜ, F x := by
        rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))),
          F (x : EuclideanSpace ℝ (Fin d)) ∂(volume.comap Subtype.val) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl F).symm
    _ = ∫⁻ p, G p.1 * φ p.2 ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1))) := by
        rw [← hmp.lintegral_comp_emb (Homeomorph.measurableEmbedding _)]
        congr 1 with x
        simp [F]
    _ = _ := by
        rw [lintegral_prod_mul (f := fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦ G ω)
          (g := fun r : Ioi (0 : ℝ) ↦ φ r) (hG.comp measurable_subtype_coe).aemeasurable
          (hφ.comp measurable_subtype_coe).aemeasurable, finrank_euclideanSpace_fin,
          Measure.volumeIoiPow,
          lintegral_withDensity_eq_lintegral_mul (Measure.comap Subtype.val volume)
            (f := fun r : Ioi (0 : ℝ) ↦ ENNReal.ofReal (r.1 ^ (d - 1))) (by fun_prop)
            (g := fun r : Ioi (0 : ℝ) ↦ φ r) (hφ.comp measurable_subtype_coe)]
        congr 1
        simp only [Pi.mul_apply]
        exact lintegral_subtype_comap measurableSet_Ioi (fun r ↦ ENNReal.ofReal (r ^ (d - 1)) * φ r)


/-- The radial profile of the standard Gaussian density on `ℝᵈ`. -/
noncomputable def gaussProfile (d : ℕ) (r : ℝ) : ℝ := (√(2 * π))⁻¹ ^ d * rexp (-r ^ 2 / 2)

lemma prod_gaussianPDFReal {d : ℕ} (v : Fin d → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (v i) =
      gaussProfile d ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  simp only [gaussianPDFReal, gaussProfile, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.prod_const, Finset.sum_div, neg_div, Finset.sum_neg_distrib]

lemma pi_gaussianReal {d : ℕ} :
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1) =
      volume.withDensity (fun v : Fin d → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (v i))) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (univ.pi s).indicator
        (fun v : Fin d → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (v i)))
      = fun v ↦ ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (v i)) := by
    ext v
    by_cases hv : v ∈ univ.pi s
    · rw [indicator_of_mem hv]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [indicator_of_mem (hv i (mem_univ i))]
    · rw [indicator_of_notMem hv]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hv
      obtain ⟨i, hi⟩ := hv
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _), ENNReal.ofReal_zero]
  have hint :
      Integrable (fun v : Fin d → ℝ ↦ ∏ i, (s i).indicator (gaussianPDFReal 0 1) (v i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun i ↦ (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [hind, ← ofReal_integral_eq_lintegral_ofReal hint
    (.of_forall fun v ↦ Finset.prod_nonneg fun i _ ↦
      indicator_nonneg (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x) _),
    volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ ↦ integral_nonneg fun x ↦
        indicator_nonneg (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x) _)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

lemma lintegral_stdGaussian {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x, h x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫⁻ x, h x * ENNReal.ofReal (gaussProfile d ‖x‖) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map hh (by fun_prop), pi_gaussianReal,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (g := fun v : Fin d → ℝ ↦ h (WithLp.toLp 2 v)) (hh.comp (by fun_prop)),
    ← (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  congr 1 with v
  simp only [Pi.mul_apply, prod_gaussianPDFReal, mul_comm]


/-- Integrals against the uniform law on the sphere of radius `R`. -/
lemma lintegral_sphereUniform (d : ℕ) (R : ℝ) {h : E d → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h x ∂(sphereUniform d R) =
      ((volume : Measure (E d)).toSphere univ)⁻¹ *
        ∫⁻ ω, h (R • (ω : E d)) ∂(volume : Measure (E d)).toSphere := by
  rw [sphereUniform, lintegral_smul_measure, lintegral_map hh (by fun_prop), smul_eq_mul]

lemma toSphere_univ_ne_zero {d : ℕ} (hd : 1 ≤ d) :
    (volume : Measure (E d)).toSphere univ ≠ 0 := by
  have := Radial.nontrivial_E hd
  exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)

lemma toSphere_univ_ne_top (d : ℕ) : (volume : Measure (E d)).toSphere univ ≠ ∞ :=
  measure_ne_top _ _

/-- Polar coordinates in terms of the uniform law on the unit sphere. -/
lemma lintegral_polar_sphereUniform {d : ℕ} (hd : 1 ≤ d) {h : E d → ℝ≥0∞} (hh : Measurable h)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, h (‖x‖⁻¹ • x) * φ ‖x‖ =
      (volume : Measure (E d)).toSphere univ * (∫⁻ x, h x ∂(sphereUniform d 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * φ r := by
  rw [lintegral_polar hd h hh φ hφ, lintegral_sphereUniform d 1 hh, ← mul_assoc,
    ENNReal.mul_inv_cancel (toSphere_univ_ne_zero hd) (toSphere_univ_ne_top d), one_mul]
  simp only [one_smul]

lemma piCongrLeft_sumPiEquivProdPi_symm {n k : ℕ} (y : Fin n → ℝ) (z : Fin k → ℝ) :
    MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k ↦ ℝ)).symm (y, z)) =
      Fin.append y z := by
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [Fin.append_left, MeasurableEquiv.coe_piCongrLeft]
    rw [show (Fin.castAdd k j) = finSumFinEquiv (Sum.inl j) by simp, Equiv.piCongrLeft_apply_apply]
    rfl
  · rw [Fin.append_right, MeasurableEquiv.coe_piCongrLeft]
    rw [show (Fin.natAdd n j) = finSumFinEquiv (Sum.inr j) by simp, Equiv.piCongrLeft_apply_apply]
    rfl

/-- Splitting `ℝ^{n+k} = ℝⁿ × ℝᵏ` in a Lebesgue integral. -/
lemma lintegral_append (n k : ℕ) {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ y : EuclideanSpace ℝ (Fin n), ∫⁻ z : EuclideanSpace ℝ (Fin k),
      F (WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (WithLp.ofLp z))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin (n + k))).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin (n + k) → ℝ)).measurableEmbedding,
    ← (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) finSumFinEquiv).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _),
    ← (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n ⊕ Fin k ↦ ℝ)).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
  rw [Measure.volume_eq_prod, lintegral_prod]
  swap
  · exact (hF.comp ((MeasurableEquiv.toLp 2 (Fin (n + k) → ℝ)).measurable.comp
      ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _)))).aemeasurable
  simp_rw [piCongrLeft_sumPiEquivProdPi_symm]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  congr 1 with y
  rw [← (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding]


/-- Scaling in `ℝⁿ`. -/
lemma lintegral_eq_smul_scale (n : ℕ) {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ENNReal.ofReal (r ^ n) * ∫⁻ u, f (r • u) := by
  rw [← lintegral_map hf (measurable_const_smul r), Measure.map_addHaar_smul _ hr.ne',
    lintegral_smul_measure, finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
    abs_of_pos (inv_pos.2 (pow_pos hr n)), ← ENNReal.ofReal_mul (pow_pos hr n).le,
    mul_inv_cancel₀ (pow_pos hr n).ne', ENNReal.ofReal_one, one_mul]

/-- Scaling on `(0, ∞)`. -/
lemma setLIntegral_Ioi_comp_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), f (c * t) = ENNReal.ofReal c⁻¹ * ∫⁻ r in Ioi (0 : ℝ), f r := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := fun t ↦ c * t)
    (f' := fun _ ↦ c) measurableSet_Ioi
    (fun t _ ↦ ((hasDerivAt_id t).const_mul c).hasDerivWithinAt.congr_deriv (mul_one c))
    (fun x _ y _ hxy ↦ mul_left_cancel₀ hc.ne' hxy) f
  rw [image_const_mul_Ioi_zero hc, abs_of_pos hc, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hc).le, inv_mul_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- The substitution `r = √(a² + s²)`. -/
lemma setLIntegral_Ioi_sqrt_subst {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (k - 1)) * F √(a ^ 2 + s ^ 2) =
      ∫⁻ r in Ioi a, ENNReal.ofReal ((r ^ 2 - a ^ 2) ^ (((k : ℝ) - 2) / 2) * r) * F r := by
  have hpos : ∀ s : ℝ, 0 < s → 0 < √(a ^ 2 + s ^ 2) := fun s hs ↦ Real.sqrt_pos.2 (by positivity)
  have hder : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s ↦ √(a ^ 2 + s ^ 2))
      (s / √(a ^ 2 + s ^ 2)) (Ioi 0) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ ↦ a ^ 2 + s ^ 2) (2 * s) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add (a ^ 2))
    have := (h1.sqrt (by have : (0 : ℝ) < s := hs; positivity)).hasDerivWithinAt (s := Ioi 0)
    convert this using 1
    field_simp
  have hinj : InjOn (fun s ↦ √(a ^ 2 + s ^ 2)) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have := congrArg (· ^ 2) hxy
    simp only [sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + x ^ 2),
      sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + y ^ 2)] at this
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    nlinarith
  have himg : (fun s ↦ √(a ^ 2 + s ^ 2)) '' Ioi (0 : ℝ) = Ioi a := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : (0 : ℝ) < s := hs
      change a < √(a ^ 2 + s ^ 2)
      exact (Real.lt_sqrt ha).2 (by nlinarith)
    · intro hr
      have hr' : a < r := hr
      refine ⟨√(r ^ 2 - a ^ 2), Real.sqrt_pos.2 (by nlinarith), ?_⟩
      change √(a ^ 2 + √(r ^ 2 - a ^ 2) ^ 2) = r
      rw [sq_sqrt (by nlinarith), add_sub_cancel, sqrt_sq (by linarith)]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
  have hs' : (0 : ℝ) < s := hs
  have hρ := hpos s hs'
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), sq_sqrt (by positivity),
    add_sub_cancel_left,
    abs_of_pos (div_pos hs' hρ)]
  congr 2
  have h2 : (s ^ 2) ^ (((k : ℝ) - 2) / 2) = s ^ (((k : ℝ) - 1) - 1) := by
    rw [← rpow_natCast, ← rpow_mul hs'.le]
    congr 1
    push_cast
    ring
  rw [h2, rpow_sub_one hs'.ne', ← rpow_natCast, Nat.cast_sub hk, Nat.cast_one]
  field_simp


lemma measurable_gaussProfile (d : ℕ) : Measurable fun r ↦ ENNReal.ofReal (gaussProfile d r) := by
  unfold gaussProfile; fun_prop

/-- The radial integral of the Gaussian profile. -/
lemma lintegral_gaussProfile {d : ℕ} (hd : 1 ≤ d) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (gaussProfile d r) =
      ((volume : Measure (E d)).toSphere univ)⁻¹ := by
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  have h1 := lintegral_stdGaussian (d := d) (fun _ ↦ 1) measurable_const
  rw [lintegral_const, measure_univ, one_mul] at h1
  have h2 := lintegral_polar hd (fun _ ↦ 1) measurable_const _ (measurable_gaussProfile d)
  rw [lintegral_const, one_mul] at h2
  rw [mul_comm]
  exact h2.symm.trans h1.symm

/-- If `Z ∼ 𝒩(0, I_d)` then `R Z/|Z|` is uniform on the sphere of radius `R`. -/
theorem stdGaussian_map_sphereUniform {d : ℕ} (hd : 1 ≤ d) (R : ℝ) :
    (ProbabilityTheory.stdGaussian (E d)).map (fun z => (R / ‖z‖) • z) = sphereUniform d R := by
  have hf : Measurable fun z : E d ↦ (R / ‖z‖) • z := by fun_prop
  refine Measure.ext_of_lintegral _ fun h hh ↦ ?_
  rw [lintegral_map hh hf, lintegral_stdGaussian (fun z ↦ h ((R / ‖z‖) • z)) (hh.comp hf),
    lintegral_sphereUniform d R hh]
  have hpt : ∀ z : E d, h ((R / ‖z‖) • z) = h (R • (‖z‖⁻¹ • z)) := fun z ↦ by
    rw [smul_smul, div_eq_mul_inv]
  simp_rw [hpt]
  rw [lintegral_polar hd (fun x ↦ h (R • x)) (hh.comp (measurable_const_smul R)) _
    (measurable_gaussProfile d), lintegral_gaussProfile hd, mul_comm]

/-- Integrals against the uniform law on the unit sphere, via the Gaussian representation. -/
lemma lintegral_sphereUniform_one {d : ℕ} (hd : 1 ≤ d) {g : E d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(sphereUniform d 1) =
      ∫⁻ x, g (‖x‖⁻¹ • x) * ENNReal.ofReal (gaussProfile d ‖x‖) := by
  have hf : Measurable fun z : E d ↦ (1 / ‖z‖) • z := by fun_prop
  rw [← stdGaussian_map_sphereUniform hd 1, lintegral_map hg hf,
    lintegral_stdGaussian (fun z ↦ g ((1 / ‖z‖) • z)) (hg.comp hf)]
  simp_rw [one_div]

lemma norm_append {n k : ℕ} (y : E n) (z : E k) :
    ‖(WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (WithLp.ofLp z)) : E (n + k))‖ =
      √(‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    sq_sqrt (by positivity), sq_sqrt (by positivity), Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

lemma measurable_projFirst {n d : ℕ} (h : n ≤ d) : Measurable (projFirst h) := by
  unfold projFirst; fun_prop

lemma projFirst_smul_append {n k : ℕ} (c : ℝ) (y : E n) (z : E k) :
    projFirst (Nat.le_add_right n k)
      (c • (WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (WithLp.ofLp z)) : E (n + k))) = c • y := by
  ext i
  simp only [projFirst, PiLp.smul_apply]
  rw [show Fin.castLE (Nat.le_add_right n k) i = Fin.castAdd k i from rfl]
  simp [Fin.append_left]

/-- The (unnormalized) density `(1 - |u|²)₊^{(k-2)/2}` of the projection on `ℝⁿ` of the uniform
law on the unit sphere of `ℝ^{n+k}`. -/
noncomputable def projWeight {n : ℕ} (k : ℕ) (u : E n) : ℝ≥0∞ :=
  if ‖u‖ < 1 then ENNReal.ofReal ((1 - ‖u‖ ^ 2) ^ (((k : ℝ) - 2) / 2)) else 0

lemma measurable_projWeight (n k : ℕ) : Measurable (projWeight (n := n) k) := by
  unfold projWeight
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
    measurable_const

lemma psi_smul {n k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (u : E n) {h : E n → ℝ≥0∞}
    (A : ℝ≥0∞) :
    (if ‖r • u‖ < r then ENNReal.ofReal ((r ^ 2 - ‖r • u‖ ^ 2) ^ (((k : ℝ) - 2) / 2) * r) *
      (h (r⁻¹ • r • u) * A) else 0) =
      ENNReal.ofReal (r ^ (k - 1)) * A * (projWeight k u * h u) := by
  rw [norm_smul, Real.norm_of_nonneg hr.le, inv_smul_smul₀ hr.ne', projWeight]
  by_cases hu : ‖u‖ < 1
  · have h1 : r * ‖u‖ < r := by nlinarith
    simp only [h1, hu, ↓reduceIte]
    have h2 : (r ^ 2 - (r * ‖u‖) ^ 2) ^ (((k : ℝ) - 2) / 2) * r =
        r ^ (k - 1) * (1 - ‖u‖ ^ 2) ^ (((k : ℝ) - 2) / 2) := by
      have h0 : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
      rw [show r ^ 2 - (r * ‖u‖) ^ 2 = r ^ 2 * (1 - ‖u‖ ^ 2) by ring,
        mul_rpow (by positivity) h0, ← rpow_natCast r 2, ← rpow_mul hr.le, ← rpow_natCast r (k - 1),
        Nat.cast_sub hk]
      rw [mul_comm _ r, ← mul_assoc, mul_comm r, ← rpow_add_one hr.ne']
      congr 2
      push_cast
      ring
    rw [h2, ENNReal.ofReal_mul (by positivity)]
    ring
  · have h1 : ¬ r * ‖u‖ < r := by
      intro h1; exact hu (by nlinarith)
    simp only [h1, hu, ↓reduceIte]
    simp

/-- Core computation for the projection of the uniform law on the sphere. -/
lemma lintegral_sphereUniform_projFirst {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {h : E n → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ x, h (projFirst (Nat.le_add_right n k) x) ∂(sphereUniform (n + k) 1) =
      (volume : Measure (E k)).toSphere univ * ((volume : Measure (E (n + k))).toSphere univ)⁻¹ *
        ∫⁻ u, projWeight k u * h u := by
  set φ : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal (gaussProfile (n + k) r) with hφdef
  have hφ : Measurable φ := measurable_gaussProfile _
  set e : ℝ := ((k : ℝ) - 2) / 2 with he
  let Ψ : E n → ℝ → ℝ≥0∞ := fun y r ↦
    if ‖y‖ < r then ENNReal.ofReal ((r ^ 2 - ‖y‖ ^ 2) ^ e * r) * (h (r⁻¹ • y) * φ r) else 0
  have hΨ : Measurable (Function.uncurry Ψ) := by
    refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) ?_ measurable_const
    refine Measurable.mul (by fun_prop) (Measurable.mul ?_ (hφ.comp measurable_snd))
    exact hh.comp (by fun_prop)
  calc ∫⁻ x, h (projFirst (Nat.le_add_right n k) x) ∂(sphereUniform (n + k) 1)
      = ∫⁻ y : E n, ∫⁻ z : E k, h ((√(‖y‖ ^ 2 + ‖z‖ ^ 2))⁻¹ • y) * φ √(‖y‖ ^ 2 + ‖z‖ ^ 2) := by
        rw [lintegral_sphereUniform_one (by omega) (g := fun x ↦ h (projFirst _ x))
          (hh.comp (measurable_projFirst _)), lintegral_append n k]
        · congr 1 with y
          congr 1 with z
          rw [projFirst_smul_append, norm_append]
        · exact (hh.comp ((measurable_projFirst _).comp (by fun_prop))).mul (hφ.comp (by fun_prop))
    _ = ∫⁻ y : E n, (volume : Measure (E k)).toSphere univ * ∫⁻ r, Ψ y r := by
        congr 1 with y
        have hF : Measurable fun s : ℝ ↦ h ((√(‖y‖ ^ 2 + s ^ 2))⁻¹ • y) * φ √(‖y‖ ^ 2 + s ^ 2) :=
          (hh.comp (by fun_prop)).mul (hφ.comp (by fun_prop))
        have := lintegral_polar hk (fun _ ↦ 1) measurable_const _ hF
        simp only [one_mul, lintegral_const] at this
        have hS := setLIntegral_Ioi_sqrt_subst hk (norm_nonneg y) (fun r ↦ h (r⁻¹ • y) * φ r)
        rw [this, hS, ← lintegral_indicator measurableSet_Ioi]
        congr 2 with r
    _ = (volume : Measure (E k)).toSphere univ * ∫⁻ r, ∫⁻ y, Ψ y r := by
        rw [lintegral_const_mul' _ _ (toSphere_univ_ne_top k),
          lintegral_lintegral_swap hΨ.aemeasurable]
    _ = (volume : Measure (E k)).toSphere univ * ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ (n + k - 1)) * φ r * ∫⁻ u, projWeight k u * h u := by
        rw [← lintegral_indicator measurableSet_Ioi]
        congr 1
        refine lintegral_congr fun r ↦ ?_
        by_cases hr : 0 < r
        · rw [indicator_of_mem (mem_Ioi.2 hr), lintegral_eq_smul_scale n hr (f := fun y ↦ Ψ y r)
            hΨ.of_uncurry_right]
          have hpt : ∀ u : E n, Ψ (r • u) r =
              ENNReal.ofReal (r ^ (k - 1)) * φ r * (projWeight k u * h u) := fun u ↦
            psi_smul hk hr u (h := h) (φ r)
          simp_rw [hpt]
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← pow_add]
          congr 4
          omega
        · rw [indicator_of_notMem (by simpa using hr)]
          refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y ↦ ?_)
          have : ¬ ‖y‖ < r := fun h' ↦ hr ((norm_nonneg y).trans_lt h')
          simp [Ψ, this]
    _ = _ := by
        have hm : Measurable fun r : ℝ ↦ ENNReal.ofReal (r ^ (n + k - 1)) * φ r :=
          (by fun_prop : Measurable fun r : ℝ ↦ ENNReal.ofReal (r ^ (n + k - 1))).mul hφ
        rw [lintegral_mul_const _ hm, lintegral_gaussProfile (by omega), mul_assoc]

/-- The total surface measure of the unit sphere of `ℝᵐ`. -/
lemma toSphere_univ_eq {m : ℕ} (hm : 1 ≤ m) :
    (volume : Measure (E m)).toSphere univ =
      ENNReal.ofReal (2 * (π ^ ((m : ℝ) / 2) / Gamma (m / 2))) := by
  rw [← ENNReal.ofReal_toReal (toSphere_univ_ne_top m), ← measureReal_def,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, Radial.real_vol_ball hm]

lemma lintegral_sphereUniform_eq_one (d : ℕ) (R : ℝ) {g : E d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(sphereUniform d R) = ∫⁻ x, g (R • x) ∂(sphereUniform d 1) := by
  rw [lintegral_sphereUniform d R hg, lintegral_sphereUniform d 1 (h := fun x ↦ g (R • x))
    (hg.comp (measurable_const_smul R))]
  simp only [one_smul]

lemma projFirst_smul {n d : ℕ} (h : n ≤ d) (c : ℝ) (x : E d) :
    projFirst h (c • x) = c • projFirst h x := by
  ext i
  simp [projFirst]

/-- The density of the projection, pointwise. -/
lemma projDensity_eq {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {R : ℝ} (hR : 0 < R) (u : E n) :
    (volume : Measure (E k)).toSphere univ * ((volume : Measure (E (n + k))).toSphere univ)⁻¹ *
      projWeight k u =
    ENNReal.ofReal (R ^ n) * ENNReal.ofReal ((ball (0 : E n) R).indicator (fun y ↦
      Gamma (((n + k : ℕ) : ℝ) / 2) / (π ^ ((n : ℝ) / 2) * Gamma ((((n + k : ℕ) : ℝ) - n) / 2) *
        R ^ (((n + k : ℕ) : ℝ) - 2)) *
        (R ^ 2 - ‖y‖ ^ 2) ^ ((((n + k : ℕ) : ℝ) - n - 2) / 2)) (R • u)) := by
  have hGk : 0 < Gamma ((k : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hGd : 0 < Gamma (((n + k : ℕ) : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  rw [toSphere_univ_eq hk, toSphere_univ_eq (by omega), ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity), projWeight]
  by_cases hu : ‖u‖ < 1
  · have hmem : R • u ∈ ball (0 : E n) R := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
    simp only [hu, ↓reduceIte, indicator_of_mem hmem]
    have h0 : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_smul, Real.norm_of_nonneg hR.le]
    have e1 : (((n + k : ℕ) : ℝ) - n) / 2 = (k : ℝ) / 2 := by push_cast; ring
    have e2 : (((n + k : ℕ) : ℝ) - n - 2) / 2 = ((k : ℝ) - 2) / 2 := by push_cast; ring
    have e3 : R ^ 2 - (R * ‖u‖) ^ 2 = R ^ 2 * (1 - ‖u‖ ^ 2) := by ring
    have e4 : (R ^ 2) ^ (((k : ℝ) - 2) / 2) = R ^ ((k : ℝ) - 2) := by
      rw [← rpow_natCast R 2, ← rpow_mul hR.le]
      congr 1
      push_cast
      ring
    have e5 : R ^ (((n + k : ℕ) : ℝ) - 2) = R ^ n * R ^ ((k : ℝ) - 2) := by
      rw [← rpow_natCast R n, ← rpow_add hR]
      congr 1
      push_cast
      ring
    have e6 : π ^ (((n + k : ℕ) : ℝ) / 2) = π ^ ((n : ℝ) / 2) * π ^ ((k : ℝ) / 2) := by
      rw [← rpow_add pi_pos]
      congr 1
      push_cast
      ring
    rw [e1, e2, e3, mul_rpow (by positivity) h0, e4, e5, e6]
    have : 0 < R ^ ((k : ℝ) - 2) := rpow_pos_of_pos hR _
    have : 0 < π ^ ((n : ℝ) / 2) := rpow_pos_of_pos pi_pos _
    have : 0 < π ^ ((k : ℝ) / 2) := rpow_pos_of_pos pi_pos _
    field_simp
  · have hmem : R • u ∉ ball (0 : E n) R := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hR.le]
      intro h1
      exact hu (by nlinarith)
    simp [hu, indicator_of_notMem hmem]

/-- **Remark 4.3**, corrected form: the first `n` coordinates of a uniform point on the sphere of
radius `R` of `ℝᵈ` have density `C (R² - |y|²)^{(d-n-2)/2}` on the ball of radius `R` (and `0`
outside), `C = Γ(d/2) / (π^{n/2} Γ((d-n)/2) R^{d-2})`. -/
theorem sphereUniform_map_projFirst_ball {n d : ℕ} (hn : 1 ≤ n) (hnd : n + 1 ≤ d) {R : ℝ}
    (hR : 0 < R) :
    (sphereUniform d R).map (projFirst (Nat.le_of_succ_le hnd)) =
      densityMeasure (fun y : E n => (ball (0 : E n) R).indicator (fun y ↦
        Gamma (d / 2) / (π ^ ((n : ℝ) / 2) * Gamma ((d - n) / 2) *
        R ^ ((d : ℝ) - 2)) * (R ^ 2 - ‖y‖ ^ 2) ^ (((d : ℝ) - n - 2) / 2)) y) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = n + k := ⟨d - n, by omega⟩
  have hk : 1 ≤ k := by omega
  refine Measure.ext_of_lintegral _ fun h hh ↦ ?_
  have hdens : Measurable fun y : E n ↦ ENNReal.ofReal ((ball (0 : E n) R).indicator (fun y ↦
      Gamma (((n + k : ℕ) : ℝ) / 2) / (π ^ ((n : ℝ) / 2) * Gamma ((((n + k : ℕ) : ℝ) - n) / 2) *
        R ^ (((n + k : ℕ) : ℝ) - 2)) *
        (R ^ 2 - ‖y‖ ^ 2) ^ ((((n + k : ℕ) : ℝ) - n - 2) / 2)) y) :=
    ((Measurable.indicator (by fun_prop) measurableSet_ball)).ennreal_ofReal
  rw [lintegral_map hh (measurable_projFirst _),
    lintegral_sphereUniform_eq_one _ R (g := fun x ↦ h (projFirst _ x))
      (hh.comp (measurable_projFirst _))]
  simp_rw [projFirst_smul]
  rw [lintegral_sphereUniform_projFirst hn hk (h := fun u ↦ h (R • u))
      (hh.comp (measurable_const_smul R)), densityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hdens hh,
    lintegral_eq_smul_scale n hR (hdens.mul hh),
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (toSphere_univ_ne_top k)
      (ENNReal.inv_ne_top.2 (toSphere_univ_ne_zero (by omega)))),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun u ↦ ?_
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← mul_assoc, projDensity_eq hn hk hR u]

/-- For `d = n + 2` the interface statement `sphereUniform_map_projFirst'` is false: its right-hand
side has density `C (max (R² - |y|²) 0) ^ 0 = C` on all of `ℝⁿ`, hence infinite mass. -/
theorem sphereUniform_map_projFirst_counterexample {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) :
    (sphereUniform (n + 2) R).map (projFirst (by omega : n ≤ n + 2)) ≠
      densityMeasure (fun y : E n => Gamma (((n + 2 : ℕ) : ℝ) / 2) / (π ^ ((n : ℝ) / 2) *
        Gamma ((((n + 2 : ℕ) : ℝ) - n) / 2) * R ^ (((n + 2 : ℕ) : ℝ) - 2)) *
        (max (R ^ 2 - ‖y‖ ^ 2) 0) ^ ((((n + 2 : ℕ) : ℝ) - n - 2) / 2)) := by
  intro heq
  have hU := congrArg (fun μ : Measure (E n) ↦ μ univ) heq
  have hl : (sphereUniform (n + 2) R).map (projFirst (by omega : n ≤ n + 2)) univ = 1 := by
    rw [Measure.map_apply (measurable_projFirst _) MeasurableSet.univ, preimage_univ,
      ← setLIntegral_one, Measure.restrict_univ,
      lintegral_sphereUniform _ R (h := fun _ ↦ 1) measurable_const, lintegral_const, one_mul,
      ENNReal.inv_mul_cancel (toSphere_univ_ne_zero (by omega)) (toSphere_univ_ne_top _)]
  have he : (((n + 2 : ℕ) : ℝ) - n - 2) / 2 = 0 := by push_cast; ring
  have hC : 0 < Gamma (((n + 2 : ℕ) : ℝ) / 2) / (π ^ ((n : ℝ) / 2) *
        Gamma ((((n + 2 : ℕ) : ℝ) - n) / 2) * R ^ (((n + 2 : ℕ) : ℝ) - 2)) := by
    have : 0 < Gamma ((((n + 2 : ℕ) : ℝ) - n) / 2) := Gamma_pos_of_pos (by push_cast; linarith)
    have : 0 < Gamma (((n + 2 : ℕ) : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    have : 0 < π ^ ((n : ℝ) / 2) := rpow_pos_of_pos pi_pos _
    have : 0 < R ^ (((n + 2 : ℕ) : ℝ) - 2) := rpow_pos_of_pos hR _
    positivity
  have := Radial.nontrivial_E hn
  rw [hl, densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hU
  simp only [he, rpow_zero, mul_one, lintegral_const] at hU
  rw [measure_univ_of_isAddLeftInvariant, ENNReal.mul_top (by simpa using hC)] at hU
  exact ENNReal.one_ne_top hU

/-- Integrals over `ℝ¹`. -/
lemma lintegral_E_one {F : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞} :
    ∫⁻ z, F z = ∫⁻ t : ℝ, F (WithLp.toLp 2 (fun _ ↦ t)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 1)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurableEmbedding,
    ← (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
  congr 1 with v
  congr 2
  ext i
  simp [Subsingleton.elim i default]

/-- The substitution `t = (a² - λ²)/(2λ)`, inverse of `λ = √(a² + t²) - t`. -/
lemma lintegral_stereo_subst {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ≥0∞) :
    ∫⁻ t, G t = ∫⁻ l in Ioi (0 : ℝ),
      ENNReal.ofReal ((a ^ 2 + l ^ 2) / (2 * l ^ 2)) * G ((a ^ 2 - l ^ 2) / (2 * l)) := by
  have hder : ∀ l ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun l ↦ (a ^ 2 - l ^ 2) / (2 * l))
      (-((a ^ 2 + l ^ 2) / (2 * l ^ 2))) (Ioi 0) l := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have h1 : HasDerivAt (fun l : ℝ ↦ a ^ 2 - l ^ 2) (-(2 * l)) l := by
      simpa using ((hasDerivAt_pow 2 l).const_sub (a ^ 2))
    have h2 : HasDerivAt (fun l : ℝ ↦ 2 * l) 2 l := by
      simpa using (hasDerivAt_id l).const_mul (2 : ℝ)
    have := (h1.div h2 (by positivity)).hasDerivWithinAt (s := Ioi 0)
    convert this using 1
    field_simp
    ring
  have hinj : InjOn (fun l : ℝ ↦ (a ^ 2 - l ^ 2) / (2 * l)) (Ioi 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    simp only at hxy
    rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
    have : (x - y) * (a ^ 2 + x * y) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith [mul_pos hx' hy']
  have himg : (fun l : ℝ ↦ (a ^ 2 - l ^ 2) / (2 * l)) '' Ioi 0 = univ := by
    refine eq_univ_of_forall fun t ↦ ⟨√(a ^ 2 + t ^ 2) - t, ?_, ?_⟩
    · have : |t| < √(a ^ 2 + t ^ 2) := by
        rw [← sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
      change 0 < √(a ^ 2 + t ^ 2) - t
      linarith [le_abs_self t]
    · have hs : √(a ^ 2 + t ^ 2) ^ 2 = a ^ 2 + t ^ 2 := sq_sqrt (by positivity)
      have : |t| < √(a ^ 2 + t ^ 2) := by
        rw [← sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
      have hpos : 0 < √(a ^ 2 + t ^ 2) - t := by linarith [le_abs_self t]
      simp only
      rw [div_eq_iff (by positivity)]
      nlinarith
  rw [← setLIntegral_univ, ← himg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi fun l hl ↦ ?_
  rw [abs_neg, abs_of_nonneg (by positivity)]


/-- The normalizing constant of the stereographic projection (Legendre duplication). -/
lemma stereo_const {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q) :
    q / 2 * ((q / 2)⁻¹) ^ (m + 1) * (2 * (π ^ (((m + 1 : ℕ) : ℝ) / 2) /
      Gamma (((m + 1 : ℕ) : ℝ) / 2)))⁻¹ =
    Gamma (((m + 1 : ℕ) : ℝ) - 1) / (π ^ ((((m + 1 : ℕ) : ℝ) - 1) / 2) *
      Gamma ((((m + 1 : ℕ) : ℝ) - 1) / 2)) * q ^ (-(((m + 1 : ℕ) : ℝ) - 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have c1 : ((m + 1 : ℕ) : ℝ) - 1 = m := by push_cast; ring
  have c2 : ((m + 1 : ℕ) : ℝ) / 2 = (m : ℝ) / 2 + 1 / 2 := by push_cast; ring
  rw [c1, c2]
  have hdup := Gamma_mul_Gamma_add_half ((m : ℝ) / 2)
  rw [show 2 * ((m : ℝ) / 2) = m by ring] at hdup
  have hG1 : 0 < Gamma ((m : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Gamma (m : ℝ) := Gamma_pos_of_pos hm'
  have hdup' : Gamma ((m : ℝ) / 2 + 1 / 2) =
      Gamma (m : ℝ) * (2 / 2 ^ m) * √π / Gamma ((m : ℝ) / 2) := by
    rw [eq_div_iff hG1.ne', mul_comm, hdup, rpow_sub two_pos, rpow_one, rpow_natCast]
  have hpi : π ^ ((m : ℝ) / 2 + 1 / 2) = π ^ ((m : ℝ) / 2) * √π := by
    rw [rpow_add pi_pos, sqrt_eq_rpow]
  rw [hdup', hpi, rpow_neg hq.le, rpow_natCast]
  have : 0 < π ^ ((m : ℝ) / 2) := rpow_pos_of_pos pi_pos _
  have : 0 < √π := sqrt_pos.2 pi_pos
  rw [inv_pow]
  field_simp
  rw [div_pow, pow_succ]
  field_simp
  ring

/-- Scaling of a power-weighted radial integral. -/
lemma lintegral_pow_comp_mul (m : ℕ) {c : ℝ} (hc : 0 < c) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ m) * φ (c * l) =
      ENNReal.ofReal (c⁻¹ ^ (m + 1)) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) * φ r := by
  have h1 := setLIntegral_Ioi_comp_mul hc
    (fun r ↦ ENNReal.ofReal (c⁻¹ ^ m) * (ENNReal.ofReal (r ^ m) * φ r))
  have h2 : ∀ l : ℝ, ENNReal.ofReal (c⁻¹ ^ m) * (ENNReal.ofReal ((c * l) ^ m) * φ (c * l)) =
      ENNReal.ofReal (l ^ m) * φ (c * l) := by
    intro l
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_pow, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hc.ne', one_pow, one_mul]
  simp only [h2] at h1
  rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), pow_succ']

lemma stereo_smul_append {m : ℕ} (c : ℝ) (y : E m) (t : ℝ) :
    (1 - (c • (WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (fun _ : Fin 1 ↦ t)) : E (m + 1)))
      (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1)
      (c • (WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (fun _ : Fin 1 ↦ t)) : E (m + 1))) =
    ((1 - c * t)⁻¹ * c) • y := by
  have := projFirst_smul_append c y (WithLp.toLp 2 (fun _ : Fin 1 ↦ t) : E 1)
  rw [this, smul_smul, PiLp.smul_apply, show Fin.last m = Fin.natAdd m (0 : Fin 1) from rfl,
    WithLp.ofLp_toLp, Fin.append_right, smul_eq_mul]

lemma norm_append_one {m : ℕ} (y : E m) (t : ℝ) :
    ‖(WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (fun _ : Fin 1 ↦ t)) : E (m + 1))‖ =
      √(‖y‖ ^ 2 + t ^ 2) := by
  rw [norm_append y (WithLp.toLp 2 (fun _ : Fin 1 ↦ t) : E 1),
    EuclideanSpace.norm_eq (WithLp.toLp 2 (fun _ : Fin 1 ↦ t) : E 1)]
  simp [sq_sqrt (sq_nonneg t)]

/-- Core computation for the stereographic projection of the uniform law on the unit sphere. -/
lemma lintegral_sphereUniform_stereo {m : ℕ} (hm : 1 ≤ m) {h : E m → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h ((1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x)
        ∂(sphereUniform (m + 1) 1) =
      ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖ ^ 2) / 2) *
        (ENNReal.ofReal ((((1 + ‖u‖ ^ 2) / 2)⁻¹) ^ (m + 1)) *
          ((volume : Measure (E (m + 1))).toSphere univ)⁻¹) * h u := by
  set φ : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal (gaussProfile (m + 1) r) with hφdef
  have hφ : Measurable φ := measurable_gaussProfile _
  have hS : Measurable fun x : E (m + 1) ↦
      (1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x := by
    have hcoord : Measurable fun x : E (m + 1) ↦ x (Fin.last m) := by fun_prop
    exact ((measurable_const.sub hcoord).inv).smul (measurable_projFirst _)
  let Ξ : E m → ℝ → ℝ≥0∞ := fun y l ↦ ENNReal.ofReal ((‖y‖ ^ 2 + l ^ 2) / (2 * l ^ 2)) *
    (h (l⁻¹ • y) * φ ((‖y‖ ^ 2 + l ^ 2) / (2 * l)))
  have hΞ : Measurable (Function.uncurry Ξ) := by
    refine Measurable.mul (by fun_prop) (Measurable.mul (hh.comp (by fun_prop))
      (hφ.comp (by fun_prop)))
  let Θ : E m → ℝ → ℝ≥0∞ := fun u l ↦ ENNReal.ofReal (l ^ m) *
    (ENNReal.ofReal ((1 + ‖u‖ ^ 2) / 2) * (h u * φ ((1 + ‖u‖ ^ 2) / 2 * l)))
  have hΘ : Measurable (Function.uncurry Θ) := by
    refine Measurable.mul (by fun_prop) (Measurable.mul (by fun_prop)
      (Measurable.mul (hh.comp measurable_fst) (hφ.comp (by fun_prop))))
  have h0 : ∀ᵐ y : E m, y ≠ 0 := by
    have := Radial.nontrivial_E hm
    rw [ae_iff]
    simp
  calc ∫⁻ x, h ((1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x)
        ∂(sphereUniform (m + 1) 1)
      = ∫⁻ y : E m, ∫⁻ t : ℝ, h (((1 - (√(‖y‖ ^ 2 + t ^ 2))⁻¹ * t)⁻¹ *
          (√(‖y‖ ^ 2 + t ^ 2))⁻¹) • y) * φ √(‖y‖ ^ 2 + t ^ 2) := by
        rw [lintegral_sphereUniform_one (by omega)
          (g := fun x ↦ h ((1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x))
          (hh.comp hS), lintegral_append m 1]
        · congr 1 with y
          rw [lintegral_E_one]
          congr 1 with t
          simp only
          rw [stereo_smul_append, norm_append_one]
        · exact (hh.comp (hS.comp (by fun_prop))).mul (hφ.comp (by fun_prop))
    _ = ∫⁻ y : E m, ∫⁻ l in Ioi (0 : ℝ), Ξ y l := by
        refine lintegral_congr_ae (h0.mono fun y hy ↦ ?_)
        have ha : 0 < ‖y‖ := norm_pos_iff.2 hy
        beta_reduce
        rw [lintegral_stereo_subst ha]
        refine setLIntegral_congr_fun measurableSet_Ioi fun l hl ↦ ?_
        have hl' : (0 : ℝ) < l := hl
        have hρ : √(‖y‖ ^ 2 + ((‖y‖ ^ 2 - l ^ 2) / (2 * l)) ^ 2) =
            (‖y‖ ^ 2 + l ^ 2) / (2 * l) := by
          rw [show ‖y‖ ^ 2 + ((‖y‖ ^ 2 - l ^ 2) / (2 * l)) ^ 2 =
            ((‖y‖ ^ 2 + l ^ 2) / (2 * l)) ^ 2 by field_simp; ring]
          exact sqrt_sq (by positivity)
        have hc : (1 - ((‖y‖ ^ 2 + l ^ 2) / (2 * l))⁻¹ * ((‖y‖ ^ 2 - l ^ 2) / (2 * l)))⁻¹ *
            ((‖y‖ ^ 2 + l ^ 2) / (2 * l))⁻¹ = l⁻¹ := by
          have : 0 < ‖y‖ ^ 2 + l ^ 2 := by positivity
          field_simp
          ring
        simp only [Ξ]
        rw [hρ, hc]
    _ = ∫⁻ l in Ioi (0 : ℝ), ∫⁻ y : E m, Ξ y l := lintegral_lintegral_swap hΞ.aemeasurable
    _ = ∫⁻ l in Ioi (0 : ℝ), ∫⁻ u : E m, Θ u l := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun l hl ↦ ?_
        have hl' : (0 : ℝ) < l := hl
        rw [lintegral_eq_smul_scale m hl' (f := fun y ↦ Ξ y l) hΞ.of_uncurry_right,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun u ↦ ?_
        simp only [Ξ, Θ]
        rw [inv_smul_smul₀ hl'.ne', norm_smul, Real.norm_of_nonneg hl'.le]
        have e1 : ((l * ‖u‖) ^ 2 + l ^ 2) / (2 * l ^ 2) = (1 + ‖u‖ ^ 2) / 2 := by
          field_simp; ring
        have e2 : ((l * ‖u‖) ^ 2 + l ^ 2) / (2 * l) = (1 + ‖u‖ ^ 2) / 2 * l := by
          field_simp; ring
        rw [e1, e2]
    _ = ∫⁻ u : E m, ∫⁻ l in Ioi (0 : ℝ), Θ u l :=
        lintegral_lintegral_swap (by exact (hΘ.comp measurable_swap).aemeasurable)
    _ = _ := by
        refine lintegral_congr fun u ↦ ?_
        have hc : 0 < (1 + ‖u‖ ^ 2) / 2 := by positivity
        simp only [Θ]
        have hpt : ∀ l : ℝ, ENNReal.ofReal (l ^ m) *
            (ENNReal.ofReal ((1 + ‖u‖ ^ 2) / 2) * (h u * φ ((1 + ‖u‖ ^ 2) / 2 * l))) =
            (ENNReal.ofReal ((1 + ‖u‖ ^ 2) / 2) * h u) *
              (ENNReal.ofReal (l ^ m) * φ ((1 + ‖u‖ ^ 2) / 2 * l)) := fun l ↦ by ring
        simp_rw [hpt]
        have hG := lintegral_gaussProfile (d := m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hG
        have hm' : Measurable fun l : ℝ ↦ ENNReal.ofReal (l ^ m) * φ ((1 + ‖u‖ ^ 2) / 2 * l) :=
          (by fun_prop : Measurable fun l : ℝ ↦ ENNReal.ofReal (l ^ m)).mul
            (hφ.comp (measurable_const_mul _))
        rw [lintegral_const_mul _ hm', lintegral_pow_comp_mul m hc φ, hG]
        ring

end Sphere

open Sphere Set

/-- **Remark 4.3.** If `X` is uniform on the sphere of radius `R` of `ℝᵈ`, then for
`1 ≤ n ≤ d-1`, `(X₁, …, X_n)` has density `C (R² - |y|²)₊^{(d-n-2)/2}` on `ℝⁿ`, with
`C = Γ(d/2) / (π^{n/2} Γ((d-n)/2) R^{d-2})`. -/
theorem sphereUniform_map_projFirst' {n d : ℕ} (hn : 1 ≤ n) (hnd : n + 1 ≤ d) {R : ℝ}
    (hR : 0 < R) :
    (sphereUniform d R).map (projFirst (Nat.le_of_succ_le hnd)) =
      densityMeasure (fun y : E n => (ball (0 : E n) R).indicator (fun y =>
        Gamma (d / 2) / (π ^ ((n : ℝ) / 2) * Gamma ((d - n) / 2) * R ^ ((d : ℝ) - 2)) *
          (R ^ 2 - ‖y‖ ^ 2) ^ (((d : ℝ) - n - 2) / 2)) y) :=
  Sphere.sphereUniform_map_projFirst_ball hn hnd hR

/-- **Remark 4.3.** If `Z ∼ 𝒩(0, I_d)` then `R Z/|Z|` is uniform on the sphere of radius `R`. -/
theorem stdGaussian_map_sphereUniform' {d : ℕ} (hd : 1 ≤ d) (R : ℝ) :
    (ProbabilityTheory.stdGaussian (E d)).map (fun z => (R / ‖z‖) • z) = sphereUniform d R :=
  Sphere.stdGaussian_map_sphereUniform hd R

/-- **Remark 4.3, stereographic projection.** If `X` is uniform on the unit sphere of `ℝᵈ`,
`d ≥ 2`, then its stereographic projection on `ℝ^{d-1}` has the full-space Barenblatt density
`Γ(d-1) / (π^{(d-1)/2} Γ((d-1)/2)) (1 + |y|²)^{-(d-1)}` (no extra radial weight). -/
theorem sphereUniform_map_stereoProj' {d : ℕ} (hd : 2 ≤ d) :
    (sphereUniform d 1).map (stereoProj (Nat.le_of_succ_le hd)) =
      densityMeasure (fun y : E (d - 1) => Gamma ((d : ℝ) - 1) /
        (π ^ (((d : ℝ) - 1) / 2) * Gamma (((d : ℝ) - 1) / 2)) * (1 + ‖y‖ ^ 2) ^ (-((d : ℝ) - 1)))
          := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hS : Measurable fun x : E (m + 1) ↦
      (1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x := by
    have hcoord : Measurable fun x : E (m + 1) ↦ x (Fin.last m) := by fun_prop
    exact ((measurable_const.sub hcoord).inv).smul (measurable_projFirst _)
  change (sphereUniform (m + 1) 1).map (fun x : E (m + 1) ↦
      ((1 - x (Fin.last m))⁻¹ • projFirst (Nat.le_add_right m 1) x : E m)) =
    densityMeasure (fun y : E m ↦ Gamma (((m + 1 : ℕ) : ℝ) - 1) /
      (π ^ ((((m + 1 : ℕ) : ℝ) - 1) / 2) * Gamma ((((m + 1 : ℕ) : ℝ) - 1) / 2)) *
        (1 + ‖y‖ ^ 2) ^ (-(((m + 1 : ℕ) : ℝ) - 1)))
  refine Measure.ext_of_lintegral _ fun h hh ↦ ?_
  rw [lintegral_map hh hS, Sphere.lintegral_sphereUniform_stereo hm hh, densityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hh]
  refine lintegral_congr fun u ↦ ?_
  congr 1
  have hq : 0 < 1 + ‖u‖ ^ 2 := by positivity
  rw [Sphere.toSphere_univ_eq (by omega), ← ENNReal.ofReal_inv_of_pos (by
      have : 0 < Gamma (((m + 1 : ℕ) : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
      have : 0 < π ^ (((m + 1 : ℕ) : ℝ) / 2) := rpow_pos_of_pos pi_pos _
      positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
    Sphere.stereo_const hm hq]

end Cutfast
