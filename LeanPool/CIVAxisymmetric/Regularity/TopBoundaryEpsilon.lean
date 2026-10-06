/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.ParabolicRescaling
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremA
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# ε-regularity at the blow-up time

The manuscript applies an ε-regularity criterion at points `(x, 0)` of the top boundary of
`Q = B(1) × (-1, 0)`, where the solution is not defined; the criterion available here,
`CKN.epsilonRegularityL3`, is an interior statement on an open space-time set and is therefore
used only at interior base points `(x, t)` with `t < 0`, at the fixed scale `r / 2`. Its
conclusion is quantitative and scale invariant, so the resulting bound does not depend on `t`,
and a countable family of the resulting half cylinders covers `B(x₀, r/2) × (-r²/4, 0)`. This is
the route to `eq:interior:regular` described in design note R3.

The dimensionless smallness quantity on a cylinder of radius `μ` is
`μ⁻² ∫ |u|³ + μ⁻² ∫ |π|^{3/2} + μ^{3q-5} ∫ |f|^q`: the velocity and pressure terms carry the same
power of `μ` and the force term does not, because `u`, `π` and `f` rescale by `μ`, `μ²` and `μ³`
while the cylinder has measure `μ⁵`. The hypothesis below is the single integral
`∫ (|u|³ + |π|^{3/2} + μ^{3q-3} |f|^q) ≤ ε₀ μ²`, which is exactly that quantity multiplied by
`μ²`, and exactly the hypothesis of `CKN.epsilonRegularityL3` for the rescaled fields.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- A real power of a product of nonnegative reals, read in `ℝ≥0∞`. -/
theorem ofReal_mul_rpow {c a e : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (he : 0 ≤ e) :
    ENNReal.ofReal (c * a) ^ e = ENNReal.ofReal (c ^ e) * ENNReal.ofReal a ^ e := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) he, Real.mul_rpow hc ha,
    ENNReal.ofReal_mul (Real.rpow_nonneg hc e), ENNReal.ofReal_rpow_of_nonneg ha he]

/-- The integrand of the smallness hypothesis of `CKN.epsilonRegularityL3` for the fields
rescaled by `μ` at `z₀` equals `μ³` times the integrand of the smallness hypothesis at scale `μ`,
evaluated at the rescaled point. The three powers `μ`, `μ²`, `μ³` of `CKN.rescaleVelocity`,
`CKN.rescalePressure` and `CKN.rescaleForce` contribute `μ³`, `μ³` and `μ^{3q}`, and the factor
`μ^{3q-3}` on the force term is what makes the three contributions share the factor `μ³`. -/
theorem rescaled_smallness_integrand {μ q : ℝ} (hμ : 0 < μ) (hq : 0 ≤ q)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |rescalePressure μ z₀ p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ z₀ f z)) ^ q =
      ENNReal.ofReal (μ ^ (3 : ℝ)) *
        (ENNReal.ofReal (vec3EuclideanNorm (u (scalingParabolic μ z₀ z))) ^ (3 : ℝ) +
          ENNReal.ofReal |p (scalingParabolic μ z₀ z)| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (μ ^ (3 * q - 3)) *
            ENNReal.ofReal (vec3EuclideanNorm (f (scalingParabolic μ z₀ z))) ^ q) := by
  have hμ0 : (0 : ℝ) ≤ μ := hμ.le
  have hvel : vec3EuclideanNorm (rescaleVelocity μ z₀ u z) =
      μ * vec3EuclideanNorm (u (scalingParabolic μ z₀ z)) := by
    change vec3EuclideanNorm (μ • u (scalingParabolic μ z₀ z)) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos hμ]
  have hpre : |rescalePressure μ z₀ p z| = μ ^ 2 * |p (scalingParabolic μ z₀ z)| := by
    change |μ ^ 2 * p (scalingParabolic μ z₀ z)| = _
    rw [abs_mul, abs_of_pos (pow_pos hμ 2)]
  have hfor : vec3EuclideanNorm (rescaleForce μ z₀ f z) =
      μ ^ 3 * vec3EuclideanNorm (f (scalingParabolic μ z₀ z)) := by
    change vec3EuclideanNorm (μ ^ 3 • f (scalingParabolic μ z₀ z)) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos (pow_pos hμ 3)]
  have h32 : (μ ^ 2) ^ (3 / 2 : ℝ) = μ ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast μ 2, ← Real.rpow_mul hμ0]
    norm_num
  have h3q : (μ ^ 3) ^ q = μ ^ (3 : ℝ) * μ ^ (3 * q - 3) := by
    rw [← Real.rpow_natCast μ 3, ← Real.rpow_mul hμ0, ← Real.rpow_add hμ]
    norm_num
  rw [hvel, hpre, hfor,
    ofReal_mul_rpow hμ0 (vec3EuclideanNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 3),
    ofReal_mul_rpow (by positivity) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3 / 2),
    ofReal_mul_rpow (by positivity) (vec3EuclideanNorm_nonneg _) hq,
    h32, h3q, ENNReal.ofReal_mul (Real.rpow_nonneg hμ0 3)]
  ring


/-- ε-regularity at an interior base point, rescaled to an arbitrary radius: there are
universal `ε₀ > 0` and `C ≥ 0`, depending only on the force exponent `q`, such that if the
closed cylinder `B(x₀, μ) × [t₀ - μ², t₀]` lies in the domain and the dimensionless quantity
`μ⁻² ∫ (|u|³ + |π|^{3/2}) + μ^{3q-5} ∫ |f|^q` over `B(x₀, μ) × (t₀ - μ², t₀]` is at most `ε₀`,
then `|u| ≤ C / μ` almost everywhere on `B(x₀, μ/2) × (t₀ - μ²/4, t₀]`. This is
`CKN.epsilonRegularityL3` transported by `CKN.isSuitableWeakSolutionIntegrable_rescale`, with
the conversions `isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution` and
`isSuitableWeakSolution_of_integrable` between the two suitable-solution predicates; the
constants are
the `ε₀` and `C₄` of that theorem. -/
theorem ae_norm_le_of_small_L3_cylinder (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3) (z₀ : ParabolicPoint) (μ : ℝ), 0 < μ →
        IsSuitableWeakSolution Ω I q u Du p f →
        closure (parabolicCylinder z₀.1 z₀.2 μ) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder z₀.1 z₀.2 μ,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (μ ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
          ENNReal.ofReal (ε₀ * μ ^ 2) →
        ∀ᵐ z ∂(volume.restrict (parabolicCylinder z₀.1 z₀.2 (μ / 2))),
          vec3EuclideanNorm (u z) ≤ C / μ := by
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, hA⟩ := CKN.epsilonRegularityL3 q hq
  refine ⟨ε₀, hε₀, C₄, hC₄, ?_⟩
  intro Ω I u Du p f z₀ μ hμ hsol hclo hsmall
  have hq0 : (0 : ℝ) ≤ q := by linarith only [hq]
  have hμ0 : (0 : ℝ) ≤ μ := hμ.le
  have hsol' := isSuitableWeakSolution_of_integrable
    (CKN.isSuitableWeakSolutionIntegrable_rescale
      (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) z₀ hμ)
  have hfst : ∀ z : ParabolicPoint, (scalingParabolic μ z₀ z).1 - z₀.1 = μ • z.1 := by
    intro z
    change z₀.1 + μ • z.1 - z₀.1 = μ • z.1
    rw [add_sub_cancel_left]
  have hsnd : ∀ z : ParabolicPoint, (scalingParabolic μ z₀ z).2 = z₀.2 + μ ^ 2 * z.2 :=
    fun _ => rfl
  have hclo' : closure (parabolicCylinder 0 0 1) ⊆
      spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) := by
    rw [rescaledSpaceTimeSet_eq_preimage μ z₀ Ω I]
    intro z hz
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hz
    have hz1 : vec3EuclideanNorm (z.1 - (0 : Vec3)) ≤ 1 := hz.1
    have hz2 : z.2 ∈ Icc ((0 : ℝ) - 1 ^ 2) 0 := hz.2
    rw [sub_zero] at hz1
    refine hclo ?_
    rw [closure_parabolicCylinder hμ]
    refine ⟨?_, ?_⟩
    · change vec3EuclideanNorm ((scalingParabolic μ z₀ z).1 - z₀.1) ≤ μ
      rw [hfst z, vec3EuclideanNorm_smul, abs_of_pos hμ]
      nlinarith only [hz1, hμ, vec3EuclideanNorm_nonneg z.1]
    · change (scalingParabolic μ z₀ z).2 ∈ Icc (z₀.2 - μ ^ 2) z₀.2
      rw [hsnd z]
      have hμ2 : (0 : ℝ) < μ ^ 2 := pow_pos hμ 2
      have h1 : (-1 : ℝ) ≤ z.2 := by
        have := hz2.1
        norm_num at this
        linarith only [this]
      constructor
      · nlinarith only [h1, hμ2]
      · nlinarith only [hz2.2, hμ2]
  have hmeasmu : MeasurableSet (parabolicCylinder z₀.1 z₀.2 μ) :=
    measurableSet_parabolicCylinder _ _ _
  have hpre : scalingParabolic μ z₀ ⁻¹' parabolicCylinder z₀.1 z₀.2 μ =
      parabolicCylinder 0 0 1 := by
    have h := preimage_scalingParabolic_parabolicCylinder hμ z₀ 1
    rwa [mul_one] at h
  have hmu3 : ENNReal.ofReal (μ ^ (3 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmall' : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |rescalePressure μ z₀ p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ z₀ f z)) ^ q) ≤
      ENNReal.ofReal ε₀ := by
    have hcov := setLIntegral_comp_scalingParabolic hμ z₀ hmeasmu
      (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (μ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)
    rw [← hpre, lintegral_congr (fun z => rescaled_smallness_integrand hμ hq0 z₀ u p f z),
      lintegral_const_mul' _ _ hmu3, hcov]
    have hconst : ENNReal.ofReal (μ ^ (3 : ℝ)) *
        (ENNReal.ofReal (μ⁻¹ ^ 5) * ENNReal.ofReal (ε₀ * μ ^ 2)) = ENNReal.ofReal ε₀ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.rpow_nonneg hμ0 3)]
      congr 1
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [← hconst]
    gcongr
  obtain ⟨w, hw, hholder, -⟩ := hA _ _ _ _ _ _ hsol' hclo' hsmall'
  obtain ⟨Bc, Kc, hBc, hKc, hBK, hbdd, -⟩ := hholder
  have hhalf : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (1 / 2)) :=
    measurableSet_parabolicCylinder _ _ _
  have hae : ∀ᵐ z ∂(volume.restrict (parabolicCylinder (0 : Vec3) 0 (1 / 2))),
      vec3EuclideanNorm (u (scalingParabolic μ z₀ z)) ≤ C₄ / μ := by
    filter_upwards [hw, ae_restrict_mem hhalf] with z hz hzmem
    have h1 : vec3EuclideanNorm (rescaleVelocity μ z₀ u z) ≤ C₄ := by
      rw [← hz]
      exact (hbdd z (subset_closure hzmem)).trans (by linarith only [hKc, hBK])
    rw [show vec3EuclideanNorm (rescaleVelocity μ z₀ u z) =
        μ * vec3EuclideanNorm (u (scalingParabolic μ z₀ z)) by
      change vec3EuclideanNorm (μ • u (scalingParabolic μ z₀ z)) = _
      rw [vec3EuclideanNorm_smul, abs_of_pos hμ]] at h1
    rw [le_div_iff₀ hμ]
    linarith only [h1]
  have hpre2 : scalingParabolic μ z₀ ⁻¹' parabolicCylinder z₀.1 z₀.2 (μ / 2) =
      parabolicCylinder 0 0 (1 / 2) := by
    have h := preimage_scalingParabolic_parabolicCylinder hμ z₀ (1 / 2)
    rwa [show μ * (1 / 2) = μ / 2 by ring] at h
  refine ae_restrict_of_ae_restrict_comp_scalingParabolic hμ z₀
    (measurableSet_parabolicCylinder _ _ _) ?_
  rw [hpre2]
  exact hae

/-- ε-regularity at a point of the blow-up time: if the dimensionless `L³` quantity of
`CKN.epsilonRegularityL3` is small on the backward cylinder `B(x₀, r) × (-r², 0)`, then `u` is
bounded by `K / r` almost everywhere on `B(x₀, r/2) × (-r²/4, 0)`, for universal `ε₀ > 0` and
`K ≥ 0` depending only on the force exponent `q`. The solution need not be defined at the top
time `t = 0`: the bound is obtained from `ae_norm_le_of_small_L3_cylinder` at the interior base
points `(x, t)` with `t < 0` at the single scale `r / 2`, and a countable family of the resulting
half cylinders covers `B(x₀, r/2) × (-r²/4, 0)`. Design note R3. -/
theorem bounded_of_small_L3_top (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3) (x₀ : Vec3) (r : ℝ), 0 < r →
        IsSuitableWeakSolution Ω I q u Du p f →
        vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0 ⊆ spaceTimeSet Ω I →
        (∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
          ENNReal.ofReal (ε₀ * r ^ 2) →
        ∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0)),
          vec3EuclideanNorm (u z) ≤ K / r := by
  obtain ⟨ε₀, hε₀, C, hC, hone⟩ := ae_norm_le_of_small_L3_cylinder q hq
  refine ⟨ε₀ / 4, by positivity, 2 * C, by positivity, ?_⟩
  intro Ω I u Du p f x₀ r hr hsol hQ hsmall
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr 2
  have hq3 : (0 : ℝ) ≤ 3 * q - 3 := by linarith only [hq]
  have hmeasU : MeasurableSet
      (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint) :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  -- every base point of the top half cylinder carries a full cylinder of radius `r / 2`
  have hsub : ∀ w ∈ (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint),
      closure (parabolicCylinder w.1 w.2 (r / 2)) ⊆ vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0 := by
    intro w hw z hz
    rw [closure_parabolicCylinder (by positivity : (0 : ℝ) < r / 2)] at hz
    have hz1 : vec3EuclideanNorm (z.1 - w.1) ≤ r / 2 := hz.1
    have hz2 : z.2 ∈ Icc (w.2 - (r / 2) ^ 2) w.2 := hz.2
    have hw1 : vec3EuclideanNorm (w.1 - x₀) < r / 2 := hw.1
    have hw2 : w.2 ∈ Ioo (-(r ^ 2) / 4) 0 := hw.2
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (z.1 - x₀) < r
      have htri : vec3EuclideanNorm (z.1 - x₀) ≤
          vec3EuclideanNorm (z.1 - w.1) + vec3EuclideanNorm (w.1 - x₀) := by
        rw [show z.1 - x₀ = (z.1 - w.1) + (w.1 - x₀) by abel]
        exact vec3EuclideanNorm_add_le _ _
      linarith only [htri, hz1, hw1]
    · linarith only [hz2.1, hw2.1, hr2]
    · linarith only [hz2.2, hw2.2]
  -- the smallness hypothesis descends to every such cylinder
  have hsmallw : ∀ w ∈ (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint),
      (∫⁻ z in parabolicCylinder w.1 w.2 (r / 2),
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal ((r / 2) ^ (3 * q - 3)) *
              ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
        ENNReal.ofReal (ε₀ * (r / 2) ^ 2) := by
    intro w hw
    have hpow : ENNReal.ofReal ((r / 2) ^ (3 * q - 3)) ≤ ENNReal.ofReal (r ^ (3 * q - 3)) :=
      ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by positivity) (by linarith only [hr]) hq3)
    have hconst : ENNReal.ofReal (ε₀ / 4 * r ^ 2) = ENNReal.ofReal (ε₀ * (r / 2) ^ 2) := by
      congr 1
      ring
    calc (∫⁻ z in parabolicCylinder w.1 w.2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal ((r / 2) ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)
        ≤ ∫⁻ z in parabolicCylinder w.1 w.2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
          lintegral_mono fun z => by gcongr
      _ ≤ ∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
          lintegral_mono_set ((parabolicCylinder_subset_closure _ _ _).trans (hsub w hw))
      _ ≤ ENNReal.ofReal (ε₀ / 4 * r ^ 2) := hsmall
      _ = ENNReal.ofReal (ε₀ * (r / 2) ^ 2) := hconst
  -- the bound at one base point
  have hpt : ∀ w ∈ (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint),
      ∀ᵐ z ∂(volume.restrict (parabolicCylinder w.1 w.2 (r / 4))),
        vec3EuclideanNorm (u z) ≤ 2 * C / r := by
    intro w hw
    have h := hone Ω I u Du p f w (r / 2) (by positivity) hsol
      ((hsub w hw).trans hQ) (hsmallw w hw)
    rw [show r / 2 / 2 = r / 4 by ring, show C / (r / 2) = 2 * C / r by
      field_simp] at h
    exact h
  -- a countable family of such cylinders covers the top half cylinder
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Vec3
  have hJc : ((D ×ˢ Set.range ((↑) : ℚ → ℝ)) ∩
      (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0) : Set ParabolicPoint).Countable :=
    Set.Countable.mono Set.inter_subset_left (hDc.prod (Set.countable_range _))
  have hcover : (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint) ⊆
      ⋃ w ∈ ((D ×ˢ Set.range ((↑) : ℚ → ℝ)) ∩
        (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0) : Set ParabolicPoint),
        parabolicCylinder w.1 w.2 (r / 4) := by
    intro z hz
    have hz1 : vec3EuclideanNorm (z.1 - x₀) < r / 2 := hz.1
    have hz2 : z.2 ∈ Ioo (-(r ^ 2) / 4) 0 := hz.2
    have hδpos : 0 < min (r / 4) (r / 2 - vec3EuclideanNorm (z.1 - x₀)) :=
      lt_min (by positivity) (by linarith only [hz1])
    obtain ⟨x, hxb, hxD⟩ := hDd.inter_open_nonempty
      (vec3Ball z.1 (min (r / 4) (r / 2 - vec3EuclideanNorm (z.1 - x₀))))
      (isOpen_vec3Ball _ _)
      ⟨z.1, by simpa [sub_self, vec3EuclideanNorm_zero] using hδpos⟩
    have hxb' : vec3EuclideanNorm (x - z.1) <
        min (r / 4) (r / 2 - vec3EuclideanNorm (z.1 - x₀)) := hxb
    have hxz : vec3EuclideanNorm (z.1 - x) =
        vec3EuclideanNorm (x - z.1) := by
      rw [show z.1 - x = -(x - z.1) by abel, vec3EuclideanNorm_neg]
    have hxball : vec3EuclideanNorm (x - x₀) < r / 2 := by
      have htri : vec3EuclideanNorm (x - x₀) ≤
          vec3EuclideanNorm (x - z.1) + vec3EuclideanNorm (z.1 - x₀) := by
        rw [show x - x₀ = (x - z.1) + (z.1 - x₀) by abel]
        exact vec3EuclideanNorm_add_le _ _
      have := min_le_right (r / 4) (r / 2 - vec3EuclideanNorm (z.1 - x₀))
      linarith only [htri, hxb', this]
    have hxr4 : vec3EuclideanNorm (z.1 - x) < r / 4 := by
      have := min_le_left (r / 4) (r / 2 - vec3EuclideanNorm (z.1 - x₀))
      rw [hxz]
      linarith only [hxb', this]
    obtain ⟨tq, htq1, htq2⟩ := exists_rat_btwn
      (show z.2 < min 0 (z.2 + (r / 4) ^ 2) from
        lt_min hz2.2 (by nlinarith only [hr]))
    refine Set.mem_iUnion₂.2 ⟨(x, (tq : ℝ)), ⟨⟨hxD, Set.mem_range_self _⟩, ⟨hxball, ?_, ?_⟩⟩,
      ?_, ?_, ?_⟩
    · exact lt_trans hz2.1 htq1
    · exact lt_of_lt_of_le htq2 (min_le_left _ _)
    · exact hxr4
    · have := lt_of_lt_of_le htq2 (min_le_right _ _)
      linarith only [this]
    · exact le_of_lt htq1
  exact ae_restrict_of_countable_cover hJc hmeasU
    (fun w _ => measurableSet_parabolicCylinder _ _ _) hcover
    (fun w hw => hpt w hw.2)

/-- `bounded_of_small_L3_top` with the two parts of the smallness hypothesis separated, each
with its own power of `r`: `∫ (|u|³ + |π|^{3/2}) ≤ ε₀ r²` on the backward cylinder, and
`∫ |f|^q ≤ ε₀ r^{5-3q}`. Splitting the single integral of `bounded_of_small_L3_top` uses
additivity of the lower Lebesgue integral, which is why the measurability of the velocity and of
the pressure on the cylinder is a hypothesis here; the solution class supplies it on every box
compactly contained in the domain. -/
theorem bounded_of_small_L3_top_split (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3) (x₀ : Vec3) (r : ℝ), 0 < r →
        IsSuitableWeakSolution Ω I q u Du p f →
        vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0 ⊆ spaceTimeSet Ω I →
        AEStronglyMeasurable (fun z : Vec3 × ℝ => u z)
          (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0)) →
        AEStronglyMeasurable (fun z : Vec3 × ℝ => p z)
          (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0)) →
        (∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal (ε₀ * r ^ 2) →
        (∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
          ENNReal.ofReal (ε₀ * r ^ (5 - 3 * q)) →
        ∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0)),
          vec3EuclideanNorm (u z) ≤ K / r := by
  obtain ⟨ε₀, hε₀, K, hK, hmain⟩ := bounded_of_small_L3_top q hq
  refine ⟨ε₀ / 2, by positivity, K, hK, ?_⟩
  intro Ω I u Du p f x₀ r hr hsol hQ hu hp h1 h2
  refine hmain Ω I u Du p f x₀ r hr hsol hQ ?_
  have hmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0)) := by
    refine AEMeasurable.add ?_ ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (ENNReal.measurable_ofReal.comp_aemeasurable
          (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
            hu.aemeasurable))
    · exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (ENNReal.measurable_ofReal.comp_aemeasurable
          (continuous_abs.measurable.comp_aemeasurable hp.aemeasurable))
  rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hforce : ENNReal.ofReal (r ^ (3 * q - 3)) * ENNReal.ofReal (ε₀ / 2 * r ^ (5 - 3 * q)) =
      ENNReal.ofReal (ε₀ / 2 * r ^ 2) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    congr 1
    rw [show r ^ (3 * q - 3) * (ε₀ / 2 * r ^ (5 - 3 * q)) =
        ε₀ / 2 * (r ^ (3 * q - 3) * r ^ (5 - 3 * q)) by ring, ← Real.rpow_add hr,
      show 3 * q - 3 + (5 - 3 * q) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsum : ENNReal.ofReal (ε₀ / 2 * r ^ 2) + ENNReal.ofReal (ε₀ / 2 * r ^ 2) =
      ENNReal.ofReal (ε₀ * r ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc (∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) +
        ENNReal.ofReal (r ^ (3 * q - 3)) *
          ∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q
      ≤ ENNReal.ofReal (ε₀ / 2 * r ^ 2) +
          ENNReal.ofReal (r ^ (3 * q - 3)) * ENNReal.ofReal (ε₀ / 2 * r ^ (5 - 3 * q)) := by
        gcongr
    _ = ENNReal.ofReal (ε₀ * r ^ 2) := by rw [hforce, hsum]

/-- The everywhere form of `bounded_of_small_L3_top` for a continuous representative: on the
open set `B(x₀, r/2) × (-r²/4, 0)` an almost-everywhere bound on a continuous function is a bound
at every point, because a nonempty open subset has positive measure. This is the form in which
`eq:interior:regular` is used. -/
theorem norm_le_of_small_L3_top_of_continuousOn (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3) (x₀ : Vec3) (r : ℝ), 0 < r →
        IsSuitableWeakSolution Ω I q u Du p f →
        vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0 ⊆ spaceTimeSet Ω I →
        (∫⁻ z in vec3Ball x₀ r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
          ENNReal.ofReal (ε₀ * r ^ 2) →
        ContinuousOn (fun z : Vec3 × ℝ => u z)
          (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0) →
        ∀ z ∈ vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0,
          vec3EuclideanNorm (u z) ≤ K / r := by
  obtain ⟨ε₀, hε₀, K, hK, hmain⟩ := bounded_of_small_L3_top q hq
  refine ⟨ε₀, hε₀, K, hK, ?_⟩
  intro Ω I u Du p f x₀ r hr hsol hQ hsmall hcont z hz
  by_contra hcon
  rw [not_le] at hcon
  have hVopen : IsOpen (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set (Vec3 × ℝ)) :=
    (isOpen_vec3Ball _ _).prod isOpen_Ioo
  have hmeasV : MeasurableSet
      (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set ParabolicPoint) :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  have hWopen : IsOpen ((vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set (Vec3 × ℝ)) ∩
      (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w)) ⁻¹' Ioi (K / r)) :=
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_continuousOn
      hcont).isOpen_inter_preimage
      hVopen isOpen_Ioi
  have hWpos : 0 < volume ((vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0 : Set (Vec3 × ℝ)) ∩
      (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w)) ⁻¹' Ioi (K / r)) :=
    hWopen.measure_pos volume ⟨z, hz, hcon⟩
  have hnull := ae_iff.1 (hmain Ω I u Du p f x₀ r hr hsol hQ hsmall)
  have hnull' : volume ({a : ParabolicPoint | ¬ vec3EuclideanNorm (u a) ≤ K / r} ∩
      (vec3Ball x₀ (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0)) = 0 :=
    (Measure.restrict_apply' hmeasV).symm.trans hnull
  refine absurd (measure_mono_null ?_ hnull') hWpos.ne'
  rintro w ⟨hw1, hw2⟩
  exact ⟨not_le.2 hw2, hw1⟩

end CIV
