/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity

/-!
# Local tools for the exterior vorticity at the terminal face

Uniqueness of weak time derivatives, agreement of continuous representatives on overlapping
half-cylinders, a countable family of half-cylinders covering the exterior region, and finite
covers of bounded subsets of the exterior region (`lem:vorticity-top-extension`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Uniqueness of the weak time derivative. -/
theorem vorticity_weakTime_unique {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {f g₁ g₂ : Vec3 × ℝ → ℝ} (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * timePartial ψ y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * timePartial ψ y = -∫ y in W, g₂ y * ψ y) :
    ∀ᵐ y ∂(volume.restrict W), g₁ y = g₂ y := by
  have hloc : LocallyIntegrableOn (fun y => g₁ y - g₂ y) W :=
    (hg₁.sub hg₂).locallyIntegrableOn
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hψc hψW => by
    have e₁ := h₁ ψ hψ hψc hψW
    have e₂ := h₂ ψ hψ hψc hψW
    have hi₁ : Integrable (fun y => g₁ y * ψ y) (volume.restrict W) :=
      vorticity_integrableOn_mul_smooth hg₁ hψ.continuous hψc
    have hi₂ : Integrable (fun y => g₂ y * ψ y) (volume.restrict W) :=
      vorticity_integrableOn_mul_smooth hg₂ hψ.continuous hψc
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

/-- Two representatives, continuous on closed half-cylinders and almost everywhere equal to the
same function on the open half-cylinders, agree at every common point below or on the tops. -/
theorem vorticityTop_agree {ω₁ ω₂ h : Vec3 × ℝ → ℝ} {c₁ c₂ : Vec3 × ℝ}
    (hc₁ : ContinuousOn ω₁
      ({x : Vec3 | vec3EuclideanNorm (x - c₁.1) ≤ 1 / 2} ×ˢ Icc (c₁.2 - 1 / 4) c₁.2))
    (hc₂ : ContinuousOn ω₂
      ({x : Vec3 | vec3EuclideanNorm (x - c₂.1) ≤ 1 / 2} ×ˢ Icc (c₂.2 - 1 / 4) c₂.2))
    (hae₁ : ω₁ =ᵐ[volume.restrict (vec3Ball c₁.1 (1 / 2) ×ˢ Ioo (c₁.2 - 1 / 4) c₁.2)] h)
    (hae₂ : ω₂ =ᵐ[volume.restrict (vec3Ball c₂.1 (1 / 2) ×ˢ Ioo (c₂.2 - 1 / 4) c₂.2)] h)
    {x : Vec3} {t : ℝ} (hx₁ : vec3EuclideanNorm (x - c₁.1) < 1 / 2)
    (hx₂ : vec3EuclideanNorm (x - c₂.1) < 1 / 2) (ht₁ : t ∈ Ioc (c₁.2 - 1 / 4) c₁.2)
    (ht₂ : t ∈ Ioc (c₂.2 - 1 / 4) c₂.2) : ω₁ (x, t) = ω₂ (x, t) := by
  set O : Set (Vec3 × ℝ) := (vec3Ball c₁.1 (1 / 2) ×ˢ Ioo (c₁.2 - 1 / 4) c₁.2) ∩
    (vec3Ball c₂.1 (1 / 2) ×ˢ Ioo (c₂.2 - 1 / 4) c₂.2) with hOdef
  have hO : IsOpen O := (vorticityBox_isOpen _ _ _ _).inter (vorticityBox_isOpen _ _ _ _)
  have hOK₁ : O ⊆ {x : Vec3 | vec3EuclideanNorm (x - c₁.1) ≤ 1 / 2} ×ˢ
      Icc (c₁.2 - 1 / 4) c₁.2 := fun z hz =>
    ⟨show vec3EuclideanNorm (z.1 - c₁.1) ≤ 1 / 2 from le_of_lt hz.1.1, le_of_lt hz.1.2.1,
      le_of_lt hz.1.2.2⟩
  have hOK₂ : O ⊆ {x : Vec3 | vec3EuclideanNorm (x - c₂.1) ≤ 1 / 2} ×ˢ
      Icc (c₂.2 - 1 / 4) c₂.2 := fun z hz =>
    ⟨show vec3EuclideanNorm (z.1 - c₂.1) ≤ 1 / 2 from le_of_lt hz.2.1, le_of_lt hz.2.2.1,
      le_of_lt hz.2.2.2⟩
  have hae₁' : ω₁ =ᵐ[volume.restrict O] h :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hae₁
  have hae₂' : ω₂ =ᵐ[volume.restrict O] h :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hae₂
  have hae : ω₁ =ᵐ[volume.restrict O] ω₂ := hae₁'.trans hae₂'.symm
  have heq : EqOn ω₁ ω₂ O := Measure.eqOn_open_of_ae_eq hae hO (hc₁.mono hOK₁) (hc₂.mono hOK₂)
  have hev : ∀ᶠ s in 𝓝[<] t, ((x, s) : Vec3 × ℝ) ∈ O := by
    filter_upwards [Ioo_mem_nhdsLT (max_lt ht₁.1 ht₂.1)] with s hs
    exact ⟨⟨hx₁, lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 ht₁.2⟩,
      ⟨hx₂, lt_of_le_of_lt (le_max_right _ _) hs.1, lt_of_lt_of_le hs.2 ht₂.2⟩⟩
  have hpath : Tendsto (fun s : ℝ => ((x, s) : Vec3 × ℝ)) (𝓝[<] t) (𝓝 (x, t)) :=
    ((continuous_const.prodMk continuous_id).tendsto t).mono_left nhdsWithin_le_nhds
  have hT₁ : Tendsto (fun s => ω₁ (x, s)) (𝓝[<] t) (𝓝 (ω₁ (x, t))) :=
    (hc₁ (x, t) ⟨le_of_lt hx₁, le_of_lt ht₁.1, ht₁.2⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hpath, hev.mono fun s hs => hOK₁ hs⟩)
  have hT₂ : Tendsto (fun s => ω₂ (x, s)) (𝓝[<] t) (𝓝 (ω₂ (x, t))) :=
    (hc₂ (x, t) ⟨le_of_lt hx₂, le_of_lt ht₂.1, ht₂.2⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hpath, hev.mono fun s hs => hOK₂ hs⟩)
  exact tendsto_nhds_unique hT₁ (hT₂.congr' (hev.mono fun s hs => (heq hs).symm))

/-- A countable family of exterior half-cylinders with tops below zero covering the open
exterior region. -/
theorem vorticityTop_centers (R₂ : ℝ) :
    ∃ A₀ : Set (Vec3 × ℝ), A₀.Countable ∧
      (∀ c ∈ A₀, R₂ < vec3EuclideanNorm c.1 ∧ c.2 ∈ Ioo (-2 : ℝ) 0) ∧
      ∀ z ∈ ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioo (-2 : ℝ) 0 : Set (Vec3 × ℝ)),
        ∃ c ∈ A₀, z ∈ vec3Ball c.1 (1 / 2) ×ˢ Ioo (c.2 - 1 / 4) c.2 := by
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense (Vec3 × ℝ)
  refine ⟨Q ∩ {c | R₂ < vec3EuclideanNorm c.1 ∧ c.2 ∈ Ioo (-2 : ℝ) 0},
    hQc.mono inter_subset_left, fun c hc => hc.2, ?_⟩
  rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
  have hx' : R₂ < vec3EuclideanNorm x := hx
  set V : Set (Vec3 × ℝ) := {c | vec3EuclideanNorm (x - c.1) < 1 / 2 ∧
    R₂ < vec3EuclideanNorm c.1 ∧ t < c.2 ∧ c.2 < t + 1 / 4 ∧ c.2 < 0} with hVdef
  have hVo : IsOpen V := by
    have h1 : Continuous fun c : Vec3 × ℝ => vec3EuclideanNorm (x - c.1) :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
        (continuous_const.sub continuous_fst)
    have h2 : Continuous fun c : Vec3 × ℝ => vec3EuclideanNorm c.1 :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp continuous_fst
    exact (isOpen_lt h1 continuous_const).inter ((isOpen_lt continuous_const h2).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_const).inter
          (isOpen_lt continuous_snd continuous_const))))
  have hδ : 0 < min (1 / 8 : ℝ) (-t / 2) := lt_min (by norm_num) (by linarith only [ht2])
  have hδ1 := min_le_left (1 / 8 : ℝ) (-t / 2)
  have hδ2 := min_le_right (1 / 8 : ℝ) (-t / 2)
  have hVne : V.Nonempty := by
    refine ⟨(x, t + min (1 / 8) (-t / 2)), ?_, hx', ?_, ?_, ?_⟩
    · change vec3EuclideanNorm (x - x) < 1 / 2
      rw [sub_self, vec3EuclideanNorm_zero]
      norm_num
    · change t < t + min (1 / 8) (-t / 2)
      linarith only [hδ]
    · change t + min (1 / 8) (-t / 2) < t + 1 / 4
      linarith only [hδ1]
    · change t + min (1 / 8) (-t / 2) < 0
      linarith only [hδ2, ht2]
  obtain ⟨c, hcQ, hcV⟩ := hQd.exists_mem_open hVo hVne
  refine ⟨c, ⟨hcQ, hcV.2.1, lt_trans ht1 hcV.2.2.1, hcV.2.2.2.2⟩, hcV.1, ?_, hcV.2.2.1⟩
  change c.2 - 1 / 4 < t
  linarith only [hcV.2.2.2.1]

/-- A bounded subset of the open exterior region is covered by finitely many exterior
half-cylinders with tops in `(-2, 0]`. -/
theorem vorticityTop_finiteCover {R₂ : ℝ} (hR₂ : 0 < R₂) {S : Set (Vec3 × ℝ)}
    (hS : S ⊆ {x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioo (-2 : ℝ) 0)
    (hSb : Bornology.IsBounded S) :
    ∃ F : Finset (Vec3 × ℝ), (∀ c ∈ F, R₂ < vec3EuclideanNorm c.1 ∧ c.2 ∈ Ioc (-2 : ℝ) 0) ∧
      S ⊆ ⋃ c ∈ F, vec3Ball c.1 (1 / 2) ×ˢ Ioo (c.2 - 1 / 4) c.2 := by
  have hK : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hSb.closure
  have hclosed : IsClosed ({x : Vec3 | R₂ ≤ vec3EuclideanNorm x} ×ˢ Icc (-2 : ℝ) 0 :
      Set (Vec3 × ℝ)) :=
    (isClosed_le continuous_const CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).prod
      isClosed_Icc
  have hKsub : closure S ⊆ {x : Vec3 | R₂ ≤ vec3EuclideanNorm x} ×ˢ Icc (-2 : ℝ) 0 :=
    closure_minimal (fun z hz => ⟨show R₂ ≤ vec3EuclideanNorm z.1 from le_of_lt (hS hz).1,
      le_of_lt (hS hz).2.1, le_of_lt (hS hz).2.2⟩) hclosed
  -- the centre attached to a point of the closure
  let cen : Vec3 × ℝ → Vec3 × ℝ := fun p =>
    ((1 + 1 / (4 * vec3EuclideanNorm p.1)) • p.1, if -1 / 8 < p.2 then 0 else p.2 + 1 / 16)
  let O : Vec3 × ℝ → Set (Vec3 × ℝ) := fun p => {y | vec3EuclideanNorm (y.1 - (cen p).1) < 1 / 2 ∧
    (cen p).2 - 1 / 4 < y.2 ∧ y.2 < (cen p).2 + (if (cen p).2 = 0 then 1 else 0)}
  have hOo : ∀ p, IsOpen (O p) := fun p =>
    (isOpen_lt (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
      (continuous_fst.sub continuous_const)) continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hnorm : ∀ p ∈ closure S, 0 < vec3EuclideanNorm p.1 := fun p hp =>
    lt_of_lt_of_le hR₂ (hKsub hp).1
  have hcen1 : ∀ p ∈ closure S, vec3EuclideanNorm (cen p).1 = vec3EuclideanNorm p.1 + 1 / 4 := by
    intro p hp
    have hn := hnorm p hp
    change vec3EuclideanNorm ((1 + 1 / (4 * vec3EuclideanNorm p.1)) • p.1) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos (by positivity)]
    field_simp
  have hcen2 : ∀ p ∈ closure S, vec3EuclideanNorm (p.1 - (cen p).1) = 1 / 4 := by
    intro p hp
    have hn := hnorm p hp
    have e : p.1 - (cen p).1 = (-(1 / (4 * vec3EuclideanNorm p.1))) • p.1 := by
      change p.1 - (1 + 1 / (4 * vec3EuclideanNorm p.1)) • p.1 = _
      rw [add_smul, one_smul, neg_smul]
      abel
    rw [e, vec3EuclideanNorm_smul, abs_neg, abs_of_pos (by positivity)]
    field_simp
  have hmem : ∀ p ∈ closure S, p ∈ O p := by
    intro p hp
    have ht := (hKsub hp).2
    refine ⟨by rw [hcen2 p hp]; norm_num, ?_⟩
    show (cen p).2 - 1 / 4 < p.2 ∧ p.2 < (cen p).2 + (if (cen p).2 = 0 then 1 else 0)
    by_cases h : -1 / 8 < p.2
    · have e : (cen p).2 = 0 := by simp [cen, h]
      have e2 : (if (0 : ℝ) = 0 then (1 : ℝ) else 0) = 1 := by simp
      rw [e, e2]
      exact ⟨by linarith only [h], by linarith only [ht.2]⟩
    · have e : (cen p).2 = p.2 + 1 / 16 := by simp [cen, h]
      have hnn : (0 : ℝ) ≤ if (cen p).2 = 0 then 1 else 0 := by split_ifs <;> norm_num
      rw [e] at hnn ⊢
      exact ⟨by linarith only [], by linarith only [hnn]⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun p : closure S => O p.1) (fun p => hOo p.1)
    (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, hmem p hp⟩)
  refine ⟨T.image fun p => cen p.1, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hc
    have ht := (hKsub p.2).2
    have hR : R₂ ≤ vec3EuclideanNorm p.1.1 := (hKsub p.2).1
    refine ⟨by rw [hcen1 p.1 p.2]; linarith only [hR], ?_, ?_⟩
    · change -2 < if -1 / 8 < p.1.2 then (0 : ℝ) else p.1.2 + 1 / 16
      split_ifs
      · norm_num
      · linarith only [ht.1]
    · change (if -1 / 8 < p.1.2 then (0 : ℝ) else p.1.2 + 1 / 16) ≤ 0
      split_ifs with h
      · exact le_rfl
      · linarith only [not_lt.1 h]
  · intro z hz
    obtain ⟨p, hpT, hzp⟩ := mem_iUnion₂.1 (hT (subset_closure hz))
    refine mem_iUnion₂.2 ⟨cen p.1, Finset.mem_image_of_mem _ hpT, hzp.1, hzp.2.1, ?_⟩
    have hz0 : z.2 < 0 := (hS hz).2.2
    have h3 := hzp.2.2
    change z.2 < (cen p.1).2
    by_cases h0 : (cen p.1).2 = 0
    · rw [h0]; exact hz0
    · have e3 : (if (cen p.1).2 = 0 then (1 : ℝ) else 0) = 0 := by simp [h0]
      rw [e3, add_zero] at h3
      exact h3

/-- The time derivative of a test function vanishes off its support. -/
theorem vorticity_timePartial_off {ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartial ψ z = 0 := by
  by_contra hne
  exact hz (CKN.tsupport_timePartial_subset ψ (subset_tsupport _ hne))

/-- A weak time derivative restricts to smaller sets. -/
theorem vorticity_weakTime_restrict {W W' : Set (Vec3 × ℝ)} (hW' : W' ⊆ W)
    {f g : Vec3 × ℝ → ℝ}
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * timePartial ψ y = -∫ y in W, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W' → ∫ y in W', f y * timePartial ψ y = -∫ y in W', g y * ψ y := by
  intro ψ hψ hψc hψW'
  have h' := vorticity_restrict_identity (Φ := fun ψ y => f y * timePartial ψ y)
    (Ψ := fun ψ y => -(g y * ψ y)) hW'
    (fun ψ z hz => by simp [vorticity_timePartial_off hz])
    (fun ψ z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
    (fun ψ hψ hψc hψW => by rw [integral_neg]; exact h ψ hψ hψc hψW) ψ hψ hψc hψW'
  rw [← integral_neg]
  exact h'

/-- Uniqueness of the weak spatial derivative of almost everywhere equal functions. -/
theorem vorticity_weakPartial_unique_of_ae {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {f₁ f₂ g₁ g₂ : Vec3 × ℝ → ℝ} {j : Fin 3} (hf : f₁ =ᵐ[volume.restrict W] f₂)
    (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₁ y * spatialPartial ψ j y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₂ y * spatialPartial ψ j y = -∫ y in W, g₂ y * ψ y) :
    g₁ =ᵐ[volume.restrict W] g₂ :=
  vorticity_weakPartial_unique hW hg₁ hg₂ h₁ fun ψ hψ hψc hψW =>
    (integral_congr_ae (hf.mono fun z hz => congrArg (fun r => r * spatialPartial ψ j z) hz)).trans
      (h₂ ψ hψ hψc hψW)

/-- Uniqueness of the weak time derivative of almost everywhere equal functions. -/
theorem vorticity_weakTime_unique_of_ae {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {f₁ f₂ g₁ g₂ : Vec3 × ℝ → ℝ} (hf : f₁ =ᵐ[volume.restrict W] f₂)
    (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₁ y * timePartial ψ y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₂ y * timePartial ψ y = -∫ y in W, g₂ y * ψ y) :
    g₁ =ᵐ[volume.restrict W] g₂ :=
  vorticity_weakTime_unique hW hg₁ hg₂ h₁ fun ψ hψ hψc hψW =>
    (integral_congr_ae (hf.mono fun z hz => congrArg (fun r => r * timePartial ψ z) hz)).trans
      (h₂ ψ hψ hψc hψW)

/-- A weak identity on a neighbourhood passes to a larger domain for tests supported in both,
when the integrands agree almost everywhere on the intersection. -/
theorem vorticityTop_localIdentity {D N : Set (Vec3 × ℝ)} {f g f' g' : Vec3 × ℝ → ℝ}
    (L : (Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ) (hLoff : ∀ ψ z, z ∉ tsupport ψ → L ψ z = 0)
    (hf : f =ᵐ[volume.restrict (N ∩ D)] f') (hg : g =ᵐ[volume.restrict (N ∩ D)] g')
    (hid : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ N →
      ∫ y in N, f' y * L ψ y = -∫ y in N, g' y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ N →
      tsupport ψ ⊆ D → ∫ y in D, f y * L ψ y = -∫ y in D, g y * ψ y := by
  intro ψ hψ hψc hψN hψD
  have hsub : tsupport ψ ⊆ N ∩ D := subset_inter hψN hψD
  have v1 : ∀ (h : Vec3 × ℝ → ℝ) z, z ∉ N ∩ D → h z * L ψ z = 0 := fun h z hz => by
    rw [hLoff ψ z (fun h' => hz (hsub h')), mul_zero]
  have v2 : ∀ (h : Vec3 × ℝ → ℝ) z, z ∉ N ∩ D → h z * ψ z = 0 := fun h z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hz (hsub h')), mul_zero]
  have a1 := vorticity_setIntegral_congr_of_vanish inter_subset_right (v1 f)
  have a2 := vorticity_setIntegral_congr_of_vanish inter_subset_left (v1 f')
  have a3 := vorticity_setIntegral_congr_of_vanish inter_subset_right (v2 g)
  have a4 := vorticity_setIntegral_congr_of_vanish inter_subset_left (v2 g')
  have b1 : ∫ y in N ∩ D, f y * L ψ y = ∫ y in N ∩ D, f' y * L ψ y :=
    integral_congr_ae (hf.mono fun z hz => congrArg (fun r => r * L ψ z) hz)
  have b2 : ∫ y in N ∩ D, g y * ψ y = ∫ y in N ∩ D, g' y * ψ y :=
    integral_congr_ae (hg.mono fun z hz => congrArg (fun r => r * ψ z) hz)
  calc
    _ = ∫ y in N ∩ D, f y * L ψ y := a1.symm
    _ = ∫ y in N ∩ D, f' y * L ψ y := b1
    _ = ∫ y in N, f' y * L ψ y := a2
    _ = -∫ y in N, g' y * ψ y := hid ψ hψ hψc hψN
    _ = -∫ y in N ∩ D, g' y * ψ y := congrArg Neg.neg a4.symm
    _ = -∫ y in N ∩ D, g y * ψ y := congrArg Neg.neg b2.symm
    _ = -∫ y in D, g y * ψ y := congrArg Neg.neg a3

/-- The differential inequality of the vorticity from its componentwise form. -/
theorem vorticity_ineq_convert {Cb : ℝ} (hCb : 0 ≤ Cb) (w Dtw : Vec3) (Dw : Fin 3 → Vec3)
    (D2w : Fin 3 → Fin 3 → Vec3)
    (h : ∀ i, |Dtw i - ∑ j : Fin 3, D2w i j j| ≤
      Cb * (∑ l : Fin 3, |w l| + ∑ a : Fin 3, ∑ b : Fin 3, |Dw a b|)) :
    vec3EuclideanNorm (fun i => Dtw i - ∑ j : Fin 3, D2w i j j) ≤
      27 * Cb * (vec3EuclideanNorm w + Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2)) := by
  have hN := vec3EuclideanNorm_nonneg w
  have hA : ∑ l : Fin 3, |w l| ≤ 3 * vec3EuclideanNorm w := by
    calc
      _ ≤ ∑ _l : Fin 3, vec3EuclideanNorm w :=
        Finset.sum_le_sum fun l _ => abs_apply_le_vec3EuclideanNorm w l
      _ = 3 * vec3EuclideanNorm w := by
        rw [Fin.sum_univ_three]
        ring
  have hB : ∑ a : Fin 3, ∑ b : Fin 3, |Dw a b| ≤
      9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2) := by
    calc
      _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Real.abs_le_sqrt (vorticity_sq_le_sum_two (fun i j => Dw i j) a b)
      _ = 9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2) := by
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        ring
  have hsum : ∑ i : Fin 3, |Dtw i - ∑ j : Fin 3, D2w i j j| ≤
      3 * (Cb * (∑ l : Fin 3, |w l| + ∑ a : Fin 3, ∑ b : Fin 3, |Dw a b|)) := by
    calc
      _ ≤ ∑ _i : Fin 3, Cb * (∑ l : Fin 3, |w l| + ∑ a : Fin 3, ∑ b : Fin 3, |Dw a b|) :=
        Finset.sum_le_sum fun i _ => h i
      _ = _ := by
        rw [Fin.sum_univ_three]
        ring
  have hmono := mul_le_mul_of_nonneg_left (add_le_add hA hB) hCb
  have e1 : 27 * Cb * (vec3EuclideanNorm w +
      Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2)) =
      3 * (Cb * (3 * vec3EuclideanNorm w +
        9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2))) +
        18 * (Cb * vec3EuclideanNorm w) := by ring
  have p := mul_nonneg hCb hN
  exact (vec3EuclideanNorm_le_sum_abs _).trans (by linarith only [hsum, hmono, e1, p])

/-- A set bounded for the parabolic distance is bounded in `Vec3 × ℝ`. -/
theorem vorticity_isBounded_of_parabolic {S : Set ParabolicPoint} (h : Bornology.IsBounded S) :
    @Bornology.IsBounded (Vec3 × ℝ) _ S := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 h
  refine Metric.isBounded_iff.2 ⟨max C (C ^ 2), fun x hx y hy => ?_⟩
  have h1 : max (vec3EuclideanNorm (x.1 - y.1)) (Real.sqrt |x.2 - y.2|) ≤ C :=
    (dist_eq_parabolicDist x y).symm.le.trans (hC hx hy)
  have hs0 := Real.sqrt_nonneg |x.2 - y.2|
  have hs1 : Real.sqrt |x.2 - y.2| ≤ C := le_trans (le_max_right _ _) h1
  have hn1 : vec3EuclideanNorm (x.1 - y.1) ≤ C := le_trans (le_max_left _ _) h1
  change max (dist x.1 y.1) (dist x.2 y.2) ≤ max C (C ^ 2)
  refine max_le_max ?_ ?_
  · rw [dist_eq_norm]
    exact (norm_le_vec3EuclideanNorm _).trans hn1
  · rw [Real.dist_eq, ← Real.sq_sqrt (abs_nonneg (x.2 - y.2))]
    exact pow_le_pow_left₀ hs0 hs1 2

end ESS
