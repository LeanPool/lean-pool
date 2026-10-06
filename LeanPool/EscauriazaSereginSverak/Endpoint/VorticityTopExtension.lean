/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityGlue
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopData
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopZero
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopLocal

/-!
# The exterior vorticity at the terminal face

`lem:vorticity-top-extension`: the vorticity of a suitable weak solution which is bounded, with
bounded gradient energy, on every unit past cylinder centred in the exterior region
`{|x| > R₂} × (-2, 0)`, and whose velocity has zero weak trace at time zero, has a representative
continuous on `{|x| > R₂} × (-2, 0]`, vanishing at time zero, bounded, with space-time weak
derivatives in `L²` on bounded sets, satisfying `|∂ₜω - Δω| ≤ C (|ω| + |∇ω|)`.

The representative is glued from the continuous representatives of `thm:vorticity-regularity` on
the half-cylinders below the points of the exterior region, including those with top at time
zero; the weak derivatives are glued from a countable family of half-cylinders and a smooth
partition of unity.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem vorticityTopExtension_continuousShift
    (R₂ : ℝ) (A : Vec3 × ℝ → Vec3 × ℝ)
    (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (hA1 : ∀ z, (A z).1 = z.1)
    (hA2 : ∀ z, (A z).2 = if -1 / 8 < z.2 then 0 else z.2 + 1 / 16)
    (hadmA : ∀ z : Vec3 × ℝ, R₂ < vec3EuclideanNorm z.1 → z.2 ∈ Ioc (-2 : ℝ) 0 →
      R₂ < vec3EuclideanNorm (A z).1 ∧ (A z).2 ∈ Ioc (-2 : ℝ) 0 ∧
        vec3EuclideanNorm (z.1 - (A z).1) < 1 / 2 ∧ z.2 ∈ Ioc ((A z).2 - 1 / 4) (A z).2)
    (F1 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z : Vec3 × ℝ, R₂ < vec3EuclideanNorm z.1 → z.2 ∈ Ioc (-2 : ℝ) 0 →
      vec3EuclideanNorm (z.1 - c.1) < 1 / 2 → z.2 ∈ Ioc (c.2 - 1 / 4) c.2 →
      ∀ i, ω (A z) i z = ω c i z)
    (hωc : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      ContinuousOn (fun z => ω c i z)
        ({x : Vec3 | vec3EuclideanNorm (x - c.1) ≤ 1 / 2} ×ˢ Icc (c.2 - 1 / 4) c.2)) :
    ContinuousOn (fun z : Vec3 × ℝ => fun i => ω (A z) i z)
      ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) := by
  have hcontP : ContinuousOn (fun z : Vec3 × ℝ => fun i => ω (A z) i z)
      ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) := by
    intro z hz
    obtain ⟨h1, h2, -, -⟩ := hadmA z hz.1 hz.2
    set N : Set (Vec3 × ℝ) := {y | vec3EuclideanNorm (y.1 - z.1) < 1 / 4 ∧
      z.2 - 1 / 16 < y.2 ∧ y.2 < z.2 + 1 / 16} with hNdef
    have hNo : IsOpen N :=
      (isOpen_lt (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
        (continuous_fst.sub continuous_const)) continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
    have hzN : z ∈ N := ⟨by rw [sub_self, vec3EuclideanNorm_zero]; norm_num,
      by linarith only [], by linarith only []⟩
    have hgood : ∀ y ∈ ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) ∩ N,
        vec3EuclideanNorm (y.1 - (A z).1) < 1 / 2 ∧ y.2 ∈ Ioc ((A z).2 - 1 / 4) (A z).2 := by
      intro y hy
      have hy1 : vec3EuclideanNorm (y.1 - z.1) < 1 / 4 := hy.2.1
      have hy2 := hy.2.2
      have hy3 : y.2 ≤ 0 := hy.1.2.2
      rw [hA1, hA2]
      refine ⟨by linarith only [hy1], ?_⟩
      split_ifs with h
      · exact ⟨by linarith only [h, hy2.1], hy3⟩
      · exact ⟨by linarith only [hy2.1], le_of_lt hy2.2⟩
    have hagree : ∀ y ∈ ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) ∩ N,
        (fun i => ω (A y) i y) = fun i => ω (A z) i y := fun y hy => funext fun i =>
      F1 (A z) h1 h2 y hy.1.1 hy.1.2 (hgood y hy).1 (hgood y hy).2 i
    have hK : ContinuousOn (fun y : Vec3 × ℝ => fun i => ω (A z) i y)
        ({x : Vec3 | vec3EuclideanNorm (x - (A z).1) ≤ 1 / 2} ×ˢ
          Icc ((A z).2 - 1 / 4) (A z).2) :=
      continuousOn_pi.2 fun i => hωc (A z) h1 h2 i
    have hsubK : ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) ∩ N ⊆
        {x : Vec3 | vec3EuclideanNorm (x - (A z).1) ≤ 1 / 2} ×ˢ
          Icc ((A z).2 - 1 / 4) (A z).2 := fun y hy =>
      ⟨show vec3EuclideanNorm (y.1 - (A z).1) ≤ 1 / 2 from le_of_lt (hgood y hy).1,
        le_of_lt (hgood y hy).2.1, (hgood y hy).2.2⟩
    have hcw : ContinuousWithinAt (fun y : Vec3 × ℝ => fun i => ω (A z) i y)
        ({x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioc (-2 : ℝ) 0) z :=
      (continuousWithinAt_inter (hNo.mem_nhds hzN)).1 ((hK.mono hsubK) z ⟨hz, hzN⟩)
    exact hcw.congr_of_eventuallyEq
      (mem_nhdsWithin.2 ⟨N, hNo, hzN, fun y hy => hagree y ⟨hy.2, hy.1⟩⟩)
      (hagree z ⟨hz, hzN⟩)
  exact hcontP.comp parabolicHomeomorph.continuous.continuousOn fun p hp => hp

private theorem vorticityTopExtension_inwardTimeShift :
    ∃ A : Vec3 × ℝ → Vec3 × ℝ,
      (∀ z, (A z).1 = z.1) ∧
      (∀ z, (A z).2 = if -1 / 8 < z.2 then 0 else z.2 + 1 / 16) ∧
      (∀ z : Vec3 × ℝ, z.2 ∈ Ioc (-2 : ℝ) 0 →
        (A z).2 ∈ Ioc (-2 : ℝ) 0 ∧
        vec3EuclideanNorm (z.1 - (A z).1) < 1 / 2 ∧
        z.2 ∈ Ioc ((A z).2 - 1 / 4) (A z).2) := by
  refine ⟨fun z => (z.1, if -1 / 8 < z.2 then 0 else z.2 + 1 / 16), ?_, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    rfl
  · intro z hz
    rw [sub_self, vec3EuclideanNorm_zero]
    refine ⟨?_, by norm_num, ?_⟩
    · split_ifs with h
      · exact ⟨by norm_num, le_rfl⟩
      · exact ⟨by linarith only [hz.1], by linarith only [not_lt.1 h]⟩
    · split_ifs with h
      · exact ⟨by linarith only [h], hz.2⟩
      · exact ⟨by linarith only [], by linarith only []⟩

private theorem vorticityTopExtension_patchVorticity_ae
    {R₂ : ℝ} (D A₀ : Set (Vec3 × ℝ)) (S : (Vec3 × ℝ) → Set (Vec3 × ℝ))
    (hA₀c : A₀.Countable) (hcovD : D ⊆ ⋃ b ∈ A₀, S b)
    (hDm : MeasurableSet D) (A : (Vec3 × ℝ) → (Vec3 × ℝ))
    (hSo : ∀ b, IsOpen (S b))
    (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (v : (Vec3 × ℝ) → Fin 3 → ℝ)
    (hωae : ∀ b, R₂ < vec3EuclideanNorm b.1 → b.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ i, ω b i =ᵐ[volume.restrict (S b)] fun z => v z i)
    (hagree : ∀ b, R₂ < vec3EuclideanNorm b.1 → b.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z ∈ S b ∩ D, ∀ i, ω (A z) i z = ω b i z)
    (hA₀adm : ∀ b ∈ A₀, R₂ < vec3EuclideanNorm b.1 ∧ b.2 ∈ Ioo (-2 : ℝ) 0) :
    (fun z i => ω (A z) i z) =ᵐ[volume.restrict D] v := by
  have h1 : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (⋃ b ∈ A₀, S b)), z ∈ D →
      (fun i => ω (A z) i z) = v z := by
    rw [ae_restrict_biUnion_iff _ hA₀c]
    intro b hb
    have hb' := hA₀adm b hb
    have hb2 : b.2 ∈ Ioc (-2 : ℝ) 0 := ⟨hb'.2.1, le_of_lt hb'.2.2⟩
    have hl : ∀ᵐ z ∂(volume.restrict (D ∩ S b)), (fun i => ω (A z) i z) = v z := by
      filter_upwards [ae_all_iff.2 (hωae b hb'.1 hb2),
        ae_restrict_mem (hDm.inter (hSo b).measurableSet)] with z hz hzm
      funext i
      exact (hagree b hb'.1 hb2 z ⟨hzm.2, hzm.1⟩ i).trans (hz i)
    rw [← Measure.restrict_restrict (hSo b).measurableSet] at hl
    exact (ae_restrict_iff' (hSo b).measurableSet).1 hl
  exact ((ae_restrict_of_ae_restrict_of_subset hcovD h1).and
    (ae_restrict_mem hDm)).mono fun z hz => hz.1 hz.2

private theorem vorticityTopExtension_integrablePatchedFields
    {R₂ : ℝ} (S : (Vec3 × ℝ) → Set (Vec3 × ℝ)) (D : Set (Vec3 × ℝ))
    (A B : (Vec3 × ℝ) → Vec3 × ℝ) (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω1 : (Vec3 × ℝ) → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω2 : (Vec3 × ℝ) → Fin 3 → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Dt : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (hint : ∀ (c : Vec3 × ℝ) (f : Vec3 × ℝ → ℝ),
      MemLp f 2 (volume.restrict (S c)) → IntegrableOn f (S c))
    (Eω : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      (fun z => ω (A z) i z) =ᵐ[volume.restrict (S c ∩ D)] ω c i)
    (E2 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      (fun z => Ω1 (B z) i j z) =ᵐ[volume.restrict (S c ∩ D)] Ω1 c i j ∧
      (∀ k, (fun z => Ω2 (B z) i j k z) =ᵐ[volume.restrict (S c ∩ D)] Ω2 c i j k) ∧
      (fun z => Dt (B z) i z) =ᵐ[volume.restrict (S c ∩ D)] Dt c i)
    (hωL : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      MemLp (ω c i) 2 (volume.restrict (S c)))
    (hΩ1L : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      MemLp (Ω1 c i j) 2 (volume.restrict (S c)))
    (hΩ2L : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j k,
      MemLp (Ω2 c i j k) 2 (volume.restrict (S c)))
    (hDtL : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      MemLp (Dt c i) 2 (volume.restrict (S c))) :
    ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      (∀ i, IntegrableOn (fun z => ω (A z) i z) (S c ∩ D)) ∧
      (∀ i j, IntegrableOn (fun z => Ω1 (B z) i j z) (S c ∩ D)) ∧
      (∀ i j k, IntegrableOn (fun z => Ω2 (B z) i j k z) (S c ∩ D)) ∧
      (∀ i, IntegrableOn (fun z => Dt (B z) i z) (S c ∩ D)) := by
  intro c hc1 hc2
  refine ⟨fun i => ?_, fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
  · exact ((hint c _ (hωL c hc1 hc2 i)).mono_set inter_subset_left).congr_fun_ae
      (Eω c hc1 hc2 i).symm
  · exact ((hint c _ (hΩ1L c hc1 hc2 i j)).mono_set inter_subset_left).congr_fun_ae
      (E2 c hc1 hc2 i j).1.symm
  · exact ((hint c _ (hΩ2L c hc1 hc2 i j k)).mono_set inter_subset_left).congr_fun_ae
      ((E2 c hc1 hc2 i j).2.1 k).symm
  · exact ((hint c _ (hDtL c hc1 hc2 i)).mono_set inter_subset_left).congr_fun_ae
      (E2 c hc1 hc2 i 0).2.2.symm

private theorem vorticityTopExtension_localDerivativeUnique
    {R₂ : ℝ} (S : (Vec3 × ℝ) → Set (Vec3 × ℝ))
    (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω1 : (Vec3 × ℝ) → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω2 : (Vec3 × ℝ) → Fin 3 → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Dt : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (hSo : ∀ c, IsOpen (S c))
    (hint : ∀ (c : Vec3 × ℝ) (f : Vec3 × ℝ → ℝ),
      MemLp f 2 (volume.restrict (S c)) → IntegrableOn f (S c))
    (V : Vec3 × ℝ → Vec3)
    (hωae : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      ω c i =ᵐ[volume.restrict (S c)] V i)
    (hΩ1L : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      MemLp (Ω1 c i j) 2 (volume.restrict (S c)))
    (hΩ2L : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j k,
      MemLp (Ω2 c i j k) 2 (volume.restrict (S c)))
    (hDtL : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      MemLp (Dt c i) 2 (volume.restrict (S c)))
    (hdw : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ S c →
        ∫ y in S c, ω c i y * spatialPartial ψ j y = -∫ y in S c, Ω1 c i j y * ψ y)
    (hdΩ : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j k,
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ S c →
        ∫ y in S c, Ω1 c i j y * spatialPartial ψ k y = -∫ y in S c, Ω2 c i j k y * ψ y)
    (hdt : ∀ c, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ S c →
        ∫ y in S c, ω c i y * timePartial ψ y = -∫ y in S c, Dt c i y * ψ y) :
    ∀ c b : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      R₂ < vec3EuclideanNorm b.1 → b.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      Ω1 b i j =ᵐ[volume.restrict (S b ∩ S c)] Ω1 c i j ∧
      (∀ k, Ω2 b i j k =ᵐ[volume.restrict (S b ∩ S c)] Ω2 c i j k) ∧
      Dt b i =ᵐ[volume.restrict (S b ∩ S c)] Dt c i := by
  intro c b hc1 hc2 hb1 hb2 i j
  have hO : IsOpen (S b ∩ S c) := (hSo b).inter (hSo c)
  have hOb : S b ∩ S c ⊆ S b := inter_subset_left
  have hOc : S b ∩ S c ⊆ S c := inter_subset_right
  have wb : ω b i =ᵐ[volume.restrict (S b ∩ S c)] V i :=
    ae_restrict_of_ae_restrict_of_subset hOb (hωae b hb1 hb2 i)
  have wc : ω c i =ᵐ[volume.restrict (S b ∩ S c)] V i :=
    ae_restrict_of_ae_restrict_of_subset hOc (hωae c hc1 hc2 i)
  have wbc : ω b i =ᵐ[volume.restrict (S b ∩ S c)] ω c i := wb.trans wc.symm
  have e1 : Ω1 b i j =ᵐ[volume.restrict (S b ∩ S c)] Ω1 c i j :=
    vorticity_weakPartial_unique_of_ae hO wbc
      ((hint b _ (hΩ1L b hb1 hb2 i j)).mono_set hOb)
      ((hint c _ (hΩ1L c hc1 hc2 i j)).mono_set hOc)
      (vorticity_weakPartial_restrict hOb (hdw b hb1 hb2 i j))
      (vorticity_weakPartial_restrict hOc (hdw c hc1 hc2 i j))
  refine ⟨e1, fun k => ?_, ?_⟩
  · exact vorticity_weakPartial_unique_of_ae hO e1
      ((hint b _ (hΩ2L b hb1 hb2 i j k)).mono_set hOb)
      ((hint c _ (hΩ2L c hc1 hc2 i j k)).mono_set hOc)
      (vorticity_weakPartial_restrict hOb (hdΩ b hb1 hb2 i j k))
      (vorticity_weakPartial_restrict hOc (hdΩ c hc1 hc2 i j k))
  · exact vorticity_weakTime_unique_of_ae hO wbc
      ((hint b _ (hDtL b hb1 hb2 i)).mono_set hOb)
      ((hint c _ (hDtL c hc1 hc2 i)).mono_set hOc)
      (vorticity_weakTime_restrict hOb (hdt b hb1 hb2 i))
      (vorticity_weakTime_restrict hOc (hdt c hc1 hc2 i))

private theorem vorticityTopExtension_coverDerivativeIdentities
    {R₂ : ℝ} (D A₀ : Set (Vec3 × ℝ)) (S : (Vec3 × ℝ) → Set (Vec3 × ℝ))
    (A B : (Vec3 × ℝ) → Vec3 × ℝ)
    (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω1 : (Vec3 × ℝ) → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω2 : (Vec3 × ℝ) → Fin 3 → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Dt : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (hA₀c : A₀.Countable) (hA₀adm : ∀ b ∈ A₀,
      R₂ < vec3EuclideanNorm b.1 ∧ b.2 ∈ Ioo (-2 : ℝ) 0)
    (hBA : ∀ z ∈ D, B z ∈ A₀) (hBS : ∀ z ∈ D, z ∈ S (B z))
    (hDm : MeasurableSet D) (hDo : IsOpen D) (hSo : ∀ c, IsOpen (S c))
    (E1 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z ∈ S c ∩ D, ∀ i, ω (A z) i z = ω c i z)
    (huniq : ∀ c b : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      R₂ < vec3EuclideanNorm b.1 → b.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      Ω1 b i j =ᵐ[volume.restrict (S b ∩ S c)] Ω1 c i j ∧
      (∀ k, Ω2 b i j k =ᵐ[volume.restrict (S b ∩ S c)] Ω2 c i j k) ∧
      Dt b i =ᵐ[volume.restrict (S b ∩ S c)] Dt c i) :
    (∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      (fun z => Ω1 (B z) i j z) =ᵐ[volume.restrict (S c ∩ D)] Ω1 c i j ∧
      (∀ k, (fun z => Ω2 (B z) i j k z) =ᵐ[volume.restrict (S c ∩ D)] Ω2 c i j k) ∧
      (fun z => Dt (B z) i z) =ᵐ[volume.restrict (S c ∩ D)] Dt c i) ∧
    (∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      (fun z => ω (A z) i z) =ᵐ[volume.restrict (S c ∩ D)] ω c i) := by
  have E2 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      (fun z => Ω1 (B z) i j z) =ᵐ[volume.restrict (S c ∩ D)] Ω1 c i j ∧
      (∀ k, (fun z => Ω2 (B z) i j k z) =ᵐ[volume.restrict (S c ∩ D)] Ω2 c i j k) ∧
      (fun z => Dt (B z) i z) =ᵐ[volume.restrict (S c ∩ D)] Dt c i := by
    intro c hc1 hc2 i j
    have key : ∀ᵐ z ∂(volume.restrict (S c)), ∀ b ∈ A₀, z ∈ S b →
        (Ω1 b i j z = Ω1 c i j z ∧ (∀ k, Ω2 b i j k z = Ω2 c i j k z) ∧
          Dt b i z = Dt c i) := by
      rw [ae_ball_iff hA₀c]
      intro b hb
      have hb' := hA₀adm b hb
      obtain ⟨u1, u2, u3⟩ := huniq c b hc1 hc2 hb'.1 ⟨hb'.2.1, le_of_lt hb'.2.2⟩ i j
      have hall : ∀ᵐ z ∂(volume.restrict (S b ∩ S c)),
          (Ω1 b i j z = Ω1 c i j z ∧ (∀ k, Ω2 b i j k z = Ω2 c i j k z) ∧
            Dt b i z = Dt c i z) := by
        filter_upwards [u1, ae_all_iff.2 u2, u3] with z h1 h2 h3 using ⟨h1, h2, h3⟩
      rw [← Measure.restrict_restrict (hSo b).measurableSet] at hall
      exact (ae_restrict_iff' (hSo b).measurableSet).1 hall
    have hcD : MeasurableSet (S c ∩ D) := ((hSo c).inter hDo).measurableSet
    have key' : ∀ᵐ z ∂(volume.restrict (S c ∩ D)),
        (Ω1 (B z) i j z = Ω1 c i j z ∧ (∀ k, Ω2 (B z) i j k z = Ω2 c i j k z) ∧
          Dt (B z) i z = Dt c i z) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left key,
        ae_restrict_mem hcD] with z hz hzm
      exact hz (B z) (hBA z hzm.2) (hBS z hzm.2)
    exact ⟨key'.mono fun z hz => hz.1, fun k => key'.mono fun z hz => hz.2.1 k,
      key'.mono fun z hz => hz.2.2⟩
  have Eω : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i,
      (fun z => ω (A z) i z) =ᵐ[volume.restrict (S c ∩ D)] ω c i := fun c hc1 hc2 i =>
    (ae_restrict_mem ((hSo c).inter hDo).measurableSet).mono fun z hz => E1 c hc1 hc2 z hz i
  exact ⟨E2, Eω⟩

private theorem vorticityTopExtension_patchedDifferentialInequality
    {R₂ Cb : ℝ} (D A₀ : Set (Vec3 × ℝ)) (S : (Vec3 × ℝ) → Set (Vec3 × ℝ))
    (A B : (Vec3 × ℝ) → Vec3 × ℝ)
    (ω : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω1 : (Vec3 × ℝ) → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Ω2 : (Vec3 × ℝ) → Fin 3 → Fin 3 → Fin 3 → (Vec3 × ℝ) → ℝ)
    (Dt : (Vec3 × ℝ) → Fin 3 → (Vec3 × ℝ) → ℝ)
    (hA₀c : A₀.Countable) (hcovD : D ⊆ ⋃ b ∈ A₀, S b)
    (hDm : MeasurableSet D) (hDo : IsOpen D) (hSo : ∀ b, IsOpen (S b))
    (hA₀adm : ∀ b ∈ A₀,
      R₂ < vec3EuclideanNorm b.1 ∧ b.2 ∈ Ioo (-2 : ℝ) 0)
    (E1 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z ∈ S c ∩ D, ∀ i, ω (A z) i z = ω c i z)
    (E2 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 → ∀ i j,
      (fun z => Ω1 (B z) i j z) =ᵐ[volume.restrict (S c ∩ D)] Ω1 c i j ∧
      (∀ k, (fun z => Ω2 (B z) i j k z) =ᵐ[volume.restrict (S c ∩ D)] Ω2 c i j k) ∧
      (fun z => Dt (B z) i z) =ᵐ[volume.restrict (S c ∩ D)] Dt c i)
    (hineq : ∀ b : Vec3 × ℝ, R₂ < vec3EuclideanNorm b.1 → b.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ᵐ z ∂(volume.restrict (S b)), ∀ i,
        |Dt b i z - ∑ j : Fin 3, Ω2 b i j j z| ≤
          Cb * (∑ l : Fin 3, |ω b l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 b a b z|))
    (hCb : 0 ≤ Cb) :
    ∀ᵐ z ∂(volume.restrict D),
      vec3EuclideanNorm (fun i => Dt (B z) i z - ∑ j, Ω2 (B z) i j j z) ≤
        27 * Cb * (vec3EuclideanNorm (fun i => ω (A z) i z) +
          Real.sqrt (spatialGradientSq (fun z => fun i => ω (A z) i z)
            (fun z i j => Ω1 (B z) i j z) z)) := by
  have h1 : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (⋃ b ∈ A₀, S b)), z ∈ D → ∀ i,
      |Dt (B z) i z - ∑ j : Fin 3, Ω2 (B z) i j j z| ≤
        Cb * (∑ l : Fin 3, |ω (A z) l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 (B z) a b z|) := by
    rw [ae_restrict_biUnion_iff _ hA₀c]
    intro b hb
    have hb' := hA₀adm b hb
    have hb2 : b.2 ∈ Ioc (-2 : ℝ) 0 := ⟨hb'.2.1, le_of_lt hb'.2.2⟩
    have hsw : D ∩ S b ⊆ S b ∩ D := fun z hz => ⟨hz.2, hz.1⟩
    have hl : ∀ᵐ z ∂(volume.restrict (D ∩ S b)), ∀ i,
        |Dt (B z) i z - ∑ j : Fin 3, Ω2 (B z) i j j z| ≤
          Cb * (∑ l : Fin 3, |ω (A z) l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 (B z) a b z|) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right
          (hineq b hb'.1 hb2),
        ae_restrict_mem (hDo.inter (hSo b)).measurableSet,
        ae_restrict_of_ae_restrict_of_subset hsw
          (ae_all_iff.2 fun a => ae_all_iff.2 fun c => (E2 b hb'.1 hb2 a c).1),
        ae_restrict_of_ae_restrict_of_subset hsw (ae_all_iff.2 fun a => ae_all_iff.2 fun c =>
          ae_all_iff.2 fun k => (E2 b hb'.1 hb2 a c).2.1 k),
        ae_restrict_of_ae_restrict_of_subset hsw
          (ae_all_iff.2 fun a => (E2 b hb'.1 hb2 a 0).2.2)] with z hz hzm e1 e2 e3 i
      have e0 : ∀ l, ω (A z) l z = ω b l z := fun l => E1 b hb'.1 hb2 z ⟨hzm.2, hzm.1⟩ l
      have e1' : ∀ a c, Ω1 (B z) a c z = Ω1 b a c z := e1
      have e2' : ∀ a c k, Ω2 (B z) a c k z = Ω2 b a c k z := e2
      have e3' : ∀ a, Dt (B z) a z = Dt b a z := e3
      simp only [e0, e1', e2', e3']
      exact hz i
    rw [← Measure.restrict_restrict hDm] at hl
    exact (ae_restrict_iff' hDm).1 hl
  refine (((ae_restrict_of_ae_restrict_of_subset hcovD h1).and (ae_restrict_mem hDm)).mono
    fun z hz => hz.1 hz.2).mono fun z hz => ?_
  exact vorticity_ineq_convert hCb (fun i => ω (A z) i z) (fun i => Dt (B z) i z)
    (fun i j => Ω1 (B z) i j z) (fun i j k => Ω2 (B z) i j k z) hz


/-- `lem:vorticity-top-extension`. -/
theorem vorticityTopExtension : ∀ (T₂ R₂ M E : ℝ), 2 < T₂ →
      0 < R₂ → 0 ≤ M → 0 ≤ E →
      ∀ (U : ParabolicPoint → Vec3)
        (DU : ParabolicPoint → Fin 3 → Vec3)
        (q : ParabolicPoint → ℝ),
        IsSuitableWeakSolution Set.univ (Ioo (-4 * T₂) 0) 3 U DU q
          (0 : ParabolicPoint → Vec3) →
        (essSup (fun t : ℝ => eLpNorm
          (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
          (3 : ℝ≥0∞) volume)
          (volume.restrict (Ioo (-4 * T₂) 0)) < ⊤) →
        HasZeroDistributionalVelocityTrace U →
        (∀ (x₁ : Vec3) (t₁ : ℝ), R₂ < vec3EuclideanNorm x₁ →
          t₁ ∈ Ioo (-2 : ℝ) 0 →
          ∃ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω ∧ IsOpen I ∧
            closure (parabolicCylinder x₁ t₁ 1) ⊆ spaceTimeSet Ω I ∧
            IsSuitableWeakSolution Ω I 3 U DU q
              (0 : ParabolicPoint → Vec3) ∧
            (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
              vec3EuclideanNorm (U z) ≤ M) ∧
            (∫⁻ z in parabolicCylinder x₁ t₁ 1,
              ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2)) →
        ∃ C : ℝ, 0 ≤ C ∧
        ∃ (ω : ParabolicPoint → Vec3)
          (Dω : ParabolicPoint → Fin 3 → Vec3)
          (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
          (Dtω : ParabolicPoint → Vec3),
          ω =ᵐ[volume.restrict
            (spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x}
              (Ioo (-2 : ℝ) 0))] weakVorticity DU ∧
          ContinuousOn ω
            (spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x}
              (Ioc (-2 : ℝ) 0)) ∧
          (∀ x : Vec3, R₂ < vec3EuclideanNorm x → ω (x, 0) = 0) ∧
          (∀ x : Vec3, R₂ < vec3EuclideanNorm x → ∀ t ∈ Ioc (-2 : ℝ) 0,
            vec3EuclideanNorm (ω (x, t)) ≤ C) ∧
          HasSpaceTimeWeakDerivs
            {x : Vec3 | R₂ < vec3EuclideanNorm x} (Ioo (-2 : ℝ) 0)
            ω Dω D2ω Dtω ∧
          (∀ S : Set ParabolicPoint,
            S ⊆ spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x}
              (Ioo (-2 : ℝ) 0) → Bornology.IsBounded S →
            (∫⁻ z in S,
              ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
                ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤) ∧
          (∀ᵐ z ∂(volume.restrict
              (spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x}
                (Ioo (-2 : ℝ) 0))),
            vec3EuclideanNorm
              (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
              C * (vec3EuclideanNorm (ω z) +
                Real.sqrt (spatialGradientSq ω Dω z))) := by
  intro T₂ R₂ M E _ hR₂ hM _ U DU q _ _ htrace hfam
  obtain ⟨Cb, hCb, hbox⟩ := vorticityRegularity_box M (18 * E ^ 2) hM
  have hloc := fun (c : Vec3 × ℝ) (hc1 : R₂ < vec3EuclideanNorm c.1)
      (hc2 : c.2 ∈ Ioc (-2 : ℝ) 0) =>
    match vorticityExterior_boxData hfam hc1 hc2 with
    | ⟨hU, hG, hUb, hK, hdU, hdiv, hheat⟩ =>
      hbox c.1 c.2 (fun i z => U z i) (fun i j z => DU z i j) hU hG hUb hK hdU hdiv hheat
  choose! ω Ω1 Ω2 Dt hωc hωb hωae hωL hΩ1L hΩ2L hDtL hdw hdΩ hdt hineq using hloc
  obtain ⟨A₀, hA₀c, hA₀adm, hA₀cov⟩ := vorticityTop_centers R₂
  choose! B hBA hBS using hA₀cov
  set D : Set (Vec3 × ℝ) := {x : Vec3 | R₂ < vec3EuclideanNorm x} ×ˢ Ioo (-2 : ℝ) 0 with hDdef
  set S : Vec3 × ℝ → Set (Vec3 × ℝ) := fun c => vec3Ball c.1 (1 / 2) ×ˢ Ioo (c.2 - 1 / 4) c.2
    with hSdef
  obtain ⟨A, hA1, hA2, hshift⟩ := vorticityTopExtension_inwardTimeShift
  have hadmA : ∀ z : Vec3 × ℝ, R₂ < vec3EuclideanNorm z.1 → z.2 ∈ Ioc (-2 : ℝ) 0 →
      R₂ < vec3EuclideanNorm (A z).1 ∧ (A z).2 ∈ Ioc (-2 : ℝ) 0 ∧
        vec3EuclideanNorm (z.1 - (A z).1) < 1 / 2 ∧ z.2 ∈ Ioc ((A z).2 - 1 / 4) (A z).2 := by
    intro z hz1 hz2
    obtain ⟨ht, hs, hi⟩ := hshift z hz2
    exact ⟨by simpa only [hA1] using hz1, ht, hs, hi⟩
  have F1 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z : Vec3 × ℝ, R₂ < vec3EuclideanNorm z.1 → z.2 ∈ Ioc (-2 : ℝ) 0 →
      vec3EuclideanNorm (z.1 - c.1) < 1 / 2 → z.2 ∈ Ioc (c.2 - 1 / 4) c.2 →
      ∀ i, ω (A z) i z = ω c i z := by
    intro c hc1 hc2 z hz1 hz2 hzc1 hzc2 i
    obtain ⟨h1, h2, h3, h4⟩ := hadmA z hz1 hz2
    exact vorticityTop_agree (hωc (A z) h1 h2 i) (hωc c hc1 hc2 i) (hωae (A z) h1 h2 i)
      (hωae c hc1 hc2 i) h3 hzc1 h4 hzc2
  have hDo : IsOpen D :=
    (isOpen_lt continuous_const CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).prod
      isOpen_Ioo
  have hDm : MeasurableSet D := hDo.measurableSet
  have hSo : ∀ c, IsOpen (S c) := fun c => vorticityBox_isOpen _ _ _ _
  have hint : ∀ (c : Vec3 × ℝ) (f : Vec3 × ℝ → ℝ), MemLp f 2 (volume.restrict (S c)) →
      IntegrableOn f (S c) := fun c f hf => by
    have : IsFiniteMeasure (volume.restrict (S c)) := isFiniteMeasure_restrict.2
      (vorticityBox_isBounded c.1 _ _ (Metric.isBounded_Ioo _ _)).measure_lt_top.ne
    exact hf.integrable (by norm_num)
  have E1 : ∀ c : Vec3 × ℝ, R₂ < vec3EuclideanNorm c.1 → c.2 ∈ Ioc (-2 : ℝ) 0 →
      ∀ z ∈ S c ∩ D, ∀ i, ω (A z) i z = ω c i z :=
    fun c hc1 hc2 z hz i => F1 c hc1 hc2 z hz.2.1 ⟨hz.2.2.1, le_of_lt hz.2.2.2⟩ hz.1.1
      ⟨hz.1.2.1, le_of_lt hz.1.2.2⟩ i
  have uniq := vorticityTopExtension_localDerivativeUnique R₂ S ω Ω1 Ω2 Dt hSo hint
    (weakVorticity DU) hωae hΩ1L hΩ2L hDtL hdw hdΩ hdt
  have admB : ∀ z ∈ D, R₂ < vec3EuclideanNorm (B z).1 ∧ (B z).2 ∈ Ioc (-2 : ℝ) 0 :=
    fun z hz => ⟨(hA₀adm _ (hBA z hz)).1, (hA₀adm _ (hBA z hz)).2.1,
      le_of_lt (hA₀adm _ (hBA z hz)).2.2⟩
  obtain ⟨E2, Eω⟩ := vorticityTopExtension_coverDerivativeIdentities
    D A₀ S A B ω Ω1 Ω2 Dt hA₀c hA₀adm hBA hBS hDm hDo hSo E1 uniq
  have IS := vorticityTopExtension_integrablePatchedFields S D A B ω Ω1 Ω2 Dt hint Eω E2
    hωL hΩ1L hΩ2L hDtL
  have locI : ∀ f : Vec3 × ℝ → ℝ, (∀ z ∈ D, IntegrableOn f (S (B z) ∩ D)) →
      LocallyIntegrableOn f D := fun f hf z hz =>
    ⟨S (B z) ∩ D, mem_nhdsWithin.2 ⟨S (B z), hSo _, hBS z hz, fun y hy => hy⟩, hf z hz⟩
  -- the glued weak identities
  have gw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ D →
      ∫ y in D, ω (A y) i y * spatialPartial ψ j y = -∫ y in D, Ω1 (B y) i j y * ψ y :=
    fun i j => vorticity_weak_glue_spatial hDo
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).1 i)
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).2.1 i j) j
      fun z hz => ⟨S (B z), hSo _, hBS z hz,
        vorticityTop_localIdentity (fun ψ y => spatialPartial ψ j y)
          (fun ψ y hy => vorticity_spatialPartial_off hy j)
          (Eω (B z) (admB z hz).1 (admB z hz).2 i)
          (E2 (B z) (admB z hz).1 (admB z hz).2 i j).1
          (hdw (B z) (admB z hz).1 (admB z hz).2 i j)⟩
  have gΩ : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ D →
      ∫ y in D, Ω1 (B y) i j y * spatialPartial ψ k y = -∫ y in D, Ω2 (B y) i j k y * ψ y :=
    fun i j k => vorticity_weak_glue_spatial hDo
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).2.1 i j)
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).2.2.1 i j k) k
      fun z hz => ⟨S (B z), hSo _, hBS z hz,
        vorticityTop_localIdentity (fun ψ y => spatialPartial ψ k y)
          (fun ψ y hy => vorticity_spatialPartial_off hy k)
          (E2 (B z) (admB z hz).1 (admB z hz).2 i j).1
          ((E2 (B z) (admB z hz).1 (admB z hz).2 i j).2.1 k)
          (hdΩ (B z) (admB z hz).1 (admB z hz).2 i j k)⟩
  have gt : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ D →
      ∫ y in D, ω (A y) i y * timePartial ψ y = -∫ y in D, Dt (B y) i y * ψ y :=
    fun i => vorticity_weak_glue_time hDo
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).1 i)
      (locI _ fun z hz => (IS (B z) (admB z hz).1 (admB z hz).2).2.2.2 i)
      fun z hz => ⟨S (B z), hSo _, hBS z hz,
        vorticityTop_localIdentity (fun ψ y => timePartial ψ y)
          (fun ψ y hy => vorticity_timePartial_off hy)
          (Eω (B z) (admB z hz).1 (admB z hz).2 i)
          (E2 (B z) (admB z hz).1 (admB z hz).2 i 0).2.2
          (hdt (B z) (admB z hz).1 (admB z hz).2 i)⟩
  have hcovD : D ⊆ ⋃ b ∈ A₀, S b := fun z hz => mem_iUnion₂.2 ⟨B z, hBA z hz, hBS z hz⟩
  have hSoP : ∀ c, @IsOpen ParabolicPoint _ (S c) := fun c => by
    have h := (parabolicHomeomorph.isOpen_preimage (s := S c)).2 (hSo c)
    rwa [parabolicHomeomorph_preimage] at h
  refine ⟨27 * Cb, by positivity, fun z i => ω (A z) i z, fun z i j => Ω1 (B z) i j z,
    fun z i j k => Ω2 (B z) i j k z, fun z i => Dt (B z) i z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the representative of the weak vorticity
    exact vorticityTopExtension_patchVorticity_ae D A₀ S hA₀c hcovD hDm A hSo ω
      (weakVorticity DU) hωae (fun b hb1 hb2 z hz i => E1 b hb1 hb2 z hz i) hA₀adm
  · -- continuity up to the top time
    exact vorticityTopExtension_continuousShift R₂ A ω hA1 hA2 hadmA F1 hωc
  · -- zero at the top time
    intro x hx
    have hAx : A (x, 0) = (x, 0) := by
      ext <;> simp [hA1, hA2]
    have hc2 : ((x, (0 : ℝ)) : Vec3 × ℝ).2 ∈ Ioc (-2 : ℝ) 0 := ⟨by norm_num, le_rfl⟩
    have hz := vorticityTop_zero hfam htrace hx (hωc (x, 0) hx hc2) (hωb (x, 0) hx hc2)
      (hωae (x, 0) hx hc2)
    funext i
    show ω (A (x, 0)) i (x, 0) = 0
    rw [hAx]
    exact hz x (by rw [sub_self, vec3EuclideanNorm_zero]; norm_num) i
  · -- the uniform bound
    intro x hx t ht
    obtain ⟨h1, h2, h3, h4⟩ := hadmA (x, t) hx ht
    refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    have hb : ∀ i, |ω (A (x, t)) i (x, t)| ≤ Cb := fun i =>
      hωb (A (x, t)) h1 h2 i (x, t)
        ⟨show vec3EuclideanNorm ((x, t).1 - (A (x, t)).1) ≤ 1 / 2 from le_of_lt h3,
          le_of_lt h4.1, h4.2⟩
    calc
      _ ≤ ∑ _i : Fin 3, Cb := Finset.sum_le_sum fun i _ => hb i
      _ = 3 * Cb := by
        rw [Fin.sum_univ_three]
        ring
      _ ≤ 27 * Cb := by linarith only [hCb]
  · -- the space-time weak derivatives
    have locV : ∀ {F : Type} [NormedAddCommGroup F] (f : ParabolicPoint → F),
        (∀ z ∈ D, IntegrableOn (fun y : Vec3 × ℝ => f y) (S (B z) ∩ D)) →
        LocallyIntegrableOn f
          (spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x} (Ioo (-2 : ℝ) 0)) :=
      fun {F} _ f hf z hz =>
        ⟨S (B z) ∩ D, mem_nhdsWithin.2 ⟨S (B z), hSoP _, hBS z hz, fun y hy => hy⟩, hf z hz⟩
    refine ⟨locV _ fun z hz => Integrable.of_eval fun i =>
        (IS (B z) (admB z hz).1 (admB z hz).2).1 i,
      locV _ fun z hz => Integrable.of_eval fun i => Integrable.of_eval fun j =>
        (IS (B z) (admB z hz).1 (admB z hz).2).2.1 i j,
      locV _ fun z hz => Integrable.of_eval fun i => Integrable.of_eval fun j =>
        Integrable.of_eval fun k => (IS (B z) (admB z hz).1 (admB z hz).2).2.2.1 i j k,
      locV _ fun z hz => Integrable.of_eval fun i =>
        (IS (B z) (admB z hz).1 (admB z hz).2).2.2.2 i,
      fun φ hφ => ⟨fun i j => gw i j φ hφ.1 hφ.2.1 hφ.2.2,
        fun i j k => gΩ i j k φ hφ.1 hφ.2.1 hφ.2.2, fun i => gt i φ hφ.1 hφ.2.1 hφ.2.2⟩⟩
  · -- square integrability on bounded sets
    intro S' hS' hS'b
    have hS'D : S' ⊆ D := hS'
    obtain ⟨F, hFadm, hFcov⟩ := vorticityTop_finiteCover hR₂ hS'D
      (vorticity_isBounded_of_parabolic hS'b)
    have hcov : S' ⊆ ⋃ c : F, (S c.1 ∩ D) := fun z hz => by
      obtain ⟨c, hcF, hzc⟩ := mem_iUnion₂.1 (hFcov hz)
      exact mem_iUnion.2 ⟨⟨c, hcF⟩, hzc, hS'D hz⟩
    refine lt_of_le_of_lt (lintegral_mono_set hcov) (lt_of_le_of_lt (lintegral_iUnion_le _ _) ?_)
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.2 fun c _ => ?_
    obtain ⟨hc1, hc2⟩ := hFadm c.1 c.2
    have hvec : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (S c.1 ∩ D)),
        (fun i => ω (A z) i z) = (fun i => ω c.1 i z) ∧
        (fun i j => Ω1 (B z) i j z) = (fun i j => Ω1 c.1 i j z) ∧
        (fun i j k => Ω2 (B z) i j k z) = (fun i j k => Ω2 c.1 i j k z) ∧
        (fun i => Dt (B z) i z) = (fun i => Dt c.1 i z) := by
      filter_upwards [ae_all_iff.2 (Eω c.1 hc1 hc2),
        ae_all_iff.2 fun i => ae_all_iff.2 fun j => (E2 c.1 hc1 hc2 i j).1,
        ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_all_iff.2 fun k =>
          (E2 c.1 hc1 hc2 i j).2.1 k,
        ae_all_iff.2 fun i => (E2 c.1 hc1 hc2 i 0).2.2] with z h1 h2 h3 h4
      exact ⟨funext h1, funext fun i => funext (h2 i),
        funext fun i => funext fun j => funext (h3 i j),
        funext h4⟩
    have hfin := vorticity_lintegral_four_lt_top
      (μ := (volume : Measure (Vec3 × ℝ)).restrict (S c.1))
      (MemLp.of_eval (hωL c.1 hc1 hc2)) (MemLp.of_eval fun i => MemLp.of_eval (hΩ1L c.1 hc1 hc2 i))
      (MemLp.of_eval fun i => MemLp.of_eval fun j => MemLp.of_eval (hΩ2L c.1 hc1 hc2 i j))
      (MemLp.of_eval (hDtL c.1 hc1 hc2))
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_))
      (lt_of_le_of_lt (lintegral_mono_set inter_subset_left) hfin)
    filter_upwards [hvec] with z hz
    simp only [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  · -- the differential inequality
    exact vorticityTopExtension_patchedDifferentialInequality D A₀ S A B ω Ω1 Ω2 Dt
      hA₀c hcovD hDm hDo hSo hA₀adm E1 E2 hineq hCb

end ESS
