/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitInterpolation
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTenThirdsVector
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuityInputsData

/-!
# Subcritical convergence in the Leray limit

Strong `L²` convergence on a time slab together with a uniform `L^(10/3)`
bound gives strong convergence in every exponent `2 ≤ q < 10/3`, as in
`prop:leray-limit`. Neither square integrability of the individual fields nor
integrability of the limit is assumed: both follow from the two hypotheses.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A strong `L²` limit of a sequence that is uniformly bounded in `L^(10/3)`
is a strong limit in every intermediate exponent. The limit is not assumed to be
measurable or integrable; this follows from the two hypotheses. -/
theorem lerayLimit_subcritical_of_strongL2_and_tenThirds
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {U : ℕ → α → E} {u : α → E} {B : ℝ≥0∞}
    (hB : B < ⊤)
    (hhigh : ∀ n, MemLp (U n) (ENNReal.ofReal (10 / 3 : ℝ)) μ ∧
      eLpNorm (U n) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ B)
    (h2 : Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal 2) μ)
      atTop (𝓝 0)) :
    ∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
        atTop (𝓝 0) := by
  have hmeasure : TendstoInMeasure μ U atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (μ := μ) (p := ENNReal.ofReal 2) (f := U) (g := u) (l := atTop)
      (by norm_num) h2
  obtain ⟨ns, _, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have humeas : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun i => (hhigh (ns i)).1.aestronglyMeasurable) hae
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
      (p := ENNReal.ofReal (10 / 3 : ℝ))
      (fun i => (hhigh (ns i)).1.aestronglyMeasurable) u humeas hae
  have hliminf : atTop.liminf
      (fun i => eLpNorm (U (ns i)) (ENNReal.ofReal (10 / 3 : ℝ)) μ) ≤ B :=
    liminf_le_of_frequently_le' <|
      (Eventually.of_forall fun i => (hhigh (ns i)).2).frequently
  have huHigh : eLpNorm u (ENNReal.ofReal (10 / 3 : ℝ)) μ < ⊤ :=
    lt_of_le_of_lt (hFatou.trans hliminf) hB
  have hfinite : ∀ᶠ n : ℕ in atTop,
      eLpNorm (U n - u) (ENNReal.ofReal 2) μ < 1 :=
    (ENNReal.tendsto_nhds_zero.mp h2 (1 / 2 : ℝ≥0∞) (by norm_num)).mono
      fun _ hn => lt_of_le_of_lt hn (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinite
  let F : ℕ → α → E := fun k => U (k + N) - u
  have hFsub (k : ℕ) : F k - 0 = U (k + N) - u := sub_zero (F k)
  have hFlow (k : ℕ) : MemLp (F k) (ENNReal.ofReal 2) μ :=
    memLp_iff.mpr
      (lt_trans (hN (k + N) (Nat.le_add_left N k)) ENNReal.one_lt_top)
  have hFbound : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k, eLpNorm (F k) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ C := by
    refine ⟨B + eLpNorm u (ENNReal.ofReal (10 / 3 : ℝ)) μ,
      ENNReal.add_lt_top.mpr ⟨hB, huHigh⟩, fun k => ?_⟩
    calc
      eLpNorm (F k) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
          eLpNorm (U (k + N)) (ENNReal.ofReal (10 / 3 : ℝ)) μ +
            eLpNorm u (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
        eLpNorm_sub_le (p := ENNReal.ofReal (10 / 3 : ℝ)) (μ := μ)
          (f := U (k + N)) (g := u) (by norm_num)
      _ ≤ B + eLpNorm u (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
        add_le_add (hhigh (k + N)).2 le_rfl
  have hF2 : Tendsto (fun k => eLpNorm (F k - 0) (ENNReal.ofReal 2) μ)
      atTop (𝓝 0) := by
    simp_rw [hFsub]
    exact (tendsto_add_atTop_iff_nat
      (f := fun n => eLpNorm (U n - u) (ENNReal.ofReal 2) μ) N).mpr h2
  intro q hqLower hqUpper
  have hFq := lerayLimit_strongLp_of_strongL2_and_uniform_high
    (μ := μ) (F := F) (G := 0) hFlow hFbound hF2 q hqLower hqUpper
  simp_rw [hFsub] at hFq
  exact (tendsto_add_atTop_iff_nat
    (f := fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ) N).mp hFq
variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


/-- The subcritical convergence of `prop:leray-limit` for a selected sequence of
regularized solutions: strong `L²` convergence on the time slab `(0,T)` upgrades
to strong convergence in every exponent `2 ≤ q < 10/3`, the uniform
`L^(10/3)` bound coming from the regularized energy identity. -/
theorem lerayLimit_regularised_subcritical
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (σ : ℕ → ℕ) (T : ℝ) (u : ParabolicPoint → Vec3)
    (h2 : Tendsto
      (fun n => eLpNorm (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal 2)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
      atTop (𝓝 0)) :
    ∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto
        (fun n => eLpNorm (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal q)
          (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
        atTop (𝓝 0) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))
  obtain ⟨B, _, hB⟩ := regEquicontinuity_regularized_velocity_tenThirds_bound
    ρ uε pε hregularised a ha (fun n => εseq (σ n)) (fun n => hseq (σ n))
  have hle : μ ≤ regUniformPositiveTimeMeasure := by
    refine Measure.restrict_mono (fun z hz => ?_) le_rfl
    exact ⟨hz.1, hz.2.1⟩
  have hvector := lerayLimit_vector_tenThirds_of_component_bounds μ
    (fun n => uε a ha (εseq (σ n))) (ENNReal.ofReal B)
    (fun n i => (hB n i).1.mono_measure hle)
    (fun n i => (eLpNorm_mono_measure _ hle).trans (hB n i).2)
  exact lerayLimit_subcritical_of_strongL2_and_tenThirds
    (μ := μ) (U := fun n => uε a ha (εseq (σ n))) (u := u)
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hvector h2

end CKN.Leray

end
