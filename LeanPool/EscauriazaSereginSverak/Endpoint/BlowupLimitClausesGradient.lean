/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesWeak
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientComponent

/-!
# Weak gradient convergence up to the top face

Clause (c) of `prop:blowup-limit` for the gradients: the weak `L²` convergence
of the rescaled gradients on compact subsets of the open past, together with
the uniform `L²` bound of clause (a) on a bounded cylinder `B_R × (a, 0)`
including its top face, gives weak convergence in `L²(B_R × (a, 0))`, and the
limit gradient is square integrable there.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Weak `L²` convergence on a compact set gives weak `L²` convergence on each
measurable subset. -/
theorem blowupLimitClauses_weak_restrict_subset
    {K S : Set (Vec3 × ℝ)} (hS : MeasurableSet S) (hSK : S ⊆ K)
    {g : ℕ → Vec3 × ℝ → ℝ} {G : Vec3 × ℝ → ℝ}
    (hweak : ∀ w : Vec3 × ℝ → ℝ, MemLp w 2 (volume.restrict K) →
      Tendsto (fun k => ∫ z in K, g k z * w z) atTop (𝓝 (∫ z in K, G z * w z)))
    (w : Vec3 × ℝ → ℝ) (hw : MemLp w 2 (volume.restrict S)) :
    Tendsto (fun k => ∫ z in S, g k z * w z) atTop (𝓝 (∫ z in S, G z * w z)) := by
  have hrestr : (volume.restrict K).restrict S = volume.restrict S := by
    rw [Measure.restrict_restrict hS, Set.inter_eq_left.mpr hSK]
  have hwK : MemLp (S.indicator w) 2 (volume.restrict K) := by
    rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hS, hrestr]
    exact hw
  have hpair : ∀ f : Vec3 × ℝ → ℝ,
      ∫ z in K, f z * S.indicator w z = ∫ z in S, f z * w z := by
    intro f
    have hfun : (fun z => f z * S.indicator w z) = S.indicator (fun z => f z * w z) := by
      funext z
      by_cases hz : z ∈ S
      · simp [hz]
      · simp [hz]
    rw [hfun, integral_indicator hS, hrestr]
  have h := hweak _ hwK
  simp only [hpair] at h
  exact h

/-- The limit gradient is square integrable on every bounded past cylinder
including its top face, and the rescaled gradients converge to it weakly in
`L²` there (`prop:blowup-limit`, clause (c)). -/
theorem blowupLimitClauses_gradient_weak_to_top
    {Du Dm : ParabolicPoint → Fin 3 → Vec3} (hDm : Measurable Dm)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    {x₀ : Vec3} {t₀ : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) {φ : ℕ → ℕ}
    {DU : ParabolicPoint → Fin 3 → Vec3} (hDU : Measurable DU)
    (hweakK : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
      ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ, MemLp w 2 (volume.restrict Q) →
        Tendsto (fun k => ∫ z in Q, blowupGradient x₀ t₀ (r (φ k)) Dm z i j * w z) atTop
          (𝓝 (∫ z in Q, DU z i j * w z)))
    (hDUmem : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
      MemLp DU 2 (volume.restrict Q))
    {R a : ℝ} (ha : a < 0) {C : ℝ}
    (hbound : ∀ᶠ k in atTop,
      IntegrableOn (fun z => spatialGradientSq (fun _ => (0 : Vec3))
        (blowupGradient x₀ t₀ (r (φ k)) Du) z) (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) ∧
      (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0), spatialGradientSq (fun _ => (0 : Vec3))
        (blowupGradient x₀ t₀ (r (φ k)) Du) z) ≤ C)
    (i j : Fin 3) :
    MemLp (fun z : Vec3 × ℝ => DU z i j) 2 (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      ∀ w : Vec3 × ℝ → ℝ, MemLp w 2 (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) →
        Tendsto (fun k => ∫ z in vec3Ball 0 R ×ˢ Ioo a 0,
            blowupGradient x₀ t₀ (r (φ k)) Du z i j * w z) atTop
          (𝓝 (∫ z in vec3Ball 0 R ×ˢ Ioo a 0, DU z i j * w z)) := by
  set Q : Set (Vec3 × ℝ) := vec3Ball 0 R ×ˢ Ioo a 0 with hQdef
  set δ : ℕ → ℝ := fun n => -a / ((n : ℝ) + 2) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos (neg_pos.mpr ha) (by positivity)
  have hδlt : ∀ n, δ n < -a := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact div_lt_self (neg_pos.mpr ha) (by linarith only [hn0])
  have hδanti : Antitone δ := by
    intro m n hmn
    apply div_le_div_of_nonneg_left (neg_pos.mpr ha).le (by positivity)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith only [this]
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (-a)
    rw [mul_zero] at h
    apply squeeze_zero (fun n => (hδpos n).le) _ h
    intro n
    simp only [δ, one_div]
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (neg_pos.mpr ha).le
    apply inv_anti₀
    · positivity
    · linarith only
  set S : ℕ → Set (Vec3 × ℝ) := fun n => vec3Ball 0 R ×ˢ Ioo a (-δ n) with hSdef
  set K : ℕ → Set (Vec3 × ℝ) := fun n => closure (vec3Ball (0 : Vec3) R) ×ˢ Icc a (-δ n)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo
  have hSmono : Monotone S := by
    intro m n hmn
    apply prod_mono subset_rfl
    apply Ioo_subset_Ioo_right
    linarith only [hδanti hmn]
  have hSQ : ⋃ n, S n = Q := by
    ext z
    simp only [mem_iUnion, S, Q, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨n, hz1, hz2, hz3⟩
      exact ⟨hz1, hz2, hz3.trans (neg_neg_of_pos (hδpos n))⟩
    · rintro ⟨hz1, hz2, hz3⟩
      obtain ⟨n, hn⟩ := (hδlim.eventually (gt_mem_nhds (neg_pos.mpr hz3))).exists
      exact ⟨n, hz1, hz2, by linarith only [hn]⟩
  have hSK : ∀ n, S n ⊆ K n := fun n =>
    prod_mono subset_closure Ioo_subset_Icc_self
  have hKc : ∀ n, IsCompact (K n) := by
    intro n
    have hball : IsCompact (closure (vec3Ball (0 : Vec3) R)) := by
      have hbd : Bornology.IsBounded (vec3Ball (0 : Vec3) R) := by
        refine (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := R)).subset ?_
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        have hy' : vec3EuclideanNorm (y - 0) < R := hy
        rw [sub_zero] at hy'
        exact (norm_le_vec3EuclideanNorm _).trans hy'.le
      exact hbd.isCompact_closure
    exact hball.prod isCompact_Icc
  have hKneg : ∀ n, K n ⊆ univ ×ˢ Iio 0 := by
    intro n z hz
    exact ⟨mem_univ _, lt_of_le_of_lt hz.2.2 (neg_neg_of_pos (hδpos n))⟩
  -- the rescaled gradients with the measurable representative
  have hae : ∀ k, (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) =ᵐ[volume]
      (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Du z i j) := by
    intro k
    filter_upwards [blowupLimitAssembly_blowupGradient_ae_eq hDmEq x₀ t₀ (r (φ k)) (hr _)]
      with z hz
    rw [hz]
  have hgm : ∀ k, Measurable (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) := by
    intro k
    have h := measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ (r (φ k))
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h)
  -- the uniform bound on the full cylinder
  have hg : ∀ᶠ k in atTop,
      MemLp (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) 2
        (volume.restrict Q) ∧
      (eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) 2
        (volume.restrict Q)).toReal ≤ Real.sqrt (max C 0) := by
    filter_upwards [hbound] with k hk
    have hDuMeas : AEStronglyMeasurable (blowupGradient x₀ t₀ (r (φ k)) Du)
        (volume.restrict (spaceTimeSet (vec3Ball 0 R) (Ioo a 0))) := by
      have hmD := measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ (r (φ k))
      exact (hmD.aestronglyMeasurable.congr
        (blowupLimitAssembly_blowupGradient_ae_eq hDmEq x₀ t₀ (r (φ k)) (hr _))).restrict
    have hrow := blowup_gradient_component_eLpNorm_le_of_integral_bound
      (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) (fun _ => (0 : Vec3))
      (blowupGradient x₀ t₀ (r (φ k)) Du) i C hDuMeas hk.1 hk.2
    have hcomp : eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) 2
        (volume.restrict Q) ≤ (ENNReal.ofReal C) ^ (1 / 2 : ℝ) := by
      have h1 : eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) 2
          (volume.restrict Q) =
          eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Du z i j) 2
            (volume.restrict Q) :=
        eLpNorm_congr_ae (ae_restrict_of_ae (hae k))
      have h2 : eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Du z i j) 2
          (volume.restrict Q) ≤
          eLpNorm (fun z : Vec3 × ℝ => vec3EuclideanNorm
            (blowupGradient x₀ t₀ (r (φ k)) Du z i)) 2 (volume.restrict Q) := by
        apply eLpNorm_mono_real
        · exact ((hgm k).aestronglyMeasurable.congr (hae k)).restrict
        · intro z
          exact (norm_le_pi_norm _ j).trans (norm_le_vec3EuclideanNorm _)
      rw [h1]
      exact h2.trans hrow
    have hfin : (ENNReal.ofReal C) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    refine ⟨memLp_iff.2 (hcomp.trans_lt hfin), ?_⟩
    calc
      (eLpNorm (fun z : Vec3 × ℝ => blowupGradient x₀ t₀ (r (φ k)) Dm z i j) 2
          (volume.restrict Q)).toReal ≤ ((ENNReal.ofReal C) ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono hfin.ne hcomp
      _ = Real.sqrt (max C 0) := by
        rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal', Real.sqrt_eq_rpow]
  -- weak convergence on each exhausting set
  have hweakS : ∀ n (w : Vec3 × ℝ → ℝ), MemLp w 2 (volume.restrict (S n)) →
      Tendsto (fun k => ∫ z in S n, (fun z : Vec3 × ℝ =>
          blowupGradient x₀ t₀ (r (φ k)) Dm z i j) z * w z) atTop
        (𝓝 (∫ z in S n, (fun z : Vec3 × ℝ => DU z i j) z * w z)) := fun n w hw =>
    blowupLimitClauses_weak_restrict_subset (hSm n) (hSK n)
      (fun w' hw' => hweakK (K n) (hKc n) (hKneg n) i j w' hw') w hw
  have hGS : ∀ n, MemLp (fun z : Vec3 × ℝ => DU z i j) 2 (volume.restrict (S n)) := by
    intro n
    have h := ((hDUmem (K n) (hKc n) (hKneg n)).eval i).eval j
    exact h.mono_measure (Measure.restrict_mono_set volume (hSK n))
  have hGm : AEStronglyMeasurable (fun z : Vec3 × ℝ => DU z i j) (volume.restrict Q) :=
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hDU)).aestronglyMeasurable
  obtain ⟨hGQ, -, hlim⟩ := blowupLimitClauses_weak_L2_of_exhaustion hSm hSmono hSQ hg hGm hGS
    hweakS
  refine ⟨hGQ, fun w hw => ?_⟩
  refine (hlim w hw).congr fun k => ?_
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (hae k)] with z hz
  rw [hz]

end ESS

end
