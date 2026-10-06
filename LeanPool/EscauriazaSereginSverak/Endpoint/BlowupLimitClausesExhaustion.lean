/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyExhaustion

/-!
# Compactness on an exhaustion of space-time, with every slice

The diagonal compactness passage of `prop:blowup-limit` (via
`lem:compactness` of the CKN manuscript), exporting in addition the clause of `prop:blowup-limit`
(c) on time slices: at every negative time the limit slice is square
integrable on every compact set, and the slices of the subsequence converge
to it weakly in `L²` of that set.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Diagonal compactness for sequences that are uniformly controlled on each
fixed bounded past cylinder from a stage-dependent index on, with weak `L²`
convergence of every negative-time slice on every compact set
(`prop:blowup-limit`, via `lem:compactness` of the CKN manuscript). -/
theorem blowupLimitClauses_exhaustion_compactness
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (hf : ∀ n, Measurable (f n)) (hDf : ∀ n, Measurable (Df n))
    (hslice : ∀ C : Set Vec3, IsCompact C → ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f n (x,t))) ^ (2 : ℝ)) ≤ M)
    (hstage : ∀ m : ℕ, ∃ N : ℕ,
      (∀ n, N ≤ n → ∀ᵐ t ∂(volume.restrict (Ioo (-((m : ℝ) + 1)) 0)),
        ∀ i : Fin 3, HasWeakGradientOn (vec3Ball (0 : Vec3) ((m : ℝ) + 1))
          (fun x => f n (x,t) i) (fun x => Df n (x,t) i)) ∧
      (∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n, N ≤ n →
        (∫⁻ t in Icc (-((m : ℝ) + 1)) 0,
          ∫⁻ x in vec3Ball (0 : Vec3) ((m : ℝ) + 1),
            ENNReal.ofReal (spatialGradientSq (f n) (Df n) (x,t))) ≤ G) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ vec3Ball (0 : Vec3) ((m : ℝ) + 1) →
        ∀ a b : ℝ, Icc a b ⊆ Icc (-((m : ℝ) + 1)) 0 →
        ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
          HasCompactSupport w → tsupport w ⊆ C →
        ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
          ∀ n, N ≤ n → ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
            |(∫ x : Vec3, ∑ i : Fin 3, f n (x,t) i * w x i) -
              (∫ x : Vec3, ∑ i : Fin 3, f n (x,s) i * w x i)| ≤
              A * dist t s + B * (dist t s) ^ θ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ U : ParabolicPoint → Vec3, Measurable U ∧
    ∃ DU : ParabolicPoint → Fin 3 → Vec3, Measurable DU ∧
      (∀ t : ℝ, t < 0 → ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        Integrable (fun x => ∑ i : Fin 3, U (x,t) i * ψ x i) ∧
        Tendsto (fun k => ∫ x : Vec3, ∑ i : Fin 3, f (φ k) (x,t) i * ψ x i)
          atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, U (x,t) i * ψ x i))) ∧
      (∀ t : ℝ, t < 0 → ∀ C : Set Vec3, IsCompact C →
        MemLp (fun x => U (x,t)) 2 (volume.restrict C) ∧
        ∀ g : Vec3 → Vec3, MemLp g 2 (volume.restrict C) →
          Tendsto (fun k => ∫ x in C, ∑ i : Fin 3, f (φ k) (x,t) i * g x i)
            atTop (nhds (∫ x in C, ∑ i : Fin 3, U (x,t) i * g x i))) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
        Tendsto (fun k => eLpNorm (fun z => f (φ k) z - U z) 2
          (volume.restrict Q)) atTop (nhds 0)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
        ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ, MemLp w 2 (volume.restrict Q) →
        Tendsto (fun k => ∫ z in Q, Df (φ k) z i j * w z) atTop
          (nhds (∫ z in Q, DU z i j * w z))) ∧
      (∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => U (x,t) i) (fun x => DU (x,t) i)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
        MemLp DU 2 (volume.restrict Q)) := by
  classical
  choose N hN using hstage
  set ν := blowupLimitAssemblyIndex N with hνdef
  set w := blowupLimitAssemblyCutoffField f ν with hwdef
  set Dw := blowupLimitAssemblyCutoffGradient f Df ν with hDwdef
  have hwM : ∀ k, Measurable (w k) :=
    measurable_blowupLimitAssemblyCutoffField f ν hf
  have hDwM : ∀ k, Measurable (Dw k) :=
    measurable_blowupLimitAssemblyCutoffGradient f Df ν hf hDf
  have hνN : ∀ k, N k ≤ ν k := fun k => le_blowupLimitAssemblyIndex N le_rfl
  have hsliceBall : ∀ R : ℝ, 0 < R → ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
      (∫⁻ x in closure (vec3Ball (0 : Vec3) R),
        ENNReal.ofReal (vec3EuclideanNorm (f n (x,t))) ^ (2 : ℝ)) ≤ M :=
    fun R hR => hslice _ (isCompact_closure_vec3Ball hR)
  have hweak : ∀ k, ∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => w k (x,t) i) (fun x => Dw k (x,t) i) := by
    intro k
    obtain ⟨G, hG, hGb⟩ := (hN k).2.1
    obtain ⟨M, hM, hMb⟩ := hsliceBall ((k : ℝ) + 1) (by positivity)
    have hint := blowupLimitAssembly_slice_integrability (f (ν k)) (Df (ν k))
      (hf _) (hDf _) (by positivity : (0 : ℝ) < (k : ℝ) + 1)
      (-((k : ℝ) + 1)) 0 ⟨M, hM, fun t => hMb (ν k) t⟩ G hG (hGb (ν k) (hνN k))
    apply blowupLimitAssemblyCutoff_hasWeakGradientOn f Df ν k
    have hDint := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hint.2
    filter_upwards [(hN k).1 (ν k) (hνN k), hDint] with t h1 h2
    exact ⟨h1, fun i => hint.1 t i, h2⟩
  have hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ univ →
      ∀ a b : ℝ, Icc a b ⊆ Iio 0 →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t, t ∈ Icc a b →
        (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (w n (x,t))) ^
          (2 : ℝ) ∂volume) ≤ M := by
    intro C hC _ a b _
    obtain ⟨M, hM, hMb⟩ := hslice C hC
    refine ⟨M, hM, fun n t _ => ?_⟩
    calc
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (w n (x,t))) ^ (2 : ℝ)) ≤
          ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (ν n) (x,t))) ^ (2 : ℝ) :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal
            (blowupLimitAssemblyCutoffField_norm_le f ν n (x,t))) (by norm_num)
      _ ≤ M := hMb _ t
  have hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ univ →
      ∀ a b : ℝ, Icc a b ⊆ Iio 0 →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc a b, ∫⁻ x in C,
          ENNReal.ofReal (spatialGradientSq (w n) (Dw n) (x,t)) ∂volume) ≤ G := by
    intro C hC _ a b hab
    by_cases hab' : a ≤ b
    swap
    · refine ⟨0, by norm_num, fun n => ?_⟩
      rw [Icc_eq_empty hab', Measure.restrict_empty, lintegral_zero_measure]
    have hb : b < 0 := hab ⟨hab', le_rfl⟩
    obtain ⟨ρ, hρ⟩ := hC.exists_bound_of_continuousOn
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
    obtain ⟨j, hj⟩ := exists_nat_gt (max ρ (-a))
    have hjρ : ρ < j := (le_max_left _ _).trans_lt hj
    have hja : -a < j := (le_max_right _ _).trans_lt hj
    have hCj : ∀ x ∈ C, vec3EuclideanNorm x < j := by
      intro x hx
      have h := hρ x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg x)] at h
      exact h.trans_lt hjρ
    have hsingle : ∀ k, ∃ Bd : ℝ≥0∞, Bd < ⊤ ∧
        (∫⁻ t in Icc a b, ∫⁻ x in C,
          ENNReal.ofReal (spatialGradientSq (w k) (Dw k) (x,t))) ≤ Bd := by
      intro k
      obtain ⟨G, hG, hGb⟩ := (hN k).2.1
      obtain ⟨M, hM, hMb⟩ := hsliceBall ((k : ℝ) + 1) (by positivity)
      exact blowupLimitAssemblyCutoff_gradient_bound_single f Df ν k hf hDf
        ⟨M, hM, fun t => hMb (ν k) t⟩ G hG (hGb (ν k) (hνN k)) C a b hb.le
    choose Bd hBd hBdb using hsingle
    obtain ⟨Gj, hGj, hGjb⟩ := (hN j).2.1
    refine ⟨Gj + ∑ k ∈ Finset.range (j + 1), Bd k,
      ENNReal.add_lt_top.mpr ⟨hGj, ENNReal.sum_lt_top.mpr fun k _ => hBd k⟩, ?_⟩
    intro k
    rcases le_total k j with hkj | hjk
    · calc
        (∫⁻ t in Icc a b, ∫⁻ x in C,
            ENNReal.ofReal (spatialGradientSq (w k) (Dw k) (x,t))) ≤ Bd k :=
          hBdb k
        _ ≤ ∑ k ∈ Finset.range (j + 1), Bd k :=
          Finset.single_le_sum (fun _ _ => zero_le)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hkj))
        _ ≤ Gj + ∑ k ∈ Finset.range (j + 1), Bd k := le_add_self
    · have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
      have heq : ∀ t ∈ Icc a b, ∀ x ∈ C,
          ENNReal.ofReal (spatialGradientSq (w k) (Dw k) (x,t)) =
            ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x,t)) := by
        intro t ht x hx
        have hxk : (x,t).1 ∈ vec3Ball (0 : Vec3) (k : ℝ) := by
          rw [mem_vec3Ball, sub_zero]
          exact (hCj x hx).trans_le hjk'
        have htk : -(k : ℝ) ≤ (x,t).2 := by
          change -(k : ℝ) ≤ t
          linarith only [ht.1, hja, hjk']
        have hD : Dw k (x,t) = Df (ν k) (x,t) :=
          (blowupLimitAssemblyCutoff_eq_of_mem f Df ν hxk htk).2
        unfold spatialGradientSq
        rw [hD]
      have hCsub : C ⊆ vec3Ball (0 : Vec3) ((j : ℝ) + 1) := by
        intro x hx
        rw [mem_vec3Ball, sub_zero]
        linarith only [hCj x hx]
      have hIsub : Icc a b ⊆ Icc (-((j : ℝ) + 1)) 0 := by
        intro t ht
        exact ⟨by linarith only [ht.1, hja], ht.2.trans hb.le⟩
      calc
        (∫⁻ t in Icc a b, ∫⁻ x in C,
            ENNReal.ofReal (spatialGradientSq (w k) (Dw k) (x,t))) =
            ∫⁻ t in Icc a b, ∫⁻ x in C,
              ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x,t)) :=
          setLIntegral_congr_fun measurableSet_Icc fun t ht =>
            setLIntegral_congr_fun hC.measurableSet fun x hx => heq t ht x hx
        _ ≤ ∫⁻ t in Icc a b, ∫⁻ x in vec3Ball (0 : Vec3) ((j : ℝ) + 1),
              ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x,t)) :=
          lintegral_mono fun t => lintegral_mono_set hCsub
        _ ≤ ∫⁻ t in Icc (-((j : ℝ) + 1)) 0,
              ∫⁻ x in vec3Ball (0 : Vec3) ((j : ℝ) + 1),
              ENNReal.ofReal (spatialGradientSq (f (ν k)) (Df (ν k)) (x,t)) :=
          lintegral_mono_set hIsub
        _ ≤ Gj := hGjb (ν k) (le_blowupLimitAssemblyIndex N hjk)
        _ ≤ Gj + ∑ k ∈ Finset.range (j + 1), Bd k := le_self_add
  have hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ univ →
      ∀ a b : ℝ, Icc a b ⊆ Iio 0 →
      ∀ ψ : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, w n (x,t) i * ψ x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, w n (x,s) i * ψ x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ :=
    fun C hC _ a b hab ψ hψ hψc hψC =>
      blowupLimitAssemblyCutoff_modulus f N (fun m => (hN m).2.2) C hC a b hab
        ψ hψ hψc hψC
  obtain ⟨σ, hσ, v, hv, g, hg, hC1, hC2, hC3, hC4, _, _, hC7⟩ :=
    CKN.Leray.lem_compactness isOpen_univ isOpen_Iio ordConnected_Iio w Dw
      hwM hDwM hweak hbound hgradBound hmod
  -- eventual agreement on compact sets
  have hev : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ z ∈ Q, w (σ k) z = f (ν (σ k)) z ∧ Dw (σ k) z = Df (ν (σ k)) z := by
    intro Q hQ
    obtain ⟨ρ, hρ⟩ := blowupLimitAssembly_compact_bound hQ
    obtain ⟨K, hK⟩ := blowupLimitAssemblyCutoff_eventually_eq f Df ν ρ
    refine ⟨K, fun k hk z hz => ?_⟩
    exact hK (σ k) (hk.trans (hσ.id_le k)) z (hρ z hz).1 (hρ z hz).2
  let DU : ParabolicPoint → Fin 3 → Vec3 := fun z i m => g z i m
  have hDU : Measurable DU := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro m
    exact (CKN.Leray.gradientCoordinateCLM i m).continuous.measurable.comp hg
  refine ⟨fun k => ν (σ k), (strictMono_blowupLimitAssemblyIndex N).comp hσ,
    v, hv, DU, hDU, ?_, ?_, ?_, ?_, hC4, ?_⟩
  · -- every negative-time slice, smooth tests
    intro t ht ψ hψ hψc
    set C : Set Vec3 := tsupport ψ
    have hCc : IsCompact C := hψc
    obtain ⟨hs, hl, hweakC⟩ := hC1 ⟨t, ht⟩ C hCc (subset_univ _)
    have hψC : ∀ x ∉ C, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hWc : Continuous (fun x => (WithLp.toLp 2 (ψ x) : L2Vec3)) :=
      (PiLp.continuous_toLp 2 _).comp hψ.continuous
    have hWsupp : HasCompactSupport (fun x => (WithLp.toLp 2 (ψ x) : L2Vec3)) :=
      hψc.comp_left (by simp)
    have hW : MemLp (fun x => (WithLp.toLp 2 (ψ x) : L2Vec3)) 2
        (volume.restrict C) :=
      (hWc.memLp_of_hasCompactSupport hWsupp).restrict C
    refine ⟨blowupLimitAssembly_integrable_pairing (fun x => v (x,t)) ψ hψC hl hW, ?_⟩
    have hlim := hweakC (hW.toLp _)
    rw [blowupLimitAssembly_inner_eq_pairing (fun x => v (x,t)) ψ hψC hl hW] at hlim
    obtain ⟨K, hK⟩ := hev (C ×ˢ {t}) (hCc.prod isCompact_singleton)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [blowupLimitAssembly_inner_eq_pairing (fun x => w (σ k) (x,t)) ψ hψC (hs k) hW]
    congr 1
    funext x
    by_cases hx : x ∈ C
    · rw [(hK k hk (x,t) ⟨hx, rfl⟩).1]
    · simp [hψC x hx]
  · -- every negative-time slice, square-integrable tests on compact sets
    intro t ht C hCc
    obtain ⟨hs, hl, hweakC⟩ := hC1 ⟨t, ht⟩ C hCc (subset_univ _)
    have hlVec : MemLp (fun x => v (x,t)) 2 (volume.restrict C) :=
      hl.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
    refine ⟨hlVec, fun g hg => ?_⟩
    have hG : MemLp (fun x => (WithLp.toLp 2 (g x) : L2Vec3)) 2 (volume.restrict C) :=
      hg.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    have hlim := hweakC (hG.toLp _)
    rw [CKN.Leray.inner_toLp_vec3_eq_integral_dot_measure _ _ _ hl hG] at hlim
    obtain ⟨K, hK⟩ := hev (C ×ˢ {t}) (hCc.prod isCompact_singleton)
    have hlim' : Tendsto (fun k => ∫ x in C, ∑ i : Fin 3,
        (WithLp.toLp 2 (w (σ k) (x,t)) : L2Vec3) i * (WithLp.toLp 2 (g x) : L2Vec3) i)
        atTop (nhds (∫ x in C, ∑ i : Fin 3,
          (WithLp.toLp 2 (v (x,t)) : L2Vec3) i * (WithLp.toLp 2 (g x) : L2Vec3) i)) := by
      refine hlim.congr fun k => ?_
      rw [CKN.Leray.inner_toLp_vec3_eq_integral_dot_measure _ _ _ (hs k) hG]
    simp only at hlim'
    apply hlim'.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    apply setIntegral_congr_fun hCc.measurableSet
    intro x hx
    simp only [(hK k hk (x,t) ⟨hx, rfl⟩).1]
  · -- strong local convergence
    intro Q hQ hQI
    have hlim := hC2 Q hQ hQI
    obtain ⟨K, hK⟩ := hev Q hQ
    have hQm : MeasurableSet Q := hQ.measurableSet
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall fun k => zero_le
    · filter_upwards [eventually_ge_atTop K] with k hk
      have hmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ => f (ν (σ k)) z - v z)
          (volume.restrict Q) := ((hf _).sub hv).aestronglyMeasurable
      calc
        eLpNorm (fun z : Vec3 × ℝ => f (ν (σ k)) z - v z) 2 (volume.restrict Q) ≤
            eLpNorm (fun z : Vec3 × ℝ => (WithLp.toLp 2 (f (ν (σ k)) z) : L2Vec3) -
              WithLp.toLp 2 (v z)) 2 (volume.restrict Q) :=
          eLpNorm_mono hmeas fun z => blowupLimitAssembly_norm_sub_le _ _
        _ = eLpNorm ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (w (σ k) z) : L2Vec3)) -
              (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
              (volume.restrict Q) := by
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_mem hQm] with z hz
          simp only [Pi.sub_apply, (hK k hk z hz).1]
  · -- weak gradient convergence
    intro Q hQ hQI i j ψ hψ
    obtain ⟨hs, hl, hweakQ⟩ := hC3 Q hQ hQI
    have hlim := CKN.Leray.weak_l2_scalar_integral_of_fiber_weak
      (CKN.Leray.gradientCoordinateCLM i j)
      (fun k z => CKN.Leray.toCompactnessGradientFiber (Dw (σ k) z))
      (hl.toLp g) hs hweakQ ψ hψ
    simp only [CKN.Leray.gradientCoordinateCLM_toCompactnessGradientFiber] at hlim
    have hlimEq : (∫ z, CKN.Leray.gradientCoordinateCLM i j
        ((hl.toLp g : Lp CKN.Leray.CompactnessGradientFiber 2 (volume.restrict Q)) z) *
          ψ z ∂(volume.restrict Q)) = ∫ z in Q, DU z i j * ψ z := by
      apply integral_congr_ae
      filter_upwards [hl.coeFn_toLp] with z hz
      rw [hz]
      rfl
    obtain ⟨K, hK⟩ := hev Q hQ
    have hlim' : Tendsto (fun k => ∫ z in Q, Dw (σ k) z i j * ψ z) atTop
        (nhds (∫ z in Q, DU z i j * ψ z)) := by
      convert hlim using 2
      all_goals first
        | rfl
        | exact hlimEq.symm
    apply hlim'.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    apply setIntegral_congr_fun hQ.measurableSet
    intro z hz
    simp only [(hK k hk z hz).2]
  · -- square integrability of the limit gradient
    intro Q hQ hQI
    obtain ⟨ρ, hρ⟩ := blowupLimitAssembly_compact_bound hQ
    obtain ⟨b, hb, hbQ⟩ : ∃ b : ℝ, b < 0 ∧ ∀ z ∈ Q, z.2 ≤ b := by
      rcases Q.eq_empty_or_nonempty with hempty | hne
      · exact ⟨-1, by norm_num, fun z hz => by simp [hempty] at hz⟩
      · obtain ⟨z₀, hz₀, hmax⟩ := hQ.exists_isMaxOn hne
          (continuous_snd (X := Vec3) (Y := ℝ)).continuousOn
        exact ⟨z₀.2, (hQI hz₀).2, fun z hz => hmax hz⟩
    set C : Set Vec3 := closure (vec3Ball (0 : Vec3) (|ρ| + 1))
    have hCc : IsCompact C := isCompact_closure_vec3Ball (by positivity)
    have hIab : Icc (-ρ) b ⊆ Iio 0 := fun t ht => ht.2.trans_lt hb
    obtain ⟨G, hG, hGb⟩ := hgradBound C hCc (subset_univ _) (-ρ) b hIab
    have hlimBound := hC7 C hCc (subset_univ _) (-ρ) b hIab G hG hGb
    apply blowupLimitAssembly_memLp_gradient_of_energy (fun _ => (0 : Vec3)) DU hDU
      C (-ρ) b (lt_of_le_of_lt hlimBound hG) Q
    intro z hz
    refine ⟨subset_closure ?_, (hρ z hz).2, hbQ z hz⟩
    rw [mem_vec3Ball, sub_zero]
    linarith only [(hρ z hz).1, le_abs_self ρ]


end ESS

end
