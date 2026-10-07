/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticEquation
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegSlab

/-!
# Weak time derivatives from pointwise time derivatives

A function on a slab which is differentiable in time at every point of space, whose time derivative
is square integrable on every slab strictly inside, has that time derivative as its weak time
derivative against smooth compactly supported tests on the slab (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The time projection of the support of a space-time test function lies in a closed interval
strictly inside the time interval. -/
theorem lps_test_time_margin {a T : ℝ} (hab : a < T) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a T)) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < T ∧ ∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → z ∉ tsupport φ := by
  obtain ⟨-, hc, hsupp⟩ := hφ
  set K : Set ℝ := (fun z : Vec3 × ℝ => z.2) '' tsupport φ with hK
  have hKc : IsCompact K := hc.isCompact.image continuous_snd
  have hKsub : K ⊆ Ioo a T := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hsupp hz).2
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨a + (T - a) / 3, a + 2 * (T - a) / 3, ?_, ?_, ?_, ?_⟩
    · linarith only [hab]
    · linarith only [hab]
    · linarith only [hab]
    · intro z _ hz
      have : z.2 ∈ K := ⟨z, hz, rfl⟩
      rw [hempty] at this
      exact this
  · have h1 : sInf K ∈ K := hKc.sInf_mem hne
    have h2 : sSup K ∈ K := hKc.sSup_mem hne
    have h3 : sInf K ≤ sSup K := (csInf_le hKc.bddBelow h2)
    have h4 := hKsub h1
    have h5 := hKsub h2
    refine ⟨(a + sInf K) / 2, (sSup K + T) / 2, ?_, ?_, ?_, ?_⟩
    · linarith only [h4.1]
    · linarith only [h4.1, h5.2, h3]
    · linarith only [h5.2]
    · intro z hz hzs
      have hzK : z.2 ∈ K := ⟨z, hzs, rfl⟩
      apply hz
      exact ⟨by linarith only [csInf_le hKc.bddBelow hzK, h4.1],
        by linarith only [le_csSup hKc.bddAbove hzK, h5.2]⟩

/-- A function differentiable in time at every point of space, with time derivative square
integrable on every slab strictly inside, has that derivative as weak time derivative on the slab
(`prop:lps-local-strong`). -/
theorem lps_slab_time_weak_of_pointwise {a T : ℝ} (hab : a < T) {f g : Vec3 × ℝ → ℝ}
    (hd : ∀ x : Vec3, ∀ t ∈ Ioo a T, HasDerivAt (fun s => f (x, s)) (g (x, t)) t)
    (hgc : ∀ x : Vec3, ContinuousOn (fun s => g (x, s)) (Ioo a T))
    (hf : ∀ a' b', a < a' → a' < b' → b' < T → MemLp f 2 (volume.restrict (vlSlab a' b')))
    (hg : ∀ a' b', a < a' → a' < b' → b' < T → MemLp g 2 (volume.restrict (vlSlab a' b')))
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a T)) :
    ∫ z in vlSlab a T, f z * timePartial φ z = -∫ z in vlSlab a T, g z * φ z := by
  obtain ⟨a', b', h1, h2, h3, hout⟩ := lps_test_time_margin hab hφ
  have hφ0 : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (hout z hz)
  have hφt0 : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → timePartial φ z = 0 := fun z hz =>
    CKN.timePartial_eq_zero_off_tsupport (hout z hz)
  have hsub : vlSlab a' b' ⊆ vlSlab a T := fun z hz =>
    ⟨hz.1, ⟨by linarith only [h1, hz.2.1], by linarith only [h3, hz.2.2]⟩⟩
  have hmeas : MeasurableSet (vlSlab a' b') := MeasurableSet.univ.prod measurableSet_Ioo
  have hmeasT : MeasurableSet (vlSlab a T) := MeasurableSet.univ.prod measurableSet_Ioo
  have hred : ∀ F : Vec3 × ℝ → ℝ, (∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → F z = 0) →
      ∫ z in vlSlab a T, F z = ∫ z in vlSlab a' b', F z := fun F hF =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasT hsub fun z hz =>
      hF z fun hz2 => hz.2 ⟨hz.1.1, hz2⟩
  rw [hred _ (fun z hz => by rw [hφt0 z hz, mul_zero]),
    hred _ (fun z hz => by rw [hφ0 z hz, mul_zero])]
  obtain ⟨hT0, -, hT2⟩ := lps_test_memLp_slab hφ 0
  have hT0' := hT0.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hT2' := hT2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hIf : Integrable (fun z => f z * timePartial φ z) (volume.restrict (vlSlab a' b')) :=
    (hf a' b' h1 h2 h3).integrable_mul hT2'
  have hIg : Integrable (fun z => g z * φ z) (volume.restrict (vlSlab a' b')) :=
    (hg a' b' h1 h2 h3).integrable_mul hT0'
  have key : ∀ x : Vec3, (∫ t in Ioo a' b', f (x, t) * timePartial φ (x, t)) =
      -∫ t in Ioo a' b', g (x, t) * φ (x, t) := by
    intro x
    have hdiff : Differentiable ℝ (fun s : ℝ => φ (x, s)) :=
      (hφ.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hv : ∀ t ∈ [[a', b']], HasDerivAt (fun s : ℝ => φ (x, s)) (timePartial φ (x, t)) t :=
      fun t _ => (hdiff t).hasFDerivAt.hasDerivAt
    have hIcc : [[a', b']] ⊆ Ioo a T := by
      rw [uIcc_of_le h2.le]
      exact fun t ht => ⟨by linarith only [h1, ht.1], by linarith only [h3, ht.2]⟩
    have hu : ∀ t ∈ [[a', b']], HasDerivAt (fun s : ℝ => f (x, s)) (g (x, t)) t :=
      fun t ht => hd x t (hIcc ht)
    have hu'I : IntervalIntegrable (fun s : ℝ => g (x, s)) volume a' b' :=
      ((hgc x).mono hIcc).intervalIntegrable
    have hv'I : IntervalIntegrable (fun s : ℝ => timePartial φ (x, s)) volume a' b' :=
      ((CKN.contDiff_timePartial hφ.1).continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'I hv'I
    rw [hφ0 (x, a') (by simp), hφ0 (x, b') (by simp), mul_zero, mul_zero, sub_zero,
      zero_sub] at hibp
    rw [intervalIntegral.integral_of_le h2.le, integral_Ioc_eq_integral_Ioo] at hibp
    rw [intervalIntegral.integral_of_le h2.le, integral_Ioc_eq_integral_Ioo] at hibp
    exact hibp
  rw [vlSlab_measure] at hIf hIg ⊢
  rw [integral_prod _ hIf, integral_prod _ hIg, ← integral_neg]
  congr 1
  funext x
  exact key x

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The regularized velocity is square integrable on every positive-time slab
(`thm:regularised` of the CKN manuscript, (R3)). -/
theorem lps_regR12_velocity_memLp_slab {δ T : ℝ} (hδ : 0 < δ) (hδT : δ < T) (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => lpsRegU ρ ε hε b hb z i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hL2, -, -, -⟩ := h
  exact (hL2 δ T hδ hδT).1 i

/-- The regularized velocity has its momentum right-hand side as weak time derivative on every
slab `ℝ³ × (0, T)` (`thm:regularised` of the CKN manuscript, (R2)). -/
theorem lps_regR12_weak_time {T : ℝ} (hT : 0 < T) (i : Fin 3) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T)) :
    ∫ z in vlSlab 0 T, lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i * timePartial φ z =
      -∫ z in vlSlab 0 T, lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i * φ z := by
  obtain ⟨hQcont, hQL2⟩ := lps_regR12_Q_facts ρ ε hε b hb
  refine lps_slab_time_weak_of_pointwise hT
    (f := fun z : Vec3 × ℝ => lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i)
    (g := fun z : Vec3 × ℝ => lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i)
    ?_ ?_ ?_ ?_ hφ
  · intro x t ht
    exact lps_regR12_hasDerivAt_time ρ ε hε b hb (x, t) ht.1 i
  · intro x
    have h1 : ContinuousOn (fun z : Vec3 × ℝ => lpsRegQ ρ ε hε b hb
        ((z.1, z.2) : ParabolicPoint) i) (Set.univ ×ˢ Ioi 0) :=
      (hQcont i).comp parabolicHomeomorph.symm.continuous.continuousOn (fun _ hz => hz)
    exact h1.comp (f := fun t : ℝ => ((x, t) : Vec3 × ℝ))
      (s := Ioo 0 T) (by fun_prop) (fun t ht => ⟨Set.mem_univ _, ht.1⟩)
  · intro a' b' ha' hab' hb'
    exact lps_regR12_velocity_memLp_slab ρ ε hε b hb ha' hab' i
  · intro a' b' ha' hab' hb'
    exact hQL2 a' b' ha' hab' i

end

end ESS.LPS

end
