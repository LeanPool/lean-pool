/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressureBounds

/-!
# Convergence of the whole-space pressures

Strong local L³ convergence of velocities with uniformly bounded global
L³ slices gives strong local L^(3/2) convergence of their whole-space
Riesz pressures (`prop:blowup-limit`, pressure-limit step): the pressure of
the tensor near a large ball converges by the L^(3/2) bound of the double
Riesz transforms, and the pressure of the far tensor is uniformly small.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS


/-- Truncating a time-truncated tensor to a smaller set inside the time
window is the truncation of the original tensor. -/
theorem blowupLimitAssemblyPressure_indicator_time_window
    (U : Vec3 × ℝ → Vec3) {A : Set (Vec3 × ℝ)} (J : Set ℝ)
    (hA : A ⊆ Set.univ ×ˢ J) (i j : Fin 3) :
    A.indicator ((Set.univ ×ˢ J).indicator (fun z => U z i * U z j)) =
      A.indicator (fun z => U z i * U z j) := by
  rw [Set.indicator_indicator, Set.inter_eq_left.mpr hA]

/-- The norm of a canonical pressure class restricted to a set is the
L^(3/2) seminorm of the representative. -/
theorem blowupLimitAssemblyPressure_mass_to_eLpNorm
    {μ : Measure (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ} (hf : Measurable f) {ε : ℝ≥0∞}
    (hmass : (∫⁻ z, ENNReal.ofReal |f z| ^ (3 / 2 : ℝ) ∂μ) ≤ ε) :
    eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ ε ^ (2 / 3 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  have htoReal : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = 3 / 2 := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
  rw [htoReal]
  have heq : (∫⁻ z, ‖f z‖ₑ ^ (3 / 2 : ℝ) ∂μ) =
      ∫⁻ z, ENNReal.ofReal |f z| ^ (3 / 2 : ℝ) ∂μ := by
    congr 1
    funext z
    rw [Real.enorm_eq_ofReal_abs]
  rw [heq]
  have h23 : (1 / (3 / 2 : ℝ)) = 2 / 3 := by norm_num
  rw [h23]
  exact ENNReal.rpow_le_rpow hmass (by norm_num)

/-- Strong local convergence of pressures from strong local L³ convergence
of velocities with uniform global L³ slice bounds on a past time window. -/
theorem blowupLimitAssemblyPressure_riesz_tendsto
    (vs : ℕ → Vec3 × ℝ → Vec3) (hvs : ∀ k, Measurable (vs k))
    (U : Vec3 × ℝ → Vec3) (hU : Measurable U)
    {a : ℝ} (ha : a < 0) {N : ℝ≥0∞} (hN : N < ⊤)
    (hslice : ∀ k, ∀ᵐ t ∂volume.restrict (Ioo a 0),
      eLpNorm (fun x : Vec3 => vs k (x,t)) 3 volume ≤ N)
    (hUslice : ∀ᵐ t ∂volume.restrict (Ioo a 0),
      eLpNorm (fun x : Vec3 => U (x,t)) 3 volume ≤ N)
    (hconv : ∀ L : ℝ, 0 < L → Tendsto (fun k => eLpNorm (fun z => vs k z - U z) 3
      (volume.restrict (CKN.euclideanBall (0 : Vec3) L ×ˢ Ioo a 0))) atTop (nhds 0))
    (hF : ∀ k i j, MemLp (fun z => vs k z i * vs k z j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hG : ∀ i j, MemLp ((Set.univ ×ˢ Ioo a 0).indicator (fun z => U z i * U z j))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun k => eLpNorm (fun z =>
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (fun i j z => vs k z i * vs k z j) (hF k) z -
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (fun i j => (Set.univ ×ˢ Ioo a 0).indicator (fun z => U z i * U z j)) hG z)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (CKN.euclideanBall (0 : Vec3) R ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  set J : Set ℝ := Ioo a 0 with hJdef
  have hJ : MeasurableSet J := measurableSet_Ioo
  set C : Set (Vec3 × ℝ) := CKN.euclideanBall (0 : Vec3) R ×ˢ J with hCdef
  set μC : Measure (Vec3 × ℝ) := volume.restrict C with hμCdef
  let Fk : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun k i j z => vs k z i * vs k z j
  let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun i j => (Set.univ ×ˢ J).indicator (fun z => U z i * U z j)
  let P : (Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) → Prop := fun X =>
    ∀ i j, MemLp (X i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume
  have hmemC : ∀ (X : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (hX : P X),
      MemLp (CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) X hX)
        (ENNReal.ofReal (3 / 2 : ℝ)) μC :=
    fun X hX => (CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      X hX).mono_measure Measure.restrict_le_self
  let toE : ∀ (X : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ), P X →
      Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC := fun X hX =>
    (hmemC X hX).toLp (CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) X hX)
  let A : ℕ → Set (Vec3 × ℝ) := fun L => CKN.euclideanBall 0 ((L : ℝ) + 1) ×ˢ J
  let B : ℕ → Set (Vec3 × ℝ) := fun L => (CKN.euclideanBall 0 ((L : ℝ) + 1))ᶜ ×ˢ J
  have hAm : ∀ L, MeasurableSet (A L) := fun L =>
    (CKN.isOpen_euclideanBall 0 _).measurableSet.prod hJ
  have hBm : ∀ L, MeasurableSet (B L) := fun L =>
    (CKN.isOpen_euclideanBall 0 _).measurableSet.compl.prod hJ
  have hAJ : ∀ L, A L ⊆ Set.univ ×ˢ J := fun L z hz => ⟨mem_univ _, hz.2⟩
  have hBJ : ∀ L, B L ⊆ Set.univ ×ˢ J := fun L z hz => ⟨mem_univ _, hz.2⟩
  have hFA : ∀ k L, P (fun i j => (A L).indicator (Fk k i j)) :=
    fun k L i j => (hF k i j).indicator (hAm L)
  have hFB : ∀ k L, P (fun i j => (B L).indicator (Fk k i j)) :=
    fun k L i j => (hF k i j).indicator (hBm L)
  have hGA : ∀ L, P (fun i j => (A L).indicator (G i j)) :=
    fun L i j => (hG i j).indicator (hAm L)
  have hGB : ∀ L, P (fun i j => (B L).indicator (G i j)) :=
    fun L i j => (hG i j).indicator (hBm L)
  let p : ℕ → Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC := fun k => toE (Fk k) (hF k)
  let q : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC := toE G hG
  let near : ℕ → ℕ → Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC :=
    fun L k => toE _ (hFA k L)
  let nearLimit : ℕ → Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC :=
    fun L => toE _ (hGA L)
  let far : ℕ → ℕ → Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC :=
    fun L k => toE _ (hFB k L)
  let farLimit : ℕ → Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) μC :=
    fun L => toE _ (hGB L)
  have hsplit : ∀ L k, p k = near L k + far L k := fun L k =>
    blowup_rieszPressure_full_near_far_local_Lp (Fk k) (hF k) ((L : ℝ) + 1) R J hJ
  have hlimitSplit : ∀ L, q = nearLimit L + farLimit L := fun L =>
    blowup_rieszPressure_full_near_far_local_Lp G hG ((L : ℝ) + 1) R J hJ
  -- norms in the restricted space are controlled by global seminorms
  have hnormLe : ∀ (X Y : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (hX : P X) (hY : P Y),
      ‖toE X hX - toE Y hY‖ ≤ (eLpNorm (fun z =>
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) X hX z -
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) Y hY z)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal := by
    intro X Y hX hY
    have hglob := ((CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      X hX).sub (CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      Y hY)).eLpNorm_ne_top
    simp only [toE]
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    exact ENNReal.toReal_mono hglob (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hnear : ∀ L, Tendsto (near L) atTop (nhds (nearLimit L)) := by
    intro L
    have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
    have hsliceA : ∀ k, eLpNorm (vs k) 3 (volume.restrict (A L)) ≤
        (volume J * N ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := fun k =>
      blowupLimitAssemblyPressure_memLp_three_of_slices (hvs k) (hslice k) _
    have hUA : eLpNorm U 3 (volume.restrict (A L)) ≤
        (volume J * N ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
      blowupLimitAssemblyPressure_memLp_three_of_slices hU hUslice _
    have hBfin : (volume J * N ^ (3 : ℝ)) ^ (1 / 3 : ℝ) < ⊤ := by
      have hJfin : volume J < ⊤ := by
        simp only [J, Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_lt_top hJfin (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          hN.ne)).ne
    have hvA : ∀ k, MemLp (vs k) 3 (volume.restrict (A L)) := fun k =>
      memLp_iff.2 ((hsliceA k).trans_lt hBfin)
    have hUA' : MemLp U 3 (volume.restrict (A L)) := memLp_iff.2 (hUA.trans_lt hBfin)
    obtain ⟨hF', hG', hlim⟩ := blowup_rieszPressureSpaceTime_near_tendsto (A L) (hAm L)
      vs U hUA' hvA (hconv _ hLpos) ⟨_, hBfin, hsliceA⟩
    have hGeq : (fun i j => (A L).indicator (G i j)) =
        (fun i j => (A L).indicator (fun z => U z i * U z j)) := by
      funext i j
      exact blowupLimitAssemblyPressure_indicator_time_window U J (hAJ L) i j
    have hPGeq := blowup_rieszPressureSpaceTime_congr (hGA L) hG' hGeq
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim)
    have h := hnormLe _ _ (hFA k L) (hGA L)
    simp only [near, nearLimit, Function.comp_apply]
    rw [hPGeq] at h
    exact h
  have hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ,
      (∀ k, ‖far L k‖ < ε) ∧ ‖farLimit L‖ < ε := by
    intro ε hε
    let ws : ℕ → Vec3 × ℝ → Vec3 := fun k => Nat.casesOn k U (fun k => vs k)
    have hwsM : ∀ k, Measurable (ws k) := by
      intro k
      cases k with
      | zero => exact hU
      | succ k => exact hvs k
    have hwsSlice : ∀ k, ∀ᵐ t ∂volume.restrict (Ioo a 0),
        eLpNorm (fun x : Vec3 => ws k (x,t)) 3 volume ≤ N := by
      intro k
      cases k with
      | zero => exact hUslice
      | succ k => exact hslice k
    have hJfin : volume J < ⊤ := by
      simp only [J, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hBfin : (volume J * N ^ (3 : ℝ)) ^ (1 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_lt_top hJfin (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          hN.ne)).ne
    have hwsMem : ∀ (n : ℝ) (k : ℕ), MemLp (ws k) 3
        ((volume : Measure (Vec3 × ℝ)).restrict
          ((CKN.euclideanBall 0 (n + 1))ᶜ ×ˢ Ioo a 0)) := fun n k =>
      memLp_iff.2 ((blowupLimitAssemblyPressure_memLp_three_of_slices (hwsM k)
        (hwsSlice k) _).trans_lt hBfin)
    have hwsSliceMem : ∀ k, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a 0),
        MemLp (fun x : Vec3 => ws k (x,t)) 3 volume ∧
        eLpNorm (fun x : Vec3 => ws k (x,t)) 3 volume ≤ N := by
      intro k
      filter_upwards [hwsSlice k] with t ht
      exact ⟨memLp_iff.2 (ht.trans_lt hN), ht⟩
    obtain ⟨hFfar, hsmall⟩ := blowup_riesz_far_velocity_uniform_mass_small ws R a 0 hR ha
      N hN hwsMem hwsSliceMem
    set δ : ℝ≥0∞ := ENNReal.ofReal ((ε / 2) ^ (3 / 2 : ℝ)) with hδdef
    have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨n, hn⟩ := hsmall δ hδ
    have hμ : (volume.restrict (CKN.euclideanBall (0 : Vec3) R)).prod
        (volume.restrict (Ioo a 0)) = μC := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    have hδpow : δ ^ (2 / 3 : ℝ) = ENNReal.ofReal (ε / 2) := by
      rw [hδdef, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hbound : ∀ (X : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (hX : P X),
        (∫⁻ z, ENNReal.ofReal |CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) X hX z| ^ (3 / 2 : ℝ) ∂μC) ≤ δ → ‖toE X hX‖ < ε := by
      intro X hX hmass
      have he := blowupLimitAssemblyPressure_mass_to_eLpNorm
        (CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) X hX) hmass
      rw [hδpow] at he
      simp only [toE]
      rw [Lp.norm_toLp]
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
      rw [ENNReal.toReal_ofReal (by positivity)] at hreal
      linarith only [hreal, hε]
    refine ⟨n, fun k => ?_, ?_⟩
    · have hmass := hn (k + 1)
      rw [hμ] at hmass
      exact hbound _ (hFB k n) hmass
    · have hmass := hn 0
      rw [hμ] at hmass
      have hGeq : (fun i j => (B n).indicator (G i j)) =
          (fun i j => (B n).indicator (fun z => ws 0 z i * ws 0 z j)) := by
        funext i j
        exact blowupLimitAssemblyPressure_indicator_time_window U J (hBJ n) i j
      have hPGeq := blowup_rieszPressureSpaceTime_congr (hGB n) (hFfar n 0) hGeq
      apply hbound _ (hGB n)
      rw [hPGeq]
      exact hmass
  have hconvE := blowup_pressure_two_radius_convergence p q near nearLimit far farLimit
    hsplit hlimitSplit hnear hfar
  exact blowupLimitAssemblyPressure_eLpNorm_sub_tendsto (fun k => hmemC _ (hF k))
    (hmemC _ hG) hconvE

end ESS

end
