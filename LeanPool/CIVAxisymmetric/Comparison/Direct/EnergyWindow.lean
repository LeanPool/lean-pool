/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.EnergyGronwall
public import LeanPool.CIVAxisymmetric.Comparison.EnergySpatialIntegration

/-!
# The comparison energy on a working interval

The assembled Grönwall bound of `CIV.Comparison.Direct.EnergyGronwall` on a working interval
`[τ₀, b] ⊆ I`: see that module's docstring for the statement and the route.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

private theorem comparison_primitive_bound {P S r : ℝ → ℝ} {τ₀ b : ℝ} {Λ : NNReal}
    (hτ₀b : τ₀ ≤ b) (hPcont : ContinuousOn P (Icc τ₀ b))
    (hSint : IntervalIntegrable S volume τ₀ b) (hrint : IntervalIntegrable r volume τ₀ b)
    (hrnn : ∀ s, 0 ≤ r s)
    (hswapP : ∀ t ∈ Icc τ₀ b, P t = ∫ s in τ₀..t, S s)
    (hSle : ∀ᵐ s ∂(volume.restrict (Icc τ₀ b)), S s ≤ Λ * P s + r s) :
    ∀ t ∈ Icc τ₀ b, P t ≤ (∫ s in τ₀..b, r s) * Real.exp (Λ * (b - τ₀)) := by
  have hPint : ∀ t ∈ Icc τ₀ b, IntervalIntegrable P volume τ₀ t := fun t ht =>
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hPcont.mono (Icc_subset_Icc le_rfl ht.2))
  have hc₀ : 0 ≤ ∫ s in τ₀..b, r s :=
    intervalIntegral.integral_nonneg hτ₀b (fun s _ => hrnn s)
  have hy : ∀ t ∈ Icc τ₀ b, P t ≤ (∫ s in τ₀..b, r s) + Λ * ∫ s in τ₀..t, P s := by
    intro t ht
    have hsubt : uIcc τ₀ t ⊆ uIcc τ₀ b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hτ₀b]
      exact Icc_subset_Icc le_rfl ht.2
    have hSt : IntervalIntegrable S volume τ₀ t := hSint.mono_set hsubt
    have hrt : IntervalIntegrable r volume τ₀ t := hrint.mono_set hsubt
    have hmono : ∫ s in τ₀..t, S s ≤ ∫ s in τ₀..t, (Λ * P s + r s) :=
      intervalIntegral.integral_mono_ae_restrict ht.1 hSt (((hPint t ht).const_mul _).add hrt)
        (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl ht.2) hSle)
    rw [intervalIntegral.integral_add ((hPint t ht).const_mul _) hrt,
      intervalIntegral.integral_const_mul] at hmono
    have hrle : ∫ s in τ₀..t, r s ≤ ∫ s in τ₀..b, r s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun s => hrnn s) hrint
    rw [hswapP t ht]
    linarith only [hmono, hrle]
  have hgr := le_mul_exp_of_le_primitive hτ₀b Λ.coe_nonneg hc₀ hPcont hy
  exact hgr

/-- **The comparison energy bound at fixed `ε` and `σ`** (`eq:aniso:comparison:positive:energy`
followed by Grönwall's inequality). -/
theorem ae_integral_comparisonProfile_le {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    {M σ Mq τ₀ b : ℝ} {Λ : NNReal} (hσ : 0 < σ) (hM : 0 ≤ M) (hMq : 0 ≤ Mq)
    (hτ₀b : τ₀ ≤ b) (hsub : Icc τ₀ b ⊆ I)
    (hgood : ∀ᵐ s ∂(volume.restrict (Icc τ₀ b)),
      AEStronglyMeasurable (fun y => q (y, s)) volume ∧ (∀ᵐ y ∂volume, |q (y, s)| ≤ Mq) ∧
      (∀ x, ‖B (x, s)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, s)) ∧
      (∀ x, |divB (x, s)| ≤ Λ) ∧
      (∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, divB (x, s) * ψ x = -∫ x, ∑ i, B (x, s) i * fderiv ℝ ψ x (basisVec i)))
    (hq0 : ∀ x, mollifySlice m ε q (x, τ₀) ≤ M)
    (hA1 : ∀ᵐ x : Vec m, ∀ᵐ τ ∂(volume.restrict I),
      mollifySlice m ε q (x, τ) - mollifySlice m ε q (x, τ₀)
        = ∫ s in τ₀..τ, mollifiedRHS m d ε B divB q x s)
    (hA2 : ∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x : Vec m,
      mollifySlice m ε q (x, τ) - mollifySlice m ε q (x, τ₀)
        = ∫ s in τ₀..τ, mollifiedRHS m d ε B divB q x s) :
    ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)), ∀ δ : ℝ, 0 < δ →
      ∫ x, comparisonProfile
          (mollifySlice m ε q (x, τ) - barrier m M σ (barrierRate m d Λ) τ₀ (x, τ))
        ≤ (δ * (volume (Metric.closedBall (0 : Vec m) (Mq / σ))).toReal * (b - τ₀)
            + (1 / (4 * δ)) * ∫ s in τ₀..b, commutatorL2Sq m ε (Mq / σ) B divB q s)
          * Real.exp (Λ * (b - τ₀)) := by
  classical
  set K : ℝ := barrierRate m d Λ with hKdef
  have hK : 0 ≤ K := barrierRate_nonneg m d Λ.coe_nonneg
  set Bl : Set (Vec m) := Metric.closedBall (0 : Vec m) (Mq / σ) with hBl
  have hτ₀I : τ₀ ∈ I := hsub ⟨le_rfl, hτ₀b⟩
  -- a measurable set of good times of full measure
  obtain ⟨T, hTm, hTsub, hTgood, hTnull⟩ :=
    exists_measurableSet_subset_forall_of_ae measurableSet_Icc hgood
  have hTall : ∀ᵐ s ∂volume, s ∈ Icc τ₀ b → s ∈ T := by
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hTnull
    simp only [mem_ofPred_eq, not_imp] at hs
    exact hs
  -- the integrand
  set Φ : Vec m → ℝ → ℝ := fun x s => Real.smoothTransition
      (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s))
      * (mollifiedRHS m d ε B divB q x s - σ * K) with hΦdef
  set F : ℝ → Vec m → ℝ := fun s x => T.indicator (fun s' => Φ x s') s with hFdef
  set C : ℝ := |mollifiedRHSBound m d ε Λ Mq| + |σ * K| with hCdef
  have hdivm : ∀ s, AEStronglyMeasurable (fun x => divB (x, s)) volume := fun s =>
    (hB.2.1.comp measurable_prodMk_right).aestronglyMeasurable
  have hFb : ∀ s x, ‖F s x‖ ≤ C := by
    intro s x
    by_cases hs : s ∈ T
    · obtain ⟨hmeas, hbdd, hBb, hBlip, hdiv, -⟩ := hTgood s hs
      simp only [hFdef, indicator_of_mem hs, hΦdef, Real.norm_eq_abs, abs_mul]
      have h1 : |Real.smoothTransition (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s))|
          ≤ 1 := by
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      have h2 := abs_mollifiedRHS_le d hε hMq hmeas hbdd hBb hBlip hdiv (hdivm s) x
      have h3 := abs_sub (mollifiedRHS m d ε B divB q x s) (σ * K)
      have h4 := le_abs_self (mollifiedRHSBound m d ε Λ Mq)
      have h5 : |mollifiedRHS m d ε B divB q x s - σ * K| ≤ C := by
        rw [hCdef]; linarith only [h2, h3, h4]
      calc _ ≤ 1 * |mollifiedRHS m d ε B divB q x s - σ * K| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ C := by rw [one_mul]; exact h5
    · simp only [hFdef, indicator_of_notMem hs, norm_zero, hCdef]
      positivity
  have hFs : ∀ s x, x ∉ Bl → F s x = 0 := by
    intro s x hx
    by_cases hs : s ∈ T
    · obtain ⟨hmeas, hbdd, -, -, -, -⟩ := hTgood s hs
      have hneg := mollifySlice_sub_barrier_neg hε hσ hM hK (hTsub hs).1 hmeas hbdd hx
      simp only [hFdef, indicator_of_mem hs, hΦdef,
        Real.smoothTransition.zero_of_nonpos hneg.le, zero_mul]
    · simp only [hFdef, indicator_of_notMem hs]
  -- joint measurability
  have hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have heq2 : (volume : Measure (Vec m)).prod (volume.restrict I)
        = volume.restrict (univ ×ˢ I) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))),
        Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [heq2]; exact hq.1
  set g : Vec m × ℝ → ℝ := fun z => Real.smoothTransition
      (mollifySlice m ε q z - barrier m M σ K τ₀ z)
      * (mollifiedRHS m d ε B divB q z.1 z.2 - σ * K) with hgdef
  have hg : AEStronglyMeasurable g ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have hmoll := aestronglyMeasurable_mollifySlice (ε := ε) hqmeas
    have hbar : AEStronglyMeasurable (barrier m M σ K τ₀)
        ((volume : Measure (Vec m)).prod (volume.restrict I)) :=
      (contDiff_barrier M σ K τ₀).continuous.aestronglyMeasurable
    have hH : AEStronglyMeasurable (fun z : Vec m × ℝ => mollifiedRHS m d ε B divB q z.1 z.2)
        ((volume : Measure (Vec m)).prod (volume.restrict I)) :=
      aestronglyMeasurable_comparisonRHS hε hI hB hq
    exact (Real.smoothTransition.continuous.comp_aestronglyMeasurable (hmoll.sub hbar)).mul
      (hH.sub aestronglyMeasurable_const)
  have hgi : AEStronglyMeasurable ((univ ×ˢ T).indicator g)
      ((volume : Measure (Vec m)).prod (volume.restrict I)) :=
    hg.indicator (MeasurableSet.univ.prod hTm)
  have hFuncurry : Function.uncurry F = fun p : ℝ × Vec m => (univ ×ˢ T).indicator g p.swap := by
    funext p
    by_cases hp : p.1 ∈ T
    · have hmem : p.swap ∈ (univ ×ˢ T : Set (Vec m × ℝ)) := ⟨mem_univ _, hp⟩
      simp only [Function.uncurry, hFdef, indicator_of_mem hp, indicator_of_mem hmem, hΦdef,
        hgdef, Prod.fst_swap, Prod.snd_swap]
      rfl
    · have hmem : p.swap ∉ (univ ×ˢ T : Set (Vec m × ℝ)) := fun h => hp h.2
      simp only [Function.uncurry, hFdef, indicator_of_notMem hp, indicator_of_notMem hmem]
  have hFm : ∀ τ ∈ Icc τ₀ b, AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (uIoc τ₀ τ)).prod (volume : Measure (Vec m))) := by
    intro τ hτ
    have hsubU : uIoc τ₀ τ ⊆ I :=
      uIoc_subset_uIcc.trans ((uIcc_subset_Icc (left_mem_Icc.mpr hτ₀b) hτ).trans hsub)
    rw [hFuncurry]
    exact hgi.prod_swap.mono_measure (Measure.prod_mono (Measure.restrict_mono hsubU le_rfl) le_rfl)
  -- the primitive
  set P : ℝ → ℝ := fun τ => ∫ x, ∫ s in τ₀..τ, F s x with hPdef
  set S : ℝ → ℝ := fun s => ∫ x, F s x with hSdef
  have hFint : ∀ x, ∀ τ ∈ Icc τ₀ b, ∫ s in τ₀..τ, F s x = ∫ s in τ₀..τ, Φ x s := by
    intro x τ hτ
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hTall] with s hs hsmem
    have hsIcc : s ∈ Icc τ₀ b :=
      (uIcc_subset_Icc (left_mem_Icc.mpr hτ₀b) hτ) (uIoc_subset_uIcc hsmem)
    simp only [hFdef, indicator_of_mem (hs hsIcc)]
  have hEP : ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)),
      ∫ x, comparisonProfile (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) = P τ := by
    have hrep := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_ae_comparisonProfile_eq_intervalIntegral (M := M) (σ := σ) (K := K) hI hIoc hB hq heq
        hε hσ.le hτ₀I hq0 hA1 hA2)
    filter_upwards [hrep, ae_restrict_mem measurableSet_Icc] with τ hτ hτmem
    refine integral_congr_ae ?_
    filter_upwards [hτ] with x hx
    rw [hx, hFint x τ hτmem]
  have hswapP : ∀ τ ∈ Icc τ₀ b, P τ = ∫ s in τ₀..τ, S s := fun τ hτ =>
    (intervalIntegral_integral_swap_of_bounded_of_spatialSupport (isCompact_closedBall _ _)
      (hFm τ hτ) hFb hFs).symm
  have hSint : IntervalIntegrable S volume τ₀ b := by
    have hint := integrable_uncurry_of_bounded_of_spatialSupport (isCompact_closedBall _ _)
      (hFm b ⟨hτ₀b, le_rfl⟩) hFb hFs
    rw [intervalIntegrable_iff]
    exact hint.integral_prod_left
  -- continuity of the primitive
  have hSIcc : IntegrableOn S (Icc τ₀ b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hτ₀b).mp hSint
  have hPcont : ContinuousOn P (Icc τ₀ b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := τ₀) (b := b)
      (μ := volume) (by rw [uIcc_of_le hτ₀b]; exact hSIcc)
    rw [uIcc_of_le hτ₀b] at h
    exact h.congr fun τ hτ => hswapP τ hτ
  -- the commutator mass is integrable in time
  set c : ℝ → ℝ := fun s => commutatorL2Sq m ε (Mq / σ) B divB q s with hcdef
  set Cr : ℝ := Λ * Mq * (mollifierGradConst m + 1) with hCrdef
  have hcle : ∀ s ∈ T, c s ≤ Cr ^ 2 * (volume Bl).toReal := by
    intro s hs
    obtain ⟨hmeas, hbdd, -, hBlip, hdiv, -⟩ := hTgood s hs
    have hfin : volume Bl ≠ ⊤ := measure_closedBall_lt_top.ne
    have hR := fun x => abs_diPernaLionsCommutator_le_of_ae (m := m) hε hMq hBlip hdiv
      (hdivm s) hbdd hmeas x
    have hmono : ∫ x in Bl, diPernaLionsCommutator m ε (fun y => B (y, s))
          (fun y => divB (y, s)) (fun y => q (y, s)) x ^ 2 ≤ ∫ x in Bl, Cr ^ 2 :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
        (integrableOn_const hfin) (Eventually.of_forall fun x =>
          (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hR x) 2))
    rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm] at hmono
    exact hmono
  have hcint : IntervalIntegrable c volume τ₀ b := by
    rw [intervalIntegrable_iff, uIoc_of_le hτ₀b]
    have hqm' : AEStronglyMeasurable q (volume.restrict (univ ×ˢ Ioc τ₀ b)) :=
      hq.1.mono_set (prod_mono subset_rfl (Ioc_subset_Icc_self.trans hsub))
    refine Integrable.of_bound (aestronglyMeasurable_commutatorL2Sq hB.1 hB.2.1 hqm')
      (Cr ^ 2 * (volume Bl).toReal) ?_
    have hTIoc : ∀ᵐ s ∂(volume.restrict (Ioc τ₀ b)), s ∈ T := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hTall] with s hs hsmem
      exact hs (Ioc_subset_Icc_self hsmem)
    filter_upwards [hTIoc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (commutatorL2Sq_nonneg ε (Mq / σ) B divB q s)]
    exact hcle s hs
  -- the bound for each `δ`
  have hbound : ∀ δ : ℝ, 0 < δ → ∀ t ∈ Icc τ₀ b, P t
      ≤ (δ * (volume Bl).toReal * (b - τ₀) + (1 / (4 * δ)) * ∫ s in τ₀..b, c s)
        * Real.exp (Λ * (b - τ₀)) := by
    intro δ hδ
    set r : ℝ → ℝ := fun s => δ * (volume Bl).toReal + (1 / (4 * δ)) * c s with hrdef
    have hrint : IntervalIntegrable r volume τ₀ b :=
      intervalIntegrable_const.add (hcint.const_mul _)
    have hrnn : ∀ s, 0 ≤ r s := fun s => by
      have h1 : 0 ≤ δ * (volume Bl).toReal := mul_nonneg hδ.le ENNReal.toReal_nonneg
      have h2 : 0 ≤ (1 / (4 * δ)) * c s :=
        mul_nonneg (by positivity) (commutatorL2Sq_nonneg ε (Mq / σ) B divB q s)
      simp only [hrdef]
      linarith only [h1, h2]
    have hr0 : ∫ s in τ₀..b, r s
        = δ * (volume Bl).toReal * (b - τ₀) + (1 / (4 * δ)) * ∫ s in τ₀..b, c s := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hcint.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      ring
    -- the a.e. differential inequality
    have hSle : ∀ᵐ s ∂(volume.restrict (Icc τ₀ b)), S s ≤ Λ * P s + r s := by
      filter_upwards [hEP, ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hTall]
        with s hEs hsmem hsT
      have hs : s ∈ T := hsT hsmem
      obtain ⟨hmeas, hbdd, hBb, hBlip, hdiv, hweak⟩ := hTgood s hs
      have hSs : S s = ∫ x, Φ x s := by
        simp only [hSdef, hFdef, indicator_of_mem hs]
      have hslice := integral_smoothTransition_mul_mollifiedRHS_le d hε hσ hM hMq hsmem.1 hmeas
        hbdd hBb hBlip hdiv (hdivm s) hweak
      have hsplit := integral_mul_abs_le_of_support (m := m) (ρ := Mq / σ) hδ
        (f := fun x => Real.smoothTransition
          (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)))
        (R := fun x => diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x) (Cr := Cr)
        (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _)
        (fun x hx => Real.smoothTransition.zero_of_nonpos
          (mollifySlice_sub_barrier_neg hε hσ hM hK hsmem.1 hmeas hbdd hx).le)
        (aestronglyMeasurable_diPernaLionsCommutator ε hBlip.continuous (hdivm s) hmeas)
        (Eventually.of_forall fun x =>
          abs_diPernaLionsCommutator_le_of_ae hε hMq hBlip hdiv (hdivm s) hbdd hmeas x)
      have hcs : c s = ∫ x in Bl, diPernaLionsCommutator m ε (fun y => B (y, s))
          (fun y => divB (y, s)) (fun y => q (y, s)) x ^ 2 := rfl
      rw [hSs]
      rw [hEs] at hslice
      simp only [hrdef]
      rw [hcs]
      linarith only [hslice, hsplit]
    intro t ht
    rw [← hr0]
    exact comparison_primitive_bound hτ₀b hPcont hSint hrint hrnn hswapP hSle t ht
  filter_upwards [hEP, ae_restrict_mem measurableSet_Icc] with τ hτ hτmem δ hδ
  rw [hτ]
  exact hbound δ hδ τ hτmem

end CIV
