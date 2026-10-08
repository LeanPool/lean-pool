/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationZeroForce
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationZeroForcePressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalTimeWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12TimeCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12TimePairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12TimeSeparation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12TimeIBP
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalComponent
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.WeakContL3Support
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim

/-!
# Classical time derivative of the regularized velocity

The zero-force weak momentum identity, paired with a compactly supported
smooth spatial field `η`, gives each spatial pairing a weak time derivative
(`regularisedR12TimePairing_weakDeriv`). It is classical by
`regularisedR12TimeCore_hasDerivAt_of_weakDeriv`, and spatial integration by
parts (`regularisedR12TimeIBP_flux_eq`) identifies it with the pairing of the
right-hand side `Δu − (J_ε u · ∇) u − ∇p`. Integrating in time and exchanging
the order of integration gives the paired time increments. Spatial separation
(`regularisedR12TimeSeparation_eq_zero_of_interval_tests`) then gives the
pointwise increments, and the fundamental theorem of calculus gives the
classical time derivative of `thm:regularised`.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- A differentiable function on `ℝ³` with continuous coordinate partial
derivatives is `C¹`. -/
private theorem regularisedR12TimeFinal_contDiff_of_partials
    (F : Vec3 → ℝ) (hF : Differentiable ℝ F)
    (hpartial : ∀ j : Fin 3,
      Continuous (fun x : Vec3 => (fderiv ℝ F x) (basisVec j))) :
    ContDiff ℝ 1 F := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨hF, continuous_clm_apply.2 fun v => ?_⟩
  have hv : v = ∑ j : Fin 3, v j • basisVec j := by
    ext k
    simp [basisVec, Pi.single_apply]
  have hsum : (fun x : Vec3 => (fderiv ℝ F x) v) =
      fun x => ∑ j : Fin 3, v j * (fderiv ℝ F x) (basisVec j) := by
    funext x
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hsum]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hpartial j)

/-- The time-increment and pointwise-derivative argument on `ℝ³ × (0,T)`. -/
private theorem regularisedR12TimeFinal_core
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeak : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ k : Fin 3, u z k * timePartial (fun y => φ y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u z j * u z k *
              spatialPartial (fun y => φ y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
            spatialPartial (fun y => u y k) j z *
              spatialPartial (fun y => φ y k) j z
          - p z * (∑ k : Fin 3, spatialPartial (fun y => φ y k) k z)) = 0)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hD : ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDD : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hP : ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDp : ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j : Fin 3,
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hDiv : ∀ t : ℝ, 0 < t → CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t))) :
    ∀ z : ParabolicPoint, 0 < z.2 → z.2 < T → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => u (z.1, s) i) (regR12TimeRHS ρ ε hε u p z i) z.2 := by
  let V : Vec3 × ℝ → Vec3 := fun w => u w
  let R : Vec3 × ℝ → Vec3 := fun w k => regR12TimeRHS ρ ε hε u p w k
  have hSlicePos : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    fun t ht => hSlice t ht.le
  have hSliceIcc : ∀ t : ℝ, t ∈ Icc 0 T → MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    fun t ht => hSlice t ht.1
  have hVc : ContinuousOn V (Set.univ ×ˢ Ioo (0 : ℝ) T) := by
    refine continuousOn_pi.2 fun k => ?_
    exact regUniform_continuousOn_pullback (hU k) (fun w hw => ⟨Set.mem_univ _, hw.2.1⟩)
  have hRc : ContinuousOn R (Set.univ ×ˢ Ioo (0 : ℝ) T) := by
    refine continuousOn_pi.2 fun k => ?_
    exact regUniform_continuousOn_pullback
      (regR12TimeRHS_continuousOn ρ ε hε u p hSlicePos hU hD hDD hDp k)
      (fun w hw => ⟨Set.mem_univ _, hw.2.1⟩)
  have hline (x : Vec3) : Continuous (fun s : ℝ => (x, s)) :=
    continuous_const.prodMk continuous_id
  have hRline (x : Vec3) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < T) :
      ContinuousOn (fun s : ℝ => R (x, s)) (Icc t₁ t₂) :=
    hRc.comp (hline x).continuousOn fun s hs =>
      ⟨Set.mem_univ _, Icc_subset_Ioo ht₁ ht₂ hs⟩
  have hcomm (x : Vec3) (t₁ t₂ : ℝ) (h12 : t₁ ≤ t₂) (ht₁ : 0 < t₁) (ht₂ : t₂ < T)
      (i : Fin 3) :
      (∫ s in t₁..t₂, R (x, s)) i = ∫ s in t₁..t₂, R (x, s) i :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm
      ((hRline x ht₁ ht₂).intervalIntegrable_of_Icc h12)).symm
  -- paired time increments
  have hzero : ∀ η : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₁ ∈ Ioo 0 T → t₂ ∈ Ioo 0 T →
      ∫ x : Vec3, ∑ i : Fin 3,
        (V (x, t₂) i - V (x, t₁) i - (∫ s in t₁..t₂, R (x, s)) i) * η x i = 0 := by
    intro η hη hηc t₁ t₂ h12 ht₁ ht₂
    obtain ⟨hFc, hGc, hW⟩ := regularisedR12TimePairing_weakDeriv ρ ε hε u p T hT
      hSliceIcc hWeak hU hD hP η hη hηc
    have hderiv := regularisedR12TimeCore_hasDerivAt_of_weakDeriv T hT hFc hGc hW
    have hIcc : Icc t₁ t₂ ⊆ Ioo 0 T := Icc_subset_Ioo ht₁.1 ht₂.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (hIcc (by rwa [uIcc_of_le h12.le] at ht)))
      ((hGc.mono hIcc).intervalIntegrable_of_Icc h12.le)
    let g : Vec3 × ℝ → ℝ := fun w => ∑ i : Fin 3, R w i * η w.1 i
    have hGH : ∀ t ∈ uIcc t₁ t₂,
        (∫ x : Vec3,
          (∑ i : Fin 3, ∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
              spatialDeriv (fun y => η y i) j x)
            - (∑ i : Fin 3, ∑ j : Fin 3,
              spatialPartial (fun y => u y i) j (x, t) *
                spatialDeriv (fun y => η y i) j x)
            + p (x, t) * (∑ i : Fin 3, spatialDeriv (fun y => η y i) i x)) =
          ∫ x : Vec3, g (x, t) := by
      intro t ht
      rw [uIcc_of_le h12.le] at ht
      have ht0 : 0 < t := (hIcc ht).1
      exact regularisedR12TimeIBP_flux_eq ρ ε hε u p hD hDD hDp hUdiff hDdiff hPdiff
        t ht0 (hSlicePos t ht0) (hDiv t ht0) η hη hηc
    have hgc : ContinuousOn g (Set.univ ×ˢ Ioo (0 : ℝ) T) :=
      continuousOn_finsetSum _ fun i _ => (continuousOn_pi.1 hRc i).mul
        ((continuous_apply i).comp (hη.continuous.comp continuous_fst)).continuousOn
    have hK : IsCompact (tsupport η ×ˢ Icc t₁ t₂) := hηc.isCompact.prod isCompact_Icc
    have hgK : IntegrableOn g (tsupport η ×ˢ Icc t₁ t₂) (volume : Measure (Vec3 × ℝ)) :=
      (hgc.mono fun w hw => ⟨Set.mem_univ _, hIcc hw.2⟩).integrableOn_compact hK
    have hgS : IntegrableOn g (Set.univ ×ˢ Ioc t₁ t₂) (volume : Measure (Vec3 × ℝ)) := by
      refine hgK.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioc) ?_
      rintro w ⟨⟨-, hw2⟩, hwn⟩
      have hx : w.1 ∉ tsupport η := fun hx => hwn ⟨hx, Ioc_subset_Icc_self hw2⟩
      have h0 : η w.1 = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [g, h0]
    have hgInt : Integrable (Function.uncurry fun (x : Vec3) (s : ℝ) => g (x, s))
        ((volume : Measure Vec3).prod (volume.restrict (Ioc t₁ t₂))) := by
      have hprod : (volume : Measure Vec3).prod (volume.restrict (Ioc t₁ t₂)) =
          ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
            (Set.univ ×ˢ Ioc t₁ t₂) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hprod]
      exact hgS
    have hswap := integral_integral_swap hgInt
    have hcInt : Integrable (fun x : Vec3 => ∫ s in Ioc t₁ t₂, g (x, s)) :=
      hgInt.integral_prod_left
    -- the slice pairings
    have hslice (t : ℝ) (ht : t ∈ Ioo 0 T) : Integrable
        (fun x : Vec3 => ∑ i : Fin 3, u (x, t) i * η x i) := by
      refine integrable_finsetSum _ fun i _ => ?_
      have hc : Continuous (fun x : Vec3 => u (x, t) i) :=
        continuous_iff_continuousAt.2 fun x =>
          (hUdiff (x, t) ⟨Set.mem_univ _, ht.1⟩ i).continuousAt
      exact (hc.mul ((continuous_apply i).comp hη.continuous)).integrable_of_hasCompactSupport
        (hηc.comp_left (g := fun v : Vec3 => v i) rfl).mul_left
    have hcx (x : Vec3) : ∫ s in Ioc t₁ t₂, g (x, s) =
        ∑ i : Fin 3, (∫ s in t₁..t₂, R (x, s)) i * η x i := by
      have hint (i : Fin 3) : Integrable (fun s : ℝ => R (x, s) i * η x i)
          (volume.restrict (Ioc t₁ t₂)) := by
        have hc : ContinuousOn (fun s : ℝ => R (x, s) i * η x i) (Icc t₁ t₂) :=
          ((continuous_apply i).comp_continuousOn (hRline x ht₁.1 ht₂.2)).mul
            continuousOn_const
        exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [integral_finsetSum _ fun i _ => hint i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const, hcomm x t₁ t₂ h12.le ht₁.1 ht₂.2 i,
        intervalIntegral.integral_of_le h12.le]
    have hpt : (fun x : Vec3 => ∑ i : Fin 3,
        (V (x, t₂) i - V (x, t₁) i - (∫ s in t₁..t₂, R (x, s)) i) * η x i) =
        fun x => (∑ i : Fin 3, u (x, t₂) i * η x i) - (∑ i : Fin 3, u (x, t₁) i * η x i) -
          ∫ s in Ioc t₁ t₂, g (x, s) := by
      funext x
      rw [hcx x, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [V]
      ring
    have hab : Integrable (fun x : Vec3 =>
        (∑ i : Fin 3, u (x, t₂) i * η x i) - (∑ i : Fin 3, u (x, t₁) i * η x i)) :=
      (hslice t₂ ht₂).sub (hslice t₁ ht₁)
    rw [hpt, integral_sub hab hcInt,
      integral_sub (hslice t₂ ht₂) (hslice t₁ ht₁), ← hFTC,
      intervalIntegral.integral_congr hGH, intervalIntegral.integral_of_le h12.le]
    rw [hswap]
    exact sub_self _
  have hsep := regularisedR12TimeSeparation_eq_zero_of_interval_tests T hVc hRc hzero
  -- the fundamental theorem of calculus at each point
  intro z hz hzT i
  let a : ℝ := z.2 / 2
  have ha0 : 0 < a := half_pos hz
  have haz : a < z.2 := half_lt_self hz
  let f : ℝ → ℝ := fun s => R (z.1, s) i
  have hfc : ContinuousOn f (Ioo 0 T) :=
    (continuousOn_pi.1 hRc i).comp (hline z.1).continuousOn fun s hs => ⟨Set.mem_univ _, hs⟩
  have hzmem : z.2 ∈ Ioo 0 T := ⟨hz, hzT⟩
  have hInt : IntervalIntegrable f volume a z.2 :=
    (hfc.mono (Icc_subset_Ioo ha0 hzT)).intervalIntegrable_of_Icc haz.le
  have hmeas : StronglyMeasurableAtFilter f (𝓝 z.2) :=
    hfc.stronglyMeasurableAtFilter isOpen_Ioo z.2 hzmem
  have hcont : ContinuousAt f z.2 := hfc.continuousAt (isOpen_Ioo.mem_nhds hzmem)
  have hDer := (intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont).const_add
    (u (z.1, a) i)
  refine hDer.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds haz hzT] with s hs
  have has : a < s := hs.1
  have h := congrArg (fun v : Vec3 => v i)
    (hsep z.1 a s has ⟨ha0, haz.trans hzT⟩ ⟨ha0.trans has, hs.2⟩)
  simp only [V, Pi.sub_apply] at h
  rw [hcomm z.1 a s has.le ha0 hs.2 i] at h
  simp only [f]
  linarith only [h]

/-- The canonical pointwise regularized velocity has its classical time
derivative given by the regularized momentum equation (`thm:regularised`). -/
theorem regularisedR12_timeDerivative
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hCurve : ∀ t : ℝ, 0 ≤ t →
      (fun x : Vec3 => u (x, t)) =ᵐ[volume]
        realVectorL2Representative
          (regularizedGlobalMildCurve ρ ε hε
            (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
              (regMollifiedInitial_isInJ ρ ε hε ha).1)
            (regUniformMollifiedInitial_mildJData ρ ε hε ha) t))
    (hPressure : ∀ z : ParabolicPoint, 0 < z.2 →
      p z = forcedQuadPressure ρ ε hε
        (regularizedGlobalMildCurve ρ ε hε
          (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
            (regMollifiedInitial_isInJ ρ ε hε ha).1)
          (regUniformMollifiedInitial_mildJData ρ ε hε ha)) z)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hD : ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDD : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hP : ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDp : ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j : Fin 3,
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) :
    ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => u (z.1, s) i)
        ((∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) -
          (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
            spatialPartial (fun y => u y i) j z) -
          spatialPartial (fun y => p y) i z) z.2 := by
  intro z hz i
  let b₀ : RealVectorL2 := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  let h₀ : RegularizedMildJData b₀ :=
    regUniformMollifiedInitial_mildJData ρ ε hε ha
  let U : ℝ → RealVectorL2 := regularizedGlobalMildCurve ρ ε hε b₀ h₀
  let T : ℝ := z.2 + 1
  have hT : 0 < T := by dsimp [T]; linarith only [hz]
  have hTz : z.2 < T := by dsimp [T]; linarith only [hz]
  have hSliceAll (t : ℝ) (ht : 0 ≤ t) :
      MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    (realVectorL2Representative_memLp_two (U t)).ae_eq (hCurve t ht).symm
  have hSlice (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      MemLp (fun x : Vec3 => u (x, t)) 2 volume := hSliceAll t ht.1
  have hRep (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t))
        (hSlice t ht) = U t := by
    apply realVectorL2Representative_injective_ae
    exact (realVectorL2OfCoordinateFunction_rep _ _).trans (hCurve t ht.1)
  have hPath (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      regularisedIntervalMildCurve u T hT.le hSlice t = U t := by
    simp only [regularisedIntervalMildCurve,
      regularizedMildTimeClamp_eq_of_mem T hT.le ht]
    exact hRep t ht
  have hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1))
        (hSlice t.1 t.2)) := by
    have hUcont := regularizedGlobalMildCurve_continuous ρ ε hε b₀ h₀
    have hRepCont : (fun t : Set.Icc (0 : ℝ) T =>
        realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1))
          (hSlice t.1 t.2)) = fun t => U t.1 := by
      funext t
      exact hRep t.1 t.2
    rw [hRepCont]
    exact hUcont.comp continuous_subtype_val
  have hMild : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t)) (hSlice t ht) =
        realHeatOperator t ht.1 b₀ - regularizedMildStokesIntegral
          (regularizedMildTensorTrajectory ρ ε hε
            (regularisedIntervalMildCurve u T hT.le hSlice)) t := by
    intro t ht
    rw [hRep t ht]
    refine (regularizedGlobalMildCurve_mild ρ ε hε b₀ h₀ t ht.1).trans ?_
    congr 1
    apply regularizedMildStokesIntegral_congr_Icc
    intro s hs
    simp only [regularizedMildTensorTrajectory]
    rw [hPath s ⟨hs.1, hs.2.trans ht.2⟩]
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    Set.prod_mono subset_rfl Set.Ioc_subset_Ioi_self
  have hPc : ContinuousOn
      (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)) := by
    apply (hP.mono hsub).congr
    intro w hw
    have hPath' := hPath w.2 ⟨hw.2.1.le, hw.2.2⟩
    rw [hPressure w hw.2.1]
    unfold regularisedIntervalCanonicalPressure forcedQuadPressure
    rw [hPath']
  have hUspatial (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (i : Fin 3) :
      ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) := by
    have hmem (x : Vec3) : ((x, t) : ParabolicPoint) ∈
        spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) := ⟨Set.mem_univ _, ht.1⟩
    refine regularisedR12TimeFinal_contDiff_of_partials _
      (fun x => hUdiff (x, t) (hmem x) i) fun j => ?_
    have hprod := regUniform_continuousOn_pullback
      (Sprod := Set.univ ×ˢ Set.Ioi 0) (hD i j) (fun w hw => ⟨Set.mem_univ _, hw.2⟩)
    exact hprod.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => ⟨Set.mem_univ _, ht.1⟩)
  have hWeak := regularisedR12_weakMomentum_spatial ρ ε hε a ha u T hT
    hSlice hL2Continuous hMild (fun i => (hU i).mono hsub) (fun i j => (hD i j).mono hsub)
    hPc hUspatial
  have hWeakP : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∫ w in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
        (-(∑ k : Fin 3, u w k * timePartial (fun y => φ y k) w)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u w j * u w k *
              spatialPartial (fun y => φ y k) j w
          + ∑ k : Fin 3, ∑ j : Fin 3,
            spatialPartial (fun y => u y k) j w *
              spatialPartial (fun y => φ y k) j w
          - p w * (∑ k : Fin 3, spatialPartial (fun y => φ y k) k w)) = 0 := by
    intro φ hφ
    have heq (w : ParabolicPoint)
        (hw : w ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T)) :
        regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice w = p w := by
      have hPath' := hPath w.2 ⟨hw.2.1.le, hw.2.2.le⟩
      rw [hPressure w hw.2.1]
      unfold regularisedIntervalCanonicalPressure forcedQuadPressure
      rw [hPath']
    have h := hWeak φ hφ
    calc
      _ = ∫ w in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
          (-(∑ k : Fin 3, u w k * timePartial (fun y => φ y k) w)
            - ∑ k : Fin 3, ∑ j : Fin 3,
              regUniformMollifiedVelocity ρ ε hε u w j * u w k *
                spatialPartial (fun y => φ y k) j w
            + ∑ k : Fin 3, ∑ j : Fin 3,
              spatialPartial (fun y => u y k) j w *
                spatialPartial (fun y => φ y k) j w
            - regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice w *
                (∑ k : Fin 3, spatialPartial (fun y => φ y k) k w)) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)]
            with w hw
          rw [heq w hw]
      _ = 0 := h
  have hDiv (t : ℝ) (ht : 0 < t) :
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)) := by
    have hcurveJ := regularizedGlobalMildCurve_mildJData ρ ε hε b₀ h₀ t ht.le
    have hweak := (CKN.isInJ_iff_weakDivFree).1 hcurveJ
    exact isWeakDivFree_congr_ae (hCurve t ht.le).symm hweak
  exact regularisedR12TimeFinal_core ρ ε hε u p T hT hSliceAll hWeakP hU hD hDD hP hDp
    hUdiff hDdiff hPdiff hDiv z hz hTz i

end CKN.Leray

end
