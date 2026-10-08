/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalTimeWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalMollified
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport

/-!
# Time derivatives of spatial momentum pairings

Testing the interval weak momentum identity with a spatial field times a
compact time test identifies the weak derivative of each spatial pairing.
Continuity of the fields makes the paired flux continuous in time.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regularisedR12TimePairing_continuous_integral
    {T : ℝ} {K : Set Vec3} (hK : IsCompact K)
    {H : Vec3 × ℝ → ℝ}
    (hH : ContinuousOn H (Set.univ ×ˢ Ioo 0 T))
    (hzero : ∀ z ∈ Set.univ ×ˢ Ioo 0 T, z.1 ∉ K → H z = 0) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, H (x, t) ∂volume) (Ioo 0 T) := by
  let Q : ℝ → Vec3 → ℝ := fun t x => H (x, t)
  have hQ : ContinuousOn Q.uncurry (Ioo 0 T ×ˢ Set.univ) := by
    have hswap : Continuous (fun z : ℝ × Vec3 => (z.2, z.1)) :=
      continuous_snd.prodMk continuous_fst
    exact hH.comp hswap.continuousOn (fun z hz => ⟨Set.mem_univ _, hz.1⟩)
  exact continuousOn_integral_of_compact_support hK hQ
    (fun t x ht hx => hzero (x, t) ⟨Set.mem_univ _, ht⟩ hx)

private theorem regularisedR12TimePairing_integrable_product
    {T : ℝ} {K : Set Vec3} (hK : IsCompact K)
    {H : Vec3 × ℝ → ℝ}
    (hH : ContinuousOn H (Set.univ ×ˢ Ioo 0 T))
    (hzero : ∀ z ∈ Set.univ ×ˢ Ioo 0 T, z.1 ∉ K → H z = 0)
    {θ : ℝ → ℝ} (hθc : Continuous θ) (hθk : HasCompactSupport θ)
    (hθs : tsupport θ ⊆ Ioo 0 T) :
    Integrable (fun z : Vec3 × ℝ => H z * θ z.2)
      (volume.restrict (Set.univ ×ˢ Ioo 0 T)) := by
  let Q : Vec3 × ℝ → ℝ := fun z => H z * θ z.2
  let L : Set ℝ := tsupport θ
  have hKL : IsCompact (K ×ˢ L) := hK.prod hθk.isCompact
  have hQzero (z : Vec3 × ℝ) (hz : z ∉ K ×ˢ L) : Q z = 0 := by
    by_cases ht : z.2 ∈ L
    · have hx : z.1 ∉ K := fun hx => hz ⟨hx, ht⟩
      change H z * θ z.2 = 0
      rw [hzero z ⟨Set.mem_univ _, hθs ht⟩ hx, zero_mul]
    · have hθzero : θ z.2 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [Q, hθzero]
  have hQs : tsupport Q ⊆ K ×ˢ L := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      exact (Function.mem_support.mp hz) (hQzero z hnot)
    · exact hK.isClosed.prod (isClosed_tsupport θ)
  have hQk : HasCompactSupport Q := HasCompactSupport.intro hKL hQzero
  have hQS : tsupport Q ⊆ Set.univ ×ˢ Ioo 0 T :=
    hQs.trans (Set.prod_mono (Set.subset_univ _) hθs)
  have hQcontOn : ContinuousOn Q (Set.univ ×ˢ Ioo 0 T) :=
    hH.mul ((hθc.comp continuous_snd).continuousOn)
  have hQcont : Continuous Q := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ Set.univ ×ˢ Ioo 0 T
    · exact (hQcontOn z hz).continuousAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
    · have hzt : z ∉ tsupport Q := fun h => hz (hQS h)
      have hnear : Q =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
        (notMem_tsupport_iff_eventuallyEq).mp hzt
      exact continuousAt_const.congr_of_eventuallyEq hnear
  exact (hQcont.integrable_of_hasCompactSupport hQk).integrableOn

private theorem regularisedR12TimePairing_of_product_tests
    (T : ℝ) {K : Set Vec3} (hK : IsCompact K)
    {A B : Vec3 × ℝ → ℝ}
    (hA : ContinuousOn A (Set.univ ×ˢ Ioo 0 T))
    (hB : ContinuousOn B (Set.univ ×ˢ Ioo 0 T))
    (hAz : ∀ z ∈ Set.univ ×ˢ Ioo 0 T, z.1 ∉ K → A z = 0)
    (hBz : ∀ z ∈ Set.univ ×ˢ Ioo 0 T, z.1 ∉ K → B z = 0)
    (hWeak : ∀ θ : ℝ → ℝ, CKN.IsIntervalTest (Ioo 0 T) θ →
      ∫ z in Set.univ ×ˢ Ioo 0 T,
        (-(A z * deriv θ z.2) - B z * θ z.2) = 0) :
    let F : ℝ → ℝ := fun t => ∫ x : Vec3, A (x, t) ∂volume
    let G : ℝ → ℝ := fun t => ∫ x : Vec3, B (x, t) ∂volume
    ContinuousOn F (Ioo 0 T) ∧ ContinuousOn G (Ioo 0 T) ∧
      CKN.HasWeakDerivOn (Ioo 0 T) F G := by
  dsimp only
  have hFc := regularisedR12TimePairing_continuous_integral hK hA hAz
  have hGc := regularisedR12TimePairing_continuous_integral hK hB hBz
  refine ⟨hFc, hGc, ?_⟩
  intro θ hθ
  have hθdcont : Continuous (deriv θ) := hθ.1.continuous_deriv (by norm_num)
  have hθdk : HasCompactSupport (deriv θ) := hθ.2.1.deriv
  have hθds : tsupport (deriv θ) ⊆ Ioo 0 T :=
    (tsupport_deriv_subset (f := θ)).trans hθ.2.2
  have hAint := regularisedR12TimePairing_integrable_product hK hA hAz
    hθdcont hθdk hθds
  have hBint := regularisedR12TimePairing_integrable_product hK hB hBz
    hθ.1.continuous hθ.2.1 hθ.2.2
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ Ioo 0 T) =
      (volume.restrict Set.univ).prod (volume.restrict (Ioo 0 T)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod Vec3 ℝ]
  have hAprod : Integrable (fun z : Vec3 × ℝ => A z * deriv θ z.2)
      ((volume.restrict Set.univ).prod (volume.restrict (Ioo 0 T))) := by
    rwa [← hmeasure]
  have hBprod : Integrable (fun z : Vec3 × ℝ => B z * θ z.2)
      ((volume.restrict Set.univ).prod (volume.restrict (Ioo 0 T))) := by
    rwa [← hmeasure]
  have hFubiniA :
      (∫ z in Set.univ ×ˢ Ioo 0 T, A z * deriv θ z.2) =
        ∫ t in Ioo 0 T, (∫ x : Vec3, A (x, t) ∂volume) * deriv θ t := by
    rw [hmeasure, integral_prod_symm _ hAprod]
    simp only [Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [integral_mul_const]
  have hFubiniB :
      (∫ z in Set.univ ×ˢ Ioo 0 T, B z * θ z.2) =
        ∫ t in Ioo 0 T, (∫ x : Vec3, B (x, t) ∂volume) * θ t := by
    rw [hmeasure, integral_prod_symm _ hBprod]
    simp only [Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [integral_mul_const]
  have hzero := hWeak θ hθ
  have hsplit : (∫ z in Set.univ ×ˢ Ioo 0 T,
      -(A z * deriv θ z.2) - B z * θ z.2) =
      -(∫ z in Set.univ ×ˢ Ioo 0 T, A z * deriv θ z.2) -
        ∫ z in Set.univ ×ˢ Ioo 0 T, B z * θ z.2 := by
    simpa only [Pi.neg_apply, integral_neg] using (integral_sub hAint.neg hBint)
  rw [hsplit, hFubiniA, hFubiniB] at hzero
  dsimp [CKN.HasWeakDerivOn]
  linarith only [hzero]

/-- The interval weak momentum identity gives a continuous weak derivative
for every smooth compactly supported spatial momentum pairing. -/
theorem regularisedR12TimePairing_weakDeriv
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
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
    (hP : ContinuousOn p
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (η : Vec3 → Vec3) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) :
    let F : ℝ → ℝ := fun t => ∫ x : Vec3,
      ∑ i : Fin 3, u (x, t) i * η x i
    let G : ℝ → ℝ := fun t => ∫ x : Vec3,
      (∑ i : Fin 3, ∑ j : Fin 3,
        regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
          spatialDeriv (fun y => η y i) j x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j (x, t) *
            spatialDeriv (fun y => η y i) j x)
        + p (x, t) * (∑ i : Fin 3,
          spatialDeriv (fun y => η y i) i x)
    ContinuousOn F (Ioo 0 T) ∧ ContinuousOn G (Ioo 0 T) ∧
      CKN.HasWeakDerivOn (Ioo 0 T) F G := by
  have hTpos : 0 < T := hT
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioo 0 T
  let K : Set Vec3 := tsupport η
  have hK : IsCompact K := hηc.isCompact
  have hηi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => η x i) :=
    hη.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hηsupport (i : Fin 3) : tsupport (fun x : Vec3 => η x i) ⊆ K := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hnot
      exact (Function.mem_support.mp hx) (congrFun hz i)
    · exact isClosed_tsupport η
  have hηzero (x : Vec3) (hx : x ∉ K) (i : Fin 3) : η x i = 0 := by
    have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    exact congrFun hz i
  have hDηzero (x : Vec3) (hx : x ∉ K) (i j : Fin 3) :
      spatialDeriv (fun y => η y i) j x = 0 := by
    have hnot : x ∉ tsupport (spatialDeriv (fun y => η y i) j) :=
      fun h => hx (hηsupport i (CKN.tsupport_spatialDeriv_subset j h))
    exact image_eq_zero_of_notMem_tsupport hnot
  have hSsub : S ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2.1⟩
  have hUc (i : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => u z i) S :=
    regUniform_continuousOn_pullback (hU i) (fun z hz => hSsub hz)
  have hDc (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => u y i) j z) S :=
    regUniform_continuousOn_pullback (hD i j) (fun z hz => hSsub hz)
  have hPc : ContinuousOn (fun z : Vec3 × ℝ => p z) S :=
    regUniform_continuousOn_pullback hP (fun z hz => hSsub hz)
  have hJc (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u z j) S := by
    have hconv := regR12_convolution_continuousOn
      (regR12Kernel_mollifier_continuous ρ ε hε)
      (regR12Kernel_mollifier_compact ρ ε hε) (hUc j)
      (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
    apply hconv.congr
    intro z hz
    exact regR12_mollifiedVelocity_eq_integral ρ ε hε u z.2
      (hSlice z.2 ⟨hz.2.1.le, hz.2.2.le⟩) z.1 j
  let A : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, u z i * η z.1 i
  let B : Vec3 × ℝ → ℝ := fun z =>
    (∑ i : Fin 3, ∑ j : Fin 3,
      regUniformMollifiedVelocity ρ ε hε u z j * u z i *
        spatialDeriv (fun y => η y i) j z.1)
      - (∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (fun y => u y i) j z *
          spatialDeriv (fun y => η y i) j z.1)
      + p z * (∑ i : Fin 3, spatialDeriv (fun y => η y i) i z.1)
  have hA : ContinuousOn A S := by
    exact continuousOn_finsetSum _ fun i _ =>
      (hUc i).mul (((hηi i).continuous.comp continuous_fst).continuousOn)
  have hB : ContinuousOn B S := by
    refine ((continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ =>
        ((hJc j).mul (hUc i)).mul
          ((((hηi i).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
            continuous_fst).continuousOn).sub
      (continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun j _ =>
          (hDc i j).mul
            ((((hηi i).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
              continuous_fst).continuousOn)).add ?_
    exact hPc.mul (continuous_finsetSum _ fun i _ =>
      ((((hηi i).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
        continuous_fst)).continuousOn
  have hAz : ∀ z ∈ S, z.1 ∉ K → A z = 0 := by
    intro z hz hx
    simp [A, hηzero z.1 hx]
  have hBz : ∀ z ∈ S, z.1 ∉ K → B z = 0 := by
    intro z hz hx
    simp [B, hDηzero z.1 hx]
  have hWeakAB : ∀ θ : ℝ → ℝ, CKN.IsIntervalTest (Ioo 0 T) θ →
      ∫ z in S, (-(A z * deriv θ z.2) - B z * θ z.2) = 0 := by
    intro θ hθ
    let Φ : ParabolicPoint → Vec3 := fun z i => η z.1 i * θ z.2
    have hΦsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Φ z) := by
      apply contDiff_pi.mpr
      intro i
      exact ((hηi i).comp contDiff_fst).mul (hθ.1.comp contDiff_snd)
    have hΦsupp : Function.support (show Vec3 × ℝ → Vec3 from Φ) ⊆
        K ×ˢ tsupport θ := by
      intro z hz
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (Function.mem_support.mp hz)
      have hi' : η z.1 i * θ z.2 ≠ 0 := hi
      have hx : z.1 ∈ K := by
        by_contra hnot
        exact hi' (by rw [hηzero z.1 hnot i, zero_mul])
      exact ⟨hx, subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hi'))⟩
    have hΦcompact : HasCompactSupport (show Vec3 × ℝ → Vec3 from Φ) :=
      HasCompactSupport.of_support_subset_isCompact (hK.prod hθ.2.1.isCompact) hΦsupp
    have hΦts : tsupport (show Vec3 × ℝ → Vec3 from Φ) ⊆ S := by
      refine (closure_minimal hΦsupp (hK.isClosed.prod (isClosed_tsupport θ))).trans ?_
      exact Set.prod_mono (Set.subset_univ _) hθ.2.2
    have hΦ : Φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Ioo 0 T) := by
      exact ⟨hΦsmooth, hΦcompact, hΦts⟩
    have htime (i : Fin 3) (z : ParabolicPoint) :
        timePartial (fun y => Φ y i) z = η z.1 i * deriv θ z.2 :=
      CKN.Core.Endgame.timePartial_separatedProduct (fun x => η x i) hθ.1 z
    have hspace (i j : Fin 3) (z : ParabolicPoint) :
        spatialPartial (fun y => Φ y i) j z =
          spatialDeriv (fun x => η x i) j z.1 * θ z.2 :=
      CKN.Core.Endgame.spatialPartial_separatedProduct θ (hηi i) j z
    have hpoint (z : ParabolicPoint) :
        (-(∑ k : Fin 3, u z k * timePartial (fun y => Φ y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u z j * u z k *
              spatialPartial (fun y => Φ y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
            spatialPartial (fun y => u y k) j z *
              spatialPartial (fun y => Φ y k) j z
          - p z * (∑ k : Fin 3, spatialPartial (fun y => Φ y k) k z)) =
        -(A z * deriv θ z.2) - B z * θ z.2 := by
      simp only [htime, hspace, A, B]
      simp_rw [← mul_assoc]
      simp only [← Finset.sum_mul]
      ring
    have hid := hWeak Φ hΦ
    rw [setIntegral_parabolic_to_product] at hid
    simp only [parabolicHomeomorph_symm_apply] at hid
    calc
      (∫ q in S, (-(A q * deriv θ q.2) - B q * θ q.2)) =
          ∫ q in S,
            (-(∑ k : Fin 3, u q k * timePartial (fun y => Φ y k) q)
              - ∑ k : Fin 3, ∑ j : Fin 3,
                regUniformMollifiedVelocity ρ ε hε u q j * u q k *
                  spatialPartial (fun y => Φ y k) j q
              + ∑ k : Fin 3, ∑ j : Fin 3,
                spatialPartial (fun y => u y k) j q *
                  spatialPartial (fun y => Φ y k) j q
              - p q * (∑ k : Fin 3, spatialPartial (fun y => Φ y k) k q)) := by
          apply integral_congr_ae
          filter_upwards [] with q
          exact (hpoint q).symm
      _ = 0 := by simpa only [S] using hid
  exact regularisedR12TimePairing_of_product_tests T hK hA hB hAz hBz hWeakAB

end CKN.Leray

end
