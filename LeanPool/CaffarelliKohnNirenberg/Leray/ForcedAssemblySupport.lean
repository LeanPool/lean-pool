/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyHopfData
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureMixedNorm
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsForcedLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallyQIntegrableForce
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data

/-!
# Data and divergence clauses for the forced limit

The data clauses and the divergence identity of `def:sws` for the forced
limit in the proof of `thm:leray-forced`. They use only the energy class, the
weak-gradient and divergence clauses shared by `def:forced-leray-hopf` and
`def:leray-hopf`, the local pressure integrability, and the assumed local
integrability of the force.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Strong `L²` convergence passes to the pairing with a fixed `L²` field. -/
theorem forcedAssembly_pairing_tendsto_of_strong_two
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ) (G w : α → ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ) (hw : MemLp w 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x * w x ∂μ) atTop
      (nhds (∫ x, G x * w x ∂μ)) := by
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hbound (n : ℕ) :
      eLpNorm ((fun x => F n x * w x) - fun x => G x * w x) 1 μ ≤
        eLpNorm (F n - G) 2 μ * eLpNorm w 2 μ := by
    have heq : ((fun x => F n x * w x) - fun x => G x * w x) =
        (F n - G) • w := by
      funext x
      change F n x * w x - G x * w x = (F n x - G x) * w x
      ring
    rw [heq]
    exact eLpNorm_smul_le_mul_eLpNorm_of_pos (by norm_num)
  have hmul : Tendsto (fun n => eLpNorm (F n - G) 2 μ * eLpNorm w 2 μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hw.eLpNorm_ne_top)
  refine tendsto_integral_of_L1' (fun x => G x * w x)
    (Eventually.of_forall fun n => (hF n).integrable_mul hw) ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hbound)

/-- The weak-divergence clause of a forced Leray--Hopf solution pairs to zero
with any compact smooth scalar test on the finite-time product slab. -/
theorem forcedAssembly_divergence_pairing_zero
    {T : ℝ} {a : Vec3 → Vec3} {f u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsForcedLerayHopfSolution T a f u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
        CKN.spatialPartialProd g i z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  rcases hLH with ⟨_, _, _, huMeas, _, _, hJointTop, _, hWeakDiv, _, _, _,
    _⟩
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have huFinite : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_right (by positivity)
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top huMeas huFinite
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q)) (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  have hcomp := hu2.comp_measurePreserving hMapProd
  change MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' Q)) at hcomp
  have hset : parabolicHomeomorph.symm ⁻¹' Q =
      ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
    ext z
    change ((parabolicHomeomorph.symm z).1 ∈ Set.univ ∧
      (parabolicHomeomorph.symm z).2 ∈ Ioo 0 T) ↔ z ∈ Set.univ ×ˢ Ioo 0 T
    simp
  rw [hset, ← Measure.prod_restrict] at hcomp
  have hU : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 μ := by
    simpa only [Measure.restrict_univ] using hcomp
  let F : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd g i z
  have hGrad (i : Fin 3) : MemLp (CKN.spatialPartialProd g i) 2 μ := by
    have hglobal : MemLp (CKN.spatialPartialProd g i) 2
        (volume : Measure (Vec3 × ℝ)) := by
      change MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) 2 _
      have hcont : Continuous (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) :=
        (CKN.spatialPartial_contDiff hg i).continuous
      have hcompact := CKN.hasCompactSupport_spatialPartial hgc i
      simpa [CKN.spatialPartialProd] using
        hcont.memLp_of_hasCompactSupport hcompact
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hFint : Integrable F μ := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i _
    have hUi : MemLp
        (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    have hterm : MemLp
        (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
          CKN.spatialPartialProd g i z) 1 μ := hUi.mul (hGrad i)
    exact memLp_one_iff_integrable.mp (by simpa [F] using hterm)
  have hEq :
      ∫ z : Vec3 × ℝ, F z ∂μ =
        ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, F z ∂μ =
          ∫ z : ℝ × Vec3, F z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) F).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => F z.swap) hFint.swap
  have hzeroSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x, t) ∂volume = 0 := by
    filter_upwards [hWeakDiv] with t ht
    let K : Set Vec3 := (tsupport g).image Prod.fst
    have hK : IsCompact K := hgc.isCompact.image continuous_fst
    have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) :=
      hg.comp (contDiff_id.prodMk contDiff_const)
    have hgcSlice : HasCompactSupport (fun x : Vec3 => g (x, t)) :=
      HasCompactSupport.of_support_subset_isCompact hK (by
        intro x hx
        have hx' : (x, t) ∈ Function.support g := by
          change g (x, t) ≠ 0
          exact Function.mem_support.mp hx
        exact ⟨(x, t), (subset_tsupport (f := g)) hx', rfl⟩)
    let htest : CKN.WeakTestFunction (Set.univ : Set Vec3) :=
      ⟨fun x => g (x, t), hgSlice, hgcSlice, Set.subset_univ _⟩
    have hzero := ht htest
    have hpartial (i : Fin 3) (x : Vec3) :
        htest.partialDeriv i x = CKN.spatialPartialProd g i (x, t) := by
      rfl
    have hfun : (fun x : Vec3 => F (x, t)) =
        (fun x => ∑ i : Fin 3, u (x, t) i * htest.partialDeriv i x) := by
      funext x
      simp [F, hpartial, parabolicHomeomorph_symm_apply]
    rw [hfun]
    exact hzero
  rw [hEq]
  rw [integral_congr_ae hzeroSlice]
  simp

/-- The divergence identity of `def:sws` on positive time follows from the
every-slab forced Leray--Hopf weak-divergence clause. -/
theorem forcedAssembly_hopfDivergence
    {a : Vec3 → Vec3} {f u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hglobal : ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
  let K : Set ParabolicPoint := tsupport ψ
  have hK : IsCompact K := by
    simpa [K, CKN.tsupport_parabolic_eq] using
      CKN.isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) := by
    simpa [K] using CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  obtain ⟨Ω', J, hbox, hKboxRaw⟩ := CKN.caccioppoli_localBox_of_compact_subset
    isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
  have hKbox : K ⊆ spaceTimeSet Ω' J := by
    simpa [K] using hKboxRaw
  obtain ⟨δ, T, hδ, hδT, hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
  have hT : 0 < T := lt_trans hδ hδT
  have hJ : J ⊆ Ioo 0 T := fun t ht =>
    ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
  have hlocalToSlab : spaceTimeSet Ω' J ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    Set.prod_mono (Set.subset_univ _) hJ
  have hKslabProduct : tsupport (show Vec3 × ℝ → ℝ from ψ) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    rw [← CKN.tsupport_parabolic_eq]
    exact hKbox.trans hlocalToSlab
  have hψslab : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioo 0 T) :=
    ⟨hψ.1, hψ.2.1, hKslabProduct⟩
  have hfullLocal := CKN.stability_divergence_integral_eq_localBox
    ψ hψ hKbox u
  have hslabLocal := CKN.stability_divergence_integral_eq_localBox
    ψ hψslab hKbox u
  let F : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
      CKN.spatialPartialProd ψ i z
  have hmeasure :
      ((volume : Measure Vec3).prod
        (volume.restrict (Ioo 0 T))) =
        (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.Leray.lerayPressureLimitSlab T) := by
    calc
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
          ((volume.restrict (Set.univ : Set Vec3)).prod
            (volume.restrict (Ioo 0 T))) := by simp
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Ioo 0 T) := by rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.Leray.lerayPressureLimitSlab T) := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
        rfl
  have hAssoc := forcedAssembly_divergence_pairing_zero
    (hglobal T hT) hψ.1 hψ.2.1
  have hAssocZero : (∫ z : Vec3 × ℝ, F z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))) = 0 := by
    simpa [F, CKN.spatialPartialProd] using hAssoc
  have hfiniteProduct : (∫ z in CKN.Leray.lerayPressureLimitSlab T,
      F z ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
    rw [← hmeasure]
    exact hAssocZero
  have hfinite := CKN.setIntegral_parabolic_to_product
    (Ω := (Set.univ : Set Vec3)) (I := Ioo 0 T)
    (F := fun z : ParabolicPoint =>
      ∑ i : Fin 3, u z i * spatialPartial ψ i z)
  have hslabZero :
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z) = 0 := by
    rw [hfinite]
    simpa [F, CKN.spatialPartialProd, CKN.Leray.lerayPressureLimitSlab]
      using hfiniteProduct
  calc
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z) =
      ∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, u z i * spatialPartial ψ i z := hfullLocal
    _ = ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z := hslabLocal.symm
    _ = 0 := hslabZero

/-- A global forced Leray--Hopf pair, local `L^{3/2}` pressure integrability
and local `L^q` integrability of the force give the data clauses of
`def:sws` on the positive-time half space. -/
theorem forcedAssembly_hopfData
    {a : Vec3 → Vec3} {f u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hglobal : ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du)
    (hp : ∀ Ω' J, CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)))
    {q : ℝ} (hq : 5 / 2 < q) (hfq : IsLocallyQIntegrableForce q f) :
    CKN.IsSuitableWeakSolutionData (Set.univ : Set Vec3) (Ioi 0) q u Du p
      f := by
  unfold CKN.IsSuitableWeakSolutionData
  refine ⟨isOpen_univ, isOpen_Ioi, ordConnected_Ioi, hq, hfq, ?_⟩
  intro Ω' J hbox
  obtain ⟨δ, T, hδ, hδT, hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
  have hT : 0 < T := lt_trans hδ hδT
  have hJ : J ⊆ Ioo 0 T := fun t ht =>
    ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
  let Q : Set ParabolicPoint := spaceTimeSet Ω' J
  have hΩ : Ω' ⊆ (Set.univ : Set Vec3) := Set.subset_univ _
  have hQ : Q ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
    Set.prod_mono hΩ hJ
  rcases hglobal T hT with
    ⟨_, _, hfT, hU, hDu, hSliceTop, hEnergyTop, hWeakGradient, _, _, _, _,
      _⟩
  have hQle : volume.restrict Q ≤
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono hQ le_rfl
  have hL2slice : essSup
      (fun s : ℝ => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ⊤ := by
    let G : ℝ → ℝ≥0∞ := fun s =>
      ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)
    have hglobalAE := ae_le_essSup
      (μ := volume.restrict (Ioo 0 T)) (f := G)
    have hJAE := ae_restrict_of_ae_restrict_of_subset hJ hglobalAE
    have hbound : ∀ᵐ s ∂volume.restrict J,
        (∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) ≤
          essSup G (volume.restrict (Ioo 0 T)) := by
      filter_upwards [hJAE] with s hs
      exact (lintegral_mono_set hΩ).trans (by simpa [G] using hs)
    exact lt_of_le_of_lt (essSup_le_of_ae_le _ hbound) hSliceTop
  have hEnergy :
      (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hQ) hEnergyTop
  have hWeakGradientLoc :
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i)
          (fun x => Du (x, s) i) := by
    intro i
    have hJAE := ae_restrict_of_ae_restrict_of_subset hJ hWeakGradient
    filter_upwards [hJAE] with s hs
    exact HasWeakGradientOn.restrict hbox.1 hΩ (hs i)
  have hfLoc : MemLp f (ENNReal.ofReal q) (volume.restrict Q) :=
    memLp_pi_iff.mpr (hfq Ω' J hbox)
  exact ⟨hU.mono_measure hQle, hDu.mono_measure hQle,
    (hp Ω' J hbox).aestronglyMeasurable,
    hfT.aestronglyMeasurable.mono_measure hQle, hL2slice, hEnergy,
    hp Ω' J hbox, hfLoc, hWeakGradientLoc⟩

end CKN.Leray

end
