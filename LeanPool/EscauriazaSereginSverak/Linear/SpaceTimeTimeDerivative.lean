/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportProduct
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Time sections of space-time weak derivatives

This module extracts the one-dimensional weak time derivative on almost every
spatial section from the space-time identity in `def:sws`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

@[expose] def timeCompact (τ : ℝ) (n : ℕ) : Set ℝ :=
  Icc (τ / ((n : ℝ) + 2)) (τ - τ / ((n : ℝ) + 2))

private theorem timeCompact_subset_Ioo {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    timeCompact τ n ⊆ Ioo 0 τ := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hleft : 0 < τ / ((n : ℝ) + 2) := div_pos hτ hden
  have hquot : 0 < τ / ((n : ℝ) + 2) := hleft
  have hright : τ - τ / ((n : ℝ) + 2) < τ := by linarith only [hquot]
  intro s hs
  exact ⟨lt_of_lt_of_le hleft hs.1, lt_of_le_of_lt hs.2 hright⟩

structure IntervalTestWithSupport (τ : ℝ) (n : ℕ) where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun
  supportInterval : tsupport toFun ⊆ Ioo 0 τ
  supportCompact : tsupport toFun ⊆ timeCompact τ n

@[expose] def intervalTestPair {τ : ℝ} {n : ℕ} (φ : IntervalTestWithSupport τ n) :
    C(ℝ, ℝ) × C(ℝ, ℝ) :=
  (⟨φ.toFun, φ.smooth.continuous⟩,
    ⟨deriv φ.toFun, φ.smooth.continuous_deriv (by norm_num)⟩)

private instance intervalTestTopology (τ : ℝ) (n : ℕ) :
    TopologicalSpace (IntervalTestWithSupport τ n) :=
  TopologicalSpace.induced intervalTestPair inferInstance

private instance intervalTestSecondCountable (τ : ℝ) (n : ℕ) :
    SecondCountableTopology (IntervalTestWithSupport τ n) :=
  TopologicalSpace.secondCountableTopology_induced _ _ intervalTestPair

private theorem exists_countable_dense_intervalTests (τ : ℝ) (n : ℕ) :
    ∃ S : Set (IntervalTestWithSupport τ n), S.Countable ∧ Dense S :=
  TopologicalSpace.exists_countable_dense _

private theorem dense_intervalTest_approx {τ : ℝ} {n : ℕ}
    (S : Set (IntervalTestWithSupport τ n)) (hS : Dense S)
    (φ : IntervalTestWithSupport τ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ S, ∀ t ∈ timeCompact τ n,
      |ψ.toFun t - φ.toFun t| < ε ∧
        |deriv ψ.toFun t - deriv φ.toFun t| < ε := by
  let pφ := intervalTestPair φ
  let N : Set (C(ℝ, ℝ) × C(ℝ, ℝ)) :=
    {p | MapsTo (p.1 - pφ.1) (timeCompact τ n) (Ioo (-ε) ε) ∧
      MapsTo (p.2 - pφ.2) (timeCompact τ n) (Ioo (-ε) ε)}
  have hbase : IsOpen {g : C(ℝ, ℝ) | MapsTo g (timeCompact τ n) (Ioo (-ε) ε)} :=
    ContinuousMap.isOpen_setOfPred_mapsTo
      (by simp [timeCompact]; exact isCompact_Icc) isOpen_Ioo
  have hN : IsOpen N := by
    apply IsOpen.inter
    · exact hbase.preimage (continuous_fst.sub continuous_const)
    · exact hbase.preimage (continuous_snd.sub continuous_const)
  have hφN : pφ ∈ N := by
    constructor
    · intro t _
      change pφ.1 t - pφ.1 t ∈ Ioo (-ε) ε
      simp only [sub_self, mem_Ioo]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
    · intro t _
      change pφ.2 t - pφ.2 t ∈ Ioo (-ε) ε
      simp only [sub_self, mem_Ioo]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
  let W : Set (IntervalTestWithSupport τ n) := intervalTestPair ⁻¹' N
  have hW : IsOpen W := hN.preimage continuous_induced_dom
  obtain ⟨ψ, hψW, hψS⟩ := hS.inter_open_nonempty W hW ⟨φ, hφN⟩
  refine ⟨ψ, hψS, ?_⟩
  have hψN : intervalTestPair ψ ∈ N := hψW
  intro t ht
  constructor
  · have hh := hψN.1 ht
    simpa [pφ, intervalTestPair, mem_Ioo, abs_lt] using hh
  · have hh := hψN.2 ht
    simpa [pφ, intervalTestPair, mem_Ioo, abs_lt] using hh

private theorem intervalTest_support_compact_exhaustion {τ : ℝ}
    {φ : ℝ → ℝ} (hφ : IsIntervalTest (Ioo 0 τ) φ) :
    ∃ n : ℕ, tsupport φ ⊆ timeCompact τ n := by
  let K := tsupport φ
  have hKcompact : IsCompact K := hφ.2.1.isCompact
  by_cases hKne : K.Nonempty
  · obtain ⟨m, hmK, hmmin⟩ := hKcompact.exists_isMinOn hKne continuousOn_id
    obtain ⟨M, hMK, hMmax⟩ := hKcompact.exists_isMaxOn hKne continuousOn_id
    have hmpos : 0 < m := (hφ.2.2 hmK).1
    have hMτ : M < τ := (hφ.2.2 hMK).2
    let δ := min m (τ - M)
    have hδ : 0 < δ := lt_min hmpos (sub_pos.mpr hMτ)
    obtain ⟨n, hn⟩ := exists_nat_gt (τ / δ)
    have hnratio : τ / δ < (n : ℝ) + 2 := by
      exact lt_trans hn (by norm_num)
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hmargin : τ / ((n : ℝ) + 2) < δ := by
      apply (div_lt_iff₀ hden).2
      have hnum' : τ < ((n : ℝ) + 2) * δ := (div_lt_iff₀ hδ).1 hnratio
      simpa [mul_comm] using hnum'
    refine ⟨n, ?_⟩
    intro t htK
    have htU := hφ.2.2 htK
    have hmt : m ≤ t := hmmin htK
    have htM : t ≤ M := hMmax htK
    dsimp [timeCompact, δ]
    constructor
    · have hleft : τ / ((n : ℝ) + 2) < m := lt_of_lt_of_le hmargin (min_le_left _ _)
      exact le_of_lt (lt_of_lt_of_le hleft hmt)
    · have hright : M < τ - τ / ((n : ℝ) + 2) := by
        have hMδ : M ≤ τ - δ := by
          dsimp [δ]
          linarith only [min_le_right m (τ - M)]
        exact lt_of_le_of_lt hMδ (sub_lt_sub_left hmargin τ)
      exact le_trans htM (le_of_lt hright)
  · refine ⟨0, ?_⟩
    intro t ht
    exact (hKne ⟨t, ht⟩).elim

private theorem intervalTest_deriv_tsupport_subset {τ : ℝ} {n : ℕ}
    (ψ : IntervalTestWithSupport τ n) :
    tsupport (deriv ψ.toFun) ⊆ timeCompact τ n := by
  change closure (Function.support (deriv ψ.toFun)) ⊆ timeCompact τ n
  rw [timeCompact]
  apply closure_minimal
  · intro s hs
    exact ψ.supportCompact (support_deriv_subset hs)
  · exact isClosed_Icc

private theorem locallyIntegrableOn_mul_continuousCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} {U : Set X}
    (hf : LocallyIntegrableOn f U μ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ U) :
    IntegrableOn (fun x => f x * g x) U μ := by
  let K := tsupport g
  have hKcompact : IsCompact K := hgc.isCompact
  have hfK : IntegrableOn f K μ := hf.integrableOn_compact_subset hgsupp hKcompact
  have hprodK : IntegrableOn (fun x => f x * g x) K μ := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      hfK.smul_continuousOn hg.continuousOn hKcompact
  have hprodSupport : Function.support (fun x => f x * g x) ⊆ K := by
    intro x hx
    have hgne : g x ≠ 0 := by
      intro hgz
      apply hx
      simp [hgz]
    exact subset_tsupport g (Function.mem_support.mpr hgne)
  exact ((integrableOn_iff_integrable_of_support_subset hprodSupport).mp hprodK).integrableOn

private theorem setIntegral_eq_of_support_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    {f : X → ℝ} (hKU : K ⊆ U) (hsupp : Function.support f ⊆ K) :
    (∫ x in U, f x ∂μ) = ∫ x in K, f x ∂μ := by
  have hU : (∫ x in U, f x ∂μ) = ∫ x, f x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxK : x ∉ K := fun h => hx (hKU h)
    by_contra hne
    exact hxK (hsupp (Function.mem_support.mpr hne))
  have hK : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hne
    exact hx (hsupp (Function.mem_support.mpr hne))
  exact hU.trans hK.symm

private theorem abs_setIntegral_mul_sub_le
    {K : Set ℝ} {f g h : ℝ → ℝ} {ε : ℝ}
    (hKmeas : MeasurableSet K)
    (hf : IntegrableOn f K volume)
    (hfg : IntegrableOn (fun s => f s * (g s - h s)) K volume)
    (hclose : ∀ s ∈ K, |g s - h s| ≤ ε) :
    |∫ s in K, f s * (g s - h s)| ≤ ε * ∫ s in K, |f s| := by
  have hfgAbs : IntegrableOn (fun s => |f s * (g s - h s)|) K volume := by
    change Integrable (fun s => |f s * (g s - h s)|) (volume.restrict K)
    exact hfg.norm
  have hfAbs : IntegrableOn (fun s => |f s|) K volume := by
    change Integrable (fun s => |f s|) (volume.restrict K)
    exact hf.norm
  have hupper : IntegrableOn (fun s => ε * |f s|) K volume := hfAbs.const_mul ε
  have hmono :
      (∫ s in K, |f s * (g s - h s)|) ≤ ∫ s in K, ε * |f s| := by
    apply integral_mono_ae hfgAbs hupper
    filter_upwards [ae_restrict_mem hKmeas] with s hs
    calc
      |f s * (g s - h s)| = |f s| * |g s - h s| := abs_mul _ _
      _ ≤ |f s| * ε := mul_le_mul_of_nonneg_left (hclose s hs) (abs_nonneg _)
      _ = ε * |f s| := mul_comm _ _
  calc
    |∫ s in K, f s * (g s - h s)| ≤ ∫ s in K, |f s * (g s - h s)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in K, ε * |f s| := hmono
    _ = ε * ∫ s in K, |f s| := integral_const_mul _ _

private theorem locallyIntegrableOn_parabolic_component_to_product
    {B : Set Vec3} {I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I)
    {f : ParabolicPoint → Vec3} (hf : LocallyIntegrableOn f (spaceTimeSet B I) volume)
    (i : Fin 3) :
    LocallyIntegrableOn
      (fun q : Vec3 × ℝ => f (parabolicHomeomorph.symm q) i) (B ×ˢ I) volume := by
  rw [locallyIntegrableOn_iff ((hB.prod hI).isLocallyClosed)]
  intro K hKU hK
  let Kp : Set ParabolicPoint := parabolicHomeomorph.symm '' K
  have hKp : IsCompact Kp := parabolicHomeomorph.symm.isCompact_image.mpr hK
  have hKpU : Kp ⊆ spaceTimeSet B I := by
    rintro p ⟨q, hq, rfl⟩
    exact hKU hq
  have hInt : IntegrableOn f Kp volume := hf.integrableOn_compact_subset hKpU hKp
  have hLp : MemLp f 1 (volume.restrict Kp) := memLp_one_iff_integrable.mpr hInt
  have hCoordLp : MemLp (fun p : ParabolicPoint => f p i) 1
      (volume.restrict Kp) :=
    hLp.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hCoord : IntegrableOn (fun p : ParabolicPoint => f p i) Kp volume :=
    memLp_one_iff_integrable.mp hCoordLp
  exact (parabolicHomeomorphSymm_measurePreserving.integrableOn_image
    parabolicHomeomorph.symm.measurableEmbedding).mp hCoord

private theorem timePartial_eq_zero_off_tsupport_parabolic
    {φ : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hz : z ∉ tsupport φ) : timePartial φ z = 0 := by
  have hzProd : (show Vec3 × ℝ from z) ∉
      tsupport (show Vec3 × ℝ → ℝ from φ) := by
    rw [← CKN.tsupport_parabolic_eq (show Vec3 × ℝ → ℝ from φ)]
    exact hz
  exact CKN.timePartial_eq_zero_off_tsupport hzProd

private theorem tsupport_timePartial_subset {φ : ParabolicPoint → ℝ} :
    tsupport (fun z : ParabolicPoint => timePartial φ z) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro z hz
  by_contra hnot
  exact hz (timePartial_eq_zero_off_tsupport_parabolic hnot)

private theorem hasCompactSupport_timePartial {φ : ParabolicPoint → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (fun z => timePartial φ z) := by
  have hφcompact : IsCompact (tsupport φ) := hφ.isCompact
  refine HasCompactSupport.intro hφcompact ?_
  intro z hz
  exact timePartial_eq_zero_off_tsupport_parabolic hz

private theorem mul_mem_spaceTimeTestFunction {B : Set Vec3} {I : Set ℝ}
    {η : Vec3 → ℝ} {ψ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηB : tsupport η ⊆ B)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψI : tsupport ψ ⊆ I) :
    (fun z : Vec3 × ℝ => η z.1 * ψ z.2) ∈
      spaceTimeTestFunction (V := ℝ) B I := by
  have hts : tsupport (fun z : Vec3 × ℝ => η z.1 * ψ z.2) =
      tsupport η ×ˢ tsupport ψ := CKN.tsupport_mul_prod_eq η ψ
  refine ⟨?_, ?_, ?_⟩
  · exact (hη.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hψ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  · change IsCompact (tsupport (fun z : Vec3 × ℝ => η z.1 * ψ z.2))
    rw [hts]
    exact IsCompact.prod hηc.isCompact hψc.isCompact
  · rw [hts]
    exact Set.prod_mono hηB hψI

@[expose] def sectionTimePairing {τ : ℝ}
  (w Dtw : ParabolicPoint → Vec3) (i : Fin 3)
    (ψ : ℝ → ℝ) (x : Vec3) : ℝ :=
  (∫ s in Ioo 0 τ,
    w (parabolicHomeomorph.symm (x, s)) i * deriv ψ s) +
  ∫ s in Ioo 0 τ,
    Dtw (parabolicHomeomorph.symm (x, s)) i * ψ s

private theorem sectionTimePairing_locallyIntegrableOn
    {B : Set Vec3} {τ : ℝ} (hB : IsOpen B) (hτ : 0 < τ)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs B (Ioo 0 τ) w Dw D2w Dtw)
    {n : ℕ} (ψ : IntervalTestWithSupport τ n) (i : Fin 3) :
    LocallyIntegrableOn (sectionTimePairing (τ := τ) w Dtw i ψ.toFun)
      B volume := by
  rw [locallyIntegrableOn_iff hB.isLocallyClosed]
  intro K hKB hK
  let Kt := timeCompact τ n
  have hKt : IsCompact Kt := by
    simp only [Kt, timeCompact]
    exact isCompact_Icc
  have hKtB : Kt ⊆ Ioo 0 τ := timeCompact_subset_Ioo hτ n
  have hKtderiv : tsupport (deriv ψ.toFun) ⊆ Kt := by
    change closure (Function.support (deriv ψ.toFun)) ⊆ timeCompact τ n
    rw [timeCompact]
    apply closure_minimal
    · intro s hs
      exact ψ.supportCompact (support_deriv_subset hs)
    · exact isClosed_Icc
  have hKprod : IsCompact (K ×ˢ Kt) := IsCompact.prod hK hKt
  have hKprodB : K ×ˢ Kt ⊆ B ×ˢ Ioo 0 τ := Set.prod_mono hKB hKtB
  have hWloc := locallyIntegrableOn_parabolic_component_to_product
    hB isOpen_Ioo hderiv.1 i
  have hDloc := locallyIntegrableOn_parabolic_component_to_product
    hB isOpen_Ioo hderiv.2.2.2.1 i
  have hWint := hWloc.integrableOn_compact_subset hKprodB hKprod
  have hDint := hDloc.integrableOn_compact_subset hKprodB hKprod
  have hWint' : IntegrableOn
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) (K ×ˢ Kt) volume := hWint
  have hDint' : IntegrableOn
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q) i) (K ×ˢ Kt) volume := hDint
  have hWA : IntegrableOn
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i *
        (deriv ψ.toFun ∘ Prod.snd) q)
      (K ×ˢ Kt) volume := by
    simpa only [smul_eq_mul] using
      hWint'.smul_continuousOn
        ((ψ.smooth.continuous_deriv (by norm_num)).comp continuous_snd).continuousOn
        hKprod
  have hDA : IntegrableOn
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q) i * ψ.toFun q.2)
      (K ×ˢ Kt) volume := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      hDint'.smul_continuousOn
        (ψ.smooth.continuous.comp continuous_snd).continuousOn hKprod
  have hWArest : Integrable
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i *
        (deriv ψ.toFun ∘ Prod.snd) q)
      ((volume.restrict K).prod (volume.restrict Kt)) := by
    change Integrable _ ((volume.prod volume).restrict (K ×ˢ Kt)) at hWA
    rw [← Measure.prod_restrict] at hWA
    exact hWA
  have hDArest : Integrable
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q) i * ψ.toFun q.2)
      ((volume.restrict K).prod (volume.restrict Kt)) := by
    change Integrable _ ((volume.prod volume).restrict (K ×ˢ Kt)) at hDA
    rw [← Measure.prod_restrict] at hDA
    exact hDA
  have hWAinner : IntegrableOn
      (fun x : Vec3 => ∫ s in Kt,
        w (parabolicHomeomorph.symm (x, s)) i * deriv ψ.toFun s) K volume :=
    hWArest.integral_prod_left
  have hDAinner : IntegrableOn
      (fun x : Vec3 => ∫ s in Kt,
        Dtw (parabolicHomeomorph.symm (x, s)) i * ψ.toFun s) K volume :=
    hDArest.integral_prod_left
  have hWsupport (x : Vec3) :
      Function.support (fun s : ℝ => w (parabolicHomeomorph.symm (x, s)) i *
        deriv ψ.toFun s) ⊆ Kt := by
    intro s hs
    have hne : deriv ψ.toFun s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    exact hKtderiv (subset_tsupport _ (Function.mem_support.mpr hne))
  have hDsupport (x : Vec3) :
      Function.support (fun s : ℝ => Dtw (parabolicHomeomorph.symm (x, s)) i *
        ψ.toFun s) ⊆ Kt := by
    intro s hs
    have hne : ψ.toFun s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    exact ψ.supportCompact (subset_tsupport _ (Function.mem_support.mpr hne))
  have hWeq (x : Vec3) :
      (∫ s in Ioo 0 τ, w (parabolicHomeomorph.symm (x, s)) i * deriv ψ.toFun s) =
        ∫ s in Kt, w (parabolicHomeomorph.symm (x, s)) i * deriv ψ.toFun s :=
    setIntegral_eq_of_support_subset hKtB (hWsupport x)
  have hDeq (x : Vec3) :
      (∫ s in Ioo 0 τ, Dtw (parabolicHomeomorph.symm (x, s)) i * ψ.toFun s) =
        ∫ s in Kt, Dtw (parabolicHomeomorph.symm (x, s)) i * ψ.toFun s :=
    setIntegral_eq_of_support_subset hKtB (hDsupport x)
  have hsum : IntegrableOn
      (fun x : Vec3 =>
        (∫ s in Kt, w (show ParabolicPoint from (x, s)) i * deriv ψ.toFun s) +
        ∫ s in Kt, Dtw (show ParabolicPoint from (x, s)) i * ψ.toFun s)
      K volume := hWAinner.add hDAinner
  have heq : ∀ x,
      sectionTimePairing (τ := τ) w Dtw i ψ.toFun x =
        (∫ s in Kt, w (parabolicHomeomorph.symm (x, s)) i * deriv ψ.toFun s) +
        ∫ s in Kt, Dtw (parabolicHomeomorph.symm (x, s)) i * ψ.toFun s := by
    intro x
    simp only [sectionTimePairing, hWeq x, hDeq x]
  exact hsum.congr (Filter.Eventually.of_forall fun x => (heq x).symm)

private theorem sectionTimePairing_eq_zero_of_dense
    {τ : ℝ} (hτ : 0 < τ) {w Dtw : ParabolicPoint → Vec3}
    (x : Vec3) (i : Fin 3)
    (hwcont : ContinuousOn (fun s => w (parabolicHomeomorph.symm (x, s)) i)
      (Ico 0 τ))
    (hDtwLp : MemLp (fun s => Dtw (parabolicHomeomorph.symm (x, s)) i) 2
      (volume.restrict (Ioo 0 τ)))
    {n : ℕ} (S : Set (IntervalTestWithSupport τ n)) (hS : Dense S)
    (hzero : ∀ ψ ∈ S,
      sectionTimePairing (τ := τ) w Dtw i ψ.toFun x = 0)
    (φ : IntervalTestWithSupport τ n) :
    sectionTimePairing (τ := τ) w Dtw i φ.toFun x = 0 := by
  let Kt := timeCompact τ n
  let u : ℝ → ℝ := fun s => w (parabolicHomeomorph.symm (x, s)) i
  let v : ℝ → ℝ := fun s => Dtw (parabolicHomeomorph.symm (x, s)) i
  have hKt : IsCompact Kt := by
    simp only [Kt, timeCompact]
    exact isCompact_Icc
  have hKtmeas : MeasurableSet Kt := hKt.measurableSet
  have hKtI : Kt ⊆ Ioo 0 τ := timeCompact_subset_Ioo hτ n
  have hKtIco : Kt ⊆ Ico 0 τ := by
    intro s hs
    exact ⟨le_of_lt (hKtI hs).1, (hKtI hs).2⟩
  have hucont : ContinuousOn u Kt := by
    exact hwcont.mono hKtIco
  have huInt : IntegrableOn u Kt volume := hucont.integrableOn_compact hKt
  have hvLp : MemLp v 2 (volume.restrict Kt) :=
    hDtwLp.mono_measure (Measure.restrict_mono_set volume hKtI)
  have hvμ : (volume.restrict Kt) Set.univ ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ, Set.univ_inter] using hKt.measure_ne_top
  let vLp : Lp ℝ 2 (volume.restrict Kt) := hvLp.toLp v
  have hvLpInt : Integrable vLp (volume.restrict Kt) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top vLp (by norm_num) hvμ
  have hvInt : IntegrableOn v Kt volume := by
    change Integrable v (volume.restrict Kt)
    exact hvLpInt.congr hvLp.coeFn_toLp
  have hderivSupport (θ : IntervalTestWithSupport τ n) :
      tsupport (deriv θ.toFun) ⊆ Kt := by
    simpa [Kt] using intervalTest_deriv_tsupport_subset θ
  have huSupport (θ : IntervalTestWithSupport τ n) :
      Function.support (fun s => u s * deriv θ.toFun s) ⊆ Kt := by
    intro s hs
    have hne : deriv θ.toFun s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    exact hderivSupport θ (subset_tsupport _ (Function.mem_support.mpr hne))
  have hvSupport (θ : IntervalTestWithSupport τ n) :
      Function.support (fun s => v s * θ.toFun s) ⊆ Kt := by
    intro s hs
    have hne : θ.toFun s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    exact θ.supportCompact (subset_tsupport _ (Function.mem_support.mpr hne))
  have hAeq (θ : IntervalTestWithSupport τ n) :
      (∫ s in Ioo 0 τ, u s * deriv θ.toFun s) =
        ∫ s in Kt, u s * deriv θ.toFun s :=
    setIntegral_eq_of_support_subset hKtI (huSupport θ)
  have hBeq (θ : IntervalTestWithSupport τ n) :
      (∫ s in Ioo 0 τ, v s * θ.toFun s) =
        ∫ s in Kt, v s * θ.toFun s :=
    setIntegral_eq_of_support_subset hKtI (hvSupport θ)
  have hpairCompact (θ : IntervalTestWithSupport τ n) :
      sectionTimePairing (τ := τ) w Dtw i θ.toFun x =
        (∫ s in Kt, u s * deriv θ.toFun s) +
          ∫ s in Kt, v s * θ.toFun s := by
    change (∫ s in Ioo 0 τ, u s * deriv θ.toFun s) +
        ∫ s in Ioo 0 τ, v s * θ.toFun s = _
    rw [hAeq θ, hBeq θ]
  have hAint (θ : IntervalTestWithSupport τ n) :
      IntegrableOn (fun s => u s * deriv θ.toFun s) Kt volume := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      huInt.smul_continuousOn
        (θ.smooth.continuous_deriv (by norm_num)).continuousOn hKt
  have hBint (θ : IntervalTestWithSupport τ n) :
      IntegrableOn (fun s => v s * θ.toFun s) Kt volume := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      hvInt.smul_continuousOn θ.smooth.continuous.continuousOn hKt
  have hCnonneg : 0 ≤
      (∫ s in Kt, |u s|) + (∫ s in Kt, |v s|) := by
    apply add_nonneg
    · positivity
    · positivity
  let C : ℝ := (∫ s in Kt, |u s|) + (∫ s in Kt, |v s|)
  have hpairEq (θ : IntervalTestWithSupport τ n) (hθ : θ ∈ S) :
      sectionTimePairing (τ := τ) w Dtw i φ.toFun x =
        ((∫ s in Kt, u s * deriv φ.toFun s) -
            ∫ s in Kt, u s * deriv θ.toFun s) +
          ((∫ s in Kt, v s * φ.toFun s) -
            ∫ s in Kt, v s * θ.toFun s) := by
    rw [hpairCompact φ]
    have hz := hzero θ hθ
    rw [hpairCompact θ] at hz
    linarith only [hz]
  have hpairBound (ε : ℝ) (θ : IntervalTestWithSupport τ n) (hθ : θ ∈ S)
      (happrox : ∀ s ∈ Kt,
        |θ.toFun s - φ.toFun s| < ε ∧
          |deriv θ.toFun s - deriv φ.toFun s| < ε) :
      |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| ≤ ε * C := by
    have hAdiffInt :
        IntegrableOn (fun s => u s * (deriv φ.toFun s - deriv θ.toFun s)) Kt volume := by
      simpa only [smul_eq_mul, Function.comp_apply, Pi.sub_apply] using
        huInt.smul_continuousOn
          ((φ.smooth.continuous_deriv (by norm_num)).sub
            (θ.smooth.continuous_deriv (by norm_num))).continuousOn hKt
    have hBdiffInt :
        IntegrableOn (fun s => v s * (φ.toFun s - θ.toFun s)) Kt volume := by
      simpa only [smul_eq_mul, Function.comp_apply, Pi.sub_apply] using
        hvInt.smul_continuousOn
          (φ.smooth.continuous.sub θ.smooth.continuous).continuousOn hKt
    have hAcalc :
        (∫ s in Kt, u s * deriv φ.toFun s) -
            ∫ s in Kt, u s * deriv θ.toFun s =
          ∫ s in Kt, u s * (deriv φ.toFun s - deriv θ.toFun s) := by
      rw [← integral_sub (hAint φ) (hAint θ)]
      apply setIntegral_congr_fun hKtmeas
      intro s hs
      ring
    have hBcalc :
        (∫ s in Kt, v s * φ.toFun s) -
            ∫ s in Kt, v s * θ.toFun s =
          ∫ s in Kt, v s * (φ.toFun s - θ.toFun s) := by
      rw [← integral_sub (hBint φ) (hBint θ)]
      apply setIntegral_congr_fun hKtmeas
      intro s hs
      ring
    have hAclose : ∀ s ∈ Kt,
        |deriv φ.toFun s - deriv θ.toFun s| ≤ ε := by
      intro s hs
      calc
        |deriv φ.toFun s - deriv θ.toFun s| =
            |deriv θ.toFun s - deriv φ.toFun s| := abs_sub_comm _ _
        _ ≤ ε := le_of_lt (happrox s hs).2
    have hBclose : ∀ s ∈ Kt,
        |φ.toFun s - θ.toFun s| ≤ ε := by
      intro s hs
      calc
        |φ.toFun s - θ.toFun s| = |θ.toFun s - φ.toFun s| := abs_sub_comm _ _
        _ ≤ ε := le_of_lt (happrox s hs).1
    have hAbound := abs_setIntegral_mul_sub_le hKtmeas huInt hAdiffInt hAclose
    have hBbound := abs_setIntegral_mul_sub_le hKtmeas hvInt hBdiffInt hBclose
    rw [hpairEq θ hθ, hAcalc, hBcalc]
    calc
      |(∫ s in Kt, u s * (deriv φ.toFun s - deriv θ.toFun s)) +
          ∫ s in Kt, v s * (φ.toFun s - θ.toFun s)| ≤
          |∫ s in Kt, u s * (deriv φ.toFun s - deriv θ.toFun s)| +
          |∫ s in Kt, v s * (φ.toFun s - θ.toFun s)| := abs_add_le _ _
      _ ≤ ε * (∫ s in Kt, |u s|) + ε * (∫ s in Kt, |v s|) :=
        add_le_add hAbound hBbound
      _ = ε * C := by dsimp [C]; ring
  by_contra hne
  have hFpos : 0 < |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| := abs_pos.mpr hne
  have hC : 0 ≤ C := by simpa [C] using hCnonneg
  have hden : 0 < C + 1 := by linarith only [hC]
  let ε := |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| / (C + 1)
  have hε : 0 < ε := div_pos hFpos hden
  obtain ⟨θ, hθ, happrox⟩ := dense_intervalTest_approx S hS φ hε
  have hbound := hpairBound ε θ hθ happrox
  have hstrict : ε * C < |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| := by
    dsimp [ε]
    rw [show |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| / (C + 1) * C =
      |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| * C / (C + 1) by ring]
    apply (div_lt_iff₀ hden).2
    calc
      |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| * C <
          |sectionTimePairing (τ := τ) w Dtw i φ.toFun x| * (C + 1) := by
        apply mul_lt_mul_of_pos_left _ hFpos
        linarith only [hC]
      _ = _ := by ring
  exact (not_le_of_gt hstrict) hbound

private theorem integral_eta_mul_sectionTimePairing_eq_zero
    {B : Set Vec3} {τ : ℝ} (hB : IsOpen B) (hτ : 0 < τ)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs B (Ioo 0 τ) w Dw D2w Dtw)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηB : tsupport η ⊆ B)
    {n : ℕ} (ψ : IntervalTestWithSupport τ n) (i : Fin 3) :
    ∫ x in B, η x * sectionTimePairing (τ := τ) w Dtw i ψ.toFun x = 0 := by
  let φ : ParabolicPoint → ℝ := fun z => η z.1 * ψ.toFun z.2
  have hψtest : IsIntervalTest (Ioo 0 τ) ψ.toFun :=
    ⟨ψ.smooth, ψ.compact, ψ.supportInterval⟩
  have htest : φ ∈ spaceTimeTestFunction (V := ℝ) B (Ioo 0 τ) := by
    change (fun z : Vec3 × ℝ => η z.1 * ψ.toFun z.2) ∈ _
    exact mul_mem_spaceTimeTestFunction hη hηc hηB ψ.smooth ψ.compact
      ψ.supportInterval
  have hformula (z : ParabolicPoint) :
      timePartial φ z = η z.1 * deriv ψ.toFun z.2 := by
    exact CKN.Core.Endgame.timePartial_separatedProduct η ψ.smooth z
  have htime := (hderiv.2.2.2.2 φ htest).2.2 i
  simp only [hformula] at htime
  have hWloc := locallyIntegrableOn_parabolic_component_to_product
    hB isOpen_Ioo hderiv.1 i
  have hDloc := locallyIntegrableOn_parabolic_component_to_product
    hB isOpen_Ioo hderiv.2.2.2.1 i
  have hderivSupport : tsupport (deriv ψ.toFun) ⊆ timeCompact τ n := by
    change closure (Function.support (deriv ψ.toFun)) ⊆ timeCompact τ n
    rw [timeCompact]
    apply closure_minimal
    intro s hs
    exact ψ.supportCompact (support_deriv_subset hs)
    exact isClosed_Icc
  have htimeK : IsCompact (timeCompact τ n) := by
    simp only [timeCompact]
    exact isCompact_Icc
  have hderivCompact : HasCompactSupport (deriv ψ.toFun) :=
    HasCompactSupport.of_support_subset_isCompact htimeK
      (fun s hs => hderivSupport (subset_tsupport _ hs))
  let ga : Vec3 × ℝ → ℝ := fun q => η q.1 * deriv ψ.toFun q.2
  have hgaCont : Continuous ga := by
    exact (hη.continuous.comp continuous_fst).mul
      ((ψ.smooth.continuous_deriv (by norm_num)).comp continuous_snd)
  have hgaSupport : tsupport ga = tsupport η ×ˢ tsupport (deriv ψ.toFun) :=
    CKN.tsupport_mul_prod_eq η (deriv ψ.toFun)
  have hgaCompact : HasCompactSupport ga := by
    apply HasCompactSupport.of_support_subset_isCompact
      (IsCompact.prod hηc.isCompact hderivCompact.isCompact)
    intro q hq
    rw [Function.mem_support] at hq
    have hηne : η q.1 ≠ 0 := by
      intro hz
      exact hq (mul_eq_zero.mpr (Or.inl hz))
    have hderivne : deriv ψ.toFun q.2 ≠ 0 := by
      intro hz
      exact hq (mul_eq_zero.mpr (Or.inr hz))
    exact ⟨subset_tsupport η (Function.mem_support.mpr hηne),
      subset_tsupport (deriv ψ.toFun) (Function.mem_support.mpr hderivne)⟩
  have hgaSubset : tsupport ga ⊆ B ×ˢ Ioo 0 τ := by
    rw [hgaSupport]
    exact Set.prod_mono hηB (hderivSupport.trans (timeCompact_subset_Ioo hτ n))
  let gb : Vec3 × ℝ → ℝ := fun q => η q.1 * ψ.toFun q.2
  have hgbCont : Continuous gb := by
    exact (hη.continuous.comp continuous_fst).mul
      (ψ.smooth.continuous.comp continuous_snd)
  have hgbSupport : tsupport gb = tsupport η ×ˢ tsupport ψ.toFun :=
    CKN.tsupport_mul_prod_eq η ψ.toFun
  have hgbCompact : HasCompactSupport gb := by
    apply HasCompactSupport.of_support_subset_isCompact
      (IsCompact.prod hηc.isCompact ψ.compact.isCompact)
    intro q hq
    rw [Function.mem_support] at hq
    have hηne : η q.1 ≠ 0 := by
      intro hz
      exact hq (mul_eq_zero.mpr (Or.inl hz))
    have hψne : ψ.toFun q.2 ≠ 0 := by
      intro hz
      exact hq (mul_eq_zero.mpr (Or.inr hz))
    exact ⟨subset_tsupport η (Function.mem_support.mpr hηne),
      subset_tsupport ψ.toFun (Function.mem_support.mpr hψne)⟩
  have hgbSubset : tsupport gb ⊆ B ×ˢ Ioo 0 τ := by
    rw [hgbSupport]
    exact Set.prod_mono hηB ψ.supportInterval
  have hWA : IntegrableOn
      (fun q : Vec3 × ℝ => w (show ParabolicPoint from q) i * ga q)
      (B ×ˢ Ioo 0 τ) volume := by
    simpa [ga] using locallyIntegrableOn_mul_continuousCompact hWloc hgaCont
      hgaCompact hgaSubset
  have hDA : IntegrableOn
      (fun q : Vec3 × ℝ => Dtw (show ParabolicPoint from q) i * gb q)
      (B ×ˢ Ioo 0 τ) volume := by
    simpa [gb] using locallyIntegrableOn_mul_continuousCompact hDloc hgbCont
      hgbCompact hgbSubset
  have hWAprod := setIntegral_prod
    (fun q : Vec3 × ℝ => w (show ParabolicPoint from q) i * ga q) hWA
  have hDAprod := setIntegral_prod
    (fun q : Vec3 × ℝ => Dtw (show ParabolicPoint from q) i * gb q) hDA
  have hWArest : Integrable
      (fun q : Vec3 × ℝ => w (show ParabolicPoint from q) i * ga q)
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))) := by
    change Integrable _ ((volume.prod volume).restrict (B ×ˢ Ioo 0 τ)) at hWA
    rw [← Measure.prod_restrict] at hWA
    exact hWA
  have hDArest : Integrable
      (fun q : Vec3 × ℝ => Dtw (show ParabolicPoint from q) i * gb q)
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))) := by
    change Integrable _ ((volume.prod volume).restrict (B ×ˢ Ioo 0 τ)) at hDA
    rw [← Measure.prod_restrict] at hDA
    exact hDA
  have hWAinner : IntegrableOn
      (fun x : Vec3 => ∫ s in Ioo 0 τ,
        w (show ParabolicPoint from (x, s)) i * ga (x, s)) B volume :=
    hWArest.integral_prod_left
  have hDAinner : IntegrableOn
      (fun x : Vec3 => ∫ s in Ioo 0 τ,
        Dtw (show ParabolicPoint from (x, s)) i * gb (x, s)) B volume :=
    hDArest.integral_prod_left
  have hWAfactor (x : Vec3) :
      (∫ s in Ioo 0 τ, w (show ParabolicPoint from (x, s)) i *
        (η x * deriv ψ.toFun s)) = η x *
          (∫ s in Ioo 0 τ,
            w (show ParabolicPoint from (x, s)) i * deriv ψ.toFun s) := by
    calc
      _ = ∫ s in Ioo 0 τ, η x *
          (w (show ParabolicPoint from (x, s)) i * deriv ψ.toFun s) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        ring
      _ = _ := integral_const_mul _ _
  have hDAfactor (x : Vec3) :
      (∫ s in Ioo 0 τ, Dtw (show ParabolicPoint from (x, s)) i *
        (η x * ψ.toFun s)) = η x *
          (∫ s in Ioo 0 τ,
            Dtw (show ParabolicPoint from (x, s)) i * ψ.toFun s) := by
    calc
      _ = ∫ s in Ioo 0 τ, η x *
          (Dtw (show ParabolicPoint from (x, s)) i * ψ.toFun s) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        ring
      _ = _ := integral_const_mul _ _
  have htimeProduct :
      (∫ q in B ×ˢ Ioo 0 τ,
        w (show ParabolicPoint from q) i * ga q) =
      -(∫ q in B ×ˢ Ioo 0 τ,
        Dtw (show ParabolicPoint from q) i * gb q) := by
    have hconvert := htime
    rw [setIntegral_parabolic_to_product, setIntegral_parabolic_to_product] at hconvert
    simpa [ga, gb, φ, parabolicHomeomorph_symm_apply] using hconvert
  rw [Measure.volume_eq_prod Vec3 ℝ] at htimeProduct
  calc
    ∫ x in B, η x * sectionTimePairing w Dtw i ψ.toFun x =
        ∫ x in B,
          ((∫ s in Ioo 0 τ,
              w (show ParabolicPoint from (x, s)) i * ga (x, s)) +
            ∫ s in Ioo 0 τ,
              Dtw (show ParabolicPoint from (x, s)) i * gb (x, s)) := by
      apply setIntegral_congr_fun hB.measurableSet
      intro x hx
      dsimp [sectionTimePairing]
      rw [hWAfactor, hDAfactor]
      simp only [mul_add]
    _ = (∫ x in B, ∫ s in Ioo 0 τ,
          w (show ParabolicPoint from (x, s)) i * ga (x, s)) +
        ∫ x in B, ∫ s in Ioo 0 τ,
          Dtw (show ParabolicPoint from (x, s)) i * gb (x, s) :=
      integral_add hWAinner hDAinner
    _ = 0 := by
      rw [← hWAprod, ← hDAprod, htimeProduct]
      ring

private theorem ae_sectionTimePairing_eq_zero
    {B : Set Vec3} {τ : ℝ} (hB : IsOpen B) (hτ : 0 < τ)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs B (Ioo 0 τ) w Dw D2w Dtw)
    {n : ℕ} (ψ : IntervalTestWithSupport τ n) (i : Fin 3) :
    ∀ᵐ x ∂(volume.restrict B), sectionTimePairing (τ := τ) w Dtw i ψ.toFun x = 0 := by
  have hloc := sectionTimePairing_locallyIntegrableOn hB hτ hderiv ψ i
  have hzero := hB.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro η hη hηc hηB
    have hset := integral_eta_mul_sectionTimePairing_eq_zero hB hτ hderiv
      hη hηc hηB ψ i
    have hfull :
        (∫ x, η x * sectionTimePairing (τ := τ) w Dtw i ψ.toFun x) =
          ∫ x in B, η x * sectionTimePairing (τ := τ) w Dtw i ψ.toFun x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hηzero : η x = 0 := by
        by_contra hne
        exact hx (hηB (subset_tsupport η (Function.mem_support.mpr hne)))
      simp [hηzero]
    simpa only [smul_eq_mul, hfull] using hset)
  have hzeroAE : ∀ᵐ x ∂volume,
      x ∈ B → sectionTimePairing (τ := τ) w Dtw i ψ.toFun x = 0 := by
    rw [ae_iff]
    exact hzero
  filter_upwards [ae_restrict_of_ae hzeroAE, ae_restrict_mem hB.measurableSet]
    with x hx hxB
  exact hx hxB

/-- The time clause of the space-time weak derivative identity holds on almost
every spatial section, as required in `lem:ftc-small-time`. -/
theorem hasSectionwiseTimeWeakDeriv_of_hasSpaceTimeWeakDerivs
    {B : Set Vec3} {τ : ℝ} (hB : IsOpen B) (hτ : 0 < τ)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hwcont : ContinuousOn w (spaceTimeSet B (Ico 0 τ)))
    (hDtwL2 : MemLp Dtw 2
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (hderiv : HasSpaceTimeWeakDerivs B (Ioo 0 τ) w Dw D2w Dtw) :
    ∀ᵐ x ∂(volume.restrict B), ∀ i : Fin 3,
      HasWeakDerivOn (Ioo 0 τ)
        (fun s => w ((show ParabolicPoint from (x, s))) i)
        (fun s => Dtw ((show ParabolicPoint from (x, s))) i) := by
  classical
  choose S hScount hSdense using
    (fun n : ℕ => exists_countable_dense_intervalTests τ n)
  have hDtwSq : Integrable (fun z : ParabolicPoint => ‖Dtw z‖ ^ 2)
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))) :=
    hDtwL2.integrable_norm_pow (p := 2) (by norm_num)
  have hDtwSectionMeas := hDtwL2.aestronglyMeasurable.prodMk_left
  have hDtwSectionSq := hDtwSq.prod_right_ae
  have hDtwSectionLp : ∀ᵐ x ∂(volume.restrict B),
      MemLp (fun s => Dtw ((show ParabolicPoint from (x, s)))) 2
        (volume.restrict (Ioo 0 τ)) := by
    filter_upwards [hDtwSectionMeas, hDtwSectionSq] with x hxmeas hxsq
    exact (memLp_two_iff_integrable_sq_norm hxmeas).2 hxsq
  have htests : ∀ᵐ x ∂(volume.restrict B), ∀ n,
      ∀ ψ : {ψ : IntervalTestWithSupport τ n // ψ ∈ S n},
        ∀ i : Fin 3,
          sectionTimePairing (τ := τ) w Dtw i ψ.1.toFun x = 0 := by
    rw [ae_all_iff]
    intro n
    let : Countable {ψ : IntervalTestWithSupport τ n // ψ ∈ S n} := hScount n
    rw [ae_all_iff]
    intro ψ
    rw [ae_all_iff]
    intro i
    exact ae_sectionTimePairing_eq_zero hB hτ hderiv ψ.1 i
  filter_upwards [htests, hDtwSectionLp, ae_restrict_mem hB.measurableSet]
    with x hxTests hxDtw hxB
  intro i
  have hmap : Continuous (fun s : ℝ => parabolicHomeomorph.symm (x, s)) :=
    parabolicHomeomorph.symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hwcontx : ContinuousOn
      (fun s => w (parabolicHomeomorph.symm (x, s))) (Ico 0 τ) := by
    apply hwcont.comp hmap.continuousOn
    intro s hs
    change x ∈ B ∧ s ∈ Ico 0 τ
    exact ⟨hxB, hs⟩
  have hwconti : ContinuousOn
      (fun s => w (parabolicHomeomorph.symm (x, s)) i) (Ico 0 τ) :=
    (continuous_apply i).comp_continuousOn hwcontx
  have hDtwLpi : MemLp
      (fun s => Dtw ((show ParabolicPoint from (x, s))) i) 2
      (volume.restrict (Ioo 0 τ)) := by
    exact (hxDtw.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))
  have hDtwLpiSymm : MemLp
      (fun s => Dtw (parabolicHomeomorph.symm (x, s)) i) 2
      (volume.restrict (Ioo 0 τ)) := by
    simpa only [parabolicHomeomorph_symm_apply] using hDtwLpi
  have hweak : HasWeakDerivOn (Ioo 0 τ)
      (fun s => w (parabolicHomeomorph.symm (x, s)) i)
      (fun s => Dtw (parabolicHomeomorph.symm (x, s)) i) := by
    intro ψ hψ
    obtain ⟨n, hn⟩ := intervalTest_support_compact_exhaustion hψ
    let ψn : IntervalTestWithSupport τ n :=
      ⟨ψ, hψ.1, hψ.2.1, hψ.2.2, hn⟩
    have hzeroN : ∀ θ ∈ S n,
        sectionTimePairing (τ := τ) w Dtw i θ.toFun x = 0 := by
      intro θ hθ
      exact hxTests n ⟨θ, hθ⟩ i
    have hpair := sectionTimePairing_eq_zero_of_dense (w := w) (Dtw := Dtw)
      hτ x i hwconti
      hDtwLpiSymm (S n) (hSdense n) hzeroN ψn
    have hpair' :
        (∫ s in Ioo 0 τ,
          w ((show ParabolicPoint from (x, s))) i * deriv ψ s) +
        ∫ s in Ioo 0 τ,
          Dtw ((show ParabolicPoint from (x, s))) i * ψ s = 0 := by
      simpa only [sectionTimePairing, ψn, parabolicHomeomorph_symm_apply] using hpair
    change (∫ s in Ioo 0 τ,
        w ((show ParabolicPoint from (x, s))) i * deriv ψ s) =
      -(∫ s in Ioo 0 τ, Dtw ((show ParabolicPoint from (x, s))) i * ψ s)
    linarith only [hpair']
  simpa only [parabolicHomeomorph_symm_apply] using hweak

end ESS
