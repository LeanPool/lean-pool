/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedPairMaxLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineStrictSuperlevelCover

/-! # Original mixed agreement on a genuine bounded PSH superlevel

The complete mathematical statement and entire proof preceded this source.
ROOT14 remains strictly excluded from the fixed C91 batch.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.BoundedBasicPlurifineLocality

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylor SmoothMax LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalBedfordTaylorDecreasing
  LocalBedfordTaylorCanonicalTraceMeasure LocalBedfordTaylorSmoothTraceMeasure
  LocalBedfordTaylorCalculus

variable {n : ℕ}

private theorem perturbation_psh {O : Opens (ComplexModel n)}
    {g : ComplexModel n → ℝ}
    (hg : PlurisubharmonicOn (fun z ↦ (g z : EReal)) O)
    (hgn : ∀ z ∈ O, -1 ≤ g z ∧ g z ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    IsLocallyBoundedPshOn O (fun z ↦ ε * (g z + 1)) := by
  have hgb : IsLocallyBoundedPshOn O g :=
    isLocallyBoundedPshOn_of_abs_le hg (C := 1) fun z hz ↦ abs_le.mpr (hgn z hz)
  have hgs := isLocallyBoundedPshOn_add_const hgb 1
  refine isLocallyBoundedPshOn_of_abs_le
    (plurisubharmonicOn_coe_const_mul hgs.1 hε) (C := 2 * ε) ?_
  intro z hz
  have h0 : 0 ≤ g z + 1 := by linarith [(hgn z hz).1]
  rw [abs_mul, abs_of_nonneg hε.le, abs_of_nonneg h0]
  nlinarith [(hgn z hz).2]

private theorem canonical_vague_of_antitone {O : Opens (ComplexModel n)}
    {v : ℕ → Fin n → ComplexModel n → ℝ} {u : Fin n → ComplexModel n → ℝ}
    (hv : ∀ k i, IsLocallyBoundedPshOn O (v k i))
    (hu : IsLocallyBoundedMixedPshOn O u)
    (hanti : ∀ i, ∀ z ∈ O, Antitone fun k ↦ v k i z)
    (hlim : ∀ i, ∀ z ∈ O, Tendsto (fun k ↦ v k i z) atTop (𝓝 (u i z)))
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ (O : Set (ComplexModel n))) :
    Tendsto (fun k ↦ ∫ z, χ z ∂MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure
      O (v k) (hv k)) atTop
      (𝓝 (∫ z, χ z ∂MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O u hu)) := by
  let hP := fun k ↦ (isPositive_btProduct n 0 (v k)
    (oneCurrentOf (U := O) (Nat.zero_add n)) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (hv k)).1
  let hP₀ := (isPositive_btProduct n 0 u (oneCurrentOf (U := O) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1
  have hw := weakTendsto_btProduct_of_antitone n 0
    (oneCurrentOf (U := O) (Nat.zero_add n)) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) v u hv hu hanti hlim
  have hl := tendsto_integral_traceMeasure_of_weakTendsto hP hP₀ hw hχ hχc hχO
  change Tendsto (fun k ↦ ∫ z, χ z ∂recursiveMixedTraceMeasure O (v k) (hv k))
    atTop (𝓝 (∫ z, χ z ∂recursiveMixedTraceMeasure O u hu)) at hl
  have es (k : ℕ) := canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure (hv k)
  have et := canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hu
  simpa only [es, et] using hl

private theorem perturbed_stage_restrict_eq {O : Opens (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ} {g : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedMixedPshOn O a) (hb : IsLocallyBoundedMixedPshOn O b)
    (hg : PlurisubharmonicOn (fun z ↦ (g z : EReal)) O)
    (hgn : ∀ z ∈ O, -1 ≤ g z ∧ g z ≤ 1)
    (heq : ∀ i, EqOn (a i) (b i) {z | z ∈ O ∧ 0 < g z})
    {ε : ℝ} (hε : 0 < ε) :
    let A := fun i z ↦ a i z + ε * (g z + 1)
    let B := fun i z ↦ b i z + ε * (g z + 1)
    let hA := fun i ↦ isLocallyBoundedPshOn_add (ha i) (perturbation_psh hg hgn hε)
    let hB := fun i ↦ isLocallyBoundedPshOn_add (hb i) (perturbation_psh hg hgn hε)
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O A hA).restrict
      {z | z ∈ O ∧ 0 < g z} =
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O B hB).restrict
      {z | z ∈ O ∧ 0 < g z} := by
  classical
  dsimp only
  let A := fun i z ↦ a i z + ε * (g z + 1)
  let B := fun i z ↦ b i z + ε * (g z + 1)
  let C := fun i z ↦ max (a i z) (b i z) + ε
  let W := fun i z ↦ max (A i z) (C i z)
  let Z := fun i z ↦ max (B i z) (C i z)
  let hA : IsLocallyBoundedMixedPshOn O A := fun i ↦
    isLocallyBoundedPshOn_add (ha i) (perturbation_psh hg hgn hε)
  let hB : IsLocallyBoundedMixedPshOn O B := fun i ↦
    isLocallyBoundedPshOn_add (hb i) (perturbation_psh hg hgn hε)
  let hC : IsLocallyBoundedMixedPshOn O C := fun i ↦
    isLocallyBoundedPshOn_add_const (LocalBedfordTaylorCollar.isLocallyBoundedPshOn_max
      (ha i) (hb i)) ε
  let hW : IsLocallyBoundedMixedPshOn O W := fun i ↦
    LocalBedfordTaylorCollar.isLocallyBoundedPshOn_max (hA i) (hC i)
  have hWZ : ∀ i, EqOn (W i) (Z i) O := by
    intro i z hz
    by_cases hgz : 0 < g z
    · simp only [W, Z, A, B, heq i ⟨hz, hgz⟩]
    · have hgle : g z ≤ 0 := le_of_not_gt hgz
      have hac : A i z ≤ C i z := by
        dsimp [A, C]
        nlinarith [le_max_left (a i z) (b i z)]
      have hbc : B i z ≤ C i z := by
        dsimp [B, C]
        nlinarith [le_max_right (a i z) (b i z)]
      exact (max_eq_right hac).trans (max_eq_right hbc).symm
  let μA := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O A hA
  let μB := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O B hB
  let ν := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O W hW
  have hν := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O W hW)
  have hνZ : IsBTLimit O Z ν := hν.congr hWZ
  have eA := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O A hA))
    hν hC (fun _ _ _ ↦ rfl)
  have eB := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O B hB))
    hνZ hC (fun _ _ _ ↦ rfl)
  let G := {z | z ∈ O ∧ 0 < g z}
  have hGA : G ⊆ {z | z ∈ O ∧ ∀ i, C i z < A i z} := by
    intro z hz
    refine ⟨hz.1, fun i ↦ ?_⟩
    have hba := (heq i hz).symm
    dsimp [C, A]
    rw [hba, max_self]
    nlinarith [mul_pos hε hz.2]
  have hGB : G ⊆ {z | z ∈ O ∧ ∀ i, C i z < B i z} := by
    intro z hz
    refine ⟨hz.1, fun i ↦ ?_⟩
    have hab := heq i hz
    dsimp [C, B]
    rw [hab, max_self]
    nlinarith [mul_pos hε hz.2]
  have ea : ν.restrict G = μA.restrict G := by
    rw [← Measure.restrict_restrict_of_subset hGA, eA,
      Measure.restrict_restrict_of_subset hGA]
  have eb : ν.restrict G = μB.restrict G := by
    rw [← Measure.restrict_restrict_of_subset hGB, eB,
      Measure.restrict_restrict_of_subset hGB]
  exact ea.symm.trans eb

private theorem perturbation_compact_bound {O : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {g : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn O u)
    (hgn : ∀ z ∈ O, -1 ≤ g z ∧ g z ≤ 1)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ M : ℝ, ∀ k i, ∀ z ∈ K,
      |u i z + maxScale k * (g z + 1)| ≤ M := by
  classical
  choose C hC using fun i ↦ BedfordTaylor.IsLocallyBoundedPshOn.exists_abs_le
    (hu i) hK hKO
  refine ⟨(∑ i, |C i|) + 2, fun k i z hz ↦ ?_⟩
  have hs : maxScale k ≤ 1 := by
    simpa [maxScale] using maxScale_antitone (Nat.zero_le k)
  have h0 : 0 ≤ g z + 1 := by linarith [(hgn z (hKO hz)).1]
  have h2 : g z + 1 ≤ 2 := by linarith [(hgn z (hKO hz)).2]
  have hc : C i ≤ ∑ j, |C j| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j ↦ |C j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i))
  have hp : |maxScale k * (g z + 1)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (maxScale_pos k).le, abs_of_nonneg h0]
    nlinarith [(maxScale_pos k).le]
  exact (abs_add_le _ _).trans (by linarith [hC i z hz])

/-- Agreement on a genuine normalized PSH superlevel for the original mixed measures. -/
theorem canonicalMixed_restrict_eq_on_normalized_psh_superlevel
    {Ω O : Opens (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ} {g : ComplexModel n → ℝ}
    (hOΩ : O ≤ Ω)
    (ha : IsLocallyBoundedMixedPshOn Ω a) (hb : IsLocallyBoundedMixedPshOn Ω b)
    (hg : PlurisubharmonicOn (fun z ↦ (g z : EReal)) O)
    (hgn : ∀ z ∈ O, -1 ≤ g z ∧ g z ≤ 1)
    (heq : ∀ i, EqOn (a i) (b i) {z | z ∈ O ∧ 0 < g z}) :
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω a ha).restrict
      {z | z ∈ O ∧ 0 < g z} =
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω b hb).restrict
      {z | z ∈ O ∧ 0 < g z} := by
  classical
  let haO : IsLocallyBoundedMixedPshOn O a := fun i ↦
    isLocallyBoundedPshOn_mono (ha i) hOΩ
  let hbO : IsLocallyBoundedMixedPshOn O b := fun i ↦
    isLocallyBoundedPshOn_mono (hb i) hOΩ
  let A := fun k i z ↦ a i z + maxScale k * (g z + 1)
  let B := fun k i z ↦ b i z + maxScale k * (g z + 1)
  let hA : ∀ k, IsLocallyBoundedMixedPshOn O (A k) := fun k i ↦
    isLocallyBoundedPshOn_add (haO i) (perturbation_psh hg hgn (maxScale_pos k))
  let hB : ∀ k, IsLocallyBoundedMixedPshOn O (B k) := fun k i ↦
    isLocallyBoundedPshOn_add (hbO i) (perturbation_psh hg hgn (maxScale_pos k))
  let μA := fun k ↦ MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O (A k) (hA k)
  let μB := fun k ↦ MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O (B k) (hB k)
  let μa := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O a haO
  let μb := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure O b hbO
  have hBTa : IsBTLimit O a μa := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O a haO)
  have hBTb : IsBTLimit O b μb := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O b hbO)
  have hBTA (k : ℕ) : IsBTLimit O (A k) (μA k) :=
    BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O (A k) (hA k))
  have hBTB (k : ℕ) : IsBTLimit O (B k) (μB k) :=
    BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec O (B k) (hB k))
  have hantiA : ∀ i, ∀ z ∈ O, Antitone fun k ↦ A k i z := by
    intro i z hz j k hjk
    change a i z + maxScale k * (g z + 1) ≤ a i z + maxScale j * (g z + 1)
    have hgg : 0 ≤ g z + 1 := by linarith [(hgn z hz).1]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (maxScale_antitone hjk) hgg)
  have hantiB : ∀ i, ∀ z ∈ O, Antitone fun k ↦ B k i z := by
    intro i z hz j k hjk
    change b i z + maxScale k * (g z + 1) ≤ b i z + maxScale j * (g z + 1)
    have hgg : 0 ≤ g z + 1 := by linarith [(hgn z hz).1]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (maxScale_antitone hjk) hgg)
  have hlimA : ∀ i, ∀ z ∈ O, Tendsto (fun k ↦ A k i z) atTop (𝓝 (a i z)) := by
    intro i z _
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (tendsto_maxScale.mul_const (g z + 1))
  have hlimB : ∀ i, ∀ z ∈ O, Tendsto (fun k ↦ B k i z) atTop (𝓝 (b i z)) := by
    intro i z _
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (tendsto_maxScale.mul_const (g z + 1))
  have hconvA : ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (O : Set (ComplexModel n)) →
      Tendsto (fun k ↦ ∫ z, χ z ∂μA k) atTop (𝓝 (∫ z, χ z ∂μa)) :=
    fun _ hc hk ht ↦ canonical_vague_of_antitone hA haO hantiA hlimA hc hk ht
  have hconvB : ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (O : Set (ComplexModel n)) →
      Tendsto (fun k ↦ ∫ z, χ z ∂μB k) atTop (𝓝 (∫ z, χ z ∂μb)) :=
    fun _ hc hk ht ↦ canonical_vague_of_antitone hB hbO hantiB hlimB hc hk ht
  let G := {z | z ∈ O ∧ 0 < g z}
  have hGO : G ⊆ O := fun _ hz ↦ hz.1
  have hGm : MeasurableSet G := by
    simpa only [G, ← EReal.coe_zero, EReal.coe_lt_coe_iff] using
      FirstPass.MongeAmpere.measurableSet_psh_superlevel hg (0 : ℝ)
  let f := fun z ↦ max (g z) 0
  have hgb : IsLocallyBoundedPshOn O g :=
    isLocallyBoundedPshOn_of_abs_le hg (C := 1) fun z hz ↦ abs_le.mpr (hgn z hz)
  have hzero : IsLocallyBoundedPshOn O (fun _ ↦ (0 : ℝ)) :=
    isLocallyBoundedPshOn_of_abs_le
      (fun z _ ↦ plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)
      (C := 0) (fun _ _ ↦ by simp)
  have hf : IsLocallyBoundedPshOn O f :=
    LocalBedfordTaylorCollar.isLocallyBoundedPshOn_max hgb hzero
  have hf0 (z : ComplexModel n) : 0 ≤ f z := le_max_right _ _
  let d := fun z ↦ ENNReal.ofReal ((O : Set (ComplexModel n)).indicator f z)
  have hdmeas : Measurable d :=
    (BedfordTaylor.measurable_indicator_of_plurisubharmonicOn hf.1).ennreal_ofReal
  have hdf (z : ComplexModel n) (hz : z ∈ O) : d z = ENNReal.ofReal (f z) := by
    simp only [d, Set.indicator_of_mem hz]
  have hdle (z : ComplexModel n) : d z ≤ 1 := by
    by_cases hz : z ∈ O
    · rw [hdf z hz]
      have hfl : f z ≤ 1 := max_le (hgn z hz).2 zero_le_one
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hfl
    · simp only [d, Set.indicator_of_notMem hz, ENNReal.ofReal_zero, zero_le]
  have hdtop (z : ComplexModel n) : d z < ⊤ := ENNReal.ofReal_lt_top
  have hdnotG (z : ComplexModel n) (hz : z ∉ G) : d z = 0 := by
    by_cases hzO : z ∈ O
    · have hgle : g z ≤ 0 := le_of_not_gt (fun h ↦ hz ⟨hzO, h⟩)
      simp only [hdf z hzO, f, max_eq_right hgle, ENNReal.ofReal_zero]
    · simp only [d, Set.indicator_of_notMem hzO, ENNReal.ofReal_zero]
  have hind : G.indicator d = d := by
    funext z
    by_cases hz : z ∈ G
    · exact Set.indicator_of_mem hz _
    · simp only [Set.indicator_of_notMem hz, hdnotG z hz]
  have hstage (k : ℕ) : (μA k).withDensity d = (μB k).withDensity d := by
    rw [← hind, withDensity_indicator hGm, withDensity_indicator hGm]
    congr 1
    exact perturbed_stage_restrict_eq haO hbO hg hgn heq (maxScale_pos k)
  have hint (ν : Measure (ComplexModel n)) (χ : ComplexModel n → ℝ)
      (hχO : tsupport χ ⊆ (O : Set (ComplexModel n))) :
      ∫ z, χ z ∂ν.withDensity d = ∫ z, χ z * f z ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdmeas.aemeasurable
      (Eventually.of_forall hdtop)]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    change (d z).toReal • χ z = χ z * f z
    by_cases hz : z ∈ O
    · rw [hdf z hz, ENNReal.toReal_ofReal (hf0 z), smul_eq_mul, mul_comm]
    · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz (hχO h))
      simp only [hχz, smul_zero, zero_mul]
  have hfin (ν : Measure (ComplexModel n))
      (hνf : ∀ K, IsCompact K → K ⊆ O → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ O → ν.withDensity d K < ⊤ := by
    have hle : ν.withDensity d ≤ ν := by
      simpa only [← Pi.one_def, withDensity_one] using
        (withDensity_mono (μ := ν) (Eventually.of_forall hdle))
    exact fun K hK hKO ↦ (hle K).trans_lt (hνf K hK hKO)
  have hweighted : (μa.withDensity d).restrict (O : Set (ComplexModel n)) =
      (μb.withDensity d).restrict (O : Set (ComplexModel n)) :=
    restrict_eq_of_testFunction_integral_eq (hfin μa hBTa.2.1) (hfin μb hBTb.2.1) fun φ ↦ by
      rw [hint μa φ φ.tsupport_subset, hint μb φ φ.tsupport_subset]
      have he (k : ℕ) : (∫ z, φ z * f z ∂μA k) = ∫ z, φ z * f z ∂μB k := by
        rw [← hint (μA k) φ φ.tsupport_subset,
          ← hint (μB k) φ φ.tsupport_subset, hstage k]
      have hla := tendsto_integral_mul_of_isBTLimit hA hBTA haO hBTa
        (fun _ hK hKO ↦ perturbation_compact_bound haO hgn hK hKO)
        hconvA hf φ.continuous φ.hasCompactSupport φ.tsupport_subset
      have hlb := tendsto_integral_mul_of_isBTLimit hB hBTB hbO hBTb
        (fun _ hK hKO ↦ perturbation_compact_bound hbO hgn hK hKO)
        hconvB hf φ.continuous φ.hasCompactSupport φ.tsupport_subset
      exact tendsto_nhds_unique (by simpa only [he] using hla) hlb
  have hweightedG : (μa.withDensity d).restrict G = (μb.withDensity d).restrict G := by
    rw [← Measure.restrict_restrict_of_subset hGO, hweighted,
      Measure.restrict_restrict_of_subset hGO]
  have hinv (ν : Measure (ComplexModel n)) :
      ((ν.withDensity d).restrict G).withDensity (fun z ↦ (d z)⁻¹) = ν.restrict G := by
    rw [restrict_withDensity hGm]
    apply withDensity_inv_same₀ hdmeas.aemeasurable
    · filter_upwards [ae_restrict_mem hGm] with z hz
      rw [hdf z hz.1]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (lt_of_lt_of_le hz.2 (le_max_left _ _)))
    · exact Eventually.of_forall fun z ↦ ne_of_lt (hdtop z)
  have eG : μa.restrict G = μb.restrict G := by
    rw [← hinv μa, ← hinv μb, hweightedG]
  have eaO : (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω a ha).restrict
      (O : Set (ComplexModel n)) = μa := by
    rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure,
      recursiveMixedTraceMeasure_restrict ha hOΩ]
    exact (canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure haO).symm
  have ebO : (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω b hb).restrict
      (O : Set (ComplexModel n)) = μb := by
    rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure,
      recursiveMixedTraceMeasure_restrict hb hOΩ]
    exact (canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hbO).symm
  calc
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω a ha).restrict G =
        μa.restrict G := by
      rw [← eaO, Measure.restrict_restrict_of_subset hGO]
    _ = μb.restrict G := eG
    _ = (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω b hb).restrict G := by
      rw [← ebO, Measure.restrict_restrict_of_subset hGO]

end SGPT.Foundations.Analysis.Pending.BoundedBasicPlurifineLocality
