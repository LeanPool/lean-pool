/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Radial extension of a convex function

A nonnegative real convex function `g` on an open convex set `K ∋ 0` with `g 0 = 0` extends to `ψ :
E → EReal` that is
nonnegative, vanishes at `0`, has convex real epigraph and Borel `toENNReal`, equals `g` on `K`, is
`⊤` off `closure K`, and
equals at every point its radial limit `lim_{t → 1⁻} ψ (t • x)`
(`exists_radial_extension_of_convexOn`). No boundedness,
lower semicontinuity, closure or envelope hypothesis is used; boundary values are radial limits (no
claim either way about
equality with a lower-semicontinuous closure).

This is the extension step in the proof of Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Lemma 17.
Construction (private): `ψ x = ⨆ n, radialCut (radialScale n) x` with `radialScale n = 1 − 1/(n +
2)`, the value at
`radialScale n • x` when that point lies in `K` and `⊤` otherwise; a countable supremum, hence
Borel, and equal to the source's
monotone radial limit.
-/

@[expose] public section

noncomputable section
open Set Filter
namespace FunctionalInequalities.Analysis

section NormedSpace

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]


private lemma smul_mem_of_mem_closure
    {K : Set E} (hK : IsOpen K) (hconv : Convex ℝ K) (h0K : (0 : E) ∈ K)
    {x : E} (hx : x ∈ closure K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t • x ∈ K := by
  have hz : (0 : E) ∈ interior K := by rwa [hK.interior_eq]
  have h := hconv.combo_interior_closure_mem_interior hz hx
    (show 0 < 1 - t by linarith) ht0 (by ring)
  simpa only [smul_zero, zero_add, hK.interior_eq] using h

private lemma radial_mono
    {K : Set E} (h0K : (0 : E) ∈ K) {g : E → ℝ} (hg : ConvexOn ℝ K g)
    (hnn : ∀ y ∈ K, 0 ≤ g y) (hg0 : g 0 = 0) {x : E} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) (htK : t • x ∈ K) :
    g (s • x) ≤ g (t • x) := by
  have ha : 0 ≤ s / t := div_nonneg hs ht.le
  have ha1 : s / t ≤ 1 := (div_le_iff₀ ht).mpr (by simpa using hst)
  have h := hg.2 htK h0K ha (sub_nonneg.mpr ha1) (show s / t + (1 - s / t) = 1 by ring)
  have he : (s / t) • (t • x) + (1 - s / t) • (0 : E) = s • x := by
    rw [smul_zero, add_zero, smul_smul, div_mul_cancel₀ _ ht.ne']
  rw [he, hg0, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at h
  exact h.trans (mul_le_of_le_one_left (hnn _ htK) ha1)

private def radialCut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (g : E → ℝ) (a : ℝ) (x : E) : EReal := by
  classical
  exact if a • x ∈ K then (g (a • x) : EReal) else ⊤

private lemma radialCut_convex_epigraph {K : Set E} {g : E → ℝ} (hg : ConvexOn ℝ K g) (a : ℝ) :
    Convex ℝ {p : E × ℝ | radialCut K g a p.1 ≤ (p.2 : EReal)} := by
  classical
  let L : E × ℝ →ₗ[ℝ] E × ℝ :=
    (a • LinearMap.fst ℝ E ℝ).prod (LinearMap.snd ℝ E ℝ)
  have he : {p : E × ℝ | radialCut K g a p.1 ≤ (p.2 : EReal)} =
      L ⁻¹' {p : E × ℝ | p.1 ∈ K ∧ g p.1 ≤ p.2} := by
    ext p
    by_cases hp : a • p.1 ∈ K
    · simp [radialCut, hp, L, EReal.coe_le_coe_iff]
    · simp [radialCut, hp, L]
  rw [he]
  exact hg.convex_epigraph.linear_preimage L

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E]

private lemma measurable_radialCut {K : Set E} (hK : IsOpen K)
    {g : E → ℝ} (hcont : ContinuousOn g K) (a : ℝ) : Measurable (radialCut K g a) := by
  classical
  let S : Set E := {x | a • x ∈ K}
  have hS : IsOpen S := hK.preimage (continuous_const.smul continuous_id)
  have hin : ContinuousOn (fun x => (g (a • x) : EReal)) S :=
    continuous_coe_real_ereal.comp_continuousOn
      (hcont.comp (continuous_const.smul continuous_id).continuousOn (by intro x hx; exact hx))
  have hout : ContinuousOn (fun _ : E => (⊤ : EReal)) Sᶜ := continuous_const.continuousOn
  have hm := hin.measurable_piecewise hout hS.measurableSet
  have he : radialCut K g a = S.piecewise (fun x => (g (a • x) : EReal))
      (fun _ => ⊤) := by
    funext x
    by_cases hx : a • x ∈ K
    · simp [radialCut, S, hx]
    · simp [radialCut, S, hx]
  rw [he]
  exact hm

private lemma measurable_radialCut_toENNReal {K : Set E} (hK : IsOpen K)
    {g : E → ℝ} (hcont : ContinuousOn g K) (a : ℝ) :
    Measurable (fun x => (radialCut K g a x).toENNReal) :=
  (measurable_radialCut hK hcont a).ereal_toENNReal

end MeasurableSpace


private def radialScale (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

private theorem radialScale_pos (n : ℕ) : 0 < radialScale n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 < (n : ℝ) + 2 := by linarith
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
  dsimp [radialScale]
  simp only [one_div_one] at h
  linarith

private theorem radialScale_lt_one (n : ℕ) : radialScale n < 1 := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have h := one_div_pos.mpr hden
  dsimp [radialScale]
  linarith

private theorem radialScale_monotone : Monotone radialScale := by
  intro m n hmn
  have hm : 0 < (m : ℝ) + 2 := by positivity
  have hle : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
  have h := one_div_le_one_div_of_le hm hle
  dsimp [radialScale]
  linarith

private theorem radialScale_tendsto : Tendsto radialScale atTop (nhds (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds (0 : ℝ)) := by
    have h₀ : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h₂ := (tendsto_add_atTop_iff_nat 2).2 h₀
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h₂
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (nhds (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub h


private def radialExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (g : E → ℝ) (x : E) : EReal :=
  ⨆ n, radialCut K g (radialScale n) x

private lemma radialExtension_nonneg
    {K : Set E} {g : E → ℝ} (hnn : ∀ x ∈ K, 0 ≤ g x) (x : E) :
    0 ≤ radialExtension K g x := by
  classical
  apply le_iSup_of_le 0
  by_cases hx : radialScale 0 • x ∈ K
  · simp only [radialCut, ite_eq_left hx]
    exact EReal.coe_nonneg.mpr (hnn _ hx)
  · simp [radialCut, hx]

private lemma radialExtension_convex_epigraph {K : Set E} {g : E → ℝ} (hg : ConvexOn ℝ K g) :
    Convex ℝ {p : E × ℝ | radialExtension K g p.1 ≤ (p.2 : EReal)} := by
  have he : {p : E × ℝ | radialExtension K g p.1 ≤ (p.2 : EReal)} =
      ⋂ n, {p : E × ℝ | radialCut K g (radialScale n) p.1 ≤ (p.2 : EReal)} := by
    ext p
    simp only [radialExtension, iSup_le_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  exact convex_iInter fun n => radialCut_convex_epigraph hg (radialScale n)

private lemma measurable_radialExtension
    [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsOpen K)
    {g : E → ℝ} (hcont : ContinuousOn g K) :
    Measurable (radialExtension K g) := by
  exact Measurable.iSup fun n => measurable_radialCut hK hcont (radialScale n)

private lemma radialExtension_eq_on
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0)
    {x : E} (hx : x ∈ K) : radialExtension K g x = (g x : EReal) := by
  have hmem (n : ℕ) : radialScale n • x ∈ K :=
    smul_mem_of_mem_closure hK hg.1 h0K (subset_closure hx)
      (radialScale_pos n).le (radialScale_lt_one n)
  have hmono : Monotone (fun n => (g (radialScale n • x) : EReal)) := by
    intro m n hmn
    exact EReal.coe_le_coe_iff.mpr
      (radial_mono h0K hg hnn hg0 (radialScale_pos m).le
        (radialScale_monotone hmn) (radialScale_pos n) (hmem n))
  have hcont : ContinuousAt g x := (hg.continuousOn hK).continuousAt (hK.mem_nhds hx)
  have htx : Tendsto (fun n => radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hlim : Tendsto (fun n => (g (radialScale n • x) : EReal)) atTop
      (nhds (g x : EReal)) := EReal.tendsto_coe.mpr (hcont.tendsto.comp htx)
  have he : radialExtension K g x = ⨆ n, (g (radialScale n • x) : EReal) := by
    simp only [radialExtension, radialCut, ite_eq_left (hmem _)]
  rw [he]
  exact iSup_eq_of_tendsto hmono hlim

private lemma radialExtension_eq_top_off {K : Set E} {g : E → ℝ} {x : E} (hx : x ∉ closure K) :
    radialExtension K g x = ⊤ := by
  classical
  have htx : Tendsto (fun n => radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hevent : ∀ᶠ n in atTop, radialScale n • x ∉ closure K :=
    htx.eventually (isClosed_closure.isOpen_compl.mem_nhds hx)
  obtain ⟨n, hn⟩ := hevent.exists
  have hnot : radialScale n • x ∉ K := fun h => hn (subset_closure h)
  apply top_unique
  have h : radialCut K g (radialScale n) x ≤ radialExtension K g x :=
    le_iSup (fun n => radialCut K g (radialScale n) x) n
  simpa [radialCut, hnot] using h

section FiniteDimensional

variable [FiniteDimensional ℝ E]


private lemma radialExtension_radial_limit {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) (x : E) :
    Tendsto (fun t : ℝ => radialExtension K g (t • x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (radialExtension K g x)) := by
  classical
  by_cases hx : x ∈ closure K
  · have hmem (n : ℕ) : radialScale n • x ∈ K :=
      smul_mem_of_mem_closure hK hg.1 h0K hx (radialScale_pos n).le (radialScale_lt_one n)
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have ha' : a < ⨆ n, radialCut K g (radialScale n) x := ha
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp ha'
      have hn' : a < (g (radialScale n • x) : EReal) := by
        simpa only [radialCut, ite_eq_left (hmem n)] using hn
      have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), radialScale n < t :=
        nhdsWithin_le_nhds (eventually_gt_nhds (radialScale_lt_one n))
      filter_upwards [hevent, self_mem_nhdsWithin] with t ht ht1
      have ht0 : 0 < t := (radialScale_pos n).trans ht
      have htK : t • x ∈ K := smul_mem_of_mem_closure hK hg.1 h0K hx ht0.le ht1
      rw [radialExtension_eq_on hK h0K hg hnn hg0 htK]
      exact hn'.trans_le (EReal.coe_le_coe_iff.mpr
        (radial_mono h0K hg hnn hg0 (radialScale_pos n).le ht.le ht0 htK))
    · intro a ha
      have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), (0 : ℝ) < t :=
        nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hevent, self_mem_nhdsWithin] with t ht0 ht1
      have htK : t • x ∈ K := smul_mem_of_mem_closure hK hg.1 h0K hx ht0.le ht1
      have hle : radialExtension K g (t • x) ≤ radialExtension K g x := by
        apply iSup_le
        intro n
        have hmtK : radialScale n • (t • x) ∈ K :=
          smul_mem_of_mem_closure hK hg.1 h0K (subset_closure htK)
            (radialScale_pos n).le (radialScale_lt_one n)
        have hprod : radialScale n * t ≤ radialScale n :=
          mul_le_of_le_one_right (radialScale_pos n).le ht1.le
        have hg_le := radial_mono h0K hg hnn hg0
          (mul_nonneg (radialScale_pos n).le ht0.le) hprod (radialScale_pos n) (hmem n)
        have hcut : radialCut K g (radialScale n) (t • x) ≤
            radialCut K g (radialScale n) x := by
          simp only [radialCut, ite_eq_left hmtK, ite_eq_left (hmem n)]
          rw [smul_smul]
          exact EReal.coe_le_coe_iff.mpr hg_le
        exact hcut.trans (le_iSup (fun n => radialCut K g (radialScale n) x) n)
      exact hle.trans_lt ha
  · rw [radialExtension_eq_top_off hx]
    have htx : Tendsto (fun t : ℝ => t • x) (nhdsWithin 1 (Set.Iio 1)) (nhds x) := by
      have h : Tendsto (fun t : ℝ => t • x) (nhds (1 : ℝ)) (nhds ((1 : ℝ) • x)) :=
        (continuous_id.smul continuous_const).continuousAt.tendsto
      simpa only [one_smul] using h.mono_left nhdsWithin_le_nhds
    have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), t • x ∉ closure K :=
      htx.eventually (isClosed_closure.isOpen_compl.mem_nhds hx)
    apply (tendsto_const_nhds (x := (⊤ : EReal))).congr'
    filter_upwards [hevent] with t ht
    exact (radialExtension_eq_top_off ht).symm


/--
**Radial extension of a convex function.** A nonnegative real convex function on an open convex set
`K ∋ 0` vanishing at
`0` extends to a nonnegative extended-real function with convex real epigraph and Borel `toENNReal`,
equal to it on `K`,
`⊤` off `closure K`, and equal at every point to its radial limit from below. -/
theorem exists_radial_extension_of_convexOn [MeasurableSpace E] [BorelSpace E] {K : Set E}
    (hK : IsOpen K) (h0K : (0 : E) ∈ K) {g : E → ℝ} (hg : ConvexOn ℝ K g)
    (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) :
    ∃ ψ : E → EReal,
      (∀ x, 0 ≤ ψ x) ∧
        ψ 0 = 0 ∧
          Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
            Measurable (fun x => (ψ x).toENNReal) ∧
              (∀ x ∈ K, ψ x = (g x : EReal)) ∧
                (∀ x ∉ closure K, ψ x = ⊤) ∧
                  (∀ x,
                    Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1))
                      (nhds (ψ x))) := by
  refine
    ⟨radialExtension K g, radialExtension_nonneg hnn, ?_, radialExtension_convex_epigraph hg,
      (measurable_radialExtension hK (hg.continuousOn hK)).ereal_toENNReal, ?_, ?_, ?_⟩
  · rw [radialExtension_eq_on hK h0K hg hnn hg0 h0K, hg0, EReal.coe_zero]
  · intro x hx
    exact radialExtension_eq_on hK h0K hg hnn hg0 hx
  · intro x hx
    exact radialExtension_eq_top_off hx
  · intro x
    exact radialExtension_radial_limit hK h0K hg hnn hg0 x

end FiniteDimensional

end NormedSpace

end FunctionalInequalities.Analysis
