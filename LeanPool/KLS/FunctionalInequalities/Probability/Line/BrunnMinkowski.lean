/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.MeanInequalities

/-!
# Brunn--Minkowski and Prekopa--Leindler on the line

General one-dimensional tools with no log-concavity input. Read `volume_add_le_volume_add`
(Brunn--Minkowski for compact sets), then `le_volume_combination` (its inner-regular form for
measurable sets and a convex combination), and finally `prekopaLeindler`.

The pinned Mathlib has neither inequality. The compact Brunn--Minkowski step is elementary on the
line: translating `K` by `sInf L` and `L` by `sSup K` gives two subsets of `K + L` whose
intersection is a single point. Prekopa--Leindler follows by the layer-cake formula, since the
superlevel sets of `h` contain the corresponding combination of those of `f` and `g`; the
reduction to functions of supremum one is by homogeneity, and unbounded functions are reached by
truncation.

No ledger, certificate, or Blueprint claim is made by this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Pointwise

namespace FunctionalInequalities.Probability.Line

section BrunnMinkowski

/-- **One-dimensional Brunn--Minkowski inequality** for compact sets: the Minkowski sum of two
nonempty compact subsets of the line is at least as large as the sum of their volumes. -/
theorem volume_add_le_volume_add {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  set a := sSup K with ha
  set b := sInf L with hb
  have haK : a ∈ K := hK.sSup_mem hKne
  have hbL : b ∈ L := hL.sInf_mem hLne
  set A := (fun x : ℝ ↦ x + b) '' K with hA
  set B := (fun y : ℝ ↦ a + y) '' L with hB
  have hBm : MeasurableSet B := (hL.image (by fun_prop)).measurableSet
  have hAvol : volume A = volume K := by
    have himg : A = (fun y : ℝ ↦ -b + y) ⁻¹' K := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨-b + y, hy, by ring⟩
    rw [himg]
    exact measure_preimage_add volume (-b) K
  have hBvol : volume B = volume L := by
    have himg : B = (fun y : ℝ ↦ -a + y) ⁻¹' L := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨-a + y, hy, by ring⟩
    rw [himg]
    exact measure_preimage_add volume (-a) L
  have hAsub : A ⊆ K + L := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.add_mem_add hx hbL
  have hBsub : B ⊆ K + L := by
    rintro _ ⟨y, hy, rfl⟩
    exact Set.add_mem_add haK hy
  have hint : A ∩ B ⊆ {a + b} := by
    rintro z ⟨⟨x, hx, rfl⟩, hzB⟩
    obtain ⟨y, hy, hxy⟩ := hzB
    have h1 : x ≤ a := le_csSup hK.bddAbove hx
    have h2 : b ≤ y := csInf_le hL.bddBelow hy
    simp only [Set.mem_singleton_iff]
    linarith
  calc volume K + volume L = volume A + volume B := by rw [hAvol, hBvol]
    _ = volume (A ∪ B) + volume (A ∩ B) := (measure_union_add_inter A hBm).symm
    _ ≤ volume (K + L) + volume ({a + b} : Set ℝ) :=
        add_le_add (measure_mono (Set.union_subset hAsub hBsub)) (measure_mono hint)
    _ = volume (K + L) := by simp

/-- Inner-regular form of one-dimensional Brunn--Minkowski: a convex combination of two nonempty
measurable sets carries at least the corresponding combination of their volumes. The combination
set need not be measurable; the outer measure bound is what is used. -/
theorem le_volume_combination {S T : Set ℝ} (hS : MeasurableSet S) (hSne : S.Nonempty)
    (hT : MeasurableSet T) (hTne : T.Nonempty) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal t * volume S + ENNReal.ofReal (1 - t) * volume T ≤
      volume {z : ℝ | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  set C := {z : ℝ | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} with hC
  have key : ∀ K : Set ℝ, K ⊆ S → IsCompact K → K.Nonempty →
      ∀ L : Set ℝ, L ⊆ T → IsCompact L → L.Nonempty →
      ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L ≤ volume C := by
    intro K hKS hK hKne L hLT hL hLne
    have hsub : t • K + (1 - t) • L ⊆ C := by
      rintro z ⟨u, hu, v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hv
      exact ⟨x, hKS hx, y, hLT hy, rfl⟩
    have hbm := volume_add_le_volume_add (IsCompact.smul t hK) (IsCompact.smul (1 - t) hL)
      hKne.smul_set hLne.smul_set
    have hsK : volume (t • K) = ENNReal.ofReal t * volume K := by
      rw [Measure.addHaar_smul volume t K]
      simp [Module.finrank_self, abs_of_pos ht0]
    have hsL : volume ((1 - t) • L) = ENNReal.ofReal (1 - t) * volume L := by
      rw [Measure.addHaar_smul volume (1 - t) L]
      simp [Module.finrank_self, abs_of_pos ht1']
    calc ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L
        = volume (t • K) + volume ((1 - t) • L) := by rw [hsK, hsL]
      _ ≤ volume (t • K + (1 - t) • L) := hbm
      _ ≤ volume C := measure_mono hsub
  have hsup : ∀ U : Set ℝ, MeasurableSet U → U.Nonempty →
      volume U = ⨆ K : {K : Set ℝ // K ⊆ U ∧ IsCompact K ∧ K.Nonempty}, volume (K : Set ℝ) := by
    intro U hU hUne
    refine le_antisymm ?_ (iSup_le fun K ↦ measure_mono K.2.1)
    rw [hU.measure_eq_iSup_isCompact volume]
    refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
    obtain ⟨x₀, hx₀⟩ := hUne
    exact le_iSup_of_le ⟨K ∪ {x₀}, Set.union_subset hKU (by simpa using hx₀),
      hK.union isCompact_singleton, ⟨x₀, by simp⟩⟩ (measure_mono Set.subset_union_left)
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨t₀, ht₀⟩ := hTne
  have : Nonempty {K : Set ℝ // K ⊆ S ∧ IsCompact K ∧ K.Nonempty} :=
    ⟨⟨{s₀}, by simpa using hs₀, isCompact_singleton, ⟨s₀, rfl⟩⟩⟩
  have : Nonempty {L : Set ℝ // L ⊆ T ∧ IsCompact L ∧ L.Nonempty} :=
    ⟨⟨{t₀}, by simpa using ht₀, isCompact_singleton, ⟨t₀, rfl⟩⟩⟩
  rw [hsup S hS ⟨s₀, hs₀⟩, hsup T hT ⟨t₀, ht₀⟩, ENNReal.mul_iSup, ENNReal.mul_iSup]
  exact ENNReal.iSup_add_iSup_le fun K L ↦
    key (K : Set ℝ) K.2.1 K.2.2.1 K.2.2.2 (L : Set ℝ) L.2.1 L.2.2.1 L.2.2.2

end BrunnMinkowski


section PrekopaLeindler

/-- Weighted arithmetic-geometric mean inequality for two extended nonnegative reals. -/
private theorem geom_le_arith (a b : ENNReal) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have htne : ENNReal.ofReal t ≠ 0 := by simp [ENNReal.ofReal_eq_zero]; linarith
  have ht'ne : ENNReal.ofReal (1 - t) ≠ 0 := by simp [ENNReal.ofReal_eq_zero]; linarith
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [ENNReal.mul_top htne]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.mul_top ht'ne]
  lift a to NNReal using ha with a'
  lift b to NNReal using hb with b'
  have hw : t.toNNReal + (1 - t).toNNReal = 1 := by
    rw [← NNReal.coe_inj]
    push_cast [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ ht1'.le]
    ring
  have h := NNReal.geom_mean_le_arith_mean2_weighted t.toNNReal (1 - t).toNNReal a' b' hw
  rw [Real.coe_toNNReal t ht0.le, Real.coe_toNNReal (1 - t) ht1'.le] at h
  have h2 : ((a' ^ t * b' ^ (1 - t) : NNReal) : ENNReal) ≤
      ((t.toNNReal * a' + (1 - t).toNNReal * b' : NNReal) : ENNReal) := by exact_mod_cast h
  rw [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ ht0.le, ENNReal.coe_rpow_of_nonneg _ ht1'.le] at h2
  exact h2

/-- Prekopa-Leindler on the line, after normalizing both factors to supremum one. The conclusion
is the arithmetic form, which is what the layer-cake argument produces. -/
private theorem lintegral_add_le_of_sup_one {f g h : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ s : ℝ, s < 1 → ∃ x, s < f x) (hgs : ∀ s : ℝ, s < 1 → ∃ y, s < g y)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    ENNReal.ofReal t * (∫⁻ x, ENNReal.ofReal (f x)) +
        ENNReal.ofReal (1 - t) * (∫⁻ y, ENNReal.ofReal (g y)) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have hh0 : ∀ z, 0 ≤ h z := by
    intro z
    have hz := hfgh z z
    rw [show t * z + (1 - t) * z = z by ring] at hz
    exact le_trans (mul_nonneg (Real.rpow_nonneg (hf0 z) _) (Real.rpow_nonneg (hg0 z) _)) hz
  have hmf : Measurable fun s : ℝ ↦ volume {x : ℝ | s < f x} :=
    Antitone.measurable fun s₁ s₂ hs ↦ measure_mono fun x hx ↦ lt_of_le_of_lt hs hx
  rw [lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall hf0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall hg0) hg.aemeasurable,
    lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall hh0) hh.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left (hmf.const_mul _)]
  refine lintegral_mono fun s ↦ ?_
  by_cases hs : s < 1
  · have hSne : {x : ℝ | s < f x}.Nonempty := hfs s hs
    have hTne : {y : ℝ | s < g y}.Nonempty := hgs s hs
    have hSm : MeasurableSet {x : ℝ | s < f x} := measurableSet_lt measurable_const hf
    have hTm : MeasurableSet {y : ℝ | s < g y} := measurableSet_lt measurable_const hg
    refine le_trans (le_volume_combination hSm hSne hTm hTne ht0 ht1) (measure_mono ?_)
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hfx : s < f x := hx
    have hgy : s < g y := hy
    have key : s < f x ^ t * g y ^ (1 - t) := by
      rcases le_or_gt s 0 with hs0 | hs0
      · rcases lt_or_eq_of_le hs0 with hneg | heq
        · exact hneg.trans_le
            (mul_nonneg (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hg0 y) _))
        · subst heq
          exact mul_pos (Real.rpow_pos_of_pos hfx t) (Real.rpow_pos_of_pos hgy _)
      · have h1 : s ^ t < f x ^ t := Real.rpow_lt_rpow hs0.le hfx ht0
        have h2 : s ^ (1 - t) < g y ^ (1 - t) := Real.rpow_lt_rpow hs0.le hgy ht1'
        have hss : s ^ t * s ^ (1 - t) = s := by
          rw [← Real.rpow_add hs0]
          norm_num
        calc s = s ^ t * s ^ (1 - t) := hss.symm
          _ < f x ^ t * g y ^ (1 - t) :=
              mul_lt_mul'' h1 h2 (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hs0.le _)
    change s < h (t • x + (1 - t) • y)
    simp only [smul_eq_mul]
    exact key.trans_le (hfgh x y)
  · rw [not_lt] at hs
    have h1 : {x : ℝ | s < f x} = ∅ := by
      ext x
      simpa using (hf1 x).trans hs
    have h2 : {y : ℝ | s < g y} = ∅ := by
      ext y
      simpa using (hg1 y).trans hs
    simp [h1, h2]

/-- Prekopa-Leindler on the line for functions with bounded range. -/
private theorem prekopaLeindler_bddAbove {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfb : BddAbove (Set.range f)) (hgb : BddAbove (Set.range g))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have hh0 : ∀ z, 0 ≤ h z := by
    intro z
    have hz := hfgh z z
    rw [show t * z + (1 - t) * z = z by ring] at hz
    exact le_trans (mul_nonneg (Real.rpow_nonneg (hf0 z) _) (Real.rpow_nonneg (hg0 z) _)) hz
  set A := sSup (Set.range f) with hAdef
  set B := sSup (Set.range g) with hBdef
  have hfA : ∀ x, f x ≤ A := fun x ↦ le_csSup hfb (Set.mem_range_self x)
  have hgB : ∀ y, g y ≤ B := fun y ↦ le_csSup hgb (Set.mem_range_self y)
  rcases eq_or_lt_of_le ((hf0 0).trans (hfA 0)) with hA0 | hApos
  · have hfz : ∀ x, f x = 0 := fun x ↦ le_antisymm (hA0 ▸ hfA x) (hf0 x)
    have hI : (∫⁻ x, ENNReal.ofReal (f x)) = 0 := by simp [hfz]
    rw [hI, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le
  rcases eq_or_lt_of_le ((hg0 0).trans (hgB 0)) with hB0 | hBpos
  · have hgz : ∀ y, g y = 0 := fun y ↦ le_antisymm (hB0 ▸ hgB y) (hg0 y)
    have hJ : (∫⁻ y, ENNReal.ofReal (g y)) = 0 := by simp [hgz]
    rw [hJ, ENNReal.zero_rpow_of_pos ht1', mul_zero]
    exact zero_le
  -- normalize both factors to supremum one
  set D := A ^ t * B ^ (1 - t) with hDdef
  have hDpos : 0 < D := mul_pos (Real.rpow_pos_of_pos hApos t) (Real.rpow_pos_of_pos hBpos _)
  have hcore := lintegral_add_le_of_sup_one (f := fun x ↦ A⁻¹ * f x) (g := fun y ↦ B⁻¹ * g y)
    (h := fun z ↦ D⁻¹ * h z) (hf.const_mul _) (hg.const_mul _) (hh.const_mul _)
    (fun x ↦ mul_nonneg (inv_nonneg.2 hApos.le) (hf0 x))
    (fun y ↦ mul_nonneg (inv_nonneg.2 hBpos.le) (hg0 y))
    (fun x ↦ by
      rw [inv_mul_le_iff₀ hApos]
      simpa using hfA x)
    (fun y ↦ by
      rw [inv_mul_le_iff₀ hBpos]
      simpa using hgB y)
    (fun s hsl ↦ by
      obtain ⟨r, ⟨x, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (Set.range_nonempty f)
        (show s * A < A by nlinarith)
      exact ⟨x, by rw [lt_inv_mul_iff₀ hApos]; linarith⟩)
    (fun s hsl ↦ by
      obtain ⟨r, ⟨y, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g)
        (show s * B < B by nlinarith)
      exact ⟨y, by rw [lt_inv_mul_iff₀ hBpos]; linarith⟩)
    ht0 ht1
    (fun x y ↦ by
      rw [Real.mul_rpow (inv_nonneg.2 hApos.le) (hf0 x),
        Real.mul_rpow (inv_nonneg.2 hBpos.le) (hg0 y), Real.inv_rpow hApos.le,
        Real.inv_rpow hBpos.le,
        show (A ^ t)⁻¹ * f x ^ t * ((B ^ (1 - t))⁻¹ * g y ^ (1 - t))
          = D⁻¹ * (f x ^ t * g y ^ (1 - t)) by rw [hDdef, mul_inv]; ring]
      exact mul_le_mul_of_nonneg_left (hfgh x y) (inv_nonneg.2 hDpos.le))
  -- rewrite the three normalized integrals
  have hlin : ∀ (c : ℝ) (u : ℝ → ℝ), 0 < c → Measurable u → (∀ x, 0 ≤ u x) →
      (∫⁻ x, ENNReal.ofReal (c⁻¹ * u x)) = (ENNReal.ofReal c)⁻¹ * ∫⁻ x, ENNReal.ofReal (u x) := by
    intro c u hc hu hu0
    rw [← lintegral_const_mul' _ _ (by simp [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]; linarith)]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ENNReal.ofReal_inv_of_pos hc]
  rw [hlin A f hApos hf hf0, hlin B g hBpos hg hg0, hlin D h hDpos hh hh0] at hcore
  set α := ENNReal.ofReal A with hαdef
  set β := ENNReal.ofReal B with hβdef
  have hαfin : α ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht0.le ENNReal.ofReal_ne_top
  have hβfin : β ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1'.le ENNReal.ofReal_ne_top
  have hδ : ENNReal.ofReal D = α ^ t * β ^ (1 - t) := by
    rw [hDdef, ENNReal.ofReal_mul (Real.rpow_nonneg hApos.le t), hαdef, hβdef,
      ENNReal.ofReal_rpow_of_pos hApos, ENNReal.ofReal_rpow_of_pos hBpos]
  have hδ0 : ENNReal.ofReal D ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hDpos
  have hchain := (geom_le_arith (α⁻¹ * ∫⁻ x, ENNReal.ofReal (f x))
    (β⁻¹ * ∫⁻ y, ENNReal.ofReal (g y)) ht0 ht1).trans hcore
  have hLHS : (α⁻¹ * ∫⁻ x, ENNReal.ofReal (f x)) ^ t *
      (β⁻¹ * ∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) =
      (ENNReal.ofReal D)⁻¹ *
        ((∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ ht1'.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hδ, ENNReal.mul_inv (Or.inr hβfin) (Or.inl hαfin)]
    ring
  rw [hLHS] at hchain
  have hcancel : ∀ X : ENNReal, (ENNReal.ofReal D)⁻¹ * X * ENNReal.ofReal D = X := by
    intro X
    rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hδ0 ENNReal.ofReal_ne_top, one_mul]
  calc (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t)
      = (ENNReal.ofReal D)⁻¹ *
          ((∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t)) *
          ENNReal.ofReal D := (hcancel _).symm
    _ ≤ (ENNReal.ofReal D)⁻¹ * (∫⁻ z, ENNReal.ofReal (h z)) * ENNReal.ofReal D :=
        mul_le_mul_left hchain _
    _ = ∫⁻ z, ENNReal.ofReal (h z) := hcancel _

/--
**Prekopa-Leindler inequality** on the line: if `f x ^ t * g y ^ (1 - t)` is dominated by `h`
at the corresponding convex combination of `x` and `y`, then the same holds for the integrals. -/
theorem prekopaLeindler {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hstep :
    ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (min (f x) ((n : ℝ) + 1))) ^ t *
          (∫⁻ y, ENNReal.ofReal (min (g y) ((n : ℝ) + 1))) ^ (1 - t) ≤
        ∫⁻ z, ENNReal.ofReal (h z) := by
    intro n
    set N : ℝ := (n : ℝ) + 1 with hN
    have hNp : 0 < N := hNpos n
    refine
      le_trans
        (prekopaLeindler_bddAbove (f := fun x ↦ min (f x) N) (g := fun y ↦ min (g y) N) (h :=
          fun z ↦ min (h z) N) (hf.min measurable_const) (hg.min measurable_const)
          (hh.min measurable_const) (fun x ↦ le_min (hf0 x) hNp.le)
          (fun y ↦ le_min (hg0 y) hNp.le) ⟨N, by rintro _ ⟨x, rfl⟩; exact min_le_right _ _⟩
          ⟨N, by rintro _ ⟨y, rfl⟩; exact min_le_right _ _⟩ ht0 ht1 ?_)
        ?_
    · intro x y
      refine
        le_min
          (le_trans
            (mul_le_mul (Real.rpow_le_rpow (le_min (hf0 x) hNp.le) (min_le_left _ _) ht0.le)
              (Real.rpow_le_rpow (le_min (hg0 y) hNp.le) (min_le_left _ _) ht1'.le)
              (Real.rpow_nonneg (le_min (hg0 y) hNp.le) _) (Real.rpow_nonneg (hf0 x) _))
            (hfgh x y))
          ?_
      calc
        min (f x) N ^ t * min (g y) N ^ (1 - t) ≤ N ^ t * N ^ (1 - t) :=
          mul_le_mul (Real.rpow_le_rpow (le_min (hf0 x) hNp.le) (min_le_right _ _) ht0.le)
            (Real.rpow_le_rpow (le_min (hg0 y) hNp.le) (min_le_right _ _) ht1'.le)
            (Real.rpow_nonneg (le_min (hg0 y) hNp.le) _) (Real.rpow_nonneg hNp.le _)
        _ = N := by rw [← Real.rpow_add hNp]; norm_num
    · exact lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hcast : ∀ a b : ℕ, a ≤ b → ((a : ℝ) + 1 ≤ (b : ℝ) + 1) := by
    intro a b hab
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
    linarith
  have hsup :
    ∀ u : ℝ → ℝ,
      Measurable u →
        (⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (u x) ((n : ℝ) + 1))) =
          ∫⁻ x, ENNReal.ofReal (u x) := by
    intro u hu
    have hlim :=
      lintegral_iSup (μ := (volume : Measure ℝ)) (f := fun (n : ℕ) (x : ℝ) ↦
        ENNReal.ofReal (min (u x) ((n : ℝ) + 1)))
        (fun n ↦ (hu.min measurable_const).ennreal_ofReal)
        (fun a b hab x ↦ ENNReal.ofReal_le_ofReal (min_le_min le_rfl (hcast a b hab)))
    rw [← hlim]
    refine lintegral_congr fun x ↦ ?_
    refine le_antisymm (iSup_le fun n ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (u x)
    exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (le_min le_rfl (by linarith)))
  have hmono :
    ∀ u : ℝ → ℝ, Monotone fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (min (u x) ((n : ℝ) + 1)) :=
    fun u a b hab ↦
    lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (min_le_min le_rfl (hcast a b hab))
  rw [← hsup f hf, ← hsup g hg]
  simp_rw (config := { congrConsts := false }) [← ENNReal.orderIsoRpow_apply t ht0, ←
    ENNReal.orderIsoRpow_apply (1 - t) ht1']
  rw [(ENNReal.orderIsoRpow _ ht0).map_iSup _, (ENNReal.orderIsoRpow _ ht1').map_iSup _,
    ENNReal.iSup_mul]
  refine iSup_le fun n ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m ↦ ?_
  refine
    le_trans
      (mul_le_mul' (ENNReal.rpow_le_rpow (hmono f (le_max_left n m)) ht0.le)
        (ENNReal.rpow_le_rpow (hmono g (le_max_right n m)) ht1'.le))
      (hstep (max n m))

end PrekopaLeindler

end FunctionalInequalities.Probability.Line
