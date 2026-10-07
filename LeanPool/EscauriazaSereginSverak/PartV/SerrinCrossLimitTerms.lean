/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCutoff
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify

/-!
# Removing the mollification and cutoff from space-time pairings

On the slab `ℝ³ × (0, t)`, pairings of slice-wise mollified fields weighted by
the cutoffs converge to the pairings of the fields, and those weighted by
cutoff gradients tend to zero. These are the limit terms of the cross-testing
identity in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem serrin_slab_restrict_le {t T : ℝ} (ht : t ≤ T) :
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)) : Measure ParabolicPoint) ≤
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) := by
  apply Measure.restrict_mono _ le_rfl
  intro z hz
  exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht⟩

/-- Slice-wise mollification converges in `L^p` on every shorter slab. -/
theorem serrinSM_tendsto_restrict {t T : ℝ} (ht : t ≤ T) {f : ParabolicPoint → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Tendsto (fun n => eLpNorm (fun z => serrinSM f n z - f z) p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (serrinSM_tendsto hp hptop hf) (fun _ => bot_le) (fun n => ?_)
  exact eLpNorm_mono_measure _ (serrin_slab_restrict_le ht)

private theorem serrin_cutoff_weight_measurable (n : ℕ) (t : ℝ) :
    AEStronglyMeasurable (fun z : ParabolicPoint => serrinCutoff n z.1)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
  ((serrinCutoff_contDiff n).continuous.measurable.comp measurable_fst).aestronglyMeasurable

/-- Cutoff-weighted pairings of mollified fields converge to the pairing of the
fields. -/
theorem serrin_cutoff_pairing_limit {t T : ℝ} (ht : t ≤ T) {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] (hp : 1 ≤ p) (hptop : p ≠ ⊤) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    {f g : ParabolicPoint → ℝ}
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : MemLp g q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), f z * g z)) := by
  have hle := serrin_slab_restrict_le ht
  have h := serrin_weighted_pairing_tendsto (μ := volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) hq
    (hf.mono_measure hle) (hg.mono_measure hle)
    (Eventually.of_forall fun n =>
      (serrinSM_aestronglyMeasurable hf.aestronglyMeasurable n).mono_measure hle)
    (Eventually.of_forall fun n =>
      (serrinSM_aestronglyMeasurable hg.aestronglyMeasurable n).mono_measure hle)
    (serrinSM_tendsto_restrict ht hp hptop hf) (serrinSM_tendsto_restrict ht hq hqtop hg)
    (cs := fun n z => serrinCutoff n z.1) (c := fun _ => 1)
    (fun n => serrin_cutoff_weight_measurable n t) (fun n z => serrinCutoff_abs_le_one n z.1)
    aestronglyMeasurable_const (fun _ => by simp)
    (Eventually.of_forall fun z => serrinCutoff_tendsto_one z.1)
  simpa only [one_mul] using h

/-- Pairings of mollified fields weighted by a cutoff gradient tend to zero. -/
theorem serrin_cutoff_deriv_pairing_limit {t T : ℝ} (ht : t ≤ T) {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] (hp : 1 ≤ p) (hptop : p ≠ ⊤) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    {f g : ParabolicPoint → ℝ}
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : MemLp g q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (j : Fin 3) :
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        spatialDeriv (serrinCutoff n) j z.1 * serrinSM f n z * serrinSM g n z) atTop (𝓝 0) := by
  have hle := serrin_slab_restrict_le ht
  obtain ⟨C, hC0, hC⟩ := serrinCutoff_deriv_bound
  have hε : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  exact serrin_weighted_pairing_tendsto_zero (μ := volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) hp hq
    (hf.mono_measure hle) (hg.mono_measure hle)
    (Eventually.of_forall fun n =>
      (serrinSM_aestronglyMeasurable hf.aestronglyMeasurable n).mono_measure hle)
    (Eventually.of_forall fun n =>
      (serrinSM_aestronglyMeasurable hg.aestronglyMeasurable n).mono_measure hle)
    (serrinSM_tendsto_restrict ht hp hptop hf) (serrinSM_tendsto_restrict ht hq hqtop hg)
    (cs := fun n z => spatialDeriv (serrinCutoff n) j z.1) (fun n z => hC n j z.1) hε

/-- Slice-wise mollifications of an `L^p` field are eventually in `L^p` on
every shorter slab. -/
theorem serrinSM_memLp_eventually {t T : ℝ} (ht : t ≤ T) {f : ParabolicPoint → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ∀ᶠ n in atTop, MemLp (serrinSM f n)
      p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := by
  have hle := serrin_slab_restrict_le ht
  have hsmall : ∀ᶠ n in atTop, eLpNorm (fun z => serrinSM f n z - f z) p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) < ⊤ :=
    (tendsto_order.1 (serrinSM_tendsto_restrict ht hp hptop hf)).2 1 one_pos |>.mono
      fun _ h => h.trans ENNReal.one_lt_top
  filter_upwards [hsmall] with n hn
  have hd : MemLp (fun z => serrinSM f n z - f z) p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := hn
  have h := hd.add (hf.mono_measure hle)
  refine h.congr_norm ((serrinSM_aestronglyMeasurable hf.aestronglyMeasurable n).mono_measure
    hle) (Eventually.of_forall fun z => ?_)
  simp

/-- A bounded continuous weight times two slice-wise mollified fields in
conjugate spaces is eventually integrable on the shorter slab. -/
theorem serrin_weighted_term_integrable {t T : ℝ} (ht : t ≤ T) {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] (hp : 1 ≤ p) (hptop : p ≠ ⊤) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    {f g : ParabolicPoint → ℝ}
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : MemLp g q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    {c : ℕ → Vec3 → ℝ} (hc : ∀ n, Continuous (c n)) (hcb : ∀ n, ∃ C, ∀ y, |c n y| ≤ C) :
    ∀ᶠ n in atTop, Integrable (fun z : ParabolicPoint => c n z.1 * serrinSM f n z *
      serrinSM g n z) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := by
  filter_upwards [serrinSM_memLp_eventually ht hp hptop hf,
    serrinSM_memLp_eventually ht hq hqtop hg] with n hfn hgn
  have hprod : Integrable (fun z => serrinSM f n z * serrinSM g n z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    memLp_one_iff_integrable.mp (hfn.mul (r := 1) hgn)
  obtain ⟨C, hC⟩ := hcb n
  refine (hprod.bdd_mul (c := C) (((hc n).measurable.comp measurable_fst).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)).congr (Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs]
    exact hC z.1
  · simp only [mul_assoc]
    rfl

end ESS
