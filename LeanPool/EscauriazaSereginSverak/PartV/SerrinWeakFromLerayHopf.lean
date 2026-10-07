/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEstimate
public import LeanPool.CaffarelliKohnNirenberg.Statements.AssociatedPressure

/-!
# Leray–Hopf solutions are finite-energy weak solutions with a pressure

With the canonical associated pressure (`thm:assoc-pressure`), a Leray–Hopf
solution belongs to the class used by the weak–strong comparison of
`lem:pv-serrin-uniqueness`. The initial pairing is identified with the datum
through the weak continuity at time zero and the strong `L²` trace.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Pairing against a fixed square-integrable function is continuous along any
filter under `L²` convergence of the other factor. -/
theorem serrin_integral_mul_tendsto_filter {ι : Type} {l : Filter ι}
    {f g : Vec3 → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {gseq : ι → Vec3 → ℝ} (hgseq : ∀ᶠ n in l, MemLp (gseq n) 2 volume)
    (herror : Tendsto (fun n => eLpNorm (fun x => gseq n x - g x) 2 volume) l (𝓝 0)) :
    Tendsto (fun n => ∫ x : Vec3, f x * gseq n x) l (𝓝 (∫ x : Vec3, f x * g x)) := by
  -- Cauchy–Schwarz for the difference
  have hbound : ∀ᶠ n in l, |(∫ x : Vec3, f x * gseq n x) - ∫ x : Vec3, f x * g x| ≤
      (eLpNorm f 2 volume).toReal *
        (eLpNorm (fun x => gseq n x - g x) 2 volume).toReal := by
    filter_upwards [hgseq] with n hn
    have hdiff : MemLp (fun x => gseq n x - g x) 2 volume := hn.sub hg
    have hint1 : Integrable (fun x => f x * gseq n x) volume := hf.integrable_mul hn
    have hint2 : Integrable (fun x => f x * g x) volume := hf.integrable_mul hg
    rw [← integral_sub hint1 hint2]
    have heq : (fun x => f x * gseq n x - f x * g x) = fun x => f x * (gseq n x - g x) := by
      funext x
      ring
    rw [heq]
    let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ENNReal.HolderConjugate.instTwoTwo
    have hprodLe : eLpNorm (f * fun x => gseq n x - g x) 1 volume ≤
        eLpNorm f 2 volume * eLpNorm (fun x => gseq n x - g x) 2 volume :=
      eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hdiff.aestronglyMeasurable
    have hfin : eLpNorm f 2 volume * eLpNorm (fun x => gseq n x - g x) 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top hf.eLpNorm_ne_top hdiff.eLpNorm_ne_top
    calc
      |∫ x : Vec3, f x * (gseq n x - g x)| ≤
          (∫⁻ x : Vec3, ‖f x * (gseq n x - g x)‖ₑ).toReal := by
        have h := norm_integral_le_lintegral_norm (μ := volume)
          (fun x : Vec3 => f x * (gseq n x - g x))
        simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using h
      _ = (eLpNorm (f * fun x => gseq n x - g x) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm (hf.aestronglyMeasurable.mul
          hdiff.aestronglyMeasurable)]
        simp only [Pi.mul_apply]
      _ ≤ (eLpNorm f 2 volume * eLpNorm (fun x => gseq n x - g x) 2 volume).toReal :=
        ENNReal.toReal_mono hfin hprodLe
      _ = (eLpNorm f 2 volume).toReal *
            (eLpNorm (fun x => gseq n x - g x) 2 volume).toReal := ENNReal.toReal_mul
  have hlim : Tendsto (fun n => (eLpNorm f 2 volume).toReal *
      (eLpNorm (fun x => gseq n x - g x) 2 volume).toReal) l (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herror
    simpa using h.const_mul (eLpNorm f 2 volume).toReal
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (by simpa only [Real.norm_eq_abs] using hbound) hlim

/-- Every right neighborhood of zero meets every full-measure subset of `(0, T)`. -/
theorem serrin_trace_filter_neBot {T : ℝ} (hT : 0 < T) :
    (𝓝[>] (0 : ℝ) ⊓ ae (volume.restrict (Ioo 0 T))).NeBot := by
  rw [inf_neBot_iff]
  intro s hs t ht
  obtain ⟨δ, hδ, hδs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hs
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hsub : Ioo 0 (min δ T) ⊆ Ioo 0 T ∩ tᶜ := by
    intro r hr
    refine ⟨⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩, fun hrt => ?_⟩
    have hrs : r ∈ s := hδs ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have : r ∈ s ∩ t := ⟨hrs, hrt⟩
    rw [hempty] at this
    exact this
  have hnull : volume (Ioo 0 T ∩ tᶜ) = 0 := by
    have h := (mem_ae_iff).mp ht
    rw [Measure.restrict_apply' measurableSet_Ioo] at h
    rwa [inter_comm] at h
  have hpos : 0 < volume (Ioo (0 : ℝ) (min δ T)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by rw [sub_zero]; exact lt_min hδ hT)
  exact (ne_of_gt hpos) (le_antisymm ((measure_mono hsub).trans_eq hnull) bot_le)

/-- The initial pairings of a Leray–Hopf solution with smooth compactly
supported fields are those of the datum. -/
theorem lerayHopf_initial_pairing {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x : Vec3, ∑ i : Fin 3, u (x, 0) i * ψ x i) =
      ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i := by
  have hT : 0 < T := hLH.1
  have ha2 : MemLp a 2 volume := hLH.2.1.1
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  let l : Filter ℝ := 𝓝[>] (0 : ℝ) ⊓ ae (volume.restrict (Ioo 0 T))
  have : l.NeBot := serrin_trace_filter_neBot hT
  let f : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ x i
  have hcont : ContinuousOn f (Icc 0 T) := hLH.2.2.2.2.2.2.2.2.1 ψ hψ2
  have hlim0 : Tendsto f l (𝓝 (f 0)) := by
    have h1 : Tendsto f (𝓝[Icc 0 T] 0) (𝓝 (f 0)) :=
      hcont (0 : ℝ) ⟨le_rfl, hT.le⟩
    have h2 : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 T] 0 := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
      exact nhdsWithin_mono _ Ioo_subset_Icc_self
    exact h1.mono_left (inf_le_left.trans h2)
  have htrace := serrin_difference_initial_trace_l2_ae hLH
  have hslices := serrin_slice_memLp_two_ae hLH
  have hslicesL : ∀ᶠ t in l, MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
    have h : ∀ᶠ t in ae (volume.restrict (Ioo 0 T)), MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
      filter_upwards [hslices] with t ht
      exact ht.1
    exact h.filter_mono inf_le_right
  have hcomp (i : Fin 3) : Tendsto (fun t => ∫ x : Vec3, ψ x i * u (x, t) i) l
      (𝓝 (∫ x : Vec3, ψ x i * a x i)) := by
    refine serrin_integral_mul_tendsto_filter (hψ2.eval i) (ha2.eval i) ?_ ?_
    · filter_upwards [hslicesL] with t ht
      exact ht.eval i
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htrace
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [hslicesL] with t ht
      have hm : AEStronglyMeasurable (fun x => u (x, t) i - a x i) volume :=
        ((ht.eval i).sub (ha2.eval i)).aestronglyMeasurable
      refine eLpNorm_mono_ae hm ?_
      filter_upwards [] with x
      exact norm_le_pi_norm (u (x, t) - a x) i
  have hlimA : Tendsto f l (𝓝 (∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i)) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => hcomp i
    have hA : (∑ i : Fin 3, ∫ x : Vec3, ψ x i * a x i) =
        ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i := by
      have hint (i : Fin 3) : Integrable (fun x : Vec3 => ψ x i * a x i) volume :=
        (hψ2.eval i).integrable_mul (ha2.eval i)
      rw [← integral_finsetSum _ fun i _ => hint i]
      congr 1
      funext x
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hA]
    refine hsum.congr' ?_
    filter_upwards [hslicesL] with t ht
    change (∑ i : Fin 3, ∫ x : Vec3, ψ x i * u (x, t) i) = f t
    simp only [f]
    have hint (i : Fin 3) : Integrable (fun x : Vec3 => ψ x i * u (x, t) i) volume :=
      (hψ2.eval i).integrable_mul (ht.eval i)
    rw [← integral_finsetSum _ fun i _ => hint i]
    congr 1
    funext x
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact tendsto_nhds_unique hlim0 hlimA

/-- A Leray–Hopf solution, with its canonical associated pressure, is a
finite-energy weak solution with pressure. -/
theorem serrinWeak_of_lerayHopf {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∃ p : ParabolicPoint → ℝ, IsSerrinWeakSolution T a u Du p := by
  obtain ⟨p, hp, hmom, _⟩ := associatedPressure T a u Du hLH
  refine ⟨p, ⟨hLH.1, hLH.2.1.1, hLH.2.2.1, hLH.2.2.2.1, hLH.2.2.2.2.1,
    hLH.2.2.2.2.2.1, hLH.2.2.2.2.2.2.1, hLH.2.2.2.2.2.2.2.1, hp, hmom, ?_, ?_⟩⟩
  · intro ψ hψ hψc
    exact hLH.2.2.2.2.2.2.2.2.1 ψ (hψ.continuous.memLp_of_hasCompactSupport hψc)
  · intro ψ hψ hψc
    exact lerayHopf_initial_pairing hLH hψ hψc

end ESS
