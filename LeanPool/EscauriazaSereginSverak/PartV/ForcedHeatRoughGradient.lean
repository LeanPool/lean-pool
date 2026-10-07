/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatWeakSmoothQ

/-!
# The weak spatial gradient of the rough forced heat response

Along a fast smooth approximation of a tensor in `L^{5/2} ∩ L²` supported in
`Q_τ`, the spatial gradients of the smooth forced heat responses form a Cauchy
sequence in `L²(Q_τ)` by the energy estimate applied to differences; their limit
is the weak spatial gradient of the rough response, with the energy bound of
`eq:pv-stokes-energy` in `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `L²(Q_τ)` limit of the spatial gradients of smooth responses along a fast
smooth approximation of a rough tensor, with the energy bound. -/
theorem forcedHeat_rough_gradient :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      ∃ Gs : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ, ∃ DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
        (∀ k i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => Gs k i j p)) ∧
        (∀ k i j, HasCompactSupport (fun p : Vec3 × ℝ => Gs k i j p)) ∧
        (∀ k i j, tsupport (fun p : Vec3 × ℝ => Gs k i j p) ⊆ {p | 0 < p.2}) ∧
        (∀ i j, Tendsto (fun k => eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2 volume)
          atTop (𝓝 0)) ∧
        (∀ k i j, MemLp (fun z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z) 2
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        (∀ i j, MemLp (DZ i j) 2
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        (∀ i j, Tendsto (fun k => eLpNorm
          ((fun z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z) - DZ i j) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) atTop (𝓝 0)) ∧
        eLpNorm (fun z => fun i j => DZ i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  obtain ⟨C, hC, hsmooth⟩ := forcedHeat_smooth_estimates
  refine ⟨C, hC, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨Gn, hGn, hGnc, hGnpos, _, h2, _⟩ := forcedHeat_rough_approx hτ hG52 hG2 hGsupp
  set Q : Set ParabolicPoint := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set μQ : Measure ParabolicPoint := volume.restrict Q
  set C' : ℝ≥0∞ := ENNReal.ofReal C
  have hC' : C' ≠ ∞ := ENNReal.ofReal_ne_top
  -- the componentwise errors
  let e : ℕ → ℝ≥0∞ := fun n => ∑ i : Fin 3, ∑ j : Fin 3,
    eLpNorm (fun p : Vec3 × ℝ => Gn n i j p - G i j p) 2 volume
  have he : Tendsto e atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => h2 i j
    simpa only [Finset.sum_const_zero] using h
  set r : ℝ≥0∞ := (4 : ℝ≥0∞)⁻¹
  have hr0 : r ≠ 0 := by simp [r]
  have hr1 : r < 1 := by
    simp only [r]
    exact ENNReal.inv_lt_one.2 (by norm_num)
  have hrk (k : ℕ) : 0 < r ^ k := ENNReal.pow_pos (pos_iff_ne_zero.2 hr0) k
  have hfast (k : ℕ) : ∃ n, e n ≤ r ^ k :=
    (he.eventually (ge_mem_nhds (hrk k))).exists
  choose m hm using hfast
  let Gs : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun k => Gn (m k)
  have hGsm (k : ℕ) (i j : Fin 3) :
      eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2 volume ≤ r ^ k := by
    refine le_trans ?_ (hm k)
    exact (Finset.single_le_sum (f := fun j' => eLpNorm (fun p : Vec3 × ℝ =>
      Gn (m k) i j' p - G i j' p) 2 volume) (fun _ _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, eLpNorm (fun p : Vec3 × ℝ =>
        Gn (m k) i' j' p - G i' j' p) 2 volume) (fun _ _ => bot_le) (Finset.mem_univ i))
  have hrpow : Tendsto (fun k : ℕ => r ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1
  have hGsconv (i j : Fin 3) : Tendsto (fun k => eLpNorm (fun p : Vec3 × ℝ =>
      Gs k i j p - G i j p) 2 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrpow (fun k => bot_le)
      fun k => hGsm k i j
  have hGs (k : ℕ) := hGn (m k)
  have hGsc (k : ℕ) := hGnc (m k)
  have hGspos (k : ℕ) := hGnpos (m k)
  -- smooth differences
  have hsubsmooth (k l : ℕ) (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) :=
    (hGs k i j).sub (hGs l i j)
  have hsubc (k l : ℕ) (i j : Fin 3) :
      HasCompactSupport (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) :=
    (hGsc k i j).sub (hGsc l i j)
  have hsubpos (k l : ℕ) (i j : Fin 3) :
      tsupport (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) ⊆ {p | 0 < p.2} := by
    have hsupp : Function.support (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) ⊆
        Function.support (fun p : Vec3 × ℝ => Gs k i j p) ∪
          Function.support (fun p : Vec3 × ℝ => Gs l i j p) := by
      intro p hp
      by_contra hno
      simp only [mem_union, Function.mem_support, not_or, not_not] at hno
      apply hp
      change Gs k i j p - Gs l i j p = 0
      rw [hno.1, hno.2, sub_zero]
    refine (closure_mono hsupp).trans ?_
    rw [closure_union]
    exact union_subset (hGspos k i j) (hGspos l i j)
  -- the gradient sequence
  let DZs : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun k i j z =>
    CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  have hDZc (k : ℕ) (i j : Fin 3) : Continuous (fun z : Vec3 × ℝ => DZs k i j z) := by
    have h := (continuous_apply i).comp ((response_continuity (hGs k) (hGsc k) hT).2.1 j)
    refine h.congr fun z => ?_
    exact (spatialPartial_forcedHeat_eq (hGs k) (hGsc k) i j z).symm
  -- the tensor bound on the slab
  have htensorQ (H : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
      (hH : ∀ i j, AEStronglyMeasurable (fun p : Vec3 × ℝ => H i j p) volume) :
      eLpNorm (fun z => fun i j => H i j z) 2 μQ ≤
        ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun p : Vec3 × ℝ => H i j p) 2 volume :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (eLpNorm_tensor_le_sum (by norm_num) _ fun i j => hH i j)
  have hcomp (T : ParabolicPoint → Fin 3 → Fin 3 → ℝ) (i j : Fin 3)
      (hTm : AEStronglyMeasurable (fun z => T z i j) μQ) :
      eLpNorm (fun z => T z i j) 2 μQ ≤ eLpNorm T 2 μQ :=
    eLpNorm_mono_ae hTm (Eventually.of_forall fun z =>
      (norm_le_pi_norm (T z i) j).trans (norm_le_pi_norm (T z) i))
  -- membership in `L²(Q)` of each gradient
  have hDZmem (k : ℕ) (i j : Fin 3) : MemLp (DZs k i j) 2 μQ := by
    refine memLp_iff.2 ?_
    have hbound := (hsmooth (Gs k) (hGs k) (hGsc k) (hGspos k) τ hτ).2.1
    refine lt_of_le_of_lt ((hcomp (fun z => fun i j => DZs k i j z) i j
      (hDZc k i j).aestronglyMeasurable.restrict).trans hbound) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (htensorQ (Gs k)
      fun i j => (hGs k i j).continuous.aestronglyMeasurable) ?_)
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ =>
      ((hGs k i j).continuous.memLp_of_hasCompactSupport (hGsc k i j)).eLpNorm_lt_top
  -- componentwise errors of the fast sequence
  let es : ℕ → ℝ≥0∞ := fun k => ∑ i : Fin 3, ∑ j : Fin 3,
    eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2 volume
  have hes (k : ℕ) : es k ≤ r ^ k := hm k
  have hGmeas (i j : Fin 3) : AEStronglyMeasurable (fun p : Vec3 × ℝ => G i j p) volume :=
    (hG2 i j).aestronglyMeasurable
  have hGsmeas (k : ℕ) (i j : Fin 3) :
      AEStronglyMeasurable (fun p : Vec3 × ℝ => Gs k i j p) volume :=
    (hGs k i j).continuous.aestronglyMeasurable
  -- the Cauchy estimate
  have hdiff (k l : ℕ) (i j : Fin 3) :
      eLpNorm (DZs k i j - DZs l i j) 2 μQ ≤ C' * (r ^ k + r ^ l) := by
    have hfun : DZs k i j - DZs l i j = fun z =>
        CKN.spatialPartial (fun w => forcedHeat (Gs k - Gs l) w i) j z :=
      funext fun z => (spatialPartial_forcedHeat_sub (hGs k) (hGsc k) (hGs l) (hGsc l) i j z).symm
    have hb := (hsmooth (Gs k - Gs l) (hsubsmooth k l) (hsubc k l) (hsubpos k l) τ hτ).2.1
    have hDc : Continuous (fun z : Vec3 × ℝ =>
        CKN.spatialPartial (fun w => forcedHeat (Gs k - Gs l) w i) j z) := by
      refine ((hDZc k i j).sub (hDZc l i j)).congr fun z => ?_
      exact (spatialPartial_forcedHeat_sub (hGs k) (hGsc k) (hGs l) (hGsc l) i j z).symm
    rw [hfun]
    refine ((hcomp (fun z => fun i j =>
      CKN.spatialPartial (fun w => forcedHeat (Gs k - Gs l) w i) j z) i j
        hDc.aestronglyMeasurable.restrict).trans hb).trans ?_
    refine mul_le_mul_right ((htensorQ (Gs k - Gs l) fun i j =>
      (hsubsmooth k l i j).continuous.aestronglyMeasurable).trans ?_) _
    have hpt (i j : Fin 3) : eLpNorm (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) 2 volume ≤
        eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2 volume +
          eLpNorm (fun p : Vec3 × ℝ => Gs l i j p - G i j p) 2 volume := by
      have hsplit : (fun p : Vec3 × ℝ => (Gs k - Gs l) i j p) =
          (fun p : Vec3 × ℝ => Gs k i j p - G i j p) -
            fun p : Vec3 × ℝ => Gs l i j p - G i j p := by
        funext p
        change Gs k i j p - Gs l i j p = (Gs k i j p - G i j p) - (Gs l i j p - G i j p)
        ring
      rw [hsplit]
      exact eLpNorm_sub_le (by norm_num)
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2 volume +
            eLpNorm (fun p : Vec3 × ℝ => Gs l i j p - G i j p) 2 volume) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
      _ = es k + es l := by
        simp only [es, Finset.sum_add_distrib]
      _ ≤ r ^ k + r ^ l := add_le_add (hes k) (hes l)
  have hrN {N k : ℕ} (hk : N ≤ k) : r ^ k ≤ r ^ N := pow_le_pow_right_of_le_one' hr1.le hk
  have hrfin (N : ℕ) : r ^ N ≠ ∞ := ENNReal.pow_ne_top (by simp [r])
  let B : ℕ → ℝ≥0∞ := fun N => (2 * C' + 1) * r ^ N
  have hB : ∑' N, B N ≠ ∞ := by
    simp only [B]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hC',
      ENNReal.one_ne_top⟩) (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt hr1).ne'
  have hcau (i j : Fin 3) (N k l : ℕ) (hk : N ≤ k) (hl : N ≤ l) :
      eLpNorm (DZs k i j - DZs l i j) 2 μQ < B N := by
    refine lt_of_le_of_lt ((hdiff k l i j).trans (mul_le_mul_right
      (add_le_add (hrN hk) (hrN hl)) _)) ?_
    have hfin : C' * (r ^ N + r ^ N) ≠ ∞ :=
      ENNReal.mul_ne_top hC' (ENNReal.add_ne_top.2 ⟨hrfin N, hrfin N⟩)
    calc
      C' * (r ^ N + r ^ N) < C' * (r ^ N + r ^ N) + r ^ N :=
        ENNReal.lt_add_right hfin (pow_ne_zero N hr0)
      _ = B N := by simp only [B]; ring
  choose DZ hDZlmem hDZlim using fun (ij : Fin 3 × Fin 3) =>
    Lp.cauchy_complete_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (fun k => hDZmem k ij.1 ij.2) hB (hcau ij.1 ij.2)
  refine ⟨Gs, fun i j => DZ (i, j), hGs, hGsc, hGspos, hGsconv, hDZmem,
    fun i j => hDZlmem (i, j), fun i j => hDZlim (i, j), ?_⟩
  -- the energy bound for the limit
  set A : ℝ≥0∞ := eLpNorm (fun z => fun i j => G i j z) 2 μQ
  have hbound (k : ℕ) : eLpNorm (fun z => fun i j => DZ (i, j) z) 2 μQ ≤
      C' * (A + es k) + ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (DZs k i j - DZ (i, j)) 2 μQ := by
    have hsplit : (fun z => fun i j => DZ (i, j) z) =
        (fun z => fun i j => DZs k i j z) + fun z => fun i j => DZ (i, j) z - DZs k i j z := by
      funext z i j
      simp
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · have hb := (hsmooth (Gs k) (hGs k) (hGsc k) (hGspos k) τ hτ).2.1
      refine hb.trans (mul_le_mul_right ?_ _)
      have hsplitG : (fun z => fun i j => Gs k i j z) =
          (fun z => fun i j => G i j z) + fun z => fun i j => Gs k i j z - G i j z := by
        funext z i j
        simp
      rw [hsplitG]
      refine (eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ?_)
      exact htensorQ (fun i j z => Gs k i j z - G i j z) fun i j =>
        (hGsmeas k i j).sub (hGmeas i j)
    · refine (eLpNorm_tensor_le_sum (by norm_num) _ fun i j =>
        (hDZlmem (i, j)).aestronglyMeasurable.sub
          (hDZc k i j).aestronglyMeasurable.restrict).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← eLpNorm_neg]
      congr 1
      funext z
      change -(DZ (i, j) z - DZs k i j z) = DZs k i j z - DZ (i, j) z
      ring
  have hes0 : Tendsto es atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrpow (fun k => bot_le) hes
  have hsum0 : Tendsto (fun k => ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (DZs k i j - DZ (i, j)) 2 μQ) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hDZlim (i, j)
    simpa only [Finset.sum_const_zero] using h
  have hlim : Tendsto (fun k => C' * (A + es k) + ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (DZs k i j - DZ (i, j)) 2 μQ) atTop (𝓝 (C' * A)) := by
    have h1 := ENNReal.Tendsto.const_mul (a := C') (tendsto_const_nhds (x := A) |>.add hes0)
      (Or.inr hC')
    rw [add_zero] at h1
    have h2 := h1.add hsum0
    rwa [add_zero] at h2
  exact ge_of_tendsto' hlim hbound

end ESS

end
