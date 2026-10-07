/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import LeanPool.CIVAxisymmetric.Analysis.ENNRealDecay
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Ancient Vanishing

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN


noncomputable section

namespace CIV

/-- From an almost-everywhere property on `Iio a`, extract a sequence in the good set that
tends to `-∞`. Used to pass a countable family of "early enough" reference times through the
comparison monotonicity bound. -/
private theorem exists_seq_mem_ae_tendsto_atBot {a : ℝ} {S : Set ℝ}
    (hS : ∀ᵐ x ∂(volume.restrict (Iio a)), x ∈ S) :
    ∃ f : ℕ → ℝ, (∀ n, f n ∈ S) ∧ Filter.Tendsto f Filter.atTop Filter.atBot := by
  have hSnull : volume (Iio a \ S) = 0 := by
    have h := (ae_iff).mp hS
    have hset : Iio a \ S = {x | x ∉ S} ∩ Iio a := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩; exact ⟨hx2, hx1⟩
      · rintro ⟨hx1, hx2⟩; exact ⟨hx2, hx1⟩
    rw [hset, ← Measure.restrict_apply' measurableSet_Iio]
    exact h
  have hchoice : ∀ n : ℕ, (Iio (a - (n : ℝ)) ∩ S).Nonempty := by
    intro n
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Iio (a - (n : ℝ)) \ S ⊆ Iio a \ S :=
      Set.sdiff_subset_sdiff_left (fun x hx => by
        simp only [mem_Iio] at hx ⊢
        have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith only [hx, hnn])
    have hnull2 : volume (Iio (a - (n : ℝ)) \ S) = 0 := measure_mono_null hsub hSnull
    have hsubset2 : Iio (a - (n:ℝ)) ⊆ Iio (a - (n:ℝ)) \ S := by
      intro x hx
      refine ⟨hx, fun hxS => ?_⟩
      have hmem : x ∈ (∅ : Set ℝ) := hcon ▸ Set.mem_inter hx hxS
      exact hmem
    have hle : volume (Iio (a - (n:ℝ))) ≤ 0 := hnull2 ▸ measure_mono hsubset2
    exact absurd hle (not_le.mpr (Measure.measure_Iio_pos volume (a - (n:ℝ))))
  choose f hf using hchoice
  refine ⟨f, fun n => (hf n).2, ?_⟩
  have hupper : ∀ n : ℕ, f n ≤ a - (n : ℝ) := fun n => le_of_lt (hf n).1
  have hatbot : Filter.Tendsto (fun n : ℕ => a - (n:ℝ)) Filter.atTop Filter.atBot := by
    have h1 : Filter.Tendsto (fun n : ℕ => -(n:ℝ)) Filter.atTop Filter.atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    have h2 := tendsto_atBot_add_const_right Filter.atTop a h1
    refine h2.congr (fun n => ?_)
    ring
  exact tendsto_atBot_mono hupper hatbot

/-- For almost every reference time in `Iio T`, the `L^∞` norm of the corresponding slice of `q`
is exactly zero: the comparison monotonicity bound at any earlier time is controlled by the decay
hypothesis, and letting the earlier time recede to `-∞` forces the value at `τ` to vanish. -/
private theorem eLpNorm_slice_eq_zero_ae {m : ℕ} {T : ℝ} {q : Vec m × ℝ → ℝ}
    (C κ : ℝ) (hκ : 0 < κ)
    (hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1) T))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ ENNReal.ofReal (C * |τ| ^ (-κ)))
    (hcomp : ∀ᵐ τ₀ ∂(volume.restrict (Iio T)), ∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume) :
    ∀ᵐ τ ∂(volume.restrict (Iio T)), eLpNorm (fun x => q (x, τ)) ⊤ volume = 0 := by
  set F : ℝ → ℝ≥0∞ := fun τ => eLpNorm (fun x => q (x, τ)) ⊤ volume with hF
  have hsub : Iio (min (-1) T) ⊆ Iio T :=
    fun x hx => mem_Iio.mpr (lt_of_lt_of_le (mem_Iio.mp hx) (min_le_right _ _))
  have hcomp' : ∀ᵐ τ₀ ∂(volume.restrict (Iio (min (-1) T))),
      ∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ → F τ ≤ F τ₀ :=
    ae_restrict_of_ae_restrict_of_subset hsub hcomp
  have hgood : ∀ᵐ τ₀ ∂(volume.restrict (Iio (min (-1) T))),
      (F τ₀ ≤ ENNReal.ofReal (C * |τ₀| ^ (-κ))) ∧
        (∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ → F τ ≤ F τ₀) :=
    hdecay.and hcomp'
  obtain ⟨g, hgmem, hgtendsto⟩ :=
    exists_seq_mem_ae_tendsto_atBot (S := {τ₀ | F τ₀ ≤ ENNReal.ofReal (C * |τ₀| ^ (-κ)) ∧
      ∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ → F τ ≤ F τ₀}) hgood
  have hinner : ∀ᵐ τ ∂(volume.restrict (Iio T)), ∀ n : ℕ, g n < τ → F τ ≤ F (g n) :=
    (ae_all_iff).mpr (fun n => (hgmem n).2)
  filter_upwards [hinner] with τ hτ
  have hbound : ∀ n : ℕ, g n < τ → F τ ≤ ENNReal.ofReal (C * |g n| ^ (-κ)) := by
    intro n hn
    exact le_trans (hτ n hn) (hgmem n).1
  have heventually : ∀ᶠ n : ℕ in Filter.atTop, F τ ≤ ENNReal.ofReal (C * |g n| ^ (-κ)) := by
    have hev : ∀ᶠ n : ℕ in Filter.atTop, g n < τ := hgtendsto.eventually_lt_atBot τ
    filter_upwards [hev] with n hn using hbound n hn
  have htendsto0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (C * |g n| ^ (-κ))) Filter.atTop
      (nhds 0) :=
    (tendsto_ofReal_mul_abs_rpow_neg_atBot C hκ).comp hgtendsto
  have hle0 : F τ ≤ 0 := ge_of_tendsto htendsto0 heventually
  exact le_antisymm hle0 bot_le

/-- Turn a per-slice almost-everywhere vanishing statement into the corresponding
almost-everywhere vanishing statement on the product `Vec m × Iio T`, using a globally
strongly measurable representative of `q` and Fubini for null sets in both index orders. -/
private theorem ae_zero_prod_of_ae_slice_zero {m : ℕ} {T : ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m (Iio T) q)
    (hslice : ∀ᵐ τ ∂(volume.restrict (Iio T)), (fun x : Vec m => q (x, τ)) =ᵐ[volume] 0) :
    ∀ᵐ z ∂(volume.restrict (univ ×ˢ Iio T)), q z = 0 := by
  have hqprod : AEStronglyMeasurable q
      ((volume : Measure (Vec m)).prod (volume.restrict (Iio T))) := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict (Iio T)) =
        volume.restrict (univ ×ˢ Iio T) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]
    exact hq.1
  obtain ⟨q₀, hq₀meas, hq₀eq⟩ := hqprod
  have hq₀eq' : ∀ᵐ w ∂((volume.restrict (Iio T)).prod (volume : Measure (Vec m))),
      q w.swap = q₀ w.swap := by
    refine ae_of_ae_map (f := (Prod.swap : ℝ × Vec m → Vec m × ℝ))
      (p := fun z : Vec m × ℝ => q z = q₀ z)
      (measurable_swap.aemeasurable
        (μ := (volume.restrict (Iio T)).prod (volume : Measure (Vec m)))) ?_
    rw [Measure.prod_swap]
    exact hq₀eq
  have htimeouter : ∀ᵐ τ ∂(volume.restrict (Iio T)),
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) = q₀ (x, τ) :=
    Measure.ae_ae_of_ae_prod hq₀eq'
  have hslice' : ∀ᵐ τ ∂(volume.restrict (Iio T)),
      ∀ᵐ x ∂(volume : Measure (Vec m)), q₀ (x, τ) = 0 := by
    filter_upwards [hslice, htimeouter] with τ hτ1 hτ2
    filter_upwards [hτ1, hτ2] with x hx1 hx2
    rw [← hx2]
    exact hx1
  have hq₀measurable : Measurable q₀ := hq₀meas.measurable
  have hMeas : MeasurableSet {z : Vec m × ℝ | q₀ z = 0} :=
    hq₀measurable (measurableSet_singleton (0 : ℝ))
  have hspaceouter : ∀ᵐ x ∂(volume : Measure (Vec m)),
      ∀ᵐ τ ∂(volume.restrict (Iio T)), q₀ (x, τ) = 0 := by
    have hcomm := Measure.ae_ae_comm
      (μ := (volume : Measure (Vec m))) (ν := volume.restrict (Iio T))
      (p := fun (x : Vec m) (τ : ℝ) => q₀ (x, τ) = 0)
      (by
        have hset : {w : Vec m × ℝ | q₀ (w.1, w.2) = 0} = {z : Vec m × ℝ | q₀ z = 0} := by
          ext w; simp
        rw [hset]
        exact hMeas)
    exact hcomm.mpr hslice'
  have hprod0 : ∀ᵐ z ∂((volume : Measure (Vec m)).prod (volume.restrict (Iio T))), q₀ z = 0 :=
    (Measure.ae_prod_iff_ae_ae hMeas).mpr hspaceouter
  have heq : (volume : Measure (Vec m)).prod (volume.restrict (Iio T)) =
      volume.restrict (univ ×ˢ Iio T) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  rw [heq] at hprod0
  have hqeq : q =ᵐ[volume.restrict (univ ×ˢ Iio T)] q₀ := by
    rwa [heq] at hq₀eq
  filter_upwards [hqeq, hprod0] with z hz1 hz2
  rw [hz1]
  exact hz2

/-- Ancient vanishing, first conjunct of `CIV.comparisonAncient`. Given the comparison
monotonicity conclusion (the `L^∞` norm of a later slice is bounded by an earlier one, almost
everywhere) together with the stated `L^∞` decay as the reference time recedes to `-∞`, `q`
vanishes almost everywhere on `Vec m × Iio T`. -/
theorem ancientVanishing_ae_eq_zero {m : ℕ} {T : ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m (Iio T) q)
    (C κ : ℝ) (hκ : 0 < κ)
    (hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1) T))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ ENNReal.ofReal (C * |τ| ^ (-κ)))
    (hcomp : ∀ᵐ τ₀ ∂(volume.restrict (Iio T)), ∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume) :
    ∀ᵐ z ∂(volume.restrict (univ ×ˢ Iio T)), q z = 0 := by
  have hslice0 : ∀ᵐ τ ∂(volume.restrict (Iio T)), eLpNorm (fun x => q (x, τ)) ⊤ volume = 0 :=
    eLpNorm_slice_eq_zero_ae C κ hκ hdecay hcomp
  have hslicemeas := hq.ae_slice_measurable
  have hslice : ∀ᵐ τ ∂(volume.restrict (Iio T)), (fun x : Vec m => q (x, τ)) =ᵐ[volume] 0 := by
    filter_upwards [hslice0, hslicemeas] with τ hτ0 hτmeas
    rw [eLpNorm_exponent_top hτmeas, eLpNormEssSup_eq_zero_iff] at hτ0
    exact hτ0
  exact ae_zero_prod_of_ae_slice_zero hq hslice

/-- Ancient vanishing, second conjunct of `CIV.comparisonAncient`. Given that `q` vanishes
almost everywhere on `univ ×ˢ Iio T`, any continuous representative `q'` on `V ∩ univ ×ˢ Iic T`
that agrees with `q` almost everywhere on the open set `V ∩ univ ×ˢ Iio T` vanishes at *every*
point of the closed set `V ∩ univ ×ˢ Iic T`: the open set is dense in the closed one (every point
with `τ = T` is a limit of points with `τ < T`), so the almost-everywhere vanishing upgrades to
everywhere vanishing by continuity, including at the endpoint `τ = T`. -/
theorem ancientVanishing_continuousOn_eq_zero {m : ℕ} {T : ℝ} {q : Vec m × ℝ → ℝ}
    (hzero : ∀ᵐ z ∂(volume.restrict (univ ×ˢ Iio T)), q z = 0)
    {V : Set (Vec m × ℝ)} {q' : Vec m × ℝ → ℝ} (hV : IsOpen V)
    (hcont : ContinuousOn q' (V ∩ univ ×ˢ Iic T))
    (heqOn : ∀ᵐ z ∂(volume.restrict (V ∩ univ ×ˢ Iio T)), q' z = q z) :
    ∀ z ∈ V ∩ univ ×ˢ Iic T, q' z = 0 := by
  set W : Set (Vec m × ℝ) := V ∩ univ ×ˢ Iio T with hWdef
  set D : Set (Vec m × ℝ) := V ∩ univ ×ˢ Iic T with hDdef
  have hWD : W ⊆ D := by
    rintro z ⟨hzV, -, hzT⟩
    exact ⟨hzV, mem_univ _, mem_Iic.mpr (le_of_lt (mem_Iio.mp hzT))⟩
  have hWopen : IsOpen W := hV.inter (isOpen_univ.prod isOpen_Iio)
  have hzeroW : ∀ᵐ z ∂(volume.restrict W), q z = 0 := by
    have hsub : W ⊆ univ ×ˢ Iio T := fun z hz => hz.2
    exact ae_restrict_of_ae_restrict_of_subset hsub hzero
  have hq'zeroW : ∀ᵐ z ∂(volume.restrict W), q' z = 0 := by
    filter_upwards [heqOn, hzeroW] with z hz1 hz2
    rw [hz1, hz2]
  have hDWnull : volume (D \ W) = 0 := by
    have hsubset : D \ W ⊆ univ ×ˢ ({T} : Set ℝ) := by
      rintro z ⟨⟨hzV, -, hzTle⟩, hzW⟩
      refine ⟨mem_univ _, ?_⟩
      rcases lt_or_eq_of_le (mem_Iic.mp hzTle) with hlt | heq
      · exact absurd ⟨hzV, mem_univ _, mem_Iio.mpr hlt⟩ hzW
      · exact heq
    have hnull : volume (univ ×ˢ ({T} : Set ℝ) : Set (Vec m × ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    exact measure_mono_null hsubset hnull
  have hDmeas : MeasurableSet D :=
    hV.measurableSet.inter (MeasurableSet.univ.prod measurableSet_Iic)
  have hWmeas : MeasurableSet W :=
    hV.measurableSet.inter (MeasurableSet.univ.prod measurableSet_Iio)
  have hq'zeroD : ∀ᵐ z ∂(volume.restrict D), q' z = 0 := by
    rw [ae_restrict_iff' hDmeas]
    have h1 : ∀ᵐ z ∂volume, z ∈ W → q' z = 0 := (ae_restrict_iff' hWmeas).mp hq'zeroW
    have h2 : ∀ᵐ z ∂volume, z ∈ D → z ∈ W := by
      rw [ae_iff]
      have hsub2 : {z | ¬(z ∈ D → z ∈ W)} ⊆ D \ W := by
        rintro z hz
        by_contra hz'
        apply hz
        intro hzD
        by_contra hzW
        exact hz' ⟨hzD, hzW⟩
      exact measure_mono_null hsub2 hDWnull
    filter_upwards [h1, h2] with z hz1 hz2 hzD
    exact hz1 (hz2 hzD)
  have hDsubclosureW : D ⊆ closure (interior D) := by
    have hWinterior : W ⊆ interior D := interior_maximal hWD hWopen
    refine Subset.trans ?_ (closure_mono hWinterior)
    intro z hz
    obtain ⟨hzV, -, hzTle⟩ := hz
    rcases lt_or_eq_of_le (mem_Iic.mp hzTle) with hlt | heq
    · exact subset_closure ⟨hzV, mem_univ _, mem_Iio.mpr hlt⟩
    · have hseqsnd : Filter.Tendsto (fun n : ℕ => T - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds T) := by
        have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have := h0.const_sub T
        simpa using this
      have hseq : Filter.Tendsto (fun n : ℕ => ((z.1, T - 1 / ((n : ℝ) + 1)) : Vec m × ℝ))
          Filter.atTop (nhds (z.1, T)) :=
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds hseqsnd
      have hzeq : z = (z.1, T) := by
        apply Prod.ext
        · rfl
        · exact heq
      rw [hzeq]
      refine mem_closure_of_tendsto hseq ?_
      have hmemV : ∀ᶠ n : ℕ in Filter.atTop, (z.1, T - 1 / ((n : ℝ) + 1)) ∈ V := by
        have : V ∈ nhds ((z.1, T) : Vec m × ℝ) := hV.mem_nhds (hzeq ▸ hzV)
        exact hseq.eventually_mem this
      filter_upwards [hmemV] with n hn
      refine ⟨hn, mem_univ _, mem_Iio.mpr ?_⟩
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith only [hpos]
  have hq'zeroD' : q' =ᵐ[volume.restrict D] (0 : Vec m × ℝ → ℝ) := by
    filter_upwards [hq'zeroD] with z hz
    simpa using hz
  have hcontD : ContinuousOn q' D := hcont
  have hcont0 : ContinuousOn (fun _ : Vec m × ℝ => (0:ℝ)) D := continuousOn_const
  have hEqOn : Set.EqOn q' (fun _ : Vec m × ℝ => (0:ℝ)) D :=
    Measure.eqOn_of_ae_eq hq'zeroD' hcontD hcont0 hDsubclosureW
  intro z hz
  exact hEqOn hz

end CIV
