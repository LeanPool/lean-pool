/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Background.InvariantHahnBanach
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Separation.CompletelyRegular


/-!
# An exotic invariant mean on periodic `L^∞` functions (Lemma 3.2)

**Lemma 3.2** (`lem:exotic-mean`). Let `L^∞_per` be the space of `1`-periodic elements of
`L^∞(ℝ; ℝ)`. There exists a linear map `m : L^∞_per → ℝ` such that
* (a) `m(f) ≥ 0` whenever `f ≥ 0` almost everywhere, and `m(1) = 1`;
* (b) `m(f(· - a)) = m(f)` for all `f ∈ L^∞_per` and `a ∈ ℝ`;
* (c) `m(f) ≠ ∫_0^1 f(s) ds` for some `f ∈ L^∞_per`.

The paper quotes this classical fact from the literature; here it is proved. The final
statement is `ExoticMean.exotic_mean`.

## Proof

Let `V ⊆ L^∞_per` be the subspace of functions vanishing a.e. on some open dense set.
The constants are at distance `|c|` from `V` (`constant_separation`). A Hahn–Banach
argument combined with finite Cesàro averages of translations
(`ALCS/Background/InvariantHahnBanach.lean`) gives a translation-invariant functional `m`
of norm `≤ 1` with `m(1) = 1` and `m = 0` on `V` (`exists_strong_mean`); positivity
follows from `‖m‖ ≤ 1` and `m(1) = 1`. For (c), take the indicator of a periodic open
dense set of small measure (`exists_small_periodic_open`): its mean is `1` while its
integral over a period is `< 1/2`.

## Formalization choices

* `L^∞_per` (`LinftyPer`) is the subspace of `L^∞(ℝ)` fixed by the translation by `1`;
  translations act on a.e. classes (`shift`, `translate`).
* Positivity (`Positive`) is an a.e. property of the class, not of a representative.
* `exists_strong_mean` proves more than needed (vanishing on `V`); this extra property is
  used in Proposition 3.3 and does not appear in the statement of `exotic_mean`.
-/

namespace AbstractLinearControl

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ExoticMean

local instance : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩

/-! ## Generic `L^∞` helpers (also used in Proposition 3.3) -/

lemma linfty_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  have htop : eLpNorm (⇑f) ∞ μ = eLpNormEssSup (⇑f) μ :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable f)
  rw [Lp.norm_def, htop]
  calc
    (eLpNormEssSup (⇑f) μ).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hf)
    _ = C := ENNReal.toReal_ofReal hC

lemma linfty_ae_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have htop : eLpNorm (⇑f) ∞ μ = eLpNormEssSup (⇑f) μ :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable f)
  have hfinite : eLpNormEssSup (⇑f) μ ≠ ∞ := by
    rw [← htop]
    exact Lp.eLpNorm_ne_top f
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑f) μ] with x hx
  have h := ENNReal.toReal_mono hfinite hx
  simpa only [Lp.norm_def, htop, toReal_enorm] using h

/-- A constant is in L∞ even if the underlying measure has infinite mass. -/
def linftyConst {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ) :
    Lp ℝ ∞ μ :=
  (memLp_top_of_bound stronglyMeasurable_const.aestronglyMeasurable ‖c‖
    (Eventually.of_forall (fun _ => le_rfl))).toLp (fun _ => c)

lemma linftyConst_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ) :
    ⇑(linftyConst μ c) =ᵐ[μ] fun _ => c :=
  MemLp.coeFn_toLp _

/-- A measurable indicator, as an actual L∞ equivalence class. -/
def linftyIndicator {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound
    (stronglyMeasurable_const.indicator hs).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      by_cases hx : x ∈ s <;> simp [Set.indicator, hx]))).toLp
      (s.indicator (fun _ => (1 : ℝ)))

lemma linftyIndicator_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) :
    ⇑(linftyIndicator μ s hs) =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

/-! ## Translations and periodic functions -/

/-- `L^∞(ℝ)`. -/
abbrev Ambient := Lp ℝ ∞ (volume : Measure ℝ)

/-- `shift a f` is the a.e. class of `r ↦ f (r-a)`. -/
def shift (a : ℝ) : Ambient →ₗ[ℝ] Ambient :=
  Lp.compMeasurePreservingₗ ℝ (fun r : ℝ => -a + r)
    (measurePreserving_add_left (volume : Measure ℝ) (-a))

lemma shift_ae (a : ℝ) (f : Ambient) :
    ⇑(shift a f) =ᵐ[volume] fun r => f (-a + r) :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_left (volume : Measure ℝ) (-a))

lemma shift_zero (f : Ambient) : shift 0 f = f := by
  apply Lp.ext
  filter_upwards [shift_ae 0 f] with r hr
  simpa using hr

lemma shift_add (a b : ℝ) (f : Ambient) :
    shift (a + b) f = shift a (shift b f) := by
  apply Lp.ext
  have hab := (measurePreserving_add_left (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae
      (shift_ae b f)
  filter_upwards [shift_ae (a + b) f, shift_ae a (shift b f), hab] with r h1 h2 h3
  rw [h1, h2, h3]
  congr 1
  ring

lemma shift_commute (a b : ℝ) (f : Ambient) :
    shift a (shift b f) = shift b (shift a f) := by
  rw [← shift_add, ← shift_add, add_comm a b]

lemma norm_shift (a : ℝ) (f : Ambient) : ‖shift a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f
    (measurePreserving_add_left (volume : Measure ℝ) (-a))

/-- `L^∞_per`: the subspace of `L^∞(ℝ)` fixed by the translation by `1`, i.e. the a.e.
`1`-periodic functions. (This avoids choosing periodic representatives.) -/
def periodicSubspace : Submodule ℝ Ambient where
  carrier := {f | shift 1 f = f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change shift 1 (f + g) = f + g
    rw [map_add, hf, hg]
  smul_mem' := by
    intro c f hf
    change shift 1 (c • f) = c • f
    rw [map_smul, hf]

/-- Almost-everywhere periodic bounded functions, with their inherited norm. -/
abbrev LinftyPer := periodicSubspace

/-- The real-translation action on the periodic subspace. -/
def translate (a : ℝ) : LinftyPer →ₗ[ℝ] LinftyPer where
  toFun f := ⟨shift a f.val, by
    change shift 1 (shift a f.val) = shift a f.val
    rw [shift_commute, f.property]⟩
  map_add' := by intros; apply Subtype.ext; apply map_add
  map_smul' := by intros; apply Subtype.ext; apply map_smul

lemma translate_ae (a : ℝ) (f : LinftyPer) :
    ⇑((translate a f).val) =ᵐ[volume] fun r => f.val (r - a) := by
  simpa [translate, sub_eq_add_neg, add_comm] using shift_ae a f.val

lemma translate_zero (f : LinftyPer) : translate 0 f = f :=
  Subtype.ext (shift_zero f.val)

lemma translate_add (a b : ℝ) (f : LinftyPer) :
    translate (a + b) f = translate a (translate b f) :=
  Subtype.ext (shift_add a b f.val)

lemma norm_translate (a : ℝ) (f : LinftyPer) : ‖translate a f‖ = ‖f‖ :=
  norm_shift a f.val

lemma shift_const (a c : ℝ) : shift a (linftyConst volume c) = linftyConst volume c := by
  apply Lp.ext
  have hc := (measurePreserving_add_left (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae
      (linftyConst_ae volume c)
  filter_upwards [shift_ae a (linftyConst volume c), linftyConst_ae volume c, hc]
    with r hr h1 h2
  exact hr.trans (h2.trans h1.symm)

/-- The periodic class of the constant one function. -/
def one : LinftyPer := ⟨linftyConst volume 1, shift_const 1 1⟩

lemma one_ae : ⇑one.val =ᵐ[volume] fun _ => (1 : ℝ) := linftyConst_ae volume 1

lemma translate_one (a : ℝ) : translate a one = one :=
  Subtype.ext (shift_const a 1)

/-- The ordinary Lebesgue integral over `[0,1]`.
`Ioc` is the usual set-integral implementation of the interval integral;
changing either endpoint does not change an integral for Lebesgue measure. -/
def integral01 (f : LinftyPer) : ℝ := ∫ r in Ioc (0 : ℝ) 1, f.val r

/-- Positivity is explicitly an a.e. property, not pointwise positivity of
Mathlib's arbitrarily chosen `Lp` representative. -/
def Positive (m : LinftyPer →ₗ[ℝ] ℝ) : Prop :=
  ∀ f, (∀ᵐ r ∂volume, 0 ≤ f.val r) → 0 ≤ m f

/-! ## The open-dense vanishing subspace -/

private lemma dense_inter_open {s t : Set ℝ}
    (hs : IsOpen s) (hds : Dense s) (hdt : Dense t) : Dense (s ∩ t) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hx⟩ := hdt.inter_open_nonempty (U ∩ s) (hU.inter hs)
    (hds.inter_open_nonempty U hU hUne)
  exact ⟨x, hx.1.1, hx.1.2, hx.2⟩

/-- The subspace `V` of periodic functions vanishing a.e. on some open dense set. -/
def vanishingOnDenseOpen : Submodule ℝ LinftyPer where
  carrier := {f | ∃ O : Set ℝ, IsOpen O ∧ Dense O ∧
    ∀ᵐ r ∂volume, r ∈ O → f.val r = 0}
  zero_mem' := by
    refine ⟨univ, isOpen_univ, dense_univ, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ ∞ (volume : Measure ℝ)] with r hr
    intro _
    exact hr
  add_mem' := by
    rintro f g ⟨O, hOo, hOd, hf⟩ ⟨P, hPo, hPd, hg⟩
    refine ⟨O ∩ P, hOo.inter hPo, dense_inter_open hOo hOd hPd, ?_⟩
    filter_upwards [hf, hg, Lp.coeFn_add f.val g.val] with r hfr hgr hsum
    intro hr
    change (f.val + g.val) r = 0
    simpa [hfr hr.1, hgr hr.2] using hsum
  smul_mem' := by
    rintro c f ⟨O, hOo, hOd, hf⟩
    refine ⟨O, hOo, hOd, ?_⟩
    filter_upwards [hf, Lp.coeFn_smul c f.val] with r hfr hsmul
    intro hr
    change (c • f.val) r = 0
    simpa [hfr hr] using hsmul

lemma translate_mem_vanishing (a : ℝ) (f : LinftyPer)
    (hf : f ∈ vanishingOnDenseOpen) : translate a f ∈ vanishingOnDenseOpen := by
  obtain ⟨O, hOo, hOd, hf⟩ := hf
  let P : Set ℝ := (fun r : ℝ => -a + r) ⁻¹' O
  have hPo : IsOpen P := hOo.preimage (continuous_const.add continuous_id)
  have hPd : Dense P := by
    rw [dense_iff_inter_open]
    intro U hU hUne
    have himage : IsOpen ((fun r : ℝ => -a + r) '' U) :=
      isOpenMap_add_left (-a) U hU
    obtain ⟨y, hy⟩ := hOd.inter_open_nonempty _ himage (hUne.image _)
    obtain ⟨r, hrU, rfl⟩ := hy.1
    exact ⟨r, hrU, hy.2⟩
  refine ⟨P, hPo, hPd, ?_⟩
  have hshift := (measurePreserving_add_left (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae hf
  filter_upwards [shift_ae a f.val, hshift] with r hr hfr
  intro hrP
  exact hr.trans (hfr hrP)

lemma constant_separation (c : ℝ) (v : LinftyPer)
    (hv : v ∈ vanishingOnDenseOpen) : |c| ≤ ‖c • one + v‖ := by
  obtain ⟨O, hOo, hOd, hv⟩ := hv
  have hgood : ∀ᵐ r ∂volume, r ∈ O → |c| ≤ ‖c • one + v‖ := by
    filter_upwards [hv, one_ae, Lp.coeFn_smul c one.val,
      Lp.coeFn_add (c • one.val) v.val,
      linfty_ae_norm_le ((c • one + v).val)] with r hvr h1 hc hsum hbound
    intro hrO
    have heq : (c • one + v).val r = c := by
      change (c • one.val + v.val) r = c
      simp only [Pi.add_apply] at hsum
      simp only [Pi.smul_apply] at hc
      rw [hsum, hc, h1, hvr hrO]
      simp
    change |c| ≤ ‖(c • one + v).val‖
    simpa only [heq, Real.norm_eq_abs] using hbound
  obtain ⟨r, hr⟩ := (Measure.dense_of_ae hgood).inter_open_nonempty O hOo hOd.nonempty
  exact hr.2 hr.1

/-- Positivity follows from normalization and the norm bound, with the
unscaled argument `‖f‖ 1 - f`; this also handles `f = 0`. -/
lemma positive_of_norm_le_one (m : LinftyPer →L[ℝ] ℝ)
    (hm : ‖m‖ ≤ 1) (h1 : m one = 1) : Positive m.toLinearMap := by
  intro f hf
  have hnorm : ‖‖f‖ • one - f‖ ≤ ‖f‖ := by
    apply linfty_norm_le (‖f‖ • one - f).val (norm_nonneg f)
    filter_upwards [hf, linfty_ae_norm_le f.val, one_ae,
      Lp.coeFn_smul ‖f‖ one.val,
      Lp.coeFn_sub (‖f‖ • one.val) f.val] with r hfr hbr h1r hsmul hsub
    change ‖(‖f‖ • one.val - f.val) r‖ ≤ ‖f‖
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.smul_apply] at hsmul
    rw [hsub, hsmul, h1r]
    simp only [smul_eq_mul, mul_one, Real.norm_eq_abs]
    change |f.val r| ≤ ‖f‖ at hbr
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hbr).2], by linarith⟩
  have hmap : m (‖f‖ • one - f) = ‖f‖ - m f := by
    rw [map_sub, map_smul, h1]
    simp
  have hbound : ‖m (‖f‖ • one - f)‖ ≤ ‖f‖ :=
    (m.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans
      (by simpa using hnorm))
  rw [hmap, Real.norm_eq_abs] at hbound
  have h := (abs_le.mp hbound).2
  change 0 ≤ m f
  linarith

/-- The invariant mean, with the extra property that it vanishes on functions vanishing
a.e. on an open dense set (used in Proposition 3.3). -/
theorem exists_strong_mean :
    ∃ m : LinftyPer →L[ℝ] ℝ,
      ‖m‖ ≤ 1 ∧ Positive m.toLinearMap ∧ m one = 1 ∧
      (∀ a f, m (translate a f) = m f) ∧
      ∀ v ∈ vanishingOnDenseOpen, m v = 0 := by
  let R : HahnBanach.Action LinftyPer :=
    { T := translate
      zero_apply := translate_zero
      add_apply := translate_add
      bound := fun a f => (norm_translate a f).le }
  obtain ⟨m, hm, h1, hV, hT⟩ :=
    HahnBanach.exists_invariant_extension R one vanishingOnDenseOpen
      translate_one translate_mem_vanishing constant_separation
  exact ⟨m, hm, positive_of_norm_le_one m hm h1, h1, hT, hV⟩

/-! ## Small periodic open dense sets -/

/-- A Borel set with the exact period needed for the indicator class. -/
structure PeriodicSet where
  /-- The measurable periodic subset of the real line. -/
  carrier : Set ℝ
  measurable : MeasurableSet carrier
  period : ∀ r : ℝ, -1 + r ∈ carrier ↔ r ∈ carrier

namespace PeriodicSet

/-- The periodic indicator as an almost-everywhere bounded-function class. -/
def indicator (O : PeriodicSet) : LinftyPer :=
  ⟨linftyIndicator volume O.carrier O.measurable, by
    apply Lp.ext
    have hs := (measurePreserving_add_left (volume : Measure ℝ) (-1)).quasiMeasurePreserving.ae
        (linftyIndicator_ae volume O.carrier O.measurable)
    filter_upwards [shift_ae 1 (linftyIndicator volume O.carrier O.measurable),
      linftyIndicator_ae volume O.carrier O.measurable, hs] with r h1 h2 h3
    rw [h1, h2, h3]
    by_cases hr : r ∈ O.carrier
    · simp [Set.indicator, hr, (O.period r).mpr hr]
    · have hr' : -1 + r ∉ O.carrier := fun h => hr ((O.period r).mp h)
      simp [Set.indicator, hr, hr']⟩

lemma indicator_ae (O : PeriodicSet) :
    ⇑O.indicator.val =ᵐ[volume] O.carrier.indicator (fun _ => (1 : ℝ)) :=
  linftyIndicator_ae volume O.carrier O.measurable

lemma mean_indicator (m : LinftyPer →L[ℝ] ℝ) (h1 : m one = 1)
    (hV : ∀ v ∈ vanishingOnDenseOpen, m v = 0)
    (O : PeriodicSet) (hOo : IsOpen O.carrier) (hOd : Dense O.carrier) :
    m O.indicator = 1 := by
  have hv : one - O.indicator ∈ vanishingOnDenseOpen := by
    refine ⟨O.carrier, hOo, hOd, ?_⟩
    filter_upwards [one_ae, O.indicator_ae,
      Lp.coeFn_sub one.val O.indicator.val] with r h1r hOr hsub
    intro hr
    change (one.val - O.indicator.val) r = 0
    simp only [Pi.sub_apply] at hsub
    rw [hsub, h1r, hOr]
    simp [hr]
  have h := hV (one - O.indicator) hv
  rw [map_sub, h1] at h
  linarith

lemma integral_indicator (O : PeriodicSet) :
    integral01 O.indicator = (volume (O.carrier ∩ Ioc (0 : ℝ) 1)).toReal := by
  unfold integral01
  rw [integral_congr_ae (ae_restrict_of_ae O.indicator_ae)]
  rw [MeasureTheory.integral_indicator O.measurable]
  simp [Measure.real, Measure.restrict_apply, O.measurable]

end PeriodicSet

/-- A general topological observation: the inverse image of a dense set
under an open map is dense. Surjectivity is not needed for this assertion. -/
private lemma dense_preimage_of_open {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsOpenMap q) {s : Set β} (hs : Dense s) :
    Dense (q ⁻¹' s) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨y, hy⟩ := hs.inter_open_nonempty (q '' U) (hq U hU) (hUne.image q)
  obtain ⟨x, hx, rfl⟩ := hy.1
  exact ⟨x, hx, hy.2⟩

/-- Outer regularity around a countable dense null set gives a small open
dense set on the circle; pulling it back makes it genuinely periodic. -/
theorem exists_small_periodic_open (ε : ℝ) (hε : 0 < ε) :
    ∃ O : PeriodicSet, IsOpen O.carrier ∧ Dense O.carrier ∧
      (volume (O.carrier ∩ Ioc (0 : ℝ) 1)).toReal < ε := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let _ : NullSingletonClass (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨fun x => by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (AddCircle (1 : ℝ))
  have hD0 : (volume : Measure (AddCircle (1 : ℝ))) D = 0 := hDc.measure_zero _
  obtain ⟨U, hDU, hUo, hUμ⟩ :=
    D.exists_isOpen_lt_of_lt (μ := (volume : Measure (AddCircle (1 : ℝ))))
      (ENNReal.ofReal ε) (by rw [hD0]; exact ENNReal.ofReal_pos.mpr hε)
  have hUd : Dense U := Dense.mono hDU hDd
  let q : ℝ → AddCircle (1 : ℝ) := fun r => (r : AddCircle (1 : ℝ))
  have hq : Continuous q := AddCircle.continuous_mk' 1
  have hqo : IsOpenMap q := QuotientAddGroup.isOpenMap_coe
  let O : PeriodicSet :=
    { carrier := q ⁻¹' U
      measurable := (hUo.preimage hq).measurableSet
      period := by
        intro r
        have heq : q (-1 + r) = q r := by
          change ((-1 + r : ℝ) : AddCircle (1 : ℝ)) = (r : AddCircle (1 : ℝ))
          rw [AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_period]
          simp
        change q (-1 + r) ∈ U ↔ q r ∈ U
        rw [heq] }
  refine ⟨O, hUo.preimage hq, dense_preimage_of_open hqo hUd, ?_⟩
  have hμ : volume (O.carrier ∩ Ioc (0 : ℝ) 1) =
      (volume : Measure (AddCircle (1 : ℝ))) U := by
    simpa [O, q] using (AddCircle.add_projection_respects_measure 1 0
      hUo.measurableSet).symm
  rw [hμ]
  have hfin : (volume : Measure (AddCircle (1 : ℝ))) U ≠ ∞ :=
    ne_top_of_lt (hUμ.trans ENNReal.ofReal_lt_top)
  have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hUμ
  simpa [ENNReal.toReal_ofReal hε.le] using h

/-! ## Lemma 3.2 -/

/-- **Lemma 3.2** (`lem:exotic-mean`). There is a linear map `m : L^∞_per → ℝ` which is
(a) positive and normalized, (b) invariant under every real translation, and
(c) different from the Lebesgue integral over a period. -/
theorem exotic_mean :
    ∃ m : LinftyPer →ₗ[ℝ] ℝ,
      (Positive m ∧ m one = 1) ∧
      (∀ (f : LinftyPer) (a : ℝ), m (translate a f) = m f) ∧
      ∃ f : LinftyPer, m f ≠ integral01 f := by
  obtain ⟨m, hm, hpos, h1, hT, hV⟩ := exists_strong_mean
  obtain ⟨O, hOo, hOd, hOμ⟩ := exists_small_periodic_open (1 / 2) (by norm_num)
  refine ⟨m.toLinearMap, ⟨hpos, h1⟩, fun f a => hT a f, O.indicator, ?_⟩
  have hmean := O.mean_indicator m h1 hV hOo hOd
  have hint := O.integral_indicator
  change m O.indicator ≠ integral01 O.indicator
  rw [hmean, hint]
  linarith

end ExoticMean

end
end

end AbstractLinearControl
