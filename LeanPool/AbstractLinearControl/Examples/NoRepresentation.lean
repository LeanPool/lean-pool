/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Definitions
public import LeanPool.AbstractLinearControl.Examples.Periodization


/-!
# A system without integral representation (Proposition 3.3)

**Proposition 3.3** (`prop:no-representation`). There exists an abstract linear control
system `(𝕋, Φ)` with `p = ∞`, `X = U = ℝ` and `𝕋_t = Id` for all `t ≥ 0`, such that
* (i) `κ(t) = t` for every `t ≥ 0`;
* (ii) `(𝕋, Φ)` admits no integral representation;
* (iii) `(𝕋, Φ)` is not `E_F`-admissible, for any Young function `F`.

The final statement is `ExoticMean.Counterexample.no_representation`.

## Proof

* Steps 1–2 (`exists_local_control_from_mean`, using `ALCS/Examples/Periodization.lean`):
  with the exotic mean `m` of Lemma 3.2, `J = m ∘ P` and `Φ_t u = J(1_{(0,t]} u)`.
* Step 3 (`LocalControlData.smallIndicators`): for a periodic open dense set `O` of small
  measure, `m(1_O) = 1` while `|O ∩ (0, 1]|` is small. (The paper uses a set `E` with
  `J(1_E) ≠ |E|`; here the mean vanishes on functions vanishing on an open dense set,
  which directly gives inputs of small support with output `1`.)
* Steps 4–5 (`not_integral_of_smallIndicators`, `not_EF_of_smallIndicators`).

## Formalization choices

* Since `A = 0`, the extrapolation space `X_{-1}` is `ℝ`, so an integral representation
  (`eq:representation`) is given by a real bounded operator `B` (`HasIntegralRepresentation`).
* `YoungFunction` only records `F(0) = 0`, nonnegativity, convexity, continuity and growth
  at infinity: it contains all Young functions of the paper, so (iii) is proved for a
  larger class. The Luxemburg norm `luxemburg` is defined by its infimum formula.
* `EFAdmissible` asks for `eq:orlicz` at all times `t ≥ 0`, for inputs whose modular is
  finite (which is automatic for `L^∞` inputs and finite-valued `F`).
* Intervals `[0, t)` of the paper become `(0, t]`, which only changes null sets.
-/

namespace AbstractLinearControl

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace ExoticMean.Counterexample

local instance : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩

/-- Bounded scalar inputs on the nonnegative half-line. -/
abbrev Input := Lp ℝ ∞ muPlus
/-- Scalar-state, scalar-input systems with bounded inputs. -/
abbrev ScalarSystem := ALCS ℝ ℝ ℝ ∞

/-- The constant unit input. -/
def inputOne : Input := linftyConst muPlus 1

/-- The input represented by the indicator of a measurable set. -/
def inputIndicator (A : Set ℝ) (hA : MeasurableSet A) : Input :=
  linftyIndicator muPlus A hA

/-- The choice `(0,1]` rather than `[0,1)` changes only null endpoints. -/
def cell : Set ℝ := Ioc 0 1

lemma cell_measurable : MeasurableSet cell := measurableSet_Ioc

lemma cell_subset_halfline : cell ⊆ Ici (0 : ℝ) := fun _ hx => hx.1.le

lemma inputOne_norm_le : ‖inputOne‖ ≤ 1 := by
  apply linfty_norm_le inputOne (by norm_num)
  filter_upwards [linftyConst_ae muPlus 1] with r hr
  simp [inputOne, hr]

lemma ae_on_cell {p : ℝ → Prop} (hp : ∀ᵐ r ∂muPlus, p r) :
    ∀ᵐ r ∂volume.restrict cell, p r := by
  have h := (ae_restrict_iff' (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))).mp hp
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem cell_measurable] with r hr hrC
  exact hr (cell_subset_halfline hrC)

lemma cell_measure_ne_top : volume cell ≠ ∞ := by
  simp [cell, Real.volume_Ioc]

lemma measure_ne_top_of_subset_cell {A : Set ℝ} (hA : A ⊆ cell) : volume A ≠ ∞ :=
  ne_top_of_le_ne_top cell_measure_ne_top (measure_mono hA)

lemma inputIndicator_integral {A : Set ℝ} (hA : MeasurableSet A) (hAC : A ⊆ cell) :
    (∫ r in cell, inputIndicator A hA r) = (volume A).toReal := by
  unfold inputIndicator
  rw [integral_congr_ae (ae_on_cell (linftyIndicator_ae muPlus A hA))]
  rw [MeasureTheory.integral_indicator hA]
  simp [Measure.real, Measure.restrict_apply, hA, inter_eq_left.mpr hAC]

/-! ## Step 2: the input maps `Φ_t u = J(1_{(0,t]} u)` -/

/-- The periodization `r ↦ Σ_{k ∈ ℤ} (1_{(0,t]} u)(r + k)` (raw formula). -/
def rawPeriodization (t : ℝ) (u : Input) (r : ℝ) : ℝ :=
  ∑' k : ℤ, (Ioc (0 : ℝ) t).indicator (fun s => u s) (r + (k : ℝ))

/-- The input maps `Φ_t u = m(P(1_{(0,t]} u))` of Step 2, before packaging as continuous
linear maps, together with the properties used in Steps 3–5. They are constructed in
`exists_local_control_from_mean`. -/
structure LocalControlData (m : LinftyPer →L[ℝ] ℝ) where
  /-- The response at each time, before its continuity bound is bundled. -/
  out : ℝ → Input →ₗ[ℝ] ℝ
  /-- The exact formula `m(P(1_(0,t] u))`, on a.e. classes. -/
  formula : ∀ t, 0 ≤ t → ∀ u,
    ∃ g : LinftyPer, (⇑g.val =ᵐ[volume] rawPeriodization t u) ∧ out t u = m g
  bound : ∀ t, 0 ≤ t → ∀ u, ‖out t u‖ ≤ t * ‖u‖
  one_value : ∀ t, 0 ≤ t → out t inputOne = t
  composition : ∀ τ t, 0 ≤ τ → 0 ≤ t → ∀ u v w : Input,
    (⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) → out (τ + t) w = out τ u + out t v
  periodic_test : ∀ O : PeriodicSet,
    out 1 (inputIndicator (O.carrier ∩ cell) (O.measurable.inter cell_measurable)) =
      m O.indicator

private lemma input_ae_on_halfline {p : ℝ → Prop} (hp : ∀ᵐ r ∂muPlus, p r) :
    ∀ᵐ r ∂volume, 0 ≤ r → p r :=
  (ae_restrict_iff' (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))).mp hp

open Periodization

/-- The test function `1_{(0,t]} u` (built from the representative of `u`). -/
private def truncated (t : ℝ) (u : Input) : TestFunction :=
  supportedInterval 0 t (⇑u) (Lp.stronglyMeasurable u) ‖u‖ (norm_nonneg _)
    (by
      filter_upwards [input_ae_on_halfline (linfty_ae_norm_le u)] with r hr
      intro hrt
      exact hr hrt.1.le)

private lemma truncated_bound (t : ℝ) (u : Input) :
    ∀ᵐ r ∂volume, ‖(truncated t u).val r‖ ≤
      (Ioc (0 : ℝ) t).indicator (fun _ => ‖u‖) r := by
  filter_upwards [input_ae_on_halfline (linfty_ae_norm_le u)] with r hr
  change ‖(Ioc (0 : ℝ) t).indicator (⇑u) r‖ ≤ _
  by_cases h : r ∈ Ioc (0 : ℝ) t
  · simpa [h] using hr h.1.le
  · simp [h]

private lemma truncated_add (t : ℝ) (u v : Input) :
    periodize (truncated t (u + v)) =
      periodize (truncated t u) + periodize (truncated t v) := by
  apply periodize_add
  filter_upwards [input_ae_on_halfline (Lp.coeFn_add u v)] with r hr
  change (Ioc (0 : ℝ) t).indicator (⇑(u + v)) r =
    (Ioc (0 : ℝ) t).indicator (⇑u) r + (Ioc (0 : ℝ) t).indicator (⇑v) r
  by_cases h : r ∈ Ioc (0 : ℝ) t
  · simpa [h] using hr h.1.le
  · simp [h]

private lemma truncated_smul (t c : ℝ) (u : Input) :
    periodize (truncated t (c • u)) = c • periodize (truncated t u) := by
  apply periodize_smul
  filter_upwards [input_ae_on_halfline (Lp.coeFn_smul c u)] with r hr
  change (Ioc (0 : ℝ) t).indicator (⇑(c • u)) r =
    c * (Ioc (0 : ℝ) t).indicator (⇑u) r
  by_cases h : r ∈ Ioc (0 : ℝ) t
  · simpa [h] using hr h.1.le
  · simp [h]

private def localOutput (m : LinftyPer →L[ℝ] ℝ) (t : ℝ) : Input →ₗ[ℝ] ℝ where
  toFun u := m (periodize (truncated t u))
  map_add' := by intro u v; rw [truncated_add, map_add]
  map_smul' := by intro c u; rw [truncated_smul, map_smul]; rfl

/-- Steps 1–2 of the proof of Proposition 3.3: from a positive, normalized,
translation-invariant mean `m`, the maps `Φ_t u = J(1_{(0,t]} u)` satisfy the bound
`|Φ_t u| ≤ t ‖u‖`, `Φ_t 1 = t`, the composition property with `T = Id`, and recover `m`
on periodic indicators. -/
theorem exists_local_control_from_mean
    (m : LinftyPer →L[ℝ] ℝ) (hpos : Positive m.toLinearMap)
    (h1 : m one = 1) (hT : ∀ a f, m (translate a f) = m f) :
    Nonempty (LocalControlData m) := by
  refine ⟨{
    out := localOutput m
    formula := ?_
    bound := ?_
    one_value := ?_
    composition := ?_
    periodic_test := ?_ }⟩
  · intro t ht u
    exact ⟨periodize (truncated t u), (truncated t u).periodize_ae, rfl⟩
  · intro t ht u
    exact mean_support_bound m hpos h1 hT (truncated t u) 0 t ‖u‖ ht
      (norm_nonneg _) (truncated_bound t u) |>.trans_eq (by simp)
  · intro t ht
    change m (periodize (truncated t inputOne)) = t
    have heq : periodize (truncated t inputOne) = periodize (interval 0 t 1) := by
      apply periodize_congr
      filter_upwards [input_ae_on_halfline (linftyConst_ae muPlus 1)] with r hr
      change (Ioc (0 : ℝ) t).indicator (⇑inputOne) r =
        (Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) r
      by_cases h : r ∈ Ioc (0 : ℝ) t
      · simpa [h, inputOne] using hr h.1.le
      · simp [h]
    rw [heq, mean_interval m hpos h1 hT 0 t ht, sub_zero]
  · intro τ t hτ ht u v w hw
    change m (periodize (truncated (τ + t) w)) =
      m (periodize (truncated τ u)) + m (periodize (truncated t v))
    have heq : periodize (truncated (τ + t) w) =
        periodize (truncated τ u) + periodize (shifted τ (truncated t v)) := by
      apply periodize_add
      have hne : ∀ᵐ r : ℝ ∂volume, r ≠ τ := by
        exact ae_iff.mpr (by simp)
      filter_upwards [input_ae_on_halfline hw, hne] with r hr hne
      change (Ioc (0 : ℝ) (τ + t)).indicator (⇑w) r =
        (Ioc (0 : ℝ) τ).indicator (⇑u) r +
          (Ioc (0 : ℝ) t).indicator (⇑v) (-τ + r)
      by_cases h0 : 0 < r
      · have hwr := hr h0.le
        change w r = if r < τ then u r else v (r - τ) at hwr
        by_cases hτr : r < τ
        · have hleft : r ∈ Ioc (0 : ℝ) τ := ⟨h0, hτr.le⟩
          have hall : r ∈ Ioc (0 : ℝ) (τ + t) := ⟨h0, by linarith⟩
          have hoff : -τ + r ∉ Ioc (0 : ℝ) t := by intro h; linarith [h.1]
          simp [hleft, hall, hoff, hwr, hτr]
        · have hτlt : τ < r := lt_of_le_of_ne (not_lt.mp hτr) (Ne.symm hne)
          have hoff : r ∉ Ioc (0 : ℝ) τ := by intro h; linarith [h.2]
          have hiff : -τ + r ∈ Ioc (0 : ℝ) t ↔ r ∈ Ioc (0 : ℝ) (τ + t) := by
            constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
          simp only [Set.indicator, hoff, hiff, ite_false, zero_add]
          split_ifs with h
          · simpa [hτr, sub_eq_neg_add] using hwr
          · rfl
      · have hoff1 : r ∉ Ioc (0 : ℝ) (τ + t) := fun h => h0 h.1
        have hoff2 : r ∉ Ioc (0 : ℝ) τ := fun h => h0 h.1
        have hoff3 : -τ + r ∉ Ioc (0 : ℝ) t := by intro h; linarith [h.1]
        simp [hoff1, hoff2, hoff3]
    rw [heq, map_add, periodize_shifted, hT]
  · intro O
    let u := inputIndicator (O.carrier ∩ cell) (O.measurable.inter cell_measurable)
    change m (periodize (truncated 1 u)) = m O.indicator
    congr 1
    apply Subtype.ext
    apply Lp.ext
    have hcut : (truncated 1 u).val =ᵐ[volume]
        cell.indicator (O.carrier.indicator (fun _ => (1 : ℝ))) := by
      filter_upwards [input_ae_on_halfline
        (linftyIndicator_ae muPlus (O.carrier ∩ cell) (O.measurable.inter cell_measurable))]
        with r hr
      change cell.indicator (⇑u) r = _
      by_cases h : r ∈ cell
      · dsimp [u, inputIndicator]
        rw [indicator_of_mem h, hr (cell_subset_halfline h), indicator_of_mem h]
        by_cases hO : r ∈ O.carrier <;> simp [hO, h]
      · simp [h]
    have hp : Function.Periodic (O.carrier.indicator (fun _ => (1 : ℝ))) 1 := by
      have hmem : Function.Periodic (fun r : ℝ => r ∈ O.carrier) (-1) := by
        intro r
        exact propext (by simpa [add_comm] using O.period r)
      intro r
      have h : (r + 1 ∈ O.carrier) = (r ∈ O.carrier) := by simpa using hmem.neg r
      by_cases hr : r ∈ O.carrier
      · have hr' : r + 1 ∈ O.carrier := Eq.mp h.symm hr
        simp [Set.indicator, hr, hr']
      · have hr' : r + 1 ∉ O.carrier := fun hx => hr (Eq.mp h hx)
        simp [Set.indicator, hr, hr']
    filter_upwards [(truncated 1 u).periodize_ae, O.indicator_ae, ae_shifts hcut]
      with r hr hO hcut
    rw [hr, hO]
    unfold raw
    rw [tsum_congr hcut]
    exact raw_cell_recovery _ hp r

namespace LocalControlData

variable {m : LinftyPer →L[ℝ] ℝ} (D : LocalControlData m)

/-- Values at negative times are irrelevant to `ALCS`; set them to zero. -/
def phi (t : ℝ) : Input →L[ℝ] ℝ :=
  if ht : 0 ≤ t then (D.out t).mkContinuous t (D.bound t ht) else 0

lemma phi_apply (t : ℝ) (ht : 0 ≤ t) (u : Input) : D.phi t u = D.out t u := by
  simp [phi, ht]

/-- The system of Proposition 3.3: `T_t = Id` and the input maps of Step 2. -/
def system : ScalarSystem where
  T := fun _ => ContinuousLinearMap.id ℝ ℝ
  T_zero := rfl
  T_add := by intros; ext; rfl
  T_cont := by intro y; exact tendsto_const_nhds
  Φ := D.phi
  composition := by
    intro τ t hτ ht u v w hw
    change D.phi (τ + t) w = D.phi τ u + D.phi t v
    rw [D.phi_apply (τ + t) (add_nonneg hτ ht),
      D.phi_apply τ hτ, D.phi_apply t ht]
    exact D.composition τ t hτ ht u v w hw

lemma system_T (t : ℝ) : D.system.T t = ContinuousLinearMap.id ℝ ℝ := rfl

/-- Property (i) of Proposition 3.3: `κ(t) = ‖Φ t‖ = t`. The upper bound is `eq:J-bound`;
the constant input `1` attains it. -/
theorem kappa (t : ℝ) (ht : 0 ≤ t) : ‖D.system.Φ t‖ = t := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ ht
    intro u
    rw [show D.system.Φ t u = D.out t u from D.phi_apply t ht u]
    exact D.bound t ht u
  · have hone : D.system.Φ t inputOne = t :=
      (D.phi_apply t ht inputOne).trans (D.one_value t ht)
    calc
      t = ‖D.system.Φ t inputOne‖ := by rw [hone, Real.norm_eq_abs, abs_of_nonneg ht]
      _ ≤ ‖D.system.Φ t‖ * ‖inputOne‖ := (D.system.Φ t).le_opNorm inputOne
      _ ≤ ‖D.system.Φ t‖ * 1 :=
        mul_le_mul_of_nonneg_left inputOne_norm_le (norm_nonneg _)
      _ = ‖D.system.Φ t‖ := mul_one _

end LocalControlData

/-! ## Integral representation (`eq:representation`) and `E_F`-admissibility (`eq:orlicz`) -/

/-- Integral representation `eq:representation`, `Φ_t u = ∫_0^t T_{t-s} B u(s) ds`, with
`B : ℝ → ℝ`. For `T = Id` the generator is `A = 0` and `X_{-1} = ℝ`, so this is the
representation of the paper specialized to the systems considered here. -/
def HasIntegralRepresentation (S : ScalarSystem) : Prop :=
  ∃ B : ℝ →L[ℝ] ℝ, ∀ t : ℝ, 0 ≤ t → ∀ u : Input,
    S.Φ t u = ∫ s in Ioc (0 : ℝ) t, S.T (t - s) (B (u s))

lemma scalar_form_of_representation (S : ScalarSystem)
    (hT : ∀ t, S.T t = ContinuousLinearMap.id ℝ ℝ)
    (h : HasIntegralRepresentation S) :
    ∃ b : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ u : Input,
      S.Φ t u = b * ∫ s in Ioc (0 : ℝ) t, u s := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B 1, ?_⟩
  have hBx (x : ℝ) : B x = B 1 * x := by
    calc
      B x = B (x • (1 : ℝ)) := by simp
      _ = x • B 1 := B.map_smul x 1
      _ = B 1 * x := by simp [mul_comm]
  intro t ht u
  rw [hB t ht u]
  have heq : (fun s => S.T (t - s) (B (u s))) = (fun s => B 1 * u s) := by
    funext s
    rw [hT, ContinuousLinearMap.id_apply, hBx]
  rw [heq]
  exact integral_const_mul _ _

/-- Young functions. This class contains the Young functions of the paper (it does not
require `F(r)/r → 0` at `0` nor `F(r)/r → ∞` at `∞`); the proofs only use `F(0) = 0` and
`F ≥ 0`. -/
structure YoungFunction where
  /-- The scalar function defining the Orlicz modular. -/
  toFun : ℝ → ℝ
  zero : toFun 0 = 0
  nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ toFun x
  convex : ConvexOn ℝ (Ici 0) toFun
  continuous : ContinuousOn toFun (Ici 0)
  growth : Tendsto toFun atTop atTop

/-- The modular is an extended nonnegative integral, so divergence is not
silently converted to the real number zero. -/
def modular (F : YoungFunction) (t : ℝ) (u : Input) (lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (F.toFun (|u s| / lam))

/-- Membership of the restriction to `(0,t]` in the Orlicz heart. -/
def InHeart (F : YoungFunction) (t : ℝ) (u : Input) : Prop :=
  ∀ lam : ℝ, 0 < lam → modular F t u lam < ∞

/-- The Luxemburg gauge, by its infimum definition, not an abstract norm
postulated to tend to zero. -/
def luxemburg (F : YoungFunction) (t : ℝ) (u : Input) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧ modular F t u lam ≤ 1}

lemma luxemburg_le (F : YoungFunction) (t : ℝ) (u : Input)
    {lam : ℝ} (hlam : 0 < lam) (hmod : modular F t u lam ≤ 1) :
    luxemburg F t u ≤ lam := by
  exact csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨hlam, hmod⟩

/-- `E_F`-admissibility, estimate `eq:orlicz`: `|Φ_t u| ≤ C_t ‖u‖_{F,t}` for every `t`. -/
def EFAdmissible (S : ScalarSystem) (F : YoungFunction) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Input,
    InHeart F t u → |S.Φ t u| ≤ C * luxemburg F t u

lemma indicator_modular (F : YoungFunction) {A : Set ℝ}
    (hA : MeasurableSet A) (hAC : A ⊆ cell) (lam : ℝ) :
    modular F 1 (inputIndicator A hA) lam =
      ENNReal.ofReal ((volume A).toReal * F.toFun (1 / lam)) := by
  have hrep := ae_on_cell (linftyIndicator_ae muPlus A hA)
  have heq : (fun s => ENNReal.ofReal (F.toFun (|inputIndicator A hA s| / lam)))
      =ᵐ[volume.restrict cell]
      A.indicator (fun _ => ENNReal.ofReal (F.toFun (1 / lam))) := by
    filter_upwards [hrep] with s hs
    dsimp [inputIndicator]
    rw [hs]
    by_cases h : s ∈ A <;> simp [Set.indicator, h, F.zero]
  change (∫⁻ s, ENNReal.ofReal (F.toFun (|inputIndicator A hA s| / lam))
    ∂volume.restrict cell) = _
  rw [lintegral_congr_ae heq, lintegral_indicator hA]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.restrict_apply hA, inter_eq_left.mpr hAC]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal
    (measure_ne_top_of_subset_cell hAC)]
  simp [mul_comm]

lemma indicator_inHeart (F : YoungFunction) {A : Set ℝ}
    (hA : MeasurableSet A) (hAC : A ⊆ cell) :
    InHeart F 1 (inputIndicator A hA) := by
  intro lam hlam
  rw [indicator_modular F hA hAC lam]
  exact ENNReal.ofReal_lt_top

/-! ## Steps 4–5: the two obstructions -/

/-- Step 3: indicators of sets of arbitrarily small measure with output exactly one. -/
def SmallIndicators (S : ScalarSystem) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : Set ℝ, ∃ hA : MeasurableSet A,
    A ⊆ cell ∧ (volume A).toReal < ε ∧ S.Φ 1 (inputIndicator A hA) = 1

lemma not_integral_of_smallIndicators (S : ScalarSystem)
    (hT : ∀ t, S.T t = ContinuousLinearMap.id ℝ ℝ)
    (hsmall : SmallIndicators S) : ¬ HasIntegralRepresentation S := by
  intro hrepr
  obtain ⟨b, hb⟩ := scalar_form_of_representation S hT hrepr
  let ε : ℝ := 1 / (2 * (|b| + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨A, hA, hAC, hμ, hout⟩ := hsmall ε hε
  have hrep := hb 1 (by norm_num) (inputIndicator A hA)
  change S.Φ 1 (inputIndicator A hA) = b * ∫ s in cell, inputIndicator A hA s at hrep
  rw [inputIndicator_integral hA hAC, hout] at hrep
  have habs : (1 : ℝ) = |b| * (volume A).toReal := by
    have h := congrArg abs hrep
    simpa [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using h
  have hscaled := (lt_div_iff₀ (show 0 < 2 * (|b| + 1) by positivity)).mp hμ
  have hμ0 : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
  nlinarith

lemma not_EF_of_smallIndicators (S : ScalarSystem)
    (hsmall : SmallIndicators S) (F : YoungFunction) : ¬ EFAdmissible S F := by
  intro hEF
  obtain ⟨C, hC, hbound⟩ := hEF 1 (by norm_num)
  let lam : ℝ := 1 / (2 * (C + 1))
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hClam : C * lam < 1 := by
    dsimp [lam]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith
  let K : ℝ := F.toFun (1 / lam)
  have hK : 0 ≤ K := F.nonneg _ (by positivity)
  let δ : ℝ := 1 / (K + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hAC, hμ, hout⟩ := hsmall δ hδ
  have hmod : modular F 1 (inputIndicator A hA) lam ≤ 1 := by
    rw [indicator_modular F hA hAC lam]
    have hμK : (volume A).toReal * K ≤ 1 := by
      have hscaled := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hμ
      have hμ0 : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
      nlinarith
    calc
      ENNReal.ofReal ((volume A).toReal * F.toFun (1 / lam))
          ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hμK
      _ = 1 := by simp
  have hlu := luxemburg_le F 1 (inputIndicator A hA) hlam hmod
  have houtbound := hbound (inputIndicator A hA) (indicator_inHeart F hA hAC)
  rw [hout, abs_one] at houtbound
  have hmul := mul_le_mul_of_nonneg_left hlu hC
  linarith

lemma LocalControlData.smallIndicators
    {m : LinftyPer →L[ℝ] ℝ} (D : LocalControlData m)
    (h1 : m one = 1) (hV : ∀ v ∈ vanishingOnDenseOpen, m v = 0) :
    SmallIndicators D.system := by
  intro ε hε
  obtain ⟨O, hOo, hOd, hμ⟩ := exists_small_periodic_open ε hε
  refine ⟨O.carrier ∩ cell, O.measurable.inter cell_measurable,
    inter_subset_right, hμ, ?_⟩
  change D.phi 1 _ = 1
  rw [D.phi_apply 1 (by norm_num), D.periodic_test]
  exact O.mean_indicator m h1 hV hOo hOd

/-- Steps 3–5 of the proof of Proposition 3.3: the system built from `LocalControlData` has
properties (i), (ii), (iii), provided the mean vanishes on `vanishingOnDenseOpen`. -/
theorem counterexample_from_data
    {m : LinftyPer →L[ℝ] ℝ} (D : LocalControlData m)
    (h1 : m one = 1) (hV : ∀ v ∈ vanishingOnDenseOpen, m v = 0) :
    (∀ t : ℝ, 0 ≤ t → D.system.T t = ContinuousLinearMap.id ℝ ℝ) ∧
    (∀ t : ℝ, 0 ≤ t → ‖D.system.Φ t‖ = t) ∧
    ¬ HasIntegralRepresentation D.system ∧
    ∀ F : YoungFunction, ¬ EFAdmissible D.system F := by
  have hsmall := D.smallIndicators h1 hV
  exact ⟨fun t _ => D.system_T t, D.kappa,
    not_integral_of_smallIndicators D.system D.system_T hsmall,
    not_EF_of_smallIndicators D.system hsmall⟩

/-- **Proposition 3.3** (`prop:no-representation`). There is an abstract linear control
system with `p = ∞`, `X = U = ℝ` and `T_t = Id` such that (i) `κ(t) = t` for `t ≥ 0`,
(ii) it has no integral representation, (iii) it is not `E_F`-admissible for any Young
function `F`. -/
theorem no_representation :
    ∃ S : ALCS ℝ ℝ ℝ ∞,
      (∀ t : ℝ, 0 ≤ t → S.T t = ContinuousLinearMap.id ℝ ℝ) ∧
      (∀ t : ℝ, 0 ≤ t → ‖S.Φ t‖ = t) ∧
      ¬ HasIntegralRepresentation S ∧
      ∀ F : YoungFunction, ¬ EFAdmissible S F := by
  obtain ⟨m, hm, hpos, h1, hT, hV⟩ := exists_strong_mean
  obtain ⟨D⟩ := exists_local_control_from_mean m hpos h1 hT
  exact ⟨D.system, counterexample_from_data D h1 hV⟩

end ExoticMean.Counterexample

end
end

end AbstractLinearControl
