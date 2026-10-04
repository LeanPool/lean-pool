/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Sobolev.H01Lattice
public import LeanPool.EllipticPDE.Embedding.H01SobolevTwo


/-!
# Weak maximum principle with a transport term

Gilbarg and Trudinger's Theorem 8.1 with the transport term present, in dimension at least
two. The transport-free case tests the subsolution inequality against `(u - k)⁺` and finds
the energy of the truncation nonpositive. With a transport term the energy is bounded by the
transport coefficient times the gradient norm of the truncation times its `L²` norm over the
set `Γ_k` where `u > k` and the gradient does not vanish. Ellipticity, a Sobolev inequality on
`H₀¹` at an exponent above `2`, which is the critical one in dimension at least three and the
embedding into `L⁴` in dimension two, and Hölder's inequality then bound the measure of `Γ_k`
below by a constant independent of `k`, at every level whose superlevel set has positive
measure.

The bound is contradicted as `k` increases to the supremum `T` of the levels at which the
superlevel set has positive measure: the sets `Γ_k` decrease to a subset of `{u ≥ T}` on which
the gradient does not vanish, and this set is null because `{u > T}` is null by the choice of
`T` and the gradient vanishes almost everywhere on `{u = T}`. So no level above the boundary
value has a nonzero truncation, which is the conclusion.

The membership of `(u - k)⁺` in `H₀¹(Ω)` for every `k` above the boundary value comes from the
truncation lemma of `EllipticPdes.Sobolev.H01Lattice`.

## Main declarations

* `EllipticPdes.Sobolev.weak_maximum_principle_transport`: the weak maximum principle with a
  transport term, in dimension at least two.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (pp. 179–180).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding EllipticPdes.Extension

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### The set where the truncation has nonvanishing gradient -/

/-- The set where `u > k` and the gradient does not vanish. -/
def truncSupport (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | k < u x ∧ ∃ i, g i x ≠ 0}

/-- The set is measurable when the functions are. -/
theorem measurableSet_truncSupport {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (hg : ∀ i, Measurable (g i))
    (k : ℝ) : MeasurableSet (truncSupport u g k) := by
  have : truncSupport u g k = {x | k < u x} ∩ ⋃ i, {x | g i x = 0}ᶜ := by
    ext x
    simp only [truncSupport, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_compl_iff]
  rw [this]
  exact (measurableSet_lt measurable_const hu).inter
    (MeasurableSet.iUnion fun i => (measurableSet_eq_fun (hg i) measurable_const).compl)

/-- The set is antitone in the level. -/
theorem truncSupport_antitone (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Antitone (truncSupport u g) :=
  fun _ _ hst _ hx => ⟨lt_of_le_of_lt hst hx.1, hx.2⟩

/-- The set lies in the superlevel set. -/
theorem truncSupport_subset (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : ℝ) :
    truncSupport u g k ⊆ {x | k < u x} := fun _ hx => hx.1

/-! ### The tail of the argument -/

/-- **Impossibility of a uniform lower bound on the measure of `Γ_k`.** If the measure of `Γ_k`
is at least `c > 0` at every level `k ≥ k₀` whose superlevel set has positive measure, and the
gradient vanishes almost everywhere on every level set, then the superlevel set of `k₀` is
null. -/
theorem measure_superlevel_eq_zero {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ]
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Measurable u) (hg : ∀ i, Measurable (g i))
    (hlevel : ∀ (T : ℝ) (i : Fin d), ∀ᵐ x ∂μ, u x = T → g i x = 0)
    {c : ℝ} (hc : 0 < c) {k₀ : ℝ}
    (hest : ∀ k, k₀ ≤ k → 0 < μ {x | k < u x} → c ≤ (μ (truncSupport u g k)).toReal) :
    μ {x | k₀ < u x} = 0 := by
  by_contra hpos
  replace hpos : 0 < μ {x | k₀ < u x} := pos_iff_ne_zero.mpr hpos
  have hsup_meas : ∀ t : ℝ, MeasurableSet {x | t < u x} := fun t =>
    measurableSet_lt measurable_const hu
  have hΓm : ∀ t, MeasurableSet (truncSupport u g t) := measurableSet_truncSupport hu hg
  -- the superlevel sets of `n` shrink to nothing, so some has measure below `c`
  have hshrink : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < u x}) atTop
      (𝓝 (μ (⋂ n : ℕ, {x | (n : ℝ) < u x}))) :=
    tendsto_measure_iInter_atTop (fun n => (hsup_meas n).nullMeasurableSet)
      (fun m n hmn x hx => by
        have hx' : (n : ℝ) < u x := hx
        exact lt_of_le_of_lt (Nat.cast_le.mpr hmn) hx') ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {x | (n : ℝ) < u x}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt (u x)
    exact ⟨n, hn.le⟩
  rw [hempty, measure_empty] at hshrink
  obtain ⟨N, hN⟩ := (hshrink.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hc))).exists
  -- the levels with a nonzero truncation
  set S : Set ℝ := {t | k₀ ≤ t ∧ 0 < μ {x | t < u x}} with hSdef
  have hk₀S : k₀ ∈ S := ⟨le_rfl, hpos⟩
  have hSbdd : BddAbove S := by
    refine ⟨N, fun t ht => ?_⟩
    by_contra hlt
    have h1 : μ {x | t < u x} ≤ μ {x | (N : ℝ) < u x} :=
      measure_mono fun x hx => lt_trans (not_le.mp hlt) hx
    have h2 : c ≤ (μ (truncSupport u g t)).toReal := hest t ht.1 ht.2
    have h3 : (μ (truncSupport u g t)).toReal ≤ (μ {x | t < u x}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (truncSupport_subset u g t))
    have h4 : (μ {x | t < u x}).toReal < c := by
      rw [← ENNReal.toReal_ofReal hc.le]
      exact ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top (lt_of_le_of_lt h1 hN)
    linarith
  set T : ℝ := sSup S with hTdef
  have hk₀T : k₀ ≤ T := le_csSup hSbdd hk₀S
  -- the superlevel set of `T` is null
  have hTnull : μ {x | T < u x} = 0 := by
    have hcover : {x | T < u x} = ⋃ n : ℕ, {x | T + 1 / (n + 1 : ℝ) < u x} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
    rw [hcover]
    refine measure_iUnion_null fun n => ?_
    by_contra hne
    have hmem : T + 1 / (n + 1 : ℝ) ∈ S :=
      ⟨by linarith [(by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))], pos_iff_ne_zero.mpr hne⟩
    have := le_csSup hSbdd hmem
    linarith [(by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))]
  -- the gradient vanishes almost everywhere on the level set of `T`
  have hlevelnull : μ ({x | u x = T} ∩ {x | ∃ i, g i x ≠ 0}) = 0 := by
    have : {x | u x = T} ∩ {x | ∃ i, g i x ≠ 0} = ⋃ i, {x | ¬(u x = T → g i x = 0)} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, Classical.not_imp]
      exact ⟨fun ⟨h1, i, hi⟩ => ⟨i, h1, hi⟩, fun ⟨i, h1, hi⟩ => ⟨h1, i, hi⟩⟩
    rw [this]
    exact measure_iUnion_null fun i => ae_iff.mp (hlevel T i)
  -- the sets `Γ_t` for `t < T` have measure at least `c`, and shrink into the level set
  have hbelow : ∀ t, k₀ ≤ t → t < T → ENNReal.ofReal c ≤ μ (truncSupport u g t) := by
    intro t hk₀t htT
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨k₀, hk₀S⟩ htT
    have hpos' : 0 < μ {x | t < u x} :=
      lt_of_lt_of_le hs.2 (measure_mono fun x hx => lt_trans hts hx)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hest t hk₀t hpos')
  have hkey : ENNReal.ofReal c ≤ μ ({x | T ≤ u x} ∩ {x | ∃ i, g i x ≠ 0}) := by
    rcases eq_or_lt_of_le hk₀T with hTk | hTk
    · -- the supremum is the boundary level itself
      refine le_trans ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
        (hest k₀ le_rfl hpos)) (measure_mono fun x hx => ⟨?_, hx.2⟩)
      rw [← hTk]
      exact hx.1.le
    · -- levels increasing to the supremum
      set t : ℕ → ℝ := fun n => max k₀ (T - 1 / (n + 1 : ℝ)) with htdef
      have ht_lt : ∀ n, t n < T := fun n =>
        max_lt hTk (by linarith [(by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))])
      have ht_ge : ∀ n, k₀ ≤ t n := fun n => le_max_left _ _
      have ht_mono : Monotone t := fun m n hmn => max_le_max le_rfl (by
        have : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
        linarith)
      have ht_lim : Tendsto t atTop (𝓝 T) := by
        have h1 : Tendsto (fun n : ℕ => T - 1 / (n + 1 : ℝ)) atTop (𝓝 (T - 0)) :=
          tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
        rw [sub_zero] at h1
        have hcm : Continuous fun s : ℝ => max k₀ s := continuous_const.max continuous_id
        have h2 := (hcm.tendsto T).comp h1
        simp only [Function.comp_def, max_eq_right hk₀T] at h2
        exact h2
      have hanti : Antitone fun n => truncSupport u g (t n) :=
        fun m n hmn => truncSupport_antitone u g (ht_mono hmn)
      have hlim := tendsto_measure_iInter_atTop (μ := μ)
        (fun n => (hΓm (t n)).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
      have hge : ENNReal.ofReal c ≤ μ (⋂ n, truncSupport u g (t n)) :=
        ge_of_tendsto' hlim fun n => hbelow (t n) (ht_ge n) (ht_lt n)
      refine hge.trans (measure_mono fun x hx => ?_)
      rw [mem_iInter] at hx
      refine ⟨?_, (hx 0).2⟩
      exact le_of_tendsto' ht_lim fun n => (hx n).1.le
  -- the two null sets cover the intersection
  have hcover : {x | T ≤ u x} ∩ {x | ∃ i, g i x ≠ 0}
      ⊆ {x | T < u x} ∪ ({x | u x = T} ∩ {x | ∃ i, g i x ≠ 0}) := by
    intro x hx
    have hx1 : T ≤ u x := hx.1
    rcases lt_or_eq_of_le hx1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, hx.2⟩
  have hzero : μ ({x | T ≤ u x} ∩ {x | ∃ i, g i x ≠ 0}) = 0 :=
    measure_mono_null hcover (measure_union_null hTnull hlevelnull)
  rw [hzero] at hkey
  exact absurd hkey (not_le.mpr (ENNReal.ofReal_pos.mpr hc))

/-! ### The truncation at every level above the boundary value -/

/-- Truncating twice is truncating once. -/
theorem max_max_sub_eq {a k₀ k : ℝ} (hk : k₀ ≤ k) :
    max (max (a - k₀) 0 - (k - k₀)) 0 = max (a - k) 0 := by
  rcases le_or_gt a k₀ with h | h
  · have h1 : max (a - k₀) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (a - k) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    exact max_eq_right (by linarith)
  · have h1 : max (a - k₀) 0 = a - k₀ := max_eq_left (by linarith)
    rw [h1]
    congr 1
    ring

/-- The indicator of the second truncation is the indicator of `{k < a}`. -/
theorem ite_lt_max_sub {k₀ k : ℝ} (hk : k₀ ≤ k) (a b : ℝ) :
    (if k - k₀ < max (a - k₀) 0 then (if k₀ < a then b else 0) else 0)
      = if k < a then b else 0 := by
  rcases lt_or_ge k a with h | h
  · have h1 : max (a - k₀) 0 = a - k₀ := max_eq_left (by linarith)
    have h2 : k - k₀ < max (a - k₀) 0 := by rw [h1]; linarith
    have h3 : k₀ < a := by linarith
    rw [ite_eq_left h2, ite_eq_left h3, ite_eq_left h]
  · have h2 : ¬ k - k₀ < max (a - k₀) 0 := by
      rw [not_lt]
      exact max_le (by linarith) (by linarith)
    rw [ite_eq_right h2, ite_eq_right (not_lt.mpr h)]

/-- **Truncations at every level above the boundary value in `H₀¹`.** If `(u - k₀)⁺` is
the function coordinate of an element of `H₀¹(Ω)`, then for every `k ≥ k₀` there is an element
of `H₀¹(Ω)` with function coordinate `(u - k)⁺` and gradient coordinates those of `u` on
`{u > k}` and zero elsewhere. -/
theorem exists_truncation_mem_H01 (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {U : H1amb Ω} (hU : U ∈ W12 Ω) {k₀ : ℝ} (V₀ : H01 Ω)
    (hV₀ : ((V₀ : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k₀) 0)
    {k : ℝ} (hk : k₀ ≤ k) :
    ∃ V : H01 Ω,
      (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) ∧
      ∀ i : Fin d, ((V : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => if k < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  -- the gradient coordinates of `V₀`
  have hwg := hasWeakGradOn_of_mem_W12 hU
  have huint : IntegrableOn (fun x => (U 0 x : ℝ)) Ω volume :=
    (Lp.memLp (U 0)).integrable one_le_two
  have hgint : ∀ i : Fin d, IntegrableOn (fun x => (U i.succ x : ℝ)) Ω volume := fun i =>
    (Lp.memLp (U i.succ)).integrable one_le_two
  have hum : Measurable fun x => (U 0 x : ℝ) := (Lp.stronglyMeasurable (U 0)).measurable
  have hw := hasWeakGradOn_posPart_sub_const hΩopen huint.locallyIntegrableOn
    (fun i => (hgint i).locallyIntegrableOn) hwg k₀
  have hhint : ∀ i : Fin d, IntegrableOn
      (fun x => if k₀ < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0) Ω volume := fun i => by
    have : (fun x => if k₀ < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0)
        = {x | k₀ < (U 0 x : ℝ)}.indicator fun x => (U i.succ x : ℝ) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [this]
    exact (hgint i).indicator (measurableSet_lt measurable_const hum)
  have hwgV' : HasWeakGradOn Ω (fun x => max ((U 0 x : ℝ) - k₀) 0)
      fun i x => ((V₀ : H1amb Ω) i.succ x : ℝ) :=
    (hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω V₀.2)).congr_ae hV₀ fun _ => EventuallyEq.rfl
  have hV₀grad : ∀ i : Fin d, (fun x => ((V₀ : H1amb Ω) i.succ x : ℝ))
      =ᵐ[volume.restrict Ω] fun x => if k₀ < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0 :=
    fun i => hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet
      (fun i => (Lp.memLp ((V₀ : H1amb Ω) i.succ)).integrable one_le_two) hhint hwgV' hw i
  -- truncate `V₀` by `k - k₀`
  obtain ⟨W, hW, hW0, hWi⟩ := exists_mem_H01_posPart_sub_const hΩopen V₀.2 (sub_nonneg.mpr hk)
  refine ⟨⟨W, hW⟩, ?_, fun i => ?_⟩
  · filter_upwards [hW0, hV₀] with x hx hx0
    rw [hx, hx0]
    exact max_max_sub_eq hk
  · filter_upwards [hWi i, hV₀, hV₀grad i] with x hx hx0 hxi
    have hxi' : ((V₀ : H1amb Ω) i.succ x : ℝ)
        = if k₀ < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0 := hxi
    rw [hx, hx0, hxi']
    exact ite_lt_max_sub hk _ _

/-! ### The energy estimate -/

/-- A bounded coefficient times two `L²` classes is integrable. -/
theorem integrable_coeff_mul_mul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (p q : L2D Ω) :
    Integrable (fun x => f x * (p x : ℝ) * (q x : ℝ)) (volume.restrict Ω) := by
  refine (MeasureTheory.L2.integrable_inner (mulCoeffL hf hM p) q).congr ?_
  filter_upwards [mulCoeffL_coeFn hf hM p] with x hx
  simp only [Real.inner_apply, hx]

/-- **Energy estimate from testing with the truncation.** For a subsolution `U` and an
element `V` of `H₀¹(Ω)` whose coordinates are the truncation `(u - k)⁺` and its gradient,
ellipticity times the gradient norm squared of `V` is at most the transport bound times the
sum of the gradient norms times the `L²` norm of the truncation over `Γ_k`. -/
theorem energy_le_transport (Op : FullEllipticOp d)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x)
    {U : H1amb Ω}
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫)
        + ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ ≤ 0)
    {k : ℝ} (hk : 0 ≤ k) (V : H01 Ω)
    (hV0 : ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0)
    (hVi : ∀ i : Fin d, ((V : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => if k < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0) :
    Op.lam * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2
      ≤ Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
        * (eLpNorm ((V : H1amb Ω) 0) 2 ((volume.restrict Ω).restrict
            (truncSupport (fun x => (U 0 x : ℝ)) (fun i x => (U i.succ x : ℝ)) k))).toReal := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Ω with hμdef
  set u : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (U 0 x : ℝ) with hudef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => (U i.succ x : ℝ) with hgdef
  have hum : Measurable u := (Lp.stronglyMeasurable (U 0)).measurable
  have hgm : ∀ i, Measurable (g i) := fun i => (Lp.stronglyMeasurable (U i.succ)).measurable
  set Γ := truncSupport u g k with hΓdef
  have hΓ : MeasurableSet Γ := measurableSet_truncSupport hum hgm k
  -- the truncation restricted to `Γ`
  set vΓ : EuclideanSpace ℝ (Fin d) → ℝ := Γ.indicator fun x => ((V : H1amb Ω) 0 x : ℝ)
    with hvΓdef
  have hvΓm : MemLp vΓ 2 μ := (Lp.memLp _).indicator hΓ
  have hnormΓ : (eLpNorm vΓ 2 μ).toReal = (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal := by
    rw [hvΓdef, eLpNorm_indicator_eq_eLpNorm_restrict hΓ]
  -- the test is nonnegative
  have hVnn : ∀ᵐ x ∂μ, 0 ≤ ((V : H1amb Ω) 0 x : ℝ) := by
    filter_upwards [hV0] with x hx
    rw [hx]
    exact le_max_right _ _
  have hineq := hsub V hVnn
  -- the zeroth-order term is nonnegative
  have hcterm : 0 ≤ ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ := by
    simp only [FullEllipticOp.cAct, inner_mulCoeffL_eq]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hc, hV0] with x hcx hx
    rw [hx]
    simp only [Pi.zero_apply]
    by_cases hxk : k < u x
    · have hu0 : 0 ≤ u x := hk.trans hxk.le
      exact mul_nonneg (mul_nonneg hcx hu0) (le_max_right _ _)
    · have hle : u x ≤ k := not_lt.mp hxk
      rw [max_eq_right (by linarith), mul_zero]
  -- the principal term is the energy of `V`
  have hprin : (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
      = Op.toEllipticCoeff.bilin Ω V V := by
    rw [EllipticCoeff.bilin_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [EllipticCoeff.inner_actL_eq, EllipticCoeff.inner_actL_eq]
    refine integral_congr_ae ?_
    filter_upwards [hVi i, hVi j] with x hi hj
    have hi' : ((V : H1amb Ω) i.succ x : ℝ) = if k < u x then g i x else 0 := hi
    have hj' : ((V : H1amb Ω) j.succ x : ℝ) = if k < u x then g j x else 0 := hj
    rw [hi', hj']
    simp only [hgdef]
    split_ifs <;> simp
  -- the transport term is bounded below
  have hbi : ∀ i : Fin d,
      -(Op.Bsup * (‖(V : H1amb Ω) i.succ‖ * (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal))
        ≤ ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫ := by
    intro i
    simp only [FullEllipticOp.bAct, inner_mulCoeffL_eq]
    -- the classes `|∂ᵢv|` and `|v 1_Γ|`
    set A : L2D Ω := (Lp.memLp ((V : H1amb Ω) i.succ)).norm.toLp _ with hAdef
    set B : L2D Ω := hvΓm.norm.toLp _ with hBdef
    have hA : ‖A‖ = ‖(V : H1amb Ω) i.succ‖ := by
      rw [hAdef, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable _), Lp.norm_def]
    have hB : ‖B‖ = (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal := by
      rw [hBdef, Lp.norm_toLp, eLpNorm_norm _ hvΓm.aestronglyMeasurable, hnormΓ]
    have hAB : ⟪A, B⟫ = ∫ x, ‖((V : H1amb Ω) i.succ x : ℝ)‖ * ‖vΓ x‖ ∂μ := by
      rw [hAdef, hBdef, inner_toLp_eq]
    have hint1 : Integrable (fun x => Op.b x i * (U i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)) μ :=
      integrable_coeff_mul_mul (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) _ _
    have hint2 : Integrable (fun x => ‖((V : H1amb Ω) i.succ x : ℝ)‖ * ‖vΓ x‖) μ := by
      refine (MeasureTheory.L2.integrable_inner A B).congr ?_
      filter_upwards [(Lp.memLp ((V : H1amb Ω) i.succ)).norm.coeFn_toLp, hvΓm.norm.coeFn_toLp]
        with x hx1 hx2
      simp only [hAdef, hBdef, Real.inner_apply, hx1, hx2]
    have hpt : ∀ᵐ x ∂μ, -(Op.Bsup * (‖((V : H1amb Ω) i.succ x : ℝ)‖ * ‖vΓ x‖))
        ≤ Op.b x i * (U i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ) := by
      filter_upwards [ae_restrict_of_ae (Op.b_bdd i), hV0, hVi i] with x hbx hx0 hxi
      have hxi' : ((V : H1amb Ω) i.succ x : ℝ) = if k < u x then g i x else 0 := hxi
      -- the product `∂ᵢu · v` is `∂ᵢv · (v 1_Γ)`
      have hprod : (U i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)
          = ((V : H1amb Ω) i.succ x : ℝ) * vΓ x := by
        rw [hxi', hvΓdef, Set.indicator_apply, hx0]
        by_cases hxk : k < u x
        · rw [ite_eq_left hxk]
          by_cases hxΓ : x ∈ Γ
          · rw [ite_eq_left hxΓ]
          · have h0 : g i x = 0 := by
              by_contra hne
              exact hxΓ ⟨hxk, i, hne⟩
            rw [ite_eq_right hxΓ]
            simp only [hgdef] at h0
            rw [h0, zero_mul, mul_zero]
        · have hle : u x ≤ k := not_lt.mp hxk
          rw [ite_eq_right hxk, max_eq_right (by linarith), mul_zero, zero_mul]
      rw [mul_assoc, hprod, ← mul_assoc]
      have habs : |Op.b x i * ((V : H1amb Ω) i.succ x : ℝ) * vΓ x|
          ≤ Op.Bsup * (‖((V : H1amb Ω) i.succ x : ℝ)‖ * ‖vΓ x‖) := by
        rw [abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
        gcongr
      linarith [neg_abs_le (Op.b x i * ((V : H1amb Ω) i.succ x : ℝ) * vΓ x)]
    calc -(Op.Bsup * (‖(V : H1amb Ω) i.succ‖
            * (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal))
        = -(Op.Bsup * ⟪A, B⟫) + -(Op.Bsup * (‖A‖ * ‖B‖ - ⟪A, B⟫)) := by rw [hA, hB]; ring
      _ ≤ -(Op.Bsup * ⟪A, B⟫) := by
          have : 0 ≤ ‖A‖ * ‖B‖ - ⟪A, B⟫ := sub_nonneg.mpr (real_inner_le_norm A B)
          nlinarith [Op.Bsup_nonneg]
      _ = ∫ x, -(Op.Bsup * (‖((V : H1amb Ω) i.succ x : ℝ)‖ * ‖vΓ x‖)) ∂μ := by
          rw [hAB, integral_neg, integral_const_mul]
      _ ≤ ∫ x, Op.b x i * (U i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ) ∂μ :=
          integral_mono_ae ((hint2.const_mul _).neg) hint1 hpt
  have hbsum : -(Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
        * (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal)
      ≤ ∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫ := by
    calc -(Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
            * (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal)
        = ∑ i : Fin d, -(Op.Bsup * (‖(V : H1amb Ω) i.succ‖
            * (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal)) := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ ∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫ := Finset.sum_le_sum fun i _ => hbi i
  rw [hprin] at hineq
  have henergy := Op.toEllipticCoeff.bilin_self_ge V
  linarith

/-! ### The Sobolev-Hölder lower bound -/

/-- **Uniform lower bound on the measure of `Γ_k`**, from a Sobolev inequality on `H₀¹(Ω)` at
an exponent above `2`. On a bounded open set there is `c > 0`, depending on the domain, the
dimension, the operator and the Sobolev constant alone, such that, whenever the truncation
`(u - k)⁺` is the function coordinate of an element `V` of `H₀¹(Ω)` whose superlevel set has
positive measure and satisfies the energy estimate, the set `Γ_k` has measure at least `c`. -/
theorem exists_measure_truncSupport_ge_of_sobolev (hΩb : Bornology.IsBounded Ω)
    (Op : FullEllipticOp d) {q : ℝ≥0} (hq2 : 2 < q) {C : ℝ≥0}
    (hsobolev : ∀ V : H01 Ω, eLpNorm ((V : H1amb Ω) 0) q (volume.restrict Ω)
      ≤ C * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ₑ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : H01 Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ), Measurable u → (∀ i, Measurable (g i)) →
      ∀ k : ℝ, (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max (u x - k) 0) →
      0 < (volume.restrict Ω) {x | k < u x} →
      Op.lam * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2
        ≤ Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
          * (eLpNorm ((V : H1amb Ω) 0) 2
              ((volume.restrict Ω).restrict (truncSupport u g k))).toReal →
      c ≤ ((volume.restrict Ω) (truncSupport u g k)).toReal := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  set μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Ω with hμdef
  have hq2r : (2 : ℝ) < q := by exact_mod_cast hq2
  set θ : ℝ := 1 / 2 - 1 / (q : ℝ) with hθdef
  have hθpos : 0 < θ := by
    have : 1 / (q : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hq2r
    rw [hθdef]
    linarith
  have h2q : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    have : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_ofNat 2).symm
    rw [this]
    exact ENNReal.coe_le_coe.mpr hq2.le
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact (lt_trans (by norm_num) hq2).ne'
  -- the constant
  set K : ℝ := (C : ℝ) * d * (Op.Bsup * d / Op.lam) + 1 with hKdef
  have hKbase : 0 ≤ (C : ℝ) * d * (Op.Bsup * d / Op.lam) :=
    mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (mul_nonneg Op.Bsup_nonneg (Nat.cast_nonneg _)) Op.lam_pos.le)
  have hKpos : 0 < K := by linarith
  refine ⟨K⁻¹ ^ θ⁻¹, Real.rpow_pos_of_pos (inv_pos.mpr hKpos) _,
    fun V u g hu hg k hV0 hpos henergy => ?_⟩
  set Γ := truncSupport u g k with hΓdef
  have hΓ : MeasurableSet Γ := measurableSet_truncSupport hu hg k
  set γ : ℝ := (μ Γ).toReal with hγdef
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  -- the Sobolev inequality on `H₀¹`
  have hsob := hsobolev V
  set N : ℝ := (eLpNorm ((V : H1amb Ω) 0) q μ).toReal with hNdef
  have hNfin : eLpNorm ((V : H1amb Ω) 0) q μ ≠ ⊤ := (memLp_of_mem_H01 hsob).eLpNorm_ne_top
  have hN : N ≤ (C : ℝ) * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.sum_ne_top.mpr fun i _ => by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top)) hsob
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_sum
      (fun i _ => by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top)] at this
  -- the gradient norm
  set S : ℝ := Real.sqrt (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsumle : ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ≤ d * S := by
    calc ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ≤ ∑ _i : Fin d, S := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hSdef, Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)]
          exact Finset.single_le_sum (f := fun j : Fin d => ‖(V : H1amb Ω) j.succ‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      _ = d * S := by simp
  -- the `L²` norm of the truncation over `Γ`
  set vΓ : ℝ := (eLpNorm ((V : H1amb Ω) 0) 2 (μ.restrict Γ)).toReal with hvΓdef
  have hvΓ0 : 0 ≤ vΓ := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ Op.Bsup := Op.Bsup_nonneg
  have hS : Op.lam * S ≤ Op.Bsup * d * vΓ := by
    have h1 : Op.lam * S * S ≤ (Op.Bsup * d * vΓ) * S := by
      calc Op.lam * S * S = Op.lam * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2 := by
            rw [← hS2]; ring
        _ ≤ Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖) * vΓ := henergy
        _ ≤ Op.Bsup * (d * S) * vΓ := by gcongr
        _ = (Op.Bsup * d * vΓ) * S := by ring
    rcases hS0.lt_or_eq with hSpos | hSzero
    · exact le_of_mul_le_mul_right h1 hSpos
    · rw [← hSzero, mul_zero]
      exact mul_nonneg (mul_nonneg Op.Bsup_nonneg (Nat.cast_nonneg _)) hvΓ0
  -- Hölder's inequality on `Γ`
  have hhold : vΓ ≤ N * γ ^ θ := by
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict Γ) h2q
      ((Lp.aestronglyMeasurable ((V : H1amb Ω) 0)).mono_measure Measure.restrict_le_self)
    have hres : eLpNorm ((V : H1amb Ω) 0) q (μ.restrict Γ) ≤ eLpNorm ((V : H1amb Ω) 0) q μ :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    have hθ' : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (q : ℝ≥0∞).toReal := by
      simp only [ENNReal.toReal_ofNat, ENNReal.coe_toReal]
      exact hθpos.le
    have hfin : eLpNorm ((V : H1amb Ω) 0) q (μ.restrict Γ)
        * (μ.restrict Γ) univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (q : ℝ≥0∞).toReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (ne_top_of_le_ne_top hNfin hres)
        (ENNReal.rpow_ne_top_of_nonneg hθ' (measure_ne_top _ _))
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ,
      ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h2
    calc vΓ ≤ (eLpNorm ((V : H1amb Ω) 0) q (μ.restrict Γ)).toReal * γ ^ θ := h2
      _ ≤ N * γ ^ θ :=
          mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hNfin hres) (Real.rpow_nonneg hγ0 _)
  -- the truncation is not zero
  have hNpos : 0 < N := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ N).lt_or_eq with h | h
    · exact h
    · exfalso
      have hzero : eLpNorm ((V : H1amb Ω) 0) q μ = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp h.symm with h0 | htop
        · exact h0
        · exact absurd htop hNfin
      have hae := (eLpNorm_eq_zero_iff hq0).mp hzero
      have hle : ∀ᵐ x ∂μ, u x ≤ k := by
        filter_upwards [hae, hV0] with x hx hx0
        simp only [Pi.zero_apply] at hx
        rw [hx0] at hx
        by_contra hlt
        rw [max_eq_left (by linarith [not_le.mp hlt])] at hx
        linarith [not_le.mp hlt]
      have : μ {x | k < u x} = 0 := by
        have := ae_iff.mp hle
        simpa only [not_le] using this
      exact absurd this hpos.ne'
  -- assembling the chain
  have hchain : N ≤ K * γ ^ θ * N := by
    have hSle : S ≤ Op.Bsup * d * vΓ / Op.lam := by
      rw [le_div_iff₀ Op.lam_pos]
      linarith [hS]
    have hK0 : 0 ≤ (C : ℝ) * d := by positivity
    calc N ≤ (C : ℝ) * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ := hN
      _ ≤ (C : ℝ) * (d * S) := by gcongr
      _ = ((C : ℝ) * d) * S := by ring
      _ ≤ ((C : ℝ) * d) * (Op.Bsup * d * vΓ / Op.lam) := by gcongr
      _ = ((C : ℝ) * d * (Op.Bsup * d / Op.lam)) * vΓ := by ring
      _ ≤ ((C : ℝ) * d * (Op.Bsup * d / Op.lam)) * (N * γ ^ θ) := by
          gcongr
      _ ≤ K * (N * γ ^ θ) := by
          refine mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith)
            (mul_nonneg hNpos.le (Real.rpow_nonneg hγ0 _))
      _ = K * γ ^ θ * N := by ring
  have hone : 1 ≤ K * γ ^ θ := by
    have := hchain
    rw [← one_mul N] at this
    nth_rewrite 2 [mul_comm] at this
    exact le_of_mul_le_mul_right (by rw [one_mul]; linarith) hNpos
  have hinv : K⁻¹ ≤ γ ^ θ := by
    calc K⁻¹ = K⁻¹ * 1 := (mul_one _).symm
      _ ≤ K⁻¹ * (K * γ ^ θ) := mul_le_mul_of_nonneg_left hone (inv_nonneg.mpr hKpos.le)
      _ = γ ^ θ := by rw [← mul_assoc, inv_mul_cancel₀ hKpos.ne', one_mul]
  calc K⁻¹ ^ θ⁻¹ ≤ (γ ^ θ) ^ θ⁻¹ :=
        Real.rpow_le_rpow (inv_nonneg.mpr hKpos.le) hinv (inv_nonneg.mpr hθpos.le)
    _ = γ := Real.rpow_rpow_inv hγ0 hθpos.ne'

/-- **Uniform lower bound on the measure of `Γ_k` in dimension at least three**, through the
Sobolev inequality at the exponent `2d/(d - 1)`. -/
theorem exists_measure_truncSupport_ge (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hd : 2 < d) (Op : FullEllipticOp d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : H01 Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ), Measurable u → (∀ i, Measurable (g i)) →
      ∀ k : ℝ, (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max (u x - k) 0) →
      0 < (volume.restrict Ω) {x | k < u x} →
      Op.lam * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2
        ≤ Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
          * (eLpNorm ((V : H1amb Ω) 0) 2
              ((volume.restrict Ω).restrict (truncSupport u g k))).toReal →
      c ≤ ((volume.restrict Ω) (truncSupport u g k)).toReal := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d - 1 := by linarith
  set q : ℝ≥0 := ⟨2 * d / (d - 1), div_nonneg (by positivity) hd1.le⟩ with hqdef
  have hqcoe : (q : ℝ) = 2 * d / (d - 1) := rfl
  have hqinv : (q : ℝ)⁻¹ = (d - 1) / (2 * d) := by rw [hqcoe, inv_div]
  have hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    rw [hqinv]
    have : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ = (d - 2) / (2 * d) := by
      push_cast
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hq2 : (2 : ℝ≥0) < q := by
    rw [← NNReal.coe_lt_coe, hqcoe, NNReal.coe_ofNat, lt_div_iff₀ hd1]
    linarith
  exact exists_measure_truncSupport_ge_of_sobolev hΩb Op hq2
    fun V => eLpNorm_le_of_mem_H01_of_isBounded hΩopen.measurableSet hΩb hd hq V.2

/-- **Uniform lower bound on the measure of `Γ_k` in dimension two**, through the embedding
into `L⁴(Ω)`. -/
theorem exists_measure_truncSupport_ge_two {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : H01 Ω) (u : EuclideanSpace ℝ (Fin 2) → ℝ)
      (g : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ), Measurable u → (∀ i, Measurable (g i)) →
      ∀ k : ℝ, (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin 2) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max (u x - k) 0) →
      0 < (volume.restrict Ω) {x | k < u x} →
      Op.lam * ∑ i : Fin 2, ‖(V : H1amb Ω) i.succ‖ ^ 2
        ≤ Op.Bsup * (∑ i : Fin 2, ‖(V : H1amb Ω) i.succ‖)
          * (eLpNorm ((V : H1amb Ω) 0) 2
              ((volume.restrict Ω).restrict (truncSupport u g k))).toReal →
      c ≤ ((volume.restrict Ω) (truncSupport u g k)).toReal :=
  exists_measure_truncSupport_ge_of_sobolev hΩb Op (q := 4) (by norm_num)
    (C := sobolevConstTwo Ω) fun V => by
    have := eLpNorm_le_of_mem_H01_two hΩopen.measurableSet hΩb V.2
    rwa [ENNReal.coe_ofNat]

/-- **Uniform lower bound on the measure of `Γ_k` in dimension at least two.** -/
theorem exists_measure_truncSupport_ge' (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hd : 2 ≤ d) (Op : FullEllipticOp d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : H01 Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ), Measurable u → (∀ i, Measurable (g i)) →
      ∀ k : ℝ, (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max (u x - k) 0) →
      0 < (volume.restrict Ω) {x | k < u x} →
      Op.lam * ∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖ ^ 2
        ≤ Op.Bsup * (∑ i : Fin d, ‖(V : H1amb Ω) i.succ‖)
          * (eLpNorm ((V : H1amb Ω) 0) 2
              ((volume.restrict Ω).restrict (truncSupport u g k))).toReal →
      c ≤ ((volume.restrict Ω) (truncSupport u g k)).toReal := by
  rcases lt_or_eq_of_le hd with hd' | hd'
  · exact exists_measure_truncSupport_ge hΩopen hΩb hd' Op
  · subst hd'
    exact exists_measure_truncSupport_ge_two hΩopen hΩb Op

/-! ### The weak maximum principle -/

/-- **Weak maximum principle with a transport term** (Gilbarg and Trudinger Theorem 8.1, in
dimension at least two). Let `Ω` be a bounded open set in dimension at least two, `L` a
divergence-form operator with bounded transport term and nonnegative zeroth-order coefficient,
and `U ∈ H¹(Ω)` a weak subsolution, meaning the bilinear pairing of `U` against every
nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If `k ≥ 0` and `(u - k)⁺` is the function coordinate
of some element of `H₀¹(Ω)`, then `u ≤ k` almost everywhere on `Ω`. -/
theorem weak_maximum_principle_transport (hd : 2 ≤ d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x)
    {U : H1amb Ω} (hU : U ∈ W12 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫)
        + ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 Ω, ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) :
    ∀ᵐ x ∂(volume.restrict Ω), (U 0 x : ℝ) ≤ k := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨V₀, hV₀⟩ := hbd
  set u : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (U 0 x : ℝ) with hudef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => (U i.succ x : ℝ) with hgdef
  have hum : Measurable u := (Lp.stronglyMeasurable (U 0)).measurable
  have hgm : ∀ i, Measurable (g i) := fun i => (Lp.stronglyMeasurable (U i.succ)).measurable
  have huint : IntegrableOn u Ω volume := (Lp.memLp (U 0)).integrable one_le_two
  have hgint : ∀ i, IntegrableOn (g i) Ω volume := fun i =>
    (Lp.memLp (U i.succ)).integrable one_le_two
  -- the gradient vanishes almost everywhere on every level set
  have hlevel : ∀ (T : ℝ) (i : Fin d), ∀ᵐ x ∂(volume.restrict Ω), u x = T → g i x = 0 :=
    fun T i => ae_eq_zero_of_eq_const_of_hasWeakGradOn hΩopen huint.locallyIntegrableOn
      (fun i => (hgint i).locallyIntegrableOn) (hasWeakGradOn_of_mem_W12 hU) T i
  -- the uniform lower bound
  obtain ⟨c, hc0, hest⟩ := exists_measure_truncSupport_ge' hΩopen hΩb hd Op
  have hest' : ∀ k', k ≤ k' → 0 < (volume.restrict Ω) {x | k' < u x} →
      c ≤ ((volume.restrict Ω) (truncSupport u g k')).toReal := by
    intro k' hkk' hpos
    obtain ⟨V, hV0, hVi⟩ := exists_truncation_mem_H01 hΩopen hΩb hU V₀ hV₀ hkk'
    have henergy := energy_le_transport Op hc hsub (hk.trans hkk') V hV0 hVi
    exact hest V u g hum hgm k' hV0 hpos henergy
  have hzero := measure_superlevel_eq_zero hum hgm hlevel hc0 hest'
  rw [ae_iff]
  simpa only [not_le] using hzero

end EllipticPdes.Sobolev
