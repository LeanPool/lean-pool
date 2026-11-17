/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.GaussMeasure
public import LeanPool.CCDN.ArithmeticHeights.LogConcave

/-!
# The Gauss measure of a symmetric convex set is at most its volume inside a product of balls

**Bombieri–Gubler, Lemma C.3.7.** Let `Q` be a product of euclidean balls each of volume one, one
factor per block of a partition of the coordinates. Then for every measurable convex symmetric
`A`, the Gauss measure of `A` is at most `vol (A ∩ Q)`. This is the inequality Vaaler's
cube-slicing theorem is extracted from by an `ε`-thickening.

The predicate `HasSliceBound μ g Q` states the conclusion for a measure `μ`, a density `g` and a
set `Q`, in the form that both makes the induction on the number of blocks a `Measure.prod`
statement and makes the base case a one-dimensional comparison along rays.

## Main definitions

* `HasSliceBound μ g Q`: for every measurable convex symmetric `A`,
  `∫⁻ x in A, g x ∂μ ≤ μ (A ∩ Q)`.

## Main results

* `HasSliceBound.lintegral_le`: the bound upgrades from sets to even log-concave functions,
  by the layer cake.
* `hasSliceBound_unitVolumeBall`: **the base case, `r = 1`**, for the ball of volume one.
* `HasSliceBound.prod`: **the induction step**, the case of a product of two blocks.
* `HasSliceBound.of_measurePreserving`: transport along a measure-preserving linear equivalence.

## Implementation notes

⚠ **The base case needs no Gamma function and no closed form for the radius.** Polar decomposition
turns both sides into integrals over the unit sphere; on each ray, a symmetric convex set meets the
ray in an interval, so either the ray's segment of the volume-one ball lies in `A` or the reverse,
and the two cases need only `exp (-π r ^ 2) ≤ 1` and the *equality* of the two radial integrals.
That equality is forced by the two normalizations — the Gauss measure and the ball both have total
mass one — once the sphere measure, a positive finite constant, is cancelled. This is why
Bombieri–Gubler's Remark C.3.6 does not appear.

⚠ **The induction step needs the bound twice, in both factors, because slices of a symmetric set
are not symmetric.** `A_y = {z | (y, z) ∈ A}` satisfies `A_{-y} = -A_y`, not `A_y = -A_y`, so the
bound cannot be applied slice by slice. Bombieri–Gubler's remedy, followed here, is to apply the
upgraded form `HasSliceBound.lintegral_le` once in each factor, with the layer cake of the first
density in between: the superlevel sets of a log-concave even density are convex *and* symmetric,
and the marginals over them are log-concave by Lemma C.3.4 and even because the density is.

⚠ **Closedness of `A` is not needed, only convexity, symmetry and measurability.** Bombieri–Gubler
ask for a closed symmetric convex set, and their approximation argument in the induction step needs
closedness to know the superlevel sets are closed. The layer cake used here replaces that argument,
and the superlevel sets of a log-concave function are convex whether or not they are closed, so the
hypothesis disappears. It is worth having: in the induction step the sets the bound is applied to
are superlevel sets of a marginal, whose closedness would be an upper semicontinuity question.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma C.3.7.

This is Layer 4.5 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Measure Set Metric ENNReal Pointwise
open scoped Real

variable {E F : Type*}

/-- `HasSliceBound μ g Q` says that the measure with density `g` of a measurable convex symmetric
set `A` never exceeds `μ (A ∩ Q)`. With `g` the Gauss density and `Q` a product of balls of volume
one this is Bombieri–Gubler's Lemma C.3.7. -/
@[expose] def HasSliceBound [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) (g : E → ℝ≥0∞) (Q : Set E) : Prop :=
  ∀ A : Set E, MeasurableSet A → Convex ℝ A → (∀ x ∈ A, -x ∈ A) →
    ∫⁻ x in A, g x ∂μ ≤ μ (A ∩ Q)

/-- A set closed under negation equals its own negation. -/
theorem Set.neg_eq_self_of_neg_mem {G : Type*} [InvolutiveNeg G] {A : Set G}
    (h : ∀ x ∈ A, -x ∈ A) : -A = A := by
  ext x
  simp only [Set.mem_neg]
  exact ⟨fun hx => by simpa using h _ hx, fun hx => h x hx⟩

/-- **The slice bound upgrades from sets to even log-concave functions.** Writing `f` as a
superposition of the indicators of its superlevel sets — which are convex because `f` is
log-concave and symmetric because `f` is even — turns the bound for sets into a bound for
integrals. -/
theorem HasSliceBound.lintegral_le [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    {μ : Measure E} [SFinite μ] {g : E → ℝ≥0∞} {Q : Set E}
    (hb : HasSliceBound μ g Q) (hg : Measurable g)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hfe : ∀ x, f (-x) = f x) (hflc : LogConcave f) :
    ∫⁻ x, f x * g x ∂μ ≤ ∫⁻ x in Q, f x ∂μ := by
  have hK : ∀ t : ℝ, MeasurableSet {x : E | ENNReal.ofReal t < f x} := fun t =>
    measurableSet_lt measurable_const hf
  calc ∫⁻ x, f x * g x ∂μ = ∫⁻ x, f x ∂(μ.withDensity g) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hg hf]
        exact lintegral_congr fun x => mul_comm _ _
    _ = ∫⁻ t in Ioi (0 : ℝ), (μ.withDensity g) {x | ENNReal.ofReal t < f x} :=
        lintegral_eq_lintegral_measure_ofReal_lt _ hf
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | ENNReal.ofReal t < f x}, g x ∂μ :=
        lintegral_congr fun t => withDensity_apply g (hK t)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), μ ({x | ENNReal.ofReal t < f x} ∩ Q) :=
        lintegral_mono fun t => hb _ (hK t) (hflc.convex_lt _)
          (fun x hx => by change ENNReal.ofReal t < f (-x); rw [hfe x]; exact hx)
    _ = ∫⁻ t in Ioi (0 : ℝ), (μ.restrict Q) {x | ENNReal.ofReal t < f x} :=
        lintegral_congr fun t => (Measure.restrict_apply (hK t)).symm
    _ = ∫⁻ x, f x ∂(μ.restrict Q) := (lintegral_eq_lintegral_measure_ofReal_lt _ hf).symm

/-- **The base case of Bombieri–Gubler's Lemma C.3.7**, stated for an arbitrary norm: if the Gauss
density has total mass one and the closed ball of radius `ρ` has measure one, then the Gauss
measure of a measurable convex symmetric set is at most its measure inside that ball. -/
theorem hasSliceBound_closedBall [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (hball : μ (closedBall 0 ρ) = 1)
    (hgauss : ∫⁻ x, gaussDensity x ∂μ = 1) :
    HasSliceBound μ gaussDensity (closedBall (0 : E) ρ) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro A hA _ _
    have hcb : closedBall (0 : E) ρ = univ := by
      ext x; simp [Subsingleton.elim x (0 : E), hρ.le]
    have hg : ∀ x : E, gaussDensity x = 1 := fun x => by
      rw [Subsingleton.elim x (0 : E), gaussDensity_zero]
    simp [hg, hcb]
  intro A hA hAconv hAsymm
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have h0 : (0 : E) ∈ A := by
    have := hAconv ha (hAsymm a ha) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  set n := Module.finrank ℝ E with hn
  set W := Measure.volumeIoiPow (n - 1) with hW
  set c : ℝ≥0∞ := ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-π * (r : ℝ) ^ 2)) ∂W with hcdef
  set d : ℝ≥0∞ := W {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} with hddef
  have hnorm : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)), ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    intro u r
    rw [norm_smul, mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs, abs_of_pos r.2]
  have hgsmul : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)),
      gaussDensity ((r : ℝ) • (u : E)) = ENNReal.ofReal (Real.exp (-π * (r : ℝ) ^ 2)) := by
    intro u r; rw [gaussDensity_def, hnorm]
  have hSne : μ.toSphere univ ≠ 0 := by
    simp only [ne_eq, measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero μ
  have hStop : μ.toSphere univ ≠ ⊤ := measure_ne_top _ _
  have hdmeas : MeasurableSet {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} :=
    measurable_subtype_coe measurableSet_Iic
  have claim1 : μ.toSphere univ * c = 1 := by
    rw [← hgauss, lintegral_eq_lintegral_sphere' μ (f := gaussDensity) (by fun_prop),
      show (fun u : sphere (0 : E) 1 => ∫⁻ r : Ioi (0 : ℝ), gaussDensity ((r : ℝ) • (u : E)) ∂W)
        = fun _ => c from funext fun u => lintegral_congr fun r => hgsmul u r,
      lintegral_const, mul_comm]
  have hcbmem : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)),
      ((r : ℝ) • (u : E) ∈ closedBall (0 : E) ρ) ↔ (r : ℝ) ≤ ρ := by
    intro u r; rw [mem_closedBall, dist_zero_right, hnorm]
  have hd1 : ∀ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
      Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W = d := by
    intro u
    have he : (fun r : Ioi (0 : ℝ) =>
        Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)))
        = Set.indicator {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} (fun _ => (1 : ℝ≥0∞)) := by
      funext r
      by_cases h : (r : ℝ) ≤ ρ
      · rw [Set.indicator_of_mem ((hcbmem u r).mpr h),
          Set.indicator_of_mem (show r ∈ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from h)]
      · rw [Set.indicator_of_notMem (fun hm => h ((hcbmem u r).mp hm)),
          Set.indicator_of_notMem (show r ∉ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from h)]
    rw [he, lintegral_indicator hdmeas, setLIntegral_one, hddef]
  have claim2 : μ.toSphere univ * d = 1 := by
    rw [← hball]
    have h1 : μ (closedBall (0 : E) ρ)
        = ∫⁻ x, Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator measurableSet_closedBall, setLIntegral_one]
    rw [h1, lintegral_eq_lintegral_sphere' μ
      (f := Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)))
      (measurable_one.indicator measurableSet_closedBall),
      show (fun u : sphere (0 : E) 1 => ∫⁻ r : Ioi (0 : ℝ),
        Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W)
        = fun _ => d from funext hd1, lintegral_const, mul_comm]
  have hcd : c = d := (ENNReal.mul_right_inj hSne hStop).mp (claim1.trans claim2.symm)
  have key : ∀ u : sphere (0 : E) 1,
      ∫⁻ r : Ioi (0 : ℝ), Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ≤
      ∫⁻ r : Ioi (0 : ℝ),
        Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W := by
    intro u
    by_cases hc : (ρ • (u : E)) ∈ A
    · have hsub : ∀ t : ℝ, 0 < t → t ≤ ρ → (t • (u : E)) ∈ A := by
        intro t ht htρ
        have h1 : (0 : ℝ) ≤ t / ρ := by positivity
        have h2 : (0 : ℝ) ≤ 1 - t / ρ := by
          have : t / ρ ≤ 1 := (div_le_one hρ).mpr htρ
          linarith
        have := hAconv hc h0 h1 h2 (by ring)
        simpa [smul_smul, div_mul_cancel₀ _ hρ.ne'] using this
      have hle : ∫⁻ r : Ioi (0 : ℝ), Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ≤ c :=
        lintegral_mono fun r => (Set.indicator_le_self _ _ _).trans (hgsmul u r).le
      refine hle.trans ?_
      rw [hcd, hddef, ← setLIntegral_one, ← lintegral_indicator hdmeas]
      refine lintegral_mono fun r => ?_
      by_cases hr : (r : ℝ) ≤ ρ
      · rw [Set.indicator_of_mem (show r ∈ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from hr),
          Set.indicator_of_mem (show ((r : ℝ) • (u : E)) ∈ A ∩ closedBall (0 : E) ρ from
            ⟨hsub r r.2 hr, (hcbmem u r).mpr hr⟩)]
      · rw [Set.indicator_of_notMem (show r ∉ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from hr)]
        exact zero_le
    · refine lintegral_mono fun r => ?_
      have hr0 : (0 : ℝ) < (r : ℝ) := r.2
      by_cases hmem : ((r : ℝ) • (u : E)) ∈ A
      · have hr : (r : ℝ) ≤ ρ := by
          by_contra hgt
          refine hc ?_
          have hgt' : ρ < (r : ℝ) := not_le.mp hgt
          have h1 : (0 : ℝ) ≤ ρ / (r : ℝ) := le_of_lt (div_pos hρ hr0)
          have h2 : (0 : ℝ) ≤ 1 - ρ / (r : ℝ) := by
            have : ρ / (r : ℝ) ≤ 1 := (div_le_one hr0).mpr hgt'.le
            linarith
          have := hAconv hmem h0 h1 h2 (by ring)
          simpa [smul_smul, div_mul_cancel₀ _ hr0.ne'] using this
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (show ((r : ℝ) • (u : E)) ∈ A ∩ closedBall (0 : E) ρ from
            ⟨hmem, (hcbmem u r).mpr hr⟩)]
        exact gaussDensity_le_one _
      · rw [Set.indicator_of_notMem hmem]; exact zero_le
  calc ∫⁻ x in A, gaussDensity x ∂μ
      = ∫⁻ x, Set.indicator A gaussDensity x ∂μ := (lintegral_indicator hA _).symm
    _ = ∫⁻ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
          Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ∂μ.toSphere :=
        lintegral_eq_lintegral_sphere' μ (measurable_gaussDensity.indicator hA)
    _ ≤ ∫⁻ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
          Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W
          ∂μ.toSphere := lintegral_mono key
    _ = ∫⁻ x, Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
        (lintegral_eq_lintegral_sphere' μ
          (measurable_one.indicator (hA.inter measurableSet_closedBall))).symm
    _ = μ (A ∩ closedBall (0 : E) ρ) := by
        rw [lintegral_indicator (hA.inter measurableSet_closedBall), setLIntegral_one]

/-- **Bombieri–Gubler's Lemma C.3.7 for a single block**: the Gauss measure of a measurable convex
symmetric set is at most its volume inside the ball of volume one. -/
theorem hasSliceBound_unitVolumeBall [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    HasSliceBound (volume : Measure E) gaussDensity (closedBall (0 : E) (unitVolumeRadius E)) :=
  hasSliceBound_closedBall volume unitVolumeRadius_pos volume_closedBall_unitVolumeRadius
    lintegral_gaussDensity_eq_one

/-- **The induction step of Bombieri–Gubler's Lemma C.3.7.** If the slice bound holds in each
factor, for densities that are log-concave and even, then it holds for the product measure, the
product density and the product of the two sets. -/
theorem HasSliceBound.prod
    [MeasurableSpace E] [AddCommGroup E] [Module ℝ E] [MeasurableNeg E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] [MeasurableNeg F]
    {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    [μ.IsNegInvariant] [ν.IsNegInvariant]
    {g : E → ℝ≥0∞} {h : F → ℝ≥0∞} {Q : Set E} {R : Set F}
    (hg : Measurable g) (hge : ∀ x, g (-x) = g x) (hglc : LogConcave g)
    (hh : Measurable h) (hR : MeasurableSet R)
    (hRc : Convex ℝ R) (hRs : ∀ z ∈ R, -z ∈ R)
    (hPLμ : HasPrekopaLeindler μ) (hPLν : HasPrekopaLeindler ν)
    (hE : HasSliceBound μ g Q) (hF : HasSliceBound ν h R) :
    HasSliceBound (μ.prod ν) (fun p => g p.1 * h p.2) (Q ×ˢ R) := by
  intro A hA hAconv hAsymm
  set K : ℝ → Set E := fun s => {y | ENNReal.ofReal s < g y} with hKdef
  have hKmeas : ∀ s, MeasurableSet (K s) := fun s => measurableSet_lt measurable_const hg
  have hKconv : ∀ s, Convex ℝ (K s) := fun s => hglc.convex_lt _
  have hKsymm : ∀ s, ∀ y ∈ K s, -y ∈ K s := fun s y hy => by
    change ENNReal.ofReal s < g (-y); rw [hge y]; exact hy
  have hAsecE : ∀ z : F, MeasurableSet {y : E | (y, z) ∈ A} := fun z => hA.preimage (by fun_prop)
  have hAsecF : ∀ y : E, MeasurableSet {z : F | (y, z) ∈ A} := fun y => hA.preimage (by fun_prop)
  have hnegE : ∀ z : F, {y : E | (y, -z) ∈ A} = -{y : E | (y, z) ∈ A} := fun z => by
    ext y
    simp only [Set.mem_neg, Set.mem_ofPred_eq]
    exact ⟨fun hy => by simpa using hAsymm _ hy, fun hy => by simpa using hAsymm _ hy⟩
  have hnegF : ∀ y : E, {z : F | (-y, z) ∈ A} = -{z : F | (y, z) ∈ A} := fun y => by
    ext z
    simp only [Set.mem_neg, Set.mem_ofPred_eq]
    exact ⟨fun hz => by simpa using hAsymm _ hz, fun hz => by simpa using hAsymm _ hz⟩
  have hRneg : (-R : Set F) = R := Set.neg_eq_self_of_neg_mem hRs
  have hKneg : ∀ s, (-(K s) : Set E) = K s := fun s => Set.neg_eq_self_of_neg_mem (hKsymm s)
  set f : E → ℝ≥0∞ := fun y => (ν.restrict R) {z | (y, z) ∈ A} with hfdef
  set θ : ℝ → F → ℝ≥0∞ := fun s z => (μ.restrict (K s)) {y | (y, z) ∈ A} with hθdef
  have hfmeas : Measurable f := measurable_measure_prodMk_left hA
  have hθmeas : ∀ s, Measurable (θ s) := fun s => measurable_measure_prodMk_right hA
  have hΘmeas : Measurable fun p : F × ℝ => θ p.2 p.1 := by
    have hS : MeasurableSet {q : E × (F × ℝ) |
        ENNReal.ofReal q.2.2 < g q.1 ∧ (q.1, q.2.1) ∈ A} :=
      (measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.comp measurable_snd))
        (hg.comp measurable_fst)).inter (hA.preimage (by fun_prop))
    have heq : (fun p : F × ℝ => θ p.2 p.1)
        = fun p : F × ℝ => μ ((fun y => (y, p)) ⁻¹'
          {q : E × (F × ℝ) | ENNReal.ofReal q.2.2 < g q.1 ∧ (q.1, q.2.1) ∈ A}) := by
      funext p
      rw [hθdef]
      simp only
      rw [Measure.restrict_apply' (hKmeas p.2)]
      congr 1
      ext y
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    rw [heq]
    exact measurable_measure_prodMk_right hS
  have hfeven : ∀ y, f (-y) = f y := fun y => by
    rw [hfdef]
    simp only
    rw [hnegF y, Measure.restrict_apply (hAsecF y).neg, Measure.restrict_apply (hAsecF y),
      show (-{z : F | (y, z) ∈ A} ∩ R) = -({z : F | (y, z) ∈ A} ∩ R) by
        rw [inter_neg, hRneg], measure_neg]
  have hθeven : ∀ s z, θ s (-z) = θ s z := fun s z => by
    rw [hθdef]
    simp only
    rw [hnegE z, Measure.restrict_apply' (hKmeas s), Measure.restrict_apply' (hKmeas s),
      show (-{y : E | (y, z) ∈ A} ∩ K s) = -({y : E | (y, z) ∈ A} ∩ K s) by
        rw [inter_neg, hKneg], measure_neg]
  have hindA : LogConcave (Set.indicator A (fun _ => (1 : ℝ≥0∞))) := logConcave_indicator hAconv 1
  have hindAmeas : Measurable (Set.indicator A (fun _ => (1 : ℝ≥0∞))) := measurable_one.indicator hA
  have hfeq : (fun y => ∫⁻ z in R, Set.indicator A (fun _ => (1 : ℝ≥0∞)) (y, z) ∂ν) = f := by
    funext y
    rw [show (fun z => Set.indicator A (fun _ => (1 : ℝ≥0∞)) (y, z))
        = Set.indicator {z | (y, z) ∈ A} (fun _ => (1 : ℝ≥0∞)) from rfl,
      lintegral_indicator (hAsecF y), setLIntegral_one, hfdef]
  have hflc : LogConcave f :=
    hfeq ▸ LogConcave.setLIntegral_prod_right hPLν hindAmeas hindA hR hRc
  have hAswapconv : Convex ℝ {q : F × E | (q.2, q.1) ∈ A} :=
    fun _ h1 _ h2 _ _ ha hb hab => hAconv h1 h2 ha hb hab
  have hindA' : LogConcave (Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞))) :=
    logConcave_indicator hAswapconv 1
  have hindA'meas :
      Measurable (Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞))) :=
    measurable_one.indicator (hA.preimage (by fun_prop))
  have hθlc : ∀ s, LogConcave (θ s) := fun s => by
    have heq : (fun z => ∫⁻ y in K s,
        Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞)) (z, y) ∂μ) = θ s := by
      funext z
      rw [show (fun y => Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞)) (z, y))
          = Set.indicator {y | (y, z) ∈ A} (fun _ => (1 : ℝ≥0∞)) from rfl,
        lintegral_indicator (hAsecE z), setLIntegral_one, hθdef]
    exact heq ▸ LogConcave.setLIntegral_prod_right hPLμ hindA'meas hindA' (hKmeas s) (hKconv s)
  have hlayer : ∀ S : Set E, MeasurableSet S →
      ∫⁻ y in S, g y ∂μ = ∫⁻ s in Ioi (0 : ℝ), (μ.restrict (K s)) S := by
    intro S _
    rw [lintegral_eq_lintegral_measure_ofReal_lt (μ.restrict S) hg]
    refine lintegral_congr fun s => ?_
    rw [Measure.restrict_apply (hKmeas s), Measure.restrict_apply' (hKmeas s), Set.inter_comm]
  have hW1 : Measurable (Set.indicator A (fun p : E × F => g p.1 * h p.2)) :=
    ((hg.comp measurable_fst).mul (hh.comp measurable_snd)).indicator hA
  have hW2 : Measurable (Set.indicator A (fun p : E × F => g p.1)) :=
    (hg.comp measurable_fst).indicator hA
  have hθs : ∀ z, Measurable fun s => θ s z := fun _ => hΘmeas.comp measurable_prodMk_left
  calc ∫⁻ x in A, g x.1 * h x.2 ∂(μ.prod ν)
      = ∫⁻ z, (∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ) * h z ∂ν := by
        rw [← lintegral_indicator hA, lintegral_prod _ hW1.aemeasurable,
          lintegral_lintegral_swap
            (f := fun (y : E) (z : F) =>
              Set.indicator A (fun p : E × F => g p.1 * h p.2) (y, z)) hW1.aemeasurable]
        refine lintegral_congr fun z => ?_
        rw [show (fun y => Set.indicator A (fun p : E × F => g p.1 * h p.2) (y, z))
            = Set.indicator {y | (y, z) ∈ A} (fun y => g y * h z) from rfl,
          lintegral_indicator (hAsecE z), lintegral_mul_const _ hg]
    _ = ∫⁻ z, (∫⁻ s in Ioi (0 : ℝ), θ s z * h z) ∂ν := by
        refine lintegral_congr fun z => ?_
        rw [hlayer _ (hAsecE z), ← lintegral_mul_const _ (hθs z)]
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z, θ s z * h z ∂ν :=
        lintegral_lintegral_swap (f := fun (z : F) (s : ℝ) => θ s z * h z)
          (hΘmeas.mul (hh.comp measurable_fst)).aemeasurable
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z in R, θ s z ∂ν :=
        lintegral_mono fun s => hF.lintegral_le hh (hθmeas s) (hθeven s) (hθlc s)
    _ = ∫⁻ z in R, (∫⁻ s in Ioi (0 : ℝ), θ s z) ∂ν :=
        lintegral_lintegral_swap (f := fun (s : ℝ) (z : F) => θ s z)
          (hΘmeas.comp measurable_swap).aemeasurable
    _ = ∫⁻ z in R, (∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ) ∂ν :=
        lintegral_congr fun z => (hlayer _ (hAsecE z)).symm
    _ = ∫⁻ y, f y * g y ∂μ := by
        have h1 : ∀ z : F, ∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ
            = ∫⁻ y, Set.indicator A (fun p : E × F => g p.1) (y, z) ∂μ := by
          intro z
          rw [show (fun y => Set.indicator A (fun p : E × F => g p.1) (y, z))
              = Set.indicator {y | (y, z) ∈ A} (fun y => g y) from rfl,
            lintegral_indicator (hAsecE z)]
        simp only [h1]
        rw [lintegral_lintegral_swap (μ := ν.restrict R) (ν := μ)
          (f := fun z y => Set.indicator A (fun p : E × F => g p.1) (y, z))
          (hW2.comp measurable_swap).aemeasurable]
        refine lintegral_congr fun y => ?_
        rw [show (fun z => Set.indicator A (fun p : E × F => g p.1) (y, z))
            = Set.indicator {z | (y, z) ∈ A} (fun _ => g y) from rfl,
          lintegral_indicator (hAsecF y), setLIntegral_const, hfdef, mul_comm]
    _ ≤ ∫⁻ y in Q, f y ∂μ := hE.lintegral_le hg hfmeas hfeven hflc
    _ = (μ.prod ν) (A ∩ (Q ×ˢ R)) := by
        rw [← Measure.restrict_apply hA, ← Measure.prod_restrict, Measure.prod_apply hA]
        rfl

/-- The slice bound transports along a measure-preserving linear equivalence. -/
theorem HasSliceBound.of_measurePreserving [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ₗ[ℝ] F) (he : MeasurePreserving e μ ν) (hsymm : Measurable e.symm)
    {g : F → ℝ≥0∞} (hg : Measurable g) {Q : Set F} (hQ : MeasurableSet Q)
    (hb : HasSliceBound ν g Q) :
    HasSliceBound μ (fun x => g (e x)) (e ⁻¹' Q) := by
  intro A hA hAconv hAsymm
  have hBA : e ⁻¹' (e.symm ⁻¹' A) = A := by ext x; simp
  have hBmeas : MeasurableSet (e.symm ⁻¹' A) := hsymm hA
  have hBconv : Convex ℝ (e.symm ⁻¹' A) := hAconv.linear_preimage (e.symm : F →ₗ[ℝ] E)
  have hBsymm : ∀ y ∈ e.symm ⁻¹' A, -y ∈ e.symm ⁻¹' A := by
    intro y hy
    have : e.symm (-y) = -(e.symm y) := map_neg _ _
    simpa [Set.mem_preimage, this] using hAsymm _ hy
  have h1 : ∫⁻ x in A, g (e x) ∂μ = ∫⁻ y in e.symm ⁻¹' A, g y ∂ν := by
    rw [← lintegral_indicator hBmeas, ← he.lintegral_comp (hg.indicator hBmeas),
      ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show e x ∈ e.symm ⁻¹' A by simpa using hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show e x ∉ e.symm ⁻¹' A by simpa using hx)]
  have h2 : μ (A ∩ e ⁻¹' Q) = ν (e.symm ⁻¹' A ∩ Q) := by
    have hpre : A ∩ e ⁻¹' Q = e ⁻¹' (e.symm ⁻¹' A ∩ Q) := by rw [Set.preimage_inter, hBA]
    rw [hpre, he.measure_preimage (hBmeas.inter hQ).nullMeasurableSet]
  rw [h1, h2]
  exact hb _ hBmeas hBconv hBsymm
