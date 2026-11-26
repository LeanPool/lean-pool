/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.TameDisc
public import LeanPool.GraphMinor.GM07.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Pushing a collar across an annulus

The step of Graph Minors VII, (6.1), page 238: "Loosely, we regard $\Sigma'$ as a subset of
$\Sigma$" and "By replacing $H$ by a homotopic forest if necessary".
We take two annuli that share their outer circle, the second inside the first. Then the part of the
surface off the inner annulus is the image of the whole
surface under a map `h` that fixes everything off the outer annulus, and `h` is homotopic to the
identity. The annuli are given by charts on `1 ≤ ‖z‖ ≤ 2`.

We twist the first chart so that the path traced by a chosen point of the inner circle is homotopic
to a chosen path `Q` (`exists_collar_push`). This needs a lift of the angle of `Q`, and a straight
line homotopy in polar coordinates.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface

universe u

/-- The annulus `1 ≤ ‖z‖ ≤ 2`. -/
def collarAnnulus : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

/-- The annulus without its outer circle. -/
def collarOpen : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ < 2}

/-- The radial push of the annulus onto its outer circle. -/
noncomputable def radialPush (t : ℝ) (z : ℂ) : ℂ := (((1 - t) * ‖z‖ + 2 * t : ℝ) : ℂ) * dirOf z

theorem collarOpen_subset : collarOpen ⊆ collarAnnulus := fun _ hz => ⟨hz.1, hz.2.le⟩

theorem ne_zero_of_mem_collar {z : ℂ} (hz : z ∈ collarAnnulus) : z ≠ 0 := fun h => by
  have := hz.1
  rw [h, norm_zero] at this
  linarith

theorem norm_real_mul_dirOf {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : z ≠ 0) : ‖(r : ℂ) * dirOf z‖ = r
  := by
  rw [norm_mul, norm_dirOf hz, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

theorem norm_radialPush {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℂ} (hz : z ∈ collarAnnulus) :
  ‖radialPush t z‖ = (1 - t) * ‖z‖ + 2 * t := by
  have h1 := hz.1
  refine norm_real_mul_dirOf ?_ (ne_zero_of_mem_collar hz)
  nlinarith

theorem radialPush_mem {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℂ} (hz : z ∈ collarAnnulus) :
  radialPush t z ∈ collarAnnulus := by
  have h1 := hz.1
  have h2 := hz.2
  have := norm_radialPush ht0 ht1 hz
  constructor <;> rw [this] <;> nlinarith

theorem radialPush_zero {z : ℂ} (hz : z ≠ 0) : radialPush 0 z = z := by
  have := eq_mul_dirOf hz
  simp only [radialPush]
  rw [show ((1 - 0) * ‖z‖ + 2 * 0 : ℝ) = ‖z‖ by ring]
  exact this.symm

theorem radialPush_of_norm {t : ℝ} {z : ℂ} (hz : ‖z‖ = 2) : radialPush t z = z := by
  have h0 : z ≠ 0 := fun h => by
    rw [h, norm_zero] at hz
    norm_num at hz
  have := eq_mul_dirOf h0
  simp only [radialPush]
  rw [show ((1 - t) * ‖z‖ + 2 * t : ℝ) = ‖z‖ by rw [hz]; ring]
  exact this.symm

theorem continuousOn_radialPush : ContinuousOn (fun q : ℝ × ℂ => radialPush q.1 q.2)
  (univ ×ˢ collarAnnulus) := by
  have h : ContinuousOn (fun q : ℝ × ℂ => dirOf q.2) (univ ×ˢ collarAnnulus) :=
    continuousOn_dirOf.comp continuous_snd.continuousOn fun q hq => ne_zero_of_mem_collar hq.2
  simp only [radialPush]
  refine ContinuousOn.mul ?_ h
  exact Complex.continuous_ofReal.comp_continuousOn (by fun_prop)

variable {S : Type*} [TopologicalSpace S]

/-- A chart of an annulus in `S`. -/
structure IsCollarChart (c : ℂ → S) (c' : S → ℂ) : Prop where
  cont : ContinuousOn c collarAnnulus
  cont' : ContinuousOn c' (c '' collarAnnulus)
  left : LeftInvOn c' c collarAnnulus

theorem IsCollarChart.injOn {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c') : InjOn c
  collarAnnulus :=
  h.left.injOn

theorem IsCollarChart.mem_of_mem {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c') {x : S}
  (hx : x ∈ c '' collarAnnulus) : c' x ∈ collarAnnulus ∧ c (c' x) = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [h.left hz]
  exact ⟨hz, rfl⟩

/-- A self map of the annulus that keeps norms carries a chart to a chart. -/
theorem IsCollarChart.comp {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c') {f f' : ℂ → ℂ}
  (hf : ContinuousOn f collarAnnulus) (hf' : ContinuousOn f' collarAnnulus)
    (hn : ∀ z ∈ collarAnnulus, ‖f z‖ = ‖z‖) (hn' : ∀ z ∈ collarAnnulus, ‖f' z‖ = ‖z‖)
      (hl : ∀ z ∈ collarAnnulus, f' (f z) = z) (hr : ∀ z ∈ collarAnnulus, f (f' z) = z) :
    IsCollarChart (c ∘ f) (f' ∘ c') := by
  have hm : MapsTo f collarAnnulus collarAnnulus := fun z hz => ⟨(hn z hz).ge.trans' hz.1,
    (hn z hz).le.trans hz.2⟩
  have hm' : MapsTo f' collarAnnulus collarAnnulus := fun z hz => ⟨(hn' z hz).ge.trans' hz.1,
    (hn' z hz).le.trans hz.2⟩
  have him : ∀ B : Set ℂ, B ⊆ collarAnnulus → (∀ z ∈ collarAnnulus, f z ∈ B ↔ z ∈ B) → (c ∘ f) '' B
    = c '' B := fun B hB hiff => by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨f z, (hiff z (hB hz)).mpr hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f' z, ?_, by simp [hr z (hB hz)]⟩
      refine (hiff _ (hm' (hB hz))).mp ?_
      rwa [hr z (hB hz)]
  have hA : (c ∘ f) '' collarAnnulus = c '' collarAnnulus := him _ Subset.rfl fun z hz => ⟨fun _
    => hz, fun _ => hm hz⟩
  refine ⟨h.cont.comp hf hm, ?_, fun z hz => ?_⟩
  · rw [hA]
    exact hf'.comp h.cont' fun x hx => (h.mem_of_mem hx).1
  · simp [h.left (hm hz), hl z hz]

/-- The map that fixes the point off the open annulus, and is `E ∘ c'` on it. -/
noncomputable def chartSwap (c E : ℂ → S) (c' : S → ℂ) (x : S) : S := open Classical in if x ∈ c ''
  collarOpen then E (c' x) else x

/-- The radial push of the annulus in `S`. -/
noncomputable def chartPush (c : ℂ → S) (c' : S → ℂ) (t : ℝ) (x : S) : S
  := open Classical in if x ∈ c '' collarOpen then c (radialPush t (c' x)) else x

/-- Gluing a map on the annulus to a map off its open part. -/
theorem continuous_glue {W : Type*} [TopologicalSpace W] [T2Space S] {c : ℂ
  → S} {c' : S → ℂ} (h : IsCollarChart c c') (hO : IsOpen (c '' collarOpen)) {π : W → S}
    (hπ : Continuous π)
    {f g : W → S} (hf : ContinuousOn f (π ⁻¹' (c '' collarAnnulus))) (hg : ContinuousOn g (π ⁻¹'
      (c '' collarOpen)ᶜ)) (he : ∀ w, ∀ z, ‖z‖ = 2 → z ∈ collarAnnulus → π w = c z → f w = g w) :
    Continuous fun w => open Classical in if π w ∈ c '' collarOpen then f w else g w := by
  classical
  have hcA : IsClosed (c '' collarAnnulus) := by
    have hK : IsCompact collarAnnulus := by
      refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
      · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm
          continuous_const)
      · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz
          => by simpa using hz.2
    exact (hK.image_of_continuousOn h.cont).isClosed
  have hsub : c '' collarOpen ⊆ c '' collarAnnulus := image_mono collarOpen_subset
  have hO' : IsOpen (π ⁻¹' (c '' collarOpen)) := hO.preimage hπ
  have hcl : closure {w | π w ∈ c '' collarOpen} ⊆ π ⁻¹' (c '' collarAnnulus) :=
    closure_minimal (fun w hw => hsub hw) (hcA.preimage hπ)
  have hcl' : closure {w | ¬ π w ∈ c '' collarOpen} ⊆ π ⁻¹' (c '' collarOpen)ᶜ :=
    closure_minimal (fun w hw => hw) hO'.isClosed_compl
  refine continuous_if ?_ (hf.mono hcl) (hg.mono hcl')
  intro w hw
  have h1 : w ∈ closure {w | π w ∈ c '' collarOpen} := hw.1
  have h2 : w ∉ π ⁻¹' (c '' collarOpen) := fun hc => by
    have := hO'.frontier_eq ▸ hw
    exact this.2 hc
  obtain ⟨z, hz, hzw⟩ := hcl h1
  refine he w z ?_ hz hzw.symm
  refine le_antisymm hz.2 (not_lt.mp fun hlt => h2 ⟨z, ⟨hz.1, hlt⟩, hzw⟩)

variable [T2Space S] [CompactSpace S]

omit [T2Space S] [CompactSpace S] in
theorem IsCollarChart.outer_not_mem {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c') {z : ℂ}
  (hz : z ∈ collarAnnulus) (h2 : ‖z‖ = 2) : c z ∉ c '' collarOpen := by
  rintro ⟨y, hy, he⟩
  have := h.injOn (collarOpen_subset hy) hz he
  rw [this] at hy
  exact hy.2.ne h2

omit [T2Space S] [CompactSpace S] in
theorem chartPush_zero {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c')
  (x : S) : chartPush c c' 0 x = x := by
  classical
  simp only [chartPush]
  split_ifs with hx
  · obtain ⟨hz, hzx⟩ := h.mem_of_mem (image_mono collarOpen_subset hx)
    rw [radialPush_zero (ne_zero_of_mem_collar hz), hzx]
  · rfl

omit [CompactSpace S] in
theorem continuous_chartPush {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c') (hO : IsOpen
  (c '' collarOpen)) {W : Type*} [TopologicalSpace W] {t : W → ℝ} {π : W → S} (ht : Continuous t)
    (hπ : Continuous π)
    (ht0 : ∀ w, 0 ≤ t w) (ht1 : ∀ w, t w ≤ 1) : Continuous fun w => chartPush c c' (t w) (π w) := by
  have h1 : ContinuousOn (fun w => c' (π w)) (π ⁻¹' (c '' collarAnnulus))
    := h.cont'.comp hπ.continuousOn fun w hw => hw
  have h2 : ContinuousOn (fun w => radialPush (t w) (c' (π w))) (π ⁻¹' (c '' collarAnnulus)) :=
    continuousOn_radialPush.comp (ht.continuousOn.prodMk h1) fun w hw => ⟨mem_univ _,
      (h.mem_of_mem hw).1⟩
  have h3 : ContinuousOn (fun w => c (radialPush (t w) (c' (π w)))) (π ⁻¹' (c '' collarAnnulus)) :=
    h.cont.comp h2 fun w hw => radialPush_mem (ht0 w) (ht1 w) (h.mem_of_mem hw).1
  refine continuous_glue h hO hπ h3 hπ.continuousOn fun w z hz hzA he => ?_
  rw [he, h.left hzA, radialPush_of_norm hz]

omit [CompactSpace S] in
theorem continuous_chartSwap {c E : ℂ → S} {c' E' : S → ℂ} (h : IsCollarChart c c') (hO : IsOpen
  (c '' collarOpen)) (hE : IsCollarChart E E') (he : ∀ z, ‖z‖ = 2 → E z = c z) : Continuous
    (chartSwap c E c') := by
  have h1 : ContinuousOn (fun x => E (c' x)) (c '' collarAnnulus) := hE.cont.comp h.cont' fun x hx
    => (h.mem_of_mem hx).1
  refine continuous_glue h hO continuous_id h1 continuousOn_id fun x z hz hzA hx => ?_
  rw [id] at hx
  rw [hx, h.left hzA, he z hz]

omit [TopologicalSpace S] [T2Space S] [CompactSpace S] in
theorem chartSwap_of_not_mem {c E : ℂ → S} {c' : S → ℂ} {x : S} (hx : x ∉ c '' collarOpen) :
  chartSwap c E c' x = x := by
  classical
  simp only [chartSwap, ite_eq_right hx]

omit [TopologicalSpace S] [T2Space S] [CompactSpace S] in
theorem chartPush_of_not_mem {c : ℂ → S} {c' : S → ℂ} {t : ℝ} {x : S}
  (hx : x ∉ c '' collarOpen) : chartPush c c' t x = x := by
  classical
  simp only [chartPush, ite_eq_right hx]

omit [T2Space S] [CompactSpace S] in
theorem chartPush_one_not_mem {c : ℂ → S} {c' : S → ℂ} (h : IsCollarChart c c')
  (x : S) : chartPush c c' 1 x ∉ c '' collarOpen := by
  classical
  simp only [chartPush]
  split_ifs with hx
  · obtain ⟨hz, -⟩ := h.mem_of_mem (image_mono collarOpen_subset hx)
    refine h.outer_not_mem (radialPush_mem zero_le_one le_rfl hz) ?_
    rw [norm_radialPush zero_le_one le_rfl hz]
    ring
  · exact hx

/-- The homotopy from the identity to `chartSwap`: push out to the outer circle, then come back by
`chartSwap`. -/
noncomputable def collarHomotopy (c E : ℂ → S) (c' : S → ℂ) (q : ℝ × S) : S :=
  if q.1 ≤ 1 / 2 then chartPush c c' (2 * q.1) q.2 else chartSwap c E c' (chartPush c c'
    (2 - 2 * q.1) q.2)

omit [CompactSpace S] in
theorem continuous_collarHomotopy {c E : ℂ → S} {c' E' : S → ℂ} (h : IsCollarChart c c')
  (hO : IsOpen (c '' collarOpen)) (hE : IsCollarChart E E') (he : ∀ z, ‖z‖ = 2 → E z = c z) :
    Continuous fun q : unitInterval × S => collarHomotopy c E c' (q.1.1, q.2) := by
  let p : unitInterval × S → ℝ := fun q => max 0 (min 1 (2 * q.1.1))
  let p' : unitInterval × S → ℝ := fun q => max 0 (min 1 (2 - 2 * q.1.1))
  have hp : Continuous p := by fun_prop
  have hp' : Continuous p' := by fun_prop
  have hp0 : ∀ q, 0 ≤ p q := fun q => le_max_left _ _
  have hp1 : ∀ q, p q ≤ 1 := fun q => max_le zero_le_one (min_le_left _ _)
  have hp0' : ∀ q, 0 ≤ p' q := fun q => le_max_left _ _
  have hp1' : ∀ q, p' q ≤ 1 := fun q => max_le zero_le_one (min_le_left _ _)
  have c1 := continuous_chartPush h hO hp continuous_snd hp0 hp1
  have c2 := (continuous_chartSwap h hO hE he).comp (continuous_chartPush h hO hp' continuous_snd
    hp0' hp1')
  have hmain : Continuous fun q : unitInterval × S => if q.1.1 ≤ 1 / 2 then chartPush c c'
    (p q) q.2 else (chartSwap c E c' ∘ fun q => chartPush c c' (p' q) q.2) q := by
    refine Continuous.if_le c1 c2 (by fun_prop) continuous_const ?_
    intro q hq
    have h1 : p q = 1 := by
      simp only [p]
      rw [hq]
      norm_num
    have h2 : p' q = 1 := by
      simp only [p']
      rw [hq]
      norm_num
    simp only [comp_apply]
    rw [h1, h2, chartSwap_of_not_mem (chartPush_one_not_mem h _)]
  convert hmain using 2 with q
  simp only [collarHomotopy, comp_apply]
  split_ifs with hq
  · have ht0 := q.1.2.1
    have h1 : p q = 2 * q.1.1 := by
      simp only [p]
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    rw [h1]
  · have ht1 := q.1.2.2
    have h1 : p' q = 2 - 2 * q.1.1 := by
      simp only [p']
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    rw [h1]

/-- The twist of the annulus by the angle `κ` on the outer circle. -/
noncomputable def collarTwist (κ : ℝ) (z : ℂ) : ℂ := z * Complex.exp (((κ *
  (‖z‖ - 1) : ℝ) : ℂ) * Complex.I)

theorem norm_collarTwist (κ : ℝ) (z : ℂ) : ‖collarTwist κ z‖ = ‖z‖ := by
  rw [collarTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_collarTwist (κ : ℝ) : Continuous (collarTwist κ) := by
  unfold collarTwist
  fun_prop

theorem collarTwist_neg (κ : ℝ) (z : ℂ) : collarTwist (-κ) (collarTwist κ z) = z := by
  rw [collarTwist, norm_collarTwist, collarTwist, mul_assoc, ← Complex.exp_add]
  have : ((κ * (‖z‖ - 1) : ℝ) : ℂ) * Complex.I + ((-κ * (‖z‖ - 1) : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    ring
  rw [this, Complex.exp_zero, mul_one]

/-- A map of the annulus that keeps radii, given by a map `u` from the unit circle to the circle of
radius 2. -/
noncomputable def fiberMap (u : ℂ → ℂ) (z : ℂ) : ℂ := ((‖z‖ / 2 : ℝ) : ℂ) * u (dirOf z)

theorem continuousOn_fiberMap {u : ℂ → ℂ} (hu : ContinuousOn u {w | ‖w‖ = 1}) : ContinuousOn
  (fiberMap u) collarAnnulus := by
  have h1 : ContinuousOn dirOf collarAnnulus := continuousOn_dirOf.mono fun z hz
    => ne_zero_of_mem_collar hz
  have h2 : ContinuousOn (fun z => u (dirOf z)) collarAnnulus := hu.comp h1 fun z hz => norm_dirOf
    (ne_zero_of_mem_collar hz)
  unfold fiberMap
  refine ContinuousOn.mul ?_ h2
  exact Complex.continuous_ofReal.comp_continuousOn (by fun_prop)

theorem norm_fiberMap {u : ℂ → ℂ} (hn : ∀ w, ‖w‖ = 1 → ‖u w‖ = 2) {z : ℂ}
  (hz : z ∈ collarAnnulus) : ‖fiberMap u z‖ = ‖z‖ := by
  have h0 := ne_zero_of_mem_collar hz
  rw [fiberMap, norm_mul, hn _ (norm_dirOf h0), Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  ring

theorem dirOf_fiberMap {u : ℂ → ℂ} (hn : ∀ w, ‖w‖ = 1 → ‖u w‖ = 2) {z : ℂ}
  (hz : z ∈ collarAnnulus) : dirOf (fiberMap u z) = u (dirOf z) / 2 := by
  have h0 := ne_zero_of_mem_collar hz
  have h1 := norm_fiberMap hn hz
  have h2 : (‖z‖ : ℂ) ≠ 0 := by simpa using h0
  have h3 : fiberMap u z ≠ 0 := by
    rw [← norm_ne_zero_iff, h1]
    exact norm_ne_zero_iff.mpr h0
  have h4 := eq_mul_dirOf h3
  rw [h1] at h4
  nth_rw 1 [fiberMap] at h4
  push_cast at h4
  have h5 : (‖z‖ : ℂ) * (u (dirOf z) / 2) = (‖z‖ : ℂ) * dirOf (fiberMap u z) := by
    rw [← h4]
    ring
  exact (mul_left_cancel₀ h2 h5).symm

theorem fiberMap_inv {u v : ℂ → ℂ} (hn : ∀ w, ‖w‖ = 1 → ‖u w‖ = 2) (huv : ∀ w, ‖w‖ = 1 → v
  (u w / 2) = 2 * w) {z : ℂ} (hz : z ∈ collarAnnulus) : fiberMap v (fiberMap u z) = z := by
  have h0 := ne_zero_of_mem_collar hz
  rw [fiberMap, norm_fiberMap hn hz, dirOf_fiberMap hn hz, huv _ (norm_dirOf h0)]
  nth_rw 3 [eq_mul_dirOf h0]
  push_cast
  ring

theorem path_homotopic_of_map {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y} {H :
  unitInterval × unitInterval → X} (hH : Continuous H) (h0 : ∀ t, H (0, t) = p t) (h1 : ∀ t, H
    (1, t) = q t)
    (hx : ∀ u, H (u, 0) = x) (hy : ∀ u, H (u, 1) = y) : p.Homotopic q := by
  refine ⟨⟨⟨⟨H, hH⟩, ?_, ?_⟩, ?_⟩⟩
  · intro t
    simpa using h0 t
  · intro t
    simpa using h1 t
  · rintro u t (rfl | rfl)
    · simpa using hx u
    · simpa using hy u

private theorem collar_inclusion_from_open_and_outer_images
    {S : Type*}
    {c : ℂ → S}
    {e : ℂ → S}
    (hout : e '' {z | ‖z‖ = 2} = c '' {z | ‖z‖ = 2})
    (hsub : e '' collarOpen ⊆ c '' collarOpen) :
    e '' collarAnnulus ⊆ c '' collarAnnulus := by
  rintro _ ⟨z, hz, rfl⟩
  rcases hz.2.lt_or_eq with hlt | heq
  · exact image_mono collarOpen_subset (hsub ⟨z, ⟨hz.1, hlt⟩, rfl⟩)
  · obtain ⟨y, hy, hye⟩ := hout.le ⟨z, heq, rfl⟩
    exact ⟨y, ⟨by rw [show ‖y‖ = 2 from hy]; norm_num, (show ‖y‖ = 2 from hy).le⟩, hye⟩

private theorem adjusted_collar_agrees_on_outer_circle
    {S : Type*}
    {e : ℂ → S}
    {e' : S → ℂ}
    (t₁ : ℂ → S)
    (hemem : ∀ x ∈ e '' {z | ‖z‖ = 2}, ‖e' x‖ = 2 ∧ e (e' x) = x)
    (hto : ∀ {w : ℂ}, ‖w‖ = 1 → t₁ (2 * w) ∈ e '' {z | ‖z‖ = 2})
    (hs2 : {z | ‖z‖ = 2} ⊆ collarAnnulus)
    (z : ℂ)
    (hz : ‖z‖ = 2) :
    (e ∘ fiberMap (fun w => e' (t₁ (2 * w)))) z = t₁ z := by
  let u := fun w => e' (t₁ (2 * w))
  have hzA : z ∈ collarAnnulus := hs2 hz
  have hdn : ‖dirOf z‖ = 1 := norm_dirOf (ne_zero_of_mem_collar hzA)
  have h2d : 2 * dirOf z = z := by
    nth_rw 2 [eq_mul_dirOf (ne_zero_of_mem_collar hzA)]
    rw [hz]
    norm_num
  have hf : fiberMap u z = u (dirOf z) := by
    rw [fiberMap, hz]
    norm_num
  change e (fiberMap u z) = t₁ z
  rw [hf]
  change e (e' (t₁ (2 * dirOf z))) = t₁ z
  rw [h2d]
  simpa only [h2d] using (hemem _ (hto hdn)).2

private theorem lifted_angle_gives_collar_homotopy
    {S : Type*}
    [TopologicalSpace S]
    {c : ℂ → S}
    {e : ℂ → S}
    {c' : S → ℂ}
    (hc : IsCollarChart c c')
    {w₀ : ℂ}
    {w₁ : ℂ}
    (h₀ : ‖w₀‖ = 1)
    (L : Path (c w₀) (e (2 * w₁)))
    (ℓ : ↑unitInterval → ℂ)
    (hℓc : Continuous ℓ)
    (hℓA : ∀ (t : ↑unitInterval), ℓ t ∈ collarAnnulus)
    (hℓe : ∀ (t : ↑unitInterval), c (ℓ t) = L t)
    (hℓ0 : ℓ 0 = w₀)
    (hℓn1 : ‖ℓ 1‖ = 2)
    (θ : C(↑unitInterval, ℝ))
    (hθ : ∀ (t : ↑unitInterval), Complex.exp (↑(θ t) * Complex.I) = dirOf (ℓ t))
    (hθ0 : Complex.exp (↑(θ 0) * Complex.I) = w₀)
    (hθ1 : Complex.exp (↑(θ 1) * Complex.I) = ℓ 1 / 2)
    (R₁' : Path (c w₀) (e (2 * w₁)))
    (hR₁' : ∀ (t : unitInterval),
      R₁' t = (c ∘ collarTwist (θ 1 - θ 0)) (((1 + (t : ℝ) : ℝ) : ℂ) * w₀)) :
    L.Homotopic R₁' := by
  let κ := θ 1 - θ 0
  let t₁ := c ∘ collarTwist κ
  let hz : unitInterval × unitInterval → ℂ := fun q => (((1 - q.1.1) * ‖ℓ q.2‖ + q.1.1 *
    (1 + q.2.1) : ℝ) : ℂ) *
      Complex.exp ((((1 - q.1.1) * θ q.2 + q.1.1 * (θ 0 + κ * q.2.1) : ℝ) : ℂ) * Complex.I)
  have hzc : Continuous hz := by
    simp only [hz]
    have := θ.continuous
    fun_prop
  have hzA : ∀ q, hz q ∈ collarAnnulus := fun q => by
    have hn : ‖hz q‖ = (1 - q.1.1) * ‖ℓ q.2‖ + q.1.1 * (1 + q.2.1) := by
      have h1 := q.1.2.1
      have h2 := q.1.2.2
      have h3 := q.2.2.1
      have h4 := (hℓA q.2).1
      simp only [hz]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by nlinarith)]
    have h1 := q.1.2.1
    have h2 := q.1.2.2
    have h3 := q.2.2.1
    have h4 := q.2.2.2
    have h5 := (hℓA q.2).1
    have h6 := (hℓA q.2).2
    constructor <;> rw [hn] <;> nlinarith
  refine path_homotopic_of_map (H := fun q => c (hz q)) (hc.cont.comp_continuous hzc hzA) (fun t
    => ?_) (fun t => ?_) (fun w => ?_) fun w => ?_
  · simp only [hz, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    rw [hθ, ← eq_mul_dirOf (ne_zero_of_mem_collar (hℓA t))]
    exact hℓe t
  · simp only [hz, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    rw [hR₁']
    simp only [comp_apply, collarTwist]
    congr 1
    have hn : ‖((1 + t.1 : ℝ) : ℂ) * w₀‖ = 1 + t.1 := by
      have h1 := t.2.1
      rw [norm_mul, h₀, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hn]
    rw [← hθ0, mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [κ]
    push_cast
    ring
  · simp only [hz, Set.Icc.coe_zero, mul_zero, add_zero, mul_one]
    have hn1 : ‖ℓ 0‖ = 1 := by rw [hℓ0, h₀]
    rw [hn1, show (1 - w.1) * 1 + w.1 = 1 by ring, show (1 - w.1) * θ 0 + w.1 * θ 0
      = θ 0 by ring, hθ0]
    simp
  · simp only [hz, Set.Icc.coe_one]
    have h3 : ((1 - w.1) * ‖ℓ 1‖ + w.1 * (1 + 1) : ℝ) = 2 := by
      rw [hℓn1]
      ring
    have h4 : ((1 - w.1) * θ 1 + w.1 * (θ 0 + κ * 1) : ℝ) = θ 1 := by
      simp only [κ]
      ring
    rw [h3, h4, hθ1, show (((2 : ℝ) : ℂ) * (ℓ 1 / 2)) = ℓ 1 by push_cast; ring, hℓe, L.target]

private theorem collar_motion_follows_radial_paths
    {S : Type*} [TopologicalSpace S] {c e t₁ : ℂ → S} {e' t₁' : S → ℂ}
    (he : IsCollarChart e e') {w₀ w₁ : ℂ} (h₀ : ‖w₀‖ = 1) (h₁ : ‖w₁‖ = 1)
    (hw1A : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ collarAnnulus)
    (hw1O : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ collarOpen)
    (h2A : ∀ {w : ℂ}, ‖w‖ = 1 → 2 * w ∈ collarAnnulus)
    (R₂ : Path (e w₁) (e (2 * w₁)))
    (hR₂ : ∀ t : unitInterval, R₂ t = e (((1 + (t : ℝ) : ℝ) : ℂ) * w₁))
    (ht : IsCollarChart t₁ t₁') (htw₀ : t₁ w₀ = c w₀) (htb : t₁ (2 * w₀) = e (2 * w₁))
    (hht : ∀ z ∈ collarOpen, (chartSwap t₁ (e ∘ fiberMap (fun w => e' (t₁ (2 * w)))) t₁') (t₁ z) =
      (e ∘ fiberMap (fun w => e' (t₁ (2 * w)))) z)
    (R₁' : Path (c w₀) (e (2 * w₁)))
    (hR₁' : ∀ t : unitInterval, R₁' t = t₁ (((1 + (t : ℝ) : ℝ) : ℂ) * w₀))
    (P : Path (c w₀) (e w₁))
    (hP : ∀ t : unitInterval, P t = collarHomotopy t₁ (e ∘ fiberMap (fun w => e' (t₁ (2 * w))))
      t₁' (t.1, c w₀))
    (hunit : ∀ {τ : ℝ}, 0 ≤ τ → τ ≤ 1 → radialPush τ w₀ = ((1 + τ : ℝ) : ℂ) * w₀) :
    P = R₁'.trans R₂.symm := by
  let u := fun w => e' (t₁ (2 * w))
  let E := e ∘ fiberMap u
  ext t
  rw [hP]
  rw [Path.trans_apply]
  simp only [collarHomotopy]
  conv_lhs => rw [← htw₀]
  have hc1 : ∀ τ : ℝ, chartPush t₁ t₁' τ (t₁ w₀) = t₁ (radialPush τ w₀) := fun τ => by
    simp only [chartPush]
    rw [ite_eq_left ⟨w₀, hw1O h₀, rfl⟩, ht.left (hw1A h₀)]
  by_cases hle : (t : ℝ) ≤ 1 / 2
  · rw [ite_eq_left hle, dite_eq_left hle, hR₁', hc1,
      hunit (by have := t.2.1; linarith) (by linarith)]
  · rw [ite_eq_right hle, dite_eq_right hle, hc1]
    have h1 := t.2.2
    have hle' : 1 / 2 < (t : ℝ) := not_le.mp hle
    rw [hunit (by linarith) (by linarith)]
    have hOm : ((1 + (2 - 2 * t.1) : ℝ) : ℂ) * w₀ ∈ collarOpen := by
      have : ‖((1 + (2 - 2 * t.1) : ℝ) : ℂ) * w₀‖ = 1 + (2 - 2 * t.1) := by
        rw [norm_mul, h₀, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      constructor <;> rw [this] <;> linarith
    rw [show chartSwap t₁ E t₁' (t₁ (((1 + (2 - 2 * t.1) : ℝ) : ℂ) * w₀)) = E _ from hht _ hOm]
    rw [Path.symm_apply, comp_apply, hR₂]
    simp only [E, comp_apply]
    have hu0 : u w₀ = 2 * w₁ := by
      simp only [u]
      rw [htb, he.left (h2A h₁)]
    have hn : ‖((1 + (2 - 2 * t.1) : ℝ) : ℂ) * w₀‖ = 1 + (2 - 2 * t.1) := by
      rw [norm_mul, h₀, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hd : dirOf (((1 + (2 - 2 * t.1) : ℝ) : ℂ) * w₀) = w₀ := by
      rw [dirOf_mul_pos (by linarith) (by rintro rfl; simp at h₀), dirOf_of_norm_one h₀]
    rw [fiberMap, hn, hd, hu0]
    congr 1
    simp only [unitInterval.coe_symm_eq]
    push_cast
    ring

omit [T2Space S] [CompactSpace S] in
private theorem exists_aligned_collar_chart {e t₁ : ℂ → S} {e' t₁' : S → ℂ}
    (he : IsCollarChart e e') (ht : IsCollarChart t₁ t₁')
    (hout : e '' {z | ‖z‖ = 2} = t₁ '' {z | ‖z‖ = 2}) :
    let E := e ∘ fiberMap (fun w => e' (t₁ (2 * w)))
    ∃ E' : S → ℂ, IsCollarChart E E' ∧
      (∀ z, ‖z‖ = 2 → E z = t₁ z) ∧ E '' collarOpen = e '' collarOpen ∧
      E '' {z | ‖z‖ = 1} = e '' {z | ‖z‖ = 1} ∧
      (∀ w₀ w₁, ‖w₀‖ = 1 → ‖w₁‖ = 1 → t₁ (2 * w₀) = e (2 * w₁) → E w₀ = e w₁) := by
  intro E
  have hw1A : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ collarAnnulus :=
    fun {w} hw => ⟨hw.ge, by rw [hw]; norm_num⟩
  have h2w : ∀ {w : ℂ}, ‖w‖ = 1 → ‖2 * w‖ = 2 := fun {w} hw => by simp [hw]
  have h2A : ∀ {w : ℂ}, ‖w‖ = 1 → 2 * w ∈ collarAnnulus :=
    fun {w} hw => ⟨by rw [h2w hw]; norm_num, (h2w hw).le⟩
  have hs2 : {z : ℂ | ‖z‖ = 2} ⊆ collarAnnulus := by
    intro z hz
    change ‖z‖ = 2 at hz
    exact ⟨by rw [hz]; norm_num, hz.le⟩
  have hemem : ∀ x ∈ e '' {z | ‖z‖ = 2}, ‖e' x‖ = 2 ∧ e (e' x) = x := by
    rintro _ ⟨z, hz, rfl⟩
    have hzA : z ∈ collarAnnulus := hs2 hz
    rw [he.left hzA]
    exact ⟨hz, rfl⟩
  have htmem : ∀ x ∈ t₁ '' {z | ‖z‖ = 2}, ‖t₁' x‖ = 2 ∧ t₁ (t₁' x) = x := by
    rintro _ ⟨z, hz, rfl⟩
    have hzA : z ∈ collarAnnulus := hs2 hz
    rw [ht.left hzA]
    exact ⟨hz, rfl⟩
  have heo : ∀ {w : ℂ}, ‖w‖ = 1 → e (2 * w) ∈ t₁ '' {z | ‖z‖ = 2} :=
    fun {w} hw => hout ▸ ⟨_, h2w hw, rfl⟩
  have hto : ∀ {w : ℂ}, ‖w‖ = 1 → t₁ (2 * w) ∈ e '' {z | ‖z‖ = 2} :=
    fun {w} hw => hout.symm ▸ ⟨_, h2w hw, rfl⟩
  let u : ℂ → ℂ := fun w => e' (t₁ (2 * w))
  let v : ℂ → ℂ := fun w => t₁' (e (2 * w))
  have h2c : Continuous fun w : ℂ => 2 * w := by fun_prop
  have hu : ContinuousOn u {w | ‖w‖ = 1} := by
    have h1 : ContinuousOn (fun w : ℂ => t₁ (2 * w)) {w | ‖w‖ = 1} := ht.cont.comp h2c.continuousOn
      fun w hw => h2A hw
    exact he.cont'.comp h1 fun w hw => image_mono hs2 (hto hw)
  have hv : ContinuousOn v {w | ‖w‖ = 1} := by
    have h1 : ContinuousOn (fun w : ℂ => e (2 * w)) {w | ‖w‖ = 1} := he.cont.comp h2c.continuousOn
      fun w hw => h2A hw
    exact ht.cont'.comp h1 fun w hw => image_mono hs2 (heo hw)
  have hnu : ∀ w, ‖w‖ = 1 → ‖u w‖ = 2 := fun w hw => (hemem _ (hto hw)).1
  have hnv : ∀ w, ‖w‖ = 1 → ‖v w‖ = 2 := fun w hw => (htmem _ (heo hw)).1
  have huv : ∀ w, ‖w‖ = 1 → v (u w / 2) = 2 * w := fun w hw => by
    simp only [v]
    rw [show 2 * (u w / 2) = u w by ring]
    simp only [u]
    rw [(hemem _ (hto hw)).2, ht.left (h2A hw)]
  have hvu : ∀ w, ‖w‖ = 1 → u (v w / 2) = 2 * w := fun w hw => by
    simp only [u]
    rw [show 2 * (v w / 2) = v w by ring]
    simp only [v]
    rw [(htmem _ (heo hw)).2, he.left (h2A hw)]
  have hnfu : ∀ z ∈ collarAnnulus, ‖fiberMap u z‖ = ‖z‖ := fun z hz => norm_fiberMap hnu hz
  have hnfv : ∀ z ∈ collarAnnulus, ‖fiberMap v z‖ = ‖z‖ := fun z hz => norm_fiberMap hnv hz
  let E' : S → ℂ := fiberMap v ∘ e'
  have hE : IsCollarChart E E' := he.comp (continuousOn_fiberMap hu) (continuousOn_fiberMap hv)
    hnfu hnfv (fun z hz => fiberMap_inv hnu huv hz) fun z hz => fiberMap_inv hnv hvu hz
  have hEout : ∀ z, ‖z‖ = 2 → E z = t₁ z := fun z hz => by
    exact adjusted_collar_agrees_on_outer_circle (S := S) (e := e) (e' := e') t₁ hemem hto hs2 z
      hz
  have hbijE : ∀ B : Set ℂ, B ⊆ collarAnnulus → (∀ z w : ℂ, ‖z‖ = ‖w‖ → (z ∈ B ↔ w ∈ B)) → E '' B
    = e '' B := fun B hBA hB => by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, (hB _ _ (hnfu z (hBA hz))).mpr hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨fiberMap v z, (hB _ _ (hnfv z (hBA hz))).mpr hz, ?_⟩
      change e (fiberMap u (fiberMap v z)) = e z
      rw [fiberMap_inv hnv hvu (hBA hz)]
  have hEO : E '' collarOpen = e '' collarOpen := hbijE _ collarOpen_subset fun z w h => by
    simp only [collarOpen, mem_ofPred_eq, h]
  have hE1 : E '' {z | ‖z‖ = 1} = e '' {z | ‖z‖ = 1} :=
    hbijE _ (fun _ hz => hw1A hz) fun z w h => by
    simp only [mem_ofPred_eq, h]
  refine ⟨E', hE, hEout, hEO, hE1, ?_⟩
  intro w₀ w₁ h₀ h₁ htb
  have hu0 : u w₀ = 2 * w₁ := by
    simp only [u]
    rw [htb, he.left (h2A h₁)]
  have hf : fiberMap u w₀ = w₁ := by
    rw [fiberMap, dirOf_of_norm_one h₀, hu0, h₀]
    push_cast
    ring
  change e (fiberMap u w₀) = e w₁
  rw [hf]

omit [T2Space S] [CompactSpace S] in
private theorem collar_radial_path {b : ℂ → S} {b' : S → ℂ}
    (hb : IsCollarChart b b') {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ R : Path (b w) (b (2 * w)),
      ∀ t : unitInterval, R t = b (((1 + t.1 : ℝ) : ℂ) * w) := by
  have hm : ∀ t : unitInterval, ((1 + t.1 : ℝ) : ℂ) * w ∈ collarAnnulus := fun t => by
    have h1 := t.2.1
    have h2 := t.2.2
    have : ‖((1 + t.1 : ℝ) : ℂ) * w‖ = 1 + t.1 := by
      rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    constructor <;> rw [this] <;> linarith
  have hcont : Continuous fun t : unitInterval => b (((1 + t.1 : ℝ) : ℂ) * w) :=
    hb.cont.comp_continuous (by fun_prop) hm
  refine ⟨⟨⟨_, hcont⟩, ?_, ?_⟩, fun _ => rfl⟩
  · simp
  · simp only [Set.Icc.coe_one]
    norm_num

omit [CompactSpace S] in
/-- **Pushing a collar.** Two annuli share their outer circle, the second inside the first. A map
`h` of `S` onto the part off the first annulus and in the second fixes all points
off the first annulus. It is homotopic to the identity, by a homotopy that also fixes those points,
and the path traced by `c w₀` is homotopic to `Q`. -/
theorem exists_collar_push {c e : ℂ → S} {c' e' : S → ℂ} (hc : IsCollarChart c c') (hO : IsOpen
  (c '' collarOpen)) (he : IsCollarChart e e') (hout : e '' {z | ‖z‖ = 2} = c '' {z | ‖z‖ = 2})
    (hsub : e '' collarOpen ⊆ c '' collarOpen) {w₀ w₁ : ℂ} (h₀ : ‖w₀‖ = 1) (h₁ : ‖w₁‖ = 1)
      (Q : Path (c w₀) (e w₁)) (hQ : range Q ⊆ c '' collarAnnulus) :
    ∃ (h : S → S) (Φ : unitInterval × S → S), Continuous h ∧ Continuous Φ ∧ Injective h ∧
      (∀ x ∉ c '' collarOpen, h x = x ∧ ∀ t, Φ (t, x) = x) ∧
      (∀ x, Φ (0, x) = x) ∧ (∀ x, Φ (1, x) = h x) ∧
      range h = (c '' collarOpen)ᶜ ∪ e '' collarOpen ∧ h '' (c '' {z | ‖z‖ = 1}) = e '' {z | ‖z‖
        = 1} ∧ h (c w₀) = e w₁ ∧
      ∃ P : Path (c w₀) (e w₁), (∀ t, P t = Φ (t, c w₀)) ∧ P.Homotopic Q := by
  classical
  -- the path `L`: `Q`, then the radial line of `e` at `w₁`
  have hw1A : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ collarAnnulus := fun {w} hw => ⟨hw.ge, by rw [hw]; norm_num⟩
  have hw1O : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ collarOpen := fun {w} hw => ⟨hw.ge, by rw [hw]; norm_num⟩
  have h2w : ∀ {w : ℂ}, ‖w‖ = 1 → ‖2 * w‖ = 2 := fun {w} hw => by simp [hw]
  have h2A : ∀ {w : ℂ}, ‖w‖ = 1 → 2 * w ∈ collarAnnulus :=
    fun {w} hw => ⟨by rw [h2w hw]; norm_num, (h2w hw).le⟩
  have heA : e '' collarAnnulus ⊆ c '' collarAnnulus := by
    exact collar_inclusion_from_open_and_outer_images (S := S) (c := c) (e := e) hout hsub
  obtain ⟨R₂, hR₂⟩ := collar_radial_path he h₁
  let L : Path (c w₀) (e (2 * w₁)) := Q.trans R₂
  have hLA : ∀ t, L t ∈ c '' collarAnnulus := by
    intro t
    have : range L ⊆ c '' collarAnnulus := by
      rw [Path.trans_range]
      refine union_subset hQ ?_
      rintro _ ⟨t, rfl⟩
      rw [hR₂ t]
      refine heA ⟨_, ?_, rfl⟩
      have h1 := t.2.1
      have h2 := t.2.2
      have : ‖((1 + t.1 : ℝ) : ℂ) * w₁‖ = 1 + t.1 := by
        rw [norm_mul, h₁, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      constructor <;> rw [this] <;> linarith
    exact this (mem_range_self t)
  let ℓ : unitInterval → ℂ := fun t => c' (L t)
  have hℓc : Continuous ℓ := hc.cont'.comp_continuous L.continuous hLA
  have hℓA : ∀ t, ℓ t ∈ collarAnnulus := fun t => (hc.mem_of_mem (hLA t)).1
  have hℓe : ∀ t, c (ℓ t) = L t := fun t => (hc.mem_of_mem (hLA t)).2
  have hℓ0 : ℓ 0 = w₀ := by
    change c' (L 0) = w₀
    rw [L.source]
    exact hc.left (hw1A h₀)
  have hℓn1 : ‖ℓ 1‖ = 2 := by
    obtain ⟨y, hy, hye⟩ := hout.le ⟨2 * w₁, h2w h₁, rfl⟩
    change ‖c' (L 1)‖ = 2
    have hy' : ‖y‖ = 2 := hy
    have hyA : y ∈ collarAnnulus := ⟨by rw [hy']; norm_num, hy'.le⟩
    rw [L.target, ← hye, hc.left hyA]
    exact hy
  -- the angle of `ℓ`
  let direction : unitInterval → Circle := fun t =>
    ⟨dirOf (ℓ t), by
      simpa [Submonoid.unitSphere] using norm_dirOf (ne_zero_of_mem_collar (hℓA t))⟩
  let γ : C(unitInterval, Circle) := ⟨direction, by
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_dirOf.comp_continuous hℓc fun t => ne_zero_of_mem_collar (hℓA t)⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : C(unitInterval, ℝ), ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = dirOf (ℓ t)
    := by
    refine ⟨Circle.isCoveringMap_exp.liftPath γ (Complex.arg (γ 0 : ℂ)) (Circle.exp_arg
      (γ 0)).symm, fun t => ?_⟩
    have := congr_fun (Circle.isCoveringMap_exp.liftPath_lifts γ (Complex.arg (γ 0 : ℂ))
      (Circle.exp_arg (γ 0)).symm) t
    have h2 := congrArg (fun z : Circle => (z : ℂ)) this
    simp only [comp_apply, Circle.coe_exp] at h2
    exact h2
  let κ : ℝ := θ 1 - θ 0
  have hθ0 : Complex.exp ((θ 0 : ℂ) * Complex.I) = w₀ := by
    rw [hθ, hℓ0, dirOf_of_norm_one h₀]
  have hθ1 : Complex.exp ((θ 1 : ℂ) * Complex.I) = ℓ 1 / 2 := by
    have h0 : ℓ 1 ≠ 0 := ne_zero_of_mem_collar (hℓA 1)
    have h3 := eq_mul_dirOf h0
    rw [hℓn1, ← hθ] at h3
    nth_rw 1 [h3]
    push_cast
    ring
  -- the twisted chart
  have hnt : ∀ (κ : ℝ), ∀ z ∈ collarAnnulus, ‖collarTwist κ z‖ = ‖z‖ := fun κ z _
    => norm_collarTwist κ z
  have htw : ∀ κ, ∀ z, collarTwist κ (collarTwist (-κ) z) = z := fun κ z => by
    have := collarTwist_neg (-κ) z
    rwa [neg_neg] at this
  let t₁ : ℂ → S := c ∘ collarTwist κ
  let t₁' : S → ℂ := collarTwist (-κ) ∘ c'
  have ht : IsCollarChart t₁ t₁' := hc.comp (continuous_collarTwist κ).continuousOn
    (continuous_collarTwist (-κ)).continuousOn (hnt κ) (hnt (-κ))
    (fun z _ => collarTwist_neg κ z) fun z _ => htw κ z
  have hbij : ∀ B : Set ℂ, (∀ z w : ℂ, ‖z‖ = ‖w‖ → (z ∈ B ↔ w ∈ B)) → t₁ '' B = c '' B := fun B hB
    => by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, (hB _ _ (norm_collarTwist κ z)).mpr hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨collarTwist (-κ) z, (hB _ _ (norm_collarTwist _ z)).mpr hz, ?_⟩
      simp only [t₁, comp_apply, htw]
  have htO : t₁ '' collarOpen = c '' collarOpen := hbij _ fun z w h => by
    simp only [collarOpen, mem_ofPred_eq, h]
  have htA : t₁ '' collarAnnulus = c '' collarAnnulus := hbij _ fun z w h => by
    simp only [collarAnnulus, mem_ofPred_eq, h]
  have ht1 : t₁ '' {z | ‖z‖ = 1} = c '' {z | ‖z‖ = 1} := hbij _ fun z w h => by
    simp only [mem_ofPred_eq, h]
  have ht2 : t₁ '' {z | ‖z‖ = 2} = c '' {z | ‖z‖ = 2} := hbij _ fun z w h => by
    simp only [mem_ofPred_eq, h]
  have htw₀ : t₁ w₀ = c w₀ := by
    simp [t₁, collarTwist, h₀]
  have htb : t₁ (2 * w₀) = e (2 * w₁) := by
    have h1 : collarTwist κ (2 * w₀) = ℓ 1 := by
      rw [collarTwist, h2w h₀, ← hθ0, mul_assoc, ← Complex.exp_add]
      have : (θ 0 : ℂ) * Complex.I + ((κ * (2 - 1) : ℝ) : ℂ) * Complex.I = (θ 1 : ℂ) * Complex.I
        := by
        simp only [κ]
        push_cast
        ring
      rw [this, hθ1]
      ring
    simp only [t₁, comp_apply, h1, hℓe, L.target]
  let E : ℂ → S := e ∘ fiberMap (fun w => e' (t₁ (2 * w)))
  obtain ⟨E', hE, hEout, hEO, hE1, hEpoints⟩ :=
    exists_aligned_collar_chart he ht (hout.trans ht2.symm)
  let h : S → S := chartSwap t₁ E t₁'
  let Φ : unitInterval × S → S := fun q => collarHomotopy t₁ E t₁' (q.1.1, q.2)
  have hOt : IsOpen (t₁ '' collarOpen) := htO ▸ hO
  have hc_h : Continuous h := continuous_chartSwap ht hOt hE hEout
  have hc_Φ : Continuous Φ := continuous_collarHomotopy ht hOt hE hEout
  have hsubE : E '' collarOpen ⊆ t₁ '' collarOpen := by
    rw [hEO, htO]
    exact hsub
  have hht : ∀ z ∈ collarOpen, h (t₁ z) = E z := fun z hz => by
    simp only [h, chartSwap]
    rw [ite_eq_left ⟨z, hz, rfl⟩, ht.left (collarOpen_subset hz)]
  have hinj : Injective h := by
    intro x y hxy
    by_cases hx : x ∈ t₁ '' collarOpen <;> by_cases hy : y ∈ t₁ '' collarOpen
    · obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨z', hz', rfl⟩ := hy
      rw [hht z hz, hht z' hz'] at hxy
      rw [hE.injOn (collarOpen_subset hz) (collarOpen_subset hz') hxy]
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hht z hz, show h y = y from chartSwap_of_not_mem hy] at hxy
      exact absurd (hxy ▸ hsubE ⟨z, hz, rfl⟩) hy
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hht z hz, show h x = x from chartSwap_of_not_mem hx] at hxy
      exact absurd (hxy.symm ▸ hsubE ⟨z, hz, rfl⟩) hx
    · rwa [show h y = y from chartSwap_of_not_mem hy, show h x = x from chartSwap_of_not_mem hx]
        at hxy
  have hΦ0 : ∀ x, Φ (0, x) = x := fun x => by
    simp only [Φ, collarHomotopy, Set.Icc.coe_zero]
    rw [ite_eq_left (by norm_num), mul_zero, chartPush_zero ht]
  have hΦ1 : ∀ x, Φ (1, x) = h x := fun x => by
    simp only [Φ, collarHomotopy, Set.Icc.coe_one]
    rw [ite_eq_right (by norm_num), show (2 : ℝ) - 2 * 1 = 0 by ring, chartPush_zero ht]
  have hΦoff : ∀ x, x ∉ t₁ '' collarOpen → ∀ t, Φ (t, x) = x := fun x hx t => by
    simp only [Φ, collarHomotopy]
    split_ifs
    · exact chartPush_of_not_mem hx
    · rw [chartPush_of_not_mem hx]
      exact chartSwap_of_not_mem hx
  have hE2 : E w₀ = e w₁ := hEpoints w₀ w₁ h₀ h₁ htb
  have hhw : h (c w₀) = e w₁ := by
    rw [← htw₀, hht _ (hw1O h₀), hE2]
  refine ⟨h, Φ, hc_h, hc_Φ, hinj, fun x hx => ?_, hΦ0, hΦ1, ?_, ?_, hhw, ?_⟩
  · rw [← htO] at hx
    exact ⟨chartSwap_of_not_mem hx, hΦoff x hx⟩
  · rw [← htO, ← hEO]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ t₁ '' collarOpen
      · obtain ⟨z, hz, rfl⟩ := hx
        rw [hht z hz]
        exact .inr ⟨z, hz, rfl⟩
      · rw [show h x = x from chartSwap_of_not_mem hx]
        exact .inl hx
    · rintro (hy | ⟨z, hz, rfl⟩)
      · exact ⟨y, chartSwap_of_not_mem hy⟩
      · exact ⟨t₁ z, hht z hz⟩
  · rw [← ht1, ← hE1, image_image]
    refine image_congr fun z hz => hht z (hw1O hz)
  obtain ⟨R₁, hR₁⟩ := collar_radial_path ht h₀
  let R₁' : Path (c w₀) (e (2 * w₁)) := R₁.cast htw₀.symm htb.symm
  have hR₁' : ∀ t : unitInterval, R₁' t = t₁ (((1 + t.1 : ℝ) : ℂ) * w₀) := fun t => hR₁ t
  have hLR : L.Homotopic R₁' := by
    exact lifted_angle_gives_collar_homotopy (S := S) (c := c) (e := e) (c' := c') hc (w₀ := w₀)
      (w₁ := w₁) h₀ L ℓ hℓc hℓA hℓe hℓ0 hℓn1 θ hθ hθ0 hθ1 R₁' hR₁'
  let P : Path (c w₀) (e w₁) := ⟨⟨fun t => Φ (t, c w₀), hc_Φ.comp (continuous_id.prodMk
    continuous_const)⟩, hΦ0 _, by
    change Φ (1, c w₀) = e w₁
    rw [hΦ1, hhw]⟩
  have hunit : ∀ {τ : ℝ}, 0 ≤ τ → τ ≤ 1 → radialPush τ w₀ = ((1 + τ : ℝ) : ℂ) * w₀ := fun {τ} h0 h1
    => by
    rw [radialPush, dirOf_of_norm_one h₀, h₀]
    congr 2
    ring
  have hPeq : P = R₁'.trans R₂.symm := by
    exact collar_motion_follows_radial_paths he h₀ h₁ hw1A hw1O h2A R₂ hR₂ ht htw₀ htb hht
      R₁' hR₁' P (fun _ => rfl) hunit
  refine ⟨P, fun _ => rfl, ?_⟩
  rw [hPeq]
  have h1 : (R₁'.trans R₂.symm).Homotopic (L.trans R₂.symm) := Path.Homotopic.hcomp hLR.symm
    (Path.Homotopic.refl _)
  have h2 : (L.trans R₂.symm).Homotopic (Q.trans (R₂.trans R₂.symm)) := ⟨Path.Homotopy.transAssoc Q
    R₂ R₂.symm⟩
  have h3 : (Q.trans (R₂.trans R₂.symm)).Homotopic (Q.trans (Path.refl _)) := Path.Homotopic.hcomp
    (Path.Homotopic.refl _) ⟨(Path.Homotopy.reflTransSymm R₂).symm⟩
  have h4 : (Q.trans (Path.refl _)).Homotopic Q := ⟨Path.Homotopy.transRefl Q⟩
  exact h1.trans (h2.trans (h3.trans h4))

section Capped

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T2Space T] [CompactSpace S]

theorem isPathConnected_collarAnnulus : IsPathConnected collarAnnulus := by
  have h1 : IsPathConnected (Icc (1 : ℝ) 2 ×ˢ (univ : Set ℝ)) :=
    ((convex_Icc (1 : ℝ) 2).prod convex_univ).isPathConnected ⟨(1, 0), by simp⟩
  have h2 : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) := by
    fun_prop
  have h3 := h1.image h2
  convert h3 using 1
  ext z
  constructor
  · intro hz
    refine ⟨(‖z‖, Complex.arg z), ⟨⟨hz.1, hz.2⟩, mem_univ _⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I z
  · rintro ⟨⟨r, θ⟩, ⟨⟨h1, h2⟩, -⟩, rfl⟩
    have : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    simp only at h1 h2 ⊢
    constructor <;> simp only [this] <;> assumption

/-- A chart in `S` of the part of the disc `Y` off the disc `E`. -/
theorem exists_collar_chart (hman : ∀ x : T, IsManifoldPoint x) [Nonempty S] {j : S → T}
  (hj : IsEmbedding j) {D E Y : Set T} (hE : IsClosedDisc E) (hY : IsClosedDisc Y)
    (hEY : E ⊆ Y \ discBd Y)
    (hD : IsClosedDisc D) (hDE : D ⊆ E) (hcov : range j ∪ D = univ) (hbdD : discBd D ⊆ range j) :
    ∃ (c : ℂ → S) (c' : S → ℂ), IsCollarChart c c' ∧ c '' {z | ‖z‖ = 1} = j ⁻¹' discBd E
      ∧ c '' {z | ‖z‖ = 2} = j ⁻¹' discBd Y ∧ c '' collarOpen = j ⁻¹' (discInt Y \ discInt E) ∧
      c '' collarAnnulus = j ⁻¹' (Y \ discInt E) := by
  classical
  obtain ⟨p⟩ := hE.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, hr, hcE, hcb, hcp⟩ := exists_disc_collar hE hY hEY p
  obtain ⟨pr, hprc, hprl⟩ := exists_inv_of_compactOn (K := (univ : Set S)) isCompact_univ
    hj.continuous.continuousOn hj.injective.injOn
  have hAb : collarAnnulus ⊆ Metric.closedBall 0 2 := fun z hz => by simpa using hz.2
  have hinj : InjOn c (Metric.closedBall 0 2) := hl.injOn
  have hdisc : discInt D ⊆ discInt E := discInt_mono hman hD hDE
  have hs1 : c '' {z | ‖z‖ = 1} = discBd E := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h2 : c z = _ := hcp ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
      rw [h2]
      exact (p _).2
    · intro hx
      refine ⟨(p.symm ⟨x, hx⟩ : Circle), by simp, ?_⟩
      rw [hcp]
      simp
  have hin1 : ∀ z, ‖z‖ < 1 → c z ∉ discBd E ∪ (Y \ E) ∧ c z ∈ E := fun z hz => by
    have hb : z ∈ Metric.closedBall (0 : ℂ) 2 := by simpa using (hz.le.trans one_le_two)
    have hzE : c z ∈ E := hcE ▸ mem_image_of_mem c (by simpa using hz.le)
    refine ⟨?_, hzE⟩
    rintro (h | h)
    · rw [← hs1] at h
      obtain ⟨y, hy, he⟩ := h
      have hyb : y ∈ Metric.closedBall (0 : ℂ) 2 := by
        have : ‖y‖ = 1 := hy
        simp [this]
      rw [hinj hyb hb he] at hy
      exact hz.ne hy
    · exact h.2 hzE
  have hoff : ∀ z ∈ collarAnnulus, c z ∉ discInt E := fun z hz h => by
    by_cases h1 : ‖z‖ = 1
    · exact h.2 (hs1 ▸ mem_image_of_mem c h1)
    · have hlt : 1 < ‖z‖ := lt_of_le_of_ne hz.1 (Ne.symm h1)
      obtain ⟨y, hy, he⟩ := hcE.ge h.1
      have hyb : y ∈ Metric.closedBall (0 : ℂ) 2 := by
        have : ‖y‖ ≤ 1 := by simpa using hy
        simp only [mem_closedBall_zero_iff]
        linarith
      rw [hinj hyb (hAb hz) he] at hy
      have : ‖z‖ ≤ 1 := by simpa using hy
      linarith
  have hrange : ∀ z ∈ collarAnnulus, c z ∈ range j := fun z hz => by
    rcases hcov.ge (mem_univ (c z)) with h | h
    · exact h
    · by_cases hb : c z ∈ discBd D
      · exact hbdD hb
      · exact absurd (hdisc ⟨h, hb⟩) (hoff z hz)
  have hjpr : ∀ y ∈ range j, j (pr y) = y := by
    rintro _ ⟨x, rfl⟩
    rw [hprl (mem_univ x)]
  have hcY : ∀ x, x ∈ Y → ∃ z, ‖z‖ ≤ 2 ∧ c z = x := fun x hx => ⟨c' x, by simpa using hmc' hx, hr
    hx⟩
  have hsame : ∀ B : Set ℂ, B ⊆ collarAnnulus → (fun z => pr (c z)) '' B = j ⁻¹' (c '' B)
    := fun B hB => by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (hjpr _ (hrange z (hB hz))).symm⟩
    · rintro ⟨z, hz, he⟩
      refine ⟨z, hz, ?_⟩
      change pr (c z) = x
      rw [he, hprl (mem_univ x)]
  have hprS : {z : ℂ | ‖z‖ = 1} ⊆ collarAnnulus := fun z hz => by
    have h : ‖z‖ = 1 := hz
    exact ⟨h.ge, by rw [h]; norm_num⟩
  have hprT : {z : ℂ | ‖z‖ = 2} ⊆ collarAnnulus := fun z hz => by
    have h : ‖z‖ = 2 := hz
    exact ⟨by rw [h]; norm_num, h.le⟩
  have hs2 : c '' {z | ‖z‖ = 2} = discBd Y := by
    rw [← hcb]
    congr 1
    ext z
    simp
  have hA : c '' collarAnnulus = Y \ discInt E := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hmc (hAb hz), hoff z hz⟩
    · rintro ⟨hx, hxi⟩
      obtain ⟨z, hz, rfl⟩ := hcY x hx
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      by_contra hlt
      obtain ⟨h1, h2⟩ := hin1 z (not_le.mp hlt)
      exact hxi ⟨h2, fun hb => h1 (.inl hb)⟩
  have hO : c '' collarOpen = discInt Y \ discInt E := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨hmc (hAb (collarOpen_subset hz)), fun hb => ?_⟩, hoff z (collarOpen_subset hz)⟩
      rw [← hs2] at hb
      obtain ⟨y, hy, he⟩ := hb
      have hyA : y ∈ collarAnnulus := hprT hy
      rw [hinj (hAb hyA) (hAb (collarOpen_subset hz)) he] at hy
      exact hz.2.ne hy
    · rintro ⟨⟨hx, hxb⟩, hxi⟩
      obtain ⟨z, hzA, rfl⟩ := hA.ge ⟨hx, hxi⟩
      refine ⟨z, ⟨hzA.1, lt_of_le_of_ne hzA.2 fun h2 => hxb ?_⟩, rfl⟩
      exact hs2 ▸ mem_image_of_mem c h2
  have hYU : ContinuousOn (fun x => c' (j x)) ((fun z => pr (c z)) '' collarAnnulus) := by
    refine hc'c.comp hj.continuous.continuousOn ?_
    rintro _ ⟨z, hz, rfl⟩
    change j (pr (c z)) ∈ Y
    rw [hjpr _ (hrange z hz)]
    exact hmc (hAb hz)
  refine ⟨fun z => pr (c z), fun x => c' (j x), ⟨?_, hYU, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.comp (t := j '' univ) hprc (hcc.mono hAb) fun z hz => ?_
    rw [image_univ]
    exact hrange z hz
  · intro z hz
    change c' (j (pr (c z))) = z
    rw [hjpr _ (hrange z hz), hl (hAb hz)]
  · rw [hsame _ hprS, hs1]
  · rw [hsame _ hprT, hs2]
  · rw [hsame _ collarOpen_subset, hO]
  · rw [hsame _ Subset.rfl, hA]

end Capped

/-- A path in `S` between the two circles of the annulus, inside the disc `Y`. -/
theorem exists_path_in_collar {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
  [CompactSpace S] {C : Set S} {j : S → T} {D Δ Y : Set T} (hc : IsCappedCuff C T j D)
    (_hΔ : IsClosedDisc Δ)
    (hDΔ : D ⊆ Δ) (hY : IsClosedDisc Y) (hΔY : Δ ⊆ Y \ discBd Y) {x₀ a₁ : S} (hx₀ : x₀ ∈ C)
      (ha : j a₁ ∈ discBd Δ) : ∃ Q : Path x₀ a₁, ∀ t, j (Q t) ∈ Y := by
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : Nonempty S := ⟨x₀⟩
  have hbdD : discBd D ⊆ range j := by
    rw [hc.discBd_eq]
    exact image_subset_range _ _
  obtain ⟨c, c', hcc, -, -, -, hA⟩ := exists_collar_chart hT.2.2 hc.isEmbedding hc.isClosedDisc hY
    (fun x hx => hΔY (hDΔ hx)) hc.isClosedDisc Subset.rfl hc.union_eq hbdD
  have hp : IsPathConnected (c '' collarAnnulus) := isPathConnected_collarAnnulus.image' hcc.cont
  have hmem : ∀ y, j y ∈ Y → y ∈ c '' collarAnnulus := fun y hy => by
    rw [hA]
    refine ⟨hy, fun hi => hi.2 ?_⟩
    rw [hc.discBd_eq]
    have h2 : j y ∈ range j ∩ D := ⟨mem_range_self y, hi.1⟩
    rwa [hc.inter_eq] at h2
  have hx₀_bd : j x₀ ∈ discBd D := by
    rw [hc.discBd_eq]
    exact mem_image_of_mem j hx₀
  have h1 : j x₀ ∈ Y := (hΔY (hDΔ (Surface.discBd_subset _ hx₀_bd))).1
  have h2 : j a₁ ∈ Y := (hΔY (Surface.discBd_subset _ ha)).1
  obtain ⟨Q, hQ⟩ := (hp.joinedIn _ (hmem _ h1) _ (hmem _ h2))
  refine ⟨Q, fun t => ?_⟩
  have := hQ t
  rw [hA] at this
  exact this.1

/-- **Pushing a cuff out to the boundary of a disc.** See the top of the file. Here `D` is the disc
pasted on the cuff `C`, and `Δ` is a larger disc inside `Y`. -/
theorem exists_capped_push {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [CompactSpace
  S] {C : Set S} {j : S → T} {D Δ Y : Set T} (hc : IsCappedCuff C T j D) (hΔ : IsClosedDisc Δ)
    (hDΔ : D ⊆ Δ) (hY : IsClosedDisc Y) (hΔY : Δ ⊆ Y \ discBd Y) (_hbΔ : discBd Δ ⊆ range j) {x₀ a₁
      : S} (hx₀ : x₀ ∈ C) (ha : j a₁ ∈ discBd Δ) (Q : Path x₀ a₁) (hQ : ∀ t, j (Q t) ∈ Y) :
    ∃ (h : S → S) (Φ : unitInterval × S → S), Continuous h ∧ Continuous Φ ∧ Injective h ∧
      (∀ x, j x ∉ discInt Y → h x = x ∧ ∀ t, Φ (t, x) = x) ∧
      (∀ x, Φ (0, x) = x) ∧ (∀ x, Φ (1, x) = h x) ∧
      range h = j ⁻¹' (discInt Δ)ᶜ ∧ h '' C = j ⁻¹' discBd Δ ∧ h x₀ = a₁ ∧ ∃ P : Path x₀ a₁,
        (∀ t, P t = Φ (t, x₀)) ∧ P.Homotopic Q := by
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hc.isEmbedding.t2Space
  have : Nonempty S := ⟨x₀⟩
  have hman := hT.2.2
  have hbdD : discBd D ⊆ range j := by
    rw [hc.discBd_eq]
    exact image_subset_range _ _
  have hC : j ⁻¹' discBd D = C := by
    rw [hc.discBd_eq]
    exact preimage_image_eq _ hc.isEmbedding.injective
  have hin : ∀ y, j y ∉ discInt D := fun y hi => hi.2 (by
    rw [hc.discBd_eq]
    have h2 : j y ∈ range j ∩ D := ⟨mem_range_self y, hi.1⟩
    rwa [hc.inter_eq] at h2)
  obtain ⟨c, c', hcc, hc1, hc2, hcO, hcA⟩ := exists_collar_chart hman hc.isEmbedding
    hc.isClosedDisc hY (fun x hx => hΔY (hDΔ hx)) hc.isClosedDisc Subset.rfl hc.union_eq hbdD
  obtain ⟨e, e', hec, he1, he2, heO, -⟩ := exists_collar_chart hman hc.isEmbedding hΔ hY hΔY
    hc.isClosedDisc hDΔ hc.union_eq hbdD
  have hO : IsOpen (c '' collarOpen) := by
    rw [hcO]
    have : j ⁻¹' (discInt Y \ discInt D) = j ⁻¹' discInt Y := by
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, hin y⟩⟩
    rw [this]
    exact (hY.isOpen_discInt hman).preimage hc.isEmbedding.continuous
  have hx : x₀ ∈ c '' {z | ‖z‖ = 1} := by
    rw [hc1, hC]
    exact hx₀
  have hax : a₁ ∈ e '' {z | ‖z‖ = 1} := by
    rw [he1]
    exact ha
  obtain ⟨w₀, h₀, rfl⟩ := hx
  obtain ⟨w₁, h₁, rfl⟩ := hax
  have hsub : e '' collarOpen ⊆ c '' collarOpen := by
    rw [heO, hcO]
    exact fun y hy => ⟨hy.1, hin y⟩
  obtain ⟨h, Φ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := exists_collar_push hcc hO hec
    (he2.trans hc2.symm) hsub h₀ h₁ Q fun y hy => by
    obtain ⟨t, rfl⟩ := hy
    rw [hcA]
    exact ⟨hQ t, hin _⟩
  refine ⟨h, Φ, h1, h2, h3, fun x hx => h4 x ?_, h5, h6, ?_, ?_, h9, h10⟩
  · rw [hcO]
    exact fun hh => hx hh.1
  · rw [h7, hcO, heO]
    ext y
    constructor
    · rintro (hy | hy) hi
      · exact hy ⟨(discInt_mono hman hΔ (fun x hx => (hΔY hx).1 ) ) hi, hin y⟩
      · exact hy.2 hi
    · intro hy
      by_cases hyY : j y ∈ discInt Y
      · exact .inr ⟨hyY, hy⟩
      · exact .inl fun hh => hyY hh.1
  · rw [← hC, ← hc1, h8, he1]

end GraphMinor.GM07
