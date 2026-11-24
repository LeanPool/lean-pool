/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.OneManifold
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Making an arc meet a finite graph in finitely many pieces

Two arcs of a surface can meet in a wild way. Here we replace an arc `a` by a nearby arc with the
same
ends that meets a given finite union of arcs `G` in a tame way: the part of the new arc off `G` is
a finite union of connected sets (`FinConn`). This is the tool that replaces general position, and
it needs no straightening of arcs.

The step (`exists_arc_step`) is loop erasure. Let `g` be one arc of `G`, and let `x` and `y` be the
first and the last point of `a` on `g`. Replace the part of `a` from `x` to `y` by the part of `g`
from `x` to `y`. The new arc meets `g` in one connected piece. Doing this for all arcs of `G` gives
`exists_erase`. If the arcs of `G` are first cut into small pieces, then the new arc stays near the
old one, and two arcs with the same ends can be treated at the same time (`exists_tame_pair`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- `B` is a finite union of connected sets. -/
def FinConn (B : Set X) : Prop :=
  ∃ F : Set (Set X), F.Finite ∧ (∀ J ∈ F, IsPreconnected J) ∧ ⋃₀ F = B

theorem finConn_of_isPreconnected {B : Set X} (h : IsPreconnected B) : FinConn B :=
  ⟨{B}, finite_singleton _, by simpa using h, by simp⟩

theorem FinConn.union {B C : Set X} (hB : FinConn B) (hC : FinConn C) : FinConn (B ∪ C) := by
  obtain ⟨F, h1, h2, rfl⟩ := hB
  obtain ⟨F', h1', h2', rfl⟩ := hC
  refine ⟨F ∪ F', h1.union h1', ?_, sUnion_union F F'⟩
  rintro J (hJ | hJ)
  · exact h2 J hJ
  · exact h2' J hJ

/-- A convex combination of two points of the unit interval. -/
noncomputable def lerpI (s t r : 𝕀) : 𝕀 :=
  ⟨(1 - r.1) * s.1 + r.1 * t.1, by
    have h1 := s.2
    have h2 := t.2
    have h3 := r.2
    constructor
    · have := mul_nonneg (sub_nonneg.mpr h3.2) h1.1
      have := mul_nonneg h3.1 h2.1
      linarith
    · have := mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.mpr h3.2)
      have := mul_le_mul_of_nonneg_left h2.2 h3.1
      linarith⟩

theorem continuous_lerpI (s t : 𝕀) : Continuous (lerpI s t) := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

theorem lerpI_zero (s t : 𝕀) : lerpI s t 0 = s := Subtype.ext (by simp [lerpI])

theorem lerpI_one (s t : 𝕀) : lerpI s t 1 = t := Subtype.ext (by simp [lerpI])

theorem lerpI_injective {s t : 𝕀} (h : s ≠ t) : Function.Injective (lerpI s t) := by
  intro r r' he
  have h1 : (1 - r.1) * s.1 + r.1 * t.1 = (1 - r'.1) * s.1 + r'.1 * t.1 := congrArg Subtype.val he
  have h2 : (r.1 - r'.1) * (t.1 - s.1) = 0 := by linarith
  have h3 : t.1 - s.1 ≠ 0 := fun h0 => h (Subtype.ext (by linarith))
  have h4 : r.1 - r'.1 = 0 := (mul_eq_zero.mp h2).resolve_right h3
  exact Subtype.ext (by linarith)

theorem range_lerpI {s t : 𝕀} (h : s ≤ t) : range (lerpI s t) = Icc s t := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    have h1 : s.1 ≤ t.1 := h
    constructor
    · change s.1 ≤ (1 - r.1) * s.1 + r.1 * t.1
      nlinarith [r.2.1]
    · change (1 - r.1) * s.1 + r.1 * t.1 ≤ t.1
      nlinarith [r.2.2]
  · rintro ⟨h1, h2⟩
    have h1' : s.1 ≤ x.1 := h1
    have h2' : x.1 ≤ t.1 := h2
    by_cases hst : s = t
    · refine ⟨0, ?_⟩
      rw [lerpI_zero]
      exact le_antisymm h1 (hst ▸ h2)
    · have hlt : 0 < t.1 - s.1 := by
        have : s.1 ≠ t.1 := fun h0 => hst (Subtype.ext h0)
        have h3 : s.1 ≤ t.1 := h
        exact sub_pos.mpr (lt_of_le_of_ne h3 this)
      refine ⟨⟨(x.1 - s.1) / (t.1 - s.1), div_nonneg (by linarith) hlt.le, ?_⟩, ?_⟩
      · rw [div_le_one hlt]
        linarith
      · apply Subtype.ext
        change (1 - (x.1 - s.1) / (t.1 - s.1)) * s.1 + (x.1 - s.1) / (t.1 - s.1) * t.1 = x.1
        field_simp
        ring

/-- The part of an arc between two parameters. -/
noncomputable def subArc (a : 𝕀 → X) (s t : 𝕀) : 𝕀 → X := a ∘ lerpI s t

omit [TopologicalSpace X] in
theorem subArc_zero (a : 𝕀 → X) (s t : 𝕀) : subArc a s t 0 = a s := by
  simp [subArc, lerpI_zero]

omit [TopologicalSpace X] in
theorem subArc_one (a : 𝕀 → X) (s t : 𝕀) : subArc a s t 1 = a t := by
  simp [subArc, lerpI_one]

theorem IsArcMap.sub {a : 𝕀 → X} (ha : IsArcMap a) {s t : 𝕀} (h : s ≠ t) :
    IsArcMap (subArc a s t) :=
  ⟨ha.1.comp (continuous_lerpI s t), ha.2.comp (lerpI_injective h)⟩

omit [TopologicalSpace X] in
theorem range_subArc (a : 𝕀 → X) {s t : 𝕀} (h : s ≤ t) :
    range (subArc a s t) = a '' Icc s t := by
  rw [subArc, range_comp, range_lerpI h]

omit [TopologicalSpace X] in
theorem range_subArc_subset (a : 𝕀 → X) (s t : 𝕀) : range (subArc a s t) ⊆ range a := by
  rintro _ ⟨r, rfl⟩
  exact ⟨_, rfl⟩

/-- A connected part of an arc stays connected when cut by an interval. -/
theorem IsArcMap.isPreconnected_inter [T2Space X] {a : 𝕀 → X} (ha : IsArcMap a) {J : Set X}
    (hJ : IsPreconnected J) (hsub : J ⊆ range a) {I : Set 𝕀} (hI : I.OrdConnected) :
    IsPreconnected (J ∩ a '' I) := by
  have hemb : IsInducing a := (ha.1.isClosedEmbedding ha.2).isInducing
  have h1 : a '' (a ⁻¹' J) = J := image_preimage_eq_of_subset hsub
  have h2 : IsPreconnected (a ⁻¹' J) := by
    rw [← hemb.isPreconnected_image, h1]
    exact hJ
  have h3 : (a ⁻¹' J ∩ I).OrdConnected := h2.ordConnected.inter hI
  have h4 := h3.isPreconnected.image a ha.1.continuousOn
  have h5 : a '' (a ⁻¹' J ∩ I) = J ∩ a '' I := by
    rw [image_inter ha.2, image_preimage_eq_of_subset hsub]
  rwa [h5] at h4

theorem FinConn.inter_arc [T2Space X] {a : 𝕀 → X} (ha : IsArcMap a) {B : Set X} (hB : FinConn B)
    (hsub : B ⊆ range a) {I : Set 𝕀} (hI : I.OrdConnected) : FinConn (B ∩ a '' I) := by
  obtain ⟨F, h1, h2, rfl⟩ := hB
  refine ⟨(· ∩ a '' I) '' F, h1.image _, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    exact ha.isPreconnected_inter (h2 J hJ) ((subset_sUnion_of_mem hJ).trans hsub) hI
  · ext x
    simp only [sUnion_image, mem_iUnion, mem_inter_iff, mem_sUnion, exists_prop]
    constructor
    · rintro ⟨J, hJ, hx, hx'⟩
      exact ⟨⟨J, hJ, hx⟩, hx'⟩
    · rintro ⟨⟨J, hJ, hx⟩, hx'⟩
      exact ⟨J, hJ, hx, hx'⟩

/-- **Loop erasure, one step.** The arc `a` is rerouted along `g` between its first and its last
point on `g`. -/
theorem exists_arc_step [T2Space X] {a g : 𝕀 → X} (ha : IsArcMap a) (hg : IsArcMap g)
    (h0 : a 0 ∉ range g) (h1 : a 1 ∉ range g) {G₀ : Set X} (hF : FinConn (range a \ G₀)) :
    ∃ a' : 𝕀 → X, IsArcMap a' ∧ a' 0 = a 0 ∧ a' 1 = a 1 ∧ range a' ⊆ range a ∪ range g ∧
      FinConn (range a' \ (G₀ ∪ range g)) := by
  have hgc : IsClosed (range g) := (isCompact_range hg.1).isClosed
  have hTc : IsCompact (a ⁻¹' range g) := (hgc.preimage ha.1).isCompact
  by_cases hne : (a ⁻¹' range g).Nonempty
  swap
  · refine ⟨a, ha, rfl, rfl, subset_union_left, ?_⟩
    have : range a \ (G₀ ∪ range g) = range a \ G₀ := by
      ext x
      constructor
      · rintro ⟨h2, h3⟩
        exact ⟨h2, fun h => h3 (.inl h)⟩
      · rintro ⟨⟨r, rfl⟩, h3⟩
        exact ⟨⟨r, rfl⟩, fun h => h.elim h3 fun h' => hne ⟨r, h'⟩⟩
    rwa [this]
  obtain ⟨t₁, ht₁⟩ := hTc.exists_isLeast hne
  obtain ⟨t₂, ht₂⟩ := hTc.exists_isGreatest hne
  have hle : t₁ ≤ t₂ := ht₁.2 ht₂.1
  have hmiss₁ : ∀ r, r < t₁ → a r ∉ range g := fun r hr h => absurd (ht₁.2 h) (not_le.mpr hr)
  have hmiss₂ : ∀ r, t₂ < r → a r ∉ range g := fun r hr h => absurd (ht₂.2 h) (not_le.mpr hr)
  obtain ⟨s₁, hs₁⟩ := ht₁.1
  obtain ⟨s₂, hs₂⟩ := ht₂.1
  have ht₁0 : t₁ ≠ 0 := fun h => h0 (h ▸ ⟨s₁, hs₁⟩)
  have ht₂1 : t₂ ≠ 1 := fun h => h1 (h ▸ ⟨s₂, hs₂⟩)
  have ht₁0' : 0 < t₁ := lt_of_le_of_ne unitInterval.nonneg' ht₁0.symm
  have ht₂1' : t₂ < 1 := lt_of_le_of_ne unitInterval.le_one' ht₂1
  -- the set that survives off `g`
  have hFF : FinConn (range a \ G₀ ∩ a '' (Iio t₁) ∪ (range a \ G₀ ∩ a '' (Ioi t₂))) :=
    (hF.inter_arc ha sdiff_subset ordConnected_Iio).union
      (hF.inter_arc ha sdiff_subset ordConnected_Ioi)
  have hpart₁ : IsArcMap (subArc a 0 t₁) := ha.sub ht₁0.symm
  have hpart₃ : IsArcMap (subArc a t₂ 1) := ha.sub ht₂1
  by_cases heq : t₁ = t₂
  · subst heq
    refine ⟨a, ha, rfl, rfl, subset_union_left, ?_⟩
    have : range a \ (G₀ ∪ range g) =
        range a \ G₀ ∩ a '' (Iio t₁) ∪ (range a \ G₀ ∩ a '' (Ioi t₁)) := by
      ext x
      constructor
      · rintro ⟨⟨r, rfl⟩, h3⟩
        have h4 : a r ∉ G₀ := fun h => h3 (.inl h)
        rcases lt_trichotomy r t₁ with h | rfl | h
        · exact .inl ⟨⟨⟨r, rfl⟩, h4⟩, r, h, rfl⟩
        · exact absurd (.inr ⟨s₁, hs₁⟩) h3
        · exact .inr ⟨⟨⟨r, rfl⟩, h4⟩, r, h, rfl⟩
      · rintro (⟨⟨h2, h3⟩, r, hr, rfl⟩ | ⟨⟨h2, h3⟩, r, hr, rfl⟩)
        · exact ⟨h2, fun h => h.elim h3 (hmiss₁ r hr)⟩
        · exact ⟨h2, fun h => h.elim h3 (hmiss₂ r hr)⟩
    rwa [this]
  have hlt : t₁ < t₂ := lt_of_le_of_ne hle heq
  have hs : s₁ ≠ s₂ := fun h => heq (ha.2 (by rw [← hs₁, ← hs₂, h]))
  have hpart₂ : IsArcMap (subArc g s₁ s₂) := hg.sub hs
  -- first join
  obtain ⟨c, hc, hcr, hc0, hc1⟩ := exists_arc_join hpart₁ hpart₂
    (by rw [subArc_one, subArc_zero, hs₁]) (by
      intro s t he
      have hrt : subArc a 0 t₁ s ∈ a '' Icc 0 t₁ := by
        rw [← range_subArc a unitInterval.nonneg']
        exact ⟨s, rfl⟩
      obtain ⟨r, hr, hrs⟩ := hrt
      have hrng : a r ∈ range g := by
        rw [hrs, he]
        exact range_subArc_subset g _ _ ⟨t, rfl⟩
      have hr1 : r = t₁ := le_antisymm hr.2 (ht₁.2 hrng)
      subst hr1
      have hs1 : s = 1 := by
        apply hpart₁.2
        rw [subArc_one]
        exact hrs.symm
      subst hs1
      refine ⟨rfl, hpart₂.2 ?_⟩
      rw [← he, subArc_zero, subArc_one, hs₁])
  have hrc : range c = a '' Icc 0 t₁ ∪ range (subArc g s₁ s₂) := by
    rw [hcr, range_subArc a unitInterval.nonneg']
  -- second join
  obtain ⟨c', hc', hcr', hc0', hc1'⟩ := exists_arc_join hc hpart₃
    (by rw [hc1, subArc_one, subArc_zero, hs₂]) (by
      intro s t he
      have hrt : subArc a t₂ 1 t ∈ a '' Icc t₂ 1 := by
        rw [← range_subArc a unitInterval.le_one']
        exact ⟨t, rfl⟩
      obtain ⟨r, hr, hrs⟩ := hrt
      have hcs : c s ∈ a '' Icc 0 t₁ ∪ range (subArc g s₁ s₂) := by
        rw [← hrc]
        exact ⟨s, rfl⟩
      have hrng : a r ∈ range g := by
        rcases hcs with ⟨r', hr', hr's⟩ | hcs
        · have : r' = r := ha.2 (by rw [hr's, he, hrs])
          subst this
          exact absurd (hr'.2.trans_lt hlt) (not_lt.mpr hr.1)
        · rw [hrs, ← he]
          exact range_subArc_subset g _ _ hcs
      have hr2 : r = t₂ := le_antisymm (ht₂.2 hrng) hr.1
      subst hr2
      have ht0 : t = 0 := by
        apply hpart₃.2
        rw [subArc_zero]
        exact hrs.symm
      subst ht0
      refine ⟨hc.2 ?_, rfl⟩
      rw [he, subArc_zero, hc1, subArc_one, hs₂])
  refine ⟨c', hc', ?_, ?_, ?_, ?_⟩
  · rw [hc0', hc0, subArc_zero]
  · rw [hc1', subArc_one]
  · rw [hcr', hrc, range_subArc a unitInterval.le_one']
    rintro x ((⟨r, -, rfl⟩ | hx) | ⟨r, -, rfl⟩)
    · exact .inl ⟨r, rfl⟩
    · exact .inr (range_subArc_subset g _ _ hx)
    · exact .inl ⟨r, rfl⟩
  · have : range c' \ (G₀ ∪ range g) =
        range a \ G₀ ∩ a '' (Iio t₁) ∪ (range a \ G₀ ∩ a '' (Ioi t₂)) := by
      rw [hcr', hrc, range_subArc a unitInterval.le_one']
      ext x
      constructor
      · rintro ⟨(⟨r, hr, rfl⟩ | hx) | ⟨r, hr, rfl⟩, h3⟩
        · have h4 : a r ∉ G₀ := fun h => h3 (.inl h)
          have h5 : r ≠ t₁ := fun h => h3 (.inr (h ▸ ⟨s₁, hs₁⟩))
          exact .inl ⟨⟨⟨r, rfl⟩, h4⟩, r, (lt_of_le_of_ne hr.2 h5 : r < t₁), rfl⟩
        · exact absurd (.inr (range_subArc_subset g _ _ hx)) h3
        · have h4 : a r ∉ G₀ := fun h => h3 (.inl h)
          have h5 : t₂ ≠ r := fun h => h3 (.inr (h ▸ ⟨s₂, hs₂⟩))
          exact .inr ⟨⟨⟨r, rfl⟩, h4⟩, r, (lt_of_le_of_ne hr.1 h5 : t₂ < r), rfl⟩
      · rintro (⟨⟨h2, h3⟩, r, hr, rfl⟩ | ⟨⟨h2, h3⟩, r, hr, rfl⟩)
        · refine ⟨.inl (.inl ⟨r, ⟨unitInterval.nonneg', le_of_lt hr⟩, rfl⟩),
            fun h => h.elim h3 (hmiss₁ r hr)⟩
        · refine ⟨.inr ⟨r, ⟨le_of_lt hr, unitInterval.le_one'⟩, rfl⟩,
            fun h => h.elim h3 (hmiss₂ r hr)⟩
    rwa [this]

/-- **Loop erasure.** An arc can be rerouted along a finite list of arcs so that the rest of it is a
finite union of connected sets. -/
theorem exists_erase [T2Space X] (L : List (𝕀 → X)) (hL : ∀ g ∈ L, IsArcMap g) {a : 𝕀 → X}
    (ha : IsArcMap a) (h0 : ∀ g ∈ L, a 0 ∉ range g) (h1 : ∀ g ∈ L, a 1 ∉ range g) :
    ∃ a' : 𝕀 → X, IsArcMap a' ∧ a' 0 = a 0 ∧ a' 1 = a 1 ∧
      range a' ⊆ range a ∪ ⋃ g ∈ L, range g ∧ FinConn (range a' \ ⋃ g ∈ L, range g) := by
  induction L with
  | nil =>
    refine ⟨a, ha, rfl, rfl, subset_union_left, ?_⟩
    simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, sdiff_empty]
    exact finConn_of_isPreconnected (isPreconnected_range ha.1)
  | cons g L ih =>
    obtain ⟨a₁, ha₁, h10, h11, h12, h13⟩ := ih (fun g' hg' => hL g' (.tail _ hg'))
      (fun g' hg' => h0 g' (.tail _ hg')) (fun g' hg' => h1 g' (.tail _ hg'))
    obtain ⟨a₂, ha₂, h20, h21, h22, h23⟩ := exists_arc_step ha₁ (hL g (.head _))
      (by rw [h10]; exact h0 g (.head _)) (by rw [h11]; exact h1 g (.head _)) h13
    have hU : (⋃ g' ∈ g :: L, range g') = (⋃ g' ∈ L, range g') ∪ range g := by
      ext x
      simp only [List.mem_cons, iUnion_iUnion_eq_or_left, mem_iUnion, mem_union, exists_prop]
      exact or_comm
    refine ⟨a₂, ha₂, h20.trans h10, h21.trans h11, ?_, ?_⟩
    · rw [hU]
      intro x hx
      rcases h22 hx with hx | hx
      · rcases h12 hx with hx | hx
        · exact .inl hx
        · exact .inr (.inl hx)
      · exact .inr (.inr hx)
    · rw [hU]
      exact h23

/-- An arc is a finite union of small arcs. -/
theorem IsArcMap.exists_small {Y : Type u} [PseudoMetricSpace Y] {ℓ : 𝕀 → Y} (hℓ : IsArcMap ℓ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : List (𝕀 → Y), (∀ g ∈ L, IsArcMap g) ∧ (⋃ g ∈ L, range g) = range ℓ ∧
      ∀ g ∈ L, ∀ x ∈ range g, ∀ y ∈ range g, dist x y < δ := by
  have hu : UniformContinuous ℓ := CompactSpace.uniformContinuous_of_continuous hℓ.1
  obtain ⟨η, hη, hu'⟩ := Metric.uniformContinuous_iff.mp hu δ hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  let N : ℕ := n + 1
  have hN : (0 : ℝ) < N := by positivity
  let pt : ℕ → 𝕀 := fun i => ⟨min (i / N : ℝ) 1, le_min (by positivity) zero_le_one, min_le_right _
    _⟩
  have hpt : ∀ i ≤ N, (pt i).1 = (i / N : ℝ) := fun i hi => by
    refine min_eq_left ?_
    rw [div_le_one hN]
    exact_mod_cast hi
  have hne : ∀ i < N, pt i ≠ pt (i + 1) := fun i hi h => by
    have h1 := congrArg Subtype.val h
    rw [hpt i hi.le, hpt (i + 1) hi] at h1
    push_cast at h1
    have h2 : (i : ℝ) = i + 1 := by
      field_simp at h1
      linarith
    linarith
  have hle : ∀ i < N, pt i ≤ pt (i + 1) := fun i hi => by
    change (pt i).1 ≤ (pt (i + 1)).1
    rw [hpt i hi.le, hpt (i + 1) hi]
    push_cast
    gcongr
    linarith
  refine ⟨(List.range N).map fun i => subArc ℓ (pt i) (pt (i + 1)), ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact hℓ.sub (hne i (List.mem_range.mp hi))
  · refine subset_antisymm (iUnion₂_subset fun g hg => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
      exact range_subArc_subset _ _ _
    · rintro _ ⟨x, rfl⟩
      -- the interval containing `x`
      have hex : ∃ i, i < N ∧ (i / N : ℝ) ≤ x.1 ∧ x.1 ≤ ((i + 1 : ℕ) / N : ℝ) := by
        by_cases hx1 : x.1 = 1
        · refine ⟨n, by simp [N], ?_, ?_⟩
          · rw [hx1, div_le_one hN]
            simp [N]
          · rw [hx1]
            simp only [N]
            rw [div_self (by positivity)]
        · have hx1' : x.1 < 1 := lt_of_le_of_ne x.2.2 hx1
          refine ⟨⌊x.1 * N⌋₊, ?_, ?_, ?_⟩
          · have : (⌊x.1 * N⌋₊ : ℝ) ≤ x.1 * N := Nat.floor_le (by have := x.2.1; positivity)
            have h3 : (⌊x.1 * N⌋₊ : ℝ) < N := by nlinarith
            exact_mod_cast h3
          · rw [div_le_iff₀ hN]
            exact Nat.floor_le (by have := x.2.1; positivity)
          · rw [le_div_iff₀ hN]
            push_cast
            exact (Nat.lt_floor_add_one _).le
      obtain ⟨i, hi, h1, h2⟩ := hex
      refine mem_iUnion₂.mpr ⟨subArc ℓ (pt i) (pt (i + 1)), List.mem_map.mpr ⟨i, List.mem_range.mpr
        hi,
        rfl⟩, ?_⟩
      rw [range_subArc ℓ (hle i hi)]
      refine ⟨x, ⟨?_, ?_⟩, rfl⟩
      · change (pt i).1 ≤ x.1
        rwa [hpt i hi.le]
      · change x.1 ≤ (pt (i + 1)).1
        rwa [hpt (i + 1) hi]
  · intro g hg x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    have hi' := List.mem_range.mp hi
    rw [range_subArc ℓ (hle i hi')] at hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨r', hr', rfl⟩ := hy
    refine hu' ?_
    have h1 : (pt i).1 = (i / N : ℝ) := hpt i hi'.le
    have h2 : (pt (i + 1)).1 = ((i + 1 : ℕ) / N : ℝ) := hpt (i + 1) hi'
    have h3 : (i / N : ℝ) ≤ r.1 := h1 ▸ hr.1
    have h4 : (i / N : ℝ) ≤ r'.1 := h1 ▸ hr'.1
    have h5 : r.1 ≤ ((i + 1 : ℕ) / N : ℝ) := h2 ▸ hr.2
    have h6 : r'.1 ≤ ((i + 1 : ℕ) / N : ℝ) := h2 ▸ hr'.2
    have h7 : ((i + 1 : ℕ) / N : ℝ) = i / N + 1 / N := by
      push_cast
      ring
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    have h8 : (1 / N : ℝ) = 1 / (n + 1) := by simp [N]
    constructor <;> linarith

/-- **Taming two arcs.** Let `a` and `b` be two arcs with the same ends, meeting only in their ends,
and let `G` be a finite union of arcs that misses the ends. Then `a` and `b` can be moved, by less
than `ε`, so that the result has the same properties and the part of it off `G` is a finite union
of connected sets. -/
theorem exists_tame_pair {Y : Type u} [MetricSpace Y] (G : List (𝕀 → Y)) (hG : ∀ g ∈ G, IsArcMap g)
    {a b : 𝕀 → Y} (ha : IsArcMap a) (hb : IsArcMap b) (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hp : ∀ g ∈ G, a 0 ∉ range g) (hq : ∀ g ∈ G, a 1 ∉ range g) {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b' : 𝕀 → Y, IsArcMap a' ∧ IsArcMap b' ∧ a' 0 = a 0 ∧ a' 1 = a 1 ∧ b' 0 = a 0 ∧ b' 1 = a 1 ∧
      (∀ s t, a' s = b' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      range a' ⊆ thickening ε (range a) ∧ range b' ⊆ thickening ε (range b) ∧
      FinConn ((range a' ∪ range b') \ ⋃ g ∈ G, range g) := by
  classical
  set G₀ : Set Y := ⋃ g ∈ G, range g with hG₀
  have hG₀c : IsClosed G₀ := by
    have : IsCompact G₀ := G.finite_toSet.isCompact_biUnion fun g hg =>
      isCompact_range (hG g hg).1
    exact this.isClosed
  have hAc : IsCompact (range a) := isCompact_range ha.1
  have hBc : IsCompact (range b) := isCompact_range hb.1
  have hdisj : Disjoint (range a ∩ G₀) (range b ∩ G₀) := by
    rw [Set.disjoint_left]
    rintro _ ⟨⟨s, rfl⟩, hs⟩ ⟨⟨t, ht⟩, -⟩
    obtain ⟨g, hg, hsg⟩ := mem_iUnion₂.mp hs
    rcases hm s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hp g hg hsg
    · exact hq g hg hsg
  obtain ⟨δ₀, hδ₀, hthick⟩ := hdisj.exists_thickenings (hAc.inter_right hG₀c)
    (hBc.isClosed.inter hG₀c)
  have hfar : ∀ x ∈ range a ∩ G₀, ∀ y ∈ range b ∩ G₀, δ₀ ≤ dist x y := by
    intro x hx y hy
    by_contra hlt
    refine Set.disjoint_left.mp hthick (self_subset_thickening hδ₀ _ hx) ?_
    exact mem_thickening_iff.mpr ⟨y, hy, not_le.mp hlt⟩
  set δ : ℝ := min ε (δ₀ / 3) with hδdef
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ3 : δ ≤ δ₀ / 3 := min_le_right _ _
  -- cut `G` into small arcs
  have hcut : ∃ L : List (𝕀 → Y), (∀ g ∈ L, IsArcMap g) ∧ (⋃ g ∈ L, range g) = G₀ ∧
      ∀ g ∈ L, ∀ x ∈ range g, ∀ y ∈ range g, dist x y < δ := by
    clear_value G₀
    subst hG₀
    clear hG₀c hdisj hthick hfar
    induction G with
    | nil =>
      exact ⟨[], by simp, by simp, by simp⟩
    | cons g G ih =>
      obtain ⟨L₁, h1', h2', h3'⟩ := (hG g (.head _)).exists_small hδ
      obtain ⟨L₂, h1'', h2'', h3''⟩ := ih (fun g' hg' => hG g' (.tail _ hg'))
        (fun g' hg' => hp g' (.tail _ hg')) (fun g' hg' => hq g' (.tail _ hg'))
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h1' g' h
        · exact h1'' g' h
      · ext x
        simp only [mem_iUnion, List.mem_append, exists_prop, List.mem_cons]
        have e1 := Set.ext_iff.mp h2' x
        have e2 := Set.ext_iff.mp h2'' x
        simp only [mem_iUnion, exists_prop] at e1 e2
        constructor
        · rintro ⟨g', hg' | hg', hx⟩
          · exact ⟨g, .inl rfl, e1.mp ⟨g', hg', hx⟩⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mp ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
        · rintro ⟨g', rfl | hg', hx⟩
          · obtain ⟨g'', h5, h6⟩ := e1.mpr hx
            exact ⟨g'', .inl h5, h6⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mpr ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h3' g' h
        · exact h3'' g' h
  obtain ⟨L, hL1, hL2, hL3⟩ := hcut
  have hLG : ∀ g ∈ L, range g ⊆ G₀ := fun g hg => by
    rw [← hL2]
    intro x hx
    exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hx⟩⟩
  let La := L.filter fun g => (range g ∩ range a).Nonempty
  let Lb := L.filter fun g => (range g ∩ range b).Nonempty
  have hLa : ∀ g ∈ La, g ∈ L ∧ (range g ∩ range a).Nonempty := fun g hg => by
    simpa [La] using hg
  have hLb : ∀ g ∈ Lb, g ∈ L ∧ (range g ∩ range b).Nonempty := fun g hg => by
    simpa [Lb] using hg
  have hmissG : ∀ g ∈ L, a 0 ∉ range g ∧ a 1 ∉ range g := fun g hg => by
    constructor
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hp g' h5 h6
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hq g' h5 h6
  obtain ⟨a', ha', ha0, ha1, ha2, ha3⟩ := exists_erase La (fun g hg => hL1 g (hLa g hg).1) ha
    (fun g hg => (hmissG g (hLa g hg).1).1) (fun g hg => (hmissG g (hLa g hg).1).2)
  obtain ⟨b', hb', hb0, hb1, hb2, hb3⟩ := exists_erase Lb (fun g hg => hL1 g (hLb g hg).1) hb
    (fun g hg => h0 ▸ (hmissG g (hLb g hg).1).1) (fun g hg => h1 ▸ (hmissG g (hLb g hg).1).2)
  -- a point of the new arc off the old one is near the old one
  have hnear : ∀ {c : 𝕀 → Y} {L' : List (𝕀 → Y)}, (∀ g ∈ L', g ∈ L ∧ (range g ∩ range c).Nonempty) →
      ∀ x ∈ ⋃ g ∈ L', range g, ∃ y ∈ range c ∩ G₀, dist x y < δ := by
    intro c L' hL' x hx
    obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyg, hyc⟩ := (hL' g hg).2
    exact ⟨y, ⟨hyc, hLG g (hL' g hg).1 hyg⟩, hL3 g (hL' g hg).1 x hxg y hyg⟩
  have hsep : ∀ x y, x ∈ range a ∪ ⋃ g ∈ La, range g → y ∈ range b ∪ ⋃ g ∈ Lb, range g → x = y →
      x ∈ range a ∧ x ∈ range b := by
    intro x y hx hy hxy
    subst hxy
    have hxG : ∀ {L' : List (𝕀 → Y)}, (∀ g ∈ L', g ∈ L) → x ∈ (⋃ g ∈ L', range g) → x ∈ G₀ := by
      intro L' h1 h2
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h2
      exact hLG g (h1 g hg) hxg
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨hx, hy⟩
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLb x hy
      have h3 := hfar x ⟨hx, hxG (fun g hg => (hLb g hg).1) hy⟩ w hw
      linarith
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLa x hx
      have h3 := hfar w hw x ⟨hy, hxG (fun g hg => (hLa g hg).1) hx⟩
      rw [dist_comm] at h3
      linarith
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLa x hx
      obtain ⟨w', hw', hd'⟩ := hnear hLb x hy
      have h3 := hfar w hw w' hw'
      have h4 := dist_triangle_left w w' x
      linarith
  have hsdiff : ∀ {c : 𝕀 → Y} {c' : 𝕀 → Y} {L' : List (𝕀 → Y)},
      (∀ g ∈ L, (range g ∩ range c).Nonempty → g ∈ L') → (∀ g ∈ L', g ∈ L) →
      range c' ⊆ range c ∪ ⋃ g ∈ L', range g → range c' \ G₀ = range c' \ ⋃ g ∈ L', range g := by
    intro c c' L' h1 h2 h3
    ext x
    constructor
    · rintro ⟨h4, h5⟩
      refine ⟨h4, fun h6 => h5 ?_⟩
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
      exact hLG g (h2 g hg) hxg
    · rintro ⟨h4, h5⟩
      refine ⟨h4, fun h6 => ?_⟩
      rw [← hL2] at h6
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
      rcases h3 h4 with h7 | h7
      · exact h5 (mem_iUnion₂.mpr ⟨g, h1 g hg ⟨x, hxg, h7⟩, hxg⟩)
      · exact h5 h7
  have hthickA : ∀ {c c' : 𝕀 → Y} {L' : List (𝕀 → Y)},
      (∀ g ∈ L', g ∈ L ∧ (range g ∩ range c).Nonempty) → range c' ⊆ range c ∪ ⋃ g ∈ L', range g →
      range c' ⊆ thickening ε (range c) := by
    intro c c' L' h1 h2 x hx
    rcases h2 hx with h3 | h3
    · exact self_subset_thickening hε _ h3
    · obtain ⟨y, hy, hd⟩ := hnear h1 x h3
      exact mem_thickening_iff.mpr ⟨y, hy.1, hd.trans_le hδε⟩
  refine ⟨a', b', ha', hb', ha0, ha1, hb0.trans h0, hb1.trans h1, ?_, hthickA hLa ha2,
    hthickA hLb hb2, ?_⟩
  · intro s t he
    obtain ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ := hsep _ _ (ha2 ⟨s, rfl⟩) (hb2 ⟨t, rfl⟩) he
    rcases hm s' t' (hs'.trans ht'.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      have e1 : a' s = a' 0 := by rw [← hs', ha0]
      have e2 : b' t = b' 0 := by rw [← he, ← hs', hb0, h0]
      exact ⟨ha'.2 e1, hb'.2 e2⟩
    · right
      have e1 : a' s = a' 1 := by rw [← hs', ha1]
      have e2 : b' t = b' 1 := by rw [← he, ← hs', hb1, h1]
      exact ⟨ha'.2 e1, hb'.2 e2⟩
  · have e1 := hsdiff (c := a) (c' := a') (L' := La) (fun g hg h => by simp [La, hg, h])
      (fun g hg => (hLa g hg).1) ha2
    have e2 := hsdiff (c := b) (c' := b') (L' := Lb) (fun g hg h => by simp [Lb, hg, h])
      (fun g hg => (hLb g hg).1) hb2
    rw [union_sdiff_distrib, e1, e2]
    exact ha3.union hb3

end GraphMinor.Surface
