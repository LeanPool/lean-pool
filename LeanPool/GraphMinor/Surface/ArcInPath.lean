/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.UnitInterval
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Zorn
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Denumerable
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Rat

/-!
# A path in a Hausdorff space contains an arc

Let `γ` be a path in a Hausdorff space with different ends. This file finds an injective path with
the same ends inside the image of `γ`. Mathlib does not have this fact.

The route: call a closed set `T ⊆ [0, 1]` containing the ends *admissible* if `γ` takes equal values
at the two ends of every gap of `T`. By Zorn's lemma there is a minimal admissible set
(`exists_minimal_admissible`). Minimality gives: if `γ s = γ t` with `s < t` in `T`, then `T` has no
point between `s` and `t`. So the order on `T`, with the gaps closed up, is dense, and Cantor's
isomorphism theorem gives a monotone continuous map from `[0, 1]` onto `[0, 1]` that closes the
gaps.
Then `γ` restricted to `T` factors through this map, and the factor is the injective path.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

local notation "𝕀" => unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- The closed set `T` contains the ends of `[0, 1]`, and `γ` agrees at the two ends of each gap. -/
def IsAdmissible (γ : 𝕀 → X) (T : Set 𝕀) : Prop :=
  IsClosed T ∧ (0 : 𝕀) ∈ T ∧ (1 : 𝕀) ∈ T ∧
    ∀ a ∈ T, ∀ b ∈ T, a < b → Ioo a b ∩ T = ∅ → γ a = γ b

/-- The intersection of a chain of admissible sets is admissible. -/
private theorem isAdmissible_sInter [T2Space X] {γ : 𝕀 → X} (hγ : Continuous γ) {c : Set (Set 𝕀)}
    (hc : ∀ T ∈ c, IsAdmissible γ T) (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    IsAdmissible γ (⋂₀ c) := by
  refine ⟨isClosed_sInter fun T hT => (hc T hT).1, fun T hT => (hc T hT).2.1,
    fun T hT => (hc T hT).2.2.1, fun a ha b hb hab hgap => ?_⟩
  by_contra hne'
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hne'
  have hUn : γ ⁻¹' U ∈ 𝓝[>] a := mem_nhdsWithin_of_mem_nhds (hγ.continuousAt.preimage_mem_nhds
    (hU.mem_nhds haU))
  have hVn : γ ⁻¹' V ∈ 𝓝[<] b := mem_nhdsWithin_of_mem_nhds (hγ.continuousAt.preimage_mem_nhds
    (hV.mem_nhds hbV))
  obtain ⟨a', ha', hUsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hab).mp hUn
  obtain ⟨b', hb', hVsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hab).mp hVn
  -- Choose points `p ≤ q` strictly inside the gap, near `a` and near `b`.
  have ha'' : a < a' := ha'
  have hb'' : b' < b := hb'
  obtain ⟨p, hp⟩ := exists_between (lt_min ha'' hab)
  have hpa' : p < a' := lt_of_lt_of_le hp.2 (min_le_left _ _)
  have hpb : p < b := lt_of_lt_of_le hp.2 (min_le_right _ _)
  obtain ⟨q, hq⟩ := exists_between (max_lt hb'' hpb)
  have hqb' : b' < q := lt_of_le_of_lt (le_max_left _ _) hq.1
  have hpq : p < q := lt_of_le_of_lt (le_max_right _ _) hq.1
  -- One member of the chain misses `[p, q]`.
  have hmiss : ∃ T ∈ c, Icc p q ∩ T = ∅ := by
    by_contra hall
    push Not at hall
    have hcomp : IsCompact (Icc p q) := isCompact_Icc
    have hnon := hcomp.inter_iInter_nonempty (fun T : c => T.1) (fun T => (hc T.1 T.2).1) ?_
    · obtain ⟨z, hz1, hz2⟩ := hnon
      have hz : z ∈ ⋂₀ c := mem_sInter.mpr fun T hT => mem_iInter.mp hz2 ⟨T, hT⟩
      have hzgap : z ∈ Ioo a b := ⟨lt_of_lt_of_le hp.1 hz1.1, lt_of_le_of_lt hz1.2 hq.2⟩
      have : z ∈ Ioo a b ∩ ⋂₀ c := ⟨hzgap, hz⟩
      rw [hgap] at this
      exact this
    · intro s
      induction s using Finset.induction_on with
      | empty =>
        obtain ⟨T, hT⟩ := hne
        obtain ⟨z, hz⟩ := hall T hT
        exact ⟨z, hz.1, by simp⟩
      | insert T s hTs ih =>
        obtain ⟨z, hz1, hz2⟩ := ih
        by_cases hs : s = ∅
        · subst hs
          obtain ⟨z', hz'⟩ := hall T.1 T.2
          exact ⟨z', hz'.1, by simpa using hz'.2⟩
        · -- The smallest set in `s ∪ {T}` lies in all of them.
          have hmin : ∃ T' ∈ c, (T' ⊆ T.1) ∧ ∀ W ∈ s, T' ⊆ W.1 := by
            have : ∀ s : Finset c, ∃ T' ∈ c, (T' ⊆ T.1) ∧ ∀ W ∈ s, T' ⊆ W.1 := by
              intro s
              induction s using Finset.induction_on with
              | empty => exact ⟨T.1, T.2, Subset.rfl, by simp⟩
              | insert W s _ ih =>
                obtain ⟨T', hT', h1, h2⟩ := ih
                rcases hchain.total hT' W.2 with h | h
                · refine ⟨T', hT', h1, ?_⟩
                  intro W' hW'
                  rcases Finset.mem_insert.mp hW' with rfl | hW'
                  · exact h
                  · exact h2 W' hW'
                · refine ⟨W.1, W.2, h.trans h1, ?_⟩
                  intro W' hW'
                  rcases Finset.mem_insert.mp hW' with rfl | hW'
                  · exact Subset.rfl
                  · exact h.trans (h2 W' hW')
            exact this s
          obtain ⟨T', hT', h1, h2⟩ := hmin
          obtain ⟨z', hz'⟩ := hall T' hT'
          refine ⟨z', hz'.1, ?_⟩
          simp only [Finset.set_biInter_insert]
          refine ⟨h1 hz'.2, ?_⟩
          simp only [mem_iInter]
          exact fun W hW => h2 W hW hz'.2
  obtain ⟨T, hT, hmissT⟩ := hmiss
  have haT : a ∈ T := mem_sInter.mp ha T hT
  have hbT : b ∈ T := mem_sInter.mp hb T hT
  have hTc : IsClosed T := (hc T hT).1
  -- The last point of `T` below `p` and the first point of `T` above `q`.
  have hL : IsCompact (T ∩ Iic p) := hTc.isCompact.inter_right isClosed_Iic
  have hR : IsCompact (T ∩ Ici q) := hTc.isCompact.inter_right isClosed_Ici
  obtain ⟨l, hl, hlmax⟩ := hL.exists_isGreatest ⟨a, haT, hp.1.le⟩
  obtain ⟨r, hr, hrmin⟩ := hR.exists_isLeast ⟨b, hbT, hq.2.le⟩
  have hal : a ≤ l := hlmax ⟨haT, hp.1.le⟩
  have hrb : r ≤ b := hrmin ⟨hbT, hq.2.le⟩
  have hlr : l < r := lt_of_le_of_lt hl.2 (lt_of_lt_of_le hpq hr.2)
  have hgapT : Ioo l r ∩ T = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hzT⟩
    rcases le_total z p with h | h
    · exact absurd (hlmax ⟨hzT, h⟩) (not_le.mpr hz1.1)
    · rcases le_total z q with h' | h'
      · have : z ∈ Icc p q ∩ T := ⟨⟨h, h'⟩, hzT⟩
        rw [hmissT] at this
        exact this
      · exact absurd (hrmin ⟨hzT, h'⟩) (not_le.mpr hz1.2)
  have heq := (hc T hT).2.2.2 l hl.1 r hr.1 hlr hgapT
  have hlU : γ l ∈ U := by
    rcases eq_or_lt_of_le hal with h | h
    · rw [← h]; exact haU
    · exact hUsub ⟨h, lt_of_le_of_lt hl.2 hpa'⟩
  have hrV : γ r ∈ V := by
    rcases eq_or_lt_of_le hrb with h | h
    · rw [h]; exact hbV
    · exact hVsub ⟨lt_of_lt_of_le hqb' hr.2, h⟩
  exact Set.disjoint_left.mp hUV hlU (heq ▸ hrV)

/-- There is a minimal admissible set. -/
theorem exists_minimal_admissible [T2Space X] {γ : 𝕀 → X} (hγ : Continuous γ) :
    ∃ T, Minimal (IsAdmissible γ) T := by
  have hS : IsAdmissible γ (univ : Set 𝕀) :=
    ⟨isClosed_univ, mem_univ _, mem_univ _, fun a _ b _ hab h => by
      obtain ⟨z, hz⟩ := exists_between hab
      have : z ∈ Ioo a b ∩ univ := ⟨hz, mem_univ _⟩
      rw [h] at this
      exact absurd this (notMem_empty z)⟩
  obtain ⟨T, -, hT⟩ := zorn_superset_nonempty {T | IsAdmissible γ T}
    (fun c hc hchain hne => ⟨⋂₀ c, isAdmissible_sInter hγ hc hchain hne,
      fun T hT => sInter_subset_of_mem hT⟩) univ hS
  exact ⟨T, hT⟩

/-- A monotone continuous surjection of `[0, 1]` that is strictly increasing on a given dense-in-
itself order `Z`, and that closes every interval free of `Z`. This is where Cantor's isomorphism
theorem enters. -/
private theorem exists_collapse (Z : Set 𝕀) (hne : Z.Nonempty)
    (hdense : ∀ y ∈ Z, ∀ y' ∈ Z, y < y' → ∃ z ∈ Z, y < z ∧ z < y')
    (hmax : ∀ y ∈ Z, ∃ z ∈ Z, y < z) (hmin : ∀ y ∈ Z, ∃ z ∈ Z, z < y) :
    ∃ c : 𝕀 → 𝕀, Monotone c ∧ Continuous c ∧ Dense (c '' Z) ∧ c 0 = 0 ∧ c 1 = 1 ∧
      (∀ y ∈ Z, ∀ y' ∈ Z, y < y' → c y < c y') ∧
      (∀ s t : 𝕀, s < t → Ioc s t ∩ Z = ∅ → c s = c t) := by
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Z
  -- Between two points of `Z` lies a point of `S`.
  have hbetween : ∀ y y' : Z, y < y' → ∃ d ∈ S, y < d ∧ d < y' := by
    intro y y' hyy
    obtain ⟨z, hz, h1, h2⟩ := hdense y.1 y.2 y'.1 y'.2 hyy
    have hopen : IsOpen {w : Z | y < w ∧ w < y'} :=
      isOpen_Ioo.preimage continuous_subtype_val
    obtain ⟨d, hd1, hd2⟩ := hSdense.inter_open_nonempty _ hopen ⟨⟨z, hz⟩, h1, h2⟩
    exact ⟨d, hd2, hd1.1, hd1.2⟩
  let D := S
  have : Countable D := hScount.to_subtype
  have hDne : Nonempty D := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, hyz⟩ := hmax y hy
    obtain ⟨d, hd, -⟩ := hbetween ⟨y, hy⟩ ⟨z, hz⟩ hyz
    exact ⟨⟨d, hd⟩⟩
  have : DenselyOrdered D := ⟨fun a b hab => by
    obtain ⟨d, hd, h1, h2⟩ := hbetween a.1 b.1 hab
    exact ⟨⟨d, hd⟩, h1, h2⟩⟩
  have : NoMaxOrder D := ⟨fun a => by
    obtain ⟨z, hz, h⟩ := hmax a.1.1 a.1.2
    obtain ⟨d, hd, h1, -⟩ := hbetween a.1 ⟨z, hz⟩ h
    exact ⟨⟨d, hd⟩, h1⟩⟩
  have : NoMinOrder D := ⟨fun a => by
    obtain ⟨z, hz, h⟩ := hmin a.1.1 a.1.2
    obtain ⟨d, hd, -, h2⟩ := hbetween ⟨z, hz⟩ a.1 h
    exact ⟨⟨d, hd⟩, h2⟩⟩
  let E := Ioo (0 : ℚ) 1
  have : Countable E := Subtype.countable
  have hEne : Nonempty E := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  have : DenselyOrdered E := ⟨fun a b hab => by
    obtain ⟨q, h1, h2⟩ := exists_between (show (a : ℚ) < b from hab)
    exact ⟨⟨q, a.2.1.trans h1, h2.trans b.2.2⟩, h1, h2⟩⟩
  have : NoMaxOrder E := ⟨fun a => by
    obtain ⟨q, h1, h2⟩ := exists_between a.2.2
    exact ⟨⟨q, a.2.1.trans h1, h2⟩, h1⟩⟩
  have : NoMinOrder E := ⟨fun a => by
    obtain ⟨q, h1, h2⟩ := exists_between a.2.1
    exact ⟨⟨q, h1, h2.trans a.2.2⟩, h2⟩⟩
  obtain ⟨e⟩ : Nonempty (D ≃o E) := Order.iso_of_countable_dense D E
  -- The real value attached to a point of `D`.
  let v : D → ℝ := fun d => ((e d : ℚ) : ℝ)
  have hv0 : ∀ d, 0 ≤ v d := fun d => by
    have := (e d).2.1
    simp only [v]
    exact_mod_cast this.le
  have hv1 : ∀ d, v d ≤ 1 := fun d => by
    have := (e d).2.2
    simp only [v]
    exact_mod_cast this.le
  have hvmono : ∀ {a b : D}, a ≤ b → v a ≤ v b := fun {a b} h => by
    have : (e a : ℚ) ≤ e b := e.monotone h
    simp only [v]
    exact_mod_cast this
  have hvstrict : ∀ {a b : D}, a < b → v a < v b := fun {a b} h => by
    have : (e a : ℚ) < e b := e.strictMono h
    simp only [v]
    exact_mod_cast this
  let W : 𝕀 → Set ℝ := fun t => insert 0 (v '' {d : D | ((d : Z) : 𝕀) ≤ t})
  have hWbdd : ∀ t, BddAbove (W t) := fun t => ⟨1, by
    rintro x (rfl | ⟨d, -, rfl⟩)
    · exact zero_le_one
    · exact hv1 d⟩
  have hWne : ∀ t, (W t).Nonempty := fun t => ⟨0, mem_insert _ _⟩
  let r : 𝕀 → ℝ := fun t => sSup (W t)
  have hr0 : ∀ t, 0 ≤ r t := fun t => le_csSup (hWbdd t) (mem_insert _ _)
  have hr1 : ∀ t, r t ≤ 1 := fun t => csSup_le (hWne t) (by
    rintro x (rfl | ⟨d, -, rfl⟩)
    · exact zero_le_one
    · exact hv1 d)
  let c : 𝕀 → 𝕀 := fun t => ⟨r t, hr0 t, hr1 t⟩
  have hcmono : Monotone c := by
    intro s t hst
    refine csSup_le_csSup (hWbdd t) (hWne s) ?_
    rintro x (rfl | ⟨d, hd, rfl⟩)
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨d, le_trans hd hst, rfl⟩
  have hcD : ∀ d : D, r ((d : Z) : 𝕀) = v d := by
    intro d
    refine le_antisymm (csSup_le (hWne _) ?_) (le_csSup (hWbdd _) (mem_insert_of_mem _ ⟨d, le_refl
      ((d : Z) : 𝕀), rfl⟩))
    rintro x (rfl | ⟨d', hd', rfl⟩)
    · exact hv0 d
    · exact hvmono hd'
  have hdenseimg : Dense (c '' Z) := by
    refine dense_of_exists_between fun a b hab => ?_
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt a.2.1 h1
    have hq1 : (q : ℝ) < 1 := lt_of_lt_of_le h2 b.2.2
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have hq1' : q < (1 : ℚ) := by exact_mod_cast hq1
    let d : D := e.symm ⟨q, hq0', hq1'⟩
    have hdv : v d = q := by simp [v, d]
    refine ⟨c ((d : Z) : 𝕀), ⟨_, (d : Z).2, rfl⟩, ?_, ?_⟩
    · change (a : ℝ) < r _
      rw [hcD, hdv]
      exact h1
    · change r _ < (b : ℝ)
      rw [hcD, hdv]
      exact h2
  have hcc : Continuous c := hcmono.continuous_of_denseRange
    (hdenseimg.mono (image_subset_range c Z))
  have hsurj : Function.Surjective c := by
    have hcl : IsClosed (range c) := (isCompact_range hcc).isClosed
    have : range c = univ :=
      (hdenseimg.mono (image_subset_range c Z)).closure_eq ▸ hcl.closure_eq.symm
    exact range_eq_univ.mp this
  refine ⟨c, hcmono, hcc, hdenseimg, ?_, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hsurj 0
    have h := hcmono (unitInterval.nonneg' (t := t))
    rw [ht] at h
    exact le_antisymm h unitInterval.nonneg'
  · obtain ⟨t, ht⟩ := hsurj 1
    have h := hcmono (unitInterval.le_one' (t := t))
    rw [ht] at h
    exact le_antisymm unitInterval.le_one' h
  · intro y hy y' hy' hyy
    obtain ⟨d₁, hd₁, h1, h2⟩ := hbetween ⟨y, hy⟩ ⟨y', hy'⟩ hyy
    obtain ⟨d₂, hd₂, h3, h4⟩ := hbetween d₁ ⟨y', hy'⟩ h2
    have h5 : c y ≤ c (d₁ : 𝕀) := hcmono (le_of_lt h1)
    have h6 : c (d₂ : 𝕀) ≤ c y' := hcmono (le_of_lt h4)
    have h7 : c (d₁ : 𝕀) < c (d₂ : 𝕀) := by
      change r _ < r _
      rw [hcD ⟨d₁, hd₁⟩, hcD ⟨d₂, hd₂⟩]
      exact hvstrict h3
    exact lt_of_le_of_lt h5 (lt_of_lt_of_le h7 h6)
  · intro s t hst hgap
    refine Subtype.ext ?_
    change sSup (W s) = sSup (W t)
    have : W s = W t := by
      refine congrArg (insert 0) (congrArg _ ?_)
      ext d
      constructor
      · exact fun h => le_trans h hst.le
      · intro h
        by_contra hd
        have hm : ((d : Z) : 𝕀) ∈ Ioc s t ∩ Z := ⟨⟨not_le.mp hd, h⟩, (d : Z).2⟩
        rw [hgap] at hm
        exact hm
    rw [this]

section Minimal

variable [T2Space X] {γ : 𝕀 → X} {T : Set 𝕀}

omit [TopologicalSpace X] [T2Space X] in
/-- In a minimal admissible set, equal values of `γ` leave no point of the set between them. -/
private theorem Ioo_inter_eq_empty (hT : Minimal (IsAdmissible γ) T) {s t : 𝕀} (hs : s ∈ T)
    (ht : t ∈ T) (_hst : s < t) (heq : γ s = γ t) : Ioo s t ∩ T = ∅ := by
  have hadm : IsAdmissible γ (T \ Ioo s t) := by
    refine ⟨hT.1.1.sdiff isOpen_Ioo, ⟨hT.1.2.1, fun h => absurd h.1 (unitInterval.nonneg' (t
      := s)).not_gt⟩,
      ⟨hT.1.2.2.1, fun h => absurd h.2 (unitInterval.le_one' (t := t)).not_gt⟩, ?_⟩
    rintro a ⟨haT, ha⟩ b ⟨hbT, hb⟩ hab hgap
    by_cases hempty : Ioo a b ∩ T = ∅
    · exact hT.1.2.2.2 a haT b hbT hab hempty
    obtain ⟨z, hz, hzT⟩ := nonempty_iff_ne_empty.mpr hempty
    have hzin : z ∈ Ioo s t := by
      by_contra hn
      have : z ∈ Ioo a b ∩ (T \ Ioo s t) := ⟨hz, hzT, hn⟩
      rw [hgap] at this
      exact this
    have has : a ≤ s := by
      by_contra hc
      exact ha ⟨not_le.mp hc, hz.1.trans hzin.2⟩
    have htb : t ≤ b := by
      by_contra hc
      exact hb ⟨hzin.1.trans hz.2, not_le.mp hc⟩
    have hab' : a = s := by
      by_contra hne
      have : s ∈ Ioo a b ∩ (T \ Ioo s t) :=
        ⟨⟨lt_of_le_of_ne has hne, hzin.1.trans hz.2⟩, hs, fun h => lt_irrefl _ h.1⟩
      rw [hgap] at this
      exact this
    have hbb : b = t := by
      by_contra hne
      have : t ∈ Ioo a b ∩ (T \ Ioo s t) :=
        ⟨⟨hz.1.trans hzin.2, lt_of_le_of_ne htb (Ne.symm hne)⟩, ht, fun h => lt_irrefl _ h.2⟩
      rw [hgap] at this
      exact this
    rw [hab', hbb]
    exact heq
  have hsub : T ⊆ T \ Ioo s t := hT.2 hadm sdiff_subset
  rw [eq_empty_iff_forall_notMem]
  rintro z ⟨hz, hzT⟩
  exact (hsub hzT).2 hz

/-- `t` is the right end of a gap of `T`. -/
private def IsRightEnd (T : Set 𝕀) (t : 𝕀) : Prop := ∃ a ∈ T, a < t ∧ Ioo a t ∩ T = ∅

/-- Between two points of `T` with different values lies a point of `T` that is no right end, with
a third value. -/
private theorem exists_between_of_ne (hγ : Continuous γ) (hT : Minimal (IsAdmissible γ) T)
    {s t : 𝕀} (hs : s ∈ T) (ht : t ∈ T) (hst : s < t) (hne : γ s ≠ γ t) :
    ∃ z ∈ T, s < z ∧ z < t ∧ ¬ IsRightEnd T z ∧ γ z ≠ γ s ∧ γ z ≠ γ t := by
  have hTc := hT.1.1
  have hA : IsCompact (T ∩ Icc s t ∩ γ ⁻¹' {γ s}) :=
    (hTc.inter isClosed_Icc).isCompact.inter_right (isClosed_singleton.preimage hγ)
  obtain ⟨a, ha, hamax⟩ := hA.exists_isGreatest ⟨s, ⟨hs, le_rfl, hst.le⟩, rfl⟩
  have hB : IsCompact (T ∩ Icc a t ∩ γ ⁻¹' {γ t}) :=
    (hTc.inter isClosed_Icc).isCompact.inter_right (isClosed_singleton.preimage hγ)
  obtain ⟨b, hb, hbmin⟩ := hB.exists_isLeast ⟨t, ⟨ht, ha.1.2.2, le_rfl⟩, rfl⟩
  have hγa : γ a = γ s := ha.2
  have hγb : γ b = γ t := hb.2
  have hab : a < b := lt_of_le_of_ne hb.1.2.1 fun h => hne (by rw [← hγa, h, hγb])
  have hgapne : Ioo a b ∩ T ≠ ∅ := by
    intro hempty
    apply hne
    rw [← hγa, ← hγb]
    exact hT.1.2.2.2 a ha.1.1 b hb.1.1 hab hempty
  obtain ⟨p, hp, hpT⟩ := nonempty_iff_ne_empty.mpr hgapne
  have hsa : s ≤ a := ha.1.2.1
  have hbt : b ≤ t := hb.1.2.2
  have hps : γ p ≠ γ s := fun h =>
    absurd (hamax ⟨⟨hpT, hsa.trans hp.1.le, hp.2.le.trans hbt⟩, h⟩) (not_le.mpr hp.1)
  have hpt : γ p ≠ γ t := fun h =>
    absurd (hbmin ⟨⟨hpT, hp.1.le, hp.2.le.trans hbt⟩, h⟩) (not_le.mpr hp.2)
  by_cases hre : IsRightEnd T p
  · obtain ⟨q, hqT, hqp, hgap⟩ := hre
    have hγq : γ q = γ p := hT.1.2.2.2 q hqT p hpT hqp hgap
    have haq : a ≤ q := by
      by_contra hc
      have : a ∈ Ioo q p ∩ T := ⟨⟨not_le.mp hc, hp.1⟩, ha.1.1⟩
      rw [hgap] at this
      exact this
    have haq' : a < q := lt_of_le_of_ne haq fun h => hps (by rw [← hγq, ← h, hγa])
    refine ⟨q, hqT, lt_of_le_of_lt hsa haq', hqp.trans (hp.2.trans_le hbt), ?_, hγq ▸ hps, hγq ▸
      hpt⟩
    rintro ⟨q', hq'T, hq'q, hgap'⟩
    have hγq' : γ q' = γ q := hT.1.2.2.2 q' hq'T q hqT hq'q hgap'
    have := Ioo_inter_eq_empty hT hq'T hpT (hq'q.trans hqp) (hγq'.trans hγq)
    have hm : q ∈ Ioo q' p ∩ T := ⟨⟨hq'q, hqp⟩, hqT⟩
    rw [this] at hm
    exact hm
  · exact ⟨p, hpT, lt_of_le_of_lt hsa hp.1, hp.2.trans_le hbt, hre, hps, hpt⟩

/-- The points of `T` that survive the collapse. -/
private def coreSet (T : Set 𝕀) (γ : 𝕀 → X) : Set 𝕀 :=
  {t | t ∈ T ∧ ¬ IsRightEnd T t ∧ γ t ≠ γ 0 ∧ γ t ≠ γ 1}

private theorem exists_core_between (hγ : Continuous γ) (hT : Minimal (IsAdmissible γ) T)
    (h01 : γ 0 ≠ γ 1) {s t : 𝕀} (hs : s ∈ T) (ht : t ∈ T) (hst : s < t) (hne : γ s ≠ γ t) :
    ∃ z ∈ coreSet T γ, s < z ∧ z < t ∧ γ z ≠ γ s := by
  have hTc := hT.1.1
  have h0T := hT.1.2.1
  have h1T := hT.1.2.2.1
  have hA : IsCompact (T ∩ γ ⁻¹' {γ 0}) := hTc.isCompact.inter_right (isClosed_singleton.preimage
    hγ)
  have hB : IsCompact (T ∩ γ ⁻¹' {γ 1}) := hTc.isCompact.inter_right (isClosed_singleton.preimage
    hγ)
  obtain ⟨a, ha, hamax⟩ := hA.exists_isGreatest ⟨0, h0T, rfl⟩
  obtain ⟨b, hb, hbmin⟩ := hB.exists_isLeast ⟨1, h1T, rfl⟩
  have hγa : γ a = γ 0 := ha.2
  have hγb : γ b = γ 1 := hb.2
  have h01lt : (0 : 𝕀) < 1 := zero_lt_one
  have hend0 : ∀ z ∈ T, z < a → z = 0 := by
    intro z hz hza
    by_contra h0
    have hzpos : 0 < z := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm h0)
    have := Ioo_inter_eq_empty hT h0T ha.1 (hzpos.trans hza) hγa.symm
    have hm : z ∈ Ioo 0 a ∩ T := ⟨⟨hzpos, hza⟩, hz⟩
    rw [this] at hm
    exact hm
  have hend1 : ∀ z ∈ T, b < z → z = 1 := by
    intro z hz hbz
    by_contra h1
    have hzlt : z < 1 := lt_of_le_of_ne unitInterval.le_one' h1
    have := Ioo_inter_eq_empty hT hb.1 h1T (hbz.trans hzlt) hγb
    have hm : z ∈ Ioo b 1 ∩ T := ⟨⟨hbz, hzlt⟩, hz⟩
    rw [this] at hm
    exact hm
  have hab : a < b := by
    rcases lt_trichotomy a b with h | h | h
    · exact h
    · exact absurd (by rw [← hγa, h, hγb]) h01
    · exact absurd (by rw [← hγb, hend0 b hb.1 h]) h01.symm
  have hsb : s < b := by
    by_contra hc
    rw [not_lt] at hc
    have ht1 : t = 1 := hend1 t ht (lt_of_le_of_lt hc hst)
    rcases eq_or_lt_of_le hc with h | h
    · exact hne (by rw [← h, hγb, ht1])
    · have hs1 := hend1 s hs h
      rw [hs1, ht1] at hst
      exact lt_irrefl _ hst
  have hat : a < t := by
    by_contra hc
    rw [not_lt] at hc
    have hs0 : s = 0 := hend0 s hs (lt_of_lt_of_le hst hc)
    rcases eq_or_lt_of_le hc with h | h
    · exact hne (by rw [h, hγa, hs0])
    · have ht0 := hend0 t ht h
      rw [ht0, hs0] at hst
      exact lt_irrefl _ hst
  set s₁ := max s a with hs₁
  set t₁ := min t b with ht₁
  have hs₁T : s₁ ∈ T := by
    rcases max_choice s a with h | h <;> rw [hs₁, h]
    · exact hs
    · exact ha.1
  have ht₁T : t₁ ∈ T := by
    rcases min_choice t b with h | h <;> rw [ht₁, h]
    · exact ht
    · exact hb.1
  have hst₁ : s₁ < t₁ := max_lt (lt_min hst hsb) (lt_min hat hab)
  have hne₁ : γ s₁ ≠ γ t₁ := by
    intro h
    rcases max_choice s a with h1 | h1 <;> rcases min_choice t b with h2 | h2 <;>
      rw [hs₁, ht₁, h1, h2] at h
    · exact hne h
    · exact absurd (hbmin ⟨hs, h.trans hγb⟩) (not_le.mpr hsb)
    · exact absurd (hamax ⟨ht, (h.symm.trans hγa)⟩) (not_le.mpr hat)
    · exact h01 (by rw [← hγa, h, hγb])
  obtain ⟨z, hzT, h1, h2, hre, h3, h4⟩ := exists_between_of_ne hγ hT hs₁T ht₁T hst₁ hne₁
  have hza : a < z := lt_of_le_of_lt (le_max_right _ _) h1
  have hzb : z < b := lt_of_lt_of_le h2 (min_le_right _ _)
  have hz0 : γ z ≠ γ 0 := fun h => absurd (hamax ⟨hzT, h⟩) (not_le.mpr hza)
  have hz1 : γ z ≠ γ 1 := fun h => absurd (hbmin ⟨hzT, h⟩) (not_le.mpr hzb)
  refine ⟨z, ⟨hzT, hre, hz0, hz1⟩, lt_of_le_of_lt (le_max_left _ _) h1,
    lt_of_lt_of_le h2 (min_le_left _ _), ?_⟩
  intro h
  rcases max_choice s a with h' | h'
  · rw [hs₁, h'] at h3
    exact h3 h
  · -- Here `s ≤ a`, and `γ z = γ s` puts `a` strictly between `s` and `z` unless `s = a`.
    rw [hs₁, h'] at h3
    have hsa : s ≤ a := max_eq_right_iff.mp h'
    rcases eq_or_lt_of_le hsa with he | hl
    · exact h3 (by rw [h, he])
    · have := Ioo_inter_eq_empty hT hs hzT (hl.trans hza) h.symm
      have hm : a ∈ Ioo s z ∩ T := ⟨⟨hl, hza⟩, ha.1⟩
      rw [this] at hm
      exact hm

end Minimal

/-- **Arcs in paths.** A path with different ends in a Hausdorff space contains an injective path
with the same ends. -/
theorem exists_arc_of_path [T2Space X] {γ : 𝕀 → X} (hγ : Continuous γ) (h01 : γ 0 ≠ γ 1) :
    ∃ e : 𝕀 → X, Continuous e ∧ Function.Injective e ∧ e 0 = γ 0 ∧ e 1 = γ 1 ∧
      range e ⊆ range γ := by
  classical
  obtain ⟨T, hT⟩ := exists_minimal_admissible hγ
  have h0T := hT.1.2.1
  have h1T := hT.1.2.2.1
  have h01lt : (0 : 𝕀) < 1 := zero_lt_one
  have hZsub : coreSet T γ ⊆ T := fun _ h => h.1
  have hcore := fun {s t : 𝕀} => @exists_core_between X _ _ γ T hγ hT h01 s t
  have hdist : ∀ y ∈ coreSet T γ, ∀ y' ∈ coreSet T γ, y < y' → γ y ≠ γ y' := by
    intro y hy y' hy' hyy heq
    exact hy'.2.1 ⟨y, hy.1, hyy, Ioo_inter_eq_empty hT hy.1 hy'.1 hyy heq⟩
  obtain ⟨c, hcm, hcc, hcd, hc0, hc1, hcs, hcgap⟩ := exists_collapse (coreSet T γ)
    (by
      obtain ⟨z, hz, -⟩ := hcore h0T h1T h01lt h01
      exact ⟨z, hz⟩)
    (fun y hy y' hy' hyy => by
      obtain ⟨z, hz, h1, h2, -⟩ := hcore hy.1 hy'.1 hyy (hdist y hy y' hy' hyy)
      exact ⟨z, hz, h1, h2⟩)
    (fun y hy => by
      have hy1 : y < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hy.2.2.2 (by rw [h])
      obtain ⟨z, hz, h1, -⟩ := hcore hy.1 h1T hy1 hy.2.2.2
      exact ⟨z, hz, h1⟩)
    (fun y hy => by
      have hy0 : 0 < y := lt_of_le_of_ne unitInterval.nonneg' fun h => hy.2.2.1 (by rw [← h])
      obtain ⟨z, hz, -, h2, -⟩ := hcore h0T hy.1 hy0 (Ne.symm hy.2.2.1)
      exact ⟨z, hz, h2⟩)
  have hTcl : IsClosed T := hT.1.1
  have hcT : c '' T = univ := by
    have h1 : IsClosed (c '' T) := (hTcl.isCompact.image hcc).isClosed
    have h2 : closure (c '' coreSet T γ) ⊆ c '' T :=
      h1.closure_subset_iff.mpr (image_mono hZsub)
    rw [hcd.closure_eq] at h2
    exact univ_subset_iff.mp h2
  -- Equal images under `c` force equal values of `γ`.
  have hlt : ∀ s ∈ T, ∀ t ∈ T, s < t → γ s ≠ γ t → c s < c t := by
    intro s hs t ht hst hne
    obtain ⟨z, hz, h1, h2, h3⟩ := hcore hs ht hst hne
    obtain ⟨z', hz', h4, h5, -⟩ := hcore hs hz.1 h1 (Ne.symm h3)
    exact lt_of_le_of_lt (hcm h4.le) (lt_of_lt_of_le (hcs z' hz' z hz h5) (hcm h2.le))
  have hfib : ∀ s ∈ T, ∀ t ∈ T, c s = c t → γ s = γ t := by
    intro s hs t ht h
    rcases lt_trichotomy s t with hst | rfl | hst
    · by_contra hne
      exact absurd h (hlt s hs t ht hst hne).ne
    · rfl
    · by_contra hne
      exact absurd h (hlt t ht s hs hst (Ne.symm hne)).ne'
  let cT : T → 𝕀 := fun t => c t
  have hcTc : Continuous cT := hcc.comp continuous_subtype_val
  have hcTs : Function.Surjective cT := fun r => by
    have : r ∈ c '' T := hcT ▸ mem_univ r
    obtain ⟨t, ht, rfl⟩ := this
    exact ⟨⟨t, ht⟩, rfl⟩
  have : CompactSpace T := isCompact_iff_compactSpace.mp hTcl.isCompact
  have hq : IsQuotientMap cT := hcTc.isClosedMap.isQuotientMap hcTc hcTs
  let e : 𝕀 → X := fun r => γ (Classical.choose (hcTs r)).1
  have hee : ∀ t : T, e (cT t) = γ t := fun t =>
    hfib _ (Classical.choose (hcTs (cT t))).2 _ t.2 (Classical.choose_spec (hcTs (cT t)))
  have hecont : Continuous e := by
    rw [hq.continuous_iff]
    have : e ∘ cT = fun t : T => γ t := funext hee
    rw [this]
    exact hγ.comp continuous_subtype_val
  refine ⟨e, hecont, ?_, ?_, ?_, ?_⟩
  · intro r r' h
    obtain ⟨s, rfl⟩ := hcTs r
    obtain ⟨t, rfl⟩ := hcTs r'
    rw [hee, hee] at h
    have key : ∀ s t : 𝕀, s ∈ T → t ∈ T → s < t → γ s = γ t → c s = c t := by
      intro s t hs ht hst heq
      refine hcgap s t hst ?_
      have hgap := Ioo_inter_eq_empty hT hs ht hst heq
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨hz1, hz2⟩
      rcases eq_or_lt_of_le hz1.2 with he | hl
      · exact (he ▸ hz2).2.1 ⟨s, hs, hst, hgap⟩
      · have : z ∈ Ioo s t ∩ T := ⟨⟨hz1.1, hl⟩, hz2.1⟩
        rw [hgap] at this
        exact this
    rcases lt_trichotomy s.1 t.1 with hst | hst | hst
    · exact key _ _ s.2 t.2 hst h
    · exact congrArg cT (Subtype.ext hst)
    · exact (key _ _ t.2 s.2 hst h.symm).symm
  · have := hee ⟨0, h0T⟩
    simpa [cT, hc0] using this
  · have := hee ⟨1, h1T⟩
    simpa [cT, hc1] using this
  · rintro _ ⟨r, rfl⟩
    exact ⟨_, rfl⟩

end GraphMinor.Surface
