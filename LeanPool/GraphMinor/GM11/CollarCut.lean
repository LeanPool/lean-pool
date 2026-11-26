/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PerimeterCount

/-!
# Cutting a collar along a line

Graph Minors XI, proof of (8.7), takes a line `L` outside `X` between two points of `bd(X)`, and
says that
`Σ − (X ∪ L)` has at most two components `Δ₁, Δ₂` and that the perimeter walk splits at the ends of
`L` into
two walks, one on the boundary of each.

We show the part of this that the proof needs, by means of a collar `h` of `X`. The ends of `L` tend
to two
points of the circle (`exists_end_limit`), the two arcs of the circle between them lead to two
components
(`arc_germ`), each arc lies in the closure of its component, and each component of `Σ − (X ∪ L)`
with a
limit point in `X − L` is one of the two (`exists_cut`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Filter

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {h : C(Circle × I, S)}

/-- The inverse of a collar on the part with positive height. -/
noncomputable def collarInv (h : C(Circle × I, S)) : S → Circle × I :=
  Function.invFunOn h {p | 0 < p.2}

omit [T2Space S] in
theorem collarInv_apply (hinj : InjOn h {p | 0 < p.2}) {p : Circle × I} (hp : 0 < p.2) :
    collarInv h (h p) = p :=
  hinj.leftInvOn_invFunOn hp

omit [T2Space S] in
theorem apply_collarInv {y : S} (hy : y ∈ h '' {p | 0 < p.2}) :
    h (collarInv h y) = y ∧ 0 < (collarInv h y).2 :=
  ⟨Function.invFunOn_eq hy, Function.invFunOn_mem hy⟩

/-- Each neighbourhood of `0` in the unit interval contains an initial piece. -/
theorem exists_small {V : Set I} (hV : V ∈ 𝓝 (0 : I)) : ∃ ε : I, 0 < ε ∧ ∀ t : I, t ≤ ε → t ∈ V
  := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨⟨min (δ / 2) 1, by positivity, min_le_right _ _⟩, ?_, fun t ht => hball ?_⟩
  · change (0 : ℝ) < min (δ / 2) 1
    positivity
  · have h₁ : (t : ℝ) ≤ min (δ / 2) 1 := ht
    have h₂ : (t : ℝ) ≤ δ / 2 := h₁.trans (min_le_left _ _)
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    change |(t : ℝ) - 0| < δ
    rw [sub_zero, abs_of_nonneg t.2.1]
    linarith

variable {X : Set S}

/-- The inverse of a collar is continuous on the part with positive height. -/
theorem collarInv_continuousWithinAt (hinj : InjOn h {p | 0 < p.2})
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X) {y : S}
    (hy : y ∈ h '' {p | 0 < p.2}) : ContinuousWithinAt (collarInv h) (h '' {p | 0 < p.2}) y := by
  obtain ⟨p₀, hp₀, rfl⟩ := hy
  rw [ContinuousWithinAt, collarInv_apply hinj hp₀]
  have hp₀' : (0 : I) < p₀.2 := hp₀
  have hp₀r : (0 : ℝ) < p₀.2 := hp₀'
  let ε : I := ⟨(p₀.2 : ℝ) / 2, by positivity, by have := p₀.2.2.2; linarith⟩
  have hε : ε < p₀.2 := by
    change (p₀.2 : ℝ) / 2 < p₀.2
    linarith
  have hε0 : 0 < ε := by
    change (0 : ℝ) < (p₀.2 : ℝ) / 2
    linarith
  rw [tendsto_nhds]
  intro N hN hp₀N
  have hlow : IsClosed (h '' {p | p.2 ≤ ε}) :=
    ((isClosed_le continuous_snd continuous_const).isCompact.image h.continuous).isClosed
  have hhigh : IsClosed (h '' ({p | ε ≤ p.2} ∩ Nᶜ)) :=
    (((isClosed_le continuous_const continuous_snd).inter hN.isClosed_compl).isCompact.image
      h.continuous).isClosed
  have hpos : ∀ q : Circle × I, h q = h p₀ → 0 < q.2 := by
    intro q hqe
    by_contra hq0
    have hq : q = (q.1, 0) := Prod.ext rfl (le_antisymm (not_lt.mp hq0) (unitInterval.nonneg _))
    refine hoff p₀ hp₀ ?_
    rw [← hqe, hq]
    exact hbot q.1
  have hnot₁ : h p₀ ∉ h '' {p | p.2 ≤ ε} := by
    rintro ⟨q, hq, hqe⟩
    have hq' : q.2 ≤ ε := hq
    have := hinj (hpos q hqe) hp₀ hqe
    rw [this] at hq'
    exact not_le.mpr hε hq'
  have hnot₂ : h p₀ ∉ h '' ({p | ε ≤ p.2} ∩ Nᶜ) := by
    rintro ⟨q, hq, hqe⟩
    have := hinj (hpos q hqe) hp₀ hqe
    exact hq.2 (this ▸ hp₀N)
  refine mem_nhdsWithin.mpr ⟨(h '' {p | p.2 ≤ ε})ᶜ ∩ (h '' ({p | ε ≤ p.2} ∩ Nᶜ))ᶜ,
    hlow.isOpen_compl.inter hhigh.isOpen_compl, ⟨hnot₁, hnot₂⟩, ?_⟩
  rintro y ⟨⟨hy₁, hy₂⟩, hyΩ⟩
  obtain ⟨hgy, hg0⟩ := apply_collarInv hyΩ
  by_contra hn
  have hle : ε ≤ (collarInv h y).2 := by
    by_contra hlt
    exact hy₁ ⟨_, (not_le.mp hlt).le, hgy⟩
  exact hy₂ ⟨_, ⟨hle, hn⟩, hgy⟩

variable {ψ : I → S}

/-- The end of a path that leaves `X` tends to one point of the circle of the collar. -/
theorem exists_end_limit (hinj : InjOn h {p | 0 < p.2})
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X)
    (hop : IsOpen (X ∪ h '' {p | p.2 < 1})) (hψ : Continuous ψ) (hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X)
    (h0 : ψ 0 ∈ X) (hfin : {z : Circle | h (z, 0) = ψ 0}.Finite) :
    ∃ z, h (z, 0) = ψ 0 ∧ ∀ N ∈ 𝓝 ((z, 0) : Circle × I), ∃ s : I, 0 < s ∧
      ∀ s' ∈ Ioo (0 : I) s, collarInv h (ψ s') ∈ N := by
  classical
  let f : I → Circle × I := fun s => collarInv h (ψ s)
  let Ω := h '' {p | 0 < p.2}
  let F : Filter I := 𝓝[>] (0 : I)
  have hFne : F.NeBot := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one' I⟩
  -- Near `0` the path is in the collar.
  obtain ⟨s₀, hs₀, hsmall⟩ : ∃ s₀ : I, 0 < s₀ ∧ ∀ s, s ≤ s₀ → ψ s ∈ X ∪ h '' {p | p.2 < 1} := by
    refine exists_small ((hop.preimage hψ).mem_nhds (Or.inl h0))
  have hs₁ : ∀ s ∈ Ioo (0 : I) 1, s ≤ s₀ → ψ s ∈ Ω := by
    intro s hs hle
    rcases hsmall s hle with hx | ⟨p, hp, hpe⟩
    · exact (hψX s hs hx).elim
    · refine ⟨p, ?_, hpe⟩
      by_contra hn
      have hq : p = (p.1, 0) := Prod.ext rfl (le_antisymm (not_lt.mp hn) (unitInterval.nonneg _))
      refine hψX s hs ?_
      rw [← hpe, hq]
      exact hbot p.1
  have hs₀1 : ∃ s₁ : I, 0 < s₁ ∧ s₁ ≤ s₀ ∧ s₁ ≤ 1 := ⟨s₀, hs₀, le_rfl, unitInterval.le_one _⟩
  have hev : ∀ s : I, 0 < s → Ioo (0 : I) s ∈ F := fun s hs => Ioo_mem_nhdsGT hs
  have hmemΩ : ∀ s' ∈ Ioo (0 : I) s₀, ψ s' ∈ Ω := fun s' hs' =>
    hs₁ s' ⟨hs'.1, hs'.2.trans_le (unitInterval.le_one _)⟩ hs'.2.le
  have hfc : ContinuousOn f (Ioo (0 : I) s₀) := by
    intro s hs
    exact (collarInv_continuousWithinAt hinj hoff hbot (hmemΩ s hs)).comp hψ.continuousWithinAt
      hmemΩ
  have hψt : Tendsto ψ F (𝓝 (ψ 0)) := (hψ.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhf : ∀ᶠ s in F, h (f s) = ψ s := by
    filter_upwards [hev s₀ hs₀] with s hs
    exact (apply_collarInv (hmemΩ s hs)).1
  -- All cluster points lie over `ψ 0` with height zero.
  have hcl : ∀ p, MapClusterPt p F f → h p = ψ 0 ∧ p.2 = 0 := by
    intro p hp
    have hmap : MapClusterPt (h p) F (h ∘ f) := hp.continuousAt_comp h.continuous.continuousAt
    have heq : h p = ψ 0 := by
      have h₁ : MapClusterPt (h p) F ψ := by
        rw [mapClusterPt_iff_frequently] at hmap ⊢
        intro s hs
        exact (hmap s hs).mp (hhf.mono fun x hx hm => by
          change h (f x) ∈ s at hm
          rwa [hx] at hm)
      exact eq_of_nhds_neBot (ClusterPt.mono h₁ hψt)
    refine ⟨heq, ?_⟩
    by_contra hne
    exact hoff p (unitInterval.pos_iff_ne_zero.mpr hne) (heq ▸ h0)
  let T : Set (Circle × I) := (fun z => (z, (0 : I))) '' {z | h (z, 0) = ψ 0}
  have hT : T.Finite := hfin.image _
  have hclT : ∀ p, MapClusterPt p F f → p ∈ T := fun p hp => by
    obtain ⟨h₁, h₂⟩ := hcl p hp
    exact ⟨p.1, by simpa [← h₂] using h₁, Prod.ext rfl h₂.symm⟩
  obtain ⟨p, hp⟩ : ∃ p, MapClusterPt p F f := exists_clusterPt_of_compactSpace (map f F)
  have huniq : ∀ q, MapClusterPt q F f → q = p := by
    intro q hq
    by_contra hne
    have hT' : IsClosed (T \ {p}) := (hT.subset sdiff_subset).isClosed
    obtain ⟨C₁, hC₁, hC₁c, hC₁s⟩ := exists_mem_nhds_isClosed_subset
      (hT'.isOpen_compl.mem_nhds (fun h => h.2 rfl))
    have hfrc : IsCompact (C₁ \ interior C₁) := (hC₁c.sdiff isOpen_interior).isCompact
    have hfr : ∀ᶠ s in F, f s ∉ C₁ \ interior C₁ := by
      refine hfrc.induction_on (p := fun A => ∀ᶠ s in F, f s ∉ A) (by simp) ?_ ?_ ?_
      · intro A B hAB hB
        exact hB.mono fun s hs hA => hs (hAB hA)
      · intro A B hA hB
        exact (hA.and hB).mono fun s hs hm => hm.elim hs.1 hs.2
      · intro x hx
        have hnc : ¬ MapClusterPt x F f := by
          intro hc
          have hxT := hclT x hc
          have hxp : x = p := by
            by_contra hxp
            exact hC₁s hx.1 ⟨hxT, hxp⟩
          exact hx.2 (hxp ▸ mem_interior_iff_mem_nhds.mpr hC₁)
        rw [mapClusterPt_iff_frequently] at hnc
        push Not at hnc
        obtain ⟨A, hA, hev'⟩ := hnc
        exact ⟨A, mem_nhdsWithin_of_mem_nhds hA, hev'⟩
    obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (zero_lt_one' I)).mp hfr
    let s₂ : I := min u s₀
    have hs₂ : 0 < s₂ := lt_min hu hs₀
    have hsub : Ioo (0 : I) s₂ ⊆ Ioo (0 : I) s₀ := fun x hx => ⟨hx.1, hx.2.trans_le
      (min_le_right _ _)⟩
    have hpc : IsPreconnected (f '' Ioo (0 : I) s₂) :=
      isPreconnected_Ioo.image f (hfc.mono hsub)
    have hcover : f '' Ioo (0 : I) s₂ ⊆ interior C₁ ∪ C₁ᶜ := by
      rintro _ ⟨x, hx, rfl⟩
      by_cases hC : f x ∈ C₁
      · by_contra hn
        exact hus ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩ ⟨hC, fun hi => hn (Or.inl hi)⟩
      · exact Or.inr hC
    have hdis : Disjoint (interior C₁) C₁ᶜ :=
      disjoint_left.mpr fun x hx hc => hc (interior_subset hx)
    have hev₂ : ∀ᶠ s in F, s ∈ Ioo (0 : I) s₂ := hev s₂ hs₂
    rcases hpc.subset_or_subset isOpen_interior hC₁c.isOpen_compl hdis hcover with hin | hin
    · have hqC : q ∉ C₁ := fun hqc => hC₁s hqc ⟨hclT q hq, hne⟩
      obtain ⟨s, hs₁, hs₂'⟩ := (hq.frequently (hC₁c.isOpen_compl.mem_nhds hqC)).and_eventually hev₂
        |>.exists
      exact hs₁ (interior_subset (hin ⟨s, hs₂', rfl⟩))
    · obtain ⟨s, hs₁, hs₂'⟩ := (hp.frequently hC₁).and_eventually hev₂ |>.exists
      exact hin ⟨s, hs₂', rfl⟩ hs₁
  have hle : map f F ≤ 𝓝 p := isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ hx
    => huniq x hx
  obtain ⟨hp₁, hp₂⟩ := hcl p hp
  have hpe : ((p.1, 0) : Circle × I) = p := Prod.ext rfl hp₂.symm
  refine ⟨p.1, by rw [hpe]; exact hp₁, fun N hN => ?_⟩
  rw [hpe] at hN
  obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (zero_lt_one' I)).mp (hle hN)
  exact ⟨u, hu, fun s' hs' => hus hs'⟩

variable {z₀ z₁ : Circle}

/-- Away from the two ends of the line, a low enough part of the collar misses the line. This is the
step
where the limits at the two ends are used. -/
theorem exists_tube (hinj : InjOn h {p | 0 < p.2}) (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X)
    (hbot : ∀ z, h (z, 0) ∈ X) (hψ : Continuous ψ) (hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X)
    (h0 : ψ 0 ∈ X) (h1 : ψ 1 ∈ X)
    (hl₀ : ∀ N ∈ 𝓝 ((z₀, 0) : Circle × I), ∃ s : I, 0 < s ∧ ∀ s' ∈ Ioo (0 : I) s, collarInv h
      (ψ s') ∈ N)
    (hl₁ : ∀ N ∈ 𝓝 ((z₁, 0) : Circle × I), ∃ s : I, s < 1 ∧ ∀ s' ∈ Ioo s (1 : I), collarInv h
      (ψ s') ∈ N)
    {K : Set Circle} (hK : IsCompact K) (hK₀ : z₀ ∉ K) (hK₁ : z₁ ∉ K) :
    ∃ ε : I, 0 < ε ∧ ∀ z ∈ K, ∀ t : I, 0 < t → t ≤ ε → h (z, t) ∉ range ψ := by
  let B : Set (Circle × I) := {p | 0 < p.2 ∧ h p ∈ range ψ}
  have hnot : ∀ z ∈ K, (z, (0 : I)) ∉ closure B := by
    intro z hz hcl
    obtain ⟨x, hxB, hxt⟩ := mem_closure_iff_seq_limit.mp hcl
    have hx : ∀ n, ∃ s : I, ψ s = h (x n) := fun n => (hxB n).2
    choose s hs using hx
    obtain ⟨s', hs', φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := s) fun _ => mem_univ _
    have hsI : ∀ n, s n ∈ Ioo (0 : I) 1 := by
      intro n
      have hoffn := hoff (x n) (hxB n).1
      refine ⟨unitInterval.pos_iff_ne_zero.mpr fun h' => hoffn ?_,
        unitInterval.lt_one_iff_ne_one.mpr fun h' => hoffn ?_⟩
      · rw [← hs n, h']
        exact h0
      · rw [← hs n, h']
        exact h1
    have hg : ∀ n, collarInv h (ψ (s n)) = x n := fun n => by
      rw [hs n]
      exact collarInv_apply hinj (hxB n).1
    have hxφ : Tendsto (x ∘ φ) atTop (𝓝 (z, (0 : I))) := hxt.comp hφ.tendsto_atTop
    have hval : ψ s' = h (z, 0) := by
      have h₁ : Tendsto (fun n => ψ (s (φ n))) atTop (𝓝 (ψ s')) := (hψ.tendsto s').comp hlim
      have h₂ : Tendsto (fun n => h (x (φ n))) atTop (𝓝 (h (z, 0))) :=
        (h.continuous.tendsto _).comp hxφ
      refine tendsto_nhds_unique h₁ (h₂.congr fun n => (hs (φ n)).symm)
    have hsend : s' = 0 ∨ s' = 1 := by
      by_contra hn
      push Not at hn
      refine hψX s' ⟨unitInterval.pos_iff_ne_zero.mpr hn.1, unitInterval.lt_one_iff_ne_one.mpr
        hn.2⟩ ?_
      rw [hval]
      exact hbot z
    rcases hsend with rfl | rfl
    · have hne : ((z₀, 0) : Circle × I) ≠ (z, 0) := fun he =>
        hK₀ (by rw [show z₀ = z from congrArg Prod.fst he]; exact hz)
      obtain ⟨N, N', hN, hN', hdis⟩ := t2_separation_nhds hne
      obtain ⟨u, hu, hus⟩ := hl₀ N hN
      have hev₁ : ∀ᶠ n in atTop, s (φ n) ∈ Iio u := hlim (Iio_mem_nhds hu)
      have hev₂ : ∀ᶠ n in atTop, x (φ n) ∈ N' := hxφ hN'
      obtain ⟨n, hn₁, hn₂⟩ := (hev₁.and hev₂).exists
      have := hus (s (φ n)) ⟨(hsI _).1, hn₁⟩
      rw [hg] at this
      exact disjoint_left.mp hdis this hn₂
    · have hne : ((z₁, 0) : Circle × I) ≠ (z, 0) := fun he =>
        hK₁ (by rw [show z₁ = z from congrArg Prod.fst he]; exact hz)
      obtain ⟨N, N', hN, hN', hdis⟩ := t2_separation_nhds hne
      obtain ⟨u, hu, hus⟩ := hl₁ N hN
      have hev₁ : ∀ᶠ n in atTop, s (φ n) ∈ Ioi u := hlim (Ioi_mem_nhds hu)
      have hev₂ : ∀ᶠ n in atTop, x (φ n) ∈ N' := hxφ hN'
      obtain ⟨n, hn₁, hn₂⟩ := (hev₁.and hev₂).exists
      have := hus (s (φ n)) ⟨hn₁, (hsI _).2⟩
      rw [hg] at this
      exact disjoint_left.mp hdis this hn₂
  have hsub : K ×ˢ ({0} : Set I) ⊆ (closure B)ᶜ := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    obtain rfl : t = 0 := ht
    exact hnot z hz
  obtain ⟨A, V, hA, hV, hKA, h0V, hAV⟩ := generalized_tube_lemma hK isCompact_singleton
    isClosed_closure.isOpen_compl hsub
  obtain ⟨ε, hε, hsm⟩ := exists_small (hV.mem_nhds (h0V rfl))
  refine ⟨ε, hε, fun z hz t ht hle hm => ?_⟩
  exact hAV (mk_mem_prod (hKA hz) (hsm t hle)) (subset_closure ⟨ht, hm⟩)

/-- The point `e^{2π i t}` of the circle. -/
noncomputable def circlePt (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

theorem continuous_circlePt : Continuous circlePt :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

theorem isOpenMap_circlePt : IsOpenMap circlePt :=
  isLocalHomeomorph_circleExp.isOpenMap.comp
    (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity)).isOpenMap

/-- An arc of the circle away from the ends of the line leads to one component of `Σ − (X ∪ L)`. -/
theorem arc_germ (hinj : InjOn h {p | 0 < p.2}) (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X)
    (hbot : ∀ z, h (z, 0) ∈ X) (hψ : Continuous ψ) (hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X)
    (h0 : ψ 0 ∈ X) (h1 : ψ 1 ∈ X)
    (hl₀ : ∀ N ∈ 𝓝 ((z₀, 0) : Circle × I), ∃ s : I, 0 < s ∧ ∀ s' ∈ Ioo (0 : I) s, collarInv h
      (ψ s') ∈ N)
    (hl₁ : ∀ N ∈ 𝓝 ((z₁, 0) : Circle × I), ∃ s : I, s < 1 ∧ ∀ s' ∈ Ioo s (1 : I), collarInv h
      (ψ s') ∈ N)
    {α β : ℝ} (hαβ : α < β) (hρ : ∀ t ∈ Ioo α β, circlePt t ≠ z₀ ∧ circlePt t ≠ z₁) :
    ∃ y ∈ (X ∪ range ψ)ᶜ, ∀ t ∈ Ioo α β, ∀ᶠ p in 𝓝 ((circlePt t, 0) : Circle × I), 0 < p.2 →
      h p ∈ connectedComponentIn (X ∪ range ψ)ᶜ y := by
  have htube : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo α β → ∃ ε : I, 0 < ε
    ∧ ∀ z ∈ circlePt '' K, ∀ t : I, 0 < t →
      t ≤ ε → h (z, t) ∉ range ψ := by
    intro K hK hsub
    refine exists_tube hinj hoff hbot hψ hψX h0 h1 hl₀ hl₁ (hK.image continuous_circlePt) ?_ ?_
    · rintro ⟨t, ht, he⟩
      exact (hρ t (hsub ht)).1 he
    · rintro ⟨t, ht, he⟩
      exact (hρ t (hsub ht)).2 he
  let Y := (X ∪ range ψ)ᶜ
  let τ := (α + β) / 2
  have hτ : τ ∈ Ioo α β := ⟨by simp only [τ]; linarith, by simp only [τ]; linarith⟩
  obtain ⟨ε₀, hε₀, hsm₀⟩ := htube {τ} isCompact_singleton (singleton_subset_iff.mpr hτ)
  have hmemY : ∀ z ∈ circlePt '' Ioo α β, ∀ (K : Set Circle) (ε : I), z ∈ K →
      (∀ z ∈ K, ∀ t : I, 0 < t → t ≤ ε → h (z, t) ∉ range ψ) →
      ∀ t : I, 0 < t → t ≤ ε → h (z, t) ∈ Y := by
    intro z _ K ε hzK hK t ht hle hn
    rcases hn with hn | hn
    · exact hoff _ ht hn
    · exact hK z hzK t ht hle hn
  let y := h (circlePt τ, ε₀)
  have hyY : y ∈ Y := hmemY _ ⟨τ, hτ, rfl⟩ (circlePt '' {τ}) ε₀ ⟨τ, rfl, rfl⟩ hsm₀ ε₀ hε₀ le_rfl
  refine ⟨y, hyY, fun t ht => ?_⟩
  let a' := (α + min t τ) / 2
  let b' := (β + max t τ) / 2
  have ha' : α < a' ∧ a' < min t τ := by
    have := lt_min ht.1 hτ.1
    constructor <;> simp only [a'] <;> linarith
  have hb' : max t τ < b' ∧ b' < β := by
    have := max_lt ht.2 hτ.2
    constructor <;> simp only [b'] <;> linarith
  have hsubI : Icc a' b' ⊆ Ioo α β := fun x hx => ⟨ha'.1.trans_le hx.1, hx.2.trans_lt hb'.2⟩
  obtain ⟨ε, hε, hsm⟩ := htube (Icc a' b') isCompact_Icc hsubI
  -- The low part of the collar over `[a', b']`, with the segment up to `y`.
  let m : I := min ε ε₀
  have hm : 0 < m := lt_min hε hε₀
  let G₀ : Set S := (fun u : I => h (circlePt τ, u)) '' Icc m ε₀
  let G : Set S := (fun q : ℝ × I => h (circlePt q.1, q.2)) '' (Icc a' b' ×ˢ Ioc 0 ε)
  have hcG : Continuous fun q : ℝ × I => h (circlePt q.1, q.2) := h.continuous.comp
    ((continuous_circlePt.comp continuous_fst).prodMk continuous_snd)
  have hG₀p : IsPreconnected G₀ := isPreconnected_Icc.image _ (h.continuous.comp
    (continuous_const.prodMk continuous_id)).continuousOn
  have hGp : IsPreconnected G := (isPreconnected_Icc.prod isPreconnected_Ioc).image _
    hcG.continuousOn
  have hτI : τ ∈ Icc a' b' := ⟨(ha'.2.le.trans (min_le_right _ _)), (le_max_right _ _).trans
    hb'.1.le⟩
  have htI : t ∈ Icc a' b' := ⟨(ha'.2.le.trans (min_le_left _ _)), (le_max_left _ _).trans hb'.1.le⟩
  have hjoin : (G₀ ∩ G).Nonempty :=
    ⟨h (circlePt τ, m), ⟨m, ⟨le_rfl, min_le_right _ _⟩, rfl⟩, ⟨(τ, m), ⟨hτI, hm, min_le_left _ _⟩,
      rfl⟩⟩
  have hU := hG₀p.union' hjoin hGp
  have hUY : G₀ ∪ G ⊆ Y := by
    rintro _ (⟨u, hu, rfl⟩ | ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩)
    · exact hmemY _ ⟨τ, hτ, rfl⟩ (circlePt '' {τ}) ε₀ ⟨τ, rfl, rfl⟩ hsm₀ u (hm.trans_le hu.1) hu.2
    · exact hmemY _ ⟨u, hsubI hu, rfl⟩ (circlePt '' Icc a' b') ε ⟨u, hu, rfl⟩ hsm v hv.1 hv.2
  have hyG : y ∈ G₀ ∪ G := Or.inl ⟨ε₀, ⟨min_le_right _ _, le_rfl⟩, rfl⟩
  have hcomp := hU.subset_connectedComponentIn hyG hUY
  have hN₁ : circlePt '' Ioo a' b' ∈ 𝓝 (circlePt t) :=
    (isOpenMap_circlePt _ isOpen_Ioo).mem_nhds ⟨t, ⟨ha'.2.trans_le (min_le_left _ _),
      (le_max_left _ _).trans_lt hb'.1⟩, rfl⟩
  have hN₂ : Iic ε ∈ 𝓝 (0 : I) := by
    exact Iic_mem_nhds hε
  filter_upwards [prod_mem_nhds hN₁ hN₂] with p hp hpos
  obtain ⟨⟨u, hu, hue⟩, hv⟩ := hp
  refine hcomp (Or.inr ⟨(u, p.2), ⟨⟨hu.1.le, hu.2.le⟩, hpos, hv⟩, ?_⟩)
  change h (circlePt u, p.2) = h p
  rw [hue]

/-- Each point of the circle is `e^{2π i t}` with `lo ≤ t < lo + 1`. -/
theorem exists_circlePt_time (lo : ℝ) (z : Circle) : ∃ t ∈ Ico lo (lo + 1), circlePt t = z := by
  obtain ⟨t, ht, hz⟩ := exists_collar_time z
  obtain ⟨t', ht', hz'⟩ := exists_collar_time ((circlePt lo)⁻¹ * z)
  refine ⟨lo + t', ⟨by linarith [ht'.1], by linarith [ht'.2]⟩, ?_⟩
  have h₁ : circlePt (lo + t') = circlePt lo * circlePt t' := by
    simp only [circlePt, mul_add, Circle.exp_add]
  rw [h₁]
  change circlePt lo * circlePt t' = z
  have h₂ : circlePt t' = (circlePt lo)⁻¹ * z := hz'.symm
  rw [h₂, mul_inv_cancel_left]

/-- `e^{2π i t}` is injective on a half-open interval of length one. -/
theorem circlePt_injOn {lo : ℝ} {s t : ℝ} (hs : s ∈ Ico lo (lo + 1)) (ht : t ∈ Ico lo (lo + 1))
    (h : circlePt s = circlePt t) : s = t := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hpi := Real.pi_pos
  have hm' : s = t + m := by
    have : 2 * Real.pi * s = 2 * Real.pi * (t + m) := by rw [hm]; ring
    exact mul_left_cancel₀ (by positivity) this
  have hlt₁ : (m : ℝ) < 1 := by linarith [hs.2, ht.1]
  have hlt₂ : (-1 : ℝ) < m := by linarith [hs.1, ht.2]
  have h₁ : m < 1 := by exact_mod_cast hlt₁
  have h₂ : -1 < m := by exact_mod_cast hlt₂
  obtain rfl : m = 0 := by omega
  simpa using hm'

/-- **Cutting along a line.** Let `ψ` be a path outside `X` with its two ends on `X`, and suppose
the ends
tend to the points `e^{2π i lo}` and `e^{2π i hi}` of the circle of the collar `h`. Then the two
arcs between
those points lead to components `D₁, D₂` of `Σ − (X ∪ L)`. Each arc lies in the closure of its
component, and
each component of `Σ − (X ∪ L)` with a limit point in `X − L` is `D₁` or `D₂`. -/
theorem exists_cut (hinj : InjOn h {p | 0 < p.2}) (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X)
    (hbot : ∀ z, h (z, 0) ∈ X) (hop : IsOpen (X ∪ h '' {p | p.2 < 1})) (hψ : Continuous ψ)
    (hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X) (h0 : ψ 0 ∈ X) (h1 : ψ 1 ∈ X)
    (hl₀ : ∀ N ∈ 𝓝 ((z₀, 0) : Circle × I), ∃ s : I, 0 < s ∧ ∀ s' ∈ Ioo (0 : I) s, collarInv h
      (ψ s') ∈ N)
    (hl₁ : ∀ N ∈ 𝓝 ((z₁, 0) : Circle × I), ∃ s : I, s < 1 ∧ ∀ s' ∈ Ioo s (1 : I), collarInv h
      (ψ s') ∈ N)
    (hz₀ : h (z₀, 0) ∈ range ψ) (hz₁ : h (z₁, 0) ∈ range ψ)
    {lo hi : ℝ} (hlo : lo < hi) (hhi : hi < lo + 1)
    (hends : (z₀ = circlePt lo ∧ z₁ = circlePt hi) ∨ (z₀ = circlePt hi ∧ z₁ = circlePt lo)) :
    ∃ y₁ ∈ (X ∪ range ψ)ᶜ, ∃ y₂ ∈ (X ∪ range ψ)ᶜ,
      (∀ t ∈ Icc lo hi, h (circlePt t, 0) ∈ closure (connectedComponentIn (X ∪ range ψ)ᶜ y₁)) ∧
      (∀ t ∈ Icc hi (lo + 1), h (circlePt t, 0) ∈ closure (connectedComponentIn (X ∪ range ψ)ᶜ y₂))
        ∧
      ∀ y ∈ (X ∪ range ψ)ᶜ, ∀ x ∈ closure (connectedComponentIn (X ∪ range ψ)ᶜ y), x ∈ X
        → x ∉ range ψ →
        connectedComponentIn (X ∪ range ψ)ᶜ y = connectedComponentIn (X ∪ range ψ)ᶜ y₁ ∨
        connectedComponentIn (X ∪ range ψ)ᶜ y = connectedComponentIn (X ∪ range ψ)ᶜ y₂ := by
  have harc : ∀ {α β : ℝ}, α < β → lo ≤ α → β ≤ lo + 1 → (α = lo ∧ β = hi ∨ α = hi ∧ β = lo + 1) →
      ∀ t ∈ Ioo α β, circlePt t ≠ z₀ ∧ circlePt t ≠ z₁ := by
    intro α β _ hα hβ hcase t ht
    have htI : t ∈ Ico lo (lo + 1) := ⟨hα.trans ht.1.le, ht.2.trans_le hβ⟩
    have hne : circlePt t ≠ circlePt lo ∧ circlePt t ≠ circlePt hi := by
      constructor
      · intro he
        have := circlePt_injOn htI ⟨le_rfl, by linarith⟩ he
        rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> linarith [ht.1]
      · intro he
        have := circlePt_injOn htI ⟨hlo.le, hhi⟩ he
        rcases hcase with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> linarith [ht.1, ht.2]
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact hne.symm
  obtain ⟨y₁, hy₁, hg₁⟩ := arc_germ hinj hoff hbot hψ hψX h0 h1 hl₀ hl₁ hlo
    (harc hlo le_rfl (by linarith) (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨y₂, hy₂, hg₂⟩ := arc_germ hinj hoff hbot hψ hψX h0 h1 hl₀ hl₁ hhi
    (harc hhi hlo.le le_rfl (Or.inr ⟨rfl, rfl⟩))
  have hclosure : ∀ {α β : ℝ} {D : Set S}, α < β → (∀ t ∈ Ioo α β, ∀ᶠ p in 𝓝
    ((circlePt t, 0) : Circle × I),
      0 < p.2 → h p ∈ D) → ∀ t ∈ Icc α β, h (circlePt t, 0) ∈ closure D := by
    intro α β D hαβ hg t ht
    have hsub : Ioo α β ⊆ (fun t => h (circlePt t, 0)) ⁻¹' closure D := by
      intro t ht
      have hev := hg t ht
      have hc : ContinuousAt (fun u : I => ((circlePt t, u) : Circle × I)) 0 := by fun_prop
      have hev' := hc.eventually hev
      have hF : (𝓝[>] (0 : I)).NeBot := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one' I⟩
      have hev₂ : ∀ᶠ u in 𝓝[>] (0 : I), h (circlePt t, u) ∈ D := by
        filter_upwards [hev'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu₀
        exact hu hu₀
      have hlim : Tendsto (fun u : I => h (circlePt t, u)) (𝓝[>] (0 : I)) (𝓝 (h (circlePt t, 0))) :=
        ((h.continuous.comp (continuous_const.prodMk continuous_id)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      exact mem_closure_of_tendsto hlim hev₂
    have hcl : IsClosed ((fun t => h (circlePt t, 0)) ⁻¹' closure D) :=
      isClosed_closure.preimage (h.continuous.comp (continuous_circlePt.prodMk continuous_const))
    have := closure_minimal hsub hcl
    rw [closure_Ioo hαβ.ne] at this
    exact this ht
  refine ⟨y₁, hy₁, y₂, hy₂, hclosure hlo hg₁, hclosure hhi hg₂, ?_⟩
  intro y hy x hx hxX hxL
  let Q := connectedComponentIn (X ∪ range ψ)ᶜ y
  have hQY : Q ⊆ (X ∪ range ψ)ᶜ := connectedComponentIn_subset _ _
  let Ω := h '' {p | 0 < p.2}
  have hne : (𝓝[Q] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hev₁ : ∀ᶠ q in 𝓝[Q] x, q ∈ Ω := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hop.mem_nhds (Or.inl hxX)), self_mem_nhdsWithin]
      with q hq hqQ
    rcases hq with hq | ⟨p, hp, hpe⟩
    · exact ((hQY hqQ) (Or.inl hq)).elim
    · refine ⟨p, ?_, hpe⟩
      by_contra hn
      have hq0 : p = (p.1, 0) := Prod.ext rfl (le_antisymm (not_lt.mp hn) (unitInterval.nonneg _))
      refine hQY hqQ (Or.inl ?_)
      rw [← hpe, hq0]
      exact hbot p.1
  obtain ⟨p, hp⟩ : ∃ p, MapClusterPt p (𝓝[Q] x) (collarInv h) :=
    exists_clusterPt_of_compactSpace (map (collarInv h) (𝓝[Q] x))
  have hpx : h p = x := by
    have hmap : MapClusterPt (h p) (𝓝[Q] x) (h ∘ collarInv h) :=
      hp.continuousAt_comp h.continuous.continuousAt
    have h₁ : MapClusterPt (h p) (𝓝[Q] x) id := by
      rw [mapClusterPt_iff_frequently] at hmap ⊢
      intro s hs
      exact (hmap s hs).mp (hev₁.mono fun q hq hm => by
        change h (collarInv h q) ∈ s at hm
        rwa [(apply_collarInv hq).1] at hm)
    have htend : Tendsto id (𝓝[Q] x) (𝓝 x) := tendsto_id.mono_left nhdsWithin_le_nhds
    exact eq_of_nhds_neBot (ClusterPt.mono h₁ htend)
  have hp0 : p.2 = 0 := by
    by_contra hn
    exact hoff p (unitInterval.pos_iff_ne_zero.mpr hn) (hpx ▸ hxX)
  obtain ⟨t, htI, htz⟩ := exists_circlePt_time lo p.1
  have hpe : p = (circlePt t, 0) := Prod.ext htz.symm hp0
  have hcirc₀ : circlePt lo ≠ p.1 ∧ circlePt hi ≠ p.1 := by
    have hpz : h (p.1, 0) = x := by
      rw [← hpx]
      exact congrArg h (Prod.ext rfl hp0.symm)
    have hnotz : ∀ z, h (z, 0) ∈ range ψ → z ≠ p.1 := fun z hz he => hxL
      (by rw [← hpz, ← he]; exact hz)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hnotz _ hz₀, hnotz _ hz₁⟩
    · exact ⟨hnotz _ hz₁, hnotz _ hz₀⟩
  have htlo : t ≠ lo := fun he => hcirc₀.1 (by rw [← he, htz])
  have hthi : t ≠ hi := fun he => hcirc₀.2 (by rw [← he, htz])
  have hcase : t ∈ Ioo lo hi ∨ t ∈ Ioo hi (lo + 1) := by
    rcases lt_or_gt_of_ne hthi with h' | h'
    · exact Or.inl ⟨lt_of_le_of_ne htI.1 htlo.symm, h'⟩
    · exact Or.inr ⟨h', htI.2⟩
  have hfinish : ∀ y' ∈ (X ∪ range ψ)ᶜ, (∀ᶠ p' in 𝓝 ((circlePt t, 0) : Circle × I), 0 < p'.2 →
      h p' ∈ connectedComponentIn (X ∪ range ψ)ᶜ y') →
      connectedComponentIn (X ∪ range ψ)ᶜ y = connectedComponentIn (X ∪ range ψ)ᶜ y' := by
    intro y' _ hg
    rw [← hpe] at hg
    have hfr := hp.frequently hg
    have hmap : ∃ᶠ q in 𝓝[Q] x, (q ∈ Q ∧ q ∈ Ω) ∧
        (0 < (collarInv h q).2 → h (collarInv h q) ∈ connectedComponentIn (X ∪ range ψ)ᶜ y') :=
      (hfr.and_eventually ((eventually_mem_nhdsWithin).and hev₁)).mono fun q hq => ⟨hq.2, hq.1⟩
    obtain ⟨q, ⟨hqQ, hqΩ⟩, hq⟩ := hmap.exists
    obtain ⟨he, hpos⟩ := apply_collarInv hqΩ
    have hqD := hq hpos
    rw [he] at hqD
    have e₁ := connectedComponentIn_eq hqQ
    have e₂ := connectedComponentIn_eq hqD
    exact e₁.trans e₂.symm
  rcases hcase with h' | h'
  · exact Or.inl (hfinish y₁ hy₁ (hg₁ t h'))
  · exact Or.inr (hfinish y₂ hy₂ (hg₂ t h'))

end GraphMinor.GM11
