/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffOrder

/-!
# The collapse map of a system of boxes

Graph Minors VII, (5.9), page 235. From a system of boxes around the cuffs, with `H(C)` the graphs
of the functions `f`, we get the map `ρ`, the part `G₁` of `G` above the graphs, and the graph `G'`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {ι : Type*}

/-- The facts on the boxes. -/
structure IsCollapseFrame (G : Drawing S) (φ : ι → ℝ × ℝ → S) (g f : ι → ℝ → ℝ) (Tr : S
  → Drawing S) : Prop where
  box : IsBoxSystem φ
  data : ∀ i, IsCollapseData (g i) (f i)
  bottom : ∀ i p, p ∈ cuffBox → (φ i p ∈ bd S ↔ p.2 = 0)
  allBottom : bd S ⊆ boxBottom φ
  graphU : ∀ i p, p ∈ cuffBox → p.2 = f i p.1 → φ i p ∈ G.U → φ i p ∈ G.V
  graphV : ∀ i p, p ∈ cuffBox → p.2 = f i p.1 → φ i p ∈ G.V → φ i (g i p.1, 0) ∈ G.V ∩ bd S
    ∧ φ i p ∈ (Tr (φ i (g i p.1, 0))).V
  corner : ∀ x ∈ G.V ∩ bd S, ∃ i e, (e = (0 : ℝ) ∨ e = 1) ∧ φ i (e, 0) = x ∧ φ i (e, 1) ∈ G.V
  tree : ∀ x ∈ G.V ∩ bd S, (Tr x).IsSubdrawing G ∧ IsGraphForest (Tr x).toGraph ∧ x ∈ (Tr x).V ∧
    (∀ a ∈ (Tr x).U, ∃ i p, p ∈ cuffBox ∧ φ i p = a ∧ p.2 ≤ f i p.1 ∧ φ i (g i p.1, 0) = x) ∧ ∀ a ∈
      (Tr x).V, ∀ b ∈ (Tr x).V, Nonempty (GraphWalk (Tr x).toGraph a b)

theorem boxCollapse_under {g f : ℝ → ℝ} (hd : IsCollapseData g f) {p : ℝ × ℝ} (hp : p ∈ cuffBox)
  (hle : p.2 ≤ f p.1) : boxCollapse g f p = (g p.1, 0) := by
  have h1 := (boxLevel_eq_zero hd hp).mpr hle
  refine Prod.ext ?_ ?_
  · simp [boxCollapse, h1]
  · simp [boxCollapse, h1]

/-- The level on a side of the box for the map that picks out the part below the graph. -/
noncomputable def lowLevel (w : ℝ) : ℝ := 2 * (1 - max 0 (1 - w))

/-- The map of a box that goes to level `2` exactly from the part on or above the graph. -/
noncomputable def lowMap (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, 2 * (1 - max 0
  ((f p.1 - p.2) / f p.1)))

theorem isBoxMap_lowMap {g f : ι → ℝ → ℝ} (hd : ∀ i, IsCollapseData (g i) (f i)) : IsBoxMap (fun i
  => lowMap (f i)) lowLevel := by
  refine ⟨fun i => ?_, fun i p hp => ?_, fun i p hp h2 => ?_, fun i m w hm hw => ?_⟩
  · have h1 : ContinuousOn (fun p : ℝ × ℝ => f i p.1) cuffBox := (hd i).fcont.comp continuousOn_fst
      fun p hp => hp.1
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (f i p.1 - p.2) / f i p.1) cuffBox :=
      (h1.sub continuousOn_snd).div h1 fun p hp => by
      have := ((hd i).f1 p.1 hp.1).1
      linarith
    have h3 : ContinuousOn (fun p : ℝ × ℝ => max 0 ((f i p.1 - p.2) / f i p.1)) cuffBox
      := continuous_max.comp_continuousOn (continuousOn_const.prodMk h2)
    exact continuousOn_fst.prodMk (continuousOn_const.mul (continuousOn_const.sub h3))
  · obtain ⟨h1, h2⟩ := (hd i).f1 p.1 hp.1
    have h3 : 0 < f i p.1 := by linarith
    have h4 : (f i p.1 - p.2) / f i p.1 ≤ 1 := by
      rw [div_le_one h3]
      linarith [hp.2.1]
    have h5 := le_max_left 0 ((f i p.1 - p.2) / f i p.1)
    have h6 : max 0 ((f i p.1 - p.2) / f i p.1) ≤ 1 := max_le zero_le_one h4
    refine ⟨hp.1, ?_, ?_⟩ <;> simp only [lowMap] <;> linarith
  · obtain ⟨h1, h3⟩ := (hd i).f1 p.1 hp.1
    have h4 : 0 < f i p.1 := by linarith
    have h5 : (f i p.1 - p.2) / f i p.1 ≤ 0 := by
      rw [h2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h4.le
    refine Prod.ext rfl ?_
    change 2 * (1 - max 0 ((f i p.1 - p.2) / f i p.1)) = p.2
    rw [max_eq_left h5, h2]
    ring
  · have hf : f i m = 1 := by
      rcases hm with rfl | rfl
      · exact (hd i).f0
      · exact (hd i).f1'
    simp [lowMap, lowLevel, hf]

variable [Finite ι] {G : Drawing S} {φ : ι → ℝ × ℝ → S} {g f : ι → ℝ → ℝ} {Tr : S → Drawing S}

/-- The points strictly below a graph. -/
def IsBelowGraph (φ : ι → ℝ × ℝ → S) (f : ι → ℝ → ℝ) (x : S) : Prop := ∃ i p, p ∈ cuffBox ∧ φ i p
  = x ∧ p.2 < f i p.1

omit [TopologicalSpace S] [T2Space S] [Finite ι] in
theorem not_below_of_above {x : S} (hx : IsAboveGraph φ f x) : ¬ IsBelowGraph φ f x
  := fun ⟨i, p, hp, he, hlt⟩ => absurd (hx i p hp he) (not_lt.mpr hlt.le)

theorem isOpen_below (h : IsBoxSystem φ) (hd : ∀ i, IsCollapseData (g i)
  (f i)) : IsOpen {x | IsBelowGraph φ f x} := by
  obtain ⟨Ψ, hc, h0, hb, hoff⟩ := h.exists_homotopy (isBoxMap_lowMap hd)
  have hcl : Continuous fun x => Ψ (1, x) := by fun_prop
  have hval : ∀ i p, p ∈ cuffBox → Ψ (1, φ i p) = φ i (lowMap (f i) p) := fun i p hp => by
    have h1 := hb i p 1 hp
    rwa [Set.Icc.coe_one, boxLine_one] at h1
  have hset : {x | IsBelowGraph φ f x} = (fun x => Ψ (1, x)) ⁻¹' (⋃ i, φ i '' {p | p ∈ cuffBox
    ∧ p.2 < 2}) := by
    ext x
    constructor
    · rintro ⟨i, p, hp, rfl, hlt⟩
      obtain ⟨h1, h3⟩ := (hd i).f1 p.1 hp.1
      have h4 : 0 < f i p.1 := by linarith
      have hm := (isBoxMap_lowMap hd).maps i hp
      refine mem_iUnion.mpr ⟨i, lowMap (f i) p, ⟨hm, ?_⟩, (hval i p hp).symm⟩
      have h5 : 0 < (f i p.1 - p.2) / f i p.1 := div_pos (by linarith) h4
      have h6 := le_max_right 0 ((f i p.1 - p.2) / f i p.1)
      change 2 * (1 - max 0 ((f i p.1 - p.2) / f i p.1)) < 2
      linarith
    · intro hx
      obtain ⟨i', p', ⟨hp', hlt⟩, he⟩ := mem_iUnion.mp hx
      by_cases hb' : ∃ i, x ∈ φ i '' cuffBox
      · obtain ⟨i, p, hp, rfl⟩ := hb'
        by_cases hlt' : p.2 < f i p.1
        · exact ⟨i, p, hp, rfl, hlt'⟩
        · exfalso
          push Not at hlt'
          obtain ⟨h1, h3⟩ := (hd i).f1 p.1 hp.1
          have h4 : 0 < f i p.1 := by linarith
          have h5 : (f i p.1 - p.2) / f i p.1 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
            (by linarith) h4.le
          have h6 : lowMap (f i) p = (p.1, 2) := by
            refine Prod.ext rfl ?_
            change 2 * (1 - max 0 ((f i p.1 - p.2) / f i p.1)) = 2
            rw [max_eq_left h5]
            ring
          have h7 : (p.1, (2 : ℝ)) ∈ cuffBox := ⟨hp.1, by norm_num, le_rfl⟩
          have h8 : φ i' p' = φ i (p.1, 2) := by
            rw [he]
            change Ψ (1, φ i p) = _
            rw [hval i p hp, h6]
          rcases h.meet i' i p' _ hp' h7 h8 with ⟨-, h9⟩ | ⟨h9, -⟩
          · rw [h9] at hlt
            exact lt_irrefl _ hlt
          · simp only at h9
            linarith
      · push Not at hb'
        have h1 : Ψ (1, x) = x := hoff x 1 hb'
        have h2 : φ i' p' = x := he.trans h1
        exact (hb' i' (h2 ▸ mem_image_of_mem (φ i') hp')).elim
  rw [hset]
  exact h.isOpen.preimage hcl

/-- What the collapse map of a frame gives. -/
structure IsGlued (G G₁ G' : Drawing S) (ρ : S → S) (Ψ : unitInterval × S → S) (φ : ι → ℝ × ℝ → S)
  (g f : ι → ℝ → ℝ) (Tr : S → Drawing S) : Prop where
  col : IsCollapse G G₁ G' ρ Ψ (G.V ∩ bd S) {x | IsAboveGraph φ f x} Tr
  val : ∀ i p, p ∈ cuffBox → ρ (φ i p) = φ i (boxCollapse (g i) (f i) p)
  voff : ∀ x, (∀ i, x ∉ φ i '' cuffBox) → ρ x = x
  upU : ∀ z, IsAboveGraph φ f z → z ∈ G.U → z ∈ G₁.U
  downV : ∀ z, IsAboveGraph φ f z → z ∈ G₁.V → z ∈ G.V
  down : ∀ z ∈ G₁.U, IsAboveGraph φ f z ∨ ∃ i p, p ∈ cuffBox ∧ φ i p = z ∧ p.2 = f i p.1 ∧ z ∈ G.V
  above_iff : ∀ x, IsAboveGraph φ f x ↔ ρ x ∉ bd S
  upV : ∀ z, IsAboveGraph φ f z → z ∈ G.V → z ∈ G₁.V
  bdV : G'.V ∩ bd S = G.V ∩ bd S

/-- The collapse data of a frame. -/
theorem IsCollapseFrame.exists_collapse [CompactSpace S] [Nonempty S]
  (h : IsCollapseFrame G φ g f Tr) (hbdc : IsClosed (bd S)) :
    ∃ (G₁ G' : Drawing S) (ρ : S → S) (Ψ : unitInterval × S → S), IsGlued G G₁ G' ρ Ψ φ g f Tr := by
  classical
  have hd := h.data
  obtain ⟨Ψ, hc, h0, hb, hoff⟩ := h.box.exists_homotopy (isBoxMap_collapse hd)
  let ρ : S → S := fun x => Ψ (1, x)
  have hρc : Continuous ρ := by fun_prop
  have hval : ∀ i p, p ∈ cuffBox → ρ (φ i p) = φ i (boxCollapse (g i) (f i) p) := fun i p hp => by
    have h1 := hb i p 1 hp
    rwa [Set.Icc.coe_one, boxLine_one] at h1
  have hvoff : ∀ x, (∀ i, x ∉ φ i '' cuffBox) → ρ x = x := fun x hx => hoff x 1 hx
  set A : Set S := {x | IsAboveGraph φ f x} with hA
  have hbot : ∀ i (m : ℝ), m ∈ Icc (0 : ℝ) 1 → φ i (m, 0) ∈ bd S := fun i m hm =>
    (h.bottom i (m, 0) ⟨hm, le_rfl, by norm_num⟩).mpr rfl
  have hnotA : ∀ x, x ∉ A → ∃ i p, p ∈ cuffBox ∧ φ i p = x ∧ p.2 ≤ f i p.1 := fun x hx => by
    simp only [hA, mem_ofPred_eq, IsAboveGraph] at hx
    push Not at hx
    obtain ⟨i, p, hp, he, hle⟩ := hx
    exact ⟨i, p, hp, he, hle⟩
  have hunder : ∀ i p, p ∈ cuffBox → p.2 ≤ f i p.1 → boxCollapse (g i) (f i) p = (g i p.1, 0)
    := fun i p hp hle => boxCollapse_under (hd i) hp hle
  have hrb : ∀ x, x ∈ A ↔ ρ x ∉ bd S := fun x => by
    constructor
    · intro hx hb'
      have h1 : bd S ⊆ boxBottom φ := h.allBottom
      exact h.box.not_bottom_above hd hval hvoff hx (h1 hb')
    · intro hx
      by_contra hn
      obtain ⟨i, p, hp, rfl, hle⟩ := hnotA x hn
      rw [hval i p hp, hunder i p hp hle] at hx
      exact hx (hbot i _ ((hd i).gmem hp.1))
  have hAo : IsOpen A := by
    have : A = ρ ⁻¹' (bd S)ᶜ := by
      ext x
      exact hrb x
    rw [this]
    exact hbdc.isOpen_compl.preimage hρc
  have hinj : ∀ x ∈ A, ∀ y, ρ y = ρ x → y = x := fun x hx y he => by
    have hy : y ∈ A := (hrb y).mpr (he ▸ (hrb x).mp hx)
    exact h.box.inj_above hd hval hvoff hy hx he
  have hBo := isOpen_below h.box hd
  have hdisAB : ∀ x, x ∈ A → ¬ IsBelowGraph φ f x := fun x hx ⟨i, p, hp, he, hlt⟩ => absurd
    (hx i p hp he) (not_lt.mpr hlt.le)
  let E₁ : Set (Set S) := {e | e ∈ G.E ∧ e ⊆ A}
  let V₁ : Set S := {v | v ∈ G.V ∧ ¬ IsBelowGraph φ f v}
  have hclA : ∀ e ∈ E₁, ∀ z ∈ closure e, ¬ IsBelowGraph φ f z := fun e he z hz hbz => by
    obtain ⟨w, hw, hwB⟩ := mem_closure_iff.mp hz _ hBo hbz
    exact hdisAB w (he.2 hwB) hw
  have hV₁ : G.spanV V₁ E₁ = V₁ := by
    refine subset_antisymm ?_ fun v hv => .inl ⟨hv, hv.1⟩
    rintro v (hv | hv)
    · exact hv.1
    · obtain ⟨e, he, hv⟩ := mem_iUnion₂.mp hv
      exact ⟨hv.2, hclA e he.1 v hv.1⟩
  set G₁ : Drawing S := G.span V₁ E₁ with hG₁
  have hG₁V : G₁.V = V₁ := hV₁
  have hG₁E : G₁.E = E₁ := by
    rw [hG₁, G.span_E]
    exact inter_eq_left.mpr fun e he => he.1
  have hsub : G₁.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hoffU : G₁.U \ G₁.V ⊆ A := by
    rintro z ⟨hz, hzV⟩
    obtain ⟨e, he, hze⟩ := G₁.exists_edge_of_mem hz hzV
    rw [hG₁E] at he
    exact he.2 hze
  obtain ⟨G', hU, hV, hE⟩ := exists_collapse_drawing hρc hinj G₁ hoffU
  have hvert : ∀ v ∈ G₁.V, v ∈ A ∨ (ρ v ∈ G.V ∩ bd S ∧ v ∈ (Tr (ρ v)).V) := fun v hv => by
    rw [hG₁V] at hv
    by_cases hvA : v ∈ A
    · exact .inl hvA
    · obtain ⟨i, p, hp, rfl, hle⟩ := hnotA v hvA
      have heq : p.2 = f i p.1 := le_antisymm hle (not_lt.mp fun hlt => hv.2 ⟨i, p, hp, rfl, hlt⟩)
      obtain ⟨h1, h2⟩ := h.graphV i p hp heq hv.1
      rw [hval i p hp, hunder i p hp hle]
      exact .inr ⟨h1, h2⟩
  have hcol : IsCollapse G G₁ G' ρ Ψ (G.V ∩ bd S) A Tr := by
    refine ⟨hc, fun x => ?_, fun _ => rfl, fun x hx τ => ?_, hinj, hsub, hoffU, hU, hV, hE, rfl,
      hvert, fun x hx => ?_⟩
    · have h1 := h0 x
      exact h1
    · obtain ⟨i, e, he, rfl, -⟩ := h.corner x hx
      have hp : (e, (0 : ℝ)) ∈ cuffBox := by
        rcases he with rfl | rfl
        · exact ⟨⟨le_rfl, zero_le_one⟩, le_rfl, by norm_num⟩
        · exact ⟨⟨zero_le_one, le_rfl⟩, le_rfl, by norm_num⟩
      rw [hb i _ τ hp, boxCollapse_side (hd i) he]
      have h1 : sideLevel 0 = 0 := by simp [sideLevel]
      rw [h1, boxLine_self]
    · obtain ⟨h1, h2, h3, h4, h5⟩ := h.tree x hx
      refine ⟨h1, h2, h3, fun a ha => ?_, h5⟩
      obtain ⟨i, p, hp, rfl, hle, he⟩ := h4 a ha
      rw [hval i p hp, hunder i p hp hle, he]
  have hfe : ∀ i (e : ℝ), (e = 0 ∨ e = 1) → f i e = 1 := fun i e he => by
    rcases he with rfl | rfl
    · exact (hd i).f0
    · exact (hd i).f1'
  have hge : ∀ i (e : ℝ), (e = 0 ∨ e = 1) → g i e = e := fun i e he => by
    rcases he with rfl | rfl
    · exact (hd i).g0
    · exact (hd i).g1
  refine ⟨G₁, G', ρ, Ψ, hcol, hval, hvoff, fun z hz hzU => ?_, fun z _ hz => hsub.1 hz,
    fun z hz => ?_, hrb, fun z hz hzV => hG₁V ▸ ⟨hzV, hdisAB z hz⟩, ?_⟩
  · by_cases hzV : z ∈ G.V
    · exact G₁.V_subset_U (hG₁V ▸ ⟨hzV, hdisAB z hz⟩)
    · obtain ⟨e, he, hze⟩ := G.exists_edge_of_mem hzU hzV
      -- An edge that meets `A` lies in `A`, as it misses the graphs.
      have heU : e ⊆ A ∪ {x | IsBelowGraph φ f x} := fun y hy => by
        by_cases hyA : y ∈ A
        · exact .inl hyA
        · obtain ⟨i, p, hp, rfl, hle⟩ := hnotA y hyA
          rcases hle.lt_or_eq with hlt | heq
          · exact .inr ⟨i, p, hp, rfl, hlt⟩
          · exact absurd (h.graphU i p hp heq ((he.2.1 hy).1)) (he.2.1 hy).2
      have hsubA : e ⊆ A := by
        have hpc := he.2.2.1.isConnected.isPreconnected
        by_contra hn
        obtain ⟨y, hy, hyA⟩ := not_subset.mp hn
        have hyB : y ∈ {x | IsBelowGraph φ f x} := (heU hy).resolve_left hyA
        obtain ⟨w, -, hw'⟩ := hpc A _ hAo hBo heU ⟨z, hze, hz⟩ ⟨y, hy, hyB⟩
        exact hdisAB w hw'.1 hw'.2
      exact G₁.closure_subset_U (hG₁E ▸ (⟨he, hsubA⟩ : e ∈ E₁)) (subset_closure hze)
  · by_cases hzV : z ∈ G₁.V
    · by_cases hzA : z ∈ A
      · exact .inl hzA
      · obtain ⟨i, p, hp, rfl, hle⟩ := hnotA z hzA
        have hz' : φ i p ∈ V₁ := hG₁V ▸ hzV
        exact .inr ⟨i, p, hp, rfl, le_antisymm hle (not_lt.mp fun hlt => hz'.2 ⟨i, p, hp, rfl,
          hlt⟩), hz'.1⟩
    · exact .inl (hoffU ⟨hz, hzV⟩)
  · ext x
    constructor
    · rintro ⟨hx, hxb⟩
      rw [hV] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rcases hvert a ha with h1 | h1
      · exact absurd hxb ((hrb a).mp h1)
      · exact h1.1
    · intro hx
      obtain ⟨i, e, he, rfl, hv⟩ := h.corner x hx
      have hp : (e, (1 : ℝ)) ∈ cuffBox := by
        rcases he with rfl | rfl
        · exact ⟨⟨le_rfl, zero_le_one⟩, zero_le_one, by norm_num⟩
        · exact ⟨⟨zero_le_one, le_rfl⟩, zero_le_one, by norm_num⟩
      refine ⟨?_, hx.2⟩
      rw [hV]
      refine ⟨φ i (e, 1), hG₁V ▸ ⟨hv, ?_⟩, ?_⟩
      · rintro ⟨i', p, hp', he', hlt⟩
        rcases h.box.meet i' i p _ hp' hp he' with ⟨rfl, h1⟩ | ⟨h1, h2, -⟩
        · rw [h1, show f i' (e, (1 : ℝ)).1 = 1 from hfe i' e he] at hlt
          exact lt_irrefl _ hlt
        · rw [hfe i' _ h2] at hlt
          exact hlt.ne h1
      · rw [hval i _ hp, hunder i _ hp (by rw [show f i (e, (1 : ℝ)).1 = 1 from hfe i e he]),
          show g i (e, (1 : ℝ)).1 = e from hge i e he]

end GraphMinor.GM07
