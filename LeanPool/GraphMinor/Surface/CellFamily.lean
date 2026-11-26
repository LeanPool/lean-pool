/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CellMap
public import LeanPool.GraphMinor.Surface.WordSide
public import LeanPool.GraphMinor.Surface.WordSlide
public import LeanPool.GraphMinor.Surface.VertexLink

/-!
# From a dissection to words

The cells of a dissection give a family of polygons, one word for each cell, and a letter for each
edge
(`exists_family`). The letters of a word say which edges go around the cell. Each edge comes with a
fixed arc, so
that two sides with the same letter are pasted by the parameter of the arc. Fibres over points that
are not vertices
are read off from the sides, and fibres over vertices come from `prel_of_vertex`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X] {V : Set X} {E : Set (Set X)}

omit [T2Space X] in
theorem continuousOn_slots {W : ℕ → List Letter} {f : ℕ × ℂ → X}
    (h : ∀ i, W i ≠ [] → ContinuousOn (fun z => f (i, z)) (closedBall 0 1)) : ContinuousOn f
      (Dsk W) := by
  rw [continuousOn_prod_of_discrete_left]
  intro s
  by_cases hs : W s = []
  · have : {z | (s, z) ∈ Dsk W} = ∅ := by
      ext z
      simp [Dsk, hs]
    rw [this]
    exact continuousOn_empty _
  · exact (h s hs).mono fun z hz => mem_closedBall_zero_iff.mpr hz.2

omit [T2Space X] in
theorem sd_end {a : 𝕀 → X} (ha : IsArcMap a) (b : Bool) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (h : sd a b u = a 0 ∨ sd a b u = a 1) : u = 0 := by
  have e0 : extI a 0 = a 0 := extI_coe a 0
  have e1 : extI a 1 = a 1 := extI_coe a 1
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
  have hinj := sd_injOn ha b
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have s0 : sd a b 0 = a 0 ∨ sd a b 0 = a 1 := by
    cases b
    · right
      simp [sd, e1]
    · left
      simp [sd, e0]
  have s1 : sd a b 1 = a 0 ∨ sd a b 1 = a 1 := by
    cases b
    · left
      simp [sd, e0]
    · right
      simp [sd, e1]
  have hsw : sd a b 0 ≠ sd a b 1 := fun he => zero_ne_one (hinj h0 h1 he)
  rcases h with h | h <;> rcases s0 with s0 | s0 <;> rcases s1 with s1 | s1
  · exact absurd (s0.trans s1.symm) hsw
  · exact hinj hu' h0 (h.trans s0.symm)
  · exact absurd (hu.2.ne (hinj hu' h1 (h.trans s1.symm))) (by simp)
  · exact absurd (s0.trans s1.symm) hsw
  · exact absurd (s0.trans s1.symm) hsw
  · exact absurd (hu.2.ne (hinj hu' h1 (h.trans s1.symm))) (by simp)
  · exact hinj hu' h0 (h.trans s0.symm)
  · exact absurd (s0.trans s1.symm) hsw

/-- The data of one cell of a dissection. -/
theorem exists_cell_data (hg : IsGraph V E) (A : Set X → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) {Φ : Set X}
      (hΦ : IsClosedDisc Φ)
    (hbd : discBd Φ ⊆ ⋃₀ E) :
    ∃ (m : ℕ) (s : ℕ → Set X) (ε : ℕ → Bool) (Ψ : ℂ → X), 2 ≤ m ∧ (∀ p < m, s p ∈ E
      ∧ s p ⊆ discBd Φ) ∧
      (∀ p < m, ∀ q < m, p ≠ q → s p ≠ s q) ∧ ContinuousOn Ψ (closedBall 0 1) ∧ InjOn Ψ
        (closedBall 0 1) ∧
      Ψ '' closedBall 0 1 = Φ ∧ (∀ z ∈ closedBall (0 : ℂ) 1, Ψ z ∈ discBd Φ ↔ ‖z‖ = 1) ∧
      ∀ p < m, ∀ t ∈ Icc (0 : ℝ) 1, Ψ (sdPt m p (ε p) t) = extI (A (s p)) t := by
  obtain ⟨m, s, ε, hm, hs, hcov, hadj, hclose, hne⟩ := exists_edge_walk hg hΦ.isOArc_discBd hbd A hA
  have harc : ∀ p < m, IsArcMap (A (s p)) := fun p hp => (hA _ (hs p hp).1).1
  have hdis : ∀ p < m, ∀ q < m, p ≠ q → ∀ u ∈ Ico (0 : ℝ) 1, ∀ v ∈ Ico (0 : ℝ) 1,
      sd (A (s p)) (ε p) u ≠ sd (A (s q)) (ε q) v := by
    intro p hp q hq hpq u hu v hv he
    obtain ⟨hsne, hst⟩ := hne p hp q hq hpq
    have h1 : sd (A (s p)) (ε p) u ∈ s p := (hA _ (hs p hp).1).2.1.subset (sd_mem _ _)
    have h2 : sd (A (s q)) (ε q) v ∈ s q := (hA _ (hs q hq).1).2.1.subset (sd_mem _ _)
    have hV : sd (A (s p)) (ε p) u ∈ V := hg.disj _ (hs p hp).1 _ (hs q hq).1 hsne ⟨h1, he ▸ h2⟩
    have h3 : sd (A (s p)) (ε p) u ∈ s p ∩ V := ⟨h1, hV⟩
    have h4 : sd (A (s q)) (ε q) v ∈ s q ∩ V := ⟨h2, he ▸ hV⟩
    rw [(hA _ (hs p hp).1).2.2] at h3
    rw [(hA _ (hs q hq).1).2.2] at h4
    have hu0 := sd_end (harc p hp) (ε p) hu h3
    have hv0 := sd_end (harc q hq) (ε q) hv h4
    rw [hu0, hv0] at he
    exact hst he
  obtain ⟨Ψ, h1, h2, h3, h4, h5⟩ := exists_cell_map hΦ hm (fun p => A (s p)) ε harc hadj hclose hdis
    (fun p hp => by
      rw [(hA _ (hs p hp).1).2.1]
      exact (hs p hp).2)
    (fun y hy => by
      obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcov hy)
      exact mem_biUnion hp (by rw [(hA _ (hs p hp).1).2.1]; exact hyp))
  refine ⟨m, s, ε, Ψ, ?_, hs, fun p hp q hq hpq => (hne p hp q hq hpq).1, h1, h2, h3, h4, h5⟩
  by_contra hlt
  have hm1 : m = 1 := by omega
  subst hm1
  have := sd_injOn (harc 0 hm) (ε 0) (by simp) (by simp) hclose
  exact one_ne_zero this

theorem exists_side_of_sphere {n : ℕ} (hn : 0 < n) (b : ℕ → Bool) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ p < n, ∃ t ∈ Icc (0 : ℝ) 1, sdPt n p (b p) t = z := by
  have h1 : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
  rw [← per_image hn] at h1
  obtain ⟨x, hx, rfl⟩ := h1
  have hex : ∃ p < n, x ∈ Icc (p : ℝ) (p + 1) := by
    refine ⟨min ⌊x⌋₊ (n - 1), by omega, ?_⟩
    have hle : ⌊x⌋₊ ≤ x := Nat.floor_le hx.1
    have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    by_cases h1 : ⌊x⌋₊ ≤ n - 1
    · rw [min_eq_left h1]
      exact ⟨hle, hlt.le⟩
    · have h2 : ⌊x⌋₊ = n := by
        have : ⌊x⌋₊ ≤ n := Nat.floor_le_of_le hx.2
        omega
      have h3 : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub hn]
        simp
      rw [min_eq_right (by omega), h3]
      rw [h2] at hle
      constructor <;> linarith [hx.2]
  obtain ⟨p, hp, hxp⟩ := hex
  refine ⟨p, hp, if b p then x - p else 1 - (x - p), ?_, ?_⟩
  · cases b p
    · simpa using ⟨by linarith [hxp.2], by linarith [hxp.1]⟩
    · simpa using ⟨by linarith [hxp.1], by linarith [hxp.2]⟩
  · cases b p <;> simp [sdPt]

theorem cnt_le_one_of_nodup {w : List Letter} (h : (w.map Prod.fst).Nodup) (c : ℕ) : cnt w c ≤ 1
  := by
  have h1 : cnt w c = (w.map Prod.fst).count c := by
    rw [List.count, List.countP_map]
    rfl
  rw [h1]
  exact List.nodup_iff_count_le_one.mp h c

omit [T2Space X] in
private theorem cell_label_bounds {𝓕 : Set (Set X)} (hd : IsDissection V E 𝓕)
    {A : Set X → 𝕀 → X} (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1})
    {lab : Set X → ℕ} (hlab : InjOn lab E) {D : Set ℕ} (hDf : D.Finite)
    {idx : Set X → ℕ} {cl : ℕ → Set X} {m : Set X → ℕ} {s : Set X → ℕ → Set X}
    {ε : Set X → ℕ → Bool} {W : ℕ → List Letter}
    (hclm : ∀ i ∈ D, cl i ∈ 𝓕) (hcli : ∀ i ∈ D, idx (cl i) = i)
    (hs : ∀ Φ ∈ 𝓕, ∀ p < m Φ, s Φ p ∈ E ∧ s Φ p ⊆ discBd Φ)
    (hsne : ∀ Φ ∈ 𝓕, ∀ p < m Φ, ∀ q < m Φ, p ≠ q → s Φ p ≠ s Φ q)
    (hget' : ∀ i p l, (W i)[p]? = some l → i ∈ D ∧ p < m (cl i) ∧ l = (lab (s (cl i) p), ε
      (cl i) p))
    (hlabels : ∀ i ∈ D, (W i).map Prod.fst = (List.range (m (cl i))).map (fun p => lab (s
      (cl i) p))) :
    (∀ c, ∑ i ∈ hDf.toFinset, cnt (W i) c ≤ 2) ∧ IsPaired W := by
  classical
  have hle1 : ∀ c, ∀ i ∈ hDf.toFinset, cnt (W i) c ≤ 1 := by
    intro c i hi
    have hiD : i ∈ D := by simpa using hi
    refine cnt_le_one_of_nodup ?_ c
    rw [hlabels i hiD]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro p hp q hq he
    by_contra hpq
    have hp' : p < m (cl i) := List.mem_range.mp hp
    have hq' : q < m (cl i) := List.mem_range.mp hq
    exact hsne _ (hclm i hiD) p hp' q hq' hpq
      (hlab (hs _ (hclm i hiD) p hp').1 (hs _ (hclm i hiD) q hq').1 he)
  have hTc : ∀ c, (hDf.toFinset.filter fun i => 0 < cnt (W i) c).card ≤ 2 := by
    intro c
    let T := hDf.toFinset.filter fun i => 0 < cnt (W i) c
    change T.card ≤ 2
    rcases T.eq_empty_or_nonempty with he | ⟨i₀, hi₀⟩
    · simp [he]
    have hwit : ∀ i ∈ T, ∃ p < m (cl i), lab (s (cl i) p) = c := fun i hi => by
      obtain ⟨W₁, l, W₂, he, hl⟩ := exists_of_cnt_pos (Finset.mem_filter.mp hi).2
      have hl' : l ∈ W i := by simp [he]
      obtain ⟨p, hp⟩ := List.getElem?_of_mem hl'
      obtain ⟨-, hp', e⟩ := hget' _ _ _ hp
      exact ⟨p, hp', (congrArg Prod.fst e).symm.trans hl⟩
    obtain ⟨p₀, hp₀, hl₀⟩ := hwit i₀ hi₀
    have hi₀D : i₀ ∈ D := by simpa using (Finset.mem_filter.mp hi₀).1
    let e₀ := s (cl i₀) p₀
    have he₀ : e₀ ∈ E := (hs _ (hclm _ hi₀D) p₀ hp₀).1
    obtain ⟨harc, hran, hends⟩ := hA e₀ he₀
    let x : X := A e₀ ⟨1 / 2, by norm_num, by norm_num⟩
    have hxe : x ∈ e₀ := hran.subset ⟨_, rfl⟩
    have hxV : x ∉ V := fun h => by
      have h1 : x ∈ e₀ ∩ V := ⟨hxe, h⟩
      rw [hends] at h1
      rcases h1 with h1 | h1
      · have := congrArg Subtype.val (harc.2 h1)
        norm_num at this
      · have := congrArg Subtype.val (harc.2 h1)
        norm_num at this
    have hsubT : cl '' (T : Set ℕ) ⊆ {Φ ∈ 𝓕 | x ∈ Φ} := by
      rintro _ ⟨i, hi, rfl⟩
      have hiD : i ∈ D := by simpa using (Finset.mem_filter.mp hi).1
      obtain ⟨p, hp, hl⟩ := hwit i hi
      refine ⟨hclm i hiD, ?_⟩
      have h1 : s (cl i) p = e₀ := hlab (hs _ (hclm _ hiD) p hp).1 he₀ (hl.trans hl₀.symm)
      exact discBd_subset _ ((hs _ (hclm _ hiD) p hp).2 (h1 ▸ hxe))
    have hinjT : InjOn cl (T : Set ℕ) := fun i hi j hj he => by
      have hiD : i ∈ D := by simpa using (Finset.mem_filter.mp hi).1
      have hjD : j ∈ D := by simpa using (Finset.mem_filter.mp hj).1
      rw [← hcli i hiD, ← hcli j hjD, he]
    have h2 := (encard_le_encard hsubT).trans (hd.count x hxV)
    rw [hinjT.encard_image, encard_coe_eq_coe_finsetCard] at h2
    exact_mod_cast h2
  constructor
  · intro c
    have hsum : ∑ i ∈ hDf.toFinset, cnt (W i) c ≤ (hDf.toFinset.filter fun i => 0 < cnt
      (W i) c).card := by
      rw [Finset.card_filter]
      refine Finset.sum_le_sum fun i hi => ?_
      have := hle1 c i hi
      split_ifs with h <;> omega
    exact hsum.trans (hTc c)
  · intro k
    have hinj : InjOn Prod.fst {t : ℕ × ℕ | ∃ e, (W t.1)[t.2]? = some (k, e)} := by
      rintro ⟨i, p⟩ ⟨e, h1⟩ ⟨j, q⟩ ⟨e', h2⟩ (he : i = j)
      subst he
      simp only at h1 h2
      obtain ⟨hi, hp, hl⟩ := hget' _ _ _ h1
      obtain ⟨-, hq, hl'⟩ := hget' _ _ _ h2
      have h3 : lab (s (cl i) p) = lab (s (cl i) q) := (congrArg Prod.fst hl).symm.trans
        (congrArg Prod.fst hl')
      by_contra hne
      have hpq : p ≠ q := fun h => hne (by rw [h])
      exact hsne _ (hclm i hi) p hp q hq hpq (hlab (hs _ (hclm i hi) p hp).1 (hs _
        (hclm i hi) q hq).1 h3)
    rw [← hinj.encard_image]
    refine (encard_le_encard (t := ((hDf.toFinset.filter fun i => 0 < cnt
      (W i) k : Finset ℕ) : Set ℕ)) ?_).trans ?_
    · rintro _ ⟨⟨i, p⟩, ⟨e, h1⟩, rfl⟩
      simp only at h1
      have hi := (hget' _ _ _ h1).1
      have hm' : (k, e) ∈ W i := List.mem_of_getElem? h1
      have := cnt_pos hm'
      simp only [Finset.coe_filter, mem_ofPred_eq]
      exact ⟨by simpa using hi, this⟩
    · rw [encard_coe_eq_coe_finsetCard]
      exact_mod_cast hTc k

/-- **Words of a dissection.** Each letter of the word names an edge, and each side runs along its
edge. -/
theorem exists_family_edges [Nonempty X] (hman : ∀ x : X, IsManifoldPoint x) {𝓕 : Set (Set X)}
  (hd : IsDissection V E 𝓕)
    (hne : 𝓕.Nonempty) :
    ∃ (W : ℕ → List Letter) (f : ℕ × ℂ → X) (S : Finset ℕ) (A : Set X → 𝕀 → X) (lab : Set X
      → ℕ), FinW W ∧ W 0 ≠ [] ∧
      Presents W f ∧ (∀ i, W i ≠ [] → 2 ≤ (W i).length) ∧ (∀ i, i ∉ S → W i = []) ∧
        (∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2) ∧
      (∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) ∧ InjOn lab E ∧
      (∀ i p k e', (W i)[p]? = some (k, e') → ∃ e ∈ E, lab e = k ∧ ∀ u ∈ Icc (0 : ℝ) 1,
        f (spt W i p u) = extI (A e) (ofs e' u)) ∧ (∀ a ∈ Dsk W, f a ∈ ⋃₀ E → ‖a.2‖ = 1)
          ∧ IsPaired W := by
  classical
  have hg := hd.graph
  have harcs : ∀ e, ∃ a : 𝕀 → X, e ∈ E → IsArcMap a ∧ range a = e ∧ e ∩ V = {a 0, a 1} := by
    intro e
    by_cases he : e ∈ E
    · obtain ⟨u, v, -, hl, hi⟩ := hg.edge e he
      obtain ⟨a, ha, h1, rfl, rfl⟩ := hl.exists_arc
      exact ⟨a, fun _ => ⟨ha, h1, hi⟩⟩
    · exact ⟨fun _ => Classical.arbitrary X, fun h => absurd h he⟩
  choose A hA using harcs
  have hdata := fun Φ (hΦ : Φ ∈ 𝓕) => exists_cell_data hg A hA (hd.disc Φ hΦ) (hd.bd Φ hΦ)
  choose! m s ε Ψ hm hs hsne hΨc hΨi hΨr hΨb hΨs using hdata
  obtain ⟨Φ₀, hΦ₀⟩ := hne
  obtain ⟨idx0, hidx0⟩ := Set.countable_iff_exists_injOn.mp hd.fin.countable
  let idx : Set X → ℕ := fun Φ => Equiv.swap (idx0 Φ₀) 0 (idx0 Φ)
  have hidx : InjOn idx 𝓕 := fun x hx y hy he => hidx0 hx hy ((Equiv.swap _ _).injective he)
  have hidxΦ₀ : idx Φ₀ = 0 := by simp [idx]
  obtain ⟨lab, hlab⟩ := Set.countable_iff_exists_injOn.mp (hg.fine.countable)
  let D : Set ℕ := idx '' 𝓕
  have hDf : D.Finite := hd.fin.image _
  let cl : ℕ → Set X := Function.invFunOn idx 𝓕
  have hclm : ∀ i ∈ D, cl i ∈ 𝓕 := fun i hi => Function.invFunOn_mem hi
  have hcli : ∀ i ∈ D, idx (cl i) = i := fun i hi => Function.invFunOn_eq hi
  have hcld : ∀ Φ ∈ 𝓕, cl (idx Φ) = Φ := fun Φ hΦ => hidx (hclm _ ⟨Φ, hΦ, rfl⟩) hΦ
    (hcli _ ⟨Φ, hΦ, rfl⟩)
  let word : Set X → List Letter := fun Φ => (List.range (m Φ)).map fun p => (lab (s Φ p), ε Φ p)
  let W : ℕ → List Letter := fun i => if i ∈ D then word (cl i) else []
  let f : ℕ × ℂ → X := fun a => Ψ (cl a.1) a.2
  have hlen : ∀ i ∈ D, (W i).length = m (cl i) := fun i hi => by simp [W, hi, word]
  have hget : ∀ i ∈ D, ∀ p < m (cl i), (W i)[p]? = some (lab (s (cl i) p), ε (cl i) p)
    := fun i hi p hp => by
    simp [W, hi, word, hp]
  have hget' : ∀ i p l, (W i)[p]? = some l → i ∈ D ∧ p < m (cl i) ∧ l = (lab (s (cl i) p), ε
    (cl i) p) := by
    intro i p l h
    by_cases hi : i ∈ D
    · have hlt : p < (W i).length := (List.getElem?_eq_some_iff.mp h).1
      rw [hlen i hi] at hlt
      rw [hget i hi p hlt] at h
      exact ⟨hi, hlt, (Option.some.inj h).symm⟩
    · simp [W, hi] at h
  have hWne : ∀ i, W i ≠ [] ↔ i ∈ D := fun i => by
    constructor
    · intro h
      by_contra hi
      exact h (by simp [W, hi])
    · intro hi he
      have := hlen i hi
      rw [he] at this
      have h2 := hm _ (hclm i hi)
      simp only [List.length_nil] at this
      omega
  have hmemD : ∀ {a}, a ∈ Dsk W → a.1 ∈ D ∧ a.2 ∈ closedBall (0 : ℂ) 1 := fun {a} ha =>
    ⟨(hWne _).mp ha.1, by simpa using ha.2⟩
  have hfW : FinW W := hDf.subset fun i hi => (hWne i).mp hi
  have hcont : ContinuousOn f (Dsk W) :=
    continuousOn_slots fun i hi => hΨc _ (hclm i ((hWne i).mp hi))
  have hsurj : f '' Dsk W = univ := by
    refine eq_univ_of_forall fun x => ?_
    have h1 : x ∈ ⋃₀ 𝓕 := hd.cover ▸ mem_univ x
    obtain ⟨Φ, hΦ, hx⟩ := h1
    rw [← hΨr Φ hΦ] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hi : idx Φ ∈ D := ⟨Φ, hΦ, rfl⟩
    refine ⟨(idx Φ, z), ⟨(hWne _).mpr hi, by simpa using hz⟩, ?_⟩
    simp only [f, hcld Φ hΦ]
  have hsval : ∀ i ∈ D, ∀ p < m (cl i), ∀ t ∈ Icc (0 : ℝ) 1,
      f (i, sdPt (W i).length p (ε (cl i) p) t) = extI (A (s (cl i) p)) t := fun i hi p hp t ht
        => by
    simp only [f, hlen i hi]
    exact hΨs _ (hclm i hi) p hp t ht
  have hst : ∀ a b, Stp W a b → f a = f b := by
    rintro _ _ ⟨i, j, p, q, k, e, e', t, h1, h2, -, ht, rfl, rfl⟩
    obtain ⟨hi, hp, hl⟩ := hget' _ _ _ h1
    obtain ⟨hj, hq, hl'⟩ := hget' _ _ _ h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl
    obtain ⟨h3, rfl⟩ := Prod.mk.inj hl'
    have hes : s (cl i) p = s (cl j) q := hlab (hs _ (hclm i hi) p hp).1 (hs _
      (hclm j hj) q hq).1 h3
    rw [hsval i hi p hp t ht, hsval j hj q hq t ht, hes]
  have hinj : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, a.1 = b.1 → f a = f b → a = b := by
    rintro ⟨i, z⟩ ha ⟨j, z'⟩ hb he hf
    obtain rfl : i = j := he
    have := hΨi _ (hclm i (hmemD ha).1) (hmemD ha).2 (hmemD hb).2 hf
    rw [show z = z' from this]
  have hint : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, ‖a.2‖ ≠ 1 → f a = f b → a = b := by
    rintro ⟨i, z⟩ ha ⟨j, z'⟩ hb hn hf
    have hi := (hmemD ha).1
    have hj := (hmemD hb).1
    have h1 : f (i, z) ∈ discInt (cl i) := by
      refine ⟨(hΨr _ (hclm i hi)) ▸ mem_image_of_mem _ (hmemD ha).2, fun h => hn ?_⟩
      exact (hΨb _ (hclm i hi) z (hmemD ha).2).mp h
    have h2 : f (j, z') ∈ cl j := (hΨr _ (hclm j hj)) ▸ mem_image_of_mem _ (hmemD hb).2
    rw [← hf] at h2
    have hc : cl i = cl j := by
      by_contra hc
      exact Set.disjoint_left.mp (hd.disj _ (hclm i hi) _ (hclm j hj) hc) h1 h2
    have hij : i = j := by rw [← hcli i hi, ← hcli j hj, hc]
    subst hij
    exact hinj _ ha _ hb rfl hf
  have hside : ∀ a ∈ Dsk W, ‖a.2‖ = 1 → ∃ p < m (cl a.1), ∃ t ∈ Icc (0 : ℝ) 1,
      a = (a.1, sdPt (W a.1).length p (ε (cl a.1) p) t) ∧ f a = extI (A (s (cl a.1) p)) t := by
    rintro ⟨i, z⟩ ha hn
    have hi := (hmemD ha).1
    have hm0 : 0 < m (cl i) := by
      have := hm _ (hclm i hi)
      omega
    obtain ⟨p, hp, t, ht, e⟩ := exists_side_of_sphere hm0 (ε (cl i)) hn
    refine ⟨p, hp, t, ht, ?_, ?_⟩
    · simp only [hlen i hi, e]
    · have := hsval i hi p hp t ht
      rw [hlen i hi, e] at this
      exact this
  have hoff : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, f a = f b → f a ∉ V → PRel W a b := by
    intro a ha b hb hf hV
    by_cases hna : ‖a.2‖ = 1
    · by_cases hnb : ‖b.2‖ = 1
      · obtain ⟨p, hp, t, ht, e1, e2⟩ := hside a ha hna
        obtain ⟨q, hq, t', ht', e3, e4⟩ := hside b hb hnb
        have hi := (hmemD ha).1
        have hj := (hmemD hb).1
        have hsE := (hs _ (hclm _ hi) p hp).1
        have hsE' := (hs _ (hclm _ hj) q hq).1
        have mem1 : f a ∈ s (cl a.1) p := by
          rw [e2]
          exact (hA _ hsE).2.1.subset ⟨_, rfl⟩
        have mem2 : f a ∈ s (cl b.1) q := by
          rw [hf, e4]
          exact (hA _ hsE').2.1.subset ⟨_, rfl⟩
        have hes : s (cl a.1) p = s (cl b.1) q := by
          by_contra hc
          exact hV (hg.disj _ hsE _ hsE' hc ⟨mem1, mem2⟩)
        have htt : t = t' := by
          have h1 : extI (A (s (cl a.1) p)) t = extI (A (s (cl a.1) p)) t' := by
            rw [← e2, hf, e4, hes]
          exact extI_injOn (hA _ hsE).1.2 ht ht' h1
        subst htt
        by_cases hpq : (a.1, p) = (b.1, q)
        · obtain ⟨h1, h2⟩ := Prod.mk.inj hpq
          have : a = b := by
            rw [e1, e3]
            subst h2
            simp only [h1]
          rw [this]
          exact .refl _
        · refine .rel _ _ ⟨a.1, b.1, p, q, lab (s (cl a.1) p), ε (cl a.1) p, ε (cl b.1) q, t,
            hget _ hi p hp, ?_, hpq, ht,
            e1, e3⟩
          rw [hes]
          exact hget _ hj q hq
      · rw [hint b hb a ha hnb hf.symm]
        exact .refl _
    · rw [hint a ha b hb hna hf]
      exact .refl _
  have hrelf : ∀ a b, PRel W a b → f a = f b := fun a b h => by
    induction h with
    | rel _ _ h => exact hst _ _ h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  have hpres : Presents W f := by
    refine ⟨hcont, hsurj, fun a ha b hb => ⟨fun he => ?_, hrelf a b⟩⟩
    by_cases hV : f a ∈ V
    · have hZ : (Dsk W ∩ f ⁻¹' {f a}).Finite := by
        refine Set.Finite.of_finite_image (f := Prod.fst) (hDf.subset ?_) ?_
        · rintro _ ⟨x, hx, rfl⟩
          exact (hmemD hx.1).1
        · intro x hx y hy he'
          exact hinj x hx.1 y hy.1 he' (hx.2.trans hy.2.symm)
      exact prel_of_vertex hfW hcont hsurj hst hinj hg.fin (hman (f a)) hZ hoff ha hb rfl he.symm
    · exact hoff a ha b hb he hV
  obtain ⟨hTotal, hPaired⟩ :=
    cell_label_bounds hd hA hlab hDf hclm hcli hs hsne hget' (fun i hi => by
      simp [W, hi, word, Function.comp_def])
  refine ⟨W, f, hDf.toFinset, A, lab, hfW, ?_, hpres, ?_, ?_, hTotal, hA, hlab, ?_, ?_, hPaired⟩
  · exact (hWne 0).mpr ⟨Φ₀, hΦ₀, hidxΦ₀⟩
  · intro i hi
    rw [hlen i ((hWne i).mp hi)]
    exact hm _ (hclm i ((hWne i).mp hi))
  · intro i hi
    by_contra he
    exact hi (by simpa using (hWne i).mp he)
  · intro i p k e' h
    obtain ⟨hi, hp, hl⟩ := hget' _ _ _ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl
    refine ⟨s (cl i) p, (hs _ (hclm i hi) p hp).1, rfl, fun u hu => ?_⟩
    have h1 := hsval i hi p hp (ofs (ε (cl i) p) u) (ofs_mem hu)
    rw [sdPt_eq, ofs_ofs] at h1
    exact h1
  · intro a ha hfa
    by_contra hn
    have hi := (hmemD ha).1
    have h1 : f a ∈ discInt (cl a.1) :=
      ⟨(hΨr _ (hclm _ hi)) ▸ mem_image_of_mem _ (hmemD ha).2, fun h => hn ((hΨb _ (hclm _ hi) a.2
        (hmemD ha).2).mp h)⟩
    exact Set.disjoint_left.mp (hd.int _ (hclm _ hi)) h1 hfa

/-- **Words of a dissection.** -/
theorem exists_family [Nonempty X] (hman : ∀ x : X, IsManifoldPoint x) {𝓕 : Set (Set X)}
  (hd : IsDissection V E 𝓕)
    (hne : 𝓕.Nonempty) :
    ∃ (W : ℕ → List Letter) (f : ℕ × ℂ → X) (S : Finset ℕ), FinW W ∧ W 0 ≠ [] ∧ Presents W f ∧
      (∀ i, W i ≠ [] → 2 ≤ (W i).length) ∧ (∀ i, i ∉ S → W i = []) ∧ ∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2
        := by
  obtain ⟨W, f, S, A, lab, h1, h2, h3, h4, h5, h6, -⟩ := exists_family_edges hman hd hne
  exact ⟨W, f, S, h1, h2, h3, h4, h5, h6⟩

end GraphMinor.Surface
