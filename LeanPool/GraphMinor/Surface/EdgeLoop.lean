/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Dissection

/-!
# An `O`-arc in a graph as a loop of edges

Let `P` be an `O`-arc in a graph. Going once around `P` we pass through finitely many edges, each of
them as a whole
(`exists_edge_loop`). The loop is parametrized by `[0, m]`, and on each `[p, p + 1]` it runs along
the given
parametrization of an edge, forwards or backwards.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

/-- The points of a finite set in increasing order. -/
theorem exists_sorted {T : Set ℝ} (hT : T.Finite) (hsub : T ⊆ Icc 0 1) (h0 : (0 : ℝ) ∈ T) (h1 :
  (1 : ℝ) ∈ T) :
    ∃ (m : ℕ) (t : ℕ → ℝ), 0 < m ∧ t 0 = 0 ∧ t m = 1 ∧ (∀ p < m, t p < t (p + 1)) ∧ (∀ p
      ≤ m, t p ∈ T) ∧
      (∀ p < m, ∀ x ∈ T, x ∉ Ioo (t p) (t (p + 1))) ∧ (∀ x ∈ T, ∃ p ≤ m, t p = x) := by
  classical
  set s := hT.toFinset with hs
  have hcard : 2 ≤ s.card := by
    have h2 : ({0, 1} : Finset ℝ) ⊆ s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa [hs]
    have h3 := Finset.card_le_card h2
    rwa [Finset.card_pair (zero_ne_one' ℝ)] at h3
  set n := s.card with hn
  let e := s.orderEmbOfFin (k := n) rfl
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : ∀ p, min p m < n := fun p => by omega
  let t : ℕ → ℝ := fun p => e ⟨min p m, hb p⟩
  have hmem : ∀ i, e i ∈ T := fun i => by
    have : e i ∈ s := Finset.orderEmbOfFin_mem s rfl i
    simpa [hs] using this
  have hmin : ∀ x ∈ T, t 0 ≤ x := fun x hx => by
    obtain ⟨i, rfl⟩ : x ∈ range e := by
      rw [Finset.range_orderEmbOfFin]
      simpa [hs] using hx
    refine e.monotone ?_
    simp [Fin.le_def]
  have hmax : ∀ x ∈ T, x ≤ t m := fun x hx => by
    obtain ⟨i, rfl⟩ : x ∈ range e := by
      rw [Finset.range_orderEmbOfFin]
      simpa [hs] using hx
    refine e.monotone ?_
    simp only [Fin.le_def, min_self]
    omega
  refine ⟨m, t, by omega, ?_, ?_, ?_, fun p _ => hmem _, ?_, ?_⟩
  · exact le_antisymm (hmin 0 h0) (hsub (hmem _)).1
  · exact le_antisymm (hsub (hmem _)).2 (hmax 1 h1)
  · intro p hp
    refine e.strictMono ?_
    simp only [Fin.lt_def]
    omega
  · rintro p hp x hx ⟨h2, h3⟩
    obtain ⟨i, rfl⟩ : x ∈ range e := by
      rw [Finset.range_orderEmbOfFin]
      simpa [hs] using hx
    have h4 := e.lt_iff_lt.mp h2
    have h5 := e.lt_iff_lt.mp h3
    simp only [Fin.lt_def] at h4 h5
    omega
  · intro x hx
    obtain ⟨i, rfl⟩ : x ∈ range e := by
      rw [Finset.range_orderEmbOfFin]
      simpa [hs] using hx
    refine ⟨i, by omega, ?_⟩
    simp only [t]
    congr 1
    ext
    simp
    omega

variable {X : Type u} [TopologicalSpace X] [T2Space X] {V : Set X} {E : Set (Set X)}

/-- A connected set off the vertices lies in one edge. -/
theorem IsGraph.subset_edge (hg : IsGraph V E) {J : Set X} (hJ : IsPreconnected J) (hG : J ⊆ ⋃₀ E)
  (hV : Disjoint J V)
    {e : Set X} (he : e ∈ E) (hm : (J ∩ e).Nonempty) : J ⊆ e := by
  classical
  have hcl : ∀ f ∈ E, IsClosed f := fun f hf => by
    obtain ⟨u, v, -, hl, -⟩ := hg.edge f hf
    exact hl.isCompact.isClosed
  have h2 : IsClosed (⋃₀ (E \ {e})) := (hg.fine.subset sdiff_subset).isClosed_sUnion fun f hf
    => hcl f hf.1
  by_contra hcon
  obtain ⟨z, hz, hz'⟩ := not_subset.mp hcon
  obtain ⟨f, hf, hzf⟩ := hG hz
  have hfe : f ≠ e := fun h => hz' (h ▸ hzf)
  obtain ⟨y, hy, hy1, ⟨g, hg', hyg⟩⟩ := isPreconnected_closed_iff.mp hJ _ _ (hcl e he) h2
    (fun w hw => by
      obtain ⟨f', hf', hw'⟩ := hG hw
      by_cases h : f' = e
      · exact .inl (h ▸ hw')
      · exact .inr ⟨f', ⟨hf', h⟩, hw'⟩) (by
      obtain ⟨w, hw, hw'⟩ := hm
      exact ⟨w, hw, hw'⟩) ⟨z, hz, f, ⟨hf, hfe⟩, hzf⟩
  exact Set.disjoint_left.mp hV hy (hg.disj e he g hg'.1 (Ne.symm hg'.2) ⟨hy1, hyg⟩)

/-- A connected set in an arc that contains both ends is the whole arc. -/
theorem IsLineWithEnds.eq_of_subset {L J : Set X} {u v : X} (hl : IsLineWithEnds L u v)
  (hJ : IsPreconnected J)
    (hs : J ⊆ L) (hu : u ∈ J) (hv : v ∈ J) : J = L := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  refine subset_antisymm hs ?_
  have hemb : IsEmbedding a := (ha.1.isClosedEmbedding ha.2).isEmbedding
  have hpc : IsPreconnected (a ⁻¹' J) := by
    refine hemb.isInducing.isPreconnected_image.mp ?_
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hs]
    exact hJ
  rintro _ ⟨t, rfl⟩
  exact hpc.ordConnected.out hu hv ⟨unitInterval.nonneg t, unitInterval.le_one t⟩

omit [T2Space X] in
/-- The circle `P` as a loop on the unit interval from a given point of `P`. -/
theorem IsOArc.exists_iota {P : Set X} (hP : IsOArc P) {v : X} (hv : v ∈ P) :
    ∃ ι : ℝ → X, Continuous ι ∧ ι 0 = v ∧ ι 1 = v ∧ InjOn ι (Ico 0 1) ∧ InjOn ι (Ioc 0 1)
      ∧ ι '' Ico 0 1 = P := by
  obtain ⟨φ⟩ := id hP
  obtain ⟨θ0, hθ0⟩ : ∃ θ : ℝ, Circle.exp θ = φ.symm ⟨v, hv⟩ := ⟨Complex.arg _, Circle.exp_arg _⟩
  let ι : ℝ → X := fun t => (φ (Circle.exp (θ0 + 2 * Real.pi * t))).1
  have hpi := Real.pi_pos
  have hinj : ∀ x y : ℝ, |x - y| < 1 → ι x = ι y → x = y := fun x y hxy he => by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (φ.injective (Subtype.ext he))
    have h1 : x - y = m := by
      have h2 : (2 * Real.pi) * (x - y) = (2 * Real.pi) * m := by linarith
      exact mul_left_cancel₀ (by positivity) h2
    rw [h1] at hxy
    have h3 : |m| < 1 := by exact_mod_cast hxy
    have h4 : m = 0 := Int.abs_lt_one_iff.mp h3
    rw [h4] at h1
    simp only [Int.cast_zero] at h1
    linarith
  have h0 : ι 0 = v := by
    simp only [ι, mul_zero, add_zero, hθ0]
    simp
  have h1 : ι 1 = v := by
    have : Circle.exp (θ0 + 2 * Real.pi * 1) = Circle.exp θ0 := by
      rw [mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one]
    simp only [ι, this, hθ0]
    simp
  refine ⟨ι, ?_, h0, h1, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (φ.continuous.comp (Circle.exp.continuous.comp (by fun_prop)))
  · intro x hx y hy he
    exact hinj x y (abs_lt.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩) he
  · intro x hx y hy he
    exact hinj x y (abs_lt.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩) he
  · ext z
    constructor
    · rintro ⟨t, -, rfl⟩
      exact (φ _).2
    · intro hz
      obtain ⟨t, ht, e⟩ := exists_circle_angle (Circle.exp θ0) (φ.symm ⟨z, hz⟩)
      rw [← Circle.exp_add] at e
      refine ⟨t / (2 * Real.pi), ⟨by have := ht.1; positivity, ?_⟩, ?_⟩
      · rw [div_lt_one (by positivity)]
        exact ht.2
      · simp only [ι]
        rw [show 2 * Real.pi * (t / (2 * Real.pi)) = t by field_simp, ← e]
        simp

/-- The consecutive vertex preimages of a parametrized graph arc bound entire oriented edges.
For a loop, the presence of an interior vertex excludes the interval with equal endpoints. -/
theorem IsGraph.exists_edge_intervals (hg : IsGraph V E) (A : Set X → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1})
    {ι : ℝ → X} (hιc : Continuous ι) (hinj : InjOn ι (Ico 0 1)) (hinj' : InjOn ι (Ioc 0 1))
    (hG : ι '' Icc 0 1 ⊆ gr V E) (h0 : ι 0 ∈ V) (h1 : ι 1 ∈ V)
    (hne : ι 0 ≠ ι 1 ∨ ∃ x ∈ Ioo (0 : ℝ) 1, ι x ∈ V) :
    ∃ (m : ℕ) (t : ℕ → ℝ) (s : ℕ → Set X) (ε : ℕ → Bool), 0 < m ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ p < m, t p < t (p + 1)) ∧
      (∀ p ≤ m, t p ∈ Icc (0 : ℝ) 1 ∩ ι ⁻¹' V) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ∩ ι ⁻¹' V, ∃ p ≤ m, t p = x) ∧
      ∀ p < m, s p ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = s p ∧
        ι (t p) = extI (A (s p)) (if ε p then 0 else 1) ∧
        ι (t (p + 1)) = extI (A (s p)) (if ε p then 1 else 0) := by
  classical
  have hcl : ∀ f ∈ E, IsClosed f := fun f hf => by
    obtain ⟨u, v, -, hl, -⟩ := hg.edge f hf
    exact hl.isCompact.isClosed
  have hline : ∀ e ∈ E, IsLineWithEnds e (A e 0) (A e 1) := fun e he => by
    have := (hA e he).1.isLineWithEnds
    rwa [(hA e he).2.1] at this
  let T : Set ℝ := Icc 0 1 ∩ ι ⁻¹' V
  have hTf : T.Finite := by
    have h1 : (Ico 0 1 ∩ ι ⁻¹' V : Set ℝ).Finite :=
      Set.Finite.of_finite_image (hg.fin.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
        (hinj.mono inter_subset_left)
    refine (h1.union (finite_singleton (1 : ℝ))).subset ?_
    rintro x ⟨hx, hxV⟩
    rcases eq_or_lt_of_le hx.2 with rfl | h2
    · exact .inr rfl
    · exact .inl ⟨⟨hx.1, h2⟩, hxV⟩
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, h0⟩
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  obtain ⟨m, t, hm, ht0, htm, hlt, hmem, hgap, hall⟩ := exists_sorted hTf inter_subset_left h0T h1T
  have key : ∀ p, ∃ (e : Set X) (b : Bool), p < m → e ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = e ∧
      ι (t p) = extI (A e) (if b then 0 else 1) ∧ ι (t (p + 1)) = extI (A e) (if b then 1 else 0)
        := by
    intro p
    by_cases hp : p < m
    swap
    · exact ⟨∅, true, fun h => absurd h hp⟩
    have hab := hlt p hp
    have ha1 := hmem p hp.le
    have hb1 := hmem (p + 1) hp
    have hopen : ∀ x ∈ Ioo (t p) (t (p + 1)), ι x ∉ V := fun x hx hxV =>
      hgap p hp x ⟨⟨ha1.1.1.trans hx.1.le, hx.2.le.trans hb1.1.2⟩, hxV⟩ hx
    have hsubI : Ioo (t p) (t (p + 1)) ⊆ Icc 0 1 := fun x hx => ⟨ha1.1.1.trans hx.1.le,
      hx.2.le.trans hb1.1.2⟩
    have hJP : ι '' Ioo (t p) (t (p + 1)) ⊆ ι '' Icc 0 1 := image_mono hsubI
    have hconn : IsPreconnected (ι '' Ioo (t p) (t (p + 1))) := isPreconnected_Ioo.image _
      hιc.continuousOn
    have hdisj : Disjoint (ι '' Ioo (t p) (t (p + 1))) V := Set.disjoint_left.mpr fun z hz hzV => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact hopen x hx hzV
    obtain ⟨x0, hx0⟩ : (Ioo (t p) (t (p + 1))).Nonempty := nonempty_Ioo.mpr hab
    have hJG : ι '' Ioo (t p) (t (p + 1)) ⊆ ⋃₀ E := fun z hz =>
      (hG (hJP hz)).resolve_left (Set.disjoint_left.mp hdisj hz)
    obtain ⟨e, he, hxe⟩ := hJG (mem_image_of_mem ι hx0)
    have hJe := hg.subset_edge hconn hJG hdisj he ⟨_, mem_image_of_mem ι hx0, hxe⟩
    have hIe : ι '' Icc (t p) (t (p + 1)) ⊆ e := by
      rw [← closure_Ioo hab.ne]
      exact (image_closure_subset_closure_image hιc).trans (closure_minimal hJe (hcl e he))
    have hea : ι (t p) ∈ e ∩ V := ⟨hIe ⟨_, ⟨le_rfl, hab.le⟩, rfl⟩, ha1.2⟩
    have heb : ι (t (p + 1)) ∈ e ∩ V := ⟨hIe ⟨_, ⟨hab.le, le_rfl⟩, rfl⟩, hb1.2⟩
    have hne' : ι (t p) ≠ ι (t (p + 1)) := by
      intro he'
      have ha0 : t p = 0 := by
        by_contra hc
        have h1 : t p ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ha1.1.1 (Ne.symm hc), ha1.1.2⟩
        exact hab.ne (hinj' h1 ⟨ha1.1.1.trans_lt hab, hb1.1.2⟩ he')
      have hb2 : t (p + 1) = 1 := by
        by_contra hc
        have h1 : t (p + 1) ∈ Ico (0 : ℝ) 1 := ⟨hb1.1.1, lt_of_le_of_ne hb1.1.2 hc⟩
        exact hab.ne (hinj ⟨ha1.1.1, hab.trans h1.2⟩ h1 he')
      rw [ha0, hb2] at he' hopen
      rcases hne with h3 | ⟨x, hx, hxV⟩
      · exact h3 he'
      · exact hopen x hx hxV
    have hpair : e ∩ V = {A e 0, A e 1} := (hA e he).2.2
    rw [hpair] at hea heb
    have hval0 : extI (A e) 0 = A e 0 := extI_coe (A e) 0
    have hval1 : extI (A e) 1 = A e 1 := extI_coe (A e) 1
    have hconnI : IsPreconnected (ι '' Icc (t p) (t (p + 1))) := isPreconnected_Icc.image _
      hιc.continuousOn
    rcases hea with hea | hea <;> rcases heb with heb | heb
    · exact absurd (hea.trans heb.symm) hne'
    · have heb' : ι (t (p + 1)) = A e 1 := heb
      refine ⟨e, true, fun _ => ⟨he, ?_, by simp [hea, hval0], by simp [heb', hval1]⟩⟩
      exact (hline e he).eq_of_subset hconnI hIe ⟨_, ⟨le_rfl, hab.le⟩, hea⟩ ⟨_, ⟨hab.le, le_rfl⟩,
        heb⟩
    · have hea' : ι (t p) = A e 1 := hea
      refine ⟨e, false, fun _ => ⟨he, ?_, by simp [hea', hval1], by simp [heb, hval0]⟩⟩
      exact (hline e he).eq_of_subset hconnI hIe ⟨_, ⟨hab.le, le_rfl⟩, heb⟩ ⟨_, ⟨le_rfl, hab.le⟩,
        hea⟩
    · exact absurd (hea.trans heb.symm) hne'
  choose s ε hs using key
  exact ⟨m, t, s, ε, hm, ht0, htm, hlt, hmem, hall, hs⟩

/-- The sides of the loop around `P`, before gluing them. -/
theorem exists_edge_sides (hg : IsGraph V E) {P : Set X} (hP : IsOArc P) (hPG : P ⊆ ⋃₀ E)
  (A : Set X → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) :
    ∃ (ι : ℝ → X) (m : ℕ) (t : ℕ → ℝ) (s : ℕ → Set X) (ε : ℕ → Bool), Continuous ι ∧ 0 < m ∧ t 0
      = 0 ∧ t m = 1 ∧
      (∀ p < m, t p < t (p + 1)) ∧ ι 0 = ι 1 ∧ InjOn ι (Ico 0 1) ∧ ι '' Ico 0 1 = P ∧
      ∀ p < m, s p ∈ E ∧ s p ⊆ P ∧ ι (t p) = extI (A (s p)) (if ε p then 0 else 1) ∧
        ι (t (p + 1)) = extI (A (s p)) (if ε p then 1 else 0) ∧ ι '' Icc (t p) (t (p + 1)) = s p
          := by
  classical
  have hPg : P ⊆ gr V E := hPG.trans subset_union_right
  have hends : ∀ e ∈ E, A e 0 ≠ A e 1 := fun e he he' => by
    have h1 := (hA e he).1.2 he'
    exact zero_ne_one h1
  have hline : ∀ e ∈ E, IsLineWithEnds e (A e 0) (A e 1) := fun e he => by
    have := (hA e he).1.isLineWithEnds
    rwa [(hA e he).2.1] at this
  have hmemV0 : ∀ e ∈ E, A e 0 ∈ V := fun e he => by
    have : A e 0 ∈ e ∩ V := (hA e he).2.2 ▸ mem_insert _ _
    exact this.2
  have hmemV1 : ∀ e ∈ E, A e 1 ∈ V := fun e he => by
    have : A e 1 ∈ e ∩ V := (hA e he).2.2 ▸ mem_insert_of_mem _ rfl
    exact this.2
  obtain ⟨v0, hv0P, hv0V⟩ : ∃ v ∈ P, v ∈ V := by
    obtain ⟨φ⟩ := id hP
    obtain ⟨e, he, hxe⟩ := hPG (φ 1).2
    by_cases hx : (φ 1).1 ∈ V
    · exact ⟨_, (φ 1).2, hx⟩
    · rcases hg.edge_or hP hPg he with h1 | h1
      · exact ⟨A e 0, h1 ((hline e he).left_mem), hmemV0 e he⟩
      · exact absurd (φ 1).2 (Set.disjoint_left.mp h1 ⟨hxe, hx⟩)
  obtain ⟨ι, hιc, hι0, hι1, hinj, hinj', hιim⟩ := hP.exists_iota hv0P
  have hIcc : ι '' Icc 0 1 = P := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases eq_or_lt_of_le hx.2 with rfl | h1
      · rw [hι1]
        exact hv0P
      · exact hιim ▸ mem_image_of_mem ι ⟨hx.1, h1⟩
    · exact hιim ▸ image_mono Ico_subset_Icc_self
  have hinterior : ∃ x ∈ Ioo (0 : ℝ) 1, ι x ∈ V := by
    have hmid : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
    have hmidP : ι (1 / 2) ∈ P := hIcc ▸ mem_image_of_mem ι (Ioo_subset_Icc_self hmid)
    by_cases hmidV : ι (1 / 2) ∈ V
    · exact ⟨1 / 2, hmid, hmidV⟩
    obtain ⟨e, he, hme⟩ := hPG hmidP
    have heP : e ⊆ P := by
      rcases hg.edge_or hP hPg he with heP | hdisjoint
      · exact heP
      · exact (Set.disjoint_left.mp hdisjoint ⟨hme, hmidV⟩ hmidP).elim
    obtain ⟨w, hwP, hwV, hwne⟩ : ∃ w ∈ P, w ∈ V ∧ w ≠ v0 := by
      by_cases h : A e 0 = v0
      · exact ⟨A e 1, heP (hline e he).right_mem, hmemV1 e he,
          fun h' => hends e he (h.trans h'.symm)⟩
      · exact ⟨A e 0, heP (hline e he).left_mem, hmemV0 e he, h⟩
    rw [← hιim] at hwP
    obtain ⟨x, hx, rfl⟩ := hwP
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm fun h => hwne (h ▸ hι0)), hx.2⟩, hwV⟩
  obtain ⟨m, t, s, ε, hm, ht0, htm, hlt, hmem, _, hs⟩ :=
    hg.exists_edge_intervals A hA hιc hinj hinj' (hIcc.symm ▸ hPg)
      (hι0.symm ▸ hv0V) (hι1.symm ▸ hv0V) (Or.inr hinterior)
  refine ⟨ι, m, t, s, ε, hιc, hm, ht0, htm, hlt, hι0.trans hι1.symm, hinj, hιim,
    fun p hp => ?_⟩
  obtain ⟨he, himage, hleft, hright⟩ := hs p hp
  refine ⟨he, ?_, hleft, hright, himage⟩
  rw [← himage, ← hIcc]
  exact image_mono (Icc_subset_Icc (hmem p hp.le).1.1 (hmem (p + 1) hp).1.2)

/-- The side of the edge with arc `a`, in the direction of `b`, with parameter `x ∈ [0, 1]`. -/
noncomputable def sd (a : 𝕀 → X) (b : Bool) (x : ℝ) : X := extI a (if b then x else 1 - x)

omit [T2Space X] in
theorem continuous_sd {a : 𝕀 → X} (ha : Continuous a) (b : Bool) : Continuous (sd a b) := by
  have h : Continuous fun x : ℝ => if b then x else 1 - x := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact (continuous_extI ha).comp h

omit [TopologicalSpace X] [T2Space X] in
theorem sd_true (a : 𝕀 → X) (x : ℝ) : sd a true x = extI a x := by simp [sd]

omit [TopologicalSpace X] [T2Space X] in
theorem sd_false (a : 𝕀 → X) (x : ℝ) : sd a false x = extI a (1 - x) := by simp [sd]

omit [TopologicalSpace X] [T2Space X] in
theorem sd_mem (a : 𝕀 → X) (b : Bool) {x : ℝ} : sd a b x ∈ range a := ⟨_, rfl⟩

/-- Going around `P` is a cyclic list of whole edges, with no edge and no corner repeated. -/
theorem exists_edge_walk (hg : IsGraph V E) {P : Set X} (hP : IsOArc P) (hPG : P ⊆ ⋃₀ E) (A : Set X
  → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) :
    ∃ (m : ℕ) (s : ℕ → Set X) (ε : ℕ → Bool), 0 < m ∧ (∀ p < m, s p ∈ E ∧ s p ⊆ P)
      ∧ P ⊆ ⋃ p ∈ Iio m, s p ∧
      (∀ p, p + 1 < m → sd (A (s p)) (ε p) 1 = sd (A (s (p + 1))) (ε (p + 1)) 0) ∧
      sd (A (s (m - 1))) (ε (m - 1)) 1 = sd (A (s 0)) (ε 0) 0 ∧
      ∀ p < m, ∀ q < m, p ≠ q → s p ≠ s q ∧ sd (A (s p)) (ε p) 0 ≠ sd (A (s q)) (ε q) 0 := by
  classical
  obtain ⟨ι, m, t, s, ε, hιc, hm, ht0, htm, hlt, hι01, hinj, hιim, hs⟩
    := exists_edge_sides hg hP hPG A hA
  have hstart : ∀ p < m, sd (A (s p)) (ε p) 0 = ι (t p) := fun p hp => by
    rw [(hs p hp).2.2.1]
    cases ε p <;> simp [sd]
  have hend : ∀ p < m, sd (A (s p)) (ε p) 1 = ι (t (p + 1)) := fun p hp => by
    rw [(hs p hp).2.2.2.1]
    cases ε p <;> simp [sd]
  have hmono : StrictMonoOn t (Iic m) := by
    intro p hp q hq hpq
    induction q, hpq using Nat.le_induction with
    | base => exact hlt p hq
    | succ q hq' ih => exact (ih (Nat.le_of_succ_le hq)).trans (hlt q hq)
  have ht01 : ∀ p ≤ m, t p ∈ Icc (0 : ℝ) 1 := fun p hp => by
    constructor
    · rcases Nat.eq_zero_or_pos p with rfl | h
      · exact ht0.ge
      · rw [← ht0]
        exact (hmono (by simp) hp h).le
    · rcases eq_or_lt_of_le hp with rfl | h
      · exact htm.le
      · rw [← htm]
        exact (hmono hp (by simp) h).le
  have hlt1 : ∀ p < m, t p < 1 := fun p hp => by
    rw [← htm]
    exact hmono hp.le (by simp) hp
  refine ⟨m, s, ε, hm, fun p hp => ⟨(hs p hp).1, (hs p hp).2.1⟩, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hιim.symm ▸ hy
    have hexists : ∃ p < m, x ∈ Icc (t p) (t (p + 1)) := by
      by_contra hcon
      push Not at hcon
      have key : ∀ p ≤ m, t p ≤ x := by
        intro p
        induction p with
        | zero => exact fun _ => ht0.le.trans hx.1
        | succ p ih =>
          intro hp
          have h1 := ih (by omega)
          by_contra h2
          exact hcon p (by omega) ⟨h1, (not_le.mp h2).le⟩
      have := key m le_rfl
      rw [htm] at this
      exact absurd hx.2 (not_lt.mpr this)
    obtain ⟨p, hp, hxp⟩ := hexists
    exact mem_biUnion (show p ∈ Iio m from hp) ((hs p hp).2.2.2.2 ▸ mem_image_of_mem ι hxp)
  · intro p hp
    rw [hend p (by omega), hstart (p + 1) hp]
  · have h1 : m - 1 + 1 = m := by omega
    rw [hend (m - 1) (by omega), h1, hstart 0 hm, htm, ht0, hι01]
  · intro p hp q hq hpq
    have hval : ∀ p q, p < m → q < m → p < q → s p ≠ s q ∧ ι (t p) ≠ ι (t q) := by
      intro p q hp hq hpq
      have htpq : t p < t q := hmono hp.le hq.le hpq
      have hne2 : ι (t p) ≠ ι (t q) := fun he =>
        htpq.ne (hinj ⟨(ht01 p hp.le).1, hlt1 p hp⟩ ⟨(ht01 q hq.le).1, hlt1 q hq⟩ he)
      refine ⟨fun he => ?_, hne2⟩
      obtain ⟨x, hx⟩ : (Ioo (t q) (t (q + 1))).Nonempty := nonempty_Ioo.mpr (hlt q hq)
      have hxI : x ∈ Ico (0 : ℝ) 1 := ⟨(ht01 q hq.le).1.trans hx.1.le, hx.2.trans_le (ht01 _ hq).2⟩
      have h1 : ι x ∈ s q := (hs q hq).2.2.2.2 ▸ mem_image_of_mem ι (Ioo_subset_Icc_self hx)
      rw [← he, ← (hs p hp).2.2.2.2] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hple : t (p + 1) ≤ t q := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpq) with h | h
        · rw [Nat.succ_eq_add_one] at h
          rw [h]
        · exact (hmono hp hq.le h).le
      rcases eq_or_lt_of_le ((ht01 _ hp).2.trans' hy.2) with hy1 | hy1
      · have h3 : ι 0 = ι x := by rw [hι01, ← hyx, hy1]
        have h4 := hinj ⟨le_rfl, one_pos⟩ hxI h3
        have h5 : 0 < x := (ht01 q hq.le).1.trans_lt hx.1
        exact h5.ne h4
      · have h3 := hinj ⟨(ht01 p hp.le).1.trans hy.1, hy1⟩ hxI hyx
        have h4 := hx.1
        rw [← h3] at h4
        exact absurd (hy.2.trans hple) (not_le.mpr h4)
    rw [hstart p hp, hstart q hq]
    rcases lt_or_gt_of_ne hpq with h | h
    · exact hval p q hp hq h
    · exact ⟨(hval q p hq hp h).1.symm, (hval q p hq hp h).2.symm⟩

omit [T2Space X] in
/-- The closed curve that goes along the sides of a cyclic list of edges, at unit speed. -/
noncomputable def walkMap (m : ℕ) (a : ℕ → 𝕀 → X) (b : ℕ → Bool) (x : ℝ) : X :=
  sd (a (min ⌊x⌋₊ (m - 1))) (b (min ⌊x⌋₊ (m - 1))) (x - min ⌊x⌋₊ (m - 1))

section walk

variable {m : ℕ} {a : ℕ → 𝕀 → X} {b : ℕ → Bool}

omit [TopologicalSpace X] [T2Space X] in
theorem walkMap_eq (hm : 0 < m) (hadj : ∀ p, p + 1 < m → sd (a p) (b p) 1 = sd (a (p + 1)) (b
  (p + 1)) 0) {p : ℕ}
    (hp : p < m) {x : ℝ} (hx : x ∈ Icc (p : ℝ) (p + 1)) : walkMap m a b x = sd (a p) (b p) (x - p)
      := by
  have h0 : (0 : ℝ) ≤ x := (Nat.cast_nonneg p).trans hx.1
  rcases eq_or_lt_of_le hx.2 with he | hl
  · have hf : ⌊x⌋₊ = p + 1 := by
      rw [he]
      exact_mod_cast Nat.floor_natCast (R := ℝ) (p + 1)
    by_cases h1 : p + 1 < m
    · have hmin : min ⌊x⌋₊ (m - 1) = p + 1 := by omega
      simp only [walkMap, hmin]
      have e1 : x - ((p + 1 : ℕ) : ℝ) = 0 := by
        push_cast
        linarith
      have e2 : x - p = 1 := by linarith
      rw [e1, e2]
      exact (hadj p h1).symm
    · have hmin : min ⌊x⌋₊ (m - 1) = p := by omega
      simp only [walkMap, hmin]
  · have hf : ⌊x⌋₊ = p := (Nat.floor_eq_iff h0).mpr ⟨hx.1, hl⟩
    have hmin : min ⌊x⌋₊ (m - 1) = p := by omega
    simp only [walkMap, hmin]

omit [T2Space X] in
theorem continuousOn_walkMap (hm : 0 < m) (ha : ∀ p < m, Continuous (a p))
    (hadj : ∀ p, p + 1 < m → sd (a p) (b p) 1 = sd (a (p + 1)) (b (p + 1)) 0) :
    ContinuousOn (walkMap m a b) (Icc 0 m) := by
  have key : ∀ k ≤ m, ContinuousOn (walkMap m a b) (Icc 0 k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have h1 : Icc (0 : ℝ) ((k + 1 : ℕ) : ℝ) = Icc (0 : ℝ) (k : ℝ) ∪ Icc (k : ℝ) ((k : ℝ) + 1)
        := by
        push_cast
        rw [Icc_union_Icc_eq_Icc (by positivity) (by linarith)]
      rw [h1]
      refine (ih (by omega)).union_of_isClosed ?_ isClosed_Icc isClosed_Icc
      have hc : Continuous fun x : ℝ => sd (a k) (b k) (x - k) :=
        (continuous_sd (ha k hk) _).comp (by fun_prop)
      exact hc.continuousOn.congr fun x hx => walkMap_eq hm hadj hk hx
  exact key m le_rfl

end walk

end GraphMinor.Surface
