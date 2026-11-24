/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Sides
public import LeanPool.GraphMinor.GM11.Section810
public import LeanPool.GraphMinor.GM11.RadialAccess

/-!
# Graph Minors XII, Section 6: the regions `r_0, …, r_k`

"Since $\Gamma_1$ is 2-cell it follows that $r_0, r_1, \dots, r_{\theta/2}$ are all distinct." The
paper gives no more.
`no_bypass` fills this in. Suppose a path joins the two sides of a chord and misses the chord. A
part
of it runs outside `Δ` between two points of `F`, one on each of the two arcs of `F` at the chord.
Close this part up by a chord of `Δ`. This gives an `O`-arc inside one region of `Γ₁`, so it bounds
a
closed disc in this region, as the region is an open disc. The new chord cuts `Δ` in two, and each
side holds an end of the old chord. One side lies in the closed disc, and this is impossible since
the ends of the old chord are vertices of `Γ₁`.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Two disjoint closed sets of `[0, 1]`, one with `0` and one with `1`, have a gap between them. -/
theorem exists_crossing {T T' : Set 𝕀} (hT : IsClosed T) (hT' : IsClosed T') (hd : Disjoint T T')
    (h0 : (0 : 𝕀) ∈ T) (h1 : (1 : 𝕀) ∈ T') :
    ∃ s s' : 𝕀, s < s' ∧ s ∈ T ∧ s' ∈ T' ∧ ∀ t, s < t → t < s' → t ∉ T ∧ t ∉ T' := by
  have hne' : T'.Nonempty := ⟨1, h1⟩
  let s' := sInf T'
  have hs' : s' ∈ T' := hT'.csInf_mem hne' (OrderBot.bddBelow _)
  let A := T ∩ Iic s'
  have hAc : IsClosed A := hT.inter isClosed_Iic
  have hne : A.Nonempty := ⟨0, h0, show (⊥ : 𝕀) ≤ s' from bot_le⟩
  let s := sSup A
  have hs : s ∈ A := hAc.csSup_mem hne (OrderTop.bddAbove _)
  have hlt : s < s' := by
    refine lt_of_le_of_ne hs.2 fun he => ?_
    have h2 : s ∈ T' := by
      have : s = s' := he
      rw [this]
      exact hs'
    exact Set.disjoint_left.mp hd hs.1 h2
  refine ⟨s, s', hlt, hs.1, hs', fun t h3 h4 => ⟨fun hx => ?_, fun hy => ?_⟩⟩
  · exact not_le.mpr h3 (le_csSup (OrderTop.bddAbove A) (show t ∈ A from ⟨hx, h4.le⟩))
  · exact not_le.mpr h4 (csInf_le (OrderBot.bddBelow T') hy)

private theorem opposite_side_arc_meets_disc_only_at_ends
    {S : Type u}
    [TopologicalSpace S]
    {Δ : Set S}
    {X : Set S}
    {Y : Set S}
    (hu : X ∪ Y = Δ)
    {p : S}
    {q : S}
    (c : Path p q)
    (s : 𝕀)
    (s' : 𝕀)
    (hgap : ∀ (t : 𝕀), s < t → t < s' → t ∉ ⇑c ⁻¹' X ∧ t ∉ ⇑c ⁻¹' Y)
    (hsn : ↑s < ↑s')
    (u : 𝕀 → 𝕀) (huval : ∀ t : 𝕀, (u t).1 = s.1 + t.1 * (s'.1 - s.1))
    (n : S)
    (m : S)
    (hδ0 : c (u 0) = n)
    (hδ1 : c (u 1) = m)
    (e : 𝕀 → S)
    (hrng : range e ⊆ range (fun t => c (u t))) :
    ∀ z ∈ range e, z ∈ Δ → z = n ∨ z = m := by
  intro z hz hzΔ
  obtain ⟨t, rfl⟩ := hrng hz
  by_cases h0 : t = 0
  · exact .inl (h0.symm ▸ hδ0)
  by_cases h1 : t = 1
  · exact .inr (h1.symm ▸ hδ1)
  exfalso
  have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun he => h0 (Subtype.ext he.symm)
  have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun he => h1 (Subtype.ext he)
  have hd : 0 < s'.1 - s.1 := sub_pos.mpr hsn
  have h3 : s < u t := by
    change s.1 < (u t).1
    rw [huval]
    nlinarith
  have h4 : u t < s' := by
    change (u t).1 < s'.1
    rw [huval]
    nlinarith
  obtain ⟨h5, h6⟩ := hgap _ h3 h4
  have hz : c (u t) ∈ X ∪ Y := by
    rw [hu]
    exact hzΔ
  rcases hz with hz | hz
  · exact h5 hz
  · exact h6 hz

/-- **No way around a chord.** See the module docstring. -/
theorem no_bypass (hS : IsClosedSurface S) {Δ F X Y A B R : Set S} {a b : S}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F) (hX : IsClosed X) (hY : IsClosed Y)
    (hu : X ∪ Y = Δ) (hi : X ∩ Y = R) (hAB : A ∪ B = F) (hABi : A ∩ B = {a, b})
    (hAc : IsClosed A) (hBc : IsClosed B) (hAX : A ⊆ X) (hBY : B ⊆ Y) {Γ₁ : Drawing S}
    (hdisc : ∀ r ∈ Γ₁.R, IsOpenDisc r)
    (hU : Γ₁.U ∩ Δ ⊆ F) (ha : a ∈ Γ₁.U) (hb : b ∈ Γ₁.U) {Z : Set S} (hZ : IsPathConnected Z)
    (hZR : Disjoint Z R) (hZU : Disjoint Z Γ₁.U) {p q : S} (hp : p ∈ Z) (hq : q ∈ Z) (hpX : p ∈ X)
    (hqY : q ∈ Y) : False := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfr : frontier Δ = F := by rw [IsClosedDisc.frontier_eq_discBd hS hΔ, hbd]
  have hXΔ : X ⊆ Δ := hu ▸ subset_union_left
  have hYΔ : Y ⊆ Δ := hu ▸ subset_union_right
  have hΔc : IsClosed Δ := hΔ.isClosed
  have hXYZ : ∀ {x : S}, x ∈ Z → x ∈ X → x ∈ Y → False := fun hz h1 h2 =>
    Set.disjoint_left.mp hZR hz (hi ▸ ⟨h1, h2⟩)
  have hoffU : ∀ {x : S}, x ∈ Z → x ∉ Γ₁.U := fun hz h1 => Set.disjoint_left.mp hZU hz h1
  obtain ⟨c, hc⟩ := hZ.joinedIn p hp q hq
  have hcc : Continuous c := c.continuous
  obtain ⟨s, s', hss, hsT, hsT', hgap⟩ := exists_crossing (hX.preimage hcc) (hY.preimage hcc)
    (Set.disjoint_left.mpr fun t h1 h2 => hXYZ (hc t) h1 h2)
    (by change c 0 ∈ X; rw [c.source]; exact hpX) (by change c 1 ∈ Y; rw [c.target]; exact hqY)
  have hsn : s.1 < s'.1 := hss
  let u : 𝕀 → 𝕀 := fun t => ⟨s.1 + t.1 * (s'.1 - s.1), by
    have h1 := s.2.1
    have h2 := t.2.1
    have := mul_nonneg h2 (sub_nonneg.mpr hsn.le)
    linarith, by
    have h1 := t.2.2
    have h2 := s'.2.2
    have := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hsn.le)
    linarith⟩
  have huc : Continuous u := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let δ : 𝕀 → S := fun t => c (u t)
  have hδ : Continuous δ := hcc.comp huc
  have hu0 : u 0 = s := Subtype.ext (by simp [u])
  have hu1 : u 1 = s' := Subtype.ext (by simp [u])
  set n := c s with hn
  set m := c s' with hm
  have hδ0 : δ 0 = n := by simp only [δ, hu0, hn]
  have hδ1 : δ 1 = m := by simp only [δ, hu1, hm]
  have hnZ : n ∈ Z := hc s
  have hmZ : m ∈ Z := hc s'
  have hnm : n ≠ m := fun he => hXYZ hnZ hsT (he ▸ hsT')
  obtain ⟨e, he, hei, he0, he1, hrng⟩ := exists_arc_of_path hδ (by rw [hδ0, hδ1]; exact hnm)
  rw [hδ0] at he0
  rw [hδ1] at he1
  have harc : IsArcMap e := ⟨he, hei⟩
  have hL : IsLineWithEnds (range e) n m := he0 ▸ he1 ▸ harc.isLineWithEnds
  have hLZ : range e ⊆ Z := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := hrng ⟨t, rfl⟩
    rw [← ht']
    exact hc _
  have hLΔ : ∀ z ∈ range e, z ∈ Δ → z = n ∨ z = m := by
    exact opposite_side_arc_meets_disc_only_at_ends (S := S) (Δ := Δ) (X := X) (Y := Y) hu (p :=
      p) (q := q) c s s' hgap hsn u (fun _ => rfl) n m hδ0 hδ1 e hrng
  have hLcl : closure (range e \ {n, m}) = range e := closure_sdiff_pair hL
  have hcomp : range e \ {n, m} ⊆ Δᶜ := fun z hz hzΔ => by
    rcases hLΔ z hz.1 hzΔ with rfl | rfl
    · exact hz.2 (.inl rfl)
    · exact hz.2 (.inr rfl)
  have honF : ∀ {z : S}, z ∈ Δ → z ∈ range e → z ∈ F := fun hz hzL => by
    rw [← hfr, frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hz, closure_mono hcomp (by rw [hLcl]; exact hzL)⟩
  have hnL : n ∈ range e := hL.left_mem
  have hmL : m ∈ range e := hL.right_mem
  have hnF : n ∈ F := honF (hXΔ hsT) hnL
  have hmF : m ∈ F := honF (hYΔ hsT') hmL
  have hnA : n ∈ A := by
    rcases (hAB ▸ hnF : n ∈ A ∪ B) with h | h
    · exact h
    · exact (hXYZ hnZ hsT (hBY h)).elim
  have hmB : m ∈ B := by
    rcases (hAB ▸ hmF : m ∈ A ∪ B) with h | h
    · exact (hXYZ hmZ (hAX h) hsT').elim
    · exact h
  have hnab : n ≠ a ∧ n ≠ b := ⟨fun h => hoffU hnZ (h ▸ ha), fun h => hoffU hnZ (h ▸ hb)⟩
  have hmab : m ≠ a ∧ m ≠ b := ⟨fun h => hoffU hmZ (h ▸ ha), fun h => hoffU hmZ (h ▸ hb)⟩
  obtain ⟨C₀, hC₀, hC₀Δ, hC₀F⟩ := chord_in_disc hΔ (hbd ▸ hnF) (hbd ▸ hmF) hnm
  rw [hbd] at hC₀F
  obtain ⟨e', harc', hr', he'0, he'1⟩ := hC₀.exists_arc
  have hO : IsOArc (range e ∪ C₀) := by
    rw [← hr']
    refine oArc_of_two_arcs harc harc' (by rw [he0, he'0]) (by rw [he1, he'1]) ?_
    intro t t' hee
    have hz : e t ∈ Δ := hC₀Δ (hr' ▸ (hee ▸ mem_range_self t'))
    rcases hLΔ _ ⟨t, rfl⟩ hz with h1 | h1
    · left
      refine ⟨hei (h1.trans he0.symm), harc'.2 ?_⟩
      rw [← hee, h1, he'0]
    · right
      refine ⟨hei (h1.trans he1.symm), harc'.2 ?_⟩
      rw [← hee, h1, he'1]
  have hC₀U : Disjoint C₀ Γ₁.U := by
    refine Set.disjoint_left.mpr fun x hx hxU => ?_
    have hxF : x ∈ F := hU ⟨hxU, hC₀Δ hx⟩
    have : x ∈ ({n, m} : Set S) := hC₀F ▸ ⟨hx, hxF⟩
    rcases this with rfl | rfl
    · exact hoffU hnZ hxU
    · exact hoffU hmZ hxU
  have hGU : Disjoint (range e ∪ C₀) Γ₁.U :=
    disjoint_union_left.mpr ⟨hZU.mono_left hLZ, hC₀U⟩
  have hGc : IsPreconnected (range e ∪ C₀) :=
    IsPreconnected.union n hnL hC₀.left_mem (line_conn hL) (line_conn hC₀)
  obtain ⟨r', hr'R, hnr'⟩ := exists_region_of_notMem (hoffU hnZ)
  have hsub : range e ∪ C₀ ⊆ r' := subset_region hr'R hGc hGU (Or.inl hnL) hnr'
  obtain ⟨E, hEr, hE, hEb⟩ := exists_disc_in_openDisc (hdisc r' hr'R) hO hsub
  have hoffE : ∀ {x : S}, x ∈ Γ₁.U → x ∉ E := fun hx hxE => region_subset hr'R (hEr hxE) hx
  obtain ⟨Δ₁, Δ₂, A₁, A₂, lA₁, lA₂, hAu, -, d₁, d₂, hun, -, hb₁, hb₂⟩ :=
    split_disc hΔ hC₀Δ hnm hC₀ (by rw [hbd]; exact hC₀F)
  have hAF : ∀ {A' : Set S}, A' ⊆ F → IsLineWithEnds A' n m → ∃ x ∈ A', x ∈ Γ₁.U := by
    intro A' hA' hl
    by_contra hc'
    push Not at hc'
    have hd : Disjoint A' (A ∩ B) := by
      rw [hABi]
      refine Set.disjoint_left.mpr ?_
      rintro x hx (rfl | rfl)
      · exact hc' _ hx ha
      · exact hc' _ hx hb
    rcases subset_side hAc hBc (line_conn hl) (by rw [hAB]; exact hA') hd with h1 | h1
    · have : m ∈ A ∩ B := ⟨h1 hl.right_mem, hmB⟩
      rw [hABi] at this
      rcases this with h | h
      · exact hmab.1 h
      · exact hmab.2 h
    · have : n ∈ A ∩ B := ⟨hnA, h1 hl.left_mem⟩
      rw [hABi] at this
      rcases this with h | h
      · exact hnab.1 h
      · exact hnab.2 h
  have hA₁F : A₁ ⊆ F := by rw [← hbd, ← hAu]; exact subset_union_left
  have hA₂F : A₂ ⊆ F := by rw [← hbd, ← hAu]; exact subset_union_right
  obtain ⟨c₁, hc₁, hc₁U⟩ := hAF hA₁F lA₁
  obtain ⟨c₂, hc₂, hc₂U⟩ := hAF hA₂F lA₂
  obtain ⟨z, hzC, hzn⟩ := line_mid hC₀
  have hzF : z ∉ F := fun h => hzn (hC₀F ▸ ⟨hzC, h⟩)
  have hzInt : z ∈ interior Δ := by
    by_contra hc'
    apply hzF
    rw [← hfr]
    exact ⟨subset_closure (hC₀Δ hzC), hc'⟩
  have hzE : z ∈ closure (discInt E) :=
    hE.subset_closure_discInt (GraphMinor.Surface.discBd_subset E (hEb ▸ Or.inr hzC))
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hzE _ isOpen_interior hzInt
  have hwΔ : w ∈ Δ := interior_subset hw1
  have hwF : w ∉ F := by
    rw [← hfr]
    exact fun h => h.2 hw1
  have hwC : w ∉ C₀ := fun h => hw2.2 (hEb ▸ Or.inr h)
  have key : ∀ {Δ' A' : Set S} {x : S}, IsClosedDisc Δ' → Δ' ⊆ Δ → discBd Δ' = A' ∪ C₀ → A' ⊆ F →
      w ∈ Δ' → x ∈ A' → x ∈ Γ₁.U → False := by
    intro Δ' A' x hd hsubΔ hbd' hA' hwΔ' hx hxU
    have hint : w ∈ discInt Δ' := ⟨hwΔ', by
      rw [hbd']
      rintro (h | h)
      · exact hwF (hA' h)
      · exact hwC h⟩
    have hdG : ∀ y ∈ discInt Δ', y ∉ discBd E := by
      intro y hy hyG
      rw [hEb] at hyG
      apply hy.2
      rw [hbd']
      rcases hyG with h | h
      · rcases hLΔ y h (hsubΔ hy.1) with rfl | rfl
        · exact .inr hC₀.left_mem
        · exact .inr hC₀.right_mem
      · exact .inr h
    have hdj : Disjoint (discInt E) Eᶜ :=
      Set.disjoint_left.mpr fun y h1 h2 => h2 h1.1
    have hcov : discInt Δ' ⊆ discInt E ∪ Eᶜ := by
      intro y hy
      by_cases hyE : y ∈ E
      · exact .inl ⟨hyE, hdG y hy⟩
      · exact .inr hyE
    rcases hd.isPreconnected_discInt.subset_or_subset (hE.isOpen_discInt hman)
      hE.isClosed.isOpen_compl hdj hcov with h1 | h1
    · have h2 : Δ' ⊆ E := hd.subset_closure_discInt.trans
        (closure_minimal (h1.trans sdiff_subset) hE.isClosed)
      have hxΔ' : x ∈ Δ' := GraphMinor.Surface.discBd_subset _ (hbd' ▸ Or.inl hx)
      exact hoffE hxU (h2 hxΔ')
    · exact h1 hint hw2.1
  have hwd : w ∈ Δ₁ ∪ Δ₂ := by rw [hun]; exact hwΔ
  rcases hwd with h1 | h1
  · exact key d₁ (hun ▸ subset_union_left) hb₁ hA₁F h1 hc₁ hc₁U
  · exact key d₂ (hun ▸ subset_union_right) hb₂ hA₂F h1 hc₂ hc₂U

/-- The drawing of (6.1): the facts on `Γ`, `F`, `Δ` and the paths `P_i`. -/
structure Setup61 (Γ : Drawing S) (F Δ : Set S) (k : ℕ) (a b : Fin k → S) (P : Fin k → Drawing S) :
    Prop where
  /-- `F` is `Γ`-normal. -/
  normal : Γ.IsNormal F
  /-- `Δ` is a closed disc. -/
  disc : IsClosedDisc Δ
  /-- `Δ` is bounded by `F`. -/
  bd : subBd Δ = F
  /-- The vertices on `F` are all different. -/
  nodup : (List.ofFn a ++ (List.ofFn b).reverse).Nodup
  /-- They are in order on `F`. -/
  order : IsListedInOrderOn F (List.ofFn a ++ (List.ofFn b).reverse)
  /-- They are all the vertices of `Γ` on `F`. -/
  verts : range a ∪ range b = F ∩ Γ.V
  /-- Each `P i` is a path from `a i` to `b i` in `Γ ∩ Δ`. -/
  path : ∀ i, (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet Δ)
  /-- The paths are disjoint. -/
  disj : Pairwise fun i j => Disjoint (P i).U (P j).U
  /-- The paths are all of `Γ ∩ Δ`. -/
  cover : (Γ.interSet Δ).U = ⋃ i, (P i).U

namespace Setup61

variable {Γ : Drawing S} {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S}

theorem ne (h : Setup61 Γ F Δ k a b P) (i : Fin k) : a i ≠ b i := by
  intro he
  have hd := (List.nodup_append.mp h.nodup).2.2
  exact hd (a i) (List.mem_ofFn.mpr ⟨i, rfl⟩) (b i) (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨i,
    rfl⟩)) he

theorem isSub (h : Setup61 Γ F Δ k a b P) (i : Fin k) : (P i).IsSubdrawing Γ :=
  (h.path i).2.trans interSet_isSub

theorem line (h : Setup61 Γ F Δ k a b P) (i : Fin k) : IsLineWithEnds (P i).U (a i) (b i) :=
  GM14.isLine_of_isPathBetween (h.path i).1 (h.ne i)

theorem U_sub (h : Setup61 Γ F Δ k a b P) (i : Fin k) : (P i).U ⊆ Δ :=
  (h.path i).2.U_subset.trans (interSet_U_subset h.disc.isClosed)

theorem a_mem (h : Setup61 Γ F Δ k a b P) (i : Fin k) : a i ∈ F ∩ Γ.V := by
  rw [← h.verts]
  exact .inl ⟨i, rfl⟩

theorem b_mem (h : Setup61 Γ F Δ k a b P) (i : Fin k) : b i ∈ F ∩ Γ.V := by
  rw [← h.verts]
  exact .inr ⟨i, rfl⟩

/-- A point of `U(P i)` on `F` is an end of `P i`. -/
theorem end_of_mem_F (h : Setup61 Γ F Δ k a b P) {i : Fin k} {x : S} (hx : x ∈ (P i).U)
    (hF : x ∈ F) : x = a i ∨ x = b i := by
  have hxV : x ∈ F ∩ Γ.V := ⟨hF, h.normal ⟨hF, (h.isSub i).U_subset hx⟩⟩
  rw [← h.verts] at hxV
  have same : ∀ j, x ∈ (P j).U → j = i := fun j hj => by
    by_contra hne
    exact Set.disjoint_left.mp (h.disj hne) hj hx
  rcases hxV with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [same j (h.line j).left_mem]
    exact .inl rfl
  · rw [same j (h.line j).right_mem]
    exact .inr rfl

/-- The lines `U(P i)` are chords of `Δ`. -/
theorem chords (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S) :
    Chords F Δ k a b fun i => (P i).U where
  disc := h.disc
  bd := by rw [← GraphMinor.GM14.IsClosedDisc.subBd_eq_discBd hS h.disc, h.bd]
  line := h.line
  sub := h.U_sub
  meet i := by
    refine subset_antisymm (fun x hx => h.end_of_mem_F hx.1 hx.2) ?_
    rintro _ (rfl | rfl)
    · exact ⟨(h.line i).left_mem, (h.a_mem i).1⟩
    · exact ⟨(h.line i).right_mem, (h.b_mem i).1⟩
  disj _ _ hij := h.disj hij
  ne := h.ne
  arcs i := exists_chord_arcs h.order i

/-- An edge of `Γ` that meets `Δ` lies in `Δ`, and is an edge of one of the paths. -/
theorem edge_mem (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S) {g : Set S} (hg : g ∈ Γ.E)
    (hm : (g ∩ Δ).Nonempty) : g ⊆ interior Δ ∧ ∃ i, g ∈ (P i).E := by
  have hc := h.disc.isClosed
  have hfr : frontier Δ = F := by
    rw [IsClosedDisc.frontier_eq_discBd hS h.disc, ← GraphMinor.GM14.IsClosedDisc.subBd_eq_discBd
      hS h.disc, h.bd]
  have hoff : ∀ y ∈ g, y ∉ F := fun y hy hyF =>
    edge_notMem_V hg hy (h.normal ⟨hyF, Γ.closure_subset_U hg (subset_closure hy)⟩)
  have hcov : g ⊆ interior Δ ∪ Δᶜ := by
    intro y hy
    by_cases hyΔ : y ∈ Δ
    · refine .inl ?_
      by_contra hn
      exact hoff y hy (hfr ▸ ⟨subset_closure hyΔ, hn⟩)
    · exact .inr hyΔ
  have hdj : Disjoint (interior Δ) Δᶜ :=
    Set.disjoint_left.mpr fun y h1 h2 => h2 (interior_subset h1)
  have hsub : g ⊆ interior Δ := by
    rcases hg.2.2.1.isConnected.isPreconnected.subset_or_subset isOpen_interior hc.isOpen_compl hdj
      hcov with h1 | h1
    · exact h1
    · obtain ⟨y, hy, hyΔ⟩ := hm
      exact (h1 hy hyΔ).elim
  refine ⟨hsub, ?_⟩
  have hgI : g ∈ (Γ.interSet Δ).E := mem_interSet_E_iff.mpr ⟨hg, hsub.trans interior_subset⟩
  obtain ⟨x, hx⟩ := hg.1
  have hxU : x ∈ (Γ.interSet Δ).U :=
    (Γ.interSet Δ).closure_subset_U hgI (subset_closure hx)
  rw [h.cover] at hxU
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
  have hxV : x ∉ (P i).V := fun hv => edge_notMem_V hg hx ((h.isSub i).1 hv)
  obtain ⟨e, he, hxe⟩ := (P i).exists_edge_of_mem hi hxV
  have : g = e := Γ.edge_eq_of_mem hg ((h.isSub i).2 he) hx hxe
  exact ⟨i, this ▸ he⟩

/-- Every point of `Γ` in `Δ` lies on a path. -/
theorem U_inter (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S) {x : S} (hx : x ∈ Γ.U)
    (hxΔ : x ∈ Δ) : ∃ i, x ∈ (P i).U := by
  by_cases hxV : x ∈ Γ.V
  · have : x ∈ (Γ.interSet Δ).U :=
      (Γ.interSet Δ).V_subset_U ((mem_interSet_V_iff h.disc.isClosed).mpr ⟨hxV, hxΔ⟩)
    rw [h.cover] at this
    exact mem_iUnion.mp this
  · obtain ⟨g, hg, hxg⟩ := Γ.exists_edge_of_mem hx hxV
    obtain ⟨-, i, hi⟩ := h.edge_mem hS hg ⟨x, hxg, hxΔ⟩
    exact ⟨i, (P i).closure_subset_U hi (subset_closure hxg)⟩

/-- An edge at an inner vertex of `P i` is an edge of `P i`. -/
theorem edge_at_inner (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S) {i : Fin k} {x : S}
    (hx : x ∈ (P i).U) (hxa : x ≠ a i) (hxb : x ≠ b i) {g : Set S} (hg : g ∈ Γ.E)
    (hxg : x ∈ closure g) : g ∈ (P i).E := by
  have hfr : frontier Δ = F := by
    rw [IsClosedDisc.frontier_eq_discBd hS h.disc, ← GraphMinor.GM14.IsClosedDisc.subBd_eq_discBd
      hS h.disc, h.bd]
  have hxF : x ∉ F := fun hF => by
    rcases h.end_of_mem_F hx hF with h1 | h1
    · exact hxa h1
    · exact hxb h1
  have hint : x ∈ interior Δ := by
    by_contra hn
    exact hxF (hfr ▸ ⟨subset_closure (h.U_sub i hx), hn⟩)
  obtain ⟨y, hy, hyg⟩ := mem_closure_iff.mp hxg _ isOpen_interior hint
  obtain ⟨-, j, hj⟩ := h.edge_mem hS hg ⟨y, hyg, interior_subset hy⟩
  have hxj : x ∈ (P j).U := (P j).closure_subset_U hj hxg
  have : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (h.disj hne) hxj hx
  exact this ▸ hj

end Setup61

/-- The sides of the chords, the closed discs `DBar_m` between them, and the regions `r_m ⊇ D_m` of
(6.1). -/
structure Pieces61 (Γ : Drawing S) (F Δ : Set S) {k : ℕ} (a b : Fin k → S) (P : Fin k → Drawing S)
    (X Y A B : Fin k → Set S) (E r : Fin (k + 1) → Set S) : Prop where
  side : ∀ i, IsSide F Δ (P i).U a b i (X i) (Y i) (A i) (B i)
  disc : ∀ m, IsClosedDisc (E m)
  sub : ∀ m, E m ⊆ Δ
  bd : ∀ i, (P i).U ⊆ discBd (E i.castSucc) ∧ (P i).U ⊆ discBd (E i.succ)
  int_X : ∀ m i, m.1 ≤ i.1 → discInt (E m) ⊆ X i
  int_Y : ∀ m i, i.1 < m.1 → discInt (E m) ⊆ Y i
  int_P : ∀ m i, Disjoint (discInt (E m)) (P i).U
  reg : ∀ m, r m ∈ Γ.R
  inj : Function.Injective r
  int_r : ∀ m, discInt (E m) ⊆ r m

namespace Setup61

variable {Γ : Drawing S} {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S}

/-- The regions of (6.1). `r m` is the region of `Γ` that includes `D_m`, with the numbering from
`0`. They are distinct since `Γ₁` is 2-cell, and each path lies between its two regions. -/
theorem exists_regions (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    (hk : 0 < k) (h2 : (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsTwoCell) :
    ∃ (X Y A B : Fin k → Set S) (E r : Fin (k + 1) → Set S), Pieces61 Γ F Δ a b P X Y A B E r ∧
      ∀ i : Fin k, (P i).U ⊆ closure (r i.castSucc) ∧ (P i).U ⊆ closure (r i.succ) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hC := h.chords hS
  have hex := fun i => hC.exists_side i
  choose X Y A B hs using hex
  obtain ⟨E, W, hEW, hEb, hW, hWd, hWX, hWY, hWc⟩ := exists_pieces hC hs hk
  have hWU : ∀ m, Disjoint (W m) Γ.U := fun m => by
    refine Set.disjoint_left.mpr fun x hx hxU => ?_
    obtain ⟨i, hi⟩ := h.U_inter hS hxU ((hW m).2.2 hx)
    exact Set.disjoint_left.mp (hWd m i) hx hi
  have hreg : ∀ m, ∃ r ∈ Γ.R, W m ⊆ r := fun m => by
    obtain ⟨x, hx⟩ := (hW m).2.1
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (Set.disjoint_left.mp (hWU m) hx)
    exact ⟨r, hr, subset_region hr (hW m).1 (hWU m) hx hxr⟩
  choose r hr hWr using hreg
  have hsubU : (Γ.interSet (closure (univ \ Δ))).U ⊆ Γ.U := interSet_isSub.U_subset
  have hfr : frontier Δ = F := by
    rw [IsClosedDisc.frontier_eq_discBd hS h.disc, ← GraphMinor.GM14.IsClosedDisc.subBd_eq_discBd
      hS h.disc, h.bd]
  have hFcl : F ⊆ closure (univ \ Δ) := by
    rw [← hfr, frontier_eq_closure_inter_closure]
    intro x hx
    rw [compl_eq_univ_sdiff] at hx
    exact hx.2
  have hU₁ : (Γ.interSet (closure (univ \ Δ))).U ∩ Δ ⊆ F := by
    rintro x ⟨hx, hxΔ⟩
    rw [← hfr, frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hxΔ, ?_⟩
    rw [compl_eq_univ_sdiff]
    exact interSet_U_subset isClosed_closure hx
  have hV₁ : ∀ {x : S}, x ∈ F ∩ Γ.V → x ∈ (Γ.interSet (closure (univ \ Δ))).U := fun hx =>
    (Γ.interSet _).V_subset_U ((mem_interSet_V_iff isClosed_closure).mpr ⟨hx.2, hFcl hx.1⟩)
  have hinj : ∀ m m' : Fin (k + 1), m < m' → r m ≠ r m' := by
    intro m m' hmm he
    have hm' := m'.2
    have hmm' : m.1 < m'.1 := hmm
    let i : Fin k := ⟨m.1, by omega⟩
    have hZ : IsPathConnected (r m) := isPathConnected_of_isOpen hS (region_isOpen (hr m))
      (region_isPreconnected (hr m)) (region_nonempty (hr m))
    obtain ⟨p, hp⟩ := (hW m).2.1
    obtain ⟨q, hq⟩ := (hW m').2.1
    have hd : Disjoint (r m) Γ.U := Set.disjoint_left.mpr fun x hx hxU => region_subset
      (hr m) hx hxU
    refine no_bypass hS h.disc hC.bd (hs i).discX.isClosed (hs i).discY.isClosed (hs i).union
      (hs i).inter (hs i).arcs (hs i).arcs_inter (hs i).lineA.isCompact.isClosed
      (hs i).lineB.isCompact.isClosed ?_ ?_ h2.2 hU₁ (hV₁ (h.a_mem i)) (hV₁ (h.b_mem i)) hZ
      (hd.mono_right (h.isSub i).U_subset) (hd.mono_right hsubU) (hWr m hp) (he ▸ hWr m' hq)
      (hWX m i le_rfl hp) (hWY m' i hmm' hq)
    · exact (subset_union_left.trans (hs i).bdX.symm.subset).trans
        (GraphMinor.Surface.discBd_subset _)
    · exact (subset_union_left.trans (hs i).bdY.symm.subset).trans
        (GraphMinor.Surface.discBd_subset _)
  have hrinj : Function.Injective r := by
    intro m m' he
    rcases lt_trichotomy m m' with h1 | h1 | h1
    · exact (hinj m m' h1 he).elim
    · exact h1
    · exact (hinj m' m h1 he.symm).elim
  refine ⟨X, Y, A, B, E, r, ⟨hs, fun m => (hEW m).1, fun m => (hEW m).2.1, hEb,
    fun m i hi => (hEW m).2.2 ▸ hWX m i hi, fun m i hi => (hEW m).2.2 ▸ hWY m i hi,
    fun m i => (hEW m).2.2 ▸ hWd m i, hr, hrinj, fun m => (hEW m).2.2 ▸ hWr m⟩,
    fun i => ⟨(hWc i).1.trans (closure_mono (hWr _)), (hWc i).2.trans (closure_mono (hWr _))⟩⟩

end Setup61

end GraphMinor.GM12
