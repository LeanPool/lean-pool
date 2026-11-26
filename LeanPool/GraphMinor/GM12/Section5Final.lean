/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Respect
public import LeanPool.GraphMinor.GM12.Section5Band
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM15.Section3Disc
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM10.Section12

/-!
# Graph Minors XII, (5.1) and (5.2)

The paper says that these follow from (5.3). Conditions (i) and (ii) of (5.3) are direct, by
[4, Theorem (12.2)] in the case of (5.1). For (iii), a curve in `Σ₂` of length `< θ` misses one of
the
`θ` disjoint paths, and cutting `Σ₂` along this path gives a closed disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {P₂ : Set S}

omit [T2Space S] in
/-- A curve of length `< θ` misses one of `θ` disjoint paths. -/
theorem exists_missed_path {θ : ℕ} (P : Fin θ → Drawing S)
    (hd : Pairwise fun i j => Disjoint (P i).U (P j).U) (hsub : ∀ i, (P i).U ⊆ Γ.U)
      (c : C(Circle, S))
    (hN : Γ.IsNormal (range c)) (hc : (range c ∩ Γ.V).ncard < θ) : ∃ i, ∀ x, c x ∉ (P i).U := by
  classical
  by_contra hn
  push Not at hn
  choose z hz using hn
  have hinj : Function.Injective fun i => c (z i) := by
    intro i j he
    by_contra hij
    exact Set.disjoint_left.mp (hd hij) (hz i) (by simpa only [he] using hz j)
  have hr : range (fun i => c (z i)) ⊆ range c ∩ Γ.V := by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨_, rfl⟩, hN ⟨⟨_, rfl⟩, hsub i (hz i)⟩⟩
  have := ncard_le_ncard hr (Γ.finite_V.subset inter_subset_right)
  rw [← image_univ, ncard_image_of_injective _ hinj, ncard_univ, Nat.card_fin] at this
  omega

/-- A closed curve in `Σ₂` that misses a line along which `Σ₂` cuts to a closed disc is
null-homotopic in `Σ₂`. -/
theorem curve_null {F : Set P₂} (c : C(Circle, S)) (hc : ∀ x, c x ∈ P₂) (hm : ∀ x,
  (⟨c x, hc x⟩ : P₂) ∉ F)
    (hcut : ∃ (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → P₂), IsSurface Y ∧ IsCutting ψ F ∧
      Nonempty (Y ≃ₜ ClosedUnitDisc)) : ClosedCurveIsNullHomotopicIn P₂ c := by
  obtain ⟨Y, tY, ψ, hY, hψ, ⟨e⟩⟩ := hcut
  have : CompactSpace Y := hY.1
  let c' : C(Circle, P₂) := ⟨fun x => ⟨c x, hc x⟩, c.continuous.subtype_mk _⟩
  obtain ⟨z, -, H, -, h0, h1⟩ := null_of_cut hψ e c' hm
  refine ⟨z.1, z.2, ⟨fun p => (H p).1, continuous_subtype_val.comp H.continuous⟩,
    fun p => (H p).2, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (h0 x)
  · intro x
    exact congrArg Subtype.val (h1 x)

variable {n : ℕ} {T : Type u} [TopologicalSpace T] [T2Space T] {C : Fin n → Set S} {P₁ : Set S}
  {ι : P₁ → T} {D : Fin n → Set T}

omit [T2Space S] [T2Space T] in
theorem bd_two (h : IsCappedSplit C P₁ P₂ ι D) : bd P₂ = (↑) ⁻¹' ⋃ i, C i := by
  rw [← h.bd₂]
  exact (preimage_image_eq _ Subtype.val_injective).symm

omit [T2Space T] in
/-- A line in `Σ₂` with ends on the common boundary, and no other point on it, is a proper line of
`Σ₂`. -/
theorem line_in_two (h : IsCappedSplit C P₁ P₂ ι D) {L : Set S} {s t : S}
  (hl : IsLineWithEnds L s t)
    (hL : L ⊆ P₂) (hmeet : L ∩ ⋃ i, C i = {s, t}) :
    ∃ u v : P₂, u.1 = s ∧ v.1 = t ∧ IsLineWithEnds ((↑) ⁻¹' L : Set P₂) u v ∧
      ((↑) ⁻¹' L : Set P₂) ∩ bd P₂ = {u, v} := by
  have hr : L ⊆ range ((↑) : P₂ → S) := by
    rw [Subtype.range_coe]
    exact hL
  obtain ⟨u, v, hu, hv, hp⟩ := hl.pull IsEmbedding.subtypeVal hr
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · exact hp
  · rw [bd_two h]
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      have : x.1 ∈ L ∩ ⋃ i, C i := ⟨h₁, h₂⟩
      rw [hmeet] at this
      rcases this with he | he
      · exact .inl (Subtype.ext (he.trans hu.symm))
      · exact .inr (Subtype.ext (he.trans hv.symm))
    · rintro hx
      have : x.1 ∈ ({s, t} : Set S) := by
        rcases hx with rfl | rfl
        · exact .inl hu
        · exact .inr hv
      rw [← hmeet] at this
      exact this

omit [T2Space S] in
/-- The points of the paths on the boundary. -/
theorem path_meet {θ : ℕ} {P : Fin θ → Drawing S} (hd : Pairwise fun i j => Disjoint (P i).U
  (P j).U)
    {Y : Set S} (hN : Γ.IsNormal Y) (hsub : ∀ i, (P i).U ⊆ Γ.U) {e : Fin θ → S} (he : ∀ i, e i ∈
      (P i).U)
    (hr : Γ.V ∩ Y ⊆ range e) (i : Fin θ) {x : S} (hx : x ∈ (P i).U) (hxY : x ∈ Y) : x = e i := by
  have hV : x ∈ Γ.V := hN ⟨hxY, hsub i hx⟩
  obtain ⟨j, rfl⟩ := hr ⟨hV, hxY⟩
  by_cases hij : i = j
  · rw [hij]
  · exact (Set.disjoint_left.mp (hd hij) hx (he j)).elim

omit [TopologicalSpace S] [T2Space S] in
/-- Every set of `θ` distinct points in a set of size `θ` is all of it. -/
theorem range_eq_of_ncard {θ : ℕ} {e : Fin θ → S} {Y : Set S} (hY : Y.Finite) (hc : Y.ncard = θ)
    (he : Function.Injective e) (hs : range e ⊆ Y) : Y ⊆ range e := by
  have h1 : (range e).ncard = θ := by
    rw [← image_univ, ncard_image_of_injective _ he, ncard_univ, Nat.card_fin]
  exact (eq_of_subset_of_ncard_le hs (by omega) hY).symm.subset

theorem interSet_U_two {P₂ : Set S} (hP : IsClosed P₂) {θ : ℕ} {P : Fin θ → Drawing S}
    (hU : (Γ.interSet P₂).U = ⋃ i : Fin θ, (P i).U) (i : Fin θ) : (P i).U ⊆ Γ.U ∧ (P i).U ⊆ P₂ := by
  have h : (P i).U ⊆ (Γ.interSet P₂).U := hU ▸ subset_iUnion (fun i => (P i).U) i
  exact ⟨h.trans interSet_isSub.U_subset, h.trans (interSet_U_subset hP)⟩

omit [T2Space T] in
theorem comp_ne (h : IsCappedSplit C P₁ P₂ ι D) {k l : Fin n} (hkl : k ≠ l) {u v : P₂}
  (hu : u.1 ∈ C k)
    (hv : v.1 ∈ C l) : connectedComponentIn (bd P₂) u ≠ connectedComponentIn (bd P₂) v := by
  intro he
  have hb : ∀ {w : P₂} {m : Fin n}, w.1 ∈ C m → w ∈ bd P₂ := fun {w m} hw => by
    rw [bd_two h]
    exact mem_iUnion.mpr ⟨m, hw⟩
  have hcl : ∀ m, IsClosed ((↑) ⁻¹' C m : Set P₂) := fun m =>
    ((h.isOArc m).isCompact.isClosed).preimage continuous_subtype_val
  have hsub : connectedComponentIn (bd P₂) u ⊆ (↑) ⁻¹' C k ∪ ⋃ m ∈ {m | m ≠ k}, (↑) ⁻¹' C m := by
    intro y hy
    have hyb := connectedComponentIn_subset _ _ hy
    rw [bd_two h] at hyb
    obtain ⟨m, hm⟩ := mem_iUnion.mp hyb
    by_cases hmk : m = k
    · subst hmk
      exact .inl hm
    · exact .inr (mem_biUnion hmk hm)
  have hcl' : IsClosed (⋃ m ∈ {m | m ≠ k}, ((↑) ⁻¹' C m : Set P₂)) :=
    (Set.toFinite _).isClosed_biUnion fun m _ => hcl m
  obtain ⟨z, -, hz, hzz⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn _ _
    (hcl k) hcl'
    hsub ⟨u, mem_connectedComponentIn (hb hu), hu⟩
    ⟨v, he ▸ mem_connectedComponentIn (hb hv), mem_biUnion hkl.symm hv⟩
  obtain ⟨m, hmk, hm⟩ := mem_iUnion₂.mp hzz
  exact Set.disjoint_left.mp (h.disjoint k m (Ne.symm hmk)) hz hm

theorem free_mono {α β : Type*} {G : Hypergraph α β} {θ : ℕ} {𝒯 : Set
  (Hypergraph α β × Hypergraph α β)}
    (hT : IsTangle G θ 𝒯) {X Z : Set α} (hZ : IsFreeSet G 𝒯 θ Z) (hs : X ⊆ Z) : IsFreeSet G 𝒯 θ X
      := by
  obtain ⟨M, -, hM, -⟩ := GraphMinor.GM10.theorem_12_2_proof G hT
  exact (hM X).mp (((hM Z).mpr hZ).subset hs)

/-- **Graph Minors XII, (5.1)** (page 254). -/
theorem theorem_5_1_proof : GM15.GM12Theorem51Statement.{u} := by
  intro S _ _ T _ _ C P₁ P₂ ι D Γ Γ₁ θ 𝒯 P a b _ _ hsplit hΓ hN0 hN1 hc0 hc1 hpath hd hU hline hT
    hR hf0 hf1
  obtain ⟨h, hconnT, ⟨eA⟩⟩ := hsplit
  have hN : ∀ k, Γ.IsNormal (C k) := Fin.forall_fin_two.mpr ⟨hN0, hN1⟩
  have hsub := interSet_U_two h.isClosed₂ hU
  have hab : ∀ i, a i ≠ b i := fun i he =>
    Set.disjoint_left.mp (h.disjoint 0 1 (by decide)) (hpath i).1.2 (he ▸ (hpath i).2.1.2)
  have hl : ∀ i, IsLineWithEnds (P i).U (a i) (b i) := fun i =>
    GM14.isLine_of_isPathBetween (hpath i).2.2.1 (hab i)
  have hinj : ∀ {e : Fin θ → S}, (∀ i, e i ∈ (P i).U) → Function.Injective e := by
    intro e he i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) (he i) (hij ▸ he j)
  have ha : ∀ i, a i ∈ (P i).U := fun i => (hl i).left_mem
  have hb : ∀ i, b i ∈ (P i).U := fun i => (hl i).right_mem
  have hr0 : Γ.V ∩ C 0 ⊆ range a := range_eq_of_ncard (Γ.finite_V.subset inter_subset_left) hc0
    (hinj ha)
    (by rintro _ ⟨i, rfl⟩; exact (hpath i).1)
  have hr1 : Γ.V ∩ C 1 ⊆ range b := range_eq_of_ncard (Γ.finite_V.subset inter_subset_left) hc1
    (hinj hb)
    (by rintro _ ⟨i, rfl⟩; exact (hpath i).2.1)
  have hiii : CurvesNull Γ P₂ θ := by
    intro c hcP hcN hcc
    obtain ⟨i, hi⟩ := exists_missed_path P hd (fun i => (hsub i).1) c hcN hcc
    have hmeet : (P i).U ∩ ⋃ k, C k = {a i, b i} := by
      ext x
      constructor
      · rintro ⟨hx, hxC⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp hxC
        obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
        · exact .inl (path_meet hd (hN 0) (fun i => (hsub i).1) ha hr0 i hx hk)
        · exact .inr (path_meet hd (hN 1) (fun i => (hsub i).1) hb hr1 i hx hk)
      · rintro (rfl | rfl)
        · exact ⟨ha i, mem_iUnion.mpr ⟨0, (hpath i).1.2⟩⟩
        · exact ⟨hb i, mem_iUnion.mpr ⟨1, (hpath i).2.1.2⟩⟩
    obtain ⟨u, v, hu, hv, hL, hB⟩ := line_in_two h (hl i) (hsub i).2 hmeet
    have hne : u ≠ v := fun he => hab i (by rw [← hu, ← hv, he])
    have hM : Nonempty (P₂ ≃ₜ SurfaceModel 0 0 2) := by
      obtain ⟨e₁⟩ := nonempty_cyl_homeo
      exact ⟨eA.trans (GM15.closedCylinderHomeoAnnulus.symm.trans e₁.symm)⟩
    have hconnP : ConnectedSpace P₂ := by
      obtain ⟨e₁⟩ := hM
      have := (modelCriterion.1 0 0 2).2
      exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
    have hu0 : u.1 ∈ C 0 := by rw [hu]; exact (hpath i).1.2
    have hv1 : v.1 ∈ C 1 := by rw [hv]; exact (hpath i).2.1.2
    exact curve_null c hcP (fun x => hi x)
      (exists_cut_annulus h.manifold₂ hne hB hL hM (comp_ne h (by decide) hu0 hv1))
  have hlineall : ∀ k l : Fin 2, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ →
      (F ∩ C k).Nonempty → (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard := by
    intro k l hkl F h1 h2 h3 h4 h5
    obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    · obtain rfl | rfl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
      · exact (hkl rfl).elim
      · exact hline F h1 h2 h3 h4 h5
    · obtain rfl | rfl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
      · exact hline F h1 h2 h3 h5 h4
      · exact (hkl rfl).elim
  have : ConnectedSpace T := hconnT
  exact theorem_5_3_proof h hΓ hN hT hR hlineall (Fin.forall_fin_two.mpr ⟨hc0.ge, hc1.ge⟩)
    (Fin.forall_fin_two.mpr ⟨fun X hX _ => free_mono hT hf0 hX, fun X hX _
      => free_mono hT hf1 hX⟩) hiii

omit [T2Space S] in
/-- The two open arcs of an `O`-arc between two points, read by angle. -/
theorem two_pieces {Y : Set S} (f : Circle ≃ₜ Y) {α β : ℝ} (h1 : α < β) (h2 : β < α + 2 * Real.pi) :
    let e : ℝ → S := fun r => (f (Circle.exp r)).1
    IsPreconnected (e '' Ioo α β) ∧ IsPreconnected (e '' Ioo β (α + 2 * Real.pi)) ∧
      (∀ x ∈ Y, x ≠ e α → x ≠ e β → x ∈ e '' Ioo α β ∪ e '' Ioo β (α + 2 * Real.pi)) ∧
      ∀ r, α < r → r < α + 2 * Real.pi → r ≠ β → e r ≠ e α ∧ e r ≠ e β := by
  intro e
  have hpi := Real.pi_pos
  have hc : Continuous e :=
    continuous_subtype_val.comp (f.continuous.comp Circle.exp.continuous)
  have hinj : ∀ {r s : ℝ}, e r = e s → ∃ m : ℤ, r = s + m * (2 * Real.pi) := fun {r s} he =>
    Circle.exp_eq_exp.mp (f.injective (Subtype.ext he))
  refine ⟨isPreconnected_Ioo.image _ hc.continuousOn, isPreconnected_Ioo.image _ hc.continuousOn,
    ?_, ?_⟩
  · intro x hx hxα hxβ
    let z := f.symm ⟨x, hx⟩
    have hrz := toIcoMod_mem_Ico (by positivity : (0 : ℝ) < 2 * Real.pi) α (Complex.arg (z : ℂ))
    set r := toIcoMod (by positivity : (0 : ℝ) < 2 * Real.pi) α (Complex.arg (z : ℂ)) with hr
    have hez : e r = x := by
      have hp : Circle.exp r = z := by
        have hs := toIcoMod_add_toIcoDiv_zsmul (by positivity : (0 : ℝ) < 2 * Real.pi) α
          (Complex.arg (z : ℂ))
        rw [← hr] at hs
        have : Circle.exp (r + toIcoDiv (by positivity : (0 : ℝ) < 2 * Real.pi) α (Complex.arg
          (z : ℂ)) • (2 * Real.pi)) =
            Circle.exp r := by
          rw [Circle.exp_eq_exp]
          exact ⟨toIcoDiv (by positivity : (0 : ℝ) < 2 * Real.pi) α (Complex.arg (z : ℂ)),
            by rw [zsmul_eq_mul]⟩
        rw [← this, hs, Circle.exp_arg]
      change (f (Circle.exp r)).1 = x
      rw [hp]
      simp [z]
    rw [← hez] at hxα hxβ ⊢
    have hrα : α < r := lt_of_le_of_ne hrz.1 (fun he => hxα (by rw [he]))
    have hrβ : r ≠ β := fun he => hxβ (by rw [he])
    rcases lt_or_gt_of_ne hrβ with hlt | hgt
    · exact .inl ⟨r, ⟨hrα, hlt⟩, rfl⟩
    · exact .inr ⟨r, ⟨hgt, hrz.2⟩, rfl⟩
  · intro r hrα hr2 hrβ
    constructor
    · intro he
      obtain ⟨m, hm⟩ := hinj he
      have h3 : (0 : ℝ) < m * (2 * Real.pi) := by linarith
      have h4 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
      have h5 : (0 : ℝ) < m := by nlinarith
      have h6 : (m : ℝ) < 1 := by nlinarith
      have h7 : 0 < m := by exact_mod_cast h5
      have h8 : m < 1 := by exact_mod_cast h6
      omega
    · intro he
      obtain ⟨m, hm⟩ := hinj he
      have h3 : -(2 * Real.pi) < m * (2 * Real.pi) := by linarith
      have h4 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
      have h5 : (-1 : ℝ) < m := by nlinarith
      have h6 : (m : ℝ) < 1 := by nlinarith
      have h7 : -1 < m := by exact_mod_cast h5
      have h8 : m < 1 := by exact_mod_cast h6
      have h9 : m = 0 := by omega
      subst h9
      apply hrβ
      simpa using hm

/-- **Graph Minors XII, (5.2)** (page 254), for `θ ≥ 2`. The statement fails for `θ = 1`, because a
path with ends on the boundary of the band need not cross it. -/
theorem theorem_5_2_proof : GM15.GM12Theorem52Statement.{u} := by
  intro S _ _ T _ _ C P₁ P₂ ι D Γ Γ₁ θ 𝒯 P a b hθ _ _ hsplit hΓ hN0 hc _ hord hrange hpath hd hU hT
    hR hf
  classical
  obtain ⟨h, hconnT, ⟨eB⟩⟩ := hsplit
  have hN : ∀ k, Γ.IsNormal (C k) := fun k => by rwa [Subsingleton.elim k 0]
  have hsub := interSet_U_two h.isClosed₂ hU
  obtain ⟨f, t, hmono, hlt, hv⟩ := hord
  have hlen : (List.ofFn a ++ List.ofFn b).length = θ + θ := by simp
  have hat : ∀ i : Fin θ, (f (Circle.exp (t i))).1 = a i := by
    intro i
    have := hv i.1 (by rw [hlen]; omega)
    rw [this, List.getElem_append_left (by simp)]
    simp
  have hbt : ∀ i : Fin θ, (f (Circle.exp (t (θ + i)))).1 = b i := by
    intro i
    have := hv (θ + i.1) (by rw [hlen]; omega)
    rw [this, List.getElem_append_right (by simp)]
    simp
  have hlt' : ∀ k, k < θ + θ → t k < t 0 + 2 * Real.pi := fun k hk => hlt k (by rwa [hlen])
  have hpi := Real.pi_pos
  have hstep : ∀ i : Fin θ, t i < t (θ + i) ∧ t (θ + i) < t i + 2 * Real.pi := by
    intro i
    have h3 := hlt' (θ + i) (by have := i.2; omega)
    have h4 : t 0 ≤ t i := hmono.monotone (Nat.zero_le _)
    exact ⟨hmono (by have := i.2; omega), by linarith⟩
  have hne_ab : ∀ i : Fin θ, a i ≠ b i := by
    intro i he
    obtain ⟨h1, h2⟩ := hstep i
    have h5 : (f (Circle.exp (t i))).1 = (f (Circle.exp (t (θ + i)))).1 := by rw [hat, hbt, he]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (f.injective (Subtype.ext h5))
    have h6 : (m : ℝ) * (2 * Real.pi) < 0 := by linarith
    have h7 : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith
    have h8 : (m : ℝ) < 0 := by nlinarith
    have h9 : (-1 : ℝ) < m := by nlinarith
    have h10 : m < 0 := by exact_mod_cast h8
    have h11 : -1 < m := by exact_mod_cast h9
    omega
  have hl : ∀ i, IsLineWithEnds (P i).U (a i) (b i) := fun i =>
    GM14.isLine_of_isPathBetween (hpath i).1 (hne_ab i)
  have ha : ∀ i, a i ∈ (P i).U := fun i => (hl i).left_mem
  have hb : ∀ i, b i ∈ (P i).U := fun i => (hl i).right_mem
  have haC : ∀ i, a i ∈ C 0 := fun i => by rw [← hat]; exact (f _).2
  have hbC : ∀ i, b i ∈ C 0 := fun i => by rw [← hbt]; exact (f _).2
  have hmeetV : ∀ i, ∀ x ∈ (P i).U, x ∈ C 0 → x = a i ∨ x = b i := by
    intro i x hx hxC
    have hxV : x ∈ Γ.V := hN0 ⟨hxC, (hsub i).1 hx⟩
    have hsame : ∀ j, x ∈ (P j).U → x = a j ∨ x = b j → x = a i ∨ x = b i := by
      intro j hj he
      by_cases hij : i = j
      · rwa [hij]
      · exact (Set.disjoint_left.mp (hd hij) hx hj).elim
    have hmem : x ∈ range a ∪ range b := hrange ▸ ⟨hxV, hxC⟩
    rcases hmem with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hsame j (ha j) (.inl rfl)
    · exact hsame j (hb j) (.inr rfl)
  have hiii : CurvesNull Γ P₂ θ := by
    intro c hcP hcN hcc
    obtain ⟨i, hi⟩ := exists_missed_path P hd (fun i => (hsub i).1) c hcN hcc
    have hmeet : (P i).U ∩ ⋃ k, C k = {a i, b i} := by
      ext x
      constructor
      · rintro ⟨hx, hxC⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp hxC
        rw [Subsingleton.elim k 0] at hk
        exact hmeetV i x hx hk
      · rintro (rfl | rfl)
        · exact ⟨ha i, mem_iUnion.mpr ⟨0, haC i⟩⟩
        · exact ⟨hb i, mem_iUnion.mpr ⟨0, hbC i⟩⟩
    obtain ⟨u, v, hu, hv, hL, hB⟩ := line_in_two h (hl i) (hsub i).2 hmeet
    have hne : u ≠ v := fun he => hne_ab i (by rw [← hu, ← hv, he])
    have hM : Nonempty (P₂ ≃ₜ SurfaceModel 0 1 1) := by
      obtain ⟨e₁⟩ := nonempty_mob_homeo
      exact ⟨eB.trans e₁.symm⟩
    have hconnP : ConnectedSpace P₂ := by
      obtain ⟨e₁⟩ := hM
      have := (modelCriterion.1 0 1 1).2
      exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
    obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hun, hdX, hX, hX', hcase⟩ := exists_cut_band h.manifold₂
      hne hB hL hM
    rcases hcase with hdisc | ⟨W₁, W₂, hX₁, hX₂, hW₁, hW₂, hUW, hdW⟩
    · exact curve_null c hcP (fun x => hi x) ⟨Y, tY, ψ, hY, hψ, hdisc⟩
    · exfalso
      have : CompactSpace Y := hY.1
      -- A second path has its ends on the two arcs of `C` between the ends of the first.
      obtain ⟨j, hji⟩ : ∃ j : Fin θ, j ≠ i := by
        by_cases h0 : i.1 = 0
        · exact ⟨⟨1, by omega⟩, fun he => by rw [← he] at h0; simp at h0⟩
        · exact ⟨⟨0, by omega⟩, fun he => h0 (by rw [← he])⟩
      obtain ⟨hs1, hs2⟩ := hstep i
      obtain ⟨p1, p2, hcov, hmiss⟩ := two_pieces f hs1 hs2
      set e : ℝ → S := fun r => (f (Circle.exp r)).1 with he
      set A₁ := e '' Ioo (t i) (t (θ + i)) with hA₁
      set A₂ := e '' Ioo (t (θ + i)) (t i + 2 * Real.pi) with hA₂
      have hA₁C : A₁ ⊆ C 0 := by
        rintro _ ⟨r, -, rfl⟩
        exact (f _).2
      have hA₂C : A₂ ⊆ C 0 := by
        rintro _ ⟨r, -, rfl⟩
        exact (f _).2
      have hmeets : ((P j).U ∩ A₁).Nonempty ∧ ((P j).U ∩ A₂).Nonempty := by
        have h4 : t 0 ≤ t j := hmono.monotone (Nat.zero_le _)
        have h4' : t 0 ≤ t i := hmono.monotone (Nat.zero_le _)
        have hj := j.2
        have hii := i.2
        have hneq : (j : ℕ) ≠ i := fun he => hji (Fin.ext he)
        rcases lt_or_gt_of_ne hneq with hlt₁ | hgt₁
        · -- `j` comes first: the end `b j` is on the first arc, and `a j` one turn on is on the
          -- second.
          refine ⟨⟨b j, hb j, t (θ + j), ⟨hmono (by omega), hmono (by omega)⟩, hbt j⟩,
            ⟨a j, ha j, t j + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩⟩
          · have := hlt' (θ + i) (by omega)
            linarith
          · have : t j < t i := hmono hlt₁
            linarith
          · change (f (Circle.exp (t j + 2 * Real.pi))).1 = a j
            rw [← hat j]
            congr 2
            rw [Circle.exp_eq_exp]
            exact ⟨1, by simp⟩
        · -- `i` comes first: `a j` is on the first arc, and `b j` is on the second.
          refine ⟨⟨a j, ha j, t j, ⟨hmono hgt₁, hmono (by omega)⟩, hat j⟩,
            ⟨b j, hb j, t (θ + j), ⟨hmono (by omega), ?_⟩, hbt j⟩⟩
          have := hlt' (θ + j) (by omega)
          linarith
      have hG : IsPreconnected ((P j).U ∪ A₁ ∪ A₂) := by
        have hPc : IsPreconnected (P j).U := by
          obtain ⟨α, hα, hr, -, -⟩ := (hl j).exists_arc
          rw [← hr]
          exact isPreconnected_range hα.1
        have h1 := hPc.union' hmeets.1 p1
        obtain ⟨z, hz, hz'⟩ := hmeets.2
        exact h1.union z (.inl hz) hz' p2
      have hGP : (P j).U ∪ A₁ ∪ A₂ ⊆ P₂ := by
        refine union_subset (union_subset (hsub j).2 ?_) ?_
        · exact hA₁C.trans (h.C_sub₂ 0)
        · exact hA₂C.trans (h.C_sub₂ 0)
      have hGimg : ((↑) : P₂ → S) '' ((↑) ⁻¹' ((P j).U ∪ A₁ ∪ A₂)) = (P j).U ∪ A₁ ∪ A₂ := by
        rw [Subtype.image_preimage_coe, inter_eq_right.mpr hGP]
      have hoff : ∀ r, t i < r → r < t i + 2 * Real.pi → r ≠ t (θ + i) → e r ∉ (P i).U := by
        intro r h1 h2 h3 hm
        obtain ⟨h5, h6⟩ := hmiss r h1 h2 h3
        rcases hmeetV i _ hm (f _).2 with he' | he'
        · exact h5 (he'.trans (hat i).symm)
        · exact h6 (he'.trans (hbt i).symm)
      refine no_split hY hψ (((hl i).isCompact.isClosed).preimage continuous_subtype_val) hun hX
        hX' hX₁ hX₂
        hW₁ hW₂ hUW hdW (G := (↑) ⁻¹' ((P j).U ∪ A₁ ∪ A₂))
        (IsEmbedding.subtypeVal.isInducing.isPreconnected_image.mp (by rw [hGimg]; exact hG)) ?_ ?_
      · refine Set.disjoint_left.mpr ?_
        rintro w ((hw | hw) | hw) hwi
        · exact Set.disjoint_left.mp (hd (Ne.symm hji)) hwi hw
        · obtain ⟨r, hr, hre⟩ := hw
          refine hoff r hr.1 ?_ (ne_of_lt hr.2) (by rw [hre]; exact hwi)
          linarith [hr.2]
        · obtain ⟨r, hr, hre⟩ := hw
          refine hoff r ?_ hr.2 (ne_of_gt hr.1) (by rw [hre]; exact hwi)
          linarith [hr.1]
      · rintro w ⟨hwb, hwF⟩
        rw [bd_two h] at hwb
        obtain ⟨k, hk⟩ := mem_iUnion.mp hwb
        rw [Subsingleton.elim k 0] at hk
        have hw1 : w.1 ≠ e (t i) := fun hw => hwF (by
          change w.1 ∈ (P i).U
          rw [hw]
          change (f (Circle.exp (t i))).1 ∈ (P i).U
          rw [hat]
          exact ha i)
        have hw2 : w.1 ≠ e (t (θ + i)) := fun hw => hwF (by
          change w.1 ∈ (P i).U
          rw [hw]
          change (f (Circle.exp (t (θ + i)))).1 ∈ (P i).U
          rw [hbt]
          exact hb i)
        rcases hcov w.1 hk hw1 hw2 with hm | hm
        · exact .inl (.inr hm)
        · exact .inr hm
  have : ConnectedSpace T := hconnT
  refine theorem_5_3_proof h hΓ hN hT hR ?_ ?_ ?_ hiii
  · intro k l hkl
    exact (hkl (Subsingleton.elim k l)).elim
  · intro k
    rw [Subsingleton.elim k 0, hc]
    omega
  · intro k
    rw [Subsingleton.elim k 0]
    exact hf

end GraphMinor.GM12
