/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.CurveArc
public import LeanPool.GraphMinor.GM11.NicePush
public import LeanPool.GraphMinor.GM11.RadialBasics
public import LeanPool.GraphMinor.GM11.NiceStatements
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# (7.3) of Graph Minors XI for closed nice sets

We show that a closed curve in a compact Hausdorff space which is covered by flat open sets is
null-homotopic if each `O`-arc in the curve is (`loop_homotopic_of_oArcs`). This is the proof of
Graph Minors VII, (11.2), with `CurveArc.lean` as its main step. The steps here are the first ones
of that
proof: the curve is cut in small pieces, and by (11.1) each piece can be taken to be a line or a
point.

The paper's (7.3) says that the proof of VII, (11.2) "applies", and closed nice sets are cones at
each point by
`isLocalCone`, so they are covered by flat open sets. This proves `Nice73Statement`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {T : Type u} [TopologicalSpace T]

variable [T2Space T]

/-- A short path is, up to homotopy in the flat set around it, a path along a line or a point. This
is
Graph Minors VII, (11.1). -/
theorem exists_arm_of_path {A : Set T} (hA : Flat A) {a b : T} (p : Path a b) (hp : ∀ u, p u ∈ A) :
    ∃ B ⊆ range p, IsArmTo B a b ∧ Arw B (Cl.mk p) := by
  by_cases hab : a = b
  · subst hab
    have ha : a ∈ range p := ⟨0, p.source⟩
    have e : Cl.mk p = Cl.rf a := hA.eq ⟨p, hp, rfl⟩ (arw_refl (by simpa using hp 0))
    rw [e]
    exact ⟨{a}, singleton_subset_iff.mpr ha, isArmTo_point a, arw_refl rfl⟩
  · obtain ⟨e, he, hi, h0, h1, hr⟩ := exists_arc_of_path p.continuous (by simpa using hab)
    have h0' : e 0 = a := by simpa using h0
    have h1' : e 1 = b := by simpa using h1
    have harc : IsArcMap e := ⟨he, hi⟩
    have hl : IsLineWithEnds (range e) a b := by
      have := harc.isLineWithEnds
      rwa [h0', h1'] at this
    have ham : IsArmTo (range e) a b := Or.inr hl
    obtain ⟨f, hf⟩ := ham.exists_arw
    refine ⟨range e, hr, ham, ?_⟩
    rwa [hA.eq ⟨p, hp, rfl⟩ (hf.mono fun y hy => ?_)]
    obtain ⟨u, rfl⟩ := hr hy
    exact hp u

omit [T2Space T] in
private theorem Ch.of_cast {Y : Set T} {Sm : Set T → Prop} {l : List (Set T)} {a b a' b' : T}
  (ea : a' = a)
    (eb : b' = b) {p : Path a b} (h : Ch Y Sm l a' b' (Cl.mk (p.cast ea eb))) : Ch Y Sm l a b
      (Cl.mk p) := by
  subst ea eb
  exact h

/-- A path, each point of which has a neighbourhood mapping into a small set, is a chain. -/
theorem exists_ch_of_path {Y : Set T} {Sm : Set T → Prop} (hflat : ∀ {A : Set T}, Sm A → A.Nonempty
  → Flat A)
    (hmono : ∀ {A B : Set T}, Sm A → B ⊆ A → Sm B) {a b : T} (γ : Path a b) (hY : ∀ u, γ u ∈ Y)
    (hcov : ∀ u : I, ∃ O : Set I, IsOpen O ∧ u ∈ O ∧ Sm (γ '' O)) :
    ∃ l, Ch Y Sm l a b (Cl.mk γ) := by
  let good : Set I → Prop := fun O => IsOpen O ∧ Sm (γ '' O)
  have hcover : (univ : Set I) ⊆ ⋃ O : {O : Set I // good O}, O.1 := by
    intro u _
    obtain ⟨O, h₁, h₂, h₃⟩ := hcov u
    exact mem_iUnion.mpr ⟨⟨O, h₁, h₃⟩, h₂⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htO⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun O : {O : Set I // good O} => O.2.1) hcover
  have key : ∀ n, ∃ l, Ch Y Sm l (γ 0) (γ (t n)) (Cl.mk (γ.subpath 0 (t n))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨[], ?_⟩
      rw [ht0, Path.subpath_self]
      exact Ch.nil _
    | succ n ih =>
      obtain ⟨l, hl⟩ := ih
      obtain ⟨⟨O, _, hSm⟩, hsub⟩ := htO n
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      have hpiece : ∀ u, (γ.subpath (t n) (t (n + 1))) u ∈ γ '' O := by
        intro u
        have : (γ.subpath (t n) (t (n + 1))) u ∈ γ '' uIcc (t n) (t (n + 1)) := by
          rw [← Path.range_subpath]
          exact mem_range_self u
        obtain ⟨v, hv, hv'⟩ := this
        rw [uIcc_of_le hle] at hv
        exact ⟨v, hsub hv, hv'⟩
      have hA : Flat (γ '' O) := hflat hSm ⟨_, hpiece 0⟩
      obtain ⟨B, hB, harm, hBa⟩ := exists_arm_of_path hA _ hpiece
      have hBs : B ⊆ γ '' O := fun y hy => by
        obtain ⟨u, rfl⟩ := hB hy
        exact hpiece u
      have hBY : B ⊆ Y := fun y hy => by
        obtain ⟨u, -, rfl⟩ := hBs hy
        exact hY u
      refine ⟨l ++ [B], ?_⟩
      have h := hl.append (Ch.single harm hBY (hmono hSm hBs) hBa)
      have e : (Cl.mk (γ.subpath 0 (t n))).trans (Cl.mk (γ.subpath (t n) (t (n + 1)))) =
          Cl.mk (γ.subpath 0 (t (n + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans]
        exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.subpath_trans_subpath _ _ _ _)
      rwa [e] at h
  obtain ⟨l, hl⟩ := key n₀
  rw [hn₀ n₀ le_rfl, Path.subpath_zero_one] at hl
  exact ⟨l, Ch.of_cast γ.source γ.target hl⟩

/-- **A closed curve is null-homotopic if each `O`-arc in it is.** Here the curve is covered by open
sets `U i` such
that each of them is flat where it meets the curve. This is the proof of Graph Minors VII, (11.2)
(page 249). -/
theorem loop_homotopic_of_oArcs {ι : Type*} (U : ι → Set T) (hU : ∀ i, IsOpen (U i)) {a : T}
  (γ : Path a a)
    (hc : range γ ⊆ ⋃ i, U i) (hflat : ∀ i, Flat (U i ∩ range γ))
    (hO : ∀ F : Set T, IsOArc F → F ⊆ range γ → ∀ (x : T) (p : Path x x), (∀ u, p u ∈ F) →
      p.Homotopic (Path.refl x)) :
    γ.Homotopic (Path.refl a) := by
  classical
  have hK : CompactSpace (range γ) := isCompact_iff_compactSpace.mp (isCompact_range γ.continuous)
  obtain ⟨R', hR', hN'⟩ := exists_small_rel (fun i => (Subtype.val ⁻¹' U i : Set (range γ)))
    (fun i => (hU i).preimage continuous_subtype_val) (fun x _ => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc x.2)
      exact mem_iUnion.mpr ⟨i, hi⟩)
  let R : T → T → Prop := fun x y => ∃ (hx : x ∈ range γ) (hy : y ∈ range γ), R' ⟨x, hx⟩ ⟨y, hy⟩
  have hR : ∀ x ∈ range γ, ∃ i, ∀ y, R x y → y ∈ U i ∩ range γ := fun x hx => by
    obtain ⟨i, hi⟩ := hR' ⟨x, hx⟩
    exact ⟨i, fun y ⟨_, hy, h⟩ => ⟨hi _ h, hy⟩⟩
  have hN : ∀ x ∈ range γ, ∃ N : Set T, IsOpen N ∧ x ∈ N ∧ ∀ a ∈ N, ∀ b ∈ N, a ∈ range γ
    → b ∈ range γ → R a b :=
    fun x hx => by
      obtain ⟨N, hNo, hxN, hNr⟩ := hN' ⟨x, hx⟩
      obtain ⟨N₀, hN₀, rfl⟩ := isOpen_induced_iff.mp hNo
      exact ⟨N₀, hN₀, hxN, fun a ha b hb h₁ h₂ => ⟨h₁, h₂, hNr ⟨a, h₁⟩ ha ⟨b, h₂⟩ hb⟩⟩
  let Sm : Set T → Prop := fun A => ∀ x ∈ A, ∀ y ∈ A, R x y
  have hmono : ∀ {A B : Set T}, Sm A → B ⊆ A → Sm B := fun h hBA x hx y hy => h x (hBA hx) y
    (hBA hy)
  have hpair : ∀ {A B : Set T}, Sm A → Sm B → (A ∩ B).Nonempty → Flat (A ∪ B) := by
    rintro A B hA hB ⟨w, hwA, hwB⟩
    obtain ⟨hw, -, -⟩ := hA w hwA w hwA
    obtain ⟨i, hi⟩ := hR w hw
    refine (hflat i).mono ?_
    rintro y (hy | hy)
    · exact hi y (hA w hwA y hy)
    · exact hi y (hB w hwB y hy)
  have hsm : ∀ {A : Set T}, Sm A → A.Nonempty → Flat A := fun {A} hA ⟨w, hw⟩ => by
    have := hpair hA hA ⟨w, hw, hw⟩
    rwa [union_self] at this
  have hcov : ∀ u : I, ∃ O : Set I, IsOpen O ∧ u ∈ O ∧ Sm (γ '' O) := by
    intro u
    obtain ⟨N, hNo, hNm, hNr⟩ := hN (γ u) (mem_range_self u)
    refine ⟨γ ⁻¹' N, hNo.preimage γ.continuous, hNm, ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨r, hr, rfl⟩
    exact hNr _ hs _ hr (mem_range_self s) (mem_range_self r)
  obtain ⟨l, hl⟩ := exists_ch_of_path (Y := range γ) hsm hmono γ (fun u => mem_range_self u) hcov
  have hO' : ∀ {x y : T} {L₁ L₂ : Set T}, IsLineWithEnds L₁ x y → IsLineWithEnds L₂ x y
    → L₁ ∩ L₂ ⊆ {x, y} →
      L₁ ∪ L₂ ⊆ range γ → ∀ f g : Cl x y, Arw L₁ f → Arw L₂ g → f = g := by
    intro x y L₁ L₂ h₁ h₂ hcap hsub f g hf hg
    obtain ⟨r, hr, e⟩ := Arw.trans (hf.mono (subset_union_left (t := L₂)))
      (Arw.symm (hg.mono (subset_union_right (s := L₁))))
    have hloop : f.trans g.symm = Cl.rf x := by
      rw [e]
      exact Path.Homotopic.Quotient.eq.mpr (hO _ (isOArc_union h₁ h₂ hcap) hsub x r hr)
    calc f = f.trans (g.symm.trans g) := by rw [cl_symm_trans, cl_trans_refl]
      _ = g := by rw [← cl_assoc, hloop, cl_refl_trans]
  have := Ch.eq_refl hmono hpair hO' _ l a _ rfl hl
  exact Path.Homotopic.Quotient.eq.mp this

/-- A closed curve in an `O`-arc that is null-homotopic in `W` is null-homotopic in `W`. -/
theorem homotopic_refl_of_null {S : Type u} [TopologicalSpace S] {W G : Set S}
  (hG : IsNullHomotopicOArcIn W G)
    {x : W} (p : Path x x) (hp : ∀ u, (p u).1 ∈ G) : p.Homotopic (Path.refl x) := by
  obtain ⟨ψ, c, hcW, H, hHW, h0, h1⟩ := hG
  let P : I → G := fun s => ⟨(p s).1, hp s⟩
  have hP : Continuous P := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let F : C(I × I, W) := ⟨fun w => ⟨H (ψ.symm (P w.1), w.2), hHW _⟩, by
    refine Continuous.subtype_mk ?_ _
    exact H.continuous.comp ((ψ.symm.continuous.comp (hP.comp continuous_fst)).prodMk
      continuous_snd)⟩
  refine loop_homotopic_refl p F (c := ⟨c, hcW⟩) (fun s => Subtype.ext ?_) (fun v => Subtype.ext ?_)
    fun s => Subtype.ext ?_
  · change H (ψ.symm (P s), 0) = (p s).1
    rw [h0]
    change ((ψ (ψ.symm (P s))) : S) = _
    rw [ψ.apply_symm_apply]
  · have e : P 0 = P 1 := Subtype.ext (by simp [P])
    change H (ψ.symm (P 0), v) = H (ψ.symm (P 1), v)
    rw [e]
  · change H (ψ.symm (P s), 1) = c
    rw [h1]
    rfl

/-- The heart of (7.3): a closed nice set `Z` in a closed surface, and a closed curve in `Z` in the
subtype `W ⊇ Z`.
The curve is null-homotopic in `W` if each `O`-arc in the curve is. -/
theorem loop_homotopic_of_null {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {Z W : Set S} (hZ : IsClosed Z)
      (hZn : IsGammaNice Γ Z) (hZW : Z ⊆ W)
    {a : W} (γ : Path a a) (hγ : ∀ u, (γ u).1 ∈ Z)
    (hall : ∀ F : Set S, IsOArc F → F ⊆ Subtype.val '' range γ → IsNullHomotopicOArcIn W F) :
    γ.Homotopic (Path.refl a) := by
  let good : Set W → Prop := fun O => IsOpen O ∧ Flat (O ∩ range γ)
  have hc : range γ ⊆ ⋃ O : {O : Set W // good O}, O.1 := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨O, K, hO, hzO, hsub, hK, hsc, -⟩ := isLocalCone hS hZ hZ hZn hZn (Or.inl (hγ u))
    rw [union_self] at hsub hK
    refine mem_iUnion.mpr ⟨⟨Subtype.val ⁻¹' O, hO.preimage continuous_subtype_val, ?_⟩, hzO⟩
    have hin : ∀ {x : W}, x ∈ Subtype.val ⁻¹' O ∩ range γ → x.1 ∈ K := by
      rintro _ ⟨h₁, v, rfl⟩
      exact hsub ⟨hγ v, h₁⟩
    intro b c p q hp hq
    exact homotopic_of_mem hsc (hK.trans hZW) p q (hin (by simpa using hp 0)) (hin
      (by simpa using hp 1))
      (fun u => hin (hp u)) fun u => hin (hq u)
  refine loop_homotopic_of_oArcs (fun O : {O : Set W // good O} => O.1) (fun O => O.2.1) γ hc
    (fun O => O.2.2) ?_
  intro F hF hFγ x p hp
  have hG : IsOArc (Subtype.val '' F) :=
    isOArc_image hF continuous_subtype_val.continuousOn Subtype.val_injective.injOn
  have hGγ : Subtype.val '' F ⊆ Subtype.val '' range γ := image_mono hFγ
  exact homotopic_refl_of_null (hall _ hG hGγ) p fun u => ⟨_, hp u, rfl⟩

/-- **(7.3)** of Graph Minors XI (page 93), for closed nice sets. -/
theorem nice_73 : Nice73Statement.{u} := by
  intro S _ _ _ hS Γ Z hZ hZn φ hφ hnot
  by_contra! hall
  have hmem : ∀ t, φ (arcParam 1 t) ∈ Z := fun t => hφ (mem_range_self _)
  let a : Z := ⟨φ (arcParam 1 0), hmem 0⟩
  let γ : Path a a := ⟨⟨fun t => ⟨φ (arcParam 1 t), hmem t⟩, by fun_prop⟩, rfl,
    Subtype.ext (by simp [a])⟩
  have hh : γ.Homotopic (Path.refl a) := by
    refine loop_homotopic_of_null hS hZ hZn subset_rfl γ (fun u => (γ u).2) fun F hF hFγ
      => hall F hF ?_
    refine hFγ.trans ?_
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact mem_range_self _
  exact hnot ⟨a.1, a.2, closedCurvesHomotopicIn_of_path 1 φ (ContinuousMap.const _ a.1) γ
    (Path.refl a)
    (fun _ => rfl) (fun _ => rfl) hh⟩

/-- **(7.3)** of Graph Minors XI (page 93), for closed nice sets: "If $Z \subseteq \Sigma$ is nice
and $\phi \colon S^1 \to Z$ is continuous and not null-homotopic in $Z$, then there is an $O$-arc $F
\subseteq |\phi|$ which is not null-homotopic in $Z$." -/
theorem theorem_7_3_proof {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Z : Set S} (hZ : IsClosed Z) (hZn : IsNice Z)
    (φ : C(Circle, S)) (hφ : range φ ⊆ Z) (hnot : ¬ ClosedCurveIsNullHomotopicIn Z φ) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArcIn Z F := by
  obtain ⟨Γ, hΓ⟩ := hZn
  exact nice_73 S hS Γ Z hZ hΓ φ hφ hnot

/-- A closed nice set is flat in `W` if each `O`-arc in it is null-homotopic in `W`. This is the
form of (7.3) that
(7.5) uses. -/
theorem flat_of_null_oArcs {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {Z W : Set S} (hZ : IsClosed Z)
      (hZn : IsGammaNice Γ Z) (hZW : Z ⊆ W)
    (hall : ∀ F : Set S, F ⊆ Z → IsOArc F → IsNullHomotopicOArcIn W F) :
    Flat (Subtype.val ⁻¹' Z : Set W) := by
  intro a b p q hp hq
  let γ : Path a a := p.trans q.symm
  have hin : ∀ u, (γ u).1 ∈ Z := by
    intro u
    have hu : γ u ∈ range p ∪ range q.symm := by
      rw [← Path.trans_range]
      exact mem_range_self u
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]
      exact hp v
    · rw [← hv]
      exact hq _
  have hγ : γ.Homotopic (Path.refl a) := loop_homotopic_of_null hS hZ hZn hZW γ hin fun F hF hFγ =>
    hall F (hFγ.trans (by rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩; exact hin u)) hF
  refine Path.Homotopic.Quotient.eq.mp ?_
  have h₁ : (Cl.mk p).trans (Cl.mk q).symm = Cl.rf a := by
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans, Cl.rf,
      ← Path.Homotopic.Quotient.mk_refl]
    exact Path.Homotopic.Quotient.eq.mpr hγ
  calc Cl.mk p = ((Cl.mk p).trans (Cl.mk q).symm).trans (Cl.mk q) := by
        rw [cl_assoc, cl_symm_trans, cl_trans_refl]
    _ = Cl.mk q := by rw [h₁, cl_refl_trans]

/-- **(7.4)** of Graph Minors XI (page 94), for closed nice sets: "If $\Sigma$ is connected and $X
\subseteq \Sigma$ is nice, then $X$ is simply-connected if
and only if $X$ is arc-wise connected and every $O$-arc $F \subseteq X$ bounds a disc in
$X$." Here
`X` is non-empty, since our simply-connected sets are. -/
theorem theorem_7_4_proof {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} (hc : IsClosed X) (hn : IsGammaNice Γ X)
    (hne : X.Nonempty) : IsSimplyConnectedSet X ↔ IsArcConnected X ∧
      ∀ F : Set S, F ⊆ X → IsOArc F → ∃ Δ : Set S, Δ ⊆ X ∧ IsClosedDisc Δ ∧ subBd Δ = F := by
  constructor
  · intro hs
    refine ⟨isArcConnected_of_isPathConnected hs.1, fun F hFX hF => theorem_7_2_proof hS hF hFX ?_⟩
    obtain ⟨ψ⟩ := id hF
    exact ⟨ψ, hs.2 _ (by
      rintro _ ⟨x, rfl⟩
      exact hFX (ψ x).2)⟩
  · rintro ⟨harc, hdisc⟩
    obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨⟨x₀, hx₀, fun {y} hy => ?_⟩, fun φ hφ => ?_⟩
    · by_cases hxy : x₀ = y
      · subst hxy
        exact JoinedIn.refl hx₀
      · obtain ⟨L, hL, hl⟩ := harc x₀ hx₀ y hy hxy
        obtain ⟨f, h0, h1⟩ := hl
        exact (show JoinedIn L x₀ y from ⟨⟨⟨fun t => (f t).1, by fun_prop⟩, h0, h1⟩,
          fun t => (f t).2⟩).mono hL
    · by_contra hnot
      obtain ⟨F, hF, hFφ, hFn⟩ := nice_73 S hS Γ X hc hn φ hφ hnot
      obtain ⟨Δ, hΔX, hΔ, hb⟩ := hdisc F (hFφ.trans hφ) hF
      have hFΔ : F ⊆ Δ := by
        rw [← hb, subBd_eq_frontier]
        exact (IsClosedDisc.isCompact hΔ).isClosed.frontier_subset
      obtain ⟨ψ⟩ := id hF
      obtain ⟨c, hcΔ, hh⟩ := (IsClosedDisc.isSimplyConnectedSet hΔ).2
        ⟨fun x => (ψ x).1, continuous_subtype_val.comp ψ.continuous⟩ (by
          rintro _ ⟨x, rfl⟩
          exact hFΔ (ψ x).2)
      exact hFn ⟨ψ, c, hΔX hcΔ, hh.mono hΔX⟩

end GraphMinor.GM11
