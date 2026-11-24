/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.LoopLift
public import LeanPool.GraphMinor.GM07.CutBuild
public import LeanPool.GraphMinor.GM07.CutBounds
import LeanPool.GraphMinor.GM06.DiscRegions

/-!
# The two sides of a loop

Let `f` be a loop of `G` at `v`, off the boundary. In the proof of (7.3) the paper says: "From this
and the fact that $\alpha(G) \ge 9$ it
follows that for every loop $e$ of $G$, $\bar{e}$ surrounds some cuff", and later speaks of "both
regions incident with `e`". We prove what
these sentences use. Push `ē` to each of its two sides, in the surface cut along `ē`, and keep `v`
fixed. This gives two `G`-normal
`O`-arcs that meet only in `v` and are homotopic to `ē`. Their union `K` meets each region incident
with `f` (`exists_loop_sides`).
If no `G`-normal null-homotopic `O`-arc with at most one vertex has an edge inside, then `ē` is not
null-homotopic
(`closure_loop_not_null`), so `K` is not planar.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

/-- An `O`-arc in the boundary is a cuff. -/
theorem isCuff_of_isOArc_subset_bd {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y) {X : Set Y}
  (hO : IsOArc X)
    (hs : X ⊆ bd Y) : IsCuff X := by
  have : T2Space Y := hY.2.1
  obtain ⟨x, hx⟩ := (isConnected_of_isOArc hO).1
  have hc : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨x, hs hx, rfl⟩
  obtain ⟨φ⟩ := (cuff_statement.{u} Y hY).2.2 _ hc
  have hsub : X ⊆ connectedComponentIn (bd Y) x :=
    (isConnected_of_isOArc hO).isPreconnected.subset_connectedComponentIn hx hs
  have := oarc_eq φ hO hsub
  rw [this]
  exact hc

section

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- Push a surface off a cuff `C` that lies over an `O`-arc `F`, away from a closed set `W` of the
target which meets `C` only over
the point `v`. -/
theorem exists_side_push (hY : IsSurface Y) {ψ : Y → S} (hψ : Continuous ψ) {F W : Set S} {C C' :
  Set Y} {v : S} (hCO : IsOArc C)
    (hCb : C ⊆ bd Y) (hC'c : IsClosed C') (hdis : Disjoint C C') (hsub : ψ ⁻¹' F ⊆ C ∪ C')
      (hWc : IsClosed W)
    (hvW : ∀ y ∈ C, ψ y ∈ W → ψ y = v) (hvW' : v ∈ W) :
    ∃ H : 𝕀 × Y → Y, Continuous H ∧ (∀ y, H (0, y) = y) ∧ Injective (fun y => H (1, y)) ∧
      (∀ p, ∀ y ∈ C, ψ y = v → H (p, y) = y) ∧
      (∀ y ∈ C, ψ y ≠ v → ψ (H (1, y)) ∉ F ∧ ψ (H (1, y)) ∉ W) ∧
      ∀ y ∈ C, ψ y ≠ v → ∃ N ∈ 𝓝 y, ∀ y' ∈ N, y' ∉ C → ∃ y'' ∈ C, ψ y'' ≠ v ∧ JoinedIn (F ∪ W)ᶜ
        (ψ y') (ψ (H (1, y''))) := by
  obtain ⟨φ⟩ := id hCO
  let Z : Set Y := ψ ⁻¹' W ∪ C'
  have hZ : IsClosed Z := (hWc.preimage hψ).union hC'c
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_taper_sides hY
    (isCuff_of_isOArc_subset_bd hY hCO hCb) φ hZ
  have hoff : ∀ y ∈ C, ψ y ≠ v → y ∉ Z := fun y hy hv hz =>
    hz.elim (fun h => hv (hvW y hy h)) fun h => disjoint_left.mp hdis hy h
  have hin : ∀ z, z ∈ Z → z ∈ ψ ⁻¹' W ∪ C' := fun _ h => h
  have hout : ∀ z, z ∉ Z → z ∉ C → ψ z ∉ F ∧ ψ z ∉ W := fun z hz hzC => by
    refine ⟨fun hF => ?_, fun hW => hz (.inl hW)⟩
    exact (hsub hF).elim hzC fun h => hz (.inr h)
  refine ⟨H, h1, h2, h3, fun p y hy hv => h7 p y (.inl ?_), fun y hy hv => ?_, fun y hy hv => ?_⟩
  · change ψ y ∈ W
    rw [hv]
    exact hvW'
  · have hn : H (1, y) ∉ Z := fun h => hoff y hy hv (h5 y h)
    exact hout _ hn fun h => hn (h6 y h)
  · obtain ⟨N, hN, hcap⟩ := h8 y hy (hoff y hy hv)
    refine ⟨N, hN, fun y' hy' hyC => ?_⟩
    obtain ⟨y'', hy''C, γ, hγ⟩ := hcap y' hy' hyC
    have hend : H (1, y'') ∈ Zᶜ ∩ Cᶜ := by simpa using hγ 1
    refine ⟨y'', hy''C, fun hv' => ?_, γ.map hψ, fun t => ?_⟩
    · have hzy : y'' ∈ Z := .inl (by
        change ψ y'' ∈ W
        rw [hv']
        exact hvW')
      apply hend.2
      rw [h7 1 y'' hzy]
      exact hy''C
    · have := hout _ (hγ t).1 (hγ t).2
      simpa [not_or] using this

variable [T2Space S]

/-- The pushed loop is an `O`-arc. -/
theorem isOArc_pushed_loop {ψ : Y → S} (hψ : Continuous ψ) {F W : Set S} {C : Set Y} {v : S} {H : 𝕀
  × Y → Y} (hH : Continuous H)
    (hi : Injective (fun y => H (1, y))) (hfix : ∀ p, ∀ y ∈ C, ψ y = v → H (p, y) = y)
    (hpush : ∀ y ∈ C, ψ y ≠ v → ψ (H (1, y)) ∉ F ∧ ψ (H (1, y)) ∉ W) (hinj : InjOn ψ (ψ ⁻¹' F)ᶜ)
      (hvW : v ∈ W)
    {ξ : 𝕀 → Y} (hξ : Continuous ξ) (hξC : ∀ t, ξ t ∈ C) {a : 𝕀 → S} (hξa : ∀ t, ψ (ξ t) = a t)
      (ha0 : a 0 = v) (ha1 : a 1 = v)
    (hinja : InjOn a (Ioo 0 1)) (hne : ∀ t ∈ Ioo (0 : 𝕀) 1, a t ≠ v) :
    IsOArc (range fun t => ψ (H (1, ξ t))) := by
  have hzero : ψ (H (1, ξ 0)) = v := by
    rw [hfix 1 _ (hξC 0) (by rw [hξa, ha0]), hξa, ha0]
  have hone : ψ (H (1, ξ 1)) = v := by
    rw [hfix 1 _ (hξC 1) (by rw [hξa, ha1]), hξa, ha1]
  have hval : ∀ t ∈ Ioo (0 : 𝕀) 1, ψ (H (1, ξ t)) ∉ F ∧ ψ (H (1, ξ t)) ∉ W := fun t ht =>
    hpush _ (hξC t) (by rw [hξa]; exact hne t ht)
  refine isOArc_of_loop (m := fun t => ψ (H (1, ξ t))) (hψ.comp (hH.comp (by fun_prop)))
    (hzero.trans hone.symm) ?_ ?_
  · intro t ht t' ht' he
    have h1 := hinj (hval t ht).1 (hval t' ht').1 he
    have h2 := hi h1
    apply hinja ht ht'
    rw [← hξa, ← hξa, h2]
  · intro t ht he
    apply (hval t ht).2
    change ψ (H (1, ξ t)) = ψ (H (1, ξ 0)) at he
    rw [he, hzero]
    exact hvW

end

/-- A loop that is homotopic, through loops, to a curve in a closed disc inside `Z` is
null-homotopic in `Z`. -/
theorem null_of_loop_homotopy {W : Type u} [TopologicalSpace W] [T2Space W] {A : 𝕀 × 𝕀 → W}
  (hA : Continuous A)
    (he : ∀ p, A (0, p) = A (1, p)) (hinj : InjOn (fun t => A (t, 0)) (Ioo 0 1)) (hne : ∀ t ∈ Ioo
      (0 : 𝕀) 1, A (t, 0) ≠ A (0, 0))
    {Z Δ : Set W} (hz : ∀ q, A q ∈ Z) (hΔ : IsClosedDisc Δ) (hΔZ : Δ ⊆ Z) (h1 : ∀ t, A (t, 1) ∈ Δ) :
    IsNullHomotopicOArcIn Z (range fun t => A (t, 0)) := by
  obtain ⟨K, hK, hKe⟩ := exists_circle_descent hA he
  let c : Circle → W := fun w => K (w, 0)
  have hc : Continuous c := hK.comp (continuous_id.prodMk continuous_const)
  have hval : ∀ t : 𝕀, c (ee t.1) = A (t, 0) := fun t => hKe t 0
  have hrep : ∀ w : Circle, ∃ t : 𝕀, (t = 0 ∨ t ∈ Ioo (0 : 𝕀) 1) ∧ ee t.1 = w := by
    intro w
    obtain ⟨x, rfl⟩ := ee_surjective w
    have h2 : ee (Int.fract x) = ee x := ee_eq_iff.mpr ⟨-⌊x⌋, by
      rw [Int.fract]
      push_cast
      ring⟩
    refine ⟨⟨Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, ?_, h2⟩
    by_cases h3 : Int.fract x = 0
    · exact .inl (Subtype.ext h3)
    · exact .inr ⟨Subtype.mk_lt_mk.mpr (lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h3)),
        Subtype.mk_lt_mk.mpr (Int.fract_lt_one x)⟩
  have hci : Injective c := by
    intro w w' hw
    obtain ⟨t, ht, rfl⟩ := hrep w
    obtain ⟨t', ht', rfl⟩ := hrep w'
    rw [hval, hval] at hw
    rcases ht with rfl | ht <;> rcases ht' with rfl | ht'
    · rfl
    · exact absurd hw.symm (hne t' ht')
    · exact absurd hw (hne t ht)
    · rw [hinj ht ht' hw]
  have hrange : range c = range fun t => A (t, 0) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨t, -, rfl⟩ := hrep w
      exact ⟨t, (hval t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨ee t.1, hval t⟩
  rw [← hrange]
  have hemb : IsEmbedding c := (hc.isClosedEmbedding hci).isEmbedding
  refine ⟨hemb.toHomeomorph, ?_⟩
  let d : C(Circle, W) := ⟨fun w => K (w, 1), hK.comp (continuous_id.prodMk continuous_const)⟩
  have hd : ClosedCurveIsNullHomotopicIn Δ d := hΔ.isSimplyConnectedSet.2 d (by
    rintro _ ⟨w, rfl⟩
    obtain ⟨t, -, rfl⟩ := hrep w
    change K (ee t.1, 1) ∈ Δ
    rw [hKe]
    exact h1 t)
  refine null_of_homotopic hΔZ ⟨⟨K, hK⟩, fun q => ?_, fun w => rfl, fun w => rfl⟩ hd
  obtain ⟨w, s⟩ := q
  obtain ⟨t, -, rfl⟩ := hrep w
  change K (ee t.1, s) ∈ Z
  rw [hKe]
  exact hz _

/-- No `G`-normal null-homotopic `O`-arc with at most one vertex has an edge of `G` inside. -/
def NoEdgeInSmallDisc {S : Type u} [TopologicalSpace S] (G : Drawing S) : Prop :=
  ¬ ∃ F e : Set S, G.IsNormal F ∧ IsNullHomotopicOArc F ∧ (G.V ∩ F).ncard ≤ 1 ∧ e ∈ G.E
    ∧ IsInsideOArc e F

variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- The facts on a loop that the pushes use. -/
theorem loop_facts (hS : IsSurface S) {G : Drawing S} {f : Set S} {v : S} (hf : f ∈ G.E)
  (hcap : closure f ∩ G.V = {v}) :
    ∀ x ∈ closure f, x ∈ G.U \ f → x = v := by
  have : T2Space S := hS.2.1
  rintro x hx ⟨-, hxf⟩
  by_contra hne
  apply hxf
  rw [← G.closure_diff_V hf]
  refine ⟨hx, fun hV => hne ?_⟩
  have : x ∈ closure f ∩ G.V := ⟨hx, hV⟩
  rw [hcap] at this
  exact this

omit [T1Space S] in
/-- A parametrisation of a loop from `v`. -/
theorem exists_loop_param (hS : IsSurface S) {G : Drawing S} {f : Set S} {v : S} (hf : f ∈ G.E)
  (hcap : closure f ∩ G.V = {v}) :
    ∃ a : 𝕀 → S, Continuous a ∧ a 0 = v ∧ a 1 = v ∧ range a = closure f ∧ InjOn a (Ioo 0 1)
      ∧ ∀ t ∈ Ioo (0 : 𝕀) 1, a t ≠ v := by
  have : T2Space S := hS.2.1
  obtain ⟨a, hc, h0, h1, hi, hrange, hcl, -⟩ := GraphMinor.GM06.exists_edge_param_isLink G hf
  have h0' : a 0 ∈ closure f ∩ G.V := ⟨hcl ▸ mem_range_self 0, h0⟩
  have h1' : a 1 ∈ closure f ∩ G.V := ⟨hcl ▸ mem_range_self 1, h1⟩
  rw [hcap] at h0' h1'
  refine ⟨a, hc, h0', h1', hcl.symm, hi, fun t ht he => ?_⟩
  have h2 : a t ∈ f := hrange ▸ mem_image_of_mem a ht
  have h3 : a t ∈ closure f \ G.V := by
    rw [G.closure_diff_V hf]
    exact h2
  exact h3.2 (he ▸ (show v ∈ G.V from by
    have : v ∈ closure f ∩ G.V := by rw [hcap]; rfl
    exact this.2))

omit [T1Space S] in
/-- A loop off the boundary is not null-homotopic, if no small disc holds an edge. -/
theorem closure_loop_not_null (hS : IsSurface S) [ConnectedSpace S] {a₀ b₀ c₀ : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a₀ b₀ c₀))
    (hns : ¬ IsSphere S) {G : Drawing S} {f : Set S} {v : S} (hf : f ∈ G.E) (hcap : closure f ∩ G.V
      = {v})
    (hO : IsOArc (closure f)) (hoff : Disjoint (closure f) (bd S)) (hred : NoEdgeInSmallDisc G) :
    ¬ IsNullHomotopicOArc (closure f) := by
  classical
  intro hnull
  have ht2 : T2Space S := hS.2.1
  have hcpt : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨e⟩ := hm
  set F := closure f with hFdef
  obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hS hO hnull
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := fun x hx => by
    by_contra hn
    exact disjoint_left.mp hoff (hbd ▸ hx) hn
  obtain ⟨hcl, hY, hbdY⟩ := remove_disc_homeo hS e hΔ hint
  let Y := ↥(discInt Δ)ᶜ
  let ψ : Y → S := Subtype.val
  have hψe : IsEmbedding ψ := IsEmbedding.subtypeVal
  have hψc : Continuous ψ := continuous_subtype_val
  have hFsub : F ⊆ range ψ := by
    rw [Subtype.range_val_subtype]
    exact fun x hx hi => hi.2 (hbd ▸ hx)
  have hCO : IsOArc (ψ ⁻¹' F) := IsOArc.pull_of_embedding hψe hO hFsub
  have hCb : ψ ⁻¹' F ⊆ bd Y := fun y hy => by
    rw [hbdY]
    exact .inr (hbd ▸ hy)
  obtain ⟨a, hac, ha0, ha1, har, hai, hane⟩ := exists_loop_param hS hf hcap
  have haF : ∀ t, a t ∈ F := fun t => by
    rw [hFdef, ← har]
    exact mem_range_self t
  let ξ : 𝕀 → Y := fun t => ⟨a t, by
    obtain ⟨y, hy⟩ := hFsub (haF t)
    rw [← hy]
    exact y.2⟩
  have hξ : Continuous ξ := hac.subtype_mk _
  have hW : IsClosed (G.U \ f) := isClosed_U_sdiff_edge G hf
  have hv : v ∈ closure f ∩ G.V := by rw [hcap]; rfl
  have hvW : v ∈ G.U \ f := ⟨G.V_subset_U hv.2, fun h => (hf.2.1 h).2 hv.2⟩
  obtain ⟨H, h1, h2, h3, h4, h5, -⟩ := exists_side_push hY hψc (F := F) (W := G.U \ f) (C' := ∅) (v
    := v) hCO hCb
    isClosed_empty (disjoint_empty _) (subset_union_left) hW (fun y hy hyW
      => loop_facts hS hf hcap _ hy hyW) hvW
  let σ : 𝕀 → S := fun t => ψ (H (1, ξ t))
  have hσc : Continuous σ := hψc.comp (h1.comp (by fun_prop))
  have hσO : IsOArc (range σ) := isOArc_pushed_loop hψc h1 h3 h4 h5 hψe.injective.injOn hvW hξ
    (fun t => haF t)
    (fun t => rfl) ha0 ha1 hai hane
  have hσ0 : σ 0 = v := by
    have := h4 1 (ξ 0) (haF 0) ha0
    change ψ (H (1, ξ 0)) = v
    rw [this]
    exact ha0
  have hσ1 : σ 1 = v := by
    have := h4 1 (ξ 1) (haF 1) ha1
    change ψ (H (1, ξ 1)) = v
    rw [this]
    exact ha1
  have hσoff : ∀ t ∈ Ioo (0 : 𝕀) 1, σ t ∉ F ∧ σ t ∉ G.U \ f := fun t ht => h5 _ (haF t) (hane t ht)
  have hend : ∀ t : 𝕀, t ∉ Ioo (0 : 𝕀) 1 → σ t = v := fun t ht => by
    have h6 : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    rcases h6 with rfl | rfl
    · exact hσ0
    · exact hσ1
  have hUoff : ∀ x ∈ range σ, x ∈ G.U → x = v := by
    rintro _ ⟨t, rfl⟩ hU
    by_cases ht : t ∈ Ioo (0 : 𝕀) 1
    · obtain ⟨h6, h7⟩ := hσoff t ht
      exact absurd ⟨hU, fun hf' => h6 (subset_closure hf')⟩ h7
    · exact hend t ht
  have hnorm : G.IsNormal (range σ) := by
    rintro x ⟨hx, hU⟩
    rw [hUoff x hx hU]
    exact hv.2
  have hcount : (G.V ∩ range σ).ncard ≤ 1 := by
    have : G.V ∩ range σ ⊆ {v} := fun x hx => hUoff x hx.2 (G.V_subset_U hx.1)
    simpa using ncard_le_ncard this
  -- `σ` is null-homotopic, by the homotopy back to `a`.
  let A : 𝕀 × 𝕀 → Y := fun q => H (q.2, ξ q.1)
  have hAc : Continuous A := h1.comp (by fun_prop)
  have hA0 : ∀ p, A (0, p) = A (1, p) := fun p => by
    have h6 : ξ 0 = ξ 1 := Subtype.ext (ha0.trans ha1.symm)
    simp only [A, h6]
  let B : 𝕀 × 𝕀 → S := fun q => ψ (A (q.1, unitInterval.symm q.2))
  have hBc : Continuous B := hψc.comp (hAc.comp (by fun_prop))
  have hnullσ : IsNullHomotopicOArc (range σ) := by
    have hB0 : (fun t => B (t, 0)) = σ := by
      funext t
      simp [B, A, σ]
    have hinjB : InjOn (fun t => B (t, 0)) (Ioo 0 1) := by
      rw [hB0]
      intro t ht t' ht' he
      have h6 : H (1, ξ t) = H (1, ξ t') := hψe.injective he
      have h7 := h3 h6
      exact Subtype.ext (hai ht ht' (congrArg ψ h7) ▸ rfl)
    have hneB : ∀ t ∈ Ioo (0 : 𝕀) 1, B (t, 0) ≠ B (0, 0) := fun t ht he => by
      have h6 : B (t, 0) = σ t := congrFun hB0 t
      have h7 : B (0, 0) = σ 0 := congrFun hB0 0
      rw [h6, h7, hσ0] at he
      exact (hσoff t ht).2 (he ▸ hvW)
    have := null_of_loop_homotopy hBc (fun p => congrArg ψ (hA0 _)) hinjB hneB (Z := univ) (Δ := Δ)
      (fun _ => mem_univ _) hΔ (subset_univ _) (fun t => by
        have : B (t, 1) = a t := by
          simp only [B, A, unitInterval.symm_one, h2]
          rfl
        rw [this]
        have : a t ∈ discBd Δ := hbd ▸ haF t
        exact Surface.discBd_subset _ this)
    rwa [hB0] at this
  obtain ⟨Δ₃, hΔ₃, hbd₃⟩ := nullHomotopicOArc_bounds_disc hS hσO hnullσ
  have hfoff : Disjoint f (discBd Δ₃) := by
    rw [hbd₃, disjoint_left]
    intro x hx hxr
    have hv' := hUoff x hxr (G.closure_subset_U hf (subset_closure hx))
    exact (hf.2.1 hx).2 (hv' ▸ hv.2)
  have hfne : f.Nonempty := hf.2.2.1.nonempty
  have hfpre : IsPreconnected f := hf.2.2.1.isConnected.isPreconnected
  rcases hΔ₃.side hman hfpre hfoff with hin | hdj
  · refine hred ⟨range σ, f, hnorm, hnullσ, hcount, hf, fun x hx => .inl ⟨hnullσ, Δ₃, hΔ₃, hbd₃,
      (hin hx).1, ?_⟩⟩
    exact fun hc => disjoint_left.mp hfoff hx (hbd₃ ▸ hc)
  · have hIoff : Disjoint (discInt Δ) (discBd Δ₃) := by
      rw [hbd₃, disjoint_left]
      rintro x hx ⟨t, rfl⟩
      exact (H (1, ξ t)).2 hx
    rcases hΔ₃.side hman hΔ.isPreconnected_discInt hIoff with hin | hdj'
    · obtain ⟨x, hx⟩ := hfne
      have h6 : x ∈ Δ := by
        have : x ∈ discBd Δ := hbd ▸ subset_closure hx
        exact Surface.discBd_subset _ this
      have h7 := closure_minimal (hin.trans (discInt_subset Δ₃)) hΔ₃.isCompact.isClosed
        (hΔ.subset_closure_discInt h6)
      exact disjoint_left.mp hdj hx h7
    · -- The disc `Δ₃` lies in the surface `Y`, so the cuff of `Y` over `F` bounds a disc of `Y`.
      have hY2 : T2Space Y := hY.2.1
      have hYc : CompactSpace Y := hY.1
      have hrangeΔ : Δ₃ ⊆ range ψ := by
        rw [Subtype.range_val_subtype]
        exact fun x hx hi => disjoint_left.mp hdj' hi hx
      have hdiscY : IsClosedDisc (ψ ⁻¹' Δ₃) :=
        isClosedDisc_preimage_of_subset_range hψc hψe.injective hΔ₃ hrangeΔ
      have hnullY : IsNullHomotopicOArc (ψ ⁻¹' F) := by
        have hA00 : (fun t => A (t, 0)) = ξ := by
          funext t
          simp [A, h2]
        have hrξ : range ξ = ψ ⁻¹' F := by
          ext y
          constructor
          · rintro ⟨t, rfl⟩
            exact haF t
          · intro hy
            have hy' : y.1 ∈ range a := by
              rw [har]
              exact hy
            obtain ⟨t, ht⟩ := hy'
            exact ⟨t, Subtype.ext ht⟩
        have := null_of_loop_homotopy hAc hA0 (fun t ht t' ht' he => hai ht ht' (by
          have h6 := congrArg ψ he
          simp only [A, h2] at h6
          exact h6))
          (fun t ht he => hane t ht (by
            have h6 := congrArg ψ he
            have h7 : ψ (A (t, 0)) = a t := by
              simp only [A, h2]
              rfl
            have h8 : ψ (A (0, 0)) = a 0 := by
              simp only [A, h2]
              rfl
            rw [h7, h8, ha0] at h6
            exact h6)) (Z := univ) (fun _ => mem_univ _) hdiscY (subset_univ _) (fun t => by
            change σ t ∈ Δ₃
            have : σ t ∈ discBd Δ₃ := by
              rw [hbd₃]
              exact mem_range_self t
            exact Surface.discBd_subset _ this)
        rwa [hA00, hrξ] at this
      obtain ⟨Δ_Y, hΔY, hbdY'⟩ := nullHomotopicOArc_bounds_disc hY hCO hnullY
      obtain ⟨hΔi, hbi⟩ := isClosedDisc_image_of_injOn hΔY hψc hψe.injective.injOn
      have hbi' : discBd (ψ '' Δ_Y) = discBd Δ := by
        rw [hbi, hbdY', image_preimage_eq_of_subset hFsub, hbd]
      have hEq := eq_of_discBd_eq hS hns hΔi hΔ hbi'
      obtain ⟨p, hp⟩ : (discInt Δ).Nonempty := by
        obtain ⟨hh, g, cc⟩ := hΔ.exists_isChart
        refine ⟨g 0, cc.gm (by simp), fun hb => ?_⟩
        have h2' : hh (g 0) ∈ Metric.sphere (0 : ℂ) 1 := cc.bd ▸ mem_image_of_mem hh hb
        rw [cc.hg (by simp)] at h2'
        simp at h2'
      have hpi : p ∈ ψ '' Δ_Y := hEq ▸ hp.1
      obtain ⟨y, -, rfl⟩ := hpi
      exact y.2 hp

/-- The facts on a push off a cuff `C`, from `exists_side_push`. -/
def IsSidePush {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S] (ψ : Y → S) (F W : Set S)
  (v : S) (C : Set Y)
    (H : 𝕀 × Y → Y) : Prop :=
  Continuous H ∧ (∀ y, H (0, y) = y) ∧ Injective (fun y => H (1, y)) ∧ (∀ p, ∀ y ∈ C, ψ y = v → H
    (p, y) = y) ∧
    (∀ y ∈ C, ψ y ≠ v → ψ (H (1, y)) ∉ F ∧ ψ (H (1, y)) ∉ W) ∧
    ∀ y ∈ C, ψ y ≠ v → ∃ N ∈ 𝓝 y, ∀ y' ∈ N, y' ∉ C → ∃ y'' ∈ C, ψ y'' ≠ v ∧ JoinedIn (F ∪ W)ᶜ
      (ψ y') (ψ (H (1, y'')))

omit [T1Space S] in
/-- The union of the two pushes of a loop. -/
theorem sides_of_pushes (hS : IsSurface S) [ConnectedSpace S] {a₀ b₀ c₀ : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a₀ b₀ c₀))
    (hns : ¬ IsSphere S) {G : Drawing S} {f : Set S} {v : S} (hf : f ∈ G.E) (hcap : closure f ∩ G.V
      = {v})
    (hO : IsOArc (closure f)) (hoff : Disjoint (closure f) (bd S)) (hred : NoEdgeInSmallDisc G)
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] {ψ : Y → S} (hψ : Continuous ψ)
      (hsurj : Surjective ψ)
    (hinj : InjOn ψ (ψ ⁻¹' closure f)ᶜ) {a : 𝕀 → S} {ξ η : 𝕀 → Y} (hξ : Continuous ξ)
      (hη : Continuous η)
    (hξa : ∀ t, ψ (ξ t) = a t) (hηa : ∀ t, ψ (η t) = a t) (ha0 : a 0 = v) (ha1 : a 1 = v)
      (har : range a = closure f)
    (hai : InjOn a (Ioo 0 1)) (hane : ∀ t ∈ Ioo (0 : 𝕀) 1, a t ≠ v) (hcov : ∀ y, ψ y ∈ closure f
      → ∃ t, y = ξ t ∨ y = η t)
    {C₁ C₂ : Set Y} {H₁ H₂ : 𝕀 × Y → Y} (hp₁ : IsSidePush ψ (closure f) (G.U \ f) v C₁ H₁)
      (hp₂ : IsSidePush ψ (closure f) (G.U \ f) v C₂ H₂)
    (hξC : ∀ t, ξ t ∈ C₁) (hηC : ∀ t, η t ∈ C₂) (hC₁ : C₁ ⊆ ψ ⁻¹' closure f)
      (hC₂ : C₂ ⊆ ψ ⁻¹' closure f)
    (hK₁ : ∀ y ∈ C₁, ψ y ≠ v → ψ (H₁ (1, y)) ∈ (range fun t => ψ (H₁ (1, ξ t))) ∪ range fun t => ψ
      (H₂ (1, η t)))
    (hK₂ : ∀ y ∈ C₂, ψ y ≠ v → ψ (H₂ (1, y)) ∈ (range fun t => ψ (H₁ (1, ξ t))) ∪ range fun t => ψ
      (H₂ (1, η t))) :
    ∃ K : Set S, IsSolid K ∧ IsConnected K ∧ G.IsNormal K ∧ G.V ∩ K ⊆ {v} ∧ ¬ IsPlanar K ∧
      ∀ x ∈ f, ∀ ρ ∈ G.R, x ∈ closure ρ → (ρ ∩ K).Nonempty := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hv : v ∈ closure f ∩ G.V := by rw [hcap]; rfl
  have hvW : v ∈ G.U \ f := ⟨G.V_subset_U hv.2, fun h => (hf.2.1 h).2 hv.2⟩
  obtain ⟨h1c, h10, h1i, h1f, h1p, h1t⟩ := hp₁
  obtain ⟨h2c, h20, h2i, h2f, h2p, h2t⟩ := hp₂
  have hO₁ : IsOArc (range fun t => ψ (H₁ (1, ξ t))) :=
    isOArc_pushed_loop hψ h1c h1i h1f h1p hinj hvW hξ hξC hξa ha0 ha1 hai hane
  have hO₂ : IsOArc (range fun t => ψ (H₂ (1, η t))) :=
    isOArc_pushed_loop hψ h2c h2i h2f h2p hinj hvW hη hηC hηa ha0 ha1 hai hane
  have hend : ∀ {C : Set Y} {H : 𝕀 × Y → Y} {ζ : 𝕀 → Y}, (∀ p, ∀ y ∈ C, ψ y = v → H (p, y) = y) →
    (∀ t, ζ t ∈ C) →
      (∀ t, ψ (ζ t) = a t) → (∀ t : 𝕀, t ∉ Ioo (0 : 𝕀) 1 → ∀ p, ψ (H (p, ζ t)) = v) := by
    intro C H ζ hfx hζ hζa t ht p
    have h6 : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    have h7 : ψ (ζ t) = v := by
      rcases h6 with rfl | rfl
      · rw [hζa, ha0]
      · rw [hζa, ha1]
    rw [hfx p _ (hζ t) h7, h7]
  have hUoff : ∀ {C : Set Y} {H : 𝕀 × Y → Y} {ζ : 𝕀 → Y}, (∀ p, ∀ y ∈ C, ψ y = v → H (p, y) = y) →
      (∀ y ∈ C, ψ y ≠ v → ψ (H (1, y)) ∉ closure f ∧ ψ (H (1, y)) ∉ G.U \ f) → (∀ t, ζ t ∈ C) →
      (∀ t, ψ (ζ t) = a t) → ∀ x ∈ (range fun t => ψ (H (1, ζ t))), x ∈ G.U → x = v := by
    rintro C H ζ hfx hps hζ hζa _ ⟨t, rfl⟩ hU
    by_cases ht : t ∈ Ioo (0 : 𝕀) 1
    · obtain ⟨h6, h7⟩ := hps _ (hζ t) (by rw [hζa]; exact hane t ht)
      exact absurd ⟨hU, fun hf' => h6 (subset_closure hf')⟩ h7
    · exact hend hfx hζ hζa t ht 1
  have hU₁ := hUoff h1f h1p hξC hξa
  have hU₂ := hUoff h2f h2p hηC hηa
  have hv₁ : v ∈ range fun t => ψ (H₁ (1, ξ t)) := ⟨0, hend h1f hξC hξa 0 (fun h => h.1.false) 1⟩
  have hv₂ : v ∈ range fun t => ψ (H₂ (1, η t)) := ⟨0, hend h2f hηC hηa 0 (fun h => h.1.false) 1⟩
  have hUK : ∀ x ∈ (range fun t => ψ (H₁ (1, ξ t))) ∪ range fun t => ψ (H₂ (1, η t)), x ∈ G.U → x
    = v := by
    rintro x (hx | hx) hU
    · exact hU₁ x hx hU
    · exact hU₂ x hx hU
  refine ⟨_, theorem_11_6_proof hS (isSolid_of_isOArc hS hO₁) (isSolid_of_isOArc hS hO₂), ⟨⟨v,
    .inl hv₁⟩,
    (isConnected_of_isOArc hO₁).isPreconnected.union v hv₁ hv₂ (isConnected_of_isOArc
      hO₂).isPreconnected⟩, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hU⟩
    rw [hUK x hx hU]
    exact hv.2
  · rintro x ⟨hxV, hx⟩
    exact hUK x hx (G.V_subset_U hxV)
  · intro hpl
    obtain ⟨Δ, hΔ, hsub⟩ := IsPlanar.mono hpl (subset_union_left (s := range fun t => ψ (H₁
      (1, ξ t))) (t := range fun t => ψ (H₂ (1, η t))))
    let A : 𝕀 × 𝕀 → S := fun q => ψ (H₁ (q.2, ξ q.1))
    have hAc : Continuous A := hψ.comp (h1c.comp (by fun_prop))
    have hA0 : (fun t => A (t, 0)) = a := by
      funext t
      simp only [A, h10, hξa]
    have hn := null_of_loop_homotopy hAc (fun p => by
        rw [show A (0, p) = v from hend h1f hξC hξa 0 (fun h => h.1.false) p,
          show A (1, p) = v from hend h1f hξC hξa 1 (fun h => h.2.false) p])
      (by rw [hA0]; exact hai) (fun t ht => by
        have h6 : A (t, 0) = a t := congrFun hA0 t
        have h7 : A (0, 0) = a 0 := congrFun hA0 0
        rw [h6, h7, ha0]
        exact hane t ht) (Z := univ) (fun _ => mem_univ _) hΔ (subset_univ _) (fun t => hsub ⟨t,
          rfl⟩)
    rw [hA0, har] at hn
    exact closure_loop_not_null hS hm hns hf hcap hO hoff hred hn
  · intro x hxf ρ hρ hxρ
    have hxF : x ∈ closure f := subset_closure hxf
    have hxv : x ≠ v := fun h => (hf.2.1 hxf).2 (h ▸ hv.2)
    obtain ⟨t, rfl⟩ : x ∈ range a := by rw [har]; exact hxF
    have htI : t ∈ Ioo (0 : 𝕀) 1 := by
      refine ⟨unitInterval.pos_iff_ne_zero.mpr fun h => hxv (by rw [h, ha0]),
        unitInterval.lt_one_iff_ne_one.mpr fun h => hxv (by rw [h, ha1])⟩
    obtain ⟨N₁, hN₁, hc₁⟩ := h1t (ξ t) (hξC t) (by rw [hξa]; exact hxv)
    obtain ⟨N₂, hN₂, hc₂⟩ := h2t (η t) (hηC t) (by rw [hηa]; exact hxv)
    let O := interior N₁ ∪ interior N₂
    have hOo : IsOpen O := isOpen_interior.union isOpen_interior
    let T := ψ '' Oᶜ
    have hT : IsClosed T := (hOo.isClosed_compl.isCompact.image hψ).isClosed
    have hxT : a t ∉ T := by
      rintro ⟨y, hy, he⟩
      apply hy
      obtain ⟨s, hs⟩ := hcov y (by rw [he]; exact hxF)
      have hsI : ∀ {ζ : 𝕀 → Y}, (∀ s, ψ (ζ s) = a s) → y = ζ s → s = t := by
        intro ζ hζ hys
        have h6 : a s = a t := by rw [← hζ, ← hys, he]
        have hsI : s ∈ Ioo (0 : 𝕀) 1 := by
          refine ⟨unitInterval.pos_iff_ne_zero.mpr fun h => hxv (by rw [← h6, h, ha0]),
            unitInterval.lt_one_iff_ne_one.mpr fun h => hxv (by rw [← h6, h, ha1])⟩
        exact hai hsI htI h6
      rcases hs with hs | hs
      · have := hsI hξa hs
        rw [hs, this]
        exact .inl (mem_interior_iff_mem_nhds.mpr hN₁)
      · have := hsI hηa hs
        rw [hs, this]
        exact .inr (mem_interior_iff_mem_nhds.mpr hN₂)
    obtain ⟨w, hwT, hwρ⟩ := mem_closure_iff.mp hxρ _ hT.isOpen_compl hxT
    obtain ⟨y', rfl⟩ := hsurj w
    have hy'O : y' ∈ O := by
      by_contra hn
      exact hwT ⟨y', hn, rfl⟩
    obtain ⟨z₀, -, hz₀⟩ := hρ
    have hwU : ψ y' ∈ univ \ G.U := by
      have := connectedComponentIn_subset _ _ (hz₀ ▸ hwρ)
      exact this
    have hoffF : ψ y' ∉ closure f := fun h => hwU.2 (G.closure_subset_U hf h)
    have hjoin : ∀ z, JoinedIn (closure f ∪ (G.U \ f))ᶜ (ψ y') z → z ∈ ρ := by
      intro z hj
      have hsubU : (closure f ∪ (G.U \ f))ᶜ ⊆ univ \ G.U := fun q hq => ⟨mem_univ _, fun hU => by
        by_cases hqf : q ∈ f
        · exact hq (.inl (subset_closure hqf))
        · exact hq (.inr ⟨hU, hqf⟩)⟩
      obtain ⟨γ, hγ⟩ := hj
      have hr : IsPreconnected (range γ) := isPreconnected_range γ.continuous
      have hrs : range γ ⊆ univ \ G.U := by
        rintro _ ⟨s, rfl⟩
        exact hsubU (hγ s)
      have hsub := hr.subset_connectedComponentIn (x := ψ y') ⟨0, by simp⟩ hrs
      rw [← connectedComponentIn_eq (hz₀ ▸ hwρ : ψ y' ∈ connectedComponentIn _ z₀), hz₀] at hsub
      exact hsub ⟨1, by simp⟩
    rcases hy'O with hy | hy
    · have hy1 : y' ∉ C₁ := fun h => hoffF (hC₁ h)
      obtain ⟨y'', hy''C, hy''v, hj⟩ := hc₁ y' (interior_subset hy) hy1
      exact ⟨_, hjoin _ hj, hK₁ y'' hy''C hy''v⟩
    · have hy1 : y' ∉ C₂ := fun h => hoffF (hC₂ h)
      obtain ⟨y'', hy''C, hy''v, hj⟩ := hc₂ y' (interior_subset hy) hy1
      exact ⟨_, hjoin _ hj, hK₂ y'' hy''C hy''v⟩

omit [T1Space S] in
/-- **The two sides of a loop.** See the module docstring. -/
theorem exists_loop_sides (hS : IsSurface S) [ConnectedSpace S] {a₀ b₀ c₀ : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a₀ b₀ c₀))
    (hns : ¬ IsSphere S) {G : Drawing S} {f : Set S} {v : S} (hf : f ∈ G.E) (hcap : closure f ∩ G.V
      = {v})
    (hO : IsOArc (closure f)) (hoff : Disjoint (closure f) (bd S)) (hred : NoEdgeInSmallDisc G) :
    ∃ K : Set S, IsSolid K ∧ IsConnected K ∧ G.IsNormal K ∧ G.V ∩ K ⊆ {v} ∧ ¬ IsPlanar K ∧
      ∀ x ∈ f, ∀ ρ ∈ G.R, x ∈ closure ρ → (ρ ∩ K).Nonempty := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hv : v ∈ closure f ∩ G.V := by rw [hcap]; rfl
  have hvW : v ∈ G.U \ f := ⟨G.V_subset_U hv.2, fun h => (hf.2.1 h).2 hv.2⟩
  have hvF : v ∈ closure f := hv.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hcut, hcase, Z₁, Z₂, u, c, X₁, Y₁, X₂, Y₂, h7, h8, hi, hun, huc, hfu,
    hfc⟩ := exists_cut_loop hS hO hoff
  have : CompactSpace Y := hY.1
  obtain ⟨a, ξ, η, hξ, hη, hξa, hηa, ha0, ha1, har, hai, hane, hne, hcov⟩
    := exists_loop_lifts hcut h7 h8 hi hun huc hfu hfc hvF
  have hψ := hcut.1
  have hsurj := hcut.2.1
  have hinj : InjOn ψ (ψ ⁻¹' closure f)ᶜ := hcut.2.2.1
  have hbdF : ψ ⁻¹' closure f ⊆ bd Y := hcut.2.2.2.2
  have hW : IsClosed (G.U \ f) := isClosed_U_sdiff_edge G hf
  have hvfact : ∀ {C : Set Y}, C ⊆ ψ ⁻¹' closure f → ∀ y ∈ C, ψ y ∈ G.U \ f → ψ y = v :=
    fun hC y hy hyW => loop_facts hS hf hcap _ (hC hy) hyW
  have hpush : ∀ {C C' : Set Y}, IsOArc C → C ⊆ ψ ⁻¹' closure f → IsClosed C' → Disjoint C C'
    → ψ ⁻¹' closure f ⊆ C ∪ C' →
      ∃ H, IsSidePush ψ (closure f) (G.U \ f) v C H := fun {C C'} h1 h2 h3 h4 h5 =>
    exists_side_push hY hψ h1 (h2.trans hbdF) h3 h4 h5 hW (hvfact h2) hvW
  rcases hcase with ⟨X, X', hdis, hXu, hXO, hXO', hXb, hXb'⟩ | hC
  · -- Two lifts of the loop: each one lies on its own `O`-arc.
    have main : ∀ {X X' : Set Y}, Disjoint X X' → X ∪ X' = ψ ⁻¹' closure f → IsOArc X → IsOArc X'
      → BijOn ψ X (closure f) →
        BijOn ψ X' (closure f) → (∀ t, ξ t ∈ X) → (∀ t, η t ∈ X') →
        ∃ K : Set S, IsSolid K ∧ IsConnected K ∧ G.IsNormal K ∧ G.V ∩ K ⊆ {v} ∧ ¬ IsPlanar K ∧
          ∀ x ∈ f, ∀ ρ ∈ G.R, x ∈ closure ρ → (ρ ∩ K).Nonempty := by
      intro X X' hdis hXu hXO hXO' hXb hXb' hξX hηX
      have hsub : X ⊆ ψ ⁻¹' closure f := hXu ▸ subset_union_left
      have hsub' : X' ⊆ ψ ⁻¹' closure f := hXu ▸ subset_union_right
      obtain ⟨H₁, hp₁⟩ := hpush hXO hsub (isCompact_of_isOArc hXO').isClosed hdis hXu.ge
      obtain ⟨H₂, hp₂⟩ := hpush hXO' hsub' (isCompact_of_isOArc hXO).isClosed hdis.symm
        (by
          rw [union_comm]
          exact hXu.ge)
      have hin : ∀ y ∈ X, ψ y ≠ v → y ∈ range ξ := fun y hy _ => by
        obtain ⟨t, rfl | rfl⟩ := hcov y (hsub hy)
        · exact mem_range_self t
        · exact absurd (hηX t) (disjoint_left.mp hdis hy)
      have hin' : ∀ y ∈ X', ψ y ≠ v → y ∈ range η := fun y hy _ => by
        obtain ⟨t, rfl | rfl⟩ := hcov y (hsub' hy)
        · exact absurd (hξX t) (disjoint_left.mp hdis.symm hy)
        · exact mem_range_self t
      refine sides_of_pushes hS hm hns hf hcap hO hoff hred hψ hsurj hinj hξ hη hξa hηa ha0 ha1 har
        hai hane hcov hp₁ hp₂ hξX hηX
        hsub hsub' (fun y hy hv' => ?_) fun y hy hv' => ?_
      · obtain ⟨t, rfl⟩ := hin y hy hv'
        exact .inl ⟨t, rfl⟩
      · obtain ⟨t, rfl⟩ := hin' y hy hv'
        exact .inr ⟨t, rfl⟩
    have hcX : IsClosed X := (isCompact_of_isOArc hXO).isClosed
    have hcX' : IsClosed X' := (isCompact_of_isOArc hXO').isClosed
    have hpre : IsPreconnected (range ξ) := isPreconnected_range hξ
    have hrs : range ξ ⊆ X ∪ X' := by
      rw [hXu]
      rintro _ ⟨t, rfl⟩
      change ψ (ξ t) ∈ closure f
      rw [hξa, ← har]
      exact mem_range_self t
    have hηin : ∀ t, η t ∈ X ∪ X' := fun t => by
      rw [hXu]
      change ψ (η t) ∈ closure f
      rw [hηa, ← har]
      exact mem_range_self t
    rcases subset_or_subset_of_closed hpre hcX hcX' hrs (fun x _ hx hx'
      => disjoint_left.mp hdis hx hx') with hsub | hsub
    · refine main hdis hXu hXO hXO' hXb hXb' (fun t => hsub ⟨t, rfl⟩) fun t =>
        (hηin t).resolve_left fun hc => hne t ?_
      exact hXb.injOn (hsub ⟨t, rfl⟩) hc (by rw [hξa, hηa])
    · refine main hdis.symm (by rwa [union_comm]) hXO' hXO hXb' hXb
        (fun t => hsub ⟨t, rfl⟩) fun t =>
        (hηin t).resolve_right fun hc => hne t ?_
      exact hXb'.injOn (hsub ⟨t, rfl⟩) hc (by rw [hξa, hηa])
  · -- One lift: the cuff goes twice around the loop.
    obtain ⟨H, hp⟩ := hpush hC subset_rfl isClosed_empty (disjoint_empty _) subset_union_left
    have hin : ∀ t, ξ t ∈ ψ ⁻¹' closure f := fun t => by
      change ψ (ξ t) ∈ closure f
      rw [hξa, ← har]
      exact mem_range_self t
    have hin' : ∀ t, η t ∈ ψ ⁻¹' closure f := fun t => by
      change ψ (η t) ∈ closure f
      rw [hηa, ← har]
      exact mem_range_self t
    have hK : ∀ y ∈ ψ ⁻¹' closure f, ψ y ≠ v → ψ (H (1, y)) ∈ (range fun t => ψ (H
      (1, ξ t))) ∪ range fun t => ψ (H (1, η t)) := by
      intro y hy _
      obtain ⟨t, rfl | rfl⟩ := hcov y hy
      · exact .inl ⟨t, rfl⟩
      · exact .inr ⟨t, rfl⟩
    exact sides_of_pushes hS hm hns hf hcap hO hoff hred hψ hsurj hinj hξ hη hξa hηa ha0 ha1 har
      hai hane hcov hp hp hin hin'
      subset_rfl subset_rfl hK hK

end GraphMinor.GM07
