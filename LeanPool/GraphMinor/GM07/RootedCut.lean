/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MultiCut
public import LeanPool.GraphMinor.GM07.CutFeasible
public import LeanPool.GraphMinor.GM07.SplitForest

/-!
# From a forest to a minor

The last line of step 2 of (9.1), page 243: "By (7.5), $\theta_r^{-1}(H')$ is
$\theta_r^{-1}(G_r)$-feasible. But that implies the conclusion of the theorem". Each component
of the forest in `G_r` is the image of a star of `H'` with centre at a vertex `v` of `H`, and its
image in `G` is the connected subgraph `φ(v)`. The edges
`e_i` give `φ(f_i)`.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

section Walks

variable {α : Type*} {β : Type*} {G : Graph α β}

theorem GraphWalk.exists_simple_suffix {u v x : α} (W : GraphWalk G u v) (hW : W.IsSimple)
  (hx : x ∈ W.support) : ∃ W' : GraphWalk G x v, W'.IsSimple := by
  induction W with
  | nil _ =>
    simp only [GraphWalk.support, List.mem_singleton] at hx
    subst hx
    exact ⟨_, hW⟩
  | cons hl rest ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hW⟩
    · exact ih hW.of_cons hx

theorem GraphWalk.exists_simple {u v : α} (W : GraphWalk G u v) : ∃ W' : GraphWalk G u v,
  W'.IsSimple := by
  induction W with
  | nil hv => exact ⟨.nil hv, by simp [GraphWalk.IsSimple, GraphWalk.support]⟩
  | @cons a b c e hl rest ih =>
    obtain ⟨W', hW'⟩ := ih
    by_cases ha : a ∈ W'.support
    · exact GraphWalk.exists_simple_suffix W' hW' ha
    · refine ⟨.cons hl W', ?_⟩
      simp only [GraphWalk.IsSimple, GraphWalk.support, List.nodup_cons]
      exact ⟨ha, hW'⟩

end Walks

section Component

variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- The component of a vertex. -/
theorem exists_component (Γ : Drawing X) {r : X} (hr : r ∈ Γ.V) :
    ∃ D : Drawing X, D.IsSubdrawing Γ ∧ D.IsConnected ∧ ∀ x, x ∈ D.V ↔ Nonempty
      (GraphWalk Γ.toGraph r x) := by
  classical
  set R : Set X := {x | Nonempty (GraphWalk Γ.toGraph r x)} with hR
  have hRV : R ⊆ Γ.V := by
    rintro x ⟨W⟩
    have key : ∀ {a b : X}, GraphWalk Γ.toGraph a b → a ∈ Γ.V → b ∈ Γ.V := fun W => by
      induction W with
      | nil h => exact fun _ => h
      | cons hl _ ih => exact fun _ => ih hl.2.2.1
    exact key W hr
  have hstep : ∀ {a c : X} {e : Set X}, a ∈ R → Γ.toGraph.IsLink e a c → c ∈ R := fun ⟨W⟩ hl =>
    ⟨W.append (.cons hl (.nil hl.2.2.1))⟩
  set 𝓕 : Set (Set X) := {e | closure e ∩ Γ.V ⊆ R} with h𝓕
  set D := Γ.span R 𝓕 with hD
  have hDV : D.V = R := by
    change Γ.spanV R 𝓕 = R
    rw [Drawing.spanV, inter_eq_left.mpr hRV]
    exact union_eq_left.mpr (iUnion₂_subset fun e he => he.1)
  have hDE : D.E = 𝓕 ∩ Γ.E := Γ.span_E _ _
  have hlift : ∀ {a b : X} (W : GraphWalk Γ.toGraph a b), a ∈ R → Nonempty
    (GraphWalk D.toGraph a b) := fun W => by
    induction W with
    | nil h =>
      intro ha
      exact ⟨.nil (show _ ∈ D.V by rw [hDV]; exact ha)⟩
    | @cons a c b e hl rest ih =>
      intro ha
      have hc : c ∈ R := hstep ha hl
      obtain ⟨W'⟩ := ih hc
      have hsub : closure e ∩ Γ.V ⊆ R := by
        rw [hl.2.2.2]
        rintro x (rfl | rfl)
        · exact ha
        · exact hc
      have hcap : closure e ∩ D.V = {a, c} := by
        rw [hDV, ← hl.2.2.2]
        apply Subset.antisymm
        · exact fun x hx => ⟨hx.1, hRV hx.2⟩
        · exact fun x hx => ⟨hx.1, hsub hx⟩
      have heD : e ∈ D.E := by
        rw [hDE]
        exact ⟨hsub, hl.1⟩
      have haD : a ∈ D.V := by
        rwa [hDV]
      have hcD : c ∈ D.V := by
        rwa [hDV]
      exact ⟨.cons ⟨heD, haD, hcD, hcap⟩ W'⟩
  have hrR : r ∈ R := ⟨.nil hr⟩
  have hrD : r ∈ D.V := by rwa [hDV]
  refine ⟨D, Γ.span_isSubdrawing _ _, ⟨⟨r, hrD⟩, fun u hu v hv => ?_⟩, fun x => by
    rw [hDV]
    rfl⟩
  rw [hDV] at hu hv
  obtain ⟨Wu⟩ := hu
  obtain ⟨Wv⟩ := hv
  obtain ⟨Wu'⟩ := hlift Wu hrR
  obtain ⟨Wv'⟩ := hlift Wv hrR
  exact ⟨Wu'.reverse.append Wv'⟩

end Component

section Matched

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
  [T2Space Y]

omit [T2Space X] in
/-- A pulled back drawing matches the drawing. -/
theorem matched_pullDrawing (Γ : Drawing Y) {f : X → Y} (hf : Continuous f) (hs : Surjective f)
  (hi : InjOn f (f ⁻¹' Γ.U)) :
    IsMatched (pullDrawing Γ hf hs hi) Γ f ∅ := by
  refine ⟨hf, hi, empty_subset _, fun _ _ => disjoint_empty _, ?_, ?_, ?_⟩
  · rw [sdiff_empty]
    exact image_preimage_eq _ hs
  · rw [sdiff_empty]
    exact image_preimage_eq _ hs
  · have h : (pullDrawing Γ hf hs hi).E = preimage f '' Γ.E := by
      change arcComponentsIn (f ⁻¹' Γ.U \ f ⁻¹' Γ.V) = _
      rw [← preimage_sdiff]
      exact arcComponentsIn_preimage hf hs Γ.isClosed_U hi sdiff_subset
    rw [h, image_image]
    have : (fun C => f '' (f ⁻¹' C)) = id := funext fun C => image_preimage_eq C hs
    change Γ.E = (fun C => f '' (f ⁻¹' C)) '' Γ.E
    rw [this, image_id]

omit [CompactSpace X] [T2Space X] [T2Space Y] in
/-- A homeomorphism of the drawing above. -/
theorem IsMatched.pre {Γ : Drawing X} {Γ' : Drawing Y} {f : X → Y} (m : IsMatched Γ Γ' f ∅)
  (α : X ≃ₜ X) :
    IsMatched (mapDrawingHomeo α Γ) Γ' (f ∘ α.symm) ∅ := by
  have hU : (f ∘ α.symm) '' (mapDrawingHomeo α Γ).U = f '' Γ.U := by
    change (f ∘ α.symm) '' (α '' Γ.U) = _
    rw [image_comp, ← image_comp α.symm, Homeomorph.symm_comp_self, image_id]
  have hV : (f ∘ α.symm) '' (mapDrawingHomeo α Γ).V = f '' Γ.V := by
    change (f ∘ α.symm) '' (α '' Γ.V) = _
    rw [image_comp, ← image_comp α.symm, Homeomorph.symm_comp_self, image_id]
  refine ⟨m.cont.comp α.symm.continuous, ?_, empty_subset _, fun _ _ => disjoint_empty _, ?_, ?_,
    ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    simp only [comp_apply, Homeomorph.symm_apply_apply] at he
    rw [m.inj hx hy he]
  · rw [sdiff_empty, hU]
    simpa using m.image_U
  · rw [sdiff_empty, hV]
    simpa using m.image_V
  · rw [mapDrawingHomeo_E, m.image_E, image_image]
    refine image_congr fun e _ => ?_
    rw [image_comp, ← image_comp α.symm, Homeomorph.symm_comp_self, image_id]

omit [CompactSpace X] [T2Space X] [T2Space Y] in
/-- A homeomorphism of the drawing below. -/
theorem IsMatched.post {Γ : Drawing X} {Γ' : Drawing Y} {f : X → Y} (m : IsMatched Γ Γ' f ∅)
  (e : Y ≃ₜ Y) :
    IsMatched Γ (mapDrawingHomeo e Γ') (e ∘ f) ∅ := by
  refine ⟨e.continuous.comp m.cont, fun x hx y hy he => m.inj hx hy (e.injective he),
    empty_subset _, fun _ _ => disjoint_empty _, ?_, ?_, ?_⟩
  · change _ = e '' Γ'.U
    rw [← m.image_U, image_comp]
  · change _ = e '' Γ'.V
    rw [← m.image_V, image_comp]
  · rw [mapDrawingHomeo_E, m.image_E, image_image]
    exact image_congr fun z _ => (image_comp e f z).symm

end Matched

variable {S S_r : Type u} [TopologicalSpace S] [TopologicalSpace S_r] [T2Space S] [CompactSpace
  S_r] [T2Space S_r]

/-- The forest in `G_r` gives the minor. -/
theorem isBoundaryRootedMinor_of_forest {Gd Hd : SurfaceDigraph S} (hVbd : Hd.G.V ∩ bd S
  = Gd.G.V ∩ bd S) {𝓔 : Set (Set S)} {θ : S_r → S} {G_r : Drawing S_r}
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r) {H₃ : Drawing S} {O : S → S} {Mid H'' : Drawing S_r} {w : S_r
      → S} (M : IsMatched Mid H₃ w ∅)
    (hsub : H''.IsSubdrawing G_r) (hhom : ForestsHomotopic Mid H'')
    (hwalkO : ∀ {x y : S}, GraphWalk H₃.toGraph x y → O x = O y)
    (hsimple : ∀ x ∈ H₃.V, ∀ y ∈ H₃.V, O x = O y → x ≠ y → ∃ W : GraphWalk H₃.toGraph x y,
      W.IsSimple)
    {ρ : S → S_r} (hρ : ∀ v ∈ Hd.G.V, ρ v ∈ Mid.V ∩ bd S_r ∧ O (w (ρ v)) = v)
      (hρb : ∀ v ∈ Hd.G.V ∩ bd S, θ (ρ v) = v)
    {ε : Set S → Set S} (hε : ∀ f ∈ Hd.G.E, ε f ∈ 𝓔) (hεi : ∀ f ∈ Hd.G.E, ∀ f' ∈ Hd.G.E, f ≠ f'
      → ε f ≠ ε f')
    {zp zm : Set S → S_r} (hzp : ∀ f ∈ Hd.G.E, zp f ∈ Mid.V ∩ bd S_r ∧ θ (zp f) = Gd.plus (ε f) ∧ O
      (w (zp f)) = Hd.plus f)
    (hzm : ∀ f ∈ Hd.G.E, zm f ∈ Mid.V ∩ bd S_r ∧ θ (zm f) = Gd.minus (ε f) ∧ O (w (zm f))
      = Hd.minus f) [Nonempty S_r] :
    IsBoundaryRootedMinor Hd Gd := by
  classical
  obtain ⟨ψ, hl, hr, hc⟩ := M.exists_inverse
  obtain ⟨-, -, -, -, hbdeq, hpaths⟩ := hhom
  have hH''V : ∀ s ∈ Mid.V ∩ bd S_r, s ∈ H''.V := fun s hs => (hbdeq ▸ hs : s ∈ H''.V ∩ bd S_r).1
  have hMid : Mid.V ⊆ Mid.V \ ∅ := fun x hx => ⟨hx, not_false⟩
  have hH₃ : ∀ s ∈ Mid.V, w s ∈ H₃.V := fun s hs => (M.carry.mem s (hMid hs)).2
  have key : ∀ s ∈ Mid.V ∩ bd S_r, ∀ t ∈ Mid.V ∩ bd S_r, (Nonempty (GraphWalk H''.toGraph s t) ↔ O
    (w s) = O (w t)) := by
    intro s hs t ht
    by_cases hst : s = t
    · subst hst
      exact ⟨fun _ => rfl, fun _ => ⟨.nil (hH''V s hs)⟩⟩
    obtain ⟨hiff, -⟩ := hpaths s hs t ht hst
    constructor
    · rintro ⟨W⟩
      obtain ⟨R, hR⟩ := GraphWalk.exists_simple W
      obtain ⟨P, -⟩ := hiff.mpr ⟨R, hR⟩
      obtain ⟨Q, -⟩ := M.carry.walk P (hMid hs.1) _ _ rfl rfl
      exact hwalkO Q
    · intro hO
      have hne : w s ≠ w t := fun he => hst (M.inj (Mid.V_subset_U hs.1) (Mid.V_subset_U ht.1) he)
      obtain ⟨W, hW⟩ := hsimple _ (hH₃ s hs.1) _ (hH₃ t ht.1) hO hne
      obtain ⟨P, h1, -, h3, -⟩ := hc.walk W (M.carry.mem s (hMid hs.1)).2 s t (hl s
        (Mid.V_subset_U hs.1)) (hl t (Mid.V_subset_U ht.1))
      have hP : P.IsSimple := by
        rw [GraphWalk.IsSimple, h1]
        exact hW.map_on fun z hz z' hz' he =>
          hc.inj (H₃.V_subset_U (hc.mem _ (h3 z hz)).1) (H₃.V_subset_U (hc.mem _ (h3 z' hz')).1) he
      obtain ⟨R, -⟩ := hiff.mp ⟨P, hP⟩
      exact ⟨R⟩
  have hne : Nonempty (Drawing S_r) := ⟨G_r⟩
  have hcomp : ∀ v, v ∈ Hd.G.V → ∃ D : Drawing S_r, D.IsSubdrawing H'' ∧ D.IsConnected
    ∧ ∀ x, x ∈ D.V ↔ Nonempty (GraphWalk H''.toGraph (ρ v) x) := fun v hv =>
    exists_component H'' (hH''V _ (hρ v hv).1)
  choose! D hD1 hD2 hD3 using hcomp
  have hVinj : ∀ a ∈ G_r.V, ∀ b ∈ G_r.V, θ a = θ b → a = b := fun a ha b _ he => by
    refine (hmc.inj a b he).resolve_right ?_
    rintro ⟨e, he', hae⟩
    rw [hmc.preV] at ha
    exact (hmc.sub he').2.1 hae |>.2 ha
  have hUinj : InjOn θ G_r.U := fun a ha b _ he => by
    refine (hmc.inj a b he).resolve_right ?_
    rw [hmc.preU] at ha
    exact ha.2
  have hsubG : ∀ v ∈ Hd.G.V, (D v).IsSubdrawing G_r := fun v hv => ⟨(hD1 v hv).1.trans hsub.1,
    (hD1 v hv).2.trans hsub.2⟩
  have hm : ∀ v ∈ Hd.G.V, IsMatched (D v) (cutImage Gd.G θ (D v)) θ ∅ := fun v hv =>
    matched_cutImage_of hmc.quot.continuous hUinj hmc.preV (fun f₁ hf₁ => (hmc.edges f₁ hf₁).1)
      (hsubG v hv)
  have hrep : ∀ v (hv : v ∈ Hd.G.V), ρ v ∈ (D v).V := fun v hv => (hD3 v hv _).mpr ⟨.nil (hH''V _
    (hρ v hv).1)⟩
  have hmemD : ∀ v (hv : v ∈ Hd.G.V) z, z ∈ Mid.V ∩ bd S_r → O (w z) = v → z ∈ (D v).V
    := fun v hv z hz hO =>
    (hD3 v hv z).mpr ((key _ (hρ v hv).1 z hz).mpr (by rw [(hρ v hv).2, hO]))
  refine ⟨hVbd, fun v => cutImage Gd.G θ (D v), ε, fun v hv => ⟨Gd.G.span_isSubdrawing _ _, ?_,
    ?_⟩, fun f hf => hmc.sub (hε f hf), ?_, hεi, ?_, ?_, ?_⟩
  · rw [← (hm v hv).image_V, sdiff_empty]
    exact ⟨θ (ρ v), ρ v, hrep v hv, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [← (hm v hv).image_V, sdiff_empty]
      exact ⟨θ (ρ v), ρ v, hrep v hv, rfl⟩
    · intro a ha b hb
      rw [← (hm v hv).image_V, sdiff_empty] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      obtain ⟨W⟩ := (hD2 v hv).2 a' ha' b' hb'
      obtain ⟨W', -⟩ := (hm v hv).carry.walk W ⟨ha', not_false⟩ _ _ rfl rfl
      exact ⟨W'⟩
  · intro v hv v' hv' hne'
    rw [disjoint_left]
    intro x hx hx'
    rw [← (hm v hv).image_V, sdiff_empty] at hx
    rw [← (hm v' hv').image_V, sdiff_empty] at hx'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, he⟩ := hx'
    have hab : b = a := hVinj b (hsubG v' hv' |>.1 hb) a (hsubG v hv |>.1 ha) he
    subst hab
    obtain ⟨W₁⟩ := (hD3 v hv _).mp ha
    obtain ⟨W₂⟩ := (hD3 v' hv' _).mp hb
    have h1 := (key _ (hρ v hv).1 _ (hρ v' hv').1).mp ⟨W₁.append W₂.reverse⟩
    rw [(hρ v hv).2, (hρ v' hv').2] at h1
    exact hne' h1
  · intro v hv f hf hmem
    have hmem' : ε f ∈ image θ '' (D v).E := by
      have := (hm v hv).image_E
      rw [← this]
      exact hmem
    obtain ⟨g, hg, hge⟩ := hmem'
    have hgr := (hsubG v hv).2 hg
    obtain ⟨-, h2, -⟩ := hmc.edges g hgr
    have hef := hε f hf
    obtain ⟨x, hx⟩ := (hmc.sub hef).2.2.1.nonempty
    exact disjoint_left.mp h2 (hge.symm ▸ hx) ⟨_, hef, hx⟩
  · intro f hf
    have hp := Hd.plus_mem f hf
    have hmi := Hd.minus_mem f hf
    constructor
    · rw [← (hm _ hp).image_V, sdiff_empty, ← (hzp f hf).2.1]
      exact ⟨_, hmemD _ hp _ (hzp f hf).1 (hzp f hf).2.2, rfl⟩
    · rw [← (hm _ hmi).image_V, sdiff_empty, ← (hzm f hf).2.1]
      exact ⟨_, hmemD _ hmi _ (hzm f hf).1 (hzm f hf).2.2, rfl⟩
  · intro v hv
    rw [← (hm v hv.1).image_V, sdiff_empty]
    exact ⟨ρ v, hrep v hv.1, hρb v hv⟩

end GraphMinor.GM07
