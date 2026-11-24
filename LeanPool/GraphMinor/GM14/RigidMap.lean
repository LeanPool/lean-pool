/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Whitney
public import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Moving a drawing to another surface

Let `f` and `f'` be inverse homeomorphisms between a compact set `A` and a set `B` in another space.
A
drawing in `A` then has an image in `B`: `mapD`. The image has the same graph (`mapIso`), and paths
go
to paths. If `A` and `B` are closed discs whose boundaries correspond, then frontiers of closed
subsets
correspond too (`subBd_image`), and rigidity carries over (`isRigidIn_mapD`).
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
variable {A : Set X} {B : Set Y} {f : X → Y} {f' : Y → X}

omit [T2Space X] [T2Space Y] in
theorem PH.injOn (h : PH A B f f') : InjOn f A := h.2.2.1.injOn

omit [T2Space X] [T2Space Y] in
theorem PH.left (h : PH A B f f') {x : X} (hx : x ∈ A) : f' (f x) = x := h.2.2.1 hx

omit [T2Space X] [T2Space Y] in
theorem PH.right (h : PH A B f f') {y : Y} (hy : y ∈ B) : f (f' y) = y := h.2.2.2.1 hy

omit [T2Space X] [T2Space Y] in
theorem PH.back (h : PH A B f f') {Z : Set X} (hZ : Z ⊆ A) : f' '' (f '' Z) = Z := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rwa [h.left (hZ hz)]
  · intro hx
    exact ⟨f x, mem_image_of_mem f hx, h.left (hZ hx)⟩

omit [T2Space X] [T2Space Y] in
theorem PH.mem_image_iff (h : PH A B f f') {Z : Set X} (hZ : Z ⊆ A) {x : X} (hx : x ∈ A) :
    f x ∈ f '' Z ↔ x ∈ Z := by
  constructor
  · rintro ⟨z, hz, he⟩
    rwa [← h.injOn (hZ hz) hx he]
  · exact fun hz => mem_image_of_mem f hz

omit [T2Space X] [T2Space Y] in
theorem PH.image_sub (h : PH A B f f') {Z : Set X} (hZ : Z ⊆ A) : f '' Z ⊆ B :=
  fun _ ⟨_, hz, he⟩ => he ▸ h.1 (hZ hz)

omit [T2Space X] in
omit [T2Space Y] in
theorem PH.image_isCompact (h : PH A B f f') {Z : Set X} (hZ : Z ⊆ A) (hc : IsCompact Z) :
    IsCompact (f '' Z) := hc.image_of_continuousOn (h.2.2.2.2.1.mono hZ)

omit [T2Space X] in
theorem PH.image_isClosed (h : PH A B f f') (hA : IsCompact A) {Z : Set X} (hZ : Z ⊆ A)
    (hc : IsClosed Z) : IsClosed (f '' Z) :=
  (h.image_isCompact hZ (hA.of_isClosed_subset hc hZ)).isClosed

/-- Inverse homeomorphisms carry closures to closures. -/
theorem PH.image_closure (h : PH A B f f') (hA : IsCompact A) {Z : Set X} (hZ : Z ⊆ A) :
    f '' closure Z = closure (f '' Z) := by
  have hcl : closure Z ⊆ A := closure_minimal hZ hA.isClosed
  refine subset_antisymm ((h.2.2.2.2.1.mono hcl).image_closure) ?_
  exact closure_minimal (image_mono subset_closure) (h.image_isClosed hA hcl isClosed_closure)

omit [T2Space X] [T2Space Y] in
theorem PH.restrict' (h : PH A B f f') {Z : Set X} (hZ : Z ⊆ A) : PH Z (f '' Z) f f' :=
  PH.restrict h hZ (h.image_sub hZ) (fun _ hz => mem_image_of_mem f hz) (fun _ hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [h.left (hZ hz)])

omit [T2Space X] [T2Space Y] in
/-- Inverse homeomorphisms carry arc components to arc components. -/
theorem arcComponentsIn_PH (h : PH A B f f') {F : Set X} (hF : F ⊆ A) :
    arcComponentsIn (f '' F) = image f '' arcComponentsIn F := by
  have hpath : ∀ {Z : Set X}, Z ⊆ A → IsPathConnected Z → IsPathConnected (f '' Z) :=
    fun hZ hp => hp.image' (h.2.2.2.2.1.mono hZ)
  have hpath' : ∀ {Z : Set Y}, Z ⊆ B → IsPathConnected Z → IsPathConnected (f' '' Z) :=
    fun hZ hp => hp.image' (h.2.2.2.2.2.mono hZ)
  ext C'
  constructor
  · rintro ⟨hne', hsub', hpc', hmax'⟩
    have hC'B : C' ⊆ B := hsub'.trans (h.image_sub hF)
    have hback : f '' (f' '' C') = C' := h.symm.back hC'B
    have hsub : f' '' C' ⊆ F := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hsub' hy
      rwa [h.left (hF hz)]
    refine ⟨f' '' C', ⟨hne'.image f', hsub, hpath' hC'B hpc', ?_⟩, hback⟩
    intro D hDF hDpc hsubD
    have hD' : f '' D = C' := by
      refine hmax' (f '' D) (image_mono hDF) (hpath (hDF.trans hF) hDpc) ?_
      rw [← hback]
      exact image_mono hsubD
    rw [← hD', h.back (hDF.trans hF)]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image f, image_mono hsub, hpath (hsub.trans hF) hpc, ?_⟩
    intro D' hD'F hD'pc hsubD'
    have hD'B : D' ⊆ B := hD'F.trans (h.image_sub hF)
    have hD : f' '' D' = C := by
      refine hmax (f' '' D') ?_ (hpath' hD'B hD'pc) ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hD'F hy
        rwa [h.left (hF hz)]
      · have := image_mono (f := f') hsubD'
        rwa [h.back (hsub.trans hF)] at this
    rw [← hD, h.symm.back hD'B]

omit [T2Space X] in
/-- The image of a line is a line. -/
theorem PH.line_image (h : PH A B f f') {L : Set X} {u v : X} (hL : L ⊆ A)
    (hl : IsLineWithEnds L u v) : IsLineWithEnds (f '' L) (f u) (f v) := by
  obtain ⟨g, h0, h1⟩ := hl
  let e : unitInterval → Y := fun t => f (g t).1
  have hec : Continuous e :=
    (h.2.2.2.2.1.mono hL).comp_continuous (continuous_subtype_val.comp g.continuous) fun t =>
      (g t).2
  have hei : Function.Injective e := fun x y he =>
    g.injective (Subtype.ext (h.injOn (hL (g x).2) (hL (g y).2) he))
  have hr : range e = f '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (g t).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g.symm ⟨z, hz⟩, by simp [e]⟩
  have hem := hec.isClosedEmbedding hei
  refine ⟨hem.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change e 0 = f u
    simp [e, h0]
  · change e 1 = f v
    simp [e, h1]

omit [T2Space X] in
/-- The image of an `O`-arc is an `O`-arc. -/
theorem PH.oArc_image (h : PH A B f f') {L : Set X} (hL : L ⊆ A) (hl : IsOArc L) :
    IsOArc (f '' L) := by
  obtain ⟨g⟩ := hl
  let e : Circle → Y := fun t => f (g t).1
  have hec : Continuous e :=
    (h.2.2.2.2.1.mono hL).comp_continuous (continuous_subtype_val.comp g.continuous) fun t =>
      (g t).2
  have hei : Function.Injective e := fun x y he =>
    g.injective (Subtype.ext (h.injOn (hL (g x).2) (hL (g y).2) he))
  have hr : range e = f '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (g t).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g.symm ⟨z, hz⟩, by simp [e]⟩
  have hem := hec.isClosedEmbedding hei
  exact ⟨hem.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

omit [T2Space X] [T2Space Y] in
/-- The image of a closed disc is a closed disc. -/
theorem PH.disc_image (h : PH A B f f') {D : Set X} (hD : D ⊆ A) (hd : IsClosedDisc D) :
    IsClosedDisc (f '' D) := by
  obtain ⟨g⟩ := hd
  have hr := h.restrict' hD
  let e : D ≃ₜ (f '' D) :=
    { toFun := fun z => ⟨f z.1, mem_image_of_mem f z.2⟩
      invFun := fun y => ⟨f' y.1, by
        obtain ⟨_, ⟨z, hz, rfl⟩⟩ := y
        simpa [h.left (hD hz)] using hz⟩
      left_inv := fun z => Subtype.ext (h.left (hD z.2))
      right_inv := fun y => Subtype.ext (h.right (h.image_sub hD y.2))
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (h.2.2.2.2.1.mono hD).comp_continuous continuous_subtype_val fun z => z.2
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (h.2.2.2.2.2.mono (h.image_sub hD)).comp_continuous continuous_subtype_val
          fun z => z.2 }
  exact ⟨g.trans e⟩

section Map

variable (hP : PH A B f f') (hA : IsCompact A) (H : Drawing X) (hU : H.U ⊆ A)

include hP hU in
omit [TopologicalSpace Y] [T2Space X] [T2Space Y] hP in
theorem cap_image {e : Set X} (he : e ∈ H.E) : e ⊆ A :=
  ((subset_closure.trans (H.closure_subset_U he)).trans hU)

/-- The image of a drawing. -/
noncomputable def mapD : Drawing Y where
  U := f '' H.U
  V := f '' H.V
  V_subset_U := image_mono H.V_subset_U
  isClosed_U := hP.image_isClosed hA hU H.isClosed_U
  finite_V := H.finite_V.image f
  finite_edges := by
    have hdiff : f '' H.U \ f '' H.V = f '' (H.U \ H.V) :=
      (hP.injOn.mono hU).image_sdiff_subset H.V_subset_U |>.symm
    rw [hdiff, arcComponentsIn_PH hP (sdiff_subset.trans hU)]
    exact H.finite_edges.image (image f)
  edge_cond := by
    have hdiff : f '' H.U \ f '' H.V = f '' (H.U \ H.V) :=
      (hP.injOn.mono hU).image_sdiff_subset H.V_subset_U |>.symm
    intro e' he'
    rw [hdiff, arcComponentsIn_PH hP (sdiff_subset.trans hU)] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have heA : e ⊆ A := cap_image H hU he
    have hclA : closure e ⊆ A := closure_minimal heA hA.isClosed
    have hcap : closure (f '' e) ∩ f '' H.V = f '' (closure e ∩ H.V) := by
      rw [← hP.image_closure hA heA]
      exact ((hP.injOn.mono (union_subset hclA (H.V_subset_U.trans hU))).image_inter
        subset_union_left subset_union_right).symm
    rcases H.edge_cond e he with ⟨u, v, huv, hcap_e, hL⟩ | ⟨u, hcap_e, hO⟩
    · left
      have hu : u ∈ closure e ∩ H.V := hcap_e ▸ Or.inl rfl
      have hv : v ∈ closure e ∩ H.V := hcap_e ▸ Or.inr rfl
      refine ⟨f u, f v, fun h => huv (hP.injOn (hclA hu.1) (hclA hv.1) h), ?_, ?_⟩
      · rw [hcap, hcap_e, image_pair]
      · rw [← hP.image_closure hA heA]
        exact hP.line_image hclA hL
    · right
      refine ⟨f u, ?_, ?_⟩
      · rw [hcap, hcap_e, image_singleton]
      · rw [← hP.image_closure hA heA]
        exact hP.oArc_image hclA hO

theorem mapD_U : (mapD hP hA H hU).U = f '' H.U := rfl

theorem mapD_V : (mapD hP hA H hU).V = f '' H.V := rfl

theorem mapD_E : (mapD hP hA H hU).E = image f '' H.E := by
  have hdiff : f '' H.U \ f '' H.V = f '' (H.U \ H.V) :=
    (hP.injOn.mono hU).image_sdiff_subset H.V_subset_U |>.symm
  change arcComponentsIn (f '' H.U \ f '' H.V) = _
  rw [hdiff, arcComponentsIn_PH hP (sdiff_subset.trans hU)]
  rfl

include hP hA in
theorem cap_image_eq {e Z : Set X} (he : e ⊆ A) (hZ : Z ⊆ A) :
    closure (f '' e) ∩ f '' Z = f '' (closure e ∩ Z) := by
  have hclA : closure e ⊆ A := closure_minimal he hA.isClosed
  rw [← hP.image_closure hA he]
  exact ((hP.injOn.mono (union_subset hclA hZ)).image_inter
    subset_union_left subset_union_right).symm

include hP in
omit [T2Space X] [T2Space Y] in
theorem image_injOn_E {E : Set (Set X)} (hE : ∀ e ∈ E, e ⊆ A) : InjOn (image f) E := by
  intro e he e' he' h
  have : image f e = image f e' := h
  rw [← hP.back (hE e he), ← hP.back (hE e' he')]
  exact congrArg _ this

/-- The drawing and its image are isomorphic. -/
noncomputable def mapIso : Iso H.toGraph (mapD hP hA H hU).toGraph where
  vertexEquiv :=
    { toFun := fun v => ⟨f v.1, mem_image_of_mem f v.2⟩
      invFun := fun w => ⟨f' w.1, by
        obtain ⟨_, ⟨z, hz, rfl⟩⟩ := w
        have hzH : z ∈ H.V := hz
        change f' (f z) ∈ H.V
        rwa [hP.left (hU (H.V_subset_U hzH))]⟩
      left_inv := fun v => Subtype.ext (hP.left (hU (H.V_subset_U v.2)))
      right_inv := fun w => Subtype.ext (by
        obtain ⟨_, ⟨z, hz, rfl⟩⟩ := w
        have hzH : z ∈ H.V := hz
        change f (f' (f z)) = f z
        rw [hP.left (hU (H.V_subset_U hzH))]) }
  edgeEquiv :=
    have hm : ∀ {e}, e ∈ H.E → f '' e ∈ (mapD hP hA H hU).E := fun he => by
      rw [mapD_E]
      exact mem_image_of_mem _ he
    have hm' : ∀ {e'}, e' ∈ (mapD hP hA H hU).E → ∃ e ∈ H.E, f '' e = e' := fun he' => by
      rw [mapD_E] at he'
      exact he'
    { toFun := fun e => ⟨f '' e.1, hm e.2⟩
      invFun := fun w => ⟨f' '' w.1, by
        obtain ⟨e, he, heq⟩ := hm' w.2
        rw [← heq, hP.back (cap_image H hU he)]
        exact he⟩
      left_inv := fun e => Subtype.ext (hP.back (cap_image H hU e.2))
      right_inv := fun w => Subtype.ext (by
        obtain ⟨e, he, heq⟩ := hm' w.2
        change f '' (f' '' w.1) = w.1
        rw [← heq, hP.back (cap_image H hU he)]) }
  isLink_iff := by
    rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
    have heA : e ⊆ A := cap_image H hU he
    have hVA : H.V ⊆ A := H.V_subset_U.trans hU
    have hclA : closure e ⊆ A := closure_minimal heA hA.isClosed
    have hcap := cap_image_eq hP hA heA hVA
    have hE' : f '' e ∈ (mapD hP hA H hU).E := by
      rw [mapD_E]
      exact mem_image_of_mem _ he
    constructor
    · rintro ⟨-, -, -, hc⟩
      refine ⟨hE', mem_image_of_mem f hx, mem_image_of_mem f hy, ?_⟩
      change closure (f '' e) ∩ f '' H.V = {f x, f y}
      rw [hcap, hc, image_pair]
    · rintro ⟨-, -, -, hc⟩
      refine ⟨he, hx, hy, ?_⟩
      have hc' : closure (f '' e) ∩ f '' H.V = {f x, f y} := hc
      rw [hcap, ← image_pair] at hc'
      refine (hP.injOn.image_eq_image_iff (inter_subset_left.trans hclA) ?_).mp hc'
      rintro z (rfl | rfl)
      · exact hVA hx
      · exact hVA hy

theorem mapIso_vertex (v : V(H.toGraph)) :
    ((mapIso hP hA H hU).vertexEquiv v).1 = f v.1 := rfl

theorem mapIso_edge (e : E(H.toGraph)) :
    ((mapIso hP hA H hU).edgeEquiv e).1 = f '' e.1 := rfl

end Map

omit [T2Space X] [T2Space Y] in
/-- Maps that keep links, and are injective on vertices, carry paths to paths. -/
theorem isPathBetween_map {P : Drawing X} {Q : Drawing Y} (g : X → Y) (ge : Set X → Set Y)
    (hl : ∀ e u v, P.toGraph.IsLink e u v → Q.toGraph.IsLink (ge e) (g u) (g v))
    (hV : Q.V = g '' P.V) (hE : Q.E = ge '' P.E) (hi : InjOn g P.V) {a b : X}
    (h : P.IsPathBetween a b) : Q.IsPathBetween (g a) (g b) := by
  obtain ⟨W, hs, hPV, hPE⟩ := h
  have key : ∀ {c d : X} (W : GraphWalk P.toGraph c d), ∃ W' : GraphWalk Q.toGraph (g c) (g d),
      W'.support = W.support.map g ∧ W'.edges = W.edges.map ge := by
    intro c d W
    induction W with
    | nil hv =>
      have hv' : g _ ∈ Q.V := hV ▸ mem_image_of_mem g hv
      exact ⟨GraphWalk.nil hv', rfl, rfl⟩
    | cons hlink rest ih =>
      obtain ⟨W', h₁, h₂⟩ := ih
      refine ⟨GraphWalk.cons (hl _ _ _ hlink) W', ?_, ?_⟩
      · simp [GraphWalk.support, h₁]
      · simp [GraphWalk.edges, h₂]
  obtain ⟨W', h₁, h₂⟩ := key W
  refine ⟨W', ?_, ?_, ?_⟩
  · change W'.support.Nodup
    rw [h₁]
    refine List.Nodup.map_on (fun x hx y hy he => hi ?_ ?_ he) hs
    · rw [hPV]
      exact hx
    · rw [hPV]
      exact hy
  · rw [hV, hPV]
    ext y
    simp [h₁]
  · rw [hE, hPE]
    ext y
    simp [h₂]

section Rigid

variable (hP : PH A B f f') (hA : IsCompact A) (H : Drawing X) (hU : H.U ⊆ A)

theorem interSet_E {T : Set X} : (H.interSet T).E = {e | e ∈ H.E ∧ e ⊆ T} := by
  change (H.span _ _).E = _
  rw [Drawing.span_E]
  ext e
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem mapD_interSet_E {T : Set X} (hT : T ⊆ A) :
    ((mapD hP hA H hU).interSet (f '' T)).E = image f '' (H.interSet T).E := by
  rw [interSet_E, interSet_E, mapD_E]
  ext e'
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hsub⟩
    refine ⟨e, ⟨he, ?_⟩, rfl⟩
    have := image_mono (f := f') hsub
    rwa [hP.back hT, hP.back (cap_image H hU he)] at this
  · rintro ⟨e, ⟨he, hsub⟩, rfl⟩
    exact ⟨mem_image_of_mem _ he, image_mono hsub⟩

theorem mapD_interSet_V {T : Set X} (hT : T ⊆ A) :
    ((mapD hP hA H hU).interSet (f '' T)).V = f '' (H.interSet T).V := by
  have hVA : H.V ⊆ A := H.V_subset_U.trans hU
  have hset : ∀ {e : Set X}, e ∈ H.E → closure (f '' e) ∩ f '' H.V = f '' (closure e ∩ H.V) :=
    fun he => cap_image_eq hP hA (cap_image H hU he) hVA
  ext y
  constructor
  · rintro (⟨hy, -⟩ | hy)
    · obtain ⟨⟨x, hx, rfl⟩, hxT⟩ := hy
      exact ⟨x, Or.inl ⟨⟨hx, (hP.mem_image_iff hT (hVA hx)).mp hxT⟩, hx⟩, rfl⟩
    · obtain ⟨e', he', hy'⟩ := mem_iUnion₂.mp hy
      have he₁ : e' ∈ ((mapD hP hA H hU).interSet (f '' T)).E := by
        rw [interSet_E]
        exact he'.1
      rw [mapD_interSet_E hP hA H hU hT] at he₁
      obtain ⟨e, he, rfl⟩ := he₁
      rw [interSet_E] at he
      have hy'' : y ∈ closure (f '' e) ∩ f '' H.V := hy'
      rw [hset he.1] at hy''
      obtain ⟨x, hx, rfl⟩ := hy''
      exact ⟨x, Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, he.1⟩, hx⟩), rfl⟩
  · rintro ⟨x, (⟨⟨hx, hxT⟩, -⟩ | hx), rfl⟩
    · exact Or.inl ⟨⟨mem_image_of_mem f hx, mem_image_of_mem f hxT⟩, mem_image_of_mem f hx⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      refine Or.inr (mem_iUnion₂.mpr ⟨f '' e, ?_, ?_⟩)
      · have heE : e ∈ H.E := he.1.1
        refine ⟨⟨?_, image_mono he.1.2⟩, ?_⟩
        · rw [mapD_E]
          exact mem_image_of_mem _ heE
        · rw [mapD_E]
          exact mem_image_of_mem _ heE
      · change f x ∈ closure (f '' e) ∩ f '' H.V
        rw [hset he.2]
        exact mem_image_of_mem f hxe

/-- Paths in `H ∩ T` go to paths in the image of `H` in `f(T)`. -/
theorem path_image {T : Set X} (hT : T ⊆ A) {a b : X} (h : (H.interSet T).IsPathBetween a b) :
    ((mapD hP hA H hU).interSet (f '' T)).IsPathBetween (f a) (f b) := by
  have hVA : (H.interSet T).V ⊆ A := by
    refine Subset.trans ?_ (H.V_subset_U.trans hU)
    exact (Drawing.span_isSubdrawing _ _ _).1
  refine isPathBetween_map f (image f) ?_ (mapD_interSet_V hP hA H hU hT)
    (mapD_interSet_E hP hA H hU hT) (hP.injOn.mono hVA) h
  rintro e u v ⟨he, hu, hv, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mem_image_of_mem (image f) he
    rw [← mapD_interSet_E hP hA H hU hT] at this
    exact this
  · have := mem_image_of_mem f hu
    rw [← mapD_interSet_V hP hA H hU hT] at this
    exact this
  · have := mem_image_of_mem f hv
    rw [← mapD_interSet_V hP hA H hU hT] at this
    exact this
  · have heE : e ∈ H.E := by
      have := he
      rw [interSet_E] at this
      exact this.1
    change closure (f '' e) ∩ ((mapD hP hA H hU).interSet (f '' T)).V = _
    rw [mapD_interSet_V hP hA H hU hT, cap_image_eq hP hA (cap_image H hU heE) hVA, hc,
      image_pair]

end Rigid

omit [T2Space X] [T2Space Y] in
theorem subBd_subset_of {Z : Set Y} (hZ : Z ⊆ B) (hc : IsClosed Z) : subBd Z ⊆ B := by
  rintro p ⟨hp, -⟩
  exact hZ (hc.closure_eq ▸ hp)

omit [T2Space X] [T2Space Y] in
/-- A point of a closed `Z` in `A` that is a limit of points off `Z` stays one under `f`, if the
frontier of `A` goes into the frontier of `B`. -/
theorem subBd_image (hP : PH A B f f')
    (hbd : f '' subBd A ⊆ subBd B) {Z : Set X} (hZ : Z ⊆ A) (hc : IsClosed Z) :
    f '' subBd Z ⊆ subBd (f '' Z) := by
  rintro _ ⟨p, ⟨hp, hp'⟩, rfl⟩
  have hpZ : p ∈ Z := hc.closure_eq ▸ hp
  refine ⟨subset_closure (mem_image_of_mem f hpZ), ?_⟩
  by_cases hpA : p ∈ closure (univ \ A)
  · have hq : f p ∈ subBd B := hbd ⟨p, ⟨subset_closure (hZ hpZ), hpA⟩, rfl⟩
    exact closure_mono (sdiff_subset_sdiff_right (hP.image_sub hZ)) hq.2
  · have hO : IsOpen (closure (univ \ A))ᶜ := isClosed_closure.isOpen_compl
    have hsub : (closure (univ \ A))ᶜ ⊆ A := by
      intro z hz
      by_contra hn
      exact hz (subset_closure ⟨mem_univ z, hn⟩)
    let W := (closure (univ \ A))ᶜ ∩ (univ \ Z)
    have hW : p ∈ closure W := by
      have := hO.inter_closure (t := univ \ Z)
      exact closure_mono (Subset.refl _) (this ⟨hpA, hp'⟩)
    have hWA : W ⊆ A := inter_subset_left.trans hsub
    have hcont : ContinuousWithinAt f W p :=
      (hP.2.2.2.2.1 p (hZ hpZ)).mono hWA
    refine closure_mono ?_ (hcont.mem_closure_image hW)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨mem_univ _, fun hzi => hz.2.2 ?_⟩
    exact (hP.mem_image_iff hZ (hWA hz)).mp hzi

/-- **Rigidity carries over.** -/
theorem isRigidIn_mapD (hP : PH A B f f') (hA : IsCompact A) (_hB : IsCompact B)
    (hbd : f '' subBd A ⊆ subBd B) (hbd' : f' '' subBd B ⊆ subBd A) (H : Drawing X) (hU : H.U ⊆ A)
    (hr : IsRigidIn H A) : IsRigidIn (mapD hP hA H hU) B := by
  intro F' hF'B hO hcap hc
  have hVA : H.V ⊆ A := H.V_subset_U.trans hU
  have hFA : f' '' F' ⊆ A := hP.symm.image_sub hF'B
  have hFF : f '' (f' '' F') = F' := hP.symm.back hF'B
  have hcapV : f '' (f' '' F' ∩ H.V) = F' ∩ f '' H.V := by
    conv_rhs => rw [← hFF]
    exact (hP.injOn.mono (union_subset hFA hVA)).image_inter subset_union_left subset_union_right
  obtain ⟨Δ, hΔA, hd, hbdΔ, hcase⟩ := hr (f' '' F') hFA (hP.symm.oArc_image hF'B hO)
    (by
      rintro z ⟨hz, hzU⟩
      have h₁ : f z ∈ F' := by
        rw [← hFF]
        exact mem_image_of_mem f hz
      have h₂ := hcap ⟨h₁, mem_image_of_mem f hzU⟩
      exact (hP.mem_image_iff hVA (hU hzU)).mp h₂)
    (by
      have hcfin : (F' ∩ f '' H.V).Finite := (H.finite_V.image f).subset inter_subset_right
      have hi : InjOn f (f' '' F' ∩ H.V) := hP.injOn.mono (inter_subset_left.trans hFA)
      rw [← hi.ncard_image, hcapV]
      exact hc)
  have hΔc : IsClosed Δ := hd.isClosed
  have hΔ' : f '' Δ ⊆ B := hP.image_sub hΔA
  have hsub₁ := subBd_image hP hbd hΔA hΔc
  have hsub₂ := subBd_image hP.symm hbd' hΔ' (hP.image_isClosed hA hΔA hΔc)
  rw [hP.back hΔA] at hsub₂
  have hbdeq : subBd (f '' Δ) = F' := by
    refine subset_antisymm ?_ ?_
    · have : f '' (f' '' subBd (f '' Δ)) ⊆ f '' (subBd Δ) := image_mono hsub₂
      rw [hP.symm.back (subBd_subset_of hΔ' (hP.image_isClosed hA hΔA hΔc)), hbdΔ, hFF] at this
      exact this
    · have := hsub₁
      rwa [hbdΔ, hFF] at this
  refine ⟨f '' Δ, hΔ', hP.disc_image hΔA hd, hbdeq, ?_⟩
  rcases hcase with hcase | ⟨u, v, huv, hcap₂, hpath⟩
  · refine Or.inl ?_
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, he⟩⟩
    have hxy : y = x := hP.injOn (hU hy) (hΔA hx) he
    subst hxy
    rw [← hFF]
    exact mem_image_of_mem f (hcase ⟨hx, hy⟩)
  · refine Or.inr ⟨f u, f v, ?_, ?_, path_image hP hA H hU hΔA hpath⟩
    · have hu : u ∈ f' '' F' ∩ H.V := hcap₂ ▸ Or.inl rfl
      have hv : v ∈ f' '' F' ∩ H.V := hcap₂ ▸ Or.inr rfl
      exact fun h => huv (hP.injOn (hVA hu.2) (hVA hv.2) h)
    · change F' ∩ f '' H.V = _
      rw [← hcapV, hcap₂, image_pair]

end GraphMinor.GM14.Whitney
