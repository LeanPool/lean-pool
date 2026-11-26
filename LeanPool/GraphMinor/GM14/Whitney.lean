/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.WhitneyPeripheral
public import LeanPool.GraphMinor.GM14.Cited
import LeanPool.GraphMinor.GM14.Section8Core
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.Surface.DomainHomeo
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Whitney's theorem on planar drawings

Two drawings in a sphere of a subdivision of a simple 3-connected graph are related by a
homeomorphism of the sphere that extends the given graph isomorphism.

The route is the classical one through peripheral circuits: the circuits that bound faces are
exactly the peripheral circuits, and that property depends only on the graph. So an isomorphism of
graphs carries faces to faces. We build the homeomorphism edge by edge, and then extend it over each
face, which is a closed disc.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph Metric GraphMinor.GM09 GraphMinor.GM11 GraphMinor.Surface

universe u

section PH

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- `f` and `f'` restrict to inverse homeomorphisms between `A` and `B`. -/
def PH (A : Set X) (B : Set Y) (f : X → Y) (f' : Y → X) : Prop :=
  MapsTo f A B ∧ MapsTo f' B A ∧ LeftInvOn f' f A ∧ RightInvOn f' f B ∧ ContinuousOn f A ∧
    ContinuousOn f' B

variable {A A₀ : Set X} {B B₀ : Set Y} {C : Set Z} {f : X → Y} {f' : Y → X}

theorem PH.symm (h : PH A B f f') : PH B A f' f :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

theorem PH.comp (h : PH A B f f') {k : Y → Z} {k' : Z → Y} (h' : PH B C k k') :
    PH A C (k ∘ f) (f' ∘ k') := by
  obtain ⟨m, n, l, r, c, d⟩ := h
  obtain ⟨m', n', l', r', c', d'⟩ := h'
  refine ⟨m'.comp m, n.comp n', ?_, ?_, c'.comp c m, d.comp d' n'⟩
  · intro x hx
    simp only [Function.comp]
    rw [l' (m hx), l hx]
  · intro z hz
    simp only [Function.comp]
    rw [r (n' hz), r' hz]

theorem PH.image_eq (h : PH A B f f') : f '' A = B := by
  refine Subset.antisymm (image_subset_iff.mpr h.1) fun y hy => ?_
  exact ⟨f' y, h.2.1 hy, h.2.2.2.1 hy⟩

theorem PH.restrict (h : PH A B f f') (hA : A₀ ⊆ A) (hB : B₀ ⊆ B) (hm : MapsTo f A₀ B₀)
    (hm' : MapsTo f' B₀ A₀) : PH A₀ B₀ f f' :=
  ⟨hm, hm', fun _ hx => h.2.2.1 (hA hx), fun _ hy => h.2.2.2.1 (hB hy),
    h.2.2.2.2.1.mono hA, h.2.2.2.2.2.mono hB⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Functions that agree on overlaps have a common extension. -/
theorem exists_common {ι : Type*} [Nonempty Y] {A : ι → Set X} {f : ι → X → Y}
    (hag : ∀ i j x, x ∈ A i → x ∈ A j → f i x = f j x) :
    ∃ F : X → Y, ∀ i, EqOn F (f i) (A i) := by
  classical
  refine ⟨fun x => if h : ∃ i, x ∈ A i then f h.choose x else Classical.arbitrary Y, ?_⟩
  intro i x hx
  have h : ∃ i, x ∈ A i := ⟨i, hx⟩
  simp only [dite_eq_left h]
  exact hag _ _ _ h.choose_spec hx

/-- Gluing finitely many partial homeomorphisms over closed sets. -/
theorem exists_glue {ι : Type*} [Finite ι] [Nonempty X] [Nonempty Y] {A : ι → Set X}
    {B : ι → Set Y} {f : ι → X → Y} {f' : ι → Y → X} (hA : ∀ i, IsClosed (A i))
    (hB : ∀ i, IsClosed (B i)) (hP : ∀ i, PH (A i) (B i) (f i) (f' i))
    (hag : ∀ i j x, x ∈ A i → x ∈ A j → f i x = f j x)
    (hag' : ∀ i j y, y ∈ B i → y ∈ B j → f' i y = f' j y) :
    ∃ F F', PH (⋃ i, A i) (⋃ i, B i) F F' ∧ (∀ i, EqOn F (f i) (A i)) ∧
      ∀ i, EqOn F' (f' i) (B i) := by
  obtain ⟨F, hF⟩ := exists_common hag
  obtain ⟨F', hF'⟩ := exists_common hag'
  refine ⟨F, F', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hF, hF'⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hF i hi]
    exact mem_iUnion.mpr ⟨i, (hP i).1 hi⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [hF' i hi]
    exact mem_iUnion.mpr ⟨i, (hP i).2.1 hi⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hF i hi, hF' i ((hP i).1 hi)]
    exact (hP i).2.2.1 hi
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [hF' i hi, hF i ((hP i).2.1 hi)]
    exact (hP i).2.2.2.1 hi
  · exact (locallyFinite_of_finite A).continuousOn_iUnion hA fun i =>
      (hP i).2.2.2.2.1.congr (hF i)
  · exact (locallyFinite_of_finite B).continuousOn_iUnion hB fun i =>
      (hP i).2.2.2.2.2.congr (hF' i)

/-- Two lines are homeomorphic, with ends going to ends. -/
theorem exists_line_PH [Nonempty X] [Nonempty Y] {L : Set X} {L' : Set Y} {a b : X} {a' b' : Y}
    (hL : IsLineWithEnds L a b) (hL' : IsLineWithEnds L' a' b') :
    ∃ f f', PH L L' f f' ∧ f a = a' ∧ f b = b' := by
  obtain ⟨p, hp0, hp1⟩ := hL
  obtain ⟨q, hq0, hq1⟩ := hL'
  let e : L ≃ₜ L' := p.symm.trans q
  obtain ⟨f, f', hf, hc, hc', him, hl⟩ := exists_extensions e
  have hPH : PH L L' f f' := by
    refine ⟨fun x hx => him ▸ mem_image_of_mem f hx, ?_, hl, ?_, hc, hc'⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := him.symm ▸ hy
      rw [hl hx]
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := him.symm ▸ hy
      rw [hl hx]
  refine ⟨f, f', hPH, ?_, ?_⟩
  · have h := hf (p 0)
    rw [hp0] at h
    rw [h]
    simp [e, hq0]
  · have h := hf (p 1)
    rw [hp1] at h
    rw [h]
    simp [e, hq1]

end PH

theorem closedInner_sphere_one :
    Nonempty (Circle ≃ₜ sphere (0 : ℂ) 1) ∧ closedInner (sphere (0 : ℂ) 1) = closedBall 0 1 := by
  have hd := isClosedDisc_of_convex (K := closedBall (0 : ℂ) 1) (convex_closedBall 0 1)
    (by rw [interior_closedBall _ (by norm_num)]; exact ⟨0, by simp⟩) isBounded_closedBall
    isClosed_closedBall
  rw [frontier_closedBall _ (by norm_num)] at hd
  have h1 : Nonempty (Circle ≃ₜ sphere (0 : ℂ) 1) := by
    have := hd.1.isOArc_discBd
    rwa [hd.2] at this
  exact ⟨h1, (eq_closedInner_of_discBd h1 hd.1 hd.2).symm⟩

/-- A homeomorphism between the boundaries of two closed discs extends over the discs. This is the
Schoenflies theorem for the unit circle. -/
theorem exists_disc_PH {S : Type u} {S' : Type*} [TopologicalSpace S] [TopologicalSpace S']
    {D : Set S} {D' : Set S'}
    (hD : IsClosedDisc D) (hD' : IsClosedDisc D') {g : S → S'} {g' : S' → S}
    (h : PH (discBd D) (discBd D') g g') :
    ∃ f f', PH D D' f f' ∧ EqOn f g (discBd D) ∧ EqOn f' g' (discBd D') := by
  obtain ⟨a, b, ha, hb, hm, hn, hl, hr, him⟩ := hD.exists_chart
  obtain ⟨a', b', ha', hb', hm', hn', hl', hr', him'⟩ := hD'.exists_chart
  have hch : PH D (closedBall 0 1) a b := ⟨hm, hn, hl, hr, ha, hb⟩
  have hch' : PH D' (closedBall 0 1) a' b' := ⟨hm', hn', hl', hr', ha', hb'⟩
  have hsub : discBd D ⊆ D := Surface.discBd_subset _
  have hsub' : discBd D' ⊆ D' := Surface.discBd_subset _
  have hs : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hbd : PH (discBd D) (sphere 0 1) a b := hch.restrict hsub hs
    (fun p hp => him ▸ mem_image_of_mem a hp) (fun z hz => by
      obtain ⟨p, hp, rfl⟩ := him.symm ▸ hz
      rw [hl (hsub hp)]
      exact hp)
  have hbd' : PH (discBd D') (sphere 0 1) a' b' := hch'.restrict hsub' hs
    (fun p hp => him' ▸ mem_image_of_mem a' hp) (fun z hz => by
      obtain ⟨p, hp, rfl⟩ := him'.symm ▸ hz
      rw [hl' (hsub' hp)]
      exact hp)
  have hcirc := (hbd.symm.comp h).comp hbd'
  obtain ⟨hF, hcl⟩ := closedInner_sphere_one
  obtain ⟨Ψ, hΨ⟩ := exists_homeomorph_closedInner hF hF hcirc
  obtain ⟨ψ, χ, hmatch, hv⟩ := exists_bdMatch Ψ
  have hPH : PH (closedBall (0 : ℂ) 1) (closedBall 0 1) ψ χ := by
    rw [← hcl]
    exact hmatch
  have hF1 : sphere (0 : ℂ) 1 ⊆ closedInner (sphere 0 1) := subset_union_right
  have hψ : EqOn ψ (a' ∘ g ∘ b) (sphere 0 1) := by
    intro z hz
    rw [hv ⟨z, hF1 hz⟩]
    exact hΨ ⟨z, hF1 hz⟩ hz
  have hχ : EqOn χ ((a ∘ g') ∘ b') (sphere 0 1) := by
    intro z hz
    have hw : ((a ∘ g') ∘ b') z ∈ sphere (0 : ℂ) 1 := hcirc.2.1 hz
    have hz' : ψ (((a ∘ g') ∘ b') z) = z := (hψ hw).trans (hcirc.2.2.2.1 hz)
    have := hPH.2.2.1 (hs hw)
    rwa [hz'] at this
  refine ⟨_, _, (hch.comp hPH).comp hch'.symm, ?_, ?_⟩
  · intro p hp
    have h₁ : ψ (a p) = a' (g (b (a p))) := hψ (hbd.1 hp)
    simp only [Function.comp]
    rw [h₁, hl (hsub hp), hl' (hsub' (h.1 hp))]
  · intro y hy
    have h₁ : χ (a' y) = a (g' (b' (a' y))) := hχ (hbd'.1 hy)
    simp only [Function.comp]
    rw [h₁, hl' (hsub' hy), hl (hsub (h.2.1 hy))]

section Assembly

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Total functions that carry an isomorphism between the graphs of two drawings. -/
structure IsoD (J₁ J₂ : Drawing S) (fv gv : S → S) (fe ge : Set S → Set S) : Prop where
  v₁ : ∀ x ∈ J₁.V, fv x ∈ J₂.V
  v₂ : ∀ y ∈ J₂.V, gv y ∈ J₁.V
  vl : ∀ x ∈ J₁.V, gv (fv x) = x
  vr : ∀ y ∈ J₂.V, fv (gv y) = y
  e₁ : ∀ e ∈ J₁.E, fe e ∈ J₂.E
  e₂ : ∀ e ∈ J₂.E, ge e ∈ J₁.E
  el : ∀ e ∈ J₁.E, ge (fe e) = e
  er : ∀ e ∈ J₂.E, fe (ge e) = e
  link₁ : ∀ e x y, J₁.toGraph.IsLink e x y → J₂.toGraph.IsLink (fe e) (fv x) (fv y)
  link₂ : ∀ e x y, J₂.toGraph.IsLink e x y → J₁.toGraph.IsLink (ge e) (gv x) (gv y)

variable {J J₁ J₂ : Drawing S} {fv gv : S → S} {fe ge : Set S → Set S}

omit [T2Space S] in
theorem IsoD.symm (h : IsoD J₁ J₂ fv gv fe ge) : IsoD J₂ J₁ gv fv ge fe :=
  ⟨h.v₂, h.v₁, h.vr, h.vl, h.e₂, h.e₁, h.er, h.el, h.link₂, h.link₁⟩

omit [T2Space S] in
/-- The closure of an edge with distinct ends is a line. -/
theorem closure_line {e : Set S} {x y : S} (hl : J.toGraph.IsLink e x y) (hxy : x ≠ y) :
    IsLineWithEnds (closure e) x y := by
  obtain ⟨he, -, -, hcap⟩ := hl
  rcases J.edge_cond e he with ⟨u, v, -, hc, hL⟩ | ⟨u, hc, -⟩
  · rw [hc] at hcap
    rcases Set.pair_eq_pair_iff.mp hcap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hL
    · exact hL.symm
  · rw [hc] at hcap
    have hx : x ∈ ({u} : Set S) := hcap ▸ Or.inl rfl
    have hy : y ∈ ({u} : Set S) := hcap ▸ Or.inr rfl
    exact (hxy (hx.trans hy.symm)).elim

omit [T2Space S] in
/-- Two edges meet only in vertices. -/
theorem common_closure (hloop : ∀ e u, ¬ J.toGraph.IsLink e u u) {e e' : Set S} (he : e ∈ J.E)
    (he' : e' ∈ J.E) (hne : e ≠ e') {p : S} (hp : p ∈ closure e) (hp' : p ∈ closure e') :
    p ∈ J.V := by
  by_contra hn
  obtain ⟨a, b, hl⟩ := (J.toGraph.edge_mem_iff_exists_isLink e).mp he
  obtain ⟨a', b', hl'⟩ := (J.toGraph.edge_mem_iff_exists_isLink e').mp he'
  have hab : a ≠ b := fun h' => hloop e a (h' ▸ hl)
  have hab' : a' ≠ b' := fun h' => hloop e' a' (h' ▸ hl')
  have hin : ∀ {f : Set S} {u v : S}, J.toGraph.IsLink f u v → u ≠ v → p ∈ closure f → p ∈ f := by
    intro f u v hf huv hpf
    rw [GM06.closure_edge_eq_union_ends J hf huv] at hpf
    rcases hpf with h' | rfl | h'
    · exact h'
    · exact (hn hf.2.1).elim
    · rw [mem_singleton_iff] at h'
      subst h'
      exact (hn hf.2.2.1).elim
  exact Set.disjoint_left.mp (GM06.disjoint_edges_of_ne J he he' hne) (hin hl hab hp)
    (hin hl' hab' hp')

omit [T2Space S] in
theorem U_eq_closures (hinc : ∀ v ∈ J.V, ∃ e ∈ J.E, J.toGraph.Inc e v) :
    J.U = ⋃ e : J.E, closure e.1 := by
  rw [J.U_eq]
  ext p
  simp only [mem_union, mem_iUnion, exists_prop, Subtype.exists]
  constructor
  · rintro (hp | ⟨e, he, hp⟩)
    · obtain ⟨e, he, hi⟩ := hinc p hp
      exact ⟨e, he, mem_closure_of_inc hi⟩
    · exact ⟨e, he, hp⟩
  · rintro ⟨e, he, hp⟩
    exact Or.inr ⟨e, he, hp⟩

/-- A homeomorphism between the point sets of two drawings that extends an isomorphism. -/
structure ArcD (J₁ J₂ : Drawing S) (fv gv : S → S) (fe ge : Set S → Set S) (g g' : S → S) :
    Prop where
  ph : PH J₁.U J₂.U g g'
  v₁ : ∀ v ∈ J₁.V, g v = fv v
  v₂ : ∀ v ∈ J₂.V, g' v = gv v
  e₁ : ∀ e ∈ J₁.E, MapsTo g (closure e) (closure (fe e))
  e₂ : ∀ e ∈ J₂.E, MapsTo g' (closure e) (closure (ge e))

variable {g g' : S → S}

omit [T2Space S] in
theorem ArcD.symm (h : ArcD J₁ J₂ fv gv fe ge g g') : ArcD J₂ J₁ gv fv ge fe g' g :=
  ⟨h.ph.symm, h.v₂, h.v₁, h.e₂, h.e₁⟩

omit [T2Space S] in
/-- Building the homeomorphism edge by edge. On the edges in `W`, where the isomorphism is the
identity, we use the identity. -/
theorem exists_arcD [Nonempty S] (hd : IsoD J₁ J₂ fv gv fe ge) (W : Set (Set S))
    (hW : ∀ e ∈ W, e ∈ J₁.E → fe e = e ∧ ∀ v ∈ closure e, v ∈ J₁.V → fv v = v)
    (hl₁ : ∀ e u, ¬ J₁.toGraph.IsLink e u u) (hl₂ : ∀ e u, ¬ J₂.toGraph.IsLink e u u)
    (hi₁ : ∀ v ∈ J₁.V, ∃ e ∈ J₁.E, J₁.toGraph.Inc e v)
    (hi₂ : ∀ v ∈ J₂.V, ∃ e ∈ J₂.E, J₂.toGraph.Inc e v) :
    ∃ g g', ArcD J₁ J₂ fv gv fe ge g g' ∧ ∀ e ∈ W, e ∈ J₁.E → ∀ p ∈ closure e, g p = p := by
  have hfin : Finite J₁.E := J₁.finite_edges.to_subtype
  have hex : ∀ e : J₁.E, ∃ a a' : S → S, PH (closure e.1) (closure (fe e.1)) a a' ∧
      (∀ v, v ∈ closure e.1 → v ∈ J₁.V → a v = fv v) ∧
      (∀ v, v ∈ closure (fe e.1) → v ∈ J₂.V → a' v = gv v) ∧
      (e.1 ∈ W → ∀ p ∈ closure e.1, a p = p) := by
    rintro ⟨e, he⟩
    obtain ⟨x, y, hl⟩ := (J₁.toGraph.edge_mem_iff_exists_isLink e).mp he
    have hxy : x ≠ y := fun h' => hl₁ e x (h' ▸ hl)
    have hl' := hd.link₁ e x y hl
    have hxy' : fv x ≠ fv y := fun h' => hl₂ (fe e) _ (h' ▸ hl')
    have hxc : x ∈ closure e := mem_closure_of_inc ⟨y, hl⟩
    have hyc : y ∈ closure e := mem_closure_of_inc ⟨x, hl.symm⟩
    by_cases heW : e ∈ W
    · obtain ⟨h₁, h₂⟩ := hW e heW he
      refine ⟨id, id, ?_, fun v hv hvV => (h₂ v hv hvV).symm, ?_, fun _ _ _ => rfl⟩
      · simp only [h₁]
        exact ⟨mapsTo_id _, mapsTo_id _, fun _ _ => rfl, fun _ _ => rfl, continuousOn_id,
          continuousOn_id⟩
      · intro v hv hvV
        have hm : v ∈ closure (fe e) ∩ J₂.V := ⟨hv, hvV⟩
        rw [hl'.2.2.2] at hm
        rcases hm with rfl | hm
        · rw [hd.vl x hl.left_mem]
          exact h₂ x hxc hl.left_mem
        · obtain rfl : v = fv y := hm
          rw [hd.vl y hl.right_mem]
          exact h₂ y hyc hl.right_mem
    obtain ⟨a, a', hP, h₀, h₁⟩ := exists_line_PH (closure_line hl hxy) (closure_line hl' hxy')
    refine ⟨a, a', hP, ?_, ?_, fun h' => absurd h' heW⟩
    · intro v hv hvV
      have hm : v ∈ closure e ∩ J₁.V := ⟨hv, hvV⟩
      rw [hl.2.2.2] at hm
      rcases hm with rfl | hm
      · exact h₀
      · obtain rfl : v = y := hm
        exact h₁
    · intro v hv hvV
      have hm : v ∈ closure (fe e) ∩ J₂.V := ⟨hv, hvV⟩
      rw [hl'.2.2.2] at hm
      rcases hm with rfl | hm
      · rw [hd.vl x hl.left_mem, ← h₀]
        exact hP.2.2.1 hxc
      · obtain rfl : v = fv y := hm
        rw [hd.vl y hl.right_mem, ← h₁]
        exact hP.2.2.1 hyc
  choose a a' hP hv hv' hvW using hex
  have hinj : ∀ {e e' : Set S}, e ∈ J₁.E → e' ∈ J₁.E → fe e = fe e' → e = e' := by
    intro e e' he he' h'
    rw [← hd.el e he, ← hd.el e' he', h']
  obtain ⟨g, g', hPH, hg, hg'⟩ := exists_glue (A := fun e : J₁.E => closure e.1)
    (B := fun e : J₁.E => closure (fe e.1)) (fun _ => isClosed_closure)
    (fun _ => isClosed_closure) hP
    (fun i j x hi hj => by
      by_cases hij : i = j
      · rw [hij]
      · have hx := common_closure hl₁ i.2 j.2 (fun h' => hij (Subtype.ext h')) hi hj
        rw [hv i x hi hx, hv j x hj hx])
    (fun i j y hi hj => by
      by_cases hij : i = j
      · rw [hij]
      · have hy := common_closure hl₂ (hd.e₁ _ i.2) (hd.e₁ _ j.2)
          (fun h' => hij (Subtype.ext (hinj i.2 j.2 h'))) hi hj
        rw [hv' i y hi hy, hv' j y hj hy])
  have hU₁ := U_eq_closures hi₁
  have hU₂ : J₂.U = ⋃ e : J₁.E, closure (fe e.1) := by
    rw [U_eq_closures hi₂]
    ext p
    simp only [mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨e, he, hp⟩
      exact ⟨ge e, hd.e₂ e he, by rwa [hd.er e he]⟩
    · rintro ⟨e, he, hp⟩
      exact ⟨fe e, hd.e₁ e he, hp⟩
  refine ⟨g, g', ⟨by rw [hU₁, hU₂]; exact hPH, ?_, ?_, ?_, ?_⟩, fun e heW he p hp => ?_⟩
  · intro v hv₀
    obtain ⟨e, he, hi⟩ := hi₁ v hv₀
    have hc := mem_closure_of_inc hi
    rw [hg ⟨e, he⟩ hc]
    exact hv ⟨e, he⟩ v hc hv₀
  · intro v hv₀
    obtain ⟨e, he, hi⟩ := hi₂ v hv₀
    have hc : v ∈ closure (fe (ge e)) := by
      rw [hd.er e he]
      exact mem_closure_of_inc hi
    rw [hg' ⟨ge e, hd.e₂ e he⟩ hc]
    exact hv' ⟨ge e, hd.e₂ e he⟩ v hc hv₀
  · intro e he p hp
    rw [hg ⟨e, he⟩ hp]
    exact (hP ⟨e, he⟩).1 hp
  · intro e he p hp
    have hc : p ∈ closure (fe (ge e)) := by rwa [hd.er e he]
    rw [hg' ⟨ge e, hd.e₂ e he⟩ hc]
    exact (hP ⟨ge e, hd.e₂ e he⟩).2.1 hc
  · rw [hg ⟨e, he⟩ hp]
    exact hvW ⟨e, he⟩ heW p hp

theorem walk_length_eq {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    W.length = W.edges.length := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [GraphWalk.length, GraphWalk.edges]

/-- An isomorphism carries circuits to circuits. -/
theorem transport_circuit (hd : IsoD J₁ J₂ fv gv fe ge) {C : Drawing S} (hC : C.IsCircuit)
    (hs : C.IsSubdrawing J₁) :
    ∃ C' : Drawing S, C'.IsCircuit ∧ C'.IsSubdrawing J₂ ∧ C'.V = fv '' C.V ∧ C'.E = fe '' C.E := by
  obtain ⟨u, W, ⟨hn, he⟩, hpos, hV, hE⟩ := hC
  obtain ⟨W₁, hs₁, he₁⟩ := hs.exists_walk_up W
  obtain ⟨W₂, hs₂, he₂⟩ := exists_walk_map (f := fv) (g := fe) hd.v₁ hd.link₁ W₁
  have hsub := walkDrawing_isSubdrawing J₂ W₂
  obtain ⟨W₃, hs₃, he₃⟩ := hsub.exists_walk_down W₂
    (by rw [walkDrawing_V]; exact fun x hx => hx) (by rw [walkDrawing_E]; exact fun e he => he)
  have hsup : W₃.support = W.support.map fv := by rw [hs₃, hs₂, hs₁]
  have hedg : W₃.edges = W.edges.map fe := by rw [he₃, he₂, he₁]
  have hVm : ∀ x, x ∈ W.support → x ∈ J₁.V := fun x hx => hs.1 (by rw [hV]; exact hx)
  have hEm : ∀ e, e ∈ W.edges → e ∈ J₁.E := fun e hx => hs.2 (by rw [hE]; exact hx)
  refine ⟨walkDrawing J₂ W₂, ⟨fv u, W₃, ⟨?_, ?_⟩, ?_, ?_, ?_⟩, hsub, ?_, ?_⟩
  · rw [hsup, ← List.map_tail]
    refine List.Nodup.map_on ?_ hn
    intro x hx y hy hxy
    rw [← hd.vl x (hVm x (List.mem_of_mem_tail hx)), hxy,
      hd.vl y (hVm y (List.mem_of_mem_tail hy))]
  · rw [hedg]
    refine List.Nodup.map_on ?_ he
    intro x hx y hy hxy
    rw [← hd.el x (hEm x hx), hxy, hd.el y (hEm y hy)]
  · rw [walk_length_eq, hedg, List.length_map, ← walk_length_eq]
    exact hpos
  · rw [walkDrawing_V, hs₃]
  · rw [walkDrawing_E, he₃]
  · rw [walkDrawing_V, hs₂, hs₁, hV]
    ext x
    simp
  · rw [walkDrawing_E, he₂, he₁, hE]
    ext x
    simp

omit [T2Space S] in
/-- An isomorphism carries peripheral circuits to peripheral circuits. -/
theorem peripheral_map (hd : IsoD J₁ J₂ fv gv fe ge) {C C' : Drawing S} (hs : C.IsSubdrawing J₁)
    (hP : IsPeripheral J₁ C) (hV : C'.V = fv '' C.V) (hE : C'.E = fe '' C.E) :
    IsPeripheral J₂ C' := by
  have hM : ∀ {a}, a ∈ J₁.E \ C.E → fe a ∈ J₂.E \ C'.E := by
    rintro a ⟨ha, hn⟩
    refine ⟨hd.e₁ a ha, fun hc => hn ?_⟩
    rw [hE] at hc
    obtain ⟨b, hb, hab⟩ := hc
    rw [← hd.el a ha, ← hab, hd.el b (hs.2 hb)]
    exact hb
  have hchain : ∀ {e f}, f ∈ cls J₁.toGraph C.V (J₁.E \ C.E) e →
      fe f ∈ cls J₂.toGraph C'.V (J₂.E \ C'.E) (fe e) := by
    intro e f hf
    induction hf with
    | refl => exact mem_cls_self
    | @tail a b _ hadj ih =>
      obtain ⟨ha, hb, w, hw, ⟨p, hp⟩, ⟨q, hq⟩⟩ := hadj
      refine cls_step ih ⟨hM ha, hM hb, fv w, ?_, ⟨fv p, hd.link₁ _ _ _ hp⟩,
        ⟨fv q, hd.link₁ _ _ _ hq⟩⟩
      rw [hV]
      rintro ⟨c, hc, hcw⟩
      apply hw
      rw [← hd.vl w hp.left_mem, ← hcw, hd.vl c (hs.1 hc)]
      exact hc
  intro e he f hf
  have hback : ∀ {a}, a ∈ J₂.E \ C'.E → ge a ∈ J₁.E \ C.E := by
    rintro a ⟨ha, hn⟩
    refine ⟨hd.e₂ a ha, fun hc => hn ?_⟩
    rw [hE, ← hd.er a ha]
    exact mem_image_of_mem fe hc
  have := hchain (hP _ (hback he) _ (hback hf))
  rwa [hd.er e he.1, hd.er f hf.1] at this

/-- The face of a cell structure lies on one side of its boundary, and all of `J` on the other. -/
theorem peripheral_of_face {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)} (hS : IsSphere S)
    (h : SubData J.toGraph G₀ P) {𝓕 : Set (Set S)} (hF : IsFaceSys J J 𝓕) {D : Set S}
    (hD : D ∈ 𝓕) {C : Drawing S} (hC : C.IsCircuit) (hs : C.IsSubdrawing J)
    (hU : C.U = discBd D) : IsPeripheral J C := by
  have hcl := (IsSphere.isClosedSurface hS).1
  obtain ⟨Δ₁, Δ₂, -, hd₁, hd₂, hb₁, hb₂, hun, -, -, huniq⟩ :=
    sphere_disc S hS C.U (GM11.IsCircuit.isOArc_U hC)
  have hother : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = C.U ∧ D ∪ Δ = univ := by
    rcases huniq D (hF.disc D hD) hU.symm with rfl | rfl
    · exact ⟨Δ₂, hd₂, hb₂, hun⟩
    · exact ⟨Δ₁, hd₁, hb₁, (union_comm _ _).trans hun⟩
  obtain ⟨Δ, hΔ, hb, hu⟩ := hother
  refine peripheral_of_side hcl h hC hs hΔ hb fun p hp => ?_
  have hm : p ∈ D ∪ Δ := by rw [hu]; exact mem_univ p
  rcases hm with hm | hm
  · by_cases hpb : p ∈ discBd D
    · exact Surface.discBd_subset _ (hb ▸ hU ▸ hpb)
    · exact (Set.disjoint_left.mp (hF.free D hD) ⟨hm, hpb⟩ hp).elim
  · exact hm

/-- A circuit has at most two edges at a vertex. -/
theorem circuit_not_three {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) {C : Drawing S} (hC : C.IsCircuit) (hs : C.IsSubdrawing J) {v : S}
    {a b d : Set S} (ha : a ∈ C.E) (hb : b ∈ C.E) (hd : d ∈ C.E) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (ia : J.toGraph.Inc a v) (ib : J.toGraph.Inc b v) (id' : J.toGraph.Inc d v) :
    False := by
  have hv : v ∈ C.V := by
    have hm : v ∈ closure a ∩ J.V := ⟨mem_closure_of_inc ia, ia.vertex_mem⟩
    rw [← hs.closure_inter_V ha] at hm
    exact hm.2
  obtain ⟨w, hw, hne⟩ : ∃ w ∈ C.V, w ≠ v := by
    obtain ⟨p, hp⟩ := ia
    refine ⟨p, ?_, fun h' => no_loop h (h' ▸ hp)⟩
    have hm : p ∈ closure a ∩ J.V := ⟨mem_closure_of_inc ⟨v, hp.symm⟩, hp.right_mem⟩
    rw [← hs.closure_inter_V ha] at hm
    exact hm.2
  obtain ⟨P₁, P₂, hP₁, hP₂, hs₁, hs₂, -, -, -, -, hsup⟩ :=
    Drawing.IsCircuit.exists_two_paths hC hv hw hne.symm
  obtain ⟨X₁, hX₁, hU₁, -, -⟩ := exists_walk_of_path hP₁ (hs₁.trans hs)
  obtain ⟨X₂, hX₂, hU₂, -, -⟩ := exists_walk_of_path hP₂ (hs₂.trans hs)
  have hmem : ∀ {Q : Drawing S} {r t : S} {X : GraphWalk J.toGraph r t}, Q.IsSubdrawing J →
      wU J X = Q.U → ∀ {c}, c ∈ Q.E → c ∈ X.edges := by
    intro Q r t X hQ hU c hc
    obtain ⟨p, hp⟩ : c.Nonempty := (hQ.2 hc).1
    refine edge_mem_of_meets (hQ.2 hc) hp ?_
    rw [hU, Q.U_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, subset_closure hp⟩)
  have hsplit : ∀ {c}, c ∈ C.E → c ∈ X₁.edges ∨ c ∈ X₂.edges := by
    intro c hc
    have hE := Drawing.sup_E (Γ := C) hs₁ hs₂
    rw [hsup] at hE
    rw [hE] at hc
    rcases hc with hc | hc
    · exact Or.inl (hmem (hs₁.trans hs) hU₁ hc)
    · exact Or.inr (hmem (hs₂.trans hs) hU₂ hc)
  have one : ∀ {p q}, p ∈ X₁.edges → q ∈ X₁.edges → J.toGraph.Inc p v → J.toGraph.Inc q v → p = q :=
    fun hp hq ip iq => eq_of_inc_start X₁ hX₁ hp hq ip iq
  have two : ∀ {p q}, p ∈ X₂.edges → q ∈ X₂.edges → J.toGraph.Inc p v → J.toGraph.Inc q v → p = q :=
    fun hp hq ip iq => eq_of_inc_start X₂ hX₂ hp hq ip iq
  rcases hsplit ha with h₁ | h₁ <;> rcases hsplit hb with h₂ | h₂ <;> rcases hsplit hd with h₃ | h₃
  · exact hab (one h₁ h₂ ia ib)
  · exact hab (one h₁ h₂ ia ib)
  · exact had (one h₁ h₃ ia id')
  · exact hbd (two h₂ h₃ ib id')
  · exact hbd (one h₂ h₃ ib id')
  · exact had (two h₁ h₃ ia id')
  · exact hab (two h₁ h₂ ia ib)
  · exact hab (two h₁ h₂ ia ib)

/-- Two faces with the same boundary are equal, since `J` is not a circuit. -/
theorem faces_inj {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)} (hS : IsSphere S)
    (h : SubData J.toGraph G₀ P) {𝓕 : Set (Set S)} (hF : IsFaceSys J J 𝓕) {D D' : Set S}
    (hD : D ∈ 𝓕) (hD' : D' ∈ 𝓕) (hb : discBd D = discBd D') : D = D' := by
  by_contra hne
  obtain ⟨C, hC, hs, hU⟩ := hF.circuit D hD
  obtain ⟨Δ₁, Δ₂, -, -, -, -, -, hun, -, -, huniq⟩ :=
    sphere_disc S hS C.U (GM11.IsCircuit.isOArc_U hC)
  have hcov : D ∪ D' = univ := by
    rcases huniq D (hF.disc D hD) hU.symm with rfl | rfl <;>
      rcases huniq D' (hF.disc D' hD') (hb.symm.trans hU.symm) with h' | h'
    · exact (hne h'.symm).elim
    · rw [h']
      exact hun
    · rw [h', union_comm]
      exact hun
    · exact (hne h'.symm).elim
  have hall : J.U ⊆ C.U := by
    intro p hp
    have hm : p ∈ D ∪ D' := by rw [hcov]; exact mem_univ p
    rcases hm with hm | hm
    · by_contra hn
      exact Set.disjoint_left.mp (hF.free D hD) ⟨hm, fun h' => hn (hU ▸ h')⟩ hp
    · by_contra hn
      exact Set.disjoint_left.mp (hF.free D' hD') ⟨hm, fun h' => hn (hU ▸ hb ▸ h')⟩ hp
  have hedges : ∀ e ∈ J.E, e ∈ C.E := by
    intro e he
    by_contra hn
    obtain ⟨p, hp⟩ : e.Nonempty := he.1
    exact Set.disjoint_left.mp (edge_disjoint_U hs he hn) hp (hall (he.2.1 hp).1)
  obtain ⟨v, hv⟩ : ∃ v, v ∈ V(G₀) := by
    have hpos : 0 < V(G₀).ncard := by have := h.simple.2.1; omega
    exact (Set.ncard_pos h.finite_V₀).mp hpos
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, ⟨y₁, l₁⟩, ⟨y₂, l₂⟩, ⟨y₃, l₃⟩⟩ :=
    IsSimpleThreeConnected.exists_three_edges h.simple hv
  have hpick : ∀ {e y}, G₀.IsLink e v y → ∃ a ∈ E(P e), a ∈ C.E ∧ J.toGraph.Inc a v := by
    intro e y hl
    obtain ⟨a, ha, hi⟩ := (h.exists_edge_at_ends hl).1
    exact ⟨a, ha, hedges a hi.edge_mem, hi⟩
  obtain ⟨a, ha, haC, ia⟩ := hpick l₁
  obtain ⟨b, hb', hbC, ib⟩ := hpick l₂
  obtain ⟨d, hd, hdC, id'⟩ := hpick l₃
  have hdist : ∀ {e f p q}, e ∈ E(G₀) → f ∈ E(G₀) → e ≠ f → p ∈ E(P e) → q ∈ E(P f) → p ≠ q := by
    intro e f p q he hf hef hp hq hpq
    exact Set.disjoint_left.mp (h.disj e he f hf hef).1 hp (hpq ▸ hq)
  exact circuit_not_three h hC hs haC hbC hdC (hdist l₁.edge_mem l₂.edge_mem h12 ha hb')
    (hdist l₁.edge_mem l₃.edge_mem h13 ha hd) (hdist l₂.edge_mem l₃.edge_mem h23 hb' hd) ia ib id'

omit [T2Space S] in
/-- Two faces meet only in their boundaries. -/
theorem IsFaceSys.overlap {𝓕 : Set (Set S)} (hF : IsFaceSys J J 𝓕) {D D' : Set S} (hD : D ∈ 𝓕)
    (hD' : D' ∈ 𝓕) (hne : D ≠ D') {p : S} (hp : p ∈ D) (hp' : p ∈ D') :
    p ∈ discBd D ∧ p ∈ discBd D' := by
  have hbd : ∀ {X}, X ∈ 𝓕 → discBd X ⊆ J.U := by
    intro X hX
    obtain ⟨C, -, hs, hU⟩ := hF.circuit X hX
    rw [← hU]
    exact hs.U_subset
  by_cases h₁ : p ∈ discBd D <;> by_cases h₂ : p ∈ discBd D'
  · exact ⟨h₁, h₂⟩
  · exact (Set.disjoint_left.mp (hF.free D' hD') ⟨hp', h₂⟩ (hbd hD h₁)).elim
  · exact (Set.disjoint_left.mp (hF.free D hD) ⟨hp, h₁⟩ (hbd hD' h₂)).elim
  · exact (Set.disjoint_left.mp (hF.disj D hD D' hD' hne) ⟨hp, h₁⟩ ⟨hp', h₂⟩).elim

omit [T2Space S] in
theorem mapsTo_U {C C' : Drawing S} (hV : ∀ v ∈ C.V, g v ∈ C'.V)
    (hE : ∀ e ∈ C.E, ∃ e' ∈ C'.E, MapsTo g (closure e) (closure e')) : MapsTo g C.U C'.U := by
  intro p hp
  rw [C.U_eq] at hp
  rw [C'.U_eq]
  rcases hp with hp | hp
  · exact Or.inl (hV p hp)
  · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
    obtain ⟨e', he', hm⟩ := hE e he
    exact Or.inr (mem_iUnion₂.mpr ⟨e', he', hm hpe⟩)

/-- An isomorphism carries faces to faces. -/
theorem exists_face_image {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)} (hS : IsSphere S)
    (h : SubData J₁.toGraph G₀ P) (hi₂ : ∀ v ∈ J₂.V, ∃ e ∈ J₂.E, J₂.toGraph.Inc e v)
    (hd : IsoD J₁ J₂ fv gv fe ge) (ha : ArcD J₁ J₂ fv gv fe ge g g') {𝓕₁ 𝓕₂ : Set (Set S)}
    (hF₁ : IsFaceSys J₁ J₁ 𝓕₁) (hF₂ : IsFaceSys J₂ J₂ 𝓕₂) {D : Set S} (hD : D ∈ 𝓕₁) :
    ∃ D' ∈ 𝓕₂, PH (discBd D) (discBd D') g g' := by
  have hcl := (IsSphere.isClosedSurface hS).1
  obtain ⟨C, hC, hs, hU⟩ := hF₁.circuit D hD
  have per := peripheral_of_face hS h hF₁ hD hC hs hU
  obtain ⟨C', hC', hs', hV, hE⟩ := transport_circuit hd hC hs
  have per' := peripheral_map hd hs per hV hE
  obtain ⟨D', hD', hb, hfree⟩ := exists_free_side_of_peripheral hS hC' hs' hi₂ per'
  refine ⟨D', hF₂.eq_of_free hcl hD' (hb ▸ hs'.U_subset) hfree, ?_⟩
  rw [← hU, hb]
  refine ha.ph.restrict hs.U_subset hs'.U_subset ?_ ?_
  · refine mapsTo_U (fun v hv => ?_) fun e he => ?_
    · rw [ha.v₁ v (hs.1 hv), hV]
      exact mem_image_of_mem fv hv
    · exact ⟨fe e, hE ▸ mem_image_of_mem fe he, ha.e₁ e (hs.2 he)⟩
  · refine mapsTo_U (fun v hv => ?_) fun e he => ?_
    · rw [hV] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      rw [ha.v₂ _ (hd.v₁ c (hs.1 hc)), hd.vl c (hs.1 hc)]
      exact hc
    · rw [hE] at he
      obtain ⟨c, hc, rfl⟩ := he
      refine ⟨c, hc, ?_⟩
      have := ha.e₂ _ (hd.e₁ c (hs.2 hc))
      rwa [hd.el c (hs.2 hc)] at this

/-- The main step of Whitney's theorem, for total functions that carry the isomorphism. -/
theorem exists_homeo {G₁ G₂ : Graph S (Set S)} {P₁ P₂ : Set S → Graph S (Set S)} (hS : IsSphere S)
    (h₁ : SubData J₁.toGraph G₁ P₁) (h₂ : SubData J₂.toGraph G₂ P₂)
    (hd : IsoD J₁ J₂ fv gv fe ge) (W : Set (Set S))
    (hW : ∀ e ∈ W, e ∈ J₁.E → fe e = e ∧ ∀ v ∈ closure e, v ∈ J₁.V → fv v = v) :
    ∃ h : S ≃ₜ S, (∀ v ∈ J₁.V, h v = fv v) ∧ (∀ e ∈ J₁.E, h '' e = fe e) ∧
      ∀ e ∈ W, e ∈ J₁.E → ∀ p ∈ closure e, h p = p := by
  classical
  have hne : Nonempty S := by
    obtain ⟨e⟩ := hS
    exact ⟨e.symm OnePoint.infty⟩
  have hi₁ : ∀ v ∈ J₁.V, ∃ e ∈ J₁.E, J₁.toGraph.Inc e v := fun v hv => by
    obtain ⟨e, he, -, -, -, ie, -⟩ := h₁.exists_two_edges (x := v) hv
    exact ⟨e, he, ie⟩
  have hi₂ : ∀ v ∈ J₂.V, ∃ e ∈ J₂.E, J₂.toGraph.Inc e v := fun v hv => by
    obtain ⟨e, he, -, -, -, ie, -⟩ := h₂.exists_two_edges (x := v) hv
    exact ⟨e, he, ie⟩
  have hl₁ : ∀ e u, ¬ J₁.toGraph.IsLink e u u := fun e u hl => no_loop h₁ hl
  have hl₂ : ∀ e u, ¬ J₂.toGraph.IsLink e u u := fun e u hl => no_loop h₂ hl
  obtain ⟨𝓕₁, hF₁⟩ := exists_faces hS h₁
  obtain ⟨𝓕₂, hF₂⟩ := exists_faces hS h₂
  obtain ⟨g, g', ha, hgW⟩ := exists_arcD hd W hW hl₁ hl₂ hi₁ hi₂
  have hstep : ∀ D : 𝓕₁, ∃ D' ∈ 𝓕₂, PH (discBd D.1) (discBd D') g g' := fun D =>
    exists_face_image hS h₁ hi₂ hd ha hF₁ hF₂ D.2
  have hback : ∀ {D'}, D' ∈ 𝓕₂ → ∃ D ∈ 𝓕₁, PH (discBd D') (discBd D) g' g := fun hD =>
    exists_face_image hS h₂ hi₁ hd.symm ha.symm hF₂ hF₁ hD
  choose τ hτ hPτ using hstep
  have hext : ∀ D : 𝓕₁, ∃ f f', PH D.1 (τ D) f f' ∧ EqOn f g (discBd D.1) ∧
      EqOn f' g' (discBd (τ D)) := fun D =>
    exists_disc_PH (hF₁.disc _ D.2) (hF₂.disc _ (hτ D)) (hPτ D)
  choose f f' hf hfg hfg' using hext
  have hτinj : ∀ i j, i ≠ j → τ i ≠ τ j := by
    intro i j hij heq
    apply hij
    apply Subtype.ext
    refine faces_inj hS h₁ hF₁ i.2 j.2 ?_
    rw [← (hPτ i).symm.image_eq, ← (hPτ j).symm.image_eq, heq]
  have hfin : Finite 𝓕₁ := hF₁.finite.to_subtype
  obtain ⟨F, F', hPH, hFe, hFe'⟩ := exists_glue (A := fun D : 𝓕₁ => D.1) (B := τ)
    (fun D => (hF₁.disc _ D.2).isClosed) (fun D => (hF₂.disc _ (hτ D)).isClosed) hf
    (fun i j x hi hj => by
      by_cases hij : i = j
      · rw [hij]
      · obtain ⟨h₃, h₄⟩ := hF₁.overlap i.2 j.2 (fun h' => hij (Subtype.ext h')) hi hj
        rw [hfg i h₃, hfg j h₄])
    (fun i j y hi hj => by
      by_cases hij : i = j
      · rw [hij]
      · obtain ⟨h₃, h₄⟩ := hF₂.overlap (hτ i) (hτ j) (hτinj i j hij) hi hj
        rw [hfg' i h₃, hfg' j h₄])
  have hA : (⋃ D : 𝓕₁, D.1) = univ := by
    rw [← sUnion_eq_iUnion]
    exact hF₁.cover
  have hB : (⋃ D : 𝓕₁, τ D) = univ := by
    refine eq_univ_of_univ_subset fun y _ => ?_
    have hy : y ∈ ⋃₀ 𝓕₂ := by rw [hF₂.cover]; exact mem_univ y
    obtain ⟨D', hD', hyD⟩ := hy
    obtain ⟨D, hD, hP⟩ := hback hD'
    have heq : τ ⟨D, hD⟩ = D' := by
      refine faces_inj hS h₂ hF₂ (hτ _) hD' ?_
      rw [← (hPτ ⟨D, hD⟩).image_eq]
      exact hP.symm.image_eq
    exact mem_iUnion.mpr ⟨⟨D, hD⟩, heq ▸ hyD⟩
  rw [hA, hB] at hPH
  let h : S ≃ₜ S :=
    { toFun := F
      invFun := F'
      left_inv := fun x => hPH.2.2.1 (mem_univ x)
      right_inv := fun x => hPH.2.2.2.1 (mem_univ x)
      continuous_toFun := continuousOn_univ.mp hPH.2.2.2.2.1
      continuous_invFun := continuousOn_univ.mp hPH.2.2.2.2.2 }
  have hFg : ∀ p ∈ J₁.U, F p = g p := by
    intro p hp
    have hc : p ∈ ⋃₀ 𝓕₁ := by rw [hF₁.cover]; exact mem_univ p
    obtain ⟨D, hD, hpD⟩ := hc
    have hpb : p ∈ discBd D := by
      by_contra hn
      exact Set.disjoint_left.mp (hF₁.free D hD) ⟨hpD, hn⟩ hp
    rw [hFe ⟨D, hD⟩ hpD]
    exact hfg ⟨D, hD⟩ hpb
  refine ⟨h, fun v hv => (hFg v (J₁.V_subset_U hv)).trans (ha.v₁ v hv), fun e he => ?_,
    fun e heW he p hp => ?_⟩
  swap
  · have hpU : p ∈ J₁.U := J₁.closure_subset_U he hp
    exact (hFg p hpU).trans (hgW e heW he p hp)
  obtain ⟨x, y, hl⟩ := (J₁.toGraph.edge_mem_iff_exists_isLink e).mp he
  have hxy : x ≠ y := fun h' => hl₁ e x (h' ▸ hl)
  have hl' := hd.link₁ e x y hl
  have heU : e ⊆ J₁.U := fun p hp => (he.2.1 hp).1
  have heU' : fe e ⊆ J₂.U := fun p hp => ((hd.e₁ e he).2.1 hp).1
  have hclU : closure e ⊆ J₁.U := by
    rw [J₁.U_eq]
    exact fun p hp => Or.inr (mem_iUnion₂.mpr ⟨e, he, hp⟩)
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change F p ∈ fe e
    rw [hFg p (heU hp)]
    have hin := ha.e₁ e he (subset_closure hp)
    rw [GM06.closure_edge_eq_union_ends J₂ hl' (fun h' => hl₂ _ _ (h' ▸ hl'))] at hin
    have hpV : p ∉ J₁.V := (he.2.1 hp).2
    rcases hin with h₃ | h₃ | h₃
    · exact h₃
    · rw [← ha.v₁ x hl.left_mem] at h₃
      have := congrArg g' h₃
      rw [ha.ph.2.2.1 (heU hp), ha.ph.2.2.1 (J₁.V_subset_U hl.left_mem)] at this
      exact (hpV (this ▸ hl.left_mem)).elim
    · rw [mem_singleton_iff, ← ha.v₁ y hl.right_mem] at h₃
      have := congrArg g' h₃
      rw [ha.ph.2.2.1 (heU hp), ha.ph.2.2.1 (J₁.V_subset_U hl.right_mem)] at this
      exact (hpV (this ▸ hl.right_mem)).elim
  · intro hq
    have hin := ha.e₂ _ (hd.e₁ e he) (subset_closure hq)
    rw [hd.el e he] at hin
    have hgq : g (g' q) = q := ha.ph.2.2.2.1 (heU' hq)
    have hqV : q ∉ J₂.V := ((hd.e₁ e he).2.1 hq).2
    have hmem : g' q ∈ e := by
      rw [GM06.closure_edge_eq_union_ends J₁ hl hxy] at hin
      rcases hin with h₃ | h₃ | h₃
      · exact h₃
      · rw [h₃, ha.v₁ x hl.left_mem] at hgq
        exact (hqV (hgq ▸ hl'.2.1)).elim
      · rw [mem_singleton_iff] at h₃
        rw [h₃, ha.v₁ y hl.right_mem] at hgq
        exact (hqV (hgq ▸ hl'.2.2.1)).elim
    exact ⟨g' q, hmem, (hFg _ (heU hmem)).trans hgq⟩

end Assembly

/-- Whitney's theorem, with a homeomorphism that fixes each point of the edges in `W`, given that
the
isomorphism fixes these edges and their ends. -/
theorem whitney_fixing {S : Type u} [TopologicalSpace S] (hSurf : IsSurface S)
    (hS : IsSphere S) (J₁ J₂ : Drawing S) (hsub : IsSubdivisionOfSimpleThreeConnected J₁.toGraph)
    (φ : Iso J₁.toGraph J₂.toGraph) (W : Set (Set S))
    (hW : ∀ e : E(J₁.toGraph), e.1 ∈ W → (φ.edgeEquiv e).1 = e.1 ∧
      ∀ v : V(J₁.toGraph), v.1 ∈ closure e.1 → (φ.vertexEquiv v).1 = v.1) :
    ∃ h : S ≃ₜ S, (∀ v : V(J₁.toGraph), h v.1 = (φ.vertexEquiv v).1) ∧
      (∀ e : E(J₁.toGraph), h '' e.1 = (φ.edgeEquiv e).1) ∧
      ∀ e ∈ W, e ∈ J₁.E → ∀ p ∈ closure e, h p = p := by
  classical
  have : T2Space S := hSurf.2.1
  obtain ⟨G₁, P₁, h₁⟩ := exists_subData hsub
  obtain ⟨G₂, P₂, h₂⟩ := exists_subData (isSubdivision_of_iso hsub φ)
  let fv : S → S := fun x => if hx : x ∈ J₁.V then (φ.vertexEquiv ⟨x, hx⟩).1 else x
  let gv : S → S := fun x => if hx : x ∈ J₂.V then (φ.vertexEquiv.symm ⟨x, hx⟩).1 else x
  let fe : Set S → Set S := fun x => if hx : x ∈ J₁.E then (φ.edgeEquiv ⟨x, hx⟩).1 else x
  let ge : Set S → Set S := fun x => if hx : x ∈ J₂.E then (φ.edgeEquiv.symm ⟨x, hx⟩).1 else x
  have hfv : ∀ x : V(J₁.toGraph), fv x.1 = (φ.vertexEquiv x).1 := fun x => dite_eq_left x.2
  have hgv : ∀ x : V(J₂.toGraph), gv x.1 = (φ.vertexEquiv.symm x).1 := fun x => dite_eq_left x.2
  have hfe : ∀ x : E(J₁.toGraph), fe x.1 = (φ.edgeEquiv x).1 := fun x => dite_eq_left x.2
  have hge : ∀ x : E(J₂.toGraph), ge x.1 = (φ.edgeEquiv.symm x).1 := fun x => dite_eq_left x.2
  have hd : IsoD J₁ J₂ fv gv fe ge := by
    refine ⟨fun x hx => ?_, fun y hy => ?_, fun x hx => ?_, fun y hy => ?_, fun x hx => ?_,
      fun y hy => ?_, fun x hx => ?_, fun y hy => ?_, fun e x y hl => ?_, fun e x y hl => ?_⟩
    · rw [hfv ⟨x, hx⟩]
      exact (φ.vertexEquiv ⟨x, hx⟩).2
    · rw [hgv ⟨y, hy⟩]
      exact (φ.vertexEquiv.symm ⟨y, hy⟩).2
    · rw [hfv ⟨x, hx⟩, hgv (φ.vertexEquiv ⟨x, hx⟩), Equiv.symm_apply_apply]
    · rw [hgv ⟨y, hy⟩, hfv (φ.vertexEquiv.symm ⟨y, hy⟩), Equiv.apply_symm_apply]
    · rw [hfe ⟨x, hx⟩]
      exact (φ.edgeEquiv ⟨x, hx⟩).2
    · rw [hge ⟨y, hy⟩]
      exact (φ.edgeEquiv.symm ⟨y, hy⟩).2
    · rw [hfe ⟨x, hx⟩, hge (φ.edgeEquiv ⟨x, hx⟩), Equiv.symm_apply_apply]
    · rw [hge ⟨y, hy⟩, hfe (φ.edgeEquiv.symm ⟨y, hy⟩), Equiv.apply_symm_apply]
    · have := (φ.isLink_iff ⟨e, hl.edge_mem⟩ ⟨x, hl.left_mem⟩ ⟨y, hl.right_mem⟩).mp hl
      rw [hfe ⟨e, hl.edge_mem⟩, hfv ⟨x, hl.left_mem⟩, hfv ⟨y, hl.right_mem⟩]
      exact this
    · rw [hge ⟨e, hl.edge_mem⟩, hgv ⟨x, hl.left_mem⟩, hgv ⟨y, hl.right_mem⟩]
      refine (φ.isLink_iff _ _ _).mpr ?_
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hl
  obtain ⟨h, hv, he, hfix⟩ := exists_homeo hS h₁ h₂ hd W (fun e heW he => by
    have h₃ := hW ⟨e, he⟩ heW
    refine ⟨(hfe ⟨e, he⟩).trans h₃.1, fun v hv hvV => ?_⟩
    exact (hfv ⟨v, hvV⟩).trans (h₃.2 ⟨v, hvV⟩ hv))
  exact ⟨h, fun v => (hv v.1 v.2).trans (hfv v), fun e => (he e.1 e.2).trans (hfe e), hfix⟩

/-- **Whitney's theorem.** Two drawings in a sphere of a subdivision of a simple 3-connected graph
are related by a homeomorphism of the sphere that extends the graph isomorphism. Graph Minors XIV
uses it in the proof of (6.4) (page 34). The route is the one recorded in M. Grohe and S. Kiefer,
arXiv:1904.07216v1, Section 2, page 6: the face boundaries of a 3-connected plane graph are its
chordless non-separating circuits, so they do not depend on the drawing. Here that fact is
`peripheral_of_side` and `exists_free_side_of_peripheral`. The homeomorphism is then built edge by
edge and face by face with the Schoenflies theorem. The original source is H. Whitney, *Congruent
graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932), 150--168, named here as Grohe and
Kiefer cite it. That paper was not read for this proof. -/
theorem whitney_planar_uniqueness : WhitneyPlanarUniquenessStatement.{u} := by
  intro S _ _ hSurf hS J₁ J₂ hsub φ
  obtain ⟨h, h₁, h₂, -⟩ := whitney_fixing hSurf hS J₁ J₂ hsub φ ∅ (fun _ h' => absurd h'
    (notMem_empty _))
  exact ⟨h, h₁, h₂⟩

end GraphMinor.GM14.Whitney
