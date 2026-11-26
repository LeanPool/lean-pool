/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.Surface.Circle
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Sectors of a disc around a point

Let `v` be an interior point of a closed disc `D`, and let `J_i` be finitely many (at least two)
lines from `v` to the boundary of `D`, which meet only at `v`, and which meet the boundary only at
their other ends. Then the lines cut `D` into closed discs, the sectors, one between each line and
the next in a cyclic order around `v`.

The papers use this picture without comment, whenever they speak of the edges and regions around a
vertex. Here `exists_fanInv` proves it, by adding one line at a time and splitting one sector with
`DiscIArcStatement`. The cyclic order is the function `next`.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

section Lines

/-- The range of an injective curve is a line. -/
theorem isLineWithEnds_range [T2Space S] (f : C(I, S)) (hf : Function.Injective f) :
    IsLineWithEnds (range f) (f 0) (f 1) := by
  let e : I ≃ₜ range f :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective f hf)
      f.continuous.rangeFactorization
  exact ⟨e, rfl, rfl⟩

/-- Two lines from `v` that meet only at `v` form a line between their other ends. -/
theorem IsLineWithEnds.union [T2Space S] {L₁ L₂ : Set S} {v p q : S} (h₁ : IsLineWithEnds L₁ v p)
    (h₂ : IsLineWithEnds L₂ v q) (h : L₁ ∩ L₂ = {v}) : IsLineWithEnds (L₁ ∪ L₂) p q := by
  obtain ⟨f₁, hf₁0, hf₁1⟩ := h₁
  obtain ⟨f₂, hf₂0, hf₂1⟩ := h₂
  let c₁ : Path p v :=
    ⟨⟨fun t => (f₁ (σ t)).1, by fun_prop⟩, by simpa using hf₁1, by simpa using hf₁0⟩
  let c₂ : Path v q := ⟨⟨fun t => (f₂ t).1, by fun_prop⟩, hf₂0, hf₂1⟩
  have hc₁ : Function.Injective c₁ := fun x y hxy => by
    have := f₁.injective (Subtype.ext hxy)
    simpa using this
  have hc₂ : Function.Injective c₂ := fun x y hxy => f₂.injective (Subtype.ext hxy)
  have hr₁ : range c₁ = L₁ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f₁ (σ t)).2
    · intro hx
      obtain ⟨t, ht⟩ := f₁.surjective ⟨x, hx⟩
      exact ⟨σ t, by simp [c₁, ht]⟩
  have hr₂ : range c₂ = L₂ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f₂ t).2
    · intro hx
      obtain ⟨t, ht⟩ := f₂.surjective ⟨x, hx⟩
      exact ⟨t, by simp [c₂, ht]⟩
  have hinj : Function.Injective (c₁.trans c₂) := by
    have hcross : ∀ a b : I, c₁ a = c₂ b → a = 1 ∧ b = 0 := by
      intro a b hab
      have hv : c₁ a ∈ L₁ ∩ L₂ := ⟨hr₁ ▸ mem_range_self a, hab ▸ hr₂ ▸ mem_range_self b⟩
      rw [h] at hv
      have h₁ : c₁ a = c₁ 1 := by simpa using hv
      have h₂ : c₂ b = c₂ 0 := by rw [← hab, h₁]; simp
      exact ⟨hc₁ h₁, hc₂ h₂⟩
    intro x y hxy
    simp only [Path.trans_apply] at hxy
    split_ifs at hxy with h₁ h₂ h₂
    · have := hc₁ hxy
      have := congrArg Subtype.val this
      simp only at this
      exact Subtype.ext (by linarith)
    · obtain ⟨h₃, h₄⟩ := hcross _ _ hxy
      have := congrArg Subtype.val h₃
      have h₅ := congrArg Subtype.val h₄
      simp only [Icc.coe_one, Icc.coe_zero] at this h₅
      exact Subtype.ext (by linarith)
    · obtain ⟨h₃, h₄⟩ := hcross _ _ hxy.symm
      have := congrArg Subtype.val h₃
      have h₅ := congrArg Subtype.val h₄
      simp only [Icc.coe_one, Icc.coe_zero] at this h₅
      exact Subtype.ext (by linarith)
    · have := hc₂ hxy
      have := congrArg Subtype.val this
      simp only at this
      exact Subtype.ext (by linarith)
  have := isLineWithEnds_range (c₁.trans c₂).toContinuousMap hinj
  have hrange : range (c₁.trans c₂).toContinuousMap = L₁ ∪ L₂ := by
    change range (c₁.trans c₂) = _
    rw [Path.trans_range, hr₁, hr₂]
  rw [hrange] at this
  simpa using this

/-- A line minus one end is preconnected. -/
theorem IsLineWithEnds.isPreconnected_sdiff {L : Set S} {v p : S} (h : IsLineWithEnds L v p) :
    IsPreconnected (L \ {v}) := by
  obtain ⟨f, hf0, hf1⟩ := h
  have hEq : L \ {v} = (fun t => (f t).1) '' Ioc (0 : I) 1 := by
    ext x
    constructor
    · rintro ⟨hx, hxv⟩
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hx⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hxv (by rw [← hf0, ht]; rfl)
      exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0, le_top⟩, by simp [ht]⟩
    · rintro ⟨t, ⟨h0, -⟩, rfl⟩
      refine ⟨(f t).2, fun hv => ?_⟩
      have : f t = f 0 := Subtype.ext (hv.trans hf0.symm)
      exact h0.ne (f.injective this).symm
  rw [hEq]
  exact (isPreconnected_Ioc).image _ (by fun_prop)

/-- The closure of a line minus one end contains that end. -/
theorem IsLineWithEnds.mem_closure_sdiff {L : Set S} {v p : S} (h : IsLineWithEnds L v p) :
    v ∈ closure (L \ {v}) := by
  obtain ⟨f, hf0, hf1⟩ := h
  have h1 : (0 : I) ∈ closure (Ioc (0 : I) 1) := by
    rw [closure_Ioc (zero_ne_one)]
    simp
  have hc : Continuous fun t => (f t).1 := by fun_prop
  have h2 := map_mem_closure hc h1 (t := L \ {v}) (by
    rintro t ⟨h0, -⟩
    refine ⟨(f t).2, fun hv => ?_⟩
    have : f t = f 0 := Subtype.ext (hv.trans hf0.symm)
    exact h0.ne (f.injective this).symm)
  rwa [hf0] at h2

/-- A component of an `O`-arc minus two points has both points in its closure. -/
theorem mem_closure_of_mem_componentsIn {F A : Set S} (hF : IsOArc F) {x y : S} (hx : x ∈ F)
    (hy : y ∈ F) (hxy : x ≠ y) (hA : A ∈ componentsIn (F \ {x, y})) : x ∈ closure A := by
  obtain ⟨φ⟩ := hF
  obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
  have hab : a ≠ b := by
    rintro rfl
    exact hxy (congrArg Subtype.val (ha.symm.trans hb))
  let ι : Circle → S := fun w => (φ w).1
  have hι : Continuous ι := by fun_prop
  have hιinj : Function.Injective ι := fun u w h => φ.injective (Subtype.ext h)
  have hιa : ι a = x := by simp [ι, ha]
  have hιb : ι b = y := by simp [ι, hb]
  -- each of the two open arcs is sent into the complement of the two points
  have hsub : ∀ c d : Circle, c ≠ d → (c = a ∧ d = b ∨ c = b ∧ d = a) →
      ι '' circleOpenArc c d ⊆ F \ {x, y} := by
    rintro c d hcd hor _ ⟨w, hw, rfl⟩
    refine ⟨(φ w).2, ?_⟩
    have h₁ : w ∈ ({a, b}ᶜ : Set Circle) := by
      rw [compl_pair_eq_union_circleOpenArc hab]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hw
      · exact Or.inr hw
    rintro (h | h)
    · exact h₁ (Or.inl (hιinj (h.trans hιa.symm)))
    · exact h₁ (Or.inr (hιinj (h.trans hιb.symm)))
  have hconn : ∀ c d : Circle, IsPreconnected (ι '' circleOpenArc c d) := fun c d =>
    (isPathConnected_circleOpenArc c d).isConnected.isPreconnected.image _ hι.continuousOn
  have hclos : ∀ c d : Circle, c ≠ d → ι c ∈ closure (ι '' circleOpenArc c d) ∧
      ι d ∈ closure (ι '' circleOpenArc c d) := by
    intro c d hcd
    have h0 : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
      rw [closure_Ioo zero_ne_one]
      simp
    have h1 : (1 : I) ∈ closure (Ioo (0 : I) 1) := by
      rw [closure_Ioo zero_ne_one]
      simp
    have hc : Continuous fun t => ι (Circle.path c d t) := by fun_prop
    have m0 := map_mem_closure hc h0 (t := ι '' circleOpenArc c d) fun t ht =>
      mem_image_of_mem _ (mem_image_of_mem _ ht)
    have m1 := map_mem_closure hc h1 (t := ι '' circleOpenArc c d) fun t ht =>
      mem_image_of_mem _ (mem_image_of_mem _ ht)
    simpa using And.intro m0 m1
  obtain ⟨z, hz, rfl⟩ := hA
  have hz' : (⟨z, hz.1⟩ : F) = φ (φ.symm ⟨z, hz.1⟩) := by simp
  have hzι : z = ι (φ.symm ⟨z, hz.1⟩) := by simp [ι]
  set w := φ.symm ⟨z, hz.1⟩ with hw
  have hwc : w ∈ ({a, b}ᶜ : Set Circle) := by
    rintro (h | h)
    · exact hz.2 (Or.inl (by rw [hzι, h]; exact hιa))
    · exact hz.2 (Or.inr (by rw [hzι, h]; exact hιb))
  rw [compl_pair_eq_union_circleOpenArc hab] at hwc
  rcases hwc with hwc | hwc
  · have hs := (hconn a b).subset_connectedComponentIn (x := z) ⟨w, hwc, hzι.symm⟩
      (hsub a b hab (Or.inl ⟨rfl, rfl⟩))
    exact closure_mono hs (hιa ▸ (hclos a b hab).1)
  · have hs := (hconn b a).subset_connectedComponentIn (x := z) ⟨w, hwc, hzι.symm⟩
      (hsub b a hab.symm (Or.inr ⟨rfl, rfl⟩))
    exact closure_mono hs (hιa ▸ (hclos b a hab.symm).2)

/-! ## Splitting a sector -/

/-- A closed disc contains its boundary. -/
theorem discBd_subset (Δ : Set S) : discBd Δ ⊆ Δ := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

/-- Components are disjoint, or equal. -/
private theorem disjoint_of_mem_componentsIn {T A B : Set S} (hA : A ∈ componentsIn T)
    (hB : B ∈ componentsIn T) (h : A ≠ B) : Disjoint A B := by
  obtain ⟨x, hx, rfl⟩ := hA
  obtain ⟨y, hy, rfl⟩ := hB
  refine Set.disjoint_left.mpr fun z hz hz' => h ?_
  rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']

/-- A nonempty preconnected subset of `T` lies in a component of `T`. -/
private theorem exists_component_superset {T X : Set S} (hX : IsPreconnected X) (hne : X.Nonempty)
    (hsub : X ⊆ T) : ∃ A ∈ componentsIn T, X ⊆ A := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, ⟨x, hsub hx, rfl⟩, hX.subset_connectedComponentIn hx hsub⟩

/-- The sets of `componentsIn T` lie in `T`. -/
private theorem subset_of_mem_componentsIn {T A : Set S} (hA : A ∈ componentsIn T) : A ⊆ T := by
  obtain ⟨x, -, rfl⟩ := hA
  exact connectedComponentIn_subset _ _

/-- The conclusion of `split_sector`, with the two sides named. -/
private theorem split_sector_aux {Q Jk Jl Jc B A₁ A₂ Δ₁ Δ₂ : Set S} {v p : S}
    (hdisj : Disjoint A₁ A₂) (hunion : discBd Q \ {v, p} ⊆ A₁ ∪ A₂)
    (hA₁ : A₁ ⊆ discBd Q \ {v, p}) (h₁ : discBd Δ₁ = A₁ ∪ Jc) (h₂ : discBd Δ₂ = A₂ ∪ Jc)
    (hΔ : Δ₁ ∩ Δ₂ = Jc) (hv : v ∈ Jc) (hp : p ∈ Jc)
    (hbd : discBd Q = Jk ∪ Jl ∪ B) (hkA : Jk \ {v} ⊆ A₁) (hlA : Jl \ {v} ⊆ A₂)
    (hcl : Jc ∩ Jl = {v}) (hvk : v ∈ Jk) :
    (∃ B' ⊆ B, discBd Δ₁ = Jk ∪ Jc ∪ B') ∧ Δ₁ ∩ discBd Q ⊆ discBd Δ₁ ∧ Jl ∩ Δ₁ ⊆ {v} := by
  have hA₂Δ : A₂ ⊆ Δ₂ := fun x hx => discBd_subset _ (h₂ ▸ Or.inl hx)
  have hnot : ∀ x ∈ Jl, x ∈ Δ₁ → x = v := by
    intro x hx hxΔ
    by_cases hxv : x = v
    · exact hxv
    · have hx₂ : x ∈ Δ₁ ∩ Δ₂ := ⟨hxΔ, hA₂Δ (hlA ⟨hx, hxv⟩)⟩
      rw [hΔ] at hx₂
      have : x ∈ Jc ∩ Jl := ⟨hx₂, hx⟩
      rw [hcl] at this
      exact this
  refine ⟨⟨A₁ ∩ B, inter_subset_right, ?_⟩, ?_, fun x hx => hnot x hx.1 hx.2⟩
  · rw [h₁]
    ext x
    constructor
    · rintro (hx | hx)
      · have hxQ := (hA₁ hx).1
        rw [hbd] at hxQ
        rcases hxQ with (hxk | hxl) | hxB
        · exact Or.inl (Or.inl hxk)
        · have hxv : x ≠ v := fun h => (hA₁ hx).2 (Or.inl h)
          exact absurd (hlA ⟨hxl, hxv⟩) (Set.disjoint_left.mp hdisj hx)
        · exact Or.inr ⟨hx, hxB⟩
      · exact Or.inl (Or.inr hx)
    · rintro ((hx | hx) | hx)
      · by_cases hxv : x = v
        · exact Or.inr (hxv ▸ hv)
        · exact Or.inl (hkA ⟨hx, hxv⟩)
      · exact Or.inr hx
      · exact Or.inl hx.1
  · rintro x ⟨hxΔ, hxQ⟩
    rw [h₁]
    by_cases hxc : x ∈ ({v, p} : Set S)
    · rcases hxc with rfl | rfl
      · exact Or.inr hv
      · exact Or.inr hp
    · rcases hunion ⟨hxQ, hxc⟩ with hx | hx
      · exact Or.inl hx
      · have hx₂ : x ∈ Δ₁ ∩ Δ₂ := ⟨hxΔ, hA₂Δ hx⟩
        rw [hΔ] at hx₂
        exact Or.inr hx₂

/-- Split the sector `Q`, whose boundary consists of the lines `Jk`, `Jl` from `v` and a set `B` far
from `v`, along a new line `Jc` from `v`. The new sectors are `Δ₁`, between `Jk` and `Jc`, and `Δ₂`,
between `Jc` and `Jl`. -/
theorem split_sector {Q Jk Jl Jc B E : Set S}
    {v pk pl pc : S} (hQ : IsClosedDisc Q) (hk : IsLineWithEnds Jk v pk)
    (hl : IsLineWithEnds Jl v pl) (hc : IsLineWithEnds Jc v pc) (hkv : v ≠ pk) (hlv : v ≠ pl)
    (hcv : v ≠ pc) (hbd : discBd Q = Jk ∪ Jl ∪ B) (hBE : B ⊆ E) (hE : IsClosed E) (hvE : v ∉ E)
    (hcQ : Jc ⊆ Q) (hcbd : Jc ∩ discBd Q = {v, pc}) (hck : Jc ∩ Jk = {v}) (hcl : Jc ∩ Jl = {v}) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = Q ∧ Δ₁ ∩ Δ₂ = Jc ∧
      (∃ B' ⊆ B, discBd Δ₁ = Jk ∪ Jc ∪ B') ∧ (∃ B' ⊆ B, discBd Δ₂ = Jc ∪ Jl ∪ B') ∧
      Δ₁ ∩ discBd Q ⊆ discBd Δ₁ ∧ Δ₂ ∩ discBd Q ⊆ discBd Δ₂ ∧ Jl ∩ Δ₁ ⊆ {v} ∧ Jk ∩ Δ₂ ⊆ {v} := by
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hne, hcomp, hd₁, hd₂, hun, hint, hb₁, hb₂, -⟩ :=
    disc_iArc Q Jc v pc hQ hcQ hcv hc hcbd
  have hvmem : v ∈ Jc ∩ discBd Q := by rw [hcbd]; simp
  have hpmem : pc ∈ Jc ∩ discBd Q := by rw [hcbd]; simp
  have hvc : v ∈ Jc := hvmem.1
  have hpc : pc ∈ Jc := hpmem.1
  have hA₁m : A₁ ∈ componentsIn (discBd Q \ {v, pc}) := by rw [hcomp]; simp
  have hA₂m : A₂ ∈ componentsIn (discBd Q \ {v, pc}) := by rw [hcomp]; simp
  have hdisj := disjoint_of_mem_componentsIn hA₁m hA₂m hne
  have hunion : discBd Q \ {v, pc} ⊆ A₁ ∪ A₂ := by
    intro x hx
    have : connectedComponentIn (discBd Q \ {v, pc}) x ∈ componentsIn (discBd Q \ {v, pc}) :=
      ⟨x, hx, rfl⟩
    rw [hcomp] at this
    rcases this with h | h
    · exact Or.inl (h ▸ mem_connectedComponentIn hx)
    · exact Or.inr ((mem_singleton_iff.mp h) ▸ mem_connectedComponentIn hx)
  have hA₁s := subset_of_mem_componentsIn hA₁m
  have hA₂s := subset_of_mem_componentsIn hA₂m
  have hO : IsOArc (discBd Q) := hQ.isOArc_discBd
  -- A component that misses both lines lies in `E`, and then `v` is not in its closure.
  have hfar : ∀ A ∈ componentsIn (discBd Q \ {v, pc}), Disjoint A (Jk ∪ Jl) → False := by
    intro A hA hdis
    have hAE : A ⊆ E := by
      intro x hx
      have := (subset_of_mem_componentsIn hA hx).1
      rw [hbd] at this
      rcases this with h | h
      · exact absurd h (Set.disjoint_left.mp hdis hx)
      · exact hBE h
    have hcl' : v ∈ closure A :=
      mem_closure_of_mem_componentsIn hO hvmem.2 hpmem.2 hcv hA
    exact hvE (closure_minimal hAE hE hcl')
  -- Each line minus `v` lies in one of the components.
  have hin : ∀ J : Set S, ∀ p, IsLineWithEnds J v p → v ≠ p → J ⊆ discBd Q → Jc ∩ J = {v} →
      (J \ {v} ⊆ A₁ ∨ J \ {v} ⊆ A₂) := by
    intro J p hJ hvp hJQ hcJ
    have hpJ : p ∈ J := by
      obtain ⟨f, -, hf⟩ := hJ
      exact hf ▸ (f 1).2
    have hsub : J \ {v} ⊆ discBd Q \ {v, pc} := by
      rintro x ⟨hx, hxv⟩
      refine ⟨hJQ hx, ?_⟩
      rintro (h | h)
      · exact hxv h
      · have hxpc : x = pc := h
        have : x ∈ Jc ∩ J := ⟨hxpc ▸ hpc, hx⟩
        rw [hcJ] at this
        exact hxv this
    obtain ⟨A, hA, hsA⟩ := exists_component_superset (IsLineWithEnds.isPreconnected_sdiff hJ)
      ⟨p, hpJ, fun h => hvp (mem_singleton_iff.mp h).symm⟩ hsub
    rw [hcomp] at hA
    rcases hA with rfl | hA
    · exact Or.inl hsA
    · exact Or.inr ((mem_singleton_iff.mp hA) ▸ hsA)
  have hkQ : Jk ⊆ discBd Q := fun x hx => hbd ▸ Or.inl (Or.inl hx)
  have hlQ : Jl ⊆ discBd Q := fun x hx => hbd ▸ Or.inl (Or.inr hx)
  have hvk : v ∈ Jk := by obtain ⟨f, hf, -⟩ := hk; exact hf ▸ (f 0).2
  have hvl : v ∈ Jl := by obtain ⟨f, hf, -⟩ := hl; exact hf ▸ (f 0).2
  have hsamecase : ∀ A' ∈ componentsIn (discBd Q \ {v, pc}), Disjoint A' (Jk \ {v}) →
      Disjoint A' (Jl \ {v}) → False := by
    intro A' hA' h₁ h₂
    refine hfar A' hA' (Set.disjoint_left.mpr ?_)
    rintro x hx (hxk | hxl)
    · have hxv : x ≠ v := fun h => (subset_of_mem_componentsIn hA' hx).2 (Or.inl h)
      exact Set.disjoint_left.mp h₁ hx ⟨hxk, hxv⟩
    · have hxv : x ≠ v := fun h => (subset_of_mem_componentsIn hA' hx).2 (Or.inl h)
      exact Set.disjoint_left.mp h₂ hx ⟨hxl, hxv⟩
  have hpair : (Jk \ {v} ⊆ A₁ ∧ Jl \ {v} ⊆ A₂) ∨ (Jk \ {v} ⊆ A₂ ∧ Jl \ {v} ⊆ A₁) := by
    rcases hin Jk pk hk hkv hkQ hck with h₁ | h₁ <;> rcases hin Jl pl hl hlv hlQ hcl with h₂ | h₂
    · exact absurd (hsamecase A₂ hA₂m (hdisj.symm.mono_right h₁) (hdisj.symm.mono_right h₂)) id
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact absurd (hsamecase A₁ hA₁m (hdisj.mono_right h₁) (hdisj.mono_right h₂)) id
  have hun' : A₂ ∪ A₁ = A₁ ∪ A₂ := union_comm _ _
  have hclk : Jc ∩ Jk = {v} := hck
  have hint' : Δ₂ ∩ Δ₁ = Jc := by rw [inter_comm, hint]
  have comm : ∀ {X Y Z : Set S}, Y ∪ X ∪ Z = X ∪ Y ∪ Z := fun {X Y Z} => by rw [union_comm Y X]
  rcases hpair with ⟨hkA, hlA⟩ | ⟨hkA, hlA⟩
  · obtain ⟨c₁, c₂, c₃⟩ := split_sector_aux hdisj hunion hA₁s hb₁ hb₂ hint hvc hpc hbd
      hkA hlA hcl hvk
    obtain ⟨c₄, c₅, c₆⟩ := split_sector_aux hdisj.symm (by rwa [hun']) hA₂s hb₂ hb₁ hint' hvc hpc
      (hbd.trans comm.symm) hlA hkA hck hvl
    obtain ⟨B₁, hB₁, h₁⟩ := c₁
    obtain ⟨B₂, hB₂, h₂⟩ := c₄
    refine ⟨Δ₁, Δ₂, hd₁, hd₂, hun, hint, ⟨B₁, hB₁, h₁⟩, ⟨B₂, hB₂, ?_⟩, c₂, c₅, c₃, c₆⟩
    rw [h₂, union_comm Jl Jc]
  · -- The two discs are exchanged.
    obtain ⟨c₁, c₂, c₃⟩ := split_sector_aux hdisj.symm (by rwa [hun']) hA₂s hb₂ hb₁ hint' hvc hpc
      hbd hkA hlA hcl hvk
    obtain ⟨c₄, c₅, c₆⟩ := split_sector_aux hdisj hunion hA₁s hb₁ hb₂ hint hvc hpc
      (hbd.trans comm.symm) hlA hkA hck hvl
    obtain ⟨B₁, hB₁, h₁⟩ := c₁
    obtain ⟨B₂, hB₂, h₂⟩ := c₄
    refine ⟨Δ₂, Δ₁, hd₂, hd₁, by rw [union_comm, hun], hint', ⟨B₁, hB₁, h₁⟩,
      ⟨B₂, hB₂, ?_⟩, c₂, c₅, c₃, c₆⟩
    rw [h₂, union_comm Jl Jc]

end Lines

/-! ## The sectors -/

section Fan

variable {ι : Type*} [DecidableEq ι]

/-- The sectors `Q k` of the closed disc `D` around `v`, for the lines `J i`, `i ∈ s`. The sector
`Q k` lies between the line `J k` and the next line `J (next k)`. The conditions are those that
adding a line needs. -/
structure FanInv (D : Set S) (J : ι → Set S) (v : S) (s : Finset ι) (next : ι → ι)
    (Q : ι → Set S) : Prop where
  next_mem : ∀ k ∈ s, next k ∈ s
  next_ne : ∀ k ∈ s, next k ≠ k
  next_inj : ∀ k ∈ s, ∀ l ∈ s, next k = next l → k = l
  disc : ∀ k ∈ s, IsClosedDisc (Q k)
  bd : ∀ k ∈ s, ∃ B ⊆ discBd D, discBd (Q k) = J k ∪ J (next k) ∪ B
  cover : ⋃ k ∈ s, Q k = D
  inter : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Q k ∩ Q l ⊆ ⋃ i ∈ s, J i
  edge : ∀ k ∈ s, Q k ∩ discBd D ⊆ discBd (Q k)
  off : ∀ k ∈ s, ∀ i ∈ s, i ≠ k → i ≠ next k → J i ∩ Q k ⊆ {v} ∪ discBd D
  reach : ∀ a ∈ s, ∀ b ∈ s, Relation.ReflTransGen (fun x y => y = next x) a b

variable [T2Space S] {D : Set S} {J : ι → Set S} {v : S} {p : ι → S}

/-- The two sectors of two lines. -/
theorem fanInv_pair (hD : IsClosedDisc D)
    (hline : ∀ i, IsLineWithEnds (J i) v (p i)) (hsub : ∀ i, J i ⊆ D)
    (hbd : ∀ i, J i ∩ discBd D = {p i}) (hJJ : ∀ i j, i ≠ j → J i ∩ J j = {v})
    (hne : ∀ i, v ≠ p i) {a b : ι} (hab : a ≠ b) :
    ∃ next Q, FanInv D J v {a, b} next Q := by
  have hF : IsLineWithEnds (J a ∪ J b) (p a) (p b) := IsLineWithEnds.union (hline a) (hline b)
    (hJJ a b hab)
  have hpp : p a ≠ p b := by
    intro h
    have hpa : p a ∈ J a := by
      have : p a ∈ J a ∩ discBd D := by rw [hbd]; simp
      exact this.1
    have hpb : p a ∈ J b := by
      have : p b ∈ J b ∩ discBd D := by rw [hbd]; simp
      exact h ▸ this.1
    have : p a ∈ J a ∩ J b := ⟨hpa, hpb⟩
    rw [hJJ a b hab] at this
    exact hne a this.symm
  have hcap : (J a ∪ J b) ∩ discBd D = {p a, p b} := by
    rw [union_inter_distrib_right, hbd, hbd]
    rfl
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hneA, hcomp, hd₁, hd₂, hun, hint, hb₁, hb₂, -⟩ :=
    disc_iArc D (J a ∪ J b) (p a) (p b) hD (union_subset (hsub a) (hsub b)) hpp hF hcap
  have hA₁m : A₁ ∈ componentsIn (discBd D \ {p a, p b}) := by rw [hcomp]; simp
  have hA₂m : A₂ ∈ componentsIn (discBd D \ {p a, p b}) := by rw [hcomp]; simp
  have hA₁s := subset_of_mem_componentsIn hA₁m
  have hA₂s := subset_of_mem_componentsIn hA₂m
  have hunion : discBd D \ {p a, p b} ⊆ A₁ ∪ A₂ := by
    intro x hx
    have : connectedComponentIn (discBd D \ {p a, p b}) x ∈ componentsIn (discBd D \ {p a, p b}) :=
      ⟨x, hx, rfl⟩
    rw [hcomp] at this
    rcases this with h | h
    · exact Or.inl (h ▸ mem_connectedComponentIn hx)
    · exact Or.inr ((mem_singleton_iff.mp h) ▸ mem_connectedComponentIn hx)
  have hbaF : ∀ x ∈ discBd D, x ∈ J a ∪ J b ∨ x ∈ A₁ ∨ x ∈ A₂ := by
    intro x hx
    by_cases h : x ∈ ({p a, p b} : Set S)
    · left
      rw [← hcap] at h
      exact h.1
    · exact Or.inr (hunion ⟨hx, h⟩)
  have hA₁Δ : A₁ ⊆ Δ₁ := fun x hx => discBd_subset _ (hb₁ ▸ Or.inl hx)
  have hA₂Δ : A₂ ⊆ Δ₂ := fun x hx => discBd_subset _ (hb₂ ▸ Or.inl hx)
  let next : ι → ι := fun k => if k = a then b else a
  let Q : ι → Set S := fun k => if k = a then Δ₁ else Δ₂
  have hna : next a = b := by simp [next]
  have hnb : next b = a := by simp [next, hab.symm]
  have hQa : Q a = Δ₁ := by simp [Q]
  have hQb : Q b = Δ₂ := by simp [Q, hab.symm]
  have hmem : ∀ k ∈ ({a, b} : Finset ι), k = a ∨ k = b := by simp
  refine ⟨next, Q, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk
    rcases hmem k hk with rfl | rfl
    · simp [hna]
    · simp [hnb]
  · intro k hk
    rcases hmem k hk with rfl | rfl
    · rw [hna]; exact hab.symm
    · rw [hnb]; exact hab
  · intro k hk l hl h
    rcases hmem k hk with rfl | rfl <;> rcases hmem l hl with rfl | rfl
    · rfl
    · rw [hna, hnb] at h; exact h.symm ▸ rfl
    · rw [hna, hnb] at h; exact h.symm ▸ rfl
    · rfl
  · intro k hk
    rcases hmem k hk with rfl | rfl
    · rwa [hQa]
    · rwa [hQb]
  · intro k hk
    rcases hmem k hk with rfl | rfl
    · exact ⟨A₁, fun x hx => (hA₁s hx).1, by rw [hna, hQa, hb₁, union_comm]⟩
    · refine ⟨A₂, fun x hx => (hA₂s hx).1, ?_⟩
      rw [hnb, hQb, hb₂]
      ext x
      simp only [mem_union]
      tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left,
      hQa, hQb, hun]
  · intro k hk l hl h
    rcases hmem k hk with rfl | rfl <;> rcases hmem l hl with rfl | rfl
    · exact absurd rfl h
    · rw [hQa, hQb, hint]
      rintro x (hx | hx)
      · exact mem_iUnion₂.mpr ⟨k, by simp, hx⟩
      · exact mem_iUnion₂.mpr ⟨l, by simp, hx⟩
    · rw [hQa, hQb, inter_comm, hint]
      rintro x (hx | hx)
      · exact mem_iUnion₂.mpr ⟨l, by simp, hx⟩
      · exact mem_iUnion₂.mpr ⟨k, by simp, hx⟩
    · exact absurd rfl h
  · intro k hk
    rintro x ⟨hxQ, hxD⟩
    rcases hmem k hk with rfl | rfl
    · rw [hQa] at hxQ ⊢
      rw [hb₁]
      rcases hbaF x hxD with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · have : x ∈ Δ₁ ∩ Δ₂ := ⟨hxQ, hA₂Δ h⟩
        rw [hint] at this
        exact Or.inr this
    · rw [hQb] at hxQ ⊢
      rw [hb₂]
      rcases hbaF x hxD with h | h | h
      · exact Or.inr h
      · have : x ∈ Δ₁ ∩ Δ₂ := ⟨hA₁Δ h, hxQ⟩
        rw [hint] at this
        exact Or.inr this
      · exact Or.inl h
  · intro k hk i hi h₁ h₂
    rcases hmem k hk with rfl | rfl <;> rcases hmem i hi with rfl | rfl
    · exact absurd rfl h₁
    · exact absurd hna.symm h₂
    · exact absurd hnb.symm h₂
    · exact absurd rfl h₁
  · intro x hx y hy
    have hstep : Relation.ReflTransGen (fun x y => y = next x) a b :=
      Relation.ReflTransGen.single hna.symm
    have hstep' : Relation.ReflTransGen (fun x y => y = next x) b a :=
      Relation.ReflTransGen.single hnb.symm
    rcases hmem x hx with rfl | rfl <;> rcases hmem y hy with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hstep
    · exact hstep'
    · exact Relation.ReflTransGen.refl

omit [DecidableEq ι] in
private theorem exists_sector_containing_line
    (hline : ∀ i, IsLineWithEnds (J i) v (p i)) (hsub : ∀ i, J i ⊆ D)
    (hbd : ∀ i, J i ∩ discBd D = {p i}) (hJJ : ∀ i j, i ≠ j → J i ∩ J j = {v})
    (hne : ∀ i, v ≠ p i) {s : Finset ι} {next : ι → ι} {Q : ι → Set S}
    (h : FanInv D J v s next Q) {c : ι} (hc : c ∉ s) :
    ∃ k ∈ s, J c ⊆ Q k ∧ J c ∩ discBd (Q k) = {v, p c} := by
  classical
  have hpc : p c ∈ J c ∩ discBd D := by rw [hbd]; simp
  have hvJ : ∀ i, v ∈ J i := fun i => by obtain ⟨f, hf, -⟩ := hline i; exact hf ▸ (f 0).2
  have hcJ : ∀ i ∈ s, J c ∩ J i = {v} := fun i hi => hJJ c i fun h' => hc (h' ▸ hi)
  have hpcD : p c ∈ D := hsub c hpc.1
  rw [← h.cover] at hpcD
  obtain ⟨k, hk, hpck⟩ := mem_iUnion₂.mp hpcD
  have hTne : p c ∈ J c \ {v} := ⟨hpc.1, fun h' => hne c (mem_singleton_iff.mp h').symm⟩
  have hTconn := IsLineWithEnds.isPreconnected_sdiff (hline c)
  have hcQ' : J c \ {v} ⊆ Q k := by
    by_contra hnot
    obtain ⟨x, hx, hxk⟩ := not_subset.mp hnot
    have hBclosed : IsClosed (⋃ l ∈ s.erase k, Q l) :=
      (s.erase k).finite_toSet.isClosed_biUnion fun l hl =>
        (h.disc l (Finset.mem_of_mem_erase hl)).isClosed
    have hcover : J c \ {v} ⊆ Q k ∪ ⋃ l ∈ s.erase k, Q l := by
      intro y hy
      have hyD : y ∈ D := hsub c hy.1
      rw [← h.cover] at hyD
      obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.mp hyD
      by_cases hlk : l = k
      · exact Or.inl (hlk ▸ hyl)
      · exact Or.inr (mem_iUnion₂.mpr ⟨l, Finset.mem_erase.mpr ⟨hlk, hl⟩, hyl⟩)
    have hxB : x ∈ ⋃ l ∈ s.erase k, Q l := (hcover hx).resolve_left hxk
    obtain ⟨y, hy, hyk, hyB⟩ := isPreconnected_closed_iff.mp hTconn _ _ (h.disc k hk).isClosed
      hBclosed hcover ⟨p c, hTne, hpck⟩ ⟨x, hx, hxB⟩
    obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.mp hyB
    have hle := Finset.mem_erase.mp hl
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (h.inter k hk l hle.2 (Ne.symm hle.1) ⟨hyk, hyl⟩)
    have : y ∈ J c ∩ J i := ⟨hy.1, hyi⟩
    rw [hcJ i hi] at this
    exact hy.2 this
  have hcQ : J c ⊆ Q k := by
    intro x hx
    by_cases hxv : x = v
    · have := closure_minimal hcQ' (h.disc k hk).isClosed
        (IsLineWithEnds.mem_closure_sdiff (hline c))
      exact hxv ▸ this
    · exact hcQ' ⟨hx, hxv⟩
  have hl := h.next_mem k hk
  obtain ⟨B, hBD, hbdQ⟩ := h.bd k hk
  have hkbd : J k ⊆ discBd (Q k) := fun x hx => hbdQ ▸ Or.inl (Or.inl hx)
  have hcbd : J c ∩ discBd (Q k) = {v, p c} := by
    ext x
    constructor
    · rintro ⟨hx, hxQ⟩
      rw [hbdQ] at hxQ
      rcases hxQ with (h₁ | h₁) | h₁
      · have : x ∈ J c ∩ J k := ⟨hx, h₁⟩
        rw [hcJ k hk] at this
        exact Or.inl this
      · have : x ∈ J c ∩ J (next k) := ⟨hx, h₁⟩
        rw [hcJ _ hl] at this
        exact Or.inl this
      · have : x ∈ J c ∩ discBd D := ⟨hx, hBD h₁⟩
        rw [hbd] at this
        exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨hvJ c, hkbd (hvJ k)⟩
      · exact ⟨hpc.1, h.edge k hk ⟨hpck, hpc.2⟩⟩
  exact ⟨k, hk, hcQ, hcbd⟩

/-- Add one line to the sectors: it lies in one sector, and it splits that sector into two. -/
theorem fanInv_insert (hD : IsClosedDisc D)
    (hline : ∀ i, IsLineWithEnds (J i) v (p i)) (hsub : ∀ i, J i ⊆ D)
    (hbd : ∀ i, J i ∩ discBd D = {p i}) (hJJ : ∀ i j, i ≠ j → J i ∩ J j = {v})
    (hne : ∀ i, v ≠ p i) (hvD : v ∉ discBd D) {s : Finset ι} {next : ι → ι} {Q : ι → Set S}
    (h : FanInv D J v s next Q) {c : ι} (hc : c ∉ s) :
    ∃ next' Q', FanInv D J v (insert c s) next' Q' := by
  have hEclosed : IsClosed (discBd D) := by
    obtain ⟨φ⟩ := hD.isOArc_discBd
    have : CompactSpace (discBd D) := φ.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  have hcJ : ∀ i ∈ s, J c ∩ J i = {v} := fun i hi => hJJ c i fun h' => hc (h' ▸ hi)
  obtain ⟨k, hk, hcQ, hcbd⟩ := exists_sector_containing_line hline hsub hbd hJJ hne h hc
  have hl := h.next_mem k hk
  obtain ⟨B, hBD, hbdQ⟩ := h.bd k hk
  obtain ⟨Δ₁, Δ₂, hd₁, hd₂, hun, hint, ⟨B₁, hB₁, hb₁⟩, ⟨B₂, hB₂, hb₂⟩, he₁, he₂, hoff₁, hoff₂⟩ :=
    split_sector (h.disc k hk) (hline k) (hline (next k)) (hline c) (hne k) (hne _) (hne c) hbdQ
      hBD hEclosed hvD hcQ hcbd (hcJ k hk) (hcJ _ hl)
  have hΔ₁ : Δ₁ ⊆ Q k := hun ▸ subset_union_left
  have hΔ₂ : Δ₂ ⊆ Q k := hun ▸ subset_union_right
  set l := next k with hldef
  have hcs : ∀ x ∈ s, x ≠ c := fun x hx hxc => hc (hxc ▸ hx)
  let next' : ι → ι := fun x => if x = c then l else if x = k then c else next x
  let Q' : ι → Set S := fun x => if x = c then Δ₂ else if x = k then Δ₁ else Q x
  have nc : next' c = l := by simp [next']
  have nk : next' k = c := by simp [next', hcs k hk]
  have nx : ∀ x ∈ s, x ≠ k → next' x = next x := fun x hx hxk => by simp [next', hcs x hx, hxk]
  have Qc : Q' c = Δ₂ := by simp [Q']
  have Qk : Q' k = Δ₁ := by simp [Q', hcs k hk]
  have Qx : ∀ x ∈ s, x ≠ k → Q' x = Q x := fun x hx hxk => by simp [Q', hcs x hx, hxk]
  have hmem : ∀ x ∈ insert c s, x = c ∨ x = k ∨ (x ∈ s ∧ x ≠ k) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · by_cases hxk : x = k
      · exact Or.inr (Or.inl hxk)
      · exact Or.inr (Or.inr ⟨hx, hxk⟩)
  have hkin : k ∈ insert c s := Finset.mem_insert_of_mem hk
  have hlin : l ∈ insert c s := Finset.mem_insert_of_mem hl
  have hcin : c ∈ insert c s := Finset.mem_insert_self c s
  have hnextne : ∀ x ∈ s, x ≠ k → next x ≠ l := fun x hx hxk he => hxk (h.next_inj x hx k hk he)
  have hQsub : ∀ x ∈ s, x ≠ k → Q' x ⊆ Q x := fun x hx hxk => (Qx x hx hxk).subset
  have hbig : (⋃ i ∈ s, J i) ⊆ ⋃ i ∈ insert c s, J i := by
    refine iUnion₂_subset fun i hi => ?_
    exact subset_biUnion_of_mem (u := J) (show i ∈ (↑(insert c s) : Set ι) by simp [hi])
  have hJcbig : J c ⊆ ⋃ i ∈ insert c s, J i :=
    subset_biUnion_of_mem (u := J) (show c ∈ (↑(insert c s) : Set ι) by simp)
  refine ⟨next', Q', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · rwa [nc]
    · rwa [nk]
    · rw [nx x hxs hxk]; exact Finset.mem_insert_of_mem (h.next_mem x hxs)
  · intro x hx
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · rw [nc]; exact hcs l hl
    · rw [nk]; exact (hcs x hk).symm
    · rw [nx x hxs hxk]; exact h.next_ne x hxs
  · intro x hx y hy he
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩ <;> rcases hmem y hy with rfl | rfl | ⟨hys, hyk⟩
    · rfl
    · rw [nc, nk] at he; exact absurd he (hcs l hl)
    · rw [nc, nx y hys hyk] at he; exact absurd he.symm (hnextne y hys hyk)
    · rw [nc, nk] at he; exact absurd he.symm (hcs l hl)
    · rfl
    · rw [nk, nx y hys hyk] at he
      exact absurd (he ▸ h.next_mem y hys) hc
    · rw [nc, nx x hxs hxk] at he; exact absurd he (hnextne x hxs hxk)
    · rw [nk, nx x hxs hxk] at he
      exact absurd (he.symm ▸ h.next_mem x hxs) hc
    · rw [nx x hxs hxk, nx y hys hyk] at he
      exact h.next_inj x hxs y hys he
  · intro x hx
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · rwa [Qc]
    · rwa [Qk]
    · rw [Qx x hxs hxk]; exact h.disc x hxs
  · intro x hx
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · exact ⟨B₂, hB₂.trans hBD, by rw [Qc, nc, hb₂]⟩
    · exact ⟨B₁, hB₁.trans hBD, by rw [Qk, nk, hb₁]⟩
    · rw [Qx x hxs hxk, nx x hxs hxk]; exact h.bd x hxs
  · ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      rw [← h.cover]
      rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
      · rw [Qc] at hyx; exact mem_iUnion₂.mpr ⟨k, hk, hΔ₂ hyx⟩
      · rw [Qk] at hyx; exact mem_iUnion₂.mpr ⟨x, hk, hΔ₁ hyx⟩
      · exact mem_iUnion₂.mpr ⟨x, hxs, hQsub x hxs hxk hyx⟩
    · intro hy
      rw [← h.cover] at hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      by_cases hxk : x = k
      · subst hxk
        rw [← hun] at hyx
        rcases hyx with hyx | hyx
        · exact mem_iUnion₂.mpr ⟨x, hkin, by rwa [Qk]⟩
        · exact mem_iUnion₂.mpr ⟨c, hcin, by rwa [Qc]⟩
      · exact mem_iUnion₂.mpr ⟨x, Finset.mem_insert_of_mem hx, by rwa [Qx x hx hxk]⟩
  · intro x hx y hy hxy
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩ <;> rcases hmem y hy with rfl | rfl | ⟨hys, hyk⟩
    · exact absurd rfl hxy
    · rw [Qc, Qk, inter_comm, hint]; exact hJcbig
    · rw [Qc, Qx y hys hyk]
      exact (inter_subset_inter_left _ hΔ₂).trans ((h.inter k hk y hys (Ne.symm hyk)).trans hbig)
    · rw [Qc, Qk, hint]; exact hJcbig
    · exact absurd rfl hxy
    · rw [Qk, Qx y hys hyk]
      exact (inter_subset_inter_left _ hΔ₁).trans ((h.inter x hk y hys (Ne.symm hyk)).trans hbig)
    · rw [Qc, Qx x hxs hxk]
      exact (inter_subset_inter_right _ hΔ₂).trans ((h.inter x hxs k hk hxk).trans hbig)
    · rw [Qk, Qx x hxs hxk]
      exact (inter_subset_inter_right _ hΔ₁).trans ((h.inter x hxs y hk hxk).trans hbig)
    · rw [Qx x hxs hxk, Qx y hys hyk]
      exact (h.inter x hxs y hys hxy).trans hbig
  · intro x hx
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · rw [Qc]
      rintro y ⟨hy, hyD⟩
      exact he₂ ⟨hy, h.edge k hk ⟨hΔ₂ hy, hyD⟩⟩
    · rw [Qk]
      rintro y ⟨hy, hyD⟩
      exact he₁ ⟨hy, h.edge x hk ⟨hΔ₁ hy, hyD⟩⟩
    · rw [Qx x hxs hxk]; exact h.edge x hxs
  · intro x hx i hi h₁ h₂
    rcases hmem x hx with rfl | rfl | ⟨hxs, hxk⟩
    · rw [nc] at h₂
      rw [Qc]
      have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left h₁
      by_cases hik : i = k
      · subst hik
        exact hoff₂.trans subset_union_left
      · exact (inter_subset_inter_right _ hΔ₂).trans (h.off k hk i his hik h₂)
    · rw [nk] at h₂
      rw [Qk]
      have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left h₂
      by_cases hil : i = l
      · subst hil
        exact hoff₁.trans subset_union_left
      · exact (inter_subset_inter_right _ hΔ₁).trans (h.off x hk i his h₁ hil)
    · rw [nx x hxs hxk] at h₂
      rw [Qx x hxs hxk]
      rcases Finset.mem_insert.mp hi with rfl | his
      · rintro y ⟨hyc, hyx⟩
        obtain ⟨m, hm, hym⟩ := mem_iUnion₂.mp (h.inter x hxs k hk hxk ⟨hyx, hcQ hyc⟩)
        have : y ∈ J i ∩ J m := ⟨hyc, hym⟩
        rw [hcJ m hm] at this
        exact Or.inl this
      · exact h.off x hxs i his h₁ h₂
  · have hold : ∀ a ∈ s, ∀ y, Relation.ReflTransGen (fun x y => y = next x) a y →
        y ∈ s ∧ Relation.ReflTransGen (fun x y => y = next' x) a y := by
      intro a ha y hy
      induction hy with
      | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
      | @tail x y _ hstep ih =>
        obtain ⟨hx, hr⟩ := ih
        subst hstep
        refine ⟨h.next_mem x hx, ?_⟩
        by_cases hxk : x = k
        · subst hxk
          exact (hr.tail nk.symm).tail nc.symm
        · exact hr.tail (nx x hx hxk).symm
    have hold' : ∀ a ∈ s, ∀ b ∈ s, Relation.ReflTransGen (fun x y => y = next' x) a b :=
      fun a ha b hb => (hold a ha b (h.reach a ha b hb)).2
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | has <;> rcases Finset.mem_insert.mp hb with rfl | hbs
    · exact Relation.ReflTransGen.refl
    · have hstep : Relation.ReflTransGen (fun x y => y = next' x) a l :=
        Relation.ReflTransGen.single nc.symm
      exact hstep.trans (hold' l hl b hbs)
    · exact (hold' a has k hk).tail nk.symm
    · exact hold' a has b hbs

omit [DecidableEq ι] in
/-- The sectors of finitely many lines, at least two, from an interior point of a closed disc. -/
theorem exists_fanInv (hD : IsClosedDisc D)
    (hline : ∀ i, IsLineWithEnds (J i) v (p i)) (hsub : ∀ i, J i ⊆ D)
    (hbd : ∀ i, J i ∩ discBd D = {p i}) (hJJ : ∀ i j, i ≠ j → J i ∩ J j = {v})
    (hne : ∀ i, v ≠ p i) (hvD : v ∉ discBd D) (s : Finset ι) (hs : 2 ≤ s.card) :
    ∃ next Q, FanInv D J v s next Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert c t hc ih =>
    rw [Finset.card_insert_of_notMem hc] at hs
    by_cases ht : 2 ≤ t.card
    · obtain ⟨next, Q, h⟩ := ih ht
      exact fanInv_insert hD hline hsub hbd hJJ hne hvD h hc
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
      exact fanInv_pair hD hline hsub hbd hJJ hne (fun h' => hc (by simp [h']))

omit [T2Space S] [DecidableEq ι] in
/-- Sets near `v` in the sectors. Each `P k` is a preconnected set in the sector `Q k`, off the
closed set `X` and off the boundary of the sector, and near `v` it is all of the interior of the
sector and has all of the boundary in its closure. -/
theorem exists_sector_sets {s : Finset ι} {next : ι → ι}
    {Q : ι → Set S} (h : FanInv D J v s next Q) {G : Set S} (hG : IsOpen G) (hvG : v ∈ G)
    (hvJ : ∀ i, v ∈ J i) {X : Set S} (hX : IsClosed X) (hvX : v ∉ X) :
    ∃ (P : ι → Set S) (W : Set S), IsOpen W ∧ v ∈ W ∧ W ⊆ G ∧
      (∀ k ∈ s, IsPreconnected (P k) ∧ P k ⊆ Q k ∧ Disjoint (P k) (discBd (Q k)) ∧
        Disjoint (P k) X ∧ (W ∩ Q k) \ discBd (Q k) ⊆ P k ∧
        W ∩ discBd (Q k) ⊆ closure (P k)) := by
  classical
  have hvbd : ∀ k ∈ s, v ∈ discBd (Q k) := by
    intro k hk
    obtain ⟨B, -, hb⟩ := h.bd k hk
    exact hb ▸ Or.inl (Or.inl (hvJ k))
  have hex : ∀ k : ι, ∃ A W : Set S, k ∈ s → IsOpen W ∧ v ∈ W ∧ IsPreconnected A ∧ A ⊆ Q k ∧
      Disjoint A (discBd (Q k)) ∧ Disjoint A X ∧ (W ∩ Q k) \ discBd (Q k) ⊆ A ∧
      W ∩ discBd (Q k) ⊆ closure A := by
    intro k
    by_cases hk : k ∈ s
    · obtain ⟨A, W, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ :=
        exists_half_nbhd (h.disc k hk) hX (hvbd k hk) hvX
      exact ⟨A, W, fun _ => ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩⟩
    · exact ⟨∅, ∅, fun h' => absurd h' hk⟩
  choose P W₀ hPW using hex
  refine ⟨P, G ∩ ⋂ k ∈ s, W₀ k, ?_, ?_, inter_subset_left, ?_⟩
  · exact hG.inter (s.finite_toSet.isOpen_biInter fun k hk => (hPW k hk).1)
  · exact ⟨hvG, mem_iInter₂.mpr fun k hk => (hPW k hk).2.1⟩
  · intro k hk
    obtain ⟨-, -, a₃, a₄, a₅, a₆, a₇, a₈⟩ := hPW k hk
    have hsubW : G ∩ ⋂ k ∈ s, W₀ k ⊆ W₀ k := fun x hx => mem_iInter₂.mp hx.2 k hk
    exact ⟨a₃, a₄, a₅, a₆, fun x hx => a₇ ⟨⟨hsubW hx.1.1, hx.1.2⟩, hx.2⟩,
      fun x hx => a₈ ⟨hsubW hx.1, hx.2⟩⟩

omit [T2Space S] [DecidableEq ι] in
/-- What the sets of `exists_sector_sets` give near `v`. Off the lines, a point of `W` lies in one
of
the sets `P k`. Moreover, a point of the line `J (next k)` near `v` has a neighbourhood that off the
lines lies in `P k` and `P (next k)`, and it is in the closure of both. -/
theorem sector_sets_props {s : Finset ι} {next : ι → ι} {Q : ι → Set S}
    (h : FanInv D J v s next Q) {P : ι → Set S} {W : Set S} (hW : IsOpen W)
    (hWD : W ⊆ D) (hWbd : Disjoint W (discBd D))
    (hclosed : ∀ k ∈ s, IsClosed (Q k))
    (hP : ∀ k ∈ s, (W ∩ Q k) \ discBd (Q k) ⊆ P k ∧ W ∩ discBd (Q k) ⊆ closure (P k)) :
    (W \ ⋃ i ∈ s, J i ⊆ ⋃ k ∈ s, P k) ∧
    ∀ k ∈ s, ∀ q ∈ W ∩ J (next k), q ≠ v → ∃ O, IsOpen O ∧ q ∈ O ∧
      O \ (⋃ i ∈ s, J i) ⊆ P k ∪ P (next k) ∧ q ∈ closure (P k) ∧ q ∈ closure (P (next k)) := by
  classical
  have hin : ∀ m ∈ s, ∀ x ∈ W, x ∈ Q m → x ∉ (⋃ i ∈ s, J i) → x ∈ P m := by
    intro m hm x hxW hxm hxJ
    refine (hP m hm).1 ⟨⟨hxW, hxm⟩, ?_⟩
    obtain ⟨B, hBD, hb⟩ := h.bd m hm
    rw [hb]
    rintro ((hx | hx) | hx)
    · exact hxJ (mem_iUnion₂.mpr ⟨m, hm, hx⟩)
    · exact hxJ (mem_iUnion₂.mpr ⟨_, h.next_mem m hm, hx⟩)
    · exact Set.disjoint_left.mp hWbd hxW (hBD hx)
  constructor
  · rintro x ⟨hxW, hxJ⟩
    have hxD := hWD hxW
    rw [← h.cover] at hxD
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hxD
    exact mem_iUnion₂.mpr ⟨m, hm, hin m hm x hxW hxm hxJ⟩
  · rintro k hk q ⟨hqW, hqJ⟩ hqv
    have hl := h.next_mem k hk
    obtain ⟨B₁, -, hb₁⟩ := h.bd k hk
    obtain ⟨B₂, -, hb₂⟩ := h.bd _ hl
    have hq₁ : q ∈ discBd (Q k) := hb₁ ▸ Or.inl (Or.inr hqJ)
    have hq₂ : q ∈ discBd (Q (next k)) := hb₂ ▸ Or.inl (Or.inl hqJ)
    -- Remove the other sectors.
    have hclosedU : IsClosed (⋃ m ∈ (s.erase k).erase (next k), Q m) :=
      ((s.erase k).erase (next k)).finite_toSet.isClosed_biUnion fun m hm =>
        hclosed m (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
    have hqU : q ∉ ⋃ m ∈ (s.erase k).erase (next k), Q m := by
      intro hq
      obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
      have hm₁ := Finset.mem_erase.mp hm
      have hm₂ := Finset.mem_erase.mp hm₁.2
      have hne : next k ≠ next m := fun he => hm₂.1 (h.next_inj k hk m hm₂.2 he).symm
      rcases h.off m hm₂.2 (next k) hl (Ne.symm hm₁.1) hne ⟨hqJ, hqm⟩ with hx | hx
      · exact hqv hx
      · exact Set.disjoint_left.mp hWbd hqW hx
    refine ⟨W \ ⋃ m ∈ (s.erase k).erase (next k), Q m, hW.sdiff hclosedU, ⟨hqW, hqU⟩, ?_,
      (hP k hk).2 ⟨hqW, hq₁⟩, (hP _ hl).2 ⟨hqW, hq₂⟩⟩
    rintro x ⟨⟨hxW, hxU⟩, hxJ⟩
    have hxD := hWD hxW
    rw [← h.cover] at hxD
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hxD
    by_cases hmk : m = k
    · exact Or.inl (hmk ▸ hin m hm x hxW hxm hxJ)
    · by_cases hml : m = next k
      · exact Or.inr (hml ▸ hin m hm x hxW hxm hxJ)
      · exact absurd (mem_iUnion₂.mpr ⟨m, Finset.mem_erase.mpr ⟨hml,
          Finset.mem_erase.mpr ⟨hmk, hm⟩⟩, hxm⟩) hxU

end Fan

end GraphMinor.GM11
