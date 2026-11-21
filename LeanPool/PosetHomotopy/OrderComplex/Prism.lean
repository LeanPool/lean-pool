/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Homotopy.Contractible

/-!
# The homotopy property of order complexes (roadmap 3.2, 3.3)

For monotone maps `f ≤ g : P →o Q` of preorders, the realizations of `orderComplexMap f` and
`orderComplexMap g` are homotopic (`homotopic_realizationMap_of_le`). This extends the
partially ordered case of D. Quillen, « Homotopy properties of the poset of nontrivial
p-subgroups of a group », Adv. Math. 28 (1978), 101–128, §1.3, to preorders. The homotopy is
the prism construction, written in barycentric coordinates: order the
vertices of the carrier of a point `x` increasingly (ties between equivalent elements of the
preorder are broken by a well-order, `Prec`), and read the weights of `x` as consecutive
intervals of `[0, 1]`. At time `t`, the part of each interval below `1 - t` is sent to the image
under `f` of its vertex, and the part above `1 - t` to its image under `g`
(`prismCoord`). The vertices receiving mass from `f` all lie below those receiving mass from
`g`, so the support is a chain of `Q`.

As a consequence, a preorder with an element `x₀` and a monotone `f` such that `x ≤ f x ≥ x₀`
for every `x` has a contractible realization (`contractibleSpace_of_conical`). This is the
preorder extension of the upward-cone case in Quillen 1978, §1.5.
-/

@[expose] public section

noncomputable section

open Topology unitInterval TauCeti TauCeti.SetLike AbstractSimplicialComplex

namespace LeanPool.PosetHomotopy

universe u v

section Prec

variable {P : Type u} [Preorder P]

/-- The strict order used to sort the vertices of a chain: the strict order of `P`, with ties
between equivalent elements broken by a well-order. -/
def Prec (a b : P) : Prop := a < b ∨ (a ≤ b ∧ b ≤ a ∧ WellOrderingRel a b)

theorem Prec.le {a b : P} (h : Prec a b) : a ≤ b := h.elim le_of_lt And.left

theorem prec_irrefl (a : P) : ¬ Prec a a := by
  rintro (h | ⟨-, -, h⟩)
  · exact lt_irrefl a h
  · exact irrefl_of WellOrderingRel a h

theorem Prec.trans {a b c : P} (h₁ : Prec a b) (h₂ : Prec b c) : Prec a c := by
  rcases h₁ with h₁ | ⟨h₁, h₁', w₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂', w₂⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₁.trans_le h₂)
  · exact Or.inl (h₁.trans_lt h₂)
  · exact Or.inr ⟨h₁.trans h₂, h₂'.trans h₁', trans_of WellOrderingRel w₁ w₂⟩

/-- Two comparable elements `a`, `b` with `¬ Prec b a` satisfy `a ≤ b`. -/
theorem le_of_not_prec {a b : P} (hab : a ≤ b ∨ b ≤ a) (h : ¬ Prec b a) : a ≤ b := by
  rcases hab with hab | hba
  · exact hab
  · by_contra hab
    exact h (Or.inl (lt_of_le_not_ge hba hab))

end Prec

section Coordinates

variable {P : Type u} [Preorder P]

open Classical in
/-- The weight of the vertices strictly before `v` in the support of `x`. -/
def cumul (x : P →₀ ℝ) (v : P) : ℝ := ∑ u ∈ x.support with Prec u v, x u

/-- The weight of `v` sent to the `f`-side at level `s`: the part of the interval of `v`
below `s`. -/
def lowWeight (s : ℝ) (x : P →₀ ℝ) (v : P) : ℝ := min (x v) (max 0 (s - cumul x v))

/-- `lowWeight` as a finitely supported function. -/
def lowPart (s : ℝ) (x : P →₀ ℝ) : P →₀ ℝ :=
  Finsupp.onFinset x.support (lowWeight s x) fun v hv => by
    rw [Finsupp.mem_support_iff]
    intro h
    apply hv
    simp [lowWeight, h]

@[simp]
theorem lowPart_apply (s : ℝ) (x : P →₀ ℝ) (v : P) : lowPart s x v = lowWeight s x v :=
  Finsupp.onFinset_apply

variable {x : P →₀ ℝ} (hx : ∀ v, 0 ≤ x v)
include hx

theorem lowWeight_nonneg (s : ℝ) (v : P) : 0 ≤ lowWeight s x v :=
  le_min (hx v) (le_max_left _ _)

omit hx in
theorem lowWeight_le (s : ℝ) (v : P) : lowWeight s x v ≤ x v := min_le_left _ _

theorem cumul_nonneg (v : P) : 0 ≤ cumul x v :=
  Finset.sum_nonneg fun u _ => hx u

omit hx in
theorem lt_of_lowWeight_pos {s : ℝ} {v : P} (h : 0 < lowWeight s x v) : cumul x v < s := by
  by_contra hs
  have : max 0 (s - cumul x v) = 0 := max_eq_left (by linarith)
  simp only [lowWeight, this] at h
  exact lt_irrefl _ (h.trans_le (min_le_right _ _))

omit hx in
theorem lt_of_lowWeight_lt {s : ℝ} {v : P} (h : lowWeight s x v < x v) :
    s < cumul x v + x v := by
  by_contra hs
  have : x v ≤ max 0 (s - cumul x v) := (by linarith : x v ≤ s - cumul x v).trans (le_max_right _ _)
  simp only [lowWeight, min_eq_left this] at h
  exact lt_irrefl _ h

theorem cumul_add_le {u v : P} (hu : u ∈ x.support) (huv : Prec u v) :
    cumul x u + x u ≤ cumul x v := by
  classical
  have hnot : u ∉ x.support.filter fun w => Prec w u := by simp [prec_irrefl]
  unfold cumul
  rw [add_comm, ← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => hx w
  intro w hw
  rw [Finset.mem_insert, Finset.mem_filter] at hw
  rw [Finset.mem_filter]
  rcases hw with rfl | ⟨hw, hwu⟩
  · exact ⟨hu, huv⟩
  · exact ⟨hw, hwu.trans huv⟩

/-- The vertices receiving mass on the `f`-side lie below those receiving mass on the `g`-side. -/
theorem le_of_lowWeight {s : ℝ} {a b : P} (hab : a ≤ b ∨ b ≤ a)
    (ha : 0 < lowWeight s x a) (hb : lowWeight s x b < x b) (hbs : b ∈ x.support) : a ≤ b := by
  refine le_of_not_prec hab fun hba => ?_
  have h₁ := lt_of_lowWeight_pos ha
  have h₂ := lt_of_lowWeight_lt hb
  have h₃ := cumul_add_le hx hbs hba
  linarith

theorem cumul_add_self_le_sum (v : P) : cumul x v + x v ≤ x.sum fun _ r => r := by
  classical
  by_cases hv : v ∈ x.support
  · have hnot : v ∉ x.support.filter fun w => Prec w v := by simp [prec_irrefl]
    unfold cumul
    rw [add_comm, ← Finset.sum_insert hnot, Finsupp.sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => hx w
    intro w hw
    rw [Finset.mem_insert, Finset.mem_filter] at hw
    rcases hw with rfl | ⟨hw, -⟩
    · exact hv
    · exact hw
  · rw [Finsupp.notMem_support_iff.1 hv, add_zero, Finsupp.sum, cumul]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun w _ _ => hx w

end Coordinates

section Finsupp

variable {α β : Type*}

theorem mapDomain_nonneg (f : α → β) {y : α →₀ ℝ} (hy : ∀ a, 0 ≤ y a) (b : β) :
    0 ≤ Finsupp.mapDomain f y b := by
  classical
  rw [Finsupp.mapDomain_apply]
  exact Finset.sum_nonneg fun a _ => by
    change 0 ≤ Finsupp.single (f a) (y a) b
    rw [Finsupp.single_apply]; split_ifs
    · exact hy a
    · exact le_rfl

theorem sum_mapDomain_id (f : α → β) (y : α →₀ ℝ) :
    (Finsupp.mapDomain f y).sum (fun _ r => r) = y.sum fun _ r => r :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

theorem mapDomain_apply_of_support_subset [DecidableEq β] (f : α → β) {y : α →₀ ℝ}
    {T : Finset α} (hy : y.support ⊆ T) (b : β) :
    Finsupp.mapDomain f y b = ∑ a ∈ T, if f a = b then y a else 0 := by
  rw [Finsupp.mapDomain_apply, Finsupp.sum_of_support_subset y hy]
  · simp [Finsupp.single_apply]
  · intro a _; simp

end Finsupp

section Prism

variable {P : Type u} {Q : Type v} [Preorder P]

/-- The barycentric coordinates of the prism homotopy at level `s = 1 - t`: the mass of each
vertex below level `s` goes to its image under `f`, the rest to its image under `g`. -/
def prismCoord (f g : P → Q) (s : ℝ) (x : P →₀ ℝ) : Q →₀ ℝ :=
  Finsupp.mapDomain f (lowPart s x) + Finsupp.mapDomain g (x - lowPart s x)

theorem lowPart_support_subset (s : ℝ) (x : P →₀ ℝ) : (lowPart s x).support ⊆ x.support :=
  Finsupp.support_onFinset_subset

theorem sub_lowPart_support_subset {x : P →₀ ℝ} (s : ℝ) :
    (x - lowPart s x).support ⊆ x.support := by
  intro v hv
  rw [Finsupp.mem_support_iff] at hv ⊢
  intro h
  apply hv
  simp [lowWeight, h]

theorem prismCoord_support_subset [DecidableEq Q] (f g : P → Q) (s : ℝ) (x : P →₀ ℝ) :
    (prismCoord f g s x).support ⊆ x.support.image f ∪ x.support.image g :=
  Finsupp.support_add.trans (Finset.union_subset_union
    (Finsupp.mapDomain_support.trans (Finset.image_subset_image (lowPart_support_subset s x)))
    (Finsupp.mapDomain_support.trans (Finset.image_subset_image (sub_lowPart_support_subset s))))

/-- The prism coordinates of a point of the realization of `orderComplex P` are a point of the
realization of `orderComplex Q`. -/
theorem prismCoord_mem [Preorder Q] {f g : P →o Q} (hfg : f ≤ g) (s : ℝ)
    (x : Realization (orderComplex P)) :
    prismCoord f g s x.1 ∈ (standardGeometricComplex (orderComplex Q)).space := by
  classical
  obtain ⟨hnn, hsum, hsupp⟩ := TauCeti.mem_standardGeometricComplex_space_iff.mp x.2
  have hlow := fun v => lowWeight_nonneg hnn s v
  have hlowle := fun v => lowWeight_le (x := x.1) s v
  have hsum' : (prismCoord f g s x.1).sum (fun _ r => r) = 1 := by
    rw [prismCoord, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      sum_mapDomain_id, sum_mapDomain_id,
      Finsupp.sum_sub_index (fun _ _ _ => rfl), add_sub_cancel, hsum]
  refine TauCeti.mem_standardGeometricComplex_space_iff.mpr ⟨fun w => ?_, hsum', ?_⟩
  · exact add_nonneg (mapDomain_nonneg f (fun v => by simpa using hlow v) w)
      (mapDomain_nonneg g (fun v => by simpa using sub_nonneg.2 (hlowle v)) w)
  · have hchain := (mem_orderComplex_iff'.mp hsupp).2
    refine mem_orderComplex_iff'.mpr ⟨?_, fun q₁ hq₁ q₂ hq₂ => ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [Finsupp.support_eq_empty.1 h, Finsupp.sum_zero_index] at hsum'
      exact zero_ne_one hsum'
    · have key : ∀ q ∈ (prismCoord f g s x.1).support,
          (∃ a ∈ x.1.support, 0 < lowWeight s x.1 a ∧ f a = q) ∨
            ∃ b ∈ x.1.support, lowWeight s x.1 b < x.1 b ∧ g b = q := by
        intro q hq
        rcases Finset.mem_union.1 (Finsupp.support_add hq) with hq | hq
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
          refine Or.inl ⟨a, lowPart_support_subset s _ ha,
            lt_of_le_of_ne (hlow a) (fun h => ?_), rfl⟩
          exact (Finsupp.mem_support_iff.1 ha) (by simpa using h.symm)
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
          refine Or.inr ⟨b, sub_lowPart_support_subset s hb,
            lt_of_le_of_ne (hlowle b) (fun h => ?_), rfl⟩
          exact (Finsupp.mem_support_iff.1 hb) (by simp [h])
      have cmp : ∀ a ∈ x.1.support, ∀ b ∈ x.1.support, a ≤ b ∨ b ≤ a :=
        fun a ha b hb => hchain a ha b hb
      rcases key q₁ hq₁ with ⟨a, ha, ha', rfl⟩ | ⟨b, hb, hb', rfl⟩ <;>
        rcases key q₂ hq₂ with ⟨a', ha₂, ha₂', rfl⟩ | ⟨b', hb₂, hb₂', rfl⟩
      · exact (cmp a ha a' ha₂).imp (fun h => f.monotone h) fun h => f.monotone h
      · exact Or.inl ((f.monotone (le_of_lowWeight hnn (cmp a ha b' hb₂) ha' hb₂' hb₂)).trans
          (hfg b'))
      · exact Or.inr ((f.monotone (le_of_lowWeight hnn (cmp a' ha₂ b hb) ha₂' hb' hb)).trans
          (hfg b))
      · exact (cmp b hb b' hb₂).imp (fun h => g.monotone h) fun h => g.monotone h

/-- The prism map at level `s`. -/
def prismMap [Preorder Q] {f g : P →o Q} (hfg : f ≤ g) (s : ℝ) (x : Realization (orderComplex P)) :
    Realization (orderComplex Q) :=
  ⟨prismCoord f g s x.1, prismCoord_mem hfg s x⟩

open Classical in
theorem cumul_eq_sum_of_support_subset {x : P →₀ ℝ} {T : Finset P} (hx : x.support ⊆ T)
    (v : P) : cumul x v = ∑ u ∈ T with Prec u v, x u := by
  classical
  refine Finset.sum_subset (Finset.filter_subset_filter _ hx) fun u hu hu' => ?_
  rw [Finset.mem_filter] at hu hu'
  by_contra h
  exact hu' ⟨Finsupp.mem_support_iff.2 h, hu.2⟩

/-- The prism coordinates are continuous on every closed simplex cylinder. -/
theorem continuous_prismCoord (f g : P → Q) (T : Finset P) :
    Continuous fun p : I × StandardSimplex T =>
      (prismCoord f g (1 - (p.1 : ℝ)) p.2.1 : Q → ℝ) := by
  classical
  have hx : ∀ a, Continuous fun p : I × StandardSimplex T => (p.2.1 : P →₀ ℝ) a := fun a =>
    (continuous_apply a).comp
      ((continuous_induced_dom (f := fun x : StandardSimplex T => (x.1 : P → ℝ))).comp
        continuous_snd)
  have hlow : ∀ a, Continuous fun p : I × StandardSimplex T =>
      lowWeight (1 - (p.1 : ℝ)) p.2.1 a := by
    intro a
    have hc : Continuous fun p : I × StandardSimplex T => cumul p.2.1 a := by
      have : (fun p : I × StandardSimplex T => cumul p.2.1 a) =
          fun p => ∑ u ∈ T with Prec u a, (p.2.1 : P →₀ ℝ) u :=
        funext fun p => cumul_eq_sum_of_support_subset (StandardSimplex.support_subset p.2) a
      rw [this]
      exact continuous_finsetSum _ fun u _ => hx u
    exact (hx a).min (continuous_const.max
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).sub hc))
  refine continuous_pi fun w => ?_
  have : (fun p : I × StandardSimplex T => (prismCoord f g (1 - (p.1 : ℝ)) p.2.1 : Q → ℝ) w) =
      fun p => (∑ a ∈ T, if f a = w then lowWeight (1 - (p.1 : ℝ)) p.2.1 a else 0) +
        ∑ a ∈ T, if g a = w then (p.2.1 : P →₀ ℝ) a - lowWeight (1 - (p.1 : ℝ)) p.2.1 a
          else 0 := by
    funext p
    have hT := StandardSimplex.support_subset p.2
    simp only [prismCoord, Finsupp.coe_add, Pi.add_apply,
      mapDomain_apply_of_support_subset f ((lowPart_support_subset _ _).trans hT),
      mapDomain_apply_of_support_subset g ((sub_lowPart_support_subset _).trans hT),
      lowPart_apply, Finsupp.coe_sub, Pi.sub_apply]
  rw [this]
  refine (continuous_finsetSum _ fun a _ => ?_).add (continuous_finsetSum _ fun a _ => ?_)
  · split_ifs
    · exact hlow a
    · exact continuous_const
  · split_ifs
    · exact (hx a).sub (hlow a)
    · exact continuous_const

end Prism

/-- A map into a realization whose values are supported in a fixed finite set of vertices is
continuous as soon as its barycentric coordinates are. -/
theorem continuous_of_coe {ι : Type*} {Z : Type*} [TopologicalSpace Z]
    {K : AbstractSimplicialComplex ι} {F : Z → Realization K} (V : Set ι) (hV : V.Finite)
    (hsupp : ∀ z, ((F z).1.support : Set ι) ⊆ V)
    (hc : Continuous fun z => ((F z).1 : ι → ℝ)) : Continuous F := by
  have he := isClosedEmbedding_realization_coe_restrict K
    (isCompact_setOf_support_subset K V hV)
  let F' : Z → {x : Realization K | (x.1.support : Set ι) ⊆ V} := fun z => ⟨F z, hsupp z⟩
  have : Continuous F' := he.isEmbedding.continuous_iff.2 hc
  exact continuous_subtype_val.comp this

section Homotopy

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

theorem lowPart_one {x : P →₀ ℝ} (hx : ∀ v, 0 ≤ x v) (h1 : (x.sum fun _ r => r) = 1) :
    lowPart 1 x = x := by
  ext v
  rw [lowPart_apply, lowWeight, min_eq_left]
  have := cumul_add_self_le_sum hx v
  exact (by linarith : x v ≤ 1 - cumul x v).trans (le_max_right _ _)

theorem lowPart_zero {x : P →₀ ℝ} (hx : ∀ v, 0 ≤ x v) : lowPart 0 x = 0 := by
  ext v
  rw [lowPart_apply, lowWeight, max_eq_left (by linarith [cumul_nonneg hx v]),
    min_eq_right (hx v), Finsupp.coe_zero, Pi.zero_apply]

variable [DecidableEq Q]

/-- **Roadmap 3.2.** The prism homotopy between the realizations of comparable monotone maps. -/
def prismHomotopy {f g : P →o Q} (hfg : f ≤ g) :
    (orderComplexMap f).realizationMap.Homotopy (orderComplexMap g).realizationMap where
  toFun p := prismMap hfg (1 - (p.1 : ℝ)) p.2
  continuous_toFun := by
    classical
    refine continuous_prod_iff_faceInclusion.mpr fun T => ?_
    refine continuous_of_coe (↑(T.1.image f ∪ T.1.image g)) (Finset.finite_toSet _)
      (fun p => ?_) ?_
    · have hT := StandardSimplex.support_subset p.2
      simp only [prismMap, faceInclusion_val]
      exact_mod_cast (prismCoord_support_subset f g _ _).trans
        (Finset.union_subset_union (Finset.image_subset_image hT) (Finset.image_subset_image hT))
    · simpa only [prismMap, faceInclusion_val] using continuous_prismCoord f g T.1
  map_zero_left x := by
    obtain ⟨hnn, hsum, -⟩ := TauCeti.mem_standardGeometricComplex_space_iff.mp x.2
    apply Subtype.ext
    simp only [Set.Icc.coe_zero, sub_zero, prismMap, prismCoord, lowPart_one hnn hsum, sub_self,
      Finsupp.mapDomain_zero, add_zero,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val, coe_orderComplexMap]
  map_one_left x := by
    obtain ⟨hnn, -, -⟩ := TauCeti.mem_standardGeometricComplex_space_iff.mp x.2
    apply Subtype.ext
    simp only [Set.Icc.coe_one, sub_self, prismMap, prismCoord, lowPart_zero hnn, sub_zero,
      Finsupp.mapDomain_zero, zero_add,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val, coe_orderComplexMap]

/-- **Roadmap 3.2.** Comparable monotone maps realize to homotopic maps. -/
theorem homotopic_realizationMap_of_le {f g : P →o Q} (h : f ≤ g) :
    (orderComplexMap f).realizationMap.Homotopic (orderComplexMap g).realizationMap :=
  ⟨prismHomotopy h⟩

end Homotopy

section Conical

variable {P : Type u} [Preorder P]

/-- The realization of a constant monotone map is constant at the vertex. -/
theorem realizationMap_const [DecidableEq P] (x₀ : P) :
    (orderComplexMap (OrderHom.const P x₀)).realizationMap =
      ContinuousMap.const _ (vertex (orderComplex P) x₀) := by
  ext x : 1
  obtain ⟨-, hsum, -⟩ := TauCeti.mem_standardGeometricComplex_space_iff.mp x.2
  apply Subtype.ext
  ext w
  simp only [PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val, coe_orderComplexMap,
    ContinuousMap.const_apply, vertex_val, Finsupp.mapDomain_apply, OrderHom.const_coe_coe,
    Function.const_apply]
  rw [Finsupp.single_apply]
  split_ifs with h
  · subst h
    simpa [Finsupp.sum] using hsum
  · simp [Finsupp.sum, h]

/-- **Roadmap 3.3.** The preorder extension of Quillen's upward-cone criterion: a preorder
with a monotone self-map `f` and an element `x₀` such that `x ≤ f x ≥ x₀` for every `x` has
a contractible realization. -/
theorem contractibleSpace_of_conical (x₀ : P) (f : P →o P)
    (h₁ : ∀ x, x ≤ f x) (h₂ : ∀ x, x₀ ≤ f x) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (orderComplex P)) := by
  classical
  have hid := homotopic_realizationMap_of_le (f := OrderHom.id) (g := f) h₁
  have hconst := homotopic_realizationMap_of_le (f := OrderHom.const P x₀) (g := f) h₂
  rw [orderComplexMap_id, PreAbstractSimplicialComplex.SimplicialMap.realizationMap_id] at hid
  rw [realizationMap_const] at hconst
  exact (contractible_iff_id_nullhomotopic _).2 ⟨_, hid.trans hconst.symm⟩

end Conical

end LeanPool.PosetHomotopy
