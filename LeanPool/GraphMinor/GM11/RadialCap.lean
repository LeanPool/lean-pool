/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.Surface.Circle

/-!
# A small cap at a boundary point of a closed disc

Let `Q` be a closed disc, and let `T` be a short line in `bd(Q)` through a point `x`, with ends
`y₁`,
`y₂`. A straight chord (in a chart of `Q`) from `y₁` to `y₂` cuts from `Q` a small closed disc whose
boundary is `T` together with the chord (`exists_cap`). In the proof that a radial drawing has no
corner between two of its edges, this small disc closes up an `O`-arc through `x`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A connected subset `T` of an `O`-arc with `s, t ∈ T` whose other points lie in one component `A`
of `F - {s, t}` contains all of `A`. -/
theorem subset_of_component [T2Space S] {F T A₁ A₂ : Set S} (hF : IsOArc F) {s t : S} (hst : s ≠ t)
    (hs : s ∈ F) (ht : t ∈ F) (hT : IsPreconnected T) (hTF : T ⊆ F) (hsT : s ∈ T) (htT : t ∈ T)
    (hne : A₁ ≠ A₂) (hcomp : componentsIn (F \ {s, t}) = {A₁, A₂}) (hsub : T \ {s, t} ⊆ A₁) :
    A₁ ⊆ T := by
  classical
  obtain ⟨φ⟩ := hF
  let ι : Circle → S := fun w => (φ w).1
  have hι : Continuous ι := by fun_prop
  have hinj : Function.Injective ι := fun u w h => φ.injective (Subtype.ext h)
  have hr : ∀ y ∈ F, ∃ w, ι w = y := fun y hy => ⟨φ.symm ⟨y, hy⟩, by simp [ι]⟩
  obtain ⟨a, rfl⟩ := hr s hs
  obtain ⟨b, rfl⟩ := hr t ht
  have hab : a ≠ b := fun h => hst (congrArg ι h)
  have hA₁ : A₁ ∈ componentsIn (F \ {ι a, ι b}) := by rw [hcomp]; simp
  have hA₂ : A₂ ∈ componentsIn (F \ {ι a, ι b}) := by rw [hcomp]; simp
  have harc : ∀ c d : Circle, (c = a ∧ d = b ∨ c = b ∧ d = a) →
      ι '' circleOpenArc c d ⊆ F \ {ι a, ι b} := by
    rintro c d hor _ ⟨w, hw, rfl⟩
    refine ⟨(φ w).2, ?_⟩
    have h₁ : w ∈ ({a, b}ᶜ : Set Circle) := by
      rw [compl_pair_eq_union_circleOpenArc hab]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hw
      · exact Or.inr hw
    rintro (h | h)
    · exact h₁ (Or.inl (hinj h))
    · exact h₁ (Or.inr (hinj h))
  have hconn : ∀ c d : Circle, IsPreconnected (ι '' circleOpenArc c d) := fun c d =>
    (isPathConnected_circleOpenArc c d).isConnected.isPreconnected.image _ hι.continuousOn
  have hdisj : ∀ y, y ∈ A₁ → y ∉ A₂ := by
    intro y hy hy'
    obtain ⟨u, -, rfl⟩ := hA₁
    obtain ⟨u', -, rfl⟩ := hA₂
    exact hne (by rw [connectedComponentIn_eq hy, connectedComponentIn_eq hy'])
  have hin : ∀ {A X : Set S}, A ∈ componentsIn (F \ {ι a, ι b}) → IsPreconnected X →
      X ⊆ F \ {ι a, ι b} → (X ∩ A).Nonempty → X ⊆ A := by
    rintro A X ⟨u, -, rfl⟩ hX hXs ⟨y, hyX, hyA⟩
    rw [connectedComponentIn_eq hyA]
    exact hX.subset_connectedComponentIn hyX hXs
  have hsplit : ∀ u : Circle, ι u ∉ ({ι a, ι b} : Set S) →
      u ∈ circleOpenArc a b ∨ u ∈ circleOpenArc b a := by
    intro u hu
    have : u ∈ ({a, b}ᶜ : Set Circle) := by
      rintro (h | h)
      · exact hu (Or.inl (congrArg ι h))
      · exact hu (Or.inr (congrArg ι h))
    rwa [compl_pair_eq_union_circleOpenArc hab] at this
  by_contra hn
  obtain ⟨z, hzA, hzT⟩ := not_subset.mp hn
  have hzF : z ∈ F \ {ι a, ι b} := by
    obtain ⟨u, hu, rfl⟩ := hA₁
    exact connectedComponentIn_subset _ _ hzA
  obtain ⟨w, rfl⟩ := hr z hzF.1
  have key : ∀ c d : Circle, (c = a ∧ d = b ∨ c = b ∧ d = a) → w ∈ circleOpenArc c d → False := by
    intro c d hor hw
    have hcd : c ≠ d := by
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    have hor' : d = a ∧ c = b ∨ d = b ∧ c = a := by tauto
    have hsplit' : ∀ u : Circle, ι u ∉ ({ι a, ι b} : Set S) →
        u ∈ circleOpenArc c d ∨ u ∈ circleOpenArc d c := by
      intro u hu
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hsplit u hu
      · exact (hsplit u hu).symm
    have hX : ι '' circleOpenArc c d ⊆ A₁ :=
      hin hA₁ (hconn c d) (harc c d hor) ⟨ι w, ⟨w, hw, rfl⟩, hzA⟩
    have hX' : ι '' circleOpenArc d c ⊆ A₂ := by
      obtain ⟨y, hy⟩ : A₂.Nonempty := by
        obtain ⟨u, hu, rfl⟩ := hA₂
        exact ⟨u, mem_connectedComponentIn hu⟩
      have hyF : y ∈ F \ {ι a, ι b} := by
        obtain ⟨u, hu, rfl⟩ := hA₂
        exact connectedComponentIn_subset _ _ hy
      obtain ⟨u, rfl⟩ := hr y hyF.1
      rcases hsplit' u hyF.2 with h | h
      · exact (hdisj _ (hX ⟨u, h, rfl⟩) hy).elim
      · exact hin hA₂ (hconn d c) (harc d c hor') ⟨ι u, ⟨u, h, rfl⟩, hy⟩
    let C : I → S := fun t => ι (Circle.path c d t)
    have hC : Continuous C := hι.comp (Circle.path c d).continuous
    have hCi : Function.Injective C := fun _ _ h => Circle.path_injective_of_ne hcd (hinj h)
    have hend : ({ι a, ι b} : Set S) ⊆ range C := by
      have h0 : C 0 = ι c := by simp [C]
      have h1 : C 1 = ι d := by simp [C]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rintro y (rfl | rfl)
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · rintro y (rfl | rfl)
        · exact ⟨1, h1⟩
        · exact ⟨0, h0⟩
    have hTr : T ⊆ range C := by
      intro y hy
      by_cases hye : y ∈ ({ι a, ι b} : Set S)
      · exact hend hye
      · obtain ⟨u, rfl⟩ := hr y (hTF hy)
        rcases hsplit' u hye with ⟨t, -, ht⟩ | h
        · exact ⟨t, congrArg ι ht⟩
        · exact (hdisj _ (hsub ⟨hy, hye⟩) (hX' ⟨u, h, rfl⟩)).elim
    have hemb := (hC.isClosedEmbedding hCi).isInducing
    have hpre : IsPreconnected (C ⁻¹' T) := by
      refine hemb.isPreconnected_image.mp ?_
      rwa [image_preimage_eq_of_subset hTr]
    have hm0 : (0 : I) ∈ C ⁻¹' T := by
      have h0 : C 0 = ι c := by simp [C]
      change C 0 ∈ T
      rw [h0]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hm1 : (1 : I) ∈ C ⁻¹' T := by
      have h1 : C 1 = ι d := by simp [C]
      change C 1 ∈ T
      rw [h1]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    obtain ⟨τ, hτ, rfl⟩ := hw
    exact hzT (hpre.Icc_subset hm0 hm1 ⟨unitInterval.nonneg _, unitInterval.le_one _⟩)
  rcases hsplit w hzF.2 with h | h
  · exact key a b (Or.inl ⟨rfl, rfl⟩) h
  · exact key b a (Or.inr ⟨rfl, rfl⟩) h

private theorem cap_inside_neighborhood [T2Space S] (hS : IsClosedSurface S)
    {Q W W' T C : Set S} (hQ : IsClosedDisc Q)
    {x y₁ y₂ : S} (hy : y₁ ≠ y₂) (hxT : x ∈ T) (hx₁ : x ≠ y₁) (hx₂ : x ≠ y₂)
    (hTline : IsLineWithEnds T y₁ y₂) (hTb : T ⊆ discBd Q)
    (hend : y₁ ∈ T ∧ y₂ ∈ T) (hy₁b : y₁ ∈ discBd Q) (hy₂b : y₂ ∈ discBd Q)
    (hCline : IsLineWithEnds C y₁ y₂) (hCQ : C ⊆ Q)
    (hCin : Disjoint (C \ {y₁, y₂}) (discBd Q))
    (hCinter : C ∩ discBd Q = {y₁, y₂})
    {f : ClosedUnitDisc → S} {N : Set ClosedUnitDisc}
    (hf : Continuous f) (hfi : Function.Injective f) (hfmem : ∀ y ∈ Q, ∃ z, f z = y)
    (hmem : ∀ z, f z ∈ W' ↔ z ∈ N) (hTW : T ⊆ W') (hNWs : f '' N ⊆ W)
    (hCW' : C ⊆ f '' N) (hRconn : IsPreconnected Nᶜ)
    {z₀ : ClosedUnitDisc} (hz₀ : z₀ ∉ N) (hz₀b : f z₀ ∈ discBd Q)
    (A₁ A₂ Δ₁ Δ₂ : Set S) (hne : A₁ ≠ A₂)
    (hcomp : componentsIn (discBd Q \ {y₁, y₂}) = {A₁, A₂})
    (hd₁ : IsClosedDisc Δ₁) (_hd₂ : IsClosedDisc Δ₂)
    (hcov : Δ₁ ∪ Δ₂ = Q) (hmeet : Δ₁ ∩ Δ₂ = C)
    (hb₁ : discBd Δ₁ = A₁ ∪ C) (hb₂ : discBd Δ₂ = A₂ ∪ C) (hxA : x ∈ A₁) :
    ∃ C Q₁ : Set S, IsLineWithEnds C y₁ y₂ ∧ C ⊆ W ∧ C ⊆ Q ∧
      Disjoint (C \ {y₁, y₂}) (discBd Q) ∧ IsClosedDisc Q₁ ∧ Q₁ ⊆ W ∧ Q₁ ⊆ Q ∧
      discBd Q₁ = T ∪ C ∧ Q₁ ∩ discBd Q ⊆ T := by
  classical
  have hA₁m : A₁ ∈ componentsIn (discBd Q \ {y₁, y₂}) := by rw [hcomp]; simp
  have hTo : IsPreconnected (T \ {y₁, y₂}) :=
    (isPathConnected_sdiff_pair hTline).isConnected.isPreconnected
  have hTc : IsPreconnected T := by
    obtain ⟨g, hg, hr, -⟩ := exists_line_param hTline
    rw [← hr]
    exact isPreconnected_range hg
  have hTsub : T \ {y₁, y₂} ⊆ A₁ := by
    obtain ⟨u, -, hu⟩ := hA₁m
    rw [← hu] at hxA ⊢
    rw [connectedComponentIn_eq hxA]
    exact hTo.subset_connectedComponentIn ⟨hxT, fun h => h.elim hx₁ hx₂⟩
      (fun y hy' => ⟨hTb hy'.1, hy'.2⟩)
  have hAT : A₁ ⊆ T := subset_of_component hQ.isOArc_discBd hy hy₁b hy₂b
    hTc hTb hend.1 hend.2 hne hcomp hTsub
  have hbdΔ : discBd Δ₁ = T ∪ C := by
    rw [hb₁]
    apply subset_antisymm
    · exact union_subset_union_left _ hAT
    · refine union_subset (fun y hy' => ?_) subset_union_right
      by_cases hye : y ∈ ({y₁, y₂} : Set S)
      · have hm : y ∈ C ∩ discBd Q := hCinter.symm ▸ hye
        exact Or.inr hm.1
      · exact Or.inl (hTsub ⟨hy', hye⟩)
  have hΔQ : Δ₁ ⊆ Q := hcov ▸ subset_union_left
  have hz₀T : f z₀ ∉ T := fun h => hz₀ ((hmem z₀).mp (hTW h))
  have hz₀C : f z₀ ∉ C := fun h => by
    obtain ⟨z, hz, hze⟩ := hCW' h
    exact hz₀ (hfi hze ▸ hz)
  have hz₀Δ : f z₀ ∉ Δ₁ := by
    intro h
    have hz₀A₂ : f z₀ ∈ A₂ := by
      have hcc : connectedComponentIn (discBd Q \ {y₁, y₂}) (f z₀) ∈
          componentsIn (discBd Q \ {y₁, y₂}) :=
        ⟨f z₀, ⟨hz₀b, fun h' => h'.elim (fun e => hz₀T (e ▸ hend.1)) fun e => hz₀T (e ▸ hend.2)⟩,
          rfl⟩
      rw [hcomp] at hcc
      have hmemc : f z₀ ∈ connectedComponentIn (discBd Q \ {y₁, y₂}) (f z₀) :=
        mem_connectedComponentIn
          ⟨hz₀b, fun h' => h'.elim (fun e => hz₀T (e ▸ hend.1)) fun e => hz₀T (e ▸ hend.2)⟩
      rcases hcc with e | e
      · exact (hz₀T (hAT (e ▸ hmemc))).elim
      · exact e ▸ hmemc
    have : f z₀ ∈ Δ₂ := by
      have : f z₀ ∈ discBd Δ₂ := by rw [hb₂]; exact Or.inl hz₀A₂
      exact discBd_subset _ this
    exact hz₀C (hmeet ▸ ⟨h, this⟩)
  let R : Set ClosedUnitDisc := Nᶜ
  have hRS : IsPreconnected (f '' R) := hRconn.image _ hf.continuousOn
  have hRdis : Disjoint (f '' R) (frontier Δ₁) := by
    rw [IsClosedDisc.frontier_eq_discBd hS hd₁, hbdΔ]
    refine disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ (h | h)
    · exact hz ((hmem z).mp (hTW h))
    · obtain ⟨z', hz', hze⟩ := hCW' h
      exact hz (hfi hze ▸ hz')
  have hsep : Disjoint (f '' R) Δ₁ := by
    rcases subset_or_disjoint_of_frontier hd₁.isClosed hRS hRdis with h | h
    · exact (hz₀Δ (h ⟨z₀, hz₀, rfl⟩)).elim
    · exact h
  have hΔN : Δ₁ ⊆ f '' N := by
    intro y hy'
    obtain ⟨z, rfl⟩ := hfmem y (hΔQ hy')
    by_cases hz : z ∈ N
    · exact ⟨z, hz, rfl⟩
    · exact (disjoint_left.mp hsep ⟨z, hz, rfl⟩ hy').elim
  refine ⟨C, Δ₁, hCline, hCW'.trans hNWs, hCQ, hCin, hd₁, hΔN.trans hNWs, hΔQ, hbdΔ, ?_⟩
  rintro y ⟨hyΔ, hyb⟩
  by_cases hye : y ∈ ({y₁, y₂} : Set S)
  · rcases hye with rfl | rfl
    · exact hend.1
    · exact hend.2
  · have hcc : connectedComponentIn (discBd Q \ {y₁, y₂}) y ∈
        componentsIn (discBd Q \ {y₁, y₂}) := ⟨y, ⟨hyb, hye⟩, rfl⟩
    rw [hcomp] at hcc
    have hmemc : y ∈ connectedComponentIn (discBd Q \ {y₁, y₂}) y :=
      mem_connectedComponentIn ⟨hyb, hye⟩
    rcases hcc with e | e
    · exact hAT (e ▸ hmemc)
    · have hy₂ : y ∈ Δ₂ := discBd_subset _ (by rw [hb₂]; exact Or.inl (e ▸ hmemc))
      exact (hye (hCinter ▸ ⟨hmeet ▸ ⟨hyΔ, hy₂⟩, hyb⟩)).elim

/-- **A cap at a boundary point.** See the module docstring. -/
theorem exists_cap (hS : IsClosedSurface S) {Q : Set S} (hQ : IsClosedDisc Q) {x : S}
    (hx : x ∈ discBd Q) {W : Set S} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ W', IsOpen W' ∧ x ∈ W' ∧ ∀ (y₁ y₂ : S) (T : Set S), y₁ ≠ y₂ → IsLineWithEnds T y₁ y₂ →
      T ⊆ discBd Q → T ⊆ W' → x ∈ T → x ≠ y₁ → x ≠ y₂ →
      ∃ C Q₁ : Set S, IsLineWithEnds C y₁ y₂ ∧ C ⊆ W ∧ C ⊆ Q ∧ Disjoint (C \ {y₁, y₂}) (discBd Q) ∧
        IsClosedDisc Q₁ ∧ Q₁ ⊆ W ∧ Q₁ ⊆ Q ∧ discBd Q₁ = T ∪ C ∧ Q₁ ∩ discBd Q ⊆ T := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨φ⟩ := id hQ
  have hbd := disc_boundary Q φ
  rw [hbd] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hbn : ‖(b : EuclideanPlane)‖ = 1 := by simpa [UnitCircle] using hb
  let f : ClosedUnitDisc → S := fun z => (φ z).1
  have hf : Continuous f := continuous_subtype_val.comp φ.continuous
  have hfi : Function.Injective f := fun _ _ h => φ.injective (Subtype.ext h)
  have hfmem : ∀ y ∈ Q, ∃ z, f z = y := fun y hy => ⟨φ.symm ⟨y, hy⟩, by simp [f]⟩
  have hopen : IsOpen {z : ClosedUnitDisc | f z ∈ W} := hW.preimage hf
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen b hxW
  let inner' : EuclideanPlane → ℝ := fun z => inner ℝ z (b : EuclideanPlane)
  have hinner : Continuous inner' := by fun_prop
  let η : ℝ := min (δ ^ 2 / 2) 1
  have hη : 0 < η := lt_min (by positivity) one_pos
  have hηle : η ≤ 1 := min_le_right _ _
  let N : Set ClosedUnitDisc := {z | 1 - η < inner' z}
  have hNo : IsOpen N := isOpen_lt continuous_const (hinner.comp continuous_subtype_val)
  have hNW : N ⊆ {z | f z ∈ W} := by
    intro z hz
    refine hball ?_
    have hzn : ‖(z : EuclideanPlane)‖ ≤ 1 := by
      have := z.2
      simpa [ClosedUnitDisc] using this
    have hz' : 1 - η < inner ℝ (z : EuclideanPlane) b := hz
    have h₁ : ‖(z : EuclideanPlane) - b‖ ^ 2 < δ ^ 2 := by
      rw [@norm_sub_sq_real, hbn]
      have : η ≤ δ ^ 2 / 2 := min_le_left _ _
      nlinarith [norm_nonneg (z : EuclideanPlane)]
    have h₂ : ‖(z : EuclideanPlane) - b‖ < δ := lt_of_pow_lt_pow_left₀ 2 hδ.le h₁
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    exact h₂
  have hfopen : IsOpen ((fun y : Q => φ.symm y) ⁻¹' N) := hNo.preimage φ.symm.continuous
  obtain ⟨W', hW', hWeq⟩ := isOpen_induced_iff.mp hfopen
  have hmem : ∀ z : ClosedUnitDisc, f z ∈ W' ↔ z ∈ N := by
    intro z
    have := congrArg (fun T : Set Q => φ z ∈ T) hWeq
    simpa [f] using this
  have hbN : b ∈ N := by
    change 1 - η < inner ℝ (b : EuclideanPlane) b
    rw [real_inner_self_eq_norm_sq, hbn]
    linarith
  refine ⟨W', hW', (hmem b).mpr hbN, ?_⟩
  intro y₁ y₂ T hy hTline hTb hTW hxT hx₁ hx₂
  have hsubQ : discBd Q ⊆ Q := discBd_subset Q
  have hend : y₁ ∈ T ∧ y₂ ∈ T := by
    obtain ⟨g, h0, h1⟩ := hTline
    exact ⟨h0 ▸ (g 0).2, h1 ▸ (g 1).2⟩
  have hy₁b : y₁ ∈ discBd Q := hTb hend.1
  have hy₂b : y₂ ∈ discBd Q := hTb hend.2
  have hcirc : ∀ y ∈ discBd Q, ∃ z : ClosedUnitDisc, f z = y ∧ ‖(z : EuclideanPlane)‖ = 1 := by
    intro y hy'
    rw [hbd] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    exact ⟨z, rfl, by simpa [UnitCircle] using hz⟩
  obtain ⟨z₁, rfl, hz₁⟩ := hcirc y₁ hy₁b
  obtain ⟨z₂, rfl, hz₂⟩ := hcirc y₂ hy₂b
  have hzne : (z₁ : EuclideanPlane) ≠ z₂ := fun h => hy (congrArg f (Subtype.ext h))
  have hdn : ∀ z : EuclideanPlane, z ∈ ClosedUnitDisc ↔ ‖z‖ ≤ 1 := fun z => by simp [ClosedUnitDisc]
  have hseg : ∀ t : I, (1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) • (z₂ : EuclideanPlane) ∈
      ClosedUnitDisc := by
    intro t
    exact (convex_closedBall (0 : EuclideanPlane) 1) z₁.2 z₂.2 (by linarith [t.2.2]) t.2.1 (by ring)
  let m : I → ClosedUnitDisc := fun t => ⟨_, hseg t⟩
  have hm : Continuous m := Continuous.subtype_mk (by fun_prop) _
  have hmi : Function.Injective m := by
    intro s t h
    have h' := congrArg Subtype.val h
    have h₂ : ((s : ℝ) - t) • ((z₂ : EuclideanPlane) - z₁) = 0 := by
      have h₃ : (1 - (s : ℝ)) • (z₁ : EuclideanPlane) + (s : ℝ) • (z₂ : EuclideanPlane) =
        (1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) • (z₂ : EuclideanPlane) := h'
      have h₄ : ((s : ℝ) - t) • ((z₂ : EuclideanPlane) - z₁) =
        ((1 - (s : ℝ)) • (z₁ : EuclideanPlane) + (s : ℝ) • (z₂ : EuclideanPlane)) -
        ((1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) • (z₂ : EuclideanPlane)) := by
        module
      rw [h₄, h₃, sub_self]
    have h₅ := (smul_eq_zero.mp h₂).resolve_right (sub_ne_zero.mpr hzne.symm)
    exact Subtype.ext (by linarith)
  have hm0 : m 0 = z₁ := Subtype.ext (by simp [m])
  have hm1 : m 1 = z₂ := Subtype.ext (by simp [m])
  let C : Set S := range (f ∘ m)
  have hCc : Continuous (f ∘ m) := hf.comp hm
  have hCline : IsLineWithEnds C (f z₁) (f z₂) := by
    have := isLine_range hCc (hfi.comp hmi)
    simpa [hm0, hm1] using this
  have hN₁ : z₁ ∈ N := (hmem z₁).mp (hTW hend.1)
  have hN₂ : z₂ ∈ N := (hmem z₂).mp (hTW hend.2)
  have hmN : ∀ t, m t ∈ N := by
    intro t
    have hlin : inner' (m t : EuclideanPlane) =
        (1 - (t : ℝ)) * inner' z₁ + (t : ℝ) * inner' z₂ := by
      simp only [inner', m, inner_add_left, real_inner_smul_left]
    change 1 - η < inner' (m t : EuclideanPlane)
    rw [hlin]
    have h₁ : 1 - η < inner' z₁ := hN₁
    have h₂ : 1 - η < inner' z₂ := hN₂
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hl : 1 - η < min (inner' z₁) (inner' z₂) := lt_min h₁ h₂
    have h₃ := min_le_left (inner' z₁) (inner' z₂)
    have h₄ := min_le_right (inner' z₁) (inner' z₂)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h₃), mul_nonneg ht0
      (sub_nonneg.mpr h₄)]
  have hCW' : C ⊆ f '' N := by
    rintro _ ⟨t, rfl⟩
    exact ⟨m t, hmN t, rfl⟩
  have hNWs : f '' N ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact hNW hz
  have hCQ : C ⊆ Q := by
    rintro _ ⟨t, rfl⟩
    exact (φ _).2
  have hCin : Disjoint (C \ {f z₁, f z₂}) (discBd Q) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨⟨t, rfl⟩, hne⟩ hb'
    obtain ⟨z, hze, hzn⟩ := hcirc _ hb'
    have hzm : z = m t := hfi hze
    have ht0 : t ≠ 0 := fun h => hne (Or.inl (by simp [h, hm0]))
    have ht1 : t ≠ 1 := fun h => hne (Or.inr (by simp [h, hm1]))
    have ht0' : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
    have ht1' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
    have hin : inner ℝ (z₁ : EuclideanPlane) (z₂ : EuclideanPlane) < 1 := by
      have hpos : 0 < ‖(z₁ : EuclideanPlane) - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
      have := norm_sub_sq_real (z₁ : EuclideanPlane) (z₂ : EuclideanPlane)
      rw [hz₁, hz₂] at this
      nlinarith
    have h₁ : ‖(1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) • (z₂ : EuclideanPlane)‖ ^ 2 < 1
      := by
      rw [@norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        hz₁, hz₂, Real.norm_of_nonneg (show 0 ≤ 1 - (t : ℝ) by linarith),
        Real.norm_of_nonneg (show 0 ≤ (t : ℝ) by linarith)]
      nlinarith [mul_pos ht0' (show 0 < 1 - (t : ℝ) by linarith)]
    have h₂ : ‖(1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) • (z₂ : EuclideanPlane)‖ < 1 := by
      nlinarith [norm_nonneg ((1 - (t : ℝ)) • (z₁ : EuclideanPlane) + (t : ℝ) •
        (z₂ : EuclideanPlane))]
    have : ‖(z : EuclideanPlane)‖ < 1 := by rw [hzm]; exact h₂
    linarith
  have hCinter : C ∩ discBd Q = {f z₁, f z₂} := by
    apply subset_antisymm
    · rintro y ⟨hyC, hyb⟩
      by_contra hn
      exact disjoint_left.mp hCin ⟨hyC, hn⟩ hyb
    · rintro y (rfl | rfl)
      · exact ⟨⟨0, by simp [hm0]⟩, hy₁b⟩
      · exact ⟨⟨1, by simp [hm1]⟩, hy₂b⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hne, hcomp, hd₁, hd₂, hcov, hmeet, hb₁, hb₂, -⟩ :=
    disc_iArc Q C (f z₁) (f z₂) hQ hCQ hy hCline hCinter
  -- The point opposite to `x`.
  have hmb : (-(b : EuclideanPlane)) ∈ ClosedUnitDisc := by
    rw [hdn, norm_neg, hbn]
  let z₀ : ClosedUnitDisc := ⟨_, hmb⟩
  have hz₀ : z₀ ∉ N := by
    change ¬ 1 - η < inner ℝ (-(b : EuclideanPlane)) b
    rw [inner_neg_left, real_inner_self_eq_norm_sq, hbn]
    linarith
  have hz₀b : f z₀ ∈ discBd Q := by
    rw [hbd]
    exact ⟨z₀, by simpa [UnitCircle, z₀] using hbn, rfl⟩
  let R : Set ClosedUnitDisc := Nᶜ
  have hRconn : IsPreconnected R := by
    have hlin : IsLinearMap ℝ inner' :=
      ⟨fun x y => inner_add_left _ _ _, fun c x => real_inner_smul_left _ _ _⟩
    have hconv : Convex ℝ (ClosedUnitDisc ∩ {z : EuclideanPlane | inner' z ≤ 1 - η}) :=
      (convex_closedBall (0 : EuclideanPlane) 1).inter (convex_halfSpace_le hlin _)
    refine (IsInducing.subtypeVal :
      IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
    have : Subtype.val '' R = ClosedUnitDisc ∩ {z : EuclideanPlane | inner' z ≤ 1 - η} := by
      ext z
      constructor
      · rintro ⟨y, hy', rfl⟩
        exact ⟨y.2, not_lt.mp (show ¬ 1 - η < inner' y from hy')⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨⟨z, h₁⟩, show ¬ 1 - η < inner' z from not_lt.mpr h₂, rfl⟩
    rw [this]
    exact hconv.isPreconnected
  have main := cap_inside_neighborhood hS hQ hy hxT hx₁ hx₂ hTline hTb hend hy₁b hy₂b
    hCline hCQ hCin hCinter hf hfi hfmem hmem hTW hNWs hCW' hRconn hz₀ hz₀b
  have hxnot : f b ∉ ({f z₁, f z₂} : Set S) := fun h => h.elim hx₁ hx₂
  have hcc : connectedComponentIn (discBd Q \ {f z₁, f z₂}) (f b) ∈
      componentsIn (discBd Q \ {f z₁, f z₂}) := ⟨f b, ⟨hTb hxT, hxnot⟩, rfl⟩
  have hmemc : f b ∈ connectedComponentIn (discBd Q \ {f z₁, f z₂}) (f b) :=
    mem_connectedComponentIn ⟨hTb hxT, hxnot⟩
  rw [hcomp] at hcc
  rcases hcc with e | e
  · exact main A₁ A₂ Δ₁ Δ₂ hne hcomp hd₁ hd₂ hcov hmeet hb₁ hb₂ (e ▸ hmemc)
  · exact main A₂ A₁ Δ₂ Δ₁ hne.symm (by rw [hcomp, pair_comm]) hd₂ hd₁ (by rw [union_comm, hcov])
      (by rw [inter_comm, hmeet]) hb₂ hb₁ (e ▸ hmemc)

end GraphMinor.GM11
