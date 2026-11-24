/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Null
public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.CutLift
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# Rerouting a curve through a disc

Let `F` be an `O`-arc of a surface that is not null-homotopic and meets a closed disc `D`. Choose a
line `P(a, b)` in `D` for any two points `a, b` of `bd(D)`. Then some component of `F \ D`, with
ends `a, b`, gives a non-null-homotopic `O`-arc when it is closed up by `P(a, b)`
(`exists_reroute`).

The proof is this. Finitely many components of `F \ D` leave a larger disc, so `F` is a product of
these components and paths in the larger disc (`homotopic_of_intervals`). If each closed-up
component were null-homotopic, then `F` would be homotopic to a loop in the larger disc.

Graph Minors XIX, Section 6, uses this fact twice without comment: in `rep(G \ v) ≥ rep(G) - 1`
(page 341) and for the "non-null-homotopic $O$-arc disjoint from $\Delta$" of (6.6), claim (2) (page
342).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12

local notation "𝕀" => unitInterval

variable {T : Type} [TopologicalSpace T]

instance : ContractibleSpace 𝕀 := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩

/-- The straight path from `s` to `t` in the unit interval. -/
noncomputable def seg (s t : 𝕀) : Path s t where
  toFun x := ⟨(1 - x.1) * s.1 + x.1 * t.1, by
    have h1 := x.2.1
    have h2 := x.2.2
    have h3 := s.2.1
    have h4 := s.2.2
    have h5 := t.2.1
    have h6 := t.2.2
    constructor <;> nlinarith [mul_nonneg h1 h5, mul_nonneg (sub_nonneg.mpr h2) h3, mul_nonneg h1
      (sub_nonneg.mpr h6), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h4)]⟩
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem seg_mem {s t : 𝕀} (hst : s ≤ t) (x : 𝕀) : seg s t x ∈ Icc s t := by
  have h1 := x.2.1
  have h2 := x.2.2
  have hst' : s.1 ≤ t.1 := hst
  constructor
  · change s.1 ≤ (1 - x.1) * s.1 + x.1 * t.1
    nlinarith [mul_nonneg h1 (sub_nonneg.mpr hst')]
  · change (1 - x.1) * s.1 + x.1 * t.1 ≤ t.1
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hst')]

/-- The part of a map of the interval from `s` to `t`. -/
noncomputable def subP (f : C(𝕀, T)) (s t : 𝕀) : Path (f s) (f t) := (seg s t).map f.continuous

theorem subP_trans (f : C(𝕀, T)) (s t u : 𝕀) : (subP f s u).Homotopic ((subP f s t).trans
  (subP f t u)) := by
  have h : (seg s u).Homotopic ((seg s t).trans (seg t u)) := SimplyConnectedSpace.paths_homotopic
    _ _
  have h2 := h.map f
  rw [Path.map_trans] at h2
  exact h2

theorem subP_mem (f : C(𝕀, T)) {s t : 𝕀} (hst : s ≤ t) (x : 𝕀) : ∃ y ∈ Icc s t, subP f s t x = f y
  :=
  ⟨_, seg_mem hst x, rfl⟩

/-- A path with the middle parts in `W`, and with each of finitely many other parts homotopic to a
path in `W`, is homotopic to a path in `W`. -/
theorem homotopic_of_intervals (f : C(𝕀, T)) (W : Set T) : ∀ (n : ℕ) (G : Finset (𝕀 × 𝕀)), G.card
  ≤ n → ∀ s t : 𝕀, s ≤ t → f s ∈ W → f t ∈ W →
    (∀ g ∈ G, s ≤ g.1 ∧ g.1 < g.2 ∧ g.2 ≤ t ∧ f g.1 ∈ W ∧ f g.2 ∈ W ∧ ∃ q : Path (f g.1)
      (f g.2), range q ⊆ W ∧ (subP f g.1 g.2).Homotopic q) →
    (∀ g ∈ G, ∀ g' ∈ G, g ≠ g' → g.2 ≤ g'.1 ∨ g'.2 ≤ g.1) →
    (∀ x ∈ Icc s t, (∀ g ∈ G, x ∉ Ioo g.1 g.2) → f x ∈ W) →
    ∃ q : Path (f s) (f t), range q ⊆ W ∧ (subP f s t).Homotopic q := by
  classical
  have hbase : ∀ s t : 𝕀, s ≤ t → (∀ x ∈ Icc s t, f x ∈ W) → ∃ q : Path (f s) (f t), range q ⊆ W ∧
    (subP f s t).Homotopic q := fun s t hst h =>
    ⟨subP f s t, by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, he⟩ := subP_mem f hst x
      rw [he]
      exact h y hy, Path.Homotopic.refl _⟩
  intro n
  induction n with
  | zero =>
    intro G hG s t hst _ _ _ _ hmid
    have hG' : G = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hG)
    exact hbase s t hst fun x hx => hmid x hx (by simp [hG'])
  | succ n ih =>
    intro G hG s t hst hs ht hg hdis hmid
    by_cases hne : G.Nonempty
    swap
    · exact hbase s t hst fun x hx => hmid x hx fun g hgG => absurd ⟨g, hgG⟩ hne
    obtain ⟨g, hgG⟩ := hne
    obtain ⟨h1, h2, h3, h4, h5, q, hq, hhq⟩ := hg g hgG
    have hsub₁ : (G.filter fun g' => g'.2 ≤ g.1) ⊂ G := by
      refine Finset.filter_ssubset.mpr ⟨g, hgG, not_le.mpr h2⟩
    have hsub₂ : (G.filter fun g' => g.2 ≤ g'.1) ⊂ G := by
      refine Finset.filter_ssubset.mpr ⟨g, hgG, not_le.mpr h2⟩
    have hc₁ := Finset.card_lt_card hsub₁
    have hc₂ := Finset.card_lt_card hsub₂
    obtain ⟨q₁, hq₁, hh₁⟩ := ih (G.filter fun g' => g'.2 ≤ g.1) (by omega) s g.1 h1 hs h4
      (fun g' hg' => by
      obtain ⟨a1, a2, a3, a4⟩ := hg g' (Finset.mem_of_mem_filter _ hg')
      exact ⟨a1, a2, (Finset.mem_filter.mp hg').2, a4⟩) (fun a ha b hb => hdis a
        (Finset.mem_of_mem_filter _ ha) b (Finset.mem_of_mem_filter _ hb))
      (fun x hx hno => hmid x ⟨hx.1, hx.2.trans (h2.le.trans h3)⟩ fun g' hg' hin => by
        by_cases he : g' = g
        · subst he
          exact not_lt.mpr hx.2 hin.1
        · rcases hdis g' hg' g hgG he with h6 | h6
          · exact hno g' (Finset.mem_filter.mpr ⟨hg', h6⟩) hin
          · exact not_lt.mpr (hx.2.trans (h2.le.trans h6)) hin.1)
    obtain ⟨q₂, hq₂, hh₂⟩ := ih (G.filter fun g' => g.2 ≤ g'.1) (by omega) g.2 t h3 h5 ht
      (fun g' hg' => by
      obtain ⟨a1, a2, a3, a4⟩ := hg g' (Finset.mem_of_mem_filter _ hg')
      exact ⟨(Finset.mem_filter.mp hg').2, a2, a3, a4⟩) (fun a ha b hb => hdis a
        (Finset.mem_of_mem_filter _ ha) b (Finset.mem_of_mem_filter _ hb))
      (fun x hx hno => hmid x ⟨h1.trans (h2.le.trans hx.1), hx.2⟩ fun g' hg' hin => by
        by_cases he : g' = g
        · subst he
          exact not_lt.mpr hx.1 hin.2
        · rcases hdis g' hg' g hgG he with h6 | h6
          · exact not_lt.mpr (h6.trans (h2.le.trans hx.1)) hin.2
          · exact hno g' (Finset.mem_filter.mpr ⟨hg', h6⟩) hin)
    refine ⟨q₁.trans (q.trans q₂), ?_, ?_⟩
    · rw [Path.trans_range, Path.trans_range]
      exact union_subset hq₁ (union_subset hq hq₂)
    · exact (subP_trans f s g.1 t).trans ((hh₁.hcomp ((subP_trans f g.1 g.2 t).trans
      (hhq.hcomp hh₂))))

/-- The intervals of the complement of a closed set of the interval. -/
theorem exists_intervals {U K : Set 𝕀} (hU : IsOpen U) (hKc : IsClosed K) (hKU : K ⊆ U) (h0 :
  (0 : 𝕀) ∉ U) (h1 : (1 : 𝕀) ∉ U) :
    ∃ G : Finset (𝕀 × 𝕀), (∀ g ∈ G, g.1 < g.2 ∧ g.1 ∉ U ∧ g.2 ∉ U ∧ Ioo g.1 g.2 ⊆ U) ∧
      (∀ g ∈ G, ∀ g' ∈ G, g ≠ g' → g.2 ≤ g'.1 ∨ g'.2 ≤ g.1) ∧
      ∀ x ∈ K, ∃ g ∈ G, x ∈ Ioo g.1 g.2 := by
  classical
  have hint : ∀ t ∈ U, ∃ a b : 𝕀, a < t ∧ t < b ∧ a ∉ U ∧ b ∉ U ∧ Ioo a b ⊆ U := fun t ht => by
    have hC : IsClosed (Uᶜ) := hU.isClosed_compl
    have hL : IsClosed (Uᶜ ∩ Iic t) := hC.inter isClosed_Iic
    have hR : IsClosed (Uᶜ ∩ Ici t) := hC.inter isClosed_Ici
    have ha := hL.csSup_mem ⟨0, h0, unitInterval.nonneg'⟩ (OrderTop.bddAbove _)
    have hb := hR.csInf_mem ⟨1, h1, unitInterval.le_one'⟩ (OrderBot.bddBelow _)
    refine ⟨sSup (Uᶜ ∩ Iic t), sInf (Uᶜ ∩ Ici t), lt_of_le_of_ne ha.2 fun h' => ha.1
      (by rw [h']; exact ht), lt_of_le_of_ne hb.2 (fun h' => hb.1 (by rw [← h']; exact ht)), ha.1,
        hb.1, ?_⟩
    rintro x ⟨hx1, hx2⟩
    by_contra hxU
    rcases le_total x t with hxt | hxt
    · exact not_le.mpr hx1 (le_csSup (OrderTop.bddAbove _) ⟨hxU, hxt⟩)
    · exact not_le.mpr hx2 (csInf_le (OrderBot.bddBelow _) ⟨hxU, hxt⟩)
  choose! a b ha hb haU hbU hab using hint
  obtain ⟨S, hS, hf, hcov⟩ := hKc.isCompact.elim_finite_subcover_image (b := K) (c := fun t => Ioo
    (a t) (b t)) (fun t _ => isOpen_Ioo)
    fun t ht => mem_biUnion ht ⟨ha t (hKU ht), hb t (hKU ht)⟩
  have hmem : ∀ g ∈ hf.toFinset.image (fun t => (a t, b t)), g.1 < g.2 ∧ g.1 ∉ U ∧ g.2 ∉ U
    ∧ Ioo g.1 g.2 ⊆ U := fun g hg => by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    have htU : t ∈ U := hKU (hS (hf.mem_toFinset.mp ht))
    exact ⟨(ha t htU).trans (hb t htU), haU t htU, hbU t htU, hab t htU⟩
  refine ⟨hf.toFinset.image (fun t => (a t, b t)), hmem, fun g hg g' hg' hne => ?_, fun x hx => ?_⟩
  · obtain ⟨g1, g2, g3, g4⟩ := hmem g hg
    obtain ⟨k1, k2, k3, k4⟩ := hmem g' hg'
    rcases lt_trichotomy g.1 g'.1 with h | h | h
    · left
      by_contra hc
      exact k2 (g4 ⟨h, not_le.mp hc⟩)
    · have h2 : g.2 = g'.2 := by
        rcases lt_trichotomy g.2 g'.2 with h3 | h3 | h3
        · exact absurd (k4 ⟨h ▸ g1, h3⟩) g3
        · exact h3
        · exact absurd (g4 ⟨h.symm ▸ k1, h3⟩) k3
      exact absurd (Prod.ext h h2) hne
    · right
      by_contra hc
      exact g2 (k4 ⟨h, not_le.mp hc⟩)
  · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp (hcov hx)
    exact ⟨_, Finset.mem_image.mpr ⟨t, hf.mem_toFinset.mpr ht, rfl⟩, hxt⟩

/-- A loop homotopic to the constant path is a null-homotopic closed curve. -/
theorem null_of_path_refl {w : T} (P : Path w w) {γ : C(Circle, T)} (hγ : ∀ t, γ
  (arcParam 1 t) = P t) (h : P.Homotopic (Path.refl w)) :
    ClosedCurveIsNullHomotopicIn univ γ := by
  obtain ⟨H⟩ := h
  let F : C(𝕀 × 𝕀, T) := ⟨fun z => H (z.2, z.1), by fun_prop⟩
  have hends : ∀ t, F (0, t) = F (1, t) := by intro t; simp [F]
  refine ⟨w, mem_univ _, cylinderLift 1 F hends, fun _ => mem_univ _, ?_, ?_⟩
  · intro z
    obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
    rw [cylinderLift_apply]
    change H (0, s) = γ (arcParam 1 s)
    rw [H.apply_zero, hγ]
    rfl
  · intro z
    obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
    rw [cylinderLift_apply]
    change H (1, s) = w
    simp

/-- Two paths in a closed disc with the same ends are homotopic. -/
theorem paths_homotopic_in_disc {Δ : Set T} (hΔ : IsClosedDisc Δ) {a b : T} (p q : Path a b)
  (hp : range p ⊆ Δ) (hq : range q ⊆ Δ) : p.Homotopic q := by
  obtain ⟨e⟩ := id hΔ
  have hc : ContractibleSpace ClosedUnitDisc := (convex_closedBall (0 : EuclideanPlane)
    1).contractibleSpace ⟨0, by simp⟩
  have hc' : ContractibleSpace Δ := e.symm.contractibleSpace
  have ha : a ∈ Δ := hp ⟨0, by simp⟩
  have hb : b ∈ Δ := hp ⟨1, by simp⟩
  let p' : Path (⟨a, ha⟩ : Δ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨p t, hp ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  let q' : Path (⟨a, ha⟩ : Δ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨q t, hq ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  have h : p'.Homotopic q' := SimplyConnectedSpace.paths_homotopic _ _
  have h2 := h.map ⟨Subtype.val, continuous_subtype_val⟩
  have e1 : p'.map continuous_subtype_val = p := by
    ext t
    rfl
  have e2 : q'.map continuous_subtype_val = q := by
    ext t
    rfl
  have e3 := h2
  simp only [ContinuousMap.coe_mk] at e3
  rwa [e1, e2] at e3

theorem cast_refl_of_disc {Δ : Set T} (hΔ : IsClosedDisc Δ) {a b : T} (h : a = b) (p q : Path a b)
  (hq : range q ⊆ Δ) (hp : p.Homotopic q) :
    (p.cast rfl h).Homotopic (Path.refl a) := by
  subst h
  have hrefl : range (Path.refl a) ⊆ Δ := by
    rintro _ ⟨t, rfl⟩
    exact hq ⟨0, by simp⟩
  exact hp.trans (paths_homotopic_in_disc hΔ q (Path.refl a) hq hrefl)

theorem homotopic_of_trans_symm {a b : T} {p q : Path a b} (h : (p.trans q.symm).Homotopic
  (Path.refl a)) : p.Homotopic q := by
  have h1 : ((p.trans q.symm).trans q).Homotopic ((Path.refl a).trans q) := h.hcomp
    (Path.Homotopic.refl q)
  have h2 : ((p.trans q.symm).trans q).Homotopic p := by
    refine (Path.Homotopic.trans_assoc p q.symm q).trans ?_
    have h3 := Path.Homotopic.trans_symm q.symm
    rw [Path.symm_symm] at h3
    exact ((Path.Homotopic.refl p).hcomp h3).trans (Path.Homotopic.trans_refl p)
  exact h2.symm.trans (h1.trans (Path.Homotopic.refl_trans q))

theorem seg_injective {s t : 𝕀} (hst : s < t) : Function.Injective (seg s t) := fun x y h => by
  have h1 : (1 - x.1) * s.1 + x.1 * t.1 = (1 - y.1) * s.1 + y.1 * t.1 := congrArg Subtype.val h
  have h2 : (x.1 - y.1) * (t.1 - s.1) = 0 := by linarith
  have h3 : t.1 - s.1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hst)
  exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h3))

theorem seg_zero_one (t : 𝕀) : seg 0 1 t = t := Subtype.ext (by
  change (1 - t.1) * (0 : ℝ) + t.1 * 1 = t.1
  ring)

variable [T2Space T]

/-- **Rerouting a curve through a disc.** See the module docstring. -/
theorem exists_reroute (hT : IsClosedSurface T) {D F : Set T} (hD : IsClosedDisc D) (hF : IsOArc F)
  (hnn : ¬ IsNullHomotopicOArc F) (hm : (F ∩ D).Nonempty) (P : T → T → Set T)
    (hP : ∀ a ∈ discBd D, ∀ b ∈ discBd D, P a b ⊆ D ∧ (a ≠ b → IsLineWithEnds (P a b) a b) ∧ (a = b
      → P a b = {a})) :
    ∃ C a b, IsOArc C ∧ ¬ IsNullHomotopicOArc C ∧ a ∈ F ∩ discBd D ∧ b ∈ F ∩ discBd D ∧ P a b ⊆ C
      ∧ C ⊆ (F \ D) ∪ P a b := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  by_contra hno
  push Not at hno
  obtain ⟨p₀, hp₀F, hp₀D⟩ := hm
  obtain ⟨φ₀⟩ := id hF
  let φ : Circle ≃ₜ F := (Homeomorph.mulLeft (φ₀.symm ⟨p₀, hp₀F⟩)).trans φ₀
  have hφ1 : (φ 1).1 = p₀ := by
    simp [φ]
  let f : C(𝕀, T) := ⟨fun x => (φ (arcParam 1 x)).1, by fun_prop⟩
  have hf0 : f 0 = p₀ := by
    change (φ (arcParam 1 0)).1 = p₀
    rw [arcParam_zero, hφ1]
  have hf1 : f 1 = p₀ := by
    change (φ (arcParam 1 1)).1 = p₀
    rw [arcParam_one, hφ1]
  have hfinj : ∀ {s t}, f s = f t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := fun {s t} h =>
    arcParam_eq_iff 1 (φ.injective (Subtype.ext h))
  have hfF : ∀ t, f t ∈ F := fun t => (φ (arcParam 1 t)).2
  have hfr : ∀ x ∈ F, ∃ t, f t = x := fun x hx => by
    obtain ⟨t, ht⟩ := arcParam_surjective 1 (φ.symm ⟨x, hx⟩)
    exact ⟨t, by simp [f, ht]⟩
  have hDc := hD.isClosed
  have hint : ∀ x ∈ discBd D, IsInteriorPoint x := fun x _ => hT.2.2 x
  obtain ⟨Δ, hΔ, hsub, -⟩ := exists_disc_around hman hD hint isOpen_univ (subset_univ _)
  have hI : IsOpen (Δ \ discBd Δ) := hΔ.isOpen_discInt hman
  obtain ⟨G, hG, hdis, hcov⟩ := exists_intervals (U := f ⁻¹' Dᶜ) (K := f ⁻¹' (Δ \ discBd Δ)ᶜ)
    (hDc.isOpen_compl.preimage f.continuous)
    (hI.isClosed_compl.preimage f.continuous) (fun t ht hD' => ht (hsub hD'))
    (by simpa [hf0] using hp₀D) (by simpa [hf1] using hp₀D)
  have hDint : IsOpen (D \ discBd D) := hD.isOpen_discInt hman
  have hbd : ∀ g ∈ G, f g.1 ∈ discBd D ∧ f g.2 ∈ discBd D := fun g hg => by
    obtain ⟨g1, g2, g3, g4⟩ := hG g hg
    have hcl : Icc g.1 g.2 ⊆ closure (Ioo g.1 g.2) := by rw [closure_Ioo (ne_of_lt g1)]
    have key : ∀ x ∈ Icc g.1 g.2, f x ∈ D → f x ∈ discBd D := fun x hx hxD => by
      by_contra hn
      obtain ⟨y, hy, hyI⟩ := mem_closure_iff.mp (hcl hx) (f ⁻¹' (D \ discBd D))
        (hDint.preimage f.continuous) ⟨hxD, hn⟩
      exact g4 hyI hy.1
    exact ⟨key _ ⟨le_rfl, g1.le⟩ (not_not.mp g2), key _ ⟨g1.le, le_rfl⟩ (not_not.mp g3)⟩
  have hgood : ∀ g ∈ G, ∃ q : Path (f g.1) (f g.2), range q ⊆ Δ ∧ (subP f g.1 g.2).Homotopic q
    := fun g hg => by
    obtain ⟨g1, g2, g3, g4⟩ := hG g hg
    obtain ⟨hb1, hb2⟩ := hbd g hg
    have hg1D := not_not.mp g2
    have hg2D := not_not.mp g3
    obtain ⟨hPs, hPl, hPe⟩ := hP _ hb1 _ hb2
    by_cases hab : f g.1 = f g.2
    · exfalso
      obtain ⟨h1, h2⟩ : g.1 = 0 ∧ g.2 = 1 := by
        rcases hfinj hab with h | h | h
        · exact absurd h (ne_of_lt g1)
        · exact h
        · exact absurd (h.1 ▸ g1 : (1 : 𝕀) < g.2) (not_lt.mpr unitInterval.le_one')
      have hPa := hPe hab
      refine hno F _ _ hF hnn ⟨hfF _, hb1⟩ ⟨hfF _, hb2⟩ ?_ ?_
      · rw [hPa]
        exact singleton_subset_iff.mpr (hfF _)
      · intro x hx
        obtain ⟨t, rfl⟩ := hfr x hx
        by_cases ht : t ∈ Ioo g.1 g.2
        · exact .inl ⟨hfF t, g4 ht⟩
        · right
          rw [hPa]
          have h3 : t = 0 ∨ t = 1 := by
            by_contra hc
            push Not at hc
            exact ht ⟨h1 ▸ lt_of_le_of_ne unitInterval.nonneg' hc.1.symm,
              h2 ▸ lt_of_le_of_ne unitInterval.le_one' hc.2⟩
          rw [h1]
          rcases h3 with rfl | rfl
          · rfl
          · exact hf1.trans hf0.symm
    · have hL := hPl hab
      obtain ⟨c, hc, hr, c0, c1⟩ := hL.exists_arc
      let q : Path (f g.1) (f g.2) := ⟨⟨c, hc.1⟩, c0, c1⟩
      have hqr : range q = P (f g.1) (f g.2) := hr
      let e := subP f g.1 g.2
      have hei : Function.Injective e := fun x y hxy => by
        have hxy' : f (seg g.1 g.2 x) = f (seg g.1 g.2 y) := hxy
        apply seg_injective g1
        rcases hfinj hxy' with h | h | h
        · exact h
        · exfalso
          have h1 := seg_mem g1.le x
          have h2 := seg_mem g1.le y
          rw [h.1] at h1
          rw [h.2] at h2
          have e1 : g.1 = 0 := le_antisymm h1.1 unitInterval.nonneg'
          have e2 : g.2 = 1 := le_antisymm unitInterval.le_one' h2.2
          exact hab (by rw [e1, e2, hf0, hf1])
        · exfalso
          have h1 := seg_mem g1.le x
          have h2 := seg_mem g1.le y
          rw [h.2] at h2
          rw [h.1] at h1
          have e1 : g.1 = 0 := le_antisymm h2.1 unitInterval.nonneg'
          have e2 : g.2 = 1 := le_antisymm unitInterval.le_one' h1.2
          exact hab (by rw [e1, e2, hf0, hf1])
      have harc : IsArcMap e := ⟨e.continuous, hei⟩
      have hLe : IsLineWithEnds (range e) (f g.1) (f g.2) := by
        have h1 := harc.isLineWithEnds
        have h2 : e 0 = f g.1 := e.source
        have h3 : e 1 = f g.2 := e.target
        rwa [h2, h3] at h1
      have hmemA : ∀ x, ∀ y, e x = y → (y ∉ D ∧ y ∈ F) ∨ y = f g.1 ∨ y = f g.2 := fun x y h => by
        have h1 := seg_mem g1.le x
        have h2 : y = f (seg g.1 g.2 x) := h.symm
        rcases eq_or_lt_of_le h1.1 with h3 | h3
        · right; left
          rw [h2, ← h3]
        rcases eq_or_lt_of_le h1.2 with h4 | h4
        · right; right
          rw [h2, h4]
        · left
          exact h2 ▸ ⟨g4 ⟨h3, h4⟩, hfF _⟩
      have hend : ∀ {L : Set T} {u v : T}, IsLineWithEnds L u v → u ∈ L ∧ v ∈ L := by
        rintro L u v ⟨k, h0, h1⟩
        exact ⟨h0 ▸ (k 0).2, h1 ▸ (k 1).2⟩
      have hinter : range e ∩ P (f g.1) (f g.2) = {f g.1, f g.2} := by
        ext y
        constructor
        · rintro ⟨⟨x, hx⟩, hyP⟩
          rcases hmemA x y hx with h | h | h
          · exact absurd (hPs hyP) h.1
          · exact .inl h
          · exact .inr h
        · rintro (rfl | rfl)
          · exact ⟨(hend hLe).1, (hend hL).1⟩
          · exact ⟨(hend hLe).2, (hend hL).2⟩
      have hO := oArc_of_lines hLe hL hinter
      have hnull : IsNullHomotopicOArc (range e ∪ P (f g.1) (f g.2)) := by_contra fun hn => (hno
        (range e ∪ P (f g.1) (f g.2)) _ _ hO hn ⟨hfF _, hb1⟩ ⟨hfF _, hb2⟩ subset_union_right (by
        rintro y (⟨x, hx⟩ | hy)
        · rcases hmemA x y hx with h | h | h
          · exact .inl ⟨h.2, h.1⟩
          · exact .inr (h ▸ (hend hL).1)
          · exact .inr (h ▸ (hend hL).2)
        · exact .inr hy))
      let loop := e.trans q.symm
      let γ : C(Circle, T) := loopLift 1 loop.toContinuousMap (by simp)
      have hγ : ∀ t, γ (arcParam 1 t) = loop t := fun t => loopLift_apply 1 _ _ t
      have hrange : range γ = range e ∪ P (f g.1) (f g.2) := by
        have heq : range γ = range loop := by
          ext x
          constructor
          · rintro ⟨z, rfl⟩
            obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
            exact ⟨s, (hγ s).symm⟩
          · rintro ⟨s, rfl⟩
            exact ⟨arcParam 1 s, hγ s⟩
        rw [heq, Path.trans_range, Path.symm_range, hqr]
      refine ⟨q, ?_, homotopic_of_trans_symm (path_refl_of_null loop hγ
        (null_of_param hnull γ hrange))⟩
      rw [hqr]
      exact fun y hy => (hsub (hPs hy)).1
  obtain ⟨q, hq, hh⟩ := homotopic_of_intervals f Δ G.card G le_rfl 0 1 unitInterval.nonneg'
    (by rw [hf0]; exact (hsub hp₀D).1)
    (by rw [hf1]; exact (hsub hp₀D).1) (fun g hg => by
      obtain ⟨g1, g2, g3, g4⟩ := hG g hg
      exact ⟨unitInterval.nonneg', g1, unitInterval.le_one', (hsub (not_not.mp g2)).1,
        (hsub (not_not.mp g3)).1, hgood g hg⟩) hdis
    (fun x _ hno' => by
      by_contra hx
      have hK : x ∈ f ⁻¹' (Δ \ discBd Δ)ᶜ := fun h' => hx h'.1
      obtain ⟨g, hg, hgx⟩ := hcov x hK
      exact hno' g hg hgx)
  have hcast := cast_refl_of_disc hΔ (hf0.trans hf1.symm) (subP f 0 1) q hq hh
  apply hnn
  refine ⟨φ, null_of_path_refl _ (fun t => ?_) hcast⟩
  change f t = f (seg 0 1 t)
  rw [seg_zero_one]

end GraphMinor.GM19
