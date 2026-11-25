/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section11a
import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.GM07.Section11c
import LeanPool.GraphMinor.GM07.Section11d
import LeanPool.GraphMinor.GM07.Section11e
import LeanPool.GraphMinor.GM07.Section11g
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.Epstein
import LeanPool.GraphMinor.Surface.OpenDisc
import LeanPool.GraphMinor.Surface.SphereDisc
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Graph Minors VII, Section 11: Topological Appendix

This file formalizes the topological results of Section 11 (Appendix, pages 249–254) of
N. Robertson and P. D. Seymour, *Graph Minors. VII. Disjoint paths on a surface*,
J. Combin. Theory Ser. B 45 (1988) 212–254:
- Relating `subBd Δ` and `discBd Δ` for a closed disc `Δ` in a surface `S`
  (`subBd_subset_discBd`, `subBd_eq_discBd_of_disjoint_bd`, `subBd_eq_discBd_of_bd_eq_empty`).
- `theorem_11_1`: (11.1), every continuous path in a surface with distinct ends contains a
  `[0, 1]`-arc with the same ends, deduced from `Surface.exists_arc_of_path`.
- Equivalence between arc-connectedness (`IsArcConnected`) and path-connectedness (`JoinedIn`,
  `IsPathConnected`) in any Hausdorff space (`joinedIn_iff_eq_or_exists_isLineWithEnds`,
  `isArcConnected_iff_joinedIn`).
- `theorem_11_2`: (11.2), every non-null-homotopic closed curve in a surface contains a
  non-null-homotopic `O`-arc, together with its contrapositive
  `isFlat_of_forall_isNullHomotopicOArc`
  and the corollary `IsSimplyConnectedSubset.isFlat`.
- `theorem_11_3`: (11.3), pushing a closed curve out of `Δ \ bd(Δ)` into `Y` when `Y ∩ bd(Δ)` is
  arc-connected, and deducing unconditionally from the first part via
  `ClosedCurvesHomotopicIn.trans`
  that if `Y` is flat then `Y ∪ (Δ \ bd(Δ))` is flat.
- `theorem_11_4`: (11.4), every connected and locally arc-connected subset of a surface is
  arc-connected.
- `theorem_11_5`: (11.5), every flat locally arc-connected subset `Z ⊆ Σ` is contained in an open,
  flat, locally arc-connected subset `Y ⊆ Σ` (arc-connected if `Z` is).
- `theorem_11_6`: (11.6), the union of two solid subsets of a surface is solid.
- `theorem_11_7`: (11.7), every solid flat subset `Z` of a connected surface is contained in a
  solid, flat, arc-connected subset `Y` (including unconditional proof that a solid subset has
  finitely many arc-components, `arcComponentsIn_finite_of_isSolid`).
- `theorem_11_8` and `theorem_11_8_closed`: (11.8), every open, flat, arc-connected subset `Z ⊆ Σ`
  is contained in an open simply connected subset `Y ⊆ Σ`, proved via Zorn's lemma
  (`exists_maximal_open_flat_arcConnected`), disc bounding (`EpsteinStatement`), and (11.3).
- `theorem_11_9` and `theorem_11_9_closed`: (11.9), deduced from (11.7), (11.5), and (11.8).
- `theorem_11_10_closed` and `theorem_11_10`: (11.10), deduced from (11.9), (4.2)
  (`OpenDiscStatement`), and unconditional proofs that any closed subset of an open disc is planar
  (`isPlanar_of_isClosed_subset_isOpenDisc`) and any proper closed subset of a sphere is planar
  (`isPlanar_of_isSphere_ne_univ`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric unitInterval OnePoint
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Boundary of a Closed Disc: `subBd Δ` versus `discBd Δ` -/

/-- A surface with empty boundary is a closed surface (`IsClosedSurface`). -/
theorem isClosedSurface_of_bd_eq_empty (hS : IsSurface S) (hbd : bd S = ∅) :
    IsClosedSurface S :=
  ⟨hS.1, hS.2.1, fun x => not_not.mp (eq_empty_iff_forall_notMem.mp hbd x)⟩

/-- For any closed disc `Δ` in a surface `S`, the topological frontier `subBd Δ` is contained in the
manifold boundary `discBd Δ`. -/
theorem subBd_subset_discBd (hS : IsSurface S) {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    subBd Δ ⊆ discBd Δ := by
  have : T2Space S := hS.2.1
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  obtain ⟨hunion, _⟩ := c.union_ball
  have hopen : IsOpen (g '' ball 0 1) := c.isOpen_image_ball hS.2.2
  have hcl : closure Δ = Δ := hΔ.isCompact.isClosed.closure_eq
  rintro x ⟨hxcl, hxcompl⟩
  rw [hcl, ← hunion] at hxcl
  rcases hxcl with hxball | hxbd
  · exfalso
    obtain ⟨y, hyball, hycompl⟩ := mem_closure_iff.mp hxcompl (g '' ball 0 1) hopen hxball
    have hyΔ : y ∈ Δ := by
      rw [← hunion]
      exact Or.inl hyball
    exact hycompl.2 hyΔ
  · exact hxbd

/-- In a surface `S`, if a closed disc `Δ` has `discBd Δ` disjoint from `bd S`, then its topological
frontier `subBd Δ` equals `discBd Δ`. -/
theorem subBd_eq_discBd_of_disjoint_bd (hS : IsSurface S) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hdisj : Disjoint (discBd Δ) (bd S)) :
    subBd Δ = discBd Δ := by
  refine Subset.antisymm (subBd_subset_discBd hS hΔ) ?_
  rintro x hxbd
  have hxΔ : x ∈ Δ := discBd_subset Δ hxbd
  refine ⟨subset_closure hxΔ, ?_⟩
  by_contra hxnot
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hx_sph : h x ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem h hxbd
  have hx_norm : ‖h x‖ = 1 := mem_sphere_zero_iff_norm.mp hx_sph
  have hx_intS : IsInteriorPoint x := not_not.mp (hdisj.notMem_of_mem_left hxbd)
  obtain ⟨W, hW, hxW, ⟨f⟩⟩ := hx_intS
  have : Nonempty S := ⟨x⟩
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  obtain ⟨a, a', h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (b.trans f.symm)
  let V : Set S := (closure (univ \ Δ))ᶜ
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl
  have hxV : x ∈ V := hxnot
  have hVsub : V ⊆ Δ := fun y hy => by
    by_contra hyΔ
    exact hy (subset_closure ⟨mem_univ y, hyΔ⟩)
  let M : Set ℂ := ball (0 : ℂ) 1 ∩ a ⁻¹' (W ∩ V)
  have hM : IsOpen M := h1.isOpen_inter_preimage isOpen_ball (hW.inter hVopen)
  have hG : ContinuousOn (h ∘ a) M :=
    c.hc.comp (h1.mono inter_subset_left) fun z hz => hVsub hz.2.2
  have hGi : InjOn (h ∘ a) M := fun z hz w hw he =>
    h5.injOn hz.1 hw.1 (c.gh.injOn (hVsub hz.2.2) (hVsub hw.2.2) he)
  have hopen : IsOpen ((h ∘ a) '' M) := isOpen_image_of_injOn hM hG hGi
  have hmem : h x ∈ (h ∘ a) '' M := by
    refine ⟨a' x, ⟨h4 hxW, ?_⟩, ?_⟩
    · change a (a' x) ∈ W ∩ V
      rw [h6 hxW]
      exact ⟨hxW, hxV⟩
    · change h (a (a' x)) = h x
      rw [h6 hxW]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (h x) hmem
  let z : ℂ := ((1 + ε / 2 : ℝ) : ℂ) * h x
  have hz_ball : z ∈ ball (h x) ε := by
    rw [mem_ball, dist_eq_norm]
    have hsub : z - h x = ((ε / 2 : ℝ) : ℂ) * h x := by
      simp only [z]
      push_cast
      ring
    rw [hsub, norm_mul, hx_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  obtain ⟨v, hvM, hvz⟩ := hball hz_ball
  have hz_cb : z ∈ closedBall (0 : ℂ) 1 := by
    rw [← hvz]
    exact c.hm (hVsub hvM.2.2)
  have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz_cb
  have hz_norm : ‖z‖ = 1 + ε / 2 := by
    simp only [z, norm_mul, hx_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  linarith

/-- In a surface `S` with `bd S = ∅`, `subBd Δ = discBd Δ` for every closed disc `Δ`. -/
theorem subBd_eq_discBd_of_bd_eq_empty (hS : IsSurface S) (hbd : bd S = ∅)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    subBd Δ = discBd Δ := by
  refine subBd_eq_discBd_of_disjoint_bd hS hΔ ?_
  rw [hbd]
  exact disjoint_empty _

/-! ## (11.1): Arcs in Paths and Equivalence of Arc-Connectedness with Path-Connectedness -/

/-- Graph Minors VII, (11.1) (page 249):
"If $\Sigma$ is a surface and $\phi \colon [0, 1] \to \Sigma$ is continuous with $\phi(0) \ne
\phi(1)$, there is a $[0, 1]$-arc included in $|\phi|$ with ends $\phi(0), \phi(1)$." -/
theorem theorem_11_1_proof (hS : IsSurface S) (φ : C(unitInterval, S)) (hne : φ 0 ≠ φ 1) :
    ∃ L : Set S, L ⊆ range φ ∧ IsLineWithEnds L (φ 0) (φ 1) := by
  have : T2Space S := hS.2.1
  obtain ⟨e, he_cont, he_inj, he0, he1, he_sub⟩ := exists_arc_of_path φ.continuous hne
  have he_emb : IsEmbedding e := (he_cont.isClosedEmbedding he_inj).isEmbedding
  exact ⟨range e, he_sub, he_emb.toHomeomorph, he0, he1⟩

/-- In a Hausdorff space, two points `a, b ∈ Z` are joined by a path in `Z` (`JoinedIn Z a b`) if
and only if `a = b` or there is a `[0, 1]`-arc in `Z` with ends `a, b`. -/
theorem joinedIn_iff_eq_or_exists_isLineWithEnds [T2Space S] {Z : Set S} {a b : S}
    (ha : a ∈ Z) (hb : b ∈ Z) :
    JoinedIn Z a b ↔ a = b ∨ ∃ L : Set S, L ⊆ Z ∧ IsLineWithEnds L a b := by
  constructor
  · intro h
    rcases eq_or_ne a b with rfl | hne
    · exact Or.inl rfl
    · obtain ⟨γ, hγ⟩ := h
      obtain ⟨e, he_cont, he_inj, he0, he1, he_sub⟩ :=
        exists_arc_of_path γ.continuous (by simpa [γ.source, γ.target] using hne)
      have he_emb : IsEmbedding e := (he_cont.isClosedEmbedding he_inj).isEmbedding
      refine Or.inr ⟨range e, ?_, he_emb.toHomeomorph, ?_, ?_⟩
      · intro x hx
        obtain ⟨t, rfl⟩ := he_sub hx
        exact hγ t
      · exact he0.trans γ.source
      · exact he1.trans γ.target
  · rintro (rfl | ⟨L, hLZ, f, hf0, hf1⟩)
    · exact JoinedIn.refl ha
    · let p : Path a b :=
        { toContinuousMap := ⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩
          source' := hf0
          target' := hf1 }
      exact ⟨p, fun t => hLZ (f t).2⟩

/-- In a Hausdorff space, `IsArcConnected Z` is equivalent to `∀ a ∈ Z, ∀ b ∈ Z, JoinedIn Z a b`. -/
theorem isArcConnected_iff_joinedIn [T2Space S] {Z : Set S} :
    IsArcConnected Z ↔ ∀ a ∈ Z, ∀ b ∈ Z, JoinedIn Z a b := by
  constructor
  · intro h a ha b hb
    rw [joinedIn_iff_eq_or_exists_isLineWithEnds ha hb]
    rcases eq_or_ne a b with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (h a ha b hb hne)
  · intro h a ha b hb hne
    have hj := (joinedIn_iff_eq_or_exists_isLineWithEnds ha hb).mp (h a ha b hb)
    exact hj.resolve_left hne

/-- In a Hausdorff space, a path-connected subset is arc-connected. -/
theorem IsPathConnected.isArcConnected [T2Space S] {Z : Set S} (hZ : IsPathConnected Z) :
    IsArcConnected Z :=
  isArcConnected_iff_joinedIn.mpr fun _ ha _ hb => hZ.joinedIn _ ha _ hb

/-- In a Hausdorff space, a nonempty subset is arc-connected if and only if it is path-connected. -/
theorem isArcConnected_iff_isPathConnected [T2Space S] {Z : Set S} (hne : Z.Nonempty) :
    IsArcConnected Z ↔ IsPathConnected Z := by
  refine ⟨fun h => ?_, IsPathConnected.isArcConnected⟩
  obtain ⟨x₀, hx₀⟩ := hne
  exact ⟨x₀, hx₀, fun {y} hy => isArcConnected_iff_joinedIn.mp h x₀ hx₀ y hy⟩

/-- In a Hausdorff space, every arc-connected subset is preconnected. -/
theorem IsArcConnected.isPreconnected [T2Space S] {Z : Set S} (hZ : IsArcConnected Z) :
    IsPreconnected Z := by
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · exact isPreconnected_empty
  · exact ((isArcConnected_iff_isPathConnected hne).mp hZ).isConnected.isPreconnected

/-- In a Hausdorff space, `pathComponentIn Z a` is arc-connected for every `a`. -/
theorem isArcConnected_pathComponentIn [T2Space S] (Z : Set S) (a : S) :
    IsArcConnected (pathComponentIn Z a) := by
  by_cases ha : a ∈ Z
  · exact IsPathConnected.isArcConnected (isPathConnected_pathComponentIn ha)
  · intro x hx
    exact absurd (pathComponentIn_subset hx) fun _ => ha (by
      obtain ⟨p, hp⟩ := hx
      rw [← p.source]
      exact hp 0)

/-- In a Hausdorff space, every `O`-arc is arc-connected. -/
theorem IsOArc.isArcConnected [T2Space S] {F : Set S} (hF : IsOArc F) :
    IsArcConnected F := by
  obtain ⟨φ⟩ := hF
  have hIcc : IsPathConnected (Icc (0 : ℝ) (2 * Real.pi)) :=
    (convex_Icc (0 : ℝ) (2 * Real.pi)).isPathConnected ⟨0, left_mem_Icc.mpr (by positivity)⟩
  let g : ℝ → S := fun t => (φ (Circle.exp t)).1
  have hg : Continuous g :=
    continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
  have himg : g '' Icc 0 (2 * Real.pi) = F := by
    ext x
    constructor
    · rintro ⟨t, _, rfl⟩
      exact (φ _).2
    · intro hxF
      have h2pi : (0 : ℝ) < 2 * Real.pi := mul_pos two_pos Real.pi_pos
      let z : Circle := φ.symm ⟨x, hxF⟩
      let t : ℝ := toIcoMod h2pi 0 (Complex.arg z)
      have ht_mem : t ∈ Icc 0 (2 * Real.pi) :=
        ⟨(toIcoMod_mem_Ico h2pi 0 (Complex.arg z)).1,
          by linarith [(toIcoMod_mem_Ico h2pi 0 (Complex.arg z)).2]⟩
      have hexp : Circle.exp t = z := by
        have h1 : t = Complex.arg z - toIcoDiv h2pi 0 (Complex.arg z) • (2 * Real.pi) := rfl
        have h2 : Circle.exp t = Circle.exp (Complex.arg z) := by
          rw [h1, zsmul_eq_mul]
          exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg z), by push_cast; ring⟩
        exact h2.trans (Circle.exp_arg z)
      refine ⟨t, ht_mem, ?_⟩
      change (φ (Circle.exp t)).1 = x
      rw [hexp, φ.apply_symm_apply]
  have hF_pc : IsPathConnected F := himg ▸ hIcc.image hg
  exact IsPathConnected.isArcConnected hF_pc

/-! ## (11.2) and (11.3): Non-Null-Homotopic `O`-Arcs and Disc-Interior Pushout -/

/-- Graph Minors VII, (11.2) (page 249):
"If $\Sigma$ is a surface, and $\phi \colon S^1 \to \Sigma$ is continuous and non-null-homotopic,
there is a non-null-homotopic $O$-arc included in $|\phi|$." -/
theorem theorem_11_2_proof
    (hS : IsSurface S) (φ : C(Circle, S))
    (hφ : ¬ ClosedCurveIsNullHomotopicIn univ φ) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArc F :=
  nonNullHomotopicOArc_in_curve hS φ hφ

/-- Contrapositive of (11.2): a subset `Z ⊆ S` is flat if every `O`-arc `F ⊆ Z` is null-homotopic
in `S`. -/
theorem isFlat_of_forall_isNullHomotopicOArc
    (hS : IsSurface S) {Z : Set S}
    (h : ∀ F : Set S, F ⊆ Z → IsOArc F → IsNullHomotopicOArc F) :
    IsFlat Z := by
  intro φ hφZ
  by_contra hnot
  obtain ⟨F, hF_oarc, hF_range, hF_not_null⟩ := theorem_11_2_proof hS φ hnot
  exact hF_not_null (h F (hF_range.trans hφZ) hF_oarc)

/-- "By (11.2), a simply connected set is flat." (Graph Minors VII, Section 11, page 253). -/
theorem IsSimplyConnectedSubset.isFlat
    (hS : IsSurface S) {Z : Set S} (hZ : IsSimplyConnectedSubset Z) :
    IsFlat Z := by
  refine isFlat_of_forall_isNullHomotopicOArc hS fun F hFZ hF => ?_
  obtain ⟨Δ, hΔ, hΔ_bd, _⟩ := hZ.2 F hF hFZ
  have hFΔ : F ⊆ Δ := hΔ_bd ▸ discBd_subset Δ
  exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ Δ) hΔ hFΔ

/-- Transitivity of `ClosedCurvesHomotopicIn Z` for closed curves `φ₀, φ₁, φ₂ : C(Circle, S)`. -/
theorem ClosedCurvesHomotopicIn.trans {Z : Set S} {φ₀ φ₁ φ₂ : C(Circle, S)}
    (h₁ : ClosedCurvesHomotopicIn Z φ₀ φ₁) (h₂ : ClosedCurvesHomotopicIn Z φ₁ φ₂) :
    ClosedCurvesHomotopicIn Z φ₀ φ₂ :=
  Surface.ClosedCurvesHomotopicIn.trans h₁ h₂

/-- Graph Minors VII, (11.3) (page 249):
"Let $\Sigma$ be a connected surface, let $\Delta \subseteq \Sigma$ be a closed disc, and let $Y
\subseteq \Sigma$ be such that $Y \cap bd(\Delta)$ is arc-connected. Then any continuous map $\phi
\colon S^1 \to Y \cup (\Delta - bd(\Delta))$ is homotopic to a map $\psi \colon S^1 \to Y$ with
$|\psi| \subseteq |\phi| \cup bd(\Delta)$. In particular, if $Y$ is flat then so is $Y \cup (\Delta
- bd(\Delta))$." -/
theorem theorem_11_3_proof
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ)) :
    (∀ φ : C(Circle, S), range φ ⊆ Y ∪ (Δ \ discBd Δ) →
      ((∃ z : Circle, φ z ∉ Δ \ discBd Δ) ∨ (Y ∩ discBd Δ).Nonempty) →
      ∃ ψ : C(Circle, S), range ψ ⊆ Y ∧ range ψ ⊆ range φ ∪ discBd Δ ∧
        ClosedCurvesHomotopicIn univ φ ψ) ∧
    (IsFlat Y → IsFlat (Y ∪ (Δ \ discBd Δ))) :=
  ⟨fun φ hφ hne => disc_interior_curve_homotopy hS hΔ hY_arc φ hφ hne,
   fun hY_flat => isFlat_union_disc_diff_discBd hS hΔ hY_arc hY_flat⟩

/-! ## (11.4): Connected and Locally Arc-Connected Implies Arc-Connected -/

/-- Graph Minors VII, (11.4) (page 251):
"If $Z$ is connected and l.a.c. then $Z$ is arc-connected." -/
theorem theorem_11_4_proof (hS : IsSurface S) {Z : Set S}
    (hconn : IsConnected Z) (hlac : IsLocallyArcConnected Z) :
    IsArcConnected Z := by
  have : T2Space S := hS.2.1
  obtain ⟨z₀, hz₀⟩ := hconn.1
  set A : Set S := pathComponentIn Z z₀
  set B : Set S := Z \ A
  have hA_sub : A ⊆ Z := pathComponentIn_subset
  have hAB_union : Z ⊆ A ∪ B := fun x hx => by
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨hx, hxA⟩
  have hz₀A : z₀ ∈ A := mem_pathComponentIn_self hz₀
  have hA_open_in_Z : ∀ x ∈ A, ∃ C : Set S, IsOpen C ∧ x ∈ C ∧ Z ∩ C ⊆ A := by
    intro x hxA
    obtain ⟨C, _, hxC, hC_open, hZC_arc⟩ := hlac x (hA_sub hxA) univ isOpen_univ (mem_univ x)
    refine ⟨C, hC_open, hxC, fun y hy => ?_⟩
    have hj : JoinedIn (Z ∩ C) x y :=
      isArcConnected_iff_joinedIn.mp hZC_arc x ⟨hA_sub hxA, hxC⟩ y hy
    exact JoinedIn.trans hxA (hj.mono inter_subset_left)
  have hB_open_in_Z : ∀ x ∈ B, ∃ C : Set S, IsOpen C ∧ x ∈ C ∧ Z ∩ C ⊆ B := by
    intro x hxB
    obtain ⟨C, _, hxC, hC_open, hZC_arc⟩ := hlac x hxB.1 univ isOpen_univ (mem_univ x)
    refine ⟨C, hC_open, hxC, fun y hy => ⟨hy.1, fun hyA => hxB.2 ?_⟩⟩
    have hj : JoinedIn (Z ∩ C) y x :=
      isArcConnected_iff_joinedIn.mp hZC_arc y hy x ⟨hxB.1, hxC⟩
    exact JoinedIn.trans hyA (hj.mono inter_subset_left)
  set U_A : Set S := ⋃ (x : S) (hx : x ∈ A), (hA_open_in_Z x hx).choose
  set U_B : Set S := ⋃ (x : S) (hx : x ∈ B), (hB_open_in_Z x hx).choose
  have hUA_open : IsOpen U_A :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx => (hA_open_in_Z x hx).choose_spec.1
  have hUB_open : IsOpen U_B :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx => (hB_open_in_Z x hx).choose_spec.1
  have hA_sub_UA : A ⊆ U_A := fun x hx =>
    mem_iUnion₂.mpr ⟨x, hx, (hA_open_in_Z x hx).choose_spec.2.1⟩
  have hB_sub_UB : B ⊆ U_B := fun x hx =>
    mem_iUnion₂.mpr ⟨x, hx, (hB_open_in_Z x hx).choose_spec.2.1⟩
  have hZ_sub : Z ⊆ U_A ∪ U_B := fun x hx =>
    (hAB_union hx).imp (fun hxA => hA_sub_UA hxA) (fun hxB => hB_sub_UB hxB)
  have hZ_UA_sub_A : Z ∩ U_A ⊆ A := by
    rintro y ⟨hyZ, hyUA⟩
    obtain ⟨x, hx, hyC⟩ := mem_iUnion₂.mp hyUA
    exact (hA_open_in_Z x hx).choose_spec.2.2 ⟨hyZ, hyC⟩
  have hZ_UB_sub_B : Z ∩ U_B ⊆ B := by
    rintro y ⟨hyZ, hyUB⟩
    obtain ⟨x, hx, hyC⟩ := mem_iUnion₂.mp hyUB
    exact (hB_open_in_Z x hx).choose_spec.2.2 ⟨hyZ, hyC⟩
  have hB_empty : B = ∅ := by
    by_contra hB_ne
    obtain ⟨b, hbB⟩ := nonempty_iff_ne_empty.mpr hB_ne
    obtain ⟨w, hwZ, hwUA, hwUB⟩ := hconn.2 U_A U_B hUA_open hUB_open hZ_sub
      ⟨z₀, hz₀, hA_sub_UA hz₀A⟩ ⟨b, hbB.1, hB_sub_UB hbB⟩
    exact (hZ_UB_sub_B ⟨hwZ, hwUB⟩).2 (hZ_UA_sub_A ⟨hwZ, hwUA⟩)
  have hZA : Z = A := Subset.antisymm (fun x hx => (hAB_union hx).resolve_right
    (by simp [hB_empty])) hA_sub
  rw [hZA]
  exact isArcConnected_pathComponentIn Z z₀

/-! ## (11.5): Open Flat Locally Arc-Connected Superset -/

/-- Graph Minors VII, (11.5) (page 251):
"If $Z \subseteq \Sigma$ is flat and l.a.c., there is an open, flat, l.a.c. set $Y \subseteq \Sigma$
with $Z \subseteq Y$, which may be chosen arc-connected if $Z$ is arc-connected." -/
theorem theorem_11_5_proof
    (hS : IsSurface S) {Z : Set S} (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsFlat Y ∧ IsLocallyArcConnected Y ∧
      (IsArcConnected Z → IsArcConnected Y) :=
  flat_locallyArcConnected_open_superset hS hZ_flat hZ_lac

/-! ## (11.6): Union of Solid Sets is Solid -/

/-- Graph Minors VII, (11.6) (page 252):
"If $Z_1, Z_2 \subseteq \Sigma$ are solid, so is $Z_1 \cup Z_2$." -/
theorem theorem_11_6_proof (hS : IsSurface S) {Z₁ Z₂ : Set S}
    (h₁ : IsSolid Z₁) (h₂ : IsSolid Z₂) :
    IsSolid (Z₁ ∪ Z₂) := by
  have : T2Space S := hS.2.1
  refine ⟨?_, h₁.2.union h₂.2⟩
  intro z hz A hA_open hzA
  set X : Set S := pathComponentIn ((Z₁ ∪ Z₂) ∩ A) z
  have hzX : z ∈ X := mem_pathComponentIn_self ⟨hz, hzA⟩
  have hX_sub : X ⊆ (Z₁ ∪ Z₂) ∩ A := pathComponentIn_subset
  have hex₁ : ∀ x ∈ X, ∃ A₁ : Set S, A₁ ⊆ A ∧ x ∈ A₁ ∧ IsOpen A₁ ∧ Z₁ ∩ A₁ ⊆ X := by
    intro x hxX
    by_cases hx₁ : x ∈ Z₁
    · obtain ⟨A₁, hA₁_sub, hxA₁, hA₁_open, hZ₁A₁_arc⟩ :=
        h₁.1 x hx₁ A hA_open (hX_sub hxX).2
      refine ⟨A₁, hA₁_sub, hxA₁, hA₁_open, fun y hy => ?_⟩
      have hj : JoinedIn (Z₁ ∩ A₁) x y :=
        isArcConnected_iff_joinedIn.mp hZ₁A₁_arc x ⟨hx₁, hxA₁⟩ y hy
      refine JoinedIn.trans hxX (hj.mono fun w hw => ⟨Or.inl hw.1, hA₁_sub hw.2⟩)
    · refine ⟨A \ Z₁, sdiff_subset, ⟨(hX_sub hxX).2, hx₁⟩, hA_open.sdiff h₁.2, ?_⟩
      rintro y ⟨hy₁, _, hynot₁⟩
      exact absurd hy₁ hynot₁
  have hex₂ : ∀ x ∈ X, ∃ A₂ : Set S, A₂ ⊆ A ∧ x ∈ A₂ ∧ IsOpen A₂ ∧ Z₂ ∩ A₂ ⊆ X := by
    intro x hxX
    by_cases hx₂ : x ∈ Z₂
    · obtain ⟨A₂, hA₂_sub, hxA₂, hA₂_open, hZ₂A₂_arc⟩ :=
        h₂.1 x hx₂ A hA_open (hX_sub hxX).2
      refine ⟨A₂, hA₂_sub, hxA₂, hA₂_open, fun y hy => ?_⟩
      have hj : JoinedIn (Z₂ ∩ A₂) x y :=
        isArcConnected_iff_joinedIn.mp hZ₂A₂_arc x ⟨hx₂, hxA₂⟩ y hy
      refine JoinedIn.trans hxX (hj.mono fun w hw => ⟨Or.inr hw.1, hA₂_sub hw.2⟩)
    · refine ⟨A \ Z₂, sdiff_subset, ⟨(hX_sub hxX).2, hx₂⟩, hA_open.sdiff h₂.2, ?_⟩
      rintro y ⟨hy₂, _, hynot₂⟩
      exact absurd hy₂ hynot₂
  set A' : Set S := ⋃ (x : S) (hx : x ∈ X), (hex₁ x hx).choose ∩ (hex₂ x hx).choose
  have hA'_sub : A' ⊆ A :=
    iUnion₂_subset fun x hx => inter_subset_left.trans (hex₁ x hx).choose_spec.1
  have hzA' : z ∈ A' :=
    mem_iUnion₂.mpr ⟨z, hzX, (hex₁ z hzX).choose_spec.2.1, (hex₂ z hzX).choose_spec.2.1⟩
  have hA'_open : IsOpen A' :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx =>
      (hex₁ x hx).choose_spec.2.2.1.inter (hex₂ x hx).choose_spec.2.2.1
  have h_inter_eq : (Z₁ ∪ Z₂) ∩ A' = X := by
    refine Subset.antisymm ?_ (fun x hx => ⟨(hX_sub hx).1,
      mem_iUnion₂.mpr ⟨x, hx, (hex₁ x hx).choose_spec.2.1, (hex₂ x hx).choose_spec.2.1⟩⟩)
    rintro y ⟨hyZ, hyA'⟩
    obtain ⟨x, hx, hy₁, hy₂⟩ := mem_iUnion₂.mp hyA'
    rcases hyZ with hyZ₁ | hyZ₂
    · exact (hex₁ x hx).choose_spec.2.2.2 ⟨hyZ₁, hy₁⟩
    · exact (hex₂ x hx).choose_spec.2.2.2 ⟨hyZ₂, hy₂⟩
  refine ⟨A', hA'_sub, hzA', hA'_open, ?_⟩
  rw [h_inter_eq]
  exact isArcConnected_pathComponentIn ((Z₁ ∪ Z₂) ∩ A) z

/-! ## (11.7): Finiteness of Arc-Components of Solid Sets and Solid Flat Arc-Connected Superset -/

/-- `arcComponentsIn Z` is the image of `Z` under `pathComponentIn Z`. -/
theorem arcComponentsIn_eq_image_pathComponentIn (Z : Set S) :
    arcComponentsIn Z = (pathComponentIn Z) '' Z := by
  ext C
  constructor
  · rintro ⟨⟨x, hxC⟩, hCZ, hC_pc, hC_max⟩
    have hxZ : x ∈ Z := hCZ hxC
    refine ⟨x, hxZ, ?_⟩
    exact hC_max (pathComponentIn Z x) pathComponentIn_subset (isPathConnected_pathComponentIn hxZ)
      (hC_pc.subset_pathComponentIn hxC hCZ)
  · rintro ⟨x, hxZ, rfl⟩
    exact pathComponentIn_mem_arcComponentsIn hxZ

/-- Every solid subset of a surface has only finitely many arc-components. This formalizes the
first step of the proof of Graph Minors VII, (11.7) (page 253): "Hence $Z$ has only finitely many
arc-components." -/
theorem arcComponentsIn_finite_of_isSolid (hS : IsSurface S) {Z : Set S} (hZ : IsSolid Z) :
    (arcComponentsIn Z).Finite := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hZ_compact : IsCompact Z := hZ.2.isCompact
  have hex : ∀ z : S, ∃ A : Set S, IsOpen A ∧ z ∈ A ∧ (z ∈ Z → IsArcConnected (Z ∩ A)) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨A, _, hzA, hA_open, hZA_arc⟩ := hZ.1 z hz univ isOpen_univ (mem_univ z)
      exact ⟨A, hA_open, hzA, fun _ => hZA_arc⟩
    · exact ⟨univ, isOpen_univ, mem_univ z, fun hz' => absurd hz' hz⟩
  choose A hA_open hzA hZA_arc using hex
  have hcov : Z ⊆ ⋃ z ∈ Z, A z := fun z hz => mem_iUnion₂.mpr ⟨z, hz, hzA z⟩
  obtain ⟨t, htZ, ht_fin, ht_cov⟩ :=
    hZ_compact.elim_finite_subcover_image (fun z _ => hA_open z) hcov
  rw [arcComponentsIn_eq_image_pathComponentIn]
  refine (ht_fin.image (pathComponentIn Z)).subset ?_
  rintro _ ⟨y, hyZ, rfl⟩
  obtain ⟨z, hzt, hyAz⟩ := mem_iUnion₂.mp (ht_cov hyZ)
  have hzZ : z ∈ Z := htZ hzt
  have hj : JoinedIn (Z ∩ A z) z y :=
    isArcConnected_iff_joinedIn.mp (hZA_arc z hzZ) z ⟨hzZ, hzA z⟩ y ⟨hyZ, hyAz⟩
  have hjZ : JoinedIn Z z y := hj.mono inter_subset_left
  refine ⟨z, hzt, ?_⟩
  exact (pathComponentIn_congr hjZ).symm

/-- If `arcComponentsIn Z` is finite and has `ncard ≤ 1`, then `Z` is arc-connected. -/
theorem isArcConnected_of_arcComponentsIn_ncard_le_one [T2Space S] {Z : Set S}
    (hfin : (arcComponentsIn Z).Finite) (hle : (arcComponentsIn Z).ncard ≤ 1) :
    IsArcConnected Z := by
  rw [isArcConnected_iff_joinedIn]
  intro a ha b hb
  have haC : pathComponentIn Z a ∈ arcComponentsIn Z := pathComponentIn_mem_arcComponentsIn ha
  have hbC : pathComponentIn Z b ∈ arcComponentsIn Z := pathComponentIn_mem_arcComponentsIn hb
  have heq : pathComponentIn Z a = pathComponentIn Z b :=
    (Set.ncard_le_one_iff hfin).mp hle haC hbC
  have hb_mem : b ∈ pathComponentIn Z a := heq ▸ mem_pathComponentIn_self hb
  exact hb_mem

/-- Every singleton in a Hausdorff space is solid. -/
theorem isSolid_singleton [T2Space S] (x : S) : IsSolid ({x} : Set S) := by
  refine ⟨fun z hz A hA_open hzA => ⟨A, Subset.rfl, hzA, hA_open, ?_⟩, isClosed_singleton⟩
  intro a ha b hb hne
  rw [mem_singleton_iff.mp ha.1, mem_singleton_iff.mp hb.1] at hne
  exact absurd rfl hne

/-- Every singleton is flat. -/
theorem isFlat_singleton (x : S) : IsFlat ({x} : Set S) := by
  intro φ hφ
  refine ⟨x, mem_univ x, ⟨ContinuousMap.const (Circle × unitInterval) x, fun _ => mem_univ x, ?_,
    ?_⟩⟩
  · intro z
    exact (mem_singleton_iff.mp (hφ (mem_range_self z))).symm
  · intro _
    rfl

/-- Every singleton is arc-connected. -/
theorem isArcConnected_singleton (x : S) : IsArcConnected ({x} : Set S) := by
  intro a ha b hb hne
  rw [mem_singleton_iff.mp ha, mem_singleton_iff.mp hb] at hne
  exact absurd rfl hne

/-- Graph Minors VII, (11.7) (page 253):
"If $Z \subseteq \Sigma$ is solid and flat, and $\Sigma$ is connected, there exists $Y \subseteq
\Sigma$ with $Z \subseteq Y$ such that $Y$ is solid, flat, and arc-connected." -/
theorem theorem_11_7_proof
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsSolid Y ∧ IsFlat Y ∧ IsArcConnected Y := by
  have : T2Space S := hS.2.1
  suffices h_ind : ∀ n : ℕ, ∀ W : Set S, IsSolid W → IsFlat W → (arcComponentsIn W).ncard = n →
      ∃ Y : Set S, W ⊆ Y ∧ IsSolid Y ∧ IsFlat Y ∧ IsArcConnected Y by
    exact h_ind (arcComponentsIn Z).ncard Z hZ_solid hZ_flat rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro W hW_solid hW_flat hn
    by_cases hle : n ≤ 1
    · refine ⟨W, Subset.rfl, hW_solid, hW_flat, ?_⟩
      exact isArcConnected_of_arcComponentsIn_ncard_le_one
        (arcComponentsIn_finite_of_isSolid hS hW_solid) (hn ▸ hle)
    · have h2 : 2 ≤ (arcComponentsIn W).ncard := by omega
      obtain ⟨T, a, b, _, _, hT_solid, hWT_flat, hWT_lt⟩ :=
        solid_bridge_arc hS hW_solid hW_flat h2
      have hWT_solid : IsSolid (W ∪ T) := theorem_11_6_proof hS hW_solid hT_solid
      rw [hn] at hWT_lt
      obtain ⟨Y, hWTY, hY_solid, hY_flat, hY_arc⟩ :=
        ih (arcComponentsIn (W ∪ T)).ncard hWT_lt (W ∪ T) hWT_solid hWT_flat rfl
      exact ⟨Y, subset_union_left.trans hWTY, hY_solid, hY_flat, hY_arc⟩

/-! ## (11.8): Maximal Open Flat Arc-Connected Sets and Simply Connected Superset -/

/-- By Zorn's lemma and the compactness of `S¹`, every open, flat, arc-connected subset `Z ⊆ S` is
contained in a maximal open, flat, arc-connected subset `Y ⊆ S`. This formalizes the first half of
the proof of Graph Minors VII, (11.8) (page 253). -/
theorem exists_maximal_open_flat_arcConnected {Z : Set S}
    (hZ_open : IsOpen Z) (hZ_flat : IsFlat Z) (hZ_arc : IsArcConnected Z) :
    ∃ Y : Set S, Maximal (fun W : Set S => Z ⊆ W ∧ IsOpen W ∧ IsFlat W ∧ IsArcConnected W) Y := by
  let P : Set (Set S) := {W : Set S | Z ⊆ W ∧ IsOpen W ∧ IsFlat W ∧ IsArcConnected W}
  have hZ_mem : Z ∈ P := ⟨Subset.rfl, hZ_open, hZ_flat, hZ_arc⟩
  obtain ⟨Y, _, hY_max⟩ := zorn_subset_nonempty P (fun c hcP hc_chain hc_ne => by
    obtain ⟨W₀, hW₀⟩ := hc_ne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_, ?_⟩, fun W hW => subset_sUnion_of_mem hW⟩
    · exact (hcP hW₀).1.trans (subset_sUnion_of_mem hW₀)
    · exact isOpen_sUnion fun W hW => (hcP hW).2.1
    · intro φ hφ
      have : Nonempty c := ⟨⟨W₀, hW₀⟩⟩
      have hdU : Directed (· ⊆ ·) (fun i : c => i.1) := by
        intro i j
        rcases hc_chain.total i.2 j.2 with hij | hji
        · exact ⟨j, hij, Subset.rfl⟩
        · exact ⟨i, Subset.rfl, hji⟩
      have hcov : range φ ⊆ ⋃ i : c, i.1 := by
        rwa [← sUnion_eq_iUnion]
      obtain ⟨⟨W, hW⟩, hφW⟩ := (isCompact_range φ.continuous).elim_directed_cover
        (fun i : c => i.1) (fun i => (hcP i.2).2.1) hcov hdU
      exact (hcP hW).2.2.1 φ hφW
    · intro a ha b hb hne
      obtain ⟨W₁, hW₁, ha₁⟩ := mem_sUnion.mp ha
      obtain ⟨W₂, hW₂, hb₂⟩ := mem_sUnion.mp hb
      rcases hc_chain.total hW₁ hW₂ with h12 | h21
      · obtain ⟨L, hLW₂, hL⟩ := (hcP hW₂).2.2.2 a (h12 ha₁) b hb₂ hne
        exact ⟨L, hLW₂.trans (subset_sUnion_of_mem hW₂), hL⟩
      · obtain ⟨L, hLW₁, hL⟩ := (hcP hW₁).2.2.2 a ha₁ b (h21 hb₂) hne
        exact ⟨L, hLW₁.trans (subset_sUnion_of_mem hW₁), hL⟩) Z hZ_mem
  exact ⟨Y, hY_max⟩

/-- If `Y ⊆ S` is open in a surface `S` and `Δ` is a closed disc with `discBd Δ ⊆ Y`, then `Y ∪ Δ`
is open in `S`. -/
theorem isOpen_union_disc_of_discBd_subset (hS : IsSurface S) {Y Δ : Set S}
    (hY : IsOpen Y) (hΔ : IsClosedDisc Δ) (hbd : discBd Δ ⊆ Y) :
    IsOpen (Y ∪ Δ) := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  obtain ⟨hunion, _⟩ := c.union_ball
  have hopen_ball : IsOpen (g '' ball 0 1) := c.isOpen_image_ball hS.2.2
  have heq : Y ∪ Δ = Y ∪ g '' ball 0 1 := by
    ext x
    rw [← hunion]
    constructor
    · rintro (hxY | hxball | hxbd)
      · exact Or.inl hxY
      · exact Or.inr hxball
      · exact Or.inl (hbd hxbd)
    · rintro (hxY | hxball)
      · exact Or.inl hxY
      · exact Or.inr (Or.inl hxball)
  rw [heq]
  exact hY.union hopen_ball

/-- If `Y ⊆ S` is arc-connected in a surface `S` and `Δ` is a closed disc with `discBd Δ ⊆ Y`, then
`Y ∪ Δ` is arc-connected. -/
theorem isArcConnected_union_closedDisc (hS : IsSurface S) {Y Δ : Set S}
    (hY : IsArcConnected Y) (hΔ : IsClosedDisc Δ) (hbd : discBd Δ ⊆ Y) :
    IsArcConnected (Y ∪ Δ) := by
  have : T2Space S := hS.2.1
  obtain ⟨φ⟩ := hΔ.isOArc_discBd
  let x₀ : S := (φ 1).1
  have hx₀_bd : x₀ ∈ discBd Δ := (φ 1).2
  have hx₀_Y : x₀ ∈ Y := hbd hx₀_bd
  have hx₀_Δ : x₀ ∈ Δ := discBd_subset Δ hx₀_bd
  have hY_pc : IsPathConnected Y := (isArcConnected_iff_isPathConnected ⟨x₀, hx₀_Y⟩).mp hY
  have hΔ_pc : IsPathConnected Δ := hΔ.isPathConnected
  exact IsPathConnected.isArcConnected (hY_pc.union hΔ_pc ⟨x₀, hx₀_Y, hx₀_Δ⟩)

/-- Every `O`-arc `F` contained in a flat subset `Y ⊆ S` is null-homotopic in `S`. -/
theorem isNullHomotopicOArc_of_isFlat {Y F : Set S} (hY : IsFlat Y) (hFY : F ⊆ Y)
    (hF : IsOArc F) : IsNullHomotopicOArc F := by
  obtain ⟨φ⟩ := hF
  refine ⟨φ, hY ⟨fun x => (φ x).1, continuous_subtype_val.comp φ.continuous⟩ ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hFY (φ x).2

/-- Graph Minors VII, (11.8) for closed surfaces (`bd S = ∅`), proved from `Surface.epstein` and
(11.3). -/
theorem theorem_11_8_closed
    (hS : IsSurface S) (hbd : bd S = ∅) [ConnectedSpace S] {Z : Set S}
    (hZ_open : IsOpen Z) (hZ_flat : IsFlat Z) (hZ_arc : IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsSimplyConnectedSubset Y := by
  have : T2Space S := hS.2.1
  obtain ⟨Y, ⟨hZY, hY_open, hY_flat, hY_arc⟩, hY_max⟩ :=
    exists_maximal_open_flat_arcConnected hZ_open hZ_flat hZ_arc
  refine ⟨Y, hZY, hY_open, hY_arc, fun F hF hFY => ?_⟩
  have hF_null_S : IsNullHomotopicOArc F := isNullHomotopicOArc_of_isFlat hY_flat hFY hF
  have hdisj : Disjoint F (bd S) := by
    rw [hbd]
    exact disjoint_empty F
  obtain ⟨Δ, _, hΔ, hΔ_bd⟩ :=
    (Surface.epstein S univ F hS ‹ConnectedSpace S› hF (subset_univ F) hdisj).1 hF_null_S
  have hbd_sub : discBd Δ ⊆ Y := hΔ_bd.symm ▸ hFY
  have hY_inter_bd : Y ∩ discBd Δ = F := by
    rw [inter_eq_self_of_subset_right hbd_sub, hΔ_bd]
  have hY_bd_arc : IsArcConnected (Y ∩ discBd Δ) := by
    rw [hY_inter_bd]
    exact IsOArc.isArcConnected hF
  have hYU_open : IsOpen (Y ∪ Δ) := isOpen_union_disc_of_discBd_subset hS hY_open hΔ hbd_sub
  have hYU_arc : IsArcConnected (Y ∪ Δ) := isArcConnected_union_closedDisc hS hY_arc hΔ hbd_sub
  have hYU_eq : Y ∪ (Δ \ discBd Δ) = Y ∪ Δ := by
    ext x
    constructor
    · exact Or.imp_right fun h => h.1
    · rintro (hx | hx)
      · exact Or.inl hx
      · by_cases hxb : x ∈ discBd Δ
        · exact Or.inl (hbd_sub hxb)
        · exact Or.inr ⟨hx, hxb⟩
  have hYU_flat : IsFlat (Y ∪ Δ) := by
    rw [← hYU_eq]
    exact (theorem_11_3_proof hS hΔ hY_bd_arc).2 hY_flat
  have hΔ_sub : Δ ⊆ Y :=
    subset_union_right.trans
      (hY_max ⟨hZY.trans subset_union_left, hYU_open, hYU_flat, hYU_arc⟩ subset_union_left)
  exact ⟨Δ, hΔ, hΔ_bd, hΔ_sub⟩

/-- Graph Minors VII, (11.8) (page 253):
"If $Z \subseteq \Sigma$ is open, flat, and arc-connected, there is an open, simply connected set $Y
\subseteq \Sigma$ with $Z \subseteq Y$." -/
theorem theorem_11_8_proof
    (hS : IsSurface S) {Z : Set S}
    (hZ_open : IsOpen Z) (hZ_flat : IsFlat Z) (hZ_arc : IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsSimplyConnectedSubset Y := by
  have : T2Space S := hS.2.1
  obtain ⟨Y, ⟨hZY, hY_open, hY_flat, hY_arc⟩, hY_max⟩ :=
    exists_maximal_open_flat_arcConnected hZ_open hZ_flat hZ_arc
  refine ⟨Y, hZY, hY_open, hY_arc, fun F hF hFY => ?_⟩
  have hF_null_S : IsNullHomotopicOArc F := isNullHomotopicOArc_of_isFlat hY_flat hFY hF
  obtain ⟨Δ, hΔ, hΔ_bd⟩ := nullHomotopicOArc_bounds_disc hS hF hF_null_S
  have hbd_sub : discBd Δ ⊆ Y := hΔ_bd.symm ▸ hFY
  have hY_inter_bd : Y ∩ discBd Δ = F := by
    rw [inter_eq_self_of_subset_right hbd_sub, hΔ_bd]
  have hY_bd_arc : IsArcConnected (Y ∩ discBd Δ) := by
    rw [hY_inter_bd]
    exact IsOArc.isArcConnected hF
  have hYU_open : IsOpen (Y ∪ Δ) := isOpen_union_disc_of_discBd_subset hS hY_open hΔ hbd_sub
  have hYU_arc : IsArcConnected (Y ∪ Δ) := isArcConnected_union_closedDisc hS hY_arc hΔ hbd_sub
  have hYU_eq : Y ∪ (Δ \ discBd Δ) = Y ∪ Δ := by
    ext x
    constructor
    · exact Or.imp_right fun h => h.1
    · rintro (hx | hx)
      · exact Or.inl hx
      · by_cases hxb : x ∈ discBd Δ
        · exact Or.inl (hbd_sub hxb)
        · exact Or.inr ⟨hx, hxb⟩
  have hYU_flat : IsFlat (Y ∪ Δ) := by
    rw [← hYU_eq]
    exact (theorem_11_3_proof hS hΔ hY_bd_arc).2 hY_flat
  have hΔ_sub : Δ ⊆ Y :=
    subset_union_right.trans
      (hY_max ⟨hZY.trans subset_union_left, hYU_open, hYU_flat, hYU_arc⟩ subset_union_left)
  exact ⟨Δ, hΔ, hΔ_bd, hΔ_sub⟩

/-! ## (11.9): Open Simply Connected Superset -/

/-- Graph Minors VII, (11.9) (page 253):
"If $\Sigma$ is connected and $Z \subseteq \Sigma$ is flat and l.a.c., and either $Z$ is closed or
$Z$ is arc-connected, then there is an open simply connected subset $Y \subseteq \Sigma$ with $Z
\subseteq Y$." -/
theorem theorem_11_9_proof
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z)
    (hZ_cl_or_arc : IsClosed Z ∨ IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsSimplyConnectedSubset Y ∧ Y.Nonempty := by
  have : T2Space S := hS.2.1
  have h1 : ∃ Z₁ : Set S, Z ⊆ Z₁ ∧ IsFlat Z₁ ∧ IsLocallyArcConnected Z₁ ∧
      IsArcConnected Z₁ ∧ Z₁.Nonempty := by
    rcases Z.eq_empty_or_nonempty with rfl | hZ_ne
    · obtain ⟨x₀⟩ := ( inferInstance : Nonempty S )
      exact ⟨{x₀}, empty_subset _, isFlat_singleton x₀,
        (isSolid_singleton x₀).1, isArcConnected_singleton x₀, singleton_nonempty x₀⟩
    · rcases hZ_cl_or_arc with hZ_cl | hZ_arc
      · obtain ⟨Z₁, hZZ₁, hZ₁_solid, hZ₁_flat, hZ₁_arc⟩ :=
          theorem_11_7_proof hS ⟨hZ_lac, hZ_cl⟩ hZ_flat
        exact ⟨Z₁, hZZ₁, hZ₁_flat, hZ₁_solid.1, hZ₁_arc, hZ_ne.mono hZZ₁⟩
      · exact ⟨Z, Subset.rfl, hZ_flat, hZ_lac, hZ_arc, hZ_ne⟩
  obtain ⟨Z₁, hZZ₁, hZ₁_flat, hZ₁_lac, hZ₁_arc, hZ₁_ne⟩ := h1
  obtain ⟨Z₂, hZ₁Z₂, hZ₂_open, hZ₂_flat, _, hZ₂_arc_imp⟩ :=
    theorem_11_5_proof hS hZ₁_flat hZ₁_lac
  have hZ₂_arc : IsArcConnected Z₂ := hZ₂_arc_imp hZ₁_arc
  obtain ⟨Y, hZ₂Y, hY_open, hY_sc⟩ :=
    theorem_11_8_proof hS hZ₂_open hZ₂_flat hZ₂_arc
  exact ⟨Y, hZZ₁.trans (hZ₁Z₂.trans hZ₂Y), hY_open, hY_sc, hZ₁_ne.mono (hZ₁Z₂.trans hZ₂Y)⟩

/-- In a surface `S` with `bd S = ∅`, `IsSimplyConnectedSubset Y` is equivalent to
`GM14.IsArcSimplyConnected Y`. -/
theorem isArcSimplyConnected_iff_isSimplyConnectedSubset_of_bd_eq_empty
    (hS : IsSurface S) (hbd : bd S = ∅) (Y : Set S) :
    IsArcSimplyConnected Y ↔ IsSimplyConnectedSubset Y := by
  refine and_congr_right fun _ => forall₂_congr fun F _ => forall_congr' fun _ => ?_
  refine exists_congr fun Δ => ?_
  constructor
  · rintro ⟨hΔ, hsub, hΔY⟩
    rw [subBd_eq_discBd_of_bd_eq_empty hS hbd hΔ] at hsub
    exact ⟨hΔ, hsub, hΔY⟩
  · rintro ⟨hΔ, hdisc, hΔY⟩
    rw [← subBd_eq_discBd_of_bd_eq_empty hS hbd hΔ] at hdisc
    exact ⟨hΔ, hdisc, hΔY⟩

/-- Graph Minors VII, (11.9) for closed surfaces (`bd S = ∅`), stated with
`GM14.IsArcSimplyConnected`. -/
theorem theorem_11_9_closed
    (hS : IsSurface S) (hbd : bd S = ∅) [ConnectedSpace S] {Z : Set S}
    (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z)
    (hZ_cl_or_arc : IsClosed Z ∨ IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsArcSimplyConnected Y ∧ Y.Nonempty := by
  have : T2Space S := hS.2.1
  have h1 : ∃ Z₁ : Set S, Z ⊆ Z₁ ∧ IsFlat Z₁ ∧ IsLocallyArcConnected Z₁ ∧
      IsArcConnected Z₁ ∧ Z₁.Nonempty := by
    rcases Z.eq_empty_or_nonempty with rfl | hZ_ne
    · obtain ⟨x₀⟩ := ( inferInstance : Nonempty S )
      exact ⟨{x₀}, empty_subset _, isFlat_singleton x₀,
        (isSolid_singleton x₀).1, isArcConnected_singleton x₀, singleton_nonempty x₀⟩
    · rcases hZ_cl_or_arc with hZ_cl | hZ_arc
      · obtain ⟨Z₁, hZZ₁, hZ₁_solid, hZ₁_flat, hZ₁_arc⟩ :=
          theorem_11_7_proof hS ⟨hZ_lac, hZ_cl⟩ hZ_flat
        exact ⟨Z₁, hZZ₁, hZ₁_flat, hZ₁_solid.1, hZ₁_arc, hZ_ne.mono hZZ₁⟩
      · exact ⟨Z, Subset.rfl, hZ_flat, hZ_lac, hZ_arc, hZ_ne⟩
  obtain ⟨Z₁, hZZ₁, hZ₁_flat, hZ₁_lac, hZ₁_arc, hZ₁_ne⟩ := h1
  obtain ⟨Z₂, hZ₁Z₂, hZ₂_open, hZ₂_flat, _, hZ₂_arc_imp⟩ :=
    theorem_11_5_proof hS hZ₁_flat hZ₁_lac
  have hZ₂_arc : IsArcConnected Z₂ := hZ₂_arc_imp hZ₁_arc
  obtain ⟨Y, hZ₂Y, hY_open, hY_sc⟩ :=
    theorem_11_8_closed hS hbd hZ₂_open hZ₂_flat hZ₂_arc
  rw [← isArcSimplyConnected_iff_isSimplyConnectedSubset_of_bd_eq_empty hS hbd Y] at hY_sc
  exact ⟨Y, hZZ₁.trans (hZ₁Z₂.trans hZ₂Y), hY_open, hY_sc, hZ₁_ne.mono (hZ₁Z₂.trans hZ₂Y)⟩

/-! ## (11.10): Solid Flat Sets are Equal to `Σ` or Planar -/

/-- Every closed subset of an open disc in a surface is included in a closed disc (`IsPlanar`). This
formalizes the step "since any closed subset of an open disc is included in a closed disc" in the
proof of Graph Minors VII, (11.10) (page 253). -/
theorem isPlanar_of_isClosed_subset_isOpenDisc (hS : IsSurface S) {Z Y : Set S}
    (hZ : IsClosed Z) (hY : IsOpenDisc Y) (hZY : Z ⊆ Y) :
    IsPlanar Z := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨_, ⟨e⟩⟩ := hY
  have hZ_compact : IsCompact Z := hZ.isCompact
  let inc : Z → Y := fun z => ⟨z.1, hZY z.2⟩
  have hinc_cont : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
  let g : Z → EuclideanPlane := fun z => (e.symm (inc z)).1
  have hg_cont : Continuous g := continuous_subtype_val.comp (e.symm.continuous.comp hinc_cont)
  have hg_lt : ∀ z : Z, ‖g z‖ < 1 := fun z =>
    mem_ball_zero_iff.mp (e.symm (inc z)).2
  have hr_exists : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z : Z, ‖g z‖ ≤ r := by
    rcases Z.eq_empty_or_nonempty with rfl | hZ_ne
    · exact ⟨1 / 2, by norm_num, by norm_num, fun z => False.elim z.2⟩
    · have : Nonempty Z := hZ_ne.to_subtype
      have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ_compact
      obtain ⟨z₀, _, hz₀_max⟩ :=
        isCompact_univ.exists_isMaxOn univ_nonempty (continuous_norm.comp hg_cont).continuousOn
      have hlt : ‖g z₀‖ < 1 := hg_lt z₀
      have hnn : 0 ≤ ‖g z₀‖ := norm_nonneg _
      refine ⟨(‖g z₀‖ + 1) / 2, by linarith, by linarith, fun z => ?_⟩
      have hle : ‖g z‖ ≤ ‖g z₀‖ := hz₀_max (mem_univ z)
      linarith
  obtain ⟨r, hr0, hr1, hr_bound⟩ := hr_exists
  have hmem_open : ∀ x : ClosedUnitDisc, r • x.1 ∈ OpenUnitDisc := fun x => by
    rw [OpenUnitDisc, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    exact (mul_le_of_le_one_right hr0.le (mem_closedBall_zero_iff.mp x.2)).trans_lt hr1
  let scale : ClosedUnitDisc → OpenUnitDisc := fun x => ⟨r • x.1, hmem_open x⟩
  have hscale_cont : Continuous scale := by fun_prop
  let φ : ClosedUnitDisc → S := fun x => (e (scale x)).1
  have hφ_cont : Continuous φ :=
    continuous_subtype_val.comp (e.continuous.comp hscale_cont)
  have hφ_inj : Injective φ := by
    intro x₁ x₂ h
    have h1 := e.injective (Subtype.ext h)
    have h2 : r • x₁.1 = r • x₂.1 := congrArg Subtype.val h1
    exact Subtype.ext (smul_right_injective EuclideanPlane hr0.ne' h2)
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hφ_emb : IsEmbedding φ := (hφ_cont.isClosedEmbedding hφ_inj).isEmbedding
  refine ⟨range φ, ⟨hφ_emb.toHomeomorph⟩, fun z hz => ?_⟩
  let u : EuclideanPlane := (1 / r) • g ⟨z, hz⟩
  have hu_mem : u ∈ ClosedUnitDisc := by
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hr0), one_div_mul_eq_div, div_le_one hr0]
    exact hr_bound ⟨z, hz⟩
  refine ⟨⟨u, hu_mem⟩, ?_⟩
  change (e ⟨r • ((1 / r) • g ⟨z, hz⟩), _⟩).1 = z
  have hsmul : r • ((1 / r) • g ⟨z, hz⟩) = g ⟨z, hz⟩ := by
    rw [smul_smul, mul_one_div_cancel hr0.ne', one_smul]
  have heq : (⟨r • ((1 / r) • g ⟨z, hz⟩), hmem_open ⟨u, hu_mem⟩⟩ : OpenUnitDisc) =
      e.symm (inc ⟨z, hz⟩) := Subtype.ext hsmul
  rw [heq, e.apply_symm_apply]

/-- Every proper closed subset `Z ≠ univ` of a 2-sphere `S` is planar (`IsPlanar Z`). This
formalizes the step "then $\Sigma$ is a sphere, and the result follows" in the proof of
Graph Minors VII, (11.10) (page 253). -/
theorem isPlanar_of_isSphere_ne_univ (hS_surf : IsSurface S) (hS : IsSphere S)
    {Z : Set S} (hZ : IsClosed Z) (hne : Z ≠ univ) :
    IsPlanar Z := by
  have : T2Space S := hS_surf.2.1
  obtain ⟨p, hpZ⟩ : ∃ p : S, p ∉ Z := not_forall.mp fun h => hne (eq_univ_of_forall h)
  obtain ⟨e⟩ := hS
  obtain ⟨H, hH⟩ := exists_homeomorph_onePoint (e p)
  let E : S ≃ₜ OnePoint EuclideanPlane := e.trans H
  have hp_inf : E p = ∞ := hH
  have hinf_notMem : (∞ : OnePoint EuclideanPlane) ∉ E '' Z := by
    rintro ⟨q, hqZ, hqE⟩
    have : q = p := E.injective (hqE.trans hp_inf.symm)
    exact hpZ (this ▸ hqZ)
  have hEZ_closed : IsClosed (E '' Z) := E.isClosedMap Z hZ
  have h0_mem : (0 : ℂ) ∈ rsph ⁻¹' (E '' Z)ᶜ := by
    change rsph 0 ∉ E '' Z
    rw [rsph_zero]
    exact hinf_notMem
  have hopen_pre : IsOpen (rsph ⁻¹' (E '' Z)ᶜ) :=
    hEZ_closed.isOpen_compl.preimage continuous_rsph
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen_pre 0 h0_mem
  let R : ℝ := 1 / ε
  have hR : 0 < R := one_div_pos.mpr hε
  let φ : ClosedUnitDisc → S :=
    fun x => E.symm (sph ((R : ℂ) * complexPlane.symm x.1))
  have hφ_cont : Continuous φ :=
    E.symm.continuous.comp (isOpenEmbedding_sph.continuous.comp
      (continuous_const.mul (complexPlane.symm.continuous.comp continuous_subtype_val)))
  have hφ_inj : Injective φ := by
    intro x₁ x₂ h
    have h1 := isOpenEmbedding_sph.injective (E.symm.injective h)
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have h2 := mul_left_cancel₀ hR0 h1
    exact Subtype.ext (complexPlane.symm.injective h2)
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hφ_emb : IsEmbedding φ := (hφ_cont.isClosedEmbedding hφ_inj).isEmbedding
  refine ⟨range φ, ⟨hφ_emb.toHomeomorph⟩, fun z hz => ?_⟩
  rcases eq_infty_or_sph (E z) with hinf | ⟨w, hw⟩
  · exact absurd (hinf ▸ mem_image_of_mem E hz) hinf_notMem
  · have hw_le : ‖w‖ ≤ R := by
      by_contra hw_gt
      have hw_gt' : R < ‖w‖ := not_le.mp hw_gt
      have hw0 : w ≠ 0 := norm_pos_iff.mp (hR.trans hw_gt')
      have hwinv_ball : w⁻¹ ∈ ball (0 : ℂ) ε := by
        rw [mem_ball_zero_iff, norm_inv]
        exact inv_lt_of_inv_lt₀ hε (by simpa [R] using hw_gt')
      have hnot : rsph w⁻¹ ∈ (E '' Z)ᶜ := hball hwinv_ball
      rw [rsph_of_ne (inv_ne_zero hw0), inv_inv, ← hw] at hnot
      exact hnot (mem_image_of_mem E hz)
    let u : EuclideanPlane := complexPlane (w / (R : ℂ))
    have hu_mem : u ∈ ClosedUnitDisc := by
      rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, norm_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_one hR]
      exact hw_le
    refine ⟨⟨u, hu_mem⟩, ?_⟩
    change E.symm (sph ((R : ℂ) * complexPlane.symm (complexPlane (w / (R : ℂ))))) = z
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [complexPlane.symm_apply_apply, mul_div_cancel₀ _ hR0, ← hw, E.symm_apply_apply]

/-- Graph Minors VII, (11.10) for closed surfaces (`bd S = ∅`), deduced from (11.9) and (4.2)
(`Surface.open_disc`) with no additional hypotheses. -/
theorem theorem_11_10_closed
    (hS : IsSurface S) (hbd : bd S = ∅) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) :
    Z = univ ∨ IsPlanar Z := by
  by_cases hZ_univ : Z = univ
  · exact Or.inl hZ_univ
  · right
    obtain ⟨Y, hZY, hY_open, hY_asc, hY_ne⟩ :=
      theorem_11_9_closed
        hS hbd hZ_flat hZ_solid.1 (Or.inl hZ_solid.2)
    have hY_sc : IsSimplyConnectedSubset Y :=
      (isArcSimplyConnected_iff_isSimplyConnectedSubset_of_bd_eq_empty hS hbd Y).mp hY_asc
    have : T2Space S := hS.2.1
    have hY_conn : IsConnected Y := ⟨hY_ne, IsArcConnected.isPreconnected hY_sc.1⟩
    have hS_closed : IsClosedSurface S := isClosedSurface_of_bd_eq_empty hS hbd
    rcases Surface.open_disc S Y hS_closed ‹ConnectedSpace S› hY_conn hY_open
      (fun F hFY hF => by
        obtain ⟨Δ, hΔ, hΔ_bd, hΔY⟩ := hY_sc.2 F hF hFY
        exact ⟨Δ, hΔY, hΔ, hΔ_bd⟩) with ⟨hS_sph, _⟩ | hY_odisc
    · exact isPlanar_of_isSphere_ne_univ hS hS_sph hZ_solid.2 hZ_univ
    · exact isPlanar_of_isClosed_subset_isOpenDisc hS hZ_solid.2 hY_odisc hZY

/-- Graph Minors VII, (11.10) (page 253):
"If $\Sigma$ is connected and $Z \subseteq \Sigma$ is solid and flat, then either $Z = \Sigma$ or
$Z$ is planar." -/
theorem theorem_11_10_proof
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) :
    Z = univ ∨ IsPlanar Z := by
  by_cases hbd : bd S = ∅
  · exact theorem_11_10_closed
      hS hbd hZ_solid hZ_flat
  · obtain ⟨Y, hZY, hY_open, hY_sc, _⟩ :=
      theorem_11_9_proof
        hS hZ_flat hZ_solid.1 (Or.inl hZ_solid.2)
    have : T2Space S := hS.2.1
    refine Or.inr (solidFlat_boundarySurface_planar_core hS hbd hZ_solid.2 hZY hY_open
      (IsArcConnected.isPreconnected hY_sc.1) fun F hFY hF => ?_)
    obtain ⟨Δ, hΔ, hΔ_bd, hΔY⟩ := hY_sc.2 F hF hFY
    exact ⟨Δ, hΔY, hΔ, hΔ_bd⟩

/-- Graph Minors VII, (5.1) (page 230):
"If $\Sigma$ is connected and $X \subseteq \Sigma$ is solid and $X \ne \Sigma$, then $X$ is planar
if and only if every $O$-arc included in $X$ is null-homotopic." -/
theorem theorem_5_1_proof
    (hS : IsSurface S) [ConnectedSpace S] {X : Set S}
    (hX_solid : IsSolid X) (hX_ne : X ≠ univ) :
    IsPlanar X ↔ ∀ F : Set S, IsOArc F → F ⊆ X → IsNullHomotopicOArc F := by
  constructor
  · rintro ⟨Δ, hΔ, hXΔ⟩ F hF hFX
    exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ Δ) hΔ (hFX.trans hXΔ)
  · intro h
    have hX_flat : IsFlat X :=
      isFlat_of_forall_isNullHomotopicOArc hS (fun F hFX hF => h F hF hFX)
    exact (theorem_11_10_proof hS hX_solid hX_flat).resolve_left hX_ne

end GraphMinor.GM07
