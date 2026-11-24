/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section6
public import LeanPool.GraphMinor.GM07.CutBounds
public import LeanPool.GraphMinor.GM07.GoodEdge
public import LeanPool.GraphMinor.GM07.CutFeasible
import LeanPool.GraphMinor.GM07.CuffSlide
import LeanPool.GraphMinor.GM07.Section35
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors VII, Section 7: Adding New Cuffs

This file formalizes Section 7 (pages 238–241) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- `(7.1)` (`theorem_7_1`): lower bound `α(φ_e⁻¹(G \ e)) ≥ r` when cutting along a non-loop edge `e`
  outside `Δ_{r-1}` disjoint from `bd(Σ)`;
- `(7.2)` (`theorem_7_2`): `φ_e⁻¹(G \ e)` is boundary-linked in `Σ_e` when no null-homotopic
  `G$-normal `O`-arc with `≤ 1` vertex of `G` has `e` inside it;
- `(7.3)` (`theorem_7_3`): existence of a non-loop edge `e` satisfying the hypotheses of `(7.1)` and
  `(7.2)`;
- `(7.4)` (`theorem_7_4`): deduced directly by combining `(7.1)`, `(7.2)`, and `(7.3)`;
- Unconditional monotonicity and base-case lemmas for `(7.5)` (`isW36BoundProper_anti_n`,
  `wSurfaceProper_mono_n`, `wMaxModelProper_mono_c`, `muModelProper_mono_c`, `vModelProper_mono_c`,
  `two_mul_k_le_vModelProper`, `bd_eq_empty_of_homeomorph_surfaceModel_zero`,
  `isGFeasibleProper_of_bd_inter_empty`);
- `(7.5)` (`theorem_7_5`): final form of the main feasibility theorem on `Σ ≅ Σ(a, b, c)`
  (`3a + 3b + c ≥ 3`), proved by following the paper's three cases (`c ≥ 2` via `(6.1)`,
  `V(H) ∩ bd(Σ) = ∅` via `emptyDrawing S`, and `c = 1` via `(7.4)` and `(6.1)`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Cutting along an edge: (7.1)–(7.4) -/

/-- Graph Minors VII, (7.1) (pages 238–239):
"(7.1) *Suppose that $\Sigma$, $G$ are as above, and $2 \le r \le \frac{2}{9}\alpha(G)$, and that
$e$ is an edge of $G$, not a loop, with $e \notin \Delta_{r-1}$ and with
$\bar{e} \cap bd(\Sigma) = \emptyset$. Then $\alpha(\phi_e^{-1}(G \setminus e)) \ge r$.*" -/
theorem theorem_7_1_proof
    {S_e : Type u} [TopologicalSpace S_e]
    (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (e : Set S) (φ_e : S_e → S) (G_e : Drawing S_e)
    (hr : 2 ≤ r) (halpha : 9 * r ≤ 2 * alpha G)
    (hnot_in : ¬ (e ⊆ allCuffsInsideSet G (r - 1)))
    (hCut : IsCutAlongEdge G e a b c S_e φ_e G_e) :
    r ≤ alpha G_e :=
  hCut.alpha_bound hS h3 he_model hr halpha hnot_in

/-- Graph Minors VII, (7.2) (page 239):
"(7.2) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a
boundary-linked proper graph in $\Sigma$. Let $e$ be an edge of $G$ which is not a loop, such that
$\bar{e} \cap bd(\Sigma) = \emptyset$, and there is no null-homotopic $G$-normal $O$-arc $A$ with
$|V(G) \cap A| \le 1$ and with $e$ inside $A$. Then $\phi_e^{-1}(G \setminus e)$ is boundary-linked
in $\Sigma_e$.*" -/
theorem theorem_7_2_proof
    {S_e : Type u} [TopologicalSpace S_e]
    (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (e : Set S) (φ_e : S_e → S) (G_e : Drawing S_e)
    (hBL : IsBoundaryLinked G)
    (hNoNull : ¬ ∃ A : Set S, G.IsNormal A ∧ IsNullHomotopicOArc A ∧
      (G.V ∩ A).ncard ≤ 1 ∧ IsInsideOArc e A)
    (hCut : IsCutAlongEdge G e a b c S_e φ_e G_e) :
    IsBoundaryLinked G_e :=
  hCut.boundaryLinked hS h3 he_model hBL hNoNull

/-- Graph Minors VII, (7.3) (pages 239–240):
"(7.3) *Let $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$. Let $G$ be a proper graph in
$\Sigma$, and let $r$ be an integer with $|V(G) \cap C| \le r - 1$ for every cuff $C$ of $\Sigma$,
and with $2 \le r \le \frac{2}{9}\alpha(G)$. Then there is an edge $e$ of $G$ which is not a loop,
such that $e \notin \Delta_{r-1}$ and $\bar{e} \cap bd(\Sigma) = \emptyset$, and such that there is
no $G$-normal null-homotopic $O$-arc $F$ with $|V(G) \cap F| \le 1$ and with $e$ inside $F$.*" -/
theorem theorem_7_3_proof
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (hG : G.IsProper)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r - 1)
    (hr : 2 ≤ r) (halpha : 9 * r ≤ 2 * alpha G) :
    ∃ (e : Set S) (S_e : Type u) (_ : TopologicalSpace S_e) (_ : T1Space S_e)
      (φ_e : S_e → S) (G_e : Drawing S_e),
      IsCutAlongEdge G e a b c S_e φ_e G_e ∧
      ¬ (e ⊆ allCuffsInsideSet G (r - 1)) ∧
      (¬ ∃ F : Set S, G.IsNormal F ∧ IsNullHomotopicOArc F ∧
        (G.V ∩ F).ncard ≤ 1 ∧ IsInsideOArc e F) :=
  by
  have : ConnectedSpace S := connectedSpace_of_model he_model
  have ht2 : T2Space S := hS.2.1
  obtain ⟨e, he, h1, h2, h3', h4⟩ := exists_good_edge hS h3 he_model (r := r - 1)
    (by omega) _ G rfl hG
    (by rwa [Nat.sub_add_cancel (by omega)]) hcuff
  obtain ⟨Y, tY, t1Y, φ, G', hcut⟩ := exists_cut hS he_model G hG he h1
    (disjoint_iff_inter_eq_empty.mp h2)
  exact ⟨e, Y, tY, t1Y, φ, G', hcut, h3', h4⟩

/-- Graph Minors VII, (7.4) (page 240):
"(7.4) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a
boundary-linked proper graph in $\Sigma$ with $\alpha(G) \ge \frac{9}{2}r$, where $r \ge 2$ is an
integer, and $|V(G) \cap C| \le r-1$ for every cuff $C$. Then there is an edge $e$ of $G$ which is
not a loop, with $\bar{e} \cap bd(\Sigma) = \emptyset$, such that $\phi_e^{-1}(G \setminus e)$ is
boundary-linked in $\Sigma_e$ and*
$$\alpha(\phi_e^{-1}(G \setminus e)) \ge r.$$"
Proved directly by combining `(7.1)`, `(7.2)`, and `(7.3)`. -/
theorem theorem_7_4_proof
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (hBL : IsBoundaryLinked G)
    (halpha : 9 * r ≤ 2 * alpha G) (hr : 2 ≤ r)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r - 1) :
    ∃ (e : Set S) (S_e : Type u) (_ : TopologicalSpace S_e) (_ : T1Space S_e)
      (φ_e : S_e → S) (G_e : Drawing S_e),
      IsCutAlongEdge G e a b c S_e φ_e G_e ∧
      IsBoundaryLinked G_e ∧
      r ≤ alpha G_e := by
  obtain ⟨e, S_e, tS_e, t1S_e, φ_e, G_e, hCut, hnot_in, hNoNull⟩ :=
    theorem_7_3_proof  hS h3 he_model G r hBL.1 hcuff hr halpha
  have hBL_e : @IsBoundaryLinked S_e tS_e G_e :=
    @theorem_7_2_proof S _ S_e tS_e hS a b c h3 he_model G e φ_e G_e hBL hNoNull hCut
  have halpha_e : r ≤ @alpha S_e tS_e G_e :=
    @theorem_7_1_proof S _ S_e tS_e hS a b c h3 he_model G r e φ_e G_e hr halpha hnot_in hCut
  exact ⟨e, S_e, tS_e, t1S_e, φ_e, G_e, hCut, hBL_e, halpha_e⟩

/-! ## 2. Unconditional monotonicity and base cases for (7.5) -/

/-- `IsW36Bound S k n w` is antitone in `n`: if `n₁ ≤ n₂`, any bound `w` for matchings with
`≤ 2 * n₂` vertices is also a bound for matchings with `≤ 2 * n₁` vertices. -/
theorem isW36Bound_anti_n {k n₁ n₂ w : ℕ} (hn : n₁ ≤ n₂)
    (hw : IsW36Bound S k n₂ w) :
    IsW36Bound S k n₁ w := by
  intro G H hG hGV hH hHV
  have hGV' : G.V.ncard ≤ 2 * n₂ := by omega
  exact hw G H hG hGV' hH hHV

/-- `wSurface S k n` is monotone in `n` on any surface `S`. -/
theorem wSurface_mono_n
    (hS : IsSurface S) (k : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    wSurface S k n₁ ≤ wSurface S k n₂ := by
  obtain ⟨w₀, hw₀⟩ := exists_isW36Bound hS k n₂
  refine csInf_le_csInf ⟨0, fun w _ => Nat.zero_le w⟩ ⟨w₀, hw₀⟩ ?_
  intro w hw
  exact isW36Bound_anti_n hn hw

/-- `wMaxModel a b c k ≤ wMaxModel a b (c + 1) k` (Graph Minors VII, proof of (7.5),
page 240: "since $v(\Sigma, k) \le v$"). -/
theorem wMaxModel_mono_c (a b c k : ℕ) :
    wMaxModel a b c k ≤ wMaxModel a b (c + 1) k := by
  unfold wMaxModel
  have hsub : Finset.range (2 * (2 * a + b + c - 1) + 1) ⊆
      Finset.range (2 * (2 * a + b + (c + 1) - 1) + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine le_trans (Finset.sup_mono hsub) ?_
  refine Finset.sup_mono_fun fun c' _ => ?_
  have hS_model : IsSurface (SurfaceModel a b c') := (modelCriterion.1 a b c').1
  refine wSurface_mono_n hS_model (2 * k) ?_
  exact Nat.mul_le_mul_left 3 (by omega)

/-- `muModel a b c k ≤ muModel a b (c + 1) k`. -/
theorem muModel_mono_c (a b c k : ℕ) :
    muModel a b c k ≤ muModel a b (c + 1) k := by
  unfold muModel
  have hw := wMaxModel_mono_c a b c k
  have h1 : 2 * (2 * a + b + c) ≤ 2 * (2 * a + b + (c + 1)) := by omega
  have h2 : k + wMaxModel a b c k ≤ k + wMaxModel a b (c + 1) k := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) (2 * k)

/-- `vModel a b c k ≤ vModel a b (c + 1) k` (Graph Minors VII, proof of (7.5),
page 240: "since $v(\Sigma, k) \le v$"). -/
theorem vModel_mono_c (a b c k : ℕ) :
    vModel a b c k ≤ vModel a b (c + 1) k := by
  unfold vModel
  have hw := wMaxModel_mono_c a b c k
  have hmu := muModel_mono_c a b c k
  have h1 : 6 * (2 * a + b + c - 1) ≤ 6 * (2 * a + b + (c + 1) - 1) := by omega
  have h2 :
      wMaxModel a b c k + 2 * muModel a b c k + 1 ≤
        wMaxModel a b (c + 1) k + 2 * muModel a b (c + 1) k + 1 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) (2 * k)

/-- For all `a b c k : ℕ`, `2 * k ≤ vModel a b c k`. -/
theorem two_mul_k_le_vModel (a b c k : ℕ) :
    2 * k ≤ vModel a b c k := by
  unfold vModel
  omega

/-- If `S ≃ₜ SurfaceModel a b 0`, then `cuffs S = ∅` and `bd S = ∅`. -/
theorem bd_eq_empty_of_homeomorph_surfaceModel_zero {a b : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) :
    cuffs S = ∅ ∧ bd S = ∅ := by
  rcases he with ⟨e⟩
  obtain ⟨ht, f, hf⟩ := presents_ew a b 0
  have : T2Space (SurfaceModel a b 0) := ht
  have hcuffs0 : cuffs (SurfaceModel a b 0) = ∅ := by
    rw [cuffs_eq_holeC hf]
    simp
  have hbd0 : bd (SurfaceModel a b 0) = ∅ := by
    rw [← sUnion_cuffs, hcuffs0, sUnion_empty]
  have hbdS : bd S = ∅ := by
    have himg := image_bd_homeomorph e.symm
    rw [hbd0, image_empty] at himg
    exact himg.symm
  have hcuffsS : cuffs S = ∅ := by
    unfold cuffs
    rw [hbdS]
    simp [componentsIn]
  exact ⟨hcuffsS, hbdS⟩

/-- The empty drawing `emptyDrawing S` in any space `S` is a surface forest. -/
theorem isSurfaceForest_emptyDrawing : IsSurfaceForest (emptyDrawing S) := by
  refine ⟨?_, ?_⟩
  · change bd S ∩ (emptyDrawing S).U ⊆ (emptyDrawing S).V
    simp [emptyDrawing]
  · intro u W _
    cases W with
    | nil hv => exact False.elim hv
    | cons hlink _ => exact False.elim hlink.2.1

/-- Unconditional proof of the base case `V(H) ∩ bd(Σ) = ∅` in Graph Minors VII, (7.5) (page 240:
"If $V(H) \cap bd(\Sigma) = \emptyset$ the theorem is trivial."): the empty subdrawing
`emptyDrawing S` of `G` is a surface forest homoplastic to `H`. -/
theorem isGFeasible_of_bd_inter_empty (G : Drawing S) {H : Drawing S}
    (hH : IsSurfaceForest H) (hbd_empty : H.V ∩ bd S = ∅) :
    IsGFeasible G H := by
  refine ⟨emptyDrawing S, isSurfaceForest_emptyDrawing, ?_, ?_⟩
  · refine ⟨Homeomorph.refl S, fun _ _ => rfl, ?_⟩
    have hmapV : (mapDrawingHomeo (Homeomorph.refl S) H).V = H.V := image_id H.V
    refine ⟨IsProper.map_homeo (Homeomorph.refl S) hH.1, isSurfaceForest_emptyDrawing.1,
      IsGraphForest.map_homeo (Homeomorph.refl S) hH.2, isSurfaceForest_emptyDrawing.2, ?_, ?_⟩
    · rw [hmapV, hbd_empty]
      simp [emptyDrawing]
    · intro s hs
      rw [hmapV, hbd_empty] at hs
      exact False.elim hs
  · refine ⟨empty_subset _, ?_⟩
    intro e he
    exfalso
    exact he.1.ne_empty (subset_empty_iff.mp (he.2.1.trans sdiff_subset))

/-- Graph Minors VII, (7.5) (pages 240–241):
"(7.5) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$. Let $k \ge 0$ be an
integer, and let $v = v(\Sigma(a, b, c+1), k)$. Let $G$ be a boundary-linked proper graph in
$\Sigma$ with $\alpha(G) \ge 42kv$ and with $|V(G) \cap bd(\Sigma)| \le 2k - 2c - 2$. Let $H$ be a
forest in $\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is $G$-feasible.*"
-/
theorem theorem_7_5_proof
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G)
    (halpha : 42 * k * vModel a b (c + 1) k ≤ alpha G)
    (hbd_card : (G.V ∩ bd S).ncard + 2 * c + 2 ≤ 2 * k)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by
  -- Follow the paper's three cases (pages 240–241):
  by_cases hc2 : 2 ≤ c
  · -- Case 1: "If c ≥ 2 this follows from (6.1), since v(Σ, k) ≤ v."
    have hne : (a, b, c) ≠ (0, 0, 2) := by
      rintro ⟨rfl, rfl, rfl⟩
      omega
    have hk_pos : 3 ≤ k := by omega
    have hv_le : vSurface S k ≤ vModel a b (c + 1) k :=
      le_trans (vSurface_le_vModel he k) (vModel_mono_c a b c k)
    have hv_pos : 6 ≤ vModel a b (c + 1) k := by
      have := two_mul_k_le_vModel a b (c + 1) k
      omega
    have h9_lt : 9 * k * vSurface S k < alpha G := by
      have hmul : 9 * k * vSurface S k ≤ 9 * k * vModel a b (c + 1) k :=
        Nat.mul_le_mul_left (9 * k) hv_le
      nlinarith
    have hbd_card' : (G.V ∩ bd S).ncard ≤ 2 * k - 2 * c := by omega
    exact theorem_6_1_proof hS hc2 hne he k G H hBL hbd_card' h9_lt hH hbd_eq
  · -- Case 2: "If V(H) ∩ bd(Σ) = ∅ the theorem is trivial."
    rcases (H.V ∩ bd S).eq_empty_or_nonempty with hbd_empty | hbd_ne
    · exact isGFeasible_of_bd_inter_empty G hH hbd_empty
    · -- Case 3: "We assume then that V(H) ∩ bd(Σ) ≠ ∅ and c ≤ 1. It follows that c = 1 and k ≥ 3."
      have hc_ne_zero : c ≠ 0 := by
        rintro rfl
        have hbdS := (bd_eq_empty_of_homeomorph_surfaceModel_zero he).2
        rw [hbdS, inter_empty] at hbd_ne
        exact hbd_ne.ne_empty rfl
      have hc1 : c = 1 := by omega
      subst hc1
      have hGV_ne : (G.V ∩ bd S).Nonempty := hbd_eq.symm ▸ hbd_ne
      have hGV_pos : 1 ≤ (G.V ∩ bd S).ncard :=
        (ncard_pos (G.finite_V.subset inter_subset_left)).mpr hGV_ne
      have hk3 : 3 ≤ k := by omega
      let v := vModel a b 2 k
      let r := (28 * k * v) / 3
      have hv_ge : 2 * k ≤ v := two_mul_k_le_vModel a b 2 k
      have hkv_ge : 6 * k ≤ 28 * k * v := by nlinarith
      have hr_ge : 2 * k ≤ r := by
        dsimp [r]
        omega
      have hr2 : 2 ≤ r := by omega
      have h9r : 9 * r ≤ 2 * alpha G := by
        dsimp [r]
        have hdiv : 3 * ((28 * k * v) / 3) ≤ 28 * k * v := Nat.mul_div_le (28 * k * v) 3
        nlinarith
      have hcuff_le : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r - 1 := by
        intro C hC
        have hC_sub : C ⊆ bd S := by
          rw [← sUnion_cuffs]
          exact subset_sUnion_of_mem hC
        have hle_bd : (G.V ∩ C).ncard ≤ (G.V ∩ bd S).ncard :=
          ncard_le_ncard (inter_subset_inter_right G.V hC_sub)
            (G.finite_V.subset inter_subset_left)
        omega
      obtain ⟨e, S_e, tS_e, t1S_e, φ_e, G_e, hCut, hBL_e, halpha_e⟩ :=
        theorem_7_4_proof  hS h3 he G r hBL h9r hr2 hcuff_le
      have hbd_card4 : (G.V ∩ bd S).ncard + 4 ≤ 2 * k := by omega
      obtain ⟨H', hH', hbd_eq', hbd_card', h9_lt', himp⟩ :=
        oneCuffCutEdgeFeasibilityStep hS a b he k G H e φ_e G_e hbd_card4 hH hbd_eq hCut halpha_e
      have hne2 : (a, b, 2) ≠ (0, 0, 2) := by
        rintro ⟨rfl, rfl, -⟩
        omega
      have hFeas' : @IsGFeasible S_e tS_e G_e H' :=
        theorem_6_1_general (by omega) hne2 S_e hCut.isSurface hCut.homeo_model G_e H' hBL_e
          rfl hbd_card' h9_lt' hH' hbd_eq'
      exact himp hFeas'

/-- Graph Minors VII, (7.5) for the cited interface `GM12.GM07Theorem75Statement`. -/
theorem gm07_theorem_7_5
    :
    GM12.GM07Theorem75Statement.{u} := by
  intro S _ _ hS a b c h3 he k G _ hBL halpha hbd_card H hH hbd_eq
  exact theorem_7_5_proof hS h3 he k G H hBL halpha hbd_card hH hbd_eq

end GraphMinor.GM07
