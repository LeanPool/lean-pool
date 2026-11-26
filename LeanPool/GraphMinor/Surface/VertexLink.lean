/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Polygon
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Points of a presented surface

A manifold point has small open neighbourhoods that stay connected when the point is removed
(`IsManifoldPoint.exists_punctured`). We use this at a vertex of a family of polygons with sides
glued by labels. Let
`f` send the discs onto a Hausdorff space. Suppose that `f` is compatible with the pasting and that
fibres over the
other points are single pasting classes. If the corners over the vertex `v` split into two classes,
then points near
`v` split into two parts that are closed in the punctured neighbourhood, which is impossible. So
all the corners over `v` are in one class (`prel_of_vertex`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

theorem isPreconnected_punctured_ball (w : EuclideanPlane) {r : ℝ} (_hr : 0 < r) :
    IsPreconnected (ball w r \ {w}) := by
  have hrk : 1 < Module.rank ℝ EuclideanPlane := by
    rw [← Module.finrank_eq_rank]
    simp [EuclideanPlane]
  have hs : IsPreconnected (sphere (0 : EuclideanPlane) 1) := isPreconnected_sphere hrk 0 1
  have h1 := (isPreconnected_Ioo (a := (0 : ℝ)) (b := r)).prod hs
  have h2 : ball w r \ {w} = (fun x : ℝ × EuclideanPlane => w + x.1 • x.2) ''
    (Ioo 0 r ×ˢ sphere 0 1) := by
    ext y
    constructor
    · rintro ⟨hy, hne⟩
      have h3 : y - w ≠ 0 := sub_ne_zero.mpr hne
      have h4 : ‖y - w‖ ≠ 0 := norm_ne_zero_iff.mpr h3
      refine ⟨(‖y - w‖, (‖y - w‖)⁻¹ • (y - w)), ⟨⟨norm_pos_iff.mpr h3, ?_⟩, ?_⟩, ?_⟩
      · simpa [dist_eq_norm] using hy
      · simp [norm_smul, h4]
      · simp [smul_smul, h4]
    · rintro ⟨⟨s, u⟩, ⟨hs1, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have hsn : ‖s‖ = s := Real.norm_of_nonneg hs1.1.le
      refine ⟨?_, ?_⟩
      · simp [dist_eq_norm, norm_smul, hu', hsn, hs1.2]
      · intro h3
        have h4 : s • u = 0 := by simpa using h3
        have h5 : ‖s • u‖ = s := by rw [norm_smul, hu', mul_one, hsn]
        rw [h4, norm_zero] at h5
        exact hs1.1.ne h5
  rw [h2]
  exact h1.image _ (by fun_prop)

theorem isPreconnected_punctured_half (w : EuclideanPlane) (hw : w 0 = 0) {r : ℝ} (_hr : 0 < r) :
    IsPreconnected ((ball w r ∩ {x | 0 ≤ x 0}) \ {w}) := by
  let e : EuclideanPlane := EuclideanSpace.single 0 1
  have he0 : e 0 = 1 := by simp [e]
  have hen : ‖e‖ = 1 := by simp [e]
  let C : Set EuclideanPlane := ball w r ∩ {x | 0 < x 0}
  have hcv : Convex ℝ C := by
    refine (convex_ball _ _).inter ?_
    intro a ha b hb s t hs ht hst
    have ha' : 0 < a 0 := ha
    have hb' : 0 < b 0 := hb
    change 0 < (s • a + t • b) 0
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le hs with rfl | h1
    · have : t = 1 := by linarith
      subst this
      simpa using hb'
    · have := mul_pos h1 ha'
      have := mul_nonneg ht hb'.le
      linarith
  refine hcv.isPreconnected.subset_closure ?_ ?_
  · rintro y ⟨h1, h2⟩
    refine ⟨⟨h1, le_of_lt (show 0 < y 0 from h2)⟩, fun h3 => ?_⟩
    have h4 : y = w := h3
    have h5 : 0 < y 0 := h2
    rw [h4, hw] at h5
    exact lt_irrefl _ h5
  · rintro y ⟨⟨h1, h2⟩, -⟩
    have h1' : dist y w < r := h1
    rw [mem_closure_iff_seq_limit]
    let δ : ℝ := r - dist y w
    have hδ : 0 < δ := sub_pos.mpr h1'
    let u : ℕ → EuclideanPlane := fun n => y + (δ / 2 / (n + 1)) • e
    have hsm : ∀ n : ℕ, 0 < δ / 2 / (n + 1) := fun n => by positivity
    have hsm2 : ∀ n : ℕ, δ / 2 / (n + 1) ≤ δ / 2 := fun n =>
      div_le_self (by positivity) (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    refine ⟨u, fun n => ⟨?_, ?_⟩, ?_⟩
    · have h3 : dist (u n) y = δ / 2 / (n + 1) := by
        simp only [u, dist_eq_norm, add_sub_cancel_left, norm_smul, hen, mul_one, Real.norm_eq_abs,
          abs_of_pos (hsm n)]
      have h4 := dist_triangle (u n) y w
      have h5 := hsm2 n
      change dist (u n) w < r
      simp only [δ] at *
      linarith
    · change 0 < (u n) 0
      have h2' : 0 ≤ y 0 := h2
      simp only [u, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he0, mul_one]
      linarith [hsm n]
    · have h3 : Filter.Tendsto (fun n : ℕ => δ / 2 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (δ / 2) |>.comp (Filter.tendsto_add_atTop_nat 1)
          |>.congr (by
          intro n
          simp)
      have h4 : Filter.Tendsto u Filter.atTop (𝓝 (y + (0 : ℝ) • e)) :=
        tendsto_const_nhds.add (h3.smul_const e)
      simpa using h4

/-- A point of the half plane has small open neighbourhoods that are connected without the point. -/
theorem halfSpace_punctured (w : EuclideanHalfSpace 2) {O : Set (EuclideanHalfSpace 2)}
  (hO : IsOpen O) (hw : w ∈ O) :
    ∃ O', IsOpen O' ∧ w ∈ O' ∧ O' ⊆ O ∧ IsPreconnected (O' \ {w}) := by
  have hind : IsInducing (fun x : EuclideanHalfSpace 2 => x.1) := ⟨rfl⟩
  obtain ⟨O1, hO1, e1⟩ := hind.isOpen_iff.mp hO
  have hw1 : w.1 ∈ O1 := by
    have : w ∈ (fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' O1 := e1 ▸ hw
    exact this
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hO1 w.1 hw1
  have hbdd : ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ (0 < w.1 0 → r' ≤ w.1 0) := by
    rcases eq_or_lt_of_le w.2 with h0 | h0
    · exact ⟨r, hr, le_rfl, fun h1 => absurd h1 (by rw [← h0]; exact lt_irrefl _)⟩
    · exact ⟨min r (w.1 0), lt_min hr h0, min_le_left _ _, fun _ => min_le_right _ _⟩
  obtain ⟨r', hr', hr'r, hr'w⟩ := hbdd
  refine ⟨(fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' ball w.1 r', isOpen_ball.preimage
    hind.continuous,
    mem_ball_self hr', ?_, ?_⟩
  · intro y hy
    rw [← e1]
    exact hsub (ball_subset_ball hr'r hy)
  refine hind.isPreconnected_image.mp ?_
  rcases eq_or_lt_of_le w.2 with h0 | h0
  · have e : (fun x : EuclideanHalfSpace 2 => x.1) '' ((fun x : EuclideanHalfSpace 2
    => x.1) ⁻¹' ball w.1 r' \ {w}) =
        (ball w.1 r' ∩ {x | 0 ≤ x 0}) \ {w.1} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
        exact ⟨⟨hz, z.2⟩, fun h => hne (Subtype.ext h)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨y, h2⟩, ⟨h1, fun h => h3 (congrArg Subtype.val h)⟩, rfl⟩
    rw [e]
    exact isPreconnected_punctured_half w.1 h0.symm hr'
  · have e : (fun x : EuclideanHalfSpace 2 => x.1) '' ((fun x : EuclideanHalfSpace 2
    => x.1) ⁻¹' ball w.1 r' \ {w}) =
        ball w.1 r' \ {w.1} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
        exact ⟨hz, fun h => hne (Subtype.ext h)⟩
      · rintro ⟨h1, h3⟩
        have h2 : 0 ≤ y 0 := by
          have h4 : |y 0 - w.1 0| ≤ dist y w.1 := by
            have := PiLp.norm_apply_le (y - w.1) 0
            simpa [dist_eq_norm, Real.norm_eq_abs] using this
          have h5 : dist y w.1 < r' := h1
          have h6 := hr'w h0
          have h7 := abs_lt.mp (h4.trans_lt h5)
          linarith [h7.1]
        exact ⟨⟨y, h2⟩, ⟨h1, fun h => h3 (congrArg Subtype.val h)⟩, rfl⟩
    rw [e]
    exact isPreconnected_punctured_ball w.1 hr'

/-- A manifold point has small open neighbourhoods that are connected without the point. -/
theorem IsManifoldPoint.exists_punctured {X : Type u} [TopologicalSpace X] {v : X}
  (hv : IsManifoldPoint v) {N : Set X}
    (hN : IsOpen N) (hvN : v ∈ N) : ∃ N', IsOpen N' ∧ v ∈ N' ∧ N' ⊆ N ∧ IsPreconnected (N' \ {v})
      := by
  obtain ⟨U, V, hU, hV, hvU, ⟨φ⟩⟩ := hv
  let vU : U := ⟨v, hvU⟩
  let O0 : Set V := φ '' (Subtype.val ⁻¹' N)
  have hO0 : IsOpen O0 := φ.isOpenMap _ (hN.preimage continuous_subtype_val)
  obtain ⟨O1, hO1, e1⟩ := isOpen_induced_iff.mp hO0
  have hO : IsOpen (O1 ∩ V) := hO1.inter hV
  have hw : (φ vU).1 ∈ O1 ∩ V := by
    refine ⟨?_, (φ vU).2⟩
    have : φ vU ∈ O0 := ⟨vU, hvN, rfl⟩
    rw [← e1] at this
    exact this
  obtain ⟨O', hO', hwO', hsub, hconn⟩ := halfSpace_punctured _ hO hw
  have hVO : O' ⊆ V := hsub.trans inter_subset_right
  let G : Set V := Subtype.val ⁻¹' O'
  have hG : IsOpen G := hO'.preimage continuous_subtype_val
  let N' : Set X := (fun y : U => y.1) '' (φ ⁻¹' G)
  have hN' : IsOpen N' := hU.isOpenMap_subtype_val _ (hG.preimage φ.continuous)
  refine ⟨N', hN', ⟨vU, hwO', rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : (φ y).1 ∈ O1 := (hsub hy).1
    have h2 : φ y ∈ O0 := by
      rw [← e1]
      exact h1
    obtain ⟨y', hy', e⟩ := h2
    rw [φ.injective e] at hy'
    exact hy'
  · have hm : (fun z : EuclideanHalfSpace 2 => z) ⁻¹' O' = O' := rfl
    have himg : N' \ {v} = (fun z : V => (φ.symm z).1) '' (Subtype.val ⁻¹' (O' \ {(φ vU).1})) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hne⟩
        refine ⟨φ y, ⟨hy, fun h => hne ?_⟩, by simp⟩
        have : φ y = φ vU := Subtype.ext h
        rw [φ.injective this]
        rfl
      · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
        refine ⟨⟨φ.symm z, ?_, rfl⟩, fun h => hne ?_⟩
        · simpa [G] using hz
        · have h2 : φ.symm z = vU := Subtype.ext h
          rw [← h2]
          simp
    rw [himg]
    have hind : IsInducing (Subtype.val : V → EuclideanHalfSpace 2) := IsInducing.subtypeVal
    have hpc : IsPreconnected (Subtype.val ⁻¹' (O' \ {(φ vU).1}) : Set V) := by
      refine hind.isPreconnected_image.mp ?_
      rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr
        (sdiff_subset.trans hVO)]
      exact hconn
    exact hpc.image _ (continuous_subtype_val.comp φ.symm.continuous).continuousOn

/-- The set of steps of a finite family is compact. -/
theorem isCompact_stp {W : ℕ → List Letter} (hW : {i | W i ≠ []}.Finite) :
    IsCompact {x : (ℕ × ℂ) × (ℕ × ℂ) | Stp W x.1 x.2} := by
  classical
  let Sd : Set (ℕ × ℕ × Bool) := {x | ∃ k, (W x.1)[x.2.1]? = some (k, x.2.2)}
  have hSd : Sd.Finite := by
    refine (hW.biUnion fun i _ => ((finite_singleton i).prod ((finite_lt_nat (W i).length).prod
      (finite_univ (α := Bool))))).subset ?_
    rintro ⟨i, p, ε⟩ ⟨k, h⟩
    have h1 : (W i)[p]? = some (k, ε) := h
    have hlt : p < (W i).length := (List.getElem?_eq_some_iff.mp h1).1
    refine mem_biUnion (x := i) (fun he => ?_) ⟨rfl, hlt, mem_univ _⟩
    simp [he] at hlt
  let pc : (ℕ × ℕ × Bool) × (ℕ × ℕ × Bool) → Set ((ℕ × ℂ) × (ℕ × ℂ)) := fun x =>
    (fun t : ℝ => ((x.1.1, sdPt (W x.1.1).length x.1.2.1 x.1.2.2 t),
      (x.2.1, sdPt (W x.2.1).length x.2.2.1 x.2.2.2 t))) '' Icc 0 1
  have hcp : ∀ x, IsCompact (pc x) := fun x => by
    refine isCompact_Icc.image ?_
    have hs : ∀ n p b, Continuous (sdPt n p b) := fun n p b => by
      unfold sdPt
      split_ifs
      · exact (continuous_per n).comp (by fun_prop)
      · exact (continuous_per n).comp (by fun_prop)
    exact (continuous_const.prodMk (hs _ _ _)).prodMk (continuous_const.prodMk (hs _ _ _))
  have hT : ((Sd ×ˢ Sd) ∩ {x | (x.1.1, x.1.2.1) ≠ (x.2.1, x.2.2.1) ∧ ∃ k, (W x.1.1)[x.1.2.1]?
    = some (k, x.1.2.2) ∧
      (W x.2.1)[x.2.2.1]? = some (k, x.2.2.2)}).Finite := (hSd.prod hSd).subset inter_subset_left
  have e : {x : (ℕ × ℂ) × (ℕ × ℂ) | Stp W x.1 x.2} = ⋃ x ∈ ((Sd ×ˢ Sd) ∩ {x | (x.1.1, x.1.2.1) ≠
    (x.2.1, x.2.2.1) ∧
      ∃ k, (W x.1.1)[x.1.2.1]? = some (k, x.1.2.2) ∧ (W x.2.1)[x.2.2.1]? = some
        (k, x.2.2.2)}), pc x := by
    ext ⟨a, b⟩
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
      exact ⟨((i, p, ε), (j, q, ε')), ⟨⟨⟨k, h1⟩, ⟨k, h2⟩⟩, h3, k, h1, h2⟩, t, ht, rfl⟩
    · rintro ⟨⟨⟨i, p, ε⟩, ⟨j, q, ε'⟩⟩, ⟨-, h3, k, h1, h2⟩, t, ht, e⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
  rw [e]
  exact hT.isCompact_biUnion fun x _ => hcp x

theorem Stp.symm {W : ℕ → List Letter} {a b : ℕ × ℂ} (h : Stp W a b) : Stp W b a := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  exact ⟨j, i, q, p, k, ε', ε, t, h2, h1, h3.symm, ht, rfl, rfl⟩

theorem mem_closure_punctured_ball {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    z ∈ closure (closedBall (0 : ℂ) 1 \ {z}) := by
  have h1 : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {z}ᶜ) := by
    intro y hy
    refine isOpen_ball.inter_closure ⟨hy, ?_⟩
    rw [closure_compl_singleton]
    exact mem_univ _
  have h2 : z ∈ closure (ball (0 : ℂ) 1) := by
    rwa [closure_ball _ one_ne_zero]
  have h3 := closure_minimal h1 isClosed_closure h2
  have h4 : ball (0 : ℂ) 1 ∩ {z}ᶜ ⊆ closedBall (0 : ℂ) 1 \ {z} := fun y hy =>
    ⟨ball_subset_closedBall hy.1, hy.2⟩
  exact closure_mono h4 h3

variable {X : Type u} [TopologicalSpace X] [T2Space X] {W : ℕ → List Letter} {f : ℕ × ℂ → X}

/-- If the corners over a manifold point `v` are not all related, the punctured neighbourhoods of
`v` fall apart. -/
theorem prel_of_vertex (hW : {i | W i ≠ []}.Finite) (hc : ContinuousOn f (Dsk W)) (hs : f '' Dsk W
  = univ)
    (hst : ∀ a b, Stp W a b → f a = f b)
    (hinj : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, a.1 = b.1 → f a = f b → a = b)
    {V : Set X} (hV : V.Finite) {v : X} (hv : IsManifoldPoint v) (hZ : (Dsk W ∩ f ⁻¹' {v}).Finite)
    (hoff : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, f a = f b → f a ∉ V → PRel W a b)
    {a b : ℕ × ℂ} (ha : a ∈ Dsk W) (hb : b ∈ Dsk W) (hav : f a = v) (hbv : f b = v) : PRel W a b
      := by
  classical
  by_contra hnot
  have hDc : IsCompact (Dsk W) := isCompact_Dsk hW
  let A : Set (ℕ × ℂ) := {z | z ∈ Dsk W ∧ f z = v ∧ PRel W a z}
  let B : Set (ℕ × ℂ) := {z | z ∈ Dsk W ∧ f z = v ∧ ¬ PRel W a z}
  have hAf : A.Finite := hZ.subset fun z hz => by exact ⟨hz.1, hz.2.1⟩
  have hBf : B.Finite := hZ.subset fun z hz => by exact ⟨hz.1, hz.2.1⟩
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun z hz hz' => hz'.2.2 hz.2.2
  obtain ⟨U₀, hU₀, hBU₀, hcl₀⟩ : ∃ U₀, IsOpen U₀ ∧ B ⊆ U₀ ∧ closure U₀ ⊆ Aᶜ :=
    normal_exists_closure_subset hBf.isClosed hAf.isClosed.isOpen_compl
      (subset_compl_iff_disjoint_left.mpr hAB)
  obtain ⟨UA, hUA, hAUA, hclA⟩ : ∃ UA, IsOpen UA ∧ A ⊆ UA ∧ closure UA ⊆ (closure U₀)ᶜ :=
    normal_exists_closure_subset hAf.isClosed isClosed_closure.isOpen_compl
      (fun z hz hz' => hcl₀ hz' hz)
  let UB := U₀
  have hdisj : ∀ z, z ∈ closure UA → z ∈ closure UB → False := fun z h1 h2 => hclA h1 h2
  have hdisj' : ∀ z, z ∈ UA → z ∉ UB := fun z h1 h2 => hdisj z (subset_closure h1)
    (subset_closure h2)
  let R : Set ((ℕ × ℂ) × (ℕ × ℂ)) := {x | Stp W x.1 x.2} ∩ (closure UA ×ˢ closure UB)
  have hRc : IsCompact R := (isCompact_stp hW).inter_right (isClosed_closure.prod isClosed_closure)
  let C : Set X := (fun x : (ℕ × ℂ) × (ℕ × ℂ) => f x.1) '' R
  have hCc : IsCompact C := by
    refine hRc.image_of_continuousOn ?_
    exact hc.comp continuousOn_fst fun x hx => (hx.1 : Stp W x.1 x.2).mem_Dsk.1
  have hvC : v ∉ C := by
    rintro ⟨⟨x, y⟩, ⟨hs1, hx, hy⟩, hfx⟩
    have hs2 : Stp W x y := hs1
    have hfx' : f x = v := hfx
    have hfy : f y = v := (hst x y hs2).symm.trans hfx'
    obtain ⟨hxD, hyD⟩ := hs2.mem_Dsk
    have hxA : x ∈ A := by
      by_contra hn
      have : x ∈ B := ⟨hxD, hfx', fun h => hn ⟨hxD, hfx', h⟩⟩
      exact hdisj x hx (subset_closure (hBU₀ this))
    have hyB : y ∈ B := ⟨hyD, hfy, fun h => hdisj y (subset_closure (hAUA ⟨hyD, hfy, h⟩)) hy⟩
    exact hyB.2.2 (.trans _ _ _ hxA.2.2 (.rel _ _ hs2))
  let C1 : Set X := f '' (Dsk W \ (UA ∪ UB))
  have hC1c : IsCompact C1 :=
    (hDc.diff (hUA.union hU₀)).image_of_continuousOn (hc.mono sdiff_subset)
  have hvC1 : v ∉ C1 := by
    rintro ⟨z, ⟨hzD, hz⟩, hfz⟩
    by_cases hp : PRel W a z
    · exact hz (.inl (hAUA ⟨hzD, hfz, hp⟩))
    · exact hz (.inr (hBU₀ ⟨hzD, hfz, hp⟩))
  have hC2f : (V \ {v}).Finite := hV.subset sdiff_subset
  let N : Set X := (C ∪ C1 ∪ (V \ {v}))ᶜ
  have hN : IsOpen N := ((hCc.isClosed.union hC1c.isClosed).union hC2f.isClosed).isOpen_compl
  have hvN : v ∈ N := by
    rintro ((h | h) | h)
    · exact hvC h
    · exact hvC1 h
    · exact h.2 rfl
  obtain ⟨N', hN', hvN', hsub, hconn⟩ := hv.exists_punctured hN hvN
  let FA : Set X := f '' (Dsk W \ UB)
  let FB : Set X := f '' (Dsk W \ UA)
  have hFA : IsClosed FA := ((hDc.diff hU₀).image_of_continuousOn (hc.mono sdiff_subset)).isClosed
  have hFB : IsClosed FB := ((hDc.diff hUA).image_of_continuousOn (hc.mono sdiff_subset)).isClosed
  have hcov : N' \ {v} ⊆ FA ∪ FB := by
    rintro y ⟨hy, -⟩
    have h1 : y ∈ f '' Dsk W := hs ▸ mem_univ y
    obtain ⟨x, hx, rfl⟩ := h1
    by_cases hxA : x ∈ UA
    · exact .inl ⟨x, ⟨hx, hdisj' x hxA⟩, rfl⟩
    · exact .inr ⟨x, ⟨hx, hxA⟩, rfl⟩
  have hnear : ∀ (z : ℕ × ℂ) (U : Set (ℕ × ℂ)), z ∈ Dsk W → f z = v → IsOpen U → z ∈ U →
      ∃ y ∈ N' \ {v}, ∃ z' ∈ Dsk W, z' ∈ U ∧ f z' = y := by
    rintro ⟨i, z⟩ U hzD hfz hU hzU
    have hz1 : z ∈ closedBall (0 : ℂ) 1 := by simpa using hzD.2
    have hmap : MapsTo (fun w : ℂ => (i, w)) (closedBall (0 : ℂ) 1) (Dsk W) := fun w hw =>
      ⟨hzD.1, by simpa using hw⟩
    have hcw : ContinuousOn (fun w : ℂ => f (i, w)) (closedBall 0 1) :=
      hc.comp (by fun_prop) hmap
    have hcont := hcw z hz1
    have hopen : (fun w : ℂ => (i, w)) ⁻¹' U ∈ 𝓝 z :=
      (hU.preimage (by fun_prop)).mem_nhds hzU
    have hn : (fun w : ℂ => f (i, w)) ⁻¹' N' ∈ 𝓝[closedBall 0 1] z :=
      hcont (hN'.mem_nhds (by simpa [hfz] using hvN'))
    obtain ⟨Q, hQ, hQo, hzQ⟩ := mem_nhdsWithin.mp hn
    have hcl := mem_closure_punctured_ball hz1
    obtain ⟨w, ⟨hwQ, hwU⟩, hw⟩ := mem_closure_iff.mp hcl _ (hQ.inter (hU.preimage (by fun_prop)))
      ⟨hQo, hzU⟩
    have hwN : f (i, w) ∈ N' := hzQ ⟨hwQ, hw.1⟩
    refine ⟨f (i, w), ⟨hwN, fun he => hw.2 ?_⟩, (i, w), hmap hw.1, hwU, rfl⟩
    have := hinj (i, w) (hmap hw.1) (i, z) hzD rfl (he.trans hfz.symm)
    exact (Prod.mk.inj this).2
  have haA : a ∈ A := ⟨ha, hav, .refl _⟩
  have hbB : b ∈ B := ⟨hb, hbv, hnot⟩
  obtain ⟨y1, hy1, z1, hz1, hz1U, rfl⟩ := hnear a UA ha hav hUA (hAUA haA)
  obtain ⟨y2, hy2, z2, hz2, hz2U, rfl⟩ := hnear b UB hb hbv hU₀ (hBU₀ hbB)
  obtain ⟨y, hy, hyA, hyB⟩ := isPreconnected_closed_iff.mp hconn FA FB hFA hFB hcov
    ⟨_, hy1, z1, ⟨hz1, hdisj' z1 hz1U⟩, rfl⟩ ⟨_, hy2, z2, ⟨hz2, fun h => hdisj' z2 h hz2U⟩, rfl⟩
  obtain ⟨x1, ⟨hx1, hx1U⟩, rfl⟩ := hyA
  obtain ⟨x2, ⟨hx2, hx2U⟩, he⟩ := hyB
  have hyN : f x1 ∈ N := hsub hy.1
  have hoffcov : ∀ x ∈ Dsk W, f x = f x1 → x ∈ UA ∪ UB := fun x hx hfx => by
    by_contra hn
    exact hyN (.inl (.inr ⟨x, ⟨hx, hn⟩, hfx⟩))
  have hx1A : x1 ∈ UA := (hoffcov x1 hx1 rfl).resolve_right hx1U
  have hx2B : x2 ∈ UB := (hoffcov x2 hx2 he).resolve_left hx2U
  have hnotV : f x1 ∉ V := fun h => hyN (.inr ⟨h, hy.2⟩)
  have hrel : PRel W x1 x2 := hoff x1 hx1 x2 hx2 he.symm hnotV
  have hstep : ∀ x x', PRel W x x' → x ∈ Dsk W → f x = f x1 → (x ∈ UA ↔ x' ∈ UA) ∧ f x' = f x1
    ∧ x' ∈ Dsk W := by
    intro x x' h
    induction h with
    | rel x x' hs =>
      intro hxD hfx
      have hfx' : f x' = f x1 := (hst x x' hs).symm.trans hfx
      have hxD' := hs.mem_Dsk.2
      refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, hfx', hxD'⟩
      · by_contra hn
        have h2 : x' ∈ UB := (hoffcov x' hxD' hfx').resolve_left hn
        exact hyN (.inl (.inl ⟨(x, x'), ⟨hs, subset_closure h1, subset_closure h2⟩, hfx⟩))
      · by_contra hn
        have h2 : x ∈ UB := (hoffcov x hxD hfx).resolve_left hn
        exact hyN (.inl (.inl ⟨(x', x), ⟨hs.symm, subset_closure h1, subset_closure h2⟩, hfx'⟩))
    | refl x => exact fun hxD hfx => ⟨Iff.rfl, hfx, hxD⟩
    | symm x x' h ih =>
      intro hxD hfx
      have hmem : x ∈ Dsk W := (prel_mem_iff h).mpr hxD
      have hf' : f x = f x1 := by
        have key : ∀ p q, PRel W p q → f p = f q := fun p q hpq => by
          induction hpq with
          | rel _ _ hs => exact hst _ _ hs
          | refl _ => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
        exact (key _ _ h).trans hfx
      exact ⟨(ih hmem hf').1.symm, hf', hmem⟩
    | trans x x' x'' _ _ i1 i2 =>
      intro hxD hfx
      obtain ⟨h1, h2, h3⟩ := i1 hxD hfx
      obtain ⟨h4, h5, h6⟩ := i2 h3 h2
      exact ⟨h1.trans h4, h5, h6⟩
  exact hx2U ((hstep _ _ hrel hx1 rfl).1.mp hx1A)

end GraphMinor.Surface
