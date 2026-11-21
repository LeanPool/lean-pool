/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.SixVertices
public import LeanPool.RupertMinimality.Minimality.Thm73
public import LeanPool.RupertMinimality.Minimality.BadViews
public import LeanPool.RupertMinimality.Minimality.Perturb
public import Mathlib.Analysis.Convex.Caratheodory

/-! # Unimodal -/

@[expose] public section

namespace RupertMinimality

/-!
# L7: unimodal silhouettes

Step 3 of `minimality.md`, in the standard view (`projXy`, depth =
coordinate 2).

* `exists_forces_of_not_firstOrderInward` (Lemma 7.1, the direction used):
  if no first-order motion is strictly inward, there are horizontal *corner
  forces* `f v` in the normal cones of the shadow at the points of `V`, not all
  zero, with zero sum (E1), zero depth moment (E2) and zero torque (E3).  It is
  stated with normal cones (`normalConeAt`), so it needs neither (G1) nor
  edge normals.
* `hasHorizontalDoubleNormal_of_forces` (Theorem 7.3 (⇒), pure polygon form):
  forces in the normal cones of a strictly convex counterclockwise polygon,
  balanced as in (E1)–(E3), with cyclically unimodal distinct depths, force a
  horizontal double normal of the silhouette cycle.
* `exists_firstOrderInward_of_unimodal`, `isRupert_of_unimodalView` (Theorem
  7.3 at an explicit view): a generic unimodal silhouette without horizontal
  double normal gives a passage.
* `exists_badPlanes` (Lemma 7.4) and `isRupert_of_genericUnimodalView`
  (Theorem 7.5): a generic unimodal view suffices.  The robust forms
  `isRupert_of_eventually_unimodal` and `isRupert_of_open_unimodal` allow
  depth ties at the given view.
* Theorem 7.7 and Corollary 7.8 are in `Prism.lean` and `Octahedron.lean`.

The silhouette at an explicit view is given by a cyclic list of points
`x : ZMod k → ℝ³` of `V`: (G1) is `IsCcwPolygon (projXy ∘ x)` (strictly convex,
counterclockwise) together with "every other point of `V` projects into the
interior", and (G2) is injectivity of the depths, part of `IsCyclicUnimodal`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The convex hull of a compact set in a finite-dimensional normed space is
compact (Carathéodory). -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : Set E} (hA : IsCompact A) : IsCompact (convexHull ℝ A) := by
  classical
  set n := Module.finrank ℝ E + 1
  let Φ : (Fin n → ℝ) × (Fin n → E) → E := fun wz => ∑ j, wz.1 j • wz.2 j
  have hΦ : Continuous Φ := by fun_prop
  let S : Set (Fin n → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
  have hS : IsCompact S := by
    refine (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (0 : ℝ)) (b :=
      1)).of_isClosed_subset
      ?_ ?_
    · have h1 : IsClosed {w : Fin n → ℝ | ∀ i, 0 ≤ w i} :=
        by simpa only [Set.ofPred_forall] using
          isClosed_iInter fun i : Fin n => isClosed_le continuous_const (continuous_apply i)
      have h2 : IsClosed {w : Fin n → ℝ | ∑ i, w i = 1} :=
        isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
      exact h1.inter h2
    · rintro w ⟨hw0, hw1⟩ i -
      refine ⟨hw0 i, ?_⟩
      rw [← hw1]
      exact Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
  have hD : IsCompact (S ×ˢ Set.univ.pi (fun _ : Fin n => A)) :=
    IsCompact.prod hS (isCompact_univ_pi fun _ => hA)
  suffices h : convexHull ℝ A = Φ '' (S ×ˢ Set.univ.pi (fun _ => A)) by
    rw [h]; exact hD.image hΦ
  apply le_antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hzA, hind, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card ι ≤ Fintype.card (Fin n) by
        rw [Fintype.card_fin]
        exact hind.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1))
    have hne : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hw1
    obtain ⟨i₀⟩ := hne
    let w' : Fin n → ℝ := fun j => ∑ i ∈ Finset.univ.filter (fun i => e i = j), w i
    let z' : Fin n → E := fun j => if h : ∃ i, e i = j then z h.choose else z i₀
    have hz' : ∀ i, z' (e i) = z i := fun i => by
      have h : ∃ i', e i' = e i := ⟨i, rfl⟩
      simp only [z', dite_eq_left h]
      rw [e.injective h.choose_spec]
    refine ⟨(w', z'), ⟨⟨fun j => Finset.sum_nonneg fun i _ => (hw0 i).le, ?_⟩, fun j _ => ?_⟩, ?_⟩
    · rw [← hw1]; exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (e i)) w
    · simp only [z']
      split_ifs with h
      · exact hzA ⟨_, rfl⟩
      · exact hzA ⟨_, rfl⟩
    · simp only [Φ, w', Finset.sum_smul]
      rw [← hx, ← Finset.sum_fiberwise_of_maps_to (g := e) (fun i _ => Finset.mem_univ (e i))]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [← (Finset.mem_filter.mp hi).2, hz']
  · rintro _ ⟨⟨w, z⟩, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
    exact (convex_convexHull ℝ A).sum_mem (fun j _ => hw0 j) hw1
      (fun j _ => subset_convexHull ℝ A (hz j (Set.mem_univ j)))

/-- The horizontal lift `n ↦ (n, 0)`. -/
noncomputable def liftH (n : ℝ²) : ℝ³ := !₂[n 0, n 1, 0]

theorem inner_screenVel (ω τ v : ℝ³) (n : ℝ²) :
    ⟪n, screenVel ω τ v⟫ = ⟪ω, cross v (liftH n)⟫ + ⟪τ, liftH n⟫ := by
  simp [screenVel, projXy, crossMatrix, cross, liftH, Matrix.toLpLin_apply, dotProduct,
    Fin.sum_univ_three, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem normalConeAt_isClosed (S : Set ℝ²) (p : ℝ²) : IsClosed (normalConeAt S p) := by
  have : normalConeAt S p = ⋂ q ∈ S, {n | ⟪n, q - p⟫ ≤ 0} := by ext; simp [normalConeAt]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_le (continuous_id.inner continuous_const)
    continuous_const

/-- **Lemma 7.1 (corner forces), the direction used.**  If no first-order
motion is strictly inward, there are forces `f v ∈ N_S(P v)` (`v ∈ V`), not all
zero, with `Σ f = 0`, `Σ z f = 0`, `Σ P v × f = 0`.  (Points projecting into
the interior of the shadow get `f v = 0`, their normal cone being `{0}`.) -/
theorem exists_forces_of_not_firstOrderInward (V : Finset ℝ³)
    (hint : (interior (projXy '' convexHull ℝ (V : Set ℝ³))).Nonempty)
    (h : ∀ ω τ : ℝ³, ¬ FirstOrderInward V ω τ) :
    ∃ f : ℝ³ → ℝ², (∀ v ∈ V, f v ∈ normalConeAt (projXy '' convexHull ℝ (V : Set ℝ³))
        (projXy v)) ∧ (∃ v ∈ V, f v ≠ 0) ∧ ∑ v ∈ V, f v = 0 ∧ ∑ v ∈ V, v 2 • f v = 0 ∧
      ∑ v ∈ V, cross2 (projXy v) (f v) = 0 := by
  classical
  set S := projXy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, show (projXy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  obtain ⟨c, hc⟩ := hint
  have hPv : ∀ v ∈ V, projXy v ∈ S := fun v hv => ⟨v, subset_convexHull ℝ _ hv, rfl⟩
  -- unit normals are strictly negative on the direction to the interior point `c`
  have hneg : ∀ v ∈ V, ∀ n ∈ normalConeAt S (projXy v), n ≠ 0 → ⟪n, c - projXy v⟫ < 0 := by
    intro v hv n hn hn0
    have hin : IsInwardAt S (projXy v) (c - projXy v) :=
      ⟨1, one_pos, by rw [one_smul, add_sub_cancel]; exact hc⟩
    exact hin.inner_neg hn0 hn
  let K : ℝ³ → Set ℝ² := fun v => normalConeAt S (projXy v) ∩ Metric.sphere 0 1
  have hK : ∀ v, IsCompact (K v) := fun v =>
    (isCompact_sphere (0 : ℝ²) 1).inter_left (normalConeAt_isClosed _ _)
  let a : ℝ³ → ℝ² → ℝ³ × ℝ³ := fun v n => (cross v (liftH n), liftH n)
  have ha : ∀ v, Continuous (a v) := fun v => by
    simp only [a, cross, liftH]; fun_prop
  set A := ⋃ v ∈ V, a v '' K v with hAdef
  have hA : IsCompact A := V.isCompact_biUnion fun v _ => (hK v).image (ha v)
  have hC := isCompact_convexHull_of_isCompact hA
  by_cases h0 : (0 : ℝ³ × ℝ³) ∈ convexHull ℝ A
  · rw [_root_.convexHull_eq] at h0
    obtain ⟨ι, t, w, z, hw0, hw1, hzA, hsum⟩ := h0
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hsum
    have hz' : ∀ i ∈ t, ∃ v ∈ V, ∃ n ∈ K v, a v n = z i := by
      intro i hi
      have := hzA i hi
      simp only [hAdef, Set.mem_iUnion, Set.mem_image] at this
      obtain ⟨v, hv, n, hn, h⟩ := this
      exact ⟨v, hv, n, hn, h⟩
    choose! vv hvV nn hnK hza using hz'
    have hsum' : ∑ i ∈ t, w i • a (vv i) (nn i) = 0 := by
      rw [← hsum]; exact Finset.sum_congr rfl fun i hi => by rw [hza i hi]
    have hfst := congrArg Prod.fst hsum'
    have hsnd := congrArg Prod.snd hsum'
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero, a] at hfst hsnd
    let f : ℝ³ → ℝ² := fun v => ∑ i ∈ t.filter (fun i => vv i = v), w i • nn i
    have hmaps : ∀ i ∈ t, vv i ∈ V := fun i hi => hvV i hi
    have hn0 : ∀ i ∈ t, nn i ≠ 0 := fun i hi h0 => by
      have := (hnK i hi).2; simp [h0] at this
    refine ⟨f, fun v hv q hq => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [f, sum_inner, real_inner_smul_left]
      refine Finset.sum_nonpos fun i hi => ?_
      obtain ⟨hit, hiv⟩ := Finset.mem_filter.mp hi
      have := (hnK i hit).1 q hq
      rw [hiv] at this
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 i hit) this
    · obtain ⟨i, hit, hwi⟩ : ∃ i ∈ t, 0 < w i := by
        by_contra hcon; push Not at hcon
        have : ∑ i ∈ t, w i ≤ 0 := Finset.sum_nonpos hcon
        linarith
      refine ⟨vv i, hvV i hit, fun h => ?_⟩
      have hlt : ⟪f (vv i), c - projXy (vv i)⟫ < 0 := by
        simp only [f, sum_inner, real_inner_smul_left]
        have hi' : i ∈ t.filter (fun j => vv j = vv i) := Finset.mem_filter.mpr ⟨hit, rfl⟩
        rw [← Finset.add_sum_erase _ _ hi']
        have hstrict : w i * ⟪nn i, c - projXy (vv i)⟫ < 0 :=
          mul_neg_of_pos_of_neg hwi (hneg (vv i) (hvV i hit) (nn i) (hnK i hit).1 (hn0 i hit))
        have hrest : ∑ j ∈ (t.filter (fun j => vv j = vv i)).erase i,
            w j * ⟪nn j, c - projXy (vv i)⟫ ≤ 0 := by
          refine Finset.sum_nonpos fun j hj => ?_
          obtain ⟨hjt, hjv⟩ := Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)
          have := hneg (vv j) (hvV j hjt) (nn j) (hnK j hjt).1 (hn0 j hjt)
          rw [hjv] at this
          exact mul_nonpos_of_nonneg_of_nonpos (hw0 j hjt) this.le
        linarith
      rw [h, inner_zero_left] at hlt
      exact lt_irrefl _ hlt
    · rw [show ∑ v ∈ V, f v = ∑ i ∈ t, w i • nn i from
        Finset.sum_fiberwise_of_maps_to hmaps _]
      ext j; fin_cases j
      · have := congrArg (fun x : ℝ³ => x 0) hsnd
        simpa [liftH] using this
      · have := congrArg (fun x : ℝ³ => x 1) hsnd
        simpa [liftH] using this
    · have hE2 : ∑ v ∈ V, v 2 • f v = ∑ i ∈ t, (vv i 2 * w i) • nn i := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [f, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2, mul_comm]
      rw [hE2]
      ext j; fin_cases j
      · simpa [cross, liftH, mul_assoc, mul_comm, mul_left_comm] using
          congrArg (fun x : ℝ³ => x 1) hfst
      · simpa [cross, liftH, mul_assoc, mul_comm, mul_left_comm] using
          congrArg (fun x : ℝ³ => -(x 0)) hfst
    · have hE3 : ∑ v ∈ V, cross2 (projXy v) (f v) =
          ∑ i ∈ t, w i * (vv i 0 * nn i 1 - vv i 1 * nn i 0) := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [f, cross2, projXy]
        simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
        simp
        ring
      rw [hE3]
      have := congrArg (fun x : ℝ³ => x 2) hfst
      simp [cross, liftH] at this
      linear_combination this
  · -- separate `0` from the compact convex hull
    exfalso
    obtain ⟨φ, u, u', hφ, huu', hφ0⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ A) hC (convex_singleton 0) isClosed_singleton
      (Set.disjoint_singleton_right.mpr h0)
    have hφneg : ∀ x ∈ A, φ x < 0 := fun x hx => by
      have h1 := hφ x (subset_convexHull ℝ A hx)
      have h2 := hφ0 0 rfl
      rw [map_zero] at h2
      linarith
    set ω := (InnerProductSpace.toDual ℝ ℝ³).symm (φ.comp (ContinuousLinearMap.inl ℝ ℝ³ ℝ³))
    set τ := (InnerProductSpace.toDual ℝ ℝ³).symm (φ.comp (ContinuousLinearMap.inr ℝ ℝ³ ℝ³))
    have hφa : ∀ v n, φ (a v n) = ⟪n, screenVel ω τ v⟫ := by
      intro v n
      rw [inner_screenVel, InnerProductSpace.toDual_symm_apply,
        InnerProductSpace.toDual_symm_apply]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, a]
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    apply h ω τ
    intro v hv
    refine isInwardAt_of_forall_normal hS ⟨c, hc⟩ (subset_closure (hPv v hv)) _
      (fun n hn0 hn => ?_)
    have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    have hmem : (1 / ‖n‖) • n ∈ K v := by
      refine ⟨fun q hq => ?_, by simp [norm_smul, hnpos.ne']⟩
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hn q hq)
    have := hφneg _ (Set.mem_biUnion hv ⟨_, hmem, rfl⟩)
    rw [hφa, real_inner_smul_left] at this
    by_contra hcon; push Not at hcon
    have := mul_nonneg (show 0 ≤ 1 / ‖n‖ by positivity) hcon
    linarith

/-- **Theorem 7.3 (⇒), polygon form.**  Forces in the normal cones of a
strictly convex counterclockwise polygon, not all zero, with zero sum, zero
depth moment and zero torque, at cyclically unimodal distinct depths, force a
horizontal double normal. -/
theorem hasHorizontalDoubleNormal_of_forces {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (z : ZMod k → ℝ) (hp : IsCcwPolygon p) (hz : IsCyclicUnimodal z) (f : ZMod k → ℝ²)
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) (hne : ∃ i, f i ≠ 0)
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (h3 : ∑ i, cross2 (p i) (f i) = 0) :
    HasHorizontalDoubleNormal p z := by
  classical
  have hk := hp.1
  set Sup := univ.filter (fun i => f i ≠ 0) with hSup
  have hSupne : Sup.Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [hSup, hi]⟩
  obtain ⟨B, hBS, hBmin⟩ := Sup.exists_min_image z hSupne
  obtain ⟨T₀, hTS, hTmax⟩ := Sup.exists_max_image z hSupne
  have hfB : f B ≠ 0 := (mem_filter.mp hBS).2
  have hfT : f T₀ ≠ 0 := (mem_filter.mp hTS).2
  have hBT : B ≠ T₀ := by
    intro hBT
    have hall : ∀ i, f i ≠ 0 → i = B := fun i hi => by
      have e1 := hBmin i (by simp [hSup, hi])
      have e2 := hTmax i (by simp [hSup, hi])
      rw [← hBT] at e2
      exact hz.1 (le_antisymm e2 e1)
    apply hfB
    rw [← h1, ← add_sum_erase _ _ (mem_univ B)]
    have : ∑ i ∈ univ.erase B, f i = 0 := sum_eq_zero fun i hi => by
      by_contra h; exact (mem_erase.mp hi).1 (hall i h)
    rw [this, add_zero]
  set T := (T₀ - B).val with hTdef
  have hT0 : 0 < T := by
    rw [hTdef]; exact (ZMod.val_pos).mpr (sub_ne_zero.mpr hBT.symm)
  have hTk : T < k := ZMod.val_lt _
  have hBT' : B + (T : ZMod k) = T₀ := by rw [hTdef, ZMod.natCast_zmod_val]; ring
  set g : ℕ → ℝ² := fun n => f (B + n) with hg
  set ζ : ℕ → ℝ := fun n => z (B + n) with hζ
  have hg0 : g 0 = f B := by simp [hg]
  have hgT : g T = f T₀ := by simp only [hg, hBT']
  have hζinj : ∀ a b, a < k → b < k → a ≠ b → ζ a ≠ ζ b := fun a b ha hb hab h =>
    zmod_add_ne ha hb hab B (hz.1 h)
  have hζmin : ∀ a, g a ≠ 0 → ζ 0 ≤ ζ a := fun a ha => by
    simp only [hζ, Nat.cast_zero, add_zero]; exact hBmin _ (by simpa [hSup] using ha)
  have hζmax : ∀ a, g a ≠ 0 → ζ a ≤ ζ T := fun a ha => by
    simp only [hζ, hBT']; exact hTmax _ (by simpa [hSup] using ha)
  have hζ0T : ζ 0 < ζ T := lt_of_le_of_ne (hζmin T (by rw [hgT]; exact hfT))
    (hζinj 0 T (by omega) hTk (by omega))
  have hcore := forces_parallel g ζ k T hT0 hTk (by rw [hg0]; exact hfB) (by rw [hgT]; exact hfT)
    (by rw [← sum_zmod_eq_sum_range f B]; exact h1)
    (by rw [← sum_zmod_eq_sum_range (fun i => z i • f i) B]; exact h2)
    (by
      intro a b hab hbT ha hb
      by_contra hc; push Not at hc
      have hlt : ζ b < ζ a := lt_of_le_of_ne hc (hζinj b a (by omega) (by omega) (by omega))
      have ha0 : 0 < a := by
        by_contra h0; have : a = 0 := by omega
        subst this; linarith [hζmin b hb]
      have hbT' : b < T := by
        by_contra h0; have : b = T := by omega
        subst this; linarith [hζmax a ha]
      exact hz.noZig B ha0 hab hbT' hTk (Or.inl ⟨lt_of_le_of_ne (hζmin a ha)
        (hζinj 0 a (by omega) (by omega) (by omega)), hlt,
        lt_of_le_of_ne (hζmax b hb) (hζinj b T (by omega) hTk (by omega)), hζ0T⟩))
    (by
      intro a b hTa hab hbk ha hb
      by_contra hc; push Not at hc
      have hlt : ζ a < ζ b := lt_of_le_of_ne hc (hζinj a b (by omega) hbk (by omega))
      have haT : T < a := by
        by_contra h0; have : a = T := by omega
        subst this; linarith [hζmax b hb]
      exact hz.noZig B hT0 haT hab hbk (Or.inl ⟨hζ0T,
        lt_of_le_of_ne (hζmax a ha) (hζinj a T (by omega) hTk (by omega)), hlt,
        lt_of_le_of_ne (hζmin b hb) (hζinj 0 b (by omega) hbk (by omega))⟩))
    (fun a ha0 hak ha => lt_of_le_of_ne (hζmin a ha) (hζinj 0 a (by omega) hak (by omega)))
    (fun D => hp.forces_SS hf B D)
    (by
      obtain ⟨j, hj, h1', h2'⟩ := hp.forces_oriented hf B
      exact ⟨j, hj, fun s a b => by rw [hg0]; exact h1' s a b,
        fun s a b => by rw [hg0]; exact h2' s a b⟩)
    (by
      obtain ⟨j, hj, h1', h2'⟩ := hp.forces_oriented hf T₀
      have hidx : ∀ s : ℕ, B + (((T + s) % k : ℕ) : ZMod k) = T₀ + (s : ZMod k) := fun s => by
        rw [ZMod.natCast_mod, Nat.cast_add, ← add_assoc, hBT']
      exact ⟨j, hj, fun s a b => by simp only [hg, hidx, hBT']; exact h1' s a b,
        fun s a b => by simp only [hg, hidx, hBT']; exact h2' s a b⟩)
  -- all forces are parallel to `f B`
  have hpar : ∀ i, cross2 (f B) (f i) = 0 := fun i => by
    have := hcore (i - B).val (ZMod.val_lt _)
    rwa [hg0, show g (i - B).val = f i by simp only [hg, ZMod.natCast_zmod_val]; ring_nf] at this
  have he2 : 0 < ‖f B‖ ^ 2 := by have := norm_pos_iff.mpr hfB; positivity
  refine hp.hdn_of_parallel z hf hfB (fun i => ⟪f B, f i⟫ / ‖f B‖ ^ 2) (fun i => ?_) (B := B)
    ?_ h1 h2 h3
  · have := norm_sq_smul_of_cross2 (v := f i) (e := f B) (by rw [cross2_comm, hpar i, neg_zero])
    apply smul_right_injective ℝ² he2.ne'
    simp only
    rw [this, smul_smul, mul_div_cancel₀ _ he2.ne']
  · simp only [real_inner_self_eq_norm_sq, div_self he2.ne']; exact one_pos

/-- **Theorem 7.3 at an explicit standard view.**  The silhouette is the cycle
`x`, every other point of `V` projects into the interior of the shadow, the
corner depths are cyclically unimodal and distinct, and there is no horizontal
double normal.  Then some first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_unimodal (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => projXy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      projXy v ∈ interior (convexHull ℝ (Set.range fun i => projXy (x i))))
    (hz : IsCyclicUnimodal (fun i => x i 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => projXy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  classical
  by_contra hno
  push Not at hno
  set p : ZMod k → ℝ² := fun i => projXy (x i) with hpdef
  set Q := convexHull ℝ (Set.range p) with hQdef
  have hSQ : projXy '' convexHull ℝ (V : Set ℝ³) = Q := by
    rw [show (projXy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply le_antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hc : ∃ i, v = x i
      · obtain ⟨i, rfl⟩ := hc; exact subset_convexHull ℝ _ ⟨i, rfl⟩
      · push Not at hc; exact interior_subset (hin v hv hc)
    · apply convexHull_mono
      rintro _ ⟨i, rfl⟩; exact ⟨x i, hxV i, rfl⟩
  obtain ⟨f, hfN, ⟨v₀, hv₀, hf₀⟩, hE1, hE2, hE3⟩ :=
    exists_forces_of_not_firstOrderInward V (by rw [hSQ]; exact hp.interior_nonempty) hno
  rw [hSQ] at hfN
  have hzero : ∀ v ∈ V, (∀ i, v ≠ x i) → f v = 0 := fun v hv hc =>
    normalConeAt_eq_zero_of_mem_interior (hin v hv hc) (hfN v hv)
  have hxinj : Function.Injective x := fun i j h => hp.injective (by rw [hpdef]; dsimp only; rw [h])
  have himg : univ.image x ⊆ V := fun v hv => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv; exact hxV i
  have hred : ∀ {M : Type} [AddCommMonoid M] (G : ℝ³ → M), (∀ v, f v = 0 → G v = 0) →
      ∑ v ∈ V, G v = ∑ i, G (x i) := by
    intro M _ G hG
    rw [← sum_subset himg (fun v hv hni => hG v (hzero v hv fun i h => hni (by
      rw [h]; exact mem_image_of_mem x (mem_univ i)))), sum_image (fun i _ j _ h => hxinj h)]
  refine hnd (hasHorizontalDoubleNormal_of_forces p (fun i => x i 2) hp hz (fun i => f (x i))
    (fun i => hfN (x i) (hxV i)) ?_ ?_ ?_ ?_)
  · by_contra hall; push Not at hall
    by_cases hc : ∃ i, v₀ = x i
    · obtain ⟨i, rfl⟩ := hc; exact hf₀ (hall i)
    · push Not at hc; exact hf₀ (hzero v₀ hv₀ hc)
  · rw [← hred f (fun v h => h)]; exact hE1
  · rw [← hred (fun v => v 2 • f v) (fun v h => by simp [h])]; exact hE2
  · rw [← hred (fun v => cross2 (projXy v) (f v)) (fun v h => by simp [h, cross2])]; exact hE3

/-- **Theorem 7.3, Rupert form, at the view of a rotation `R`.** -/
theorem isRupert_of_unimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → projXy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => projXy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  classical
  obtain ⟨ω, τ, h⟩ := exists_firstOrderInward_of_unimodal (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hz hnd
  exact isRupert_of_firstOrderInward_image V R hR ω τ h

/-- **Lemma 7.4 (exceptional views).**  Horizontal double normals occur only
for views `u = Rᵀ e_z` on finitely many great circles `l ⟂ u`, determined by `V`
alone (`badDirs V`, `BadViews.lean`).  Stated without (G1)/(G2): any closed
cycle of points of `V` with a horizontal double normal is covered. -/
theorem exists_badPlanes (V : Finset ℝ³) :
    ∃ Λ : Finset ℝ³, (∀ l ∈ Λ, l ≠ 0) ∧
      ∀ R ∈ SO3, ∀ (k : ℕ) (x : ZMod k → ℝ³), (∀ i, x i ∈ V) →
        HasHorizontalDoubleNormal (fun i => projXy (R.toEuclideanLin (x i)))
          (fun i => (R.toEuclideanLin (x i)) 2) →
        ∃ l ∈ Λ, (R.toEuclideanLin l) 2 = 0 :=
  ⟨badDirs V, fun _ hl => ne_zero_of_mem_badDirs hl,
    fun R hR _ x hxV h => exists_badDir_of_hdn V R hR x hxV h⟩

/-- **Theorem 7.5, robust form.**  If every view near `R₀` (rotation or not)
that avoids the great circles of a finite set `Λ₀` has the silhouette `x` with
the other points inside and a unimodal silhouette, then `V` is Rupert.  (Used
for Theorem 7.7 and Corollary 7.8, where `Λ₀` breaks depth ties.) -/
theorem isRupert_of_eventually_unimodal (V : Finset ℝ³) {R₀ : Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : R₀ ∈ SO3) (Λ₀ : Finset ℝ³) (hΛ₀ : ∀ l ∈ Λ₀, l ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (h : ∀ᶠ R in 𝓝 R₀, (∀ l ∈ Λ₀, (R.toEuclideanLin l) 2 ≠ 0) →
      IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))) ∧
      (∀ v ∈ V, (∀ i, v ≠ x i) → projXy (R.toEuclideanLin v) ∈
        interior (convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i))))) ∧
      IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  classical
  obtain ⟨R, hRU, hR, hRΛ⟩ := exists_rotation_near_avoiding hR₀ (Λ₀ ∪ badDirs V)
    (fun l hl => by
      rcases mem_union.mp hl with hl | hl
      · exact hΛ₀ l hl
      · exact ne_zero_of_mem_badDirs hl) h
  obtain ⟨hp, hin, hz⟩ := hRU fun l hl => hRΛ l (mem_union_left _ hl)
  refine isRupert_of_unimodalView V R hR x hxV hp hin hz fun hdn => ?_
  obtain ⟨l, hl, hl0⟩ := exists_badDir_of_hdn V R hR x hxV hdn
  exact hRΛ l (mem_union_right _ hl) hl0

theorem continuous_proj_xy : Continuous (projXy : ℝ³ → ℝ²) :=
  projL.continuous_of_finiteDimensional

theorem continuous_proj_toEuclideanLin (v : ℝ³) :
    Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ => projXy (R.toEuclideanLin v) :=
  continuous_proj_xy.comp (continuous_toEuclideanLin_apply v)

theorem continuous_depth_toEuclideanLin (v : ℝ³) :
    Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ => (R.toEuclideanLin v) 2 :=
  (PiLp.continuous_apply 2 _ 2).comp (continuous_toEuclideanLin_apply v)

/-- **Theorem 7.5 (unimodal view criterion).**  A generic view (strictly
convex silhouette `x`, all other points inside, distinct corner depths) with a
unimodal silhouette makes `V` Rupert. -/
theorem isRupert_of_genericUnimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → projXy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  classical
  let P : Matrix (Fin 3) (Fin 3) ℝ → ZMod k → ℝ² := fun R' i => projXy (R'.toEuclideanLin (x i))
  let Z : Matrix (Fin 3) (Fin 3) ℝ → ZMod k → ℝ := fun R' i => (R'.toEuclideanLin (x i)) 2
  have hc : ∀ i, ContinuousAt (fun R' => P R' i) R := fun i =>
    (continuous_proj_toEuclideanLin (x i)).continuousAt
  have hcz : ∀ i, ContinuousAt (fun R' => Z R' i) R := fun i =>
    (continuous_depth_toEuclideanLin (x i)).continuousAt
  have hp' : IsCcwPolygon (P R) := hp
  have hz' : IsCyclicUnimodal (Z R) := hz
  refine isRupert_of_eventually_unimodal V hR ∅ (by simp) x hxV ?_
  have hin' : ∀ᶠ R' in 𝓝 R, ∀ v ∈ V, (∀ i, v ≠ x i) → projXy (R'.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range (P R'))) := by
    refine (eventually_all_finset V).2 fun v hv => ?_
    by_cases hvx : ∀ i, v ≠ x i
    · have hq : ContinuousAt (fun R' : Matrix (Fin 3) (Fin 3) ℝ =>
          projXy (R'.toEuclideanLin v)) R := (continuous_proj_toEuclideanLin v).continuousAt
      have h0 : projXy (R.toEuclideanLin v) ∈ interior (convexHull ℝ (Set.range (P R))) :=
        hin v hv hvx
      exact (eventually_mem_interior hc hq hp' h0).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hvx
  filter_upwards [eventually_isCcwPolygon hc hp', hin', eventually_isCyclicUnimodal hcz hz']
    with R' h1 h2 h3
  exact fun _ => ⟨h1, h2, h3⟩

/-- **Theorem 7.5, open-condition form.**  At the view of `R₀` the cycle `x`
(distinct points of `V`) is a strictly convex counterclockwise silhouette, every
other point of `V` is strictly left of every edge, and the corner depths satisfy
an open condition `Q` which forces cyclic unimodality once the depths are
distinct.  Then `V` is Rupert.  (Ties in depth at `R₀` are allowed.) -/
theorem isRupert_of_open_unimodal (V : Finset ℝ³) {R₀ : Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : R₀ ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hxinj : Function.Injective x)
    (hp : IsCcwPolygon (fun i => projXy (R₀.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → ∀ i,
      0 < cross2 (projXy (R₀.toEuclideanLin (x (i + 1))) - projXy (R₀.toEuclideanLin (x i)))
        (projXy (R₀.toEuclideanLin v) - projXy (R₀.toEuclideanLin (x i))))
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQ : Q fun i => (R₀.toEuclideanLin (x i)) 2)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  classical
  let P : Matrix (Fin 3) (Fin 3) ℝ → ZMod k → ℝ² := fun R' i => projXy (R'.toEuclideanLin (x i))
  let Z : Matrix (Fin 3) (Fin 3) ℝ → ZMod k → ℝ := fun R' i => (R'.toEuclideanLin (x i)) 2
  have hc : ∀ i, ContinuousAt (fun R' => P R' i) R₀ := fun i =>
    (continuous_proj_toEuclideanLin (x i)).continuousAt
  have hZ : Continuous Z := continuous_pi fun i => continuous_depth_toEuclideanLin (x i)
  have hp' : IsCcwPolygon (P R₀) := hp
  set Λ₀ : Finset ℝ³ := ((univ ×ˢ univ).filter (fun q : ZMod k × ZMod k => q.1 ≠ q.2)).image
    (fun q => x q.1 - x q.2) with hΛ₀
  have hΛ : ∀ l ∈ Λ₀, l ≠ 0 := by
    intro l hl
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hl
    exact sub_ne_zero.mpr (hxinj.ne (mem_filter.mp hq).2)
  refine isRupert_of_eventually_unimodal V hR₀ Λ₀ hΛ x hxV ?_
  have hin' : ∀ᶠ R' in 𝓝 R₀, ∀ v ∈ V, (∀ i, v ≠ x i) →
      ∀ i, 0 < cross2 (P R' (i + 1) - P R' i) (projXy (R'.toEuclideanLin v) - P R' i) := by
    refine (eventually_all_finset V).2 fun v hv => ?_
    by_cases hvx : ∀ i, v ≠ x i
    · have hq : ContinuousAt (fun R' : Matrix (Fin 3) (Fin 3) ℝ =>
          projXy (R'.toEuclideanLin v)) R₀ := (continuous_proj_toEuclideanLin v).continuousAt
      exact (eventually_left hc hq (hin v hv hvx)).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hvx
  have hQ' : ∀ᶠ R' in 𝓝 R₀, Q (Z R') :=
    hZ.continuousAt.preimage_mem_nhds (hQo.mem_nhds hQ)
  filter_upwards [eventually_isCcwPolygon hc hp', hin', hQ'] with R' h1 h2 h3 hΛR
  have hinj : Function.Injective (Z R') := by
    intro i j hij
    by_contra hne
    apply hΛR (x i - x j) (mem_image.mpr ⟨(i, j), by simp [hne], rfl⟩)
    rw [map_sub, PiLp.sub_apply]
    exact sub_eq_zero.mpr hij
  exact ⟨h1, fun v hv hvx => h1.mem_interior_of_left (h2 v hv hvx), hQu _ hinj h3⟩

end Minimality

end RupertMinimality
