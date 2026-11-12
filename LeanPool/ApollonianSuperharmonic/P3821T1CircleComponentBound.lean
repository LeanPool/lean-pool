/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3821T1ControlledNeighborhood
public import LeanPool.ApollonianSuperharmonic.P3821T1ComponentContours
public import LeanPool.ApollonianSuperharmonic.P3821T1LoopIndexLaws
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

-- [TABLET NODE: P3821T1CircleComponentBound]

/-!
# P3821T1CircleComponentBound

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CircleComponentProof

private theorem hRadialImage :
    ∀ (r : ℝ),
    let R : ℝ := max r 0 + 1
    (0 < R) → (
    let U : Set ℂ := {w | R < ‖w‖}
    let radial : ℂ × ℝ → ℂ := fun v => v.2 • v.1
    radial '' (Metric.sphere (0 : ℂ) 1 ×ˢ Set.Ioi R) = U) := by
  classical
  intro r R hRpos U radial
  ext w
  constructor
  · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
    have hu' : ‖u‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hu
    have htpos : 0 < t := lt_trans hRpos ht
    change R < ‖t • u‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hu']
    simpa using ht
  · intro hw
    have hwpos : 0 < ‖w‖ := lt_trans hRpos hw
    refine ⟨(w / ‖w‖, ‖w‖), ?_, ?_⟩
    · constructor
      · change dist (w / ‖w‖) 0 = 1
        simp only [dist_zero_right, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_norm]
        exact div_self hwpos.ne'
      · exact hw
    · change ‖w‖ • (w / ‖w‖) = w
      change (‖w‖ : ℂ) * (w / (‖w‖ : ℂ)) = w
      field_simp [Complex.ofReal_ne_zero.mpr hwpos.ne']

private theorem boundedComponent :
    ∀ (e : C(Circle, Real × Real)),
    let h₀ : ℂ ≃ₜ (Real × Real) :=
      Complex.equivRealProd.toHomeomorphOfIsInducing
        Complex.isUniformEmbedding_equivRealProd.isInducing
    let h : (Real × Real) ≃ₜ ℂ := h₀.symm
    let ec : C(Circle, ℂ) := ⟨fun t => h (e t), h.continuous.comp e.continuous⟩
    let K : Set ℂ := Set.range ec
    let T : Set ℂ := Kᶜ
    ∀ (r : ℝ),
    let R : ℝ := max r 0 + 1
    let U : Set ℂ := {w | R < ‖w‖}
    let aInf : ℂ := (R + 1 : ℝ)
    let CInf : Set ℂ := connectedComponentIn T aInf
    (U ⊆ CInf) → (∀ w ∈ T, connectedComponentIn T w ≠ CInf → Bornology.IsBounded
        (connectedComponentIn T w)) := by
  classical
  intro e h₀ h ec K T r R U aInf CInf hUcomponent w hw hneq
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  refine ⟨R, ?_⟩
  intro v hv
  have hvT : v ∈ T := connectedComponentIn_subset T w hv
  by_contra hvball
  have hvU : v ∈ U := by
    change R < ‖v‖
    have hnotnorm : ¬ ‖v‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hvball
    exact lt_of_not_ge hnotnorm
  have hvInf : v ∈ CInf := hUcomponent hvU
  have hweqv : connectedComponentIn T w = connectedComponentIn T v :=
    connectedComponentIn_eq hv
  have hIneqv : CInf = connectedComponentIn T v := connectedComponentIn_eq hvInf
  exact hneq (hweqv.trans hIneqv.symm)

private theorem hcomp_pull :
    ∀ (e : C(Circle, Real × Real)),
    let h₀ : ℂ ≃ₜ (Real × Real) :=
      Complex.equivRealProd.toHomeomorphOfIsInducing
        Complex.isUniformEmbedding_equivRealProd.isInducing
    let h : (Real × Real) ≃ₜ ℂ := h₀.symm
    let ec : C(Circle, ℂ) := ⟨fun t => h (e t), h.continuous.comp e.continuous⟩
    let K : Set ℂ := Set.range ec
    let T : Set ℂ := Kᶜ
    let S : Set (Real × Real) := (Set.range e)ᶜ
    (h '' S = T) → ((h.symm '' T = S) → (∀ (u : ℝ × ℝ), ∀ (v : ℝ × ℝ), u ∈ S → v ∈ S →
        connectedComponentIn T ((h : ℝ × ℝ → ℂ) u) = connectedComponentIn T ((h : ℝ × ℝ → ℂ) v) →
        connectedComponentIn S u = connectedComponentIn S v)) := by
  classical
  intro e h₀ h ec K T S hImageS hSymmImageT u v hu hv hcmp
  have huT : h u ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hu
  have hvT : h v ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hv
  have hmem : h v ∈ connectedComponentIn T (h u) := by
    rw [hcmp]
    exact mem_connectedComponentIn hvT
  have himage := h.symm.continuous.continuousOn.image_connectedComponentIn_subset
    (s := T) (a := h u) huT
  have hmem' : v ∈ connectedComponentIn S u := by
    have : h.symm (h v) ∈ h.symm '' connectedComponentIn T (h u) := ⟨h v, hmem, rfl⟩
    have him := himage this
    simpa [hSymmImageT, h.symm_apply_apply] using him
  exact connectedComponentIn_eq hmem'

private theorem hcomp_push :
    ∀ (e : C(Circle, Real × Real)),
    let h₀ : ℂ ≃ₜ (Real × Real) :=
      Complex.equivRealProd.toHomeomorphOfIsInducing
        Complex.isUniformEmbedding_equivRealProd.isInducing
    let h : (Real × Real) ≃ₜ ℂ := h₀.symm
    let ec : C(Circle, ℂ) := ⟨fun t => h (e t), h.continuous.comp e.continuous⟩
    let K : Set ℂ := Set.range ec
    let T : Set ℂ := Kᶜ
    let S : Set (Real × Real) := (Set.range e)ᶜ
    (h '' S = T) → (∀ (u : ℝ × ℝ), ∀ (v : ℝ × ℝ), u ∈ S → v ∈ S → connectedComponentIn S u =
        connectedComponentIn S v → connectedComponentIn T ((h : ℝ × ℝ → ℂ) u) =
        connectedComponentIn T ((h : ℝ × ℝ → ℂ) v)) := by
  classical
  intro e h₀ h ec K T S hImageS u v hu hv hcmp
  have huT : h u ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hu
  have hvT : h v ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hv
  have hmem : v ∈ connectedComponentIn S u := by rw [hcmp]; exact mem_connectedComponentIn hv
  have himage := h.continuous.continuousOn.image_connectedComponentIn_subset
    (s := S) (a := u) hu
  have hmem' : h v ∈ connectedComponentIn T (h u) := by
    have : h v ∈ h '' connectedComponentIn S u := ⟨v, hmem, rfl⟩
    have him := himage this
    simpa [hImageS] using him
  exact connectedComponentIn_eq hmem'

private theorem impossible_pair :
    ∀ (e : C(Circle, Real × Real)), (Function.Injective (⇑e : Circle → ℝ × ℝ)) → (
    let h₀ : ℂ ≃ₜ (Real × Real) :=
      Complex.equivRealProd.toHomeomorphOfIsInducing
        Complex.isUniformEmbedding_equivRealProd.isInducing
    let h : (Real × Real) ≃ₜ ℂ := h₀.symm
    let ec : C(Circle, ℂ) := ⟨fun t => h (e t), h.continuous.comp e.continuous⟩
    let K : Set ℂ := Set.range ec
    let T : Set ℂ := Kᶜ
    (IsCompact K) → ((K.Nonempty) → (∀ (p : ℂ), ∀ (q : ℂ), p ∈ T → q ∈ T → connectedComponentIn T
        p ≠ connectedComponentIn T q → Bornology.IsBounded (connectedComponentIn T p) →
        Bornology.IsBounded (connectedComponentIn T q) → False))) := by
  classical
  intro e he h₀ h ec K T hKcompact hKne p q hp hq hne hpBound hqBound
  have hpDist : 0 < Metric.infDist p K :=
    (hKcompact.isClosed.notMem_iff_infDist_pos hKne).1 hp
  have hqDist : 0 < Metric.infDist q K :=
    (hKcompact.isClosed.notMem_iff_infDist_pos hKne).1 hq
  let eps : ℝ := min (Metric.infDist p K) (Metric.infDist q K) / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hpMargin : eps < Metric.infDist p K := by
    dsimp [eps]
    have hm : min (Metric.infDist p K) (Metric.infDist q K) ≤ Metric.infDist p K := min_le_left _ _
    linarith
  have hqMargin : eps < Metric.infDist q K := by
    dsimp [eps]
    have hm : min (Metric.infDist p K) (Metric.infDist q K) ≤ Metric.infDist q K := min_le_right _ _
    linarith
  have hec : Function.Injective ec := by
    intro s t hst
    apply he
    exact congrArg h.symm hst
  obtain ⟨N, hNopen, hKN, phi, hphi⟩ :=
    P3821T1ControlledNeighborhood ec hec eps heps
  obtain ⟨n, g, hgN, hgAvoid, hgp, hgq⟩ :=
    P3821T1ComponentContours K N hKcompact hNopen hKN p q hp hq hne hpBound
  obtain ⟨m, k, hkN, hkAvoid, hkq, hkp⟩ :=
    P3821T1ComponentContours K N hKcompact hNopen hKN q p hq hp hne.symm hqBound
  let j : C(Circle, ℂ) := ⟨fun t => (t : ℂ), continuous_subtype_val⟩
  rcases P3821T1LoopIndexLaws with ⟨_, hcomp, hhom⟩
  let alphaOf (f : C(Circle, ℂ)) (hfN : Set.range f ⊆ N) : C(Circle, Circle) :=
    phi.comp ⟨fun t => ⟨f t, hfN ⟨t, rfl⟩⟩,
      Continuous.subtype_mk f.continuous (fun t => hfN ⟨t, rfl⟩)⟩
  have index_relation (f : C(Circle, ℂ)) (hfN : Set.range f ⊆ N)
      (r : ℂ) (hr : r ∈ T) (hmargin : eps < Metric.infDist r K)
      (hfavoid : ∀ t, f t ≠ r) :
      P3821T1LoopIndex f r =
        P3821T1LoopIndex (j.comp (alphaOf f hfN)) 0 *
          P3821T1LoopIndex ec r := by
    let alpha := alphaOf f hfN
    let H : C(unitInterval × Circle, ℂ) :=
      ⟨fun st => ((1 - (st.1 : ℝ) : ℝ) : ℂ) * f st.2 +
        ((st.1 : ℝ) : ℂ) * ec (alpha st.2), by fun_prop⟩
    have hAvoid (s : unitInterval) (t : Circle) : H (s, t) ≠ r := by
      intro heq
      have happrox := hphi ⟨f t, hfN ⟨t, rfl⟩⟩
      have hmem : ec (alpha t) ∈ K := ⟨alpha t, rfl⟩
      have hinf : Metric.infDist r K ≤ dist r (ec (alpha t)) :=
        Metric.infDist_le_dist_of_mem hmem
      have hclose : dist (H (s, t)) (ec (alpha t)) < eps := by
        have hlinear : H (s, t) - ec (alpha t) =
            ((1 - (s : ℝ) : ℝ) : ℂ) * (f t - ec (alpha t)) := by
          dsimp [H]
          push_cast
          ring
        have hnorm : ‖H (s, t) - ec (alpha t)‖ < eps := by
          rw [hlinear, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
          have hs : 0 ≤ 1 - (s : ℝ) := by linarith [s.2.2]
          rw [abs_of_nonneg hs]
          have herr : ‖f t - ec (alpha t)‖ < eps := by
            simpa [alpha, alphaOf, dist_eq_norm, norm_sub_rev] using happrox
          have hcoeff : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
          calc
            (1 - (s : ℝ)) * ‖f t - ec (alpha t)‖ ≤
                1 * ‖f t - ec (alpha t)‖ := by gcongr
            _ < eps := by simpa using herr
        simpa [dist_eq_norm] using hnorm
      have hdist : dist r (ec (alpha t)) < eps := by
        rw [← heq]
        exact hclose
      linarith
    let H0 : C(Circle, ℂ) := ⟨fun t => H (⟨0, by norm_num⟩, t), by fun_prop⟩
    let H1 : C(Circle, ℂ) := ⟨fun t => H (⟨1, by norm_num⟩, t), by fun_prop⟩
    have hH0 : H0 = f := by ext t; simp [H0, H]
    have hH1 : H1 = ec.comp alpha := by ext t; simp [H1, H]
    have hhom' := hhom H r hAvoid
    have hcomp' := hcomp ec alpha r (fun t => by
      intro heq
      exact (show r ∉ K from hr) ⟨t, heq⟩)
    have hhom'' : P3821T1LoopIndex H0 r = P3821T1LoopIndex H1 r := by
      change P3821T1LoopIndex
          ⟨fun t => H (⟨0, by norm_num⟩, t), by fun_prop⟩ r =
        P3821T1LoopIndex ⟨fun t => H (⟨1, by norm_num⟩, t), by fun_prop⟩ r
      exact hhom'
    calc
      P3821T1LoopIndex f r = P3821T1LoopIndex H0 r := by rw [hH0]
      _ = P3821T1LoopIndex H1 r := hhom''
      _ = P3821T1LoopIndex (ec.comp alpha) r := by rw [hH1]
      _ = P3821T1LoopIndex (j.comp alpha) 0 * P3821T1LoopIndex ec r := hcomp'
      _ = P3821T1LoopIndex (j.comp (alphaOf f hfN)) 0 *
          P3821T1LoopIndex ec r := by rfl
  have hgRelP (i : Fin n) : P3821T1LoopIndex (g i) p =
      P3821T1LoopIndex (j.comp (alphaOf (g i) (hgN i))) 0 *
        P3821T1LoopIndex ec p :=
    index_relation (g i) (hgN i) p hp hpMargin (fun t => (hgAvoid i t).1)
  have hgRelQ (i : Fin n) : P3821T1LoopIndex (g i) q =
      P3821T1LoopIndex (j.comp (alphaOf (g i) (hgN i))) 0 *
        P3821T1LoopIndex ec q :=
    index_relation (g i) (hgN i) q hq hqMargin (fun t => (hgAvoid i t).2)
  let dg : Fin n → ℝ := fun i =>
    P3821T1LoopIndex (j.comp (alphaOf (g i) (hgN i))) 0
  let A : ℝ := ∑ i, dg i
  have hrowgp : (∑ i, P3821T1LoopIndex (g i) p) = A *
      P3821T1LoopIndex ec p := by
    calc
      _ = ∑ i, dg i * P3821T1LoopIndex ec p :=
        Finset.sum_congr rfl (fun i _ => hgRelP i)
      _ = A * P3821T1LoopIndex ec p := by
        dsimp [A]
        rw [Finset.sum_mul]
  have hrowgq : (∑ i, P3821T1LoopIndex (g i) q) = A *
      P3821T1LoopIndex ec q := by
    calc
      _ = ∑ i, dg i * P3821T1LoopIndex ec q :=
        Finset.sum_congr rfl (fun i _ => hgRelQ i)
      _ = A * P3821T1LoopIndex ec q := by
        dsimp [A]
        rw [Finset.sum_mul]
  have hAprod : A * P3821T1LoopIndex ec p = 1 := by
    rw [← hrowgp]
    exact hgp
  have hAzero : A * P3821T1LoopIndex ec q = 0 := by
    rw [← hrowgq]
    exact hgq
  have hAne : A ≠ 0 := by
    intro hz
    rw [hz] at hAprod
    norm_num at hAprod
  have hBrelQ (i : Fin m) : P3821T1LoopIndex (k i) q =
      P3821T1LoopIndex (j.comp (alphaOf (k i) (hkN i))) 0 *
        P3821T1LoopIndex ec q :=
    index_relation (k i) (hkN i) q hq hqMargin (fun t => (hkAvoid i t).1)
  have hBrelP (i : Fin m) : P3821T1LoopIndex (k i) p =
      P3821T1LoopIndex (j.comp (alphaOf (k i) (hkN i))) 0 *
        P3821T1LoopIndex ec p :=
    index_relation (k i) (hkN i) p hp hpMargin (fun t => (hkAvoid i t).2)
  let dk : Fin m → ℝ := fun i =>
    P3821T1LoopIndex (j.comp (alphaOf (k i) (hkN i))) 0
  let B : ℝ := ∑ i, dk i
  have hrowkq : (∑ i, P3821T1LoopIndex (k i) q) = B *
      P3821T1LoopIndex ec q := by
    calc
      _ = ∑ i, dk i * P3821T1LoopIndex ec q :=
        Finset.sum_congr rfl (fun i _ => hBrelQ i)
      _ = B * P3821T1LoopIndex ec q := by
        dsimp [B]
        rw [Finset.sum_mul]
  have hrowkp : (∑ i, P3821T1LoopIndex (k i) p) = B *
      P3821T1LoopIndex ec p := by
    calc
      _ = ∑ i, dk i * P3821T1LoopIndex ec p :=
        Finset.sum_congr rfl (fun i _ => hBrelP i)
      _ = B * P3821T1LoopIndex ec p := by
        dsimp [B]
        rw [Finset.sum_mul]
  have hBq : B * P3821T1LoopIndex ec q = 1 := by
    rw [← hrowkq]
    exact hkq
  have hBp : B * P3821T1LoopIndex ec p = 0 := by
    rw [← hrowkp]
    exact hkp
  have hbzero : P3821T1LoopIndex ec q = 0 :=
    (mul_eq_zero.mp hAzero).resolve_left hAne
  rw [hbzero] at hBq
  norm_num at hBq

end CircleComponentProof

theorem P3821T1CircleComponentBound (e : C(Circle, Real × Real))
    (he : Function.Injective e) (x y z : Real × Real)
    (hx : x ∈ (Set.range e)ᶜ) (hy : y ∈ (Set.range e)ᶜ)
    (hz : z ∈ (Set.range e)ᶜ) :
    connectedComponentIn (Set.range e)ᶜ x = connectedComponentIn (Set.range e)ᶜ y ∨
    connectedComponentIn (Set.range e)ᶜ y = connectedComponentIn (Set.range e)ᶜ z ∨
    connectedComponentIn (Set.range e)ᶜ x = connectedComponentIn (Set.range e)ᶜ z := by
-- BODY
  classical
  let h₀ : ℂ ≃ₜ (Real × Real) :=
    Complex.equivRealProd.toHomeomorphOfIsInducing
      Complex.isUniformEmbedding_equivRealProd.isInducing
  let h : (Real × Real) ≃ₜ ℂ := h₀.symm
  let ec : C(Circle, ℂ) := ⟨fun t => h (e t), h.continuous.comp e.continuous⟩
  let K : Set ℂ := Set.range ec
  let T : Set ℂ := Kᶜ
  have hKcompact : IsCompact K := isCompact_range ec.continuous
  have hKbounded : Bornology.IsBounded K := hKcompact.isBounded
  obtain ⟨r, hrK⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hKbounded
  let R : ℝ := max r 0 + 1
  have hRpos : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  have hKball : K ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    have hw' := hrK hw
    change dist w 0 ≤ r at hw'
    change dist w 0 ≤ R
    dsimp [R]
    have : r ≤ max r 0 := le_max_left r 0
    linarith
  let U : Set ℂ := {w | R < ‖w‖}
  have hSphere : IsPathConnected (Metric.sphere (0 : ℂ) 1) := by
    apply isPathConnected_sphere (E := ℂ)
    · rw [Complex.rank_real_complex]
      norm_num
    · norm_num
  have hHalf : IsPathConnected (Set.Ioi R : Set ℝ) := by
    apply Convex.isPathConnected (convex_Ioi R)
    exact ⟨R + 1, by simp⟩
  let radial : ℂ × ℝ → ℂ := fun v => v.2 • v.1
  have hradial_cont : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hDomain : IsPathConnected
      (Metric.sphere (0 : ℂ) 1 ×ˢ Set.Ioi R) := hSphere.prod hHalf
  have hRadialImage : radial ''
      (Metric.sphere (0 : ℂ) 1 ×ˢ Set.Ioi R) = U := CircleComponentProof.hRadialImage r hRpos
  have hU : IsPathConnected U := by
    rw [← hRadialImage]
    exact hDomain.image hradial_cont
  have hKnotU : K ⊆ Uᶜ := by
    intro w hw
    have hball := hKball hw
    change dist w 0 ≤ R at hball
    change ¬ R < ‖w‖
    simpa [dist_zero_right] using hball
  let aInf : ℂ := (R + 1 : ℝ)
  have haInfU : aInf ∈ U := by
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    calc
      R < R + 1 := by linarith
      _ = |R + 1| := (abs_of_pos (by linarith : 0 < R + 1)).symm
      _ = ‖((R + 1 : ℝ) : ℂ)‖ := (RCLike.norm_ofReal _).symm
  let CInf : Set ℂ := connectedComponentIn T aInf
  have hUsubT : U ⊆ T := by
    intro w hw
    change w ∉ K
    intro hwK
    exact hKnotU hwK hw
  have hUcomponent : U ⊆ CInf := by
    exact hU.isConnected.isPreconnected.subset_connectedComponentIn haInfU hUsubT
  have boundedComponent (w : ℂ) (hw : w ∈ T)
      (hneq : connectedComponentIn T w ≠ CInf) :
      Bornology.IsBounded (connectedComponentIn T w) := CircleComponentProof.boundedComponent e r
          hUcomponent w hw hneq
  have hKimage : K = h '' Set.range e := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨e t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  let S : Set (Real × Real) := (Set.range e)ᶜ
  have hImageS : h '' S = T := by
    change h '' S = Kᶜ
    rw [hKimage]
    change h '' (Set.range e)ᶜ = (h '' Set.range e)ᶜ
    exact h.image_compl (Set.range e)
  have hSymmImageT : h.symm '' T = S := by
    change h.symm '' Kᶜ = S
    rw [hKimage]
    change h.symm '' (h '' Set.range e)ᶜ = (Set.range e)ᶜ
    rw [← h.image_compl (Set.range e), Set.image_image]
    simp
  have hcomp_pull (u v : Real × Real) (hu : u ∈ S) (hv : v ∈ S)
      (hcmp : connectedComponentIn T (h u) = connectedComponentIn T (h v)) :
      connectedComponentIn S u = connectedComponentIn S v := CircleComponentProof.hcomp_pull e
          hImageS hSymmImageT u v hu hv hcmp
  have hcomp_push (u v : Real × Real) (hu : u ∈ S) (hv : v ∈ S)
      (hcmp : connectedComponentIn S u = connectedComponentIn S v) :
      connectedComponentIn T (h u) = connectedComponentIn T (h v) :=
          CircleComponentProof.hcomp_push e hImageS u v hu hv hcmp
  have hxS : x ∈ S := hx
  have hyS : y ∈ S := hy
  have hzS : z ∈ S := hz
  have hxT : h x ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hxS
  have hyT : h y ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hyS
  have hzT : h z ∈ T := by rw [← hImageS]; exact Set.mem_image_of_mem h hzS
  have final_of (u v : Real × Real) (hu : u ∈ S) (hv : v ∈ S)
      (hcmp : connectedComponentIn T (h u) = connectedComponentIn T (h v)) :
      connectedComponentIn S u = connectedComponentIn S v := hcomp_pull u v hu hv hcmp
  have hKne : K.Nonempty := ⟨ec 1, ⟨1, rfl⟩⟩
  have impossible_pair (p q : ℂ) (hp : p ∈ T) (hq : q ∈ T)
      (hne : connectedComponentIn T p ≠ connectedComponentIn T q)
      (hpBound : Bornology.IsBounded (connectedComponentIn T p))
      (hqBound : Bornology.IsBounded (connectedComponentIn T q)) : False :=
          CircleComponentProof.impossible_pair e he hKcompact hKne p q hp hq hne hpBound hqBound
  by_cases hxy : connectedComponentIn S x = connectedComponentIn S y
  · exact Or.inl hxy
  · by_cases hyz : connectedComponentIn S y = connectedComponentIn S z
    · exact Or.inr (Or.inl hyz)
    · by_cases hxz : connectedComponentIn S x = connectedComponentIn S z
      · exact Or.inr (Or.inr hxz)
      · have hxyNe : connectedComponentIn T (h x) ≠ connectedComponentIn T (h y) := by
          intro heq
          exact hxy (hcomp_pull x y hxS hyS heq)
        have hyzNe : connectedComponentIn T (h y) ≠ connectedComponentIn T (h z) := by
          intro heq
          exact hyz (hcomp_pull y z hyS hzS heq)
        have hxzNe : connectedComponentIn T (h x) ≠ connectedComponentIn T (h z) := by
          intro heq
          exact hxz (hcomp_pull x z hxS hzS heq)
        by_cases hxInf : connectedComponentIn T (h x) = CInf
        · have hyInf : connectedComponentIn T (h y) ≠ CInf := by
            intro heq
            exact hxyNe (hxInf.trans heq.symm)
          have hzInf : connectedComponentIn T (h z) ≠ CInf := by
            intro heq
            exact hxzNe (hxInf.trans heq.symm)
          exact (impossible_pair (h y) (h z) hyT hzT hyzNe
            (boundedComponent (h y) hyT hyInf) (boundedComponent (h z) hzT hzInf)).elim
        · by_cases hyInf : connectedComponentIn T (h y) = CInf
          · have hzInf : connectedComponentIn T (h z) ≠ CInf := by
              intro heq
              exact hyzNe (hyInf.trans heq.symm)
            exact (impossible_pair (h x) (h z) hxT hzT hxzNe
              (boundedComponent (h x) hxT hxInf) (boundedComponent (h z) hzT hzInf)).elim
          · exact (impossible_pair (h x) (h y) hxT hyT hxyNe
              (boundedComponent (h x) hxT hxInf) (boundedComponent (h y) hyT hyInf)).elim

end ApollonianSuperharmonic

end
