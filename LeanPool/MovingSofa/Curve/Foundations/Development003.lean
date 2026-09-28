/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Curve.Foundations.Development002

public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.TauCeti.Topology.JordanCurve.Path
/-!
# Moving sofa: related mathematical developments

* `Curve.PositiveGraphOrientation`.
* `Curve.PositiveGraphRegion`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The counterclockwise loop around a positive graph

For `a < b` and a continuous `f : ℝ → ℝ` vanishing at `a` and `b` and positive on `(a, b)`,
`MovingSofa.positiveGraphLoop` traverses the graph of `f` from `(b, 0)` to `(a, 0)` and then the
base segment from `(a, 0)` back to `(b, 0)`. The main result
`MovingSofa.positiveGraphLoop_counterclockwise` shows that this is a counterclockwise once-traversed
Jordan parametrization whose bounded complementary component is the open subgraph
`{p | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)}`.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Traverse the graph from right to left and return along the horizontal axis. -/
def positiveGraphLoop (a b : ℝ) (f : ℝ → ℝ) (t : Set.Icc (0 : ℝ) 2) : Point :=
  if t.val ≤ 1 then !₂[b - (b - a) * t.val, f (b - (b - a) * t.val)]
  else !₂[a + (b - a) * (t.val - 1), 0]

/-- Every planar point is built from its two coordinates. -/
private lemma point_eq_vecNotation_coords (p : Point) : p = !₂[p 0, p 1] := by
  ext i
  fin_cases i <;> simp

section PositiveGraph

variable {a b : ℝ} {f : ℝ → ℝ}

/-- A positive graph over `[a, b]` vanishing at the ends is nonnegative there. -/
private lemma nonneg_of_pos_on_Ioo (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) {c : ℝ} (hc : c ∈ Set.Icc a b) : 0 ≤ f c := by
  rcases eq_or_lt_of_le hc.1 with h | h
  · rw [← h, ha]
  · rcases eq_or_lt_of_le hc.2 with h' | h'
    · rw [h', hb]
    · exact (hpos c ⟨h, h'⟩).le

/-- Such a graph vanishes only at the two endpoints. -/
private lemma eq_endpoint_of_apply_eq_zero (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    {c : ℝ} (hc : c ∈ Set.Icc a b) (h : f c = 0) : c = a ∨ c = b := by
  by_contra hcon
  push Not at hcon
  exact (hpos c ⟨lt_of_le_of_ne hc.1 (Ne.symm hcon.1), lt_of_le_of_ne hc.2 hcon.2⟩).ne' h

/-- The reversed affine reparametrization of `[0, 1]` lands in the base interval `[a, b]`. -/
private lemma sub_mul_mem_Icc (hab : a < b) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    b - (b - a) * s ∈ Set.Icc a b := by
  obtain ⟨h0, h1⟩ := hs
  constructor <;> nlinarith [sub_pos.mpr hab]

/-- On the first half of the parameter interval the loop traverses the graph right to left. -/
lemma positiveGraphLoop_apply_of_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 2) (h : s ≤ 1) :
    positiveGraphLoop a b f ⟨s, hs⟩ = !₂[b - (b - a) * s, f (b - (b - a) * s)] :=
  ite_eq_left h

/-- On the second half of the parameter interval the loop traverses the base left to right. -/
lemma positiveGraphLoop_apply_of_not_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 2)
    (h : ¬ s ≤ 1) : positiveGraphLoop a b f ⟨s, hs⟩ = !₂[a + (b - a) * (s - 1), 0] :=
  ite_eq_right h

/-- Values of the loop on the base half, including the joining parameter. -/
private lemma positiveGraphLoop_apply_base (ha : f a = 0) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 2)
    (h1 : 1 ≤ u) : positiveGraphLoop a b f ⟨u, hu⟩ = !₂[a + (b - a) * (u - 1), 0] := by
  by_cases h : u ≤ 1
  · have hu1 : u = 1 := le_antisymm h h1
    rw [positiveGraphLoop_apply_of_le hu h, show b - (b - a) * u = a by rw [hu1]; ring, ha,
      show a + (b - a) * (u - 1) = a by rw [hu1]; ring]
  · exact positiveGraphLoop_apply_of_not_le hu h

/-- The two halves agree at the joining parameter, so the loop is continuous. -/
private lemma continuous_positiveGraphLoop (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) : Continuous (positiveGraphLoop a b f) := by
  unfold positiveGraphLoop
  apply continuous_if_le continuous_subtype_val continuous_const
  · refine (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
      (ContinuousOn.matrixVecCons (by fun_prop)
        (ContinuousOn.matrixVecCons (hf.comp (by fun_prop) ?_) continuousOn_const))
    intro t ht
    exact sub_mul_mem_Icc hab ⟨t.property.1, ht⟩
  · exact (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
      (ContinuousOn.matrixVecCons (by fun_prop)
        (ContinuousOn.matrixVecCons continuousOn_const continuousOn_const))
  · intro t ht
    have h1 : b - (b - a) * (t : ℝ) = a := by rw [ht]; ring
    have h2 : a + (b - a) * ((t : ℝ) - 1) = a := by rw [ht]; ring
    rw [h1, h2, ha]

/-- The loop traces exactly the graph of `f` together with the base segment. -/
private lemma range_positiveGraphLoop (hab : a < b) (ha : f a = 0) :
    Set.range (positiveGraphLoop a b f) =
      (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b ∪
        (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    obtain ⟨h0, h2⟩ := hs
    by_cases h : s ≤ 1
    · exact Or.inl ⟨_, sub_mul_mem_Icc hab ⟨h0, h⟩, (positiveGraphLoop_apply_of_le _ h).symm⟩
    · push Not at h
      exact Or.inr ⟨_, ⟨by nlinarith, by nlinarith⟩,
        (positiveGraphLoop_apply_of_not_le _ (not_le.mpr h)).symm⟩
  · rintro p (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · have h1 : (b - c) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.1])
      have h0 : 0 ≤ (b - c) / (b - a) := div_nonneg (by linarith [hc.2]) hL.le
      have hmem : (b - c) / (b - a) ∈ Set.Icc (0 : ℝ) 2 := ⟨h0, by linarith⟩
      refine ⟨⟨(b - c) / (b - a), hmem⟩, ?_⟩
      rw [positiveGraphLoop_apply_of_le hmem h1,
        show b - (b - a) * ((b - c) / (b - a)) = c by field_simp; ring]
    · by_cases hca : c = a
      · have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by norm_num
        refine ⟨⟨1, hmem⟩, ?_⟩
        rw [positiveGraphLoop_apply_of_le hmem le_rfl,
          show b - (b - a) * (1 : ℝ) = a by ring, ha, hca]
      · have hac : a < c := lt_of_le_of_ne hc.1 (Ne.symm hca)
        have h0 : 0 < (c - a) / (b - a) := div_pos (by linarith) hL
        have h1 : (c - a) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.2])
        have hmem : 1 + (c - a) / (b - a) ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith, by linarith⟩
        refine ⟨⟨1 + (c - a) / (b - a), hmem⟩, ?_⟩
        rw [positiveGraphLoop_apply_of_not_le hmem (by simp; linarith),
          show a + (b - a) * (1 + (c - a) / (b - a) - 1) = c by field_simp; ring]

/-- The loop is injective before its final parameter: the two halves meet only at the ends. -/
private lemma injOn_positiveGraphLoop (hab : a < b)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    Set.InjOn (positiveGraphLoop a b f) {t | (t : ℝ) < 2} := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  rintro ⟨s, hs⟩ hs2 ⟨u, hu⟩ hu2 heq
  simp only [Set.mem_ofPred_eq] at hs2 hu2
  refine Subtype.ext (show s = u from ?_)
  by_cases hsl : s ≤ 1 <;> by_cases hul : u ≤ 1
  · rw [positiveGraphLoop_apply_of_le hs hsl, positiveGraphLoop_apply_of_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    have h := heq.1
    nlinarith
  · exfalso
    rw [positiveGraphLoop_apply_of_le hs hsl, positiveGraphLoop_apply_of_not_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    push Not at hul
    rcases eq_endpoint_of_apply_eq_zero hpos (sub_mul_mem_Icc hab ⟨hs.1, hsl⟩) heq.2 with h | h
    · rw [h] at heq
      nlinarith [heq.1]
    · rw [h] at heq
      nlinarith [heq.1]
  · exfalso
    rw [positiveGraphLoop_apply_of_not_le hs hsl, positiveGraphLoop_apply_of_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    push Not at hsl
    rcases eq_endpoint_of_apply_eq_zero hpos (sub_mul_mem_Icc hab ⟨hu.1, hul⟩) heq.2.symm with h | h
    · rw [h] at heq
      nlinarith [heq.1]
    · rw [h] at heq
      nlinarith [heq.1]
  · rw [positiveGraphLoop_apply_of_not_le hs hsl, positiveGraphLoop_apply_of_not_le hu hul] at heq
    simp only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at heq
    nlinarith [heq]

/-- The graph arc and the base arc share exactly their endpoints, so they glue to a Jordan
curve. -/
private lemma isJordanCurve_range_positiveGraphLoop (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsJordanCurve (Set.range (positiveGraphLoop a b f)) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hmapsto : ∀ u : unitInterval, b - (b - a) * (u : ℝ) ∈ Set.Icc a b :=
    fun u ↦ sub_mul_mem_Icc hab u.property
  have hcontf : Continuous fun u : unitInterval ↦ f (b - (b - a) * (u : ℝ)) :=
    continuousOn_univ.mp (hf.comp (by fun_prop) fun u _ ↦ hmapsto u)
  have hcontx : Continuous fun u : unitInterval ↦ b - (b - a) * (u : ℝ) := by fun_prop
  let γ : Path (!₂[b, (0 : ℝ)] : Point) (!₂[a, (0 : ℝ)] : Point) :=
    { toFun := fun u ↦ !₂[b - (b - a) * (u : ℝ), f (b - (b - a) * (u : ℝ))]
      continuous_toFun := (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
        (hcontx.matrixVecCons (hcontf.matrixVecCons continuous_const))
      source' := by norm_num [hb]
      target' := by norm_num [ha] }
  let δ : Path (!₂[b, (0 : ℝ)] : Point) (!₂[a, (0 : ℝ)] : Point) :=
    { toFun := fun u ↦ !₂[b - (b - a) * (u : ℝ), (0 : ℝ)]
      continuous_toFun := (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
        (hcontx.matrixVecCons (continuous_const.matrixVecCons continuous_const))
      source' := by norm_num
      target' := by norm_num }
  have hparam : ∀ {u v : unitInterval},
      b - (b - a) * (u : ℝ) = b - (b - a) * (v : ℝ) → u = v :=
    fun h ↦ Subtype.ext (by nlinarith)
  have hcoords : ∀ {x y u v : ℝ}, (!₂[x, y] : Point) = !₂[u, v] → x = u ∧ y = v := by
    intro x y u v h
    simpa only [WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] using h
  have hγinj : Function.Injective γ := fun u v h ↦ hparam (hcoords h).1
  have hδinj : Function.Injective δ := fun u v h ↦ hparam (hcoords h).1
  have hparam_surj : ∀ c ∈ Set.Icc a b, ∃ u : unitInterval, b - (b - a) * (u : ℝ) = c := by
    intro c hc
    have h0 : 0 ≤ (b - c) / (b - a) := div_nonneg (by linarith [hc.2]) hL.le
    have h1 : (b - c) / (b - a) ≤ 1 := (div_le_one hL).mpr (by linarith [hc.1])
    exact ⟨⟨(b - c) / (b - a), h0, h1⟩, by field_simp; ring⟩
  have hrangeγ : Set.range γ = (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, hmapsto u, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hparam_surj c hc
      exact ⟨u, by change (!₂[_, f _] : Point) = _; rw [hu]⟩
  have hrangeδ : Set.range δ = (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, hmapsto u, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hparam_surj c hc
      exact ⟨u, by change (!₂[_, (0 : ℝ)] : Point) = _; rw [hu]⟩
  have hmeet : Set.range γ ∩ Set.range δ =
      {(!₂[b, (0 : ℝ)] : Point), (!₂[a, (0 : ℝ)] : Point)} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
      have hcoord := hcoords
        (show (!₂[b - (b - a) * (u : ℝ), f (b - (b - a) * (u : ℝ))] : Point) =
          !₂[b - (b - a) * (v : ℝ), (0 : ℝ)] from hv.symm)
      rcases eq_endpoint_of_apply_eq_zero hpos (hmapsto u) hcoord.2 with h | h
      · have hu1 : u = 1 := Subtype.ext (by simpa using show (u : ℝ) = 1 by nlinarith)
        exact Or.inr (by rw [show (γ u : Point) = γ 1 from congrArg _ hu1, γ.target]; rfl)
      · have hu0 : u = 0 := Subtype.ext (by simpa using show (u : ℝ) = 0 by nlinarith)
        exact Or.inl (by rw [show (γ u : Point) = γ 0 from congrArg _ hu0, γ.source])
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, γ.source⟩, ⟨0, δ.source⟩⟩
      · exact ⟨⟨1, γ.target⟩, ⟨1, δ.target⟩⟩
  have htau := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair hγinj hδinj hmeet
  rw [range_positiveGraphLoop hab ha, ← hrangeγ, ← hrangeδ]
  obtain ⟨e⟩ := htau
  refine ⟨fun z ↦ (e.symm z : Point), continuous_subtype_val.comp e.symm.continuous,
    fun z w h ↦ e.symm.injective (Subtype.ext h), Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨w, rfl⟩
    exact (e.symm w).property
  · intro z hz
    exact ⟨e ⟨z, hz⟩, congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)⟩

/-- The loop lies in the closed upper half-plane and traverses the supporting base segment in the
positive tangent direction, so it is counterclockwise. -/
private lemma isOrientedJordanParametrization_positiveGraphLoop (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (positiveGraphLoop a b f)) true (positiveGraphLoop a b f) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  set θ : Real.Angle := ((-(Real.pi / 2) : ℝ) : Real.Angle) with hθ
  have hN : normalVector θ = !₂[(0 : ℝ), -1] := by
    ext i
    fin_cases i <;> simp [normalVector, frame, hθ, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have hT : tangentVector θ = !₂[(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> simp [tangentVector, frame, hθ, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have hinner : ∀ p : Point, inner ℝ p (normalVector θ) = -p 1 := by
    intro p
    rw [hN]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
  have hone : positiveGraphLoop a b f ⟨1, by norm_num⟩ = !₂[a, (0 : ℝ)] := by
    rw [positiveGraphLoop_apply_base ha (by norm_num) le_rfl]
    norm_num
  have htwo : positiveGraphLoop a b f ⟨2, by norm_num⟩ = !₂[b, (0 : ℝ)] := by
    rw [positiveGraphLoop_apply_base ha (by norm_num) (by norm_num)]
    norm_num
  refine jordan_counterclockwise_of_supporting_segment 0 2 (by norm_num) _
    (continuous_positiveGraphLoop hab hf ha)
    (isJordanCurve_range_positiveGraphLoop hab hf ha hb hpos) ?_
    (injOn_positiveGraphLoop hab hpos) θ 0 ?_ ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
    (Subtype.mk_lt_mk.mpr (by norm_num)) ?_ (b - a) hL ?_ ?_
  · rw [positiveGraphLoop_apply_of_le (by norm_num) (by norm_num),
      positiveGraphLoop_apply_base ha (by norm_num) (by norm_num)]
    norm_num [hb]
  · intro t
    simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, hinner,
      neg_nonpos]
    obtain ⟨s, hs⟩ := t
    by_cases h : s ≤ 1
    · rw [positiveGraphLoop_apply_of_le hs h]
      exact nonneg_of_pos_on_Ioo ha hb hpos (sub_mul_mem_Icc hab ⟨hs.1, h⟩)
    · rw [positiveGraphLoop_apply_of_not_le hs h]
      exact le_rfl
  · simp only [normalLine, Set.mem_ofPred_eq, hinner, hone]
    norm_num
  · rw [hone, htwo, hT]
    ext i
    fin_cases i <;> simp
  · rw [hone, htwo, segment_eq_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨u, hu⟩, hmem, rfl⟩
      have h1 : (1 : ℝ) ≤ u := hmem.1
      have h2 : u ≤ 2 := hmem.2
      refine ⟨u - 1, ⟨by linarith, by linarith⟩, ?_⟩
      rw [positiveGraphLoop_apply_base ha hu h1]
      ext i
      fin_cases i
      · simp
        ring
      · simp
    · rintro _ ⟨c, hc, rfl⟩
      have hmem : 1 + c ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
      refine ⟨⟨1 + c, hmem⟩, ⟨Subtype.mk_le_mk.mpr (by linarith [hc.1]),
        Subtype.mk_le_mk.mpr (by linarith [hc.2])⟩, ?_⟩
      rw [positiveGraphLoop_apply_base ha hmem (by linarith [hc.1])]
      ext i
      fin_cases i
      · simp
        ring
      · simp

/-- The positive subgraph is open, connected, bounded and relatively closed in the complement of
the loop, hence it is the bounded complementary component. -/
private lemma jordanInterior_range_positiveGraphLoop_of_components (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    jordanInterior (Set.range (positiveGraphLoop a b f)) =
      {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} := by
  set Γ := Set.range (positiveGraphLoop a b f) with hΓ
  set U : Set Point := {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} with hU
  set K : Set Point := {p : Point | a ≤ p 0 ∧ p 0 ≤ b ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0)} with hK
  have hrange : Γ = (fun c ↦ (!₂[c, f c] : Point)) '' Set.Icc a b ∪
      (fun c ↦ (!₂[c, (0 : ℝ)] : Point)) '' Set.Icc a b := range_positiveGraphLoop hab ha
  have hUK : U ⊆ K := fun p hp ↦ ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩
  have hUΓ : U ⊆ Γᶜ := by
    intro p hp hpΓ
    rw [hrange] at hpΓ
    rcases hpΓ with ⟨c, _, hc⟩ | ⟨c, _, hc⟩
    · exact absurd hp.2.2.2 (by rw [← hc]; simp)
    · exact absurd hp.2.2.1 (by rw [← hc]; simp)
  have hKΓU : ∀ p ∈ K, p ∉ Γ → p ∈ U := by
    intro p hp hpΓ
    rw [hrange] at hpΓ
    have hpc : p = !₂[p 0, p 1] := point_eq_vecNotation_coords p
    have h1 : p 1 ≠ 0 := fun h0 ↦ hpΓ (Or.inr ⟨p 0, ⟨hp.1, hp.2.1⟩,
      show (!₂[p 0, (0 : ℝ)] : Point) = p by rw [← h0]; exact hpc.symm⟩)
    have h2 : p 1 ≠ f (p 0) := fun heq ↦ hpΓ (Or.inl ⟨p 0, ⟨hp.1, hp.2.1⟩,
      show (!₂[p 0, f (p 0)] : Point) = p by rw [← heq]; exact hpc.symm⟩)
    have h3 : 0 < p 1 := lt_of_le_of_ne hp.2.2.1 (Ne.symm h1)
    have h4 : p 1 < f (p 0) := lt_of_le_of_ne hp.2.2.2 h2
    refine ⟨?_, ?_, h3, h4⟩
    · rcases eq_or_lt_of_le hp.1 with h | h
      · rw [← h, ha] at h4
        linarith
      · exact h
    · rcases eq_or_lt_of_le hp.2.1 with h | h
      · rw [h, hb] at h4
        linarith
      · exact h
  have hcoord0 : Continuous fun q : Point ↦ q 0 := by fun_prop
  have hcoord1 : Continuous fun q : Point ↦ q 1 := by fun_prop
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨h1, h2, h3, h4⟩
    have hfat : ContinuousAt f (p 0) :=
      (hf.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds h1 h2)
    have hfcoord : ContinuousAt (fun q : Point ↦ f (q 0)) p :=
      ContinuousAt.comp (g := f) (f := fun q : Point ↦ q 0) (x := p) hfat hcoord0.continuousAt
    have hgap : ContinuousAt (fun q : Point ↦ f (q 0) - q 1) p :=
      hfcoord.sub hcoord1.continuousAt
    filter_upwards [hcoord0.continuousAt (isOpen_Ioo.mem_nhds (⟨h1, h2⟩ : p 0 ∈ Set.Ioo a b)),
      hcoord1.continuousAt (isOpen_Ioi.mem_nhds (show p 1 ∈ Set.Ioi (0 : ℝ) from h3)),
      hgap (isOpen_Ioi.mem_nhds (show f (p 0) - p 1 ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr h4))]
      with q hq1 hq2 hq3
    exact ⟨hq1.1, hq1.2, hq2, by simpa using sub_pos.mp hq3⟩
  have hSclosed : IsClosed {q : Point | q 0 ∈ Set.Icc a b} := isClosed_Icc.preimage hcoord0
  have hKclosed : IsClosed K := by
    have hgS : ContinuousOn (fun q : Point ↦ f (q 0) - q 1) {q : Point | q 0 ∈ Set.Icc a b} :=
      (hf.comp hcoord0.continuousOn fun q hq ↦ hq).sub hcoord1.continuousOn
    have hone := hgS.preimage_isClosed_of_isClosed hSclosed (isClosed_Ici (a := (0 : ℝ)))
    have htwo : IsClosed {q : Point | 0 ≤ q 1} := isClosed_Ici.preimage hcoord1
    have hsplit : K = ({q : Point | q 0 ∈ Set.Icc a b} ∩
        (fun q : Point ↦ f (q 0) - q 1) ⁻¹' Set.Ici 0) ∩ {q : Point | 0 ≤ q 1} := by
      ext q
      simp only [hK, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_Ici, sub_nonneg]
      tauto
    rw [hsplit]
    exact hone.inter htwo
  have hUconn : IsConnected U := by
    have hfcomp : ContinuousOn (fun q : ℝ × ℝ ↦ f q.1) (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) :=
      (hf.mono Set.Ioo_subset_Icc_self).comp continuous_fst.continuousOn fun q hq ↦ hq.1
    have hmap : ContinuousOn (fun q : ℝ × ℝ ↦ (!₂[q.1, q.2 * f q.1] : Point))
        (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) :=
      (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
        (continuous_fst.continuousOn.matrixVecCons
          ((continuous_snd.continuousOn.mul hfcomp).matrixVecCons continuousOn_const))
    have hset : U = (fun q : ℝ × ℝ ↦ (!₂[q.1, q.2 * f q.1] : Point)) ''
        (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1) := by
      apply Set.Subset.antisymm
      · rintro p ⟨h1, h2, h3, h4⟩
        have hfpos : 0 < f (p 0) := h3.trans h4
        refine ⟨(p 0, p 1 / f (p 0)), ⟨⟨h1, h2⟩, div_pos h3 hfpos,
          (div_lt_one hfpos).mpr h4⟩, ?_⟩
        change (!₂[p 0, p 1 / f (p 0) * f (p 0)] : Point) = p
        rw [div_mul_cancel₀ _ hfpos.ne']
        exact (point_eq_vecNotation_coords p).symm
      · rintro _ ⟨⟨c, r⟩, ⟨⟨hc1, hc2⟩, hr1, hr2⟩, rfl⟩
        have hfc : 0 < f c := hpos c ⟨hc1, hc2⟩
        refine ⟨by simpa using hc1, by simpa using hc2, by simpa using mul_pos hr1 hfc, ?_⟩
        change r * f c < f c
        nlinarith
    rw [hset]
    exact ((isConnected_Ioo hab).prod (isConnected_Ioo (by norm_num))).image _ hmap
  obtain ⟨c₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab.le) hf
  have hKbdd : Bornology.IsBounded K :=
    (EuclideanSpace.isBounded_coordinate_rectangle a b 0 (f c₀)).subset (by
      rintro p ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, h4.trans (hmax ⟨h1, h2⟩)⟩)
  have hUbdd : Bornology.IsBounded U := hKbdd.subset hUK
  have hcompU : ∀ p ∈ U, connectedComponentIn Γᶜ p = U := by
    intro p hp
    have hsub : connectedComponentIn Γᶜ p ⊆ Γᶜ := connectedComponentIn_subset _ _
    refine Set.Subset.antisymm ?_ (hUconn.isPreconnected.subset_connectedComponentIn hp hUΓ)
    have hcover : connectedComponentIn Γᶜ p ⊆ U ∪ Kᶜ := by
      intro q hq
      by_cases hqK : q ∈ K
      · exact Or.inl (hKΓU q hqK (hsub hq))
      · exact Or.inr hqK
    have hmeet : (connectedComponentIn Γᶜ p ∩ U).Nonempty :=
      ⟨p, mem_connectedComponentIn (hUΓ hp), hp⟩
    have hempty : ¬ (connectedComponentIn Γᶜ p ∩ Kᶜ).Nonempty := by
      intro hk
      obtain ⟨z, hz⟩ := isPreconnected_connectedComponentIn U Kᶜ hUopen
        hKclosed.isOpen_compl hcover hmeet hk
      exact hz.2.2 (hUK hz.2.1)
    intro q hq
    by_contra hqU
    exact hempty ⟨q, hq, fun hqK ↦ hqU (hKΓU q hqK (hsub hq))⟩
  obtain ⟨p₀, hp₀⟩ := hUconn.nonempty
  obtain ⟨U', V', -, -, -, -, -, hV'ub, -, hcover, -, -, hcU, hcV⟩ :=
    jordan_separation (isJordanCurve_range_positiveGraphLoop hab hf ha hb hpos)
  have hp₀U' : p₀ ∈ U' := by
    rcases hcover.symm.subset (hUΓ hp₀) with h | h
    · exact h
    · exact absurd (by rw [← hcV p₀ h, hcompU p₀ hp₀]; exact hUbdd) hV'ub
  have hU'eq : U' = U := by rw [← hcU p₀ hp₀U', hcompU p₀ hp₀]
  ext p
  constructor
  · rintro ⟨hpΓ, hpb⟩
    rcases hcover.symm.subset hpΓ with h | h
    · rwa [← hU'eq]
    · exact absurd (by rwa [← hcV p h]) hV'ub
  · intro hp
    exact ⟨hUΓ hp, by rw [hcompU p hp]; exact hUbdd⟩

end PositiveGraph

theorem positiveGraphLoop_counterclockwise (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (positiveGraphLoop a b f)) true (positiveGraphLoop a b f) ∧
    jordanInterior (Set.range (positiveGraphLoop a b f)) =
      {p : Point | a < p 0 ∧ p 0 < b ∧ 0 < p 1 ∧ p 1 < f (p 0)} :=
  ⟨isOrientedJordanParametrization_positiveGraphLoop hab hf ha hb hpos,
    jordanInterior_range_positiveGraphLoop_of_components hab hf ha hb hpos⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The region enclosed by the counterclockwise loop around a positive graph

`MovingSofa.positiveGraphLoop_counterclockwise` identifies the bounded complementary component
of the loop around the graph of a positive `f` with the open subgraph of `f`.  This file records
the resulting description of the closed subgraph: the loop traces exactly the frontier of either
region, and the closed subgraph is the open one together with that frontier.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

variable {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
  (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)

include hab hf ha hb hpos

/-- The bounded complementary component of the positive-graph loop is the open subgraph. -/
theorem jordanInterior_range_positiveGraphLoop :
    jordanInterior (Set.range (positiveGraphLoop a b f)) = openSubgraph a b f :=
  (positiveGraphLoop_counterclockwise a b hab f hf ha hb hpos).2

/-- The positive-graph loop traces the frontier of the open subgraph. -/
theorem frontier_openSubgraph :
    frontier (openSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [← jordanInterior_range_positiveGraphLoop hab hf ha hb hpos]
  exact (positiveGraphLoop_counterclockwise a b hab f hf ha hb
    hpos).1.2.1.frontier_jordanInterior

/-- The part of the closed subgraph outside the open one is exactly the loop. -/
theorem closedSubgraph_sdiff_openSubgraph :
    closedSubgraph a b f \ openSubgraph a b f = Set.range (positiveGraphLoop a b f) := by
  rw [← frontier_openSubgraph hab hf ha hb hpos, frontier, (isOpen_openSubgraph hf).interior_eq,
    closure_openSubgraph hab hf ha hb hpos]

/-- The closed subgraph is the open subgraph together with the loop. -/
theorem closedSubgraph_eq_openSubgraph_union_range :
    closedSubgraph a b f = openSubgraph a b f ∪ Set.range (positiveGraphLoop a b f) := by
  rw [← closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]
  exact (Set.union_sdiff_cancel openSubgraph_subset_closedSubgraph).symm

/-- The positive-graph loop also traces the frontier of the closed subgraph. -/
theorem frontier_closedSubgraph :
    frontier (closedSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [frontier, (isClosed_closedSubgraph hf).closure_eq, interior_closedSubgraph hf ha hb,
    closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]

end MovingSofa

end

end

end
