/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CapUnique
public import LeanPool.GraphMinor.GM19.CapExists
public import LeanPool.GraphMinor.GM19.Conditional2
public import LeanPool.GraphMinor.GM20.Draw10

/-!
# Filling a cuff of a model surface

The surface `Σ(a, b, c + 1)` is `Σ(a, b, c)` with one more open disc removed. So a capping of `Σ(a,
b, c)` is a
capping of `Σ(a, b, c + 1)`, and by induction `Σ(a, b, 0)` caps every `Σ(a, b, c)` (`capModel`). An
orientation of
`Σ(a, b, c)` restricts to `Σ(a, b, c + 1)` (`modelOrientation`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM20.Draw

theorem base_succ {n : ℕ} : modelBase (n + 1) ⊆ modelBase n :=
  fun _ hp i hi x hx ↦ hp i (by omega) x hx

theorem three_le_dist_centre {i j : ℕ} (h : i ≠ j) : 3 ≤ dist (modelCentre i) (modelCentre j) := by
  have h₁ := norm_sq (modelCentre i - modelCentre j)
  rw [dist_eq_norm]
  have h₂ : (1 : ℝ) ≤ ((i : ℝ) - j) ^ 2 := by
    have : ((i : ℤ) - j) ≠ 0 := by omega
    have h₃ : (1 : ℤ) ≤ ((i : ℤ) - j) ^ 2 := Int.add_one_le_iff.2 (sq_pos_iff.2 this)
    exact_mod_cast h₃
  have h₄ : ‖modelCentre i - modelCentre j‖ ^ 2 = 9 * ((i : ℝ) - j) ^ 2 := by
    rw [h₁]
    simp [modelCentre]
    ring
  have h₅ : 0 ≤ ‖modelCentre i - modelCentre j‖ := norm_nonneg _
  nlinarith

/-- A point on one of the first `n` circles is far from the `n`th centre. -/
theorem mem_base_succ {n i : ℕ} (hi : i < n) {u : EuclideanPlane} (hu : ‖u‖
  = 1) {p : OnePoint EuclideanPlane}
    (hp : p ∈ modelBase n) (he : p = ((modelCentre i + u : EuclideanPlane) : OnePoint
      EuclideanPlane)) :
    p ∈ modelBase (n + 1) := by
  intro j hj x hx
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact hp j hj x hx
  · obtain rfl : modelCentre i + u = x := OnePoint.coe_injective (he.symm.trans hx)
    have h₁ := three_le_dist_centre hi.ne
    have h₂ : dist (modelCentre i) (modelCentre j) ≤ dist (modelCentre i) (modelCentre i + u) +
        dist (modelCentre i + u) (modelCentre j) := dist_triangle _ _ _
    have h₃ : dist (modelCentre i) (modelCentre i + u) = 1 := by
      rw [dist_eq_norm]
      simpa using hu
    linarith

theorem mem_base_succ' {n i : ℕ} (hi : i < n) {u : EuclideanPlane} (hu : ‖u‖
  = 1) {p : OnePoint EuclideanPlane}
    (hp : p ∈ modelBase n) (he : p = ((modelCentre i - u : EuclideanPlane) : OnePoint
      EuclideanPlane)) :
    p ∈ modelBase (n + 1) :=
  mem_base_succ hi (u := -u) (by simpa using hu) hp (by rw [he, sub_eq_add_neg])

theorem norm_modelMirror (u : EuclideanPlane) : ‖modelMirror u‖ = ‖u‖ := by
  have h₁ := norm_sq (modelMirror u)
  have h₂ := norm_sq u
  have h₃ : ‖modelMirror u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [h₁, h₂]
    simp [modelMirror]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₃

variable (a b c : ℕ)

/-- The map `Σ(a, b, c + 1) → Σ(a, b, c)` that forgets that the last open disc was removed. -/
noncomputable def plug : SurfaceModel a b (c + 1) → SurfaceModel a b c :=
  Quot.map (fun p : modelBase (2 * a + b + (c + 1)) ↦ (⟨p.1, base_succ p.2⟩ : modelBase
    (2 * a + b + c)))
    fun p q h ↦ by
      cases h with
      | handle i hi u hu _ _ hp hq => exact ModelGlue.handle i hi u hu _ _ hp hq
      | crosscap i hi u hu _ _ hp hq => exact ModelGlue.crosscap i hi u hu _ _ hp hq

/-- A left inverse of `plug`. -/
noncomputable def unplug : SurfaceModel a b c → Option (SurfaceModel a b (c + 1)) :=
  open Classical in
  Quot.lift (fun p : modelBase (2 * a + b + c) ↦ if h : p.1 ∈ modelBase (2 * a + b + (c + 1)) then
      some (Quot.mk _ ⟨p.1, h⟩) else none) fun p q h ↦ by
    cases h with
    | handle i hi u hu _ _ hp hq =>
      have h₁ : p.1 ∈ modelBase (2 * a + b + (c + 1)) := mem_base_succ (n := 2 * a + b + c)
        (by omega) hu p.2 hp
      have h₂ : q.1 ∈ modelBase (2 * a + b + (c + 1)) :=
        mem_base_succ (n := 2 * a + b + c) (by omega) (by rwa [norm_modelMirror]) q.2 hq
      simp only [h₁, h₂, dite_true]
      exact congrArg some (Quot.sound (ModelGlue.handle i hi u hu _ _ hp hq))
    | crosscap i hi u hu _ _ hp hq =>
      have h₁ : p.1 ∈ modelBase (2 * a + b + (c + 1)) := mem_base_succ (n := 2 * a + b + c)
        (by omega) hu p.2 hp
      have h₂ : q.1 ∈ modelBase (2 * a + b + (c + 1)) := mem_base_succ' (n := 2 * a + b + c)
        (by omega) hu q.2 hq
      simp only [h₁, h₂, dite_true]
      exact congrArg some (Quot.sound (ModelGlue.crosscap i hi u hu _ _ hp hq))

theorem unplug_plug (x : SurfaceModel a b (c + 1)) : unplug a b c (plug a b c x) = some x := by
  classical
  induction x using Quot.ind with
  | mk p =>
    exact dite_eq_left p.2

theorem plug_injective : Function.Injective (plug a b c) := fun x y h ↦ by
  have := congrArg (unplug a b c) h
  rw [unplug_plug, unplug_plug] at this
  exact Option.some.inj this

theorem continuous_plug : Continuous (plug a b c) :=
  continuous_quot_lift _ (continuous_quot_mk.comp (Continuous.subtype_mk continuous_subtype_val _))

variable {a b c}

theorem ok_of_succ {z : ℝ × ℝ} (h : Ok a b (c + 1) z) : Ok a b c z := fun i hi ↦ h i (by omega)

theorem plug_qq {z : ℝ × ℝ} (h : Ok a b (c + 1) z) : plug a b c (qq a b (c + 1) z) = qq a b c z
  := by
  rw [qq_of_ok h, qq_of_ok (ok_of_succ h)]
  rfl

theorem interior_iff_of_openEmbedding {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X
  → Y}
    (hf : IsOpenEmbedding f) (x : X) : IsInteriorPoint (f x) ↔ IsInteriorPoint x := by
  constructor
  · intro h
    obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := h.exists_subset hf.isOpen_range ⟨x, rfl⟩
    exact ⟨f ⁻¹' U, hU.preimage hf.continuous, hx,
      ⟨(hf.isEmbedding.homeomorphImage _).trans
        ((Homeomorph.setCongr (image_preimage_eq_of_subset hsub)).trans e)⟩⟩
  · rintro ⟨U, hU, hx, ⟨e⟩⟩
    exact ⟨f '' U, hf.isOpenMap _ hU, mem_image_of_mem _ hx, ⟨(hf.isEmbedding.homeomorphImage
      U).symm.trans e⟩⟩

variable (a b c)

/-- The index of the circle that `plug` fills. -/
abbrev lastHole : ℕ := 2 * a + b + c

variable {a b c}

theorem ok_near {ζ : ℂ} (h : ‖ζ - cz (lastHole a b c)‖ < 2) : Ok a b c (cp ζ) := fun i hi ↦ by
  rw [← nsq]
  exact (sq_of_one_lt (one_lt_far (by unfold lastHole at *; omega) h)).le

theorem ok_near' {ζ : ℂ} (h₁ : 1 ≤ ‖ζ - cz (lastHole a b c)‖) (h : ‖ζ - cz (lastHole a b c)‖ < 2) :
    Ok a b (c + 1) (cp ζ) := fun i hi ↦ by
  rw [← nsq]
  by_cases he : i = lastHole a b c
  · subst he
    nlinarith
  · exact (sq_of_one_lt (one_lt_far he h)).le

theorem free_last {ζ : ℂ} (h : ‖ζ - cz (lastHole a b c)‖ < 2) : Free a b (cp ζ) :=
  free_near (I := lastHole a b c) (by unfold lastHole; omega) h

theorem plug_qq_near {ζ : ℂ} (h₁ : 1 ≤ ‖ζ - cz (lastHole a b c)‖) (h : ‖ζ - cz
  (lastHole a b c)‖ < 2) :
    plug a b c (qq a b (c + 1) (cp ζ)) = qq a b c (cp ζ) := plug_qq (ok_near' h₁ h)

theorem pl_cp_mk (v : EuclideanPlane) : pl (cp ⟨v 0, v 1⟩) = v := by
  ext j
  fin_cases j <;> simp [pl, cp]

theorem norm_sub_cz (ζ : ℂ) (i : ℕ) : ‖ζ - cz i‖ = dist (pl (cp ζ)) (modelCentre i) := by
  have h := dist_centre_sq (cp ζ) i
  rw [← nsq] at h
  exact ((sq_eq_sq₀ dist_nonneg (norm_nonneg _)).1 h).symm

/-- The closed disc that fills the last circle. -/
noncomputable def fillDisc (a b c : ℕ) : Set (SurfaceModel a b c) :=
  (fun ζ ↦ qq a b c (cp ζ)) '' closedBall (cz (lastHole a b c)) 1

/-- The last circle in `Σ(a, b, c + 1)`. -/
noncomputable def lastCuff (a b c : ℕ) : Set (SurfaceModel a b (c + 1)) :=
  (fun ζ ↦ qq a b (c + 1) (cp ζ)) '' sphere (cz (lastHole a b c)) 1

theorem image_lastCuff : plug a b c '' lastCuff a b c =
    (fun ζ ↦ qq a b c (cp ζ)) '' sphere (cz (lastHole a b c)) 1 := by
  unfold lastCuff
  rw [image_image]
  refine image_congr fun ζ hζ ↦ ?_
  have : ‖ζ - cz (lastHole a b c)‖ = 1 := by simpa [dist_eq_norm] using hζ
  exact plug_qq_near this.ge (by linarith)

theorem fillDisc_facts [T2Space (SurfaceModel a b c)] : IsClosedDisc (fillDisc a b c) ∧
    discBd (fillDisc a b c) = (fun ζ ↦ qq a b c (cp ζ)) '' sphere (cz (lastHole a b c)) 1 := by
  have hn : ∀ u : ClosedUnitDisc, ‖complexPlane.symm u.1‖ ≤ 1 := fun u ↦ by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 u.2
  have hn' : ∀ u : ClosedUnitDisc, ‖(cz (lastHole a b c) + complexPlane.symm u.1) - cz
    (lastHole a b c)‖ < 2 :=
    fun u ↦ by
      rw [add_sub_cancel_left]
      linarith [hn u]
  let G : ClosedUnitDisc → SurfaceModel a b c := fun u ↦ qq a b c (cp (cz
    (lastHole a b c) + complexPlane.symm u.1))
  have hc : Continuous G := continuousOn_qq.comp_continuous
    (continuous_cp.comp (continuous_const.add (complexPlane.symm.continuous.comp
      continuous_subtype_val)))
    fun u ↦ ok_near (hn' u)
  have hi : Function.Injective G := fun u v h ↦ by
    have h₁ := cp_injective (eq_of_free (ok_near (hn' u)) (free_last (hn' u)) (ok_near (hn' v))
      (free_last (hn' v)) h)
    exact Subtype.ext (complexPlane.symm.injective (add_left_cancel h₁))
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have he : IsEmbedding G := (hc.isClosedEmbedding hi).isEmbedding
  have hr : range G = fillDisc a b c := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨_, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hn u
    · rintro ⟨ζ, hζ, rfl⟩
      have h₁ : ‖complexPlane (ζ - cz (lastHole a b c))‖ ≤ 1 := by
        rw [LinearIsometryEquiv.norm_map]
        simpa [dist_eq_norm] using hζ
      refine ⟨⟨_, mem_closedBall_zero_iff.2 h₁⟩, ?_⟩
      simp [G]
  let φ : ClosedUnitDisc ≃ₜ fillDisc a b c := he.toHomeomorph.trans (Homeomorph.setCongr hr)
  refine ⟨⟨φ⟩, ?_⟩
  rw [disc_boundary (fillDisc a b c) φ]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨cz (lastHole a b c) + complexPlane.symm u.1, ?_, rfl⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.1 hu
  · rintro ⟨ζ, hζ, rfl⟩
    have h₁ : ‖complexPlane (ζ - cz (lastHole a b c))‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map]
      simpa [dist_eq_norm] using hζ
    refine ⟨⟨_, mem_closedBall_zero_iff.2 h₁.le⟩, mem_sphere_zero_iff_norm.2 h₁, ?_⟩
    change G ⟨_, _⟩ = _
    simp [G]

theorem range_union_fillDisc : range (plug a b c) ∪ fillDisc a b c = univ := by
  classical
  refine eq_univ_of_forall fun x ↦ ?_
  induction x using Quot.ind with
  | mk p =>
    by_cases h : p.1 ∈ modelBase (2 * a + b + (c + 1))
    · exact Or.inl ⟨Quot.mk _ ⟨p.1, h⟩, rfl⟩
    · right
      change ¬ ∀ i < 2 * a + b + (c + 1), ∀ x : EuclideanPlane, p.1 = x → 1 ≤ dist x
        (modelCentre i) at h
      push Not at h
      obtain ⟨i, hi, v, hv, hlt⟩ := h
      have hin : i = lastHole a b c := by
        by_contra hne
        have := p.2 i (by unfold lastHole at *; omega) v hv
        linarith
      subst hin
      have h₁ : ‖(⟨v 0, v 1⟩ : ℂ) - cz (lastHole a b c)‖ < 1 := by
        rw [norm_sub_cz, pl_cp_mk]
        exact hlt
      refine ⟨⟨v 0, v 1⟩, ?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm]
        exact h₁.le
      · have hok := ok_near (a := a) (b := b) (c := c) (ζ := ⟨v 0, v 1⟩) (by linarith)
        change qq a b c _ = _
        rw [qq_of_ok hok]
        refine congrArg _ (Subtype.ext ?_)
        change ((pl (cp ⟨v 0, v 1⟩) : EuclideanPlane) : OnePoint EuclideanPlane) = p.1
        rw [pl_cp_mk, hv]

theorem eq_one_of_mem_range {ζ : ℂ} (h : ‖ζ - cz (lastHole a b c)‖ ≤ 1)
    (hr : qq a b c (cp ζ) ∈ range (plug a b c)) : ‖ζ - cz (lastHole a b c)‖ = 1 := by
  refine le_antisymm h ?_
  obtain ⟨x, hx⟩ := hr
  induction x using Quot.ind with
  | mk p =>
    have h₂ : ‖ζ - cz (lastHole a b c)‖ < 2 := by linarith
    have h₃ := base_eq (ok_near h₂) (free_last h₂) hx
    change p.1 = _ at h₃
    have h₄ := p.2 (lastHole a b c) (by unfold lastHole; omega) _ h₃
    rw [norm_sub_cz]
    exact h₄

theorem range_inter_fillDisc :
    range (plug a b c) ∩ fillDisc a b c = plug a b c '' lastCuff a b c := by
  rw [image_lastCuff]
  apply Subset.antisymm
  · rintro x ⟨hr, ζ, hζ, rfl⟩
    have h₁ : ‖ζ - cz (lastHole a b c)‖ ≤ 1 := by simpa [dist_eq_norm] using hζ
    refine ⟨ζ, ?_, rfl⟩
    rw [mem_sphere, dist_eq_norm]
    exact eq_one_of_mem_range h₁ hr
  · rintro x ⟨ζ, hζ, rfl⟩
    have h₁ : ‖ζ - cz (lastHole a b c)‖ = 1 := by simpa [dist_eq_norm] using hζ
    exact ⟨⟨_, plug_qq_near h₁.ge (by linarith)⟩, ζ, sphere_subset_closedBall hζ, rfl⟩

theorem qq_interior {ζ : ℂ} (h : ‖ζ - cz (lastHole a b c)‖ < 2) : IsInteriorPoint (qq a b c (cp ζ))
  := by
  have hmem : ∀ ζ ∈ ball (cz (lastHole a b c)) 2, ‖ζ - cz (lastHole a b c)‖ < 2 := fun ζ hζ ↦ by
    simpa [dist_eq_norm] using hζ
  have hj := isOpenEmbedding_chart (a := a) (b := b) (c := c) (B := ball (cz
    (lastHole a b c)) 2) isOpen_ball
    fun ζ hζ _ ↦ free_last (hmem ζ hζ)
  have hW : chartDom a b c (ball (cz (lastHole a b c)) 2) = ball (cz (lastHole a b c)) 2 :=
    inter_eq_left.2 fun ζ hζ ↦ ok_near (hmem ζ hζ)
  have he : Nonempty (chartDom a b c (ball (cz (lastHole a b c)) 2) ≃ₜ OpenUnitDisc) :=
    ⟨(Homeomorph.setCongr hW).trans (ballHomeo _ two_pos)⟩
  have hw : ζ ∈ chartDom a b c (ball (cz (lastHole a b c)) 2) :=
    ⟨by simpa [dist_eq_norm] using h, ok_near h⟩
  exact interior_of_chart hj he ⟨ζ, hw⟩

theorem qq_mem_bd_circle {ζ₀ : ℂ} (h : ‖ζ₀ - cz (lastHole a b c)‖ = 1) :
    qq a b (c + 1) (cp ζ₀) ∈ bd (SurfaceModel a b (c + 1)) := by
  set d := ζ₀ - cz (lastHole a b c) with hd
  have hB : ∀ ζ ∈ ball ζ₀ (1 / 2), ‖ζ - cz (lastHole a b c)‖ < 2 := fun ζ hζ ↦ by
    have h₁ : ‖ζ - ζ₀‖ < 1 / 2 := by simpa [dist_eq_norm] using hζ
    have h₂ : ζ - cz (lastHole a b c) = (ζ - ζ₀) + d := by rw [hd]; ring
    rw [h₂]
    linarith [norm_add_le (ζ - ζ₀) d]
  have hj := isOpenEmbedding_chart (a := a) (b := b) (c := c + 1) (B := ball ζ₀ (1 / 2)) isOpen_ball
    fun ζ hζ _ ↦ free_last (hB ζ hζ)
  have hw : ζ₀ ∈ chartDom a b (c + 1) (ball ζ₀ (1 / 2)) :=
    ⟨mem_ball_self (by norm_num), ok_near' h.ge (by linarith)⟩
  refine not_interior_of_chart hj ⟨_, hw⟩ fun hint ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set t : ℝ := min ε 1 / 2 with ht
  have ht₀ : 0 < t := by positivity
  have ht₁ : t ≤ 1 / 2 := by
    have := min_le_right ε 1
    rw [ht]
    linarith
  have ht₂ : t < ε := by
    have := min_le_left ε 1
    rw [ht]
    linarith [lt_min hε one_pos]
  have hmem : ζ₀ - (t : ℂ) * d ∈ ball ζ₀ ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, h, mul_one,
      Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht₀]
    exact ht₂
  have hok := (hball hmem).2 (lastHole a b c) (by unfold lastHole; omega)
  change 1 ≤ ((cp _).1 - 3 * (lastHole a b c : ℝ)) ^ 2 + (cp _).2 ^ 2 at hok
  rw [← nsq] at hok
  have h₂ : ζ₀ - (t : ℂ) * d - cz (lastHole a b c) = ((1 - t : ℝ) : ℂ) * d := by
    rw [hd]
    push_cast
    ring
  rw [h₂, norm_mul, h, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)] at hok
  nlinarith

theorem isClosedEmbedding_plug : IsClosedEmbedding (plug a b c) := by
  have : T2Space (SurfaceModel a b c) := (presents_ew a b c).1
  have : CompactSpace (SurfaceModel a b (c + 1)) := (isSurface_model a b (c + 1)).1.1
  exact (continuous_plug a b c).isClosedEmbedding (plug_injective a b c)

theorem isClosed_lastCuff [T2Space (SurfaceModel a b (c + 1))] : IsClosed (lastCuff a b c) := by
  have hcont : ContinuousOn (fun ζ ↦ qq a b (c + 1) (cp ζ)) (sphere (cz (lastHole a b c)) 1) :=
    continuousOn_qq.comp continuous_cp.continuousOn fun ζ hζ ↦ by
      have h₁ : ‖ζ - cz (lastHole a b c)‖ = 1 := by simpa [dist_eq_norm] using hζ
      exact ok_near' h₁.ge (by linarith)
  exact ((isCompact_sphere _ _).image_of_continuousOn hcont).isClosed

/-- Off the last cuff, `plug` keeps both interior points and boundary points. -/
theorem mem_bd_plug_iff [T2Space (SurfaceModel a b c)] [T2Space (SurfaceModel a b (c + 1))]
    {s : SurfaceModel a b (c + 1)} (hs : s ∉ lastCuff a b c) :
    plug a b c s ∈ bd (SurfaceModel a b c) ↔ s ∈ bd (SurfaceModel a b (c + 1)) := by
  have hO : IsOpen (lastCuff a b c)ᶜ := isClosed_lastCuff.isOpen_compl
  have hd := (fillDisc_facts (a := a) (b := b) (c := c)).1
  have hr : range (plug a b c ∘ ((↑) : ((lastCuff a b c)ᶜ : Set (SurfaceModel a b (c + 1)))
    → SurfaceModel a b (c + 1))) = (fillDisc a b c)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩ hx
      have h₁ : plug a b c y ∈ plug a b c '' lastCuff a b c := by
        rw [← range_inter_fillDisc]
        exact ⟨mem_range_self y, hx⟩
      obtain ⟨z, hz, he⟩ := h₁
      exact hy (plug_injective a b c he ▸ hz)
    · intro hx
      obtain ⟨y, rfl⟩ : x ∈ range (plug a b c) := (range_union_fillDisc (a := a) (b := b) (c
        := c) ▸ mem_univ x :
        x ∈ range (plug a b c) ∪ fillDisc a b c).resolve_right hx
      refine ⟨⟨y, fun hy ↦ hx ?_⟩, rfl⟩
      have : plug a b c y ∈ plug a b c '' lastCuff a b c := mem_image_of_mem _ hy
      rw [← range_inter_fillDisc] at this
      exact this.2
  have hf : IsOpenEmbedding (plug a b c ∘ ((↑) : ((lastCuff a b c)ᶜ : Set (SurfaceModel a b
    (c + 1))) → SurfaceModel a b (c + 1))) :=
    ⟨isClosedEmbedding_plug.isEmbedding.comp IsEmbedding.subtypeVal, hr ▸ hd.isClosed.isOpen_compl⟩
  have h₁ := interior_iff_of_openEmbedding hf ⟨s, hs⟩
  have h₂ := interior_iff_of_openEmbedding hO.isOpenEmbedding_subtypeVal ⟨s, hs⟩
  exact not_congr (h₁.trans h₂.symm)

theorem disjoint_fillDisc_bd : Disjoint (fillDisc a b c) (bd (SurfaceModel a b c)) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨ζ, hζ, rfl⟩ hb
  have h₁ : ‖ζ - cz (lastHole a b c)‖ ≤ 1 := by simpa [dist_eq_norm] using hζ
  exact hb (qq_interior (by linarith))

theorem bd_plug [T2Space (SurfaceModel a b c)] [T2Space (SurfaceModel a b (c + 1))] :
    bd (SurfaceModel a b c) = plug a b c '' (bd (SurfaceModel a b (c + 1)) \ lastCuff a b c) := by
  apply Subset.antisymm
  · intro x hx
    have hxd : x ∉ fillDisc a b c := fun h ↦ disjoint_left.1 disjoint_fillDisc_bd h hx
    obtain ⟨y, rfl⟩ : x ∈ range (plug a b c) := (range_union_fillDisc (a := a) (b := b) (c
      := c) ▸ mem_univ x :
      x ∈ range (plug a b c) ∪ fillDisc a b c).resolve_right hxd
    have hy : y ∉ lastCuff a b c := fun hy ↦ hxd (by
      have : plug a b c y ∈ plug a b c '' lastCuff a b c := mem_image_of_mem _ hy
      rw [← range_inter_fillDisc] at this
      exact this.2)
    exact ⟨y, ⟨(mem_bd_plug_iff hy).1 hx, hy⟩, rfl⟩
  · rintro _ ⟨y, ⟨hy, hyC⟩, rfl⟩
    exact (mem_bd_plug_iff hyC).2 hy

theorem lastCuff_subset_bd : lastCuff a b c ⊆ bd (SurfaceModel a b (c + 1)) := by
  rintro _ ⟨ζ, hζ, rfl⟩
  exact qq_mem_bd_circle (by simpa [dist_eq_norm] using hζ)

theorem lastCuff_mem_cuffs [T2Space (SurfaceModel a b c)] [T2Space (SurfaceModel a b (c + 1))] :
    lastCuff a b c ∈ cuffs (SurfaceModel a b (c + 1)) := by
  have hζ₀ : cz (lastHole a b c) + 1 ∈ sphere (cz (lastHole a b c)) 1 := by simp
  set y₀ := qq a b (c + 1) (cp (cz (lastHole a b c) + 1)) with hy₀
  have hmem : y₀ ∈ lastCuff a b c := ⟨_, hζ₀, rfl⟩
  have hcont : ContinuousOn (fun ζ ↦ qq a b (c + 1) (cp ζ)) (sphere (cz (lastHole a b c)) 1) :=
    continuousOn_qq.comp continuous_cp.continuousOn fun ζ hζ ↦ by
      have h₁ : ‖ζ - cz (lastHole a b c)‖ = 1 := by simpa [dist_eq_norm] using hζ
      exact ok_near' h₁.ge (by linarith)
  have hconn : IsPreconnected (lastCuff a b c) :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) _ _).image _ hcont
  refine ⟨y₀, lastCuff_subset_bd hmem, Subset.antisymm ?_ ?_⟩
  · have hZ : IsPreconnected (connectedComponentIn (bd (SurfaceModel a b (c + 1))) y₀) :=
      isPreconnected_connectedComponentIn
    have hsub := connectedComponentIn_subset (bd (SurfaceModel a b (c + 1))) y₀
    have hcl : IsClosed (bd (SurfaceModel a b (c + 1)) \ lastCuff a b c) := by
      have : bd (SurfaceModel a b (c + 1)) \ lastCuff a b c = plug a b c ⁻¹' bd
        (SurfaceModel a b c) := by
        rw [bd_plug (a := a) (b := b) (c := c), preimage_image_eq _ (plug_injective a b c)]
      rw [this]
      exact (isClosed_bd _).preimage (continuous_plug a b c)
    intro z hz
    by_contra hzC
    obtain ⟨w, -, hw₁, hw₂⟩ := isPreconnected_closed_iff.1 hZ _ _ isClosed_lastCuff hcl
      (fun u hu ↦ by
        by_cases h : u ∈ lastCuff a b c
        · exact Or.inl h
        · exact Or.inr ⟨hsub hu, h⟩)
      ⟨y₀, mem_connectedComponentIn (lastCuff_subset_bd hmem), hmem⟩ ⟨z, hz, hsub hz, hzC⟩
    exact hw₂.2 hw₁
  · exact hconn.subset_connectedComponentIn hmem lastCuff_subset_bd

theorem bd_model_zero : bd (SurfaceModel a b 0) = ∅ := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b 0
  have hn := ncard_cuffs hf
  have hfin := (cuff_statement _ (isSurface_model a b 0).1).2.1
  have he : cuffs (SurfaceModel a b 0) = ∅ := (ncard_eq_zero hfin).1 hn
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have : connectedComponentIn (bd (SurfaceModel a b 0)) x ∈ cuffs (SurfaceModel a b 0)
    := ⟨x, hx, rfl⟩
  rw [he] at this
  exact this

/-- `Σ(a, b, 0)` is a capping of every `Σ(a, b, c)`. -/
theorem nonempty_capped_model (a b c : ℕ) : Nonempty (IsCappedSurface (SurfaceModel a b c)
  (SurfaceModel a b 0)) := by
  induction c with
  | zero =>
    have he : cuffs (SurfaceModel a b 0) = ∅ := by
      refine eq_empty_of_forall_notMem ?_
      rintro _ ⟨x, hx, -⟩
      rw [bd_model_zero] at hx
      exact hx
    exact ⟨{ isSurface := (isSurface_model a b 0).1
             connected := (isSurface_model a b 0).2
             bd_empty := bd_model_zero
             emb := id
             isEmbedding := IsEmbedding.id
             cuffDisc := fun _ ↦ ∅
             cuffDisc_closedDisc := fun Θ hΘ ↦ by simp [he] at hΘ
             cuffDisc_bd := fun Θ hΘ ↦ by simp [he] at hΘ
             cuffDisc_disjoint := fun Θ hΘ ↦ by simp [he] at hΘ
             compl_eq := by simp [he] }⟩
  | succ c ih =>
    obtain ⟨cap⟩ := ih
    have : T2Space (SurfaceModel a b c) := (presents_ew a b c).1
    have : T2Space (SurfaceModel a b (c + 1)) := (presents_ew a b (c + 1)).1
    have hd := fillDisc_facts (a := a) (b := b) (c := c)
    exact nonempty_capped_of_paste (isSurface_model a b (c + 1)).1 (isSurface_model a b c).1
      lastCuff_mem_cuffs
      isClosedEmbedding_plug hd.1 range_union_fillDisc range_inter_fillDisc
      (by rw [hd.2, image_lastCuff]) bd_plug cap

/-- A capping of `Σ(a, b, c)` is `Σ(a, b, 0)`. -/
theorem capModel : CapModelStatement := by
  intro a b c Shat _ cap
  obtain ⟨cap'⟩ := nonempty_capped_model a b c
  have : T2Space (SurfaceModel a b c) := (presents_ew a b c).1
  exact cap.nonempty_homeomorph (isSurface_model a b c).1 cap'

/-- An orientation moves back along an embedding. -/
theorem isOrientable_of_embedding {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {ι : X
  → X'}
    (hι : IsEmbedding ι) (hO : IsOrientableSurface X') : IsOrientableSurface X := by
  obtain ⟨ω⟩ := hO
  have hmem : ∀ {Δ : Set X} {a : X}, IsClosedDisc Δ → a ∈ discBd Δ → ι a ∈ discBd (ι '' Δ)
    := fun {Δ a} hΔ ha ↦
    (isClosedDisc_image hΔ hι).2 ▸ mem_image_of_mem _ ha
  refine ⟨⟨fun Δ a b c ↦ ω.pos (ι '' Δ) (ι a) (ι b) (ι c), fun Δ hΔ ↦ ?_,
    fun Δ₁ Δ₂ h₁ h₂ hsub a b c ha hb hc hab hbc hac ↦ ?_⟩⟩
  · have hd := isClosedDisc_image hΔ hι
    obtain ⟨φ, hc, hi, hr, hp⟩ := ω.isDirection (ι '' Δ) hd.1
    have hl : ∀ z, ∃ x, x ∈ discBd Δ ∧ ι x = φ z := fun z ↦ by
      have : φ z ∈ ι '' discBd Δ := hd.2 ▸ hr ▸ mem_range_self z
      exact this
    choose g hg hg' using hl
    have heq : ι ∘ g = φ := funext hg'
    refine ⟨g, hι.continuous_iff.2 (heq ▸ hc), fun z w h ↦ hi (by rw [← hg', ← hg', h]), ?_,
      fun a b c hab hbc hac ↦ ?_⟩
    · apply Subset.antisymm
      · rintro _ ⟨z, rfl⟩
        exact hg z
      · intro x hx
        have : ι x ∈ range φ := hr ▸ hd.2 ▸ mem_image_of_mem _ hx
        obtain ⟨z, hz⟩ := this
        exact ⟨z, hι.injective ((hg' z).trans hz)⟩
    · simp only [hg']
      exact hp a b c hab hbc hac
  · exact ω.agree _ _ (isClosedDisc_image h₁ hι).1 (isClosedDisc_image h₂ hι).1
      (image_mono hsub) _ _ _
      ⟨hmem h₁ ha.1, hmem h₂ ha.2⟩ ⟨hmem h₁ hb.1, hmem h₂ hb.2⟩ ⟨hmem h₁ hc.1, hmem h₂ hc.2⟩
      (fun e ↦ hab (hι.injective e)) (fun e ↦ hbc (hι.injective e)) (fun e ↦ hac (hι.injective e))

theorem modelOrientation : ModelOrientationStatement := fun _ _ _ ↦
  isOrientable_of_embedding isClosedEmbedding_plug.isEmbedding

end GraphMinor.GM19
