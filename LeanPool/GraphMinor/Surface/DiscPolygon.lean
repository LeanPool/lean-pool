/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Lunes
public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# A polygon and its lunes in a closed disc

We carry the polygon and the lunes of `exists_polygon_lunes` to a closed disc of a surface. First a
homeomorphism of the boundary of the disc with
the circle extends to a chart of the disc (`exists_chart_extending`). Then the sets of the unit disc
go over by that chart (`exists_polygon_in_disc`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

variable {S : Type} [TopologicalSpace S]

theorem eC_eq_cis' (t : ℝ) : eC t = cis' t := by simp [eC, cis', Circle.coe_exp]

theorem Circle_exp_add_int (t : ℝ) (m : ℤ) : Circle.exp (t + 2 * Real.pi * m) = Circle.exp t :=
  Circle.ext (eC_add_int t m)

/-- A parametrization of the boundary of a closed disc extends to a chart of the disc. -/
theorem exists_chart_extending {D : Set S} (hD : IsClosedDisc D) (φ : Circle ≃ₜ discBd D) :
    ∃ h g, IsChart D h g ∧ ∀ t, g (eC t) = (φ (Circle.exp t)).1 := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hpi := Real.pi_pos
  have hm : 0 < 1 := one_pos
  let β : ℝ → ℂ := fun x => h (φ (Circle.exp (2 * Real.pi * x))).1
  have hφ : ∀ w, (φ w).1 ∈ D := fun w => discBd_subset _ (φ w).2
  have hfr : ∀ t : ℝ, ∃ x ∈ Ico (0 : ℝ) 1, Circle.exp t = Circle.exp (2 * Real.pi * x) ∧ eC t
    = cis' (2 * Real.pi * x) := fun t => by
    let u := t / (2 * Real.pi)
    have ht : t = 2 * Real.pi * Int.fract u + 2 * Real.pi * ⌊u⌋ := by
      have : u = Int.fract u + ⌊u⌋ := (Int.fract_add_floor u).symm
      have e : t = 2 * Real.pi * u := by simp only [u]; field_simp
      rw [e, ← mul_add, ← this]
    refine ⟨Int.fract u, ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩, ?_, ?_⟩
    · conv_lhs => rw [ht]
      exact Circle_exp_add_int _ _
    · conv_lhs => rw [ht]
      rw [eC_add_int, eC_eq_cis']
  have hc : ContinuousOn β (Icc 0 (1 : ℕ)) := by
    have hcc : Continuous fun x : ℝ => (φ (Circle.exp (2 * Real.pi * x))).1
      := continuous_subtype_val.comp (φ.continuous.comp (Circle.exp.continuous.comp (by fun_prop)))
    exact (c.hc.comp_continuous hcc fun x => hφ _).continuousOn
  have hi : InjOn β (Ico 0 (1 : ℕ)) := fun x hx y hy he => by
    have h1 : (φ (Circle.exp (2 * Real.pi * x))).1 = (φ (Circle.exp (2 * Real.pi * y))).1 := by
      rw [← c.gh (hφ _), ← c.gh (hφ (Circle.exp (2 * Real.pi * y)))]
      exact congrArg g he
    have h2 := φ.injective (Subtype.ext h1)
    obtain ⟨m, hm'⟩ := Circle.exp_eq_exp.mp h2
    have hxy : x - y = m := by
      have : 2 * Real.pi * (x - y - m) = 0 := by linear_combination hm'
      have h3 := (mul_eq_zero.mp this).resolve_left (by positivity)
      linarith
    have h1' : x < 1 := by simpa using hx.2
    have h2' : y < 1 := by simpa using hy.2
    have hm1 : (m : ℝ) < 1 := by linarith [hy.1]
    have hm2 : (-1 : ℝ) < m := by linarith [hx.1]
    have h3 : m < 1 := by exact_mod_cast hm1
    have h4 : -1 < m := by exact_mod_cast hm2
    have h5 : m = 0 := by omega
    rw [h5, Int.cast_zero] at hxy
    linarith
  have h0 : β 0 = β (1 : ℕ) := by
    have he : Circle.exp (2 * Real.pi * ((1 : ℕ) : ℝ)) = Circle.exp (2 * Real.pi * (0 : ℝ)) := by
      simp
    change h (φ (Circle.exp (2 * Real.pi * 0))) = h (φ (Circle.exp (2 * Real.pi * ↑(1 : ℕ))))
    rw [he]
  have hr : β '' Icc 0 (1 : ℕ) = discBd (closedBall (0 : ℂ) 1) := by
    rw [isClosedDisc_closedBall.2, ← c.bd]
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨_, (φ _).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, Circle.exp t = φ.symm ⟨y, hy⟩ := ⟨_, Circle.exp_arg _⟩
      obtain ⟨x, hx, he, -⟩ := hfr t
      refine ⟨x, ⟨hx.1, by simpa using hx.2.le⟩, ?_⟩
      change h (φ (Circle.exp (2 * Real.pi * x))).1 = h y
      rw [← he, ht, φ.apply_symm_apply]
  obtain ⟨Θ, Θ', hmt, hval⟩ := exists_polygon_map isClosedDisc_closedBall.1 hm hc hi h0 hr
  refine ⟨fun y => Θ' (h y), fun z => g (Θ z), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun t => ?_⟩
  · exact hmt.2.2.2.2.2.comp c.hc c.hm
  · exact c.gc.comp hmt.2.2.2.2.1 hmt.1
  · exact fun y hy => hmt.2.1 (c.hm hy)
  · exact fun z hz => c.gm (hmt.1 hz)
  · intro y hy
    change g (Θ (Θ' (h y))) = y
    rw [hmt.2.2.2.1 (c.hm hy), c.gh hy]
  · intro z hz
    change Θ' (h (g (Θ z))) = z
    rw [c.hg (hmt.1 hz), hmt.2.2.1 hz]
  · have hb := isClosedDisc_closedBall.2
    have : (fun y => Θ' (h y)) '' discBd D = Θ' '' sphere 0 1 := by
      rw [← c.bd, image_image]
    rw [this]
    have hper : ∀ t : ℝ, ∃ x ∈ Icc (0 : ℝ) (1 : ℕ), eC t = per 1 x := fun t => by
      obtain ⟨x, hx, -, he'⟩ := hfr t
      refine ⟨x, ⟨hx.1, by simpa using hx.2.le⟩, ?_⟩
      rw [he', per]
      simp
    have hs : ∀ x ∈ Icc (0 : ℝ) (1 : ℕ), Θ' (β x) = per 1 x ∧ β x ∈ sphere (0 : ℂ) 1 := fun x hx
      => by
      have hb' : per 1 x ∈ closedBall (0 : ℂ) 1 := by simp [norm_per]
      refine ⟨by rw [← hval x hx]; exact hmt.2.2.1 hb', ?_⟩
      rw [← isClosedDisc_closedBall.2, ← hr]
      exact mem_image_of_mem _ hx
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← isClosedDisc_closedBall.2, ← hr] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [(hs x hx).1]
      simp [norm_per]
    · intro hz
      obtain ⟨t, rfl⟩ := exists_eC (show ‖z‖ = 1 by simpa using hz)
      obtain ⟨x, hx, he⟩ := hper t
      exact ⟨β x, (hs x hx).2, by rw [(hs x hx).1, he]⟩
  · obtain ⟨x, hx, he, he'⟩ := hfr t
    have hx' : x ∈ Icc (0 : ℝ) (1 : ℕ) := ⟨hx.1, by simpa using hx.2.le⟩
    have hv := hval x hx'
    have hper : per 1 x = eC t := by
      rw [he', per]
      simp
    change g (Θ (eC t)) = _
    rw [← hper, hv]
    change g (h (φ (Circle.exp (2 * Real.pi * x))).1) = _
    rw [c.gh (hφ _), he]

theorem IsLineWithEnds.image_injOn [T2Space S] {Z : Set ℂ} {a b : ℂ} (hl : IsLineWithEnds Z a b) {g
  : ℂ → S} (hc : ContinuousOn g Z) (hi : InjOn g Z) :
    IsLineWithEnds (g '' Z) (g a) (g b) :=
  hl.image_under_injOn hc hi

/-- **The polygon and the lunes in a closed disc.** Take at least three points on the boundary of a
closed disc, in order. Then the disc splits
into a polygon and one lune for each side, with the properties of `exists_polygon_lunes`. -/
theorem exists_polygon_in_disc [T2Space S] {E : Set S} (hE : IsClosedDisc E)
  (φ : Circle ≃ₜ discBd E) {k : ℕ} (hk : 3 ≤ k) (s : Fin k → ℝ) (hs : StrictMono s)
    (hl : ∀ i, s i < s ⟨0, by omega⟩ + 2 * Real.pi) (nx : Fin k → Fin k) (hnx : ∀ i, (nx i).1 =
      (i.1 + 1) % k) (n : Fin k → S)
    (hn : ∀ i, n i = (φ (Circle.exp (s i))).1) :
    ∃ (P : Set S) (L F : Fin k → Set S), IsClosedDisc P ∧ P ⊆ E ∧ discBd P = ⋃ i, F i ∧ E
      = P ∪ ⋃ i, L i ∧
      (∀ i, IsClosedDisc (L i) ∧ L i ⊆ E ∧ L i ∩ P = F i ∧ F i ⊆ discBd (L i) ∧ IsLineWithEnds
        (F i) (n i) (n (nx i))) ∧
      (∀ i j, i ≠ j → L i ∩ L j ⊆ range n) ∧ ∀ i j, n j ∈ L i ↔ j = i ∨ j = nx i := by
  obtain ⟨h, g, c, hg⟩ := exists_chart_extending hE φ
  obtain ⟨P, L, F, h1, h2, h3, h4, h5, h6, h7⟩ := exists_polygon_lunes hk s hs hl nx hnx
  have hgn : ∀ i, g (eC (s i)) = n i := fun i => by rw [hg, hn]
  have hLs : ∀ i, L i ⊆ closedBall 0 1 := fun i => (h5 i).2.1
  have hFs : ∀ i, F i ⊆ closedBall 0 1 := fun i => by
    rw [← (h5 i).2.2.1]
    exact inter_subset_left.trans (hLs i)
  have hmem : ∀ j, eC (s j) ∈ closedBall (0 : ℂ) 1 := fun j => by simp [norm_eC]
  refine ⟨g '' P, fun i => g '' L i, fun i => g '' F i, (c.disc_g h2 h1).1, c.g_subset h2, ?_, ?_,
    fun i => ⟨(c.disc_g (hLs i) (h5 i).1).1, c.g_subset (hLs i), ?_, ?_, ?_⟩, fun i j hij
      => ?_, fun i j => ?_⟩
  · rw [(c.disc_g h2 h1).2, h3, image_iUnion]
  · rw [← image_iUnion, ← image_union, ← h4, c.g_closedBall]
  · rw [← c.g_inter (hLs i) h2, (h5 i).2.2.1]
  · rw [(c.disc_g (hLs i) (h5 i).1).2]
    exact image_mono (h5 i).2.2.2.1
  · rw [← hgn, ← hgn]
    exact (h5 i).2.2.2.2.image_injOn (c.gc.mono (hFs i)) (c.injOn.mono (hFs i))
  · rw [← c.g_inter (hLs i) (hLs j)]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨m, rfl⟩ := h6 i j hij hz
    exact ⟨m, (hgn m).symm⟩
  · rw [← h7, ← hgn]
    exact c.injOn.mem_image_iff (hLs i) (hmem j)

end GraphMinor.Surface
