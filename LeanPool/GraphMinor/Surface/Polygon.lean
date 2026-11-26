/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Polygons with sides pasted by labels

A word is a list of letters, and a letter is a label with a sign. A family of words `W : ℕ → List
Letter`
stands for a family of round polygons, one for each nonempty word, where a word of length `n` gives
the unit disc
with `n` sides on its boundary. Sides with the same label are pasted, by the parameter `t`: the sign
says if `t`
runs along the side or against it.

`Presents T W f` says that `f` maps the discs onto `T`, and that two points have the same image
exactly when
the pasting relates them. This is a description of `T` by `W`. If `W` and `W'` have a map `θ` of the
discs that
is compatible with the pasting (`Presents.of_map`, `Presents.map`), then they present the same
spaces. So all the
moves on words of the later files need only such a map.

The file also has the polygon lemma `exists_polygon_map`: the unit disc goes to any closed disc of
the plane with
prescribed values on the boundary.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

local notation "𝕀" => unitInterval

universe u

/-- A label with a sign. -/
abbrev Letter := ℕ × Bool

/-- The point at position `x` of the boundary of the round polygon with `m` sides. -/
noncomputable def per (m : ℕ) (x : ℝ) : ℂ := cis' (2 * Real.pi * x / m)

/-- The point with parameter `t` on the side at position `p` with sign `b`. -/
noncomputable def sdPt (n p : ℕ) (b : Bool) (t : ℝ) : ℂ := per n (p + if b then t else 1 - t)

theorem continuous_per (m : ℕ) : Continuous (per m) :=
  continuous_cis'.comp (by fun_prop)

theorem norm_per (m : ℕ) (x : ℝ) : ‖per m x‖ = 1 := norm_cis' _

theorem per_add_self {m : ℕ} (hm : m ≠ 0) (x : ℝ) : per m (x + m) = per m x := by
  have h : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [per, per, show 2 * Real.pi * (x + m) / m = 2 * Real.pi * x / m + 2 * Real.pi by field_simp,
    cis'_period]

/-- The discs of the family `W`. -/
def Dsk (W : ℕ → List Letter) : Set (ℕ × ℂ) := {a | W a.1 ≠ [] ∧ ‖a.2‖ ≤ 1}

/-- One step of pasting: two points with the same parameter on two sides with the same label. -/
def Stp (W : ℕ → List Letter) (a b : ℕ × ℂ) : Prop :=
  ∃ (i j p q k : ℕ) (ε ε' : Bool) (t : ℝ), (W i)[p]? = some (k, ε) ∧ (W j)[q]? = some (k, ε') ∧
    (i, p) ≠ (j, q) ∧ t ∈ Icc (0 : ℝ) 1 ∧ a = (i, sdPt (W i).length p ε t) ∧
    b = (j, sdPt (W j).length q ε' t)

/-- The pasting relation. -/
abbrev PRel (W : ℕ → List Letter) : ℕ × ℂ → ℕ × ℂ → Prop := Relation.EqvGen (Stp W)

/-- `f` describes `T` as the discs of `W` with the pasting. -/
def Presents {T : Type u} [TopologicalSpace T] (W : ℕ → List Letter) (f : ℕ × ℂ → T) : Prop :=
  ContinuousOn f (Dsk W) ∧ f '' Dsk W = univ ∧ ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, f a = f b ↔ PRel W a b

theorem isCompact_Dsk {W : ℕ → List Letter} (hW : {i | W i ≠ []}.Finite) : IsCompact (Dsk W) := by
  have h : Dsk W = ⋃ i ∈ {i | W i ≠ []}, ({i} : Set ℕ) ×ˢ closedBall (0 : ℂ) 1 := by
    ext ⟨i, z⟩
    simp [Dsk]
  rw [h]
  exact hW.isCompact_biUnion fun i _ => isCompact_singleton.prod (isCompact_closedBall _ _)

theorem Stp.mem_Dsk {W : ℕ → List Letter} {a b : ℕ × ℂ} (h : Stp W a b) : a ∈ Dsk W ∧ b ∈ Dsk W
  := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, -, -, rfl, rfl⟩ := h
  refine ⟨⟨fun he => ?_, (norm_per _ _).le⟩, ⟨fun he => ?_, (norm_per _ _).le⟩⟩
  · simp [he] at h1
  · simp [he] at h2

theorem prel_mem_iff {W : ℕ → List Letter} {a b : ℕ × ℂ} (h : PRel W a b) : a ∈ Dsk W ↔ b ∈ Dsk W
  := by
  induction h with
  | rel _ _ h => exact iff_of_true h.mem_Dsk.1 h.mem_Dsk.2
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

/-- The conditions under which a map of discs is compatible with the pasting. -/
structure IsPolyMap (W W' : ℕ → List Letter) (θ : ℕ × ℂ → ℕ × ℂ) : Prop where
  cont : ContinuousOn θ (Dsk W')
  maps : MapsTo θ (Dsk W') (Dsk W)
  surj : Dsk W ⊆ θ '' Dsk W'
  /-- Points with the same image are related. -/
  fib : ∀ a ∈ Dsk W', ∀ b ∈ Dsk W', θ a = θ b → PRel W' a b
  /-- A step below comes from related points above. -/
  lift : ∀ u v, Stp W u v → ∃ a ∈ Dsk W', ∃ b ∈ Dsk W', θ a = u ∧ θ b = v ∧ PRel W' a b
  /-- A step above goes to related points. -/
  push : ∀ a b, Stp W' a b → PRel W (θ a) (θ b)

theorem IsPolyMap.rel_iff {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ} (h : IsPolyMap W W' θ)
    {a b : ℕ × ℂ} (ha : a ∈ Dsk W') (hb : b ∈ Dsk W') : PRel W (θ a) (θ b) ↔ PRel W' a b := by
  constructor
  · intro hr
    have key : ∀ u v, PRel W u v → u ∈ Dsk W →
        ∀ a ∈ Dsk W', ∀ b ∈ Dsk W', θ a = u → θ b = v → PRel W' a b := by
      intro u v huv
      induction huv with
      | rel u v hs =>
        intro _ a ha b hb hau hbv
        obtain ⟨a', ha', b', hb', e1, e2, hr⟩ := h.lift u v hs
        exact .trans _ _ _ (h.fib a ha a' ha' (hau.trans e1.symm))
          (.trans _ _ _ hr (h.fib b' hb' b hb (e2.trans hbv.symm)))
      | refl u =>
        intro _ a ha b hb hau hbv
        exact h.fib a ha b hb (hau.trans hbv.symm)
      | symm u v huv ih =>
        intro hv a ha b hb hav hbu
        exact .symm _ _ (ih ((prel_mem_iff huv).mpr hv) b hb a ha hbu hav)
      | trans u v w huv hvw ih1 ih2 =>
        intro hu a ha b hb hau hbw
        have hv : v ∈ Dsk W := (prel_mem_iff huv).mp hu
        obtain ⟨c, hc, rfl⟩ := h.surj hv
        exact .trans _ _ _ (ih1 hu a ha c hc hau rfl) (ih2 hv c hc b hb rfl hbw)
    exact key _ _ hr (h.maps ha) a ha b hb rfl rfl
  · intro hr
    induction hr with
    | rel _ _ hs => exact h.push _ _ hs
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ (ih hb ha)
    | trans _ c _ h1 _ ih1 ih2 =>
      have hc : c ∈ Dsk W' := (prel_mem_iff h1).mp ha
      exact .trans _ _ _ (ih1 ha hc) (ih2 hc hb)

variable {T : Type u} [TopologicalSpace T]

/-- A presentation by `W` gives a presentation by `W'`, through a map of discs. -/
theorem Presents.of_map {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ} (hθ : IsPolyMap W W' θ)
    {f : ℕ × ℂ → T} (hf : Presents W f) : Presents W' (f ∘ θ) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1.comp hθ.cont hθ.maps, ?_, fun a ha b hb => ?_⟩
  · rw [image_comp, Subset.antisymm hθ.maps.image_subset hθ.surj, h2]
  · rw [Function.comp_apply, Function.comp_apply, h3 _ (hθ.maps ha) _ (hθ.maps hb),
      hθ.rel_iff ha hb]

/-- A presentation by `W'` gives a presentation by `W`, through a map of discs. -/
theorem Presents.map' {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ}
  (hθ : IsPolyMap W W' θ)
    (hW' : {i | W' i ≠ []}.Finite) {f : ℕ × ℂ → T} (hf : Presents W' f) :
    ∃ g : ℕ × ℂ → T, Presents W g ∧ ∀ a ∈ Dsk W', g (θ a) = f a := by
  classical
  obtain ⟨h1, h2, h3⟩ := hf
  have hsec : ∀ u ∈ Dsk W, ∃ a ∈ Dsk W', θ a = u := fun u hu => hθ.surj hu
  choose! σ hσ1 hσ2 using hsec
  have hval : ∀ a ∈ Dsk W', f (σ (θ a)) = f a := fun a ha => by
    have hm := hθ.maps ha
    rw [h3 _ (hσ1 _ hm) _ ha, ← hθ.rel_iff (hσ1 _ hm) ha, hσ2 _ hm]
    exact .refl _
  have hcomp := isCompact_Dsk hW'
  refine ⟨f ∘ σ, ⟨?_, ?_, fun u hu v hv => ?_⟩, hval⟩
  · rw [continuousOn_iff_isClosed]
    intro C hC
    have hcl : IsCompact (Dsk W' ∩ f ⁻¹' C) :=
      hcomp.of_isClosed_subset (h1.preimage_isClosed_of_isClosed hcomp.isClosed hC)
        inter_subset_left
    refine ⟨θ '' (Dsk W' ∩ f ⁻¹' C), (hcl.image_of_continuousOn
      (hθ.cont.mono inter_subset_left)).isClosed, ?_⟩
    ext u
    constructor
    · rintro ⟨hu, huC⟩
      exact ⟨⟨σ u, ⟨hσ1 u huC, hu⟩, hσ2 u huC⟩, huC⟩
    · rintro ⟨⟨a, ⟨ha, hC'⟩, rfl⟩, hu⟩
      refine ⟨?_, hu⟩
      change f (σ (θ a)) ∈ C
      rw [hval a ha]
      exact hC'
  · rw [eq_univ_iff_forall]
    intro y
    obtain ⟨a, ha, rfl⟩ := h2.ge (mem_univ y)
    exact ⟨θ a, hθ.maps ha, hval a ha⟩
  · rw [Function.comp_apply, Function.comp_apply, h3 _ (hσ1 _ hu) _ (hσ1 _ hv),
      ← hθ.rel_iff (hσ1 _ hu) (hσ1 _ hv), hσ2 _ hu, hσ2 _ hv]

/-- A presentation by `W'` gives a presentation by `W`, through a map of discs. -/
theorem Presents.map {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ}
  (hθ : IsPolyMap W W' θ)
    (hW' : {i | W' i ≠ []}.Finite) {f : ℕ × ℂ → T} (hf : Presents W' f) :
    ∃ g : ℕ × ℂ → T, Presents W g :=
  (hf.map' hθ hW').imp fun _ h => h.1

/-- **Polygon lemma.** A closed disc of the plane, with boundary a loop `β` on `[0, m]`, is the
image of the unit
disc by a map with values `β` on the boundary. -/
theorem exists_polygon_map {K : Set ℂ} (hK : IsClosedDisc K) {m : ℕ} (hm : 0 < m) {β : ℝ → ℂ}
    (hc : ContinuousOn β (Icc 0 m)) (hi : InjOn β (Ico 0 m)) (h0 : β 0 = β m)
    (hr : β '' Icc 0 m = discBd K) :
    ∃ Φ Φ' : ℂ → ℂ, BdMatch (closedBall 0 1) K Φ Φ' ∧ ∀ x ∈ Icc (0 : ℝ) m, Φ (per m x) = β x := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  let J := Icc (0 : ℝ) m
  let q : J → Circle := fun x => Circle.exp (2 * Real.pi * x.1 / m)
  have hq : Continuous q := by fun_prop
  have hcoe : ∀ x : J, (q x : ℂ) = per m x.1 := fun x => by
    simp only [q, per, cis', Circle.coe_exp]
  have : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  have hqs : Function.Surjective q := fun w => by
    obtain ⟨t, ht, hw⟩ := exists_circle_angle 1 w
    refine ⟨⟨t * m / (2 * Real.pi), by have := ht.1; positivity, ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [ht.2]
    · simp only [q]
      rw [hw, one_mul]
      congr 1
      field_simp
  have hqeq : ∀ x y : J, q x = q y → x.1 = y.1 ∨ (x.1 = 0 ∧ y.1 = m) ∨ (x.1 = m ∧ y.1 = 0) := by
    intro x y he
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    have h1 : x.1 = y.1 + k * m := by
      field_simp at hk
      nlinarith
    have hx := x.2
    have hy := y.2
    have h2 : (-1 : ℝ) * m ≤ k * m := by nlinarith [hx.1, hy.2]
    have h3 : (k : ℝ) * m ≤ 1 * m := by nlinarith [hx.2, hy.1]
    have h4 : (-1 : ℝ) ≤ k := le_of_mul_le_mul_right h2 hm'
    have h5 : (k : ℝ) ≤ 1 := le_of_mul_le_mul_right h3 hm'
    have h6 : -1 ≤ k := by exact_mod_cast h4
    have h7 : k ≤ 1 := by exact_mod_cast h5
    have h8 : k = -1 ∨ k = 0 ∨ k = 1 := by omega
    rcases h8 with rfl | rfl | rfl
    · right; left
      push_cast at h1
      constructor <;> linarith [hx.1, hy.2]
    · left
      simpa using h1
    · right; right
      push_cast at h1
      constructor <;> linarith [hx.2, hy.1]
  let b : Circle → ℂ := fun w => β (Function.surjInv hqs w).1
  have hbq : ∀ x : J, b (q x) = β x.1 := fun x => by
    have h1 := Function.surjInv_eq hqs (q x)
    rcases hqeq _ _ h1 with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · simp only [b, h2]
    · simp only [b, h2, h3, h0]
    · simp only [b, h2, h3, h0]
  have hbc : Continuous b := by
    rw [(hq.isClosedMap.isQuotientMap hq hqs).continuous_iff]
    have : b ∘ q = fun x : J => β x.1 := funext hbq
    rw [this]
    exact hc.comp_continuous continuous_subtype_val fun x => x.2
  have hbi : Function.Injective b := by
    intro w w' he
    obtain ⟨x, rfl⟩ := hqs w
    obtain ⟨y, rfl⟩ := hqs w'
    rw [hbq, hbq] at he
    have key : ∀ z : J, ∃ z' : J, q z' = q z ∧ z'.1 < m := fun z => by
      by_cases hz : z.1 < m
      · exact ⟨z, rfl, hz⟩
      · have hzm : z.1 = m := le_antisymm z.2.2 (not_lt.mp hz)
        refine ⟨⟨0, le_rfl, hm'.le⟩, ?_, hm'⟩
        simp only [q, hzm]
        rw [show 2 * Real.pi * (m : ℝ) / m = 2 * Real.pi by field_simp, Circle.exp_two_pi]
        simp
    obtain ⟨x', e1, h1⟩ := key x
    obtain ⟨y', e2, h2⟩ := key y
    have e3 : β x'.1 = β y'.1 := by rw [← hbq, ← hbq, e1, e2, hbq, hbq, he]
    have e4 := hi ⟨x'.2.1, h1⟩ ⟨y'.2.1, h2⟩ e3
    rw [← e1, ← e2, Subtype.ext e4]
  have hrange : range b = discBd K := by
    rw [← hr]
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := hqs w
      exact ⟨x.1, x.2, (hbq x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨q ⟨x, hx⟩, hbq _⟩
  have hemb : IsEmbedding b := (hbc.isClosedEmbedding hbi).isEmbedding
  let e : Circle ≃ₜ discBd K := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have he : ∀ w, (e w).1 = b w := fun _ => rfl
  obtain ⟨o, ho⟩ := exists_circle_sphere
  have hG : Nonempty (Circle ≃ₜ discBd K) := ⟨e⟩
  obtain ⟨h₀, k₀, m₀, hv₀⟩ := exists_bdMatch (o.symm.trans e)
  obtain ⟨ψ, χ, mm, hψ⟩ := exists_bdMatch_closedInner ⟨o⟩ hG m₀
  rw [closedInner_sphere, ← eq_closedInner_of_discBd hG hK rfl] at mm
  refine ⟨ψ, χ, mm, fun x hx => ?_⟩
  have h1 : per m x ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (norm_per _ _)
  rw [hψ h1]
  have h2 : (o (q ⟨x, hx⟩)).1 = per m x := by rw [ho, hcoe]
  rw [← h2, hv₀]
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [he, hbq]

end GraphMinor.Surface
