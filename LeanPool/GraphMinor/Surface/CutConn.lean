/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutWords
public import LeanPool.GraphMinor.Surface.CutArc

/-!
# Lifts of an arc on the cuffs of a connected cut surface

Let `S'` arise from `S` by cutting along an arc. The two lifts of the arc lie on cuffs of `S'`. A
word of `S'` has a side for
each cuff (`exists_one_hole`, `exists_two_holes`). We split this side so that the lifts become sides
of the word, and paste
these sides (`glue_word`). The result is a word of `S`. There are two cases: the lifts lie on two
cuffs (`arc_two_holes`) or
on one cuff (`arc_one_hole`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

local notation "𝕀" => unitInterval

/-- Two different points of a turn have different images on the circle. -/
theorem ee_ne {x y : ℝ} (h : x < y) (h' : y < x + 1) : ee x ≠ ee y := by
  intro he
  obtain ⟨m, hm⟩ := ee_eq_iff.mp he
  have h1 : (m : ℝ) < 0 := by linarith
  have h2 : (-1 : ℝ) < m := by linarith
  have h3 : m < 0 := by exact_mod_cast h1
  have h4 : -1 < m := by exact_mod_cast h2
  omega

theorem image_rev {T : Type*} (f : ℝ → T) : (fun u => f (1 - u)) '' Icc 0 1 = f '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, rev_mem hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨1 - u, rev_mem hu, by simp⟩

theorem injOn_rev {T : Type*} {f : ℝ → T} (h : InjOn f (Icc 0 1)) : InjOn (fun u => f (1 - u))
  (Icc 0 1) := by
  intro x hx y hy he
  have := h (rev_mem hx) (rev_mem hy) he
  linarith

theorem ofs_true (u : ℝ) : ofs true u = u := by simp [ofs]

theorem ofs_false (u : ℝ) : ofs false u = 1 - u := by simp [ofs]

/-- A monotone map, or the same map backwards, is increasing. -/
theorem exists_dir {n : ℝ → ℝ} (hc : ContinuousOn n (Icc 0 1)) (h : StrictMonoOn n (Icc 0 1)
  ∨ StrictAntiOn n (Icc 0 1))
    (hi : InjOn (fun u => ee (n u)) (Icc 0 1)) :
    ∃ (σ : Bool) (n' : ℝ → ℝ), ContinuousOn n' (Icc 0 1) ∧ StrictMonoOn n' (Icc 0 1) ∧ (∀ u ∈ Icc
      (0 : ℝ) 1, n' (ofs σ u) = n u) ∧
      InjOn (fun u => ee (n' u)) (Icc 0 1) := by
  rcases h with h | h
  · exact ⟨true, n, hc, h, fun u _ => by rw [ofs_true], hi⟩
  · refine ⟨false, fun u => n (1 - u), hc.comp (by fun_prop) fun u hu => rev_mem hu,
      fun x hx y hy hxy => ?_,
      fun u hu => by simp [ofs_false], injOn_rev hi⟩
    exact h (rev_mem hy) (rev_mem hx) (by linarith)

theorem inj_of_lift {T : Type*} [TopologicalSpace T] {C : Set T} {φ : Circle ≃ₜ C} {m : ℝ
  → ℝ} {ξ : ℝ → T}
    (hm : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m u))).1 = ξ u) (hi : InjOn ξ (Icc 0 1)) : InjOn (fun u
      => ee (m u)) (Icc 0 1) := by
  intro x hx y hy he
  simp only at he
  exact hi hx hy (by rw [← hm x hx, ← hm y hy, he])

section

variable {Y S : Type uu} [TopologicalSpace Y] [TopologicalSpace S] {ψ : Y → S} {F : Set S} {a₀ : ℝ
  → S} {ξ η : ℝ → Y}

/-- After reversing the arc if needed, the lift `ξ` runs forward around its cuff. -/
theorem orient_lift (L : ArcLift ψ F a₀ ξ η) {C : Set Y} (φ : Circle ≃ₜ C) (hξ : ∀ u ∈ Icc
  (0 : ℝ) 1, ξ u ∈ C)
    (hi : InjOn ξ (Icc 0 1)) (hi' : InjOn η (Icc 0 1)) :
    ∃ (a' : ℝ → S) (ξ' η' : ℝ → Y) (m : ℝ → ℝ), ArcLift ψ F a' ξ' η' ∧ ((a' 0 = a₀ 0 ∧ a' 1 = a₀ 1)
      ∨ (a' 0 = a₀ 1 ∧ a' 1 = a₀ 0)) ∧
      ξ' '' Icc 0 1 = ξ '' Icc 0 1 ∧ η' '' Icc 0 1 = η '' Icc 0 1 ∧ InjOn ξ' (Icc 0 1) ∧ InjOn η'
        (Icc 0 1) ∧
      ContinuousOn m (Icc 0 1) ∧ StrictMonoOn m (Icc 0 1) ∧ ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m u))).1
        = ξ' u := by
  obtain ⟨m, h1, h2⟩ := exists_lift φ L.cξ hξ
  rcases lift_mono h1 (inj_of_lift h2 hi) with h3 | h3
  · exact ⟨a₀, ξ, η, m, L, .inl ⟨rfl, rfl⟩, rfl, rfl, hi, hi', h1, h3, h2⟩
  · refine ⟨_, _, _, fun u => m (1 - u), L.rev, .inr ⟨by simp, by simp⟩, image_rev ξ,
      image_rev η, injOn_rev hi, injOn_rev hi',
      h1.comp (by fun_prop) fun u hu => rev_mem hu, fun x hx y hy hxy => h3 (rev_mem hy)
        (rev_mem hx) (by linarith),
      fun u hu => h2 _ (rev_mem hu)⟩

variable [T2Space Y] [T2Space S]

omit [T2Space Y] in
/-- The two lifts of a line, as paths. -/
theorem exists_arcPart {X X' : Set Y} {s t : S} (h : LiftPair ψ F s t X X') (hcψ : Continuous ψ) :
    ∃ (a : ℝ → S) (ξ η : ℝ → Y), ContinuousOn ξ (Icc 0 1) ∧ ContinuousOn η (Icc 0 1) ∧ (∀ u ∈ Icc
      (0 : ℝ) 1, ψ (ξ u) = a u) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ψ (η u) = a u) ∧ a '' Icc 0 1 = F ∧
      (∀ y y', ψ y = ψ y' → y ≠ y' → ψ y ∈ F → ∃ u ∈ Icc (0 : ℝ) 1, (y = ξ u ∧ y' = η u) ∨ (y'
        = ξ u ∧ y = η u)) ∧
      a 0 = s ∧ a 1 = t ∧ ξ '' Icc 0 1 = X ∧ η '' Icc 0 1 = X' ∧ InjOn ξ (Icc 0 1) ∧ InjOn η
        (Icc 0 1) ∧ InjOn a (Icc 0 1) := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨b, hb, hbr, hb0, hb1⟩ := h1.exists_arc
  have hne : Nonempty Y := ⟨x0⟩
  obtain ⟨ψ', hψ'c, hψ'⟩ := exists_inv_of_compactOn h2.isCompact hcψ.continuousOn h6.injOn
  have him : ψ '' X' = F := h6.image_eq
  have hξ : ContinuousOn (extI b) (Icc 0 1) := (continuous_extI hb.1).continuousOn
  have hξX : ∀ u ∈ Icc (0 : ℝ) 1, extI b u ∈ X := fun u hu => by
    rw [← hbr, extI_of_mem b hu]
    exact ⟨_, rfl⟩
  have hc1 : ContinuousOn (fun u => ψ (extI b u)) (Icc 0 1) := hcψ.comp_continuousOn hξ
  have hc2 : ContinuousOn (fun u => ψ' (ψ (extI b u))) (Icc 0 1) :=
    hψ'c.comp hc1 fun u hu => by
      rw [him]
      exact h5.mapsTo (hξX u hu)
  have hηX : ∀ u ∈ Icc (0 : ℝ) 1, ψ' (ψ (extI b u)) ∈ X' ∧ ψ (ψ' (ψ (extI b u))) = ψ (extI b u)
    := fun u hu => by
    obtain ⟨y, hy, he⟩ := h6.surjOn (h5.mapsTo (hξX u hu))
    rw [← he, hψ' hy]
    exact ⟨hy, rfl⟩
  have hzero : extI b 0 = x0 := by
    rw [extI_of_mem b (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)]
    exact hb0
  have hone : extI b 1 = x1 := by
    rw [extI_of_mem b (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)]
    exact hb1
  have himξ : extI b '' Icc 0 1 = X := by rw [image_extI, hbr]
  have hinjξ := extI_injOn hb.2
  refine ⟨fun u => ψ (extI b u), extI b, fun u => ψ' (ψ (extI b u)), hξ, hc2, fun u _ => rfl,
    fun u hu => (hηX u hu).2, ?_, ?_,
    by simp only [hzero, h7], by simp only [hone, h9], himξ, ?_, hinjξ, ?_, ?_⟩
  · rw [← h5.image_eq, ← himξ, image_image]
  · intro y y' he hne' hy
    have m1 : y ∈ X ∪ X' := by
      rw [h4]
      exact hy
    have m2 : y' ∈ X ∪ X' := by
      rw [h4]
      change ψ y' ∈ F
      rw [← he]
      exact hy
    have key : ∀ z ∈ X, ∀ z' ∈ X', ψ z = ψ z' → ∃ u ∈ Icc (0 : ℝ) 1, z = extI b u ∧ z' = ψ' (ψ
      (extI b u)) := by
      intro z hz z' hz' he'
      obtain ⟨u, hu, rfl⟩ := himξ.symm.subset hz
      exact ⟨u, hu, rfl, by rw [he', hψ' hz']⟩
    rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2
    · exact absurd (h5.injOn m1 m2 he) hne'
    · obtain ⟨u, hu, h11, h12⟩ := key y m1 y' m2 he
      exact ⟨u, hu, .inl ⟨h11, h12⟩⟩
    · obtain ⟨u, hu, h11, h12⟩ := key y' m2 y m1 he.symm
      exact ⟨u, hu, .inr ⟨h11, h12⟩⟩
    · exact absurd (h6.injOn m1 m2 he) hne'
  · ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hηX u hu).1
    · intro hz
      obtain ⟨y, hy, he⟩ := h5.surjOn (h6.mapsTo hz)
      obtain ⟨u, hu, rfl⟩ := himξ.symm.subset hy
      refine ⟨u, hu, ?_⟩
      change ψ' (ψ (extI b u)) = z
      rw [he, hψ' hz]
  · intro u hu v hv he
    have h11 : ψ (extI b u) = ψ (extI b v) := by
      rw [← (hηX u hu).2, ← (hηX v hv).2]
      exact congrArg ψ he
    exact hinjξ hu hv (h5.injOn (hξX u hu) (hξX v hv) h11)
  · intro u hu v hv he
    exact hinjξ hu hv (h5.injOn (hξX u hu) (hξX v hv) he)

omit [T2Space Y] in
/-- The two lifts of an arc, as paths. -/
theorem exists_arcLift {X X' : Set Y} {s t : S} (h : LiftPair ψ F s t X X') (hψ : IsCutting ψ F) :
    ∃ (a : ℝ → S) (ξ η : ℝ → Y), ArcLift ψ F a ξ η ∧ a 0 = s ∧ a 1 = t ∧ ξ '' Icc 0 1 = X
      ∧ η '' Icc 0 1 = X' ∧
      InjOn ξ (Icc 0 1) ∧ InjOn η (Icc 0 1) := by
  obtain ⟨a, ξ, η, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := exists_arcPart h hψ.1
  refine ⟨a, ξ, η, ⟨h1, h2, h3, h4, h5, fun y y' he hne => ?_⟩, h7, h8, h9, h10, h11, h12⟩
  by_cases hy : ψ y ∈ F
  · exact h6 y y' he hne hy
  · exact absurd (hψ.2.2.1 hy (show ψ y' ∈ Fᶜ from he ▸ hy) he) hne

end

theorem cnt_rW_zero {a b c k : ℕ} {L : List ℕ} (h1 : 2 * a + b ≤ k) (h2 : k ≠ 2 * a + b + 2 * c)
    (h3 : ∀ m ∈ L, k ≠ 2 * a + b + 2 * m ∧ k ≠ 2 * a + b + 2 * m + 1) : cnt (rW a b c L) k = 0 :=
  noLab_iff_cnt.mp (noLab_rW h1 h2 h3)

/-- Counts labels in an explicit word whose tail has known counts. -/
local macro "ct" : tactic =>
  `(tactic| ((try simp only [hB, holB, List.cons_append, List.nil_append, List.append_assoc,
    cnt_append, cnt_cons, cnt_nil, tL, rL, frL, linv, Prod.fst, *]); (try split_ifs) <;> omega))

section

variable {Y S : Type uu} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] {ψ : Y
  → S} {F : Set S} {a₀ : ℝ → S} {ξ η : ℝ → Y}
  {a b c i j : ℕ} {L : List ℕ}

/-- The lifts lie on two cuffs. -/
theorem arc_two_aux (hS : IsSurface Y) (L₀ : ArcLift ψ F a₀ ξ η) (hψc : Continuous ψ)
  (hsurj : Surjective ψ) {C C' : Set Y}
    (hC : IsCuff C) (hC' : IsCuff C') (hcl : IsClosed C) (hcl' : IsClosed C') (hd : Disjoint C C')
      (φ : Circle ≃ₜ C) (φ' : Circle ≃ₜ C')
    (hij : i ≠ j) (hi : i < c) (hj : j < c) (hL : ∀ m ∈ L, m < c ∧ m ≠ i ∧ m ≠ j) {g₀ : ℕ × ℂ → Y}
    (hg : Presents (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀)
    (h1 : SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀ (rL a b i).1 fun u => (φ (ee u)).1)
    (h2 : SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀ (rL a b j).1 fun u => (φ'
      (ee u)).1)
    {m : ℝ → ℝ} (hmc : ContinuousOn m (Icc 0 1)) (hmm : StrictMonoOn m (Icc 0 1)) (hmξ : ∀ u ∈ Icc
      (0 : ℝ) 1, (φ (ee (m u))).1 = ξ u)
    (hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C') (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1)) :
    ∃ (σ : Bool) (g : ℕ × ℂ → Y), Presents (sW (blkA a b c i j σ ++ rW a b c L)) (ψ ∘ g) ∧
      SideVal (sW (blkA a b c i j σ ++ rW a b c L)) (ψ ∘ g) (rL a b i).1 a₀ := by
  obtain ⟨n, n1, n2⟩ := exists_lift φ' L₀.cη hη
  obtain ⟨σ, n', c', s', h3, h4⟩ := exists_dir n1 (lift_mono n1 (inj_of_lift n2 hiη))
    (inj_of_lift n2 hiη)
  have hlt := lift_lt_add_one hmc (inj_of_lift hmξ hiξ)
  have hlt' := lift_lt_add_one c' h4
  have c1 : cnt (rW a b c L) (2 * a + b + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c2 : cnt (rW a b c L) (2 * a + b + 2 * j + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c3 : cnt (rW a b c L) (2 * a + b + 2 * c + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c4 : cnt (rW a b c L) (2 * a + b + 2 * c + 1 + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have e0 : hB a b j ++ (hB a b i ++ rW a b c L) = (hB a b j ++ [tL a b i]) ++
    ((rL a b i).1, true) :: (linv (tL a b i) :: rW a b c L) := by
    simp [hB, holB, rL]
  rw [e0] at hg h1 h2
  obtain ⟨g₁, p1, p2, -, p3⟩ := exists_pieces2 hS hC hcl'.isOpen_compl
    (subset_compl_iff_disjoint_right.mpr hd) φ (q := frL a b c)
    (by simp [rL, frL]; omega) (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) hg h1 hmc
      (continuousOn_lin _ _) hmm (strictMonoOn_lin hlt)
    (lin_zero _ _).symm (lin_one _ _)
  have p4 := p3 (rL a b j).1 (by simp [rL]; omega) (by simp [rL, frL]; omega) _ h2 fun u _ h => h
    (φ' _).2
  have e1 : (hB a b j ++ [tL a b i]) ++ ((rL a b i).1, true) :: (frL a b c, true) :: (linv
    (tL a b i) :: rW a b c L) =
      [tL a b j] ++ ((rL a b j).1, true) :: (linv (tL a b j) :: tL a b i :: rL a b i ::
        (frL a b c, true) :: linv (tL a b i) :: rW a b c L) := by
    simp [hB, holB, rL]
  rw [e1] at p1 p2 p4
  obtain ⟨g₂, p5, p6, -, p7⟩ := exists_pieces2 hS hC' hcl.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd) φ' (q := frL a b c + 1)
    (by simp [rL, frL]; omega) (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) p1 p4 c'
      (continuousOn_lin _ _) s' (strictMonoOn_lin hlt')
    (lin_zero _ _).symm (lin_one _ _)
  have p8 := p7 (rL a b i).1 (by simp [rL]; omega) (by simp [rL, frL]; omega) _ p2 fun u _ h => h
    (φ _).2
  obtain ⟨h5, h6⟩ := glue_word (p₁ := 5) L₀ hψc hsurj (A := [tL a b j]) (q := (rL a b j).1) (p :=
    (rL a b i).1) (σ := σ) rfl (by simp)
    (by ct) (by ct) p5 (p8.congr hmξ) (ζ := fun u => (φ' (ee (n' u))).1) p6
    (fun u hu => by simp only [h3 u hu]; exact n2 u hu)
  exact ⟨σ, g₂, h5, h6⟩

/-- The lifts lie on one cuff. -/
theorem arc_one_aux (hS : IsSurface Y) (L₀ : ArcLift ψ F a₀ ξ η) (hψc : Continuous ψ)
  (hsurj : Surjective ψ) {C : Set Y}
    (hC : IsCuff C) (φ : Circle ≃ₜ C) (hi : i < c) (hL : ∀ m ∈ L, m < c ∧ m ≠ i) {g₀ : ℕ × ℂ → Y}
    (hg : Presents (sW (hB a b i ++ rW a b c L)) g₀)
    (h1 : SideVal (sW (hB a b i ++ rW a b c L)) g₀ (rL a b i).1 fun u => (φ (ee u)).1)
    {m : ℝ → ℝ} (hmc : ContinuousOn m (Icc 0 1)) (hmm : StrictMonoOn m (Icc 0 1)) (hmξ : ∀ u ∈ Icc
      (0 : ℝ) 1, (φ (ee (m u))).1 = ξ u)
    (hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C) (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hdj : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξ u ≠ η v) :
    ∃ (σ : Bool) (g : ℕ × ℂ → Y), Presents (sW (blkB a b c i σ ++ rW a b c L)) (ψ ∘ g) ∧
      SideVal (sW (blkB a b c i σ ++ rW a b c L)) (ψ ∘ g) (rL a b i).1 a₀ ∧
      ∃ p q : ℝ, p < q ∧ (φ (ee p)).1 = ξ 1 ∧ (φ (ee q)).1 = η (ofs σ 0) ∧
        ∀ v ∈ Ioo p q, (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee v)).1 ≠ ξ u ∧ (φ (ee v)).1 ≠ η u) := by
  obtain ⟨n, n1, n2⟩ := exists_lift φ L₀.cη hη
  obtain ⟨σ, n', c', s', h3, h4⟩ := exists_dir n1 (lift_mono n1 (inj_of_lift n2 hiη))
    (inj_of_lift n2 hiη)
  have hlt := lift_lt_add_one hmc (inj_of_lift hmξ hiξ)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hn' : ∀ v ∈ Icc (0 : ℝ) 1, (φ (ee (n' v))).1 = η (ofs σ v) := fun v hv => by
    rw [← n2 _ (ofs_mem hv), ← h3 _ (ofs_mem hv), ofs_ofs]
  obtain ⟨k, hk1, hk2⟩ := exists_shift hmc c'
    fun u hu v hv he => hdj u hu _ (ofs_mem hv) (by rw [← hmξ u hu, he, hn' v hv])
  have c1 : cnt (rW a b c L) (2 * a + b + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c3 : cnt (rW a b c L) (2 * a + b + 2 * c + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c4 : cnt (rW a b c L) (2 * a + b + 2 * c + 1 + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c5 : cnt (rW a b c L) (2 * a + b + 2 * c + 1 + 2) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have e0 : hB a b i ++ rW a b c L = [tL a b i] ++ ((rL a b i).1, true) :: (linv
    (tL a b i) :: rW a b c L) := by
    simp [hB, holB, rL]
  rw [e0] at hg h1
  have hcm2 : ContinuousOn (fun u => n' u + (k : ℝ)) (Icc 0 1) := c'.add continuousOn_const
  have hsm2 : StrictMonoOn (fun u => n' u + (k : ℝ)) (Icc 0 1) := fun x hx y hy hxy => by
    have := s' hx hy hxy
    simp only
    linarith
  have hn2 : ∀ v ∈ Icc (0 : ℝ) 1, (φ (ee (n' v + k))).1 = η (ofs σ v) := fun v hv => by
    rw [ee_add_int, hn' v hv]
  obtain ⟨g₁, p1, p2, p3, p4, p5⟩ := exists_pieces4 (U := univ) hS hC isOpen_univ (subset_univ _) φ
    (q₁ := frL a b c) (q₂ := frL a b c + 1)
    (q₃ := frL a b c + 2) (by simp [rL, frL]; omega) (by simp [rL, frL]; omega)
      (by simp [rL, frL]; omega) (by omega) (by omega) (by omega)
    (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct))
      (noLab_iff_cnt.mpr (by ct)) hg h1
    hmc (continuousOn_lin _ _) hcm2 (continuousOn_lin _ _) hmm (strictMonoOn_lin hk1) hsm2
      (strictMonoOn_lin hk2)
    (lin_zero _ _).symm (lin_one _ _) (lin_zero _ _).symm (lin_one _ _)
  obtain ⟨h5, h6⟩ := glue_word (p₁ := 1) L₀ hψc hsurj (A := [tL a b i, rL a b i,
    (frL a b c, true)]) (q := frL a b c + 1) (p := (rL a b i).1)
    (B := (frL a b c + 2, true) :: linv (tL a b i) :: rW a b c L) (σ := σ) rfl (by simp)
    (by ct) (by ct) p1 (p2.congr hmξ) p4
    (fun u hu => by simp only [hn2 _ (ofs_mem hu), ofs_ofs])
  refine ⟨σ, g₁, h5, h6, m 1, n' 0 + k, hk1, hmξ 1 h1', hn2 0 h0, fun v hv u hu => ⟨fun he => ?_,
    fun he => ?_⟩⟩
  · have h7 : (φ (ee v)) = φ (ee (m u)) := Subtype.ext (he.trans (hmξ u hu).symm)
    have h8 := φ.injective h7
    have h9 := hmm.monotoneOn hu h1' hu.2
    have h10 := hmm.monotoneOn h0 hu hu.1
    have h11 := s'.monotoneOn h0 h1' zero_le_one
    exact ee_ne (x := m u) (y := v) (by linarith [hv.1]) (by linarith [hv.2]) h8.symm
  · have h7 : (φ (ee v)) = φ (ee (n' (ofs σ u) + k)) := Subtype.ext (by rw [he, hn2 _
    (ofs_mem hu), ofs_ofs])
    have h8 := φ.injective h7
    have hm' : ofs σ u ∈ Icc (0 : ℝ) 1 := ofs_mem hu
    have h9 := s'.monotoneOn hm' h1' hm'.2
    have h10 := s'.monotoneOn h0 hm' hm'.1
    have h11 := hmm.monotoneOn h0 h1' zero_le_one
    exact ee_ne (x := v) (y := n' (ofs σ u) + k) (by linarith [hv.2]) (by linarith [hv.1]) h8

end

end GraphMinor.Surface
