/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutTwoArc

/-!
# Cutting along an `I`-arc

We prove `CutIArcStatement` (`cutIArc`). The surface `S'` comes from `exists_cut_arc`. We classify
its components by
`classification`, and write `S` as a word of `S'` with the two lifts of the arc pasted. The normal
form of this word shows
which surface `S` is. This is the classical cut and paste proof of the classification theorem, as in
Massey, *Algebraic
Topology: an Introduction*, Chapter 1, Section 7.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u

/-! ### The closed disc -/

/-- The unit disc with one side. -/
noncomputable def discMap : ℕ × ℂ → Metric.closedBall (0 : ℂ) 1 := fun a =>
  if h : ‖a.2‖ ≤ 1 then ⟨a.2, by simpa using h⟩ else ⟨0, by simp⟩

theorem prel_one {a b : ℕ × ℂ} {k : ℕ} {e : Bool} (h : PRel (sW [(k, e)]) a b) : a = b := by
  induction h with
  | rel x y hs =>
    exfalso
    obtain ⟨i, j, p, q, c, ε, ε', t, h1, h2, h3, -⟩ := hs
    obtain ⟨rfl, h4⟩ := sW_get h1
    obtain ⟨rfl, h5⟩ := sW_get h2
    have hp : p = 0 := by
      by_contra hne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      simp at h4
    have hq : q = 0 := by
      by_contra hne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      simp at h5
    exact h3 (by rw [hp, hq])
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

theorem presents_disc (k : ℕ) (e : Bool) : Presents (sW [(k, e)]) discMap := by
  have hD : ∀ a, a ∈ Dsk (sW [(k, e)]) ↔ a.1 = 0 ∧ ‖a.2‖ ≤ 1 := fun a => by
    constructor
    · intro h
      have := mem_Dsk_sW h
      exact ⟨this.1, this.2.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h1, sW_zero]
      simp
  refine ⟨?_, ?_, ?_⟩
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    refine Continuous.subtype_mk (f := fun a : Dsk (sW [(k, e)]) => a.1.2) (by fun_prop) (fun a
      => by simpa using ((hD _).mp a.2).2) |>.congr ?_
    rintro ⟨a, ha⟩
    simp [discMap, ((hD _).mp ha).2, domRestrict_apply]
  · refine eq_univ_of_forall fun z => ?_
    have hz : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    exact ⟨(0, z.1), (hD _).mpr ⟨rfl, hz⟩, by simp [discMap, hz]⟩
  · intro a ha b hb
    refine ⟨fun he => ?_, fun hp => by rw [prel_one hp]⟩
    obtain ⟨h1, h2⟩ := (hD _).mp ha
    obtain ⟨h3, h4⟩ := (hD _).mp hb
    simp only [discMap, h2, h4, dite_true, Subtype.mk.injEq] at he
    rw [show a = b from Prod.ext (h1.trans h3.symm) he]
    exact .refl _

/-- The model with one hole is a closed disc. -/
theorem nonempty_disc_homeo : Nonempty (SurfaceModel 0 0 1 ≃ₜ ClosedUnitDisc) := by
  obtain ⟨e⟩ := isClosedDisc_closedBall.1
  have hn : IsNF (holB (0, false) (1, true)) 0 0 1 :=
    ⟨[], [], holB (0, false) (1, true), by simp, .nil, .nil, .cons _ _ (by simp)
      (by simp [DisjL, NoLab]) .nil,
      by simp [DisjL, NoLab], by simp [DisjL, NoLab], by simp [DisjL, NoLab]⟩
  have h1 : WEq.{0} [(1, true)] [((0 : ℕ), true), (0, false), (1, true)] :=
    WEq.fold (0, true) (by simp) (by simp [NoLab])
  have h2 : WEq.{0} [((0 : ℕ), true), (0, false), (1, true)] (holB (0, false) (1, true)) :=
    WEq.rot' [(0, true)] [(0, false), (1, true)] rfl rfl
  have : Nonempty (Metric.closedBall (0 : ℂ) 1) := ⟨⟨0, by simp⟩⟩
  obtain ⟨e'⟩ := homeo_of_nf (presents_disc 1 true) hn (h1.trans h2)
  exact ⟨e'.symm.trans e.symm⟩

/-! ### Simpler surfaces -/

section

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

theorem cutIsSimpler_of_connected [ConnectedSpace Y] {a b c a' b' c' : ℕ}
  (e : Y ≃ₜ SurfaceModel a b c)
    (e' : S ≃ₜ SurfaceModel a' b' c') (h1 : a ≤ a') (h2 : b ≤ b')
    (h3 : 4 * a + 2 * b + c < 4 * a' + 2 * b' + c') : CutIsSimpler Y S := by
  have h4 : spaceComponents Y = {univ} := by
    rw [spaceComponents_eq]
    ext C
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact PreconnectedSpace.connectedComponent_eq_univ x
    · rintro rfl
      obtain ⟨x⟩ : Nonempty Y := inferInstance
      exact ⟨x, PreconnectedSpace.connectedComponent_eq_univ x⟩
  refine ⟨by rw [h4]; simp, fun C hC => ?_⟩
  rw [h4] at hC
  obtain rfl : C = univ := hC
  exact ⟨a, b, c, a', b', c', ⟨(Homeomorph.Set.univ Y).trans e⟩, ⟨e'⟩, h1, h2, h3⟩

theorem cutIsSimpler_of_two {W₁ W₂ : Set Y} (hC : spaceComponents Y = {W₁, W₂}) {a b c a₂ b₂ c₂ a'
  b' c' : ℕ} (e : W₁ ≃ₜ SurfaceModel a b c)
    (e₂ : W₂ ≃ₜ SurfaceModel a₂ b₂ c₂) (e' : S ≃ₜ SurfaceModel a' b' c') (h1 : a ≤ a') (h2 : b ≤ b')
    (h3 : 4 * a + 2 * b + c < 4 * a' + 2 * b' + c') (h1' : a₂ ≤ a') (h2' : b₂ ≤ b')
    (h3' : 4 * a₂ + 2 * b₂ + c₂ < 4 * a' + 2 * b' + c') : CutIsSimpler Y S := by
  refine ⟨by rw [hC]; exact (encard_insert_le _ _).trans (by simp [one_add_one_eq_two]), fun C hC'
    => ?_⟩
  rw [hC] at hC'
  rcases hC' with rfl | rfl
  · exact ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, h1, h2, h3⟩
  · exact ⟨a₂, b₂, c₂, a', b', c', ⟨e₂⟩, ⟨e'⟩, h1', h2', h3'⟩

variable [CompactSpace Y] [T2Space Y] [T2Space S] {ψ : Y → S} {F : Set S} {a₀ : ℝ → S} {ξ η : ℝ → Y}

omit [T2Space Y] in
/-- The rest of the cuff of a lift joins the two ends of the arc in the boundary. -/
theorem same_of_cuff (hψ : IsCutting ψ F) (hF : IsClosed F) (L : ArcLift ψ F a₀ ξ η) {C : Set Y}
  (hCb : C ⊆ bd Y) (φ : Circle ≃ₜ C)
    (hξ : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ C) (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
      (hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∉ C)
    (hu : ψ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1) (h0 : a₀ 0 ∈ bd S) (h1 : a₀ 1 ∈ bd S) :
    connectedComponentIn (bd S) (a₀ 0) = connectedComponentIn (bd S) (a₀ 1) := by
  obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ hξ hiξ hiη
  have hlt := lift_lt_add_one hmc hmm (inj_of_lift hmξ hix)
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hc : ContinuousOn (fun u => (φ (ee (lin (m 1) (m 0 + 1) u))).1) (Icc 0 1) := by
    refine continuous_subtype_val.comp_continuousOn (φ.continuous.comp_continuousOn ?_)
    exact continuous_ee.comp_continuousOn (continuousOn_lin _ _)
  have key := same_cuff_of_curve hψ hF hc (fun u _ => hCb (φ _).2) (fun u hu' hmem => ?_) ?_ ?_
  · simp only [lin_zero, lin_one, ee_add_one] at key
    rw [hmξ 1 m1, L'.hξ 1 m1] at key
    rw [hmξ 0 m0, L'.hξ 0 m0] at key
    rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [← h2, ← h3]
      exact key.symm
    · rw [← h2, ← h3]
      exact key
  · have hv : lin (m 1) (m 0 + 1) u ∈ Ioo (m 1) (m 0 + 1) := lin_mem hlt.le hu' hlt
    have hm' : (φ (ee (lin (m 1) (m 0 + 1) u))).1 ∈ ψ ⁻¹' F := hmem
    rw [hu, ← hxim, ← heim] at hm'
    rcases hm' with ⟨v, hv1, hv2⟩ | ⟨v, hv1, hv2⟩
    · have h7 : φ (ee (m v)) = φ (ee (lin (m 1) (m 0 + 1) u)) := Subtype.ext ((hmξ v hv1).trans hv2)
      have h8 := φ.injective h7
      have h9 := hmm.monotoneOn hv1 m1 hv1.2
      have h10 := hmm.monotoneOn m0 hv1 hv1.1
      exact ee_ne (x := m v) (y := lin (m 1) (m 0 + 1) u) (by linarith [hv.1])
        (by linarith [hv.2]) h8
    · have h7 : η' v ∈ η '' Icc 0 1 := heim ▸ ⟨v, hv1, rfl⟩
      obtain ⟨w, hw, hw'⟩ := h7
      exact hη w hw (by rw [hw', hv2]; exact (φ _).2)
  · simp only [lin_zero]
    rw [hmξ 1 m1, L'.hξ 1 m1]
    rcases ha' with ⟨-, h3⟩ | ⟨-, h3⟩ <;> rw [h3] <;> assumption
  · simp only [lin_one, ee_add_one]
    rw [hmξ 0 m0, L'.hξ 0 m0]
    rcases ha' with ⟨h3, -⟩ | ⟨h3, -⟩ <;> rw [h3] <;> assumption

omit [T2Space Y] in
/-- A part of a cuff that avoids the preimage of `F` joins its ends in the boundary. -/
theorem same_of_gap (hψ : IsCutting ψ F) (hF : IsClosed F) {C : Set Y} (hCb : C ⊆ bd Y)
  (φ : Circle ≃ₜ C) {p q : ℝ} (hpq : p < q)
    (hv : ∀ v ∈ Ioo p q, ψ (φ (ee v)).1 ∉ F) (h0 : ψ (φ (ee p)).1 ∈ bd S) (h1 : ψ (φ
      (ee q)).1 ∈ bd S) :
    connectedComponentIn (bd S) (ψ (φ (ee p)).1) = connectedComponentIn (bd S) (ψ (φ (ee q)).1)
      := by
  have hc : ContinuousOn (fun u => (φ (ee (lin p q u))).1) (Icc 0 1) := by
    refine continuous_subtype_val.comp_continuousOn (φ.continuous.comp_continuousOn ?_)
    exact continuous_ee.comp_continuousOn (continuousOn_lin _ _)
  have key := same_cuff_of_curve (γ := fun u => (φ (ee (lin p q u))).1) hψ hF hc (fun u _ => hCb
    (φ _).2)
    (fun u hu => hv _ (lin_mem hpq.le hu hpq)) (by simpa only [lin_zero] using h0)
      (by simpa only [lin_one] using h1)
  simpa only [lin_zero, lin_one] using key

end

theorem erase_erase_facts (c i j : ℕ) :
    (((List.range' 0 c).erase i).erase j).Nodup ∧ ∀ m ∈ ((List.range' 0 c).erase i).erase j, m < c
      ∧ m ≠ i ∧ m ≠ j := by
  obtain ⟨h1, h2⟩ := erase_facts c i
  refine ⟨h1.erase _, fun m hm => ?_⟩
  obtain ⟨h3, h4⟩ := h1.mem_erase_iff.mp hm
  exact ⟨(h2 m h4).1, (h2 m h4).2, h3⟩

theorem length_erase_erase {c i j : ℕ} (hij : i ≠ j) (hi : i < c) (hj : j < c) :
    (((List.range' 0 c).erase i).erase j).length = c - 2 := by
  have h1 := List.nodup_range' (s := 0) (n := c)
  rw [List.length_erase_of_mem ((h1.mem_erase_iff).mpr ⟨hij.symm,
    List.mem_range'_1.mpr (by omega)⟩), length_erase_range hi]
  omega

/-- **Cutting along an `I`-arc.** The classical cut and paste proof: Massey, *Algebraic Topology: an
Introduction*, Chapter 1,
Section 7. -/
theorem cutIArc : CutIArcStatement.{u} := by
  intro S _ F s t hS hconn hst hF hl
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst hF hl
  have hcY : CompactSpace Y := hY.1
  refine ⟨Y, tY, ψ, hY, hψ, ?_⟩
  have hFc : IsClosed F := hl.isCompact.isClosed
  have hPc := hP
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, b1, b2, h7, h8, h9, h10⟩ := hP
  have hline : ∃ X Y : Set Y, Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' F ∧ IsLine X ∧ IsLine Y ∧ BijOn ψ X F
    ∧ BijOn ψ Y F := by
    obtain ⟨f, -⟩ := l1
    obtain ⟨f', -⟩ := l2
    exact ⟨X, X', hd, hun, ⟨f⟩, ⟨f'⟩, b1, b2⟩
  obtain ⟨a₀, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hPc hψ
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hF ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hF ▸ mem_insert_of_mem _ rfl).2
  have hub : ψ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1 := by rw [himξ, himη, hun]
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ ⟨u, hu, rfl⟩
  have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu => himη ▸ ⟨u, hu, rfl⟩
  have hdcuff := cuff_statement.{u} Y hY
  have hdc : ∀ {C : Set Y}, C ∈ cuffs Y → C ⊆ bd Y := fun {C} hC => by
    obtain ⟨z, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  rcases cut_comps hψ hY pX pX' hun hx hy with hYc | ⟨W₁, W₂, hne, hsc, hX₁, hX₂, hW₁, hW₂, hU,
    hdW, hc₁, hc₂⟩
  · obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{u} Y hY hYc
    have hC : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
    have hC' : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
    have hXC := pX.subset_connectedComponentIn hx hXb
    have hXC' := pX'.subset_connectedComponentIn hy hXb'
    by_cases hCC : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
    · have hη₀ : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ connectedComponentIn (bd Y) (ξ 0) := fun u hu
      => hCC ▸ hXC' (hηm u hu)
      obtain ⟨i, hi, φ, g, hg, hs⟩ := exists_one_hole e hC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_facts c i
      have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu => by
        rw [← himξ, ← hxim]
        exact ⟨u, hu, rfl⟩
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      have hub' : ψ ⁻¹' F = ξ' '' Icc 0 1 ∪ η' '' Icc 0 1 := by rw [hxim, heim, hub]
      obtain ⟨σ, g', hp, -, p, q, hpq, e1, e2, e3⟩ := arc_one_aux hY L' hψ.1 hψ.2.1 hC φ hi hLf hg
        hs hmc hmm hmξ
        (fun u hu => hCC ▸ hXC' (hη' u hu)) hix hie (fun u hu v hv he => Set.disjoint_left.mp hd
          (hξ' u hu) (he ▸ hη' v hv))
      have hn := nf_blkB (a := a) (b := b) (c := c) hi hN hLf σ
      have hlen := length_erase_range hi
      have : Nonempty S := ⟨s⟩
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen, show c - 1 + 2 = c + 1 by omega] at e'
        exact ⟨fun _ => ⟨hYc, a, b, c, ⟨e'⟩, ⟨e⟩⟩, fun _ => .inl (cutIsSimpler_of_connected e e'
          le_rfl le_rfl (by omega)), hline⟩
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen, show c - 1 + 1 = c by omega] at e'
        have h0 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
        have hb1 : ψ (φ (ee p)).1 = a' 1 := by rw [e1, L'.hξ 1 h0]
        have hb2 : ψ (φ (ee q)).1 = a' 0 := by
          rw [e2, ofs_true, L'.hη 0 hex]
        have hends : a' 0 ∈ bd S ∧ a' 1 ∈ bd S := by
          rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3, ha0, ha1]
            <;> exact ⟨by assumption, by assumption⟩
        have key := same_of_gap hψ hFc (hdc hC) φ hpq (fun v hv hF' => by
          have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hF'
          rw [hub'] at hm'
          rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
          · exact (e3 v hv u hu).1 hu'.symm
          · exact (e3 v hv u hu).2 hu'.symm) (hb1 ▸ hends.2) (hb2 ▸ hends.1)
        rw [hb1, hb2] at key
        have same : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t := by
          rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩
          · rw [h2, h3, ha0, ha1] at key
            exact key.symm
          · rw [h2, h3, ha0, ha1] at key
            exact key
        exact ⟨fun h => absurd same h, fun _ => .inl (cutIsSimpler_of_connected e e' (by omega)
          (by omega) (by omega)), hline⟩
    · have hdis := cuffs_disjoint hC hC' hCC
      obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
      have same := same_of_cuff hψ hFc L (hdc hC) φ₀ (fun u hu => hXC (hξm u hu)) hiξ hiη
        (fun u hu hm => Set.disjoint_left.mp hdis hm (hXC' (hηm u hu))) hub (ha0 ▸ hsb) (ha1 ▸ htb)
      rw [ha0, ha1] at same
      obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, -⟩ := arc_two_aux hY L' hψ.1 hψ.2.1 hC hC' (hdcuff.2.2 _
        hC).isCompact.isClosed
        (hdcuff.2.2 _ hC').isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs hs' hmc hmm hmξ
          (fun u hu => hXC' (hη' u hu)) hix hie
      have hn := nf_blkA (a := a) (b := b) (c := c) hij hi hj hN hLf σ
      have hlen := length_erase_erase hij hi hj
      have : Nonempty S := ⟨s⟩
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        exact ⟨fun h => absurd same h, fun _ => .inl (cutIsSimpler_of_connected e e' (by omega)
          (by omega) (by omega)), hline⟩
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        exact ⟨fun h => absurd same h, fun _ => .inl (cutIsSimpler_of_connected e e' (by omega)
          (by omega) (by omega)), hline⟩
  · obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{u} W₁ (isSurface_sub hY hW₁) hc₁
    obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{u} W₂ (isSurface_sub hY hW₂) hc₂
    have hC : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
    have hXC := pX.subset_connectedComponentIn hx hXb
    have hCW : connectedComponentIn (bd Y) (ξ 0) ⊆ W₁ :=
      isPreconnected_connectedComponentIn.subset_isClopen hW₁ ⟨ξ 0, mem_connectedComponentIn
        (hXb hx), hX₁ hx⟩
    obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
    have same := same_of_cuff hψ hFc L (hdc hC) φ₀ (fun u hu => hXC (hξm u hu)) hiξ hiη
      (fun u hu hm => Set.disjoint_left.mp hdW (hCW hm) (hX₂ (hηm u hu))) hub (ha0 ▸ hsb)
        (ha1 ▸ htb)
    rw [ha0, ha1] at same
    obtain ⟨i, j, σ, a', f, hi, hj, -, -, hf, -⟩ := arc_comps_aux hY L hψ.1 hψ.2.1 hW₁ hW₂ hdW hU
      e₁ e₂
      (by rw [himξ]; exact hX₁) (by rw [himη]; exact hX₂) (by rw [himξ]; exact hXb)
        (by rw [himη]; exact hXb') hiξ hiη
    have : Nonempty S := ⟨s⟩
    obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
    obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
    obtain ⟨e'⟩ := homeo_of_two_arc hi hj hN₁ hN₂ hL₁ hL₂ hf
    rw [length_erase_range hi, length_erase_range hj] at e'
    refine ⟨fun h => absurd same h, fun _ => ?_, hline⟩
    obtain ⟨d⟩ := nonempty_disc_homeo
    by_cases h2 : a₂ = 0 ∧ b₂ = 0 ∧ c₂ = 1
    · obtain ⟨rfl, rfl, rfl⟩ := h2
      rw [show 0 + a₁ = a₁ by omega, show 0 + b₁ = b₁ by omega, show 1 - 1 + (c₁ - 1) + 1
        = c₁ by omega] at e'
      exact .inr ⟨W₂, W₁, hne.symm, by rw [hsc, pair_comm], ⟨e₂.trans d⟩, ⟨e₁.trans e'.symm⟩⟩
    by_cases h1 : a₁ = 0 ∧ b₁ = 0 ∧ c₁ = 1
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      rw [show a₂ + 0 = a₂ by omega, show b₂ + 0 = b₂ by omega, show c₂ - 1 + (1 - 1) + 1
        = c₂ by omega] at e'
      exact .inr ⟨W₁, W₂, hne, hsc, ⟨e₁.trans d⟩, ⟨e₂.trans e'.symm⟩⟩
    · refine .inl (cutIsSimpler_of_two hsc e₁ e₂ e' (by omega) (by omega) ?_ (by omega)
      (by omega) ?_)
      · omega
      · omega

end GraphMinor.Surface
