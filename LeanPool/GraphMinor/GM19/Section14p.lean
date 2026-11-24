/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14o

/-!
# Graph Minors XIX, Section 14: from staircases to an outline

We collect the staircases of all the wheels, with the part of the inflation outside the wheels. The
set `σ(x)` is then the set of the
vertices that are sent back to `x`. This is the check that the paper omits in (14.1).
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {Da Db : TangleDatum cap χ} {𝒲a 𝒲b : Set
    (Set Shat)}

/-- One step inside `σ'(x)`, in the cut painting: an edge of `sk(Γ_j)`, or an edge of the rim of a
wheel. -/
def OutStep (fb : ∀ W : ↥𝒲b, WheelFrame Db W.1) (Out : Shat → Shat → Prop) (x u w : Shat) : Prop :=
  Out u x ∧ Out w x ∧ ((∃ a b, cap.emb a = u ∧ cap.emb b = w ∧ Db.P.Γ.skAdj.Adj a b) ∨
    ∃ (W : ↥𝒲b) (q : ℕ), q < (fb W).R.k ∧ ((u = (fb W).R.vert q ∧ w = (fb W).R.vert (q + 1)) ∨ (u =
      (fb W).R.vert (q + 1) ∧ w = (fb W).R.vert q)))

/-- **The staircases of all the wheels**, with the relation `Out` that holds the inflation outside
the wheels. -/
structure StairSystem (fa : ∀ W : ↥𝒲a, WheelFrame Da W.1) (fb : ∀ W : ↥𝒲b, WheelFrame Db W.1)
  (p : ↥𝒲a → ↥𝒲b) (θ : ↥𝒲a → ℕ → ℕ) (Rt : ↥𝒲a → Shat → Shat → Prop)
    (Out : Shat → Shat → Prop) : Prop where
  p_bij : Function.Bijective p
  stair : ∀ W, Stair (fa W) (fb (p W)) (θ W) (Rt W)
  out_fun : ∀ {y x x'}, Out y x → Out y x' → x = x'
  out_hat : ∀ {y x}, Out y x → y ∈ Db.P.Γ.hatV cap ∧ x ∈ Da.P.Γ.hatV cap
  out_off_b : ∀ {y x}, Out y x → ∀ W : ↥𝒲b, y ∉ discInt W.1
  out_off_a : ∀ {y x}, Out y x → ∀ W : ↥𝒲a, x ∉ discInt W.1
  out_rim : ∀ W q, q < (fb (p W)).R.k → Out ((fb (p W)).R.vert q) ((fa W).R.vert (θ W q))
  out_ne : ∀ x ∈ Da.P.Γ.hatV cap, (∀ W : ↥𝒲a, x ∉ discInt W.1) → ∃ y, Out y x
  out_conn : ∀ {y y' x}, Out y x → Out y' x → Relation.ReflTransGen (OutStep fb Out x) y y'

variable {fa : ∀ W : ↥𝒲a, WheelFrame Da W.1} {fb : ∀ W : ↥𝒲b, WheelFrame Db W.1} {p : ↥𝒲a
  → ↥𝒲b} {θ : ↥𝒲a → ℕ → ℕ} {Rt : ↥𝒲a → Shat → Shat → Prop}
  {Out : Shat → Shat → Prop}

/-- The set `σ(x)`: `y` is sent back to `x`. -/
def StairSystem.GBack (fa : ∀ W : ↥𝒲a, WheelFrame Da W.1) (fb : ∀ W : ↥𝒲b, WheelFrame Db W.1)
  (p : ↥𝒲a → ↥𝒲b) (θ : ↥𝒲a → ℕ → ℕ) (Rt : ↥𝒲a → Shat → Shat → Prop)
    (Out : Shat → Shat → Prop) (y x : Shat) : Prop :=
  Out y x ∨ ∃ W, Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) y x

namespace Stair

variable {Wa Wb : Set Shat} {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {t : ℕ → ℕ} {R : Shat
  → Shat → Prop}

/-- A vertex that is sent back lies in the wheel, on both sides. -/
theorem back_mem (h : Stair a b t R) {y x : Shat} (hb : Back a b t R y x) : (y ∈ Wb
  ∧ y ∈ Db.P.Γ.hatV cap) ∧ x ∈ Wa ∧ x ∈ Da.P.Γ.hatV cap := by
  have hlev : ∀ {q l : ℕ}, q < b.R.k → l ≤ b.top q → (b.levV q l ∈ Wb
    ∧ b.levV q l ∈ Db.P.Γ.hatV cap) ∧ a.levV (t q) l ∈ Wa ∧ a.levV (t q) l ∈ Da.P.Γ.hatV cap
      := fun {q l} hq hl ↦
    ⟨⟨b.spoke_mem_W q (b.levV_support hl), b.levV_hatV hl⟩, a.spoke_mem_W _ (a.levV_support
      (h.lev_top hq hl)), a.levV_hatV (h.lev_top hq hl)⟩
  rcases hb with ⟨q, hq, l, hl, rfl, rfl⟩ | hb | hb
  · exact hlev hq hl
  · obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := h.rt_hub hb
    exact ⟨⟨(b.hub_int h₁).1, h₂⟩, (a.hub_int h₃).1, h₄⟩
  · rcases h.onPath_cases hb with ⟨q, hq, l, hl, rfl, rfl⟩ | ⟨q, l, hq, hl, hy, hi, rfl⟩
    · exact hlev hq hl
    · exact ⟨⟨(b.discInt_sec_off_bd q hi).1, (b.path_spec (b.path_reg hy)).hat l hl hy⟩,
        (hlev hq hl).2⟩

end Stair

namespace StairSystem

variable (h : StairSystem fa fb p θ Rt Out)
include h

theorem back_out {W : ↥𝒲a} {y x x' : Shat} (h₁ : Out y x) (h₂ : Stair.Back (fa W) (fb (p W)) (θ W)
  (Rt W) y x') : x = x' := by
  have hst := h.stair W
  have hoff := h.out_off_b h₁ (p W)
  have hlev : ∀ {x₂ : Shat}, Stair.Lev (fa W) (fb (p W)) (θ W) y x₂ → x = x₂ := by
    rintro _ ⟨q, hq, t, ht, rfl, rfl⟩
    have hmem := (fb (p W)).spoke_mem_W q ((fb (p W)).levV_support ht)
    have hbd : (fb (p W)).levV q t ∈ discBd (p W).1 := by
      by_contra hn
      exact hoff ⟨hmem, hn⟩
    have hv := (fb (p W)).spoke_bd q ((fb (p W)).levV_support ht) hbd
    rw [← (fb (p W)).levV_zero] at hv
    obtain rfl : t = 0 := (fb (p W)).levV_inj ht (Nat.zero_le _) hv
    rw [(fa W).levV_zero, h.out_fun h₁ (hv ▸ (fb (p W)).levV_zero q ▸ h.out_rim W q hq)]
  rcases h₂ with h₂ | h₂ | h₂
  · exact hlev h₂
  · exact absurd ((fb (p W)).hub_int (hst.rt_hub h₂).1.1) hoff
  · rcases hst.onPath_cases h₂ with h₃ | ⟨q, t, hq, ht, hy, hi, -⟩
    · exact hlev h₃
    · exact absurd ((fb (p W)).discInt_sec_off_bd q hi) hoff

/-- **The sets `σ(x)` are disjoint.** -/
theorem gback_fun (hdb : 𝒲b.PairwiseDisjoint id) {y x x' : Shat} (h₁ : GBack fa fb p θ Rt Out y x)
  (h₂ : GBack fa fb p θ Rt Out y x') : x = x' := by
  rcases h₁ with h₁ | ⟨W, h₁⟩ <;> rcases h₂ with h₂ | ⟨W', h₂⟩
  · exact h.out_fun h₁ h₂
  · exact h.back_out h₁ h₂
  · exact (h.back_out h₂ h₁).symm
  · have m₁ := ((h.stair W).back_mem h₁).1.1
    have m₂ := ((h.stair W').back_mem h₂).1.1
    obtain rfl : W = W' := by
      by_contra hne
      have hne' : (p W).1 ≠ (p W').1 := fun e ↦ hne (h.p_bij.1 (Subtype.ext e))
      exact disjoint_left.mp (hdb (p W).2 (p W').2 hne') m₁ m₂
    exact (h.stair W).back_fun h₁ h₂

/-- A step of the cut painting inside `σ'(x)` stays inside `σ(x)`. -/
theorem join_outStep {x u w : Shat} (hs : OutStep fb Out x u w) : Db.SkJoined {y | GBack fa fb p θ
  Rt Out y x} u w := by
  obtain ⟨hu, hw, ⟨a, b, ha, hb, hadj⟩ | ⟨W', q, hq, ho⟩⟩ := hs
  · exact Relation.ReflTransGen.single ⟨.inl hu, .inl hw, a, b, ha, hb, hadj⟩
  · obtain ⟨W, rfl⟩ := h.p_bij.2 W'
    have hst := h.stair W
    have key : Out ((fb (p W)).R.vert q) x → Out ((fb (p W)).R.vert (q + 1)) x
      → Db.SkJoined {y | GBack fa fb p θ Rt Out y x} ((fb (p W)).R.vert q) ((fb (p W)).R.vert
        (q + 1)) := by
      intro h₁ h₂
      have h2 := (fa W).R.two
      have h2' := (fb (p W)).R.two
      by_cases hlt : q + 1 < (fb (p W)).R.k
      · have e₁ := h.out_fun h₁ (h.out_rim W q hq)
        have e₂ := h.out_fun h₂ (h.out_rim W (q + 1) hlt)
        have hs : θ W (q + 1) = θ W q := (fa W).R.vert_inj (hst.lt hlt) (hst.lt hq)
          (e₂.symm.trans e₁)
        have hP := (fb (p W)).path_spec (hst.stay_reg q hlt hs)
        have hsub : (fb (p W)).path q 0 ⊆ {y | GBack fa fb p θ Rt Out y x} := fun y hy ↦
          .inr ⟨W, .inr (.inr ⟨q, 0, hlt, hs, Nat.zero_le _, hy,
            (by rw [(fa W).levV_zero]; exact e₁)⟩)⟩
        have hj := TangleDatum.SkJoined.mono hsub (hP.joined 0 (Nat.zero_le _) _ (hP.right 0
          (Nat.zero_le _)))
        rw [(fb (p W)).levV_zero, (fb (p W)).levV_zero] at hj
        exact hj
      · have hq₁ : q = (fb (p W)).R.k - 1 := by omega
        have hk : (fb (p W)).R.vert (q + 1) = (fb (p W)).R.vert 0 := by
          rw [show q + 1 = 0 + (fb (p W)).R.k by omega]
          exact (fb (p W)).R.vert_add_k 0
        rw [hk] at h₂
        have e₁ := h.out_fun h₁ (h.out_rim W q hq)
        have e₂ := h.out_fun h₂ (h.out_rim W 0 (by omega))
        rw [hq₁, hst.last] at e₁
        rw [hst.zero] at e₂
        have := (fa W).R.vert_inj (by omega) (by omega) (e₁.symm.trans e₂)
        omega
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key hu hw
    · exact (key hw hu).symm

theorem join_outs {x y y' : Shat} (h₁ : Out y x) (h₂ : Out y' x) : Db.SkJoined {y | GBack fa fb p θ
  Rt Out y x} y y' := by
  have key : ∀ {u w}, Relation.ReflTransGen (OutStep fb Out x) u w → Db.SkJoined {y | GBack fa fb p
    θ Rt Out y x} u w := by
    intro u w hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact TangleDatum.SkJoined.trans ih (h.join_outStep hs)
  exact key (h.out_conn h₁ h₂)

/-- **The sets `σ(x)` are connected.** -/
theorem gjoin (hda : 𝒲a.PairwiseDisjoint id) {x y y' : Shat} (h₁ : GBack fa fb p θ Rt Out y x)
  (h₂ : GBack fa fb p θ Rt Out y' x) : Db.SkJoined {y | GBack fa fb p θ Rt Out y x} y y' := by
  have hmixed : ∀ {W y y'}, Out y x → Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) y' x
    → Db.SkJoined {y | GBack fa fb p θ Rt Out y x} y y' := by
    intro W y y' ho hb
    have hst := h.stair W
    obtain ⟨-, hxW, hxV⟩ := hst.back_mem hb
    have hbd : x ∈ discBd W.1 := by
      by_contra hn
      exact h.out_off_a ho W ⟨hxW, hn⟩
    obtain ⟨i, hi, rfl⟩ := (fa W).R.exists_vert x ⟨hxV, hbd⟩
    obtain ⟨q, hq, rfl⟩ := hst.surj hi
    have hO := h.out_rim W q hq
    have hL : Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) ((fb (p W)).R.vert q) ((fa W).R.vert
      (θ W q)) :=
      .inl ⟨q, hq, 0, Nat.zero_le _, ((fb (p W)).levV_zero q).symm, ((fa W).levV_zero _).symm⟩
    have hsub : {y | Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) y ((fa W).R.vert
      (θ W q))} ⊆ {y | GBack fa fb p θ Rt Out y ((fa W).R.vert (θ W q))} := fun y hy ↦ .inr ⟨W, hy⟩
    exact TangleDatum.SkJoined.trans (h.join_outs ho hO) (TangleDatum.SkJoined.mono hsub
      (hst.join_back hL hb))
  rcases h₁ with h₁ | ⟨W, h₁⟩ <;> rcases h₂ with h₂ | ⟨W', h₂⟩
  · exact h.join_outs h₁ h₂
  · exact hmixed h₁ h₂
  · exact (hmixed h₂ h₁).symm
  · obtain rfl : W = W' := by
      by_contra hne
      have hne' : W.1 ≠ W'.1 := fun e ↦ hne (Subtype.ext e)
      exact disjoint_left.mp (hda W.2 W'.2 hne') ((h.stair W).back_mem h₁).2.1
        ((h.stair W').back_mem h₂).2.1
    have hsubset : {y | Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) y x} ⊆
        {y | GBack fa fb p θ Rt Out y x} := fun _ hy ↦ .inr ⟨W, hy⟩
    exact TangleDatum.SkJoined.mono hsubset ((h.stair W).join_back h₁ h₂)

end StairSystem

omit [T2Space S] [T2Space Shat] in
theorem reachable_of_skJoined {D : TangleDatum cap χ} {X : Set Shat} {T : Set S}
  (hT : ∀ a, a ∈ D.P.Γ.V → cap.emb a ∈ X → a ∈ T) {x y : Shat} (hj : D.SkJoined X x y) {u w : S}
    (hu : u ∈ T) (hw : w ∈ T) (he : cap.emb u = x) (he' : cap.emb w = y) :
      (D.P.Γ.skAdj.induce T).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  induction hj generalizing w with
  | refl =>
    obtain rfl : w = u := cap.isEmbedding.injective (he'.trans he.symm)
    exact SimpleGraph.Reachable.refl _
  | @tail b c _ hs ih =>
    obtain ⟨h₁, h₂, p, q, hp, hq, hadj⟩ := hs
    obtain rfl : q = w := cap.isEmbedding.injective (hq.trans he'.symm)
    have hpT : p ∈ T := hT p hadj.2.1 (hp ▸ h₁)
    have hr := ih hpT hp
    refine hr.trans (SimpleGraph.Adj.reachable ?_)
    exact hadj

namespace StairSystem

variable (h : StairSystem fa fb p θ Rt Out)
include h

/-- A vertex sent back that is in the image of a sector lies on the boundary of the sector. -/
theorem onSec {W : ↥𝒲a} {q : ℕ} (hq : q < (fb (p W)).R.k) (hmove : q + 1 < (fb (p W)).R.k → θ W
  (q + 1) = θ W q + 1) {x y : Shat} (hV : y ∈ Db.P.Γ.hatV cap)
    (hy : y ∈ ((fb (p W)).sec q).Δ ∪ (fb (p W)).secX q) (hdb : 𝒲b.PairwiseDisjoint id)
      (hb : GBack fa fb p θ Rt Out y x) :
    Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) y x ∧ (y ∈ ((fb (p W)).R.spoke (fb
      (p W)).sp q).support ∨ y ∈ ((fb (p W)).R.spoke (fb (p W)).sp (q + 1)).support ∨ y ∈ (fb
        (p W)).H.U) := by
  have hG : y ∈ Db.rad.G.V := Db.rad.isPreRadial.2.1 hV
  have hst := h.stair W
  set b := fb (p W) with hbdef
  have hmemW : y ∈ (p W).1 := by
    rcases hy with hy | hy
    · exact b.sec_Δ_sub q hy
    · exact b.spoke_mem_W q (support_of_mem_U _ hy.1.2 hG)
  have honbd : y ∉ discInt (b.sec q).Δ → (y ∈ (b.R.spoke b.sp q).support ∨ y ∈ (b.R.spoke b.sp
    (q + 1)).support ∨ y ∈ b.H.U) := by
    intro hn
    rcases hy with hy | hy
    · have hbd : y ∈ discBd (b.sec q).Δ := by
        by_contra hn'
        exact hn ⟨hy, hn'⟩
      exact b.bd_sector hV hbd
    · exact .inl (support_of_mem_U _ hy.1.2 hG)
  have hoffint : Stair.Lev (fa W) b (θ W) y x → y ∉ discInt (b.sec q).Δ := by
    rintro ⟨q', -, t, ht, rfl, -⟩ hi
    exact b.discInt_off_spoke q q' hi (b.levV_support ht)
  have hsec : ∀ {W' : ↥𝒲a}, Stair.Back (fa W') (fb (p W')) (θ W') (Rt W') y x → W' = W := by
    intro W' hB
    by_contra hne
    have hne' : (p W').1 ≠ (p W).1 := fun e ↦ hne (h.p_bij.1 (Subtype.ext e))
    exact disjoint_left.mp (hdb (p W').2 (p W).2 hne') ((h.stair W').back_mem hB).1.1 hmemW
  rcases hb with ho | ⟨W', hB⟩
  · have hoffb := h.out_off_b ho (p W)
    have hi : y ∉ discInt (b.sec q).Δ := fun hi ↦ hoffb (b.discInt_sec_off_bd q hi)
    have hon := honbd hi
    have hnotH : y ∉ b.H.U := fun hH ↦ hoffb (b.hub_int hH)
    have hspoke : y ∈ (b.R.spoke b.sp q).support ∨ y ∈ (b.R.spoke b.sp (q + 1)).support
      := hon.imp id (fun h' ↦ h'.resolve_right hnotH)
    obtain ⟨q₁, hq₁, t, ht, rfl⟩ : ∃ q₁ < b.R.k, ∃ t ≤ b.top q₁, y = b.levV q₁ t := by
      rcases hspoke with h' | h' <;> exact b.exists_levV_lt h' hV
    have hL : Stair.Back (fa W) b (θ W) (Rt W) (b.levV q₁ t) ((fa W).levV (θ W q₁) t)
      := .inl ⟨q₁, hq₁, t, ht, rfl, rfl⟩
    rw [h.back_out ho hL]
    exact ⟨hL, hon⟩
  · obtain rfl := hsec hB
    refine ⟨hB, ?_⟩
    rcases hB with hL | hR | hP
    · exact honbd (hoffint hL)
    · exact .inr (.inr (hst.rt_hub hR).1.1)
    · rcases hst.onPath_stay hP with hL | ⟨q', hq', hs, hi⟩
      · exact honbd (hoffint hL)
      · exfalso
        have hne : q' ≠ q := by
          rintro rfl
          have := hmove hq'
          omega
        exact disjoint_left.mp (b.sec_off_sec (i := q) (j := q') fun e ↦ hne (b.R.reg_inj
          (by omega) hq e.symm)) hy hi

/-- A vertex sent back that is in the image of a hub sector is a vertex of the hub. -/
theorem onHub {W : ↥𝒲a} (hc : (fb (p W)).H.V.ncard ≠ 1) {x y : Shat} (hV : y ∈ Db.P.Γ.hatV cap)
  (hy : y ∈ Db.ins (fb (p W)).H) (hdb : 𝒲b.PairwiseDisjoint id)
    (hb : GBack fa fb p θ Rt Out y x) : Rt W y x := by
  have hst := h.stair W
  set b := fb (p W) with hbdef
  have hhub : hubSet Db b.H = Db.ins b.H := by
    rcases b.hW.hub_cases with ⟨z, hz, -, -⟩ | ⟨-, -, -, hz⟩
    · rw [hz, ncard_singleton] at hc
      exact absurd rfl hc
    · exact hz
  obtain ⟨-, hsub, hdis, -⟩ := b.hW.hubSet_facts
  rw [hhub] at hsub hdis
  have hint : y ∈ discInt (p W).1 := ⟨hsub hy, fun hb' ↦ disjoint_left.mp hdis hy hb'⟩
  have hsec : ∀ {W' : ↥𝒲a}, Stair.Back (fa W') (fb (p W')) (θ W') (Rt W') y x → W' = W := by
    intro W' hB
    by_contra hne
    have hne' : (p W').1 ≠ (p W).1 := fun e ↦ hne (h.p_bij.1 (Subtype.ext e))
    exact disjoint_left.mp (hdb (p W').2 (p W).2 hne') ((h.stair W').back_mem hB).1.1 hint.1
  have hlev : Stair.Lev (fa W) b (θ W) y x → y ∈ b.H.U := by
    rintro ⟨q, -, t, ht, rfl, -⟩
    have hK : b.levV q t ∈ hubSet Db b.H ∩ (walkDrawing Db.rad.G (b.R.spoke b.sp q)).U
      := ⟨hhub ▸ hy, (mem_walkDrawing_U _ _).mpr (.inl (b.levV_support ht))⟩
    rw [b.hW.hubSet_inter_spoke (b.spoke_spoke q)] at hK
    rw [mem_singleton_iff.mp hK]
    exact b.H.V_subset_U (b.spoke_spoke q).2.h_mem
  rcases hb with ho | ⟨W', hB⟩
  · exact absurd hint (h.out_off_b ho (p W))
  · obtain rfl := hsec hB
    rcases hB with hL | hR | hP
    · exact hst.rt_of_hub (hlev hL) hV (.inl hL)
    · exact hR
    · rcases hst.onPath_stay hP with hL | ⟨q', -, -, hi⟩
      · exact hst.rt_of_hub (hlev hL) hV (.inr (.inr hP))
      · exact (disjoint_left.mp (b.hub_off_sec hc q') (Or.inl hy) hi).elim

end StairSystem

theorem arm_wheel {fb : ∀ W : ↥𝒲b, WheelFrame Db W.1} (hdb : 𝒲b.PairwiseDisjoint id) {W₁ W₂ : ↥𝒲b}
  {A : Arm Db.Γ} (h₁ : A ∈ (fb W₁).arms) (h₂ : A ∈ (fb W₂).arms) : W₁ = W₂ := by
  obtain ⟨Δ₁, X₁, hc₁⟩ := (fb W₁).exists_disc h₁
  obtain ⟨Δ₂, X₂, hc₂⟩ := (fb W₂).exists_disc h₂
  have hex : ∃ v ∈ A.minus.vertexSet, cap.emb v ∈ W₁.1 := by
    rcases h₁ with ⟨i, -, rfl⟩ | ⟨hc, rfl⟩
    · exact ⟨_, ((fb W₁).vert_mem_arm i).1, by
        rw [((fb W₁).vert_V i).2]
        exact Surface.discBd_subset _ ((fb W₁).R.vert_mem i).2⟩
    · exact (fb W₁).hub_minus_mem hc
  obtain ⟨v, hv, hvW⟩ := hex
  rw [hc₂.minus] at hv
  by_contra hne
  exact disjoint_left.mp (hdb W₁.2 W₂.2 fun e ↦ hne (Subtype.ext e)) hvW (hc₂.sub hv.2)

theorem sec_ne_hub {W : Set Shat} (fr : WheelFrame Db W) (hc : fr.H.V.ncard ≠ 1)
  (i : ℕ) : fr.secArm i ≠ fr.hubArm hc := by
  intro e
  have hv := (fr.vert_mem_arm i).1
  rw [e, (fr.hubArm_disc hc).minus] at hv
  have hx := hv.2
  have hy : fr.R.vert i ∈ Db.ins fr.H ∪ ∅ := by
    have h' : cap.emb (Db.pre (fr.R.vert i)) ∈ Db.ins fr.H ∪ ∅ := hx
    rwa [(fr.vert_V i).2] at h'
  rw [union_empty] at hy
  have hhub : hubSet Db fr.H = Db.ins fr.H := by
    rcases fr.hW.hub_cases with ⟨z, hz, -, -⟩ | ⟨-, -, -, hz⟩
    · rw [hz, ncard_singleton] at hc
      exact absurd rfl hc
    · exact hz
  obtain ⟨-, -, hdis, -⟩ := fr.hW.hubSet_facts
  rw [hhub] at hdis
  exact disjoint_left.mp hdis hy (fr.R.vert_mem i).2

/-- **The outline of (14.1)**, given the staircases of the wheels and the arms and edges that
correspond. -/
theorem StairSystem.isOutline (h : StairSystem fa fb p θ Rt Out) (hd : χ.IsDisjoint)
  (hfa : 𝒲a.Finite) (hda : 𝒲a.PairwiseDisjoint id) (hfb : 𝒲b.Finite) (hdb : 𝒲b.PairwiseDisjoint id)
    (τ : Arm Da.P.Γ → Arm Db.P.Γ) (σe : Set S → Set S)
    (hτS : ∀ W, ∀ i < (fa W).R.k, ∃ q < (fb (p W)).R.k, θ W q = i ∧ (q + 1 < (fb (p W)).R.k → θ W
      (q + 1) = θ W q + 1) ∧ τ ((fa W).secArm i) = (fb (p W)).secArm q)
    (hτH : ∀ W (hc : (fa W).H.V.ncard ≠ 1), ∃ hc' : (fb (p W)).H.V.ncard ≠ 1, τ ((fa W).hubArm hc)
      = (fb (p W)).hubArm hc')
    (hπ : ∀ W, ∀ A ∈ (fa W).arms, (τ A).π.length = A.π.length ∧ ∀ (i : ℕ) (hi : i < A.π.length)
      (hi' : i < (τ A).π.length),
      Stair.Back (fa W) (fb (p W)) (θ W) (Rt W) (cap.emb (τ A).π[i]) (cap.emb A.π[i]))
    (hem : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, σe e ∈ (coverLoc 𝒲b hfb hdb fb).M.edgeSet)
    (hsize : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, (tilde (σe e)).ncard = (tilde e).ncard)
    (hinj : InjOn σe (coverLoc 𝒲a hfa hda fa).M.edgeSet)
    (hends : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, ∀ (i : ℕ) (hi : i < (Da.P.Γ.γ e).length)
      (hi' : i < (Db.P.Γ.γ (σe e)).length),
      Out (cap.emb (Db.P.Γ.γ (σe e))[i]) (cap.emb (Da.P.Γ.γ e)[i]))
    (hle : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, χ.unionLE (Da.P.φ e) (Db.P.φ (σe e))) :
    IsOutline (⟨hd, Da.P, coverLoc 𝒲a hfa hda fa⟩ : Place χ) ⟨hd, Db.P, coverLoc 𝒲b hfb hdb fb⟩ τ
      := by
  classical
  have hinjE := cap.isEmbedding.injective
  let σv : S → Set S := fun v ↦ {u | u ∈ Db.P.Γ.V ∧ StairSystem.GBack fa fb p θ Rt Out (cap.emb u)
    (cap.emb v)}
  have hpick : ∀ {y x}, y ∈ Db.P.Γ.hatV cap → ∀ {v}, x = cap.emb v → StairSystem.GBack fa fb p θ Rt
    Out y x → (σv v).Nonempty := by
    rintro y x ⟨u, hu, rfl⟩ v rfl hb
    exact ⟨u, hu, hb⟩
  have hclass : ∀ A ∈ (coverLoc 𝒲a hfa hda fa).arms, ∃ W, A ∈ (fa W).arms
    := fun A hA ↦ mem_iUnion.mp hA
  refine ⟨?_, ?_, σv, σe, ⟨RootedLocation.M_le _, fun e he ↦ (hem e he).1, hsize, hinj, ?_,
    fun _ _ _ hu ↦ hu.1, ?_, ?_, ?_⟩, hem, ?_, ?_, hle⟩
  · intro A hA
    obtain ⟨W, hW⟩ := hclass A hA
    refine mem_iUnion.mpr ⟨p W, ?_⟩
    rcases hW with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩
    · obtain ⟨q, hq, -, -, e⟩ := hτS W i hi
      rw [e]
      exact .inl ⟨q, hq, rfl⟩
    · obtain ⟨hc', e⟩ := hτH W hc
      rw [e]
      exact .inr ⟨hc', rfl⟩
  · -- `τ` is one to one.
    intro A hA A' hA' he
    obtain ⟨W, hW⟩ := hclass A hA
    obtain ⟨W', hW'⟩ := hclass A' hA'
    have hmem : ∀ {W A}, A ∈ (fa W).arms → τ A ∈ (fb (p W)).arms := by
      rintro W _ (⟨i, hi, rfl⟩ | ⟨hc, rfl⟩)
      · obtain ⟨q, hq, -, -, e⟩ := hτS W i hi
        rw [e]
        exact .inl ⟨q, hq, rfl⟩
      · obtain ⟨hc', e⟩ := hτH W hc
        rw [e]
        exact .inr ⟨hc', rfl⟩
    obtain rfl : W = W' := h.p_bij.1 (arm_wheel hdb (hmem hW) (he ▸ hmem hW'))
    rcases hW with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩ <;> rcases hW' with ⟨i', hi', rfl⟩ | ⟨hc', rfl⟩
    · obtain ⟨q, hq, e₁, -, e⟩ := hτS W i hi
      obtain ⟨q', hq', e₁', -, e'⟩ := hτS W i' hi'
      rw [e, e'] at he
      obtain rfl := (fb (p W)).secArm_inj hq hq' he
      rw [← e₁, ← e₁']
    · obtain ⟨q, hq, -, -, e⟩ := hτS W i hi
      obtain ⟨hc₂, e'⟩ := hτH W hc'
      rw [e, e'] at he
      exact absurd he (sec_ne_hub _ hc₂ q)
    · obtain ⟨q, hq, -, -, e⟩ := hτS W i' hi'
      obtain ⟨hc₂, e'⟩ := hτH W hc
      rw [e, e'] at he
      exact absurd he.symm (sec_ne_hub _ hc₂ q)
    · rfl
  · -- `σ(v)` is not empty.
    rintro v ⟨hvV, hvA⟩
    have hV : cap.emb v ∈ Da.P.Γ.hatV cap := ⟨v, hvV, rfl⟩
    by_cases hin : ∃ W : ↥𝒲a, cap.emb v ∈ discInt W.1
    · obtain ⟨W, hW⟩ := hin
      have hst := h.stair W
      have hoff : ∀ A ∈ (fa W).arms, ∀ Δ X, IsDiscArm (fa W) A Δ X → cap.emb v ∉ discInt Δ
        := fun A hA Δ X hc ↦
        (fa W).emb_notMem_discInt hc (hvA A (mem_iUnion.mpr ⟨W, hA⟩))
      rcases (fa W).mem_cases hV hW.1 hoff with ⟨i, hi, t, ht, e⟩ | hH
      · obtain ⟨q, hq, rfl⟩ := hst.surj hi
        have ht' : t ≤ (fb (p W)).top q := by
          rw [hst.top_eq q hq]
          exact ht
        exact hpick ((fb (p W)).levV_hatV ht') rfl (.inr ⟨W, .inl ⟨q, hq, t, ht', rfl, e⟩⟩)
      · obtain ⟨y, hy⟩ := hst.rt_a hH hV
        exact hpick (hst.rt_hub hy).1.2 rfl (.inr ⟨W, .inr (.inl hy)⟩)
    · push Not at hin
      obtain ⟨y, hy⟩ := h.out_ne _ hV hin
      exact hpick (h.out_hat hy).1 rfl (.inl hy)
  · -- `σ(v)` is connected.
    intro v _ a a'
    obtain ⟨u, hu⟩ := a
    obtain ⟨u', hu'⟩ := a'
    exact reachable_of_skJoined (D := Db) (X := {y | StairSystem.GBack fa fb p θ Rt Out y
      (cap.emb v)}) (T := σv v) (fun a ha hx ↦ ⟨ha, hx⟩) (h.gjoin hda hu.2 hu'.2) hu hu' rfl rfl
  · -- The sets `σ(v)` are disjoint.
    intro v₁ _ v₂ _ hne
    refine disjoint_left.mpr fun u (h₁ : u ∈ σv v₁) (h₂ : u ∈ σv v₂) ↦ hne (hinjE
      (h.gback_fun hdb h₁.2 h₂.2))
  · -- The ends.
    intro e he i hi hi'
    have ho := hends e he i hi hi'
    obtain ⟨u, hu, hue⟩ := (h.out_hat ho).1
    have : u = (Db.P.Γ.γ (σe e))[i] := hinjE hue
    exact ⟨this ▸ hu, .inl ho⟩
  · -- The marches.
    intro A hA
    obtain ⟨W, hW⟩ := hclass A hA
    obtain ⟨h₁, h₂⟩ := hπ W A hW
    refine ⟨h₁, fun i hi hi' ↦ ⟨?_, .inr ⟨W, h₂ i hi hi'⟩⟩⟩
    have hmem : (τ A).π[i] ∈ {v | v ∈ (τ A).π} := List.getElem_mem hi'
    rw [(τ A).π_set] at hmem
    exact (τ A).isSeparation.left_le.vertexSet_subset hmem.1
  · -- At most one vertex of `σ(v)` is in `τ(A)`.
    intro A hA v _
    obtain ⟨W, hW⟩ := hclass A hA
    have hfin : (σv v ∩ (τ A).V).Finite := Db.P.Γ.finite_V.subset fun _ hu ↦ hu.1.1
    refine (ncard_le_one hfin).mpr fun u hu u' hu' ↦ hinjE ?_
    have hhat : ∀ {a}, a ∈ σv v → cap.emb a ∈ Db.P.Γ.hatV cap := fun {a} ha ↦ ⟨a, ha.1, rfl⟩
    rcases hW with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩
    · obtain ⟨q, hq, -, hmove, e⟩ := hτS W i hi
      have hV : ∀ {a}, a ∈ (τ ((fa W).secArm i)).V → cap.emb a ∈ ((fb (p W)).sec q).Δ ∪ (fb
        (p W)).secX q := fun {a} ha ↦ by
        rw [e] at ha
        have h₂ : a ∈ ((fb (p W)).secArm q).minus.vertexSet := ha
        rw [((fb (p W)).secArm_disc q).minus] at h₂
        exact h₂.2
      obtain ⟨b₁, s₁⟩ := h.onSec hq hmove (hhat hu.1) (hV hu.2) hdb hu.1.2
      obtain ⟨b₂, s₂⟩ := h.onSec hq hmove (hhat hu'.1) (hV hu'.2) hdb hu'.1.2
      exact (h.stair W).sector_unique hq hmove b₁ b₂ (hhat hu.1) (hhat hu'.1) s₁ s₂
    · obtain ⟨hc', e⟩ := hτH W hc
      have hV : ∀ {a}, a ∈ (τ ((fa W).hubArm hc)).V → cap.emb a ∈ Db.ins (fb (p W)).H
        := fun {a} ha ↦ by
        rw [e] at ha
        have h₂ : a ∈ ((fb (p W)).hubArm hc').minus.vertexSet := ha
        rw [((fb (p W)).hubArm_disc hc').minus] at h₂
        have h₃ : cap.emb a ∈ Db.ins (fb (p W)).H ∪ ∅ := h₂.2
        rwa [union_empty] at h₃
      exact (h.stair W).rt_inj (h.onHub hc' (hhat hu.1) (hV hu.2) hdb hu.1.2) (h.onHub hc'
        (hhat hu'.1) (hV hu'.2) hdb hu'.1.2)

end GraphMinor.GM19
