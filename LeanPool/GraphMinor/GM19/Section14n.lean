/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14m

/-!
# Graph Minors XIX, Section 14: a staircase between two wheels

A linear inflation of the cut paintings sends the rim of a wheel in `Γ_j` to the rim of the same
wheel in `Γ_i`. Each step along the
rim of `Γ_j` either stays at a vertex or moves on one vertex. This is the check that the paper omits
at the end of (14.1): it defines
`σ''` by the `k`th terms of the marches `μ(u)`, and refers to the proof of XX (9.1). We write it
here in full.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D Da Db : TangleDatum cap χ} {W Wa Wb :
    Set Shat}

namespace TangleDatum.WheelFrame

/-- The spoke at a rim position depends only on the rim vertex. -/
theorem levV_congr (fr : WheelFrame D W) {i j : ℕ} (h : fr.R.vert i = fr.R.vert j)
  (t : ℕ) : fr.levV i t = fr.levV j t := by
  have key : ∀ (x y : bdVerts D W), x.1 = y.1 → GraphWalk.vertexAt (fr.sp.K x) (2 * t)
    = GraphWalk.vertexAt (fr.sp.K y) (2 * t) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    obtain rfl : x = y := e
    rfl
  exact key _ _ h

theorem vert_mod (fr : WheelFrame D W) (i : ℕ) : fr.R.vert (i % fr.R.k) = fr.R.vert i := by
  rw [TangleDatum.Rim.vert, TangleDatum.Rim.vert, Nat.mod_mod]

theorem levV_wrap (fr : WheelFrame D W) (t : ℕ) : fr.levV fr.R.k t = fr.levV 0 t :=
  fr.levV_congr (by simpa using fr.R.vert_add_k 0) t

theorem top_congr (fr : WheelFrame D W) {i j : ℕ} (h : fr.R.vert i = fr.R.vert j) : fr.top i
  = fr.top j := by
  have key : ∀ (x y : bdVerts D W), x.1 = y.1 → (fr.sp.K x).length / 2 = (fr.sp.K y).length / 2
    := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    obtain rfl : x = y := e
    rfl
  exact key _ _ h

/-- All the spokes through a vertex at level `t`, along an arc of the rim. -/
theorem arc_level (fr : WheelFrame D W) {i j t : ℕ} (hij : i < j) (hj : j < fr.R.k) (ht : t
  ≤ fr.top i) (ht' : t ≤ fr.top j) (e : fr.levV i t = fr.levV j t) :
    (∀ l, i ≤ l → l ≤ j → t ≤ fr.top l ∧ fr.levV l t = fr.levV i t) ∨ ∀ l < fr.R.k, (l ≤ i ∨ j ≤ l)
      → t ≤ fr.top l ∧ fr.levV l t = fr.levV i t := by
  have hV := fr.levV_hatV ht
  have hsi := fr.levV_support ht
  have hsj := fr.levV_support ht'
  rw [← e] at hsj
  have key : ∀ l, fr.levV i t ∈ (fr.R.spoke fr.sp l).support → t ≤ fr.top l ∧ fr.levV l t
    = fr.levV i t := fun l hl ↦ by
    obtain ⟨t', ht₂, he⟩ := fr.exists_levV hl hV
    obtain rfl := fr.level_eq ht ht₂ he
    exact ⟨ht₂, he.symm⟩
  exact (fr.R.arc fr.hW fr.hbdS fr.hin fr.sp hij hj hsi hsj).imp (fun h l h₁ h₂ ↦ key l
    (h l h₁ h₂)) fun h l hl h₁ ↦ key l (h l hl h₁)

theorem path_reg (fr : WheelFrame D W) {i t : ℕ} {y : Shat} (hy : y ∈ fr.path i t) : fr.Reg i := by
  classical
  by_contra hn
  rw [path, dite_eq_right hn] at hy
  exact hy

end TangleDatum.WheelFrame

open TangleDatum

/-- **A staircase** from the rim of a wheel of `Γ_j` to the rim of the same wheel of `Γ_i`, with a
pairing `Rt` of the vertices of `Γ_j` and `Γ_i` on the hubs. -/
structure Stair (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (θ : ℕ → ℕ) (Rt : Shat → Shat
  → Prop) : Prop where
  zero : θ 0 = 0
  last : θ (b.R.k - 1) = a.R.k - 1
  step : ∀ q, q + 1 < b.R.k → θ (q + 1) = θ q ∨ θ (q + 1) = θ q + 1
  top_eq : ∀ q < b.R.k, b.top q = a.top (θ q)
  stay_reg : ∀ q, q + 1 < b.R.k → θ (q + 1) = θ q → b.Reg q
  move_iff : ∀ q, q + 1 < b.R.k → θ (q + 1) = θ q + 1 → ∀ t ≤ b.top q, (b.levV q t = b.levV
    (q + 1) t ↔ a.levV (θ q) t = a.levV (θ q + 1) t)
  wrap_iff : ∀ t ≤ b.top (b.R.k - 1), (b.levV (b.R.k - 1) t = b.levV 0 t ↔ a.levV (a.R.k - 1) t
    = a.levV 0 t)
  rt_fun : ∀ {y x x'}, Rt y x → Rt y x' → x = x'
  rt_inj : ∀ {y y' x}, Rt y x → Rt y' x → y = y'
  rt_hub : ∀ {y x}, Rt y x → (y ∈ b.H.U ∧ y ∈ Db.P.Γ.hatV cap) ∧ x ∈ a.H.U ∧ x ∈ Da.P.Γ.hatV cap
  rt_b : ∀ {y}, y ∈ b.H.U → y ∈ Db.P.Γ.hatV cap → ∃ x, Rt y x
  rt_a : ∀ {x}, x ∈ a.H.U → x ∈ Da.P.Γ.hatV cap → ∃ y, Rt y x
  rt_lev : ∀ {y x}, Rt y x → ∀ q < b.R.k, ∀ t ≤ b.top q, (x = a.levV (θ q) t ↔ y = b.levV q t)

namespace Stair

variable {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {θ : ℕ → ℕ} {Rt : Shat → Shat → Prop}
  (h : Stair a b θ Rt)
include h

theorem mono {q q' : ℕ} (hq : q ≤ q') (hq' : q' < b.R.k) : θ q ≤ θ q' := by
  induction q', hq using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have := ih (by omega)
    rcases h.step n hq' with e | e <;> omega

theorem lt {q : ℕ} (hq : q < b.R.k) : θ q < a.R.k := by
  have h₁ := h.mono (show q ≤ b.R.k - 1 by omega) (by have := b.R.two; omega)
  have h₂ := h.last
  have := a.R.two
  omega

theorem surj {p : ℕ} (hp : p < a.R.k) : ∃ q < b.R.k, θ q = p := by
  have h2 := b.R.two
  by_contra hn
  push Not at hn
  have hle : ∀ q, q < b.R.k → θ q < p := fun q ↦ by
    induction q with
    | zero =>
      intro hq
      have := hn 0 hq
      rw [h.zero] at this ⊢
      omega
    | succ n ih =>
      intro hq
      have h₁ := ih (by omega)
      have h₂ := hn _ hq
      rcases h.step n hq with e | e <;> omega
  have h₁ := hle _ (show b.R.k - 1 < b.R.k by omega)
  rw [h.last] at h₁
  omega

/-- Equal levels on a run of the rim of `Γ_j` give equal levels at the two ends of the image of the
run. -/
theorem run {q q' t : ℕ} (hq : q ≤ q') (hq' : q' < b.R.k) (hl : ∀ l, q ≤ l → l ≤ q' → t ≤ b.top l
  ∧ b.levV l t = b.levV q t) : a.levV (θ q) t = a.levV (θ q') t := by
  induction q', hq using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h₁ := ih (by omega) fun l h₁ h₂ ↦ hl l h₁ (by omega)
    rw [h₁]
    rcases h.step n hq' with e | e
    · rw [e]
    · rw [e]
      have e₁ := (hl n hn (by omega))
      have e₂ := (hl (n + 1) (by omega) le_rfl)
      exact (h.move_iff n hq' e t e₁.1).mp (e₁.2.trans e₂.2.symm)

/-- **Levels pass from `Γ_j` to `Γ_i`.** -/
theorem transfer {q q' t : ℕ} (hq : q < b.R.k) (hq' : q' < b.R.k) (ht : t ≤ b.top q) (ht' : t
  ≤ b.top q') (e : b.levV q t = b.levV q' t) : a.levV (θ q) t = a.levV (θ q') t := by
  have main : ∀ {q q' : ℕ}, q < q' → q' < b.R.k → t ≤ b.top q → t ≤ b.top q' → b.levV q t
    = b.levV q' t → a.levV (θ q) t = a.levV (θ q') t := by
    intro q q' hlt hq' ht ht' e
    rcases b.arc_level hlt hq' ht ht' e with hl | hl
    · exact h.run hlt.le hq' hl
    · have h₁ : a.levV (θ 0) t = a.levV (θ q) t := h.run (Nat.zero_le q) (by omega) fun l _ h₂ ↦ by
        have e₁ := hl l (by omega) (.inl h₂)
        have e₂ := hl 0 (by omega) (.inl (Nat.zero_le _))
        exact ⟨e₁.1, e₁.2.trans e₂.2.symm⟩
      have h₂ : a.levV (θ q') t = a.levV (θ (b.R.k - 1)) t :=
        h.run (show q' ≤ b.R.k - 1 by omega) (by omega) fun l h₁ h₂ ↦ by
        have e₁ := hl l (by omega) (.inr h₁)
        have e₂ := hl q' hq' (.inr le_rfl)
        exact ⟨e₁.1, e₁.2.trans e₂.2.symm⟩
      have hl₁ := hl (b.R.k - 1) (by omega) (.inr (by omega))
      have hl₀ := hl 0 (by omega) (.inl (Nat.zero_le _))
      have h₃ := (h.wrap_iff t hl₁.1).mp (hl₁.2.trans hl₀.2.symm)
      rw [h.zero] at h₁
      rw [h.last] at h₂
      rw [← h₁, h₂, h₃]
  rcases lt_trichotomy q q' with hlt | rfl | hlt
  · exact main hlt hq' ht ht' e
  · rfl
  · exact (main hlt hq ht' ht e.symm).symm

/-- A step of the rim of `Γ_j` keeps equal levels of `Γ_i` joined, by a path of (13.7) when the step
stays, and by equality when it moves. -/
theorem wrap_lev {t : ℕ} (ht : t ≤ a.top (a.R.k - 1)) (e : a.levV (a.R.k - 1) t
  = a.levV 0 t) : b.levV (b.R.k - 1) t = b.levV 0 t := by
  have h2 := b.R.two
  have htt : t ≤ b.top (b.R.k - 1) := by
    rw [h.top_eq _ (by omega), h.last]
    exact ht
  exact (h.wrap_iff t htt).mpr e

end Stair

omit [T2Space S] [T2Space Shat] in
theorem TangleDatum.SkJoined.symm {X : Set Shat} {x y : Shat} (h : D.SkJoined X x y) : D.SkJoined X
  y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨h₁, h₂, p, q, hp, hq, hadj⟩ := hs
    exact Relation.ReflTransGen.head ⟨h₂, h₁, q, p, hq, hp, hadj.symm⟩ ih

omit [T2Space S] [T2Space Shat] in
theorem TangleDatum.SkJoined.trans {X : Set Shat} {x y z : Shat} (h : D.SkJoined X x y)
  (h' : D.SkJoined X y z) : D.SkJoined X x z := Relation.ReflTransGen.trans h h'

/-- `y` is at the same level as `x`, under the staircase. -/
def Stair.Lev (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (θ : ℕ → ℕ) (y x : Shat) : Prop :=
  ∃ q < b.R.k, ∃ t ≤ b.top q, y = b.levV q t ∧ x = a.levV (θ q) t

/-- `y` lies on a path of (13.7) of a step that stays at the rim vertex below `x`. -/
def Stair.OnPath (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (θ : ℕ → ℕ) (y x : Shat) : Prop :=
  ∃ q t, q + 1 < b.R.k ∧ θ (q + 1) = θ q ∧ t ≤ b.top q ∧ y ∈ b.path q t ∧ x = a.levV (θ q) t

/-- The set `σ(x)` in the wheel: `y` is sent back to `x`. -/
def Stair.Back (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (θ : ℕ → ℕ) (Rt : Shat → Shat → Prop)
  (y x : Shat) : Prop :=
  Stair.Lev a b θ y x ∨ Rt y x ∨ Stair.OnPath a b θ y x

namespace Stair

variable {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {θ : ℕ → ℕ} {Rt : Shat → Shat → Prop}
  (h : Stair a b θ Rt)
include h

theorem onPath_cases {y x : Shat} (hp : OnPath a b θ y x) : Lev a b θ y x ∨ ∃ q t, q < b.R.k ∧ t
  ≤ b.top q ∧ y ∈ b.path q t ∧ y ∈ discInt (b.sec q).Δ ∧ x = a.levV (θ q) t := by
  obtain ⟨q, t, hq, hs, ht, hy, rfl⟩ := hp
  have hr := h.stay_reg q hq hs
  rcases b.path_cases hr ht hy with e | e | e
  · exact .inl ⟨q, by omega, t, ht, e, rfl⟩
  · refine .inl ⟨q + 1, hq, t, ?_, e, by rw [hs]⟩
    rw [← b.top_eq_of_inner hr]
    exact ht
  · exact .inr ⟨q, t, by omega, ht, hy, e, rfl⟩

theorem onPath_stay {y x : Shat} (hp : OnPath a b θ y x) : Lev a b θ y x ∨ ∃ q, q + 1 < b.R.k ∧ θ
  (q + 1) = θ q ∧ y ∈ discInt (b.sec q).Δ := by
  obtain ⟨q, t, hq, hs, ht, hy, rfl⟩ := hp
  have hr := h.stay_reg q hq hs
  rcases b.path_cases hr ht hy with e | e | e
  · exact .inl ⟨q, by omega, t, ht, e, rfl⟩
  · refine .inl ⟨q + 1, hq, t, ?_, e, by rw [hs]⟩
    rw [← b.top_eq_of_inner hr]
    exact ht
  · exact .inr ⟨q, hq, hs, e⟩

theorem lev_fun {y x x' : Shat} (h₁ : Lev a b θ y x) (h₂ : Lev a b θ y x') : x = x' := by
  obtain ⟨q, hq, t, ht, rfl, rfl⟩ := h₁
  obtain ⟨q', hq', t', ht', e, rfl⟩ := h₂
  obtain rfl := b.level_eq ht ht' e
  exact h.transfer hq hq' ht ht' e

theorem lev_rt {y x x' : Shat} (h₁ : Lev a b θ y x) (h₂ : Rt y x') : x = x' := by
  obtain ⟨q, hq, t, ht, rfl, rfl⟩ := h₁
  exact ((h.rt_lev h₂ q hq t ht).mpr rfl).symm

/-- `σ` of two vertices are disjoint. -/
theorem back_fun {y x x' : Shat} (h₁ : Back a b θ Rt y x) (h₂ : Back a b θ Rt y x') : x = x' := by
  have hoff : ∀ {x₁ x₂ : Shat} {q : ℕ}, Lev a b θ y x₁ → y ∈ discInt (b.sec q).Δ → x₁ = x₂
    := fun {x₁ x₂ q} hl hi ↦ by
    obtain ⟨q', hq', t', ht', rfl, -⟩ := hl
    exact absurd (b.levV_support ht') (b.discInt_off_spoke q q' hi)
  have hoffR : ∀ {x₁ x₂ : Shat} {q : ℕ}, Rt y x₁ → y ∈ discInt (b.sec q).Δ → x₁ = x₂
    := fun {x₁ x₂ q} hl hi ↦ absurd (h.rt_hub hl).1.1 (b.discInt_off_hub q hi)
  have hsorted : Lev a b θ y x ∨ Rt y x ∨ ∃ q t, q < b.R.k ∧ t ≤ b.top q ∧ y ∈ b.path q t
    ∧ y ∈ discInt (b.sec q).Δ ∧ x = a.levV (θ q) t := by
    rcases h₁ with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · rcases h.onPath_cases h' with h'' | h''
      · exact .inl h''
      · exact .inr (.inr h'')
  have hsorted' : Lev a b θ y x' ∨ Rt y x' ∨ ∃ q t, q < b.R.k ∧ t ≤ b.top q ∧ y ∈ b.path q t
    ∧ y ∈ discInt (b.sec q).Δ ∧ x' = a.levV (θ q) t := by
    rcases h₂ with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · rcases h.onPath_cases h' with h'' | h''
      · exact .inl h''
      · exact .inr (.inr h'')
  rcases hsorted with h₃ | h₃ | ⟨q, t, hq, ht, hy, hi, rfl⟩ <;>
    rcases hsorted' with h₄ | h₄ | ⟨q', t', hq', ht', hy', hi', rfl⟩
  · exact h.lev_fun h₃ h₄
  · exact h.lev_rt h₃ h₄
  · exact hoff h₃ hi'
  · exact (h.lev_rt h₄ h₃).symm
  · exact h.rt_fun h₃ h₄
  · exact hoffR h₃ hi'
  · exact (hoff h₄ hi).symm
  · exact (hoffR h₄ hi).symm
  · obtain rfl : q = q' := by
      by_contra hne
      refine disjoint_left.mp (b.disjoint_int (i := q) (j := q') fun e ↦ hne ?_) hi hi'
      exact b.R.reg_inj hq hq' e
    obtain rfl : t = t' := by
      by_contra hne
      exact disjoint_left.mp ((b.path_spec (b.path_reg hy)).disj t t' ht ht' hne) hy hy'
    rfl

/-- Consecutive equal levels of `Γ_i` are joined in `σ(x)`. -/
theorem join_step {x : Shat} {l t : ℕ} (hl : l + 1 < b.R.k) (ht : t ≤ b.top l)
    (h₁ : a.levV (θ l) t = x) (h₂ : a.levV (θ (l + 1)) t = x) :
    Db.SkJoined {y | Back a b θ Rt y x} (b.levV l t) (b.levV (l + 1) t) := by
  rcases h.step l hl with e | e
  · have hr := h.stay_reg l hl e
    have hP := b.path_spec hr
    have hsub : b.path l t ⊆ {y | Back a b θ Rt y x} := fun y hy ↦ .inr
      (.inr ⟨l, t, hl, e, ht, hy, h₁.symm⟩)
    exact TangleDatum.SkJoined.mono hsub (hP.joined t ht _ (hP.right t ht))
  · rw [(h.move_iff l hl e t ht).mpr (by rw [h₁, ← e, h₂])]
    exact Relation.ReflTransGen.refl

theorem join_run {x : Shat} {q q' t : ℕ} (hq : q ≤ q') (hq' : q' < b.R.k) (hl : ∀ l, q ≤ l → l ≤ q'
  → t ≤ a.top (θ l) ∧ a.levV (θ l) t = x) :
    Db.SkJoined {y | Back a b θ Rt y x} (b.levV q t) (b.levV q' t) := by
  induction q', hq using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ n hn ih =>
    have h₁ := ih (by omega) fun l h₁ h₂ ↦ hl l h₁ (by omega)
    have e₁ := hl n hn (by omega)
    have e₂ := hl (n + 1) (by omega) le_rfl
    exact TangleDatum.SkJoined.trans h₁
      (h.join_step hq' (by rw [h.top_eq _ (by omega)]; exact e₁.1) e₁.2 e₂.2)

theorem lev_top {q t : ℕ} (hq : q < b.R.k) (ht : t ≤ b.top q) : t ≤ a.top (θ q) := by
  rw [← h.top_eq q hq]
  exact ht

/-- **`σ(x)` is connected: the levels.** -/
theorem join_lev {x : Shat} {q q' t t' : ℕ} (hq : q < b.R.k) (hq' : q' < b.R.k) (ht : t ≤ b.top q)
  (ht' : t' ≤ b.top q') (h₁ : x = a.levV (θ q) t) (h₂ : x = a.levV (θ q') t') :
    Db.SkJoined {y | Back a b θ Rt y x} (b.levV q t) (b.levV q' t') := by
  obtain rfl : t = t' := a.level_eq (h.lev_top hq ht) (h.lev_top hq' ht') (h₁.symm.trans h₂)
  have main : ∀ {q q' : ℕ}, q < q' → q' < b.R.k → t ≤ b.top q → t ≤ b.top q' → x = a.levV (θ q) t
    → x = a.levV (θ q') t → Db.SkJoined {y | Back a b θ Rt y x} (b.levV q t) (b.levV q' t) := by
    intro q q' hlt hq' ht ht' h₁ h₂
    have hat := h.lev_top (by omega) ht
    have hat' := h.lev_top hq' ht'
    rcases (h.mono hlt.le hq').lt_or_eq with hθ | hθ
    · rcases a.arc_level hθ (h.lt hq') hat hat' (h₁.symm.trans h₂) with hl | hl
      · refine h.join_run hlt.le hq' fun l h₃ h₄ ↦ ?_
        have := hl (θ l) (h.mono h₃ (by omega)) (h.mono h₄ hq')
        exact ⟨this.1, this.2.trans h₁.symm⟩
      · have h₃ : Db.SkJoined {y | Back a b θ Rt y x} (b.levV 0 t) (b.levV q t) := h.join_run
          (Nat.zero_le q) (by omega) fun l _ h₄ ↦ by
          have := hl (θ l) (h.lt (by omega)) (.inl (h.mono h₄ (by omega)))
          exact ⟨this.1, this.2.trans h₁.symm⟩
        have h₄ : Db.SkJoined {y | Back a b θ Rt y x} (b.levV q' t) (b.levV (b.R.k - 1) t) :=
          h.join_run (show q' ≤ b.R.k - 1 by omega) (by omega) fun l h₄ h₅ ↦ by
          have := hl (θ l) (h.lt (by omega)) (.inr (h.mono h₄ (by omega)))
          exact ⟨this.1, this.2.trans h₁.symm⟩
        have e₀ := hl (θ 0) (h.lt (by omega)) (.inl (h.mono (Nat.zero_le q) (by omega)))
        have e₁ := hl (θ (b.R.k - 1)) (h.lt (by omega))
          (.inr (h.mono (show q' ≤ b.R.k - 1 by omega) (by omega)))
        rw [h.zero] at e₀
        rw [h.last] at e₁
        have e₂ := h.wrap_lev e₁.1 (e₁.2.trans e₀.2.symm)
        have h₅ : Db.SkJoined {y | Back a b θ Rt y x} (b.levV 0 t) (b.levV q' t) := by
          rw [← e₂]
          exact h₄.symm
        exact TangleDatum.SkJoined.trans h₃.symm h₅
    · refine h.join_run hlt.le hq' fun l h₃ h₄ ↦ ?_
      have h₅ : θ l = θ q := le_antisymm (hθ ▸ h.mono h₄ hq') (h.mono h₃ (by omega))
      rw [h₅]
      exact ⟨hat, h₁.symm⟩
  rcases lt_trichotomy q q' with hlt | rfl | hlt
  · exact main hlt hq' ht ht' h₁ h₂
  · exact Relation.ReflTransGen.refl
  · exact (main hlt hq ht' ht h₂ h₁).symm

/-- **`σ(x)` is connected in the wheel.** -/
theorem join_back {x y y' : Shat} (h₁ : Back a b θ Rt y x) (h₂ : Back a b θ Rt y' x) : Db.SkJoined
  {y | Back a b θ Rt y x} y y' := by
  by_cases hl : ∃ q, ∃ t, q < b.R.k ∧ t ≤ b.top q ∧ x = a.levV (θ q) t
  · obtain ⟨q₀, t₀, hq₀, ht₀, hx⟩ := hl
    have key : ∀ {z}, Back a b θ Rt z x → Db.SkJoined {y | Back a b θ Rt y x} (b.levV q₀ t₀) z := by
      intro z hz
      rcases hz with ⟨q, hq, t, ht, rfl, hx'⟩ | hz | ⟨q, t, hq, hs, ht, hy, hx'⟩
      · exact h.join_lev hq₀ hq ht₀ ht hx hx'
      · rw [(h.rt_lev hz q₀ hq₀ t₀ ht₀).mp hx]
        exact Relation.ReflTransGen.refl
      · have hP := b.path_spec (h.stay_reg q hq hs)
        have hsub : b.path q t ⊆ {y | Back a b θ Rt y x} := fun y hy ↦ .inr
          (.inr ⟨q, t, hq, hs, ht, hy, hx'⟩)
        exact TangleDatum.SkJoined.trans (h.join_lev hq₀ (by omega) ht₀ ht hx hx')
          (TangleDatum.SkJoined.mono hsub (hP.joined t ht z hy))
    exact TangleDatum.SkJoined.trans (key h₁).symm (key h₂)
  · have key : ∀ {z}, Back a b θ Rt z x → Rt z x := by
      intro z hz
      rcases hz with ⟨q, hq, t, ht, -, hx'⟩ | hz | ⟨q, t, hq, -, ht, -, hx'⟩
      · exact absurd ⟨q, t, hq, ht, hx'⟩ hl
      · exact hz
      · exact absurd ⟨q, t, by omega, ht, hx'⟩ hl
    rw [h.rt_inj (key h₁) (key h₂)]
    exact Relation.ReflTransGen.refl

/-- A vertex of `Γ_j` sent back to `x`, on a spoke of the wheel, is at the same level as `x`. -/
theorem lev_of_spoke {x y : Shat} {q t : ℕ} (hq : q < b.R.k) (ht : t ≤ b.top q) (hy : y
  = b.levV q t) (hb : Back a b θ Rt y x) : x = a.levV (θ q) t :=
  h.back_fun hb (.inl ⟨q, hq, t, ht, hy, rfl⟩)

/-- A vertex of the hub of `Γ_j` is paired with the vertex it is sent back to. -/
theorem rt_of_hub {x y : Shat} (hyH : y ∈ b.H.U) (hyV : y ∈ Db.P.Γ.hatV cap)
  (hb : Back a b θ Rt y x) : Rt y x := by
  obtain ⟨x', hx'⟩ := h.rt_b hyH hyV
  rw [h.back_fun hb (.inr (.inl hx'))]
  exact hx'

/-- **At most one vertex of `σ(x)` is on the boundary of the image of a sector.** -/
theorem sector_unique {x y₁ y₂ : Shat} {q : ℕ} (hq : q < b.R.k) (hmove : q + 1 < b.R.k → θ (q + 1)
  = θ q + 1) (h₁ : Back a b θ Rt y₁ x) (h₂ : Back a b θ Rt y₂ x)
    (hV₁ : y₁ ∈ Db.P.Γ.hatV cap) (hV₂ : y₂ ∈ Db.P.Γ.hatV cap) (hy₁ : y₁ ∈
      (b.R.spoke b.sp q).support ∨ y₁ ∈ (b.R.spoke b.sp (q + 1)).support ∨ y₁ ∈ b.H.U)
    (hy₂ : y₂ ∈ (b.R.spoke b.sp q).support ∨ y₂ ∈ (b.R.spoke b.sp (q + 1)).support
      ∨ y₂ ∈ b.H.U) : y₁ = y₂ := by
  have h2 := b.R.two
  -- The rim position after `q`.
  obtain ⟨q', hq'lt, hvert, hcase⟩ : ∃ q' < b.R.k, b.R.vert (q + 1) = b.R.vert q' ∧ ((q + 1 < b.R.k
    ∧ q' = q + 1) ∨ (q + 1 = b.R.k ∧ q' = 0)) := by
    by_cases hlt : q + 1 < b.R.k
    · exact ⟨q + 1, hlt, rfl, .inl ⟨hlt, rfl⟩⟩
    · have e : q + 1 = b.R.k := by omega
      refine ⟨0, by omega, ?_, .inr ⟨e, rfl⟩⟩
      rw [e]
      simpa using b.R.vert_add_k 0
  have hform : ∀ {y}, y ∈ Db.P.Γ.hatV cap → (y ∈ (b.R.spoke b.sp q).support ∨ y ∈ (b.R.spoke b.sp
    (q + 1)).support ∨ y ∈ b.H.U) →
      y ∈ b.H.U ∨ (∃ t ≤ b.top q, y = b.levV q t) ∨ ∃ t ≤ b.top q', y = b.levV q' t := by
    intro y hV hy
    rcases hy with hy | hy | hy
    · exact .inr (.inl (b.exists_levV hy hV))
    · obtain ⟨t, ht, e⟩ := b.exists_levV hy hV
      exact .inr (.inr ⟨t, by rw [← b.top_congr hvert]; exact ht,
        by rw [e]; exact b.levV_congr hvert t⟩)
    · exact .inl hy
  have hmix : ∀ {y y' : Shat} {p t : ℕ}, Back a b θ Rt y x → Back a b θ Rt y' x → y' ∈ b.H.U
    → y' ∈ Db.P.Γ.hatV cap → p < b.R.k → t ≤ b.top p → y = b.levV p t → y = y' := by
    intro y y' p t hb hb' hH hV hp ht he
    have hR := h.rt_of_hub hH hV hb'
    have hx := h.lev_of_spoke hp ht he hb
    rw [he]
    exact ((h.rt_lev hR p hp t ht).mp hx).symm
  have hpair : ∀ {t t' : ℕ}, t ≤ b.top q → t' ≤ b.top q' → Back a b θ Rt (b.levV q t) x
    → Back a b θ Rt (b.levV q' t') x → b.levV q t = b.levV q' t' := by
    intro t t' ht ht' hb hb'
    have hx := h.lev_of_spoke hq ht rfl hb
    have hx' := h.lev_of_spoke hq'lt ht' rfl hb'
    obtain rfl : t = t' := a.level_eq (h.lev_top hq ht) (h.lev_top hq'lt ht') (hx.symm.trans hx')
    rcases hcase with ⟨hlt, rfl⟩ | ⟨e, rfl⟩
    · exact (h.move_iff q hlt (hmove hlt) t ht).mpr (by rw [← hmove hlt, ← hx, ← hx'])
    · obtain rfl : q = b.R.k - 1 := by omega
      refine (h.wrap_iff t ht).mpr ?_
      rw [h.last] at hx
      rw [h.zero] at hx'
      rw [← hx, ← hx']
  have hsame : ∀ {p t t' : ℕ}, p < b.R.k → t ≤ b.top p → t' ≤ b.top p → Back a b θ Rt
    (b.levV p t) x → Back a b θ Rt (b.levV p t') x → b.levV p t = b.levV p t' := by
    intro p t t' hp ht ht' hb hb'
    have hx := h.lev_of_spoke hp ht rfl hb
    have hx' := h.lev_of_spoke hp ht' rfl hb'
    rw [a.level_eq (h.lev_top hp ht) (h.lev_top hp ht') (hx.symm.trans hx')]
  rcases hform hV₁ hy₁ with hH | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
    rcases hform hV₂ hy₂ with hH' | ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
  · exact h.rt_inj (h.rt_of_hub hH hV₁ h₁) (h.rt_of_hub hH' hV₂ h₂)
  · exact (hmix h₂ h₁ hH hV₁ hq ht' rfl).symm
  · exact (hmix h₂ h₁ hH hV₁ hq'lt ht' rfl).symm
  · exact hmix h₁ h₂ hH' hV₂ hq ht rfl
  · exact hsame hq ht ht' h₁ h₂
  · exact hpair ht ht' h₁ h₂
  · exact hmix h₁ h₂ hH' hV₂ hq'lt ht rfl
  · exact (hpair ht' ht h₂ h₁).symm
  · exact hsame hq'lt ht ht' h₁ h₂

end Stair

end GraphMinor.GM19
