/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14ac

/-!
# Graph Minors XIX, Section 14: what each painting of the sequence records

At each singular place of a rim we record a finite amount of data, and the colours of the long sides
record the sectors of the regular places. All of this
has only finitely many values, once `ρ` is bounded. So an infinite subsequence has the same data
everywhere.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The data at a singular place. -/
abbrev ZData := Bool × WheelFrame.CodeT × ℕ × Bool

/-- The values of the data, for wheels of radius at most `b`. -/
def zdataSet (b : ℕ) : Set ZData := {x | x.2.1 ∈ codeSet (2 * b + 3) ∧ x.2.2.1 ≤ 2 * b + 2}

theorem finite_zdataSet (b : ℕ) : (zdataSet b).Finite := by
  refine (((finite_univ (α := Bool)).prod ((finite_codeSet (2 * b + 3)).prod ((finite_Iic
    (2 * b + 2)).prod (finite_univ (α := Bool)))))).subset ?_
  rintro ⟨a, c, l, h⟩ ⟨h₁, h₂⟩
  exact ⟨mem_univ _, h₁, h₂, mem_univ _⟩

theorem codeSet_mono {a b : ℕ} (h : a ≤ b) : codeSet a ⊆ codeSet b := by
  rintro c ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  refine ⟨by omega, by omega, by omega, by omega, h₅.trans (Finset.range_mono (by omega)),
    by omega, fun x hx ↦ ?_⟩
  have := h₇ x hx
  rcases x with x | x
  · exact Nat.le_trans this h
  · exact Nat.le_trans this h

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)

open Classical in
/-- The data at the `p`th place of a rim. -/
noncomputable def zdata (W : ↥s.𝒲) (p : ℕ) : ZData :=
  (decide (p + 1 = (s.fr W).R.k), (s.fr W).code p, (s.fr W).hubList.length, decide
    ((s.fr W).H.V.ncard ≠ 1))

include s

theorem exists_pick {z : ↥Tᶜ} (hz : z ∈ s.markZ) : ∃ W p, p ∈ s.sing W ∧ z = s.zx W p := by
  obtain ⟨W, hz⟩ := mem_iUnion.mp hz
  obtain ⟨p, hp, hz⟩ := mem_iUnion₂.mp hz
  exact ⟨W, p, hp, hz⟩

theorem zx_uniq {W W' : ↥s.𝒲} {p q : ℕ} (hp : p < (s.fr W).R.k) (hq : q < (s.fr W').R.k)
  (h : s.zx W p = s.zx W' q) : W = W' ∧ HEq p q := by
  have e := arcComp_eq_of_mem (s.arc_mem W p) (s.arc_mem W' q) (s.zx_arc W p) (h ▸ s.zx_arc W' q)
  obtain rfl := s.arc_wheel e
  exact ⟨rfl, heq_of_eq (s.arc_pos W hp hq e)⟩

omit s in
/-- A wheel and a place for a singular vertex of `R*`. -/
noncomputable def pick (s : Slice T D) {z : ↥Tᶜ} (hz : z ∈ s.markZ) : ↥s.𝒲 × ℕ :=
  ((s.exists_pick hz).choose, (s.exists_pick hz).choose_spec.choose)

theorem pick_spec {z : ↥Tᶜ} (hz : z ∈ s.markZ) : (s.pick hz).2 ∈ s.sing (s.pick hz).1 ∧ z = s.zx
  (s.pick hz).1 (s.pick hz).2 := (s.exists_pick hz).choose_spec.choose_spec

theorem pick_eq {z : ↥Tᶜ} (hz : z ∈ s.markZ) {W : ↥s.𝒲} {p : ℕ} (hp : p ∈ s.sing W) (e : z
  = s.zx W p) : s.pick hz = (W, p) := by
  obtain ⟨h₁, h₂⟩ := s.pick_spec hz
  obtain ⟨hW, hq⟩ := s.zx_uniq h₁.1 hp.1 (h₂.symm.trans e)
  exact Prod.ext hW (eq_of_heq hq)

omit s in
open Classical in
/-- The data at a point. -/
noncomputable def ztag (s : Slice T D) (z : ↥Tᶜ) : Option ZData := if h : z ∈ s.markZ then some
  (s.zdata (s.pick h).1 (s.pick h).2) else none

theorem ztag_zx {W : ↥s.𝒲} {p : ℕ} (hp : p ∈ s.sing W) : s.ztag (s.zx W p) = some (s.zdata W p)
  := by
  classical
  have hz : s.zx W p ∈ s.markZ := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hp, rfl⟩⟩
  rw [ztag, dite_eq_left hz, s.pick_eq hz hp rfl]

theorem ztag_mem {b : ℕ} (hb : ∀ W, (s.fr W).ρ ≤ b) (z : ↥Tᶜ) : s.ztag z ∈ insert none
  (some '' zdataSet b) := by
  classical
  by_cases hz : z ∈ s.markZ
  · rw [ztag, dite_eq_left hz]
    refine .inr (mem_image_of_mem _ ⟨?_, ?_⟩)
    · exact codeSet_mono (by have := hb (s.pick hz).1; omega) ((s.fr _).code_mem _)
    · have := (s.fr (s.pick hz).1).hubList_length_le
      have := hb (s.pick hz).1
      change (s.fr (s.pick hz).1).hubList.length ≤ _
      omega
  · rw [ztag, dite_eq_right hz]
    exact .inl rfl

omit s in
open Classical in
/-- The direction of the rim on a cuff. -/
noncomputable def cuffDir (s : Slice T D) (C : Set ↥Tᶜ) : Bool :=
  if h : ∃ W : ↥s.𝒲, C = s.cf W then (s.exists_dir h.choose).choose else false

theorem cuffDir_cf (W : ↥s.𝒲) : ∀ i, arcMarch s.isSurface (s.cuffDir (s.cf W)) (s.arc W i)
  = [s.vx W i, s.vx W (i + 1)] := by
  classical
  have h : ∃ W' : ↥s.𝒲, s.cf W = s.cf W' := ⟨W, rfl⟩
  rw [cuffDir, dite_eq_left h]
  have key : ∀ W' : ↥s.𝒲, s.cf W = s.cf W' → W = W' := fun W' e ↦ by
    obtain ⟨x, hx⟩ : (s.cf W).Nonempty := ⟨_, s.vx_cf W 0⟩
    exact s.wheel_eq hx (e ▸ hx)
  have e := key _ h.choose_spec
  have key' : ∀ W' : ↥s.𝒲, W = W' → ∀ i, arcMarch s.isSurface (s.exists_dir W').choose (s.arc W i)
    = [s.vx W i, s.vx W (i + 1)] := by
    rintro _ rfl
    exact (s.exists_dir W).choose_spec
  exact key' _ e

theorem march_arc {ε : Set ↥Tᶜ → Bool} (hε : ∀ C ∈ cuffs ↥Tᶜ, ε C = s.cuffDir C) (W : ↥s.𝒲)
  (i : ℕ) :
    arcMarch s.isSurface (flipOf ε (s.arc W i)) (s.arc W i) = [s.vx W i, s.vx W (i + 1)] := by
  obtain ⟨x, hx, -⟩ := s.arc_reg W i
  rw [flipOf_eq ε (s.cf_mem W.2) ⟨x, hx⟩ (s.arc_cf W i), hε _ (s.cf_mem W.2), s.cuffDir_cf]

end Slice

end GraphMinor.GM19
