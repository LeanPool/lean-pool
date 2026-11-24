/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.HubCollar
public import LeanPool.GraphMinor.GM11.EvenCircuit

/-!
# The edges met by the collar of a region

Let `h` be the collar of `exists_hub_collar`. `collar_turn` says that the collar does not turn back
at a
vertex of valency two. `IsHubCollar.shift` moves the start of the collar by one step.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

namespace IsHubCollar

variable {Γ Γ' H : Drawing S} {r : Set S} {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S}
  {h : C(Circle × I, S)}

theorem pos (hc : IsHubCollar Γ Γ' H r n v a s P ε h) : 0 < n := by
  have := hc.two_le
  omega

/-- Periodicity of a sequence with period `n`, reducing the index. -/
theorem mod_eq {α : Type*} {f : ℕ → α} {n : ℕ} (hp : ∀ i, f (i + n) = f i) (i : ℕ) :
    f (i % n) = f i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < n
    · rw [Nat.mod_eq_of_lt hi]
    · have hs : i = (i - n) + n := by omega
      rw [Nat.mod_eq_sub_mod (not_lt.mp hi)]
      by_cases h0 : n = 0
      · subst h0
        simp
      rw [ih (i - n) (by omega)]
      conv_rhs => rw [hs]
      rw [hp]

theorem region_succ_ne (hc : IsHubCollar Γ Γ' H r n v a s P ε h) (i : ℕ) : P i ≠ P (i + 1) := by
  intro heq
  have hn := hc.two_le
  have h₁ : P (i % n) = P ((i + 1) % n) := by
    rw [mod_eq hc.per_P, mod_eq hc.per_P]
    exact heq
  have h₂ := hc.inj _ _ (Nat.mod_lt _ hc.pos) (Nat.mod_lt _ hc.pos) h₁
  rw [Nat.add_mod] at h₂
  rcases Nat.lt_or_ge (i % n + 1) n with h₃ | h₃
  · rw [show 1 % n = 1 from Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h₃] at h₂
    omega
  · have h₄ : i % n + 1 = n := by
      have := Nat.mod_lt i hc.pos
      omega
    rw [show 1 % n = 1 from Nat.mod_eq_of_lt (by omega), h₄, Nat.mod_self] at h₂
    omega

/-- Start the collar one step later. -/
theorem shift (hc : IsHubCollar Γ Γ' H r n v a s P ε h) :
    ∃ h' : C(Circle × I, S), IsHubCollar Γ Γ' H r n (fun i => v (i + 1)) (fun i => a (i + 1))
      (fun i => s (i + 1)) (fun i => P (i + 1)) (fun i => ε (i + 1)) h' ∧
      (∀ z t, h' (z, t) = h (z * Circle.exp (2 * Real.pi / n), t)) := by
  have hn := hc.pos
  have hcn : (0 : ℝ) < n := by exact_mod_cast hn
  let h' : C(Circle × I, S) := ⟨fun p => h (p.1 * Circle.exp (2 * Real.pi / n), p.2), by fun_prop⟩
  have hexp : ∀ (i : ℕ) (u : I), Circle.exp (2 * Real.pi * ((i + u.1) / n)) * Circle.exp
    (2 * Real.pi / n) =
      Circle.exp (2 * Real.pi * (((i + 1 : ℕ) + u.1) / n)) := by
    intro i u
    rw [← Circle.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hmul : ∀ {z z' : Circle}, z * Circle.exp (2 * Real.pi / n) = z' * Circle.exp
    (2 * Real.pi / n) → z = z' :=
    fun h => mul_right_cancel h
  refine ⟨h', ?_, fun _ _ => rfl⟩
  have hbij : Function.Bijective fun p : Circle × I => (p.1 * Circle.exp (2 * Real.pi / n), p.2)
    := by
    refine ⟨fun p q h => ?_, fun q => ⟨(q.1 * (Circle.exp (2 * Real.pi / n))⁻¹, q.2), ?_⟩⟩
    · have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact Prod.ext (hmul h₁) h₂
    · simp
  let g : Circle × I → Circle × I := fun p => (p.1 * Circle.exp (2 * Real.pi / n), p.2)
  have himg : ∀ T : Set I, h' '' {p | p.2 ∈ T} = h '' {p | p.2 ∈ T} := by
    intro T
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨q, rfl⟩ := hbij.2 p
      exact ⟨q, hp, rfl⟩
  refine ⟨hc.two_le, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => hc.edge _,
    fun i => hc.vertex _, fun i => hc.cap _, fun i => hc.ne _, fun i => hc.spoke _,
    fun i => hc.spoke_cap _, fun i => hc.region _, fun i => hc.region_sub _, fun i => hc.edge_cl _,
    fun i => hc.spoke_cl _, ?_, ?_, fun i => hc.ε_cont _, fun i => hc.ε_inj _, fun i => hc.ε_zero _,
    fun i => hc.ε_one _, fun i => hc.ε_range _, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [show i + n + 1 = (i + 1) + n by omega, hc.per_v]
  · simp only [show i + n + 1 = (i + 1) + n by omega, hc.per_a]
  · simp only [show i + n + 1 = (i + 1) + n by omega, hc.per_s]
  · simp only [show i + n + 1 = (i + 1) + n by omega, hc.per_P]
  · simp only [show i + n + 1 = (i + 1) + n by omega, hc.per_ε]
  · intro i j hi hj heq
    have h₁ : P ((i + 1) % n) = P ((j + 1) % n) := by
      rw [mod_eq hc.per_P, mod_eq hc.per_P]
      exact heq
    have h₂ := hc.inj _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h₁
    have h₃ : (i + 1) ≡ (j + 1) [MOD n] := h₂
    have h₄ : i ≡ j [MOD n] := Nat.ModEq.add_right_cancel' 1 h₃
    exact Nat.ModEq.eq_of_lt_of_lt h₄ hi hj
  · intro p hp hpr
    obtain ⟨i, hi, rfl⟩ := hc.all p hp hpr
    by_cases h0 : i = 0
    · subst h0
      exact ⟨n - 1, by omega, by
        rw [show n - 1 + 1 = 0 + n by omega, hc.per_P]⟩
    · exact ⟨i - 1, by omega, by
        rw [show i - 1 + 1 = i by omega]⟩
  · intro i hi u
    change h (_ * _, 0) = _
    rw [hexp]
    by_cases hi' : i + 1 < n
    · exact hc.bottom _ hi' u
    · have hin : i + 1 = n := by omega
      rw [hin]
      have := hc.bottom 0 hn u
      rw [show (((n : ℕ) : ℝ) + u.1) / n = (((0 : ℕ) : ℝ) + u.1) / n + 1 by
        simp only [Nat.cast_zero, zero_add]
        field_simp
        ring, mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one, this]
      have h₂ := hc.per_ε 0
      rw [zero_add] at h₂
      rw [h₂]
  · rintro p hp q hq heq
    have := hc.injOn (show g p ∈ {p | 0 < p.2} from hp) (show g q ∈ {p | 0 < p.2} from hq) heq
    exact hbij.1 this
  · intro p hp
    exact hc.mem_r (g p) hp
  · rw [← hc.range_bottom]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z * Circle.exp (2 * Real.pi / n), rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨z * (Circle.exp (2 * Real.pi / n))⁻¹, ?_⟩
      change h (_ * _, 0) = _
      simp
  · have := himg (Iio 1)
    change rᶜ ∪ h' '' {p | p.2 ∈ Iio 1} |> IsOpen
    rw [this]
    exact hc.isOpen

end IsHubCollar

variable [T2Space S] [ConnectedSpace S] {Γ Γ' : Drawing S}

omit [T2Space S] [ConnectedSpace S] in
/-- No set is an edge of both `Γ` and its radial drawing. -/
theorem not_both_edge (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') {e : Set S} (he : e ∈ Γ.E)
    (he' : e ∈ Γ'.E) : False := by
  obtain ⟨x, hx⟩ := he.1
  have hxU : x ∈ Γ.U ∩ Γ'.U := ⟨(he.2.1 hx).1, (he'.2.1 hx).1⟩
  rw [radial_inter hrad] at hxU
  exact (he.2.1 hx).2 hxU

omit [ConnectedSpace S] in
/-- An edge with two different ends has only one half-edge at a vertex. -/
theorem half_eq (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') {γ : Set S → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {x : S} {k k' : halfEdges (radialUnion hrad) γ x}
    (hke : k.1.1 = k'.1.1) (_he : k.1.1 ∈ Γ.E) (hne : ∃ a b, a ≠ b ∧ closure k.1.1 ∩ Γ.V = {a, b}) :
    k = k' := by
  obtain ⟨a, b, hab, hcap⟩ := hne
  apply Subtype.ext
  refine Prod.ext hke ?_
  by_contra hbb
  have h₁ : γ k.1.1 (endOf k.1.2) = x := k.2.2
  have h₂ : γ k.1.1 (endOf k'.1.2) = x := by
    rw [hke]
    exact k'.2.2
  have hall : ∀ c, γ k.1.1 (endOf c) = x := by
    intro c
    have : c = k.1.2 ∨ c = k'.1.2 := by
      cases c <;> cases hk : k.1.2 <;> cases hk' : k'.1.2 <;> simp_all
    rcases this with rfl | rfl
    · exact h₁
    · exact h₂
  have hcapH := closure_inter_V_eq hγ k.2.1
  have hmem : ∀ z, z ∈ closure k.1.1 ∩ Γ.V → z = x := by
    intro z hz
    have hzH : z ∈ closure k.1.1 ∩ (radialUnion hrad).V := by
      refine ⟨hz.1, ?_⟩
      rw [radialUnion_V]
      exact radial_V hrad hz.2
    rw [hcapH] at hzH
    rcases hzH with h | h
    · exact h.trans (hall _)
    · exact (mem_singleton_iff.mp h).trans (hall _)
  have ha : a ∈ closure k.1.1 ∩ Γ.V := by rw [hcap]; simp
  have hb : b ∈ closure k.1.1 ∩ Γ.V := by rw [hcap]; simp
  exact hab ((hmem a ha).trans (hmem b hb).symm)

/-- **The collar does not turn back** at a vertex with another edge. -/
theorem collar_turn (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty)
    (hloop : ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) {r : Set S} {n : ℕ} {v : ℕ → S}
    {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar Γ Γ' (radialUnion hrad) r n v a s P ε h) (i : ℕ) {g : Set S} (hg : g ∈ Γ.E)
    (hvg : v (i + 1) ∈ closure g) (hga : g ≠ a i) : a (i + 1) ≠ a i := by
  classical
  intro heq
  have hne : Nonempty S := ⟨v 0⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  set x := v (i + 1) with hx
  have hxV : x ∈ Γ.V := hc.vertex _
  have hxH : x ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact radial_V hrad hxV
  obtain ⟨next, ρ, Pc, Wc, Qc, τc, hsec⟩ := exists_sectors hS _ hγ hxH
    (two_half_edges hrad hS hmax hE hγ hxV)
  have hcor := IsSectors.corners hsec
  obtain ⟨c, -, hcap⟩ := hc.spoke_cap (i + 1)
  have hxs : x ∈ closure (s (i + 1)) := by
    have : x ∈ closure (s (i + 1)) ∩ Γ'.V := by rw [hcap]; simp [hx]
    exact this.1
  have hsH : s (i + 1) ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr (hc.spoke _)
  obtain ⟨b, hb⟩ := exists_end_eq hγ hsH hxH hxs
  let φ : halfEdges (radialUnion hrad) γ x := ⟨(s (i + 1), b), hsH, hb⟩
  obtain ⟨k', hk'⟩ := next_surjective hcor φ
  have hφs : φ.1.1 = s (i + 1) := rfl
  have e₁ := IsCorners.sides hcor k' (P i) (hc.region i) (by rw [hk']; exact (hc.spoke_cl i).2)
  have e₂ := IsCorners.sides hcor k' (P (i + 1)) (hc.region _) (by rw [hk']; exact
    (hc.spoke_cl _).1)
  rw [hk'] at e₁ e₂
  have hPne := hc.region_succ_ne i
  have halt₁ := corner_alternates hrad hS hmax hE hγ hxV hsec k'
  have halt₂ := corner_alternates hrad hS hmax hE hγ hxV hsec φ
  rw [hk'] at halt₁
  have hk'E : k'.1.1 ∈ Γ.E := by
    rcases halt₁ with h' | h'
    · exact (not_both_edge hrad h'.2 (hc.spoke _)).elim
    · exact h'.1
  have hnE : (next φ).1.1 ∈ Γ.E := by
    rcases halt₂ with h' | h'
    · exact h'.2
    · exact (not_both_edge hrad h'.1 (hc.spoke _)).elim
  have hcl₁ : k'.1.1 ⊆ closure (ρ k') := by
    obtain ⟨l, hl⟩ := next_surjective hcor k'
    have := IsCorners.right hcor l
    rwa [hl] at this
  have hcl₂ : (next φ).1.1 ⊆ closure (ρ φ) := IsCorners.left hcor φ
  have hae₁ : a i ⊆ closure (P i) := hc.edge_cl i
  have hae₂ : a i ⊆ closure (P (i + 1)) := heq ▸ hc.edge_cl (i + 1)
  have hρ₁ : a i ⊆ closure (ρ k') := by
    rcases e₁ with h₁ | h₁
    · exact h₁ ▸ hae₁
    · rcases e₂ with h₂ | h₂
      · exact h₂ ▸ hae₂
      · exact (hPne (h₁.trans h₂.symm)).elim
  have hρ₂ : a i ⊆ closure (ρ φ) := by
    rcases e₁ with h₁ | h₁
    · rcases e₂ with h₂ | h₂
      · exact (hPne (h₁.trans h₂.symm)).elim
      · exact h₂ ▸ hae₂
    · exact h₁ ▸ hae₁
  obtain ⟨e₀, he₀, -, huniq, -⟩ := face_edge hrad hS hmax hE (IsCorners.region hcor k')
  obtain ⟨e₃, he₃, -, huniq', -⟩ := face_edge hrad hS hmax hE (IsCorners.region hcor φ)
  have h₁ : k'.1.1 = a i := (huniq _ hk'E hcl₁).trans (huniq _ (hc.edge i) hρ₁).symm
  have h₂ : (next φ).1.1 = a i := (huniq' _ hnE hcl₂).trans (huniq' _ (hc.edge i) hρ₂).symm
  have hnk : next φ = k' := half_eq hrad hγ (h₂.trans h₁.symm) hnE (hloop _ hnE)
  have hall : ∀ z, z = φ ∨ z = k' := by
    intro z
    have hreach := IsCorners.reach hcor φ z
    induction hreach with
    | refl => exact Or.inl rfl
    | tail _ h ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (h.trans hnk)
      · exact Or.inl (h.trans hk')
  have hgH : g ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl hg
  obtain ⟨b', hb'⟩ := exists_end_eq hγ hgH hxH hvg
  rcases hall ⟨(g, b'), hgH, hb'⟩ with h₃ | h₃
  · have : g = s (i + 1) := congrArg (fun z => z.1.1) h₃
    exact not_both_edge hrad hg (this ▸ hc.spoke _)
  · have : g = k'.1.1 := congrArg (fun z => z.1.1) h₃
    exact hga (this.trans h₁)

end GraphMinor.GM11
