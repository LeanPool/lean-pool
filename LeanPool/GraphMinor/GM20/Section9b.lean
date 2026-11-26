/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9a

/-!
# Graph Minors XX, Section 9: a linear inflation around a cuff

The proof of (9.1) uses that for each node `n` on a cuff `Θ`, the nodes of `ζ(n)` on `Θ` form an
interval of `Θ`, in the same cyclic order as the nodes of `Γ`. This file proves it.

An arc of `Θ` determines the angle where it starts (`eq_of_immediatelyPrecedes`). Hence the third
condition of a linear inflation says that if `ζ(cell m) = cell' m'`, then `pos' m'` lies in `ζ(pos
m)`
and `pos' (m' + 1)` lies in `ζ(pos (m + 1))` (`image_cell`). We use the orientation of `Θ` given by
`f` or its reverse, according to which node of `cell m` is the tail.

Assume `ζ` maps the last cell of one cycle to the last cell of the other. We walk around the cycle
of
`Γ'` and count the image cells passed so far, which gives a function `L = liftIdx` from the indices
of `Γ'` to the indices of `Γ`. Then `pos' m'` lies in `ζ(pos (L m'))` for each `m'`
(`IsLift.pos_mem`), and `L` goes once around (`IsLift.lift_last`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- The node `pos m` of a cycle. -/
noncomputable def CuffCycle.pos {Γ : Painting S} {Θ : Set S} {f : Circle ≃ₜ Θ} (C : CuffCycle Γ f)
    (m : ℕ) : S :=
  GM19.cuffPoint f (C.T m)

/-- An arc of a cuff determines the point where it starts. -/
theorem eq_of_immediatelyPrecedes {Θ : Set S} {f : Circle ≃ₜ Θ} {n : S} {a b : ℝ} (hab : a < b)
    (hb : b ≤ a + 2 * Real.pi) (h : GM19.ImmediatelyPrecedes f n (GM19.cuffPoint f '' Ioo a b)) :
    n = GM19.cuffPoint f a := by
  obtain ⟨t₀, t₁, h₀, h₁, rfl, hA⟩ := h
  by_contra hne
  have hpi := Real.pi_pos
  obtain ⟨r, hr, hre⟩ := exists_cuffPoint_eq f t₀ (cuffPoint_mem f a)
  have hnot : GM19.cuffPoint f a ∉ GM19.cuffPoint f '' Ioo a b := by
    rintro ⟨t, ht, hte⟩
    have := eq_of_exp_eq ((cuffPoint_eq_iff f).mp hte.symm) ht.1.le (by linarith [ht.2])
    exact absurd this ht.1.ne
  have hrt : t₁ ≤ r := by
    by_contra hc
    have hr₀ : t₀ < r := lt_of_le_of_ne hr.1 fun heq ↦ hne (by rw [heq, hre])
    exact hnot (hA ▸ ⟨r, ⟨hr₀, not_le.mp hc⟩, hre⟩)
  obtain ⟨ε, hε₀, hε₁, hε₂⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < b - a ∧ ε < t₀ + 2 * Real.pi - r :=
    ⟨min (b - a) (t₀ + 2 * Real.pi - r) / 2, by
      have h₃ : 0 < b - a := by linarith
      have h₄ : 0 < t₀ + 2 * Real.pi - r := by linarith [hr.2]
      constructor
      · positivity
      · constructor
        · have := min_le_left (b - a) (t₀ + 2 * Real.pi - r)
          have : 0 < min (b - a) (t₀ + 2 * Real.pi - r) := lt_min h₃ h₄
          linarith
        · have := min_le_right (b - a) (t₀ + 2 * Real.pi - r)
          have : 0 < min (b - a) (t₀ + 2 * Real.pi - r) := lt_min h₃ h₄
          linarith⟩
  have hmem : GM19.cuffPoint f (a + ε) ∈ GM19.cuffPoint f '' Ioo t₀ t₁ :=
    hA ▸ ⟨a + ε, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨u, hu, hue⟩ := hmem
  have hexp : Circle.exp (a + ε) = Circle.exp (r + ε) := by
    rw [Circle.exp_add, Circle.exp_add, (cuffPoint_eq_iff f).mp hre]
  have hu' : Circle.exp u = Circle.exp (r + ε) := ((cuffPoint_eq_iff f).mp hue).trans hexp
  have huIco : u ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨hu.1.le, by linarith [hu.2]⟩
  have hrIco : r + ε ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨by linarith [hr.1], by linarith⟩
  have heq : u = r + ε := Circle.exp_injOn_Ico (a := t₀) (b := t₀ + 2 * Real.pi) (by simp)
    huIco hrIco hu'
  linarith [hu.2]

/-- The reverse parametrization of a cuff. -/
noncomputable def revParam {Θ : Set S} (f : Circle ≃ₜ Θ) : Circle ≃ₜ Θ :=
  (Homeomorph.inv Circle).trans f

theorem cuffPoint_revParam {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) :
    GM19.cuffPoint (revParam f) t = GM19.cuffPoint f (-t) := by
  simp [GM19.cuffPoint, revParam, Circle.exp_neg]

theorem image_revParam {Θ : Set S} (f : Circle ≃ₜ Θ) (a b : ℝ) :
    GM19.cuffPoint (revParam f) '' Ioo (-b) (-a) = GM19.cuffPoint f '' Ioo a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (cuffPoint_revParam f t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by
      rw [cuffPoint_revParam, neg_neg]⟩

section Cycle

variable {Γ : Painting S} {Θ : Set S} {f : Circle ≃ₜ Θ} (C : CuffCycle Γ f)

namespace CuffCycle

theorem pos_add (m : ℕ) : C.pos (m + C.k) = C.pos m := by
  simp only [pos, C.T_add]
  exact cuffPoint_add f _

theorem pos_mod (m : ℕ) : C.pos (m % C.k) = C.pos m := by
  have hm : m = m % C.k + (m / C.k) * C.k := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div m C.k).symm
  conv_rhs => rw [hm]
  simp only [pos, T_add_mul C.T_add]
  exact (cuffPoint_add_mul f _ _).symm

theorem cell_mod (m : ℕ) : C.cell (m % C.k) = C.cell m := by
  have key : ∀ a q, C.cell (a + q * C.k) = C.cell a := by
    intro a q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, C.cell_add, ih]
  have hm : m = m % C.k + (m / C.k) * C.k := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div m C.k).symm
  conv_rhs => rw [hm]
  exact (key _ _).symm

theorem k_pos : 0 < C.k := by
  have := C.two_le
  omega

theorem pos_ne {m m' : ℕ} (h₁ : m < m') (h₂ : m' < m + C.k) : C.pos m ≠ C.pos m' := by
  intro heq
  have h₃ : C.T m' < C.T m + 2 * Real.pi := by
    rw [← C.T_add]
    exact C.strictMono h₂
  exact (C.strictMono h₁).ne (eq_of_exp_eq ((cuffPoint_eq_iff f).mp heq) (C.strictMono h₁).le h₃)

theorem mod_eq_of_pos_eq {a b : ℕ} (h : C.pos a = C.pos b) : a % C.k = b % C.k := by
  have hk := C.k_pos
  have h₁ : C.pos (a % C.k) = C.pos (b % C.k) := by rw [pos_mod, pos_mod, h]
  have ha := Nat.mod_lt a hk
  have hb := Nat.mod_lt b hk
  rcases lt_trichotomy (a % C.k) (b % C.k) with h₂ | h₂ | h₂
  · exact absurd h₁ (C.pos_ne h₂ (by omega))
  · exact h₂
  · exact absurd h₁.symm (C.pos_ne h₂ (by omega))

theorem cell_eq_of_pos_eq {a b : ℕ} (h : C.pos a = C.pos b) : C.cell a = C.cell b := by
  rw [← C.cell_mod a, ← C.cell_mod b, C.mod_eq_of_pos_eq h]

theorem mem_N (m : ℕ) : C.pos m ∈ Γ.N := C.pos_mem m

theorem mem_cuff (m : ℕ) : C.pos m ∈ Θ := cuffPoint_mem f _

theorem pos_ne_succ (m : ℕ) : C.pos m ≠ C.pos (m + 1) :=
  C.pos_ne (Nat.lt_succ_self m) (by have := C.two_le; omega)

theorem meets (m : ℕ) : (C.cell m ∩ Θ).Nonempty := by
  have hlt := C.strictMono (Nat.lt_succ_self m)
  rw [C.cell_inter]
  obtain ⟨t, ht⟩ := nonempty_Ioo.mpr hlt
  exact ⟨_, t, ht, rfl⟩

theorem T_succ_le (m : ℕ) : C.T (m + 1) ≤ C.T m + 2 * Real.pi := by
  rw [← C.T_add]
  exact C.strictMono.monotone (by have := C.two_le; omega)

theorem inOrder {m₁ m₂ m₃ m₄ : ℕ} (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) (h₃ : m₃ ≤ m₄) (h₄ : m₄
  ≤ m₁ + C.k) :
    GM19.InOrderOn Θ (C.pos m₁) (C.pos m₂) (C.pos m₃) (C.pos m₄) :=
  ⟨f, C.T m₁, C.T m₂, C.T m₃, C.T m₄, C.strictMono.monotone h₁, C.strictMono.monotone h₂,
    C.strictMono.monotone h₃, by rw [← C.T_add]; exact C.strictMono.monotone h₄, rfl, rfl, rfl, rfl⟩

theorem precedes (m : ℕ) : GM19.ImmediatelyPrecedes f (C.pos m) (C.cell m ∩ Θ) :=
  ⟨C.T m, C.T (m + 1), C.strictMono (Nat.lt_succ_self m), C.T_succ_le m, rfl, C.cell_inter m⟩

theorem precedes_rev (m : ℕ) :
    GM19.ImmediatelyPrecedes (revParam f) (C.pos (m + 1)) (C.cell m ∩ Θ) := by
  refine ⟨-C.T (m + 1), -C.T m, ?_, ?_, ?_, ?_⟩
  · linarith [C.strictMono (Nat.lt_succ_self m)]
  · linarith [C.T_succ_le m]
  · rw [cuffPoint_revParam, neg_neg]
    rfl
  · rw [image_revParam]
    exact C.cell_inter m

/-- The march of the cell `cell m` is `pos m, pos (m + 1)`, or the reverse. -/
theorem γ_eq (m : ℕ) : Γ.γ (C.cell m) = [C.pos m, C.pos (m + 1)] ∨
    Γ.γ (C.cell m) = [C.pos (m + 1), C.pos m] := by
  have hset := Γ.γ_set _ (C.cell_mem m)
  have hnd := Γ.γ_nodup _ (C.cell_mem m)
  have hne := C.pos_ne_succ m
  have ht : {n | n ∈ Γ.γ (C.cell m)} = {C.pos m, C.pos (m + 1)} := hset.trans (C.tilde_eq m)
  have h₁ : C.pos m ∈ Γ.γ (C.cell m) := by
    have : C.pos m ∈ {n | n ∈ Γ.γ (C.cell m)} := ht ▸ Or.inl rfl
    exact this
  have h₂ : C.pos (m + 1) ∈ Γ.γ (C.cell m) := by
    have : C.pos (m + 1) ∈ {n | n ∈ Γ.γ (C.cell m)} := ht ▸ Or.inr rfl
    exact this
  have hsub : ∀ n ∈ Γ.γ (C.cell m), n = C.pos m ∨ n = C.pos (m + 1) := fun n hn ↦ by
    have : n ∈ {n | n ∈ Γ.γ (C.cell m)} := hn
    rw [ht] at this
    exact this
  generalize Γ.γ (C.cell m) = l at *
  match l, hnd, h₁, h₂, hsub with
  | [], _, h₁, _, _ => simp at h₁
  | [x], _, h₁, h₂, _ =>
    simp only [List.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  | [x, y], hnd, h₁, h₂, _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hne
    · exact Or.inl (by rw [h₁, h₂])
    · exact Or.inr (by rw [h₁, h₂])
    · exact absurd (h₁.trans h₂.symm) hne
  | x :: y :: z :: l, hnd, _, _, hsub =>
    exfalso
    have hxy := (List.nodup_cons.mp hnd).1
    have hyz := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    simp only [List.mem_cons, not_or] at hxy hyz
    have hx := hsub x (by simp)
    have hy := hsub y (by simp)
    have hz := hsub z (by simp)
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
      first
      | exact hxy.1 (hx.trans hy.symm)
      | exact hxy.2.1 (hx.trans hz.symm)
      | exact hyz.1 (hy.trans hz.symm)

end CuffCycle

end Cycle

section Inflation

variable {Γ Γ' : Painting S} {ζn : S → Set S} {ζc : Set S → Set S} {Θ : Set S} {f : Circle ≃ₜ Θ}
  (hζ : IsLinearInflation Γ Γ' ζn ζc) (hΘ : Θ ∈ cuffs S) (C : CuffCycle Γ f) (C' : CuffCycle Γ' f)

include hζ hΘ in
/-- If `ζ(cell m) = cell' m'`, the nodes `pos' m'` and `pos' (m' + 1)` lie in `ζ(pos m)` and
`ζ(pos (m + 1))`. -/
theorem image_cell {m m' : ℕ} (h : ζc (C.cell m) = C'.cell m') :
    C'.pos m' ∈ ζn (C.pos m) ∧ C'.pos (m' + 1) ∈ ζn (C.pos (m + 1)) := by
  have hc := C.cell_mem m
  have hne := C.pos_ne_succ m
  have hne' := C'.pos_ne_succ m'
  have hstart : ∀ {g : Circle ≃ₜ Θ} {n n' : S}, (Γ.γ (C.cell m)).head? = some n →
      (Γ'.γ (C'.cell m')).head? = some n' → GM19.ImmediatelyPrecedes g n (C.cell m ∩ Θ) →
      GM19.ImmediatelyPrecedes g n' (C'.cell m' ∩ Θ) := by
    intro g n n' h₁ h₂ h₃
    have := hζ.orientation _ hc Θ hΘ (C.meets m) g n n' h₁ (h ▸ h₂) h₃
    rwa [h] at this
  have hnodes : ∀ (a b a' b' : S), Γ.γ (C.cell m) = [a, b] → Γ'.γ (C'.cell m') = [a', b'] →
      a ∈ Γ.N → b ∈ Γ.N → a' ∈ ζn a ∧ b' ∈ ζn b := by
    intro a b a' b' h₁ h₂ ha hb
    have h₃ := hζ.nodes a ha _ hc 0 (by rw [h₁]; simp) (by rw [h, h₂]; simp)
    have h₄ := hζ.nodes b hb _ hc 1 (by rw [h₁]; simp) (by rw [h, h₂]; simp)
    simp only [h, h₁, h₂] at h₃ h₄
    exact ⟨h₃.mp (by simp), h₄.mp (by simp)⟩
  have hN := C.mem_N m
  have hN' := C.mem_N (m + 1)
  rcases C.γ_eq m with h₁ | h₁
  · rcases C'.γ_eq m' with h₂ | h₂
    · exact hnodes _ _ _ _ h₁ h₂ hN hN'
    · have h₃ := hstart (n := C.pos m) (n' := C'.pos (m' + 1)) (g := f) (by rw [h₁]; rfl)
        (by rw [h₂]; rfl) (C.precedes m)
      rw [C'.cell_inter] at h₃
      exact absurd (eq_of_immediatelyPrecedes (C'.strictMono (Nat.lt_succ_self m'))
        (C'.T_succ_le m') h₃).symm hne'
  · have hlt := C'.strictMono (Nat.lt_succ_self m')
    have hrev : C'.cell m' ∩ Θ =
        GM19.cuffPoint (revParam f) '' Ioo (-C'.T (m' + 1)) (-C'.T m') := by
      rw [image_revParam]
      exact C'.cell_inter m'
    rcases C'.γ_eq m' with h₂ | h₂
    · have h₃ := hstart (n := C.pos (m + 1)) (n' := C'.pos m') (g := revParam f)
        (by rw [h₁]; rfl) (by rw [h₂]; rfl) (C.precedes_rev m)
      rw [hrev] at h₃
      have h₄ := eq_of_immediatelyPrecedes (by linarith) (by linarith [C'.T_succ_le m']) h₃
      rw [cuffPoint_revParam, neg_neg] at h₄
      exact absurd h₄ hne'
    · obtain ⟨h₃, h₄⟩ := hnodes _ _ _ _ h₁ h₂ hN' hN
      exact ⟨h₄, h₃⟩

open Classical in
/-- The number of image cells among the first `m` cells of the cycle of `Γ'`. -/
noncomputable def liftIdx (Γ : Painting S) (ζc : Set S → Set S) (C' : CuffCycle Γ' f) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if C'.cell m ∈ ζc '' Γ.C then liftIdx Γ ζc C' m + 1 else liftIdx Γ ζc C' m

include hζ in
/-- Two nodes in one `ζ(n)` are over the same node. -/
theorem pos_eq_of_mem {m₁ m₂ : ℕ} {n' : S} (h₁ : n' ∈ ζn (C.pos m₁)) (h₂ : n' ∈ ζn (C.pos m₂)) :
    C.pos m₁ = C.pos m₂ := by
  by_contra hne
  exact Set.disjoint_left.mp (hζ.node_disjoint _ (C.mem_N m₁) _ (C.mem_N m₂) hne) h₁ h₂

theorem CuffCycle.pos_succ_eq_of_pos_eq {Γ : Painting S} {f : Circle ≃ₜ Θ} (C : CuffCycle Γ f)
    {a b : ℕ} (h : C.pos a = C.pos b) : C.pos (a + 1) = C.pos (b + 1) := by
  have h₁ := C.mod_eq_of_pos_eq h
  rw [← C.pos_mod (a + 1), ← C.pos_mod (b + 1), Nat.add_mod, h₁, ← Nat.add_mod]

include hΘ in
theorem cuff_subset_bd : Θ ⊆ bd S := by
  obtain ⟨p, hp, rfl⟩ := hΘ
  exact connectedComponentIn_subset _ _

include hζ hΘ in
/-- A cell of the cycle of `Γ'` that lies in the image of `ζ` is the image of a cell of the cycle of
`Γ`. -/
theorem exists_cell_of_image {m' : ℕ} (h : C'.cell m' ∈ ζc '' Γ.C) :
    ∃ l < C.k, ζc (C.cell l) = C'.cell m' := by
  obtain ⟨c, hc, hcz⟩ := h
  obtain ⟨l, hl, rfl⟩ := C.exists_cell c hc
    ((hζ.borders_iff c hc Θ hΘ).mpr (by rw [hcz]; exact C'.meets m'))
  exact ⟨l, hl, hcz⟩

include hζ hΘ in
/-- The walk around the cycle of `Γ'`, for an inflation that maps the last cell of the cycle of `Γ`
to
the last cell of the cycle of `Γ'`. -/
theorem exists_lift (hcut : ζc (C.cell (C.k - 1)) = C'.cell (C'.k - 1)) :
    ∃ L : ℕ → ℕ, L 0 = 0 ∧ Monotone L ∧ (∀ m', C'.pos m' ∈ ζn (C.pos (L m'))) ∧
      (∀ m', (L (m' + 1) = L m' ∧ C'.cell m' ∉ ζc '' Γ.C) ∨
        (L (m' + 1) = L m' + 1 ∧ ζc (C.cell (L m')) = C'.cell m')) ∧
      (∀ m' < C'.k, L m' < C.k) ∧ (∀ l < C.k, ∃ m' < C'.k, L m' = l) := by
  classical
  have hk := C.two_le
  have hk' := C'.two_le
  let L := liftIdx Γ ζc C'
  have hsucc : ∀ m, L (m + 1) = if C'.cell m ∈ ζc '' Γ.C then L m + 1 else L m := fun _ ↦ rfl
  have hbase : C'.pos 0 ∈ ζn (C.pos 0) := by
    have h₁ := (image_cell hζ hΘ C C' hcut).2
    rw [show C'.k - 1 + 1 = 0 + C'.k by omega, show C.k - 1 + 1 = 0 + C.k by omega, C'.pos_add,
      C.pos_add] at h₁
    exact h₁
  have hstep : ∀ m', C'.pos m' ∈ ζn (C.pos (L m')) → C'.cell m' ∈ ζc '' Γ.C →
      ζc (C.cell (L m')) = C'.cell m' ∧ C'.pos (m' + 1) ∈ ζn (C.pos (L m' + 1)) := by
    intro m' h₁ h₂
    obtain ⟨l, -, hl⟩ := exists_cell_of_image hζ hΘ C C' h₂
    obtain ⟨h₃, h₄⟩ := image_cell hζ hΘ C C' hl
    have heq := pos_eq_of_mem hζ C h₃ h₁
    exact ⟨by rw [← hl, C.cell_eq_of_pos_eq heq], C.pos_succ_eq_of_pos_eq heq ▸ h₄⟩
  have hpos : ∀ m', C'.pos m' ∈ ζn (C.pos (L m')) := by
    intro m'
    induction m' with
    | zero => exact hbase
    | succ m' ih =>
      rw [hsucc]
      split_ifs with himg
      · exact (hstep m' ih himg).2
      · obtain ⟨y, hy, hyΘ⟩ := C'.meets m'
        obtain ⟨n, hn, hsub⟩ := hζ.border_cell _ (C'.cell_mem m') ⟨y, hy, cuff_subset_bd hΘ hyΘ⟩
          himg
        have h₁ : C'.pos m' ∈ tilde (C'.cell m') := by
          rw [C'.tilde_eq]
          exact Or.inl rfl
        have h₂ : C'.pos (m' + 1) ∈ tilde (C'.cell m') := by
          rw [C'.tilde_eq]
          exact Or.inr rfl
        have heq : n = C.pos (L m') := by
          by_contra hne
          exact Set.disjoint_left.mp (hζ.node_disjoint _ hn _ (C.mem_N _) hne) (hsub h₁) ih
        exact heq ▸ hsub h₂
  have hmono : Monotone L := monotone_nat_of_le_succ fun m ↦ by
    rw [hsucc]
    split_ifs <;> omega
  have hcard : ∀ n, L n = ((Finset.range n).filter fun m ↦ C'.cell m ∈ ζc '' Γ.C).card := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hsucc, Finset.range_add_one, Finset.filter_insert]
      split_ifs with himg
      · rw [Finset.card_insert_of_notMem (by simp), ih]
      · exact ih
  have hle : L C'.k ≤ C.k := by
    rw [hcard]
    refine (Finset.card_le_card_of_injOn (fun m ↦ L m % C.k) (fun m _ ↦ ?_) ?_).trans_eq
      (Finset.card_range C.k)
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ C.k_pos))
    · intro a ha b hb hab
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨hb₁, hb₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      have ha₃ := Finset.mem_range.mp ha₁
      have hb₃ := Finset.mem_range.mp hb₁
      have h₁ := (hstep a (hpos a) ha₂).1
      have h₂ := (hstep b (hpos b) hb₂).1
      have h₃ : C'.cell a = C'.cell b := by
        rw [← h₁, ← h₂, ← C.cell_mod (L a), ← C.cell_mod (L b)]
        exact congrArg (fun i ↦ ζc (C.cell i)) hab
      rcases lt_trichotomy a b with h₄ | h₄ | h₄
      · exact absurd h₃ (C'.cell_ne a b h₄ (by omega))
      · exact h₄
      · exact absurd h₃.symm (C'.cell_ne b a h₄ (by omega))
  have hcutimg : C'.cell (C'.k - 1) ∈ ζc '' Γ.C := ⟨_, C.cell_mem _, hcut⟩
  have hlast : L C'.k = L (C'.k - 1) + 1 := by
    conv_lhs => rw [show C'.k = C'.k - 1 + 1 by omega]
    rw [hsucc, ite_eq_left hcutimg]
  have hfull : L C'.k = C.k := by
    have h₁ : C.pos (L C'.k) = C.pos 0 := by
      have h₂ := hpos C'.k
      have h₃ : C'.pos C'.k = C'.pos 0 := by
        have := C'.pos_add 0
        rwa [Nat.zero_add] at this
      rw [h₃] at h₂
      exact pos_eq_of_mem hζ C h₂ hbase
    have h₂ := C.mod_eq_of_pos_eq h₁
    rw [Nat.zero_mod] at h₂
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h₂
    rcases q with _ | q
    · omega
    · have : C.k * (q + 1) = C.k * q + C.k := by ring
      have h₄ : 0 ≤ C.k * q := Nat.zero_le _
      have : q = 0 := by
        by_contra hq0
        have : C.k * 1 ≤ C.k * q := Nat.mul_le_mul_left _ (by omega)
        omega
      subst this
      omega
  have hreach : ∀ n l, l ≤ L n → ∃ m' ≤ n, L m' = l := by
    intro n l
    induction n with
    | zero => exact fun h ↦ ⟨0, le_rfl, by have : L 0 = 0 := rfl; omega⟩
    | succ n ih =>
      intro h
      by_cases h₁ : l ≤ L n
      · obtain ⟨m', h₂, h₃⟩ := ih h₁
        exact ⟨m', by omega, h₃⟩
      · have h₂ : L (n + 1) ≤ L n + 1 := by
          rw [hsucc]
          split_ifs <;> omega
        exact ⟨n + 1, le_rfl, by omega⟩
  refine ⟨L, rfl, hmono, hpos, fun m' ↦ ?_, fun m' hm' ↦ ?_, fun l hl ↦ ?_⟩
  · by_cases himg : C'.cell m' ∈ ζc '' Γ.C
    · exact Or.inr ⟨by rw [hsucc, ite_eq_left himg], (hstep m' (hpos m') himg).1⟩
    · exact Or.inl ⟨by rw [hsucc, ite_eq_right himg], himg⟩
  · have := hmono (show m' ≤ C'.k - 1 by omega)
    omega
  · obtain ⟨m', h₁, h₂⟩ := hreach C'.k l (by omega)
    refine ⟨m', ?_, h₂⟩
    rcases h₁.eq_or_lt with h₃ | h₃
    · subst h₃
      omega
    · exact h₃

end Inflation

end GraphMinor.GM20
