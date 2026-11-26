/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordSurface
public import Mathlib.Topology.UniformSpace.Compact

/-!
# First cohomology with local cocycles

For a topological space `X` and an abelian group `A`, a local cocycle is a function `φ : X → X → A`
that adds up on
triples of near points. Two of them are equivalent if near the diagonal their difference is the
difference of a
function on `X`. This is the first Alexander-Spanier cohomology of `X` (see E. Spanier, Algebraic
Topology, Chapter 6,
Section 4). `KCl X A` is the set of classes that vanish on the boundary of `X`. It depends only on
the space, so its
size is unchanged by homeomorphisms (`card_kCl_congr`).

On a closed disc a local cocycle pulled back from `X` has a primitive (`exists_prim`), by summing it
along a radius.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u v

section Basic

variable {X : Type u} [TopologicalSpace X] {X' : Type v} [TopologicalSpace X'] {A : Type}
  [AddCommGroup A]

/-- A set that is a neighbourhood of each point of the diagonal. -/
def NearDiag (N : Set (X × X)) : Prop := ∀ x, N ∈ 𝓝 (x, x)

theorem NearDiag.inter {N N' : Set (X × X)} (h : NearDiag N) (h' : NearDiag N') : NearDiag (N ∩ N')
  :=
  fun x => Filter.inter_mem (h x) (h' x)

theorem NearDiag.mono {N N' : Set (X × X)} (h : NearDiag N) (hs : N ⊆ N') : NearDiag N' :=
  fun x => Filter.mem_of_superset (h x) hs

theorem NearDiag.mem {N : Set (X × X)} (h : NearDiag N) (x : X) : (x, x) ∈ N := mem_of_mem_nhds
  (h x)

/-- A local cocycle. The group `A` need not be commutative. -/
def IsCoc {A : Type} [Add A] (φ : X → X → A) : Prop :=
  ∃ N : Set (X × X), NearDiag N ∧ ∀ x y z, (x, y) ∈ N → (y, z) ∈ N → (x, z) ∈ N → φ x y + φ y z
    = φ x z

/-- Near the diagonal the difference of `φ` and `φ'` is the difference of a function. -/
def CohRel (φ φ' : X → X → A) : Prop :=
  ∃ (h : X → A) (N : Set (X × X)), NearDiag N ∧ ∀ x y, (x, y) ∈ N → φ x y - φ' x y = h y - h x

/-- Near the diagonal of the boundary, `φ` is the difference of a function. -/
def BdTriv {A : Type} [AddGroup A] (φ : X → X → A) : Prop :=
  ∃ (h : X → A) (N : Set (X × X)), NearDiag N ∧ ∀ x ∈ bd X, ∀ y ∈ bd X, (x, y) ∈ N → φ x y
    = -h x + h y

/-- The local cocycles that vanish on the boundary. -/
def KSet (X : Type u) [TopologicalSpace X] (A : Type) [AddCommGroup A] : Set (X → X → A) :=
  {φ | IsCoc φ ∧ BdTriv φ}

theorem CohRel.refl (φ : X → X → A) : CohRel φ φ :=
  ⟨0, univ, fun _ => univ_mem, fun x y _ => by simp⟩

theorem CohRel.symm {φ φ' : X → X → A} (h : CohRel φ φ') : CohRel φ' φ := by
  obtain ⟨g, N, hN, h⟩ := h
  refine ⟨-g, N, hN, fun x y hxy => ?_⟩
  have := h x y hxy
  simp only [Pi.neg_apply]
  rw [← neg_sub (φ x y), this]
  abel

theorem CohRel.trans {φ φ' φ'' : X → X → A} (h : CohRel φ φ') (h' : CohRel φ' φ'') : CohRel φ φ''
  := by
  obtain ⟨g, N, hN, h⟩ := h
  obtain ⟨g', N', hN', h'⟩ := h'
  refine ⟨g + g', N ∩ N', hN.inter hN', fun x y hxy => ?_⟩
  have h1 := h x y hxy.1
  have h2 := h' x y hxy.2
  simp only [Pi.add_apply]
  calc φ x y - φ'' x y = (φ x y - φ' x y) + (φ' x y - φ'' x y) := by abel
    _ = _ := by rw [h1, h2]; abel

/-- The equivalence of local cocycles. -/
def kSetoid (X : Type u) [TopologicalSpace X] (A : Type) [AddCommGroup A] : Setoid (KSet X A) :=
  ⟨fun φ φ' => CohRel φ.1 φ'.1, ⟨fun φ => .refl φ.1, fun h => h.symm, fun h h' => h.trans h'⟩⟩

/-- The classes of local cocycles that vanish on the boundary. -/
def KCl (X : Type u) [TopologicalSpace X] (A : Type) [AddCommGroup A] : Type u := Quotient
  (kSetoid X A)

/-- The pull back of a function of two points. -/
def pbk (e : X → X') (φ : X' → X' → A) : X → X → A := fun x y => φ (e x) (e y)

theorem NearDiag.pull (e : X ≃ₜ X') {N : Set (X' × X')} (h : NearDiag N) :
    NearDiag ((fun p : X × X => (e p.1, e p.2)) ⁻¹' N) := fun x => by
  have hc : Continuous fun p : X × X => (e p.1, e p.2) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (h (e x))

theorem pbk_mem (e : X ≃ₜ X') {φ : X' → X' → A} (h : φ ∈ KSet X' A) : pbk e φ ∈ KSet X A := by
  obtain ⟨⟨N, hN, h1⟩, g, N', hN', h2⟩ := h
  refine ⟨⟨_, hN.pull e, fun x y z h3 h4 h5 => h1 _ _ _ h3 h4 h5⟩, g ∘ e, _, hN'.pull e,
    fun x hx y hy hxy => ?_⟩
  have hb : ∀ {x : X}, x ∈ bd X → e x ∈ bd X' := fun {x} hx => by
    have h3 := image_bd_homeomorph e
    rw [← h3]
    exact mem_image_of_mem _ hx
  exact h2 _ (hb hx) _ (hb hy) hxy

theorem pbk_rel (e : X ≃ₜ X') {φ φ' : X' → X' → A} (h : CohRel φ φ') : CohRel (pbk e φ) (pbk e φ')
  := by
  obtain ⟨g, N, hN, h⟩ := h
  exact ⟨g ∘ e, _, hN.pull e, fun x y hxy => h _ _ hxy⟩

/-- A homeomorphism gives a bijection of the classes. -/
theorem card_kCl_congr (e : X ≃ₜ X') : Nat.card (KCl X A) = Nat.card (KCl X' A) := by
  let s : KSet X' A ≃ KSet X A :=
    { toFun := fun φ => ⟨pbk e φ.1, pbk_mem e φ.2⟩
      invFun := fun φ => ⟨pbk e.symm φ.1, pbk_mem e.symm φ.2⟩
      left_inv := fun φ => Subtype.ext (by
        funext x y
        simp [pbk])
      right_inv := fun φ => Subtype.ext (by
        funext x y
        simp [pbk]) }
  have hs : ∀ a b : KSet X' A, (kSetoid X' A).r a b ↔ (kSetoid X A).r (s a) (s b) := by
    intro a b
    refine ⟨fun h => pbk_rel e h, fun h => ?_⟩
    have h1 : CohRel (pbk e.symm (pbk e a.1)) (pbk e.symm (pbk e b.1)) := pbk_rel e.symm h
    have h2 : ∀ φ : KSet X' A, pbk e.symm (pbk e φ.1) = φ.1 := fun φ => by
      funext x y
      simp [pbk]
    rw [h2, h2] at h1
    exact h1
  exact (Nat.card_congr (Quotient.congr s hs)).symm

end Basic

section Disc

variable {Y : Type u} [TopologicalSpace Y] {A : Type} [AddGroup A]

/-- A primitive of a local cocycle pulled back to the unit disc. -/
def IsPrim (φ : Y → Y → A) (F : ℂ → Y) (g : ℂ → A) : Prop :=
  ∃ ε > 0, ∀ a ∈ closedBall (0 : ℂ) 1, ∀ b ∈ closedBall (0 : ℂ) 1, ‖a - b‖ < ε → φ (F a) (F b)
    = -g a + g b

theorem exists_eps {F : ℂ → Y} {K : Set ℂ} (hK : IsCompact K) (hF : ContinuousOn F K) {N : Set
  (Y × Y)} (hN : NearDiag N) :
    ∃ ε > 0, ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ < ε → (F a, F b) ∈ N := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let M : Set (K × K) := (fun p : K × K => (F p.1, F p.2)) ⁻¹' N
  have hc : Continuous fun p : K × K => (F p.1, F p.2) := by
    have h1 : Continuous fun a : K => F a := hF.comp_continuous continuous_subtype_val fun a => a.2
    exact (h1.comp continuous_fst).prodMk (h1.comp continuous_snd)
  have hM : M ∈ 𝓝ˢ (diagonal K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨a, a'⟩ h
    have h' : a = a' := h
    subst h'
    have h1 := hN (F a)
    have h2 : (fun p : K × K => (F p.1, F p.2)) ⁻¹' N ∈ 𝓝 (a, a) :=
      hc.continuousAt.preimage_mem_nhds h1
    exact h2
  rw [nhdsSet_diagonal_eq_uniformity, Metric.mem_uniformity_dist] at hM
  obtain ⟨ε, h0, h1⟩ := hM
  refine ⟨ε, h0, fun a ha b hb hab => ?_⟩
  exact h1 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (by simpa [Subtype.dist_eq, dist_eq_norm] using hab)

/-- A local cocycle pulled back to the unit disc has a primitive. Sum it along the radius to the
point. -/
theorem exists_prim {φ : Y → Y → A} (hφ : IsCoc φ) {F : ℂ → Y} (hF : ContinuousOn F
  (closedBall 0 1)) :
    ∃ g, IsPrim φ F g := by
  obtain ⟨N, hN, hc⟩ := hφ
  obtain ⟨ε, h0, hε⟩ := exists_eps (isCompact_closedBall 0 1) hF hN
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hmε : 1 / (m : ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hm0]
    have := (div_lt_iff₀ h0).mp hm
    linarith
  let P : ℂ → ℕ → ℂ := fun x k => ((k / m : ℝ) : ℂ) * x
  have hP : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ k ≤ m, P x k ∈ closedBall (0 : ℂ) 1 := by
    intro x hx k hk
    simp only [P, mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at hx ⊢
    have h1 : (k : ℝ) / m ≤ 1 := by
      rw [div_le_one hm0]
      exact_mod_cast hk
    rw [abs_of_nonneg (by positivity)]
    have := norm_nonneg x
    nlinarith
  have hstep : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ k, ‖P x k - P x (k + 1)‖ < ε / 2 := by
    intro x hx k
    have h1 : P x k - P x (k + 1) = ((-1 / m : ℝ) : ℂ) * x := by
      simp only [P]
      push_cast
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
      field_simp
      ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, neg_div, abs_neg,
      abs_of_pos (by positivity)]
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    have := norm_nonneg x
    have h2 : 0 < 1 / (m : ℝ) := by positivity
    nlinarith
  have hrung : ∀ x y, ∀ k ≤ m, ‖P x k - P y k‖ ≤ ‖x - y‖ := by
    intro x y k hk
    have h1 : P x k - P y k = ((k / m : ℝ) : ℂ) * (x - y) := by
      simp only [P]
      push_cast
      ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : (k : ℝ) / m ≤ 1 := by
      rw [div_le_one hm0]
      exact_mod_cast hk
    have := norm_nonneg (x - y)
    nlinarith
  let S : ℂ → ℕ → A := fun x l => Nat.rec 0 (fun k r => r + φ (F (P x k)) (F (P x (k + 1)))) l
  have hS : ∀ x l, S x (l + 1) = S x l + φ (F (P x l)) (F (P x (l + 1))) := fun _ _ => rfl
  refine ⟨fun x => S x m, ε / 2, by positivity, fun x hx y hy hxy => ?_⟩
  have hkey : ∀ l ≤ m, S x l + φ (F (P x l)) (F (P y l)) = φ (F (P x 0)) (F (P y 0)) + S y l := by
    intro l
    induction l with
    | zero => intro _; simp [S]
    | succ l ih =>
      intro hl
      have hl' : l ≤ m := by omega
      have h1 := ih hl'
      rw [hS, hS]
      have hpx := hP x hx l hl'
      have hpx' := hP x hx (l + 1) hl
      have hpy := hP y hy l hl'
      have hpy' := hP y hy (l + 1) hl
      have hr1 := hrung x y l hl'
      have hr2 := hrung x y (l + 1) hl
      have hs1 := hstep x hx l
      have hs2 := hstep y hy l
      have t1 : (F (P x l), F (P x (l + 1))) ∈ N := hε _ hpx _ hpx' (by linarith)
      have t2 : (F (P x (l + 1)), F (P y (l + 1))) ∈ N := hε _ hpx' _ hpy' (by linarith)
      have t3 : (F (P x l), F (P y (l + 1))) ∈ N := hε _ hpx _ hpy' (by
        have h3 : ‖P x l - P y (l + 1)‖ ≤ ‖P x l - P y l‖ + ‖P y l - P y (l + 1)‖ := by
          have := norm_add_le (P x l - P y l) (P y l - P y (l + 1))
          simpa using this
        linarith)
      have t4 : (F (P x l), F (P y l)) ∈ N := hε _ hpx _ hpy (by linarith)
      have t5 : (F (P y l), F (P y (l + 1))) ∈ N := hε _ hpy _ hpy' (by linarith)
      have e1 := hc _ _ _ t1 t2 t3
      have e2 := hc _ _ _ t4 t5 t3
      calc S x l + φ (F (P x l)) (F (P x (l + 1))) + φ (F (P x (l + 1))) (F (P y (l + 1)))
          = S x l + φ (F (P x l)) (F (P y l)) + φ (F (P y l)) (F (P y (l + 1))) := by
            rw [add_assoc, e1, add_assoc, e2]
        _ = _ := by rw [h1, add_assoc]
  have h1 := hkey m le_rfl
  have hPm : ∀ z, P z m = z := fun z => by
    simp only [P]
    rw [div_self hm0.ne']
    simp
  have hP0 : ∀ z, P z 0 = 0 := fun z => by simp [P]
  rw [hPm, hPm, hP0, hP0] at h1
  have hz : φ (F 0) (F 0) = 0 := by
    have h2 := hN.mem (F 0)
    have h3 := hc _ _ _ h2 h2 h2
    exact add_eq_left.mp h3
  rw [hz, zero_add] at h1
  change _ = -S x m + S y m
  rw [← h1, neg_add_cancel_left]

/-- A function that is locally constant on the interval is constant. -/
theorem const_of_near {A : Type} {v : ℝ → A} {ε : ℝ} (h0 : 0 < ε)
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < ε → v s = v t) : ∀ t ∈ Icc
      (0 : ℝ) 1, v t = v 0 := by
  intro t ht
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hle : 1 / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hm0]
    have := (div_lt_iff₀ h0).mp hm
    linarith
  have key : ∀ k ≤ m, v (k / m * t) = v 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      have hmem : ∀ l : ℕ, l ≤ m → (l : ℝ) / m * t ∈ Icc (0 : ℝ) 1 := by
        intro l hl
        have h1 : (l : ℝ) / m ≤ 1 := by
          rw [div_le_one hm0]
          exact_mod_cast hl
        have h2 : (0 : ℝ) ≤ (l : ℝ) / m := by positivity
        exact ⟨mul_nonneg h2 ht.1, by nlinarith [ht.1, ht.2]⟩
      refine hv _ (hmem _ hk) _ (hmem _ (by omega)) ?_
      have h3 : ((k + 1 : ℕ) : ℝ) / m * t - (k : ℝ) / m * t = t / m := by
        push_cast
        field_simp
        ring
      rw [h3, abs_of_nonneg (div_nonneg ht.1 hm0.le)]
      have : t / m ≤ 1 / m := div_le_div_of_nonneg_right ht.2 hm0.le
      linarith
  have h1 := key m le_rfl
  rw [div_self hm0.ne', one_mul] at h1
  exact h1

omit [TopologicalSpace Y] in
theorem IsPrim.sub_eq {φ : Y → Y → A} {F : ℂ → Y} {g g' : ℂ → A} (h : IsPrim φ F g)
  (h' : IsPrim φ F g')
    {a b : ℂ} (ha : a ∈ closedBall (0 : ℂ) 1) (hb : b ∈ closedBall (0 : ℂ) 1) : -g a + g b
      = -g' a + g' b := by
  obtain ⟨ε, h0, h1⟩ := h
  obtain ⟨ε', h0', h1'⟩ := h'
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, a + (t : ℂ) * (b - a) ∈ closedBall (0 : ℂ) 1 := by
    intro t ht
    have h2 := (convex_closedBall (0 : ℂ) 1) ha hb (sub_nonneg.mpr ht.2) ht.1 (by ring)
    convert h2 using 1
    simp only [Complex.real_smul]
    push_cast
    ring
  let v : ℝ → A := fun t => g' (a + t * (b - a)) + -g (a + t * (b - a))
  have hd : ∃ δ > 0, ∀ s t : ℝ, |s - t| < δ → ‖(a + (s : ℂ) * (b - a)) - (a + t *
    (b - a))‖ < min ε ε' := by
    refine ⟨min ε ε' / (‖b - a‖ + 1), by positivity, fun s t hst => ?_⟩
    have h2 : (a + (s : ℂ) * (b - a)) - (a + t * (b - a)) = ((s - t : ℝ) : ℂ) * (b - a) := by
      push_cast
      ring
    rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [lt_div_iff₀ (by positivity)] at hst
    have := norm_nonneg (b - a)
    have h3 := abs_nonneg (s - t)
    nlinarith
  obtain ⟨δ, hδ, hd⟩ := hd
  have hv := const_of_near (v := v) hδ (fun s hs t ht hst => by
    have h2 := hd s t hst
    have e1 := h1 _ (hm t ht) _ (hm s hs) (by
      rw [norm_sub_rev]
      exact lt_of_lt_of_le h2 (min_le_left _ _))
    have e2 := h1' _ (hm t ht) _ (hm s hs) (by
      rw [norm_sub_rev]
      exact lt_of_lt_of_le h2 (min_le_right _ _))
    have e3 := e1.symm.trans e2
    simp only [v]
    rw [neg_add_eq_iff_eq_add] at e3
    rw [e3]
    simp only [neg_add_rev, neg_neg, add_assoc, add_neg_cancel_left])
  have h2 := hv 1 ⟨zero_le_one, le_rfl⟩
  simp only [v] at h2
  simp only [Complex.ofReal_one, one_mul, add_sub_cancel, Complex.ofReal_zero, zero_mul,
    add_zero] at h2
  have e : g' b = g' a + -g a + g b := by
    rw [← h2]
    simp only [add_assoc, neg_add_cancel, add_zero]
  rw [e]
  simp only [add_assoc, neg_add_cancel_left]

end Disc

section DiscComm

variable {Y : Type u} [TopologicalSpace Y] {A : Type} [AddCommGroup A]

theorem IsPrim.of_rel {φ φ' : Y → Y → A} {F : ℂ → Y} {g : ℂ → A} (hg : IsPrim φ F g)
    (hF : ContinuousOn F (closedBall 0 1)) {h : Y → A} {N : Set (Y × Y)} (hN : NearDiag N)
    (hr : ∀ x y, (x, y) ∈ N → φ x y - φ' x y = h y - h x) : IsPrim φ' F fun a => g a - h (F a) := by
  obtain ⟨ε, h0, h1⟩ := hg
  obtain ⟨ε', h0', h2⟩ := exists_eps (isCompact_closedBall 0 1) hF hN
  refine ⟨min ε ε', by positivity, fun a ha b hb hab => ?_⟩
  have e1 := h1 a ha b hb (lt_of_lt_of_le hab (min_le_left _ _))
  have e2 := hr _ _ (h2 a ha b hb (lt_of_lt_of_le hab (min_le_right _ _)))
  rw [e1] at e2
  have e3 : φ' (F a) (F b) = -g a + g b - (h (F b) - h (F a)) := by
    rw [← e2]
    abel
  change _ = -(g a - h (F a)) + (g b - h (F b))
  rw [e3]
  abel

/-- Two local cocycles are equivalent if the difference of their primitives is a function on `Y`. -/
theorem cohRel_of_descent [T2Space Y] {φ φ' : Y → Y → A} (hφ : IsCoc φ) (hφ' : IsCoc φ') {F : ℂ → Y}
    (hF : ContinuousOn F (closedBall 0 1)) (hs : F '' closedBall 0 1 = univ) {g g' : ℂ → A}
      (hg : IsPrim φ F g)
    (hg' : IsPrim φ' F g') (hd : ∀ a ∈ closedBall (0 : ℂ) 1, ∀ b ∈ closedBall (0 : ℂ) 1, F a = F b
      → g a - g' a = g b - g' b) :
    CohRel φ φ' := by
  classical
  obtain ⟨M, hM, hc⟩ := hφ
  obtain ⟨M', hM', hc'⟩ := hφ'
  obtain ⟨ε, h0, h1⟩ := hg
  obtain ⟨ε', h0', h1'⟩ := hg'
  have hlift : ∀ y : Y, ∃ a ∈ closedBall (0 : ℂ) 1, F a = y := fun y => by
    have h2 : y ∈ F '' closedBall 0 1 := by
      rw [hs]
      exact mem_univ y
    exact h2
  choose σ hσ1 hσ2 using hlift
  let h : Y → A := fun y => g (σ y) - g' (σ y)
  have hh : ∀ a ∈ closedBall (0 : ℂ) 1, h (F a) = g a - g' a := fun a ha => hd _ (hσ1 _) _ ha
    (hσ2 _)
  set δ := min ε ε' with hδ
  have hδ0 : 0 < δ := by positivity
  have hlocal : ∀ p : Y, ∃ O : Set Y, IsOpen O ∧ p ∈ O ∧ O ×ˢ O ⊆ M ∩ M' ∧
      ∀ x ∈ O, ∃ b ∈ closedBall (0 : ℂ) 1, F b = x ∧ ∃ a ∈ closedBall (0 : ℂ) 1, F a = p
        ∧ ‖b - a‖ < δ := by
    intro p
    let U : Set ℂ := ⋃ a ∈ closedBall (0 : ℂ) 1 ∩ F ⁻¹' {p}, ball a δ
    have hU : IsOpen U := isOpen_biUnion fun _ _ => isOpen_ball
    have hC : IsClosed (F '' (closedBall 0 1 \ U)) :=
      (((isCompact_closedBall 0 1).diff hU).image_of_continuousOn (hF.mono sdiff_subset)).isClosed
    have hp : p ∉ F '' (closedBall 0 1 \ U) := by
      rintro ⟨a, ha, he⟩
      exact ha.2 (mem_biUnion (x := a) ⟨ha.1, he⟩ (mem_ball_self hδ0))
    have h2 : M ∩ M' ∈ 𝓝 (p, p) := hM.inter hM' p
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp h2
    obtain ⟨O₁, hO₁, hO₁o, hpO₁⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
    refine ⟨O₁ ∩ (F '' (closedBall 0 1 \ U))ᶜ, hO₁o.inter hC.isOpen_compl, ⟨hpO₁, hp⟩, ?_, ?_⟩
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact huv ⟨(hO₁ hx.1).1, (hO₁ hy.1).2⟩
    · intro x hx
      refine ⟨σ x, hσ1 x, hσ2 x, ?_⟩
      have h3 : σ x ∈ U := by
        by_contra hc
        exact hx.2 ⟨σ x, ⟨hσ1 x, hc⟩, hσ2 x⟩
      obtain ⟨a, ha, hb⟩ := mem_iUnion₂.mp h3
      exact ⟨a, ha.1, ha.2, mem_ball_iff_norm.mp hb⟩
  choose O hO hpO hOM hOl using hlocal
  have hN : NearDiag (⋃ p, O p ×ˢ O p) := fun p =>
    Filter.mem_of_superset (((hO p).prod (hO p)).mem_nhds ⟨hpO p, hpO p⟩) (subset_iUnion (fun p
      => O p ×ˢ O p) p)
  refine ⟨h, _, hN, fun x y hxy => ?_⟩
  obtain ⟨p, hx, hy⟩ := mem_iUnion.mp hxy
  obtain ⟨b, hb, rfl, a, ha, hap, hab⟩ := hOl p x hx
  obtain ⟨c, hcD, rfl, a', ha', hap', hac⟩ := hOl p y hy
  have hm : ∀ {u v : Y}, u ∈ O p → v ∈ O p → (u, v) ∈ M ∧ (u, v) ∈ M' := fun hu hv => hOM p ⟨hu, hv⟩
  have hab1 : ‖b - a‖ < ε := lt_of_lt_of_le hab (min_le_left _ _)
  have hab2 : ‖b - a‖ < ε' := lt_of_lt_of_le hab (min_le_right _ _)
  have hac1 : ‖a' - c‖ < ε := by
    rw [norm_sub_rev]
    exact lt_of_lt_of_le hac (min_le_left _ _)
  have hac2 : ‖a' - c‖ < ε' := by
    rw [norm_sub_rev]
    exact lt_of_lt_of_le hac (min_le_right _ _)
  have e1 := h1 b hb a ha hab1
  have e2 := h1 a' ha' c hcD hac1
  have e3 := h1' b hb a ha hab2
  have e4 := h1' a' ha' c hcD hac2
  rw [hap] at e1 e3
  rw [hap'] at e2 e4
  have e5 := hc _ _ _ (hm hx (hpO p)).1 (hm (hpO p) hy).1 (hm hx hy).1
  have e6 := hc' _ _ _ (hm hx (hpO p)).2 (hm (hpO p) hy).2 (hm hx hy).2
  have e7 : g a - g' a = g a' - g' a' := hd a ha a' ha' (hap.trans hap'.symm)
  rw [hh b hb, hh c hcD, ← e5, ← e6, e1, e2, e3, e4]
  have e8 : g a = g a' - g' a' + g' a := by
    rw [← e7]
    abel
  rw [e8]
  abel

end DiscComm

end GraphMinor.Surface
