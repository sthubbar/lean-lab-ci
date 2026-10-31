/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 4 "Initial Setup".
The local sets R_j (4.4)-(4.6), the modulus q_0 (4.2), the global residue set R_0 (4.8),
the prime set P_u (4.9), with their elementary size bounds proved in full.
Sections 5-8 (circle method) are stated as `Prop`s, NOT axioms and NOT proved here.
Lemma 3.1 is proved CONDITIONAL ON two named Props: `SizeProp A` (the asymptotic step of
(4.8)-(4.9), a Chebyshev-type statement about primes) and `RepProp A` (the output of the
paper's Sections 5-9: every odd m in [4u,5u] is a sum of three primes of P_u).
AI-written Lean code, Claude, run 20261020T1903Z-4664, unit U-1276. Checked only by the
Lean kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Statements

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Section4

/-! ### (4.4)-(4.7): the local sets `R_j` -/

/-- (4.7) as an upper bound: `#R_j ≤ 3 a_j`. The paper prints `#R_j = 3a_j`; as a set of
integers the true count is `3a_j - 2` (`a_j` and `a_j²` are listed twice), checked in Python
for all primes below 5000. Only the upper bound is used. -/
theorem card_Rset_le (a : ℕ) : #(Rset a) ≤ 3 * a := by
  unfold Rset
  calc #(Icc 1 a ∪ (Icc 1 a).image (· * a) ∪ (Icc 1 a).image (· * a ^ 2))
      ≤ #(Icc 1 a ∪ (Icc 1 a).image (· * a)) + #((Icc 1 a).image (· * a ^ 2)) :=
        card_union_le _ _
    _ ≤ #(Icc 1 a) + #((Icc 1 a).image (· * a)) + #((Icc 1 a).image (· * a ^ 2)) := by
        gcongr; exact card_union_le _ _
    _ ≤ #(Icc 1 a) + #(Icc 1 a) + #(Icc 1 a) :=
        add_le_add (add_le_add le_rfl card_image_le) card_image_le
    _ = 3 * a := by rw [Nat.card_Icc]; omega

theorem mem_Rset_of {a r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ a) : r ∈ Rset a := by
  unfold Rset; simp only [mem_union, mem_Icc]; exact Or.inl (Or.inl ⟨h1, h2⟩)

theorem two_le_aOf (p : ℕ) (hp : 0 < p) : 2 ≤ aOf p := by
  unfold aOf
  have : 0 < ⌈(p : ℝ) ^ ((1 : ℝ) / 3)⌉₊ :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
  omega

/-- For `p ≥ 5`, `a_p < p`, so no element of `R_p` built from digits in `[1, a_p]` is
divisible by a prime `p ≥ 5`. -/
theorem aOf_lt (p : ℕ) (hp : 5 ≤ p) : aOf p < p := by
  have hcube : p ≤ (p - 2) ^ 3 := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 5 := ⟨p - 5, by omega⟩
    have : n + 5 - 2 = n + 3 := by omega
    rw [this]; nlinarith [sq_nonneg (n + 3)]
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ ((p - 2 : ℕ) : ℝ) := by
    have h1 : (p : ℝ) ≤ ((p - 2 : ℕ) : ℝ) ^ (3 : ℕ) := by exact_mod_cast hcube
    have h0 : (0 : ℝ) ≤ ((p - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (((p - 2 : ℕ) : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
      _ = ((p - 2 : ℕ) : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  have : ⌈(p : ℝ) ^ ((1 : ℝ) / 3)⌉₊ ≤ p - 2 := Nat.ceil_le.mpr hle
  unfold aOf; omega

/-- The nonzero residues of `R_p` mod `p`: the local condition behind `R_0`, which asks
`(r, q_0) = 1` and `r ≡ r_j (mod p_j)` for some `r_j ∈ R_j`. -/
def Lset (p : ℕ) : Finset ℕ := ((Rset (aOf p)).image (· % p)).filter (· ≠ 0)

theorem card_Lset_le (p : ℕ) : #(Lset p) ≤ 3 * aOf p :=
  (card_filter_le _ _).trans (card_image_le.trans (card_Rset_le _))

theorem Lset_sub (p : ℕ) (hp : 0 < p) : Lset p ⊆ Ico 1 p := by
  intro x hx
  unfold Lset at hx
  simp only [mem_filter, mem_image] at hx
  obtain ⟨⟨s, -, rfl⟩, h0⟩ := hx
  simp only [mem_Ico]; exact ⟨Nat.pos_of_ne_zero h0, Nat.mod_lt _ hp⟩

theorem card_Lset_le_pred (p : ℕ) (hp : 0 < p) : #(Lset p) ≤ p - 1 := by
  have := card_le_card (Lset_sub p hp); rwa [Nat.card_Ico] at this

theorem mod_mem_Lset {p s : ℕ} (hs : s ∈ Rset (aOf p)) (h0 : s % p ≠ 0) : s % p ∈ Lset p := by
  unfold Lset; simp only [mem_filter, mem_image]; exact ⟨⟨s, hs, rfl⟩, h0⟩

/-- Lemma 4.1 with nonzero residues, the form Section 8 needs: for a prime `p` and any `n`,
odd if `p = 2`, `n` is a sum of three nonzero residues of `R_p` mod `p`. For `p = 2` the
oddness is necessary: the only nonzero residue is `1`. -/
theorem local_three (p : ℕ) (hp : p.Prime) (n : ℕ) (h2 : p = 2 → n % 2 = 1) :
    ∃ t : ℕ × ℕ × ℕ, t.1 ∈ Lset p ∧ t.2.1 ∈ Lset p ∧ t.2.2 ∈ Lset p ∧
      t.1 + t.2.1 + t.2.2 ≡ n [MOD p] := by
  have ha2 := two_le_aOf p hp.pos
  have h1 : 1 ∈ Rset (aOf p) := mem_Rset_of le_rfl (by omega)
  by_cases hp2 : p = 2
  · subst hp2
    have hm : 1 % 2 ∈ Lset 2 := mod_mem_Lset h1 (by norm_num)
    refine ⟨(1, 1, 1), hm, hm, hm, ?_⟩
    show (1 + 1 + 1) % 2 = n % 2
    rw [h2 rfl]
  by_cases hp3 : p = 3
  · subst hp3
    have hm1 : 1 % 3 ∈ Lset 3 := mod_mem_Lset h1 (by norm_num)
    have hm2 : 2 % 3 ∈ Lset 3 := mod_mem_Lset (mem_Rset_of (by norm_num) ha2) (by norm_num)
    norm_num at hm1 hm2
    have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact ⟨(1, 1, 1), hm1, hm1, hm1, by show (1 + 1 + 1) % 3 = n % 3; omega⟩
    · exact ⟨(1, 1, 2), hm1, hm1, hm2, by show (1 + 1 + 2) % 3 = n % 3; omega⟩
    · exact ⟨(1, 2, 2), hm1, hm2, hm2, by show (1 + 2 + 2) % 3 = n % 3; omega⟩
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · subst h; exact absurd hp (by norm_num)
    · exact h
  set a := aOf p with ha
  have hap : a < p := aOf_lt p hp5
  have ndvd : ∀ w, 1 ≤ w → w ≤ a → ¬ p ∣ w := fun w hw1 hw2 hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have ndvda : ¬ p ∣ a := ndvd a (by omega) le_rfl
  obtain ⟨r, hr, w₁, hw₁, w₂, hw₂, h⟩ := three_digits hp.pos (le_aOf_cube p) n
  rw [← ha] at hr hw₁ hw₂ h
  simp only [mem_Icc] at hr hw₁ hw₂
  have m1 : r ∈ Rset a := mem_Rset_of hr.1 hr.2
  have m2 : w₁ * a ∈ Rset a := by
    unfold Rset; simp only [mem_union, mem_image, mem_Icc]
    exact Or.inl (Or.inr ⟨w₁, hw₁, rfl⟩)
  have m3 : w₂ * a ^ 2 ∈ Rset a := by
    unfold Rset; simp only [mem_union, mem_image, mem_Icc]
    exact Or.inr ⟨w₂, hw₂, rfl⟩
  have z1 : r % p ≠ 0 := fun h0 => ndvd r hr.1 hr.2 (Nat.dvd_of_mod_eq_zero h0)
  have z2 : w₁ * a % p ≠ 0 := by
    intro h0
    rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h0) with h' | h'
    · exact ndvd w₁ hw₁.1 hw₁.2 h'
    · exact ndvda h'
  have z3 : w₂ * a ^ 2 % p ≠ 0 := by
    intro h0
    rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h0) with h' | h'
    · exact ndvd w₂ hw₂.1 hw₂.2 h'
    · exact ndvda (hp.dvd_of_dvd_pow h')
  refine ⟨(r % p, w₁ * a % p, w₂ * a ^ 2 % p), mod_mem_Lset m1 z1, mod_mem_Lset m2 z2,
    mod_mem_Lset m3 z3, ?_⟩
  exact (((Nat.mod_modEq _ _).add (Nat.mod_modEq _ _)).add (Nat.mod_modEq _ _)).trans h

/-! ### (4.1)-(4.3), (4.8): the modulus `q_0` and the residue set `R_0` -/

/-- (4.2) `q_0 = ∏_{p < Z} p`; the paper takes `p < z` with `z = 3A log log u`, and
`p < z ↔ p < ⌈z⌉₊` for natural `p`. -/
def q0 (Z : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow Z, p

theorem q0_pos (Z : ℕ) : 0 < q0 Z :=
  prod_pos fun p hp => (Nat.prime_of_mem_primesBelow hp).pos

theorem dvd_q0 {Z p : ℕ} (hp : p ∈ Nat.primesBelow Z) : p ∣ q0 Z := dvd_prod_of_mem _ hp

/-- `R_0 = {r ∈ [1, q_0] : (r, q_0) = 1, and for every j some r_j ∈ R_j has r ≡ r_j mod p_j}`. -/
def R0 (Z : ℕ) : Finset ℕ :=
  (Icc 1 (q0 Z)).filter (fun r => Nat.Coprime r (q0 Z) ∧
    ∀ p ∈ Nat.primesBelow Z, ∃ s ∈ Rset (aOf p), r ≡ s [MOD p])

/-- CRT, uniqueness half: congruence modulo every `p < Z` gives congruence modulo `q_0`. -/
theorem modEq_q0 {Z a b : ℕ} (h : ∀ p ∈ Nat.primesBelow Z, a ≡ b [MOD p]) :
    a ≡ b [MOD q0 Z] := by
  rcases le_total a b with hab | hab
  · rw [Nat.modEq_iff_dvd' hab]
    exact prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primesBelow hp).prime)
      (fun p hp => (Nat.modEq_iff_dvd' hab).mp (h p hp))
  · refine Nat.ModEq.symm ?_
    rw [Nat.modEq_iff_dvd' hab]
    exact prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primesBelow hp).prime)
      (fun p hp => (Nat.modEq_iff_dvd' hab).mp (h p hp).symm)

theorem mod_ne_zero_of_coprime {r p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hc : r.Coprime q) :
    r % p ≠ 0 := by
  intro h0
  have h1 : p ∣ Nat.gcd r q := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) hpq
  rw [hc.gcd_eq_one] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- (4.8) as an upper bound: `#R_0 ≤ ∏_j #(R_j mod p_j, nonzero) ≤ ∏_j 3 a_j`. The map
`r ↦ (r mod p_j)_j` is injective on `[1, q_0]` by CRT uniqueness. -/
theorem card_R0_le (Z : ℕ) : #(R0 Z) ≤ ∏ p ∈ Nat.primesBelow Z, #(Lset p) := by
  rw [← card_pi]
  refine card_le_card_of_injOn (fun r => fun p _ => r % p) ?_ ?_
  · intro r hr
    rw [mem_coe] at hr ⊢
    simp only [R0, mem_filter, mem_Icc] at hr
    rw [mem_pi]
    intro p hp
    obtain ⟨s, hs, hrs⟩ := hr.2.2 p hp
    have h0 := mod_ne_zero_of_coprime (Nat.prime_of_mem_primesBelow hp) (dvd_q0 hp) hr.2.1
    unfold Lset; simp only [mem_filter, mem_image]
    exact ⟨⟨s, hs, hrs.symm⟩, h0⟩
  · intro r hr r' hr' heq
    rw [mem_coe] at hr hr'
    simp only [R0, mem_filter, mem_Icc] at hr hr'
    have hloc : ∀ p ∈ Nat.primesBelow Z, r ≡ r' [MOD p] := fun p hp =>
      congrFun (congrFun heq p) hp
    have hq := modEq_q0 hloc
    rcases le_total r r' with h | h
    · have hd := (Nat.modEq_iff_dvd' h).mp hq
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' h).mp hq.symm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega

theorem card_R0_le_cube (Z : ℕ) : #(R0 Z) ≤ ∏ p ∈ Nat.primesBelow Z, 3 * aOf p :=
  (card_R0_le Z).trans (prod_le_prod fun p _ => card_Lset_le p)

/-- The representative of `k` in `[1, q_0]`. -/
def rep (Z k : ℕ) : ℕ := (k + q0 Z - 1) % q0 Z + 1

theorem rep_modEq (Z k : ℕ) : rep Z k ≡ k [MOD q0 Z] := by
  have hq := q0_pos Z
  have h1 : rep Z k ≡ (k + q0 Z - 1) + 1 [MOD q0 Z] := (Nat.mod_modEq _ _).add_right 1
  have h2 : k + q0 Z - 1 + 1 = k + q0 Z := by omega
  rw [h2] at h1
  refine h1.trans ?_
  show (k + q0 Z) % q0 Z = k % q0 Z
  exact Nat.add_mod_right _ _

theorem rep_mem_Icc (Z k : ℕ) : rep Z k ∈ Icc 1 (q0 Z) := by
  have := Nat.mod_lt (k + q0 Z - 1) (q0_pos Z)
  simp only [mem_Icc, rep]; omega

/-- CRT, existence half packaged: a `k` meeting a nonzero local choice `x p ∈ L_p` at every
`p < Z` has its representative in `R_0`. -/
theorem rep_mem_R0 (Z k : ℕ) (x : ℕ → ℕ) (hx : ∀ p ∈ Nat.primesBelow Z, x p ∈ Lset p)
    (hk : ∀ p ∈ Nat.primesBelow Z, k ≡ x p [MOD p]) : rep Z k ∈ R0 Z := by
  have hloc : ∀ p ∈ Nat.primesBelow Z, rep Z k ≡ x p [MOD p] := fun p hp =>
    ((rep_modEq Z k).of_dvd (dvd_q0 hp)).trans (hk p hp)
  simp only [R0, mem_filter]
  refine ⟨rep_mem_Icc Z k, ?_, ?_⟩
  · refine Nat.Coprime.prod_right fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hxl := hx p hp
    have hsub := Lset_sub p hpp.pos hxl
    simp only [mem_Ico] at hsub
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => ?_)
    have h1 : rep Z k % p = x p % p := hloc p hp
    rw [Nat.mod_eq_of_lt hsub.2, Nat.mod_eq_zero_of_dvd hd] at h1
    omega
  · intro p hp
    have hxl := hx p hp
    unfold Lset at hxl
    simp only [mem_filter, mem_image] at hxl
    obtain ⟨⟨s, hs, hse⟩, -⟩ := hxl
    refine ⟨s, hs, (hloc p hp).trans ?_⟩
    rw [← hse]; exact Nat.mod_modEq _ _

/-- Section 8.3 local-to-global step: every odd `m` is `r₁ + r₂ + r₃ mod q_0` with all
`rᵢ ∈ R_0`. This is the CRT lift of `local_three`; it is what makes the singular series
factor `G(q_0) = ∏ G(p_j)` of Lemma 8.2 positive. -/
theorem R0_three (Z m : ℕ) (hm : m % 2 = 1) :
    ∃ r₁ ∈ R0 Z, ∃ r₂ ∈ R0 Z, ∃ r₃ ∈ R0 Z, r₁ + r₂ + r₃ ≡ m [MOD q0 Z] := by
  let T : ℕ → ℕ × ℕ × ℕ := fun p =>
    if hp : p.Prime then Classical.choose (local_three p hp m (fun _ => hm)) else (0, 0, 0)
  have hT : ∀ p ∈ Nat.primesBelow Z, (T p).1 ∈ Lset p ∧ (T p).2.1 ∈ Lset p ∧
      (T p).2.2 ∈ Lset p ∧ (T p).1 + (T p).2.1 + (T p).2.2 ≡ m [MOD p] := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    simp only [T, dite_eq_left_iff, hpp, dif_pos]
    exact Classical.choose_spec (local_three p hpp m (fun _ => hm))
  have hs : ∀ p ∈ Nat.primesBelow Z, id p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primesBelow hp).ne_zero
  have pp : Set.Pairwise (↑(Nat.primesBelow Z) : Set ℕ) (Function.onFun Nat.Coprime id) :=
    fun p hp q hq hne => (Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
      (Nat.prime_of_mem_primesBelow hq)).mpr hne
  let k₁ := Nat.chineseRemainderOfFinset (fun p => (T p).1) id (Nat.primesBelow Z) hs pp
  let k₂ := Nat.chineseRemainderOfFinset (fun p => (T p).2.1) id (Nat.primesBelow Z) hs pp
  let k₃ := Nat.chineseRemainderOfFinset (fun p => (T p).2.2) id (Nat.primesBelow Z) hs pp
  refine ⟨rep Z k₁, rep_mem_R0 Z k₁ (fun p => (T p).1) (fun p hp => (hT p hp).1) k₁.2,
    rep Z k₂, rep_mem_R0 Z k₂ (fun p => (T p).2.1) (fun p hp => (hT p hp).2.1) k₂.2,
    rep Z k₃, rep_mem_R0 Z k₃ (fun p => (T p).2.2) (fun p hp => (hT p hp).2.2.1) k₃.2, ?_⟩
  apply modEq_q0
  intro p hp
  have e1 := ((rep_modEq Z k₁).of_dvd (dvd_q0 hp)).trans (k₁.2 p hp)
  have e2 := ((rep_modEq Z k₂).of_dvd (dvd_q0 hp)).trans (k₂.2 p hp)
  have e3 := ((rep_modEq Z k₃).of_dvd (dvd_q0 hp)).trans (k₃.2 p hp)
  exact ((e1.add e2).add e3).trans (hT p hp).2.2.2

/-! ### (4.9): the prime set `P_u` and its size -/

/-- `P_u = {p prime : u ≤ p ≤ 2u, p ≡ r (mod q_0) for some r ∈ R_0}`. -/
def Pu (Z : ℕ) (u : ℝ) : Finset ℕ :=
  (Icc ⌈u⌉₊ ⌊2 * u⌋₊).filter (fun k => k.Prime ∧ ∃ r ∈ R0 Z, k ≡ r [MOD q0 Z])

theorem mem_Pu {Z : ℕ} {u : ℝ} (hu : 0 ≤ u) {p : ℕ} (hp : p ∈ Pu Z u) :
    p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ 2 * u := by
  simp only [Pu, mem_filter, mem_Icc] at hp
  refine ⟨hp.2.1, (Nat.le_ceil u).trans (by exact_mod_cast hp.1.1), ?_⟩
  exact (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (by linarith))

/-- At most `(H - L)/q + 1` integers of `[L, H]` lie in one class mod `q`. -/
theorem class_card (L H q r : ℕ) (hq : 0 < q) :
    #((Icc L H).filter (· ≡ r [MOD q])) ≤ (H - L) / q + 1 := by
  rw [← card_range ((H - L) / q + 1)]
  refine card_le_card_of_injOn (fun k => (k - L) / q) ?_ ?_
  · intro k hk
    rw [mem_coe, mem_filter, mem_Icc] at hk
    rw [mem_coe, mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · intro k hk k' hk' heq
    rw [mem_coe, mem_filter, mem_Icc] at hk hk'
    have hkk : k ≡ k' [MOD q] := hk.2.trans hk'.2.symm
    have hm : k - L ≡ k' - L [MOD q] := by
      apply Nat.ModEq.add_right_cancel' L
      rwa [Nat.sub_add_cancel hk.1.1, Nat.sub_add_cancel hk'.1.1]
    have heq' : (k - L) / q = (k' - L) / q := heq
    have e1 := Nat.div_add_mod (k - L) q
    have e2 := Nat.div_add_mod (k' - L) q
    have hm' : (k - L) % q = (k' - L) % q := hm
    rw [heq', hm'] at e1
    have : k - L = k' - L := e1.symm.trans e2
    omega

/-- (4.9), elementary half: `#P_u ≤ #R_0 · (u/q_0 + 1)`. -/
theorem card_Pu_le (Z : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (#(Pu Z u) : ℝ) ≤ #(R0 Z) * (u / q0 Z + 1) := by
  set L := ⌈u⌉₊
  set H := ⌊2 * u⌋₊
  set q := q0 Z
  have hq : 0 < q := q0_pos Z
  have hsub : Pu Z u ⊆ (R0 Z).biUnion (fun r => (Icc L H).filter (· ≡ r [MOD q])) := by
    intro k hk
    simp only [Pu, mem_filter] at hk
    obtain ⟨hI, -, r, hr, hkr⟩ := hk
    exact mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨hI, hkr⟩⟩
  have hnat : #(Pu Z u) ≤ #(R0 Z) * ((H - L) / q + 1) := by
    calc #(Pu Z u) ≤ #((R0 Z).biUnion (fun r => (Icc L H).filter (· ≡ r [MOD q]))) :=
          card_le_card hsub
      _ ≤ ∑ r ∈ R0 Z, #((Icc L H).filter (· ≡ r [MOD q])) := card_biUnion_le
      _ ≤ ∑ r ∈ R0 Z, ((H - L) / q + 1) := sum_le_sum fun r _ => class_card L H q r hq
      _ = #(R0 Z) * ((H - L) / q + 1) := by rw [sum_const, smul_eq_mul]
  have hHL : ((H - L : ℕ) : ℝ) ≤ u := by
    rcases le_total L H with h | h
    · rw [Nat.cast_sub h]
      have := Nat.floor_le (show 0 ≤ 2 * u by linarith)
      have := Nat.le_ceil u
      linarith
    · rw [Nat.sub_eq_zero_of_le h]; simpa using hu
  have hdiv : (((H - L) / q : ℕ) : ℝ) ≤ u / q :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right hHL (Nat.cast_nonneg _))
  calc (#(Pu Z u) : ℝ) ≤ ((#(R0 Z) * ((H - L) / q + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = #(R0 Z) * ((((H - L) / q : ℕ) : ℝ) + 1) := by push_cast; ring
    _ ≤ #(R0 Z) * (u / q + 1) := by gcongr

/-- The finite bound used below: `#P_u ≤ (∏_{p<Z} #L_p) · (u/q_0 + 1)`. -/
theorem card_Pu_le_prod (Z : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (#(Pu Z u) : ℝ) ≤ ((∏ p ∈ Nat.primesBelow Z, #(Lset p) : ℕ) : ℝ) * (u / q0 Z + 1) := by
  refine (card_Pu_le Z u hu).trans ?_
  have : (#(R0 Z) : ℝ) ≤ ((∏ p ∈ Nat.primesBelow Z, #(Lset p) : ℕ) : ℝ) := by
    exact_mod_cast card_R0_le Z
  have h0 : 0 ≤ u / q0 Z + 1 := by positivity
  exact mul_le_mul_of_nonneg_right this h0

/-! ### The paper's parameters, and Lemma 3.1 CONDITIONAL ON two Props -/

/-- `Z = ⌈z⌉₊` for (4.1) `z = 3A log log u`. -/
def Zof (A : ℕ) (u : ℝ) : ℕ := ⌈3 * A * Real.log (Real.log u)⌉₊

/-- The paper's prime set for exponent `A` at scale `u`. -/
def PuA (A : ℕ) (u : ℝ) : Finset ℕ := Pu (Zof A u) u

/-- `SizeProp A`: the asymptotic half of (4.8)-(4.9), with `z = 3A log log u`:
eventually `(∏_{p<z} #L_p)(u/q_0 + 1) ≤ u/(log u)^A`. A statement about primes only;
true asymptotically by Chebyshev-type bounds since `#L_p ≤ 3p^{1/3} + 6` and
`log q_0 = θ(z)`, numerically from about `z ≈ 150` on. NOT proved here. -/
def SizeProp (A : ℕ) : Prop :=
  ∃ u0 : ℝ, ∀ u : ℝ, u0 ≤ u →
    ((∏ p ∈ Nat.primesBelow (Zof A u), #(Lset p) : ℕ) : ℝ) * (u / q0 (Zof A u) + 1) ≤
      u / Real.log u ^ A

/-- `RepProp A`: the output of Sections 5-9, every odd `m ∈ [4u, 5u]` is a sum of three
primes of `P_u`. NOT proved here. -/
def RepProp (A : ℕ) : Prop :=
  ∃ u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, Odd m → 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    IsSum3In (↑(PuA A u) : Set ℕ) m

/-- **Lemma 3.1, CONDITIONAL ON `SizeProp A` and `RepProp A`**, with the paper's own set
`P_u` of Section 4. -/
theorem lemma31_of_props (A : ℕ) (hS : SizeProp A) (hR : RepProp A) : Lemma31 A := by
  obtain ⟨u0, hu0⟩ := hS
  obtain ⟨u1, hu1⟩ := hR
  refine ⟨max (max u0 u1) 1, by positivity, fun u hu => ⟨PuA A u, ?_, ?_, ?_⟩⟩
  · have hu' : 0 ≤ u := by linarith [le_max_right (max u0 u1) 1]
    exact fun p hp => mem_Pu hu' hp
  · have hu' : 0 ≤ u := by linarith [le_max_right (max u0 u1) 1]
    exact (card_Pu_le_prod _ u hu').trans
      (hu0 u (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu))
  · exact hu1 u (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu)

/-- Lemma 3.1 for every positive `A` from the Props, then Theorem 1.1 by `Gluing`. -/
theorem lemma31_all_of_props (hS : ∀ A, 0 < A → SizeProp A) (hR : ∀ A, 0 < A → RepProp A) :
    ∀ A : ℕ, 0 < A → Lemma31 A := fun A hA => lemma31_of_props A (hS A hA) (hR A hA)

/-! ### Sections 5-8 as Props, not axioms -/

open Complex in
/-- `e(x) = exp(2πix)`. -/
def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The integers `k ∈ [u, 2u]` with `k mod q_0 ∈ R_0`. -/
def Aset (Z : ℕ) (u : ℝ) : Finset ℕ :=
  (Icc ⌈u⌉₊ ⌊2 * u⌋₊).filter (fun k => ∃ r ∈ R0 Z, k ≡ r [MOD q0 Z])

/-- (4.10) `S(α) = Σ_{u ≤ k ≤ 2u, k mod q_0 ∈ R_0} Λ(k) e(kα)`. -/
def Sexp (Z : ℕ) (u α : ℝ) : ℂ :=
  ∑ k ∈ Aset Z u, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * α)

/-- (4.11) `𝔑(m) = Σ_{k₁+k₂+k₃=m} Λ(k₁)Λ(k₂)Λ(k₃)`, `kᵢ` as in `Aset`. -/
def Rfrak (Z : ℕ) (u : ℝ) (m : ℕ) : ℝ :=
  ∑ k₁ ∈ Aset Z u, ∑ k₂ ∈ Aset Z u, ∑ k₃ ∈ Aset Z u,
    if k₁ + k₂ + k₃ = m then ArithmeticFunction.vonMangoldt k₁ *
      ArithmeticFunction.vonMangoldt k₂ * ArithmeticFunction.vonMangoldt k₃ else 0

/-- Section 4.2 major arcs `𝔐 = ⋃ {α : |α - a/q| ≤ 1/Q}`, `1 ≤ a ≤ q ≤ P`, `(a, q) = 1`. -/
def majorArcs (P Q : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℕ, 1 ≤ a ∧ a ≤ q ∧ a.Coprime q ∧
    |α - a / q| ≤ 1 / Q}

def minorArcs (P Q : ℝ) : Set ℝ := Set.Icc 0 1 \ majorArcs P Q

/-- (4.12) `𝔑(m) = ∫₀¹ S(α)³ e(-mα) dα`. Orthogonality; provable, NOT proved here. -/
def Identity412 : Prop :=
  ∀ (Z : ℕ) (u : ℝ) (m : ℕ),
    ((Rfrak Z u m : ℝ) : ℂ) = ∫ α in (0 : ℝ)..1, Sexp Z u α ^ 3 * ee (-(m * α))

/-- (5.16) minor arcs, `P = (log u)^B`, `Q = u (log u)^{-B}`, `z = 3A log log u`:
`∫_𝔪 S³ e(-mα) ≪_ε u² / (log u)^{B/2 - 5A - 5 - 2ε}`. Cited, NOT proved. -/
def Minor516 (A B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ,
    ‖∫ α in minorArcs (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))‖ ≤
      C * u ^ 2 / Real.log u ^ ((B : ℝ) / 2 - 5 * A - 5 - 2 * ε)

/-- (6.16) the singular integral main term `H(m, u) = u² - ((m - 4u)² + (5u - m)²)/2`. -/
def Hmu (m u : ℝ) : ℝ := u ^ 2 - ((m - 4 * u) ^ 2 + (5 * u - m) ^ 2) / 2

/-- `H(m, u) ≥ u²/2` on the window `[4u, 5u]`. Python: `H` matches the exact count of
triples in `[u, 2u]` summing to `m` to within 1%, `u = 300`. -/
theorem Hmu_ge (m u : ℝ) (h1 : 4 * u ≤ m) (h2 : m ≤ 5 * u) : u ^ 2 / 2 ≤ Hmu m u := by
  unfold Hmu; nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- Sections 6-8 combined, OUR reading: (6.18) main term `H(m,u) 𝔖`, (7.1)-(7.16) and
Lemma 8.2 `𝔖 = G(q_0) Σ h(v)` with `G(q_0) = ∏ G(p_j) > 0` by `R0_three`, give for odd
`m ∈ [4u, 5u]` a major arc integral of real part at least `u² / (log u)^κ`. The paper's
explicit lower bound lies in Section 9, which we could not reach; this is NOT a printed
display. NOT proved. -/
def MajorLower (A B : ℕ) (κ : ℝ) : Prop :=
  ∃ u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, Odd m → 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    u ^ 2 / Real.log u ^ κ ≤
      (∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))).re

/-- Lemma 8.1: `𝒞(b) = Σ_{t ∈ {0..3}^b} ∏ binom(3, tᵢ)/φ(pᵢ)^{tᵢ} = ∏ pᵢ³/φ(pᵢ)³`,
stated for any `b` reals `pᵢ ≥ 2` in place of `φ(pᵢ) = pᵢ - 1`; the paper's right side
`(p₁⋯p_b)³/φ(p₁⋯p_b)³` is this product for distinct primes. PROVED. -/
theorem lemma_8_1 (b : ℕ) (ps : Fin b → ℝ) (hps : ∀ i, 2 ≤ ps i) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin b => range 4),
        ∏ i, (Nat.choose 3 (t i) : ℝ) / (ps i - 1) ^ (t i) =
      ∏ i, ps i ^ 3 / (ps i - 1) ^ 3 := by
  refine (prod_univ_sum (fun _ : Fin b => range 4)
    (fun i (t : ℕ) => (Nat.choose 3 t : ℝ) / (ps i - 1) ^ t)).symm.trans ?_
  refine prod_congr rfl fun i _ => ?_
  have h : ps i - 1 ≠ 0 := by linarith [hps i]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [Nat.choose]
  field_simp
  ring

end LeanLab.SparseTernary.Section4
