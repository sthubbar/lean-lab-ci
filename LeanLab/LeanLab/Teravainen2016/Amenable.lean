/-
P0076 J. Teräväinen, "The Goldbach problem for primes that are sums of two squares plus one",
arXiv 1611.08585. Definition 3.1, amenable linear functions, and the local step in the proof of
Theorem 1.1 assuming Propositions 3.2 and 3.3, pages 9 to 11: every even `m ≢ 5, 8 (mod 9)` with
`m ≢ 2 (mod 2^J)` splits as `m ≡ B₁ + B₂ (mod W)` with `W n + B₁`, `W n + B₂` amenable,
`W = 2^J · 3^3 · ∏_{p ∈ S} p` for any finite set `S` of primes `≥ 5`, as in (3.3).
Also the two remarks after Definition 3.1, the necessity of `m ≢ 2 (mod 2^J)` and the mod 3 remark,
and the exponent bookkeeping for `J = ⌊10/ε⌋`.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6756.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Teravainen2016.Definitions
import LeanLab.Teravainen2016.Lemma34

open Finset

namespace LeanLab.Teravainen2016

/-! ### Definition 3.1 -/

/-- Definition 3.1: `K n + b` is amenable. Condition (ii) `(b - 1, s(K)) = 1` is written prime by
prime: `s(K)` is the product of the primes `p ∣ K`, `p ≡ -1 (mod 4)`, `p ≠ 3`. -/
def Amenable (K b : ℤ) : Prop :=
  1 ≤ K ∧ (6 : ℤ) ^ 3 ∣ K ∧ IsCoprime b K ∧
  (∀ p : ℕ, p.Prime → p % 4 = 3 → p ≠ 3 → (p : ℤ) ∣ K → ¬ (p : ℤ) ∣ b - 1) ∧
  ∃ j t : ℕ, ∃ h : ℤ, b - 1 = 2 ^ j * 3 ^ (2 * t) * (4 * h + 1) ∧ ¬ (3 : ℤ) ∣ 4 * h + 1 ∧
    (2 : ℤ) ^ (j + 2) * 3 ^ (2 * t + 1) ∣ K

/-- The modulus `W = 2^J · 3^3 · ∏_{p ∈ S} p` of (3.3), `S` any finite set of primes. -/
def Wmod (J : ℕ) (S : Finset ℕ) : ℤ := 2 ^ J * 27 * ∏ p ∈ S, (p : ℤ)

/-! ### Small helpers -/

theorem not_pow_succ_dvd_pow_mul_odd {k : ℕ} {o : ℤ} (ho : ¬ (2 : ℤ) ∣ o) :
    ¬ (2 : ℤ) ^ (k + 1) ∣ 2 ^ k * o := by
  rintro ⟨c, hc⟩
  apply ho
  refine ⟨c, ?_⟩
  have h2 : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2
  rw [hc, pow_succ]; ring

/-- `IsCoprime a b` over `ℤ` from the absence of a common prime factor. -/
theorem isCoprime_of_primes {a b : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → False) : IsCoprime a b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  apply Nat.coprime_of_dvd
  intro k hk ha hb
  exact h k hk (Int.natCast_dvd.mpr ha) (Int.natCast_dvd.mpr hb)

theorem prime_dvd_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ ∏ q ∈ S, (q : ℤ)) : p ∈ S := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp) _).mp h
  have : p ∣ q := Int.natCast_dvd_natCast.mp hpq
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp this]

/-- A prime dividing `W` is `2`, `3` or in `S`. -/
theorem prime_dvd_Wmod {J : ℕ} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ Wmod J S) : p = 2 ∨ p = 3 ∨ p ∈ S := by
  have hpi := Nat.prime_iff_prime_int.mp hp
  unfold Wmod at h
  rcases hpi.dvd_or_dvd h with h | h
  · rcases hpi.dvd_or_dvd h with h | h
    · left
      have := Int.natCast_dvd_natCast.mp (hpi.dvd_of_dvd_pow (n := J) (by exact_mod_cast h))
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    · right; left
      have h' : (p : ℤ) ∣ (3 : ℤ) ^ 3 := by norm_num; exact h
      have := Int.natCast_dvd_natCast.mp (hpi.dvd_of_dvd_pow h')
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
  · right; right; exact prime_dvd_prod hS hp h

theorem Wmod_pos {J : ℕ} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) : 0 < Wmod J S := by
  unfold Wmod
  have : 0 < ∏ p ∈ S, (p : ℤ) := prod_pos fun q hq => by exact_mod_cast (hS q hq).pos
  positivity

theorem two_pow_dvd_Wmod {J k : ℕ} (S : Finset ℕ) (hk : k ≤ J) : (2 : ℤ) ^ k ∣ Wmod J S :=
  ((pow_dvd_pow 2 hk).mul_right _).mul_right _

theorem dvd27_Wmod (J : ℕ) (S : Finset ℕ) : (27 : ℤ) ∣ Wmod J S :=
  ((dvd_mul_left _ _)).mul_right _

theorem prod_dvd_Wmod (J : ℕ) (S : Finset ℕ) : (∏ p ∈ S, (p : ℤ)) ∣ Wmod J S :=
  dvd_mul_left _ _

theorem dvd_Wmod_of_mem {J : ℕ} {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) : (p : ℤ) ∣ Wmod J S :=
  (dvd_prod_of_mem _ hp).trans (prod_dvd_Wmod J S)

/-! ### The local criterion for amenability of `W n + B` -/

/-- Local criterion: if `B - 1 ≡ 2^j (mod 2^(j+2))` with `1 ≤ j`, `j + 2 ≤ J`, the `3`-part of
`B - 1` is `1` or `9`, `3 ∤ B`, and `p ∤ B (B - 1)` for `p ∈ S`, then `W n + B` is amenable. -/
theorem amenable_of_local {J : ℕ} (hJ : 3 ≤ J) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {B : ℤ} {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j + 2 ≤ J)
    (h2 : B - 1 ≡ 2 ^ j [ZMOD 2 ^ (j + 2)]) (h3a : ¬ (3 : ℤ) ∣ B) (h3b : ¬ (27 : ℤ) ∣ B - 1)
    (h3c : (3 : ℤ) ∣ B - 1 → (9 : ℤ) ∣ B - 1)
    (hp : ∀ p ∈ S, ¬ (p : ℤ) ∣ B ∧ ¬ (p : ℤ) ∣ B - 1) : Amenable (Wmod J S) B := by
  -- `B - 1 = 2^j (1 + 4u)`
  obtain ⟨u, hu⟩ : (2 : ℤ) ^ (j + 2) ∣ (B - 1) - 2 ^ j := (Int.ModEq.dvd h2.symm)
  have hN : B - 1 = 2 ^ j * (4 * u + 1) := by
    have : (2 : ℤ) ^ (j + 2) = 2 ^ j * 4 := by rw [pow_add]; norm_num
    rw [this] at hu; linear_combination hu
  have hodd : ¬ (2 : ℤ) ∣ B := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h' : B - 1 = 2 * (2 ^ j' * (4 * u + 1)) := by rw [hN, pow_succ]; ring
    generalize 2 ^ j' * (4 * u + 1) = X at h'
    omega
  refine ⟨by have := Wmod_pos (J := J) hS; omega, ?_, ?_, ?_, ?_⟩
  · unfold Wmod
    have : (6 : ℤ) ^ 3 = 2 ^ 3 * 27 := by norm_num
    rw [this]
    exact (mul_dvd_mul (pow_dvd_pow 2 hJ) dvd_rfl).mul_right _
  · apply isCoprime_of_primes
    intro p hpp hpB hpW
    rcases prime_dvd_Wmod hS hpp hpW with rfl | rfl | hpS
    · exact hodd (by exact_mod_cast hpB)
    · exact h3a (by exact_mod_cast hpB)
    · exact (hp p hpS).1 hpB
  · intro p hpp h4 h3 hpW
    rcases prime_dvd_Wmod hS hpp hpW with rfl | rfl | hpS
    · norm_num at h4
    · exact absurd rfl h3
    · exact (hp p hpS).2
  · by_cases h3 : (3 : ℤ) ∣ B - 1
    · have h9 := h3c h3
      have h9' : (9 : ℤ) ∣ 4 * u + 1 := by
        have hc : IsCoprime (9 : ℤ) (2 ^ j) := IsCoprime.pow_right ⟨1, -4, by norm_num⟩
        rw [hN] at h9
        exact hc.dvd_of_dvd_mul_left h9
      obtain ⟨r, hr⟩ := h9'
      refine ⟨j, 1, r / 4, ?_, ?_, ?_⟩
      · have : r = 4 * (r / 4) + 1 := by omega
        rw [hN, hr, ← this]; ring
      · intro h3r
        apply h3b
        have : 4 * (r / 4) + 1 = r := by omega
        rw [this] at h3r
        obtain ⟨c, hc⟩ := h3r
        exact ⟨2 ^ j * c, by rw [hN, hr, hc]; ring⟩
      · unfold Wmod
        exact (mul_dvd_mul (pow_dvd_pow 2 hjJ) (by norm_num)).mul_right _
    · refine ⟨j, 0, u, by rw [hN]; ring, ?_, ?_⟩
      · intro h3u
        apply h3
        rw [hN]; exact h3u.mul_left _
      · unfold Wmod
        exact (mul_dvd_mul (pow_dvd_pow 2 hjJ) (by norm_num)).mul_right _

/-! ### Choosing the residues modulo the primes `5 ≤ p ≤ w` -/

/-- For a finite set `S` of primes `≥ 5` and any `m`, some `b` has `b ≢ 0, 1, m, m - 1 (mod p)`
for every `p ∈ S`; the choice of `b_p` before the Chinese remainder step on page 10. -/
theorem exists_avoid (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q) (m : ℤ) :
    ∃ b : ℤ, ∀ p ∈ S, ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ b - 1 ∧ ¬ (p : ℤ) ∣ m - b ∧
      ¬ (p : ℤ) ∣ m - b - 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q S hqS ih =>
    obtain ⟨b₀, hb₀⟩ := ih (fun r hr => hS r (mem_insert_of_mem hr))
    obtain ⟨hq, hq5⟩ := hS q (mem_insert_self q S)
    set P : ℤ := ∏ p ∈ S, (p : ℤ)
    have : Fact q.Prime := ⟨hq⟩
    have hPq : (P : ZMod q) ≠ 0 := by
      intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      exact hqS (prime_dvd_prod (fun r hr => (hS r (mem_insert_of_mem hr)).1) hq h0)
    -- four forbidden values of `k` in `ZMod q`
    let T : Finset (ZMod q) :=
      {((-b₀ : ℤ) : ZMod q) / P, ((1 - b₀ : ℤ) : ZMod q) / P, ((m - b₀ : ℤ) : ZMod q) / P,
        ((m - 1 - b₀ : ℤ) : ZMod q) / P}
    have hT : T.card < Fintype.card (ZMod q) := by
      rw [ZMod.card]
      exact lt_of_le_of_lt (card_le_four) (by omega)
    obtain ⟨k, -, hk⟩ := exists_mem_notMem_of_card_lt_card (s := T) (t := univ)
      (by simpa using hT)
    refine ⟨b₀ + P * (k.val : ℤ), ?_⟩
    have key : ∀ c : ℤ, (q : ℤ) ∣ c - (b₀ + P * (k.val : ℤ)) →
        k = ((c - b₀ : ℤ) : ZMod q) / P := by
      intro c hc
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
      push_cast at hc
      rw [ZMod.natCast_zmod_val] at hc
      rw [eq_div_iff hPq]; push_cast; linear_combination -hc
    have hq' : ∀ c : ℤ, (q : ℤ) ∣ c - (b₀ + P * (k.val : ℤ)) → c ∈ ({0, 1, m, m - 1} : Set ℤ) →
        False := by
      intro c hc hcm
      apply hk
      have := key c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcm
      rcases hcm with rfl | rfl | rfl | rfl <;> simp [T, this]
    intro p hp
    rcases mem_insert.mp hp with rfl | hpS
    · refine ⟨fun h => hq' 0 ?_ (by simp), fun h => hq' 1 ?_ (by simp),
        fun h => hq' m ?_ (by simp), fun h => hq' (m - 1) ?_ (by simp)⟩
      · have := h.neg_right; simpa using this
      · have := h.neg_right; convert this using 1; ring
      · convert h using 1
      · convert h using 1; ring
    · have hpP : (p : ℤ) ∣ P * (k.val : ℤ) := (dvd_prod_of_mem _ hpS).mul_right _
      obtain ⟨h1, h2, h3, h4⟩ := hb₀ p hpS
      refine ⟨fun h => h1 ?_, fun h => h2 ?_, fun h => h3 ?_, fun h => h4 ?_⟩
      · have := dvd_sub h hpP; simpa using this
      · have := dvd_sub h hpP; convert this using 1; ring
      · have := dvd_add h hpP; convert this using 1; ring
      · have := dvd_add h hpP; convert this using 1; ring

/-! ### Chinese remainder theorem and the `3`-adic facts -/

theorem crt2 {m n : ℤ} (h : IsCoprime m n) (a b : ℤ) : ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨a * v * n + b * u * m, Int.modEq_iff_dvd.mpr ⟨(a - b) * u, ?_⟩,
    Int.modEq_iff_dvd.mpr ⟨(b - a) * v, ?_⟩⟩
  · linear_combination (-a) * huv
  · linear_combination (-b) * huv

/-- The remark in the proof of Theorem 1.1: the largest power of `3` dividing `x² + y²` has an even
exponent; here the first step, `3 ∣ x² + y² → 9 ∣ x² + y²`. -/
theorem nine_dvd_of_three_dvd_sum_sq (x y : ℤ) (h : (3 : ℤ) ∣ x ^ 2 + y ^ 2) :
    (9 : ℤ) ∣ x ^ 2 + y ^ 2 := by
  have hx := sq_mod_nine x
  have hy := sq_mod_nine y
  generalize x ^ 2 = X at *
  generalize y ^ 2 = Y at *
  omega

theorem three_facts {B c : ℤ} (hB : B ≡ 2 * c + 1 [ZMOD 27]) (h1 : ¬ c ≡ 1 [ZMOD 3])
    (h0 : ¬ c ≡ 0 [ZMOD 27]) (h9 : (3 : ℤ) ∣ c → (9 : ℤ) ∣ c) :
    ¬ (3 : ℤ) ∣ B ∧ ¬ (27 : ℤ) ∣ B - 1 ∧ ((3 : ℤ) ∣ B - 1 → (9 : ℤ) ∣ B - 1) := by
  unfold Int.ModEq at *
  by_cases hc : (3 : ℤ) ∣ c
  · have := h9 hc; omega
  · omega

theorem dvd_of_modEq {a b d : ℤ} (h : a ≡ b [ZMOD d]) (ha : d ∣ a) : d ∣ b := by
  have := (Int.ModEq.dvd h)
  have e : b = a + (b - a) := by ring
  rw [e]; exact dvd_add ha this

/-! ### The local step of the proof of Theorem 1.1 -/

/-- **Local step, page 10 to 11.** Let `J ≥ 5` and `S` a finite set of primes `≥ 5`, so that
`W = 2^J · 3^3 · ∏_{p ∈ S} p`. Every even `m ≢ 5, 8 (mod 9)` with `m ≢ 2 (mod 2^J)` is
`m ≡ B₁ + B₂ (mod W)` with `0 ≤ B₁, B₂ < W` and both `W n + B₁`, `W n + B₂` amenable. -/
theorem local_split (J : ℕ) (hJ : 5 ≤ J) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q) (m : ℤ)
    (he : (2 : ℤ) ∣ m) (h5 : ¬ m ≡ 5 [ZMOD 9]) (h8 : ¬ m ≡ 8 [ZMOD 9])
    (h2 : ¬ m ≡ 2 [ZMOD 2 ^ J]) :
    ∃ B₁ B₂ : ℤ, 0 ≤ B₁ ∧ B₁ < Wmod J S ∧ 0 ≤ B₂ ∧ B₂ < Wmod J S ∧
      m ≡ B₁ + B₂ [ZMOD Wmod J S] ∧ Amenable (Wmod J S) B₁ ∧ Amenable (Wmod J S) B₂ := by
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' + 2 := ⟨(m - 2) / 2, by omega⟩
  have hpowJ : (2 : ℤ) ^ J = 2 * 2 ^ (J - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm' : ¬ (2 : ℤ) ^ (J - 1) ∣ m' := by
    rintro ⟨c, hc⟩
    apply h2
    refine (Int.modEq_iff_dvd.mpr ⟨c, ?_⟩).symm
    rw [hpowJ, hc]; ring
  obtain ⟨a₁, a₂, ha, i, j, hi, hj, hai, haj⟩ := lemma_3_4_proved J hJ m' hm'
  have h3 : ¬ m' ≡ 3 [ZMOD 9] := by intro h; apply h8; unfold Int.ModEq at *; omega
  have h6 : ¬ m' ≡ 6 [ZMOD 9] := by intro h; apply h5; unfold Int.ModEq at *; omega
  obtain ⟨x₁, x₂, x₃, x₄, hm27, hc1, hc2, hz1, hz2⟩ := lemma_3_5 m' h3 h6
  have h91 := nine_dvd_of_three_dvd_sum_sq x₁ x₂
  have h92 := nine_dvd_of_three_dvd_sum_sq x₃ x₄
  rw [show x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 = (x₁ ^ 2 + x₂ ^ 2) + (x₃ ^ 2 + x₄ ^ 2) by ring]
    at hm27
  norm_num at hm27 hz1 hz2
  generalize x₁ ^ 2 + x₂ ^ 2 = c₁ at *
  generalize x₃ ^ 2 + x₄ ^ 2 = c₂ at *
  obtain ⟨b, hb⟩ := exists_avoid S hS (2 * m' + 2)
  -- Chinese remainder theorem, twice
  have hc : IsCoprime ((2 : ℤ) ^ J) 27 := IsCoprime.pow_left ⟨-13, 1, by norm_num⟩
  obtain ⟨B₀, hB0a, hB0b⟩ := crt2 hc (2 * a₁ + 1) (2 * c₁ + 1)
  have hc' : IsCoprime ((2 : ℤ) ^ J * 27) (∏ p ∈ S, (p : ℤ)) := by
    apply isCoprime_of_primes
    intro p hp h1 h2'
    have hpS := prime_dvd_prod hSp hp h2'
    have : (p : ℤ) ∣ Wmod J ∅ := by unfold Wmod; simpa using h1
    rcases prime_dvd_Wmod (by simp) hp this with rfl | rfl | h
    · have := (hS 2 hpS).2; omega
    · have := (hS 3 hpS).2; omega
    · simp at h
  obtain ⟨B, hBa, hBb⟩ := crt2 hc' B₀ b
  have hBJ : B ≡ 2 * a₁ + 1 [ZMOD 2 ^ J] := (hBa.of_dvd (dvd_mul_right _ _)).trans hB0a
  have hB27 : B ≡ 2 * c₁ + 1 [ZMOD 27] := (hBa.of_dvd (dvd_mul_left _ _)).trans hB0b
  set W := Wmod J S with hW
  have hWpos : 0 < W := Wmod_pos hSp
  have hW1 : ∀ x : ℤ, ∀ d : ℤ, d ∣ W → x % W ≡ x [ZMOD d] := fun x d hd =>
    (Int.mod_modEq x W).of_dvd hd
  refine ⟨B % W, (2 * m' + 2 - B) % W, Int.emod_nonneg _ hWpos.ne', Int.emod_lt_of_pos _ hWpos,
    Int.emod_nonneg _ hWpos.ne', Int.emod_lt_of_pos _ hWpos, ?_, ?_, ?_⟩
  · have := (Int.mod_modEq B W).add (Int.mod_modEq (2 * m' + 2 - B) W)
    rw [show B + (2 * m' + 2 - B) = 2 * m' + 2 by ring] at this
    exact this.symm
  · -- `W n + B₁`
    have e1 : B % W ≡ 2 * a₁ + 1 [ZMOD 2 ^ (i + 1 + 2)] :=
      (hW1 B _ (two_pow_dvd_Wmod S (by omega))).trans (hBJ.of_dvd (pow_dvd_pow 2 (by omega)))
    have e2 : B % W - 1 ≡ 2 ^ (i + 1) [ZMOD 2 ^ (i + 1 + 2)] := by
      have := e1.sub_right 1
      rw [show 2 * a₁ + 1 - 1 = 2 * a₁ by ring] at this
      exact this.trans (double_modEq hai)
    have e3 : B % W ≡ 2 * c₁ + 1 [ZMOD 27] := (hW1 B _ (dvd27_Wmod J S)).trans hB27
    obtain ⟨f1, f2, f3⟩ := three_facts e3 hc1 hz1 h91
    refine amenable_of_local (by omega) hSp (j := i + 1) (by omega) (by omega) e2 f1 f2 f3 ?_
    intro p hp
    have ep : B % W ≡ b [ZMOD p] :=
      (hW1 B _ (dvd_Wmod_of_mem hp)).trans (hBb.of_dvd (dvd_prod_of_mem _ hp))
    exact ⟨fun h => (hb p hp).1 (dvd_of_modEq ep h),
      fun h => (hb p hp).2.1 (dvd_of_modEq (ep.sub_right 1) h)⟩
  · -- `W n + B₂`
    have e1 : (2 * m' + 2 - B) % W ≡ 2 * a₂ + 1 [ZMOD 2 ^ (j + 1 + 2)] := by
      have := (hW1 (2 * m' + 2 - B) _ (two_pow_dvd_Wmod S (show j + 1 + 2 ≤ J by omega))).trans
        ((Int.ModEq.refl (2 * m' + 2)).sub (hBJ.of_dvd (pow_dvd_pow 2 (by omega))))
      rwa [show 2 * m' + 2 - (2 * a₁ + 1) = 2 * a₂ + 1 by rw [ha]; ring] at this
    have e2 : (2 * m' + 2 - B) % W - 1 ≡ 2 ^ (j + 1) [ZMOD 2 ^ (j + 1 + 2)] := by
      have := e1.sub_right 1
      rw [show 2 * a₂ + 1 - 1 = 2 * a₂ by ring] at this
      exact this.trans (double_modEq haj)
    have e3 : (2 * m' + 2 - B) % W ≡ 2 * c₂ + 1 [ZMOD 27] := by
      have := hW1 (2 * m' + 2 - B) _ (dvd27_Wmod J S)
      unfold Int.ModEq at this hB27 hm27 ⊢
      omega
    obtain ⟨f1, f2, f3⟩ := three_facts e3 hc2 hz2 h92
    refine amenable_of_local (by omega) hSp (j := j + 1) (by omega) (by omega) e2 f1 f2 f3 ?_
    intro p hp
    have ep : (2 * m' + 2 - B) % W ≡ 2 * m' + 2 - b [ZMOD p] :=
      (hW1 _ _ (dvd_Wmod_of_mem hp)).trans
        ((Int.ModEq.refl _).sub (hBb.of_dvd (dvd_prod_of_mem _ hp)))
    exact ⟨fun h => (hb p hp).2.2.1 (dvd_of_modEq ep h),
      fun h => (hb p hp).2.2.2 (dvd_of_modEq (ep.sub_right 1) h)⟩

/-- The local step with `W` exactly as in (3.3): `S` the primes `5 ≤ p ≤ w`. -/
theorem local_split_33 (J w : ℕ) (hJ : 5 ≤ J) (m : ℤ) (he : (2 : ℤ) ∣ m)
    (h5 : ¬ m ≡ 5 [ZMOD 9]) (h8 : ¬ m ≡ 8 [ZMOD 9]) (h2 : ¬ m ≡ 2 [ZMOD 2 ^ J]) :
    let W := Wmod J ((Icc 5 w).filter Nat.Prime)
    ∃ B₁ B₂ : ℤ, 0 ≤ B₁ ∧ B₁ < W ∧ 0 ≤ B₂ ∧ B₂ < W ∧
      m ≡ B₁ + B₂ [ZMOD W] ∧ Amenable W B₁ ∧ Amenable W B₂ :=
  local_split J hJ _ (fun q hq => by
    simp only [mem_filter, mem_Icc] at hq; exact ⟨hq.2, hq.1.1⟩) m he h5 h8 h2

/-! ### The two remarks after Definition 3.1 -/

theorem sum_classes_aux {a b : ℤ} {i j s : ℕ} (hij : i ≤ j) (ha : a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)])
    (hb : b ≡ 2 ^ j [ZMOD 2 ^ (j + 2)]) (hi : i + 2 ≤ s) (hj : j + 2 ≤ s) :
    ¬ (2 : ℤ) ^ s ∣ a + b := by
  obtain ⟨u, hu⟩ := (Int.ModEq.dvd ha.symm)
  obtain ⟨v, hv⟩ := (Int.ModEq.dvd hb.symm)
  intro hs
  rcases Nat.lt_or_ge i j with hlt | hge
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    have e : a + b = 2 ^ i * (1 + 4 * u + 2 * (2 ^ d * (1 + 4 * v))) := by
      have ea : a = 2 ^ i + 2 ^ (i + 2) * u := by linear_combination hu
      have eb : b = 2 ^ (i + (d + 1)) + 2 ^ (i + (d + 1) + 2) * v := by linear_combination hv
      rw [ea, eb]; ring
    have hodd : ¬ (2 : ℤ) ∣ 1 + 4 * u + 2 * (2 ^ d * (1 + 4 * v)) := by
      generalize 2 ^ d * (1 + 4 * v) = X; omega
    apply not_pow_succ_dvd_pow_mul_odd (k := i) hodd
    rw [← e]; exact (pow_dvd_pow 2 (by omega)).trans hs
  · obtain rfl : i = j := le_antisymm hij hge
    have e : a + b = 2 ^ (i + 1) * (1 + 2 * u + 2 * v) := by
      have ea : a = 2 ^ i + 2 ^ (i + 2) * u := by linear_combination hu
      have eb : b = 2 ^ i + 2 ^ (i + 2) * v := by linear_combination hv
      rw [ea, eb]; ring
    have hodd : ¬ (2 : ℤ) ∣ 1 + 2 * u + 2 * v := by omega
    apply not_pow_succ_dvd_pow_mul_odd (k := i + 1) hodd
    rw [← e]; exact (pow_dvd_pow 2 (by omega)).trans hs

/-- Converse of Lemma 3.4: `a ≡ 2^i (mod 2^(i+2))`, `b ≡ 2^j (mod 2^(j+2))` with
`i, j ≤ s - 2` give `2^s ∤ a + b`. -/
theorem sum_classes_not_dvd {a b : ℤ} {i j s : ℕ} (ha : a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)])
    (hb : b ≡ 2 ^ j [ZMOD 2 ^ (j + 2)]) (hi : i + 2 ≤ s) (hj : j + 2 ≤ s) :
    ¬ (2 : ℤ) ^ s ∣ a + b := by
  rcases le_total i j with h | h
  · exact sum_classes_aux h ha hb hi hj
  · rw [add_comm]; exact sum_classes_aux h hb ha hj hi

/-- From (iii): if `W n + b` is amenable and `2^(s+1) ∤ K`, then `b - 1 ≡ 2^j (mod 2^(j+2))`
for some `j ≤ s - 2`. -/
theorem amenable_two_adic {K b : ℤ} {s : ℕ} (h : Amenable K b) (hK : ¬ (2 : ℤ) ^ (s + 1) ∣ K) :
    ∃ j : ℕ, j + 2 ≤ s ∧ b - 1 ≡ 2 ^ j [ZMOD 2 ^ (j + 2)] := by
  obtain ⟨-, -, -, -, j, t, hh, hb, -, hdvd⟩ := h
  refine ⟨j, ?_, ?_⟩
  · by_contra hc
    apply hK
    exact (pow_dvd_pow 2 (by omega)).trans ((dvd_mul_right _ _).trans hdvd)
  · obtain ⟨w, hw⟩ : (9 : ℤ) - 1 ∣ 9 ^ t - 1 ^ t := sub_dvd_pow_sub_pow 9 1 t
    have h9 : (3 : ℤ) ^ (2 * t) = 9 ^ t := by rw [pow_mul]; norm_num
    rw [one_pow] at hw
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(hh + 2 * w * (4 * hh + 1)), ?_⟩
    rw [hb, h9, show (9 : ℤ) ^ t = 1 + 8 * w by linear_combination hw, pow_add]
    ring

/-- **Remark after Definition 3.1, 2-adic part, PROVED.** If `K n + b₁`, `K n + b₂` are amenable
and `2^s ∥ K`, then `K n₁ + b₁ + K n₂ + b₂ ≢ 2 (mod 2^s)` for all `n₁, n₂`. This is why the proof of
Theorem 1.1 discards `m ≡ 2 (mod 2^J)`. -/
theorem amenable_sum_ne_two {K b₁ b₂ : ℤ} {s : ℕ} (h₁ : Amenable K b₁) (h₂ : Amenable K b₂)
    (hs : (2 : ℤ) ^ s ∣ K) (hK : ¬ (2 : ℤ) ^ (s + 1) ∣ K) (n₁ n₂ : ℤ) :
    ¬ K * n₁ + b₁ + (K * n₂ + b₂) ≡ 2 [ZMOD 2 ^ s] := by
  obtain ⟨i, hi, hai⟩ := amenable_two_adic h₁ hK
  obtain ⟨j, hj, haj⟩ := amenable_two_adic h₂ hK
  intro hc
  apply sum_classes_not_dvd hai haj hi hj
  have := Int.ModEq.dvd hc
  have e : b₁ - 1 + (b₂ - 1) = -(2 - (K * n₁ + b₁ + (K * n₂ + b₂))) - K * (n₁ + n₂) := by ring
  rw [e]
  exact dvd_sub this.neg_right (hs.mul_right _)

/-- **Remark after Definition 3.1, mod 3 part, PROVED.** If `K n + b₁`, `K n + b₂` are amenable
and `3 ∤ b₁ - 1`, `3 ∤ b₂ - 1`, then `K n₁ + b₁ + K n₂ + b₂ ≡ 1 (mod 3)`. -/
theorem amenable_sum_mod_three {K b₁ b₂ : ℤ} (h₁ : Amenable K b₁) (h₂ : Amenable K b₂)
    (h₁' : ¬ (3 : ℤ) ∣ b₁ - 1) (h₂' : ¬ (3 : ℤ) ∣ b₂ - 1) (n₁ n₂ : ℤ) :
    K * n₁ + b₁ + (K * n₂ + b₂) ≡ 1 [ZMOD 3] := by
  have h3K : (3 : ℤ) ∣ K := (by norm_num : (3 : ℤ) ∣ 6 ^ 3).trans h₁.2.1
  have c1 : ¬ (3 : ℤ) ∣ b₁ := fun h => by
    have := Int.dvd_gcd h h3K
    rw [Int.isCoprime_iff_gcd_eq_one.mp h₁.2.2.1] at this
    norm_num at this
  have c2 : ¬ (3 : ℤ) ∣ b₂ := fun h => by
    have := Int.dvd_gcd h h3K
    rw [Int.isCoprime_iff_gcd_eq_one.mp h₂.2.2.1] at this
    norm_num at this
  obtain ⟨k, hk⟩ := h3K
  rw [hk, show 3 * k * n₁ + b₁ + (3 * k * n₂ + b₂) = 3 * (k * n₁ + k * n₂) + b₁ + b₂ by ring]
  unfold Int.ModEq
  generalize k * n₁ + k * n₂ = A
  omega

/-! ### Exponent bookkeeping in the proof of Theorem 1.1 -/

theorem sq_le_ten_mul_two_pow : ∀ k : ℕ, (k + 1) ^ 2 ≤ 10 * 2 ^ k
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | k + 4 => by
    have ih := sq_le_ten_mul_two_pow (k + 3)
    have e : (2 : ℕ) ^ (k + 4) = 2 * 2 ^ (k + 3) := by ring
    have h : (k + 4 + 1) ^ 2 ≤ 2 * (k + 3 + 1) ^ 2 := by ring_nf; nlinarith
    rw [e]; omega

/-- With `J = ⌊10/ε⌋`, `2^(-J) ≤ ε² / 10`: the integers `m ≡ 2 (mod 2^J)` up to `N` number at most
`N / 2^J + 1`, and `N / 2^J ≤ ε² N / 10` as used on page 10. -/
theorem two_pow_floor_bound {ε : ℝ} (hε : 0 < ε) :
    10 ≤ ε ^ 2 * 2 ^ ⌊10 / ε⌋₊ := by
  set k := ⌊10 / ε⌋₊
  have hk : 10 / ε < k + 1 := Nat.lt_floor_add_one _
  have h1 : 10 < ε * (k + 1) := by rw [div_lt_iff₀ hε] at hk; linarith
  have h2 : ((k : ℝ) + 1) ^ 2 ≤ 10 * 2 ^ k := by exact_mod_cast sq_le_ten_mul_two_pow k
  have h3 : (100 : ℝ) < ε ^ 2 * (k + 1) ^ 2 := by nlinarith
  nlinarith

/-- The final count on page 12: `ε/2 + ε² ≤ ε` for `0 ≤ ε ≤ 1/2`. -/
theorem final_count {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : ε / 2 + ε ^ 2 ≤ ε := by nlinarith

end LeanLab.Teravainen2016
