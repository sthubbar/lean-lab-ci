/-
P0076 J. Teräväinen, arXiv 1611.08585: Lemma 7.1, page 29, cited there as Matomäki and Shao
Lemma 3.2, proved in full: Dirichlet approximation of each `α_k / W` with denominator at most
`N/(log N)^{100B}`, then a pigeonhole choice of `Q ≤ (log N)^B`, `B = A (3C)^C`.
The pigeonhole runs with the fixed threshold `T = (log N)^A`: start from `Q = 1`; while some
`q_k ∤ Q` has `q_k / (q_k, Q²) < T`, replace `Q` by `Q q_k`. Then `Q q_k < T Q³`, so after at most
`C` stages `Q ≤ T^{3^C - 1} ≤ (log N)^{A (3C)^C}`.
burst-20261122 step lemma71_choice1122d. AI wrote the Lean code. The binary Goldbach conjecture
is OPEN.
-/
import LeanLab.Teravainen2016.Prop51Split1122b

open Finset Filter Topology
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The pigeonhole step of Matomäki and Shao Lemma 3.2, used for Lemma 7.1 on page 29, in an
inductive form: from a start `Q₀ ≤ T^e` with at most `n` indices `k` having `q_k ∤ Q₀`, one
reaches `Q ≤ T^{3^n (e+1) - 1}` with every `q_k ∣ Q` or `q_k / (q_k, Q²) ≥ T`. -/
theorem lemma71_pigeonhole_aux {C : ℕ} (q : Fin C → ℕ) (hq : ∀ k, 1 ≤ q k) (T : ℝ)
    (hT : 1 ≤ T) : ∀ n : ℕ, ∀ Q₀ e : ℕ, 1 ≤ Q₀ → (Q₀ : ℝ) ≤ T ^ e →
      #(univ.filter (fun k => ¬ q k ∣ Q₀)) ≤ n →
      ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ T ^ (3 ^ n * (e + 1) - 1) ∧
        ∀ k, q k ∣ Q ∨ T ≤ (q k : ℝ) / (Nat.gcd (q k) (Q ^ 2) : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro Q₀ e hQ1 hQe hcard
    refine ⟨Q₀, hQ1, by simpa using hQe, ?_⟩
    intro k
    left
    by_contra hk
    have : k ∈ univ.filter (fun k => ¬ q k ∣ Q₀) := by simp [hk]
    have := Finset.card_pos.mpr ⟨k, this⟩
    omega
  | succ m ih =>
    intro Q₀ e hQ1 hQe hcard
    have hmono : (Q₀ : ℝ) ≤ T ^ (3 ^ (m + 1) * (e + 1) - 1) := by
      refine hQe.trans (pow_le_pow_right₀ hT ?_)
      have : e + 1 ≤ 3 ^ (m + 1) * (e + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    by_cases h : ∃ k, ¬ q k ∣ Q₀ ∧ (q k : ℝ) / (Nat.gcd (q k) (Q₀ ^ 2) : ℝ) < T
    · obtain ⟨k, hkd, hkT⟩ := h
      have hg0 : 0 < Nat.gcd (q k) (Q₀ ^ 2) := Nat.gcd_pos_of_pos_left _ (hq k)
      have hgle : Nat.gcd (q k) (Q₀ ^ 2) ≤ Q₀ ^ 2 :=
        Nat.le_of_dvd (by positivity) (Nat.gcd_dvd_right _ _)
      have hg0r : (0 : ℝ) < (Nat.gcd (q k) (Q₀ ^ 2) : ℝ) := by exact_mod_cast hg0
      have hqk : (q k : ℝ) ≤ T * (Q₀ : ℝ) ^ 2 := by
        rw [div_lt_iff₀ hg0r] at hkT
        have : (Nat.gcd (q k) (Q₀ ^ 2) : ℝ) ≤ (Q₀ : ℝ) ^ 2 := by exact_mod_cast hgle
        nlinarith
      have hQ0r : (0 : ℝ) ≤ Q₀ := by positivity
      have hQ1' : 1 ≤ Q₀ * q k := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by have := hq k; omega))
      have hQe' : ((Q₀ * q k : ℕ) : ℝ) ≤ T ^ (3 * e + 1) := by
        push_cast
        calc (Q₀ : ℝ) * q k ≤ Q₀ * (T * (Q₀ : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hqk hQ0r
          _ = T * (Q₀ : ℝ) ^ 3 := by ring
          _ ≤ T * (T ^ e) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact pow_le_pow_left₀ hQ0r hQe 3
          _ = T ^ (3 * e + 1) := by ring
      have hsub : univ.filter (fun j => ¬ q j ∣ Q₀ * q k) ⊂
          univ.filter (fun j => ¬ q j ∣ Q₀) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨k, by simp [hkd], by simp⟩
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj ⊢
          exact fun hd => hj (Dvd.dvd.mul_right hd _)
      have hc := Finset.card_lt_card hsub
      obtain ⟨Q, hQ, hQb, hQp⟩ := ih (Q₀ * q k) (3 * e + 1) hQ1' hQe' (by omega)
      refine ⟨Q, hQ, ?_, hQp⟩
      have : 3 ^ m * (3 * e + 1 + 1) - 1 ≤ 3 ^ (m + 1) * (e + 1) - 1 := by
        rw [pow_succ]
        have : 3 ^ m * (3 * e + 1 + 1) ≤ 3 ^ m * 3 * (e + 1) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      exact hQb.trans (pow_le_pow_right₀ hT this)
    · push Not at h
      refine ⟨Q₀, hQ1, hmono, fun k => ?_⟩
      by_cases hk : q k ∣ Q₀
      · exact Or.inl hk
      · exact Or.inr (h k hk)

/-- The pigeonhole step of Matomäki and Shao Lemma 3.2, used for Lemma 7.1 on page 29: for
denominators `q_1, …, q_C ≥ 1` and a threshold `T ≥ 1` there is `1 ≤ Q ≤ T^{3^C - 1}` with
`q_k ∣ Q` or `q_k / (q_k, Q²) ≥ T` for every `k`. -/
theorem lemma71_pigeonhole {C : ℕ} (q : Fin C → ℕ) (hq : ∀ k, 1 ≤ q k) (T : ℝ) (hT : 1 ≤ T) :
    ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ T ^ (3 ^ C - 1) ∧
      ∀ k, q k ∣ Q ∨ T ≤ (q k : ℝ) / (Nat.gcd (q k) (Q ^ 2) : ℝ) := by
  obtain ⟨Q, h1, h2, h3⟩ := lemma71_pigeonhole_aux q hq T hT C 1 0 le_rfl (by simp)
    (by simpa using (Finset.card_filter_le univ _).trans (by simp))
  exact ⟨Q, h1, by simpa using h2, h3⟩

/-- The Dirichlet step of Lemma 7.1, page 29: for `M ≥ 1` every real `α` is `W a / q + ε` with
`(a, q) = 1`, `1 ≤ q ≤ M` and `|ε| ≤ W / (q M)`. -/
theorem lemma71_dirichlet (α : ℝ) (W : ℤ) (hW : 1 ≤ W) (M : ℝ) (hM : 1 ≤ M) :
    ∃ a : ℤ, ∃ q : ℕ, ∃ ε : ℝ, α = (W : ℝ) * a / q + ε ∧ IsCoprime a (q : ℤ) ∧ 1 ≤ q ∧
      (q : ℝ) ≤ M ∧ |ε| ≤ W / (q * M) := by
  have hn : 0 < ⌊M⌋₊ := Nat.floor_pos.mpr hM
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show (0 : ℤ) < W by omega)
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le (α / W) hn
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  refine ⟨r.num, r.den, α - W * r.num / r.den, by ring, ?_, r.den_pos, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using r.reduced
  · exact (Nat.cast_le.mpr hden).trans (Nat.floor_le (by linarith))
  · have hrr : (r : ℝ) = r.num / r.den := Rat.cast_def r
    have heq : α - W * r.num / r.den = W * (α / W - r) := by
      rw [hrr]; field_simp
    rw [heq, abs_mul, abs_of_pos hWr]
    have hM' : M ≤ (⌊M⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one M).le
    have : 1 / (((⌊M⌋₊ : ℝ) + 1) * r.den) ≤ 1 / (r.den * M) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    calc (W : ℝ) * |α / W - r| ≤ W * (1 / (r.den * M)) := by
          apply mul_le_mul_of_nonneg_left _ hWr.le
          exact (by exact_mod_cast hr : |α / W - r| ≤ 1 / ((⌊M⌋₊ + 1 : ℝ) * r.den)).trans this
      _ = W / (r.den * M) := by ring

/-- Eventually `1 ≤ log N` and `(log N)^m ≤ N` along the naturals. -/
theorem lemma71_eventually (m : ℕ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    1 ≤ Real.log N ∧ Real.log N ^ m ≤ N := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max N₁ 3, fun N hN => ⟨?_, ?_⟩⟩
  · have h3 : (3 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  · have := hN₁ N ((le_max_left _ _).trans hN)
    have hNpos : (0 : ℝ) < N := by
      have : 3 ≤ N := (le_max_right _ _).trans hN
      exact_mod_cast (show 0 < N by omega)
    simp only [Function.comp, one_mul, add_zero] at this
    rw [div_lt_one hNpos] at this
    exact this.le

/-- Lemma 7.1, page 29, which is Matomäki and Shao Lemma 3.2, proved with the roles of `A` and
`B` as printed: `Q ≤ (log N)^B`, `q_k ≤ N/(log N)^{100B}`, and `q_k ∣ Q` or
`q_k / (q_k, Q²) ≥ (log N)^A`, with `B = A (3C)^C`. In `Lemma71Adapted α W N A' B' Q` the slot
`A'` is the threshold exponent and `B'` the exponent of the denominator bound. -/
theorem lemma71_choice_paper : ∀ (C A : ℕ) (W : ℤ), 1 ≤ W → ∃ N₀ : ℕ, ∀ α : Fin C → ℝ,
    ∀ N : ℕ, N₀ ≤ N → ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ Real.log N ^ (A * (3 * C) ^ C) ∧
      Lemma71Adapted α W N A (A * (3 * C) ^ C) Q := by
  intro C A W hW
  set B : ℕ := A * (3 * C) ^ C with hB
  obtain ⟨N₀, hN₀⟩ := lemma71_eventually (100 * B)
  refine ⟨N₀, fun α N hN => ?_⟩
  obtain ⟨hL1, hLN⟩ := hN₀ N hN
  set L : ℝ := Real.log N with hL
  have hLp : (0 : ℝ) < L ^ (100 * B) := by positivity
  set M : ℝ := N / L ^ (100 * B) with hMdef
  have hM : 1 ≤ M := by rw [hMdef, le_div_iff₀ hLp]; linarith
  have hD := fun k => lemma71_dirichlet (α k) W hW M hM
  choose a q ε hα hcop hq1 hqM hε using hD
  have hT : (1 : ℝ) ≤ L ^ A := one_le_pow₀ hL1
  obtain ⟨Q, hQ1, hQb, hQp⟩ := lemma71_pigeonhole q hq1 (L ^ A) hT
  refine ⟨Q, hQ1, ?_, ?_⟩
  · refine hQb.trans ?_
    rw [← pow_mul]
    apply pow_le_pow_right₀ hL1
    apply Nat.mul_le_mul_left
    rcases Nat.eq_zero_or_pos C with hC | hC
    · subst hC; simp
    · exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (by omega) _)
  · intro k
    refine ⟨a k, q k, ε k, hα k, hcop k, hq1 k, hqM k, ?_, hQp k⟩
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (le_trans (one_le_pow₀ hL1) hLN)
    have hq0 : (0 : ℝ) < q k := by exact_mod_cast hq1 k
    refine (hε k).trans (le_of_eq ?_)
    rw [hMdef]
    field_simp
    rfl

/-- Rigidity of the approximation of `1/p`: if `1/p = a/q + ε` with `(a, q) = 1`, `q ≥ 1` and
`|ε| ≤ K/(q N)` where `p K < N`, then `q = p`. -/
theorem lemma71_rigid (p : ℕ) (hp : 1 ≤ p) (a : ℤ) (q : ℕ) (ε K N : ℝ) (hq : 1 ≤ q)
    (hK : 0 < K) (hN0 : 0 < N)
    (hα : (1 : ℝ) / p = ((1 : ℤ) : ℝ) * a / q + ε) (hcop : IsCoprime a (q : ℤ))
    (hε : |ε| ≤ K * ((1 : ℤ) : ℝ) / (q * N)) (hKN : (p : ℝ) * K < N) : q = p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hεeq : ε = ((q : ℤ) - a * p : ℤ) / (p * q) := by
    have : ε = 1 / p - a / q := by simp only [Int.cast_one, one_mul] at hα; linarith
    rw [this]; push_cast; field_simp
  by_cases hz : (q : ℤ) - a * p = 0
  · have hqa : (q : ℤ) = a * p := by linarith
    rw [hqa] at hcop
    have hu : IsUnit a := isCoprime_self.mp (hcop.of_mul_right_left)
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · rw [h1] at hqa; exact_mod_cast (by simpa using hqa : (q : ℤ) = p)
    · rw [h1] at hqa
      have : (0 : ℤ) < q := by exact_mod_cast hq
      have : (0 : ℤ) < p := by exact_mod_cast hp
      omega
  · exfalso
    set z : ℝ := |(((q : ℤ) - a * p : ℤ) : ℝ)| with hzdef
    have h1 : (1 : ℝ) ≤ z := by
      rw [hzdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
    rw [hεeq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < p * q)] at hε
    simp only [Int.cast_one, mul_one] at hε
    rw [← hzdef, div_le_div_iff₀ (by positivity) (by positivity)] at hε
    have h2 : z * N ≤ K * p := by
      have : q * (z * N) ≤ q * (K * p) := by nlinarith
      exact le_of_mul_le_mul_left this hq0
    nlinarith

/-- QUESTION answered: the statement `Lemma71Choice` of Prop51Split1122b.lean is FALSE. It passes
`A (3C)^C` into the threshold slot of `Lemma71Adapted` and `A` into the denominator slot, so the
threshold for `q_k / (q_k, Q²)` equals the bound `(log N)^B` on `Q` itself. Counterexample:
`C = 2`, `A = 1`, `W = 1`, `α_k = 1/p_k` with distinct primes `p_1, p_2 < (log N)^{36}` and
`p_1 p_2 > (log N)^{36}`: the approximation forces `q_k = p_k`, so both `p_k ∣ Q` and
`Q ≥ p_1 p_2 > (log N)^{36}`. -/
theorem lemma71_choice_false : ¬ Lemma71Choice := by
  intro h
  obtain ⟨N₀, hN⟩ := h 2 1 1 le_rfl
  obtain ⟨N₁, hN₁⟩ := lemma71_eventually 136
  set N : ℕ := max (max N₀ N₁) 8 with hNdef
  obtain ⟨hL1, hLN⟩ := hN₁ N ((le_max_right _ _).trans (le_max_left _ _))
  set L : ℝ := Real.log N with hL
  have hL2 : 2 ≤ L := by
    have h8 : (8 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _ : 8 ≤ N)
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  set s : ℝ := L ^ 18 with hs
  have hs2 : (2 : ℝ) ^ 18 ≤ s := pow_le_pow_left₀ (by norm_num) hL2 18
  set n : ℕ := ⌈s⌉₊ with hn
  have hns : s ≤ n := Nat.le_ceil s
  have hns' : (n : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0] at hns; simp at hns; linarith
  obtain ⟨p1, hp1, hp1a, hp1b⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  obtain ⟨p2, hp2, hp2a, hp2b⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * n) (by omega)
  have hT : L ^ 36 = s ^ 2 := by rw [hs, ← pow_mul]
  have hp2T : (p2 : ℝ) < L ^ 36 := by
    rw [hT]
    have : (p2 : ℝ) ≤ 4 * n := by exact_mod_cast (by omega : p2 ≤ 4 * n)
    nlinarith
  have hp1T : (p1 : ℝ) < L ^ 36 := by
    have : (p1 : ℝ) ≤ p2 := by exact_mod_cast (by omega : p1 ≤ p2)
    linarith
  have hprod : L ^ 36 < (p1 : ℝ) * p2 := by
    rw [hT]
    have h1 : (n : ℝ) < p1 := by exact_mod_cast hp1a
    have h2 : (2 * n : ℝ) < p2 := by exact_mod_cast hp2a
    have hs0 : 0 ≤ s := by linarith
    nlinarith
  set p : Fin 2 → ℕ := ![p1, p2] with hpdef
  have hpT : ∀ k, (p k : ℝ) < L ^ 36 := by
    intro k; fin_cases k
    · simpa [hpdef] using hp1T
    · simpa [hpdef] using hp2T
  have hp1' : ∀ k, 1 ≤ p k := by
    intro k; fin_cases k
    · simpa [hpdef] using hp1.one_lt.le
    · simpa [hpdef] using hp2.one_lt.le
  obtain ⟨Q, hQ1, hQb, hAd⟩ := hN (fun k => 1 / (p k : ℝ)) N
    ((le_max_left _ _).trans (le_max_left _ _))
  have hdvd : ∀ k, p k ∣ Q := by
    intro k
    obtain ⟨a, q, ε, hα, hcop, hq1, -, hε, hor⟩ := hAd k
    have hKN : (p k : ℝ) * L ^ (100 * 1) < N := by
      have hLp : (0 : ℝ) < L ^ 100 := by positivity
      calc (p k : ℝ) * L ^ (100 * 1) < L ^ 36 * L ^ 100 := by
            simpa using mul_lt_mul_of_pos_right (hpT k) hLp
        _ = L ^ 136 := by rw [← pow_add]
        _ ≤ N := hLN
    have hNpos : (0 : ℝ) < N := by
      have : (8 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _ : 8 ≤ N)
      linarith
    have hqp := lemma71_rigid (p k) (hp1' k) a q ε _ N hq1 (by positivity) hNpos hα hcop hε hKN
    subst hqp
    rcases hor with hd | hge
    · exact hd
    · exfalso
      have hg : (1 : ℝ) ≤ (Nat.gcd (p k) (Q ^ 2) : ℝ) := by
        exact_mod_cast Nat.gcd_pos_of_pos_left _ (hp1' k)
      have : (p k : ℝ) / (Nat.gcd (p k) (Q ^ 2) : ℝ) ≤ p k :=
        div_le_self (by positivity) hg
      have := hpT k
      rw [show (1 * (3 * 2) ^ 2 : ℕ) = 36 from rfl] at hge
      linarith
  have h1 : p1 ∣ Q := by simpa [hpdef] using hdvd 0
  have h2 : p2 ∣ Q := by simpa [hpdef] using hdvd 1
  have hne : p1 ≠ p2 := by omega
  have hcp : Nat.Coprime p1 p2 := (Nat.coprime_primes hp1 hp2).mpr hne
  have h12 : p1 * p2 ∣ Q := hcp.mul_dvd_of_dvd_of_dvd h1 h2
  have hle : p1 * p2 ≤ Q := Nat.le_of_dvd (by omega) h12
  have hle' : (p1 : ℝ) * p2 ≤ Q := by exact_mod_cast hle
  have : (Q : ℝ) ≤ L ^ 36 := by simpa using hQb
  linarith

/-- The target LEAF `lemma71_choice` of Prop51Split1122b.lean, stated literally, is refuted. -/
theorem lemma71_choice_refuted : ¬ type_of% @LeanLab.Teravainen2016.lemma71_choice :=
  lemma71_choice_false

end LeanLab.Teravainen2016

#print axioms LeanLab.Teravainen2016.lemma71_choice_paper
#print axioms LeanLab.Teravainen2016.lemma71_choice_false
#print axioms LeanLab.Teravainen2016.lemma71_choice_refuted
#print axioms LeanLab.Teravainen2016.lemma71_pigeonhole
#print axioms LeanLab.Teravainen2016.lemma71_dirichlet
