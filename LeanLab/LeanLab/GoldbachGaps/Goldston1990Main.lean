/-
P0030 D. A. Goldston, Linnik's theorem on Goldbach numbers in short intervals,
Glasgow Math. J. 32 (1990) 285-297, read 2026-10-19 from the Cambridge PDF, papers/P0030.pdf,
pages 285 and 286 checked as page images. Unit U-5029.
STATED, as Props taken as hypotheses, CITED: J(N, h) of display 2, R(n) and r(n) of display 5,
the Theorem, display 6, Corollaries 1 and 2, and the upper half of the pair correlation
asymptotic, display 9.
PROVED from them, zero sorry: `near_of_theorem6`, the Theorem puts a sum of two primes in
`[N - K, N + K]` once `J(N, K) ≤ K² N / 2` and `K > 4C`; and `short_of_theorem6_pc`, the remark
on page 287 that under display 9 every interval of length about `(2 + ε) log N` around `N`
holds a sum of two primes for large `N`. The lab's I-5002 is an explicit relative-δ version of
this bilinear method. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

/-- Display 2: `J(N, h) = ∫_1^N (θ(x + h) - θ(x) - h)² dx`. -/
noncomputable def Jg (N h : ℝ) : ℝ := ∫ x in (1 : ℝ)..N, (θ (x + h) - θ x - h) ^ 2

/-- Display 5: `R(m) = Σ_{p + p' = m} log p log p'`, ordered pairs of primes. -/
noncomputable def Rg (m : ℕ) : ℝ :=
  ∑ p ∈ range m, if p.Prime ∧ (m - p).Prime then Real.log p * Real.log ((m - p : ℕ) : ℝ) else 0

/-- Display 5: `r(m) = #{(p, p') : p + p' = m}`. -/
noncomputable def rg (m : ℕ) : ℕ := ((range m).filter (fun p => p.Prime ∧ (m - p).Prime)).card

/-- The Fejér sum of display 6, `Σ_{|n| ≤ K} (K - |n|) R(N + n)`, indexed by `j = n + K`. -/
noncomputable def fejer (N K : ℕ) : ℝ :=
  ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * Rg (N + j - K)

/-- The Theorem, display 6: for integers `1 ≤ K ≤ N / log³ N` and all large `N`,
`|Σ (K - |n|) R(N + n) - K² N| ≤ J(N, K) + O(K N) + o(K² N)`. The lab reads the `O` and the
`o` as uniform in `K` over that range. CITED. -/
def Theorem6 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 1 ≤ K →
    (K : ℝ) ≤ N / Real.log N ^ 3 →
    |fejer N K - (K : ℝ) ^ 2 * N| ≤ Jg N K + C * K * N + ε * (K : ℝ) ^ 2 * N

/-- Corollary 1: if `J(N, K) = o(K² N)` then `Σ_{N ≤ n ≤ N + K} r(n) ~ K N / log² N`. The lab
adds the Theorem's range `1 ≤ K ≤ N / log³ N`. CITED. -/
def Corollary1 : Prop :=
  ∀ K : ℕ → ℕ, (∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3) →
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1)

/-- Corollary 2: if `J(N, K) = o(K² N)` and `K ≥ C log² N`, `C` a large absolute constant, then
`#{N ≤ n ≤ N + K : r(n) ≥ 1} ≫ K`. The lab adds `K ≤ N / log³ N`. CITED. -/
def Corollary2 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ K : ℕ → ℕ,
    (∀ᶠ N : ℕ in atTop, C * Real.log N ^ 2 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3) →
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    ∀ᶠ N : ℕ in atTop, c * K N ≤ (((Icc N (N + K N)).filter (fun n => 1 ≤ rg n)).card : ℝ)

/-- The upper half of display 9, `J(N, h) ≤ (1 + ε) h N log N` for `1 ≤ h ≤ √N`, which display 9,
`J(N, h) ~ h N log(N/h)` for `1 ≤ h ≤ N^{1-ε}`, implies. Under RH it is equivalent to a form of
Montgomery's pair correlation conjecture; NOT known. -/
def PC9Upper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ √N →
    Jg N h ≤ (1 + ε) * h * N * Real.log N

theorem Rg_eq_zero {m : ℕ} (h : ¬ IsGoldbachSum m) : Rg m = 0 := by
  unfold Rg
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg]
  rintro ⟨hp1, hp2⟩
  exact h ⟨p, m - p, hp1, hp2, by have := Finset.mem_range.mp hp; omega⟩

/-- If no sum of two primes lies in `[N - K, N + K]`, the Fejér sum vanishes. -/
theorem fejer_eq_zero {N K : ℕ} (hKN : K ≤ N)
    (h : ∀ m, N - K ≤ m → m ≤ N + K → ¬ IsGoldbachSum m) : fejer N K = 0 := by
  unfold fejer
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [Rg_eq_zero (h _ (by omega) (by omega)), mul_zero]

theorem log_cube_ge_one {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N ^ 3 := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have : 1 ≤ Real.log N := by
    have := Real.log_le_log (by norm_num) h3
    have h3e : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  nlinarith [pow_le_pow_left₀ zero_le_one this 3]

theorem K_le_N {N K : ℕ} (hN : 3 ≤ N) (hK : (K : ℝ) ≤ N / Real.log N ^ 3) : K ≤ N := by
  have h1 := log_cube_ge_one hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have : (N : ℝ) / Real.log N ^ 3 ≤ N := div_le_self hN0 h1
  exact_mod_cast le_trans hK this

/-- From the Theorem: a sum of two primes in `[N - K, N + K]` whenever `K > 4C`,
`K ≤ N / log³ N` and `J(N, K) ≤ K² N / 2`, for all large `N`. -/
theorem near_of_theorem6 (h : Theorem6) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 4 * C < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Jg N K ≤ (K : ℝ) ^ 2 * N / 2 →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ IsGoldbachSum m := by
  obtain ⟨C, hC, hε⟩ := h
  obtain ⟨N0, hN0⟩ := hε (1 / 4) (by norm_num)
  refine ⟨C, hC, max N0 3, fun N hN K hK4 hKN hJ => ?_⟩
  by_contra hno
  push_neg at hno
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by linarith
    exact_mod_cast this
  have hKle := K_le_N hN3 hKN
  have hf := fejer_eq_zero hKle (fun m h1 h2 hm => hno m h1 h2 hm)
  have := hN0 N (le_trans (le_max_left _ _) hN) K hK1 hKN
  rw [hf, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have : (K : ℝ) ^ 2 * N / 4 ≤ C * K * N := by linarith
  have : (K : ℝ) * ((K : ℝ) * N) ≤ (4 * C) * ((K : ℝ) * N) := by nlinarith
  have := le_of_mul_le_mul_right this (by positivity)
  linarith

/-- Eventually `A ≤ log N`, `(2 log N + 1)² ≤ N` and `(2 log N + 1) log³ N ≤ N`. -/
theorem eventually_log_small (A : ℝ) :
    ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → A ≤ Real.log N ∧ 1 ≤ Real.log N ∧
      (2 * Real.log N + 1) ^ 2 ≤ N ∧ (2 * Real.log N + 1) * Real.log N ^ 3 ≤ N := by
  have t1 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 / (1 * x + 0) ≤ 1 / 9 :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).eventually
      (ge_mem_nhds (by norm_num))
  have t2 : ∀ᶠ x : ℝ in atTop, max A 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have t3 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hall := (t1.and (t2.and t3))
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hall
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hN
  refine ⟨N1, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN1 N hN
  set L := Real.log N
  have hx : (0 : ℝ) < N := by linarith
  rw [one_mul, add_zero, div_le_iff₀ hx] at h1
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) h2
  refine ⟨le_trans (le_max_left _ _) h2, hL1, ?_, ?_⟩
  · nlinarith [pow_le_pow_left₀ zero_le_one hL1 2, pow_le_pow_left₀ zero_le_one hL1 4]
  · nlinarith [pow_le_pow_left₀ zero_le_one hL1 3, pow_le_pow_left₀ zero_le_one hL1 4]

/-- Page 287: subject to display 9, for all large `N` the interval
`[N - (1+ε) log N - 1, N + (1+ε) log N + 1]`, of length about `(2 + 2ε) log N`, holds a sum of
two primes. CONDITIONAL ON the Theorem and `PC9Upper`, which is not known. -/
theorem short_of_theorem6_pc (h : Theorem6) (hPC : PC9Upper) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ m : ℕ, IsGoldbachSum m ∧
      (N : ℝ) - ((1 + ε) * Real.log N + 1) ≤ m ∧ (m : ℝ) ≤ N + ((1 + ε) * Real.log N + 1) := by
  obtain ⟨C, hC, hT⟩ := h
  obtain ⟨Na, hNa⟩ := hT (ε / 4) (by positivity)
  obtain ⟨Nb, hNb⟩ := hPC (ε / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := eventually_log_small (4 * C / ε + 1)
  refine ⟨max (max Na Nb) (max N1 3), fun N hN => ?_⟩
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hA, hL1, hsq, hcube⟩ := hN1 N hN1'
  set L := Real.log N with hL
  set K := ⌈(1 + ε) * L⌉₊ with hKdef
  have hK1 : (1 + ε) * L ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < (1 + ε) * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := by nlinarith
  have hKone : 1 ≤ K := by exact_mod_cast (show (1 : ℝ) ≤ K by nlinarith)
  have hK2L : (K : ℝ) ≤ 2 * L + 1 := by nlinarith
  have hKsq : (K : ℝ) ≤ √N := by
    rw [Real.le_sqrt hKpos.le hNpos.le]
    exact le_trans (pow_le_pow_left₀ hKpos.le hK2L 2) hsq
  have hL3 : 0 < L ^ 3 := by positivity
  have hKcube : (K : ℝ) ≤ N / L ^ 3 := by
    rw [le_div_iff₀ hL3]
    exact le_trans (mul_le_mul_of_nonneg_right hK2L hL3.le) hcube
  by_contra hno
  push_neg at hno
  have hKle := K_le_N hN3 hKcube
  have hf := fejer_eq_zero hKle (fun m h1 h2 hm => by
    have hm1 : (N : ℝ) - K ≤ m := by
      have : ((N - K : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
      rw [Nat.cast_sub hKle] at this; exact this
    have hm2 : (m : ℝ) ≤ N + K := by exact_mod_cast h2
    have := hno m hm
    by_cases ha : (N : ℝ) - ((1 + ε) * L + 1) ≤ m
    · exact absurd (this ha) (by push_neg; linarith)
    · push_neg at ha; linarith)
  have hT' := hNa N hNa' K hKone hKcube
  have hJ := hNb N hNb' K hKone hKsq
  rw [hf, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at hT'
  -- K² N ≤ (1 + ε/4) K N L + C K N + (ε/4) K² N, divide by K N
  have hKN : (0 : ℝ) < K * N := by positivity
  have hmain : (K : ℝ) * (1 - ε / 4) * (K * N) ≤ ((1 + ε / 4) * L + C) * (K * N) := by nlinarith
  have h2 := le_of_mul_le_mul_right hmain hKN
  -- (1 + ε)(1 - ε/4) L ≤ K (1 - ε/4) ≤ (1 + ε/4) L + C, so (ε/4) L ≤ C
  have h3 : (1 + ε) * L * (1 - ε / 4) ≤ (K : ℝ) * (1 - ε / 4) :=
    mul_le_mul_of_nonneg_right hK1 (by linarith)
  have h4 : ε / 4 * L ≤ C := by nlinarith
  have h5 : 4 * C / ε + 1 ≤ L := hA
  have h6 : 4 * C / ε * (ε / 4) = C := by field_simp
  nlinarith

/-! Even sums. Goldston's Goldbach numbers are even, page 285. An odd `m` is a sum of two
primes only as `2 + (m - 2)`, so it adds at most `2 log 2 log m` to `R(m)`, and the odd terms
of the Fejér sum are `O(K² log N) = o(K² N)`. -/

theorem Rg_nonneg (m : ℕ) : 0 ≤ Rg m := by
  unfold Rg
  apply Finset.sum_nonneg
  intro p _
  split_ifs with h
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · exact le_rfl

theorem Rg_odd_le {m : ℕ} (hm : Odd m) : Rg m ≤ 2 * (Real.log 2 * Real.log m) := by
  unfold Rg
  have hpt : ∀ p ∈ range m, (if p.Prime ∧ (m - p).Prime then Real.log p * Real.log ((m - p : ℕ) : ℝ)
      else 0) ≤ if p = 2 ∨ p = m - 2 then Real.log 2 * Real.log m else 0 := by
    intro p hp
    have hpm := Finset.mem_range.mp hp
    split_ifs with h1 h2 h2
    · rcases h2 with rfl | rfl
      · push_cast
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast h1.2.pos)
          (by exact_mod_cast Nat.sub_le m 2)) (Real.log_nonneg (by norm_num))
      · have h2' : m - (m - 2) = 2 := by have := h1.1.two_le; omega
        rw [h2', mul_comm]
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
        exact Real.log_le_log (by exact_mod_cast h1.1.pos) (by exact_mod_cast hpm.le)
    · exfalso
      push_neg at h2
      have o1 := h1.1.odd_of_ne_two h2.1
      have o2 := h1.2.odd_of_ne_two (by omega)
      have : Even (p + (m - p)) := o1.add_odd o2
      rw [show p + (m - p) = m by omega] at this
      exact (Nat.not_even_iff_odd.mpr hm) this
    · exact mul_nonneg (Real.log_nonneg (by norm_num)) (Real.log_natCast_nonneg _)
    · exact le_rfl
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : ((range m).filter (fun p => p = 2 ∨ p = m - 2)).card ≤ 2 := by
    calc ((range m).filter (fun p => p = 2 ∨ p = m - 2)).card ≤ ({2, m - 2} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro p hp
          rcases (Finset.mem_filter.mp hp).2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  have hl : 0 ≤ Real.log 2 * Real.log m :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (Real.log_natCast_nonneg _)
  have : (((range m).filter (fun p => p = 2 ∨ p = m - 2)).card : ℝ) ≤ 2 := by exact_mod_cast hc
  nlinarith

/-- If no even sum of two primes lies in `[N - K, N + K]`, the Fejér sum is at most
`3 K² · 2 log 2 log (2N)`. -/
theorem fejer_le_of_noEven {N K : ℕ} (hK1 : 1 ≤ K) (hKN : K ≤ N)
    (h : ∀ m, N - K ≤ m → m ≤ N + K → Even m → ¬ IsGoldbachSum m) :
    fejer N K ≤ 3 * (K : ℝ) ^ 2 * (2 * (Real.log 2 * Real.log (2 * N))) := by
  unfold fejer
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hK1 hKN
  have hc : 0 ≤ 2 * (Real.log 2 * Real.log (2 * N)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.log_nonneg (by norm_num))
      (Real.log_nonneg (by linarith)))
  have hterm : ∀ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * Rg (N + j - K)
      ≤ (K : ℝ) * (2 * (Real.log 2 * Real.log (2 * N))) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hw0 : 0 ≤ (K : ℝ) - |(j : ℝ) - K| := by
      rw [sub_nonneg, abs_le]; constructor
      · have : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
      · have : (j : ℝ) ≤ 2 * K := by exact_mod_cast (by omega : j ≤ 2 * K)
        linarith
    have hwK : (K : ℝ) - |(j : ℝ) - K| ≤ K := by linarith [abs_nonneg ((j : ℝ) - K)]
    have hR : Rg (N + j - K) ≤ 2 * (Real.log 2 * Real.log (2 * N)) := by
      rcases Nat.even_or_odd (N + j - K) with he | ho
      · rw [Rg_eq_zero (h _ (by omega) (by omega) he)]; exact hc
      · refine (Rg_odd_le ho).trans ?_
        have hm : ((N + j - K : ℕ) : ℝ) ≤ 2 * N := by
          exact_mod_cast (by omega : N + j - K ≤ 2 * N)
        by_cases h0 : N + j - K = 0
        · rw [h0, Nat.cast_zero, Real.log_zero, mul_zero, mul_zero]; exact hc
        · have hm0 : (0 : ℝ) < ((N + j - K : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
          have := Real.log_le_log hm0 hm
          have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith
    calc ((K : ℝ) - |(j : ℝ) - K|) * Rg (N + j - K) ≤ K * Rg (N + j - K) :=
          mul_le_mul_of_nonneg_right hwK (Rg_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  push_cast
  have h3 : (2 * (K : ℝ) + 1) * K ≤ 3 * (K : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right h3 hc
  nlinarith

/-- `near_of_theorem6` with an EVEN sum of two primes, Goldston's Goldbach number. -/
theorem near_even_of_theorem6 (h : Theorem6) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 4 * C < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Jg N K ≤ (K : ℝ) ^ 2 * N / 2 →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ Even m ∧ IsGoldbachSum m := by
  obtain ⟨C, hC, hε⟩ := h
  obtain ⟨N0, hN0⟩ := hε (1 / 8) (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_log_small 6
  refine ⟨C, hC, max (max N0 N1) 3, fun N hN K hK4 hKN hJ => ?_⟩
  by_contra hno
  push_neg at hno
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hA, hL1, -, hcube⟩ := hN1 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by linarith
    exact_mod_cast this
  have hKle := K_le_N hN3 hKN
  have hf := fejer_le_of_noEven hK1 hKle (fun m h1 h2 he hm => hno m h1 h2 he hm)
  have hT := hN0 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) K hK1 hKN
  have hab := neg_abs_le (fejer N K - (K : ℝ) ^ 2 * N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  -- 2 log 2 log(2N) ≤ 2 (1 + log N) ≤ N / 24
  set L := Real.log N with hL
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2N : Real.log (2 * N) = Real.log 2 + L := Real.log_mul (by norm_num) hNpos.ne'
  have hL3 : 216 ≤ L ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hA 3]
  have hsmall : 2 * (Real.log 2 * Real.log (2 * N)) ≤ N / 24 := by
    rw [hlog2N]
    have : 2 * (Real.log 2 * (Real.log 2 + L)) ≤ 2 * (1 + L) := by nlinarith
    have : 216 * (2 * L + 1) ≤ N := by nlinarith
    linarith
  have hodd : fejer N K ≤ (K : ℝ) ^ 2 * N / 8 := by
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 2)
    linarith
  -- K² N - K² N/8 ≤ K² N/2 + C K N + K² N/8, so K ≤ 4C
  have : (K : ℝ) ^ 2 * N / 4 ≤ C * K * N := by linarith
  have : (K : ℝ) * ((K : ℝ) * N) ≤ (4 * C) * ((K : ℝ) * N) := by nlinarith
  have := le_of_mul_le_mul_right this (by positivity)
  linarith

set_option maxHeartbeats 800000 in
/-- `short_of_theorem6_pc` with an EVEN sum of two primes, Goldston's Goldbach number: subject to
display 9, for all large `N` a Goldbach number within `(1 + ε) log N + 1` of `N`. CONDITIONAL ON
the Theorem and `PC9Upper`, which is not known. -/
theorem short_even_of_theorem6_pc (h : Theorem6) (hPC : PC9Upper) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ m : ℕ, Even m ∧ IsGoldbachSum m ∧
      (N : ℝ) - ((1 + ε) * Real.log N + 1) ≤ m ∧ (m : ℝ) ≤ N + ((1 + ε) * Real.log N + 1) := by
  obtain ⟨C, hC, hT⟩ := h
  obtain ⟨Na, hNa⟩ := hT (ε / 8) (by positivity)
  obtain ⟨Nb, hNb⟩ := hPC (ε / 8) (by positivity)
  obtain ⟨N1, hN1⟩ := eventually_log_small (4 * C / ε + 48 / ε + 1)
  refine ⟨max (max Na Nb) (max N1 3), fun N hN => ?_⟩
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hA, hL1, hsq, hcube⟩ := hN1 N hN1'
  set L := Real.log N with hL
  set K := ⌈(1 + ε) * L⌉₊ with hKdef
  have hK1 : (1 + ε) * L ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < (1 + ε) * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := by nlinarith
  have hKone : 1 ≤ K := by exact_mod_cast (show (1 : ℝ) ≤ K by nlinarith)
  have hK2L : (K : ℝ) ≤ 2 * L + 1 := by nlinarith
  have hKsq : (K : ℝ) ≤ √N := by
    rw [Real.le_sqrt hKpos.le hNpos.le]
    exact le_trans (pow_le_pow_left₀ hKpos.le hK2L 2) hsq
  have hL3 : 0 < L ^ 3 := by positivity
  have hKcube : (K : ℝ) ≤ N / L ^ 3 := by
    rw [le_div_iff₀ hL3]
    exact le_trans (mul_le_mul_of_nonneg_right hK2L hL3.le) hcube
  by_contra hno
  push_neg at hno
  have hKle := K_le_N hN3 hKcube
  have hf := fejer_le_of_noEven hKone hKle (fun m h1 h2 he hm => by
    have hm1 : (N : ℝ) - K ≤ m := by
      have : ((N - K : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
      rw [Nat.cast_sub hKle] at this; exact this
    have hm2 : (m : ℝ) ≤ N + K := by exact_mod_cast h2
    have := hno m he hm
    by_cases ha : (N : ℝ) - ((1 + ε) * L + 1) ≤ m
    · exact absurd (this ha) (by push_neg; linarith)
    · push_neg at ha; linarith)
  have hT' := hNa N hNa' K hKone hKcube
  have hJ := hNb N hNb' K hKone hKsq
  have hab := neg_abs_le (fejer N K - (K : ℝ) ^ 2 * N)
  -- the odd terms: 3 K² · 2 log 2 log(2N) ≤ (ε/8) K² N
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2N : Real.log (2 * N) = Real.log 2 + L := Real.log_mul (by norm_num) hNpos.ne'
  have hAε : 48 / ε ≤ L := by
    have : 0 ≤ 4 * C / ε := by positivity
    linarith
  have hsmall : 3 * (2 * (Real.log 2 * Real.log (2 * N))) ≤ ε / 8 * N := by
    rw [hlog2N]
    have e1 : 3 * (2 * (Real.log 2 * (Real.log 2 + L))) ≤ 6 * (1 + L) := by nlinarith
    have e2 : 48 / ε * ε = 48 := by field_simp
    have e3 : 48 ≤ L * ε := by
      have := mul_le_mul_of_nonneg_right hAε hε.le; rw [e2] at this; linarith
    have e4 : (1 + L) * L ^ 3 ≤ N := le_trans (by nlinarith) hcube
    have e5 : L ≤ L ^ 3 := by
      have := pow_le_pow_left₀ zero_le_one hL1 2
      nlinarith
    have e5' : L * ε ≤ L ^ 3 * ε := mul_le_mul_of_nonneg_right e5 hε.le
    have e6 : (1 + L) * 48 ≤ (1 + L) * (L ^ 3 * ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e7 : (1 + L) * L ^ 3 * ε ≤ N * ε := mul_le_mul_of_nonneg_right e4 hε.le
    have e8 : (1 + L) * (L ^ 3 * ε) = (1 + L) * L ^ 3 * ε := by ring
    linarith
  have hodd : fejer N K ≤ ε / 8 * (K : ℝ) ^ 2 * N := by
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2)
    nlinarith
  have hKN : (0 : ℝ) < K * N := by positivity
  have hmain : (K : ℝ) * (1 - ε / 4) * (K * N) ≤ ((1 + ε / 8) * L + C) * (K * N) := by nlinarith
  have h2 := le_of_mul_le_mul_right hmain hKN
  have h3 : (1 + ε) * L * (1 - ε / 4) ≤ (K : ℝ) * (1 - ε / 4) :=
    mul_le_mul_of_nonneg_right hK1 (by linarith)
  have h4 : 3 * ε / 8 * L ≤ C := by nlinarith
  have h5 : 4 * C / ε ≤ L := by
    have : 0 ≤ 48 / ε := by positivity
    linarith
  have h6 : 4 * C / ε * ε = 4 * C := by field_simp
  have h7 := mul_le_mul_of_nonneg_right h5 hε.le
  rw [h6] at h7
  nlinarith

end LeanLab.GoldbachGaps.Goldston1990
