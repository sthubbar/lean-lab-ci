import Mathlib

/-!
# Goldston 1990, the Theorem of display 6, explicit form: core

Lab proof, unit U-6300, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990; the route is the lab's own.

Goldston proves display 6 by the circle method: the Fejér kernel `T(α) = |Σ_{a<K} e(aα)|²` is
nonnegative, so the minor arc integral of `S(α)² T(α) e(-Nα)` is at most that of `|S(α)|² T(α)`,
which is `J(N, K)` up to lower order terms. This file does the same step with no integral: for a
function `e` on the integers, with window sums `X(z) = Σ_{a<K} e(z - a)`, the Fejér weighted
self convolution is `Σ_z X(z) X(c - z)`, and AM-GM bounds it by `Σ_z X(z)²`, a discrete `J`.
Splitting the weight `log p` on primes `p ≤ N` as `1 + e` gives

`|Σ_{|n| ≤ K} (K - |n|) R(N + n) - K² N| ≤ Σ_{1 ≤ m < N} (θ(m + K) - θ(m) - K)²`
  `+ 2 K² |θ(N) - N| + K³ (2 log²(N + K) + 1 + 2 (log N + 1) + 2 (log N + 1)²)`

for all naturals `1 ≤ K ≤ N`, `fejerC_explicit`, with no cited input. The sum on the right is
`J(N, K)` exactly, `jg_eq_sum`; the link is in `Goldston1990Thm6.lean`.

Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean
kernel.
-/

namespace LeanLab.GoldbachGaps.Goldston1990.Thm6
open Real Chebyshev Finset

/-- `log p` at primes, `0` elsewhere. -/
noncomputable def lp (u : ℕ) : ℝ := if u.Prime then Real.log u else 0

/-- Display 5, the same definition as `Goldston1990.Rg`. -/
noncomputable def RgC (m : ℕ) : ℝ :=
  ∑ p ∈ range m, if p.Prime ∧ (m - p).Prime then Real.log p * Real.log ((m - p : ℕ) : ℝ) else 0

/-- Display 6's Fejér sum, the same definition as `Goldston1990.fejer`. -/
noncomputable def fejerC (N K : ℕ) : ℝ :=
  ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * RgC (N + j - K)

/-- `log p` on primes `p ≤ N`. -/
noncomputable def fN (N u : ℕ) : ℝ := if u ≤ N then lp u else 0

/-- The indicator of `[1, N]`. -/
noncomputable def gN (N u : ℕ) : ℝ := if 1 ≤ u ∧ u ≤ N then 1 else 0

/-- The error `e = f - g`. -/
noncomputable def eN (N u : ℕ) : ℝ := fN N u - gN N u

/-- The window sum `X(z) = Σ_{a<K} F(z - a)`, truncated subtraction. -/
noncomputable def win (K : ℕ) (F : ℕ → ℝ) (z : ℕ) : ℝ := ∑ a ∈ range K, F (z - a)

/-- The bilinear form `Σ_{z < N + K} X_F(z) X_G(N + K - 1 - z)`. -/
noncomputable def bil (N K : ℕ) (F G : ℕ → ℝ) : ℝ :=
  ∑ z ∈ range (N + K), win K F z * win K G (N + K - 1 - z)

/-- The self convolution `Σ_{u ≤ m} F(u) F(m - u)`. -/
noncomputable def conv (F : ℕ → ℝ) (m : ℕ) : ℝ := ∑ u ∈ range (m + 1), F u * F (m - u)

/-! ### θ on the naturals -/

lemma lp_nonneg (u : ℕ) : 0 ≤ lp u := by
  unfold lp; split_ifs
  · exact Real.log_natCast_nonneg u
  · exact le_refl 0

lemma lp_le {u M : ℕ} (hu : u ≤ M) : lp u ≤ Real.log M := by
  unfold lp; split_ifs with hp
  · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hu)
  · exact Real.log_natCast_nonneg M

lemma theta_nat (n : ℕ) : θ (n : ℝ) = ∑ u ∈ range (n + 1), lp u := by
  rw [theta_eq_sum_Icc, Nat.floor_natCast, sum_filter]
  have : Icc 0 n = range (n + 1) := by ext x; simp
  rw [this]; rfl

lemma theta_nat_succ (m : ℕ) : θ ((m + 1 : ℕ) : ℝ) = θ (m : ℝ) + lp (m + 1) := by
  rw [theta_nat, theta_nat, sum_range_succ]

lemma win_lp (z : ℕ) : ∀ K : ℕ, K ≤ z →
    ∑ a ∈ range K, lp (z - a) = θ (z : ℝ) - θ ((z - K : ℕ) : ℝ)
  | 0, _ => by simp
  | K + 1, hK => by
    rw [sum_range_succ, win_lp z K (by omega)]
    have hm : z - K = (z - (K + 1)) + 1 := by omega
    rw [hm, theta_nat_succ]; ring

/-! ### Shifts and reflections -/

lemma sum_shift (φ : ℕ → ℝ) {M a : ℕ} (ha : a ≤ M) (h0 : ∀ z < a, φ z = 0) :
    ∑ z ∈ range M, φ z = ∑ u ∈ range (M - a), φ (a + u) := by
  rw [← sum_range_add_sum_Ico _ ha, sum_Ico_eq_sum_range]
  have : ∑ z ∈ range a, φ z = 0 := sum_eq_zero fun z hz => h0 z (mem_range.mp hz)
  rw [this, zero_add]

lemma sum_range_eq_of_vanish (φ : ℕ → ℝ) {m M : ℕ} (hmM : m ≤ M) (h : ∀ u, m ≤ u → u < M → φ u = 0) :
    ∑ u ∈ range M, φ u = ∑ u ∈ range m, φ u := by
  symm
  apply sum_subset (range_subset_range.mpr hmM)
  intro u hu hu'
  simp only [mem_range, not_lt] at hu hu'
  exact h u hu' hu

/-- The sum of all windows. -/
lemma sum_win (N K : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (hN : ∀ u, N < u → F u = 0) :
    ∑ z ∈ range (N + K), win K F z = K * ∑ u ∈ range (N + 1), F u := by
  unfold win
  rw [sum_comm]
  have : ∀ a ∈ range K, ∑ z ∈ range (N + K), F (z - a) = ∑ u ∈ range (N + 1), F u := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [sum_shift (fun z => F (z - a)) (by omega : a ≤ N + K)
      (fun z hz => by show F (z - a) = 0; rw [Nat.sub_eq_zero_of_le hz.le, h0])]
    simp only [Nat.add_sub_cancel_left]
    exact sum_range_eq_of_vanish F (by omega) (fun u hu _ => hN u (by omega))
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

lemma bil_comm (N K : ℕ) (F G : ℕ → ℝ) : bil N K F G = bil N K G F := by
  unfold bil
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro z hz
  have hz' := mem_range.mp hz
  rw [show N + K - 1 - (N + K - 1 - z) = z by omega, mul_comm]

lemma win_add (K : ℕ) (F G : ℕ → ℝ) (z : ℕ) :
    win K (fun u => F u + G u) z = win K F z + win K G z := by
  unfold win; rw [sum_add_distrib]

lemma win_sub (K : ℕ) (F G : ℕ → ℝ) (z : ℕ) :
    win K (fun u => F u - G u) z = win K F z - win K G z := by
  unfold win; rw [sum_sub_distrib]

/-! ### The convolution identity -/

/-- One inner sum: `Σ_z F(z - a) F(c - z - b) = (F * F)(c - a - b)`. -/
lemma inner_eq (N K : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (hKN : K ≤ N) {a b : ℕ} (ha : a < K)
    (hb : b < K) :
    ∑ z ∈ range (N + K), F (z - a) * F (N + K - 1 - z - b) = conv F (N + K - 1 - a - b) := by
  rw [sum_shift (fun z => F (z - a) * F (N + K - 1 - z - b)) (by omega : a ≤ N + K)
    (fun z hz => by
      show F (z - a) * F (N + K - 1 - z - b) = 0
      rw [Nat.sub_eq_zero_of_le hz.le, h0, zero_mul])]
  unfold conv
  have hc : ∀ u, F (a + u - a) * F (N + K - 1 - (a + u) - b) =
      F u * F (N + K - 1 - a - b - u) := by
    intro u
    rw [Nat.add_sub_cancel_left, show N + K - 1 - (a + u) - b = N + K - 1 - a - b - u by omega]
  simp only [hc]
  apply sum_range_eq_of_vanish _ (by omega)
  intro u hu _
  rw [Nat.sub_eq_zero_of_le (by omega), h0, mul_zero]

/-- `Σ_z X(z) X(c - z) = Σ_{a,b<K} (F * F)(N + a - b)`. -/
lemma bil_self (N K : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (hKN : K ≤ N) :
    bil N K F F = ∑ a ∈ range K, ∑ b ∈ range K, conv F (N + a - b) := by
  unfold bil win
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  have h1 : ∀ a ∈ range K, ∑ y ∈ range (N + K), ∑ b ∈ range K, F (y - a) * F (N + K - 1 - y - b) =
      ∑ b ∈ range K, conv F (N + K - 1 - a - b) := by
    intro a ha
    rw [sum_comm]
    exact sum_congr rfl fun b hb =>
      inner_eq N K F h0 hKN (mem_range.mp ha) (mem_range.mp hb)
  rw [sum_congr rfl h1]
  rw [← sum_range_reflect (fun a => ∑ b ∈ range K, conv F (N + a - b)) K]
  apply sum_congr rfl
  intro a ha
  have ha' := mem_range.mp ha
  apply sum_congr rfl
  intro b hb
  have hb' := mem_range.mp hb
  congr 1
  omega

/-! ### The Fejér weights -/

lemma inner_count (K j a : ℕ) :
    ∑ b ∈ range K, (if j = a + K - b then (1 : ℝ) else 0) =
      if j ≤ a + K ∧ a < j then 1 else 0 := by
  by_cases hc : j ≤ a + K ∧ a < j
  · rw [if_pos hc, sum_eq_single (a + K - j)]
    · rw [if_pos (by omega)]
    · intro b hb hne
      rw [if_neg]
      intro h; apply hne; have := mem_range.mp hb; omega
    · intro h; exfalso; apply h; rw [mem_range]; omega
  · rw [if_neg hc]
    apply sum_eq_zero
    intro b hb
    have := mem_range.mp hb
    rw [if_neg]
    omega

lemma weight_eq (K j : ℕ) (hj : j ≤ 2 * K) :
    ∑ a ∈ range K, ∑ b ∈ range K, (if j = a + K - b then (1 : ℝ) else 0) =
      (K : ℝ) - |(j : ℝ) - K| := by
  simp_rw [inner_count]
  rw [sum_boole]
  have hf : (range K).filter (fun a => j ≤ a + K ∧ a < j) = Ico (j - K) (min j K) := by
    ext a; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf, Nat.card_Ico]
  rcases le_total j K with h | h
  · rw [min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_zero,
      abs_of_nonpos (by have : (j : ℝ) ≤ K := by exact_mod_cast h
                        linarith)]
    ring
  · rw [min_eq_right h, Nat.cast_sub (by omega), Nat.cast_sub h,
      abs_of_nonneg (by have : (K : ℝ) ≤ j := by exact_mod_cast h
                        linarith)]

lemma weight_nonneg (K j : ℕ) (hj : j ≤ 2 * K) : 0 ≤ (K : ℝ) - |(j : ℝ) - K| := by
  rw [← weight_eq K j hj]
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- `Σ_{a,b<K} h(N + a - b) = Σ_{|n| ≤ K} (K - |n|) h(N + n)`. -/
lemma fejer_reindex (N K : ℕ) (hKN : K ≤ N) (h : ℕ → ℝ) :
    ∑ a ∈ range K, ∑ b ∈ range K, h (N + a - b) =
      ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * h (N + j - K) := by
  have e1 : ∀ a ∈ range K, ∀ b ∈ range K, h (N + a - b) =
      ∑ j ∈ range (2 * K + 1), (if j = a + K - b then (1 : ℝ) else 0) * h (N + j - K) := by
    intro a ha b hb
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    rw [sum_eq_single (a + K - b)]
    · rw [if_pos rfl, one_mul]; congr 1; omega
    · intro j _ hne; rw [if_neg hne, zero_mul]
    · intro hn; exfalso; apply hn; rw [mem_range]; omega
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => e1 a ha b hb]
  rw [sum_congr rfl fun a _ => sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ 2 * K := by have := mem_range.mp hj; omega
  rw [← weight_eq K j hj', sum_mul]
  apply sum_congr rfl; intro a _
  rw [sum_mul]

lemma weight_sum (K : ℕ) : ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) = (K : ℝ) ^ 2 := by
  have := fejer_reindex K K le_rfl (fun _ => 1)
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul, mul_one] at this
  rw [← this]; ring

/-! ### Pieces of `f = g + e` -/

lemma fN_zero (N : ℕ) : fN N 0 = 0 := by simp [fN, lp, Nat.not_prime_zero]
lemma gN_zero (N : ℕ) : gN N 0 = 0 := by simp [gN]
lemma eN_zero (N : ℕ) : eN N 0 = 0 := by simp [eN, fN_zero, gN_zero]

lemma fN_big {N u : ℕ} (h : N < u) : fN N u = 0 := by simp [fN, show ¬ u ≤ N by omega]
lemma gN_big {N u : ℕ} (h : N < u) : gN N u = 0 := by simp [gN]; intro; omega
lemma eN_big {N u : ℕ} (h : N < u) : eN N u = 0 := by simp [eN, fN_big h, gN_big h]

lemma fN_eq : ∀ N, fN N = fun u => gN N u + eN N u := by
  intro N; funext u; simp [eN]

lemma sum_gN (N : ℕ) : ∑ u ∈ range (N + 1), gN N u = N := by
  rw [sum_range_succ']
  simp only [gN]
  rw [sum_congr rfl (g := fun _ => (1 : ℝ)) (fun i hi => by
    have := mem_range.mp hi; rw [if_pos (by omega)])]
  simp

lemma sum_fN (N : ℕ) : ∑ u ∈ range (N + 1), fN N u = θ (N : ℝ) := by
  rw [theta_nat]
  apply sum_congr rfl; intro u hu
  have := mem_range.mp hu
  simp [fN, show u ≤ N by omega]

lemma sum_eN (N : ℕ) : ∑ u ∈ range (N + 1), eN N u = θ (N : ℝ) - N := by
  simp only [eN]; rw [sum_sub_distrib, sum_fN, sum_gN]

lemma gN_mem (N u : ℕ) : 0 ≤ gN N u ∧ gN N u ≤ 1 := by
  unfold gN; split_ifs <;> norm_num

lemma abs_eN_le (N u : ℕ) : |eN N u| ≤ Real.log N + 1 := by
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hg := gN_mem N u
  unfold eN fN
  split_ifs with hu
  · have h1 := lp_nonneg u
    have h2 := lp_le hu
    rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

lemma abs_win_eN (N K z : ℕ) : |win K (eN N) z| ≤ K * (Real.log N + 1) := by
  unfold win
  calc |∑ a ∈ range K, eN N (z - a)| ≤ ∑ a ∈ range K, |eN N (z - a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ range K, (Real.log N + 1) := sum_le_sum fun a _ => abs_eN_le N _
    _ = K * (Real.log N + 1) := by rw [sum_const, card_range, nsmul_eq_mul]

lemma win_gN_mem (N K z : ℕ) : 0 ≤ win K (gN N) z ∧ win K (gN N) z ≤ K := by
  unfold win
  constructor
  · exact sum_nonneg fun a _ => (gN_mem N _).1
  · calc ∑ a ∈ range K, gN N (z - a) ≤ ∑ _a ∈ range K, (1 : ℝ) :=
          sum_le_sum fun a _ => (gN_mem N _).2
      _ = K := by simp

lemma abs_win_gN (N K z : ℕ) : |win K (gN N) z| ≤ K := by
  have := win_gN_mem N K z
  rw [abs_le]; constructor <;> linarith

/-- Inside `[K, N]` the error window is the prime count error `θ(z) - θ(z - K) - K`. -/
lemma win_eN_inside {N K z : ℕ} (hKz : K ≤ z) (hzN : z ≤ N) :
    win K (eN N) z = θ (z : ℝ) - θ ((z - K : ℕ) : ℝ) - K := by
  have he : eN N = fun u => fN N u - gN N u := rfl
  rw [he, win_sub]
  have h1 : win K (fN N) z = θ (z : ℝ) - θ ((z - K : ℕ) : ℝ) := by
    unfold win
    rw [← win_lp z K hKz]
    apply sum_congr rfl; intro a _
    simp [fN, show z - a ≤ N by omega]
  have h2 : win K (gN N) z = K := by
    unfold win
    rw [sum_congr rfl (g := fun _ => (1 : ℝ)) (fun a ha => by
      have := mem_range.mp ha
      simp [gN]; omega)]
    simp
  rw [h1, h2]

/-! ### The three bilinear pieces -/

/-- `X_g` is `K` except near the ends, so `bil g F ≈ K² Σ F`. -/
lemma bil_g_left (N K : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (hN : ∀ u, N < u → F u = 0) (B : ℝ)
    (hB : ∀ z, |win K F z| ≤ B) :
    |bil N K (gN N) F - (K : ℝ) ^ 2 * ∑ u ∈ range (N + 1), F u| ≤ B * K ^ 2 := by
  have hrefl : ∑ z ∈ range (N + K), win K F (N + K - 1 - z) = ∑ z ∈ range (N + K), win K F z :=
    sum_range_reflect (win K F) (N + K)
  have hsum := sum_win N K F h0 hN
  have hg := sum_win N K (gN N) (gN_zero N) (fun u hu => gN_big hu)
  rw [sum_gN] at hg
  have hdiff : bil N K (gN N) F - (K : ℝ) ^ 2 * ∑ u ∈ range (N + 1), F u =
      ∑ z ∈ range (N + K), (win K (gN N) z - K) * win K F (N + K - 1 - z) := by
    unfold bil
    simp_rw [sub_mul]
    rw [sum_sub_distrib, ← mul_sum, hrefl, hsum]; ring
  rw [hdiff]
  calc |∑ z ∈ range (N + K), (win K (gN N) z - K) * win K F (N + K - 1 - z)|
      ≤ ∑ z ∈ range (N + K), |(win K (gN N) z - K) * win K F (N + K - 1 - z)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ range (N + K), (K - win K (gN N) z) * B := by
        apply sum_le_sum; intro z _
        rw [abs_mul]
        have h1 := win_gN_mem N K z
        rw [abs_of_nonpos (by linarith)]
        have h2 := hB (N + K - 1 - z)
        have h3 : 0 ≤ (K : ℝ) - win K (gN N) z := by linarith
        calc -(win K (gN N) z - K) * |win K F (N + K - 1 - z)|
            = ((K : ℝ) - win K (gN N) z) * |win K F (N + K - 1 - z)| := by ring
          _ ≤ ((K : ℝ) - win K (gN N) z) * B := mul_le_mul_of_nonneg_left h2 h3
    _ = B * K ^ 2 := by
        rw [← sum_mul, sum_sub_distrib, hg, sum_const, card_range, nsmul_eq_mul]
        push_cast; ring

/-- AM-GM: `|Σ X(z) X(c - z)| ≤ Σ X(z)²`. -/
lemma abs_bil_self_le (N K : ℕ) (F : ℕ → ℝ) :
    |bil N K F F| ≤ ∑ z ∈ range (N + K), win K F z ^ 2 := by
  unfold bil
  have hrefl : ∑ z ∈ range (N + K), win K F (N + K - 1 - z) ^ 2 =
      ∑ z ∈ range (N + K), win K F z ^ 2 := sum_range_reflect (fun z => win K F z ^ 2) (N + K)
  calc |∑ z ∈ range (N + K), win K F z * win K F (N + K - 1 - z)|
      ≤ ∑ z ∈ range (N + K), |win K F z * win K F (N + K - 1 - z)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ range (N + K), (win K F z ^ 2 + win K F (N + K - 1 - z) ^ 2) / 2 := by
        apply sum_le_sum; intro z _
        rw [abs_mul]
        have := two_mul_le_add_sq |win K F z| |win K F (N + K - 1 - z)|
        rw [sq_abs, sq_abs] at this
        linarith
    _ = ∑ z ∈ range (N + K), win K F z ^ 2 := by
        rw [← sum_div, sum_add_distrib, hrefl]; ring

/-- The discrete `J`: windows inside `[K + 1, N]` are the terms of `J(N, K)`. -/
lemma sum_win_eN_sq (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N) :
    ∑ z ∈ range (N + K), win K (eN N) z ^ 2 ≤
      ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ (m : ℝ) - K) ^ 2 +
        2 * K * (K * (Real.log N + 1)) ^ 2 := by
  set B := (K : ℝ) * (Real.log N + 1) with hB
  have hsq : ∀ z, win K (eN N) z ^ 2 ≤ B ^ 2 := by
    intro z
    have h := abs_win_eN N K z
    have h0 : 0 ≤ |win K (eN N) z| := abs_nonneg _
    calc win K (eN N) z ^ 2 = |win K (eN N) z| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [← sum_range_add_sum_Ico _ (by omega : K + 1 ≤ N + K),
    ← sum_Ico_consecutive _ (by omega : K + 1 ≤ N + 1) (by omega : N + 1 ≤ N + K)]
  have hA : ∑ z ∈ range (K + 1), win K (eN N) z ^ 2 ≤ (K + 1) * B ^ 2 := by
    calc ∑ z ∈ range (K + 1), win K (eN N) z ^ 2 ≤ ∑ _z ∈ range (K + 1), B ^ 2 :=
          sum_le_sum fun z _ => hsq z
      _ = (K + 1) * B ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hC : ∑ z ∈ Ico (N + 1) (N + K), win K (eN N) z ^ 2 ≤ (K - 1) * B ^ 2 := by
    calc ∑ z ∈ Ico (N + 1) (N + K), win K (eN N) z ^ 2 ≤ ∑ _z ∈ Ico (N + 1) (N + K), B ^ 2 :=
          sum_le_sum fun z _ => hsq z
      _ = (K - 1) * B ^ 2 := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, show N + K - (N + 1) = K - 1 by omega,
            Nat.cast_sub hK]; push_cast; ring
  have hM : ∑ z ∈ Ico (K + 1) (N + 1), win K (eN N) z ^ 2 ≤
      ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ (m : ℝ) - K) ^ 2 := by
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    have hterm : ∀ m ∈ range (N + 1 - (K + 1)), win K (eN N) (K + 1 + m) ^ 2 =
        (θ (((1 + m : ℕ) : ℝ) + K) - θ ((1 + m : ℕ) : ℝ) - K) ^ 2 := by
      intro m hm
      have := mem_range.mp hm
      rw [win_eN_inside (by omega) (by omega)]
      rw [show K + 1 + m - K = 1 + m by omega, show ((K + 1 + m : ℕ) : ℝ) = ((1 + m : ℕ) : ℝ) + K by
        push_cast; ring]
    rw [sum_congr rfl hterm]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm; rw [mem_range] at hm ⊢; omega
    · intro _ _ _; exact sq_nonneg _
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  calc ∑ z ∈ range (K + 1), win K (eN N) z ^ 2 +
        (∑ z ∈ Ico (K + 1) (N + 1), win K (eN N) z ^ 2 +
          ∑ z ∈ Ico (N + 1) (N + K), win K (eN N) z ^ 2)
      ≤ (K + 1) * B ^ 2 + (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ (m : ℝ) - K) ^ 2 +
          (K - 1) * B ^ 2) := by linarith
    _ = _ := by ring

/-! ### Truncated and full representation counts -/

lemma conv_le_Rg (N K m : ℕ) (hm : m ≤ N + K) :
    0 ≤ RgC m - conv (fN N) m ∧ RgC m - conv (fN N) m ≤ 2 * K * Real.log (N + K) ^ 2 := by
  set L := Real.log ((N + K : ℕ) : ℝ) with hL
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg _
  have hconv : conv (fN N) m = ∑ u ∈ range m, fN N u * fN N (m - u) := by
    unfold conv; rw [sum_range_succ, Nat.sub_self, fN_zero, mul_zero, add_zero]
  have hR : RgC m = ∑ u ∈ range m, lp u * lp (m - u) := by
    unfold RgC; apply sum_congr rfl; intro u _
    unfold lp; split_ifs <;> simp_all
  set φ : ℕ → ℝ := fun u => lp u * lp (m - u) - fN N u * fN N (m - u) with hφ
  have hdiff : RgC m - conv (fN N) m = ∑ u ∈ range m, φ u := by
    rw [hR, hconv, ← sum_sub_distrib]
  have hφ0 : ∀ u, φ u = if u ≤ N ∧ m - u ≤ N then 0 else lp u * lp (m - u) := by
    intro u; simp only [hφ, fN]; split_ifs <;> simp_all
  have hlpL : ∀ u, u ≤ m → lp u ≤ L := fun u hu => lp_le (by omega)
  rw [hdiff]
  constructor
  · apply sum_nonneg; intro u _; rw [hφ0]; split_ifs
    · exact le_refl 0
    · exact mul_nonneg (lp_nonneg _) (lp_nonneg _)
  · have hb : ∀ u ∈ range m, φ u ≤ L ^ 2 * (if N < u ∨ u + N < m then 1 else 0) := by
      intro u hu
      have hu' := mem_range.mp hu
      rw [hφ0]
      split_ifs with h1 h2
      · positivity
      · simp
      · rw [mul_one, sq]
        exact mul_le_mul (hlpL u hu'.le) (hlpL _ (by omega)) (lp_nonneg _) hL0
      · omega
    calc ∑ u ∈ range m, φ u ≤ ∑ u ∈ range m, L ^ 2 * (if N < u ∨ u + N < m then 1 else 0) :=
          sum_le_sum hb
      _ = L ^ 2 * ((range m).filter (fun u => N < u ∨ u + N < m)).card := by
          rw [← mul_sum, sum_boole]
      _ ≤ L ^ 2 * (2 * K) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have hsub : (range m).filter (fun u => N < u ∨ u + N < m) ⊆
              Ico (N + 1) (N + K) ∪ range K := by
            intro u hu; simp only [mem_filter, mem_range, mem_union, mem_Ico] at hu ⊢; omega
          have hc := (card_le_card hsub).trans (card_union_le _ _)
          rw [Nat.card_Ico, card_range] at hc
          have : (((range m).filter (fun u => N < u ∨ u + N < m)).card : ℝ) ≤ 2 * K := by
            have h2 : ((range m).filter (fun u => N < u ∨ u + N < m)).card ≤ 2 * K := by omega
            exact_mod_cast h2
          exact this
      _ = 2 * K * Real.log (N + K) ^ 2 := by rw [hL]; push_cast; ring

/-! ### The explicit theorem -/

/-- **Goldston's display 6, explicit and unconditional.** For naturals `1 ≤ K ≤ N`,
`|Σ_{|n| ≤ K} (K - |n|) R(N + n) - K² N| ≤ Σ_{1 ≤ m < N} (θ(m + K) - θ(m) - K)² + 2 K² |θ(N) - N|`
`+ K³ (2 log²(N + K) + 1 + 2 (log N + 1) + 2 (log N + 1)²)`. -/
theorem fejerC_explicit (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N) :
    |fejerC N K - (K : ℝ) ^ 2 * N| ≤
      ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ (m : ℝ) - K) ^ 2 + 2 * (K : ℝ) ^ 2 * |θ (N : ℝ) - N| +
        (K : ℝ) ^ 3 * (2 * Real.log (N + K) ^ 2 + 1 + 2 * (Real.log N + 1) +
          2 * (Real.log N + 1) ^ 2) := by
  set J := ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ (m : ℝ) - K) ^ 2 with hJ
  -- Fejér sum against the truncated convolution
  have hbilf : bil N K (fN N) (fN N) =
      ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * conv (fN N) (N + j - K) := by
    rw [bil_self N K (fN N) (fN_zero N) hKN, fejer_reindex N K hKN]
  have h1 : |fejerC N K - bil N K (fN N) (fN N)| ≤ (K : ℝ) ^ 2 * (2 * K * Real.log (N + K) ^ 2) := by
    rw [hbilf, fejerC, ← sum_sub_distrib]
    calc |∑ j ∈ range (2 * K + 1), (((K : ℝ) - |(j : ℝ) - K|) * RgC (N + j - K) -
            ((K : ℝ) - |(j : ℝ) - K|) * conv (fN N) (N + j - K))|
        ≤ ∑ j ∈ range (2 * K + 1), |((K : ℝ) - |(j : ℝ) - K|) * RgC (N + j - K) -
            ((K : ℝ) - |(j : ℝ) - K|) * conv (fN N) (N + j - K)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (2 * K + 1), ((K : ℝ) - |(j : ℝ) - K|) * (2 * K * Real.log (N + K) ^ 2) := by
          apply sum_le_sum; intro j hj
          have hj' : j ≤ 2 * K := by have := mem_range.mp hj; omega
          have hw := weight_nonneg K j hj'
          have hc := conv_le_Rg N K (N + j - K) (by omega)
          rw [← mul_sub, abs_mul, abs_of_nonneg hw, abs_of_nonneg hc.1]
          exact mul_le_mul_of_nonneg_left hc.2 hw
      _ = (K : ℝ) ^ 2 * (2 * K * Real.log (N + K) ^ 2) := by rw [← sum_mul, weight_sum]
  -- split f = g + e
  have hsplit : bil N K (fN N) (fN N) = bil N K (gN N) (gN N) + bil N K (gN N) (eN N) +
      bil N K (eN N) (gN N) + bil N K (eN N) (eN N) := by
    rw [fN_eq]
    unfold bil
    simp_rw [win_add]
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro z _; ring
  rw [bil_comm N K (eN N) (gN N)] at hsplit
  have hgg := bil_g_left N K (gN N) (gN_zero N) (fun u hu => gN_big hu) K (abs_win_gN N K)
  rw [sum_gN] at hgg
  have hge := bil_g_left N K (eN N) (eN_zero N) (fun u hu => eN_big hu) _ (abs_win_eN N K)
  rw [sum_eN] at hge
  have hee := (abs_bil_self_le N K (eN N)).trans (sum_win_eN_sq N K hK hKN)
  have hθ : |2 * (K : ℝ) ^ 2 * (θ (N : ℝ) - N)| = 2 * (K : ℝ) ^ 2 * |θ (N : ℝ) - N| := by
    rw [abs_mul]; congr 1; rw [abs_of_nonneg (by positivity)]
  have key : fejerC N K - (K : ℝ) ^ 2 * N =
      (fejerC N K - bil N K (fN N) (fN N)) + (bil N K (gN N) (gN N) - (K : ℝ) ^ 2 * N) +
        2 * (bil N K (gN N) (eN N) - (K : ℝ) ^ 2 * (θ (N : ℝ) - N)) +
          2 * (K : ℝ) ^ 2 * (θ (N : ℝ) - N) + bil N K (eN N) (eN N) := by
    rw [hsplit]; ring
  rw [key]
  have t1 := abs_add_three (fejerC N K - bil N K (fN N) (fN N))
    (bil N K (gN N) (gN N) - (K : ℝ) ^ 2 * N)
    (2 * (bil N K (gN N) (eN N) - (K : ℝ) ^ 2 * (θ (N : ℝ) - N)))
  have t2 := abs_add_three (fejerC N K - bil N K (fN N) (fN N) + (bil N K (gN N) (gN N) -
      (K : ℝ) ^ 2 * N) + 2 * (bil N K (gN N) (eN N) - (K : ℝ) ^ 2 * (θ (N : ℝ) - N)))
    (2 * (K : ℝ) ^ 2 * (θ (N : ℝ) - N)) (bil N K (eN N) (eN N))
  have t3 : |2 * (bil N K (gN N) (eN N) - (K : ℝ) ^ 2 * (θ (N : ℝ) - N))| =
      2 * |bil N K (gN N) (eN N) - (K : ℝ) ^ 2 * (θ (N : ℝ) - N)| := by
    rw [abs_mul, abs_two]
  rw [hθ] at t2
  rw [t3] at t1
  nlinarith [t1, t2, h1, hgg, hge, hee]

end LeanLab.GoldbachGaps.Goldston1990.Thm6
