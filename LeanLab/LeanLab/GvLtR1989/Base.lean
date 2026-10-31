/-
P0042 Granville, van de Lune, te Riele 1989, Checking the Goldbach conjecture on a vector
computer. Kernel checks of their two numerical claims on the lab's own verified range.
This file: the shared machinery.
- `MinGBBound A B q`: every even n in [A, B] has minGB n ≤ q.
- `bound_of_check`, `bound_of_wcheck`, `bound_of_wcheck2`: one bignum equality of the
  Top50 bit sieve gives such a bound, with q any bound on the primes tried.
- `ratio_of_bound`: a bound q plus certified lower bounds r ≤ log A and s ≤ log r give
  minGB n < c · log² n · log log n on the whole block.
- `le_log_of`: certified lower bounds for log by a Taylor upper bound for exp.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Statements
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits
open Finset

/-- Every even `n` with `A ≤ n ≤ B` has least Goldbach prime at most `q`. -/
def MinGBBound (A B q : ℕ) : Prop :=
  ∀ n : ℕ, Even n → A ≤ n → n ≤ B → minGB n ≤ q

theorem minGB_le_of {n q : ℕ} (hq : q.Prime) (hnq : (n - q).Prime) : minGB n ≤ q := by
  classical
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨q, hq, hnq⟩
  unfold minGB
  rw [dif_pos hex]
  exact Nat.find_min' hex ⟨hq, hnq⟩

theorem take_le (K q : ℕ) (h : (P10k.take K).all (fun x => decide (x ≤ q)) = true) :
    ∀ x ∈ P10k.take K, x ≤ q := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simpa using this

/-- One full-bitmap check from `BitSieve.lean` bounds minGB on `[A, B]`. -/
theorem bound_of_check {L A B K q : ℕ} (hL : L ≤ 10 ^ 8) (hAe : Even A)
    (hq : ∀ x ∈ P10k.take K, x ≤ q)
    (h : em A B &&& gm (pm L) (P10k.take K) = em A B) : MinGBBound A B q := by
  intro n hn hA hB
  have he : 2 ∣ n - A := Nat.dvd_sub (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hAe)
  have h1 := testBit_em hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨x, hx, hxn, hp⟩ := of_gm _ _ n h1.2
  exact le_trans (minGB_le_of (take_prime K x hx) (prime_of_pm hL hp)) (hq x hx)

/-- One window check of `BitSieve.lean`, below 10^8, bounds minGB on `[A, B]`. -/
theorem bound_of_wcheck {lo W A B K q : ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8) (hlo : lo ≤ A)
    (hAe : Even A) (hq : ∀ x ∈ P10k.take K, x ≤ q)
    (h : wem lo A B &&& gm (wpm lo W) (P10k.take K) = wem lo A B) : MinGBBound A B q := by
  intro n hn hA hB
  have he : 2 ∣ n - A := Nat.dvd_sub (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hAe)
  have h1 := testBit_wem hlo hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨x, hx, hxn, hp⟩ := of_gm _ _ _ h1.2
  have hpr := prime_of_wpm h2 hW hp
  rw [show lo + (n - lo - x) = n - x by omega] at hpr
  exact le_trans (minGB_le_of (take_prime K x hx) hpr) (hq x hx)

/-- One window check of `BitSieve2.lean`, below 31700², bounds minGB on `[A, B]`. -/
theorem bound_of_wcheck2 {lo W A B K q : ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ B2) (hlo : lo ≤ A)
    (hAe : Even A) (hq : ∀ x ∈ P10k.take K, x ≤ q)
    (h : wem lo A B &&& gm (wpm2 lo W) (P10k.take K) = wem lo A B) : MinGBBound A B q := by
  intro n hn hA hB
  have he : 2 ∣ n - A := Nat.dvd_sub (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hAe)
  have h1 := testBit_wem hlo hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨x, hx, hxn, hp⟩ := of_gm _ _ _ h1.2
  have hpr := prime_of_wpm2 h2 hW hp
  rw [show lo + (n - lo - x) = n - x by omega] at hpr
  exact le_trans (minGB_le_of (take_prime K x hx) hpr) (hq x hx)

/-! ### Certified lower bounds for log -/

/-- Taylor polynomial of exp with 12 terms plus the Mathlib remainder bound. -/
noncomputable def expUp (f : ℝ) : ℝ :=
  (∑ i ∈ range 12, f ^ i / (Nat.factorial i : ℝ)) + f ^ 12 * ((13 : ℝ) / ((Nat.factorial 12 : ℝ) * 12))

theorem exp_le_expUp {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) : Real.exp f ≤ expUp f := by
  have hb := Real.exp_bound (x := f) (by rw [abs_of_nonneg h0]; exact h1) (n := 12) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have := (abs_le.mp hb).2
  unfold expUp
  push_cast at this ⊢
  linarith

/-- `a + f ≤ log x` from `e^a · expUp f ≤ x`, with `e < 2.7182818286`. -/
theorem le_log_of {x : ℝ} (a : ℕ) {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : (2.7182818286 : ℝ) ^ a * expUp f ≤ x) : (a : ℝ) + f ≤ Real.log x := by
  have hpos : 0 < Real.exp ((a : ℝ) + f) := Real.exp_pos _
  have hea : Real.exp (a : ℝ) ≤ (2.7182818286 : ℝ) ^ a := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le a
  have hle : Real.exp ((a : ℝ) + f) ≤ x := by
    rw [Real.exp_add]
    calc Real.exp a * Real.exp f ≤ (2.7182818286 : ℝ) ^ a * expUp f :=
          mul_le_mul hea (exp_le_expUp h0 h1) (Real.exp_pos _).le (by positivity)
      _ ≤ x := h
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le hpos hle)]
  exact hle

/-- The ratio bound on one block. -/
theorem ratio_of_bound {A B q : ℕ} {c r s : ℝ} (hc : 0 ≤ c) (hr0 : 1 < r) (hr : r ≤ Real.log A)
    (hs : s ≤ Real.log r) (hs0 : 0 < s) (hq : (q : ℝ) < c * r ^ 2 * s)
    (hb : MinGBBound A B q) :
    ∀ n : ℕ, Even n → A ≤ n → n ≤ B →
      (minGB n : ℝ) < c * Real.log n ^ 2 * Real.log (Real.log n) := by
  intro n hn hA hB
  have hA0 : (0 : ℝ) < A := by
    by_contra h
    push_neg at h
    have : Real.log (A : ℝ) ≤ 0 := by
      rw [show (A : ℝ) = 0 by exact le_antisymm h (Nat.cast_nonneg A)]; simp
    linarith
  have hlogn : r ≤ Real.log n :=
    le_trans hr (Real.log_le_log hA0 (by exact_mod_cast hA))
  have hll : s ≤ Real.log (Real.log n) :=
    le_trans hs (Real.log_le_log (by linarith) hlogn)
  have hq' : ((minGB n : ℕ) : ℝ) ≤ q := by exact_mod_cast hb n hn hA hB
  have : c * r ^ 2 * s ≤ c * Real.log n ^ 2 * Real.log (Real.log n) := by
    apply mul_le_mul _ hll hs0.le (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlogn 2) hc
  linarith

/-- Join two adjacent blocks. -/
theorem join {P : ℕ → Prop} {A B A' C : ℕ}
    (h1 : ∀ n, Even n → A ≤ n → n ≤ B → P n) (h2 : ∀ n, Even n → A' ≤ n → n ≤ C → P n)
    (hBA : B + 2 = A') (hB : Even B) : ∀ n, Even n → A ≤ n → n ≤ C → P n := by
  intro n hn hA hC
  by_cases h : n ≤ B
  · exact h1 n hn hA h
  · apply h2 n hn _ hC
    obtain ⟨k, hk⟩ := hn
    obtain ⟨j, hj⟩ := hB
    omega

theorem mono {A B q q' : ℕ} (h : MinGBBound A B q) (hq : q ≤ q') : MinGBBound A B q' :=
  fun n hn hA hB => le_trans (h n hn hA hB) hq

/-- The paper's ratio with constant `c`. -/
abbrev Ratio (c : ℝ) (n : ℕ) : Prop :=
  (minGB n : ℝ) < c * Real.log n ^ 2 * Real.log (Real.log n)

end LeanLab.GvLtR1989
