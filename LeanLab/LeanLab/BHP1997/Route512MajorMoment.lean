/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
The trivial bound for S2 on the major arcs: the divisor moment over the interval
J = (Y, 2Y], needed where the model vanishes, that is for moduli that are not
squarefree. The proof follows the short interval moment of page 9 and uses the three
public tools of Route512Moment.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512Moment

namespace LeanLab.BHP1997.Route512Major
open Classical

/-- P0069 page 7, the trivial bound behind display 2.5: on any integer interval `(a, b]`
of length at most `2Y + 1` with `b ≤ Y²`, the divisor moment of order `B` is at most
`2^(max B 0) 4 Y (1 + log b)^(2^M)`, with `M` depending only on `B`. -/
theorem divisor_moment_interval512j (B : ℝ) :
    ∃ M : ℕ, ∀ (a b : ℕ) (Y : ℝ), a ≤ b → 1 ≤ b → (b : ℝ) - a ≤ 2 * Y + 1 →
      (b : ℝ) ≤ Y * Y → 1 ≤ Y →
      ∑ k ∈ Finset.Ioc a b, ((k.divisors.card : ℕ) : ℝ) ^ B ≤
        (2 : ℝ) ^ (max B 0) * (4 * Y * (1 + Real.log b) ^ (2 ^ M)) := by
  obtain ⟨M, hMB⟩ : ∃ M : ℕ, 4 * max B 0 ≤ (M : ℝ) := ⟨⌈4 * max B 0⌉₊, Nat.le_ceil _⟩
  refine ⟨M, ?_⟩
  intro a b Y hab hb1 hlen hbY hY1
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have h2Bpos : (0 : ℝ) ≤ (2 : ℝ) ^ (max B 0) := by positivity
  have hY0 : 0 ≤ Y := by linarith
  have hz1 : 1 ≤ Nat.sqrt b := Nat.le_sqrt.mpr (by simpa using hb1)
  have hpt : ∀ k ∈ Finset.Ioc a b, ((k.divisors.card : ℕ) : ℝ) ^ B ≤
      (2 : ℝ) ^ (max B 0) * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
        ((d.divisors.card : ℕ) : ℝ) ^ M := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : k ≠ 0 := by omega
    obtain ⟨d, hdk, hdd, hτ⟩ := Route512.exists_small_divisor512m k hk0
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hk0 (zero_dvd_iff.mp hdk)
    have hdz : d ≤ Nat.sqrt b := Nat.le_sqrt.mpr (le_trans hdd hk.2)
    have hdmem : d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hdz⟩, hdk⟩
    have hτk1 : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
    have hτd1 : (1 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hd0⟩
    have hτd0 : (0 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hτR : ((k.divisors.card : ℕ) : ℝ) ≤ 2 * ((d.divisors.card : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast hτ
    calc ((k.divisors.card : ℕ) : ℝ) ^ B
        ≤ ((k.divisors.card : ℕ) : ℝ) ^ (max B 0) :=
          Real.rpow_le_rpow_of_exponent_le hτk1 (le_max_left _ _)
      _ ≤ (2 * ((d.divisors.card : ℕ) : ℝ) ^ 4) ^ (max B 0) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hτR hB0
      _ = (2 : ℝ) ^ (max B 0) * ((d.divisors.card : ℕ) : ℝ) ^ (4 * max B 0) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hτd0 4),
            ← Real.rpow_natCast, ← Real.rpow_mul hτd0]
          norm_num
      _ ≤ (2 : ℝ) ^ (max B 0) * ((d.divisors.card : ℕ) : ℝ) ^ (M : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hτd1 hMB) h2Bpos
      _ = (2 : ℝ) ^ (max B 0) * ((d.divisors.card : ℕ) : ℝ) ^ M := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ h2Bpos
          exact Finset.single_le_sum (f := fun d : ℕ => ((d.divisors.card : ℕ) : ℝ) ^ M)
            (fun i _ => by positivity) hdmem
  have hswap : ∑ k ∈ Finset.Ioc a b, ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
        ((d.divisors.card : ℕ) : ℝ) ^ M
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ M := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ d ∈ Finset.Icc 1 (Nat.sqrt b),
      (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ) ≤ 4 * Y / d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
    have hdY : (d : ℝ) ≤ Y := by
      have h1 : d * d ≤ b := Nat.le_sqrt.mp hd.2
      have h2 : (d : ℝ) * d ≤ Y * Y := le_trans (by exact_mod_cast h1) hbY
      by_contra hcon
      have := mul_self_lt_mul_self hY0 (not_le.mp hcon)
      linarith
    have h := Route512.count_dvd512m a b d hd.1 hab
    have hba : ((b : ℝ) - a) / d ≤ (2 * Y + 1) / d :=
      div_le_div_of_nonneg_right hlen hdpos.le
    calc (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ) ≤ ((b : ℝ) - a) / d + 1 := h
      _ ≤ (2 * Y + 1) / d + d / d := by
          rw [div_self hdpos.ne']
          linarith
      _ = (2 * Y + 1 + d) / d := by ring
      _ ≤ 4 * Y / d := div_le_div_of_nonneg_right (by linarith) hdpos.le
  have hS := Route512.harmonic_divisor_pow_sum512m M (Nat.sqrt b)
  have hlog : Real.log (Nat.sqrt b : ℝ) ≤ Real.log b :=
    Real.log_le_log (by exact_mod_cast hz1) (by exact_mod_cast Nat.sqrt_le_self b)
  have hlog0 : 0 ≤ Real.log (Nat.sqrt b : ℝ) := Real.log_nonneg (by exact_mod_cast hz1)
  have hpow : (1 + Real.log (Nat.sqrt b : ℝ)) ^ (2 ^ M) ≤ (1 + Real.log b) ^ (2 ^ M) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h4Y : 0 ≤ 4 * Y := by linarith
  calc ∑ k ∈ Finset.Ioc a b, ((k.divisors.card : ℕ) : ℝ) ^ B
      ≤ ∑ k ∈ Finset.Ioc a b, (2 : ℝ) ^ (max B 0)
          * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
            ((d.divisors.card : ℕ) : ℝ) ^ M := Finset.sum_le_sum hpt
    _ = (2 : ℝ) ^ (max B 0) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ M := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ (2 : ℝ) ^ (max B 0) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (4 * Y / d) * ((d.divisors.card : ℕ) : ℝ) ^ M := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d hd => ?_)) h2Bpos
        exact mul_le_mul_of_nonneg_right (hcount d hd) (by positivity)
    _ = (2 : ℝ) ^ (max B 0) * (4 * Y * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          ((d.divisors.card : ℕ) : ℝ) ^ M / d) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hS.trans hpow) h4Y) h2Bpos

/-- P0069 page 7, the trivial bound for S2 used with display 2.5:
`∑_{m ∈ (Y, 2Y]} τ(m)^B ≤ C Y (log x)^c` with `Y = x^(11/20 + ε)`, for `x ≥ C`. -/
theorem long_divisor_moment512j (B ε : ℝ) (hε : 0 < ε) :
    ∃ c C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        ((m.divisors.card : ℕ) : ℝ) ^ B ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ c := by
  obtain ⟨M, hM⟩ := divisor_moment_interval512j B
  refine ⟨((2 ^ M : ℕ) : ℝ), (2 : ℝ) ^ (max B 0) * 4 * (3 + ε) ^ (2 ^ M) + 4, ?_⟩
  intro x hx
  have hK : (0 : ℝ) ≤ (2 : ℝ) ^ (max B 0) * 4 * (3 + ε) ^ (2 ^ M) := by positivity
  have hx4 : (4 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have := Real.exp_one_lt_d9
    linarith
  have hY2 : (2 : ℝ) ≤ x ^ (11 / 20 + ε) := by
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x :=
    Real.log_rpow hxpos _
  generalize x ^ (11 / 20 + ε) = Y at hY2 hlogY ⊢
  have hY0 : 0 ≤ Y := by linarith
  have hab : ⌊Y⌋₊ ≤ ⌊2 * Y⌋₊ := Nat.floor_le_floor (by linarith)
  have hb : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have ha : Y < ((⌊Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb1 : 1 ≤ ⌊2 * Y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h := hM ⌊Y⌋₊ ⌊2 * Y⌋₊ Y hab hb1 (by linarith) (by nlinarith) (by linarith)
  have hb1R : (1 : ℝ) ≤ ((⌊2 * Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hb1
  have hlogb : Real.log ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ Real.log 2 + (11 / 20 + ε) * Real.log x := by
    calc _ ≤ Real.log (2 * Y) := Real.log_le_log (by linarith) hb
      _ = _ := by rw [Real.log_mul (by norm_num) (by linarith), hlogY]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlogb0 : 0 ≤ Real.log ((⌊2 * Y⌋₊ : ℕ) : ℝ) := Real.log_nonneg hb1R
  have hbase : 1 + Real.log ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ (3 + ε) * Real.log x := by nlinarith
  have hpow : (1 + Real.log ((⌊2 * Y⌋₊ : ℕ) : ℝ)) ^ (2 ^ M) ≤ ((3 + ε) * Real.log x) ^ (2 ^ M) :=
    pow_le_pow_left₀ (by linarith) hbase _
  have hLpow : 0 ≤ Real.log x ^ (2 ^ M) := pow_nonneg (by linarith) _
  have h2Bpos : (0 : ℝ) ≤ (2 : ℝ) ^ (max B 0) := by positivity
  calc _ ≤ (2 : ℝ) ^ (max B 0) * (4 * Y * (1 + Real.log ((⌊2 * Y⌋₊ : ℕ) : ℝ)) ^ (2 ^ M)) := h
    _ ≤ (2 : ℝ) ^ (max B 0) * (4 * Y * ((3 + ε) * Real.log x) ^ (2 ^ M)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by linarith)) h2Bpos
    _ = (2 : ℝ) ^ (max B 0) * 4 * (3 + ε) ^ (2 ^ M) * Y * Real.log x ^ (2 ^ M) := by
        rw [mul_pow]; ring
    _ ≤ ((2 : ℝ) ^ (max B 0) * 4 * (3 + ε) ^ (2 ^ M) + 4) * Y *
          Real.log x ^ (((2 ^ M : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        have hP : 0 ≤ Y * Real.log x ^ (2 ^ M) := mul_nonneg hY0 hLpow
        nlinarith

end LeanLab.BHP1997.Route512Major
