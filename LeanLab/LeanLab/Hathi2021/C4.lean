/-
P0080 Hathi 2021, arXiv 2109.13174v3, Section 2, pages 5-6, the constant `c_{4,P}` with
`P = {3, 5}`, used in Lemma 2.3 to bound the singular series `S(h)`.
Unit U-6150, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

**`c₄ ≤ 0.9743`, the paper's printed bound, and the sharper `c₄ ≤ 0.97428`.**
`c₄ = ∏_{p > 5} (1 + a(p)/(p - 1)⁴)` with `a(p) = -(p + 1)²` for `p ≡ 3 mod 4` and
`a(p) = 3p² - 2p - 1 = (3p + 1)(p - 1)` for `p ≡ 1 mod 4`, page 5.
Proof: the head product over the primes `5 < p < 20001` is at most `0.974238391930890313`, by a
rounded-up chain computed by the kernel; the tail is at most `exp(3003/(4000 · 20000))`, since
a factor at `p ≡ 3 mod 4` is below 1 and at `p ≡ 1 mod 4` the log of the factor is at most
`(3p + 1)/(p - 1)³ ≤ (3003/4000)(1/(p - 1) - 1/(p + 3))`, which telescopes along `p ≡ 1 mod 4`.
True value `0.9742428`, Python, numerics in PROGRESS.md. Generator gen/c4_chain_U6150.py.
`primeB` and its proof are copied from ChenExplicit/TwinCUpper.lean, PC run 20261019T1902Z-2936.
KNOWN mathematics; this checks a printed constant.
-/
import Mathlib

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace LeanLab.Hathi2021.C4
open Real Finset

/-- `a(p)` of page 5, as a function on all `n`; only `n` prime and odd is used. -/
noncomputable def aH (n : ℕ) : ℝ :=
  if n % 4 = 3 then -((n : ℝ) + 1) ^ 2 else (3 * (n : ℝ) + 1) * ((n : ℝ) - 1)

/-- The Euler factor `1 + a(p)/(p - 1)⁴`. -/
noncomputable def gH (n : ℕ) : ℝ := 1 + aH n / ((n : ℝ) - 1) ^ 4

/-- `c_{4,P}` for `P = {3, 5}`: `∏_{p ∉ P, p > 2} (1 + a(p)/(p - 1)⁴)`, page 5. -/
noncomputable def c4 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 5 < p}, gH p

/-- Its log on primes above 5, `0` elsewhere. -/
noncomputable def lH (n : ℕ) : ℝ := if n.Prime ∧ 5 < n then Real.log (gH n) else 0

lemma aH_abs_le {n : ℕ} (hn : 5 < n) : |aH n| ≤ 4 * ((n : ℝ) - 1) ^ 2 := by
  have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  unfold aH
  split_ifs
  · rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith
  · rw [abs_of_nonneg (by apply mul_nonneg <;> linarith)]; nlinarith

/-- `|a(n)/(n - 1)⁴| ≤ 4/(n - 1)² ≤ 4/25`. -/
lemma x_abs_le {n : ℕ} (hn : 5 < n) :
    |aH n / ((n : ℝ) - 1) ^ 4| ≤ 4 * (1 / ((n : ℝ) - 1) ^ 2) := by
  have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 := by nlinarith
  have hd4 : (0 : ℝ) < ((n : ℝ) - 1) ^ 4 := pow_pos (by linarith) 4
  rw [abs_div, abs_of_pos hd4, div_le_iff₀ hd4]
  have := aH_abs_le hn
  calc |aH n| ≤ 4 * ((n : ℝ) - 1) ^ 2 := this
    _ = 4 * (1 / ((n : ℝ) - 1) ^ 2) * ((n : ℝ) - 1) ^ 4 := by field_simp

lemma x_ge {n : ℕ} (hn : 5 < n) : -(4 / 25 : ℝ) ≤ aH n / ((n : ℝ) - 1) ^ 4 := by
  have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := neg_abs_le (aH n / ((n : ℝ) - 1) ^ 4)
  have h2 := x_abs_le hn
  have h3 : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
  linarith

lemma gH_pos {n : ℕ} (hn : 5 < n) : 0 < gH n := by
  have := x_ge hn; unfold gH; linarith

lemma summable_inv_sq' : Summable (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine (summable_nat_add_iff 1).mp (h.congr fun n => ?_)
  push_cast; ring_nf

lemma summable_lH : Summable lH := by
  refine Summable.of_norm_bounded (summable_inv_sq'.mul_left 8) fun n => ?_
  unfold lH
  split_ifs with hp
  · have hn := hp.2
    set x := aH n / ((n : ℝ) - 1) ^ 4 with hx
    have hxa := x_abs_le hn
    have hxg := x_ge hn
    have hpos : 0 < 1 + x := by linarith
    have hg : gH n = 1 + x := rfl
    rw [hg, Real.norm_eq_abs]
    have hup : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    have hlo : 1 - (1 + x)⁻¹ ≤ Real.log (1 + x) := Real.one_sub_inv_le_log_of_pos hpos
    rw [abs_le]
    have := le_abs_self x
    have := neg_abs_le x
    rcases le_total 0 x with h0 | h0
    · have : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
      constructor <;> nlinarith
    · have hinv : (1 + x)⁻¹ ≤ 1 - 2 * x := by
        rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
      constructor <;> nlinarith
  · simp only [norm_zero]
    have : 0 ≤ 1 / ((n : ℝ) - 1) ^ 2 := by positivity
    linarith

/-- `c₄` as `exp` of the `ℕ`-indexed log sum. -/
lemma c4_eq_exp : c4 = Real.exp (∑' n, lH n) := by
  set f : {p : ℕ // p.Prime ∧ 5 < p} → ℝ := fun p => gH p with hf
  have hpos : ∀ p, 0 < f p := fun p => gH_pos p.2.2
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := summable_lH.subtype {p : ℕ | p.Prime ∧ 5 < p}
    refine this.congr fun p => ?_
    show lH p.1 = _
    unfold lH; rw [if_pos (show Nat.Prime p.1 ∧ 5 < p.1 from p.2)]
  have hT : c4 = exp (∑' p, Real.log (f p)) := by
    rw [Real.rexp_tsum_eq_tprod hpos hlog]; rfl
  rw [hT]
  congr 1
  rw [show (∑' p, Real.log (f p)) = ∑' p : {p : ℕ | p.Prime ∧ 5 < p}, lH p from by
    apply tsum_congr; intro p; show _ = lH p.1; unfold lH
    rw [if_pos (show Nat.Prime p.1 ∧ 5 < p.1 from p.2)]]
  rw [_root_.tsum_subtype]
  apply tsum_congr
  intro n
  simp only [Set.indicator_apply, Set.mem_setOf_eq, lH]
  split_ifs <;> rfl

/-! ### The tail -/

/-- The least `m ≥ n` with `m ≡ 1 mod 4`. -/
def mH (n : ℕ) : ℕ := n + (5 - n % 4) % 4

/-- The telescoping majorant `T(n) = (3003/4000)/(m(n) - 1)`. -/
noncomputable def TH (n : ℕ) : ℝ := (3003 / 4000) / ((mH n : ℝ) - 1)

lemma TH_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ TH n := by
  unfold TH
  have : (2 : ℝ) ≤ (mH n : ℝ) := by unfold mH; exact_mod_cast (by omega)
  apply div_nonneg (by norm_num); linarith

/-- An odd prime above 5 that is not `1 mod 4` is `3 mod 4`. -/
lemma mod4_of_prime {n : ℕ} (hp : n.Prime) (hn : 5 < n) (h1 : n % 4 ≠ 1) : n % 4 = 3 := by
  rcases hp.eq_two_or_odd with h | h
  · omega
  · omega

/-- **The tail step.** For `n ≥ 20001`, `lH n ≤ T(n) - T(n + 1)`. -/
lemma lH_le_step {n : ℕ} (hn : 20001 ≤ n) : lH n ≤ TH n - TH (n + 1) := by
  have hR : (20001 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases h1 : n % 4 = 1
  · have hm0 : mH n = n := by unfold mH; omega
    have hm1 : mH (n + 1) = n + 4 := by unfold mH; omega
    have hstep : TH n - TH (n + 1) = (3003 / 4000) / ((n : ℝ) - 1) - (3003 / 4000) / ((n : ℝ) + 3) := by
      unfold TH; rw [hm0, hm1]; push_cast; ring_nf
    rw [hstep]
    have hge : 0 ≤ (3003 / 4000) / ((n : ℝ) - 1) - (3003 / 4000) / ((n : ℝ) + 3) := by
      rw [sub_nonneg]; apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    unfold lH
    split_ifs with hp
    · have hn5 : 5 < n := by omega
      have hpos := gH_pos hn5
      have hup : Real.log (gH n) ≤ gH n - 1 := Real.log_le_sub_one_of_pos hpos
      have ha : aH n = (3 * (n : ℝ) + 1) * ((n : ℝ) - 1) := by
        unfold aH; rw [if_neg (by omega)]
      have hx : gH n - 1 = (3 * (n : ℝ) + 1) / ((n : ℝ) - 1) ^ 3 := by
        unfold gH; rw [ha]
        have : (n : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      have hd1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hkey : (3 * (n : ℝ) + 1) / ((n : ℝ) - 1) ^ 3 ≤
          (3003 / 4000) / ((n : ℝ) - 1) - (3003 / 4000) / ((n : ℝ) + 3) := by
        have : (3003 / 4000) / ((n : ℝ) - 1) - (3003 / 4000) / ((n : ℝ) + 3) =
            (3003 / 1000) / (((n : ℝ) - 1) * ((n : ℝ) + 3)) := by
          field_simp; ring
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hd1 hd1]
      linarith
    · exact hge
  · have hm : mH (n + 1) = mH n := by unfold mH; omega
    rw [show TH (n + 1) = TH n by unfold TH; rw [hm], sub_self]
    unfold lH
    split_ifs with hp
    · have h3 := mod4_of_prime hp.1 hp.2 h1
      have hpos := gH_pos hp.2
      apply Real.log_nonpos hpos.le
      unfold gH aH
      rw [if_pos h3]
      have : 0 ≤ ((n : ℝ) + 1) ^ 2 / ((n : ℝ) - 1) ^ 4 := by positivity
      rw [neg_div]; linarith
    · exact le_refl 0

/-- **The tail.** `∑_{n ≥ 20001} lH n ≤ (3003/4000)/20000`. -/
lemma tail_le : ∑' k, lH (k + 20001) ≤ (3003 / 4000) / 20000 := by
  have hs : Summable (fun k => lH (k + 20001)) := (summable_nat_add_iff 20001).mpr summable_lH
  refine hs.tsum_le_of_sum_range_le fun K => ?_
  calc ∑ k ∈ range K, lH (k + 20001) ≤ ∑ k ∈ range K, (TH (k + 20001) - TH (k + 1 + 20001)) := by
        apply sum_le_sum; intro k _
        have := lH_le_step (n := k + 20001) (by omega)
        rwa [show k + 20001 + 1 = k + 1 + 20001 by ring] at this
    _ = TH (0 + 20001) - TH (K + 20001) := sum_range_sub' (fun k => TH (k + 20001)) K
    _ ≤ TH 20001 := by have := TH_nonneg (n := K + 20001) (by omega); simp; linarith
    _ = (3003 / 4000) / 20000 := by
        unfold TH; rw [show mH 20001 = 20001 by unfold mH; norm_num]; norm_num

/-! ### The head, a rounded-up chain computed by the kernel -/

/-- Trial division up to `√n`, from ChenExplicit/TwinCUpper.lean. -/
def primeB (n : ℕ) : Bool :=
  2 ≤ n && (List.range' 2 (Nat.sqrt n - 1)).all (fun d => n % d != 0)

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime := by
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hn0 : 0 < n := by omega
    have hsq := Nat.minFac_sq_le_self hn0 hnp
    have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    have hle : n.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hsq
    have hs1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn0
    exact hall n.minFac ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d hd hmod => ?_⟩
    have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hs1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by have := hp.two_le; omega)
    have hdle : d ≤ Nat.sqrt n := by omega
    have hdsq : d * d ≤ n := Nat.le_sqrt.mp hdle
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · subst h; nlinarith [hp.two_le]

/-- Denominator `(n - 1)⁴`. -/
def denN (n : ℕ) : ℕ := (n - 1) ^ 4

/-- Numerator `(n - 1)⁴ + a(n)`. -/
def numN (n : ℕ) : ℕ := if n % 4 = 3 then (n - 1) ^ 4 - (n + 1) ^ 2 else (n - 1) ^ 4 + (3 * n + 1) * (n - 1)

/-- One rounded-up step of the chain at `n`. -/
def step (a n : ℕ) : ℕ :=
  if primeB n && decide (5 < n) then (a * numN n + denN n - 1) / denN n else a

/-- The chain `a₀ = 10¹⁸`, `aₙ₊₁ = step aₙ n`. -/
def chainA : ℕ → ℕ
  | 0 => 10 ^ 18
  | n + 1 => step (chainA n) n

lemma gH_eq {n : ℕ} (hn : 5 < n) : gH n = (numN n : ℝ) / (denN n : ℝ) := by
  have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n : ℝ) - 1) ≠ 0 := by linarith
  have hden : (denN n : ℝ) = ((n : ℝ) - 1) ^ 4 := by
    unfold denN; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  rw [hden]
  unfold gH aH numN
  split_ifs with h
  · have hle : (n + 1) ^ 2 ≤ (n - 1) ^ 4 := by
      have : n + 1 ≤ (n - 1) ^ 2 := by
        have h5 : 5 ≤ n - 1 := by omega
        calc n + 1 = (n - 1) + 2 := by omega
          _ ≤ (n - 1) * (n - 1) := by nlinarith
          _ = (n - 1) ^ 2 := by ring
      calc (n + 1) ^ 2 ≤ ((n - 1) ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
        _ = (n - 1) ^ 4 := by ring
    push_cast [Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp; ring
  · push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp

/-- The rounding goes up: `a gH(n) ≤ step a n` at a prime `n > 5`. -/
lemma step_ge {a n : ℕ} (hn : 5 < n) :
    (a : ℝ) * gH n ≤ ((a * numN n + denN n - 1) / denN n : ℕ) := by
  set q := denN n with hq
  have hq1 : 1 ≤ q := by rw [hq]; unfold denN; exact Nat.one_le_pow _ _ (by omega)
  have hdiv : a * numN n ≤ (a * numN n + q - 1) / q * q := by
    have h := Nat.div_add_mod' (a * numN n + q - 1) q
    have hm := Nat.mod_lt (a * numN n + q - 1) (by omega : 0 < q)
    generalize a * numN n = P at h hm ⊢
    generalize (P + q - 1) / q * q = Z at h ⊢
    omega
  rw [gH_eq hn, ← hq]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [mul_div_assoc', div_le_iff₀ hqpos]
  exact_mod_cast hdiv

/-- **The chain bound.** `10¹⁸ ∏_{5 < p < n} gH(p) ≤ aₙ`. -/
theorem chain_bound (n : ℕ) :
    ((10 ^ 18 : ℕ) : ℝ) * ∏ k ∈ (range n).filter (fun k => k.Prime ∧ 5 < k), gH k ≤ chainA n := by
  induction n with
  | zero => simp [chainA]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n.Prime ∧ 5 < n
    · rw [if_pos h, Finset.prod_insert (by simp)]
      have hstep : step (chainA n) n = (chainA n * numN n + denN n - 1) / denN n := by
        unfold step
        rw [if_pos (by simp [(primeB_iff n).mpr h.1, h.2])]
      simp only [chainA, hstep]
      calc ((10 ^ 18 : ℕ) : ℝ) * (gH n * ∏ k ∈ (range n).filter (fun k => k.Prime ∧ 5 < k), gH k)
          = gH n * (((10 ^ 18 : ℕ) : ℝ) * ∏ k ∈ (range n).filter (fun k => k.Prime ∧ 5 < k), gH k) := by ring
        _ ≤ gH n * (chainA n : ℝ) := mul_le_mul_of_nonneg_left ih (gH_pos h.2).le
        _ = (chainA n : ℝ) * gH n := by ring
        _ ≤ _ := step_ge h.2
    · rw [if_neg h]
      have hstep : step (chainA n) n = chainA n := by
        unfold step
        rw [if_neg]
        intro hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact h ⟨(primeB_iff n).mp hb.1, hb.2⟩
      simp only [chainA, hstep]
      exact ih

theorem chain_last : chainA 20001 = 974238391930890313 := by decide +kernel

/-- `exp` of a head log sum is the head product. -/
lemma exp_head (M : ℕ) : Real.exp (∑ n ∈ range M, lH n) =
    ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 5 < n), gH n := by
  unfold lH
  rw [← Finset.sum_filter, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n hn
  exact Real.exp_log (gH_pos (mem_filter.mp hn).2.2)

/-- **`c₄ ≤ 0.97428`.** Zero sorry. True value 0.9742428. -/
theorem c4_le_97428 : c4 ≤ (97428 / 100000 : ℝ) := by
  rw [c4_eq_exp, ← summable_lH.sum_add_tsum_nat_add 20001, Real.exp_add, exp_head]
  set P := ∏ n ∈ (range 20001).filter (fun n => n.Prime ∧ 5 < n), gH n with hP
  have hc := chain_bound 20001
  rw [chain_last, ← hP] at hc
  have hP0 : 0 ≤ P := prod_nonneg fun n hn => (gH_pos (mem_filter.mp hn).2.2).le
  have hPle : P ≤ (974238391930890313 : ℝ) / 10 ^ 18 := by
    rw [le_div_iff₀ (by positivity), mul_comm]; push_cast at hc; linarith
  have ht := tail_le
  have he : Real.exp (∑' k, lH (k + 20001)) ≤ 1 / (1 - (3003 / 4000) / 20000) := by
    have hx : ∑' k, lH (k + 20001) ≤ (3003 / 4000) / 20000 := ht
    calc Real.exp (∑' k, lH (k + 20001)) ≤ Real.exp ((3003 / 4000) / 20000) := Real.exp_le_exp.mpr hx
      _ ≤ _ := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have he0 : 0 ≤ Real.exp (∑' k, lH (k + 20001)) := (Real.exp_pos _).le
  calc P * Real.exp (∑' k, lH (k + 20001))
      ≤ (974238391930890313 : ℝ) / 10 ^ 18 * (1 / (1 - (3003 / 4000) / 20000)) :=
        mul_le_mul hPle he he0 (by positivity)
    _ ≤ _ := by norm_num

/-- **Hathi 2021, page 6: `c_{4,P} ≤ 0.9743` for `P = {3, 5}`.** Zero sorry. -/
theorem c4_le : c4 ≤ (9743 / 10000 : ℝ) := by
  have := c4_le_97428; linarith

/-- Vacuity test: the factor at `7 ≡ 3 mod 4` is `1 - 64/1296`. The bound `c₄ ≤ 0.97428 < 1`
also rules out the junk value `1` of an unconvergent `tprod`. -/
example : gH 7 = 1 - 64 / 1296 := by unfold gH aH; norm_num

end LeanLab.Hathi2021.C4
