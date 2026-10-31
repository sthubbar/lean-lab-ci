/-
Lean Lab, ChenExplicit, unit U-1235, track T2 FRONTIER, idea I-0090, run 20261020T1403Z-32020.
P0009, Bordignon, Johnston, Starichkova, arXiv 2207.09452, Lemma 18, p. 18, for every u₀ ≥ 3 in
place of the paper's u₀ = 10⁹, from the paper's own Lemma 17, p. 16, taken as hypotheses:
(48) Σ_{p ≤ x} 1/p ≥ log log x + M − 2.964·10⁻⁶/log x for x ≥ 2, and
(49) Σ_{p ≤ x} 1/p ≤ log log x + M + 1.436·10⁻¹⁶/log x for x > exp 4000.

`lemma18_general`: for 3 ≤ u < z, z > exp 4000,
  ∏_{u ≤ p < z} (1 − 1/(p − 1))⁻¹ ≤ exp(1/(u−2) + 1/(u−1) + 1/u + 2.964·10⁻⁶/log u + 1.436·10⁻¹⁶/log z)
                                   · log z / log u.
`lemma18_u0`: hence (53) holds with ε = epsU0 u₀ for all u₀ < u < z, strictly.
`epsU0_50000_le`: epsU0 50000 ≤ 6.1·10⁻⁵, so 1/ε ≥ 16393 and Table 1's row 1/ε = 10000 applies.

The route differs from the paper's: (p−1)/(p−2) ≤ exp(1/(p−2)) and 1/(p−2) = 1/p + t(p) with
t(n) = 1/(n−2) − 1/n, whose sum over all n ≥ ⌈u⌉ telescopes to at most 1/(u−2) + 1/(u−1). So Lemma 15,
the prime in [0.999x, x), is not needed, which is what lets u₀ go below exp 20.

CONDITIONAL ON Lemma 17 of the paper, which rests on its own computation to 10¹² and on cited
explicit bounds for θ(x). AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ChenExplicit.Lemma18General

open Real Finset

/-- `Σ_{p ≤ x} 1/p`. -/
noncomputable def recipSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- The primes `p` with `u ≤ p < z`. -/
noncomputable def primesIco (u z : ℝ) : Finset ℕ := (Finset.Ico ⌈u⌉₊ ⌈z⌉₊).filter Nat.Prime

/-- Lemma 17 (48), cited. -/
def Lemma17Lower (M : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → log (log x) + M - 2.964e-6 / log x ≤ recipSum x

/-- Lemma 17 (49), cited. -/
def Lemma17Upper (M : ℝ) : Prop :=
  ∀ x : ℝ, exp 4000 < x → recipSum x ≤ log (log x) + M + 1.436e-16 / log x

/-- `ε(u₀)` of the general Lemma 18. -/
noncomputable def epsU0 (u0 : ℝ) : ℝ :=
  exp (1 / (u0 - 2) + 1 / (u0 - 1) + 1 / u0 + 2.964e-6 / log u0 + 1.436e-16 / 4000) - 1

lemma mem_primesIco {u z : ℝ} {p : ℕ} (h : p ∈ primesIco u z) : u ≤ p ∧ (p : ℝ) < z ∧ p.Prime := by
  unfold primesIco at h
  rw [Finset.mem_filter, Finset.mem_Ico] at h
  refine ⟨Nat.ceil_le.mp h.1.1, ?_, h.2⟩
  exact (Nat.lt_ceil).mp h.1.2

/-- Pointwise: `(1 − 1/(P − 1))⁻¹ ≤ exp(1/(P − 2))` for `P ≥ 3`. -/
lemma factor_le (P : ℝ) (hP : 3 ≤ P) : (1 - 1 / (P - 1))⁻¹ ≤ exp (1 / (P - 2)) := by
  have hne1 : P - 1 ≠ 0 := by linarith
  have hne2 : P - 2 ≠ 0 := by linarith
  have h1 : 1 - 1 / (P - 1) = (P - 2) / (P - 1) := by
    rw [one_sub_div hne1]; congr 1; ring
  have h2 : (P - 1) / (P - 2) = 1 / (P - 2) + 1 := by
    rw [div_add_one hne2]; congr 1; ring
  rw [h1, inv_div, h2]; exact Real.add_one_le_exp _

/-- `1/(n − 2) = 1/n + t n` with `t n = 1/(n − 2) − 1/n`. -/
noncomputable def t (n : ℕ) : ℝ := 1 / ((n : ℝ) - 2) - 1 / n

lemma t_nonneg (n : ℕ) (hn : 3 ≤ n) : 0 ≤ t n := by
  unfold t
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 0 < (n : ℝ) - 2 := by linarith
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le h2 (by linarith)

/-- Telescoping, exact form: `Σ_{a ≤ n < a + k} t n = 1/(a−2) + 1/(a−1) − 1/(a+k−2) − 1/(a+k−1)`. -/
lemma sum_t_eq (a : ℕ) (ha : 3 ≤ a) (k : ℕ) :
    ∑ n ∈ Finset.Ico a (a + k), t n =
      1 / ((a : ℝ) - 2) + 1 / ((a : ℝ) - 1) - 1 / ((a : ℝ) + k - 2) - 1 / ((a : ℝ) + k - 1) := by
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    unfold t
    push_cast
    rw [show (a : ℝ) + (k + 1) - 2 = a + k - 1 by ring, show (a : ℝ) + (k + 1) - 1 = a + k by ring]
    ring

lemma sum_t_le (a b : ℕ) (ha : 3 ≤ a) :
    ∑ n ∈ Finset.Ico a b, t n ≤ 1 / ((a : ℝ) - 2) + 1 / ((a : ℝ) - 1) := by
  rcases le_or_gt b a with hb | hb
  · rw [Finset.Ico_eq_empty_of_le hb, Finset.sum_empty]
    have : (3 : ℝ) ≤ a := by exact_mod_cast ha
    have : 0 < 1 / ((a : ℝ) - 2) := by apply div_pos one_pos; linarith
    have : 0 < 1 / ((a : ℝ) - 1) := by apply div_pos one_pos; linarith
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    rw [sum_t_eq a ha k]
    have : (3 : ℝ) ≤ a := by exact_mod_cast ha
    have hk : (0 : ℝ) ≤ k := by positivity
    have : 0 < 1 / ((a : ℝ) + k - 2) := by apply div_pos one_pos; linarith
    have : 0 < 1 / ((a : ℝ) + k - 1) := by apply div_pos one_pos; linarith
    linarith

/-- The prime sum over `[u, z)` against Lemma 17's sums: at most `recipSum z − recipSum u + 1/u`. -/
lemma sum_primesIco_le (u z : ℝ) (hu : 3 ≤ u) (huz : u < z) :
    ∑ p ∈ primesIco u z, (1 : ℝ) / p ≤ recipSum z - recipSum u + 1 / u := by
  set a := ⌈u⌉₊
  set A := ⌊u⌋₊
  set B := ⌊z⌋₊
  have hz0 : 0 ≤ z := by linarith
  have haA : a ≤ A + 1 := Nat.ceil_le_floor_add_one u
  have haB : a ≤ B + 1 := by
    have h1 : a ≤ ⌈z⌉₊ := Nat.ceil_mono huz.le
    have h2 : ⌈z⌉₊ ≤ B + 1 := Nat.ceil_le_floor_add_one z
    omega
  -- step 1: primesIco ⊆ primes in Ico a (B + 1)
  have hsub : primesIco u z ⊆ (Finset.Ico a (B + 1)).filter Nat.Prime := by
    intro p hp
    unfold primesIco at hp
    rw [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    have : ⌈z⌉₊ ≤ B + 1 := Nat.ceil_le_floor_add_one z
    omega
  have hstep1 : ∑ p ∈ primesIco u z, (1 : ℝ) / p ≤
      ∑ p ∈ (Finset.Ico a (B + 1)).filter Nat.Prime, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  -- step 2: recipSum z splits at a
  have hz_split : recipSum z = ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / p +
      ∑ p ∈ (Finset.Ico a (B + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    unfold recipSum
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_range_add_sum_Ico _ haB]
  have hu_split : recipSum u = ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / p +
      ∑ p ∈ (Finset.Ico a (A + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    unfold recipSum
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_range_add_sum_Ico _ haA]
  -- step 3: the piece Ico a (A + 1) has at most one element, each at most 1/u
  have hpiece : ∑ p ∈ (Finset.Ico a (A + 1)).filter Nat.Prime, (1 : ℝ) / p ≤ 1 / u := by
    have hcard : ((Finset.Ico a (A + 1)).filter Nat.Prime).card ≤ 1 := by
      calc ((Finset.Ico a (A + 1)).filter Nat.Prime).card ≤ (Finset.Ico a (A + 1)).card :=
            Finset.card_filter_le _ _
        _ = A + 1 - a := Nat.card_Ico _ _
        _ ≤ 1 := by
            have : A ≤ a := Nat.floor_le_ceil u
            omega
    have hterm : ∀ p ∈ (Finset.Ico a (A + 1)).filter Nat.Prime, (1 : ℝ) / p ≤ 1 / u := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ico] at hp
      have hup : u ≤ p := Nat.ceil_le.mp hp.1.1
      exact one_div_le_one_div_of_le (by linarith) hup
    calc ∑ p ∈ (Finset.Ico a (A + 1)).filter Nat.Prime, (1 : ℝ) / p
        ≤ ((Finset.Ico a (A + 1)).filter Nat.Prime).card • (1 / u) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 1 • (1 / u) := by
          rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_one]
          have h0 : 0 ≤ 1 / u := by apply div_nonneg one_pos.le; linarith
          have hc : (((Finset.Ico a (A + 1)).filter Nat.Prime).card : ℝ) ≤ 1 := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hc h0
      _ = 1 / u := one_smul _ _
  linarith

/-- **Lemma 18, general `u`**, from Lemma 17 (48) and (49). -/
theorem lemma18_general (M : ℝ) (h48 : Lemma17Lower M) (h49 : Lemma17Upper M) (u z : ℝ)
    (hu : 3 ≤ u) (huz : u < z) (hz : exp 4000 < z) :
    ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      exp (1 / (u - 2) + 1 / (u - 1) + 1 / u + 2.964e-6 / log u + 1.436e-16 / log z) *
        (log z / log u) := by
  have hlu : 0 < log u := Real.log_pos (by linarith)
  have hlz : 0 < log z := Real.log_pos (by linarith)
  -- every prime in range is at least 3
  have hge3 : ∀ p ∈ primesIco u z, (3 : ℝ) ≤ p := fun p hp => le_trans hu (mem_primesIco hp).1
  -- pointwise to exp of a sum
  have hprod : ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      exp (∑ p ∈ primesIco u z, ((1 : ℝ) / p + t p)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp
      have h3 := hge3 p hp
      have : 0 < 1 - 1 / ((p : ℝ) - 1) := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity
    · intro p hp
      have h3 := hge3 p hp
      have : (1 : ℝ) / p + t p = 1 / ((p : ℝ) - 2) := by unfold t; ring
      rw [this]; exact factor_le _ h3
  rw [Finset.sum_add_distrib] at hprod
  -- the t part
  have ha3 : 3 ≤ ⌈u⌉₊ := by
    have : (3 : ℝ) ≤ ⌈u⌉₊ := le_trans hu (Nat.le_ceil u)
    exact_mod_cast this
  have ht : ∑ p ∈ primesIco u z, t p ≤ 1 / (u - 2) + 1 / (u - 1) := by
    have h1 : ∑ p ∈ primesIco u z, t p ≤ ∑ n ∈ Finset.Ico ⌈u⌉₊ ⌈z⌉₊, t n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn _
      rw [Finset.mem_Ico] at hn
      exact t_nonneg n (le_trans ha3 hn.1)
    have h2 := sum_t_le ⌈u⌉₊ ⌈z⌉₊ ha3
    have hceil : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h3 : 1 / ((⌈u⌉₊ : ℝ) - 2) ≤ 1 / (u - 2) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have h4 : 1 / ((⌈u⌉₊ : ℝ) - 1) ≤ 1 / (u - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  -- the 1/p part, by Lemma 17
  have hs := sum_primesIco_le u z hu huz
  have hlow := h48 u (by linarith)
  have hup := h49 z hz
  have hsum : ∑ p ∈ primesIco u z, (1 : ℝ) / p ≤
      (log (log z) - log (log u)) + 1.436e-16 / log z + 2.964e-6 / log u + 1 / u := by linarith
  have hexp : exp (log (log z) - log (log u)) = log z / log u := by
    rw [Real.exp_sub, Real.exp_log hlz, Real.exp_log hlu]
  calc ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹
      ≤ exp (∑ p ∈ primesIco u z, (1 : ℝ) / p + ∑ p ∈ primesIco u z, t p) := hprod
    _ ≤ exp ((log (log z) - log (log u)) +
          (1 / (u - 2) + 1 / (u - 1) + 1 / u + 2.964e-6 / log u + 1.436e-16 / log z)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = exp (1 / (u - 2) + 1 / (u - 1) + 1 / u + 2.964e-6 / log u + 1.436e-16 / log z) *
          (log z / log u) := by
        rw [Real.exp_add, hexp, mul_comm]

/-- **(53) for a general `u₀ ≥ 3`**: for `u₀ ≤ u < z`, `z > exp 4000`,
`∏_{u ≤ p < z} (1 − 1/(p − 1))⁻¹ < (1 + epsU0 u₀) log z / log u`. -/
theorem lemma18_u0 (M : ℝ) (h48 : Lemma17Lower M) (h49 : Lemma17Upper M) (u0 u z : ℝ)
    (hu0 : 3 ≤ u0) (hu : u0 ≤ u) (huz : u < z) (hz : exp 4000 < z) :
    ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ < (1 + epsU0 u0) * (log z / log u) := by
  have hmain := lemma18_general M h48 h49 u z (le_trans hu0 hu) huz hz
  have hlu0 : 0 < log u0 := Real.log_pos (by linarith)
  have hlu : 0 < log u := Real.log_pos (by linarith)
  have hz4000 : 4000 < log z := by
    rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (4000 : ℝ)])]; exact hz
  have hlz : 0 < log z := by linarith
  have hratio : 0 < log z / log u := div_pos hlz hlu
  have e1 : 1 / (u - 2) ≤ 1 / (u0 - 2) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have e2 : 1 / (u - 1) ≤ 1 / (u0 - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have e3 : 1 / u ≤ 1 / u0 := one_div_le_one_div_of_le (by linarith) hu
  have e4 : 2.964e-6 / log u ≤ 2.964e-6 / log u0 :=
    div_le_div_of_nonneg_left (by norm_num) hlu0 (Real.log_le_log (by linarith) hu)
  have e5 : 1.436e-16 / log z < 1.436e-16 / 4000 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hz4000
  have hE : exp (1 / (u - 2) + 1 / (u - 1) + 1 / u + 2.964e-6 / log u + 1.436e-16 / log z) <
      1 + epsU0 u0 := by
    unfold epsU0
    rw [add_sub_cancel]
    apply Real.exp_lt_exp.mpr
    linarith
  calc ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹
      ≤ exp (1 / (u - 2) + 1 / (u - 1) + 1 / u + 2.964e-6 / log u + 1.436e-16 / log z) *
        (log z / log u) := hmain
    _ < (1 + epsU0 u0) * (log z / log u) := mul_lt_mul_of_pos_right hE hratio

/-- `c ≤ log x` from `exp c ≤ x`. -/
lemma log_ge_of_exp_le {x c : ℝ} (hx : 0 < x) (h : exp c ≤ x) : c ≤ log x := by
  rw [Real.le_log_iff_exp_le hx]; exact h

/-- `exp y ≤ 1 + y + y²` for `0 ≤ y ≤ 1`. -/
lemma exp_le_quad {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : exp y ≤ 1 + y + y ^ 2 := by
  have hb := Real.exp_bound' (x := y) h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  nlinarith

/-- `epsU0 50000 ≤ 6.1·10⁻⁵`, so `1/ε ≥ 16393` and Table 1's row `1/ε = 10000`,
`C₁ = 106`, `C₂ = 108`, applies, since `C₁, C₂` decrease in `1/ε`. -/
theorem epsU0_50000_le : epsU0 50000 ≤ 6.1e-5 := by
  unfold epsU0
  have hl : (10 : ℝ) ≤ log 50000 := by
    apply log_ge_of_exp_le (by norm_num)
    have he : exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
    have h10 : exp (10 : ℝ) = exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h10]
    have : exp (1 : ℝ) ^ 10 ≤ 2.7182818286 ^ 10 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 10
    have : (2.7182818286 : ℝ) ^ 10 ≤ 50000 := by norm_num
    linarith
  have hfrac : 2.964e-6 / log (50000 : ℝ) ≤ 2.964e-7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set y := 1 / ((50000 : ℝ) - 2) + 1 / (50000 - 1) + 1 / 50000 + 2.964e-6 / log 50000 + 1.436e-16 / 4000
  have hy0 : 0 ≤ y := by
    have : 0 ≤ 2.964e-6 / log (50000 : ℝ) := by positivity
    simp only [y]; norm_num; linarith
  have hy1 : y ≤ 6.03e-5 := by simp only [y]; norm_num; linarith
  have := exp_le_quad hy0 (by linarith)
  nlinarith

/-- The control, `epsU0 10⁹ ≤ 1.52·10⁻⁷`, within five percent of the paper's 1.452·10⁻⁷; the gap is
the extra `1/u₀` boundary term, the cruder bound for the `(p−1)²/(p(p−2))` factor, and log 10⁹ ≥ 20. -/
theorem epsU0_1e9_le : epsU0 1000000000 ≤ 1.52e-7 := by
  unfold epsU0
  have hl : (20 : ℝ) ≤ log 1000000000 := by
    apply log_ge_of_exp_le (by norm_num)
    have he : exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
    have h20 : exp (20 : ℝ) = exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h20]
    have : exp (1 : ℝ) ^ 20 ≤ 2.7182818286 ^ 20 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 20
    have : (2.7182818286 : ℝ) ^ 20 ≤ 1000000000 := by norm_num
    linarith
  have hfrac : 2.964e-6 / log (1000000000 : ℝ) ≤ 1.482e-7 := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  set y := 1 / ((1000000000 : ℝ) - 2) + 1 / (1000000000 - 1) + 1 / 1000000000 +
    2.964e-6 / log 1000000000 + 1.436e-16 / 4000
  have hy0 : 0 ≤ y := by
    have : 0 ≤ 2.964e-6 / log (1000000000 : ℝ) := by positivity
    simp only [y]; norm_num; linarith
  have hy1 : y ≤ 1.5121e-7 := by simp only [y]; norm_num; linarith
  have := exp_le_quad hy0 (by linarith)
  nlinarith

/-! ### Vacuity -/

/-- The hypotheses of `lemma18_u0` can hold together: `u₀ = u = 50000`, `z = exp 4001`. -/
example : (3 : ℝ) ≤ 50000 ∧ (50000 : ℝ) ≤ 50000 ∧ (50000 : ℝ) < exp 4001 ∧ exp 4000 < exp 4001 := by
  refine ⟨by norm_num, le_rfl, ?_, Real.exp_lt_exp.mpr (by norm_num)⟩
  have h11 : exp (11 : ℝ) = exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  have he : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have : (2.7 : ℝ) ^ 11 < exp 1 ^ 11 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have : exp (11 : ℝ) < exp 4001 := Real.exp_lt_exp.mpr (by norm_num)
  have : (50000 : ℝ) < 2.7 ^ 11 := by norm_num
  linarith

end LeanLab.ChenExplicit.Lemma18General

#print axioms LeanLab.ChenExplicit.Lemma18General.lemma18_general
#print axioms LeanLab.ChenExplicit.Lemma18General.lemma18_u0
#print axioms LeanLab.ChenExplicit.Lemma18General.epsU0_50000_le
#print axioms LeanLab.ChenExplicit.Lemma18General.epsU0_1e9_le
#print axioms LeanLab.ChenExplicit.Lemma18General.sum_primesIco_le
#print axioms LeanLab.ChenExplicit.Lemma18General.sum_t_le
