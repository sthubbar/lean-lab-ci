/-
Proof of `leaf_err_remainder` of SPLIT_Decomp409bErr.lean, P0069 page 27, display (4.13),
the remainder "at most M N gamma w times x^o(1), below x^0.96 under (4.8) or (4.9) once
epsilon is small". Restated verbatim as `leaf_err_remainder_of_leaves`.
The divisor bound tau(n) at most C n^ε is proved here, its proof copied from the proved
theorem `card_divisors_le_rpow` of LeanLab.Akeno2026.Decomp86, not imported since that
module is heavy. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- Proved helper, the divisor bound, copied from `Akeno2026.Decomp86.card_divisors_le_rpow`. -/
theorem s409r_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)


/-- Proved helper: the dyadic block Ioc of M and 2M has at most max M 0 + 1 elements. -/
theorem s409r_card_le (M : ℝ) :
    ((Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) ≤ max M 0 + 1 := by
  rw [Nat.card_Ioc]
  rcases le_or_gt M 0 with hM | hM
  · have : ⌊2 * M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [this]; simp; linarith [le_max_right M 0]
  · rcases le_total ⌊M⌋₊ ⌊2 * M⌋₊ with h | h
    · rw [Nat.cast_sub h]
      have h1 : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
      have h2 : M < ⌊M⌋₊ + 1 := Nat.lt_floor_add_one M
      have := le_max_left M 0
      linarith
    · rw [Nat.sub_eq_zero_of_le h]; simp; linarith [le_max_right M 0]

/-- Proved helper: tau(n)^B is at most C1 n^(1/1000) for n at least 1. -/
theorem s409r_tau_rpow_le (B : ℝ) : ∃ C1 : ℝ, 0 < C1 ∧ ∀ n : ℕ, 1 ≤ n →
    tau n ^ B ≤ C1 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  set e : ℝ := 1 / (1000 * (|B| + 1)) with he
  have he0 : 0 < e := by positivity
  obtain ⟨C0, hC0, h0⟩ := s409r_card_divisors_le_rpow he0
  refine ⟨max C0 1 ^ |B|, Real.rpow_pos_of_pos (by positivity) _, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htau : tau n = (n.divisors.card : ℝ) := by
    simp [tau, ArithmeticFunction.sigma_zero_apply]
  have ht1 : 1 ≤ tau n := by
    rw [htau]
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩⟩
  have hb : tau n ≤ max C0 1 * (n : ℝ) ^ e := by
    rw [htau]
    exact (h0 n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hexp : e * |B| ≤ 1 / 1000 := by
    rw [he, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg B]
  calc tau n ^ B ≤ tau n ^ |B| := Real.rpow_le_rpow_of_exponent_le ht1 (le_abs_self B)
    _ ≤ (max C0 1 * (n : ℝ) ^ e) ^ |B| :=
        Real.rpow_le_rpow (by linarith) hb (abs_nonneg B)
    _ = max C0 1 ^ |B| * (n : ℝ) ^ (e * |B|) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith)]
    _ ≤ max C0 1 ^ |B| * (n : ℝ) ^ (1 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp)
          (Real.rpow_nonneg (by positivity) _)

/-- Proved helper: the plain weight sum over the block is at most
(max M 0 + 1) times 2 C1 x^(1/1000) when M is at most x. -/
theorem s409r_sum_le {B C1 : ℝ} (hC1 : 0 < C1)
    (hτ : ∀ n : ℕ, 1 ≤ n → tau n ^ B ≤ C1 * (n : ℝ) ^ (1 / 1000 : ℝ))
    (a : ℕ → ℂ) (ha : ∀ k, ‖a k‖ ≤ tau k ^ B) {M x : ℝ} (hx : 1 ≤ x) (hMx : M ≤ x) :
    ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ ≤ (max M 0 + 1) * (2 * C1 * x ^ (1 / 1000 : ℝ)) := by
  have hK : ∀ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ ≤ 2 * C1 * x ^ (1 / 1000 : ℝ) := by
    intro m hm
    rw [mem_Ioc] at hm
    have hm1 : 1 ≤ m := by omega
    have hM0 : 0 ≤ M := by
      by_contra h; push Not at h
      have : ⌊2 * M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have hmx : (m : ℝ) ≤ 2 * x := by
      have : (m : ℝ) ≤ ⌊2 * M⌋₊ := by exact_mod_cast hm.2
      have := Nat.floor_le (show 0 ≤ 2 * M by linarith)
      linarith
    have hm1' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc ‖a m‖ ≤ C1 * (m : ℝ) ^ (1 / 1000 : ℝ) := (ha m).trans (hτ m hm1)
      _ ≤ C1 * (2 * x) ^ (1 / 1000 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm1' hmx (by norm_num)) hC1.le
      _ = C1 * (2 ^ (1 / 1000 : ℝ) * x ^ (1 / 1000 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
      _ ≤ C1 * (2 * x ^ (1 / 1000 : ℝ)) := by
          gcongr
          calc (2 : ℝ) ^ (1 / 1000 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 2 * C1 * x ^ (1 / 1000 : ℝ) := by ring
  calc _ ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, 2 * C1 * x ^ (1 / 1000 : ℝ) := sum_le_sum hK
    _ = ((Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) * (2 * C1 * x ^ (1 / 1000 : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (s409r_card_le M) (by positivity)

/-- `leaf_err_remainder` of SPLIT_Decomp409bErr, verbatim, proved outright with ε0 = 0.06:
(M+1)(N+1) at most 4 x^0.94 under (4.8) or (4.9), tau^B at most C1 n^(1/1000), gamma at most
2 x^(ε/12) and w at most x^(1/1000) for large x, total exponent 0.94 + 3/1000 + ε/12 < 0.96. -/
theorem leaf_err_remainder_of_leaves :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
        2 * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖) * (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖)) *
          (cutoff ε x * wof x + 1) ≤ C * x ^ (0.96 : ℝ) := by
  refine ⟨0.06, by norm_num, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨C1, hC1, hτ⟩ := s409r_tau_rpow_le B
  obtain ⟨Xw, hXw⟩ := wof_le_rpow_ev (1 / 1000) (by norm_num)
  refine ⟨96 * C1 ^ 2, max Xw 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hwx : wof x ≤ x ^ (1 / 1000 : ℝ) := hXw x (le_trans (le_max_left _ _) hx)
  have one_le : ∀ c : ℝ, 0 ≤ c → 1 ≤ x ^ c := fun c hc => Real.one_le_rpow hx1 hc
  have mono : ∀ c d : ℝ, c ≤ d → x ^ c ≤ x ^ d :=
    fun c d h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have key : ∃ P Q : ℝ, 1 ≤ P ∧ 1 ≤ Q ∧ P * Q ≤ x ^ (0.94 : ℝ) ∧ M x ≤ P ∧ N x ≤ Q ∧
      P ≤ x ∧ Q ≤ x := by
    rcases hr x with h | h
    · set P := max (x ^ (0.45 : ℝ)) (M x)
      set Q := max (x ^ (0.225 : ℝ)) (N x)
      have hP : 1 ≤ P := (one_le _ (by norm_num)).trans (le_max_left _ _)
      have hQ : 1 ≤ Q := (one_le _ (by norm_num)).trans (le_max_left _ _)
      have h775 : x ^ (0.775 : ℝ) ≤ x := by
        simpa using mono 0.775 1 (by norm_num)
      have hPQ1 : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hQ
      have hPQ2 : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hP
      exact ⟨P, Q, hP, hQ, h.trans (mono _ _ (by norm_num)), le_max_right _ _, le_max_right _ _,
        by linarith, by linarith⟩
    · set R := x ^ (0.46 + ε / 8)
      have hR : 1 ≤ R := one_le _ (by linarith)
      have hRx : R ≤ x := by simpa using mono (0.46 + ε / 8) 1 (by linarith)
      have hRR : R * R ≤ x ^ (0.94 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]
        exact mono _ _ (by linarith)
      exact ⟨R, R, hR, hR, hRR, (le_max_left _ _).trans h, (le_max_right _ _).trans h, hRx, hRx⟩
  obtain ⟨P, Q, hP, hQ, hPQ, hMP, hNQ, hPx, hQx⟩ := key
  set δ : ℝ := 1 / 1000
  have hxδ : 0 ≤ x ^ δ := Real.rpow_nonneg hx0 _
  have hA := s409r_sum_le hC1 hτ (a x) (ha x) hx1 (hMP.trans hPx)
  have hB := s409r_sum_le hC1 hτ (b x) (hb x) hx1 (hNQ.trans hQx)
  have hA' : ∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ ≤ 4 * C1 * P * x ^ δ := by
    have : max (M x) 0 + 1 ≤ 2 * P := by
      have := max_le hMP (show (0 : ℝ) ≤ P by linarith); linarith
    calc _ ≤ _ := hA
      _ ≤ (2 * P) * (2 * C1 * x ^ δ) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hB' : ∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ ≤ 4 * C1 * Q * x ^ δ := by
    have : max (N x) 0 + 1 ≤ 2 * Q := by
      have := max_le hNQ (show (0 : ℝ) ≤ Q by linarith); linarith
    calc _ ≤ _ := hB
      _ ≤ (2 * Q) * (2 * C1 * x ^ δ) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hγ : cutoff ε x ≤ 2 * x ^ (ε / 12) := by
    unfold cutoff
    have := one_le (ε / 12) (by linarith)
    exact max_le (by linarith) (by linarith)
  have hw1 : 1 ≤ wof x := by
    unfold wof
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hγ0 : 0 ≤ cutoff ε x := le_trans (by norm_num) (le_max_left _ _)
  have hcut : cutoff ε x * wof x + 1 ≤ 3 * (x ^ (ε / 12) * x ^ δ) := by
    have h1 := one_le (ε / 12) (by linarith)
    have h2 := one_le δ (by norm_num)
    have : cutoff ε x * wof x ≤ (2 * x ^ (ε / 12)) * x ^ δ :=
      mul_le_mul hγ hwx (by linarith) (by positivity)
    nlinarith
  have hSA : 0 ≤ ∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hSB : 0 ≤ ∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hc0 : 0 ≤ cutoff ε x * wof x + 1 := by positivity
  have hprod := mul_le_mul (mul_le_mul hA' hB' hSB (by positivity)) hcut hc0 (by positivity)
  have hexp : x ^ δ * x ^ δ * x ^ δ * x ^ (ε / 12) = x ^ (3 * δ + ε / 12) := by
    rw [← Real.rpow_add' hx0 (by norm_num), ← Real.rpow_add' hx0 (by norm_num),
      ← Real.rpow_add' hx0 (by positivity)]
    ring_nf
  have hfin : x ^ (0.94 : ℝ) * x ^ (3 * δ + ε / 12) ≤ x ^ (0.96 : ℝ) := by
    rw [← Real.rpow_add' hx0 (by positivity)]
    exact mono _ _ (by linarith)
  have hxe : 0 ≤ x ^ (3 * δ + ε / 12) := Real.rpow_nonneg hx0 _
  calc _ ≤ 2 * ((4 * C1 * P * x ^ δ) * (4 * C1 * Q * x ^ δ)) * (3 * (x ^ (ε / 12) * x ^ δ)) := by
        linarith
    _ = 96 * C1 ^ 2 * ((P * Q) * (x ^ δ * x ^ δ * x ^ δ * x ^ (ε / 12))) := by ring
    _ = 96 * C1 ^ 2 * ((P * Q) * x ^ (3 * δ + ε / 12)) := by rw [hexp]
    _ ≤ 96 * C1 ^ 2 * (x ^ (0.94 : ℝ) * x ^ (3 * δ + ε / 12)) := by
        gcongr
    _ ≤ 96 * C1 ^ 2 * x ^ (0.96 : ℝ) := by gcongr

#print axioms leaf_err_remainder_of_leaves

#print axioms s409r_card_divisors_le_rpow
#print axioms s409r_sum_le

end LeanLab.BakerHarmanPintz1997.Decomp409b
