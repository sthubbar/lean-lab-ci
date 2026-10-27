/-
P0080 Hathi 2021, page 11: `c₃` as `exp` of a summable log sum, the head over primes bounded by the
head over survivors, and the tail beyond `2000007`.
Unit U-6154, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.C3Defs

namespace LeanLab.Hathi2021.C3
open Real Finset LeanLab.Hathi2021.Lemma31Consts

/-- The log of `1 + ε(p)` on primes above 5, `0` elsewhere. -/
noncomputable def lF (n : ℕ) : ℝ := if n.Prime ∧ 5 < n then Real.log (epsF n) else 0

lemma seven_le {n : ℕ} (hp : n.Prime) (h5 : 5 < n) : 7 ≤ n := by
  rcases hp.eq_two_or_odd with h | h
  · omega
  · by_contra hc
    have h6 : n = 6 := by omega
    rw [h6] at h; norm_num at h

/-- `1 + ε(n) ≤ 1 + 7.44/n²` for `n ≥ 11`, both classes, from Lemma31Consts. -/
lemma epsF_le_744 {n : ℕ} (hn : 11 ≤ n) : epsF n ≤ 1 + (744 / 100) / (n : ℝ) ^ 2 := by
  have h : (11 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epsF; split_ifs
  · exact eps3_le _ h
  · exact eps1_le _ h

lemma lF_nonneg (n : ℕ) : 0 ≤ lF n := by
  unfold lF; split_ifs with hp
  · exact Real.log_nonneg (epsF_gt_one (seven_le hp.1 hp.2)).le
  · exact le_refl 0

lemma lF_le_eps {n : ℕ} (hn : 7 ≤ n) : lF n ≤ epsF n - 1 := by
  unfold lF; split_ifs with hp
  · exact Real.log_le_sub_one_of_pos (epsF_pos hn)
  · linarith [epsF_gt_one hn]

lemma summable_lF : Summable lF := by
  have h1 : Summable (fun n : ℕ => if n < 11 then lF n else 0) :=
    summable_of_ne_finset_zero (s := range 11) (fun n hn => by
      rw [mem_range] at hn; rw [if_neg hn])
  have h2 : Summable (fun n : ℕ => (744 / 100 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le lF_nonneg (fun n => ?_) (h1.add h2)
  by_cases hn : n < 11
  · simp only [if_pos hn]
    have : 0 ≤ (744 / 100 : ℝ) * (1 / (n : ℝ) ^ 2) := by positivity
    linarith
  · simp only [if_neg hn, zero_add]
    have := lF_le_eps (n := n) (by omega)
    have := epsF_le_744 (n := n) (by omega)
    have : (744 / 100 : ℝ) * (1 / (n : ℝ) ^ 2) = (744 / 100) / (n : ℝ) ^ 2 := by ring
    linarith

/-- `c₃` as `exp` of the `ℕ`-indexed log sum. -/
lemma c3_eq_exp : c3 = Real.exp (∑' n, lF n) := by
  set f : {p : ℕ // p.Prime ∧ 5 < p} → ℝ := fun p => epsF p with hf
  have hpos : ∀ p, 0 < f p := fun p => epsF_pos (seven_le p.2.1 p.2.2)
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := summable_lF.subtype {p : ℕ | p.Prime ∧ 5 < p}
    refine this.congr fun p => ?_
    show lF p.1 = _
    unfold lF; rw [if_pos (show Nat.Prime p.1 ∧ 5 < p.1 from p.2)]
  have hT : c3 = exp (∑' p, Real.log (f p)) := by
    rw [Real.rexp_tsum_eq_tprod hpos hlog]; rfl
  rw [hT]
  congr 1
  rw [show (∑' p, Real.log (f p)) = ∑' p : {p : ℕ | p.Prime ∧ 5 < p}, lF p from by
    apply tsum_congr; intro p; show _ = lF p.1; unfold lF
    rw [if_pos (show Nat.Prime p.1 ∧ 5 < p.1 from p.2)]]
  rw [_root_.tsum_subtype]
  apply tsum_congr
  intro n
  simp only [Set.indicator_apply, Set.mem_setOf_eq, lF]
  split_ifs <;> rfl

/-! ### The head -/

lemma exp_head (M : ℕ) : Real.exp (∑ n ∈ range M, lF n) =
    ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 5 < n), epsF n := by
  unfold lF
  rw [← Finset.sum_filter, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n hn
  exact Real.exp_log (epsF_pos (seven_le (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2))

/-- The product over primes is at most the product over survivors: the extra factors are `> 1`. -/
lemma prime_prod_le_surv (M : ℕ) :
    ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 5 < n), epsF n ≤
      ∏ n ∈ (Ico 7 M).filter (fun n => surv n = true), epsF n := by
  have hsub : (range M).filter (fun n => n.Prime ∧ 5 < n) ⊆ (Ico 7 M).filter (fun n => surv n = true) := by
    intro n hn
    simp only [mem_filter, mem_range, mem_Ico] at hn ⊢
    exact ⟨⟨seven_le hn.2.1 hn.2.2, hn.1⟩, surv_of_prime hn.2.1 hn.2.2⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 : 1 ≤ ∏ n ∈ (Ico 7 M).filter (fun n => surv n = true) \
      (range M).filter (fun n => n.Prime ∧ 5 < n), epsF n := by
    have := Finset.prod_le_prod₀ (s := (Ico 7 M).filter (fun n => surv n = true) \
      (range M).filter (fun n => n.Prime ∧ 5 < n)) (f := fun _ => (1 : ℝ)) (g := epsF)
      (h0 := fun _ _ => zero_le_one) (h1 := fun n hn => by
        simp only [mem_sdiff, mem_filter, mem_Ico] at hn
        exact (epsF_gt_one hn.1.1.1).le)
    simpa using this
  have h0 : 0 ≤ ∏ n ∈ (range M).filter (fun n => n.Prime ∧ 5 < n), epsF n :=
    prod_nonneg fun n hn => (epsF_pos (seven_le (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2)).le
  nlinarith

/-! ### The tail -/

/-- `1 + ε(n) ≤ 1 + 5.01/n²` for `n ≥ 2000`, both classes. -/
lemma eps1_le_501 (p : ℝ) (hp : 2000 ≤ p) : onePlusEps1 p ≤ 1 + (501 / 100) / p ^ 2 := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + (3 * p + 1) * (p - 1) := by positivity
  unfold onePlusEps1
  rw [eps_form p _ _ (by linarith) hA, div_le_iff₀ (by positivity)]
  have ht : (0 : ℝ) ≤ p - 2000 := by linarith
  have hd : 100 * ((1 + (501 / 100) / p ^ 2) * (((p - 1) ^ 4 + (3 * p + 1) * (p - 1)) * p) -
      ((p - 1) ^ 4 + (p - 1) * (p ^ 2 + 6 * p + 1)) * (p - 1)) * p =
      (p - 2000) ^ 4 + 7396 * (p - 2000) ^ 3 + 20379609 * (p - 2000) ^ 2 +
        24766432994 * (p - 2000) + 11182429988000 := by
    field_simp; ring
  have hpos : 0 ≤ (p - 2000) ^ 4 + 7396 * (p - 2000) ^ 3 + 20379609 * (p - 2000) ^ 2 +
      24766432994 * (p - 2000) + 11182429988000 := by positivity
  rw [← hd] at hpos
  have hp0 : 0 < 100 * p := by linarith
  nlinarith

lemma eps3_le_501 (p : ℝ) (hp : 2000 ≤ p) : onePlusEps3 p ≤ 1 + (501 / 100) / p ^ 2 := by
  have hq : (0 : ℝ) < p - 1 := by linarith
  have hA : 0 < (p - 1) ^ 4 + -(p + 1) ^ 2 := by
    have h1 : 100 ≤ (p - 1) ^ 2 := by nlinarith
    have h2 : (p - 1) ^ 4 = ((p - 1) ^ 2) ^ 2 := by ring
    have h3 : (p + 1) ^ 2 ≤ 4 * (p - 1) ^ 2 := by nlinarith
    nlinarith
  unfold onePlusEps3
  rw [eps_form p _ _ (by linarith) hA, div_le_iff₀ (by nlinarith)]
  have ht : (0 : ℝ) ≤ p - 2000 := by linarith
  have hd : 100 * ((1 + (501 / 100) / p ^ 2) * (((p - 1) ^ 4 + -(p + 1) ^ 2) * p) -
      ((p - 1) ^ 4 + (p - 1) * (p + 1) ^ 2) * (p - 1)) * p =
      (p - 2000) ^ 4 + 6596 * (p - 2000) ^ 3 + 15578005 * (p - 2000) ^ 2 +
        15160016994 * (p - 2000) + 4776013988000 := by
    field_simp; ring
  have hpos : 0 ≤ (p - 2000) ^ 4 + 6596 * (p - 2000) ^ 3 + 15578005 * (p - 2000) ^ 2 +
      15160016994 * (p - 2000) + 4776013988000 := by positivity
  rw [← hd] at hpos
  have hp0 : 0 < 100 * p := by linarith
  nlinarith

lemma epsF_le_501 {n : ℕ} (hn : 2000 ≤ n) : epsF n ≤ 1 + (501 / 100) / (n : ℝ) ^ 2 := by
  have h : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epsF; split_ifs
  · exact eps3_le_501 _ h
  · exact eps1_le_501 _ h

lemma surv_mod {n : ℕ} (h : surv n = true) : n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 := by
  simp only [surv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; omega

/-- The least `m ≥ n` with `m ≡ r mod 30`. -/
def mr (r n : ℕ) : ℕ := n + (r + 30 - n % 30) % 30

lemma mr_succ {r n : ℕ} (hr : r < 30) :
    mr r (n + 1) = if n % 30 = r then n + 30 else mr r n := by
  unfold mr; split_ifs <;> omega

lemma mr_self {r n : ℕ} (h : n % 30 = r) : mr r n = n := by unfold mr; omega

/-- One class term of the telescoping majorant. -/
noncomputable def fr (r n : ℕ) : ℝ := 1 / ((mr r n : ℝ) - 15)

lemma fr_step {r n : ℕ} (hr : r < 30) :
    fr r n - fr r (n + 1) = if n % 30 = r then 1 / ((n : ℝ) - 15) - 1 / ((n : ℝ) + 15) else 0 := by
  unfold fr; rw [mr_succ hr]
  split_ifs with h
  · rw [mr_self h]; push_cast; ring
  · ring

/-- The majorant `T(n) = (5.01/30) Σ_{r ∈ (ℤ/30)^×} 1/(m_r(n) - 15)`. -/
noncomputable def TT (n : ℕ) : ℝ :=
  (501 / 3000) * (fr 1 n + fr 7 n + fr 11 n + fr 13 n + fr 17 n + fr 19 n + fr 23 n + fr 29 n)

lemma fr_nonneg {r n : ℕ} (hn : 16 ≤ n) : 0 ≤ fr r n := by
  unfold fr
  have : (16 : ℝ) ≤ (mr r n : ℝ) := by unfold mr; exact_mod_cast (by omega)
  apply div_nonneg zero_le_one; linarith

lemma TT_nonneg {n : ℕ} (hn : 16 ≤ n) : 0 ≤ TT n := by
  unfold TT
  have := @fr_nonneg 1 n hn; have := @fr_nonneg 7 n hn; have := @fr_nonneg 11 n hn
  have := @fr_nonneg 13 n hn; have := @fr_nonneg 17 n hn; have := @fr_nonneg 19 n hn
  have := @fr_nonneg 23 n hn; have := @fr_nonneg 29 n hn
  positivity

/-- **The tail step.** For `n ≥ 2000`, `lF n ≤ T(n) - T(n + 1)`. -/
lemma lF_le_step {n : ℕ} (hn : 2000 ≤ n) : lF n ≤ TT n - TT (n + 1) := by
  have hR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiff : TT n - TT (n + 1) = (501 / 3000) *
      ((fr 1 n - fr 1 (n + 1)) + (fr 7 n - fr 7 (n + 1)) + (fr 11 n - fr 11 (n + 1)) +
        (fr 13 n - fr 13 (n + 1)) + (fr 17 n - fr 17 (n + 1)) + (fr 19 n - fr 19 (n + 1)) +
        (fr 23 n - fr 23 (n + 1)) + (fr 29 n - fr 29 (n + 1))) := by
    unfold TT; ring
  rw [hdiff, fr_step (by norm_num), fr_step (by norm_num), fr_step (by norm_num),
    fr_step (by norm_num), fr_step (by norm_num), fr_step (by norm_num), fr_step (by norm_num),
    fr_step (by norm_num)]
  set D := 1 / ((n : ℝ) - 15) - 1 / ((n : ℝ) + 15) with hD
  have hn1 : (n : ℝ) - 15 ≠ 0 := by intro h; linarith
  have hn2 : (n : ℝ) + 15 ≠ 0 := by intro h; linarith
  have hDeq : D = 30 / (((n : ℝ) - 15) * ((n : ℝ) + 15)) := by
    rw [hD, div_sub_div _ _ hn1 hn2]; congr 1; ring
  by_cases hu : n % 30 = 1 ∨ n % 30 = 7 ∨ n % 30 = 11 ∨ n % 30 = 13 ∨ n % 30 = 17 ∨
      n % 30 = 19 ∨ n % 30 = 23 ∨ n % 30 = 29
  · have hsum : (if n % 30 = 1 then D else 0) + (if n % 30 = 7 then D else 0) +
        (if n % 30 = 11 then D else 0) + (if n % 30 = 13 then D else 0) +
        (if n % 30 = 17 then D else 0) + (if n % 30 = 19 then D else 0) +
        (if n % 30 = 23 then D else 0) + (if n % 30 = 29 then D else 0) = D := by
      rcases hu with h | h | h | h | h | h | h | h <;> simp only [h] <;> norm_num
    rw [hsum]
    have h1 := lF_le_eps (n := n) (by omega)
    have h2 := epsF_le_501 hn
    have h3 : (501 / 100) / (n : ℝ) ^ 2 ≤ (501 / 3000) * D := by
      have hX : 0 < ((n : ℝ) - 15) * ((n : ℝ) + 15) := by
        have : (0 : ℝ) < (n : ℝ) - 15 := by linarith
        positivity
      have hXle : ((n : ℝ) - 15) * ((n : ℝ) + 15) ≤ (n : ℝ) ^ 2 := by nlinarith
      rw [hDeq, show (501 / 3000 : ℝ) * (30 / (((n : ℝ) - 15) * ((n : ℝ) + 15))) =
        (501 / 100) / (((n : ℝ) - 15) * ((n : ℝ) + 15)) by ring]
      exact div_le_div_of_nonneg_left (by norm_num) hX hXle
    linarith
  · push Not at hu
    obtain ⟨h1, h7, h11, h13, h17, h19, h23, h29⟩ := hu
    simp only [if_neg h1, if_neg h7, if_neg h11, if_neg h13, if_neg h17, if_neg h19, if_neg h23,
      if_neg h29, add_zero, mul_zero]
    unfold lF
    rw [if_neg]
    rintro ⟨hp, h5⟩
    obtain ⟨s2, s3, s5⟩ := surv_mod (surv_of_prime hp h5)
    rw [← Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 30)] at s2
    rw [← Nat.mod_mod_of_dvd n (by norm_num : 3 ∣ 30)] at s3
    rw [← Nat.mod_mod_of_dvd n (by norm_num : 5 ∣ 30)] at s5
    have hlt : n % 30 < 30 := Nat.mod_lt _ (by norm_num)
    generalize n % 30 = r at *
    interval_cases r <;> simp_all

/-- **The tail.** `∑_{n ≥ X} lF n ≤ T(X)` for `X ≥ 2000`. -/
lemma tail_le (X : ℕ) (hX : 2000 ≤ X) : ∑' k, lF (k + X) ≤ TT X := by
  have hs : Summable (fun k => lF (k + X)) := (summable_nat_add_iff X).mpr summable_lF
  refine hs.tsum_le_of_sum_range_le fun K => ?_
  calc ∑ k ∈ range K, lF (k + X) ≤ ∑ k ∈ range K, (TT (k + X) - TT (k + 1 + X)) := by
        apply sum_le_sum; intro k _
        have := lF_le_step (n := k + X) (by omega)
        rwa [show k + X + 1 = k + 1 + X by ring] at this
    _ = TT (0 + X) - TT (K + X) := sum_range_sub' (fun k => TT (k + X)) K
    _ ≤ TT X := by have := TT_nonneg (n := K + X) (by omega); simp; linarith

end LeanLab.Hathi2021.C3
