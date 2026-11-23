import LeanLab.Zhan1991.SingSeries1122

/-!
P0068 Zhan 1991, page 271, the tail of the singular series beyond `Q₁ = L^d`, the Prop
`SingSeriesTail`, proved by the elementary route: `|c_q(N)| ≤ φ(q)`, so
`|μ(q) c_q(N)/φ(q)³| ≤ φ(q)⁻²`, and `16 φ(q)⁴ ≥ q³` from `φ(q) ∏_{p ∣ q} p = q ∏_{p ∣ q} (p - 1)`,
so the tail beyond `Q` is at most `8 / √Q` by telescoping against `1/√q`.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real
open scoped ArithmeticFunction.Moebius

/-- `|c_q(N)| ≤ φ(q)`: a sum of `φ(q)` cosines. -/
theorem ramanujanC_abs_le (q N : ℕ) : |ramanujanC q N| ≤ (Nat.totient q : ℝ) := by
  have hc : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  unfold ramanujanC
  calc |∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          Real.cos (2 * π * (a : ℝ) * N / q)|
      ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          |Real.cos (2 * π * (a : ℝ) * N / q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => Real.abs_cos_le_one _)
    _ = (Nat.totient q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]

/-- `|μ(q) c_q(N)/φ(q)³| ≤ 1/φ(q)²`. -/
theorem singTerm_abs_le (N q : ℕ) : |singTerm N q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
  by_cases hq : q = 0
  · subst hq; simp [singTerm]
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have hμ : |(μ q : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  simp only [singTerm, hq, ite_false]
  rw [abs_mul, abs_div, abs_of_pos (pow_pos hφ 3)]
  calc |(μ q : ℝ)| / (Nat.totient q : ℝ) ^ 3 * |ramanujanC q N|
      ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) :=
        mul_le_mul (div_le_div_of_nonneg_right hμ (by positivity)) (ramanujanC_abs_le q N)
          (abs_nonneg _) (by positivity)
    _ = 1 / (Nat.totient q : ℝ) ^ 2 := by field_simp

/-- Elementary lower bound for the totient: `n³ ≤ 16 φ(n)⁴`. -/
theorem cube_le_totient_pow_four (n : ℕ) : n ^ 3 ≤ 16 * (Nat.totient n) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h1 := Nat.totient_mul_prod_primeFactors n
  set P := ∏ p ∈ n.primeFactors, p with hPdef
  set R := ∏ p ∈ n.primeFactors, (p - 1) with hRdef
  have hPn : P ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hPpos : 0 < P := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  -- the per prime weight
  have hstep : ∀ p ∈ n.primeFactors,
      p ^ 3 ≤ ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1)) * (p - 1) ^ 4 := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    by_cases h2 : p = 2
    · subst h2; norm_num
    by_cases h3 : p = 3
    · subst h3; norm_num
    simp only [h2, h3, ite_false, mul_one, one_mul]
    have h4 : p ≠ 4 := by
      rintro rfl; exact absurd hpr (by decide)
    have h5 : 5 ≤ p := by have := hpr.two_le; omega
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hk : 4 ≤ k := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith [Nat.mul_le_mul_left (k ^ 3) hk, pow_pos (show 0 < k by omega) 2]
  have hw : (∏ p ∈ n.primeFactors, ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1))) ≤ 16 := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    split_ifs <;> norm_num
  have hPR : P ^ 3 ≤ 16 * R ^ 4 := by
    rw [hPdef, hRdef, ← Finset.prod_pow, ← Finset.prod_pow]
    calc ∏ p ∈ n.primeFactors, p ^ 3
        ≤ ∏ p ∈ n.primeFactors,
            (((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1)) * (p - 1) ^ 4) :=
          Finset.prod_le_prod hstep
      _ = (∏ p ∈ n.primeFactors, ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1))) *
            ∏ p ∈ n.primeFactors, (p - 1) ^ 4 := Finset.prod_mul_distrib
      _ ≤ 16 * ∏ p ∈ n.primeFactors, (p - 1) ^ 4 := Nat.mul_le_mul_right _ hw
  have hA : n ^ 4 * P ^ 3 ≤ (16 * Nat.totient n ^ 4 * P) * P ^ 3 := by
    calc n ^ 4 * P ^ 3 ≤ n ^ 4 * (16 * R ^ 4) := Nat.mul_le_mul_left _ hPR
      _ = 16 * (n * R) ^ 4 := by ring
      _ = 16 * (Nat.totient n * P) ^ 4 := by rw [h1]
      _ = (16 * Nat.totient n ^ 4 * P) * P ^ 3 := by ring
  have hB : n ^ 4 ≤ 16 * Nat.totient n ^ 4 * P :=
    Nat.le_of_mul_le_mul_right hA (pow_pos hPpos 3)
  have hC : n ^ 3 * n ≤ 16 * Nat.totient n ^ 4 * n := by
    calc n ^ 3 * n = n ^ 4 := by ring
      _ ≤ 16 * Nat.totient n ^ 4 * P := hB
      _ ≤ 16 * Nat.totient n ^ 4 * n := Nat.mul_le_mul_left _ hPn
  exact Nat.le_of_mul_le_mul_right hC hn

/-- `1/φ(q)² ≤ 4/(q √q)` for `q ≥ 1`. -/
theorem inv_totient_sq_le (q : ℕ) (hq : 1 ≤ q) :
    1 / (Nat.totient q : ℝ) ^ 2 ≤ 4 / ((q : ℝ) * Real.sqrt q) := by
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hb : ((q : ℝ)) ^ 3 ≤ 16 * (Nat.totient q : ℝ) ^ 4 := by
    exact_mod_cast cube_le_totient_pow_four q
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((q : ℝ) * Real.sqrt q) ^ 2 ≤ (4 * (Nat.totient q : ℝ) ^ 2) ^ 2 := by
    have : ((q : ℝ) * Real.sqrt q) ^ 2 = (q : ℝ) ^ 3 := by
      rw [mul_pow, hs]; ring
    rw [this]; nlinarith
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  linarith

/-- The telescoping step: `4/(b² b) ≤ 8/a - 8/b` when `1 ≤ a ≤ b`, `b² = a² + 1`. -/
theorem tele_step_ab (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (h : b ^ 2 = a ^ 2 + 1) :
    4 / (b ^ 2 * b) ≤ 8 / a - 8 / b := by
  have hb : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have h2 : 1 ≤ 2 * b * (b - a) := by nlinarith
  rw [div_sub_div _ _ (ne_of_gt ha0) (ne_of_gt hb), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg b), mul_le_mul_of_nonneg_right hab hb.le]

/-- The telescoping step in `x`: `4/((x+1)√(x+1)) ≤ 8/√x - 8/√(x+1)` for `x ≥ 1`. -/
theorem tele_step (x : ℝ) (hx : 1 ≤ x) :
    4 / ((x + 1) * Real.sqrt (x + 1)) ≤ 8 / Real.sqrt x - 8 / Real.sqrt (x + 1) := by
  have ha : 1 ≤ Real.sqrt x := by
    have := Real.sqrt_le_sqrt hx; rwa [Real.sqrt_one] at this
  have hab : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have h : Real.sqrt (x + 1) ^ 2 = Real.sqrt x ^ 2 + 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  have := tele_step_ab _ _ ha hab h
  rwa [Real.sq_sqrt (by linarith)] at this

/-- Partial sums of the comparison series beyond `Q`. -/
theorem tele_sum (Q : ℕ) (hQ : 1 ≤ Q) : ∀ m : ℕ,
    ∑ i ∈ Finset.range m, 4 / (((Q + 1 + i : ℕ) : ℝ) * Real.sqrt ((Q + 1 + i : ℕ) : ℝ)) ≤
      8 / Real.sqrt Q - 8 / Real.sqrt ((Q + m : ℕ) : ℝ) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hx : (1 : ℝ) ≤ ((Q + m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ Q + m by omega)
    have hs := tele_step _ hx
    have e1 : ((Q + 1 + m : ℕ) : ℝ) = ((Q + m : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((Q + (m + 1) : ℕ) : ℝ) = ((Q + m : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

/-- The comparison series is nonnegative. -/
theorem cmp_nonneg (q : ℕ) : 0 ≤ 4 / ((q : ℝ) * Real.sqrt q) := by positivity

/-- `|singTerm N q| ≤ 4/(q √q)` for every `q`. -/
theorem singTerm_abs_le_cmp (N q : ℕ) : |singTerm N q| ≤ 4 / ((q : ℝ) * Real.sqrt q) := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp [singTerm]
  exact (singTerm_abs_le N q).trans (inv_totient_sq_le q h)

/-- Partial sums of the tail of the comparison series beyond `Q ≥ 1` are at most `8/√Q`. -/
theorem cmp_tail_partial (Q : ℕ) (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if Q < i then 4 / ((i : ℝ) * Real.sqrt i) else 0) ≤
      8 / Real.sqrt Q := by
  set h : ℕ → ℝ := fun i => if Q < i then 4 / ((i : ℝ) * Real.sqrt i) else 0 with hh
  have hnn : ∀ i, 0 ≤ h i := fun i => by
    simp only [hh]; split_ifs
    · exact cmp_nonneg i
    · exact le_refl _
  calc ∑ i ∈ Finset.range n, h i ≤ ∑ i ∈ Finset.range (Q + 1 + n), h i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : n ≤ Q + 1 + n))
          (fun i _ _ => hnn i)
    _ = ∑ i ∈ Finset.range (Q + 1), h i + ∑ i ∈ Finset.range n, h (Q + 1 + i) :=
        Finset.sum_range_add _ _ _
    _ = ∑ i ∈ Finset.range n,
          4 / (((Q + 1 + i : ℕ) : ℝ) * Real.sqrt ((Q + 1 + i : ℕ) : ℝ)) := by
        have h0 : ∑ i ∈ Finset.range (Q + 1), h i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have : ¬ Q < i := by have := Finset.mem_range.mp hi; omega
          simp [hh, this]
        rw [h0, zero_add]
        apply Finset.sum_congr rfl
        intro i _
        have : Q < Q + 1 + i := by omega
        simp [hh, this]
    _ ≤ 8 / Real.sqrt Q - 8 / Real.sqrt ((Q + n : ℕ) : ℝ) := tele_sum Q hQ n
    _ ≤ 8 / Real.sqrt Q := by
        have : 0 ≤ 8 / Real.sqrt ((Q + n : ℕ) : ℝ) := by positivity
        linarith

/-- The comparison series `4/(q √q)` is summable. -/
theorem cmp_summable : Summable (fun q : ℕ => 4 / ((q : ℝ) * Real.sqrt q)) := by
  apply summable_of_sum_range_le (c := 8 / Real.sqrt 1 + 4) (fun q => cmp_nonneg q)
  intro n
  have h1 := cmp_tail_partial 1 le_rfl n
  have h2 : ∑ i ∈ Finset.range n, 4 / ((i : ℝ) * Real.sqrt i) ≤
      ∑ i ∈ Finset.range n, ((if 1 < i then 4 / ((i : ℝ) * Real.sqrt i) else 0) +
        (if i = 1 then 4 else 0)) := by
    apply Finset.sum_le_sum
    intro i _
    rcases Nat.lt_trichotomy i 1 with hi | hi | hi
    · have : i = 0 := by omega
      subst this; simp
    · subst hi; simp
    · have : i ≠ 1 := by omega
      simp [hi, this]
  rw [Finset.sum_add_distrib] at h2
  have h3 : ∑ i ∈ Finset.range n, (if i = 1 then (4 : ℝ) else 0) ≤ 4 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  push_cast at h1
  linarith

/-- Page 271, the singular series is absolutely convergent. PROVED. -/
theorem singTerm_abs_summable (N : ℕ) : Summable (fun q => |singTerm N q|) :=
  cmp_summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun q => singTerm_abs_le_cmp N q)

/-- The tail of `Σ |singTerm N q|` beyond `Q ≥ 1` is at most `8/√Q`. PROVED. -/
theorem singTerm_tail_le (N Q : ℕ) (hQ : 1 ≤ Q) :
    ∑' q : ℕ, (if Q < q then |singTerm N q| else 0) ≤ 8 / Real.sqrt Q := by
  apply Real.tsum_le_of_sum_range_le
  · intro q; split_ifs
    · exact abs_nonneg _
    · exact le_refl _
  intro n
  refine le_trans (Finset.sum_le_sum fun q _ => ?_) (cmp_tail_partial Q hQ n)
  split_ifs
  · exact singTerm_abs_le_cmp N q
  · exact le_refl _

/-- Page 271, the tail of the singular series beyond `Q₁ = L^d` is `O(L⁻¹)` for `d ≥ 4`,
with the series absolutely convergent. PROVED. -/
theorem singSeriesTail_proof : SingSeriesTail := by
  refine ⟨4, by norm_num, fun d hd => ⟨16, 3, fun N _ hN => ?_⟩⟩
  refine ⟨singTerm_abs_summable N, ?_⟩
  set L := Real.log N with hLdef
  have hN3 : (3 : ℝ) ≤ N := hN
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL4 : L ^ (4 : ℝ) ≤ L ^ d := Real.rpow_le_rpow_of_exponent_le hL hd
  have hL4' : L ^ (4 : ℝ) = L ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hL4'] at hL4
  have hLd1 : 1 ≤ L ^ d := le_trans (one_le_pow₀ hL) hL4
  set Q := ⌊L ^ d⌋₊ with hQdef
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hLd1)
  have hQlt : L ^ d < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hQ1' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hQbig : L ^ 4 / 4 ≤ (Q : ℝ) := by nlinarith
  have hsq : L ^ 2 / 2 ≤ Real.sqrt Q := by
    have := Real.sqrt_le_sqrt (show (L ^ 2 / 2) ^ 2 ≤ (Q : ℝ) by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  refine le_trans (singTerm_tail_le N Q hQ1) ?_
  have hpos : 0 < L ^ 2 / 2 := by positivity
  calc 8 / Real.sqrt Q ≤ 8 / (L ^ 2 / 2) := div_le_div_of_nonneg_left (by norm_num) hpos hsq
    _ = 16 / L ^ 2 := by field_simp; ring
    _ ≤ 16 / L := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        nlinarith

end LeanLab.Zhan1991
