import LeanLab.HeathBrownPuchta.C2Inputs

/-!
# Heath-Brown and Puchta 2002: `s(x) ≤ C₀⁻¹ m/φ(m)` and the Liu, Liu and Wang input

Lab proof, unit U-1288, PC run 20261020T2203Z-17931. AI wrote the Lean code. P0012, arXiv
math/0201299 v2, Section 5, the display after (40):
`s(x) ≤ Σ_{d ∣ m} k(d) = h(m) = Π_{p ∣ m, p > 2} (p-1)/(p-2)
  ≤ Π_{p > 2} (p-1)²/(p(p-2)) · Π_{p ∣ m} p/(p-1) = C₀⁻¹ m/φ(m)`, with `m = Π_{e ≤ x} (2^e - 1)`,
and "m/φ(m) ≤ e^γ log x for x ≥ 9, as shown by Liu, Liu and Wang [13; (3.9)]".

PROVED unconditional:
* `s_le_h`: `Σ_{e ≤ n} κ(e) ≤ h(m_n)`.
* `h_eq_twin_mul`: `h(m) = Π_{p ∣ m} (1 + 1/(p(p-2))) · m/φ(m)` for odd `m ≠ 0`.
* `twin_prod_le`: every finite product of `1 + 1/(p(p-2))` over odd primes is `≤ 1.52744`,
  a partial product bound for `C₀⁻¹`; Python `C₀⁻¹ = 1.51478`.
* `exp_gamma_lt`: `e^γ < 1.79503`, from Mathlib's `γ < H_64 - log 64`.
* `s_le_mphi`: `Σ_{e ≤ n} κ(e) ≤ 1.52744 · m_n/φ(m_n)`.
* `twin_gamma_const`: `1.52744 · 1.79503 ≤ 2.742`.
CONDITIONAL ON `LLW`, the Liu, Liu and Wang bound `m_n/φ(m_n) ≤ e^γ log n` for `n ≥ 9`:
`llw_of_LLW`, `C2_le_of_mphi`, `c2Inputs_of_mphi`, `theorem1_mphi`, `theorem2_mphi`, and the
paper's own `M = 20` version `C2_le_at_20`. Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta.SReduction

open Finset LeanLab.Linnik LeanLab.HeathBrownPuchta.Lemma8Const LeanLab.HeathBrownPuchta.C2Inputs
  LeanLab.HeathBrownPuchta.C2Discharge

/-- `m = Π_{e ≤ n} (2^e - 1)`, the paper's `m` at `x = n`. -/
def mprod (n : ℕ) : ℕ := ∏ e ∈ Icc 1 n, (2 ^ e - 1)

/-- The Liu, Liu and Wang input, cited: `m/φ(m) ≤ e^γ log x` for `x ≥ 9`, at integer `x`. -/
def LLW : Prop :=
  ∀ n : ℕ, 9 ≤ n →
    (mprod n : ℝ) / (Nat.totient (mprod n) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * Real.log n

theorem mprod_ne_zero (n : ℕ) : mprod n ≠ 0 := by
  unfold mprod
  rw [Finset.prod_ne_zero_iff]
  intro e he
  exact pow_sub_one_ne_zero e (by simp at he; omega)

theorem mprod_odd (n : ℕ) : ¬ 2 ∣ mprod n := by
  unfold mprod
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨e, he, hd⟩
  simp only [Finset.mem_Icc] at he
  have h1 := Nat.one_le_two_pow (n := e)
  have : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  omega

theorem dvd_mprod {n e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ n) : 2 ^ e - 1 ∣ mprod n :=
  Finset.dvd_prod_of_mem _ (by simp [h1, h2])

/-! ## `s(x) ≤ h(m)` -/

/-- `s(n) = Σ_{e ≤ n} κ(e) = Σ_{ε(d) ≤ n} k(d) ≤ Σ_{d ∣ m} k(d) = h(m)`. -/
theorem s_le_h (n : ℕ) : ∑ e ∈ range n, kappaTrue (e + 1) ≤ (h (mprod n) : ℝ) := by
  classical
  have hdisj : ((range n : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun e => S (e + 1)) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hda hdb
    have ea := (Finset.mem_filter.1 hda).2
    have eb := (Finset.mem_filter.1 hdb).2
    exact hab (by omega)
  have e1 : ∑ e ∈ range n, kappaTrue (e + 1) = ∑ d ∈ (range n).biUnion (fun e => S (e + 1)), (k d : ℝ) := by
    rw [Finset.sum_biUnion hdisj]
    rfl
  have hsub : (range n).biUnion (fun e => S (e + 1)) ⊆ (mprod n).divisors := by
    intro d hd
    rw [Finset.mem_biUnion] at hd
    obtain ⟨e, he, hdS⟩ := hd
    simp only [Finset.mem_range] at he
    simp only [S, Finset.mem_filter, Nat.mem_divisors] at hdS
    rw [Nat.mem_divisors]
    exact ⟨hdS.1.1.trans (dvd_mprod (by omega) (by omega)), mprod_ne_zero n⟩
  rw [e1, h_eq_sum_k _ (mprod_ne_zero n), Rat.cast_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by exact_mod_cast k_nonneg d)

/-! ## `h(m) = Π (1 + 1/(p(p-2))) · m/φ(m)` for odd `m` -/

/-- The factor `(p-1)²/(p(p-2)) = 1 + 1/(p(p-2))` of `C₀⁻¹`. -/
noncomputable def tw (p : ℕ) : ℝ := 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))

theorem h_eq_twin_mul (m : ℕ) (hm : m ≠ 0) (hodd : ¬ 2 ∣ m) :
    (h m : ℝ) = (∏ p ∈ m.primeFactors, tw p) * ((m : ℝ) / (Nat.totient m : ℝ)) := by
  have hpf : ∀ p ∈ m.primeFactors, p ≠ 2 := fun p hp h2 =>
    hodd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hfil : m.primeFactors.filter (· ≠ 2) = m.primeFactors := Finset.filter_true_of_mem hpf
  have htot : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors m)
    push_cast at this
    exact this
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hp3 : ∀ p ∈ m.primeFactors, (3 : ℝ) ≤ p := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have := hpf p hp
    exact_mod_cast (show 3 ≤ p by omega)
  have hne : ∀ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := fun p hp => by
    have := hp3 p hp
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [htot, h, hfil, Rat.cast_prod]
  have hquot : (m : ℝ) / (m * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)) =
      ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [div_mul_cancel_left₀ hm', Finset.prod_inv_distrib]
  rw [hquot, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h3 := hp3 p hp
  have a : (p : ℝ) - 2 ≠ 0 := by linarith
  have b : (p : ℝ) ≠ 0 := by linarith
  have c : (p : ℝ) - 1 ≠ 0 := by linarith
  have d : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [d, tw]
  push_cast
  field_simp
  ring

/-! ## Partial products of `C₀⁻¹` -/

theorem tw_ge_one (p : ℕ) (hp : 3 ≤ p) : 1 ≤ tw p := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold tw
  have : 0 < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  have := one_div_pos.2 this
  linarith

theorem tw_le (p : ℕ) (hp : 3 ≤ p) : tw p - 1 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold tw
  have e : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    rw [div_sub_div _ _ (by linarith) (by linarith)]
    congr 1; ring
  rw [e, add_sub_cancel_left]
  apply one_div_le_one_div_of_le (by nlinarith)
  nlinarith

/-- Telescoping: the sum of `1/(j-2) - 1/(j-1)` over any finite set of `j ≥ 101` is `≤ 1/99`. -/
theorem tele_le (U : Finset ℕ) (hU : ∀ j ∈ U, 101 ≤ j) :
    ∑ j ∈ U, (1 / ((j : ℝ) - 2) - 1 / ((j : ℝ) - 1)) ≤ 1 / 99 := by
  set L := U.sup id + 1
  have hnn : ∀ j : ℕ, 101 ≤ j → 0 ≤ 1 / ((j : ℝ) - 2) - 1 / ((j : ℝ) - 1) := fun j hj => by
    have : (101 : ℝ) ≤ j := by exact_mod_cast hj
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by linarith); linarith
  have hsub : U ⊆ Finset.Ico 101 (101 + L) := by
    intro j hj
    have := hU j hj
    have : j ≤ U.sup id := Finset.le_sup (f := id) hj
    simp only [Finset.mem_Ico]; omega
  calc ∑ j ∈ U, (1 / ((j : ℝ) - 2) - 1 / ((j : ℝ) - 1))
      ≤ ∑ j ∈ Finset.Ico 101 (101 + L), (1 / ((j : ℝ) - 2) - 1 / ((j : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j (Finset.mem_Ico.1 hj).1)
    _ = ∑ i ∈ range L, (1 / ((i : ℝ) + 99) - 1 / (((i + 1 : ℕ) : ℝ) + 99)) := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring_nf
    _ = 1 / 99 - 1 / ((L : ℝ) + 99) := by
        rw [Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 99))]
        simp
    _ ≤ 1 / 99 := by
        have : 0 ≤ 1 / ((L : ℝ) + 99) := by positivity
        linarith

/-- The odd primes below `100`. -/
def smallPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

theorem mem_smallPrimes (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h : p ≤ 100) : p ∈ smallPrimes := by
  interval_cases p <;> first | decide | exact absurd rfl h2 | (norm_num at hp)

theorem smallPrimes_ge (p : ℕ) (hp : p ∈ smallPrimes) : 3 ≤ p := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  omega

theorem smallPrimes_prod : ∏ p ∈ smallPrimes, tw p < 15120 / 10000 := by
  simp only [smallPrimes, tw]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

/-- Every finite product of `1 + 1/(p(p-2))` over odd primes is below `1.52744`; these are the
partial products of `C₀⁻¹ = Π_{p > 2} (p-1)²/(p(p-2))`. -/
theorem twin_prod_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ T, tw p ≤ 152744 / 100000 := by
  classical
  have h3 : ∀ p ∈ T, 3 ≤ p := fun p hp => by
    have := (hT p hp).1.two_le; have := (hT p hp).2; omega
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun p => p ≤ 100)]
  have hsmall : ∏ p ∈ T.filter (fun p => p ≤ 100), tw p ≤ ∏ p ∈ smallPrimes, tw p := by
    have hsub : T.filter (fun p => p ≤ 100) ⊆ smallPrimes := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact mem_smallPrimes p (hT p hp.1).1 (hT p hp.1).2 hp.2
    rw [← Finset.prod_sdiff hsub]
    have hA : 0 ≤ ∏ p ∈ T.filter (fun p => p ≤ 100), tw p := Finset.prod_nonneg fun p hp => by
      have := tw_ge_one p (smallPrimes_ge p (hsub hp)); linarith
    have hB : 1 ≤ ∏ p ∈ smallPrimes \ T.filter (fun p => p ≤ 100), tw p := by
      have := Finset.prod_le_prod₀ (s := smallPrimes \ T.filter (fun p => p ≤ 100))
        (f := fun _ => (1 : ℝ)) (g := tw) (fun _ _ => zero_le_one)
        (fun p hp => tw_ge_one p (smallPrimes_ge p (Finset.mem_sdiff.1 hp).1))
      simpa using this
    nlinarith
  have hbig : ∏ p ∈ T.filter (fun p => ¬ p ≤ 100), tw p ≤ 99 / 98 := by
    set U := T.filter (fun p => ¬ p ≤ 100)
    have hU : ∀ j ∈ U, 101 ≤ j := fun j hj => by
      have := (Finset.mem_filter.1 hj).2; omega
    have hU3 : ∀ j ∈ U, 3 ≤ j := fun j hj => by have := hU j hj; omega
    have hexp : ∏ p ∈ U, tw p ≤ Real.exp (∑ p ∈ U, (tw p - 1)) := by
      rw [Real.exp_sum]
      apply Finset.prod_le_prod₀ (fun p hp => by have := tw_ge_one p (hU3 p hp); linarith)
      intro p _
      have := Real.add_one_le_exp (tw p - 1)
      linarith
    have hsum : ∑ p ∈ U, (tw p - 1) ≤ 1 / 99 :=
      (Finset.sum_le_sum fun p hp => tw_le p (hU3 p hp)).trans (tele_le U hU)
    have hx : Real.exp (1 / 99) < 1 / (1 - 1 / 99) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    have : Real.exp (∑ p ∈ U, (tw p - 1)) ≤ Real.exp (1 / 99) := Real.exp_le_exp.2 hsum
    have e : (1 : ℝ) / (1 - 1 / 99) = 99 / 98 := by norm_num
    linarith
  have hs := smallPrimes_prod
  have hnn : 0 ≤ ∏ p ∈ T.filter (fun p => ¬ p ≤ 100), tw p :=
    Finset.prod_nonneg fun p hp => by
      have := tw_ge_one p (h3 p (Finset.mem_filter.1 hp).1); linarith
  have hnn2 : 0 ≤ ∏ p ∈ smallPrimes, tw p :=
    Finset.prod_nonneg fun p hp => by have := tw_ge_one p (smallPrimes_ge p hp); linarith
  calc (∏ p ∈ T.filter (fun p => p ≤ 100), tw p) * ∏ p ∈ T.filter (fun p => ¬ p ≤ 100), tw p
      ≤ (∏ p ∈ smallPrimes, tw p) * (99 / 98) := mul_le_mul hsmall hbig hnn hnn2
    _ ≤ (15120 / 10000) * (99 / 98) := by gcongr
    _ ≤ 152744 / 100000 := by norm_num

/-! ## `e^γ < 1.79503` -/

theorem harmonic_64 : (harmonic 64 : ℝ) < 474389091 / 100000000 := by
  have : harmonic 64 < 474389091 / 100000000 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h := (Rat.cast_lt (K := ℝ)).2 this
  push_cast at h
  exact h

theorem gamma_lt : Real.eulerMascheroniConstant < 58501 / 100000 := by
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have h2 : Real.eulerMascheroniSeq' 64 = (harmonic 64 : ℝ) - Real.log 64 := by
    simp [Real.eulerMascheroniSeq']
  have h3 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h4 := Real.log_two_gt_d9
  have h5 := harmonic_64
  linarith

theorem exp_gamma_lt : Real.exp Real.eulerMascheroniConstant < 179503 / 100000 := by
  have h1 : Real.exp Real.eulerMascheroniConstant < Real.exp (58501 / 100000) := Real.exp_lt_exp.2 gamma_lt
  have h2 := Real.exp_bound' (x := 58501 / 100000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  have h3 : (∑ m ∈ Finset.range 12, ((58501 : ℝ) / 100000) ^ m / m.factorial) +
      (58501 / 100000) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12) < 179503 / 100000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  push_cast at h2 h3
  linarith

theorem twin_gamma_const : (152744 / 100000 : ℝ) * (179503 / 100000) ≤ 2742 / 1000 := by norm_num

/-! ## The reduction -/

/-- `s(n) ≤ 1.52744 · m/φ(m)`, the paper's `s(x) ≤ C₀⁻¹ m/φ(m)` with the partial product bound. -/
theorem s_le_mphi (n : ℕ) :
    ∑ e ∈ range n, kappaTrue (e + 1) ≤
      152744 / 100000 * ((mprod n : ℝ) / (Nat.totient (mprod n) : ℝ)) := by
  refine (s_le_h n).trans ?_
  rw [h_eq_twin_mul _ (mprod_ne_zero n) (mprod_odd n)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply twin_prod_le
  intro p hp
  refine ⟨Nat.prime_of_mem_primeFactors hp, fun h2 => mprod_odd n ?_⟩
  exact h2 ▸ Nat.dvd_of_mem_primeFactors hp

/-- `s(n) ≤ 2.742 log n` for `n ≥ 9`. CONDITIONAL ON `LLW`. -/
theorem llw_of_LLW (hL : LLW) (n : ℕ) (hn : 9 ≤ n) :
    ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2742 / 1000 * Real.log n := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have h1 := s_le_mphi n
  have h2 := hL n hn
  have h3 := exp_gamma_lt
  have h4 : (152744 / 100000 : ℝ) * ((mprod n : ℝ) / (Nat.totient (mprod n) : ℝ)) ≤
      152744 / 100000 * (Real.exp Real.eulerMascheroniConstant * Real.log n) := by gcongr
  have h5 : Real.exp Real.eulerMascheroniConstant * Real.log n ≤ 179503 / 100000 * Real.log n :=
    mul_le_mul_of_nonneg_right h3.le hlog
  have h6 := mul_le_mul_of_nonneg_right twin_gamma_const hlog
  nlinarith

/-- The `llw` input of `C2Inputs.lean`, `s(n) ≤ 2.744 log n` for `n ≥ 24`. CONDITIONAL ON `LLW`. -/
theorem llw_input (hL : LLW) (n : ℕ) (hn : 24 ≤ n) :
    ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2744 / 1000 * Real.log n := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have := llw_of_LLW hL n (by omega)
  nlinarith

/-- `C₂ ≤ 2.2141`. CONDITIONAL ON `LLW` alone. -/
theorem C2_le_of_mphi (hL : LLW) : C2 ≤ 22141 / 10000 := C2_le_of_LLW (llw_input hL)

/-- `C2Inputs` from `LLW` alone. CONDITIONAL ON `LLW`. -/
theorem c2Inputs_of_mphi (hL : LLW) : C2Inputs := c2Inputs_of_LLW (llw_input hL)

/-- Theorem 1, `K = 13`. CONDITIONAL ON `LLW` and the inputs of `theorem1_conditional` other than
`C₂ ≤ 2.2141`. -/
theorem theorem1_mphi (hL : LLW) (E : ℝ) (hE : 109 / 154 < E)
    (I : ∀ w : ℝ, 0 < w → InputsC2Free 13 (863665 / 1000000) (263 / 308 + 3 * w) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 13 N) :
    AllLargeEven (LinnikExact 13) :=
  theorem1_lemma8 (c2Inputs_of_mphi hL) E hE I circle

/-- Theorem 2, `K = 7` on GRH. CONDITIONAL ON `LLW` and the inputs of `theorem2_conditional`
other than `C₂ ≤ 2.2141`. -/
theorem theorem2_mphi (hL : LLW) (E : ℝ) (hE : 1 / 2 < E)
    (I : ∀ w : ℝ, 0 < w → InputsC2Free 7 (722428 / 1000000) (3 / 4) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 7 N) :
    AllLargeEven (LinnikExact 7) :=
  theorem2_lemma8 (c2Inputs_of_mphi hL) E hE I circle

/-! ## The paper's `M = 20` with the proved tail coefficient `2.742` -/

/-- `log 20 < 2.99575`, from `log x ≤ x - 1` at `x = 20 / e³`. -/
theorem log20_lt : Real.log 20 < 299575 / 100000 := by
  have h3 := exp3_gt
  have hp : 0 < Real.exp 3 := Real.exp_pos 3
  have hx : 0 < 20 / Real.exp 3 := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by norm_num) hp.ne', Real.log_exp] at hl
  have : 20 / Real.exp 3 < 20 / (2008553691 / 100000000) := by gcongr
  have : (20 : ℝ) / (2008553691 / 100000000) < 99575 / 100000 := by norm_num
  linarith

/-- `C₂ ≤ 2.2141` by (41) at the paper's own `M = 20`, with tail coefficient `2.742` in place of
`2.744`: `1.6659263 + 2.742 · (1 + 2.99575)/20 = 2.21374`. CONDITIONAL ON `LLW`. This settles the
U-1277 rounding QUESTION: at `M = 20` the printed `2.744` gives `2.2141407`, but the paper's own
ingredients `C₀⁻¹ e^γ ≤ 2.742` give `C₂ ≤ 2.2138`. -/
theorem C2_le_at_20 (hL : LLW) : C2 ≤ 22141 / 10000 := by
  rw [grouping]
  have hS : ∀ n, 20 ≤ n → ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2742 / 1000 * Real.log n :=
    fun n hn => llw_of_LLW hL n (by omega)
  have h := tsum_le_P kappaTrue kappaTrue_nonneg (by norm_num) (by norm_num) hS
  have hP : P kappaTrue (2742 / 1000) 20 =
      (finitePart 20 : ℝ) + 2742 / 1000 * (1 + Real.log 20) / 20 := by
    unfold P finitePart
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [kappaTrue_eq_kappa (e + 1) (by omega)]
  have h1 : (finitePart 20 : ℝ) < ((16659263 / 10000000 : ℚ) : ℝ) := by
    exact_mod_cast finitePart_20.2
  have h2 := log20_lt
  push_cast at h1
  linarith

/-- Vacuity check for `LLW`: its right side at the first case `n = 9` exceeds `3`, while Python
gives `m/φ(m) = 2.4544` there, so `LLW` is not contradicted at `n = 9`; Python also confirms
`m/φ(m) ≤ e^γ log n` for every `n` from `9` to `40`. Lean part: `e^γ log 9 > 3`. -/
theorem LLW_rhs_9 : 3 < Real.exp Real.eulerMascheroniConstant * Real.log 9 := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have he : Real.exp (1 / 2) < Real.exp Real.eulerMascheroniConstant := Real.exp_lt_exp.2 hg
  have h12 := Real.add_one_le_exp (1 / 2 : ℝ)
  have hl : 2 < Real.log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  nlinarith

end LeanLab.HeathBrownPuchta.SReduction
