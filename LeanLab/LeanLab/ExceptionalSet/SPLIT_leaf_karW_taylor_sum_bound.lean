/-
Split of `leaf_karW_taylor_sum_bound` of `LeanLab.ExceptionalSet.SPLIT_leaf_W_bound`, the analytic
core of the case `n ≥ n0` of Theorem 1 of A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971),
p. 245-248.

Pieces.
* `karW_sum_T_lower`, `karW_sum_T_upper`: `c0² n²/4 ≤ s_1 + ... + s_r ≤ n(n+1)/2`, p. 245 line -4.
* `karW_choice_l`: the integer `l ≥ 1` of p. 245,
  `n(n+1)(1-1/n)^l ≤ ρ(s_1+...+s_r) < n(n+1)(1-1/n)^{l-1}`.
* `karW_l_le`: `l ≤ nL + 1`, `L = log(8/(ρ c0²))`, the bound `l < c5 n` of p. 245 and p. 248.
* `karW_k_bounds`: `k = nl + [n(n+1)/4 + 1]` satisfies `nl ≤ k`, `n²/4 ≤ k`, `k ≤ n²(L + 1/2)`, p. 248 top.
* `karW_exponent_compare`: `4 e ≤ ρ(s_1+...+s_r)/(8k²)` for the leaf's exponent `e`.
* `karW_absorb_B1`: the factor `B_1 = B^{1/(4k²)}` of display (8) is at most `C1 P^{E/n²}`.
* `leaf_karW_display8`: display (8), p. 245-247, with an absolute constant in front. LEAF.
* `leaf_karW_taylor_sum_bound_split`: the assembly, the exact type of the target leaf.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_W_bound

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Step i: the sum of the `s_j` -/

private theorem karW_card_sq_le (T : Finset ℕ) : T.card * T.card ≤ 2 * (∑ s ∈ T, s) + T.card := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert m S hlt ih =>
    have hm : m ∉ S := fun h => lt_irrefl _ (hlt m h)
    rw [Finset.card_insert_of_notMem hm, Finset.sum_insert hm]
    have hS : S.card ≤ m := by
      have hsub : S ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
      simpa using Finset.card_le_card hsub
    nlinarith

/-- Karacuba p. 245 line -4: from the definition of `s_1, ..., s_r`, distinct in `[2, n]` with
`r ≥ c0 n`, one has `s_1 + ... + s_r ≥ 0.25 c0² n²`. -/
theorem karW_sum_T_lower {c0 : ℝ} {n : ℕ} {T : Finset ℕ} (hc0 : 0 < c0)
    (hT : T ⊆ Finset.Icc 2 n) (hcard : c0 * n ≤ T.card) :
    c0 ^ 2 * (n : ℝ) ^ 2 / 4 ≤ ∑ s ∈ T, (s : ℝ) := by
  have h1 := karW_card_sq_le T
  have h2 : T.card • 2 ≤ ∑ s ∈ T, s :=
    Finset.card_nsmul_le_sum T (fun s => s) 2 (fun s hs => (Finset.mem_Icc.1 (hT hs)).1)
  rw [smul_eq_mul] at h2
  have h1' : ((T.card * T.card : ℕ) : ℝ) ≤ ((2 * (∑ s ∈ T, s) + T.card : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((T.card * 2 : ℕ) : ℝ) ≤ ((∑ s ∈ T, s : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  have hn0 : (0 : ℝ) ≤ c0 * n := by positivity
  have hsq : (c0 * n) ^ 2 ≤ (T.card : ℝ) ^ 2 := pow_le_pow_left₀ hn0 hcard 2
  nlinarith

/-- `s_1 + ... + s_r ≤ 2 + ... + n ≤ n(n+1)/2`, which with `ρ ≤ 1/3` makes `ρ(s_1+...+s_r) <
n(n+1)`, so that the `l` of p. 245 is positive. -/
theorem karW_sum_T_upper {n : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 2 n) :
    2 * ∑ s ∈ T, (s : ℝ) ≤ (n : ℝ) * (n + 1) := by
  have hsub : T ⊆ Finset.range (n + 1) := fun x hx => by
    have := Finset.mem_Icc.1 (hT hx); exact Finset.mem_range.2 (by omega)
  have h := Finset.sum_le_sum_of_subset (f := fun s : ℕ => s) hsub
  have h2 := Finset.sum_range_id_mul_two (n + 1)
  simp only [Nat.add_sub_cancel] at h2
  have : 2 * ∑ s ∈ T, s ≤ n * (n + 1) := by nlinarith
  have h' : ((2 * ∑ s ∈ T, s : ℕ) : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  exact h'

/-! ### Step i: the choice of `l` and `k` -/

/-- Karacuba p. 245: "define the integer `l` by the conditions
`n(n+1)(1-1/n)^l ≤ ρ(s_1+...+s_r) < n(n+1)(1-1/n)^{l-1}`", here for any `0 < x < A`,
`0 ≤ q < 1`. -/
theorem karW_choice_l {A x q : ℝ} (hx : 0 < x) (hxA : x < A) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ l : ℕ, 1 ≤ l ∧ A * q ^ l ≤ x ∧ x < A * q ^ (l - 1) := by
  classical
  have hA : 0 < A := hx.trans hxA
  have hex : ∃ m : ℕ, A * q ^ m ≤ x := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hx hA) hq1
    refine ⟨m, ?_⟩
    rw [lt_div_iff₀ hA] at hm
    linarith [mul_comm A (q ^ m)]
  set l := Nat.find hex with hl
  have hspec : A * q ^ l ≤ x := Nat.find_spec hex
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, pow_zero, mul_one] at hspec
    linarith
  refine ⟨l, Nat.one_le_iff_ne_zero.2 hl0, hspec, ?_⟩
  have hmin := Nat.find_min hex (show l - 1 < l by omega)
  exact lt_of_not_ge hmin

/-- Karacuba p. 245 and p. 248: `l < c5 n`. Here in the form `l ≤ n L + 1`,
`L = log(8/(ρ c0²))`: from `ρ(s_1+...+s_r) < n(n+1)(1-1/n)^{l-1}` and
`ρ(s_1+...+s_r) ≥ 0.25 ρ c0² n²` one gets `(1-1/n)^{l-1} > ρ c0²/8`, and `log(1-1/n) ≤ -1/n`. -/
theorem karW_l_le {ρ c0 σ : ℝ} {n l : ℕ} (hρ : 0 < ρ) (hc0 : 0 < c0) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (hσ : c0 ^ 2 * (n : ℝ) ^ 2 / 4 ≤ σ)
    (hlt : ρ * σ < ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ (l - 1)) :
    (l : ℝ) ≤ n * Real.log (8 / (ρ * c0 ^ 2)) + 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set q : ℝ := 1 - 1 / (n : ℝ) with hq
  have hq0 : 0 < q := by
    rw [hq]; have : 1 / (n : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  set y : ℝ := ρ * c0 ^ 2 / 8 with hy
  have hypos : 0 < y := by positivity
  -- y < q^(l-1)
  have hyq : y < q ^ (l - 1) := by
    have hnn : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * (n + 1) := by push_cast; ring
    rw [hnn] at hlt
    have h1 : ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) ≤ ρ * σ := mul_le_mul_of_nonneg_left hσ hρ.le
    have h2 : y * ((n : ℝ) * (n + 1)) ≤ ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) := by
      rw [hy]
      have : (0 : ℝ) ≤ ρ * c0 ^ 2 := by positivity
      have hnn2 : (n : ℝ) * (n + 1) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hnn2 this]
    have hpos : (0 : ℝ) < (n : ℝ) * (n + 1) := by positivity
    by_contra hcon
    push_neg at hcon
    have : (n : ℝ) * (n + 1) * q ^ (l - 1) ≤ (n : ℝ) * (n + 1) * y :=
      mul_le_mul_of_nonneg_left hcon hpos.le
    nlinarith
  have hlog : Real.log y < ((l - 1 : ℕ) : ℝ) * Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_lt_log hypos hyq
  have hlq : Real.log q ≤ -(1 / (n : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hq0
    rw [hq] at this ⊢; linarith
  have hL : Real.log (8 / (ρ * c0 ^ 2)) = -Real.log y := by
    rw [hy, ← Real.log_inv, inv_div]
  rw [hL]
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl]; simp
  rw [hcast] at hlog
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h3 : ((l : ℝ) - 1) * Real.log q ≤ ((l : ℝ) - 1) * (-(1 / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hlq hl1
  have h4 : ((l : ℝ) - 1) * (-(1 / (n : ℝ))) * n = -((l : ℝ) - 1) := by
    field_simp
  nlinarith

/-- Karacuba p. 248 top: `n(n+1)/4 < k ≤ nl + n(n+1)/4 + 1`, used in the form
`n l ≤ k`, `n²/4 ≤ k` and, with `l ≤ nL + 1`, `n ≥ 12`, `k ≤ n²(L + 1/2)`. -/
theorem karW_k_bounds {L : ℝ} {n l : ℕ} (hn : 12 ≤ n) (hL : 0 ≤ L)
    (hl : (l : ℝ) ≤ n * L + 1) :
    (((n * l : ℕ) : ℝ) ≤ ((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ∧
    (n : ℝ) ^ 2 / 4 ≤ ((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) ∧
    ((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 * (L + 1 / 2) := by
  set x : ℝ := ((n * (n + 1) : ℕ) : ℝ) / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxe : x = (n : ℝ) * (n + 1) / 4 := by rw [hx]; push_cast; ring
  have hfl : ⌊x + 1⌋₊ = ⌊x⌋₊ + 1 := Nat.floor_add_one hx0
  have hlo : x < ((⌊x + 1⌋₊ : ℕ) : ℝ) := by
    rw [hfl]; push_cast; exact Nat.lt_floor_add_one x
  have hhi : ((⌊x + 1⌋₊ : ℕ) : ℝ) ≤ x + 1 := Nat.floor_le (by linarith)
  have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · push_cast; linarith [(Nat.cast_nonneg ⌊x + 1⌋₊ : (0 : ℝ) ≤ _)]
  · push_cast
    have : (n : ℝ) ^ 2 / 4 ≤ x := by rw [hxe]; nlinarith
    have : (0 : ℝ) ≤ n * l := by positivity
    linarith
  · push_cast
    have h1 : (n : ℝ) * l ≤ n * (n * L + 1) := mul_le_mul_of_nonneg_left hl (by positivity)
    have h2 : (n : ℝ) + n * (n + 1) / 4 + 1 ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
    nlinarith

/-! ### Step v: the exponent comparison -/

/-- The "simple computations" of p. 248 for the power of `P`: with `s_1+...+s_r ≥ c0² n²/4` and
`k ≤ n²(L+1/2)`, `ρ(s_1+...+s_r)/(8k²) ≥ 4 ρ c0²/(32 n² (4+L²)²)`; the factor `4` is the room
used to absorb `B_1`. -/
theorem karW_exponent_compare {ρ c0 σ L k : ℝ} {n : ℕ} (hρ : 0 < ρ) (hc0 : 0 < c0) (hn : 1 ≤ n)
    (hL : 0 ≤ L) (hσ : c0 ^ 2 * (n : ℝ) ^ 2 / 4 ≤ σ) (hk0 : 0 < k)
    (hk : k ≤ (n : ℝ) ^ 2 * (L + 1 / 2)) :
    4 * (ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)) ≤ ρ * σ / (8 * k ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < 32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2 := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
  have hk2 : k ^ 2 ≤ ((n : ℝ) ^ 2 * (L + 1 / 2)) ^ 2 := pow_le_pow_left₀ hk0.le hk 2
  have hLL : (2 * L + 1) ^ 2 ≤ (4 + L ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by nlinarith [sq_nonneg (L - 1)]) 2
  have hA : (0 : ℝ) ≤ ρ * c0 ^ 2 := by positivity
  have e1 : 4 * (ρ * c0 ^ 2) * (8 * k ^ 2) ≤ 4 * (ρ * c0 ^ 2) * (8 * ((n : ℝ) ^ 2 * (L + 1 / 2)) ^ 2) := by
    gcongr
  have e2 : 4 * (ρ * c0 ^ 2) * (8 * ((n : ℝ) ^ 2 * (L + 1 / 2)) ^ 2)
      = 8 * (ρ * c0 ^ 2) * (n : ℝ) ^ 4 * (2 * L + 1) ^ 2 := by ring
  have e3 : 8 * (ρ * c0 ^ 2) * (n : ℝ) ^ 4 * (2 * L + 1) ^ 2
      ≤ 8 * (ρ * c0 ^ 2) * (n : ℝ) ^ 4 * (4 + L ^ 2) ^ 2 := by gcongr
  have e4 : 8 * (ρ * c0 ^ 2) * (n : ℝ) ^ 4 * (4 + L ^ 2) ^ 2
      = ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) * (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2) := by ring
  have e5 : ρ * (c0 ^ 2 * (n : ℝ) ^ 2 / 4) * (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)
      ≤ ρ * σ * (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2) := by gcongr
  linarith

/-- The "simple computations" of p. 248 for the constant of display (8):
`B_1 = B^{1/(4k²)}`, `B = (30k²)^n (9n)^n (20n)^{n(n+1)l} (log P)^n`, is at most `C1 P^{E/n²}` for
any fixed `E > 0`, because `k ≥ nl`, `k ≥ n²/4` and `k ≤ K0 n²` make the first three factors
bounded after the `4k²`-th root, and `(log P)^{n/(4k²)}` is at most a constant times
`P^{E/n²}`. -/
theorem karW_absorb_B1 (K0 E : ℝ) (hK0 : 0 < K0) (hE : 0 < E) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (n l k : ℕ) (P : ℝ), 12 ≤ n → 1 ≤ l → ((n * l : ℕ) : ℝ) ≤ k →
      (n : ℝ) ^ 2 / 4 ≤ k → (k : ℝ) ≤ K0 * (n : ℝ) ^ 2 → 1 < P →
      ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
        (Real.log P) ^ n) ^ (1 / (4 * (k : ℝ) ^ 2)) ≤ C1 * P ^ (E / (n : ℝ) ^ 2) := by
  set a := Real.log (30 * K0 ^ 2) with ha
  set δ := E / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set c := |1 + Real.log δ| with hc
  set A := |a| + 4 + 1 + 40 + c with hA
  refine ⟨Real.exp A, Real.exp_pos A, ?_⟩
  intro n l k P hn hl hnl hk4 hkK hP
  set N : ℝ := (n : ℝ) with hN
  set K : ℝ := (k : ℝ) with hK
  have hN12 : (12 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hk4
  have hPpos : 0 < P := by linarith
  set u := Real.log P with hu
  have hupos : 0 < u := Real.log_pos hP
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hnl' : N * l ≤ K := by rw [hN, hK]; push_cast at hnl; exact hnl
  -- positivity of the factors
  have f1 : 0 < 30 * K ^ 2 := by positivity
  have f2 : 0 < 9 * N := by positivity
  have f3 : 0 < 20 * N := by positivity
  have hBpos : 0 < (30 * K ^ 2) ^ n * (9 * N) ^ n * (20 * N) ^ (n * (n + 1) * l) * u ^ n := by
    positivity
  rw [Real.rpow_def_of_pos hBpos, Real.rpow_def_of_pos hPpos, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hlogB : Real.log ((30 * K ^ 2) ^ n * (9 * N) ^ n * (20 * N) ^ (n * (n + 1) * l) * u ^ n)
      = N * Real.log (30 * K ^ 2) + N * Real.log (9 * N)
        + ((n * (n + 1) * l : ℕ) : ℝ) * Real.log (20 * N) + N * Real.log u := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
  rw [hlogB]
  -- size of `4k²`
  have hK2 : N ^ 4 / 4 ≤ 4 * K ^ 2 := by
    have : (N ^ 2 / 4) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) hk4 2
    have e : (N ^ 2 / 4) ^ 2 = N ^ 4 / 16 := by ring
    linarith
  have hN2 : 144 ≤ N ^ 2 := by nlinarith
  have hK36 : 36 * N ^ 2 ≤ 4 * K ^ 2 := by
    have : 144 * N ^ 2 ≤ N ^ 2 * N ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
    have e : N ^ 2 * N ^ 2 = N ^ 4 := by ring
    linarith
  have hNN2 : N ≤ N ^ 2 := by nlinarith
  have hKN : N ≤ 4 * K ^ 2 := by linarith
  have hK3 : N ^ 3 * l ≤ 4 * K ^ 2 := by
    have h := mul_le_mul hnl' hk4 (by positivity) hKpos.le
    have e1 : N * l * (N ^ 2 / 4) = N ^ 3 * l / 4 := by ring
    have e2 : K * K = K ^ 2 := by ring
    linarith
  -- term 1
  have t1 : N * Real.log (30 * K ^ 2) ≤ 4 * K ^ 2 * (|a| + 4) := by
    have hle : 30 * K ^ 2 ≤ 30 * K0 ^ 2 * N ^ 4 := by
      have : K ^ 2 ≤ (K0 * N ^ 2) ^ 2 := pow_le_pow_left₀ hKpos.le hkK 2
      have e : (K0 * N ^ 2) ^ 2 = K0 ^ 2 * N ^ 4 := by ring
      linarith
    have hlog1 : Real.log (30 * K ^ 2) ≤ a + 4 * N := by
      have h1 := Real.log_le_log f1 hle
      have e : Real.log (30 * K0 ^ 2 * N ^ 4) = a + 4 * Real.log N := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, ← ha]; push_cast; ring
      have h2 := Real.log_le_sub_one_of_pos hNpos
      linarith
    have h3 : N * Real.log (30 * K ^ 2) ≤ N * (|a| + 4 * N) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self a]) hNpos.le
    have h4 : N * (|a| + 4 * N) ≤ N ^ 2 * (|a| + 4) := by
      have := mul_le_mul_of_nonneg_right hNN2 (abs_nonneg a)
      have e1 : N * (|a| + 4 * N) = N * |a| + 4 * N ^ 2 := by ring
      have e2 : N ^ 2 * (|a| + 4) = N ^ 2 * |a| + 4 * N ^ 2 := by ring
      linarith
    have h5 : N ^ 2 * (|a| + 4) ≤ 4 * K ^ 2 * (|a| + 4) := by
      have h36 : N ^ 2 ≤ 4 * K ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_right h36 (by positivity)
    linarith
  -- term 2
  have t2 : N * Real.log (9 * N) ≤ 4 * K ^ 2 * 1 := by
    have h := Real.log_le_sub_one_of_pos f2
    have : N * Real.log (9 * N) ≤ N * (9 * N) := mul_le_mul_of_nonneg_left (by linarith) hNpos.le
    have e : N * (9 * N) = 9 * N ^ 2 := by ring
    linarith
  -- term 3
  have t3 : ((n * (n + 1) * l : ℕ) : ℝ) * Real.log (20 * N) ≤ 4 * K ^ 2 * 40 := by
    have h := Real.log_le_sub_one_of_pos f3
    have hc : ((n * (n + 1) * l : ℕ) : ℝ) = N * (N + 1) * l := by rw [hN]; push_cast; ring
    rw [hc]
    have h0 : (0 : ℝ) ≤ N * (N + 1) * l := by positivity
    have : N * (N + 1) * l * Real.log (20 * N) ≤ N * (N + 1) * l * (20 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    have h6 : N * (N + 1) * l * (20 * N) ≤ 40 * (N ^ 3 * l) := by
      have h0 : (0 : ℝ) ≤ 20 * N ^ 2 * l := by positivity
      have h7 : N + 1 ≤ 2 * N := by linarith
      have := mul_le_mul_of_nonneg_right h7 h0
      have e1 : N * (N + 1) * l * (20 * N) = (N + 1) * (20 * N ^ 2 * l) := by ring
      have e2 : 40 * (N ^ 3 * l) = 2 * N * (20 * N ^ 2 * l) := by ring
      linarith
    linarith
  -- term 4
  have t4 : N * Real.log u ≤ 4 * K ^ 2 * c + 4 * K ^ 2 * (u * (E / N ^ 2)) := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hδpos hupos)
    rw [Real.log_mul hδpos.ne' hupos.ne'] at h
    have hlu : Real.log u ≤ δ * u + c := by
      have := neg_abs_le (1 + Real.log δ)
      rw [← hc] at this
      linarith
    have hcn : 0 ≤ c := abs_nonneg _
    have h1 : N * Real.log u ≤ N * (δ * u) + N * c := by
      have := mul_le_mul_of_nonneg_left hlu hNpos.le
      linarith
    have h2 : N * c ≤ 4 * K ^ 2 * c := mul_le_mul_of_nonneg_right hKN hcn
    have hz : N ^ 2 * (u * (E / N ^ 2)) = u * E := by field_simp
    have hz0 : 0 ≤ u * (E / N ^ 2) := by positivity
    have h3 : N ^ 4 / 4 * (u * (E / N ^ 2)) ≤ 4 * K ^ 2 * (u * (E / N ^ 2)) :=
      mul_le_mul_of_nonneg_right hK2 hz0
    have h4 : N ^ 4 / 4 * (u * (E / N ^ 2)) = N ^ 2 / 4 * (u * E) := by
      rw [← hz]; ring
    have h5 : N * (δ * u) ≤ N ^ 2 / 4 * (u * E) := by
      rw [hδ]
      have h0 : (0 : ℝ) ≤ u * E / 4 := by positivity
      have := mul_le_mul_of_nonneg_right hNN2 h0
      have e1 : N * (E / 4 * u) = N * (u * E / 4) := by ring
      have e2 : N ^ 2 / 4 * (u * E) = N ^ 2 * (u * E / 4) := by ring
      linarith
    linarith
  have hsum : N * Real.log (30 * K ^ 2) + N * Real.log (9 * N)
        + ((n * (n + 1) * l : ℕ) : ℝ) * Real.log (20 * N) + N * Real.log u
      ≤ 4 * K ^ 2 * (A + u * (E / N ^ 2)) := by
    have e : 4 * K ^ 2 * (A + u * (E / N ^ 2)) = 4 * K ^ 2 * (|a| + 4) + 4 * K ^ 2 * 1
        + 4 * K ^ 2 * 40 + 4 * K ^ 2 * c + 4 * K ^ 2 * (u * (E / N ^ 2)) := by rw [hA]; ring
    rw [e]; linarith
  have h4K : 0 < 4 * K ^ 2 := by positivity
  have : (N * Real.log (30 * K ^ 2) + N * Real.log (9 * N)
        + ((n * (n + 1) * l : ℕ) : ℝ) * Real.log (20 * N) + N * Real.log u) * (1 / (4 * K ^ 2))
      ≤ A + u * (E / N ^ 2) := by
    rw [mul_one_div, div_le_iff₀ h4K]; linarith
  linarith

/-! ### Steps ii to iv: display (8) -/

/-! Details for the LEAF below. It collects p. 245 last line to p. 247: Lemma 4 a and b raising
`W_1(a)` to the powers `2k` and `4k²`, with the integrals `J_k(λ)` and their properties a, b, c,
display (5); the bound `|Σ_{m≤U} e(αm)| ≤ min(U, 1/(α))`, display (6); Lemma 3 on the sums `𝔖_s`
for `s = s_j` with `B_s = 1/Q_s + θ_s/Q_s²` and hypothesis b of `KarHyp`, display (7) and the
estimate of its product; Lemma 1 for `J_k(0)` with `b = k`. Two harmless slips of the paper are
absorbed by the absolute constant `C0`: the factor `2^{8k²}` from
`(P2+1)^{8k²-4k} ≤ 2^{8k²} P2^{8k²-4k}`, missing from `B` on p. 247, and factors `2^s` from
`P2^{-1} ≤ 2 P^{-c1/3}` raised to the power `s`; after the `4k²`-th root both are bounded. The
threshold `P ≥ e^{cc0 n²}` is the reduction of p. 245 line 1, used for `Q_s ≥ 2` and
`log P ≥ 1`. The sum is `W_1(a)` of display (4), and `(P2 + 1)²` replaces `P2²`. -/

/-- LEAF: display (8) of Karacuba p. 247, class HARD, from p. 245 to 247, displays (5) to (8):
`|W_1(a)| ≤ C0 B_1 (P2+1)² P^{-ρ(s_1+...+s_r)/(8k²)}`, `B_1 = B^{1/(4k²)}`,
`B = (30k²)^n (9n)^n (20n)^{n(n+1)l} (log P)^n`, for the `l` of p. 245,
`k = nl + [n(n+1)/4 + 1]`, `ρ = min(c1/3, c3, c4)`. -/
theorem leaf_karW_display8 (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ C0 cc0 : ℝ, 0 < C0 ∧ 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a l : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P → 1 ≤ l →
          ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ l
            ≤ min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)) →
          min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ))
            < ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ (l - 1) →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ C0 *
            ((30 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2) ^ n *
              (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
              (Real.log (P : ℝ)) ^ n) ^
              (1 / (4 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2)) *
            ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)) /
              (8 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2))) := by
  sorry

/-! ### The assembly -/

/-- The split of `leaf_karW_taylor_sum_bound`: its exact statement, from display (8),
`leaf_karW_display8`, and the proved arithmetic of p. 245 and p. 248. `ρ = min(c1/3, c3, c4)`,
`B = C0 C1`, `cc = max(cc0, 1)`. -/
theorem leaf_karW_taylor_sum_bound_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ B ρ cc : ℝ, 0 < B ∧ 0 < ρ ∧ ρ ≤ c1 / 3 ∧ ρ ≤ c3 ∧ ρ ≤ c4 ∧ 0 < cc ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ B * ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + (Real.log (8 / (ρ * c0 ^ 2))) ^ 2) ^ 2))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨C0, cc0, hC0, hcc0, h8⟩ :=
    leaf_karW_display8 h1 h3 h4 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  set ρ := min (c1 / 3) (min c3 c4) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (lt_min hc3 hc4)
  have hρ1 : ρ ≤ c1 / 3 := min_le_left _ _
  have hρ3 : ρ ≤ c3 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ c4 := (min_le_right _ _).trans (min_le_right _ _)
  set L := Real.log (8 / (ρ * c0 ^ 2)) with hL
  have hρc : ρ * c0 ^ 2 < 1 := by
    have : c0 ^ 2 < 1 := by nlinarith
    have : ρ < 1 := by linarith
    nlinarith [sq_nonneg c0]
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; linarith
  set e0 : ℝ := ρ * c0 ^ 2 / (32 * (4 + L ^ 2) ^ 2) with he0
  have he0pos : 0 < e0 := by rw [he0]; positivity
  obtain ⟨C1, hC1, habs⟩ := karW_absorb_B1 (L + 1 / 2) (3 * e0) (by linarith) (by linarith)
  refine ⟨C0 * C1, ρ, max cc0 1, mul_pos hC0 hC1, hρpos, hρ1, hρ3, hρ4,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N P n f T a hP hn hn0 hbig hH ha haP
  have hn12r : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn0
  have hn12 : 12 ≤ n := by exact_mod_cast hn12r
  have hHc := hH
  obtain ⟨_, _, hT, hcard, _⟩ := hHc
  set σ : ℝ := ∑ s ∈ T, (s : ℝ) with hσ
  have hσlo := karW_sum_T_lower hc0 hT hcard
  have hσup := karW_sum_T_upper hT
  rw [← hσ] at hσlo hσup
  have hnpos : (0 : ℝ) < n := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσlo
  have hnn : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * (n + 1) := by push_cast; ring
  have hxA : ρ * σ < ((n * (n + 1) : ℕ) : ℝ) := by
    rw [hnn]
    have : ρ * σ ≤ σ / 3 := by
      have : ρ ≤ 1 / 3 := by linarith
      nlinarith
    have : (0 : ℝ) < (n : ℝ) * (n + 1) := by positivity
    linarith
  have hq0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
    linarith
  have hq1 : 1 - 1 / (n : ℝ) < 1 := by
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  obtain ⟨l, hl1, hlo, hhi⟩ := karW_choice_l (mul_pos hρpos hσpos) hxA hq0 hq1
  have hlL := karW_l_le hρpos hc0 hn hl1 hσlo hhi
  rw [← hL] at hlL
  obtain ⟨hk1, hk2, hk3⟩ := karW_k_bounds (l := l) hn12 hL0 hlL
  set k : ℕ := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hk
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk2
  have hexp := karW_exponent_compare (n := n) hρpos hc0 (by omega) hL0 hσlo hkpos hk3
  -- `P > 1`
  have hPbig : Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P := by
    refine le_trans (Real.exp_le_exp.2 ?_) hbig
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hP1 : (1 : ℝ) < P := by
    refine lt_of_lt_of_le ?_ hbig
    rw [← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : (0 : ℝ) < max cc0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hW := h8 N P n f T a l hP hn hn0 hPbig hH ha haP hl1 hlo hhi
  have hB1 := habs n l k (P : ℝ) hn12 hl1 hk1 hk2 (by linarith) hP1
  set Bk := ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
      (Real.log (P : ℝ)) ^ n) ^ (1 / (4 * (k : ℝ) ^ 2)) with hBk
  have hBk0 : 0 ≤ Bk := by
    rw [hBk]; apply Real.rpow_nonneg
    have : 0 < Real.log (P : ℝ) := Real.log_pos hP1
    positivity
  have hPpos : (0 : ℝ) < P := by linarith
  set Mp := ((karP2 c1 n P : ℝ) + 1) ^ 2 with hMp
  have hMp0 : 0 ≤ Mp := by positivity
  -- combine the two powers of `P`
  have hpow : (P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2) * (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2)))
      ≤ (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    rw [← Real.rpow_add hPpos]
    apply Real.rpow_le_rpow_of_exponent_le hP1.le
    have he : 3 * e0 / (n : ℝ) ^ 2 = 3 * (ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)) := by
      rw [he0]; field_simp
    rw [he]; linarith
  calc ‖_‖ ≤ C0 * Bk * Mp * (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2))) := hW
    _ ≤ C0 * (C1 * (P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2)) * Mp *
          (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2))) := by
        gcongr
    _ = C0 * C1 * Mp * ((P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2) *
          (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2)))) := by ring
    _ ≤ C0 * C1 * Mp * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
        gcongr

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
