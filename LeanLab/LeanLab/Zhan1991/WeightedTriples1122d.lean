import LeanLab.Zhan1991.SingIntegral1122

/-!
P0068 Zhan 1991, page 271, the weighted count of window triples, `WeightedTriplesEval`.
The proof combines the hexagon lattice count `windowTriples_count` and the weight comparison
`weight_compare` in `weightedTriplesEval_proof`, with no sorry.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Filter

noncomputable section

/-- The unweighted count of window triples `n₁ + n₂ + n₃ = N`, page 271: the number of lattice
points of the hexagon `|x₁|, |x₂|, |x₁ + x₂| ≤ U`, the same index set as `weightedTriples`. -/
def windowTriples (N : ℕ) (U : ℝ) : ℝ :=
  ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
    ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0

theorem windowTriples_nonneg (N : ℕ) (U : ℝ) : 0 ≤ windowTriples N U := by
  unfold windowTriples
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs <;> norm_num

/-- Page 271, for a fixed `n₁` in the window, the admissible `n₂` form an interval of length
`2U - |n₁ - N/3| + O(1)`. PROVED. -/
theorem count_inner (N : ℕ) (U : ℝ) (hU : 1 ≤ U) (hU12 : U ≤ (N : ℝ) / 12) (n₁ : ℕ)
    (h₁ : n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊) :
    |(∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) - (2 * U - |(n₁ : ℝ) - N / 3|)| ≤ 3 := by
  set a := ⌈(N : ℝ) / 3 - U⌉₊ with ha
  set b := ⌊(N : ℝ) / 3 + U⌋₊ with hb
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha1 : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
  have ha2 : (a : ℝ) < (N : ℝ) / 3 - U + 1 := Nat.ceil_lt_add_one (by linarith)
  have hb1 : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by linarith)
  have hb2 : (N : ℝ) / 3 + U < b + 1 := Nat.lt_floor_add_one _
  have h2b : 2 * b ≤ N := by
    have : ((2 * b : ℕ) : ℝ) ≤ N := by push_cast; linarith
    exact_mod_cast this
  rw [Finset.mem_Icc] at h₁
  have hn1a : (a : ℝ) ≤ n₁ := by exact_mod_cast h₁.1
  have hn1b : (n₁ : ℝ) ≤ b := by exact_mod_cast h₁.2
  have inner : ∀ n₂ ∈ Finset.Icc a b, (∑ n₃ ∈ Finset.Icc a b,
      if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) =
        if N - (n₁ + n₂) ∈ Finset.Icc a b then 1 else 0 := by
    intro n₂ h₂
    rw [Finset.mem_Icc] at h₂
    rw [← Finset.sum_ite_eq' (Finset.Icc a b) (N - (n₁ + n₂)) (fun _ => (1 : ℝ))]
    apply Finset.sum_congr rfl
    intro n₃ _
    apply if_congr _ rfl rfl
    omega
  rw [Finset.sum_congr rfl inner, Finset.sum_boole]
  have hfilt : (Finset.Icc a b).filter (fun n₂ => N - (n₁ + n₂) ∈ Finset.Icc a b) =
      Finset.Icc (max a (N - b - n₁)) (min b (N - a - n₁)) := by
    ext n₂
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
    omega
  rw [hfilt, Nat.card_Icc]
  have cmin : ((min b (N - a - n₁) : ℕ) : ℝ) = min (b : ℝ) ((N : ℝ) - a - n₁) := by
    rw [Nat.cast_min]
    congr 1
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast; ring
  have cmax : ((max a (N - b - n₁) : ℕ) : ℝ) = max (a : ℝ) ((N : ℝ) - b - n₁) := by
    rw [Nat.cast_max]
    congr 1
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast; ring
  rcases le_or_gt (max a (N - b - n₁)) (min b (N - a - n₁) + 1) with h | h
  · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one, cmin, cmax]
    rcases min_cases (b : ℝ) ((N : ℝ) - a - n₁) with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ <;>
    rcases max_cases (a : ℝ) ((N : ℝ) - b - n₁) with ⟨hM, hM'⟩ | ⟨hM, hM'⟩ <;>
    rw [hm, hM] <;>
    rcases abs_cases ((n₁ : ℝ) - N / 3) with ⟨hA, hA'⟩ | ⟨hA, hA'⟩ <;> rw [hA] <;>
    rw [abs_le] <;> constructor <;> linarith
  · have h' : (min b (N - a - n₁) + 1 : ℝ) < max a (N - b - n₁) := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    rw [Nat.cast_min, Nat.cast_max] at h'
    have e1 : ((N - a - n₁ : ℕ) : ℝ) = (N : ℝ) - a - n₁ := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((N - b - n₁ : ℕ) : ℝ) = (N : ℝ) - b - n₁ := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2] at h'
    rcases min_cases (b : ℝ) ((N : ℝ) - a - n₁) with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ <;>
    rcases max_cases (a : ℝ) ((N : ℝ) - b - n₁) with ⟨hM, hM'⟩ | ⟨hM, hM'⟩ <;>
    rw [hm, hM] at h' <;>
    rcases abs_cases ((n₁ : ℝ) - N / 3) with ⟨hA, hA'⟩ | ⟨hA, hA'⟩ <;> rw [hA] <;>
    rw [abs_le] <;> constructor <;> linarith

/-- The antiderivative `2U y - y|y|/2` of the hexagon section length. -/
theorem hex_step (U y : ℝ) :
    |((2 * U * (y + 1) - (y + 1) * |y + 1| / 2) - (2 * U * y - y * |y| / 2)) - (2 * U - |y|)|
      ≤ 1 := by
  rcases abs_cases (y + 1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases y with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> rw [h1, h2] <;>
  rw [abs_le] <;> constructor <;> nlinarith

theorem tele (F : ℕ → ℝ) (a : ℕ) : ∀ k : ℕ,
    ∑ n ∈ Finset.Ico a (a + k), (F (n + 1) - F n) = F (a + k) - F a
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), tele F a k]
    ring

/-- Page 271, the lattice count of the hexagon `|x₁|, |x₂|, |x₁ + x₂| ≤ U`: summing the section
lengths `2U - |n₁ - N/3|` by telescoping gives the area `3U²` with error `O(U)`. PROVED. -/
theorem windowTriples_count : ∃ C : ℝ, ∀ (N : ℕ) (U : ℝ), 1 ≤ U → U ≤ (N : ℝ) / 12 →
    |windowTriples N U - 3 * U ^ 2| ≤ C * U := by
  refine ⟨14, fun N U hU hU12 => ?_⟩
  set a := ⌈(N : ℝ) / 3 - U⌉₊ with ha
  set b := ⌊(N : ℝ) / 3 + U⌋₊ with hb
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha1 : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
  have ha2 : (a : ℝ) < (N : ℝ) / 3 - U + 1 := Nat.ceil_lt_add_one (by linarith)
  have hb1 : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by linarith)
  have hb2 : (N : ℝ) / 3 + U < b + 1 := Nat.lt_floor_add_one _
  have hW : windowTriples N U = ∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
      ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0 := rfl
  set t : ℝ := (N : ℝ) / 3 with ht
  set G : ℝ → ℝ := fun y => 2 * U * y - y * |y| / 2 with hG
  have hab : a ≤ b + 1 := by
    have : (a : ℝ) ≤ b + 1 := by linarith
    exact_mod_cast this
  have hcard : ((Finset.Icc a b).card : ℝ) ≤ 2 * U + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub hab]; push_cast; linarith
  have hIco : Finset.Icc a b = Finset.Ico a (b + 1) := by ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have htel : ∑ n ∈ Finset.Icc a b, (G ((n : ℝ) - t + 1) - G ((n : ℝ) - t)) =
      G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) := by
    have := tele (fun n : ℕ => G ((n : ℝ) - t)) a (b + 1 - a)
    have e : a + (b + 1 - a) = b + 1 := by omega
    rw [e] at this
    rw [hIco, show ((b : ℝ) + 1 - t) = (((b + 1 : ℕ) : ℝ) - t) by push_cast; ring, ← this]
    apply Finset.sum_congr rfl
    intro n _
    congr 2
    push_cast; ring
  have hstep : ∀ n ∈ Finset.Icc a b,
      |(G ((n : ℝ) - t + 1) - G ((n : ℝ) - t)) - (2 * U - |(n : ℝ) - N / 3|)| ≤ 1 := by
    intro n _
    rw [hG]
    exact hex_step U _
  have hA : |(∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
      ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) -
      ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|)| ≤
      ((Finset.Icc a b).card : ℝ) * 3 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => count_inner N U hU hU12 n hn).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hB : |(∑ n ∈ Finset.Icc a b, (G ((n : ℝ) - t + 1) - G ((n : ℝ) - t))) -
      ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|)| ≤
      ((Finset.Icc a b).card : ℝ) * 1 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => hstep n hn).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [htel] at hB
  have hC : |G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) - 3 * U ^ 2| ≤ 2 * U := by
    set e := (b : ℝ) + 1 - t - U with he
    set f := (a : ℝ) - t + U with hf
    have he0 : 0 ≤ e := by linarith
    have he1 : e ≤ 1 := by linarith
    have hf0 : 0 ≤ f := by linarith
    have hf1 : f ≤ 1 := by linarith
    have hyb : (b : ℝ) + 1 - t = U + e := by rw [he]; ring
    have hya : (a : ℝ) - t = -U + f := by rw [hf]; ring
    have key : G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) - 3 * U ^ 2 =
        U * e - U * f - (e * e + f * f) / 2 := by
      rw [hyb, hya, hG]
      simp only
      rw [abs_of_pos (by linarith : 0 < U + e), abs_of_nonpos (by linarith : -U + f ≤ 0)]
      ring
    rw [key]
    have hU0 : 0 ≤ U := by linarith
    have h1 : U * e ≤ U * 1 := mul_le_mul_of_nonneg_left he1 hU0
    have h2 : U * f ≤ U * 1 := mul_le_mul_of_nonneg_left hf1 hU0
    have h3 : 0 ≤ U * e := mul_nonneg hU0 he0
    have h4 : 0 ≤ U * f := mul_nonneg hU0 hf0
    have h5 : e * e ≤ 1 * 1 := mul_le_mul he1 he1 he0 zero_le_one
    have h6 : f * f ≤ 1 * 1 := mul_le_mul hf1 hf1 hf0 zero_le_one
    have h7 : 0 ≤ e * e := mul_nonneg he0 he0
    have h8 : 0 ≤ f * f := mul_nonneg hf0 hf0
    rw [abs_le]; constructor <;> linarith
  rw [hW]
  set S1 := (∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
      ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) with hS1
  set Sg := ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|) with hSg
  set Sd := G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) with hSd
  set K := ((Finset.Icc a b).card : ℝ) with hK
  clear_value S1 Sg Sd K
  have i1 := abs_sub_le S1 Sg (3 * U ^ 2)
  have i2 := abs_sub_le Sg Sd (3 * U ^ 2)
  rw [abs_sub_comm] at hB
  linarith


/-- Page 271, the weight comparison: for `N/4 ≤ nᵢ ≤ N` one has `log nᵢ = L + O(1)`, so
`(log n₁ log n₂ log n₃)⁻¹ = L⁻³ + O(L⁻⁴)`. PROVED. -/
theorem weight_compare : ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ n₁ n₂ n₃ : ℕ,
    (N : ℝ) / 4 ≤ n₁ → (n₁ : ℝ) ≤ N → (N : ℝ) / 4 ≤ n₂ → (n₂ : ℝ) ≤ N →
    (N : ℝ) / 4 ≤ n₃ → (n₃ : ℝ) ≤ N →
    |1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) - Real.log N ^ (-3 : ℝ)|
      ≤ C * Real.log N ^ (-4 : ℝ) := by
  refine ⟨24 * Real.log 4, 16, fun N hN n₁ n₂ n₃ h1 h1' h2 h2' h3 h3' => ?_⟩
  set L := Real.log N with hLdef
  set l := Real.log 4 with hldef
  have hN0 : (0 : ℝ) < N := by linarith
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hL2 : 2 * l ≤ L := by
    have : Real.log 16 = 2 * l := by
      rw [hldef, ← Real.log_rpow (by norm_num)]; norm_num
    rw [← this]; exact Real.log_le_log (by norm_num) hN
  have hL0 : 0 < L := by linarith
  have key : ∀ n : ℕ, (N : ℝ) / 4 ≤ n → (n : ℝ) ≤ N →
      L - l ≤ Real.log n ∧ Real.log n ≤ L := by
    intro n hn hn'
    have hnpos : (0 : ℝ) < n := by linarith
    refine ⟨?_, Real.log_le_log hnpos hn'⟩
    have := Real.log_le_log (by positivity) hn
    rw [Real.log_div hN0.ne' (by norm_num)] at this
    linarith
  obtain ⟨a1, b1⟩ := key n₁ h1 h1'
  obtain ⟨a2, b2⟩ := key n₂ h2 h2'
  obtain ⟨a3, b3⟩ := key n₃ h3 h3'
  set x1 := Real.log n₁
  set x2 := Real.log n₂
  set x3 := Real.log n₃
  have hx1 : 0 < x1 := by linarith
  have hx2 : 0 < x2 := by linarith
  have hx3 : 0 < x3 := by linarith
  have e3 : L ^ (-3 : ℝ) = 1 / L ^ 3 := by
    rw [Real.rpow_neg hL0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have e4 : L ^ (-4 : ℝ) = 1 / L ^ 4 := by
    rw [Real.rpow_neg hL0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [e3, e4]
  set p := x1 * x2 * x3 with hp
  have hp12 : (L / 2) * (L / 2) ≤ x1 * x2 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hx1.le
  have hplo : (L / 2) * (L / 2) * (L / 2) ≤ p :=
    mul_le_mul hp12 (by linarith) (by linarith) (by positivity)
  have hq12 : x1 * x2 ≤ L * L := mul_le_mul b1 b2 hx2.le hL0.le
  have hphi : p ≤ L * L * L := mul_le_mul hq12 b3 hx3.le (by positivity)
  -- `L³ - p ≤ L² (d₁ + d₂ + d₃)` with `dᵢ = L - xᵢ ∈ [0, l]`
  have hd12 : L * L - L * ((L - x1) + (L - x2)) ≤ x1 * x2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr b1) (sub_nonneg.mpr b2)]
  have hd123 : (L * L - L * ((L - x1) + (L - x2))) * x3 ≤ p :=
    mul_le_mul_of_nonneg_right hd12 hx3.le
  have hdiff : L * L * L - p ≤ 3 * l * (L * L) := by
    nlinarith [mul_nonneg (mul_nonneg hL0.le (sub_nonneg.mpr b3))
      (by linarith : 0 ≤ (L - x1) + (L - x2)), mul_nonneg (mul_nonneg hL0.le hL0.le)
      (sub_nonneg.mpr b3)]
  have hppos : 0 < p := by positivity
  have hnn : 0 ≤ 1 / p - 1 / L ^ 3 := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hppos (by nlinarith)
  rw [abs_of_nonneg hnn, div_sub_div _ _ hppos.ne' (by positivity), mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have hL6 : 0 < L * L * L * (L * L * L) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hdiff hL4, mul_le_mul_of_nonneg_left hplo
    (by positivity : 0 ≤ 24 * l * L ^ 3)]

/-- Arithmetic of the assembly. -/
theorem weightedTriples_arith (W T U L P Q C1 C2 : ℝ) (hQ : 0 ≤ Q) (hP : P = L * Q)
    (hL : 0 ≤ L) (hLU : L ≤ U) (hC1 : 0 ≤ C1) (hC1U : C1 ≤ U) (hC2 : 0 ≤ C2) (_hT0 : 0 ≤ T)
    (hT : |T - 3 * U ^ 2| ≤ C1 * U) (hup : W ≤ (P + C2 * Q) * T)
    (hlo : (P - C2 * Q) * T ≤ W) :
    |W - 3 * U ^ 2 * P| ≤ (C1 + 4 * C2) * U ^ 2 * Q := by
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hU : 0 ≤ U := hL.trans hLU
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have h1 : P * (T - 3 * U ^ 2) ≤ P * (C1 * U) := mul_le_mul_of_nonneg_left (by linarith) hP0
  have h1' : P * (3 * U ^ 2 - T) ≤ P * (C1 * U) := mul_le_mul_of_nonneg_left (by linarith) hP0
  have h2 : P * (C1 * U) ≤ Q * U * (C1 * U) := by
    rw [hP]; nlinarith [mul_le_mul_of_nonneg_right hLU (mul_nonneg hQ (mul_nonneg hC1 hU))]
  have h3 : Q * U * (C1 * U) ≤ Q * U * (U * U) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQ hU)
    exact mul_le_mul_of_nonneg_right hC1U hU
  have hTle : T ≤ 4 * U ^ 2 := by nlinarith
  have h4 : C2 * Q * T ≤ C2 * Q * (4 * U ^ 2) :=
    mul_le_mul_of_nonneg_left hTle (mul_nonneg hC2 hQ)
  rw [abs_le]
  constructor <;> nlinarith

/-- Page 271, `WeightedTriplesEval` from the lattice count and the weight comparison. -/
theorem weightedTriplesEval_proof : WeightedTriplesEval := by
  intro c hc
  obtain ⟨C1, hC1⟩ := windowTriples_count
  obtain ⟨C2, N2, hC2⟩ := weight_compare
  have F1 := ((isLittleO_log_rpow_rpow_atTop c (by norm_num : (0 : ℝ) < 3 / 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 12))
  have F2 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have F3 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)).bound one_pos
  have F4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)).eventually_ge_atTop
    (max (max C1 0) 1)
  have F5 := eventually_ge_atTop (max N2 1 : ℝ)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (F1.and (F2.and (F3.and (F4.and F5))))
  refine ⟨max C1 0 + 4 * max C2 0, A, fun N hN => ?_⟩
  obtain ⟨f1, f2, f3, f4, f5⟩ := hA N hN
  set x : ℝ := (N : ℝ) with hx
  set L := Real.log x with hL
  have hx1 : 1 ≤ x := (le_max_right _ _).trans f5
  have hx0 : 0 < x := by linarith
  have hxN2 : N2 ≤ x := (le_max_left _ _).trans f5
  have hL1 : 1 ≤ L := f2
  have hL0 : 0 < L := by linarith
  have hr0 : 0 < x ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hs0 : 0 < x ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _), Real.norm_of_nonneg hs0.le] at f1
  rw [Real.norm_of_nonneg hL0.le, Real.norm_of_nonneg hr0.le] at f3
  have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc.le
  set U := x ^ (5 / 8 : ℝ) * L ^ c with hU
  have hUr : x ^ (5 / 8 : ℝ) ≤ U := le_mul_of_one_le_right hr0.le hLc
  have hU1 : 1 ≤ U := ((le_max_right _ _).trans f4).trans hUr
  have hLU : L ≤ U := by linarith
  have hC1U : max C1 0 ≤ U := ((le_max_left _ 1).trans f4).trans hUr
  have hU12 : U ≤ x / 12 := by
    have hrs : x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    calc U ≤ x ^ (5 / 8 : ℝ) * (1 / 12 * x ^ (3 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left f1 hr0.le
      _ = (x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ)) / 12 := by ring
      _ = x / 12 := by rw [hrs]
  have hT := hC1 N U hU1 hU12
  have hT' : |windowTriples N U - 3 * U ^ 2| ≤ max C1 0 * U :=
    hT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  -- the window lies in `[N/4, N]`
  have hwin : ∀ n ∈ Finset.Icc ⌈x / 3 - U⌉₊ ⌊x / 3 + U⌋₊, x / 4 ≤ n ∧ (n : ℝ) ≤ x := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    constructor
    · have h := (Nat.le_ceil (x / 3 - U)).trans (Nat.cast_le.mpr hn.1)
      linarith
    · have h := (Nat.cast_le (α := ℝ)).mpr hn.2
      have h' := Nat.floor_le (by linarith : (0 : ℝ) ≤ x / 3 + U)
      linarith
  have hw := hC2 N hxN2
  set P := L ^ (-3 : ℝ)
  set Q := L ^ (-4 : ℝ)
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hL0.le _
  have hPQ : P = L * Q := by
    show L ^ (-3 : ℝ) = L * L ^ (-4 : ℝ)
    have : L ^ (-3 : ℝ) = L ^ (1 : ℝ) * L ^ (-4 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [this, Real.rpow_one]
  have hC2' : C2 * Q ≤ max C2 0 * Q := mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
  have hup : weightedTriples N U ≤ (P + max C2 0 * Q) * windowTriples N U := by
    unfold weightedTriples windowTriples
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n₁ h₁
    apply Finset.sum_le_sum; intro n₂ h₂
    apply Finset.sum_le_sum; intro n₃ h₃
    split_ifs
    · have := hw n₁ n₂ n₃ (hwin n₁ h₁).1 (hwin n₁ h₁).2 (hwin n₂ h₂).1 (hwin n₂ h₂).2
        (hwin n₃ h₃).1 (hwin n₃ h₃).2
      have := (abs_le.mp this).2
      linarith
    · simp
  have hlo : (P - max C2 0 * Q) * windowTriples N U ≤ weightedTriples N U := by
    unfold weightedTriples windowTriples
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n₁ h₁
    apply Finset.sum_le_sum; intro n₂ h₂
    apply Finset.sum_le_sum; intro n₃ h₃
    split_ifs
    · have := hw n₁ n₂ n₃ (hwin n₁ h₁).1 (hwin n₁ h₁).2 (hwin n₂ h₂).1 (hwin n₂ h₂).2
        (hwin n₃ h₃).1 (hwin n₃ h₃).2
      have := (abs_le.mp this).1
      linarith
    · simp
  have := weightedTriples_arith (weightedTriples N U) (windowTriples N U) U L P Q (max C1 0)
    (max C2 0) hQ0 hPQ hL0.le hLU (le_max_right _ _) hC1U (le_max_right _ _)
    (windowTriples_nonneg N U) hT' hup hlo
  exact this

end

end LeanLab.Zhan1991
