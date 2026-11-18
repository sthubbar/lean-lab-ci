import LeanLab.PNTPort.BV.PolyaVinogradov

/-!
# Kernel bound for the even case of the explicit Polya-Vinogradov inequality

AI wrote this file. Lab proof, standard mathematics, no cited input: completion of a character
sum by Gauss sums with a Fejer type smoothing. Goldbach itself is OPEN; nothing here changes that.

For an even primitive Dirichlet character `χ` modulo `q > 1`, every `n` and every `L ≥ 1`,

  `‖∑_{1 ≤ m ≤ n} χ(m)‖ ≤ (L - 1)/2
      + 1/(2 √q) * ∑_{0<a<q} min (1/sin(π a/q)) (1/(L sin(π a/q)^2))`.

Route. With `S(i) = ∑_{m ≤ i} χ(m)`, `K = 2n + L` and
`W = ∑_{j<L} ∑_{k<K} χ(k + j - (n + L - 1))`, evenness gives
`W = ∑_{j<L} (S(n + L - 1 - j) + S(n + j))`, so `‖S(n)‖ ≤ (L - 1)/2 + ‖W‖/(2L)`.
Gauss inversion `χ⁻¹(x) τ = ∑_a χ(a) ψ(x a)` gives
`‖W‖ √q ≤ ∑_{0<a<q} ‖∑_{j<L} e(j a/q)‖ ‖∑_{k<K} e(k a/q)‖`, and each geometric sum is at most
`1/sin(π a/q)`, the first one also at most `L`.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.BV

/-- `‖e(θ) - 1‖ = 2 |sin(π θ)|`. -/
theorem kernel_norm_e_sub_one (θ : ℝ) : ‖e θ - 1‖ = 2 * |sin (π * θ)| := by
  unfold e
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
    show 2 * π * θ / 2 = π * θ by ring]

/-- `sin(π θ) > 0` for `0 < θ < 1`. -/
theorem kernel_sin_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : 0 < sin (π * θ) := by
  have hp := pi_pos
  have h2 : π * θ < π * 1 := mul_lt_mul_of_pos_left h1 hp
  exact sin_pos_of_pos_of_lt_pi (mul_pos hp h0) (by linarith)

/-- Geometric sum: `‖∑_{k<N} e(k θ)‖ ≤ 1/sin(π θ)` for `0 < θ < 1`. -/
theorem kernel_norm_geom_le_inv_sin (N : ℕ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ‖∑ k ∈ range N, e (k * θ)‖ ≤ 1 / sin (π * θ) := by
  have hs : 0 < sin (π * θ) := kernel_sin_pos h0 h1
  have hne : e θ - 1 ≠ 0 := by
    intro h
    have h2 := kernel_norm_e_sub_one θ
    rw [h, norm_zero, abs_of_pos hs] at h2
    linarith
  have hz : e θ ≠ 1 := fun h => hne (by rw [h, sub_self])
  have h2 : ‖e θ ^ N - 1‖ ≤ 2 := by
    calc ‖e θ ^ N - 1‖ ≤ ‖e θ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hz, norm_div, kernel_norm_e_sub_one, abs_of_pos hs,
    div_le_div_iff₀ (by positivity) hs]
  have := mul_le_mul_of_nonneg_right h2 hs.le
  linarith

/-- Trivial bound for the geometric sum. -/
theorem kernel_norm_geom_le_card (N : ℕ) (θ : ℝ) :
    ‖∑ k ∈ range N, e (k * θ)‖ ≤ N := by
  calc ‖∑ k ∈ range N, e (k * θ)‖ ≤ ∑ k ∈ range N, ‖e (k * θ)‖ := norm_sum_le _ _
    _ = N := by simp [norm_e]

/-- Reindexing `Icc 1 d` as `range d`. -/
theorem kernel_sum_Icc_eq_range (g : ℕ → ℂ) (d : ℕ) :
    ∑ m ∈ Icc 1 d, g m = ∑ k ∈ range d, g (k + 1) := by
  refine sum_nbij' (fun m => m - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;>
    intro m hm <;> simp only [mem_Icc, mem_range] at hm ⊢
  · omega
  · omega
  · omega
  · omega
  · rw [Nat.sub_add_cancel hm.1]

/-- An even character satisfies `χ(-x) = χ(x)`. -/
theorem kernel_char_neg {q : ℕ} (χ : DirichletCharacter ℂ q) (h_even : χ (-1) = 1)
    (x : ZMod q) : χ (-x) = χ x := by
  rw [← neg_one_mul, map_mul, h_even, one_mul]

/-- The symmetric window identity: `∑_{k < c+1+d} χ(k - c) = S(c) + S(d)` for even `χ`. -/
theorem kernel_window_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (h_even : χ (-1) = 1) (c d : ℕ) :
    ∑ k ∈ range (c + 1 + d), χ ((k : ZMod q) - (c : ZMod q)) =
      ∑ k ∈ range c, χ ((k + 1 : ℕ) : ZMod q) + ∑ k ∈ range d, χ ((k + 1 : ℕ) : ZMod q) := by
  have hq1 : 1 < q := by have := NeZero.ne q; omega
  have : Fact (1 < q) := ⟨hq1⟩
  have h1 : ∑ k ∈ range c, χ ((k : ZMod q) - (c : ZMod q)) =
      ∑ k ∈ range c, χ ((k + 1 : ℕ) : ZMod q) := by
    refine (sum_range_reflect (fun k : ℕ => χ ((k : ZMod q) - (c : ZMod q))) c).symm.trans ?_
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have hc : (c : ZMod q) = ((c - 1 - j : ℕ) : ZMod q) + ((j + 1 : ℕ) : ZMod q) := by
      rw [← Nat.cast_add]; congr 1; omega
    show χ (((c - 1 - j : ℕ) : ZMod q) - (c : ZMod q)) = χ ((j + 1 : ℕ) : ZMod q)
    rw [← kernel_char_neg χ h_even ((j + 1 : ℕ) : ZMod q)]
    congr 1
    linear_combination (-1 : ZMod q) * hc
  have h2 : ∑ x ∈ range d, χ (((c + 1 + x : ℕ) : ZMod q) - (c : ZMod q)) =
      ∑ k ∈ range d, χ ((k + 1 : ℕ) : ZMod q) := by
    refine sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring
  have h3 : χ ((c : ZMod q) - (c : ZMod q)) = 0 := by
    rw [sub_self, MulChar.map_zero]
  rw [sum_range_add, sum_range_succ, h1, h2, h3, add_zero]

/-- Increments of the partial sums are bounded by their length. -/
theorem kernel_norm_partial_sub {q : ℕ} (χ : DirichletCharacter ℂ q) (n i : ℕ) :
    ‖∑ k ∈ range (n + i), χ ((k + 1 : ℕ) : ZMod q) - ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)‖
      ≤ i := by
  rw [sum_range_add, add_sub_cancel_left]
  calc ‖∑ x ∈ range i, χ ((n + x + 1 : ℕ) : ZMod q)‖
      ≤ ∑ x ∈ range i, ‖χ ((n + x + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ range i, (1 : ℝ) := sum_le_sum fun x _ => DirichletCharacter.norm_le_one χ _
    _ = i := by simp

/-- Fejer smoothing step: the partial sum is controlled by the doubly averaged sum `W`. -/
theorem even_pv_partial_le_window {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (h_even : χ (-1) = 1) (n L : ℕ) (hL : 1 ≤ L) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ ((L : ℝ) - 1) / 2 +
      ‖∑ j ∈ range L, ∑ k ∈ range (2 * n + L),
        χ ((k : ZMod q) + (j : ZMod q) - ((n + L - 1 : ℕ) : ZMod q))‖ / (2 * L) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ, ∀ i, T i = ∑ k ∈ range i, χ ((k + 1 : ℕ) : ZMod q) :=
    ⟨_, fun _ => rfl⟩
  have hin : ∀ c d : ℕ, ∑ k ∈ range (c + 1 + d), χ ((k : ZMod q) - (c : ZMod q)) =
      T c + T d := by
    intro c d; rw [hT, hT]; exact kernel_window_sum χ hq h_even c d
  have hdiff : ∀ m i : ℕ, ‖T (m + i) - T m‖ ≤ i := by
    intro m i; rw [hT, hT]; exact kernel_norm_partial_sub χ m i
  have hS : ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) = T n := by
    rw [hT]; exact kernel_sum_Icc_eq_range (fun m => χ (m : ZMod q)) n
  have hW : ∑ j ∈ range L, ∑ k ∈ range (2 * n + L),
      χ ((k : ZMod q) + (j : ZMod q) - ((n + L - 1 : ℕ) : ZMod q)) =
      ∑ j ∈ range L, (T (n + (L - 1 - j)) + T (n + j)) := by
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have hC : ((n + L - 1 : ℕ) : ZMod q) = ((n + (L - 1 - j) : ℕ) : ZMod q) + (j : ZMod q) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [show 2 * n + L = (n + (L - 1 - j)) + 1 + (n + j) by omega, ← hin]
    refine sum_congr rfl fun k _ => ?_
    congr 1
    linear_combination (-1 : ZMod q) * hC
  rw [hS, hW]
  obtain ⟨W, hWdef⟩ : ∃ W : ℂ, W = ∑ j ∈ range L, (T (n + (L - 1 - j)) + T (n + j)) :=
    ⟨_, rfl⟩
  rw [← hWdef]
  have hsub : W - 2 * (L : ℂ) * T n =
      ∑ j ∈ range L, ((T (n + (L - 1 - j)) - T n) + (T (n + j) - T n)) := by
    rw [hWdef]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
  have hnorm : ‖W - 2 * (L : ℂ) * T n‖ ≤ L * ((L : ℝ) - 1) := by
    rw [hsub]
    calc ‖∑ j ∈ range L, ((T (n + (L - 1 - j)) - T n) + (T (n + j) - T n))‖
        ≤ ∑ j ∈ range L, ‖(T (n + (L - 1 - j)) - T n) + (T (n + j) - T n)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range L, ((L : ℝ) - 1) := by
          refine sum_le_sum fun j hj => ?_
          have hj' := mem_range.1 hj
          have hnat : L - 1 - j + j + 1 = L := by omega
          have hcast : ((L - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hnat
          have := norm_add_le (T (n + (L - 1 - j)) - T n) (T (n + j) - T n)
          have := hdiff n (L - 1 - j)
          have := hdiff n j
          linarith
      _ = L * ((L : ℝ) - 1) := by rw [sum_const, card_range, nsmul_eq_mul]
  have h2 : ‖2 * (L : ℂ) * T n‖ = 2 * (L : ℝ) * ‖T n‖ := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_two]
  have h3 : ‖2 * (L : ℂ) * T n‖ ≤ ‖W‖ + ‖W - 2 * (L : ℂ) * T n‖ := by
    calc ‖2 * (L : ℂ) * T n‖ = ‖W - (W - 2 * (L : ℂ) * T n)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have h4 : ‖T n‖ - ((L : ℝ) - 1) / 2 ≤ ‖W‖ / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Gauss inversion step: the doubly averaged sum against products of geometric sums. -/
theorem even_pv_window_gauss_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (c L K : ℕ) :
    ‖∑ j ∈ range L, ∑ k ∈ range K, χ ((k : ZMod q) + (j : ZMod q) - (c : ZMod q))‖ * sqrt q ≤
      ∑ a ∈ Finset.Ioo 0 q,
        min (L : ℝ) (1 / sin (π * ((a : ℝ) / q))) * (1 / sin (π * ((a : ℝ) / q))) := by
  have hq1 : 1 < q := by have := NeZero.ne q; omega
  have : Fact (1 < q) := ⟨hq1⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar (ZMod q) ℂ, ψ = ZMod.stdAddChar := ⟨_, rfl⟩
  have hψn : ∀ z : ZMod q, ‖ψ z‖ = 1 := by
    intro z; rw [hψ]; exact norm_stdAddChar z
  have hψe : ∀ k a : ℕ, ψ ((k : ZMod q) * (a : ZMod q)) = e (k * ((a : ℝ) / q)) := by
    intro k a
    have h := stdAddChar_mul_natCast (q := q) (k : ℤ) a
    push_cast at h
    rw [hψ]; exact h
  have hg : ∀ x : ZMod q, χ⁻¹ x * gaussSum χ ψ = ∑ a : ZMod q, χ a * ψ (x * a) := by
    intro x
    rw [← gaussSum_mulShift_of_isPrimitive ψ hχ, gaussSum]
    rfl
  have hτ : ‖gaussSum χ ψ‖ = sqrt q := by
    rw [hψ, ← normSq_gaussSum_of_isPrimitive hχ, sqrt_sq (norm_nonneg _)]
  have hconj : ∑ j ∈ range L, ∑ k ∈ range K,
      χ⁻¹ ((k : ZMod q) + (j : ZMod q) - (c : ZMod q)) =
      (starRingEnd ℂ) (∑ j ∈ range L, ∑ k ∈ range K,
        χ ((k : ZMod q) + (j : ZMod q) - (c : ZMod q))) := by
    rw [map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact sum_congr rfl fun k _ => (conj_char_eq_inv χ _).symm
  have hterm : ∀ (j k : ℕ) (x : ZMod q),
      χ x * ψ (((k : ZMod q) + (j : ZMod q) - (c : ZMod q)) * x) =
        χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x) * ψ ((k : ZMod q) * x) := by
    intro j k x
    rw [show ((k : ZMod q) + (j : ZMod q) - (c : ZMod q)) * x =
        -((c : ZMod q) * x) + (j : ZMod q) * x + (k : ZMod q) * x by ring,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  have step1 : (∑ j ∈ range L, ∑ k ∈ range K,
      χ⁻¹ ((k : ZMod q) + (j : ZMod q) - (c : ZMod q))) * gaussSum χ ψ =
      ∑ j ∈ range L, ∑ k ∈ range K, ∑ x : ZMod q,
        χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x) * ψ ((k : ZMod q) * x) := by
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [hg]
    exact sum_congr rfl fun x _ => hterm j k x
  have step2 : ∑ j ∈ range L, ∑ k ∈ range K, ∑ x : ZMod q,
        χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x) * ψ ((k : ZMod q) * x) =
      ∑ x : ZMod q, χ x * ψ (-((c : ZMod q) * x)) * (∑ j ∈ range L, ψ ((j : ZMod q) * x)) *
        (∑ k ∈ range K, ψ ((k : ZMod q) * x)) := by
    refine ((sum_congr rfl fun j _ => sum_comm).trans sum_comm).trans ?_
    refine sum_congr rfl fun x _ => ?_
    calc ∑ j ∈ range L, ∑ k ∈ range K,
          χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x) * ψ ((k : ZMod q) * x)
        = ∑ j ∈ range L, χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x) *
            (∑ k ∈ range K, ψ ((k : ZMod q) * x)) :=
          sum_congr rfl fun j _ => (mul_sum _ _ _).symm
      _ = (∑ j ∈ range L, χ x * ψ (-((c : ZMod q) * x)) * ψ ((j : ZMod q) * x)) *
            (∑ k ∈ range K, ψ ((k : ZMod q) * x)) := (sum_mul _ _ _).symm
      _ = χ x * ψ (-((c : ZMod q) * x)) * (∑ j ∈ range L, ψ ((j : ZMod q) * x)) *
            (∑ k ∈ range K, ψ ((k : ZMod q) * x)) := by rw [← mul_sum]
  have step3 : ∑ x : ZMod q, χ x * ψ (-((c : ZMod q) * x)) *
        (∑ j ∈ range L, ψ ((j : ZMod q) * x)) * (∑ k ∈ range K, ψ ((k : ZMod q) * x)) =
      ∑ a ∈ Finset.Ioo 0 q, χ (a : ZMod q) * ψ (-((c : ZMod q) * (a : ZMod q))) *
        (∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q))) *
        (∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q))) := by
    rw [sum_zmod_eq_sum_range]
    symm
    refine sum_subset ?_ ?_
    · intro a ha
      rw [mem_Ioo] at ha
      exact mem_range.2 ha.2
    · intro a ha hna
      rw [mem_range] at ha
      rw [mem_Ioo] at hna
      have ha0 : a = 0 := by omega
      rw [ha0, Nat.cast_zero, MulChar.map_zero, zero_mul, zero_mul, zero_mul]
  have hbound : ‖(∑ j ∈ range L, ∑ k ∈ range K,
      χ⁻¹ ((k : ZMod q) + (j : ZMod q) - (c : ZMod q))) * gaussSum χ ψ‖ ≤
      ∑ a ∈ Finset.Ioo 0 q,
        min (L : ℝ) (1 / sin (π * ((a : ℝ) / q))) * (1 / sin (π * ((a : ℝ) / q))) := by
    rw [step1, step2, step3]
    refine (norm_sum_le _ _).trans (sum_le_sum fun a ha => ?_)
    rw [mem_Ioo] at ha
    have ha0 : (0 : ℝ) < (a : ℝ) / q := div_pos (by exact_mod_cast ha.1) hq0
    have ha1 : (a : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast ha.2)
    have hGL : ∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q)) =
        ∑ j ∈ range L, e (j * ((a : ℝ) / q)) := sum_congr rfl fun j _ => hψe j a
    have hGK : ∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q)) =
        ∑ k ∈ range K, e (k * ((a : ℝ) / q)) := sum_congr rfl fun k _ => hψe k a
    have hL1 : ‖∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q))‖ ≤
        min (L : ℝ) (1 / sin (π * ((a : ℝ) / q))) := by
      rw [hGL]
      exact le_min (kernel_norm_geom_le_card L _) (kernel_norm_geom_le_inv_sin L ha0 ha1)
    have hK1 : ‖∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q))‖ ≤
        1 / sin (π * ((a : ℝ) / q)) := by
      rw [hGK]
      exact kernel_norm_geom_le_inv_sin K ha0 ha1
    have hχ1 : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    rw [norm_mul, norm_mul, norm_mul, hψn]
    calc ‖χ (a : ZMod q)‖ * 1 * ‖∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q))‖ *
          ‖∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q))‖
        ≤ 1 * 1 * ‖∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q))‖ *
          ‖∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q))‖ := by gcongr
      _ = ‖∑ j ∈ range L, ψ ((j : ZMod q) * (a : ZMod q))‖ *
          ‖∑ k ∈ range K, ψ ((k : ZMod q) * (a : ZMod q))‖ := by ring
      _ ≤ _ := mul_le_mul hL1 hK1 (norm_nonneg _) (le_trans (norm_nonneg _) hL1)
  rw [norm_mul, hconj, Complex.norm_conj, hτ] at hbound
  exact hbound

/-- **Kernel bound for the even case.** For an even primitive character modulo `q > 1`, the
partial sums are bounded by `(L - 1)/2` plus `1/(2 √q)` times the Fejer type kernel sum. -/
theorem even_pv_kernel_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) (n L : ℕ) (hL : 1 ≤ L) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      ((L : ℝ) - 1) / 2 + 1 / (2 * sqrt q) *
        ∑ a ∈ Finset.Ioo 0 q, min (1 / sin (π * a / q)) (1 / (L * sin (π * a / q) ^ 2)) := by
  have hq1 : 1 < q := by have := NeZero.ne q; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hsq : (0 : ℝ) < sqrt q := sqrt_pos.2 hq0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hA := even_pv_partial_le_window χ hq h_even n L hL
  have hB := even_pv_window_gauss_bound χ hχ hq (n + L - 1) L (2 * n + L)
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg =
      ∑ a ∈ Finset.Ioo 0 q, min (1 / sin (π * a / q)) (1 / (L * sin (π * a / q) ^ 2)) :=
    ⟨_, rfl⟩
  rw [← hSg]
  have hSum : ∑ a ∈ Finset.Ioo 0 q,
      min (L : ℝ) (1 / sin (π * ((a : ℝ) / q))) * (1 / sin (π * ((a : ℝ) / q))) =
      L * Sg := by
    rw [hSg, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_Ioo] at ha
    have ha0 : (0 : ℝ) < (a : ℝ) / q := div_pos (by exact_mod_cast ha.1) hq0
    have ha1 : (a : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast ha.2)
    have hs := kernel_sin_pos ha0 ha1
    rw [show π * ((a : ℝ) / q) = π * a / q by ring] at hs ⊢
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = sin (π * a / q) := ⟨_, rfl⟩
    rw [← hsdef] at hs ⊢
    have hsne : s ≠ 0 := hs.ne'
    have hLne : (L : ℝ) ≠ 0 := hL0.ne'
    rw [min_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / s),
      mul_min_of_nonneg _ _ hL0.le]
    have e2 : 1 / s * (1 / s) = (L : ℝ) * (1 / (L * s ^ 2)) := by
      field_simp
    rw [e2]
  rw [hSum] at hB
  have h2 := (le_div_iff₀ hsq).2 hB
  have h3 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * L)
  have h4 : (L : ℝ) * Sg / sqrt q / (2 * L) = 1 / (2 * sqrt q) * Sg := by
    have hLne : (L : ℝ) ≠ 0 := hL0.ne'
    have hsqne : sqrt (q : ℝ) ≠ 0 := hsq.ne'
    field_simp
  rw [h4] at h3
  linarith

end LeanLab.HelfgottMajor.PolyaVinogradov123
