/-
Second split, of `leaf_solution_count_succ_large` of `SPLIT_s5_S5_02_count_succ`, the
induction step of the counting form of Karacuba 1971 Lemma 1 p. 243, his reference [1],
Vinogradov, in the range `P ≥ (20 n)^(m+1)`.

* `leaf_count_add_n_le`: proved by CLOUD S5-02c, formerly LEAF MEDIUM, the monotonicity `J_(b+n)(P) ≤ P^(2n) J_b(P)` of the
  number of solutions, by Cauchy Schwarz over each added pair of variables.
* `s5_02b_mid`: proved, CONDITIONAL ON that leaf, from it and the hypothesis at `m`, for `P < (20 n)^n`: the excess
  `P^(N (1-1/n)^m / n)` with `N = n(n+1)/2` is then at most `(20 n)^N`.
* `leaf_solution_count_succ_large_beyond`: LEAF, HARD, the range `P ≥ (20 n)^n`.
* `leaf_solution_count_succ_large_of_leaves`: the parent leaf verbatim, with a `type_of%` twin.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_02_count_succ

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

open Classical

/-- Proved: the shifted count is at most the unshifted one, `Σ_v r(v) r(v+w) ≤ Σ_v r(v)^2`,
by the pointwise AM GM `2 ≤ a/b + b/a` on fiber sizes. Step of Vinogradov's monotonicity
behind Karacuba Lemma 1 p. 243. -/
theorem s5_02c_shift_le {X V : Type*} [Fintype X] [AddCommGroup V] (s : X → V) (w : V) :
    ∑ x : X, ∑ y : X, (if s x = s y + w then (1:ℝ) else 0)
      ≤ ∑ x : X, ∑ y : X, (if s x = s y then (1:ℝ) else 0) := by
  set r : V → ℝ := fun v => ∑ z : X, (if s z = v then (1:ℝ) else 0) with hr
  have hpos : ∀ x, 0 < r (s x) := by
    intro x
    have : (if s x = s x then (1:ℝ) else 0) ≤ r (s x) :=
      Finset.single_le_sum (f := fun z => if s z = s x then (1:ℝ) else 0)
        (fun z _ => by split_ifs <;> norm_num) (Finset.mem_univ x)
    simp at this; linarith
  have hC : ∑ x : X, ∑ y : X, (if s x = s y then (1:ℝ) else 0) = ∑ y : X, r (s y) := by
    rw [Finset.sum_comm]
  -- pointwise AM-GM
  have key : ∀ x y, (if s x = s y + w then (1:ℝ) else 0)
      ≤ ((if s x = s y + w then (1:ℝ) else 0) * (r (s y) / r (s x))
        + (if s x = s y + w then (1:ℝ) else 0) * (r (s x) / r (s y))) / 2 := by
    intro x y
    split_ifs with h
    · have a := hpos x; have b := hpos y
      rw [one_mul, one_mul, div_add_div _ _ (ne_of_gt a) (ne_of_gt b)]
      rw [le_div_iff₀ (by norm_num), one_mul, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (r (s y) - r (s x))]
    · simp
  have h1 : ∑ x : X, ∑ y : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s y) / r (s x))
      ≤ ∑ y : X, r (s y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro y _
    have : ∑ x : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s y) / r (s x))
        = r (s y) * ((∑ x : X, (if s x = s y + w then (1:ℝ) else 0)) / r (s y + w)) := by
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      split_ifs with h
      · rw [h]; ring
      · simp
    rw [this]
    have hy := hpos y
    have hq : (∑ x : X, (if s x = s y + w then (1:ℝ) else 0)) / r (s y + w) ≤ 1 := by
      change r (s y + w) / r (s y + w) ≤ 1
      exact div_self_le_one _
    nlinarith
  have h2 : ∑ x : X, ∑ y : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s x) / r (s y))
      ≤ ∑ x : X, r (s x) := by
    apply Finset.sum_le_sum; intro x _
    have : ∑ y : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s x) / r (s y))
        = r (s x) * ((∑ y : X, (if s y = s x - w then (1:ℝ) else 0)) / r (s x - w)) := by
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      by_cases h : s x = s y + w
      · have h' : s y = s x - w := by rw [h]; abel
        rw [if_pos h, if_pos h', h']; ring
      · have h' : ¬ s y = s x - w := by intro h'; apply h; rw [h']; abel
        rw [if_neg h, if_neg h']; ring
    rw [this]
    have hx := hpos x
    have hq : (∑ y : X, (if s y = s x - w then (1:ℝ) else 0)) / r (s x - w) ≤ 1 := by
      change r (s x - w) / r (s x - w) ≤ 1
      exact div_self_le_one _
    nlinarith
  rw [hC]
  calc _ ≤ ∑ x : X, ∑ y : X, ((if s x = s y + w then (1:ℝ) else 0) * (r (s y) / r (s x))
        + (if s x = s y + w then (1:ℝ) else 0) * (r (s x) / r (s y))) / 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => key x y
    _ = ((∑ x : X, ∑ y : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s y) / r (s x)))
        + ∑ x : X, ∑ y : X, (if s x = s y + w then (1:ℝ) else 0) * (r (s x) / r (s y))) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          congr 1; ext x; rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := by linarith


/-- Proved: one added variable, `J_(m+1)(P) ≤ P^2 J_m(P)`. -/
theorem s5_02c_count_succ_le (N m P : ℕ) :
    ∑ x : Fin (m + 1) → Fin P, ∑ y : Fin (m + 1) → Fin P,
        (if (∀ j : Fin N,
            ∑ i : Fin (m + 1), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
              = ∑ i : Fin (m + 1), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
          then (1 : ℝ) else 0)
      ≤ (P : ℝ) ^ 2 *
        ∑ x : Fin m → Fin P, ∑ y : Fin m → Fin P,
          (if (∀ j : Fin N,
              ∑ i : Fin m, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin m, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0) := by
  let s : (Fin m → Fin P) → (Fin N → ℝ) :=
    fun x j => ∑ i : Fin m, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
  let t : Fin P → (Fin N → ℝ) := fun a j => (((a.val + 1 : ℕ) : ℝ)) ^ ((j : ℕ) + 1)
  have e : ∀ f : (Fin (m + 1) → Fin P) → ℝ,
      ∑ x, f x = ∑ a : Fin P, ∑ x' : Fin m → Fin P, f (Fin.cons a x') := by
    intro f
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin P) _ _ (fun p => rfl)).symm
  have hcond : ∀ a c x' y', (∀ j : Fin N,
      ∑ i : Fin (m + 1), ((((Fin.cons a x' : Fin (m+1) → Fin P) i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
        = ∑ i : Fin (m + 1), ((((Fin.cons c y' : Fin (m+1) → Fin P) i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
      ↔ s x' = s y' + (t c - t a) := by
    intro a c x' y'
    rw [funext_iff]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, s, t, Pi.add_apply, Pi.sub_apply]
    constructor <;> intro h j <;> have := h j <;> linarith
  have hC : ∀ (X : Type) [Fintype X] (u : X → (Fin N → ℝ)),
      (∑ x : X, ∑ y : X, (if u x = u y then (1:ℝ) else 0))
        = ∑ x : X, ∑ y : X, (if (∀ j, u x j = u y j) then (1:ℝ) else 0) := by
    intro X _ u; simp only [funext_iff]
  rw [e]
  conv_lhs => arg 2; ext a; arg 2; ext x'; rw [e]
  simp_rw [hcond]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  have hb : ∀ a c : Fin P, ∑ x' : Fin m → Fin P, ∑ y' : Fin m → Fin P,
      (if s x' = s y' + (t c - t a) then (1:ℝ) else 0)
      ≤ ∑ x : Fin m → Fin P, ∑ y : Fin m → Fin P,
          (if (∀ j : Fin N,
              ∑ i : Fin m, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin m, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0) := by
    intro a c
    have := s5_02c_shift_le s (t c - t a)
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; congr
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    by_cases h : s x = s y
    · rw [if_pos h, if_pos (funext_iff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (funext h'))]
  calc _ ≤ ∑ a : Fin P, ∑ c : Fin P, ∑ x : Fin m → Fin P, ∑ y : Fin m → Fin P,
          (if (∀ j : Fin N,
              ∑ i : Fin m, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin m, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hb a c
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


/-- Proved: `k` added variables, `J_(b+k)(P) ≤ P^(2k) J_b(P)`. -/
theorem s5_02c_count_add_le (N b P : ℕ) : ∀ k : ℕ,
    ∑ x : Fin (b + k) → Fin P, ∑ y : Fin (b + k) → Fin P,
        (if (∀ j : Fin N,
            ∑ i : Fin (b + k), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
              = ∑ i : Fin (b + k), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
          then (1 : ℝ) else 0)
      ≤ (P : ℝ) ^ (2 * k) *
        ∑ x : Fin b → Fin P, ∑ y : Fin b → Fin P,
          (if (∀ j : Fin N,
              ∑ i : Fin b, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin b, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0)
  | 0 => by simp
  | k + 1 => by
    have ih := s5_02c_count_add_le N b P k
    refine (s5_02c_count_succ_le N (b + k) P).trans ?_
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (by positivity)

/-- Proved by CLOUD S5-02c, formerly a MEDIUM LEAF: the monotonicity of the number of solutions of Vinogradov's system in the number of
variables, `J_(b+n)(P) ≤ P^(2n) J_b(P)`, used throughout Vinogradov's method behind Karacuba's
Lemma 1 p. 243, his reference [1]. MEDIUM. Proof: with `r_b(v)` the number of `x` with power
sums `v`, `J_b = Σ_v r_b(v)^2` and `r_(b+1)(v) = Σ_(t ≤ P) r_b(v - s(t))`, so Cauchy Schwarz gives
`J_(b+1) ≤ P^2 J_b`; iterate `n` times. Equivalently `∫ |S|^(2b+2) ≤ P^2 ∫ |S|^(2b)`. -/
theorem leaf_count_add_n_le :
    ∀ n b P : ℕ,
      ∑ x : Fin (b + n) → Fin P, ∑ y : Fin (b + n) → Fin P,
        (if (∀ j : Fin n,
            ∑ i : Fin (b + n), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
              = ∑ i : Fin (b + n), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
          then (1 : ℝ) else 0)
      ≤ (P : ℝ) ^ (2 * n) *
        ∑ x : Fin b → Fin P, ∑ y : Fin b → Fin P,
          (if (∀ j : Fin n,
              ∑ i : Fin b, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin b, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0) := by
  intro n b P
  exact s5_02c_count_add_le n b P n

/-- Proved, CONDITIONAL ON the MEDIUM LEAF `leaf_count_add_n_le`, with the hypothesis at `m`: the induction step of Lemma 1
p. 243 for `0 < P < (20 n)^n`. -/
theorem s5_02b_mid (n : ℕ) (hn : 12 ≤ n) (m : ℕ) (P : ℕ) (hP : 0 < P)
    (hmid : (P : ℝ) < (20 * n : ℝ) ^ n)
    (ih : ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P : ℝ) ^ ((2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) :
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  set k := ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hk
  have hb : n * (m + 1) + k = (n * m + k) + n := by ring
  have hstep := leaf_count_add_n_le n (n * m + k) P
  rw [← hb] at hstep
  refine lt_of_le_of_lt hstep ?_
  set J := ∑ x : Fin (n * m + k) → Fin P, ∑ y : Fin (n * m + k) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + k), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + k), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0) with hJ
  set N : ℝ := ((n * (n + 1) : ℕ) : ℝ) / 2 with hN
  set D : ℝ := (1 - 1 / (n : ℝ)) ^ m with hD
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN0 : 0 < N := by rw [hN]; push_cast; positivity
  have hD0 : 0 ≤ D := by
    rw [hD]; apply pow_nonneg
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
    linarith
  have hD1 : D ≤ 1 := by
    rw [hD]; apply pow_le_one₀
    · have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
      linarith
    · have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  -- the needed comparison of the P powers
  have hcmp : (P : ℝ) ^ (N * D) ≤ (20 * n : ℝ) ^ N * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)) := by
    have hsplitP : (P : ℝ) ^ (N * D) = (P : ℝ) ^ (N * D / n) * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)) := by
      rw [← Real.rpow_add hP0]; congr 1; rw [hD, pow_succ]; field_simp; ring
    rw [hsplitP]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (P : ℝ) ^ (N * D / n) ≤ (P : ℝ) ^ (N / n) := by
          apply Real.rpow_le_rpow_of_exponent_le hPR
          apply div_le_div_of_nonneg_right _ hn0.le
          nlinarith
      _ ≤ ((20 * n : ℝ) ^ n) ^ (N / n) := Real.rpow_le_rpow hP0.le hmid.le (by positivity)
      _ = (20 * n : ℝ) ^ N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; field_simp
  have hC : (20 * n : ℝ) ^ (N * ((m + 1 : ℕ) : ℝ)) = (20 * n : ℝ) ^ (N * m) * (20 * n : ℝ) ^ N := by
    rw [← Real.rpow_add (by positivity)]; congr 1; push_cast; ring
  have hE : (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) = (P : ℝ) ^ (2 * n) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hP0]; congr 1; push_cast; ring
  rw [hC, hE]
  have hP2n : 0 < (P : ℝ) ^ (2 * n) := by positivity
  have h1 := mul_lt_mul_of_pos_left ih hP2n
  have hCm : 0 ≤ (20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hcmp hCm
  calc (P : ℝ) ^ (2 * n) * J < (P : ℝ) ^ (2 * n) * ((20 * n : ℝ) ^ (N * m) * ((P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N))) := h1
    _ = (P : ℝ) ^ (2 * n) * (((20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N)) * (P : ℝ) ^ (N * D)) := by ring
    _ ≤ (P : ℝ) ^ (2 * n) * (((20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N)) * ((20 * n : ℝ) ^ N * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)))) :=
        mul_le_mul_of_nonneg_left h2 hP2n.le
    _ = _ := by ring

/-- LEAF: Vinogradov's mean value theorem, induction step from `l = m` to `l = m + 1` as
Karacuba cites it for Lemma 1 p. 243, his reference [1], in the range `P ≥ (20 n)^(m+1)` and
`P ≥ (20 n)^n`, where neither the trivial count nor the monotonicity in the number of variables
suffices. HARD. This is the recursive inequality of Vinogradov's method, `J_(b+n)(P)` bounded
through `J_b(P_1)` with `P_1` about `P^(1 - 1/n)`. The statement is
`leaf_solution_count_succ_large` with `(20 n)^n ≤ P` added. -/
theorem leaf_solution_count_succ_large_beyond :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m →
      (∀ P : ℕ, 0 < P →
        ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P : ℝ) ^ ((2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) →
      ∀ P : ℕ, 0 < P → (20 * n : ℝ) ^ (m + 1) ≤ (P : ℝ) → (20 * n : ℝ) ^ n ≤ (P : ℝ) →
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  sorry

/-- PROVED from the leaves: the statement of `leaf_solution_count_succ_large` verbatim. -/
theorem leaf_solution_count_succ_large_of_leaves :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m →
      (∀ P : ℕ, 0 < P →
        ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P : ℝ) ^ ((2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) →
      ∀ P : ℕ, 0 < P → (20 * n : ℝ) ^ (m + 1) ≤ (P : ℝ) →
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  intro n hn m hm ih P hP hlarge
  by_cases hs : (P : ℝ) < (20 * n : ℝ) ^ n
  · exact s5_02b_mid n hn m P hP hs (ih P hP)
  · exact leaf_solution_count_succ_large_beyond n hn m hm ih P hP hlarge (not_lt.1 hs)

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_solution_count_succ_large := leaf_solution_count_succ_large_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.s5_02b_mid
