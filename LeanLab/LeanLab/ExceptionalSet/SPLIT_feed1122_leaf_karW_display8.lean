/-
Split of `leaf_karW_display8` of `LeanLab.ExceptionalSet.SPLIT_leaf_karW_taylor_sum_bound`, display (8)
of A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 245-247, the analytic core of the case
`n ≥ n0` of Theorem 1. Read from the page images of journal p. 246 and p. 247.

Pieces, with `M = P2 = karP2 c1 n P`, `B_s = f^{(s)}(a)/s!` and `ρ = min(c1/3, c3, c4)`.
* `leaf_karW_display5`: p. 246, Lemma 4 a for the power `2k`, the expansion of `|Σ_z e(...)|^{2k}`
  through the integrals `J_k(λ)`, Lemma 4 b for the power `2k` again, the properties a, b, c of
  `J_k`, giving display (5) and the factorization of its right side into the sums `𝔖_s`, written
  here with the geometric sums still in place of `min(2kP2^s+1, 1/⟨B_s μ⟩)`. LEAF, HARD.
* `leaf_karW_lemma1_J`: Lemma 1 applied to `J_k(0)` with `b = k`, p. 247, with the term `y = 0` split
  off, which costs the factor `4^k`. LEAF, MEDIUM.
* `leaf_karW_display7`: p. 246 bottom to p. 247, display (6) for each factor, Lemma 3 for
  `s = s_j` and the trivial bound otherwise, display (7) and the estimate of its product, with an
  allowance `2^{8k²}` for the factors `2^s`, `2^{2s}` and the sign of `μ` that the paper drops.
  LEAF, HARD.
* `karW_display8_combine`: the bookkeeping of p. 247 from the three bounds to display (8),
  `C0 = 16`. Pure real arithmetic.
* `karW_P2_le_sqrt`: `P2 ≤ P^{1/2}`, proved.
* `leaf_karW_display8_split`: the exact statement of `leaf_karW_display8`, proved from the pieces.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_karW_taylor_sum_bound

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- LEAF: display (5) of Karacuba p. 246 and the factorization that leads to display (6), class HARD.
For any real coefficients `B_j` and integers `k ≥ 1`, `M ≥ 0`:
`|W_1|^{4k²} ≤ (M+1)^{8k²-4k} J_k(0)² ∏_{s=1}^n Σ_{|μ|≤kM^s} |Σ_{|λ|≤kM^s} e(B_s λ μ)|`, where
`W_1 = Σ_{y,z≤M} e(c + Σ_j B_j (yz)^j)` and `J_k(0) = ∫_{[0,1]^n} |Σ_{y≤M} e(α_1 y + ... + α_n y^n)|^{2k}`.
Steps: Lemma 4 a with power `2k` over `y`; `|Σ_z e(Σ_j β_j z^j)|^{2k} = Σ_λ J_k(λ) e(β·λ)`; Lemma 4 b
with weights `J_k(λ)`, `Σ_λ J_k(λ) = (M+1)^{2k}`; `J_k(λ) ≤ J_k(0)`, `|λ_s| ≤ kM^s`. -/
theorem leaf_karW_display5 (n k M : ℕ) (hk : 1 ≤ k) (c : ℝ) (B : ℕ → ℝ) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (4 * k ^ 2)
      ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) *
        (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)) ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ := by
  sorry

/-- LEAF: Lemma 1 for `J_k(0)`, Karacuba p. 247 line 3 from below, class MEDIUM. With
`k = nl + [n(n+1)/4 + 1]`, `n ≥ 12`, `l ≥ 1`:
`J_k(0) ≤ 4^k D_l (M+1)^{2k - n(n+1)/2 + n(n+1)/2 (1-1/n)^l}`, `D_l = (20n)^{n(n+1)l/2}`.
The sum runs over `0 ≤ y ≤ M`; `|1 + S|^{2k} ≤ 2^{2k-1}(1 + |S|^{2k})` reduces it to `KarLemma1` with
`P = M` when `M ≥ 1`, and `M = 0` is direct. -/
theorem leaf_karW_lemma1_J (h1 : KarLemma1) (n l k M : ℕ) (hn : 12 ≤ n) (hl : 1 ≤ l)
    (hk : k = n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) :
    ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)
      ≤ 4 ^ k * (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        ((M : ℝ) + 1) ^ ((2 * k : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  sorry

/-- LEAF: displays (6) and (7) of Karacuba p. 246-247 and the estimate of the product (7), class HARD.
With `M = P2`, `B_s = f^{(s)}(a)/s!`, `ρ = min(c1/3, c3, c4)` and `k ≥ n(n+1)/4`:
`∏_{s=1}^n 𝔖_s ≤ 2^{8k²} (30k²)^n (9n)^n (log P)^n (P2+1)^{n(n+1)} P^{-ρ(s_1+...+s_r)}`, where
`𝔖_s = Σ_{|μ|≤kP2^s} |Σ_{|λ|≤kP2^s} e(B_s λ μ)|`. Steps: the geometric sum bound
`≤ min(2kP2^s+1, 1/(2⟨B_s μ⟩))`; for `s ∈ T` the approximation `B_s = 1/Q_s + θ_s/Q_s²` with
`P^{c2 s} - 1 ≤ Q_s ≤ P^{c2 s}` from `KarHyp` and Lemma 3; the bounds `Q_s^{-1} ≤ 2P^{-c3 s}`,
`P2^{-1} ≤ 2P^{-c1/3}`, `P2^{-2s}Q_s ≤ 2^{2s}P^{-c4 s}` from `n ≥ karN0`; for `s ∉ T` the trivial
bound `(2kP2^s+1)²`. The factor `2^{8k²}` covers the powers of `2` the paper drops. -/
theorem leaf_karW_display7 (h3 : KarLemma3) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          n * (n + 1) ≤ 4 * k →
          ∏ s ∈ Finset.Icc 1 n,
              ∑ μ ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖
            ≤ 2 ^ (8 * k ^ 2) * (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
              (Real.log (P : ℝ)) ^ n * ((karP2 c1 n P : ℝ) + 1) ^ (n * (n + 1)) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)))) := by
  sorry

/-- `P2 ≤ P^{1/2}`: the exponent of `karP2` is below `1/2` because `c1 < 1`. -/
theorem karW_P2_le_sqrt {c1 : ℝ} (hc1 : c1 < 1) (n P : ℕ) (hP : 1 ≤ (P : ℝ)) :
    (karP2 c1 n P : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := by
  unfold karP2
  refine le_trans (Nat.floor_le (by positivity)) ?_
  apply Real.rpow_le_rpow_of_exponent_le hP
  have : 0 ≤ 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) := by positivity
  linarith

/-- The bookkeeping of Karacuba p. 247 from the bounds (5), Lemma 1 and (7) to display (8), pure real
arithmetic: collect the powers of `M+1`, use `n(n+1)(1-1/n)^l ≤ x` and
`M + 1 ≤ 2P^{1/2}`, and take the `4k²`-th root; the constant `16` absorbs `2^{8k²+8k}`. -/
theorem karW_display8_combine (n l k M : ℕ) (P x Wn J S : ℝ) (hk : 1 ≤ k)
    (hnk : n * (n + 1) ≤ 4 * k) (hn : 1 ≤ n) (hP : 1 < P) (hM : (M : ℝ) ≤ P ^ ((1 : ℝ) / 2))
    (hW0 : 0 ≤ Wn) (hJ0 : 0 ≤ J) (hS0 : 0 ≤ S)
    (hA : Wn ^ (4 * k ^ 2) ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * J ^ 2 * S)
    (hB : J ≤ 4 ^ k * (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        ((M : ℝ) + 1) ^ ((2 * k : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l))
    (hC : S ≤ 2 ^ (8 * k ^ 2) * (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
        (Real.log P) ^ n * ((M : ℝ) + 1) ^ (n * (n + 1)) * P ^ (-x))
    (hx : ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ l ≤ x) :
    Wn ≤ 16 *
      ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
        (Real.log P) ^ n) ^ (1 / (4 * (k : ℝ) ^ 2)) *
      ((M : ℝ) + 1) ^ 2 * P ^ (-(x / (8 * (k : ℝ) ^ 2))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hP0 : 0 < P := by linarith
  have hlog : 0 ≤ Real.log P := (Real.log_pos hP).le
  set m : ℝ := (M : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; have := M.cast_nonneg (α := ℝ); linarith
  have hm0 : 0 < m := by linarith
  have hsq1 : 1 ≤ P ^ ((1 : ℝ) / 2) := Real.one_le_rpow hP.le (by norm_num)
  have hm2 : m ≤ 2 * P ^ ((1 : ℝ) / 2) := by rw [hm]; linarith
  set nn : ℝ := ((n * (n + 1) : ℕ) : ℝ) with hnn
  have hnn4 : nn ≤ 4 * k := by rw [hnn]; exact_mod_cast hnk
  have hnn0 : 0 ≤ nn := by positivity
  have hq0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
    linarith
  have hq1 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  set q : ℝ := (1 - 1 / (n : ℝ)) ^ l with hq
  have hqa : 0 ≤ q := pow_nonneg hq0 l
  have hqb : q ≤ 1 := pow_le_one₀ hq0 hq1
  set D : ℝ := (20 * n : ℝ) ^ (nn / 2 * l) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hD2 : D ^ 2 = (20 * (n : ℝ)) ^ (n * (n + 1) * l) := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
    congr 1; rw [hnn]; push_cast; ring
  set e : ℝ := (2 * k : ℝ) - nn / 2 + nn / 2 * q with he
  have hJ2 : J ^ 2 ≤ 16 ^ k * D ^ 2 * m ^ (2 * e) := by
    calc J ^ 2 ≤ (4 ^ k * D * m ^ e) ^ 2 := pow_le_pow_left₀ hJ0 hB 2
      _ = 16 ^ k * D ^ 2 * m ^ (2 * e) := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast (m ^ e), ← Real.rpow_mul hm0.le]
        have h16 : ((4 : ℝ) ^ k) ^ 2 = 16 ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h16]; congr 2; push_cast; ring
  set G : ℝ := (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n with hG
  have hG0 : 0 ≤ G := by positivity
  have hL0 : 0 ≤ (Real.log P) ^ n := pow_nonneg hlog n
  have hmain : Wn ^ (4 * k ^ 2) ≤ m ^ (8 * k ^ 2 - 4 * k) * (16 ^ k * D ^ 2 * m ^ (2 * e)) *
      (2 ^ (8 * k ^ 2) * G * (Real.log P) ^ n * m ^ (n * (n + 1)) * P ^ (-x)) := by
    refine hA.trans ?_
    have hC' : S ≤ 2 ^ (8 * k ^ 2) * G * (Real.log P) ^ n * m ^ (n * (n + 1)) * P ^ (-x) := by
      rw [hG]; simpa only [mul_assoc] using hC
    exact mul_le_mul (mul_le_mul_of_nonneg_left hJ2 (by positivity)) hC' hS0 (by positivity)
  have hmexp : m ^ (8 * k ^ 2 - 4 * k) * m ^ (2 * e) * m ^ (n * (n + 1))
      = m ^ (8 * k ^ 2) * m ^ (nn * q) := by
    rw [← Real.rpow_natCast m (8 * k ^ 2 - 4 * k), ← Real.rpow_natCast m (n * (n + 1)),
      ← Real.rpow_natCast m (8 * k ^ 2), ← Real.rpow_add hm0, ← Real.rpow_add hm0,
      ← Real.rpow_add hm0]
    congr 1
    rw [Nat.cast_sub (by nlinarith), he, hnn]; push_cast; ring
  have hmX : m ^ (nn * q) * P ^ (-x) ≤ 2 ^ (4 * k) * P ^ (-(x / 2)) := by
    have hX0 : 0 ≤ nn * q := mul_nonneg hnn0 hqa
    have hXn : nn * q ≤ 4 * k := le_trans (mul_le_of_le_one_right hnn0 hqb) hnn4
    have hXx : nn * q ≤ x := by rw [hnn, hq]; exact hx
    have h1 : m ^ (nn * q) ≤ 2 ^ (nn * q) * P ^ (nn * q / 2) := by
      calc m ^ (nn * q) ≤ (2 * P ^ ((1 : ℝ) / 2)) ^ (nn * q) :=
            Real.rpow_le_rpow hm0.le hm2 hX0
        _ = 2 ^ (nn * q) * P ^ (nn * q / 2) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hP0.le]
            congr 2; ring
    have h2 : (2 : ℝ) ^ (nn * q) ≤ 2 ^ (4 * k) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast; linarith
    have h3 : P ^ (nn * q / 2) ≤ P ^ (x / 2) :=
      Real.rpow_le_rpow_of_exponent_le hP.le (by linarith)
    have h4 : P ^ (x / 2) * P ^ (-x) = P ^ (-(x / 2)) := by
      rw [← Real.rpow_add hP0]; congr 1; ring
    calc m ^ (nn * q) * P ^ (-x) ≤ (2 ^ (nn * q) * P ^ (nn * q / 2)) * P ^ (-x) := by
          gcongr
      _ ≤ (2 ^ (4 * k) * P ^ (x / 2)) * P ^ (-x) := by gcongr
      _ = 2 ^ (4 * k) * P ^ (-(x / 2)) := by rw [mul_assoc, h4]
  set Bp : ℝ := (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
      (Real.log P) ^ n with hBp
  have hBp0 : 0 ≤ Bp := by
    rw [hBp]; exact mul_nonneg (by positivity) hL0
  have hconst : (16 : ℝ) ^ k * 2 ^ (8 * k ^ 2) * 2 ^ (4 * k) ≤ 16 ^ (4 * k ^ 2) := by
    have e1 : (16 : ℝ) ^ k * 2 ^ (8 * k ^ 2) * 2 ^ (4 * k) = 2 ^ (8 * k + 8 * k ^ 2) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]; ring_nf
    have e2 : (16 : ℝ) ^ (4 * k ^ 2) = 2 ^ (16 * k ^ 2) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
    rw [e1, e2]
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  have hstep : Wn ^ (4 * k ^ 2) ≤ 16 ^ (4 * k ^ 2) * Bp * m ^ (8 * k ^ 2) * P ^ (-(x / 2)) := by
    refine hmain.trans ?_
    have hre : m ^ (8 * k ^ 2 - 4 * k) * (16 ^ k * D ^ 2 * m ^ (2 * e)) *
        (2 ^ (8 * k ^ 2) * G * (Real.log P) ^ n * m ^ (n * (n + 1)) * P ^ (-x))
        = (16 ^ k * 2 ^ (8 * k ^ 2)) * (G * D ^ 2 * (Real.log P) ^ n) *
          (m ^ (8 * k ^ 2 - 4 * k) * m ^ (2 * e) * m ^ (n * (n + 1))) * P ^ (-x) := by ring
    have hBp' : G * D ^ 2 * (Real.log P) ^ n = Bp := by rw [hD2, hG, hBp]
    rw [hre, hmexp, hBp']
    have hm8 : 0 ≤ m ^ (8 * k ^ 2) := by positivity
    calc 16 ^ k * 2 ^ (8 * k ^ 2) * Bp * (m ^ (8 * k ^ 2) * m ^ (nn * q)) * P ^ (-x)
        = 16 ^ k * 2 ^ (8 * k ^ 2) * Bp * m ^ (8 * k ^ 2) * (m ^ (nn * q) * P ^ (-x)) := by ring
      _ ≤ 16 ^ k * 2 ^ (8 * k ^ 2) * Bp * m ^ (8 * k ^ 2) * (2 ^ (4 * k) * P ^ (-(x / 2))) := by
          gcongr
      _ = (16 ^ k * 2 ^ (8 * k ^ 2) * 2 ^ (4 * k)) * Bp * m ^ (8 * k ^ 2) * P ^ (-(x / 2)) := by
          ring
      _ ≤ 16 ^ (4 * k ^ 2) * Bp * m ^ (8 * k ^ 2) * P ^ (-(x / 2)) := by gcongr
  have hK : (4 * k ^ 2 : ℕ) ≠ 0 := by positivity
  have hKr : ((4 * k ^ 2 : ℕ) : ℝ) = 4 * (k : ℝ) ^ 2 := by push_cast; ring
  have hK0 : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
  have htarget : (16 * Bp ^ (1 / (4 * (k : ℝ) ^ 2)) * m ^ 2 * P ^ (-(x / (8 * (k : ℝ) ^ 2)))) ^
      (4 * k ^ 2) = 16 ^ (4 * k ^ 2) * Bp * m ^ (8 * k ^ 2) * P ^ (-(x / 2)) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul]
    rw [← Real.rpow_natCast (Bp ^ (1 / (4 * (k : ℝ) ^ 2))), ← Real.rpow_mul hBp0, hKr,
      ← Real.rpow_natCast (P ^ (-(x / (8 * (k : ℝ) ^ 2)))), ← Real.rpow_mul hP0.le, hKr]
    have ea : 1 / (4 * (k : ℝ) ^ 2) * (4 * (k : ℝ) ^ 2) = 1 := by field_simp
    have eb : -(x / (8 * (k : ℝ) ^ 2)) * (4 * (k : ℝ) ^ 2) = -(x / 2) := by field_simp; ring
    rw [ea, eb, Real.rpow_one]
    ring_nf
  have htn : 0 ≤ 16 * Bp ^ (1 / (4 * (k : ℝ) ^ 2)) * m ^ 2 * P ^ (-(x / (8 * (k : ℝ) ^ 2))) := by
    have := Real.rpow_nonneg hBp0 (1 / (4 * (k : ℝ) ^ 2))
    positivity
  rw [← htarget] at hstep
  exact (pow_le_pow_iff_left₀ hW0 htn hK).1 hstep

/-- The split of `leaf_karW_display8`: its exact statement, from the leaves above, `C0 = 16`. -/
theorem leaf_karW_display8_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
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
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨cc0, hcc0, h7⟩ := leaf_karW_display7 h3 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨16, cc0, by norm_num, hcc0, ?_⟩
  intro N P n f T a l hP hn hn0 hbig hH ha haP hl hlo _hhi
  have hn12r : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn0
  have hn12 : 12 ≤ n := by exact_mod_cast hn12r
  set k : ℕ := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hk
  have hfl : n * (n + 1) ≤ 4 * ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ := by
    have h : ((n * (n + 1) : ℕ) : ℝ) / 4 + 1 < (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    generalize ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ = F at h ⊢
    have h' : ((n * (n + 1) : ℕ) : ℝ) ≤ ((4 * F : ℕ) : ℝ) := by
      rw [Nat.cast_mul 4 F]; push_cast at h ⊢; linarith
    exact_mod_cast h'
  have hnk : n * (n + 1) ≤ 4 * k := by rw [hk]; nlinarith
  have hk1 : 1 ≤ k := by nlinarith
  have hP1 : (1 : ℝ) < P := by
    refine lt_of_lt_of_le ?_ hbig
    rw [← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    positivity
  have hA := leaf_karW_display5 n k (karP2 c1 n P) hk1 (f (a : ℝ))
    (fun j => iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ))
  have hB := leaf_karW_lemma1_J h1 n l k (karP2 c1 n P) hn12 hl hk
  have hC := h7 N P n f T a k hP hn hn0 hbig hH ha haP hnk
  have hJ0 : 0 ≤ ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      ‖∑ y ∈ Finset.range (karP2 c1 n P + 1),
        eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k) :=
    MeasureTheory.setIntegral_nonneg (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun _ _ => by positivity)
  have hcomb := karW_display8_combine n l k (karP2 c1 n P) (P : ℝ)
    (min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ))) _ _ _ hk1 hnk (by omega) hP1
    (karW_P2_le_sqrt hc11 n P hP1.le) (norm_nonneg _) hJ0
    (Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))) hA hB hC hlo
  simpa using hcomb

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
