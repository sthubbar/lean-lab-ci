/-
Split of the sealed statement `leaf_small_case` of `LeanLab.ExceptionalSet.KaracubaSplit`,
the case `2 ≤ n < n0` of Karacuba's Theorem 1, chapter I section 2, p. 244, proved on
p. 248 of the source printed in the lab under `papers/`.

The statement being split, unchanged, is

  theorem leaf_small_case (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → ... → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4)

Shape of the proof on p. 248. Put `δ = c1 - c4/2 > 0` and `L = [P^δ]`. Two facts make a
block `[a, a+m)` with `m ≤ L` inside `[N, N+P]` tame:
* Taylor's formula to order `n` at the left end of the block has remainder at most
  `P^{-c1(n+1)} m^{n+1} ≤ P^{-(n+1)c4/2}`, which the saving swallows;
* the `s`-th Taylor coefficient has size between `P^{-c2 s}` and `P^{-c3 s}`, so the
  denominator of its rational approximation is `q_s ⪅ P^{c2 s} < L^s`, because
  `c2 + c4 < c1`, and Karacuba's Lemma 2 at that level saves the factor `L^{-ρ}` with
  `ρ = τ/(3 n² l)`; the small case `n < n0 ≤ 1/√c1` keeps `n² l` bounded, so `ρ` is
  bounded away from `0` in terms of the `c`'s alone.
That is `leaf_small_block_sum_bound`. Splitting `[N, N+P₁)` into `P₁/L + 1` such blocks and
multiplying out is `leaf_small_bookkeeping` and `leaf_block_length_ge`; the assembly below
does the partition, the count and the constants.

`sorry` sits on the one analytic leaf `leaf_small_block_sum_bound` alone; the two
bookkeeping leaves are proved below. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF. The short block estimate: the case `2 ≤ n < n0` of Theorem 1 applied to a block
`[a, a+m)` of length `m ≤ [P^(c1 - c4/2)]` lying inside `[N, N+P]`, in the form
`|Σ_{x∈[a,a+m)} e(f x)| ≤ A0 m^(1-ρ)` with `A0, ρ > 0` and `ρ < 1` depending on
`c0, ..., c4` only. This is the step of p. 248: Taylor's formula to order `n` on the block,
the removal of the remainder, the rational approximation of the `s`-th coefficient with
`s ∈ T`, `2 ≤ s ≤ n`, the denominator bound `q_s ⪅ P^(c2 s) < m^s` coming from
`c2 + c4 < c1`, and Lemma 2 at that level, whose saving `ρ = τ/(3 n² l)` is bounded away
from `0` because `n < n0 ≤ 1/√c1`. -/
theorem leaf_small_block_sum_bound (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ) := by
  sorry

/-- LEAF. The bookkeeping inequality of the sum over blocks: for a block length `L` with
`L ≤ P^A` and `P^A/2 ≤ L`, and `P` above the threshold `exp(8 (log 2 / A) / min (Aρ) (1-A) n²)`,
the count `P/L + 1` of blocks times the per block factor `L^(1-ρ)` stays below
`P^(1 - γ/n²)`. Elementary powers of `P`: `P L^(-ρ) ≤ 2 P^(1-Aρ)` and
`L^(1-ρ) ≤ P^(A(1-ρ)) ≤ P^(1-γ/n²)` since `γ ≤ min (Aρ) (1-A)/2`, and the constant `2` is
paid for by `P` being large. -/
theorem leaf_small_bookkeeping :
    ∀ A ρ γ : ℝ, 0 < A → A < 1 → 0 < ρ → ρ ≤ 1 → 0 < γ →
      γ ≤ min (A * ρ) (1 - A) / 2 →
      ∀ n P L : ℕ, 2 ≤ n → 0 < P →
        Real.exp (8 * (Real.log 2 / A) / min (A * ρ) (1 - A) * (n : ℝ) ^ 2) ≤ (P : ℝ) →
        (L : ℝ) ≤ (P : ℝ) ^ A → (P : ℝ) ^ A / 2 ≤ (L : ℝ) → 1 ≤ L →
        ((P : ℝ) / (L : ℝ) + 1) * (L : ℝ) ^ (1 - ρ) ≤ (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := by
  intro A ρ γ hA hA1 hρ hρ1 hγ hγM n P L hn hP hbig hLA hLA2 hL1
  set M := min (A * ρ) (1 - A) with hMdef
  have hMpos : 0 < M := lt_min (mul_pos hA hρ) (by linarith)
  have hMAρ : M ≤ A * ρ := min_le_left _ _
  have hMA : M ≤ 1 - A := min_le_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPr : (1 : ℝ) ≤ (P : ℝ) := by
    have hgt : (1 : ℝ) < Real.exp (8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2) := by
      rw [← Real.exp_zero]
      apply Real.exp_lt_exp.2
      have hpos : 0 < 8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2 := by
        have : 0 < Real.log 2 / A := div_pos hl2 hA
        positivity
      linarith
    linarith
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hPApos : (0 : ℝ) < (P : ℝ) ^ A := Real.rpow_pos_of_pos hPpos A
  have hPAle : (P : ℝ) ^ A ≤ (P : ℝ) := by
    calc (P : ℝ) ^ A ≤ (P : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hPr hA1.le
      _ = (P : ℝ) := Real.rpow_one _
  have hlogbig : 8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2 ≤ Real.log (P : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2)) hbig
    rwa [Real.log_exp] at h
  -- `Aρ/M ≥ 1`, hence `4 ≤ P^(Aρ/2)`
  have hratio : 1 ≤ ρ / M := by
    rw [le_div_iff₀ hMpos]
    nlinarith
  have hprod : 2 * Real.log 2 ≤ (A * ρ / 2) * (8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2) := by
    have hEq : (A * ρ / 2) * (8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2)
        = 4 * Real.log 2 * (ρ / M) * (n : ℝ) ^ 2 := by
      field_simp
      ring
    rw [hEq]
    set x := ρ / M * (n : ℝ) ^ 2 with hxdef
    have hx1 : 1 ≤ x := by
      rw [hxdef]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ρ / M * (n : ℝ) ^ 2 := mul_le_mul hratio hn2 (by norm_num) (by linarith)
    nlinarith [hl2, hx1]
  have hexp4 : 4 ≤ (P : ℝ) ^ (A * ρ / 2) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ = Real.exp (2 * Real.log 2) := by rw [hlog4]
      _ ≤ Real.exp (Real.log (P : ℝ) * (A * ρ / 2)) := by
          apply Real.exp_le_exp.2
          have h := mul_le_mul_of_nonneg_left hlogbig (le_of_lt (by positivity : (0:ℝ) < A * ρ / 2))
          linarith
      _ = (P : ℝ) ^ (A * ρ / 2) := (Real.rpow_def_of_pos hPpos _).symm
  have hLpow : (L : ℝ) ^ (1 - ρ) ≤ (P : ℝ) ^ (A * (1 - ρ)) := by
    have hexp : 0 ≤ 1 - ρ := by linarith
    calc (L : ℝ) ^ (1 - ρ) ≤ ((P : ℝ) ^ A) ^ (1 - ρ) :=
          Real.rpow_le_rpow (by linarith) hLA hexp
      _ = (P : ℝ) ^ (A * (1 - ρ)) := (Real.rpow_mul hPpos.le A (1 - ρ)).symm
  have hPL : (P : ℝ) / (L : ℝ) ≤ 2 * (P : ℝ) ^ (1 - A) := by
    have h1 : (P : ℝ) / (L : ℝ) ≤ (P : ℝ) / ((P : ℝ) ^ A / 2) :=
      div_le_div_of_nonneg_left hPpos.le (by linarith) hLA2
    have h2 : (P : ℝ) / ((P : ℝ) ^ A / 2) = 2 * (P : ℝ) ^ (1 - A) := by
      rw [Real.rpow_sub hPpos, Real.rpow_one]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ 2 * (P : ℝ) ^ (1 - A) := by
    have h3 : (1 : ℝ) ≤ (P : ℝ) ^ (1 - A) := by
      calc (1 : ℝ) = (P : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (P : ℝ) ^ (1 - A) := Real.rpow_le_rpow_of_exponent_le hPr (by linarith)
    linarith
  have hsum : (P : ℝ) / (L : ℝ) + 1 ≤ 4 * (P : ℝ) ^ (1 - A) := by linarith
  have hkey : (P : ℝ) ^ (1 - A) * (P : ℝ) ^ (A * (1 - ρ)) = (P : ℝ) ^ (1 - A * ρ) := by
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hγn : γ / (n : ℝ) ^ 2 ≤ A * ρ / 2 := by
    have hg : γ ≤ A * ρ / 2 := by
      have h1 : γ ≤ min (A * ρ) (1 - A) / 2 := hγM
      have h2 : min (A * ρ) (1 - A) ≤ A * ρ := min_le_left _ _
      linarith
    calc γ / (n : ℝ) ^ 2 ≤ γ / 1 :=
          div_le_div_of_nonneg_left hγ.le (by norm_num) hn2
      _ = γ := by ring
      _ ≤ A * ρ / 2 := hg
  calc ((P : ℝ) / (L : ℝ) + 1) * (L : ℝ) ^ (1 - ρ)
      ≤ (4 * (P : ℝ) ^ (1 - A)) * (P : ℝ) ^ (A * (1 - ρ)) :=
        mul_le_mul hsum hLpow (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = 4 * ((P : ℝ) ^ (1 - A) * (P : ℝ) ^ (A * (1 - ρ))) := by ring
    _ = 4 * (P : ℝ) ^ (1 - A * ρ) := by rw [hkey]
    _ ≤ (P : ℝ) ^ (A * ρ / 2) * (P : ℝ) ^ (1 - A * ρ) :=
        mul_le_mul_of_nonneg_right hexp4 (Real.rpow_nonneg hPpos.le _)
    _ = (P : ℝ) ^ (A * ρ / 2 + (1 - A * ρ)) := by rw [← Real.rpow_add hPpos]
    _ ≤ (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hPr
        linarith


/-- LEAF. The block length is at most the real power and, once `P^A ≥ 2`, at least half of
it: `[P^A] ≥ P^A - 1 ≥ P^A/2`. The hypothesis `exp (log 2 / A) ≤ P` is exactly `P^A ≥ 2`. -/
theorem leaf_block_length_ge :
    ∀ A : ℝ, 0 < A → A ≤ 1 → ∀ P : ℕ,
      Real.exp (Real.log 2 / A) ≤ (P : ℝ) →
      (P : ℝ) ^ A / 2 ≤ ((⌊(P : ℝ) ^ A⌋₊ : ℕ) : ℝ) := by
  intro A hA0 _ P hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexpgt : (1 : ℝ) < Real.exp (Real.log 2 / A) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (div_pos hlog2 hA0)
  have hP1 : (1 : ℝ) < (P : ℝ) := lt_of_lt_of_le hexpgt hP
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hlogP : Real.log 2 / A ≤ Real.log (P : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.log 2 / A)) hP
    rwa [Real.log_exp] at h
  have hlogP2 : Real.log 2 ≤ A * Real.log (P : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogP hA0.le
    rwa [mul_div_cancel₀ (Real.log 2) hA0.ne'] at h
  have hPA : (2 : ℝ) ≤ (P : ℝ) ^ A := by
    rw [Real.rpow_def_of_pos hPpos]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (P : ℝ) * A) := Real.exp_le_exp.2 (by linarith)
  have hfloor : (P : ℝ) ^ A - 1 < ((⌊(P : ℝ) ^ A⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  linarith

/-! ### Proved assembly -/

/-- Splitting a sum over `[N, N+P₁)` inside `[S, E]` into blocks of length at most `L`, each
with the bound `C m^(1-ρ)` of the leaves, costs the factor `P₁/L + 1`. -/
private lemma block_partition_bound (g : ℕ → ℂ) (C ρ : ℝ) (L : ℕ) (hL : 0 < L) (hC : 0 ≤ C)
    (hρ1 : ρ < 1) (S E : ℕ)
    (hblk : ∀ a m : ℕ, S ≤ a → a + m ≤ E → 1 ≤ m → m ≤ L →
      ‖∑ x ∈ Finset.Ico a (a + m), g x‖ ≤ C * (m : ℝ) ^ (1 - ρ)) :
    ∀ (P₁ N : ℕ), S ≤ N → N + P₁ ≤ E →
      ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤
        ((P₁ : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hexp : 0 ≤ 1 - ρ := by linarith
  have hpow0 : (0 : ℝ) ≤ (L : ℝ) ^ (1 - ρ) := Real.rpow_nonneg hLr.le _
  have hW0 : (0 : ℝ) ≤ C * (L : ℝ) ^ (1 - ρ) := mul_nonneg hC hpow0
  intro P₁
  induction P₁ using Nat.strong_induction_on with
  | _ P₁ ih =>
    intro N hSN hNE
    rcases Nat.eq_zero_or_pos P₁ with h0 | hpos
    · subst h0
      have hz : ∑ x ∈ Finset.Ico N (N + 0), g x = 0 := by simp
      rw [hz, norm_zero]
      have : (0 : ℝ) ≤ ((0 : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) :=
        mul_nonneg (by positivity) hW0
      simpa using this
    · rcases Nat.lt_or_ge P₁ L with hPL | hLP
      · have hP1L : P₁ ≤ L := by omega
        have hb := hblk N P₁ hSN hNE hpos hP1L
        refine hb.trans ?_
        have hrp : ((P₁ : ℝ)) ^ (1 - ρ) ≤ (L : ℝ) ^ (1 - ρ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hP1L) hexp
        have hone : (1 : ℝ) ≤ (P₁ : ℝ) / (L : ℝ) + 1 := by
          have hq : (0 : ℝ) ≤ (P₁ : ℝ) / (L : ℝ) := by positivity
          linarith
        calc C * (P₁ : ℝ) ^ (1 - ρ) ≤ C * (L : ℝ) ^ (1 - ρ) :=
              mul_le_mul_of_nonneg_left hrp hC
          _ = 1 * (C * (L : ℝ) ^ (1 - ρ)) := by ring
          _ ≤ ((P₁ : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) :=
              mul_le_mul_of_nonneg_right hone hW0
      · have hLP' : L ≤ P₁ := hLP
        have hsplit : ∑ x ∈ Finset.Ico N (N + P₁), g x
            = ∑ x ∈ Finset.Ico N (N + L), g x + ∑ x ∈ Finset.Ico (N + L) (N + P₁), g x := by
          have h := Finset.sum_Ico_consecutive g (m := N) (n := N + L) (k := N + P₁)
            (by omega) (by omega)
          exact h.symm
        rw [hsplit]
        have hfirst : ‖∑ x ∈ Finset.Ico N (N + L), g x‖ ≤ C * (L : ℝ) ^ (1 - ρ) :=
          hblk N L hSN (by omega) (by omega) le_rfl
        have htail : ‖∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖ ≤
            (((P₁ - L : ℕ) : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) := by
          have hidx : (N + L) + (P₁ - L) = N + P₁ := by omega
          have h := ih (P₁ - L) (by omega) (N + L) (by omega) (by omega)
          rw [hidx] at h
          exact h
        have hcast : ((P₁ - L : ℕ) : ℝ) = (P₁ : ℝ) - (L : ℝ) := by
          push_cast [Nat.cast_sub hLP']
          ring
        have harith : ((P₁ - L : ℕ) : ℝ) / (L : ℝ) + 1 = (P₁ : ℝ) / (L : ℝ) := by
          rw [hcast]
          field_simp
          ring
        have hsum : C * (L : ℝ) ^ (1 - ρ) +
            (((P₁ - L : ℕ) : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) =
            ((P₁ : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) := by
          rw [harith]
          ring
        refine (norm_add_le _ _).trans ?_
        calc ‖∑ x ∈ Finset.Ico N (N + L), g x‖ + ‖∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖
            ≤ C * (L : ℝ) ^ (1 - ρ) +
              (((P₁ - L : ℕ) : ℝ) / (L : ℝ) + 1) * (C * (L : ℝ) ^ (1 - ρ)) :=
              add_le_add hfirst htail
          _ = _ := hsum

/-- The charged statement, from the three leaves. -/
theorem leaf_small_case_split (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨A0, ρ, hA0, hρ, hρ1, hblk⟩ :=
    leaf_small_block_sum_bound h2 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  have hApos : 0 < c1 - c4 / 2 := by linarith
  have hAlt : c1 - c4 / 2 < 1 := by linarith
  have hl2 : 0 < Real.log 2 / (c1 - c4 / 2) :=
    div_pos (Real.log_pos (by norm_num)) hApos
  have hMpos : 0 < min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) :=
    lt_min (mul_pos hApos hρ) (by linarith)
  have hMle1 : min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) ≤ 1 :=
    (min_le_right _ _).trans (by linarith)
  have hγpos : 0 < min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) / 2 :=
    div_pos hMpos two_pos
  have hccpos : 0 < 8 * (Real.log 2 / (c1 - c4 / 2)) /
      min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) :=
    div_pos (mul_pos (by norm_num) hl2) hMpos
  refine ⟨A0, min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) / 2,
    8 * (Real.log 2 / (c1 - c4 / 2)) / min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)),
    hA0, hγpos, hccpos, ?_⟩
  intro N P n hP hn hpred hbig f T hH P₁ hP₁ hP₁P
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- the threshold of the leaves is below the hypothesis on `P`
  have hcc_ge : Real.log 2 / (c1 - c4 / 2) ≤
      8 * (Real.log 2 / (c1 - c4 / 2)) /
        min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) * (n : ℝ) ^ 2 := by
    have hM1 : Real.log 2 / (c1 - c4 / 2) * min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2))
        ≤ Real.log 2 / (c1 - c4 / 2) := by nlinarith [hMle1, hl2.le]
    have hstep : Real.log 2 / (c1 - c4 / 2) ≤
        8 * (Real.log 2 / (c1 - c4 / 2)) * (n : ℝ) ^ 2 := by
      nlinarith [hn2, hl2.le]
    have hq : Real.log 2 / (c1 - c4 / 2) ≤
        (8 * (Real.log 2 / (c1 - c4 / 2)) * (n : ℝ) ^ 2) /
          min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) := by
      rw [le_div_iff₀ hMpos]
      nlinarith [hMle1, hl2.le, hstep]
    calc Real.log 2 / (c1 - c4 / 2)
        ≤ (8 * (Real.log 2 / (c1 - c4 / 2)) * (n : ℝ) ^ 2) /
            min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) := hq
      _ = 8 * (Real.log 2 / (c1 - c4 / 2)) /
            min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) * (n : ℝ) ^ 2 := by ring
  have hbig2 : Real.exp (Real.log 2 / (c1 - c4 / 2)) ≤ (P : ℝ) :=
    (Real.exp_le_exp.2 hcc_ge).trans hbig
  -- hence `P^(c1-c4/2) ≥ 2`
  have hPA2 : (2 : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) := by
    have hlog : Real.log 2 / (c1 - c4 / 2) ≤ Real.log (P : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hbig2
      simpa using h
    have hmul : Real.log 2 ≤ (c1 - c4 / 2) * Real.log (P : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hlog hApos.le
      have h2 : (c1 - c4 / 2) * (Real.log 2 / (c1 - c4 / 2)) = Real.log 2 := by
        field_simp
        exact div_self (by linarith : c1 * 2 - c4 ≠ 0)
      rwa [h2] at h
    rw [Real.rpow_def_of_pos hPr]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (P : ℝ) * (c1 - c4 / 2)) := by
          apply Real.exp_le_exp.2
          linarith
  -- the block length
  set L : ℕ := ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ with hLdef
  have hLA : (L : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) :=
    Nat.floor_le (Real.rpow_nonneg hPr.le _)
  have hLA2 : (P : ℝ) ^ (c1 - c4 / 2) / 2 ≤ (L : ℝ) :=
    leaf_block_length_ge (c1 - c4 / 2) hApos hAlt.le P hbig2
  have hL1r : (1 : ℝ) ≤ (L : ℝ) := le_trans (by linarith) hLA2
  have hLpos : 0 < L := by exact_mod_cast hL1r
  have hL1 : 1 ≤ L := hLpos
  -- every block inside `[N, N+P]` is short
  have hblk' : ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m → m ≤ L →
      ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ) := by
    intro a m ha ham hm hmL
    exact hblk N P n hP hn hpred f T hH a m ha ham hm hmL
  have hpart := block_partition_bound (fun x => eC (f x)) A0 ρ L hLpos hA0.le hρ1 N (N + P)
    hblk' P₁ N le_rfl (by omega)
  have hbook := leaf_small_bookkeeping (c1 - c4 / 2) ρ
    (min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) / 2) hApos hAlt hρ hρ1.le hγpos
    (le_refl _) n P L hn hP hbig hLA hLA2 hL1
  have hW0 : (0 : ℝ) ≤ A0 * (L : ℝ) ^ (1 - ρ) :=
    mul_nonneg hA0.le (Real.rpow_nonneg (by positivity) _)
  have hmono : ((P₁ : ℝ) / (L : ℝ) + 1) ≤ ((P : ℝ) / (L : ℝ) + 1) := by
    have hle : (P₁ : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP₁P
    have hq : (P₁ : ℝ) / (L : ℝ) ≤ (P : ℝ) / (L : ℝ) :=
      div_le_div_of_nonneg_right hle (by positivity)
    linarith
  refine hpart.trans ?_
  calc ((P₁ : ℝ) / (L : ℝ) + 1) * (A0 * (L : ℝ) ^ (1 - ρ))
      ≤ ((P : ℝ) / (L : ℝ) + 1) * (A0 * (L : ℝ) ^ (1 - ρ)) :=
        mul_le_mul_of_nonneg_right hmono hW0
    _ = A0 * (((P : ℝ) / (L : ℝ) + 1) * (L : ℝ) ^ (1 - ρ)) := by ring
    _ ≤ A0 * (P : ℝ) ^ (1 - min ((c1 - c4 / 2) * ρ) (1 - (c1 - c4 / 2)) / 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbook hA0.le

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
