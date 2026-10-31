import LeanLab.ChenDoubleSieve.Lemma41Err

/-!
# Wu 2004 Lemma 4.1 for `σ ∈ U_k(N)`, the remainder as a power saving

P0036 J. Wu 2004, Section 3 and Lemma 4.1. Unit U-5403, CLOUD 20261019T1014Z-cloud22.
AI wrote the Lean code.

Wu's `σ = π_{[V₁/Δ, V₁)} * ⋯ * π_{[V_i/Δ, V_i)}`, `π_{[Y, Z)}` the indicator of the primes of
`[Y, Z)` coprime to `N`, so `Σ_d σ(d) f(d) = Σ_{p₁, …, p_i} f(p₁⋯p_i)` over `p_j` prime,
`V_j/Δ ≤ p_j < V_j`, `(p_j, N) = 1`. We write that sum over the tuples `T` directly.
`lemma41_Uk`: for `A ⊆ {0, …, N}`, `1 < Δ ≤ 3/2`, `V_j ≥ 3` and levels `0 < W ≤ w(t) ≤ z(t)`,
`2 Σ_t S(A_{d_t}; P(d_t N), z(t)) ≤ Σ_t (Ω₁ - Ω₂ + Ω₃) + i (N/W + 2^i ∏ V_j)`, `d_t = p₁⋯p_i`.
With Wu's `w(t) = d̲^{1/s'} ≥ W_k^{1/10} = N^{δ^{1+k}/10}`, from `d̲ = Q/d ≥ V_i ≥ W_k` by (3.1),
and `∏ V_j ≤ Q = N^{1/2-δ}`, the remainder is `≤ k (N^{1-δ^{1+k}/10} + 2^k N^{1/2})`, Wu's
`O_{δ,k}(N^{1-η})`. The bound `Σ_t 1/d_t ≤ ∏ (Δ - 1 + Δ/V_j) ≤ 1` used here is the upper half of
Wu's (3.5) and needs no prime number theorem.
Binary Goldbach is OPEN.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu41

/-- The primes `p` with `a ≤ p < b`, `(p, N) = 1`. -/
def Pset (N : ℕ) (a b : ℝ) : Finset ℕ :=
  {p ∈ range ⌈b⌉₊ | p.Prime ∧ a ≤ p ∧ (p : ℝ) < b ∧ p.Coprime N}

lemma mem_Pset {N : ℕ} {a b : ℝ} {p : ℕ} :
    p ∈ Pset N a b ↔ p.Prime ∧ a ≤ p ∧ (p : ℝ) < b ∧ p.Coprime N := by
  unfold Pset
  simp only [mem_filter, mem_range, and_iff_right_iff_imp]
  rintro ⟨-, -, hb, -⟩
  exact Nat.lt_ceil.mpr hb

/-- Wu's tuples `(p₁, …, p_i)` for `σ = π_{[V₁/Δ, V₁)} * ⋯ * π_{[V_i/Δ, V_i)}`. -/
def Tset (N i : ℕ) (V : Fin i → ℝ) (Δ : ℝ) : Finset (Fin i → ℕ) :=
  Fintype.piFinset fun j => Pset N (V j / Δ) (V j)

/-- `#{p ∈ [V/Δ, V)} ≤ V - V/Δ + 1`. -/
lemma card_Pset_le (N : ℕ) {V Δ : ℝ} (hV : 0 ≤ V) (hΔ : 1 ≤ Δ) :
    (#(Pset N (V / Δ) V) : ℝ) ≤ V - V / Δ + 1 := by
  have hsub : Pset N (V / Δ) V ⊆ Ico ⌈V / Δ⌉₊ ⌈V⌉₊ := by
    intro p hp
    obtain ⟨-, h1, h2, -⟩ := mem_Pset.1 hp
    exact mem_Ico.2 ⟨Nat.ceil_le.2 h1, Nat.lt_ceil.2 h2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Ico] at h1
  have hVΔ : 0 ≤ V / Δ := div_nonneg hV (by linarith)
  have h2 : (⌈V⌉₊ : ℝ) < V + 1 := Nat.ceil_lt_add_one hV
  have h3 : V / Δ ≤ (⌈V / Δ⌉₊ : ℝ) := Nat.le_ceil _
  have h5 : (#(Pset N (V / Δ) V) : ℝ) ≤ ((⌈V⌉₊ - ⌈V / Δ⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
  have h6 : V / Δ ≤ V := div_le_self hV hΔ
  rcases le_total ⌈V / Δ⌉₊ ⌈V⌉₊ with h | h
  · rw [Nat.cast_sub h] at h5; linarith
  · rw [Nat.sub_eq_zero_of_le h] at h5; push_cast at h5; linarith

/-- `Σ_{p ∈ [V/Δ, V)} 1/p ≤ Δ - 1 + Δ/V`. -/
lemma sum_inv_Pset_le (N : ℕ) {V Δ : ℝ} (hV : 0 < V) (hΔ : 1 ≤ Δ) :
    ∑ p ∈ Pset N (V / Δ) V, (1 / (p : ℝ)) ≤ Δ - 1 + Δ / V := by
  have hVΔ : 0 < V / Δ := div_pos hV (by linarith)
  have hterm : ∀ p ∈ Pset N (V / Δ) V, 1 / (p : ℝ) ≤ Δ / V := by
    intro p hp
    obtain ⟨-, h1, -, -⟩ := mem_Pset.1 hp
    rw [div_le_div_iff₀ (lt_of_lt_of_le hVΔ h1) hV, one_mul]
    rw [div_le_iff₀ (by linarith)] at h1
    linarith
  calc ∑ p ∈ Pset N (V / Δ) V, (1 / (p : ℝ)) ≤ ∑ p ∈ Pset N (V / Δ) V, Δ / V :=
        sum_le_sum hterm
    _ = (#(Pset N (V / Δ) V) : ℝ) * (Δ / V) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (V - V / Δ + 1) * (Δ / V) :=
        mul_le_mul_of_nonneg_right (card_Pset_le N hV.le hΔ) (by positivity)
    _ = Δ - 1 + Δ / V := by field_simp

/-- `ω(p₁⋯p_i) ≤ i` for primes `p_j`. -/
lemma card_primeFactors_prod_le {i : ℕ} (t : Fin i → ℕ) (ht : ∀ j, (t j).Prime) :
    #(∏ j, t j).primeFactors ≤ i := by
  have key : ∀ s : Finset (Fin i), #(∏ j ∈ s, t j).primeFactors ≤ #s := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [prod_insert hj, Nat.primeFactors_mul (ht j).ne_zero
        (prod_ne_zero_iff.2 fun j _ => (ht j).ne_zero), card_insert_of_notMem hj]
      calc #((t j).primeFactors ∪ (∏ j ∈ s, t j).primeFactors)
          ≤ #(t j).primeFactors + #(∏ j ∈ s, t j).primeFactors := card_union_le _ _
        _ ≤ 1 + #s := by rw [(ht j).primeFactors, card_singleton]; omega
        _ = #s + 1 := by ring
  simpa using key univ

/-- `Σ_{t ∈ T} 1/(p₁⋯p_i) ≤ ∏_j (Δ - 1 + Δ/V_j)`. -/
lemma sum_inv_T_le (N i : ℕ) (V : Fin i → ℝ) {Δ : ℝ} (hV : ∀ j, 0 < V j) (hΔ : 1 ≤ Δ) :
    ∑ t ∈ Tset N i V Δ, (1 / ((∏ j, t j : ℕ) : ℝ)) ≤ ∏ j, (Δ - 1 + Δ / V j) := by
  unfold Tset
  have : ∑ t ∈ Fintype.piFinset (fun j => Pset N (V j / Δ) (V j)), (1 / ((∏ j, t j : ℕ) : ℝ))
      = ∏ j, ∑ p ∈ Pset N (V j / Δ) (V j), (1 / (p : ℝ)) := by
    rw [prod_univ_sum]
    refine sum_congr rfl fun t _ => ?_
    push_cast
    rw [one_div, ← prod_inv_distrib]
    simp [one_div]
  rw [this]
  exact prod_le_prod₀ (fun j _ => sum_nonneg fun p _ => by positivity)
    (fun j _ => sum_inv_Pset_le N (hV j) hΔ)

/-- `#T ≤ ∏_j (V_j + 1)`. -/
lemma card_T_le (N i : ℕ) (V : Fin i → ℝ) {Δ : ℝ} (hV : ∀ j, 0 ≤ V j) (hΔ : 1 ≤ Δ) :
    (#(Tset N i V Δ) : ℝ) ≤ ∏ j, (V j + 1) := by
  unfold Tset
  rw [Fintype.card_piFinset]
  push_cast
  refine prod_le_prod₀ (fun j _ => by positivity) (fun j _ => ?_)
  have := card_Pset_le N (hV j) hΔ
  have : 0 ≤ V j / Δ := div_nonneg (hV j) (by linarith)
  linarith

lemma T_prime {N i : ℕ} {V : Fin i → ℝ} {Δ : ℝ} {t : Fin i → ℕ} (ht : t ∈ Tset N i V Δ)
    (j : Fin i) : (t j).Prime := by
  unfold Tset at ht
  exact (mem_Pset.1 (Fintype.mem_piFinset.1 ht j)).1

/-- **Wu 2004 Lemma 4.1 for `σ ∈ U_k(N)`, with the remainder made explicit.** -/
theorem lemma41_Uk {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) (i : ℕ) (V : Fin i → ℝ)
    {Δ W : ℝ} (hΔ : 1 < Δ) (hΔ' : Δ ≤ 3 / 2) (hV : ∀ j, 3 ≤ V j) (hW : 0 < W)
    (w z : (Fin i → ℕ) → ℝ) (hw : ∀ t ∈ Tset N i V Δ, W ≤ w t)
    (hwz : ∀ t ∈ Tset N i V Δ, w t ≤ z t) :
    2 * ∑ t ∈ Tset N i V Δ, (S A (∏ j, t j) ((∏ j, t j) * N) (z t) : ℝ) ≤
      ∑ t ∈ Tset N i V Δ, ((Ω₁ A (∏ j, t j) N (w t) : ℝ) - Ω₂ A (∏ j, t j) N (w t) (z t)
        + Ω₃ A (∏ j, t j) N (w t) (z t)) + i * (N / W + 2 ^ i * ∏ j, V j) := by
  set T := Tset N i V Δ
  have hd : ∀ t ∈ T, 1 ≤ ∏ j, t j := fun t ht =>
    Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun j _ => (T_prime ht j).ne_zero)
  -- per tuple, `lemma41_exact` and `err_le`
  have hper : ∀ t ∈ T, 2 * (S A (∏ j, t j) ((∏ j, t j) * N) (z t) : ℝ) ≤
      ((Ω₁ A (∏ j, t j) N (w t) : ℝ) - Ω₂ A (∏ j, t j) N (w t) (z t)
        + Ω₃ A (∏ j, t j) N (w t) (z t)) + i * ((N : ℝ) / (W * ∏ j, t j) + 1) := by
    intro t ht
    have h1 := lemma41_exact A (∏ j, t j) N (hwz t ht)
    have h1' : ((2 * S A (∏ j, t j) ((∏ j, t j) * N) (z t) : ℤ) : ℝ) ≤
        (((Ω₁ A (∏ j, t j) N (w t) : ℤ) - Ω₂ A (∏ j, t j) N (w t) (z t)
          + Ω₃ A (∏ j, t j) N (w t) (z t) + Err A (∏ j, t j) N (w t) (z t) : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    have hwt : 0 < w t := lt_of_lt_of_le hW (hw t ht)
    have h2 := err_le hA (hd t ht) (z := z t) hwt
    have hω : (#(∏ j, t j).primeFactors : ℝ) ≤ i := by
      exact_mod_cast card_primeFactors_prod_le t (T_prime ht)
    have hdpos : (0 : ℝ) < ((∏ j, t j : ℕ) : ℝ) := by exact_mod_cast hd t ht
    have h3 : (N : ℝ) / ((∏ j, t j : ℕ) * w t) ≤ N / (W * ∏ j, t j) := by
      push_cast
      apply div_le_div_of_nonneg_left (by positivity) (by push_cast at hdpos; positivity)
      push_cast at hdpos
      rw [mul_comm W]
      exact mul_le_mul_of_nonneg_left (hw t ht) hdpos.le
    have h4 : (#(∏ j, t j).primeFactors : ℝ) * ((N : ℝ) / ((∏ j, t j : ℕ) * w t) + 1) ≤
        i * ((N : ℝ) / (W * ∏ j, t j) + 1) :=
      mul_le_mul hω (by linarith) (by positivity) (by positivity)
    have h5 := h2.trans h4
    linarith
  have hR : ∑ t ∈ T, (i : ℝ) * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1) =
      i * ((N / W) * ∑ t ∈ T, (1 / ((∏ j, t j : ℕ) : ℝ)) + #T) := by
    rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum]
    congr 2
    refine sum_congr rfl fun t _ => ?_
    push_cast
    field_simp
  have hprod : ∏ j, (Δ - 1 + Δ / V j) ≤ 1 := by
    refine prod_le_one₀ (fun j _ => ?_) (fun j _ => ?_)
    · have := hV j; have : 0 < Δ / V j := by apply div_pos <;> linarith
      linarith
    · have := hV j
      have : Δ / V j ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  have hsum := sum_inv_T_le N i V (fun j => by linarith [hV j]) hΔ.le
  have hcard := card_T_le N i V (fun j => by linarith [hV j]) hΔ.le
  have hpow : ∏ j, (V j + 1) ≤ 2 ^ i * ∏ j, V j := by
    rw [show (2 : ℝ) ^ i = ∏ _j : Fin i, (2 : ℝ) by simp, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun j _ => by linarith [hV j]) (fun j _ => by linarith [hV j])
  have hNW : 0 ≤ (N : ℝ) / W := by positivity
  have hmain : (N : ℝ) / W * ∑ t ∈ T, (1 / ((∏ j, t j : ℕ) : ℝ)) ≤ N / W := by
    calc _ ≤ (N : ℝ) / W * 1 := mul_le_mul_of_nonneg_left (hsum.trans hprod) hNW
      _ = _ := mul_one _
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hfin : (i : ℝ) * ((N / W) * ∑ t ∈ T, (1 / ((∏ j, t j : ℕ) : ℝ)) + #T) ≤
      i * (N / W + 2 ^ i * ∏ j, V j) :=
    mul_le_mul_of_nonneg_left (by linarith) hi0
  have hsumle := sum_le_sum hper
  rw [sum_add_distrib, hR, ← mul_sum] at hsumle
  linarith

end LeanLab.ChenDoubleSieve.Wu41
