/-
AI wrote the Lean code. CODEX task139, 2026-10-27.
Source: https://arxiv.org/pdf/2012.06322, printed pages 4 through 8.
The analytic leaves retain named published inputs as sorry.
The final assembly has the exact sealed Lemma4 proposition.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.Decomp139

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies as in the defined sawtooth. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))

/-- Pages 4 and 5. The displayed S2 bound. -/
def tailBudget (γ n y H : ℝ) : ℝ :=
  H ^ ((1 : ℝ) / 2) * n ^ (1 - γ / 2) + H⁻¹ * y * n ^ (1 - γ)

/-- Page 8. Exponent pairs of the optimized bound, with the S2 balance computed from page 5. -/
def terms (γ : ℝ) : List (ℝ × ℝ) :=
  [(3 / 2 - γ, 0),
   (1 - γ / 4, 0), ((γ + 2) / 6, 1 / 3), (γ / 4, 1 / 2), (3 / 4, 1 / 8),
   (γ / 8 + 1 / 2, 1 / 4), (γ / 10 + 3 / 5, 1 / 5), (3 * γ / 10, 3 / 5),
   (3 * γ / 14 + 2 / 7, 3 / 7), (1 - 2 * γ / 3, 1 / 3),
   (1 - 4 * γ / 7, 3 / 7), (7 / 8 - γ / 2, 1 / 2), (1 / 5 - 2 * γ / 5, 1),
   (9 / 13 - 6 * γ / 13, 9 / 13), (5 / 9 - 4 * γ / 9, 7 / 9),
   (7 / 8 - γ / 2, 9 / 16), (13 / 17 - 8 * γ / 17, 11 / 17),
   (17 / 21 - 10 * γ / 21, 13 / 21), (13 / 23 - 10 * γ / 23, 19 / 23),
   (21 / 31 - 14 * γ / 31, 23 / 31)]

/-- Page 8. The sum of the optimized monomials, including the prime power remainder. -/
def budget (γ n y : ℝ) : ℝ := (terms γ |>.map (fun ab => n ^ ab.1 * y ^ ab.2)).sum

/-- LEAF. Page 4, first two displays of the proof of Lemma 4.
The floor characteristic and Taylor remainder reduce the discrepancy to the sawtooth sum. -/
theorem characteristic_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ‖fS γ n y α - gS n y α - sawSum γ n y α‖ ≤ C * (n : ℝ) ^ (3 / 2 - γ) :=
  LeanLab.Song2020.Characteristic139.characteristic_reduction139

/-- LEAF. Pages 4 and 5, S2 bound.
Published inputs: Graham and Kolesnik, Appendix and exponent pair display 3.3.4.
The same coefficient family works at every truncation level. -/
theorem fourier_approximation :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  sorry

/-- Page 8, first display after summing over h. The exponent triples of the S1 bound:
the exponent of n, of y and of H in each monomial. The last triple uses n to the
gamma over four, from the preceding per h display on page 8, as recorded in QUESTION Q139b;
the printed page 8 display shows n to the gamma there. -/
def s1Terms (γ : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(1 - γ / 4, 0, 3 / 4), ((γ + 4) / 8, 1 / 4, 9 / 8), ((3 * γ + 4) / 14, 3 / 7, 17 / 14),
   (3 / 4, 1 / 8, 1), (γ / 2 - 1, 1, 3 / 2), (3 * γ / 10, 3 / 5, 13 / 10),
   ((γ + 6) / 10, 1 / 5, 11 / 10), ((γ + 2) / 6, 1 / 3, 7 / 6), (γ / 4, 1 / 2, 5 / 4)]

/-- Page 8, first display after summing over h. The S1 polynomial in H. -/
def s1Poly (γ n y H : ℝ) : ℝ :=
  (s1Terms γ |>.map (fun t => n ^ t.1 * y ^ t.2.1 * H ^ t.2.2)).sum

/-- CITED. Song 2020, pages 5 through 8, the S1 estimate after summing over h:
S1 is bounded by n to the 3/2 minus gamma plus n to the epsilon times the nine H monomials.
Published inputs used by the paper for this display: the reduction to Lambda weighted sums
by partial summation, page 5; the Vaughan identity, the paper's Lemma 3.2, page 5;
Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6, and for the inner sums of
T(R,S), page 7; Graham and Kolesnik Lemma 2.5 for T(R,S), page 6; Graham and Kolesnik
Lemma 2.4 for the choices of L and u, page 7; and the additive character identity, page 8.
The coefficient hypothesis is the paper's bound a_h less than 1 over h, with constant K. -/
theorem s1_estimate :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (n : ℝ) ^ ε * s1Poly γ n y H) := by
  sorry

/-- PROVED. Graham and Kolesnik, Van der Corput's Method of Exponential Sums, Lemma 2.4,
in the case of a single negative power and lower endpoint H1 equal to 1, as Song 2020 uses
it on page 8 to choose H: for L(H) the sum of A_i H to the a_i plus B over H, some integer H
with 1 at most H at most H2 has L(H) bounded by the sum of the balanced terms
A_i to the 1 over a_i plus 1 times B to the a_i over a_i plus 1, plus the endpoint terms
A_i at H equal to 1 and B over H2. The constant depends only on the exponents, which
absorbs the rounding to an integer. Proved here directly, not cited. -/
theorem gk_lemma_2_4 {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 < e i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Fin m → ℝ) (B : ℝ), (∀ i, 0 ≤ A i) → 0 ≤ B →
      ∀ H₂ : ℕ, 1 ≤ H₂ →
      ∃ H : ℕ, 1 ≤ H ∧ H ≤ H₂ ∧
        ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ ≤
          C * (∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i + B * (H₂ : ℝ)⁻¹) := by
  refine ⟨∑ i, (2 : ℝ) ^ (e i) + 1, by positivity, ?_⟩
  intro A B hA hB H₂ hH₂
  set S := ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i with hS
  have hb0 : ∀ i, 0 ≤ (A i * B ^ (e i)) ^ (1 / (e i + 1)) := fun i => by
    have := hA i; positivity
  have hS1 : 0 ≤ ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) :=
    Finset.sum_nonneg (fun i _ => hb0 i)
  have hS2 : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  have hAS : ∀ i, A i ≤ S := fun i => by
    have := Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ i)
    linarith
  have hbS : ∀ i, A i * B ^ (e i) ≤ S ^ (e i + 1) := by
    intro i
    have h1 : (A i * B ^ (e i)) ^ (1 / (e i + 1)) ≤ S := by
      have := Finset.single_le_sum (f := fun j => (A j * B ^ (e j)) ^ (1 / (e j + 1)))
        (fun j _ => hb0 j) (Finset.mem_univ i)
      linarith
    have hne : e i + 1 ≠ 0 := by linarith [he i]
    have h2 := Real.rpow_le_rpow (hb0 i) h1 (by linarith [he i] : 0 ≤ e i + 1)
    rwa [one_div, Real.rpow_inv_rpow (by have := hA i; positivity) hne] at h2
  have hC1 : (1 : ℝ) ≤ ∑ i, (2 : ℝ) ^ (e i) + 1 := by
    have : 0 ≤ ∑ i, (2 : ℝ) ^ (e i) := by positivity
    linarith
  have hBH₂ : 0 ≤ B * (H₂ : ℝ)⁻¹ := by positivity
  have hfin := le_mul_of_one_le_left hBH₂ hC1
  rcases (show 0 ≤ S by linarith).lt_or_eq with hSpos | hS0
  · set H₀ : ℕ := max 1 ⌈B / S⌉₊ with hH₀
    refine ⟨min H₀ H₂, le_min (le_max_left _ _) hH₂, min_le_right _ _, ?_⟩
    have hH₀1 : 1 ≤ H₀ := le_max_left _ _
    have hH₀R : (1 : ℝ) ≤ H₀ := by exact_mod_cast hH₀1
    have hH₂R : (1 : ℝ) ≤ H₂ := by exact_mod_cast hH₂
    have hBH₀ : B * (H₀ : ℝ)⁻¹ ≤ S := by
      have hc : B / S ≤ (H₀ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
      rw [div_le_iff₀ hSpos] at hc
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      linarith
    have hHle : ((min H₀ H₂ : ℕ) : ℝ) ≤ H₀ := by exact_mod_cast min_le_left _ _
    have hHpos : (0 : ℝ) < ((min H₀ H₂ : ℕ) : ℝ) := by
      have : 1 ≤ min H₀ H₂ := le_min hH₀1 hH₂
      exact_mod_cast (show 0 < min H₀ H₂ by omega)
    have hBH : B * ((min H₀ H₂ : ℕ) : ℝ)⁻¹ ≤ S + B * (H₂ : ℝ)⁻¹ := by
      rcases min_choice H₀ H₂ with h | h <;> rw [h] <;> linarith
    have hH₀2 : (H₀ : ℝ) ≤ 2 * max 1 (B / S) := by
      rw [hH₀, Nat.cast_max, Nat.cast_one]
      apply max_le
      · linarith [le_max_left 1 (B / S)]
      · rcases le_total (B / S) 1 with h | h
        · have h' : ⌈B / S⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using h)
          have : (⌈B / S⌉₊ : ℝ) ≤ 1 := by exact_mod_cast h'
          linarith [le_max_left 1 (B / S)]
        · have := Nat.ceil_lt_add_one (show 0 ≤ B / S by positivity)
          linarith [le_max_right 1 (B / S)]
    have key : ∀ i, A i * (max 1 (B / S)) ^ (e i) ≤ S := by
      intro i
      rcases le_total (B / S) 1 with h | h
      · rw [max_eq_left h, Real.one_rpow, mul_one]
        exact hAS i
      · rw [max_eq_right h, Real.div_rpow hB hSpos.le, ← mul_div_assoc,
          div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)]
        calc A i * B ^ e i ≤ S ^ (e i + 1) := hbS i
          _ = S * S ^ e i := by rw [Real.rpow_add hSpos, Real.rpow_one]; ring
    have hterm : ∀ i, A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i) ≤ 2 ^ (e i) * S := by
      intro i
      have hr1 : 1 ≤ max 1 (B / S) := le_max_left _ _
      calc A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i)
          ≤ A i * (2 * max 1 (B / S)) ^ (e i) := by
            apply mul_le_mul_of_nonneg_left _ (hA i)
            exact Real.rpow_le_rpow hHpos.le (hHle.trans hH₀2) (he i).le
        _ = 2 ^ (e i) * (A i * (max 1 (B / S)) ^ (e i)) := by
            rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
        _ ≤ 2 ^ (e i) * S := mul_le_mul_of_nonneg_left (key i) (by positivity)
    have hsum : ∑ i, A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i) ≤ (∑ i, (2 : ℝ) ^ (e i)) * S := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => hterm i)
    have hexp : (∑ i, (2 : ℝ) ^ (e i) + 1) * (S + B * (H₂ : ℝ)⁻¹) =
        (∑ i, (2 : ℝ) ^ (e i)) * S + S + (∑ i, (2 : ℝ) ^ (e i) + 1) * (B * (H₂ : ℝ)⁻¹) := by
      ring
    linarith
  · refine ⟨H₂, hH₂, le_rfl, ?_⟩
    have hA0 : ∀ i, A i = 0 := fun i => le_antisymm (by linarith [hAS i]) (hA i)
    have h0 : ∑ i, A i * (H₂ : ℝ) ^ (e i) = 0 := by simp [hA0]
    rw [h0, ← hS0]
    linarith

/-- PROVED. Page 8, exponent arithmetic of the balance in Graham and Kolesnik Lemma 2.4:
balancing n to the eps times n to the e1 times y to the e2 times H to the a against
n to the eps times y times n to the 1 minus gamma over H gives n to the eps times
n to the E times y to the F with E and F as below. -/
theorem balance_rpow (n y ε γ e1 e2 a E F : ℝ) (hn : 0 < n) (hy : 0 < y) (ha : 0 < a)
    (hE : e1 + a * (1 - γ) = E * (a + 1)) (hF : e2 + a = F * (a + 1)) :
    ((n ^ ε * (n ^ e1 * y ^ e2)) * (n ^ ε * (y * n ^ (1 - γ))) ^ a) ^ (1 / (a + 1)) =
      n ^ ε * (n ^ E * y ^ F) := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, y = Real.exp M := ⟨Real.log y, (Real.exp_log hy).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_add]
  congr 1
  have ha1 : a + 1 ≠ 0 := by linarith
  field_simp
  linear_combination L * hE + M * hF

/-- PROVED. Page 8. Every optimized monomial is at most the optimized budget. -/
theorem le_budget (γ n y : ℝ) (hn : 0 ≤ n) (hy : 0 ≤ y) (E F : ℝ)
    (h : (E, F) ∈ terms γ) : n ^ E * y ^ F ≤ budget γ n y := by
  unfold budget
  apply List.single_le_sum
  · intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  · exact List.mem_map.mpr ⟨(E, F), h, rfl⟩

/-- LEAF. Pages 5 through 8, S1 estimates and parameter choices.
Published inputs: Iwaniec and Kowalski Corollary 8.13, the cited Vaughan identity,
and Graham and Kolesnik Lemmas 2.4 and 2.5.
The S2 monomial uses the balance derived from page 5, as recorded in STATEMENTS.md. -/
theorem optimized_truncated_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∃ H : ℕ, 1 ≤ H ∧
              ‖truncatedSum a H γ n y α‖ + tailBudget γ n y H ≤
                C * K * (n : ℝ) ^ ε * budget γ n y := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₁, hC₁, N₀, hs1⟩ := s1_estimate γ hγ hγ1 ε hε
  let e : Fin 10 → ℝ := ![3 / 4, 9 / 8, 17 / 14, 1, 3 / 2, 13 / 10, 11 / 10, 7 / 6, 5 / 4, 1 / 2]
  obtain ⟨Cg, hCg, hgk⟩ := gk_lemma_2_4 e (by intro i; fin_cases i <;> norm_num [e])
  refine ⟨C₁ + max 1 C₁ * Cg * 21, by positivity, N₀, ?_⟩
  intro K hK a ha n hn y hy hyu α
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hse : songExponent γ ≠ 0 := by unfold songExponent; intro h; linarith
      simp [Real.zero_rpow hse] at hy hyu
      linarith
    · exact_mod_cast h
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hN0 _).trans hy
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hn1 hε.le
  let t : Fin 10 → ℝ × ℝ :=
    ![(1 - γ / 4, 0), ((γ + 4) / 8, 1 / 4), ((3 * γ + 4) / 14, 3 / 7), (3 / 4, 1 / 8),
      (γ / 2 - 1, 1), (3 * γ / 10, 3 / 5), ((γ + 6) / 10, 1 / 5), ((γ + 2) / 6, 1 / 3),
      (γ / 4, 1 / 2), (1 - γ / 2, 0)]
  let A : Fin 10 → ℝ := fun i => N ^ ε * (N ^ (t i).1 * y ^ (t i).2)
  let B : ℝ := N ^ ε * (y * N ^ (1 - γ))
  obtain ⟨H, hH, -, hL⟩ := hgk A B (by intro i; positivity) (by positivity)
    (⌈B⌉₊ + 1) (by omega)
  refine ⟨H, hH, ?_⟩
  have hs := hs1 K hK a ha n hn y hy hyu α H hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  set M : ℝ := N ^ ε * budget γ N y with hM
  have hbud0 : 0 ≤ budget γ N y := by
    unfold budget
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hM0 : 0 ≤ M := by positivity
  -- each balanced term and each endpoint term is at most M
  have hgen : ∀ e1 e2 c E F : ℝ, 0 < c → e1 + c * (1 - γ) = E * (c + 1) →
      e2 + c = F * (c + 1) → (E, F) ∈ terms γ →
      ((N ^ ε * (N ^ e1 * y ^ e2)) * B ^ c) ^ (1 / (c + 1)) ≤ M := by
    intro e1 e2 c E F hc hE hF hmem
    rw [balance_rpow N y ε γ e1 e2 c E F hN0 hy0 hc hE hF]
    exact mul_le_mul_of_nonneg_left (le_budget γ N y hN0.le hy0.le E F hmem) (by positivity)
  have hend : ∀ e1 e2 E : ℝ, e1 ≤ E → (E, e2) ∈ terms γ →
      N ^ ε * (N ^ e1 * y ^ e2) ≤ M := by
    intro e1 e2 E hle hmem
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc N ^ e1 * y ^ e2 ≤ N ^ E * y ^ e2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hle) (by positivity)
      _ ≤ budget γ N y := le_budget γ N y hN0.le hy0.le E e2 hmem
  have hbal : ∀ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) ≤ M := by
    intro i
    fin_cases i
    · exact hgen (1 - γ / 4) (0) (3 / 4) (1 - 4 * γ / 7) (3 / 7) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 4) / 8) (1 / 4) (9 / 8) (13 / 17 - 8 * γ / 17) (11 / 17) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((3 * γ + 4) / 14) (3 / 7) (17 / 14) (21 / 31 - 14 * γ / 31) (23 / 31) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (3 / 4) (1 / 8) (1) (7 / 8 - γ / 2) (9 / 16) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (γ / 2 - 1) (1) (3 / 2) (1 / 5 - 2 * γ / 5) (1) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (3 * γ / 10) (3 / 5) (13 / 10) (13 / 23 - 10 * γ / 23) (19 / 23) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 6) / 10) (1 / 5) (11 / 10) (17 / 21 - 10 * γ / 21) (13 / 21) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 2) / 6) (1 / 3) (7 / 6) (9 / 13 - 6 * γ / 13) (9 / 13) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (γ / 4) (1 / 2) (5 / 4) (5 / 9 - 4 * γ / 9) (7 / 9) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (1 - γ / 2) (0) (1 / 2) (1 - 2 * γ / 3) (1 / 3) (by norm_num) (by ring) (by ring)
        (by simp [terms])
  have hA : ∀ i, A i ≤ M := by
    intro i
    fin_cases i
    · exact hend (1 - γ / 4) (0) (1 - γ / 4) (by linarith) (by simp [terms])
    · exact hend ((γ + 4) / 8) (1 / 4) (γ / 8 + 1 / 2) (by linarith) (by simp [terms])
    · exact hend ((3 * γ + 4) / 14) (3 / 7) (3 * γ / 14 + 2 / 7) (by linarith) (by simp [terms])
    · exact hend (3 / 4) (1 / 8) (3 / 4) (by linarith) (by simp [terms])
    · exact hend (γ / 2 - 1) (1) (1 / 5 - 2 * γ / 5) (by linarith) (by simp [terms])
    · exact hend (3 * γ / 10) (3 / 5) (3 * γ / 10) (by linarith) (by simp [terms])
    · exact hend ((γ + 6) / 10) (1 / 5) (γ / 10 + 3 / 5) (by linarith) (by simp [terms])
    · exact hend ((γ + 2) / 6) (1 / 3) ((γ + 2) / 6) (by linarith) (by simp [terms])
    · exact hend (γ / 4) (1 / 2) (γ / 4) (by linarith) (by simp [terms])
    · exact hend (1 - γ / 2) (0) (1 - γ / 4) (by linarith) (by simp [terms])
  have hbase : N ^ (3 / 2 - γ) ≤ M := by
    have h := hend (3 / 2 - γ) 0 (3 / 2 - γ) le_rfl (by simp [terms])
    have : N ^ (3 / 2 - γ) ≤ N ^ ε * (N ^ (3 / 2 - γ) * y ^ (0 : ℝ)) := by
      rw [Real.rpow_zero, mul_one]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hN0.le _) hNe
    linarith
  have hR : ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i +
      B * ((⌈B⌉₊ + 1 : ℕ) : ℝ)⁻¹ ≤ 21 * M := by
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbal i)
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    push_cast at h1 h2
    have hB2 : B * ((⌈B⌉₊ + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      have hc : B ≤ ((⌈B⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith [Nat.le_ceil B]
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hc
    have hM1 : 1 ≤ M := (Real.one_le_rpow hn1 (by linarith)).trans hbase
    linarith
  -- the S1 polynomial and the S2 budget are the Lemma 2.4 sum
  have hQ : ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ =
      N ^ ε * s1Poly γ N y H + N ^ ε * (N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2)) +
        N ^ ε * ((H : ℝ)⁻¹ * y * N ^ (1 - γ)) := by
    simp [A, B, t, e, Fin.sum_univ_succ, s1Poly, s1Terms]
    ring
  have hP0 : 0 ≤ s1Poly γ N y H := by
    unfold s1Poly
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hT : tailBudget γ N y H ≤ N ^ ε * (N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2)) +
        N ^ ε * ((H : ℝ)⁻¹ * y * N ^ (1 - γ)) := by
    unfold tailBudget
    have h1 : 0 ≤ N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have h2 : 0 ≤ (H : ℝ)⁻¹ * y * N ^ (1 - γ) := by positivity
    have h3 := le_mul_of_one_le_left h1 hNe
    have h4 := le_mul_of_one_le_left h2 hNe
    linarith
  have hT0 : 0 ≤ tailBudget γ N y H := by unfold tailBudget; positivity
  have hPT : N ^ ε * s1Poly γ N y H + tailBudget γ N y H ≤ Cg * (21 * M) := by
    calc _ ≤ ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ := by rw [hQ]; linarith
      _ ≤ _ := hL
      _ ≤ _ := mul_le_mul_of_nonneg_left hR hCg
  have hK0 : 0 ≤ K := by linarith
  have hmax : 1 ≤ max 1 C₁ := le_max_left _ _
  have hmax' : C₁ ≤ max 1 C₁ := le_max_right _ _
  have hPs0 : 0 ≤ N ^ ε * s1Poly γ N y H := by positivity
  have hstep : C₁ * K * (N ^ ε * s1Poly γ N y H) + tailBudget γ N y H ≤
      max 1 C₁ * K * (N ^ ε * s1Poly γ N y H + tailBudget γ N y H) := by
    have e1 : C₁ * K * (N ^ ε * s1Poly γ N y H) ≤ max 1 C₁ * K * (N ^ ε * s1Poly γ N y H) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax' hK0) hPs0
    have e2 : tailBudget γ N y H ≤ max 1 C₁ * K * tailBudget γ N y H :=
      le_mul_of_one_le_left hT0 (one_le_mul_of_one_le_of_one_le hmax hK)
    rw [mul_add]
    linarith
  have hfin : ‖truncatedSum a H γ n y α‖ + tailBudget γ N y H ≤
      C₁ * K * M + max 1 C₁ * K * (Cg * (21 * M)) := by
    have h3 : C₁ * K * N ^ (3 / 2 - γ) ≤ C₁ * K * M :=
      mul_le_mul_of_nonneg_left hbase (mul_nonneg hC₁ hK0)
    have h4 := mul_le_mul_of_nonneg_left hPT (mul_nonneg (by linarith : 0 ≤ max 1 C₁) hK0)
    have hs' : ‖truncatedSum a H γ n y α‖ ≤
        C₁ * K * N ^ (3 / 2 - γ) + C₁ * K * (N ^ ε * s1Poly γ N y H) := by
      rw [← mul_add]; exact hs
    linarith
  calc ‖truncatedSum a H γ n y α‖ + tailBudget γ N y H
      ≤ C₁ * K * M + max 1 C₁ * K * (Cg * (21 * M)) := hfin
    _ = (C₁ + max 1 C₁ * Cg * 21) * K * N ^ ε * budget γ N y := by rw [hM]; ring

/-- LEAF. Page 8, last sentence. Endpoint exponent comparisons bound each monomial. -/
theorem monomial_le (n y θ A B D E : ℝ) (hn : 1 ≤ n) (hy : n ^ θ ≤ y)
    (hyn : y ≤ n) (hlo : A + θ * (B - E) ≤ D) (hhi : A + B - E ≤ D) :
    n ^ A * y ^ B ≤ n ^ D * y ^ E := by
  have hn0 : 0 < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans_le hy
  have hratio : n ^ A * y ^ (B - E) ≤ n ^ D := by
    by_cases hBE : B ≤ E
    · calc
        n ^ A * y ^ (B - E) ≤ n ^ A * (n ^ θ) ^ (B - E) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hy (by linarith)
        _ = n ^ (A + θ * (B - E)) := by
          rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
        _ ≤ n ^ D := Real.rpow_le_rpow_of_exponent_le hn hlo
    · calc
        n ^ A * y ^ (B - E) ≤ n ^ A * n ^ (B - E) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow hy0.le hyn (by linarith)
        _ = n ^ (A + B - E) := by rw [← Real.rpow_add hn0]; congr 1; ring
        _ ≤ n ^ D := Real.rpow_le_rpow_of_exponent_le hn hhi
  calc
    n ^ A * y ^ B = (n ^ A * y ^ (B - E)) * y ^ E := by
      rw [mul_assoc, ← Real.rpow_add hy0]
      congr 2
      ring
    _ ≤ n ^ D * y ^ E := mul_le_mul_of_nonneg_right hratio (by positivity)

/-- LEAF. Page 8, last sentence. The twenty monomials are bounded on the sealed window. -/
theorem budget_le (γ n y : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1)
    (hn : 1 ≤ n) (hy : n ^ songExponent γ ≤ y) (hyn : y ≤ n) :
    budget γ n y ≤ 20 * (n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31)) := by
  have hexps : ∀ ab ∈ terms γ,
      ab.1 + songExponent γ * (ab.2 - 23 / 31) ≤ 21 / 31 - 14 * γ / 31 ∧
      ab.1 + ab.2 - 23 / 31 ≤ 21 / 31 - 14 * γ / 31 := by
    intro ab hab
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp; unfold songExponent; constructor <;> linarith
  have hterm : ∀ ab ∈ terms γ,
      n ^ ab.1 * y ^ ab.2 ≤ n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31) := by
    intro ab hab
    exact monomial_le n y (songExponent γ) ab.1 ab.2 _ _ hn hy hyn
      (hexps ab hab).1 (hexps ab hab).2
  unfold budget
  have hsum := List.sum_le_length_nsmul (terms γ |>.map (fun ab => n ^ ab.1 * y ^ ab.2))
    (n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31)) (by
      intro x hx
      obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hx
      exact hterm ab hab)
  simpa [terms, nsmul_eq_mul] using hsum


/-- Page 8. Assembly of Lemma 4 from the named leaves, with the exact sealed proposition. -/
theorem song_lemma4_decomposed : Lemma4 := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₀, hC₀, N₀, hred⟩ := characteristic_reduction γ hγ hγ1
  obtain ⟨a, K, hK, ha, C₁, hC₁, N₁, happ⟩ := fourier_approximation γ hγ hγ1
  obtain ⟨C₂, hC₂, N₂, hopt⟩ := optimized_truncated_bound γ hγ hγ1 ε hε
  refine ⟨C₀ + 20 * (max 1 C₁ * C₂ * K), max 1 (max N₀ (max N₁ N₂)), ?_⟩
  intro n hn y hy hyupper α
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans hy
  have hyn : y ≤ (n : ℝ) := by linarith
  obtain ⟨H, hH, hbound⟩ := hopt K hK a ha n (by omega) y hy hyupper α
  have hred' := hred n (by omega) y hy hyupper α
  have happ' := happ n (by omega) y hy hyupper H hH α
  let T : ℝ := (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31)
  have hbase : (n : ℝ) ^ (3 / 2 - γ) ≤ T := by
    have h := monomial_le n y (songExponent γ) (3 / 2 - γ) 0
      (21 / 31 - 14 * γ / 31 + ε) (23 / 31) hnR hy.le hyn
      (by unfold songExponent; linarith) (by linarith)
    simpa [T] using h
  have hb : (n : ℝ) ^ ε * budget γ n y ≤ 20 * T := by
    have h := mul_le_mul_of_nonneg_left (budget_le γ n y hγ hγ1 hnR hy.le hyn)
      (Real.rpow_nonneg hn0.le ε)
    have he : (n : ℝ) ^ ε *
        (20 * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31))) = 20 * T := by
      dsimp [T]
      rw [show 21 / 31 - 14 * γ / 31 + ε = ε + (21 / 31 - 14 * γ / 31) by ring,
        Real.rpow_add hn0]
      ring
    exact h.trans_eq he
  have ht : 0 ≤ tailBudget γ n y H := by unfold tailBudget; positivity
  have hnorm := norm_nonneg (truncatedSum a H γ n y α)
  have hmax0 : 0 ≤ max 1 C₁ := le_trans (by norm_num) (le_max_left _ _)
  have htri : ‖fS γ n y α - gS n y α‖ ≤
      ‖fS γ n y α - gS n y α - sawSum γ n y α‖ +
      ‖sawSum γ n y α - truncatedSum a H γ n y α‖ + ‖truncatedSum a H γ n y α‖ := by
    calc
      _ = ‖(fS γ n y α - gS n y α - sawSum γ n y α) +
          (sawSum γ n y α - truncatedSum a H γ n y α) + truncatedSum a H γ n y α‖ := by
        congr 1
        ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hlin : ‖fS γ n y α - gS n y α‖ ≤ C₀ * (n : ℝ) ^ (3 / 2 - γ) +
      max 1 C₁ * (‖truncatedSum a H γ n y α‖ + tailBudget γ n y H) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 C₁) hnorm,
      mul_le_mul_of_nonneg_right (le_max_right 1 C₁) ht]
  calc
    ‖fS γ n y α - gS n y α‖ ≤ C₀ * (n : ℝ) ^ (3 / 2 - γ) +
        max 1 C₁ * (‖truncatedSum a H γ n y α‖ + tailBudget γ n y H) := hlin
    _ ≤ C₀ * T + max 1 C₁ * (C₂ * K * (n : ℝ) ^ ε * budget γ n y) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase hC₀)
        (mul_le_mul_of_nonneg_left hbound hmax0)
    _ ≤ C₀ * T + (max 1 C₁ * C₂ * K) * (20 * T) := by
      have h := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hmax0 hC₂) (show 0 ≤ K by linarith))
      calc
        _ = C₀ * T + (max 1 C₁ * C₂ * K) * ((n : ℝ) ^ ε * budget γ n y) := by ring
        _ ≤ _ := add_le_add le_rfl h
    _ = (C₀ + 20 * (max 1 C₁ * C₂ * K)) * T := by ring

end

end LeanLab.Song2020.Decomp139

#print axioms LeanLab.Song2020.Decomp139.characteristic_reduction
#print axioms LeanLab.Song2020.Decomp139.fourier_approximation
#print axioms LeanLab.Song2020.Decomp139.s1_estimate
#print axioms LeanLab.Song2020.Decomp139.gk_lemma_2_4
#print axioms LeanLab.Song2020.Decomp139.balance_rpow
#print axioms LeanLab.Song2020.Decomp139.le_budget
#print axioms LeanLab.Song2020.Decomp139.optimized_truncated_bound
#print axioms LeanLab.Song2020.Decomp139.monomial_le
#print axioms LeanLab.Song2020.Decomp139.budget_le

#print axioms LeanLab.Song2020.Decomp139.song_lemma4_decomposed

namespace LeanLab.Song2020.State1562

/-- OPEN: Lemma 4. -/
theorem song_lemma4 : Lemma4 :=
  LeanLab.Song2020.Decomp139.song_lemma4_decomposed

end LeanLab.Song2020.State1562

#print axioms LeanLab.Song2020.State1562.song_lemma4
