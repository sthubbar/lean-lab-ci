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
  sorry

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
