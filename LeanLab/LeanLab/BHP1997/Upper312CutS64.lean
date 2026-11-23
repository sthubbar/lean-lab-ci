/-
P0069 Baker Harman Pintz 1997, pages 23 to 27, 41 and 42, read against the page images
papers/P0069-original.pdf. ROUTE BURST S64, burst-20261122, group B.
Two proved wiring steps for `Decomp312b.upper_mean_value_supply`.
Part 1. The cut of the upper supply into a combinatorial claim for an admissibility class P
and an analytic claim that every family of class P obeys display 4.1 of page 24. This mirrors
Part A of DQ7Decisions for the lower supply. The assembly gives the exact conclusion of the
sealed leaf for every P, and the completeness theorem shows the cut loses nothing.
Part 2. Display 4.1 of page 24 is stable under adding two coefficient families. The upper
family a1 of page 41 is a signed sum of Buchstab pieces, so this is the step that moves 4.1
from the pieces to the sum, for a number of pieces that does not grow with x.
No open leaf. No new definition. No existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b

namespace LeanLab.BHP1997.Upper312CutS64
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132

/-- P0069 pages 23 to 27 and 41 to 42. The cut assembly for the upper supply, proved for
every admissibility class P. The hypothesis hA is the combinatorial part of pages 41 and 42:
the sifted family c1 above the primes on I, the auxiliary family b of class P with the I1
density u1 over log x and small L1 distance on I, with 1 <= u1 < 1.0001. The hypothesis hB
is the analytic part of pages 23 to 27, Lemma 10 with Lemmas 12 to 16: every family of
class P obeys display 4.1. The conclusion is the verbatim conclusion of the sealed
`Decomp312b.upper_mean_value_supply`. PROVED. AI wrote the Lean code. Goldbach is open. -/
theorem upper_supply_of_cut_s64 (P : ℝ → (ℝ → ℕ → ℝ) → Prop)
    (hA : ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        P ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k)
    (hB : ∀ (ε : ℝ) (b : ℝ → ℕ → ℝ), 0 < ε → P ε b → MeanValue41 ε b) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  obtain ⟨B0, η, hB0, hη, h⟩ := hA
  refine ⟨B0, η, hB0, hη, fun ε hε hεη => ?_⟩
  obtain ⟨u1, c1, b, hu, hu1, hc, hb, hP, hd, happ, hlo⟩ := h ε hε hεη
  exact ⟨u1, c1, b, hu, hu1, hc, hb, hB ε b hε hP, hd, happ, hlo⟩

/-- The cut loses nothing. From the verbatim conclusion of the sealed leaf, both hypotheses
of `upper_supply_of_cut_s64` hold with P equal to display 4.1 itself. So neither half of the
cut is false wherever the sealed leaf is true. PROVED. AI wrote the Lean code. -/
theorem upper_cut_complete_s64
    (h : ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k) :
    (∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k) ∧
      ∀ (ε : ℝ) (b : ℝ → ℕ → ℝ), 0 < ε → MeanValue41 ε b → MeanValue41 ε b :=
  ⟨h, fun _ _ _ hb => hb⟩

/-- The Dirichlet polynomial of display 4.1 of page 24 is continuous in the height t.
Every k in the window has k at least 1, so no power of zero occurs. PROVED. -/
theorem meanValue41_integrand_continuous (a : ℝ → ℕ → ℝ) (x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ : ℝ) :
    Continuous fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖ := by
  refine Continuous.norm (continuous_finsetSum _ fun k hk => ?_)
  have hk : (k : ℂ) ≠ 0 := by
    have : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1
    exact_mod_cast this.ne'
  have hhalf : Continuous fun t : ℝ => Thm4.half (σ * t) := by
    unfold Thm4.half
    fun_prop
  refine continuous_const.div (Continuous.const_cpow hhalf (Or.inl hk)) fun t => ?_
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hk)

/-- P0069 page 24, display 4.1, is additive: if two coefficient families obey 4.1 then so
does their sum. The integrand of the sum is at most the sum of the integrands by the
triangle inequality, and the constants add. PROVED. AI wrote the Lean code. -/
theorem meanValue41_add {ε : ℝ} {a b : ℝ → ℕ → ℝ} (ha : MeanValue41 ε a)
    (hb : MeanValue41 ε b) : MeanValue41 ε (fun x k => a x k + b x k) := by
  intro A hA
  obtain ⟨C1, X1, h1⟩ := ha A hA
  obtain ⟨C2, X2, h2⟩ := hb A hA
  refine ⟨|C1| + |C2|, max (max X1 X2) 1, fun x hx q hq hqA χ σ hσ => ?_⟩
  have hx1 : X1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : X2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxo : 1 ≤ x := (le_max_right _ _).trans hx
  have hpos : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hxo) _)
  set lo := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  set hi := x ^ (0.45 - 2 * ε / 3)
  set F := fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖ with hF
  set G := fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖ with hG
  set H := fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (((fun x k => a x k + b x k) x k : ℝ) : ℂ) * χ (k : ZMod q) /
        (k : ℂ) ^ Thm4.half (σ * t)‖ with hH
  have hFc : Continuous F := meanValue41_integrand_continuous a x χ σ
  have hGc : Continuous G := meanValue41_integrand_continuous b x χ σ
  have hHc : Continuous H :=
    meanValue41_integrand_continuous (fun x k => a x k + b x k) x χ σ
  have hpt : ∀ t, H t ≤ F t + G t := by
    intro t
    simp only [hF, hG, hH]
    calc _ = ‖(∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)) +
        ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖ := by
            rw [← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            push_cast
            ring
      _ ≤ _ := norm_add_le _ _
  change (∫ t in lo..hi, H t) ≤ (|C1| + |C2|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)
  rcases le_or_gt lo hi with hle | hlt
  · have hFi := h1 x hx1 q hq hqA χ σ hσ
    have hGi := h2 x hx2 q hq hqA χ σ hσ
    change (∫ t in lo..hi, F t) ≤ _ at hFi
    change (∫ t in lo..hi, G t) ≤ _ at hGi
    have hmono : (∫ t in lo..hi, H t) ≤ ∫ t in lo..hi, (F t + G t) :=
      intervalIntegral.integral_mono_on hle (hHc.intervalIntegrable _ _)
        ((hFc.add hGc).intervalIntegrable _ _) fun t _ => hpt t
    rw [intervalIntegral.integral_add (hFc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)] at hmono
    have e1 : C1 * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) ≤
        |C1| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    have e2 : C2 * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) ≤
        |C2| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    calc (∫ t in lo..hi, H t) ≤ _ := hmono
      _ ≤ |C1| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) +
          |C2| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by linarith
      _ = _ := by ring
  · have hneg : (∫ t in lo..hi, H t) ≤ 0 := by
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg hlt.le fun t _ => norm_nonneg _
    have : 0 ≤ (|C1| + |C2|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      rw [mul_assoc]; exact mul_nonneg (by positivity) hpos
    linarith

end LeanLab.BHP1997.Upper312CutS64
