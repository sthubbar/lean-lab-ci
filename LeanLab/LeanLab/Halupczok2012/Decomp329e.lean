import LeanLab.Halupczok2012.U1462Pointwise
import LeanLab.Halupczok2012.Fourier398

/-!
Elementary checks for converting Wu's fixed exponent count.
Source: arXiv 0705.1652 page 4 and page 5 Theorem 5.
The Euler product in the main term is strictly positive.
A fixed power window count transfers to windows up to twice that length.
The unrestricted or restricted predicate is an explicit parameter.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329e

open scoped Classical

/-- Wu arXiv page 4, the positive Euler product in Pi of x and theta.
This reuses the existing summability of the local perturbations. -/
theorem twinC_pos : 0 < twinC := by
  have hsNat := summable_pert f2 (q := 1) one_pos (fun k hk => by
    have hg0 : (0 : ℝ) ≤ (if k ∣ 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have h0 : 0 ≤ 1 / ((k : ℝ) - 1) ^ 2 := by positivity
    unfold f2
    by_cases h2 : k = 2
    · rw [if_pos h2, sub_self, abs_zero]
      linarith
    · rw [if_neg h2, show 1 - 1 / ((k : ℝ) - 1) ^ 2 - 1 = -(1 / ((k : ℝ) - 1) ^ 2) by ring,
        abs_neg, abs_of_nonneg h0]
      linarith)
  have hs : Summable (fun p : Nat.Primes => f2 p - 1) := by
    refine (hsNat.subtype Nat.Prime).congr ?_
    intro p
    change (if (p : ℕ).Prime then f2 p - 1 else 0) = f2 p - 1
    rw [if_pos p.property]
  have hpos : ∀ p : Nat.Primes, 0 < f2 p := by
    intro p
    unfold f2
    split_ifs with hp2
    · norm_num
    · have hp3 : (3 : ℝ) ≤ (p : ℕ) := by
        have hnat : 3 ≤ (p : ℕ) := by have := p.property.two_le; omega
        exact_mod_cast hnat
      have hd : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hden : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
      exact sub_pos.mpr ((div_lt_one hden).mpr hd)
  have hlogs : Summable (fun p : Nat.Primes => Real.log (f2 p)) :=
    (Real.summable_log_one_add_of_summable hs).congr (fun p => by congr 1; ring)
  change 0 < ∏' p : Nat.Primes, f2 p
  rw [← Real.rexp_tsum_eq_tprod hpos hlogs]
  exact Real.exp_pos _

/-- Wu arXiv page 5 Theorem 5, an elementary transfer from a fixed power window.
This theorem handles the range before a packing argument is needed. -/
theorem count_transfer_near_power (good : ℕ → Prop) {X Y θ c : ℝ}
    (hX : 2 ≤ X) (hθ : (1 / 2 : ℝ) ≤ θ) (hc : 0 < c)
    (hlow : X ^ θ ≤ Y) (hhigh : Y ≤ 2 * X ^ θ)
    (hfixed : c * X ^ θ / (Real.log X) ^ 2 ≤
      (((kRange X (X ^ θ)).filter good).card : ℝ)) :
    (c / 8) * Y / (Real.log Y) ^ 2 ≤ (((kRange X Y).filter good).card : ℝ) := by
  have hXp : 0 < X := by linarith
  have hHp : 0 < X ^ θ := Real.rpow_pos_of_pos hXp _
  have hYp : 0 < Y := hHp.trans_le hlow
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog := Real.log_le_log hHp hlow
  rw [Real.log_rpow hXp] at hlog
  have hθlog := mul_le_mul_of_nonneg_right hθ hLX.le
  have hLY : 0 < Real.log Y := by linarith
  have hcompare : Real.log X ≤ 2 * Real.log Y := by linarith
  have hsq : (Real.log X) ^ 2 ≤ 4 * (Real.log Y) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.log Y - Real.log X)]
  have htransfer : (c / 8) * Y / (Real.log Y) ^ 2 ≤ c * X ^ θ / (Real.log X) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      (c / 8 * Y) * (Real.log X) ^ 2
          ≤ (c / 8 * Y) * (4 * (Real.log Y) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (c / 2 * Y) * (Real.log Y) ^ 2 := by ring
      _ ≤ (c * X ^ θ) * (Real.log Y) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hhigh (show 0 ≤ c / 2 by positivity)]
  have hsub : kRange X (X ^ θ) ⊆ kRange X Y := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := (Fourier398.window_mem _ _ _).mp hp
    exact (Fourier398.window_mem _ _ _).mpr ⟨hlo, hhi.trans (by linarith)⟩
  have hcard : (((kRange X (X ^ θ)).filter good).card : ℝ) ≤
      (((kRange X Y).filter good).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter good hsub)
  exact htransfer.trans (hfixed.trans hcard)

end LeanLab.Halupczok2012.Decomp329e
