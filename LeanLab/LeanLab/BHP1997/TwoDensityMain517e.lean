/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: bounded variation of the E2 weight along the first outer
variable.

The prime number theorem with partial summation needs the weight of the outer prime `p1` to be
`1 / p1` times a function of bounded variation. This file proves that for the E2 weight of
display 5.15: along the first exponent each linear inequality defining E2 changes truth value
at most once, and the Buchstab factor is a function of bounded variation of a monotone
argument.

No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.PrimeWeighted517
import LeanLab.BHP1997.TwoDensityMain517a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- P0069 page 51, the set E2 along its first coordinate. Along a nondecreasing sequence of
first exponents, with the second exponent fixed, membership in E2 changes at most 14 times:
E2 is a boolean combination of 14 linear inequalities in the first exponent, each of which
changes truth value at most once. -/
theorem two_pair_region_jumps_first (ε β : ℝ) (e : ℕ → ℝ) (he : ∀ i, e i ≤ e (i + 1))
    (lo hi : ℕ) :
    ((Finset.Ico lo hi).filter (fun i =>
      ¬ (lowerTwoDiscarded ε (e (i + 1)) β ↔ lowerTwoDiscarded ε (e i) β))).card ≤ 14 := by
  have hup : ∀ f : ℝ → Prop, (∀ s t, s ≤ t → f s → f t) →
      ((Finset.Ico lo hi).filter (fun i => ¬ (f (e (i + 1)) ↔ f (e i)))).card ≤ 1 := by
    intro f hf
    have h := indicator_variation_mono_le_one (fun i => f (e i))
      (fun i h => hf _ _ (he i) h) lo hi
    have h2 := indicator_variation_eq_card (fun i => f (e i)) (Finset.Ico lo hi)
    have h3 := le_of_eq_of_le h2.symm h
    exact_mod_cast h3
  have hdown : ∀ f : ℝ → Prop, (∀ s t, s ≤ t → f t → f s) →
      ((Finset.Ico lo hi).filter (fun i => ¬ (f (e (i + 1)) ↔ f (e i)))).card ≤ 1 := by
    intro f hf
    have h := indicator_variation_anti_le_one (fun i => f (e i))
      (fun i h => hf _ _ (he i) h) lo hi
    have h2 := indicator_variation_eq_card (fun i => f (e i)) (Finset.Ico lo hi)
    have h3 := le_of_eq_of_le h2.symm h
    exact_mod_cast h3
  have key := indicator_changes_le_atoms
    ([(fun α : ℝ => β ≤ α),
      (fun α : ℝ => α ≤ 1/2),
      (fun α : ℝ => α+2*β ≤ 1),
      (fun α : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε),
      (fun α : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun α : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun α : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α),
      (fun α : ℝ => α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε),
      (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2),
      (fun α : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε),
      (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2),
      (fun α : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)] : List (ℝ → Prop)).toFinset
    (fun (f : ℝ → Prop) (i : ℕ) => f (e i))
    (fun i => lowerTwoDiscarded ε (e i) β) (Finset.Ico lo hi)
    (by
      intro i _ hk
      have h1 := hk (fun α : ℝ => β ≤ α) (List.mem_toFinset.mpr
        (.head _))
      have h2 := hk (fun α : ℝ => α ≤ 1/2) (List.mem_toFinset.mpr
        (.tail _ (.head _)))
      have h3 := hk (fun α : ℝ => α+2*β ≤ 1) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.head _))))
      have h4 := hk (fun α : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.head _)))))
      have h5 := hk (fun α : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      have h6 := hk (fun α : ℝ =>
        1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
      have h7 := hk (fun α : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
      have h8 := hk (fun α : ℝ =>
        1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
      have h9 := hk (fun α : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))
      have h10 := hk (fun α : ℝ => α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))
      have h11 := hk (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
      have h12 := hk (fun α : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
      have h13 := hk (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
      have h14 := hk (fun α : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε) (List.mem_toFinset.mpr
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))
      beta_reduce at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      unfold lowerTwoDiscarded upperPairRegion
      simp only [abs_le]
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14])
  refine key.trans ?_
  calc _ ≤ ∑ _k ∈ ([(fun α : ℝ => β ≤ α),
      (fun α : ℝ => α ≤ 1/2),
      (fun α : ℝ => α+2*β ≤ 1),
      (fun α : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε),
      (fun α : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun α : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun α : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α),
      (fun α : ℝ => α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε),
      (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2),
      (fun α : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε),
      (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2),
      (fun α : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)] : List (ℝ → Prop)).toFinset, 1 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [List.mem_toFinset] at hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | hnil
        · exact hup (fun α : ℝ => β ≤ α)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => α ≤ 1/2)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => α+2*β ≤ 1)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun α : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
            (fun s t hst h => by linarith)
        · exact hup (fun α : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun α : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2)
            (fun s t hst h => by linarith)
        · exact hdown (fun α : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · cases hnil
    _ ≤ 14 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
        exact (List.toFinset_card_le _).trans (le_of_eq rfl)

/-- P0069 page 51 display 5.17. One step of the variation of Buchstab's function with the zero
extension along a decreasing argument: the Lipschitz part plus the single jump at 1. -/
theorem two_pair_buchstab_step {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {u u' : ℝ} (h : u' ≤ u) :
    |ω u' - ω u| ≤ (u - u') + (if u' < 1 ∧ 1 ≤ u then 1 else 0) := by
  have hite : (0 : ℝ) ≤ (if u' < 1 ∧ 1 ≤ u then 1 else 0) := by split_ifs <;> norm_num
  by_cases h1 : 1 ≤ u'
  · have := two_density_buchstab_lipschitz hω hz h1 h
    linarith
  · have h1' : u' < 1 := not_le.mp h1
    by_cases h2 : 1 ≤ u
    · have h0 := two_density_buchstab_nonneg hω hz u
      have h3 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz u
      have hc : (if u' < 1 ∧ 1 ≤ u then (1 : ℝ) else 0) = 1 := by simp [h1', h2]
      rw [hz _ h1', hc, zero_sub, abs_neg, abs_of_nonneg h0]
      linarith
    · rw [hz _ h1', hz _ (not_le.mp h2), sub_self, abs_zero]
      linarith

/-- P0069 page 51, display 5.17, the E2 sum of display 5.15, bounded variation of the weight
along the first outer variable, as used by `two_pair_first_prime`. For a fixed
level `b ≥ (2 Y) ^ (1 / 10)` and a point `m` of J the function of `a` equal to
`ω(log (m / (a b)) / log b) / (b log b)` on E2 and zero off E2 has total variation at most
`50 / b` on `(b, 2 Y]`. No prime number theorem is used. -/
theorem two_pair_first_variation (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ → ∀ b : ℕ,
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ) → b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |(if lowerTwoDiscarded ε (expo ε x (i + 1)) (expo ε x b) then
            ω (Real.log ((m : ℝ) / (((i + 1 : ℕ) : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / (b : ℝ)
          else 0) -
          (if lowerTwoDiscarded ε (expo ε x i) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((i : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / (b : ℝ)
          else 0)| ≤ K / (b : ℝ) := by
  refine ⟨50, (2 : ℝ) ^ 36, fun x hx m hm1 hm2 b hWb hbN => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hX0 : 0 < 2 * x ^ (11 / 20 + ε) := by linarith
  have hW2 : (2 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have h10 : (2 : ℝ) ^ (10 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    have h2 : (2 : ℝ) = ((2 : ℝ) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 : ℝ) = ((2 : ℝ) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) := h2
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by rw [h10]; linarith) (by norm_num)
  have hb2R : (2 : ℝ) ≤ (b : ℝ) := by linarith
  have hb2 : 2 ≤ b := by exact_mod_cast hb2R
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hlb : (1 / 2 : ℝ) < Real.log (b : ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hb2R
    linarith
  have hlb0 : 0 < Real.log (b : ℝ) := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := Nat.floor_le hX0.le
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 10 * Real.log (b : ℝ) := by
    have h1 : Real.log ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) ≤ Real.log (b : ℝ) :=
      Real.log_le_log (by linarith) hWb
    rw [Real.log_rpow hX0] at h1
    by_cases hN0 : ⌊2 * x ^ (11 / 20 + ε)⌋₊ = 0
    · rw [hN0, Nat.cast_zero, Real.log_zero]
      linarith
    · have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hN0) hNle
      linarith
  obtain ⟨hM, -, -⟩ := two_cofactor_density_props ω hω hz hb2
  have hZ1 : 1 ≤ scaleZ ε x := by
    have hZ : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
    rw [hZ]; linarith
  have hmono : ∀ i : ℕ, expo ε x i ≤ expo ε x (i + 1) := by
    intro i
    unfold expo
    refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg hZ1)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, ∀ j : ℕ,
      U j = Real.log ((m : ℝ) / ((j : ℝ) * (b : ℝ))) / Real.log (b : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ j : ℕ, g j = ω (U j) / Real.log (b : ℝ) / (b : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hconv : ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |(if lowerTwoDiscarded ε (expo ε x (i + 1)) (expo ε x b) then
            ω (Real.log ((m : ℝ) / (((i + 1 : ℕ) : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / (b : ℝ)
          else 0) -
          (if lowerTwoDiscarded ε (expo ε x i) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((i : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / (b : ℝ)
          else 0)| =
      ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |g (i + 1) * (if lowerTwoDiscarded ε (expo ε x (i + 1)) (expo ε x b) then (1 : ℝ)
            else 0) -
          g i * (if lowerTwoDiscarded ε (expo ε x i) (expo ε x b) then (1 : ℝ) else 0)| := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, hg, hU, hU]
    congr 1
    split_ifs <;> simp
  rw [hconv]
  have hgM : ∀ n ∈ Finset.Icc (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊, |g n| ≤ 2 / (b : ℝ) := by
    intro n _
    rw [hg, hU, abs_div, abs_of_pos hb0]
    exact div_le_div_of_nonneg_right (hM _) hb0.le
  -- the variation of the Buchstab factor
  have hUj : ∀ j : ℕ, 1 ≤ j →
      U j = (Real.log (m : ℝ) - Real.log (j : ℝ) - Real.log (b : ℝ)) / Real.log (b : ℝ) := by
    intro j hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    rw [hU, Real.log_div hm0.ne' (mul_pos hj0 hb0).ne', Real.log_mul hj0.ne' hb0.ne']
    ring
  have hQ : ∀ j : ℕ, 1 ≤ j → (U j < 1 ↔ (m : ℝ) < (b : ℝ) * ((j : ℝ) * (b : ℝ))) := by
    intro j hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    rw [hU, div_lt_one hlb0, Real.log_lt_log_iff (div_pos hm0 (mul_pos hj0 hb0)) hb0,
      div_lt_iff₀ (mul_pos hj0 hb0)]
  have hQmono : ∀ j : ℕ, (m : ℝ) < (b : ℝ) * ((j : ℝ) * (b : ℝ)) →
      (m : ℝ) < (b : ℝ) * (((j + 1 : ℕ) : ℝ) * (b : ℝ)) := by
    intro j hj
    push_cast
    nlinarith [mul_pos hb0 hb0]
  have hstep : ∀ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      |g (i + 1) - g i| ≤ (-(U (i + 1) - U i) +
        |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
          (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)|) *
        (2 / (b : ℝ)) := by
    intro i hi
    have hi1 : 1 ≤ i := by
      have := (Finset.mem_Ico.mp hi).1
      omega
    have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hle : U (i + 1) ≤ U i := by
      rw [hUj _ (by omega), hUj _ hi1]
      refine div_le_div_of_nonneg_right ?_ hlb0.le
      have := Real.log_le_log hi0 (show (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) by push_cast; linarith)
      linarith
    have hs := two_pair_buchstab_step hω hz hle
    have hind : (if U (i + 1) < 1 ∧ 1 ≤ U i then (1 : ℝ) else 0) ≤
        |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
          (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)| := by
      by_cases hc : U (i + 1) < 1 ∧ 1 ≤ U i
      · have q1 := (hQ (i + 1) (by omega)).mp hc.1
        have q2 : ¬ (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) := fun hq =>
          absurd ((hQ i hi1).mpr hq) (not_lt.mpr hc.2)
        have e1 : (if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) =
            1 := by simp only [q1, ↓reduceIte]
        have e2 : (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) = 0 := by
          simp only [q2, ↓reduceIte]
        have e3 : (if U (i + 1) < 1 ∧ 1 ≤ U i then (1 : ℝ) else 0) = 1 := by
          simp only [hc, and_self, ↓reduceIte]
        rw [e1, e2, e3]
        norm_num
      · simp only [hc, ↓reduceIte]
        exact abs_nonneg _
    have hnum : |ω (U (i + 1)) - ω (U i)| ≤ -(U (i + 1) - U i) +
        |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
          (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)| := by
      linarith
    have hnum0 := (abs_nonneg _).trans hnum
    rw [hg, hg, ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos hb0, abs_of_pos hlb0,
      div_div, div_le_iff₀ (mul_pos hlb0 hb0)]
    have h1 : (1 : ℝ) ≤ 2 / (b : ℝ) * (Real.log (b : ℝ) * (b : ℝ)) := by
      have : 2 / (b : ℝ) * (Real.log (b : ℝ) * (b : ℝ)) = 2 * Real.log (b : ℝ) := by
        field_simp
      rw [this]; linarith
    calc |ω (U (i + 1)) - ω (U i)| ≤ _ := hnum
      _ ≤ (-(U (i + 1) - U i) +
        |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
          (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)|) *
          (2 / (b : ℝ) * (Real.log (b : ℝ) * (b : ℝ))) := le_mul_of_one_le_right hnum0 h1
      _ = _ := by ring
  have hgV : ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊, |g (i + 1) - g i| ≤
      22 / (b : ℝ) := by
    by_cases hbN' : b + 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊
    swap
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      positivity
    have htel := Finset.sum_Ico_sub (f := U) hbN'
    have hjump := indicator_variation_mono_le_one
      (fun j : ℕ => (m : ℝ) < (b : ℝ) * ((j : ℝ) * (b : ℝ))) hQmono (b + 1)
      ⌊2 * x ^ (11 / 20 + ε)⌋₊
    have hrange : U (b + 1) - U ⌊2 * x ^ (11 / 20 + ε)⌋₊ ≤ 10 := by
      rw [hUj _ (by omega), hUj _ (by omega), ← sub_div, div_le_iff₀ hlb0]
      have := Real.log_natCast_nonneg (b + 1)
      linarith
    calc ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊, |g (i + 1) - g i|
        ≤ ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊, (-(U (i + 1) - U i) +
          |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
            (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)|) *
          (2 / (b : ℝ)) := Finset.sum_le_sum hstep
      _ = (-(∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊, (U (i + 1) - U i)) +
          ∑ i ∈ Finset.Ico (b + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          |(if (m : ℝ) < (b : ℝ) * (((i + 1 : ℕ) : ℝ) * (b : ℝ)) then (1 : ℝ) else 0) -
            (if (m : ℝ) < (b : ℝ) * ((i : ℝ) * (b : ℝ)) then (1 : ℝ) else 0)|) *
          (2 / (b : ℝ)) := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      _ ≤ (10 + 1) * (2 / (b : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [htel]
          linarith
      _ = 22 / (b : ℝ) := by ring
  have hJ := two_pair_region_jumps_first ε (expo ε x b) (fun i => expo ε x i) hmono (b + 1)
    ⌊2 * x ^ (11 / 20 + ε)⌋₊
  have hfin := variation_mul_indicator_le g
    (fun a : ℕ => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (M := 2 / (b : ℝ)) (V := 22 / (b : ℝ)) (J := 14) (by positivity) hgM hgV hJ
  refine hfin.trans (le_of_eq ?_)
  push_cast
  ring

end LeanLab.BHP1997.LowerShortC165
