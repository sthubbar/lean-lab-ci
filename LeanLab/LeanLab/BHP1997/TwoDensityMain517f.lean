/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: bounded variation of the E2 weight along the second outer
variable.

The prime number theorem with partial summation needs the weight of the outer prime `p2` to be
`1 / p2` times a function of bounded variation. This file proves that for the E2 weight of
display 5.15 with the first variable fixed: along the second exponent each linear inequality
defining E2 changes truth value at most once, the factor `1 / log b` is monotone, and the
Buchstab factor is a function of bounded variation of a monotone argument.

No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.PrimeWeighted517
import LeanLab.BHP1997.TwoDensityMain517a
import LeanLab.BHP1997.TwoDensityMain517e

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- P0069 page 51, the set E2 along its second coordinate. Along a nondecreasing sequence of
second exponents, with the first exponent fixed, membership in E2 changes at most 14 times:
E2 is a boolean combination of 14 linear inequalities in the second exponent, each of which
changes truth value at most once. -/
theorem two_pair_region_jumps_second (ε α : ℝ) (e : ℕ → ℝ) (he : ∀ i, e i ≤ e (i + 1))
    (lo hi : ℕ) :
    ((Finset.Ico lo hi).filter (fun i =>
      ¬ (lowerTwoDiscarded ε α (e (i + 1)) ↔ lowerTwoDiscarded ε α (e i)))).card ≤ 14 := by
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
    ([(fun β : ℝ => (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β),
      (fun β : ℝ => β ≤ α),
      (fun β : ℝ => α+2*β ≤ 1),
      (fun β : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε),
      (fun β : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun β : ℝ => β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε),
      (fun β : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun β : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α),
      (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2),
      (fun β : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε),
      (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2),
      (fun β : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)] : List (ℝ → Prop)).toFinset
    (fun (f : ℝ → Prop) (i : ℕ) => f (e i))
    (fun i => lowerTwoDiscarded ε α (e i)) (Finset.Ico lo hi)
    (by
      intro i _ hk
      have h1 := hk (fun β : ℝ => (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β)
        (List.mem_toFinset.mpr
          (.head _))
      have h2 := hk (fun β : ℝ => β ≤ α)
        (List.mem_toFinset.mpr
          (.tail _ (.head _)))
      have h3 := hk (fun β : ℝ => α+2*β ≤ 1)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.head _))))
      have h4 := hk (fun β : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.head _)))))
      have h5 := hk (fun β : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      have h6 := hk (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
      have h7 := hk (fun β : ℝ => β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
      have h8 := hk (fun β : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
      have h9 := hk (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))
      have h10 := hk (fun β : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))
      have h11 := hk (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
      have h12 := hk (fun β : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
      have h13 := hk (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
      have h14 := hk (fun β : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)
        (List.mem_toFinset.mpr
          (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))
      beta_reduce at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      unfold lowerTwoDiscarded upperPairRegion
      simp only [abs_le]
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14])
  refine key.trans ?_
  calc _ ≤ ∑ _k ∈ ([(fun β : ℝ => (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β),
      (fun β : ℝ => β ≤ α),
      (fun β : ℝ => α+2*β ≤ 1),
      (fun β : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε),
      (fun β : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun β : ℝ => β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε),
      (fun β : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε),
      (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β),
      (fun β : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α),
      (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2),
      (fun β : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε),
      (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2),
      (fun β : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)] : List (ℝ → Prop)).toFinset, 1 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [List.mem_toFinset] at hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | hnil
        · exact hup (fun β : ℝ => (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => β ≤ α)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => α+2*β ≤ 1)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => α+2*β ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => 4*α+7*β ≤ 2+2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => 4*α+5*β ≤ 2+2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun β : ℝ => 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α+β)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => 2*β-(2*(1/16-1/10^5))+ε ≤ α)
            (fun s t hst h => by linarith)
        · exact hup (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+3*β-2)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => 4*α+3*β-2 ≤ 2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · exact hup (fun β : ℝ => -(2*(1/16-1/10^5)-ε) ≤ 4*α+β-2)
            (fun s t hst h => by linarith)
        · exact hdown (fun β : ℝ => 4*α+β-2 ≤ 2*(1/16-1/10^5)-ε)
            (fun s t hst h => by linarith)
        · cases hnil
    _ ≤ 14 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
        exact (List.toFinset_card_le _).trans (le_of_eq rfl)

set_option maxHeartbeats 400000 in
/-- P0069 page 51, display 5.17, the E2 sum of display 5.15, bounded variation of the weight
along the second outer variable, as used by `two_pair_second_prime`. For a
fixed integer `a ≤ 2 Y` and a point `m` of J the function of `b` equal to
`ω(log (m / (a b)) / log b) / (a log b)` on E2 and zero off E2 has total variation at most
`72 / a` on any range `(L, a - 1]` with `L ≥ (2 Y) ^ (1 / 20)`. No prime number theorem is
used. -/
theorem two_pair_second_variation (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ → ∀ a : ℕ, 1 ≤ a → a ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ L : ℕ, (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) ≤ (L : ℝ) →
      ∑ i ∈ Finset.Ico (L + 1) (a - 1),
        |(if lowerTwoDiscarded ε (expo ε x a) (expo ε x (i + 1)) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * ((i + 1 : ℕ) : ℝ))) /
                Real.log ((i + 1 : ℕ) : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) / (a : ℝ)
          else 0) -
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x i) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (i : ℝ))) / Real.log (i : ℝ)) /
              Real.log (i : ℝ) / (a : ℝ)
          else 0)| ≤ K / (a : ℝ) := by
  refine ⟨72, (2 : ℝ) ^ 40, fun x hx m hm1 hm2 a ha1 haN L hL => ?_⟩
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  by_cases hLa : L + 1 ≤ a - 1
  swap
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hY20 : (2 : ℝ) ^ 20 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h : ((2 : ℝ) ^ 20) ^ 2 = (2 : ℝ) ^ 40 := by norm_num
    rw [h]
    exact hx
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY20
  have hX0 : 0 < 2 * x ^ (11 / 20 + ε) := by linarith
  have ht2 : (2 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) := by
    have h20 : (2 : ℝ) ^ (20 : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    have h2 : (2 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := h2
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by rw [h20]; linarith) (by norm_num)
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by linarith
  have hL2 : 2 ≤ L := by exact_mod_cast hL2R
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := Nat.floor_le hX0.le
  have hmX : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hm2).trans hNle
  have hlj : ∀ j : ℕ, 2 ≤ j → (1 / 2 : ℝ) < Real.log (j : ℝ) := by
    intro j hj
    have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hj2
    linarith
  have hlogm : Real.log (m : ℝ) ≤ 20 * Real.log ((L + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ)) ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    rw [Real.log_rpow hX0] at h1
    have h2 := Real.log_le_log hm0 hmX
    linarith
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
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ j : ℕ, r j = 1 / Real.log (j : ℝ) / (a : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, ∀ j : ℕ,
      U j = Real.log ((m : ℝ) / ((a : ℝ) * (j : ℝ))) / Real.log (j : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ j : ℕ, S j = ω (U j) := ⟨_, fun _ => rfl⟩
  have hconv : ∑ i ∈ Finset.Ico (L + 1) (a - 1),
        |(if lowerTwoDiscarded ε (expo ε x a) (expo ε x (i + 1)) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * ((i + 1 : ℕ) : ℝ))) /
                Real.log ((i + 1 : ℕ) : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) / (a : ℝ)
          else 0) -
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x i) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (i : ℝ))) / Real.log (i : ℝ)) /
              Real.log (i : ℝ) / (a : ℝ)
          else 0)| =
      ∑ i ∈ Finset.Ico (L + 1) (a - 1),
        |r (i + 1) * S (i + 1) *
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x (i + 1)) then (1 : ℝ) else 0) -
          r i * S i * (if lowerTwoDiscarded ε (expo ε x a) (expo ε x i) then (1 : ℝ) else 0)| := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr, hr, hS, hS, hU, hU]
    congr 1
    split_ifs <;> ring
  rw [hconv]
  -- the factor `1 / log b`
  have hrb : ∀ j : ℕ, 2 ≤ j → 0 ≤ r j ∧ r j ≤ 2 / (a : ℝ) := by
    intro j hj
    have h := hlj j hj
    have h0 : 0 < Real.log (j : ℝ) := by linarith
    rw [hr]
    refine ⟨by positivity, div_le_div_of_nonneg_right ?_ ha0.le⟩
    rw [div_le_iff₀ h0]
    linarith
  have hrmono : ∀ j : ℕ, 2 ≤ j → r (j + 1) ≤ r j := by
    intro j hj
    have h := hlj j hj
    have h0 : 0 < Real.log (j : ℝ) := by linarith
    have hj0 : (0 : ℝ) < (j : ℝ) := by
      have : 0 < j := by omega
      exact_mod_cast this
    rw [hr, hr]
    refine div_le_div_of_nonneg_right ?_ ha0.le
    exact one_div_le_one_div_of_le h0 (Real.log_le_log hj0 (by push_cast; linarith))
  have hrV : ∑ i ∈ Finset.Ico (L + 1) (a - 1), |r (i + 1) - r i| ≤ 2 / (a : ℝ) := by
    have hpt : ∀ i ∈ Finset.Ico (L + 1) (a - 1), |r (i + 1) - r i| = -(r (i + 1) - r i) := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact abs_of_nonpos (by linarith [hrmono i (by omega)])
    rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib, Finset.sum_Ico_sub (f := r) hLa]
    have h1 := (hrb (L + 1) (by omega)).2
    have h2 := (hrb (a - 1) (by omega)).1
    linarith
  -- the Buchstab factor
  have hSb : ∀ j : ℕ, |S j| ≤ 1 := by
    intro j
    rw [hS, abs_of_nonneg (two_density_buchstab_nonneg hω hz _)]
    exact LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _
  have hQ : ∀ j : ℕ, 2 ≤ j → (U j < 1 ↔ (m : ℝ) < (j : ℝ) * ((a : ℝ) * (j : ℝ))) := by
    intro j hj
    have h := hlj j hj
    have h0 : 0 < Real.log (j : ℝ) := by linarith
    have hj0 : (0 : ℝ) < (j : ℝ) := by
      have : 0 < j := by omega
      exact_mod_cast this
    rw [hU, div_lt_one h0, Real.log_lt_log_iff (div_pos hm0 (mul_pos ha0 hj0)) hj0,
      div_lt_iff₀ (mul_pos ha0 hj0)]
  have hSV : ∑ i ∈ Finset.Ico (L + 1) (a - 1), |S (i + 1) - S i| ≤ 21 := by
    by_cases hc : (a : ℝ) ≤ (m : ℝ)
    · have hc0 : 0 ≤ Real.log (m : ℝ) - Real.log (a : ℝ) := by
        have := Real.log_le_log ha0 hc
        linarith
      have hUj : ∀ j : ℕ, 2 ≤ j →
          U j = (Real.log (m : ℝ) - Real.log (a : ℝ)) / Real.log (j : ℝ) - 1 := by
        intro j hj
        have h := hlj j hj
        have h0 : 0 < Real.log (j : ℝ) := by linarith
        have hj0 : (0 : ℝ) < (j : ℝ) := by
          have : 0 < j := by omega
          exact_mod_cast this
        rw [hU, Real.log_div hm0.ne' (mul_pos ha0 hj0).ne', Real.log_mul ha0.ne' hj0.ne']
        field_simp
        ring
      have hQmono : ∀ j : ℕ, (m : ℝ) < (j : ℝ) * ((a : ℝ) * (j : ℝ)) →
          (m : ℝ) < ((j + 1 : ℕ) : ℝ) * ((a : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
        intro j hj
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        push_cast
        nlinarith [mul_nonneg ha0.le hj0]
      have hstep : ∀ i ∈ Finset.Ico (L + 1) (a - 1),
          |S (i + 1) - S i| ≤ -(U (i + 1) - U i) +
            |(if (m : ℝ) < ((i + 1 : ℕ) : ℝ) * ((a : ℝ) * ((i + 1 : ℕ) : ℝ)) then (1 : ℝ)
                else 0) -
              (if (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) then (1 : ℝ) else 0)| := by
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        have hi2 : 2 ≤ i := by omega
        have h := hlj i hi2
        have h0 : 0 < Real.log (i : ℝ) := by linarith
        have hi0 : (0 : ℝ) < (i : ℝ) := by
          have : 0 < i := by omega
          exact_mod_cast this
        have hle : U (i + 1) ≤ U i := by
          rw [hUj _ (by omega), hUj _ hi2]
          have := div_le_div_of_nonneg_left hc0 h0
            (Real.log_le_log hi0 (show (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) by push_cast; linarith))
          linarith
        have hs := two_pair_buchstab_step hω hz hle
        have hind : (if U (i + 1) < 1 ∧ 1 ≤ U i then (1 : ℝ) else 0) ≤
            |(if (m : ℝ) < ((i + 1 : ℕ) : ℝ) * ((a : ℝ) * ((i + 1 : ℕ) : ℝ)) then (1 : ℝ)
                else 0) -
              (if (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) then (1 : ℝ) else 0)| := by
          by_cases hcc : U (i + 1) < 1 ∧ 1 ≤ U i
          · have q1 := (hQ (i + 1) (by omega)).mp hcc.1
            have q2 : ¬ (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) := fun hq =>
              absurd ((hQ i hi2).mpr hq) (not_lt.mpr hcc.2)
            have e1 : (if (m : ℝ) < ((i + 1 : ℕ) : ℝ) * ((a : ℝ) * ((i + 1 : ℕ) : ℝ)) then
                (1 : ℝ) else 0) = 1 := by simp only [q1, ↓reduceIte]
            have e2 : (if (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) then (1 : ℝ) else 0) = 0 := by
              simp only [q2, ↓reduceIte]
            have e3 : (if U (i + 1) < 1 ∧ 1 ≤ U i then (1 : ℝ) else 0) = 1 := by
              simp only [hcc, and_self, ↓reduceIte]
            rw [e1, e2, e3]
            norm_num
          · simp only [hcc, ↓reduceIte]
            exact abs_nonneg _
        rw [hS, hS]
        linarith
      have htel := Finset.sum_Ico_sub (f := U) hLa
      have hjump := indicator_variation_mono_le_one
        (fun j : ℕ => (m : ℝ) < (j : ℝ) * ((a : ℝ) * (j : ℝ))) hQmono (L + 1) (a - 1)
      have hrange : U (L + 1) - U (a - 1) ≤ 20 := by
        rw [hUj _ (by omega), hUj _ (by omega)]
        have h1 := hlj (L + 1) (by omega)
        have h2 := hlj (a - 1) (by omega)
        have h3 : (Real.log (m : ℝ) - Real.log (a : ℝ)) / Real.log ((L + 1 : ℕ) : ℝ) ≤ 20 := by
          rw [div_le_iff₀ (by linarith)]
          have := Real.log_nonneg (show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha1)
          linarith
        have h4 : 0 ≤ (Real.log (m : ℝ) - Real.log (a : ℝ)) / Real.log ((a - 1 : ℕ) : ℝ) :=
          div_nonneg hc0 (by linarith)
        linarith
      calc ∑ i ∈ Finset.Ico (L + 1) (a - 1), |S (i + 1) - S i|
          ≤ ∑ i ∈ Finset.Ico (L + 1) (a - 1), (-(U (i + 1) - U i) +
            |(if (m : ℝ) < ((i + 1 : ℕ) : ℝ) * ((a : ℝ) * ((i + 1 : ℕ) : ℝ)) then (1 : ℝ)
                else 0) -
              (if (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) then (1 : ℝ) else 0)|) :=
            Finset.sum_le_sum hstep
        _ = -(∑ i ∈ Finset.Ico (L + 1) (a - 1), (U (i + 1) - U i)) +
            ∑ i ∈ Finset.Ico (L + 1) (a - 1),
            |(if (m : ℝ) < ((i + 1 : ℕ) : ℝ) * ((a : ℝ) * ((i + 1 : ℕ) : ℝ)) then (1 : ℝ)
                else 0) -
              (if (m : ℝ) < (i : ℝ) * ((a : ℝ) * (i : ℝ)) then (1 : ℝ) else 0)| := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        _ ≤ 21 := by
            rw [htel]
            linarith
    · have hS0 : ∀ j : ℕ, 2 ≤ j → S j = 0 := by
        intro j hj
        have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        rw [hS]
        refine hz _ ((hQ j hj).mpr ?_)
        have hlt : (m : ℝ) < (a : ℝ) := not_le.mp hc
        nlinarith [mul_pos ha0 (show (0 : ℝ) < (j : ℝ) by linarith)]
      rw [Finset.sum_eq_zero]
      · norm_num
      · intro i hi
        have hi' := Finset.mem_Ico.mp hi
        rw [hS0 (i + 1) (by omega), hS0 i (by omega), sub_self, abs_zero]
  have hprod := variation_mul_le r S (a := L + 1) (b := a - 1) (M := 2 / (a : ℝ))
    (V := 2 / (a : ℝ)) (J := 21) (by positivity)
    (fun n hn => by
      have hn' := Finset.mem_Icc.mp hn
      have h := hrb n (by omega)
      rw [abs_of_nonneg h.1]
      exact h.2)
    (fun n _ => hSb n) hrV hSV
  have hJ := two_pair_region_jumps_second ε (expo ε x a) (fun i => expo ε x i) hmono (L + 1)
    (a - 1)
  have hfin := variation_mul_indicator_le (fun j => r j * S j)
    (fun b : ℕ => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (a := L + 1) (b := a - 1)
    (M := 2 / (a : ℝ)) (V := 2 / (a : ℝ) + 2 / (a : ℝ) * 21) (J := 14) (by positivity)
    (fun n hn => by
      have hn' := Finset.mem_Icc.mp hn
      have h := hrb n (by omega)
      have h1 := hSb n
      show |r n * S n| ≤ 2 / (a : ℝ)
      rw [abs_mul, abs_of_nonneg h.1]
      calc r n * |S n| ≤ 2 / (a : ℝ) * 1 :=
            mul_le_mul h.2 h1 (abs_nonneg _) (by positivity)
        _ = 2 / (a : ℝ) := by ring)
    hprod hJ
  refine hfin.trans (le_of_eq ?_)
  push_cast
  ring

end LeanLab.BHP1997.LowerShortC165
