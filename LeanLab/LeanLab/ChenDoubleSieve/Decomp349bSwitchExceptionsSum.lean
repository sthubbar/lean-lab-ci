import LeanLab.ChenDoubleSieve.Decomp349bSwitchExceptions

/-!
Proof of the LEAF `leaf_switch_exceptions_sum` of Decomp349bSwitchExceptions, Wu 2004
page 40, the summed exceptions of Chen's switching. Source: https://arxiv.org/pdf/0705.1652.
With it, `leaf_switching` of Decomp349bSplitFinite is proved outright through
`leaf_switching_proved` and `leaf_switch_exceptions_proved`.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- K times log N to the k over N to c tends to 0 for c positive. -/
theorem swe_decay (k : ℕ) {c : ℝ} (hc : 0 < c) (K : ℝ) :
    Tendsto (fun N : ℕ => K * log (N : ℝ) ^ k / (N : ℝ) ^ c) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hc).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ => K * (log x ^ (k : ℝ) / x ^ c)) atTop (𝓝 0) := by
    simpa using h.const_mul K
  refine (h'.comp tendsto_natCast_atTop_atTop).congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp, Real.rpow_natCast]
  ring

/-- `leaf_switch_exceptions_sum`, exactly as stated in Decomp349bSwitchExceptions,
Wu 2004 page 40: each pair term is at most c log N times N to 2/3 plus N over N to
kappa2, all over p q, since p q is at most N to 2/3 and p at least N to kappa2; the
reciprocal pair sum is at most 1 plus log N squared, and Theta N is at least the twin
prime constant times N over log N squared. -/
theorem leaf_switch_exceptions_sum_proved :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        ∑ q ∈ switchedPairs N i,
          (2 + log N / log 2 + (N : ℝ) / ((q.1 : ℝ) * (q.1 * q.2))) ≤ η * Θ N := by
  intro η hη
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have htw := LeanLab.ChenExplicit.twinC_pos
  set c1 : ℝ := 2 + 1 / log 2 with hc1
  have hc10 : 0 < c1 := by positivity
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hd1 := swe_decay 5 (show (0 : ℝ) < 1 / 3 by norm_num) (4 * c1)
  have hd2 := swe_decay 4 hk2 4
  have hε : 0 < η * LeanLab.ChenExplicit.twinC / 2 := by positivity
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp (hd1.eventually (gt_mem_nhds hε))
  obtain ⟨M2, hM2⟩ := eventually_atTop.mp (hd2.eventually (gt_mem_nhds hε))
  refine ⟨max 3 (max M1 M2), fun N hEven hN i hi => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_left hN
  have e1 := hM1 N (le_of_max_le_left (le_of_max_le_right hN))
  have e2 := hM2 N (le_of_max_le_right (le_of_max_le_right hN))
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  set L := log (N : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 < L := by linarith
  set A : ℝ := c1 * L * (N : ℝ) ^ (2 / 3 : ℝ) + (N : ℝ) / (N : ℝ) ^ kappa2 with hA
  have hNk : 0 < (N : ℝ) ^ kappa2 := Real.rpow_pos_of_pos hN0 _
  have hN23 : 0 < (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hA0 : 0 ≤ A := by positivity
  set Q := (Finset.range (N + 1)).filter Nat.Prime with hQ
  -- termwise bound
  have hterm : ∀ x ∈ switchedPairs N i,
      2 + L / log 2 + (N : ℝ) / ((x.1 : ℝ) * (x.1 * x.2)) ≤ A * (1 / ((x.1 : ℝ) * x.2)) := by
    intro x hx
    have hfree := bc_switched_subset N i hx
    obtain ⟨_, h3⟩ := bc_log_ratio (by omega) hfree
    obtain ⟨hlow, _⟩ := bc_free_lower (by omega) hfree
    obtain ⟨hp, hq, _, _⟩ := sw_mem hx
    have hp0 : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < x.2 := by exact_mod_cast hq.pos
    have hpq0 : (0 : ℝ) < (x.1 : ℝ) * x.2 := mul_pos hp0 hq0
    have hpq23 : (x.1 : ℝ) * x.2 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.log_div hN0.ne' hpq0.ne'] at h3
      rw [← Real.exp_log hpq0, Real.rpow_def_of_pos hN0]
      exact Real.exp_le_exp.mpr (by rw [← hL] at h3 ⊢; linarith)
    have h1 : 2 + L / log 2 ≤ c1 * L * (N : ℝ) ^ (2 / 3 : ℝ) * (1 / ((x.1 : ℝ) * x.2)) := by
      have hge : 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (1 / ((x.1 : ℝ) * x.2)) := by
        rw [mul_one_div, le_div_iff₀ hpq0]; linarith
      have : 2 + L / log 2 ≤ c1 * L := by
        rw [hc1]; have : L / log 2 = (1 / log 2) * L := by ring
        rw [this]; nlinarith
      calc 2 + L / log 2 ≤ c1 * L := this
        _ = c1 * L * 1 := by ring
        _ ≤ c1 * L * ((N : ℝ) ^ (2 / 3 : ℝ) * (1 / ((x.1 : ℝ) * x.2))) :=
            mul_le_mul_of_nonneg_left hge (by positivity)
        _ = _ := by ring
    have h2 : (N : ℝ) / ((x.1 : ℝ) * (x.1 * x.2)) ≤
        (N : ℝ) / (N : ℝ) ^ kappa2 * (1 / ((x.1 : ℝ) * x.2)) := by
      rw [div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_left hN0.le (by positivity)
      exact mul_le_mul_of_nonneg_right hlow hpq0.le
    calc 2 + L / log 2 + (N : ℝ) / ((x.1 : ℝ) * (x.1 * x.2))
        ≤ c1 * L * (N : ℝ) ^ (2 / 3 : ℝ) * (1 / ((x.1 : ℝ) * x.2)) +
          (N : ℝ) / (N : ℝ) ^ kappa2 * (1 / ((x.1 : ℝ) * x.2)) := add_le_add h1 h2
      _ = A * (1 / ((x.1 : ℝ) * x.2)) := by rw [hA]; ring
  -- reciprocal pair sum
  have hsubQ : switchedPairs N i ⊆ Q ×ˢ Q := by
    intro x hx
    obtain ⟨hp, hq, _, _⟩ := sw_mem hx
    have hx' := hx
    simp only [switchedPairs, Wu08Sum.P2, Finset.mem_filter] at hx'
    have hr := Finset.mem_product.mp hx'.1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by have := Finset.mem_range.mp hr.1; omega), hp⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr.2; omega), hq⟩⟩
  have hH := bc_prime_recip_le N
  have hrec : ∑ x ∈ switchedPairs N i, (1 / ((x.1 : ℝ) * x.2)) ≤ (1 + L) ^ 2 := by
    calc ∑ x ∈ switchedPairs N i, (1 / ((x.1 : ℝ) * x.2))
        ≤ ∑ x ∈ Q ×ˢ Q, (1 / ((x.1 : ℝ) * x.2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubQ (fun _ _ _ => by positivity)
      _ = (∑ p ∈ Q, (1 : ℝ) / p) * ∑ q ∈ Q, (1 : ℝ) / q := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [one_div_mul_one_div]
      _ ≤ (1 + L) * (1 + L) := mul_le_mul hH hH (Finset.sum_nonneg fun _ _ => by positivity)
          (by linarith)
      _ = (1 + L) ^ 2 := by ring
  have hsum : ∑ x ∈ switchedPairs N i, (2 + L / log 2 + (N : ℝ) / ((x.1 : ℝ) * (x.1 * x.2))) ≤
      A * (4 * L ^ 2) := by
    calc _ ≤ ∑ x ∈ switchedPairs N i, A * (1 / ((x.1 : ℝ) * x.2)) := Finset.sum_le_sum hterm
      _ = A * ∑ x ∈ switchedPairs N i, (1 / ((x.1 : ℝ) * x.2)) := by rw [Finset.mul_sum]
      _ ≤ A * (1 + L) ^ 2 := mul_le_mul_of_nonneg_left hrec hA0
      _ ≤ A * (4 * L ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hA0
  -- compare with Theta
  have hΘ : LeanLab.ChenExplicit.twinC * N / L ^ 2 ≤ Θ N := by
    unfold Θ CN
    rw [← hL]
    have := oddFactor_one_le N
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h := mul_le_mul_of_nonneg_right this (mul_pos htw hN0).le
    nlinarith [h]
  have hsplitN : (N : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hN13 : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hgoal : A * (4 * L ^ 2) * (L ^ 2 / N) ≤ η * LeanLab.ChenExplicit.twinC := by
    have hx1 : c1 * L * (N : ℝ) ^ (2 / 3 : ℝ) * (4 * L ^ 2) * (L ^ 2 / N) =
        4 * c1 * L ^ 5 / (N : ℝ) ^ (1 / 3 : ℝ) := by
      have hLN : L ^ 2 / N = L ^ 2 / ((N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ)) := by
        rw [← hsplitN]
      rw [hLN]; field_simp
    have hx2 : (N : ℝ) / (N : ℝ) ^ kappa2 * (4 * L ^ 2) * (L ^ 2 / N) =
        4 * L ^ 4 / (N : ℝ) ^ kappa2 := by
      field_simp
    have : A * (4 * L ^ 2) * (L ^ 2 / N) =
        4 * c1 * L ^ 5 / (N : ℝ) ^ (1 / 3 : ℝ) + 4 * L ^ 4 / (N : ℝ) ^ kappa2 := by
      rw [← hx1, ← hx2, hA]; ring
    rw [this]
    linarith
  have hfinal : A * (4 * L ^ 2) ≤ η * (LeanLab.ChenExplicit.twinC * N / L ^ 2) := by
    have hpos : 0 < L ^ 2 / N := by positivity
    have := (le_div_iff₀ hpos).mpr hgoal
    calc A * (4 * L ^ 2) ≤ η * LeanLab.ChenExplicit.twinC / (L ^ 2 / N) := this
      _ = η * (LeanLab.ChenExplicit.twinC * N / L ^ 2) := by field_simp
  calc _ ≤ A * (4 * L ^ 2) := hsum
    _ ≤ η * (LeanLab.ChenExplicit.twinC * N / L ^ 2) := hfinal
    _ ≤ η * Θ N := mul_le_mul_of_nonneg_left hΘ hη.le

/-- `leaf_switch_exceptions`, exactly as stated in Decomp349bSwitching, from the per pair
bound `swe_pair_le` and the summed LEAF. Fully proved through leaf_switch_exceptions_sum_proved. -/
theorem leaf_switch_exceptions_full :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        ∑ q ∈ switchedPairs N i, (((primeSequence N).filter (fun a => q.1 * q.2 ∣ a ∧
          (a = q.1 * q.2 ∨ q.1 * (q.1 * q.2) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℝ) ≤
          η * Θ N := by
  intro η hη
  obtain ⟨N0, hN0⟩ := leaf_switch_exceptions_sum_proved η hη
  refine ⟨max N0 1, fun N hEven hN i hi => le_trans ?_ (hN0 N hEven (le_of_max_le_left hN) i hi)⟩
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hp, hq', _, _⟩ := sw_mem hq
  exact_mod_cast swe_pair_le N q.1 q.2 hp hq' (le_of_max_le_right hN)

/-- `leaf_switching`, exactly as stated in Decomp349bSplitFinite, Wu 2004 page 40:
Chen's switching principle, proved from `sw_pair_le` for each pair and the
exceptional count LEAF `leaf_switch_exceptions`. Fully proved through leaf_switch_exceptions_full. -/
theorem leaf_switching_full :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ switchedCount N i + η * Θ N := by
  intro η hη
  obtain ⟨N0, hN0⟩ := leaf_switch_exceptions_full η hη
  refine ⟨max N0 2, fun N hEven hN i hi => ?_⟩
  have hE := hN0 N hEven (le_of_max_le_left hN) i hi
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  refine le_trans ?_ (add_le_add (le_refl (switchedCount N i)) hE)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma1 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma1 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 6 := by
      simp [switchedPairs]
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 q.2 hp hq'
      (sw_size_q (by omega) (by norm_num [sigma1]) hc hpq) (by positivity)
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma2 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma2 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 7 := by
      simp [switchedPairs]
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [show (7 : Fin 12) ≠ 6 by decide, ↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 q.2 hp hq'
      (sw_size_q (by omega) (by norm_num [sigma2]) hc hpq) (by positivity)
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
        (N : ℝ) ^ sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) ((N : ℝ) ^ sigma1) : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
        (N : ℝ) ^ sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 9 := by
      simp only [switchedPairs, Wu08Sum.P2, show (9 : Fin 12) ≠ 6 by decide,
        show (9 : Fin 12) ≠ 7 by decide, ↓reduceIte]
      apply Finset.filter_congr
      intro x _
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
        refine ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, ?_, h8⟩
        exact_mod_cast h6.trans_le h7
      · rintro ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, _, h8⟩
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [show (9 : Fin 12) ≠ 6 by decide, show (9 : Fin 12) ≠ 7 by decide,
      ↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 _ hp hq' (sw_size_nine hN2 hc.1 hc.2.2) (by positivity)

end LeanLab.ChenDoubleSieve.Task349

