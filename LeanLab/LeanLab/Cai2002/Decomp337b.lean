/-
Cai 2002 pages 602 to 604 displays 4.8 to 4.14.
The switched sequence keeps its indices and all endpoint multiplicities.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Decomp337a

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- The closed lower endpoint required by p at most N to theta in display 4.8.
The strict endpoint of switchedIndex306 is recovered with an explicit boundary loss. -/
def switchedClosedIndex337 (N : ℕ) (E : Finset ℕ) : Finset (ℕ × ℕ) :=
  (E ×ˢ range N).filter (fun b => b.2.Prime ∧ b.2.Coprime N ∧
    (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ (b.1 * b.2 : ℕ) ∧ b.1 * b.2 < N)

/-- Closing the lower product endpoint adds at most one index for each e.
Derived endpoint check for page 602 display 4.8. The selection retains multiplicity. -/
theorem switched_closed_selection337 (N : ℕ) (hN : 2 ≤ N) (E : Finset ℕ)
    (F : ℕ → Prop) [DecidablePred F] :
    ((switchedClosedIndex337 N E).filter (fun b => F (N - b.1 * b.2))).card ≤
      ((switchedIndex306 N E).filter (fun b => F (N - b.1 * b.2))).card + E.card := by
  classical
  let B := (switchedClosedIndex337 N E).filter
    (fun b => (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) = (b.1 * b.2 : ℕ))
  have hpow : (N : ℝ) ^ (0.95 : ℝ) < N := by
    simpa using rpow_lt_rpow_of_exponent_lt
      (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
      (by norm_num : (0.95 : ℝ) < 1)
  have hB : B.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro b hb
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp hb).1).1).1
    · intro b hb c hc he
      have hbEq := (mem_filter.mp hb).2
      have hcEq := (mem_filter.mp hc).2
      have hprod : b.1 * b.2 = c.1 * c.2 := by exact_mod_cast hbEq.symm.trans hcEq
      have hbpos : 0 < b.1 := by
        by_contra hh
        have hbzero : b.1 = 0 := by omega
        simp only [hbzero, zero_mul, Nat.cast_zero] at hbEq
        linarith
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left hbpos
      simpa only [he] using hprod
  have hsub : (switchedClosedIndex337 N E).filter (fun b => F (N - b.1 * b.2)) ⊆
      ((switchedIndex306 N E).filter (fun b => F (N - b.1 * b.2))) ∪ B := by
    intro b hb
    obtain ⟨hbT, hbF⟩ := mem_filter.mp hb
    obtain ⟨hbE, hp, hc, hlo, hhi⟩ := mem_filter.mp hbT
    by_cases heq : (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) = (b.1 * b.2 : ℕ)
    · exact mem_union_right _ (mem_filter.mpr ⟨hbT, heq⟩)
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hbE, hp, hc, lt_of_le_of_ne hlo heq, hhi⟩, hbF⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hB _))

/-- Ordered prime triples supply the square root cutoff and the closed switched index.
Derived finite data for page 602 display 4.8 and page 604 display 4.15. -/
theorem triple_switch_data337 (N p x y r : ℕ) (hp : p ∈ Pset N 0.95)
    (hx : x.Prime) (hy : y.Prime) (hr : r.Prime) (hyr : y < r)
    (hprod : N - p = x * y * r) :
    (y : ℝ) < ((N : ℝ) / x) ^ (1 / 2 : ℝ) ∧
      (x * y).Coprime N ∧ ∀ E : Finset ℕ, x * y ∈ E →
        (x * y, r) ∈ switchedClosedIndex337 N E ∧ N - (x * y) * r = p := by
  obtain ⟨hpN, hpPrime, hpCut, hpCop, _⟩ := mem_Pset hp
  have hp0 : 0 < p := hpPrime.pos
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx.pos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy.pos
  have hyrR : (y : ℝ) < r := by exact_mod_cast hyr
  have hs : x * y * r + p = N := by omega
  have hsR : (x : ℝ) * y * r + p = N := by exact_mod_cast hs
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hroot : (y : ℝ) < ((N : ℝ) / x) ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow]
    apply (lt_sqrt (Nat.cast_nonneg y)).mpr
    apply (lt_div_iff₀ hxR).mpr
    nlinarith [mul_pos (mul_pos hxR hyR) (sub_pos.mpr hyrR)]
  have hxyD : x * y ∣ N - p := by rw [hprod]; exact dvd_mul_right _ _
  have hrD : r ∣ N - p := by rw [hprod]; exact dvd_mul_left _ _
  have hrN : r < N :=
    lt_of_le_of_lt (Nat.le_of_dvd (by omega : 0 < N - p) hrD) (by omega)
  refine ⟨hroot, hpCop.coprime_dvd_left hxyD, fun E hE => ?_⟩
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hE, mem_range.mpr hrN⟩,
    hr, hpCop.coprime_dvd_left hrD, ?_, ?_⟩, ?_⟩
  · change (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) ≤ ((x * y) * r : ℕ)
    push_cast
    linarith
  · change (x * y) * r < N
    omega
  · omega

/-- Every mixed triple counted by rho2 has a prime value in the closed switched index.
Page 602 display 4.8. This is a fibre bound and retains the indexed multiplicity. -/
theorem rho2_closed_fiber337 (N p : ℕ) (hN : 2 ≤ N) (hp : p ∈ Pset N 0.95) :
    rho2 (z1 N) (z2 N) (N - p) ≤
      (((switchedClosedIndex337 N (switchedE118 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).filter
          (fun b => N - b.1 * b.2 = p)).card := by
  classical
  unfold rho2
  split_ifs with hw
  · obtain ⟨x, y, r, hx, hy, hr, hprod, hx1, hx2, hy2, hyr⟩ := hw
    obtain ⟨hroot, hcop, hdata⟩ := triple_switch_data337 N p x y r hp hx hy hr hyr hprod
    have hpair : (x, y) ∈ switchedPairs118 N :=
      (mem_switchedPairs118_iff N x y hN).mpr ⟨hx, hy, hx1, hx2, hy2, hroot, hcop⟩
    have hE : x * y ∈ switchedE118 N := mem_image.mpr ⟨(x, y), hpair, rfl⟩
    obtain ⟨hb, hback⟩ := hdata _ hE
    apply Finset.card_pos.mpr
    refine ⟨(x * y, r), mem_filter.mpr ⟨mem_filter.mpr ⟨hb, ?_⟩, hback⟩⟩
    simpa only [hback] using (mem_Pset hp).2.1
  · exact Nat.zero_le _

/-- S2 is bounded by the prime values of the closed indexed switched sequence.
Page 602 display 4.8. This avoids replacing a multiset of indices by an image set. -/
theorem sieve_two_closed337 (N : ℕ) (hN : 2 ≤ N) :
    S2 N 0.95 ≤ ((switchedClosedIndex337 N (switchedE118 N)).filter
      (fun b => (N - b.1 * b.2).Prime)).card := by
  classical
  unfold S2
  calc
    _ ≤ ∑ p ∈ Pset N 0.95,
        (((switchedClosedIndex337 N (switchedE118 N)).filter
          (fun b => (N - b.1 * b.2).Prime)).filter
            (fun b => N - b.1 * b.2 = p)).card :=
      sum_le_sum (fun p hp => rho2_closed_fiber337 N p hN hp)
    _ = _ := sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ _ := card_filter_le _ _

#print axioms triple_switch_data337
#print axioms rho2_closed_fiber337
#print axioms sieve_two_closed337

/-- Prime values of the strict switched index are sifted unless they lie below z.
Each e contributes at most ceil z small values. Page 602 display 4.9.
The indexed count is used throughout, so distinct representations are not discarded. -/
theorem switched_prime_sift337 (N : ℕ) (hN : 2 ≤ N) (E : Finset ℕ)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    ((switchedIndex306 N E).filter (fun b => (N - b.1 * b.2).Prime)).card ≤
      ((switchedIndex306 N E).filter (fun b => (N - b.1 * b.2).Coprime PP)).card +
        E.card * ⌈z⌉₊ := by
  classical
  dsimp only
  let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
  let G := (switchedIndex306 N E).filter (fun b => (N - b.1 * b.2).Prime)
  let B := G.filter (fun b => ¬ (N - b.1 * b.2).Coprime PP)
  have hB : B.card ≤ E.card * ⌈z⌉₊ := by
    calc
      B.card ≤ (E ×ˢ range ⌈z⌉₊).card := by
        apply Finset.card_le_card_of_injOn (fun b : ℕ × ℕ => (b.1, N - b.1 * b.2))
        · intro b hb
          obtain ⟨hbG, hbad⟩ := mem_filter.mp hb
          obtain ⟨hbT, hbPrime⟩ := mem_filter.mp hbG
          have hbE := (mem_product.mp (mem_filter.mp hbT).1).1
          have hlo : ((N - b.1 * b.2 : ℕ) : ℝ) < z := by
            by_contra hh
            have hgood := sieve_q_coprime306 P hP z (N - b.1 * b.2) PP
              hbPrime (le_of_not_gt hh) (dvd_refl PP)
            exact hbad hgood
          exact mem_product.mpr ⟨hbE, mem_range.mpr (Nat.lt_ceil.mpr hlo)⟩
        · intro b hb c hc he
          have hbT := (mem_filter.mp (mem_filter.mp hb).1).1
          have hcT := (mem_filter.mp (mem_filter.mp hc).1).1
          have hbHi := (mem_filter.mp hbT).2.2.2.2
          have hcHi := (mem_filter.mp hcT).2.2.2.2
          have he1 := congrArg (fun t : ℕ × ℕ => t.1) he
          have he2 := congrArg (fun t : ℕ × ℕ => t.2) he
          change b.1 = c.1 at he1
          change N - b.1 * b.2 = N - c.1 * c.2 at he2
          have hmul : b.1 * b.2 = c.1 * c.2 := by omega
          have hbpos : 0 < b.1 := by
            by_contra hh
            have hz : b.1 = 0 := by omega
            have hbLo := (mem_filter.mp hbT).2.2.2.1
            have hpow : (N : ℝ) ^ (0.95 : ℝ) < N := by
              simpa using rpow_lt_rpow_of_exponent_lt
                (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
                (by norm_num : (0.95 : ℝ) < 1)
            simp only [hz, zero_mul, Nat.cast_zero] at hbLo
            linarith
          apply Prod.ext he1
          apply Nat.eq_of_mul_eq_mul_left hbpos
          simpa only [he1] using hmul
      _ = _ := by simp
  have hsub : G ⊆ ((switchedIndex306 N E).filter
      (fun b => (N - b.1 * b.2).Coprime PP)) ∪ B := by
    intro b hb
    by_cases hc : (N - b.1 * b.2).Coprime PP
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hb).1, hc⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hb, hc⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hB _))

/-- The complete finite S2 bridge retains the small prime and closed endpoint losses.
Page 602 displays 4.8 to 4.9. This is unconditional and does not use Wu or Huxley. -/
theorem sieve_two_switching_finite337 (N : ℕ) (hN : 2 ≤ N)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    S2 N 0.95 ≤ ((switchedIndex306 N (switchedE118 N)).filter
      (fun b => (N - b.1 * b.2).Coprime PP)).card +
        (switchedE118 N).card * (⌈z⌉₊ + 1) := by
  dsimp only
  have h0 := sieve_two_closed337 N hN
  have h1 := switched_closed_selection337 N hN (switchedE118 N) Nat.Prime
  have h2 := switched_prime_sift337 N hN (switchedE118 N) P hP z
  dsimp only at h2
  have h := h0.trans (h1.trans (Nat.add_le_add_right h2 _))
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

#print axioms switched_prime_sift337
#print axioms sieve_two_switching_finite337

/-- The exact local divisor count in the strict switched index at one e.
Page 603 display 4.10. The prime coprimality and strict endpoints remain explicit. -/
def switchedLocalCount337 (N e d : ℕ) : ℕ :=
  ((range N).filter (fun r => r.Prime ∧ r.Coprime N ∧
    (N : ℝ) - (N : ℝ) ^ (0.95 : ℝ) < (e * r : ℕ) ∧ e * r < N ∧ d ∣ N - e * r)).card

/-- The Li mass attached to one prime pair product on pages 602 to 603. -/
def switchedLiTerm337 (N e : ℕ) : ℝ :=
  li118 ((N : ℝ) / e) - li118 (((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e)

/-- Grouping the actual divisor count by e loses no switched index.
Page 603 display 4.10, with all actual endpoint and coprimality restrictions retained. -/
theorem switched_local_count_sum337 (N d : ℕ) (E : Finset ℕ) :
    ((switchedIndex306 N E).filter (fun b => d ∣ N - b.1 * b.2)).card =
      ∑ e ∈ E, switchedLocalCount337 N e d := by
  classical
  simp only [switchedIndex306, switchedLocalCount337, Finset.card_filter,
    Finset.sum_filter, Finset.sum_product]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp_all
  grind

/-- The exact Li centered switched remainder splits into the coprime error
and the omitted noncoprime Li mass. Page 603 display 4.10.
The latter is kept inside an absolute value, so no unproved Li positivity is used. -/
theorem switched_remainder_split337 (N d : ℕ) (hc : N.Coprime d) (E : Finset ℕ) :
    |(((switchedIndex306 N E).filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
        (∑ e ∈ E, switchedLiTerm337 N e) / d.totient| ≤
      |∑ e ∈ E.filter (fun e => e.Coprime d),
        ((switchedLocalCount337 N e d : ℝ) - switchedLiTerm337 N e / d.totient)| +
      |∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / d.totient| := by
  classical
  have hzero (e : ℕ) (he : ¬ e.Coprime d) : switchedLocalCount337 N e d = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r _ hr
    obtain ⟨_, _, _, hhi, hdiv⟩ := hr
    apply he
    change Nat.gcd e d = 1
    apply Nat.eq_one_of_dvd_coprimes hc _ (Nat.gcd_dvd_right e d)
    have hgprod : Nat.gcd e d ∣ e * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_left e d) r
    have hgrem : Nat.gcd e d ∣ N - e * r := dvd_trans (Nat.gcd_dvd_right e d) hdiv
    have hh := dvd_add hgrem hgprod
    simpa only [Nat.sub_add_cancel hhi.le] using hh
  have hcount : (((switchedIndex306 N E).filter
      (fun b => d ∣ N - b.1 * b.2)).card : ℝ) =
      ∑ e ∈ E.filter (fun e => e.Coprime d), (switchedLocalCount337 N e d : ℝ) := by
    rw [switched_local_count_sum337]
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with he
    · rfl
    · rw [hzero e he, Nat.cast_zero]
  have hmass : (∑ e ∈ E, switchedLiTerm337 N e / (d.totient : ℝ)) =
      (∑ e ∈ E.filter (fun e => e.Coprime d), switchedLiTerm337 N e / d.totient) +
      (∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / d.totient) :=
    (Finset.sum_filter_add_sum_filter_not E (fun e => e.Coprime d)
      (fun e => switchedLiTerm337 N e / (d.totient : ℝ))).symm
  have hid : (((switchedIndex306 N E).filter
      (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
        (∑ e ∈ E, switchedLiTerm337 N e) / d.totient =
      (∑ e ∈ E.filter (fun e => e.Coprime d),
        ((switchedLocalCount337 N e d : ℝ) - switchedLiTerm337 N e / d.totient)) -
      (∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / d.totient) := by
    rw [hcount, Finset.sum_div, hmass, Finset.sum_sub_distrib]
    ring
  rw [hid, sub_eq_add_neg]
  simpa only [abs_neg] using abs_add_le
    (∑ e ∈ E.filter (fun e => e.Coprime d),
      ((switchedLocalCount337 N e d : ℝ) - switchedLiTerm337 N e / d.totient))
    (-(∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / d.totient))

#print axioms switched_local_count_sum337
#print axioms switched_remainder_split337

/-- The mixed product support has at most ceil N to two thirds elements.
Page 602, the size and range of E before display 4.9. -/
theorem switchedE_card337 (N : ℕ) (hN : 2 ≤ N) :
    (switchedE118 N).card ≤ ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ := by
  have hsub : switchedE118 N ⊆ range ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := mem_image.mp he
    obtain ⟨_, _, hp1, hp2, hq1, hq2, _⟩ :=
      (mem_switchedPairs118_iff N b.1 b.2 hN).mp hb
    have hr := (switched_product_range118 (N : ℝ) b.1 b.2
      (by exact_mod_cast (show 1 < N by omega)) hp1 hp2 hq1 hq2).2
    apply mem_range.mpr
    apply Nat.lt_ceil.mpr
    exact_mod_cast hr
  simpa only [card_range] using card_le_card hsub

/-- The explicit finite switching loss is negligible at the allowed sieve cutoff.
Pages 602 to 604 displays 4.9 to 4.15. This allows an indexed small value loss
larger than the image set loss in the paper and still retains the needed saving. -/
theorem switched_small_value_loss337 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
      E.card ≤ ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ → ∀ z : ℝ,
      z ≤ (N : ℝ) ^ (0.225 : ℝ) →
        (E.card * (⌈z⌉₊ + 1) : ℝ) ≤
          η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  obtain ⟨n0, hn0⟩ := remainder_log_cube_small118 (η / 6) (by positivity)
  refine ⟨max 2 n0, fun N hN E hE z hz => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left ..).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp1 : 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := one_le_rpow hN1 (by norm_num)
  have hq1 : 1 ≤ (N : ℝ) ^ (0.225 : ℝ) := one_le_rpow hN1 (by norm_num)
  have hEc : (E.card : ℝ) ≤ 2 * (N : ℝ) ^ (2 / 3 : ℝ) := by
    have hceil := Nat.ceil_lt_add_one (rpow_nonneg hNp.le (2 / 3 : ℝ))
    have hh : (E.card : ℝ) ≤ ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ := by exact_mod_cast hE
    linarith
  have hzc : (⌈z⌉₊ : ℝ) + 1 ≤ 3 * (N : ℝ) ^ (0.225 : ℝ) := by
    have hmono : (⌈z⌉₊ : ℝ) ≤ ⌈(N : ℝ) ^ (0.225 : ℝ)⌉₊ := by
      exact_mod_cast Nat.ceil_mono hz
    have hceil := Nat.ceil_lt_add_one (rpow_nonneg hNp.le (0.225 : ℝ))
    linarith
  have hprod : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (0.225 : ℝ) ≤
      (N : ℝ) ^ (10 / 11 : ℝ) := by
    rw [← rpow_add hNp]
    exact rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg hN1
  have hcube : 1 ≤ (1 + log (N : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
  have hbase : (N : ℝ) ^ (10 / 11 : ℝ) ≤
      (N : ℝ) ^ (10 / 11 : ℝ) * (1 + log N) ^ 3 :=
    le_mul_of_one_le_right (rpow_nonneg hNp.le _) hcube
  have hsmall := hn0 N ((le_max_right ..).trans hN)
  calc
    _ ≤ (2 * (N : ℝ) ^ (2 / 3 : ℝ)) * (3 * (N : ℝ) ^ (0.225 : ℝ)) :=
      mul_le_mul hEc hzc (by positivity) (by positivity)
    _ = 6 * ((N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (0.225 : ℝ)) := by ring
    _ ≤ 6 * (N : ℝ) ^ (10 / 11 : ℝ) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 6 * ((η / 6) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbase.trans hsmall) (by norm_num)
    _ = _ := by ring

#print axioms switchedE_card337
#print axioms switched_small_value_loss337

/-- Reciprocal multiples have the harmonic saving one over m.
Derived finite sum input for page 603 display 4.11. -/
theorem reciprocal_multiples337 (m Q : ℕ) (hm : 1 ≤ m) :
    (∑ e ∈ (Icc 1 Q).filter (fun e => m ∣ e), (1 : ℝ) / e) ≤ (1 + log Q) / m := by
  classical
  let T := (Icc 1 Q).filter (fun e => m ∣ e)
  have hinj : Set.InjOn (fun e => e / m) (T : Set ℕ) := by
    intro e he f hf hef
    change e / m = f / m at hef
    have heq := Nat.div_mul_cancel (mem_filter.mp he).2
    have hfq := Nat.div_mul_cancel (mem_filter.mp hf).2
    calc
      e = e / m * m := heq.symm
      _ = f / m * m := by rw [hef]
      _ = f := hfq
  have hsub : T.image (fun e => e / m) ⊆ Icc 1 Q := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := mem_image.mp hk
    obtain ⟨heQ, hme⟩ := mem_filter.mp he
    have he1 := (mem_Icc.mp heQ).1
    have hem : m ≤ e := Nat.le_of_dvd he1 hme
    exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr (by simpa using hem),
      (Nat.div_le_self e m).trans (mem_Icc.mp heQ).2⟩
  have hsum : (∑ e ∈ T, (1 : ℝ) / e) =
      (1 / (m : ℝ)) * ∑ k ∈ T.image (fun e => e / m), (1 : ℝ) / k := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply sum_congr rfl
    intro e he
    rw [one_div_mul_one_div, ← Nat.cast_mul, mul_comm m, Nat.div_mul_cancel (mem_filter.mp he).2]
  rw [hsum]
  calc
    _ ≤ (1 / (m : ℝ)) * ∑ k ∈ Icc 1 Q, (1 : ℝ) / k :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ (1 / (m : ℝ)) * (1 + log Q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := harmonic_le_one_add_log Q
      rw [harmonic_eq_sum_Icc] at hh
      push_cast at hh
      simpa only [one_div] using hh
    _ = _ := by ring

/-- A noncoprime reciprocal sum is controlled by the large divisors of d.
Page 603 display 4.11. The lower bound on the actual gcd is explicit. -/
theorem noncoprime_reciprocal337 (E : Finset ℕ) (Q M d : ℕ)
    (hd : 1 ≤ d) (hE : E ⊆ Icc 1 Q)
    (hM : ∀ e ∈ E, ¬ e.Coprime d → M ≤ Nat.gcd e d) :
    (∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (1 : ℝ) / e) ≤
      (1 + log Q) * ∑ m ∈ d.divisors.filter (fun m => M ≤ m), (1 : ℝ) / m := by
  classical
  let S := d.divisors.filter (fun m => M ≤ m)
  have hpoint (e : ℕ) (he : e ∈ E.filter (fun e => ¬ e.Coprime d)) :
      (1 : ℝ) / e ≤ ∑ m ∈ S, if m ∣ e then (1 : ℝ) / e else 0 := by
    obtain ⟨heE, heBad⟩ := mem_filter.mp he
    have hmem : Nat.gcd e d ∈ S := mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right e d, by omega⟩, hM e heE heBad⟩
    have hh := Finset.single_le_sum (fun m (_ : m ∈ S) =>
      show (0 : ℝ) ≤ if m ∣ e then (1 : ℝ) / e else 0 from by split_ifs <;> positivity) hmem
    simpa only [ite_eq_left (Nat.gcd_dvd_left e d)] using hh
  calc
    _ ≤ ∑ e ∈ E.filter (fun e => ¬ e.Coprime d),
        ∑ m ∈ S, if m ∣ e then (1 : ℝ) / e else 0 := sum_le_sum hpoint
    _ ≤ ∑ e ∈ Icc 1 Q, ∑ m ∈ S, if m ∣ e then (1 : ℝ) / e else 0 :=
      sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hE)
        (fun e _ _ => by apply sum_nonneg; intro m _; split_ifs <;> positivity)
    _ = ∑ m ∈ S, ∑ e ∈ (Icc 1 Q).filter (fun e => m ∣ e), (1 : ℝ) / e := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ m ∈ S, (1 + log Q) / m := by
      apply sum_le_sum
      intro m hm
      have hm0 := Nat.pos_of_mem_divisors (mem_filter.mp hm).1
      exact reciprocal_multiples337 m Q hm0
    _ = _ := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro m _
      ring

/-- The averaged noncoprime harmonic mass has the needed inverse cutoff saving.
Page 603 display 4.11, before inserting the Li upper estimate. -/
theorem noncoprime_reciprocal_tail337 :
    ∃ K : ℝ, 0 < K ∧ ∀ (M D Q : ℕ), 1 ≤ M → ∀ E : Finset ℕ,
      E ⊆ Icc 1 Q →
      (∀ d ∈ Icc 1 D, ∀ e ∈ E, ¬ e.Coprime d → M ≤ Nat.gcd e d) →
      (∑ d ∈ Icc 1 D, (1 / (d.totient : ℝ)) *
        ∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (1 : ℝ) / e) ≤
          K * (1 + log Q) * (1 + log D) ^ 2 / M := by
  classical
  obtain ⟨K, hK, htail⟩ := reciprocal_totient_divisor_tail118
  refine ⟨K, hK, fun M D Q hM E hE hrough => ?_⟩
  calc
    _ ≤ ∑ d ∈ Icc 1 D, (1 / (d.totient : ℝ)) *
        ((1 + log Q) * ∑ m ∈ d.divisors.filter (fun m => M ≤ m), (1 : ℝ) / m) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (noncoprime_reciprocal337 E Q M d (mem_Icc.mp hd).1 hE (hrough d hd)) (by positivity)
    _ = (1 + log Q) * ∑ d ∈ Icc 1 D, (1 / (d.totient : ℝ)) *
        ∑ m ∈ d.divisors.filter (fun m => M ≤ m), (1 : ℝ) / m := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (1 + log Q) * (K * (1 + log D) ^ 2 / M) :=
      mul_le_mul_of_nonneg_left (htail M hM D) (by positivity)
    _ = _ := by ring

#print axioms reciprocal_multiples337
#print axioms noncoprime_reciprocal337
#print axioms noncoprime_reciprocal_tail337

/-- Rough support forces each nontrivial gcd to exceed the same real cutoff.
Page 603 display 4.11. This is a finite prime divisor argument. -/
theorem rough_gcd_lower337 (e d : ℕ) (he : e ≠ 0) (z : ℝ)
    (hrough : ∀ p ∈ e.primeFactors, z ≤ (p : ℝ)) (hc : ¬ e.Coprime d) :
    z ≤ (Nat.gcd e d : ℝ) := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  have hpe : p ∣ e := dvd_trans hpd (Nat.gcd_dvd_left e d)
  have hmem : p ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpe, he⟩
  have hple : p ≤ Nat.gcd e d :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left d (Nat.pos_of_ne_zero he)) hpd
  exact (hrough p hmem).trans (by exact_mod_cast hple)

/-- Every prime factor of a mixed pair product is at least z1.
Pages 602 to 603, the actual support behind display 4.11. -/
theorem switchedE_rough337 (N e : ℕ) (hN : 2 ≤ N) (he : e ∈ switchedE118 N) :
    0 < e ∧ ∀ p ∈ e.primeFactors, z1 N ≤ (p : ℝ) := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, hx1, _, hy2, _, _⟩ :=
    (mem_switchedPairs118_iff N b.1 b.2 hN).mp hb
  have hz : z1 N ≤ z2 N := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  refine ⟨Nat.mul_pos hx.pos hy.pos, fun p hp => ?_⟩
  have hprime := Nat.prime_of_mem_primeFactors hp
  rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hpx | hpy
  · have heq := (Nat.prime_dvd_prime_iff_eq hprime hx).mp hpx
    simpa only [heq] using hx1
  · have heq := (Nat.prime_dvd_prime_iff_eq hprime hy).mp hpy
    simpa only [heq] using hz.trans hy2

/-- Bounded nonnegative local masses inherit the noncoprime reciprocal tail saving.
Page 603 display 4.11. This exposes the local Li bound as an elementary hypothesis. -/
theorem noncoprime_mass_tail337 :
    ∃ K : ℝ, 0 < K ∧ ∀ (M D Q : ℕ), 1 ≤ M → ∀ E : Finset ℕ,
      E ⊆ Icc 1 Q →
      (∀ d ∈ Icc 1 D, ∀ e ∈ E, ¬ e.Coprime d → M ≤ Nat.gcd e d) →
      ∀ (A : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ e ∈ E, 0 ≤ A e ∧ A e ≤ X / e) →
      (∑ d ∈ Icc 1 D,
        |∑ e ∈ E.filter (fun e => ¬ e.Coprime d), A e / (d.totient : ℝ)|) ≤
          K * X * (1 + log Q) * (1 + log D) ^ 2 / M := by
  classical
  obtain ⟨K, hK, htail⟩ := noncoprime_reciprocal_tail337
  refine ⟨K, hK, fun M D Q hM E hE hrough A X hX hA => ?_⟩
  have hlocal (d : ℕ) :
      |∑ e ∈ E.filter (fun e => ¬ e.Coprime d), A e / (d.totient : ℝ)| ≤
        X * ((1 / (d.totient : ℝ)) *
          ∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (1 : ℝ) / e) := by
    rw [abs_of_nonneg (by
      apply sum_nonneg
      intro e he
      exact div_nonneg (hA e (mem_filter.mp he).1).1 (Nat.cast_nonneg _))]
    calc
      _ ≤ ∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (X / e) / (d.totient : ℝ) := by
        apply sum_le_sum
        intro e he
        exact div_le_div_of_nonneg_right (hA e (mem_filter.mp he).1).2 (Nat.cast_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply sum_congr rfl
        intro e _
        ring
  calc
    _ ≤ ∑ d ∈ Icc 1 D, X * ((1 / (d.totient : ℝ)) *
        ∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (1 : ℝ) / e) :=
      sum_le_sum (fun d _ => hlocal d)
    _ = X * ∑ d ∈ Icc 1 D, (1 / (d.totient : ℝ)) *
        ∑ e ∈ E.filter (fun e => ¬ e.Coprime d), (1 : ℝ) / e := by rw [Finset.mul_sum]
    _ ≤ X * (K * (1 + log Q) * (1 + log D) ^ 2 / M) :=
      mul_le_mul_of_nonneg_left (htail M D Q hM E hE hrough) hX
    _ = _ := by ring

#print axioms rough_gcd_lower337
#print axioms switchedE_rough337
#print axioms noncoprime_mass_tail337

/-- Above exp one the Li increment lies between zero and the interval length.
Derived local Li estimate for page 603 display 4.11. -/
theorem li118_interval_bounds337 (a b : ℝ) (ha : exp 1 ≤ a) (hab : a ≤ b) :
    0 ≤ li118 b - li118 a ∧ li118 b - li118 a ≤ b - a := by
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1 : ℝ)]
  let f : ℝ → ℝ := fun t => 1 / log t
  have hc (u v : ℝ) (hu : 2 ≤ u) (huv : u ≤ v) :
      IntervalIntegrable f MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact continuousOn_const.div
      (continuousOn_id.log (fun t ht => by change t ≠ 0; linarith [ht.1]))
      (fun t ht => ne_of_gt (log_pos (by linarith [ht.1])))
  have hi := intervalIntegral.integral_add_adjacent_intervals (hc 2 a le_rfl ha2) (hc a b ha2 hab)
  have hid : li118 b - li118 a = ∫ t in a..b, f t := by
    change (∫ t in (2 : ℝ)..b, f t) - (∫ t in (2 : ℝ)..a, f t) = _
    linarith
  rw [hid]
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    dsimp [f]
    exact div_nonneg zero_le_one (log_nonneg (by linarith [ht.1]))
  · have hm : (∫ t in a..b, f t) ≤ ∫ _t in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hab (hc a b ha2 hab) (continuous_const.intervalIntegrable _ _)
      intro t ht
      have htE : exp 1 ≤ t := ha.trans ht.1
      have htL : 1 ≤ log t := by simpa only [log_exp] using log_le_log (exp_pos 1) htE
      dsimp [f]
      exact (div_le_one (by linarith : 0 < log t)).mpr htL
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hm

/-- The actual local Li mass is nonnegative and at most N to theta over e.
Page 603 display 4.11. The endpoint condition prevents crossing the logarithmic singularity. -/
theorem switchedLiTerm_bounds337 (N e : ℕ) (he : 0 < e)
    (hlo : exp 1 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e) :
    0 ≤ switchedLiTerm337 N e ∧
      switchedLiTerm337 N e ≤ (N : ℝ) ^ (0.95 : ℝ) / e := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hab : ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e ≤ (N : ℝ) / e :=
    div_le_div_of_nonneg_right (by linarith [rpow_nonneg (Nat.cast_nonneg N) (0.95 : ℝ)]) heR.le
  have hh := li118_interval_bounds337 _ _ hlo hab
  change 0 ≤ switchedLiTerm337 N e ∧ switchedLiTerm337 N e ≤ _ at hh
  convert hh using 1 <;> ring

/-- The exact omitted Li masses have the inverse cutoff saving in display 4.11.
No prime mean value estimate is used. The endpoint and large gcd hypotheses are explicit. -/
theorem switched_li_mass_tail337 :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M D Q : ℕ), 1 ≤ M → ∀ E : Finset ℕ,
      E ⊆ Icc 1 Q →
      (∀ d ∈ Icc 1 D, ∀ e ∈ E, ¬ e.Coprime d → M ≤ Nat.gcd e d) →
      (∀ e ∈ E, exp 1 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e) →
      (∑ d ∈ Icc 1 D,
        |∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / (d.totient : ℝ)|) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) * (1 + log Q) * (1 + log D) ^ 2 / M := by
  obtain ⟨K, hK, htail⟩ := noncoprime_mass_tail337
  refine ⟨K, hK, fun N M D Q hM E hE hrough hlo => ?_⟩
  apply htail M D Q hM E hE hrough (switchedLiTerm337 N) ((N : ℝ) ^ (0.95 : ℝ))
    (rpow_nonneg (Nat.cast_nonneg N) _)
  intro e he
  exact switchedLiTerm_bounds337 N e (mem_Icc.mp (hE he)).1 (hlo e he)

#print axioms li118_interval_bounds337
#print axioms switchedLiTerm_bounds337
#print axioms switched_li_mass_tail337

/-- The lower Li endpoints are uniformly above exp one throughout the product region.
Pages 602 to 603, the range e at most N to two thirds used in display 4.11. -/
theorem switched_endpoint_large337 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ e : ℕ, 0 < e →
      (e : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      exp 1 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e := by
  have hsmall := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.05)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hthird := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall.eventually_ge_atTop 2,
    hthird.eventually_ge_atTop (2 * exp 1)] with N hN hs ht
  intro e he heU
  change 2 ≤ (N : ℝ) ^ (0.05 : ℝ) at hs
  change 2 * exp 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) at ht
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hpow1 : (N : ℝ) ^ (0.95 : ℝ) * (N : ℝ) ^ (0.05 : ℝ) = N := by
    rw [← rpow_add hNp]
    norm_num
  have hpow2 : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = N := by
    rw [← rpow_add hNp]
    norm_num
  have hhalf1 : 2 * (N : ℝ) ^ (0.95 : ℝ) ≤ N := by
    nlinarith [mul_nonneg (rpow_nonneg hNp.le (0.95 : ℝ)) (sub_nonneg.mpr hs)]
  have hhalf2 : 2 * exp 1 * (N : ℝ) ^ (2 / 3 : ℝ) ≤ N := by
    nlinarith [mul_nonneg (rpow_nonneg hNp.le (2 / 3 : ℝ)) (sub_nonneg.mpr ht)]
  apply (le_div_iff₀ heR).mpr
  have hh := mul_le_mul_of_nonneg_left heU (exp_pos 1).le
  linarith

/-- The actual omitted Li mass is negligible for every rough product support in the paper's range.
Page 603 display 4.11. This is uniform in E and in every modulus cutoff D at most N. -/
theorem switched_li_remainder_small337 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
      (∀ e ∈ E, 0 < e ∧ (e : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧
        ∀ p ∈ e.primeFactors, z1 N ≤ (p : ℝ)) →
      ∀ D : ℕ, D ≤ N →
      (∑ d ∈ Icc 1 D,
        |∑ e ∈ E.filter (fun e => ¬ e.Coprime d), switchedLiTerm337 N e / (d.totient : ℝ)|) ≤
          η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  obtain ⟨K, hK, htail⟩ := switched_li_mass_tail337
  obtain ⟨n0, hn0⟩ := remainder_log_cube_small118 (η / (2 * K)) (by positivity)
  obtain ⟨n1, hn1⟩ := switched_endpoint_large337
  have hroot := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨n2, hn2⟩ := eventually_atTop.mp (hroot.eventually_ge_atTop 2)
  refine ⟨max 2 (max n0 (max n1 n2)), fun N hN E hE D hD => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0 : n0 ≤ N := (le_max_left ..).trans ((le_max_right ..).trans hN)
  have h1 : n1 ≤ N := (le_max_left ..).trans
    ((le_max_right ..).trans ((le_max_right ..).trans hN))
  have h2 : n2 ≤ N := (le_max_right ..).trans
    ((le_max_right ..).trans ((le_max_right ..).trans hN))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hz2 : 2 ≤ z1 N := hn2 N h2
  let M : ℕ := ⌊z1 N⌋₊
  have hM : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ z1 N by linarith)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMhalf : z1 N ≤ 2 * (M : ℝ) := by
    have hh := Nat.lt_floor_add_one (z1 N)
    change z1 N < (M : ℝ) + 1 at hh
    linarith
  have hsub : E ⊆ Icc 1 N := by
    intro e he
    have hpow : (N : ℝ) ^ (2 / 3 : ℝ) ≤ N := by
      simpa using rpow_le_rpow_of_exponent_le hN1 (by norm_num : (2 / 3 : ℝ) ≤ 1)
    exact mem_Icc.mpr ⟨(hE e he).1, by exact_mod_cast (hE e he).2.1.trans hpow⟩
  have hgcd : ∀ d ∈ Icc 1 D, ∀ e ∈ E, ¬ e.Coprime d → M ≤ Nat.gcd e d := by
    intro d _ e he hbad
    have hh := rough_gcd_lower337 e d (Nat.ne_of_gt (hE e he).1) (z1 N) (hE e he).2.2 hbad
    have hmz : (M : ℝ) ≤ z1 N := Nat.floor_le (by linarith)
    exact_mod_cast hmz.trans hh
  have hlo : ∀ e ∈ E, exp 1 ≤ ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e :=
    fun e he => hn1 N h1 e (hE e he).1 (hE e he).2.1
  have htailN := htail N M D N hM E hsub hgcd hlo
  have hlogD : log (D : ℝ) ≤ log (N : ℝ) := by
    by_cases hD0 : D = 0
    · simp only [hD0, Nat.cast_zero, log_zero]
      exact log_nonneg hN1
    · exact log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD0) (by exact_mod_cast hD)
  have hpowN : (N : ℝ) ^ (0.95 : ℝ) ≤ N := by
    simpa using rpow_le_rpow_of_exponent_le hN1 (by norm_num : (0.95 : ℝ) ≤ 1)
  have hfac : (N : ℝ) ≤ 2 * (N : ℝ) ^ (10 / 11 : ℝ) * M := by
    have hid : (N : ℝ) ^ (10 / 11 : ℝ) * z1 N = N := by
      unfold z1
      rw [← rpow_add hNp]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hMhalf (rpow_nonneg hNp.le (10 / 11 : ℝ))
    nlinarith only [hh, hid]
  apply htailN.trans
  calc
    _ ≤ K * N * (1 + log N) ^ 3 / M := by
      have hlogD0 : 0 ≤ 1 + log (D : ℝ) := by positivity
      have hlogN0 : 0 ≤ 1 + log (N : ℝ) := by positivity
      have hs := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogD0 (by linarith : 1 + log (D : ℝ) ≤ 1 + log (N : ℝ)) 2)
        (show 0 ≤ K * (N : ℝ) ^ (0.95 : ℝ) * (1 + log N) by positivity)
      have hp := mul_le_mul_of_nonneg_left hpowN
        (show 0 ≤ K * (1 + log N) ^ 3 by positivity)
      apply div_le_div_of_nonneg_right _ hMp.le
      nlinarith only [hs, hp]
    _ ≤ 2 * K * ((N : ℝ) ^ (10 / 11 : ℝ) * (1 + log N) ^ 3) := by
      apply (div_le_iff₀ hMp).mpr
      have hh := mul_le_mul_of_nonneg_left hfac (show 0 ≤ K * (1 + log N) ^ 3 by positivity)
      nlinarith only [hh]
    _ ≤ 2 * K * ((η / (2 * K)) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) :=
      mul_le_mul_of_nonneg_left (hn0 N h0) (by positivity)
    _ = _ := by field_simp

#print axioms switched_endpoint_large337
#print axioms switched_li_remainder_small337

/-- The actual mixed product region has a negligible omitted Li remainder.
Page 603 display 4.11. The threshold is uniform over every D at most N. -/
theorem sieve_two_R2_small337 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ D : ℕ, D ≤ N →
      (∑ d ∈ Icc 1 D,
        |∑ e ∈ (switchedE118 N).filter (fun e => ¬ e.Coprime d),
          switchedLiTerm337 N e / (d.totient : ℝ)|) ≤
          η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  obtain ⟨n0, hn0⟩ := switched_li_remainder_small337 η hη
  refine ⟨max 2 n0, fun N hN D hD => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left ..).trans hN
  apply hn0 N ((le_max_right ..).trans hN) (switchedE118 N) _ D hD
  intro e he
  obtain ⟨hepos, herough⟩ := switchedE_rough337 N e hN2 he
  obtain ⟨b, hb, rfl⟩ := mem_image.mp he
  obtain ⟨_, _, hp1, hp2, hq1, hq2, _⟩ :=
    (mem_switchedPairs118_iff N b.1 b.2 hN2).mp hb
  have hh := (switched_product_range118 (N : ℝ) b.1 b.2
    (by exact_mod_cast (show 1 < N by omega)) hp1 hp2 hq1 hq2).2.le
  exact ⟨hepos, by exact_mod_cast hh, herough⟩

#print axioms sieve_two_R2_small337

/-- The positive product support satisfies the paper's strict real cardinality bound.
Page 602, the strict size bound for E before display 4.9. -/
theorem switchedE_card_lt337 (N : ℕ) (hN : 2 ≤ N) :
    (switchedE118 N).card < (N : ℝ) ^ (2 / 3 : ℝ) := by
  let R : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  have hRp : 0 < R := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hceil : 1 ≤ ⌈R⌉₊ := Nat.one_le_ceil_iff.mpr hRp
  have hsub : switchedE118 N ⊆ Icc 1 (⌈R⌉₊ - 1) := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := mem_image.mp he
    obtain ⟨hx, hy, hp1, hp2, hq1, hq2, _⟩ :=
      (mem_switchedPairs118_iff N b.1 b.2 hN).mp hb
    have hp : 0 < b.1 * b.2 := Nat.mul_pos hx.pos hy.pos
    have hr := (switched_product_range118 (N : ℝ) b.1 b.2
      (by exact_mod_cast (show 1 < N by omega)) hp1 hp2 hq1 hq2).2
    have hc : b.1 * b.2 < ⌈R⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hr)
    exact mem_Icc.mpr ⟨hp, by omega⟩
  have hcard : (switchedE118 N).card ≤ ⌈R⌉₊ - 1 := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hc : ((switchedE118 N).card : ℝ) ≤ (⌈R⌉₊ - 1 : ℕ) := by exact_mod_cast hcard
  have hlt : ((⌈R⌉₊ - 1 : ℕ) : ℝ) < R := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hRp.le]
  exact hc.trans_lt hlt

#print axioms switchedE_card_lt337

/-- The normalized mixed prime pair main term in page 604 display 4.13.
Unique separated prime factorization is already checked in Switching118. -/
def sieveTwoPairSum337 (N : ℕ) : ℝ :=
  8 / (2 * (0.95 : ℝ) - 1) * log N *
    ∑ b ∈ switchedPairs118 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ)))

/-- The exact integral coefficient in page 604 display 4.14. -/
def sieveTwoCoefficient337 : ℝ :=
  8 / (2 * (0.95 : ℝ) - 1) *
    ∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t

/-- LEAF. Pages 602 to 604 displays 4.8 to 4.13, before prime pair partial summation.
This is the count to weighted pair sum step. The errors and closed endpoint loss
must be absorbed. External inputs remain the cited linear sieve, Wu 1993
https://doi.org/10.1093/qmath/44.1.109 and Huxley's short interval theorem.
This is open. No uniform Wu family estimate is inferred from WuMeanValue118. -/
theorem leaf337_two_switching :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedE118 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveTwoPairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  sorry

/-- LEAF. Page 604 display 4.13, prime pair partial summation after the Li replacement.
This contains no switched count or short interval prime error. The pair region
still excludes factors of N, so the assertion is an upper limit with every reserve. -/
theorem leaf337_two_pair_sum :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      sieveTwoPairSum337 N ≤ sieveTwoCoefficient337 + δ := by
  sorry

/-- The exact sealed second upper leaf follows from the two smaller analytic steps.
CONDITIONAL ON leaf337_two_switching and leaf337_two_pair_sum. -/
theorem sieve_two_supply337 :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S2 N 0.95 : ℝ) ≤
        6.8086 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, h0⟩ := leaf337_two_switching 0.00002 (by norm_num)
  obtain ⟨N1, h1⟩ := leaf337_two_pair_sum 0.00002 (by norm_num)
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0N : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1N : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  apply (Nat.cast_le.mpr (sieve_two_closed337 N h2)).trans
  apply (h0 N he h0N).trans
  apply mul_le_mul_of_nonneg_right _ (leaf118_scale_pos N h2).le
  have hc : sieveTwoCoefficient337 ≤ 6.8085 := eq414_margin118
  have := h1 N h1N
  linarith

#print axioms switched_closed_selection337
#print axioms leaf337_two_switching
#print axioms leaf337_two_pair_sum
#print axioms sieve_two_supply337

end LeanLab.Cai2002
