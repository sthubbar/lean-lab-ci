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

private theorem bsc_blk_sum (L : ℝ) (hL : 0 < L) (t : ℕ → ℝ) (ht : Monotone t) (h2 : log 2 ≤ t 0 * L)
    (f : ℝ → ℝ) (M : ℕ → ℝ) (K : ℕ)
    (hM : ∀ j < K, ∀ v, t j < v → v ≤ t (j+1) → f v ≤ M j) (hM0 : ∀ j < K, 0 ≤ M j) :
    ∑ q ∈ Ioc ⌊exp (t 0 * L)⌋₊ ⌊exp (t K * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      ∑ j ∈ range K, M j * (log (t (j+1) / t j) + 4 / (t j * L)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have hmon : ∀ a b : ℕ, a ≤ b → ⌊exp (t a * L)⌋₊ ≤ ⌊exp (t b * L)⌋₊ := fun a b hab =>
      Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (ht hab) hL.le))
    rw [← sum_Ioc_consecutive _ (hmon 0 K (Nat.zero_le _)) (hmon K (K+1) (Nat.le_succ _))]
    have ih' := ih (fun j hj v h1 h3 => hM j (by omega) v h1 h3) (fun j hj => hM0 j (by omega))
    have hy2 : (2 : ℝ) ≤ exp (t K * L) := by
      have : log 2 ≤ t K * L := h2.trans (mul_le_mul_of_nonneg_right (ht (Nat.zero_le _)) hL.le)
      calc (2:ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
        _ ≤ _ := exp_le_exp.mpr this
    have hyx : exp (t K * L) ≤ exp (t (K+1) * L) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right (ht (Nat.le_succ _)) hL.le)
    have hmert := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy2 hyx
    have hupper := (abs_le.mp hmert).2
    have htK : 0 < t K * L := lt_of_lt_of_le (log_pos (by norm_num)) (h2.trans
      (mul_le_mul_of_nonneg_right (ht (Nat.zero_le _)) hL.le))
    have htK0 : 0 < t K := pos_of_mul_pos_left htK hL.le
    have htK1 : 0 < t (K+1) := lt_of_lt_of_le htK0 (ht (Nat.le_succ _))
    have hll : log (log (exp (t (K+1) * L))) - log (log (exp (t K * L))) = log (t (K+1) / t K) := by
      rw [log_exp, log_exp, log_mul htK1.ne' hL.ne', log_mul htK0.ne' hL.ne', log_div htK1.ne' htK0.ne']
      ring
    rw [hll, log_exp] at hupper
    have hblock : ∑ q ∈ Ioc ⌊exp (t K * L)⌋₊ ⌊exp (t (K+1) * L)⌋₊,
        (if q.Prime then f (log q / L) / q else 0) ≤
        M K * ∑ p ∈ (Ioc ⌊exp (t K * L)⌋₊ ⌊exp (t (K+1) * L)⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
      rw [sum_filter, mul_sum]
      apply sum_le_sum
      intro q hq
      split_ifs with hp
      · have hq1 := (mem_Ioc.mp hq).1
        have hq2 := (mem_Ioc.mp hq).2
        have hy : exp (t K * L) < q := (Nat.floor_lt (exp_pos _).le).mp hq1
        have hx : (q : ℝ) ≤ exp (t (K+1) * L) := (Nat.le_floor_iff (exp_pos _).le).mp hq2
        have hqpos : (0 : ℝ) < q := lt_trans (exp_pos _) hy
        have hv1 : t K < log q / L := by
          rw [lt_div_iff₀ hL]
          have := log_lt_log (exp_pos _) hy
          rwa [log_exp] at this
        have hv2 : log q / L ≤ t (K+1) := by
          rw [div_le_iff₀ hL]
          have := log_le_log hqpos hx
          rwa [log_exp] at this
        have hfv := hM K (Nat.lt_succ_self K) _ hv1 hv2
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right hfv hqpos.le
      · simp
    have hM0K := hM0 K (Nat.lt_succ_self K)
    have := mul_le_mul_of_nonneg_left hupper hM0K
    linarith

private theorem bsc_riem (t : ℕ → ℝ) (K : ℕ) (Δ : ℝ) (f : ℝ → ℝ) (m : ℕ → ℝ)
    (ht : ∀ j < K, t j ≤ t (j+1)) (ht0 : ∀ j < K, 0 < t j)
    (hΔ : ∀ j < K, log (t (j+1) / t j) = Δ)
    (hm : ∀ j < K, ∀ u ∈ Set.Icc (t j) (t (j+1)), m j ≤ f u)
    (hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1))) :
    ∑ j ∈ range K, m j * Δ ≤ ∫ u in (t 0)..(t K), f u / u := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply sum_le_sum
  intro j hj
  have hj' := mem_range.mp hj
  have h0 := ht0 j hj'
  have h1 : 0 < t (j+1) := lt_of_lt_of_le h0 (ht j hj')
  have heq : m j * Δ = ∫ u in (t j)..(t (j+1)), m j / u := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 h1, hΔ j hj']
  rw [heq]
  apply intervalIntegral.integral_mono_on (ht j hj')
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le (ht j hj')] at hu
    exact (lt_of_lt_of_le h0 hu.1).ne'
  · exact hint j hj'
  · intro u hu
    exact div_le_div_of_nonneg_right (hm j hj' u hu) (lt_of_lt_of_le h0 hu.1).le

private theorem bsc_geo_part (α β : ℝ) (K : ℕ) (hK : 0 < K) (hα : 0 < α) (hαβ : α ≤ β) :
    let Δ := log (β / α) / K
    let t : ℕ → ℝ := fun j => α * exp (j * Δ)
    0 ≤ Δ ∧ Monotone t ∧ t 0 = α ∧ t K = β ∧ (∀ j, log (t (j+1) / t j) = Δ) := by
  intro Δ t
  have hΔ0 : 0 ≤ Δ := div_nonneg (log_nonneg ((one_le_div hα).mpr hαβ)) (Nat.cast_nonneg _)
  refine ⟨hΔ0, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply mul_le_mul_of_nonneg_left _ hα.le
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hΔ0
  · simp [t]
  · simp only [t, Δ]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hK.ne' : (K:ℝ) ≠ 0), exp_log (div_pos (by linarith) hα)]
    field_simp
  · intro j
    simp only [t]
    rw [mul_div_mul_left _ _ hα.ne', ← exp_sub, log_exp]
    push_cast; ring

private theorem bsc_fint (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (f : ℝ → ℝ)
    (h1 : IntervalIntegrable f MeasureTheory.volume α β) :
    IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
  simp only [div_eq_mul_inv]
  apply h1.mul_continuousOn
  apply ContinuousOn.inv₀ continuousOn_id
  intro u hu; rw [Set.uIcc_of_le hαβ] at hu; exact (lt_of_lt_of_le hα hu.1).ne'

private theorem bsc_mono_sum (L α β : ℝ) (K : ℕ) (hK : 0 < K) (hL : 0 < L) (hα : 0 < α) (hαβ : α ≤ β)
    (h2 : log 2 ≤ α * L) (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc α β))
    (hf0 : ∀ v ∈ Set.Icc α β, 0 ≤ f v) :
    ∑ q ∈ Ioc ⌊exp (α * L)⌋₊ ⌊exp (β * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      (∫ u in α..β, f u / u) + (f β - f α) * (log (β / α) / K) + K * f β * (4 / (α * L)) := by
  obtain ⟨hΔ0, ht, ht0, htK, hratio⟩ := bsc_geo_part α β K hK hα hαβ
  set Δ := log (β / α) / K with hΔdef
  set t : ℕ → ℝ := fun j => α * exp (j * Δ) with htdef
  have htα : ∀ j, α ≤ t j := fun j => ht0 ▸ ht (Nat.zero_le j)
  have htβ : ∀ j ≤ K, t j ≤ β := fun j hj => htK ▸ ht hj
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hα (htα j)
  have hb := bsc_blk_sum L hL t ht (by rw [ht0]; exact h2) f (fun j => f (t (j+1))) K
    (fun j hj v h1 h3 => hf ⟨(htα j).trans h1.le, h3.trans (htβ (j+1) hj)⟩ ⟨htα _, htβ _ hj⟩ h3)
    (fun j hj => hf0 _ ⟨htα _, htβ _ hj⟩)
  rw [ht0, htK] at hb
  beta_reduce at hb
  refine hb.trans ?_
  have hfi : IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
    apply bsc_fint α β hα hαβ
    apply MonotoneOn.intervalIntegrable; rwa [Set.uIcc_of_le hαβ]
  have hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1)) := by
    intro j hj
    apply hfi.mono_set
    rw [Set.uIcc_of_le hαβ, Set.uIcc_of_le (ht (Nat.le_succ j))]
    exact Set.Icc_subset_Icc (htα j) (htβ _ hj)
  have hr := bsc_riem t K Δ f (fun j => f (t j)) (fun j _ => ht (Nat.le_succ j)) (fun j _ => htpos j)
    (fun j _ => hratio j)
    (fun j hj u hu => hf ⟨htα _, htβ _ hj.le⟩ ⟨(htα j).trans hu.1, hu.2.trans (htβ _ hj)⟩ hu.1) hint
  rw [ht0, htK] at hr
  beta_reduce at hr
  have htel : ∑ j ∈ range K, (f (t (j+1)) - f (t j)) = f β - f α := by
    rw [sum_range_sub (fun j => f (t j)), htK, ht0]
  have herr : ∑ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) ≤ K * f β * (4 / (α * L)) := by
    have : ∀ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) ≤ f β * (4 / (α * L)) := by
      intro j hj
      have hj' := mem_range.mp hj
      apply mul_le_mul
      · exact hf ⟨htα _, htβ _ hj'⟩ ⟨hαβ, le_rfl⟩ (htβ _ hj')
      · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hα hL)
          (mul_le_mul_of_nonneg_right (htα j) hL.le)
      · exact (div_pos (by norm_num) (mul_pos (htpos j) hL)).le
      · exact hf0 β ⟨hαβ, le_rfl⟩
    calc _ ≤ ∑ j ∈ range K, f β * (4 / (α * L)) := sum_le_sum this
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hsplit : ∑ j ∈ range K, f (t (j+1)) * (log (t (j+1) / t j) + 4 / (t j * L)) =
      ∑ j ∈ range K, f (t j) * Δ + (∑ j ∈ range K, (f (t (j+1)) - f (t j))) * Δ +
      ∑ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) := by
    rw [sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _; rw [hratio j]; ring
  rw [hsplit, htel]
  linarith

private theorem bsc_anti_sum (L α β : ℝ) (K : ℕ) (hK : 0 < K) (hL : 0 < L) (hα : 0 < α) (hαβ : α ≤ β)
    (h2 : log 2 ≤ α * L) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc α β))
    (hf0 : ∀ v ∈ Set.Icc α β, 0 ≤ f v) :
    ∑ q ∈ Ioc ⌊exp (α * L)⌋₊ ⌊exp (β * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      (∫ u in α..β, f u / u) + (f α - f β) * (log (β / α) / K) + K * f α * (4 / (α * L)) := by
  obtain ⟨hΔ0, ht, ht0, htK, hratio⟩ := bsc_geo_part α β K hK hα hαβ
  set Δ := log (β / α) / K with hΔdef
  set t : ℕ → ℝ := fun j => α * exp (j * Δ) with htdef
  have htα : ∀ j, α ≤ t j := fun j => ht0 ▸ ht (Nat.zero_le j)
  have htβ : ∀ j ≤ K, t j ≤ β := fun j hj => htK ▸ ht hj
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hα (htα j)
  have hb := bsc_blk_sum L hL t ht (by rw [ht0]; exact h2) f (fun j => f (t j)) K
    (fun j hj v h1 h3 => hf ⟨htα _, htβ _ hj.le⟩ ⟨(htα j).trans h1.le, h3.trans (htβ (j+1) hj)⟩ h1.le)
    (fun j hj => hf0 _ ⟨htα _, htβ _ hj.le⟩)
  rw [ht0, htK] at hb
  beta_reduce at hb
  refine hb.trans ?_
  have hfi : IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
    apply bsc_fint α β hα hαβ
    apply AntitoneOn.intervalIntegrable; rwa [Set.uIcc_of_le hαβ]
  have hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1)) := by
    intro j hj
    apply hfi.mono_set
    rw [Set.uIcc_of_le hαβ, Set.uIcc_of_le (ht (Nat.le_succ j))]
    exact Set.Icc_subset_Icc (htα j) (htβ _ hj)
  have hr := bsc_riem t K Δ f (fun j => f (t (j+1))) (fun j _ => ht (Nat.le_succ j)) (fun j _ => htpos j)
    (fun j _ => hratio j)
    (fun j hj u hu => hf ⟨(htα j).trans hu.1, hu.2.trans (htβ _ hj)⟩ ⟨htα _, htβ _ hj⟩ hu.2) hint
  rw [ht0, htK] at hr
  beta_reduce at hr
  have htel : ∑ j ∈ range K, (f (t j) - f (t (j+1))) = f α - f β := by
    have := sum_range_sub (fun j => f (t j)) K
    rw [htK, ht0] at this
    rw [← neg_sub (f β), ← this, ← sum_neg_distrib]
    apply sum_congr rfl; intro j _; ring
  have herr : ∑ j ∈ range K, f (t j) * (4 / (t j * L)) ≤ K * f α * (4 / (α * L)) := by
    have : ∀ j ∈ range K, f (t j) * (4 / (t j * L)) ≤ f α * (4 / (α * L)) := by
      intro j hj
      have hj' := mem_range.mp hj
      apply mul_le_mul
      · exact hf ⟨le_rfl, hαβ⟩ ⟨htα _, htβ _ hj'.le⟩ (htα j)
      · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hα hL)
          (mul_le_mul_of_nonneg_right (htα j) hL.le)
      · exact (div_pos (by norm_num) (mul_pos (htpos j) hL)).le
      · exact hf0 α ⟨le_rfl, hαβ⟩
    calc _ ≤ ∑ j ∈ range K, f α * (4 / (α * L)) := sum_le_sum this
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hsplit : ∑ j ∈ range K, f (t j) * (log (t (j+1) / t j) + 4 / (t j * L)) =
      ∑ j ∈ range K, f (t (j+1)) * Δ + (∑ j ∈ range K, (f (t j) - f (t (j+1)))) * Δ +
      ∑ j ∈ range K, f (t j) * (4 / (t j * L)) := by
    rw [sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _; rw [hratio j]; ring
  rw [hsplit, htel]
  linarith

private theorem bsc_bdry (S : Finset ℕ) (y x B : ℝ) (g : ℕ → ℝ) (hy : 0 ≤ y) (hB : 0 ≤ B)
    (hS : ∀ q ∈ S, q.Prime ∧ y ≤ q ∧ (q : ℝ) ≤ x)
    (hg0 : ∀ q : ℕ, q.Prime → y ≤ q → (q : ℝ) ≤ x → 0 ≤ g q)
    (hgB : ∀ q ∈ S, g q ≤ B) :
    ∑ q ∈ S, g q ≤ ∑ q ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, (if q.Prime then g q else 0) + B := by
  rw [← sum_filter_add_sum_filter_not S (fun q => q ≤ ⌊y⌋₊)]
  have h1 : ∑ q ∈ S.filter (fun q => q ≤ ⌊y⌋₊), g q ≤ B := by
    have key : ∀ c ∈ S.filter (fun q => q ≤ ⌊y⌋₊), c = ⌊y⌋₊ := by
      intro c hc
      obtain ⟨hcS, hcy⟩ := mem_filter.mp hc
      have h1 : (c : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hcy
      have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
      have h3 := (hS c hcS).2.1
      have : (c : ℝ) = ⌊y⌋₊ := le_antisymm h1 (h2.trans h3)
      exact_mod_cast this
    have hc : (S.filter (fun q => q ≤ ⌊y⌋₊)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      rw [key a ha, key b hb]
    calc _ ≤ ∑ q ∈ S.filter (fun q => q ≤ ⌊y⌋₊), B :=
          sum_le_sum (fun q hq => hgB q (mem_filter.mp hq).1)
      _ = (S.filter (fun q => q ≤ ⌊y⌋₊)).card * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
      _ = B := one_mul B
  have h2 : ∑ q ∈ S.filter (fun q => ¬ q ≤ ⌊y⌋₊), g q ≤
      ∑ q ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, (if q.Prime then g q else 0) := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqS, hqy⟩ := mem_filter.mp hq
      obtain ⟨hp, _, hqx⟩ := hS q hqS
      have hx : 0 ≤ x := le_trans (Nat.cast_nonneg q) hqx
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, Nat.le_floor hqx⟩, hp⟩
    · intro q hq _
      obtain ⟨hq1, hp⟩ := mem_filter.mp hq
      have hlt := (mem_Ioc.mp hq1)
      have hx : 0 ≤ x := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_of_nonpos hneg.le] at hlt
        omega
      exact hg0 q hp ((Nat.floor_lt hy).mp hlt.1).le ((Nat.le_floor_iff hx).mp hlt.2)
  linarith

private theorem bsc_inner_int (a α : ℝ) (hα : 0 < α) (h : 2 * α ≤ a) :
    ∫ v in α..(a / 2), (1 / (a - v)) / v = log ((a - α) / α) / a := by
  have ha : 0 < a := by linarith
  have hsub : ∀ v ∈ Set.uIcc α (a / 2), 0 < v ∧ 0 < a - v := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hderiv : ∀ v ∈ Set.uIcc α (a / 2),
      HasDerivAt (fun v => (log v - log (a - v)) / a) ((1 / (a - v)) / v) v := by
    intro v hv
    obtain ⟨h1, h2⟩ := hsub v hv
    have d1 := hasDerivAt_log h1.ne'
    have d2 : HasDerivAt (fun v => log (a - v)) ((a - v)⁻¹ * (-1)) v := by
      have := ((hasDerivAt_id v).const_sub a)
      exact (hasDerivAt_log h2.ne').comp v (by simpa using this)
    convert (d1.sub d2).div_const a using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun v => (1 / (a - v)) / v) (Set.uIcc α (a / 2)) := by
    apply ContinuousOn.div (ContinuousOn.div continuousOn_const (by fun_prop) ?_) continuousOn_id
    · intro v hv; exact (hsub v hv).1.ne'
    · intro v hv; exact (hsub v hv).2.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have e1 : a - a / 2 = a / 2 := by ring
  rw [e1, sub_self, zero_div, zero_sub, ← neg_div, neg_sub, log_div (by linarith) hα.ne']

private theorem bsc_logratio_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    log a / (a + 1) ≤ log b / (b + 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hl1 : log a ≤ a - 1 := log_le_sub_one_of_pos ha0
  have hl0 : 0 ≤ log a := log_nonneg ha
  have hlr : 1 - a / b ≤ log (b / a) := by
    have := one_sub_inv_le_log_of_pos (div_pos hb0 ha0)
    rwa [inv_div] at this
  rw [log_div hb0.ne' ha0.ne'] at hlr
  have hq : (b - a) / b ≤ log b - log a := by
    have : 1 - a / b = (b - a) / b := by field_simp
    linarith
  have hq' : (b - a) ≤ (log b - log a) * b := by
    rwa [div_le_iff₀ hb0] at hq
  -- need log a * (b + 1) ≤ log b * (a + 1), i.e. log a * (b - a) ≤ (log b - log a) * (a + 1)
  have hla : log a * b ≤ a + 1 := by nlinarith
  have hdiff : 0 ≤ log b - log a := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq' hdiff, mul_nonneg hdiff hl0]

/-- The inner weight 1/(1 - u - v) of the mixed pair sum. -/
private def bsc_f2 (u v : ℝ) : ℝ := 1 / (1 - u - v)

/-- The inner integral of the mixed pair sum, in closed form. -/
private def bsc_G2 (u : ℝ) : ℝ := log ((1 - u - 100 / 329) / (100 / 329)) / (1 - u)

private lemma bsc_exp_rpow (N : ℕ) (hN : 0 < N) (c : ℝ) : (N : ℝ) ^ c = exp (c * log N) := by
  rw [rpow_def_of_pos (by exact_mod_cast hN), mul_comm]

private lemma bsc_z1 (N : ℕ) (hN : 0 < N) : z1 N = exp (1 / 11 * log N) := by
  show (N : ℝ) ^ (1 / 11 : ℝ) = _
  exact bsc_exp_rpow N hN _

private lemma bsc_z2 (N : ℕ) (hN : 0 < N) : z2 N = exp (100 / 329 * log N) := by
  show (N : ℝ) ^ (1 / 3.29 : ℝ) = _
  rw [bsc_exp_rpow N hN]; norm_num

private lemma bsc_lo {L a q : ℝ} (hL : 0 < L) (h : exp (a * L) ≤ q) : a ≤ log q / L := by
  rw [le_div_iff₀ hL]
  have := log_le_log (exp_pos _) h
  rwa [log_exp] at this

private lemma bsc_hi {L b q : ℝ} (hL : 0 < L) (hq : 0 < q) (h : q ≤ exp (b * L)) :
    log q / L ≤ b := by
  rw [div_le_iff₀ hL]
  have := log_le_log hq h
  rwa [log_exp] at this

private lemma bsc_hi' {L b q : ℝ} (hL : 0 < L) (hq : 0 < q) (h : q < exp (b * L)) :
    log q / L < b := by
  rw [div_lt_iff₀ hL]
  have := log_lt_log hq h
  rwa [log_exp] at this

private lemma bsc_N_pos (N : ℕ) (hL : 0 < log (N : ℝ)) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp at hL
  · exact h

private lemma bsc_exp_gt (c L : ℝ) : c * L < exp (c * L) := by
  linarith [add_one_le_exp (c * L)]

private lemma bsc_G2_bounds (u : ℝ) (h1 : 1 / 11 ≤ u) (h2 : u ≤ 100 / 329) :
    0 ≤ bsc_G2 u ∧ bsc_G2 u ≤ 2 := by
  unfold bsc_G2
  have hw1 : 1 ≤ (1 - u - 100 / 329) / (100 / 329) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hw2 : (1 - u - 100 / 329) / (100 / 329) ≤ 2 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  have hl0 := log_nonneg hw1
  have hl1 : log ((1 - u - 100 / 329) / (100 / 329)) ≤ 1 := by
    have := log_le_sub_one_of_pos (show 0 < (1 - u - 100 / 329) / (100 / 329) by linarith)
    linarith
  have hd : 0 < 1 - u := by linarith
  refine ⟨div_nonneg hl0 hd.le, ?_⟩
  rw [div_le_iff₀ hd]; linarith

private lemma bsc_G2_anti : AntitoneOn bsc_G2 (Set.Icc (1 / 11) (100 / 329)) := by
  intro a ha b hb hab
  have key : ∀ u, u ≤ 100 / 329 → bsc_G2 u =
      log ((1 - u - 100 / 329) / (100 / 329)) / ((1 - u - 100 / 329) / (100 / 329) + 1) *
        (329 / 100) := by
    intro u hu
    unfold bsc_G2
    have h1 : (1 - u - 100 / 329) / (100 / 329) + 1 = (1 - u) * (329 / 100) := by ring
    rw [h1]
    have hd : (1 - u) ≠ 0 := by intro h; linarith
    field_simp
  rw [key a ha.2, key b hb.2]
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  apply bsc_logratio_mono
  · rw [le_div_iff₀ (by norm_num)]; linarith [hb.2]
  · apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith [ha.1]

/-- The mixed pair region splits as an outer prime sum of inner prime sums. -/
private lemma bsc_two_split (N : ℕ) (hN : 2 ≤ N) :
    log N * ∑ b ∈ switchedPairs118 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ))) ≤
    ∑ p ∈ (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ z1 N ≤ p ∧ (p : ℝ) < z2 N),
      (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc_f2 (log p / log N) (log q / log N) / q := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos hNr
  -- the term identity and positivity
  have hterm : ∀ p q : ℕ, p.Prime → q.Prime → (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) →
      (p : ℝ) < N →
      log N * (1 / ((p * q : ℕ) * log ((N : ℝ) / (p * q : ℕ)))) =
        (1 / (p : ℝ)) * (bsc_f2 (log p / log N) (log q / log N) / q) ∧
      0 ≤ (1 / (p : ℝ)) * (bsc_f2 (log p / log N) (log q / log N) / q) := by
    intro p q hp hq hqr hpN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hNp : 0 < (N : ℝ) / p := div_pos (by linarith) hp0
    rw [← sqrt_eq_rpow, lt_sqrt hq0.le] at hqr
    have hpq : (p : ℝ) * q < N := by
      have h1 := (lt_div_iff₀ hp0).mp hqr
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      nlinarith
    have hlog : log ((N : ℝ) / (p * q)) = log N - log p - log q := by
      rw [log_div (by linarith) (by positivity), log_mul hp0.ne' hq0.ne']; ring
    have hpos : 0 < log N - log p - log q := by
      rw [← hlog]; apply log_pos; rw [one_lt_div (by positivity)]; exact hpq
    have hden : 1 - log p / log N - log q / log N = (log N - log p - log q) / log N := by
      field_simp
    unfold bsc_f2
    rw [hden]
    push_cast
    rw [hlog]
    constructor
    · field_simp
    · have : 0 < (log N - log p - log q) / log N := div_pos hpos hL
      positivity
  unfold switchedPairs118
  rw [sum_filter, Finset.product_eq_sprod, sum_product, mul_sum, sum_filter]
  apply sum_le_sum
  intro p hp
  split_ifs with hpc
  · rw [mul_sum, mul_sum, sum_filter]
    apply sum_le_sum
    intro q hq
    by_cases h1 : (p.Prime ∧ q.Prime ∧ z1 N ≤ (p : ℝ) ∧ (p : ℝ) < z2 N ∧
        z2 N ≤ (q : ℝ) ∧ (q : ℝ) < ((N : ℝ) / (p : ℝ)) ^ (1 / 2 : ℝ) ∧ Nat.Coprime (p * q) N)
    · have h2 : q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) :=
        ⟨h1.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1⟩
      have hz2N : z2 N < N := by
        show (N : ℝ) ^ (1 / 3.29 : ℝ) < N
        simpa using rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1 / 3.29 : ℝ) < 1)
      have hpN : (p : ℝ) < N := h1.2.2.2.1.trans hz2N
      rw [if_pos h1, if_pos h2]
      exact le_of_eq (hterm p q h1.1 h1.2.1 h1.2.2.2.2.2.1 hpN).1
    · rw [if_neg h1]
      split_ifs with h2
      · have hz2N : z2 N < N := by
          show (N : ℝ) ^ (1 / 3.29 : ℝ) < N
          simpa using rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1 / 3.29 : ℝ) < 1)
        rw [mul_zero]
        exact (hterm p q hpc.1 h2.1 h2.2.2 (hpc.2.2.trans hz2N)).2
      · simp
  · rw [mul_sum]
    apply le_of_eq
    apply sum_eq_zero
    intro q _
    rw [if_neg]
    · simp
    · intro h
      exact hpc ⟨h.1, h.2.2.1, h.2.2.2.1⟩

/-- The inner prime sum of the mixed region for one outer prime. -/
private lemma bsc_two_inner (N : ℕ) (hL70 : 70 ≤ log (N : ℝ)) (K : ℕ) (hK : 0 < K) (p : ℕ)
    (hp : p.Prime) (hp1 : z1 N ≤ p) (hp2 : (p : ℝ) < z2 N) :
    ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
      bsc_f2 (log p / log N) (log q / log N) / q ≤
      bsc_G2 (log p / log N) + (3 / K + 40 * K / log N + 10 / log N) := by
  set L := log (N : ℝ) with hLdef
  have hL : 0 < L := by linarith
  have hN0 : 0 < N := bsc_N_pos N hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [bsc_z1 N hN0] at hp1
  rw [bsc_z2 N hN0] at hp2
  set u := log p / L with hu
  have hu1 : 1 / 11 ≤ u := bsc_lo hL hp1
  have hu2 : u < 100 / 329 := bsc_hi' hL hp0 hp2
  have huL : u * L = log p := by rw [hu]; field_simp
  set β := (1 - u) / 2 with hβ
  have hroot : ((N : ℝ) / p) ^ (1 / 2 : ℝ) = exp (β * L) := by
    rw [rpow_def_of_pos (div_pos (by exact_mod_cast hN0) hp0), log_div (by positivity) hp0.ne',
      ← huL, hβ]
    congr 1; ring
  have hαβ : (100 / 329 : ℝ) ≤ β := by rw [hβ]; linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- the weight on the closed range
  have hfpos : ∀ v, v ≤ β → (1 - u) / 2 ≤ 1 - u - v := by intro v hv; rw [hβ] at hv; linarith
  have hf3 : ∀ v, v ≤ β → bsc_f2 u v ≤ 3 := by
    intro v hv
    have := hfpos v hv
    unfold bsc_f2
    rw [div_le_iff₀ (by linarith)]; linarith
  have hf0 : ∀ v, v ≤ β → 0 ≤ bsc_f2 u v := by
    intro v hv
    have := hfpos v hv
    unfold bsc_f2
    exact (div_pos one_pos (by linarith)).le
  have hb := bsc_bdry ((range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ exp (100 / 329 * L) ≤ q ∧ (q : ℝ) < exp (β * L)))
    (exp (100 / 329 * L)) (exp (β * L)) (3 / exp (100 / 329 * L))
    (fun q => bsc_f2 u (log q / L) / q) (exp_pos _).le (by positivity)
    (fun q hq => by
      obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hq
      exact ⟨h1, h2, h3.le⟩)
    (fun q _ hq1 hq2 => by
      have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) hq1
      exact div_nonneg (hf0 _ (bsc_hi hL hq0 hq2)) hq0.le)
    (fun q hq => by
      obtain ⟨_, _, h2, h3⟩ := mem_filter.mp hq
      have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) h2
      calc bsc_f2 u (log q / L) / q ≤ 3 / q :=
            div_le_div_of_nonneg_right (hf3 _ (bsc_hi hL hq0 h3.le)) hq0.le
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (exp_pos _) h2)
  have hlog2 : log 2 ≤ 100 / 329 * L := by
    have := log_two_lt_d9; linarith
  have hmono : MonotoneOn (bsc_f2 u) (Set.Icc (100 / 329) β) := by
    intro a ha b hb hab
    have h1 := hfpos a ha.2
    have h2 := hfpos b hb.2
    unfold bsc_f2
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hm := bsc_mono_sum L (100 / 329) β K hK hL (by norm_num) hαβ hlog2 (bsc_f2 u) hmono
    (fun v hv => hf0 v hv.2)
  have hint : ∫ v in (100 / 329 : ℝ)..β, bsc_f2 u v / v = bsc_G2 u := by
    unfold bsc_f2 bsc_G2
    rw [hβ]
    exact bsc_inner_int (1 - u) (100 / 329) (by norm_num) (by linarith)
  rw [hint] at hm
  -- the error terms
  have hratio : log (β / (100 / 329)) / K ≤ 1 / K := by
    apply div_le_div_of_nonneg_right _ hKr.le
    have := log_le_sub_one_of_pos (show 0 < β / (100 / 329) by positivity)
    have : β / (100 / 329) ≤ 2 := by rw [div_le_iff₀ (by norm_num)]; rw [hβ]; linarith
    linarith
  have hratio0 : 0 ≤ log (β / (100 / 329)) / K :=
    div_nonneg (log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)) hKr.le
  have hdiff : (bsc_f2 u β - bsc_f2 u (100 / 329)) * (log (β / (100 / 329)) / K) ≤ 3 / K := by
    have h1 : bsc_f2 u β - bsc_f2 u (100 / 329) ≤ 3 := by
      linarith [hf3 β le_rfl, hf0 (100 / 329) hαβ]
    have h0 : 0 ≤ bsc_f2 u β - bsc_f2 u (100 / 329) := by
      linarith [hmono ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ]
    calc _ ≤ 3 * (1 / (K : ℝ)) := mul_le_mul h1 hratio hratio0 (by norm_num)
      _ = 3 / (K : ℝ) := by ring
  have hlast : (K : ℝ) * bsc_f2 u β * (4 / (100 / 329 * L)) ≤ 40 * K / L := by
    have := hf3 β le_rfl
    have h0 := hf0 β le_rfl
    calc (K : ℝ) * bsc_f2 u β * (4 / (100 / 329 * L)) ≤ K * 3 * (4 / (100 / 329 * L)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left this hKr.le
      _ = 39.48 * K / L := by field_simp; ring
      _ ≤ 40 * K / L := by
          apply div_le_div_of_nonneg_right _ hL.le; nlinarith
  have hbd : 3 / exp (100 / 329 * L) ≤ 10 / L := by
    have := bsc_exp_gt (100 / 329) L
    calc 3 / exp (100 / 329 * L) ≤ 3 / (100 / 329 * L) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) this.le
      _ = 9.87 / L := by field_simp; ring
      _ ≤ 10 / L := div_le_div_of_nonneg_right (by norm_num) hL.le
  have hset : (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)) =
      (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ exp (100 / 329 * L) ≤ q ∧ (q : ℝ) < exp (β * L)) := by
    rw [hroot, bsc_z2 N hN0]
  rw [hset]
  linarith

/-- The outer prime sum of the mixed region against its integral. -/
private lemma bsc_two_outer (N : ℕ) (hL70 : 70 ≤ log (N : ℝ)) (K : ℕ) (hK : 0 < K) :
    ∑ p ∈ (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ z1 N ≤ p ∧ (p : ℝ) < z2 N),
      (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc_f2 (log p / log N) (log q / log N) / q ≤
      (∫ u in (1 / 11 : ℝ)..(100 / 329), bsc_G2 u / u) +
        (11 / K + 168 * K / log N + 42 / log N) := by
  have hL : 0 < log (N : ℝ) := by linarith
  have hN0 : 0 < N := bsc_N_pos N hL
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set E1 : ℝ := 3 / K + 40 * K / log N + 10 / log N with hE1
  have hE10 : 0 ≤ E1 := by positivity
  set P1 := (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ z1 N ≤ p ∧ (p : ℝ) < z2 N) with hP1
  have hstep : ∑ p ∈ P1, (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ z2 N ≤ q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc_f2 (log p / log N) (log q / log N) / q ≤
      ∑ p ∈ P1, bsc_G2 (log p / log N) / p + E1 * ∑ p ∈ P1, (1 / (p : ℝ)) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpp, hp1, hp2⟩ := mem_filter.mp hp
    have h := bsc_two_inner N hL70 K hK p hpp hp1 hp2
    have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    calc _ ≤ (1 / (p : ℝ)) * (bsc_G2 (log p / log N) + E1) := mul_le_mul_of_nonneg_left h hp0
      _ = _ := by ring
  have hP1' : P1 = (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ exp (1 / 11 * log N) ≤ p ∧
      (p : ℝ) < exp (100 / 329 * log N)) := by
    rw [hP1, bsc_z1 N hN0, bsc_z2 N hN0]
  have hS : ∀ p ∈ P1, p.Prime ∧ exp (1 / 11 * log N) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ exp (100 / 329 * log N) := by
    intro p hp
    rw [hP1'] at hp
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hp
    exact ⟨h1, h2, h3.le⟩
  have hlog2 : log 2 ≤ 1 / 11 * log N := by
    have := log_two_lt_d9; linarith
  have hbd1 : 1 / exp (1 / 11 * log N) ≤ 11 / log N := by
    have := bsc_exp_gt (1 / 11) (log N)
    calc 1 / exp (1 / 11 * log N) ≤ 1 / (1 / 11 * log N) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) this.le
      _ = 11 / log N := by field_simp
  -- the reciprocal mass
  have hrec : ∑ p ∈ P1, (1 / (p : ℝ)) ≤ 2 := by
    have hb := bsc_bdry P1 (exp (1 / 11 * log N)) (exp (100 / 329 * log N))
      (1 / exp (1 / 11 * log N)) (fun p => 1 / (p : ℝ)) (exp_pos _).le (by positivity) hS
      (fun q _ _ _ => by positivity)
      (fun q hq => div_le_div_of_nonneg_left (by norm_num) (exp_pos _) (hS q hq).2.1)
    have hm := bsc_mono_sum (log N) (1 / 11) (100 / 329) 1 one_pos hL (by norm_num) (by norm_num)
      hlog2 (fun _ => (1 : ℝ)) (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one)
    beta_reduce at hm
    rw [integral_one_div_of_pos (by norm_num) (by norm_num)] at hm
    have hlb : log ((100 / 329 : ℝ) / (1 / 11)) ≤ 1.2070078 := by
      rw [show (100 / 329 : ℝ) / (1 / 11) = 1100 / 329 by norm_num]; exact log_ba_le
    have h44 : (((1 : ℕ) : ℝ)) * 1 * (4 / (1 / 11 * log N)) = 44 / log N := by
      field_simp; ring
    rw [h44] at hm
    have h55 : 44 / log N + 11 / log N ≤ 0.79 := by
      rw [← add_div, div_le_iff₀ hL]; linarith
    linarith
  -- the main outer sum
  have hmain : ∑ p ∈ P1, bsc_G2 (log p / log N) / p ≤
      (∫ u in (1 / 11 : ℝ)..(100 / 329), bsc_G2 u / u) + 5 / K + 88 * K / log N +
        22 / log N := by
    have hb := bsc_bdry P1 (exp (1 / 11 * log N)) (exp (100 / 329 * log N))
      (2 / exp (1 / 11 * log N)) (fun p => bsc_G2 (log p / log N) / p) (exp_pos _).le
      (by positivity) hS
      (fun q _ hq1 hq2 => by
        have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) hq1
        exact div_nonneg (bsc_G2_bounds _ (bsc_lo hL hq1) (bsc_hi hL hq0 hq2)).1 hq0.le)
      (fun q hq => by
        obtain ⟨_, hq1, hq2⟩ := hS q hq
        have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) hq1
        have hG := (bsc_G2_bounds _ (bsc_lo hL hq1) (bsc_hi hL hq0 hq2)).2
        calc bsc_G2 (log q / log N) / q ≤ 2 / q := div_le_div_of_nonneg_right hG hq0.le
          _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (exp_pos _) hq1)
    have ha := bsc_anti_sum (log N) (1 / 11) (100 / 329) K hK hL (by norm_num) (by norm_num)
      hlog2 bsc_G2 bsc_G2_anti (fun v hv => (bsc_G2_bounds v hv.1 hv.2).1)
    have hG1 := bsc_G2_bounds (1 / 11) le_rfl (by norm_num)
    have hG2 := bsc_G2_bounds (100 / 329) (by norm_num) le_rfl
    have hlr : log ((100 / 329 : ℝ) / (1 / 11)) / K ≤ 2.4 / K := by
      apply div_le_div_of_nonneg_right _ hKr.le
      have := log_le_sub_one_of_pos (show (0 : ℝ) < (100 / 329) / (1 / 11) by norm_num)
      norm_num at this ⊢; linarith
    have hlr0 : 0 ≤ log ((100 / 329 : ℝ) / (1 / 11)) / K :=
      div_nonneg (log_nonneg (by norm_num)) hKr.le
    have hd1 : (bsc_G2 (1 / 11) - bsc_G2 (100 / 329)) * (log ((100 / 329 : ℝ) / (1 / 11)) / K)
        ≤ 5 / K := by
      calc _ ≤ 2 * (2.4 / (K : ℝ)) := mul_le_mul (by linarith) hlr hlr0 (by norm_num)
        _ ≤ 5 / (K : ℝ) := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by norm_num) hKr.le
    have hd2 : (K : ℝ) * bsc_G2 (1 / 11) * (4 / (1 / 11 * log N)) ≤ 88 * K / log N := by
      calc (K : ℝ) * bsc_G2 (1 / 11) * (4 / (1 / 11 * log N)) ≤ K * 2 * (4 / (1 / 11 * log N)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hG1.2 hKr.le
        _ = 88 * K / log N := by field_simp; ring
    have hbd2 : 2 / exp (1 / 11 * log N) ≤ 22 / log N := by
      have : 2 / exp (1 / 11 * log N) = 2 * (1 / exp (1 / 11 * log N)) := by ring
      rw [this]
      calc _ ≤ 2 * (11 / log N) := mul_le_mul_of_nonneg_left hbd1 (by norm_num)
        _ = 22 / log N := by ring
    linarith
  refine hstep.trans ?_
  have hE : E1 * ∑ p ∈ P1, (1 / (p : ℝ)) ≤ E1 * 2 := mul_le_mul_of_nonneg_left hrec hE10
  have hE2 : E1 * 2 = 6 / K + 80 * K / log N + 20 / log N := by rw [hE1]; ring
  have h11 : 5 / (K : ℝ) + 6 / K = 11 / K := by ring
  have h168 : 88 * (K : ℝ) / log N + 80 * K / log N = 168 * K / log N := by ring
  have h42 : 22 / log N + 20 / log N = 42 / log N := by ring
  linarith

private lemma bsc_two_integral :
    (∫ u in (1 / 11 : ℝ)..(100 / 329), bsc_G2 u / u) =
      ∫ t in (2.29 : ℝ)..10, log (2.29 - 3.29 / (t + 1)) / t := by
  rw [change_var]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by norm_num)] at hs
  obtain ⟨h1, h2⟩ := hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  have hs1 : 1 - s ≠ 0 := by intro h; linarith
  unfold bsc_G2
  have hw : (1 - s - 100 / 329) / (100 / 329) = 2.29 - 3.29 * s := by
    norm_num; ring
  simp only
  rw [hw]
  field_simp
  ring

/-- LEAF. Page 604 display 4.13, prime pair partial summation after the Li replacement.
This contains no switched count or short interval prime error. The pair region
still excludes factors of N, so the assertion is an upper limit with every reserve. -/
theorem leaf337_two_pair_sum :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      sieveTwoPairSum337 N ≤ sieveTwoCoefficient337 + δ := by
  intro δ hδ
  set c : ℝ := 8 / (2 * (0.95 : ℝ) - 1) with hc
  have hc0 : 0 < c := by norm_num [hc]
  have hc9 : c ≤ 9 := by norm_num [hc]
  set K : ℕ := ⌈200 / δ⌉₊ + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hKr : (200 / δ : ℝ) ≤ K := by
    rw [hKdef]; push_cast; linarith [Nat.le_ceil (200 / δ)]
  set L0 : ℝ := 70 + 18 * (168 * K + 42) / δ with hL0
  refine ⟨⌈exp L0⌉₊ + 2, fun N hN => ?_⟩
  have hNe : exp L0 ≤ (N : ℝ) := by
    have := Nat.le_ceil (exp L0)
    have h2 : ((⌈exp L0⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2; linarith
  have hN2 : 2 ≤ N := by omega
  have hLL : L0 ≤ log N := by
    have := log_le_log (exp_pos _) hNe; rwa [log_exp] at this
  have hq0 : 0 ≤ 18 * (168 * (K : ℝ) + 42) / δ := by positivity
  have hL70 : 70 ≤ log (N : ℝ) := by linarith
  have hL : 0 < log (N : ℝ) := by linarith
  have hmain := (bsc_two_split N hN2).trans (bsc_two_outer N hL70 K hK)
  unfold sieveTwoPairSum337 sieveTwoCoefficient337
  rw [← hc, ← bsc_two_integral, mul_assoc]
  have herr : c * (11 / K + 168 * K / log N + 42 / log N) ≤ δ := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hKd : 200 ≤ (K : ℝ) * δ := by rwa [div_le_iff₀ hδ] at hKr
    have e1 : 11 / (K : ℝ) ≤ 11 * δ / 200 := by
      rw [div_le_iff₀ hKpos]; nlinarith
    have e2 : 168 * K / log N + 42 / log N ≤ δ / 18 := by
      rw [← add_div, div_le_iff₀ hL]
      have h3 : 18 * (168 * (K : ℝ) + 42) / δ ≤ log N := by linarith
      rw [div_le_iff₀ hδ] at h3
      nlinarith
    have hpos : 0 ≤ 11 / (K : ℝ) + 168 * K / log N + 42 / log N := by positivity
    calc c * (11 / K + 168 * K / log N + 42 / log N) ≤
          9 * (11 / K + 168 * K / log N + 42 / log N) := mul_le_mul_of_nonneg_right hc9 hpos
      _ ≤ 9 * (11 * δ / 200 + δ / 18) := by nlinarith
      _ ≤ δ := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left hmain hc0.le
  have h5 : c * ((∫ u in (1 / 11 : ℝ)..(100 / 329), bsc_G2 u / u) +
      (11 / K + 168 * K / log N + 42 / log N)) =
      c * (∫ u in (1 / 11 : ℝ)..(100 / 329), bsc_G2 u / u) +
      c * (11 / K + 168 * K / log N + 42 / log N) := by ring
  linarith

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

