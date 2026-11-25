import LeanLab.ChenDoubleSieve.Decomp349cPrimeRegionRiemann

/-!
Proof of the LEAF `pt_region_boundary_mass` of Decomp349cPrimeRegionRiemann,
Wu 2004 page 39 equation 10.5, the boundary part of the two variable prime partial
summation. Source: https://arxiv.org/pdf/0705.1652.
The pairs of S N outside the open region have a prime dividing N or lying on a
boundary line or curve. Each such first prime is at least N to a, each such second
prime at least N to the minimum of lo, there are at most log N over log 2 plus 2 of
them per level, and the prime reciprocal sum up to N is at most 1 plus log N.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum

/-- The prime reciprocal sum up to N is at most 1 plus log N, by the harmonic bound. -/
theorem bm_prime_recip_le (N : ℕ) :
    ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / q ≤ 1 + log N := by
  have h1 : ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / q ≤
      ∑ q ∈ Finset.range (N + 1), (1 : ℝ) / q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have h2 : ∑ q ∈ Finset.range (N + 1), (1 : ℝ) / q = ((harmonic N : ℚ) : ℝ) := by
    rw [Finset.sum_range_succ', harmonic]
    push_cast
    simp [one_div]
  have h3 : ((harmonic N : ℚ) : ℝ) ≤ 1 + log N := harmonic_le_one_add_log N
  linarith

/-- N has at most log N over log 2 prime factors. -/
theorem bm_card_primeFactors_le (N : ℕ) (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ log N / log 2 := by
  have h2 : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hle : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
  have hR : (2 : ℝ) ^ N.primeFactors.card ≤ N := by exact_mod_cast h2.trans hle
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have := Real.log_le_log (by positivity) hR
  rwa [Real.log_pow] at this

/-- For a positive real x, the naturals n with log n over L equal to x form a set with
at most one element. -/
theorem bm_card_level_le (s : Finset ℕ) (L x : ℝ) (hL : 0 < L) :
    (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro m hm n hn
  simp only [Finset.mem_filter] at hm hn
  have h : log (m : ℝ) = log (n : ℝ) := by
    have := hm.2.2.trans hn.2.2.symm
    field_simp at this
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.2.1
  exact_mod_cast Real.log_injOn_pos hm0 hn0 h

/-- A level bound c at most log n over log N gives N to c at most n. -/
theorem bm_rpow_le_of_level {N n : ℕ} (hN : 2 ≤ N) (hn : 0 < n) {c : ℝ}
    (h : c ≤ log (n : ℝ) / log N) : (N : ℝ) ^ c ≤ n := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hL] at h
  rw [Real.rpow_def_of_pos hN0]
  calc rexp (log N * c) ≤ rexp (log n) := Real.exp_le_exp.mpr (by linarith)
    _ = n := Real.exp_log hn0

/-- K log N squared over N to c tends to 0 for c positive. -/
theorem bm_decay_tendsto {c : ℝ} (hc : 0 < c) (K : ℝ) :
    Tendsto (fun N : ℕ => K * (log (N : ℝ)) ^ 2 / (N : ℝ) ^ c) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hc).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ => K * (log x ^ (2 : ℝ) / x ^ c)) atTop (𝓝 0) := by
    simpa using h.const_mul K
  have := h'.comp tendsto_natCast_atTop_atTop
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp, Real.rpow_two]
  ring

/-- Primes of s that divide N or lie at one of two levels number at most the prime
factor count of N plus 2. -/
theorem bm_card_bad_le (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : ∀ n ∈ s, n.Prime)
    (L x y : ℝ) (hL : 0 < L) (R : ℕ → Prop) [DecidablePred R]
    (hR : ∀ n ∈ s, R n → (n ∣ N ∨ log (n : ℝ) / L = x ∨ log (n : ℝ) / L = y)) :
    ((s.filter R).card : ℝ) ≤ N.primeFactors.card + 2 := by
  have hsub : s.filter R ⊆ (N.primeFactors ∪ s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x)) ∪
      s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = y) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hp := hs n hn.1
    rcases hR n hn.1 hn.2 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Nat.mem_primeFactors.mpr ⟨hp, h, by omega⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hn.1, hp.pos, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn.1, hp.pos, h⟩)
  have h1 := bm_card_level_le s L x hL
  have h2 := bm_card_level_le s L y hL
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (N.primeFactors ∪ s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x))
    (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = y))
  have hu2 := Finset.card_union_le N.primeFactors (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x))
  have : (s.filter R).card ≤ N.primeFactors.card + 2 := by omega
  exact_mod_cast this

/-- Wu 2004 page 39 equation 10.5, the boundary mass, statement of
`pt_region_boundary_mass`: pairs on the boundary lines or curves, or with a prime
dividing N, have reciprocal mass at most a constant times log N squared over N to c,
with c the smaller of a and the minimum of lo. Proved by the harmonic bound, the
count of prime factors of N, and the uniqueness of a prime at a given level. -/
theorem pt_region_boundary_mass_proved {a b : ℝ} {lo hi : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (S : ℕ → Finset (ℕ × ℕ))
    (hclosed : ∀ᶠ N : ℕ in atTop, ∀ q ∈ S N, q.1.Prime ∧ q.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2 : ℝ) / log N ∈ Icc (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)))
    (hopen : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ × ℕ, q.1.Prime → q.2.Prime → q.1 < N → q.2 < N →
      q.1.Coprime N → q.2.Coprime N →
      log (q.1 : ℝ) / log N ∈ Ioo a b →
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)) →
      q ∈ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N \ ptOpenRegion a b lo hi N, 1 / ((q.1 : ℝ) * q.2))
      atTop (𝓝 0) := by
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hlo
  set m := lo t0 with hm_def
  have hm : 0 < m := hlo0 t0 ht0
  set c := min a m with hc_def
  have hc : 0 < c := lt_min ha hm
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun x _ => by positivity)
    ?_ (bm_decay_tendsto hc (4 * (1 / log 2 + 2)))
  filter_upwards [hclosed, eventually_ge_atTop 3] with N hN hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set Q := (Finset.range (N + 1)).filter Nat.Prime with hQ
  set lev : ℕ → ℝ := fun n => log (n : ℝ) / log N with hlev
  set Pb := Q.filter (fun p : ℕ => (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p ∣ N ∨ lev p = a ∨ lev p = b)) with hPb
  set Qb : ℕ → Finset ℕ := fun p : ℕ => Q.filter (fun q : ℕ => (N : ℝ) ^ m ≤ (q : ℝ) ∧
    (q ∣ N ∨ lev q = lo (lev p) ∨ lev q = hi (lev p))) with hQb
  set T := (Q ×ˢ Q).filter (fun x => x.2 ∈ Qb x.1) with hT
  set f : ℕ × ℕ → ℝ := fun x => 1 / ((x.1 : ℝ) * x.2) with hf
  have hfnn : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  -- membership of S N in the prime box
  have hle_of_lev : ∀ n : ℕ, 0 < n → lev n ≤ 1 → n ≤ N := by
    intro n hn h
    have h' : log (n : ℝ) ≤ log N := by
      simp only [hlev] at h
      rwa [div_le_one hL] at h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast (Real.log_le_log_iff hn0 hN0).mp h'
  have hsub : S N \ ptOpenRegion a b lo hi N ⊆ (Pb ×ˢ Q) ∪ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hp, hq, ht, hu⟩ := hN x hx.1
    have hp1 : x.1 ≤ N := hle_of_lev x.1 hp.pos (ht.2.trans hb1)
    have hq1 : x.2 ≤ N := hle_of_lev x.2 hq.pos (hu.2.trans (hhi1 _ ht))
    have hpQ : x.1 ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hqQ : x.2 ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
    by_cases hbad : x.1 ∣ N ∨ lev x.1 = a ∨ lev x.1 = b
    · refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, hqQ⟩)
      exact Finset.mem_filter.mpr ⟨hpQ, bm_rpow_le_of_level (by omega) hp.pos ht.1, hbad⟩
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hpQ, hqQ⟩, Finset.mem_filter.mpr ⟨hqQ, ?_, ?_⟩⟩)
      · exact bm_rpow_le_of_level (by omega) hq.pos ((hmin ht).trans hu.1)
      · by_contra hgood
        push Not at hbad hgood
        apply hx.2
        have hpN : x.1 < N := lt_of_le_of_ne hp1 (fun h => hbad.1 (h ▸ dvd_refl _))
        have hqN : x.2 < N := lt_of_le_of_ne hq1 (fun h => hgood.1 (h ▸ dvd_refl _))
        simp only [ptOpenRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨hpN, hqN⟩, hp, hq, (Nat.Prime.coprime_iff_not_dvd hp).mpr hbad.1,
          (Nat.Prime.coprime_iff_not_dvd hq).mpr hgood.1,
          ⟨lt_of_le_of_ne ht.1 (Ne.symm hbad.2.1), lt_of_le_of_ne ht.2 hbad.2.2⟩,
          ⟨lt_of_le_of_ne hu.1 (Ne.symm hgood.2.1), lt_of_le_of_ne hu.2 hgood.2.2⟩⟩
  -- the harmonic bound
  have hH := bm_prime_recip_le N
  have hpf := bm_card_primeFactors_le N (by omega)
  set cp : ℝ := (N.primeFactors.card : ℝ) + 2 with hcp
  have hcp0 : 0 ≤ cp := by positivity
  have hQprime : ∀ n ∈ Q, n.Prime := fun n hn => (Finset.mem_filter.mp hn).2
  have hNa : (N : ℝ) ^ c ≤ (N : ℝ) ^ a :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_left _ _)
  have hNm : (N : ℝ) ^ c ≤ (N : ℝ) ^ m :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_right _ _)
  have hNc : 0 < (N : ℝ) ^ c := Real.rpow_pos_of_pos hN0 c
  -- first piece
  have hP : ∑ x ∈ Pb ×ˢ Q, f x ≤ cp / (N : ℝ) ^ c * (1 + log N) := by
    rw [Finset.sum_product]
    have hstep : ∀ p ∈ Pb, ∑ q ∈ Q, f (p, q) = (1 / (p : ℝ)) * ∑ q ∈ Q, (1 : ℝ) / q := by
      intro p _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hf]
      rw [one_div_mul_one_div]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
    have hsumP : ∑ p ∈ Pb, (1 / (p : ℝ)) ≤ cp / (N : ℝ) ^ c := by
      have hcard : (Pb.card : ℝ) ≤ cp :=
        bm_card_bad_le N (by omega) Q hQprime (log N) a b hL _ (fun n _ h => h.2)
      have hterm : ∀ p ∈ Pb, (1 / (p : ℝ)) ≤ 1 / (N : ℝ) ^ c := by
        intro p hp
        have h := (Finset.mem_filter.mp hp).2.1
        exact one_div_le_one_div_of_le hNc (hNa.trans h)
      calc ∑ p ∈ Pb, (1 / (p : ℝ)) ≤ Pb.card • (1 / (N : ℝ) ^ c) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = (Pb.card : ℝ) * (1 / (N : ℝ) ^ c) := by rw [nsmul_eq_mul]
        _ ≤ cp * (1 / (N : ℝ) ^ c) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = cp / (N : ℝ) ^ c := by ring
    have hS0 : 0 ≤ ∑ q ∈ Q, (1 : ℝ) / q := Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ p ∈ Pb, 1 / (p : ℝ)) * ∑ q ∈ Q, (1 : ℝ) / q
        ≤ cp / (N : ℝ) ^ c * ∑ q ∈ Q, (1 : ℝ) / q := mul_le_mul_of_nonneg_right hsumP hS0
      _ ≤ cp / (N : ℝ) ^ c * (1 + log N) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
  -- second piece
  have hTb : ∑ x ∈ T, f x ≤ cp / (N : ℝ) ^ c * (1 + log N) := by
    rw [hT, Finset.sum_filter, Finset.sum_product]
    have hstep : ∀ p ∈ Q, (∑ q ∈ Q, if (p, q).2 ∈ Qb (p, q).1 then f (p, q) else 0) ≤
        (1 / (p : ℝ)) * (cp / (N : ℝ) ^ c) := by
      intro p _
      rw [← Finset.sum_filter]
      have hcard : ((Q.filter (fun q => (p, q).2 ∈ Qb (p, q).1)).card : ℝ) ≤ cp := by
        have h := bm_card_bad_le N (by omega) Q hQprime (log N) (lo (lev p)) (hi (lev p)) hL
          (fun q => q ∈ Qb p) (fun n _ h => ((Finset.mem_filter.mp h).2.2))
        simpa using h
      have hterm : ∀ q ∈ Q.filter (fun q => (p, q).2 ∈ Qb (p, q).1),
          f (p, q) ≤ (1 / (p : ℝ)) * (1 / (N : ℝ) ^ c) := by
        intro q hq
        have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2).2.1
        simp only [hf]
        rw [← one_div_mul_one_div]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hNc (hNm.trans h))
          (by positivity)
      calc ∑ q ∈ Q.filter (fun q => (p, q).2 ∈ Qb (p, q).1), f (p, q)
          ≤ (Q.filter (fun q => (p, q).2 ∈ Qb (p, q).1)).card •
              ((1 / (p : ℝ)) * (1 / (N : ℝ) ^ c)) := Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((Q.filter (fun q => (p, q).2 ∈ Qb (p, q).1)).card : ℝ) *
              ((1 / (p : ℝ)) * (1 / (N : ℝ) ^ c)) := by rw [nsmul_eq_mul]
        _ ≤ cp * ((1 / (p : ℝ)) * (1 / (N : ℝ) ^ c)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (1 / (p : ℝ)) * (cp / (N : ℝ) ^ c) := by ring
    calc ∑ p ∈ Q, (∑ q ∈ Q, if (p, q).2 ∈ Qb (p, q).1 then f (p, q) else 0)
        ≤ ∑ p ∈ Q, (1 / (p : ℝ)) * (cp / (N : ℝ) ^ c) := Finset.sum_le_sum hstep
      _ = (∑ p ∈ Q, (1 : ℝ) / p) * (cp / (N : ℝ) ^ c) := by rw [Finset.sum_mul]
      _ ≤ (1 + log N) * (cp / (N : ℝ) ^ c) := mul_le_mul_of_nonneg_right hH (by positivity)
      _ = cp / (N : ℝ) ^ c * (1 + log N) := by ring
  -- combine
  have hU : ∑ x ∈ (Pb ×ˢ Q) ∪ T, f x ≤ ∑ x ∈ Pb ×ˢ Q, f x + ∑ x ∈ T, f x := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => hfnn x)
  have hmono : ∑ x ∈ S N \ ptOpenRegion a b lo hi N, f x ≤ ∑ x ∈ (Pb ×ˢ Q) ∪ T, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hfnn x)
  have hcpL : cp ≤ (1 / log 2 + 2) * log N := by
    have : log (N : ℝ) / log 2 = (1 / log 2) * log N := by ring
    rw [hcp]; nlinarith
  have hfin : 2 * (cp / (N : ℝ) ^ c * (1 + log N)) ≤
      4 * (1 / log 2 + 2) * log (N : ℝ) ^ 2 / (N : ℝ) ^ c := by
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hNc]
    have h12 : 0 ≤ 1 / log 2 + 2 := by positivity
    nlinarith
  calc ∑ x ∈ S N \ ptOpenRegion a b lo hi N, 1 / ((x.1 : ℝ) * x.2)
      = ∑ x ∈ S N \ ptOpenRegion a b lo hi N, f x := rfl
    _ ≤ 2 * (cp / (N : ℝ) ^ c * (1 + log N)) := by linarith
    _ ≤ _ := hfin

end LeanLab.ChenDoubleSieve.Task349.SplitSum
