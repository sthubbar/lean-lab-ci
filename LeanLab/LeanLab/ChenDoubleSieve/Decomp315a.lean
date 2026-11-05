import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Wu2008Lemma21Chen
import LeanLab.ChenDoubleSieve.Decomp275j

/-!
Supply split for the weighted sieve leaf of Decomp275b.
Source: https://arxiv.org/pdf/0705.1652, pages 35 to 37, equations 9.7 to 9.9.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu41 (S)

/-- Separate the primes dividing N from the prime difference sequence.
Source: page 33 definition of A and page 34 coprimality reduction. -/
theorem primeSequence_decomposition (N : ℕ) :
    primeSequence N = Wu08.Achen N ∪ N.primeFactors.image (fun p => N - p) := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
    obtain ⟨hpN, hp⟩ := mem_filter.mp hp
    have hle : p ≤ N := by have := mem_range.mp hpN; omega
    by_cases hd : p ∣ N
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, ?_⟩, rfl⟩
      have := hp.pos
      omega
    · apply mem_union_left
      apply mem_image.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_range.mpr ?_, hp, hd⟩, rfl⟩
      have hne : p ≠ N := by intro he; apply hd; rw [he]
      omega
  · intro ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      obtain ⟨hpN, hp, _⟩ := mem_filter.mp hp
      apply mem_image.mpr
      exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hpN; omega), hp⟩, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      obtain ⟨hprime, hd, hN⟩ := Nat.mem_primeFactors.mp hp
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd
      apply mem_image.mpr
      exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hprime⟩, rfl⟩

/-- At most one omitted sequence element comes from each prime divisor of N.
Source: page 34 removal of elements not coprime to N. -/
theorem primeSequence_bad_card (N : ℕ) :
    (primeSequence N \ Wu08.Achen N).card ≤ N.primeFactors.card := by
  apply le_trans (card_le_card (show primeSequence N \ Wu08.Achen N ⊆
    N.primeFactors.image (fun p => N - p) from ?_)) card_image_le
  intro a ha
  obtain ⟨ha, hnot⟩ := mem_sdiff.mp ha
  rw [primeSequence_decomposition] at ha
  exact (mem_union.mp ha).resolve_left hnot

/-- Distinct prime factors have a logarithmic cardinal bound.
Source: page 34 coprimality error, derived elementary counting helper. -/
theorem primeFactors_card_log {N : ℕ} (hN : 0 < N) :
    (N.primeFactors.card : ℝ) ≤ log (N : ℝ) / log 2 := by
  have hpow : 2 ^ N.primeFactors.card ≤ N := by
    calc
      2 ^ N.primeFactors.card = ∏ _ ∈ N.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ N.primeFactors, p :=
        Finset.prod_le_prod (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
      _ ≤ N := Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  have hpowR : (2 : ℝ) ^ N.primeFactors.card ≤ N := by exact_mod_cast hpow
  have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

/-- The omitted sequence has logarithmic size.
Source: page 34 coprimality reduction, derived elementary counting helper. -/
theorem primeSequence_bad_log {N : ℕ} (hN : 0 < N) :
    ((primeSequence N \ Wu08.Achen N).card : ℝ) ≤ log (N : ℝ) / log 2 := by
  have hcard : ((primeSequence N \ Wu08.Achen N).card : ℝ) ≤ N.primeFactors.card :=
    Nat.cast_le.mpr (primeSequence_bad_card N)
  exact hcard.trans (primeFactors_card_log hN)

/-- A single sifted count changes by at most the number of omitted elements.
Source: page 34 coprimality reduction, elementary counting helper. -/
theorem sieve_count_transfer (A B : Finset ℕ) (e D : ℕ) (y : ℝ) :
    S A e D y ≤ S B e D y + (A \ B).card := by
  let P := fun a => e ∣ a ∧ Wu41.Sifted D y a
  have hcard := card_le_card_sdiff_add_card (s := A.filter P) (t := B.filter P)
  have hsub : A.filter P \ B.filter P ⊆ A \ B := by
    intro a ha
    obtain ⟨ha, hnot⟩ := mem_sdiff.mp ha
    obtain ⟨haA, hPa⟩ := mem_filter.mp ha
    exact mem_sdiff.mpr ⟨haA, fun haB => hnot (mem_filter.mpr ⟨haB, hPa⟩)⟩
  have hbound := card_le_card hsub
  change (A.filter P).card ≤ (B.filter P).card + (A \ B).card
  omega

/-- A single prime sequence sieve count has a controlled exceptional contribution.
Source: page 34 coprimality reduction, elementary counting helper. -/
theorem primeSequence_sieve_transfer (N e D : ℕ) (y : ℝ) :
    S (primeSequence N) e D y ≤ S (Wu08.Achen N) e D y + N.primeFactors.card := by
  exact (sieve_count_transfer (primeSequence N) (Wu08.Achen N) e D y).trans
    (Nat.add_le_add_left (primeSequence_bad_card N) _)

/-- The sequence reduction has a nonempty exceptional set at N equal four.
Source: page 33 definition of A and page 34 coprimality reduction. -/
theorem primeSequence_reduction_instance :
    primeSequence 4 = {1, 2} ∧ Wu08.Achen 4 = {1} ∧
      (primeSequence 4 \ Wu08.Achen 4).card = 1 := by
  norm_num [primeSequence, Wu08.Achen, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton] <;> decide

/-- Triples of primes below N, each coprime to N, in a specified domain. -/
def primeTriples (N : ℕ) (C : ℕ → ℕ → ℕ → Prop) : Finset (ℕ × ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N ×ˢ range N |
    q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.Prime ∧
    q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.Coprime N ∧ C q.1 q.2.1 q.2.2}

/-- A prime triple dividing a positive integer lies in its prime factor cube.
Source: page 37 triple remainder terms, derived counting helper. -/
theorem triple_divisor_card (N a : ℕ) (ha : 0 < a) (C : ℕ → ℕ → ℕ → Prop) :
    #{q ∈ primeTriples N C | q.1 * q.2.1 * q.2.2 ∣ a} ≤ a.primeFactors.card ^ 3 := by
  have hsub : {q ∈ primeTriples N C | q.1 * q.2.1 * q.2.2 ∣ a} ⊆
      a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors := by
    intro q hq
    obtain ⟨hq, hd⟩ := mem_filter.mp hq
    obtain ⟨_, hp, hq', hr, _⟩ := mem_filter.mp hq
    have hd12 : q.1 * q.2.1 ∣ a := (dvd_mul_right _ _).trans hd
    have hd1 : q.1 ∣ a := (dvd_mul_right _ _).trans hd12
    have hd2 : q.2.1 ∣ a := (dvd_mul_left _ _).trans hd12
    have hd3 : q.2.2 ∣ a := (dvd_mul_left _ _).trans hd
    exact mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hd1, ha.ne'⟩,
      mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq', hd2, ha.ne'⟩,
        Nat.mem_primeFactors.mpr ⟨hr, hd3, ha.ne'⟩⟩⟩
  calc
    _ ≤ (a.primeFactors ×ˢ a.primeFactors ×ˢ a.primeFactors).card := card_le_card hsub
    _ = _ := by simp only [card_product]; ring

/-- Bound a triple sieve sum by a uniform prime factor cardinal bound.
Source: page 37 triple remainder terms, derived finite summation helper. -/
theorem triple_sum_bound (A : Finset ℕ) (N K : ℕ) (C : ℕ → ℕ → ℕ → Prop)
    (M : ℕ × ℕ × ℕ → ℕ) (y : ℕ × ℕ × ℕ → ℝ)
    (hA : ∀ a ∈ A, 0 < a ∧ a.primeFactors.card ≤ K) :
    (∑ q ∈ primeTriples N C, S A (q.1 * q.2.1 * q.2.2) (M q) (y q)) ≤
      A.card * K ^ 3 := by
  rw [Wu08Sum.swap1]
  calc
    _ ≤ ∑ a ∈ A, K ^ 3 := by
      apply sum_le_sum
      intro a ha
      have hsub : {q ∈ primeTriples N C |
          q.1 * q.2.1 * q.2.2 ∣ a ∧ Wu41.Sifted (M q) (y q) a} ⊆
          {q ∈ primeTriples N C | q.1 * q.2.1 * q.2.2 ∣ a} := by
        intro q hq
        obtain ⟨hq, hd, _⟩ := mem_filter.mp hq
        exact mem_filter.mpr ⟨hq, hd⟩
      exact (card_le_card hsub).trans
        ((triple_divisor_card N a (hA a ha).1 C).trans
          (pow_le_pow_left' (hA a ha).2 3))
    _ = _ := by simp

/-- The prime difference sequence is positive and below a composite even N.
Source: page 33 definition of A. -/
theorem primeSequence_bounds {N : ℕ} (hEven : Even N) (hN : 4 ≤ N) :
    ∀ a ∈ primeSequence N, 0 < a ∧ a < N := by
  rcases hEven with ⟨k, hk⟩
  intro a ha
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨hpN, hp⟩ := mem_filter.mp hp
  have hp_le : p ≤ N := by have := mem_range.mp hpN; omega
  have hp_lt : p < N := by
    by_contra hnot
    have heq : p = N := by omega
    rw [heq] at hp
    rcases hp.eq_two_or_odd with htwo | hodd <;> omega
  exact ⟨Nat.sub_pos_of_lt hp_lt, Nat.sub_lt (by omega) hp.pos⟩

/-- Triple sums on the exceptional sequence have at most a logarithmic fourth power.
Source: page 34 coprimality reduction and page 37 triple remainders. -/
theorem exceptional_triple_sum (N : ℕ) (hEven : Even N) (hN : 4 ≤ N)
    (C : ℕ → ℕ → ℕ → Prop) (M : ℕ × ℕ × ℕ → ℕ) (y : ℕ × ℕ × ℕ → ℝ) :
    (∑ q ∈ primeTriples N C,
      S (primeSequence N \ Wu08.Achen N) (q.1 * q.2.1 * q.2.2) (M q) (y q)) ≤
      ⌈log (N : ℝ) / log 2⌉₊ ^ 4 := by
  let K : ℕ := ⌈log (N : ℝ) / log 2⌉₊
  have hNpos : 0 < N := by omega
  have hK : log (N : ℝ) / log 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hNK : N.primeFactors.card ≤ K := by
    exact_mod_cast (primeFactors_card_log hNpos).trans hK
  have hA : ∀ a ∈ primeSequence N \ Wu08.Achen N,
      0 < a ∧ a.primeFactors.card ≤ K := by
    intro a ha
    have ha' := primeSequence_bounds hEven hN a (mem_sdiff.mp ha).1
    refine ⟨ha'.1, ?_⟩
    have halog := primeFactors_card_log ha'.1
    have hlog := Real.log_le_log (by exact_mod_cast ha'.1 : (0 : ℝ) < a)
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ N)
    have hle : (a.primeFactors.card : ℝ) ≤ (K : ℝ) := halog.trans
      ((div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans hK)
    exact_mod_cast hle
  have hcount : (primeSequence N \ Wu08.Achen N).card ≤ K :=
    (primeSequence_bad_card N).trans hNK
  calc
    _ ≤ (primeSequence N \ Wu08.Achen N).card * K ^ 3 := triple_sum_bound _ N K C M y hA
    _ ≤ K * K ^ 3 := Nat.mul_le_mul_right _ hcount
    _ = K ^ 4 := by ring

/-- Transfer one sieve count while retaining the actual exceptional sieve count.
Source: page 34 coprimality reduction, derived counting helper. -/
theorem sieve_transfer_by_exception (A B : Finset ℕ) (e D : ℕ) (y : ℝ) :
    S A e D y ≤ S B e D y + S (A \ B) e D y := by
  let P := fun a => e ∣ a ∧ Wu41.Sifted D y a
  have hcard := card_le_card_sdiff_add_card (s := A.filter P) (t := B.filter P)
  have he : A.filter P \ B.filter P = (A \ B).filter P := by
    ext a
    simp only [mem_sdiff, mem_filter]
    tauto
  rw [he] at hcard
  change (A.filter P).card ≤ (B.filter P).card + ((A \ B).filter P).card
  omega

/-- Transfer a triple sum with its true exceptional multiplicities.
Source: page 34 coprimality reduction and page 37 triple terms. -/
theorem triple_sum_transfer (A B : Finset ℕ) (N : ℕ) (C : ℕ → ℕ → ℕ → Prop)
    (M : ℕ × ℕ × ℕ → ℕ) (y : ℕ × ℕ × ℕ → ℝ) :
    (∑ q ∈ primeTriples N C, S A (q.1 * q.2.1 * q.2.2) (M q) (y q)) ≤
      (∑ q ∈ primeTriples N C, S B (q.1 * q.2.1 * q.2.2) (M q) (y q)) +
      ∑ q ∈ primeTriples N C, S (A \ B) (q.1 * q.2.1 * q.2.2) (M q) (y q) := by
  simpa only [sum_add_distrib] using
    (sum_le_sum (fun q (_ : q ∈ primeTriples N C) =>
      sieve_transfer_by_exception A B (q.1 * q.2.1 * q.2.2) (M q) (y q)))

/-- The full prime sequence triple sum differs from the coprime sequence by a log power.
Source: page 34 coprimality reduction and page 37 triple terms. -/
theorem primeSequence_triple_transfer (N : ℕ) (hEven : Even N) (hN : 4 ≤ N)
    (C : ℕ → ℕ → ℕ → Prop) (M : ℕ × ℕ × ℕ → ℕ) (y : ℕ × ℕ × ℕ → ℝ) :
    (∑ q ∈ primeTriples N C, S (primeSequence N) (q.1 * q.2.1 * q.2.2) (M q) (y q)) ≤
      (∑ q ∈ primeTriples N C, S (Wu08.Achen N) (q.1 * q.2.1 * q.2.2) (M q) (y q)) +
      ⌈log (N : ℝ) / log 2⌉₊ ^ 4 := by
  exact (triple_sum_transfer (primeSequence N) (Wu08.Achen N) N C M y).trans
    (Nat.add_le_add_left (exceptional_triple_sum N hEven hN C M y) _)

/-- A fourth logarithmic ceiling power is eventually below the sieve power remainder.
Source: page 34 coprimality error and page 37 power remainder, derived helper. -/
theorem log_ceiling_power_absorbed : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 4 ≤ (N : ℝ) ^ (11 / 12 : ℝ) := by
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlo : (fun x : ℝ => log x ^ 4) =o[Filter.atTop]
      (fun x : ℝ => x ^ (11 / 12 : ℝ)) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (s := 11 / 12) (by norm_num))
  let ε : ℝ := log (2 : ℝ) ^ 4 / 16
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hnat : ∀ᶠ N : ℕ in Filter.atTop,
      ‖log (N : ℝ) ^ 4‖ ≤ ε * ‖(N : ℝ) ^ (11 / 12 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually (hlo.bound hε)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max M 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_right M 2).trans hN
  have hlog : log (2 : ℝ) ≤ log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have hquot : 1 ≤ log (N : ℝ) / log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlog)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ log (N : ℝ) / log 2 by linarith)
  have hceil : (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ≤ 2 * (log (N : ℝ) / log 2) := by
    linarith
  have hp : (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 4 ≤
      (2 * (log (N : ℝ) / log 2)) ^ 4 := by gcongr
  have hpow2 : 0 < log (2 : ℝ) ^ 4 := pow_pos hlog2 _
  have hid : (2 * (log (N : ℝ) / log 2)) ^ 4 =
      16 * log (N : ℝ) ^ 4 / log (2 : ℝ) ^ 4 := by ring
  rw [hid] at hp
  have hmul := (le_div_iff₀ hpow2).mp hp
  have hraw := hM N ((le_max_left M 2).trans hN)
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] at hraw
  dsimp only [ε] at hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 16)
  have halg : 16 * (log (2 : ℝ) ^ 4 / 16 * (N : ℝ) ^ (11 / 12 : ℝ)) =
      (N : ℝ) ^ (11 / 12 : ℝ) * log (2 : ℝ) ^ 4 := by ring
  rw [halg] at hscaled
  exact (mul_le_mul_iff_left₀ hpow2).mp (hmul.trans hscaled)

/-- The exceptional triple contribution fits the exact power remainder uniformly.
Source: page 34 coprimality reduction and page 37 power remainder. -/
theorem exceptional_triple_power : ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
    ∀ (C : ℕ → ℕ → ℕ → Prop) (M : ℕ × ℕ × ℕ → ℕ) (y : ℕ × ℕ × ℕ → ℝ),
      ((∑ q ∈ primeTriples N C,
        S (primeSequence N \ Wu08.Achen N) (q.1 * q.2.1 * q.2.2) (M q) (y q)) : ℝ) ≤
        (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨K, hK⟩ := log_ceiling_power_absorbed
  refine ⟨max K 4, ?_⟩
  intro N hEven hN C M y
  have hN4 : 4 ≤ N := (le_max_right K 4).trans hN
  have hcard : ((∑ q ∈ primeTriples N C,
      S (primeSequence N \ Wu08.Achen N) (q.1 * q.2.1 * q.2.2) (M q) (y q)) : ℝ) ≤
      (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 4 := by
    exact_mod_cast exceptional_triple_sum N hEven hN4 C M y
  exact hcard.trans (hK N ((le_max_left K 4).trans hN))

/-- Reassociate prime triples to the existing S4 sum with the same forced prime modulus.
Source: page 33 definition of S4 and page 37 equation 9.8. -/
theorem triple_sum_eq_S4 (A : Finset ℕ) (N : ℕ) (K Sg : ℝ) (hSg : Sg ≤ N) :
    (∑ q ∈ primeTriples N (fun p q r => K ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < Sg),
      S A (q.1 * q.2.1 * q.2.2) (N * q.1) q.2.1) = Wu08.S₄ A N K Sg := by
  unfold Wu08.S₄
  refine sum_bij (fun q _ => ((q.1, q.2.1), q.2.2)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro q hq
    simp only [primeTriples, mem_filter, mem_product] at hq
    obtain ⟨_, hp, hq', hr, hpc, hqc, hrc, hKp, hpq, hqr, hrS⟩ := hq
    have hpqR : (q.1 : ℝ) < q.2.1 := by exact_mod_cast hpq
    have hqrR : (q.2.1 : ℝ) < q.2.2 := by exact_mod_cast hqr
    simp only [Wu08.triples, mem_filter, mem_product]
    exact ⟨⟨⟨Wu41.mem_PS.mpr ⟨hp, hKp, hpqR.trans (hqrR.trans hrS), hpc⟩,
      Wu41.mem_PS.mpr ⟨hq', hKp.trans hpqR.le, hqrR.trans hrS, hqc⟩⟩,
      Wu41.mem_PS.mpr ⟨hr, (hKp.trans hpqR.le).trans hqrR.le, hrS, hrc⟩⟩, hpq, hqr⟩
  · rintro ⟨p, q, r⟩ _ ⟨p', q', r'⟩ _ he
    simpa only [Prod.mk.injEq, and_assoc] using he
  · rintro ⟨⟨p, q⟩, r⟩ ht
    simp only [Wu08.triples, mem_filter, mem_product] at ht
    obtain ⟨⟨⟨hp, hq⟩, hr⟩, hpq, hqr⟩ := ht
    obtain ⟨hpp, hKp, hpS, hpc⟩ := Wu41.mem_PS.mp hp
    obtain ⟨hqp, _, hqS, hqc⟩ := Wu41.mem_PS.mp hq
    obtain ⟨hrp, _, hrS, hrc⟩ := Wu41.mem_PS.mp hr
    refine ⟨(p, q, r), ?_, rfl⟩
    simp only [primeTriples, mem_filter, mem_product, mem_range]
    refine ⟨⟨?_, ?_, ?_⟩, hpp, hqp, hrp, hpc, hqc, hrc, hKp, hpq, hqr, hrS⟩
    · exact_mod_cast hpS.trans_le hSg
    · exact_mod_cast hqS.trans_le hSg
    · exact_mod_cast hrS.trans_le hSg

/-- The real square root pair cutoff equals the integer product cutoff.
Source: page 33 S2 and S3 and page 35 Upsilon 7 and 9. -/
theorem pair_sqrt_iff (N p q : ℕ) (hp : 0 < p) :
    ((q : ℝ) < Real.sqrt ((N : ℝ) / p)) ↔ p * q ^ 2 < N := by
  rw [Real.lt_sqrt (Nat.cast_nonneg q),
    lt_div_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp), mul_comm]
  exact_mod_cast (Iff.rfl : p * q ^ 2 < N ↔ p * q ^ 2 < N)

/-- The upper pair domain in Lemma 9.1 agrees with the square root domain.
Source: page 33 S2 and page 35 Upsilon 7. -/
theorem pairs_eq_upper (N : ℕ) (Sg : ℝ) :
    Wu08.pairs N Sg (N : ℝ) Sg =
      Wu08Sum.P2 N (fun p q => Sg ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) := by
  ext ⟨p, q⟩
  simp only [Wu08.pairs, Wu08Sum.P2, mem_filter, mem_product]
  constructor
  · rintro ⟨hNP, hpp, hqp, hpc, hqc, hSp, _, _, hpq, hprod⟩
    exact ⟨hNP, hpp, hqp, hpc, hqc, hSp, hpq, (pair_sqrt_iff N p q hpp.pos).mpr hprod⟩
  · rintro ⟨hNP, hpp, hqp, hpc, hqc, hSp, hpq, hsqrt⟩
    have hpN : (p : ℝ) < N := by exact_mod_cast mem_range.mp hNP.1
    have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
    exact ⟨hNP, hpp, hqp, hpc, hqc, hSp, hpN, hSp.trans hpqR.le, hpq,
      (pair_sqrt_iff N p q hpp.pos).mp hsqrt⟩

/-- The crossing pair domain agrees with the square root domain.
Source: page 33 S3 and page 35 Upsilon 9. -/
theorem pairs_eq_cross (N : ℕ) (K Sg : ℝ) :
    Wu08.pairs N K Sg Sg =
      Wu08Sum.P2 N (fun p q => K ≤ p ∧ (p : ℝ) < Sg ∧ Sg ≤ q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) := by
  ext ⟨p, q⟩
  simp only [Wu08.pairs, Wu08Sum.P2, mem_filter, mem_product]
  constructor
  · rintro ⟨hNP, hpp, hqp, hpc, hqc, hKp, hpS, hSq, _, hprod⟩
    exact ⟨hNP, hpp, hqp, hpc, hqc, hKp, hpS, hSq,
      (pair_sqrt_iff N p q hpp.pos).mpr hprod⟩
  · rintro ⟨hNP, hpp, hqp, hpc, hqc, hKp, hpS, hSq, hsqrt⟩
    have hpq : p < q := by exact_mod_cast hpS.trans_le hSq
    exact ⟨hNP, hpp, hqp, hpc, hqc, hKp, hpS, hSq, hpq,
      (pair_sqrt_iff N p q hpp.pos).mp hsqrt⟩

/-- Sifting over the coprime sequence cannot increase a count.
Source: page 34 coprimality reduction. -/
theorem Achen_sieve_le (N e D : ℕ) (y : ℝ) :
    S (Wu08.Achen N) e D y ≤ S (primeSequence N) e D y := by
  apply card_le_card
  apply filter_subset_filter
  intro a ha
  rw [primeSequence_decomposition]
  exact mem_union_left _ ha

/-- The number of exceptional primes also fits the sieve power remainder.
Source: page 34 coprimality error, derived asymptotic helper. -/
theorem primeFactors_card_absorbed : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N.primeFactors.card : ℝ) ≤ (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨K, hK⟩ := log_ceiling_power_absorbed
  refine ⟨max K 1, ?_⟩
  intro N hN
  have hNp : 0 < N := by omega
  have hceil : (N.primeFactors.card : ℝ) ≤ (⌈log (N : ℝ) / log 2⌉₊ : ℝ) :=
    (primeFactors_card_log hNp).trans (Nat.le_ceil _)
  have hpow : (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ≤
      (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 4 := by
    exact_mod_cast Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) ⌈log (N : ℝ) / log 2⌉₊
  exact (hceil.trans hpow).trans (hK N ((le_max_left K 1).trans hN))

/-- The explicit square factor remainder has the required power at kappa one.
Source: page 34 Lemma 9.1 error and page 37 equation 9.8. -/
theorem lemma21_remainder_power (N : ℕ) (hN : 4096 ≤ N) :
    2 * ((N : ℝ) / ((N : ℝ) ^ kappa1 - 1) + Real.sqrt N + 1) ≤
      8 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hbase : (4096 : ℝ) ^ kappa1 = 2 := by
    norm_num [kappa1]
  have hx : (2 : ℝ) ≤ (N : ℝ) ^ kappa1 := by
    rw [← hbase]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num [kappa1])
  have hprod : (N : ℝ) ^ kappa1 * (N : ℝ) ^ (11 / 12 : ℝ) = N := by
    rw [← Real.rpow_add hNp]
    norm_num [kappa1]
  have hp := Real.rpow_nonneg hNp.le (11 / 12 : ℝ)
  have hm := mul_le_mul_of_nonneg_right hx hp
  have hmain : (N : ℝ) / ((N : ℝ) ^ kappa1 - 1) ≤
      2 * (N : ℝ) ^ (11 / 12 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < (N : ℝ) ^ kappa1 - 1)).mpr
    nlinarith only [hprod, hm]
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ (11 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (11 / 12 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  linarith

/-- Excluding a forced prime has no effect at levels at or below that prime.
Source: page 37 Delta one, elementary modulus identification. -/
theorem sifted_modulus_prime {N p a : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ≤ p) :
    Wu41.Sifted (N * p) y a ↔ Wu41.Sifted N y a := by
  constructor
  · intro hs q hq hqy hqN
    apply hs q hq hqy
    intro hd
    rcases (Nat.Prime.dvd_mul hq).mp hd with hdN | hdp
    · exact hqN hdN
    · have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdp
      have hpy : (p : ℝ) < y := by simpa only [heq] using hqy
      linarith
  · intro hs q hq hqy hqNp
    exact hs q hq hqy (fun hd => hqNp (dvd_mul_of_dvd_left hd p))

/-- The corresponding sifted counts agree below the forced prime.
Source: page 37 Delta one, elementary modulus identification. -/
theorem sieve_modulus_prime (A : Finset ℕ) (e N p : ℕ) (hp : p.Prime)
    (y : ℝ) (hy : y ≤ p) : S A e (N * p) y = S A e N y := by
  unfold S
  congr 1
  ext a
  simp only [mem_filter, sifted_modulus_prime hp hy]

/-- Failure of higher sifting has a least newly encountered prime divisor.
Source: pages 36 and 37 Buchstab decompositions. -/
theorem least_sifting_prime_exists {N a : ℕ} {w z : ℝ}
    (hw : Wu41.Sifted N w a) (hz : ¬ Wu41.Sifted N z a) :
    ∃ p : ℕ, p ∈ Wu41.PS N w z ∧ p ∣ a ∧ Wu41.Sifted N p a := by
  have hbad : ∃ q : ℕ, q.Prime ∧ (q : ℝ) < z ∧ ¬ q ∣ N ∧ q ∣ a := by
    by_contra h
    apply hz
    intro q hq hqz hqN hqa
    exact h ⟨q, hq, hqz, hqN, hqa⟩
  obtain ⟨q, hq, hqz, hqN, hqa⟩ := hbad
  have hwq : w ≤ (q : ℝ) := by
    by_contra h
    exact hw q hq (lt_of_not_ge h) hqN hqa
  let P := (Wu41.PS N w z).filter (fun p => p ∣ a)
  have hP : P.Nonempty := ⟨q, mem_filter.mpr
    ⟨Wu41.mem_PS.mpr ⟨hq, hwq, hqz, (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN⟩, hqa⟩⟩
  let p := P.min' hP
  have hpP : p ∈ P := min'_mem P hP
  obtain ⟨hpPS, hpa⟩ := mem_filter.mp hpP
  obtain ⟨hp, hwp, hpz, hpc⟩ := Wu41.mem_PS.mp hpPS
  refine ⟨p, hpPS, hpa, ?_⟩
  intro r hr hrp hrN hra
  have hwr : w ≤ (r : ℝ) := by
    by_contra h
    exact hw r hr (lt_of_not_ge h) hrN hra
  have hrP : r ∈ P := mem_filter.mpr ⟨Wu41.mem_PS.mpr
    ⟨hr, hwr, hrp.trans hpz, (Nat.Prime.coprime_iff_not_dvd hr).mpr hrN⟩, hra⟩
  have hmin : p ≤ r := min'_le P r hrP
  have hrpNat : r < p := by exact_mod_cast hrp
  omega

/-- The newly encountered prime in the Buchstab partition is unique.
Source: pages 36 and 37 Buchstab decompositions. -/
theorem least_sifting_prime_unique {N a p q : ℕ} {w z : ℝ}
    (hp : p ∈ Wu41.PS N w z) (hq : q ∈ Wu41.PS N w z)
    (hpa : p ∣ a) (hqa : q ∣ a)
    (hps : Wu41.Sifted N p a) (hqs : Wu41.Sifted N q a) : p = q := by
  have hpp := Wu41.mem_PS.mp hp
  have hqp := Wu41.mem_PS.mp hq
  rcases lt_trichotomy p q with hpq | heq | hqp'
  · exact False.elim (hqs p hpp.1 (by exact_mod_cast hpq)
      ((Nat.Prime.coprime_iff_not_dvd hpp.1).mp hpp.2.2.2) hpa)
  · exact heq
  · exact False.elim (hps q hqp.1 (by exact_mod_cast hqp')
      ((Nat.Prime.coprime_iff_not_dvd hqp.1).mp hqp.2.2.2) hqa)

/-- Pointwise Buchstab partition by the unique first prime in a sifting interval.
Source: pages 36 and 37 Buchstab identities. -/
theorem sifting_partition_card (N a : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    (if Wu41.Sifted N w a then (1 : ℕ) else 0) =
      (if Wu41.Sifted N z a then 1 else 0) +
      #{p ∈ Wu41.PS N w z | p ∣ a ∧ Wu41.Sifted N p a} := by
  let P := {p ∈ Wu41.PS N w z | p ∣ a ∧ Wu41.Sifted N p a}
  change (if Wu41.Sifted N w a then (1 : ℕ) else 0) =
    (if Wu41.Sifted N z a then 1 else 0) + P.card
  have hle : P.card ≤ 1 := by
    rw [card_le_one]
    intro p hp q hq
    obtain ⟨hpPS, hpa, hps⟩ := mem_filter.mp hp
    obtain ⟨hqPS, hqa, hqs⟩ := mem_filter.mp hq
    exact least_sifting_prime_unique hpPS hqPS hpa hqa hps hqs
  by_cases hw : Wu41.Sifted N w a
  · by_cases hz : Wu41.Sifted N z a
    · have hzero : P.card = 0 := by
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpPS, hpa, _⟩ := mem_filter.mp hp
        obtain ⟨hpp, _, hpz, hpc⟩ := Wu41.mem_PS.mp hpPS
        exact hz p hpp hpz ((Nat.Prime.coprime_iff_not_dvd hpp).mp hpc) hpa
      simp [hw, hz, hzero]
    · obtain ⟨p, hp, hpa, hps⟩ := least_sifting_prime_exists hw hz
      have hne : P.Nonempty := ⟨p, mem_filter.mpr ⟨hp, hpa, hps⟩⟩
      have hone : P.card = 1 := by have := card_pos.mpr hne; omega
      simp [hw, hz, hone]
  · have hz : ¬ Wu41.Sifted N z a := fun hz => hw (Wu41.sifted_mono hwz hz)
    have hzero : P.card = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpPS, _, hps⟩ := mem_filter.mp hp
      exact hw (Wu41.sifted_mono (Wu41.mem_PS.mp hpPS).2.1 hps)
    simp [hw, hz, hzero]

/-- The base finite Buchstab identity, with no asymptotic or distribution input.
Source: page 36 first Buchstab expansion and page 37 cancellation. -/
theorem buchstab_base (A : Finset ℕ) (N : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    S A 1 N w = S A 1 N z + ∑ p ∈ Wu41.PS N w z, S A p N p := by
  rw [Wu08Sum.swap1]
  simp only [Wu41.S_eq_sum, one_dvd, true_and]
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun a _ => sifting_partition_card N a hwz)

/-- Filtering the sequence by a divisor equals putting that divisor in the sifted count.
Source: pages 35 to 37 subscripts A with a divisor. -/
theorem sieve_filter_divisor (A : Finset ℕ) (e N : ℕ) (y : ℝ) :
    S (A.filter (fun a => e ∣ a)) 1 N y = S A e N y := by
  unfold S
  congr 1
  ext a
  simp only [mem_filter, one_dvd, true_and]
  tauto

/-- The finite divisor Buchstab identity when new primes are coprime to the divisor.
Source: pages 36 and 37 Buchstab expansions. -/
theorem buchstab_divisor (A : Finset ℕ) (e N : ℕ) {w z : ℝ} (hwz : w ≤ z)
    (hc : ∀ p ∈ Wu41.PS N w z, p.Coprime e) :
    S A e N w = S A e N z + ∑ p ∈ Wu41.PS N w z, S A (e * p) N p := by
  have hbase := buchstab_base (A.filter (fun a => e ∣ a)) N hwz
  rw [sieve_filter_divisor, sieve_filter_divisor] at hbase
  rw [hbase]
  congr 1
  apply sum_congr rfl
  intro p hp
  unfold S
  congr 1
  ext a
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨ha, hea⟩, hpa, hs⟩
    exact ⟨ha, Nat.Coprime.mul_dvd_of_dvd_of_dvd (hc p hp).symm hea hpa, hs⟩
  · rintro ⟨ha, hd, hs⟩
    exact ⟨⟨ha, (dvd_mul_right e p).trans hd⟩, (dvd_mul_left p e).trans hd, hs⟩

/-- The literal third Delta modulus sifts out its forced second prime.
Source: page 37 third Delta one term, notation check using the existing literal_zero. -/
theorem literal_delta_third_zero (A : Finset ℕ) (N p q r : ℕ)
    (hq : q.Prime) (hqr : q < r) (hqc : q.Coprime (N * p)) :
    S A (p * q * r) (N * p) r = 0 := by
  have hnot : ¬ q ∣ 1 * (N * p) := by
    simpa only [one_mul] using (hq.coprime_iff_not_dvd).mp hqc
  have hd : q ∣ p * q * r := dvd_mul_of_dvd_left (dvd_mul_left q p) r
  simpa only [one_mul] using Wu42.literal_zero A 1 (N * p) (p * q * r) hq hqr hnot hd

/-- A nonzero finite instance distinguishes the two third Delta modulus readings.
Source: page 37 third Delta one term, notation check. -/
theorem delta_modulus_instance :
    S {231} 231 3000 11 = 0 ∧ S {231} 231 21000 11 = 1 := by
  constructor
  · have h := literal_delta_third_zero {231} 1000 3 7 11
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · have hs : Wu41.Sifted 21000 11 231 := by
      intro q hq hq11 hqD
      have hqsmall : q < 11 := by exact_mod_cast hq11
      interval_cases q <;> norm_num at *
    have he : ∀ a ∈ ({231} : Finset ℕ), 231 ∣ a ∧ Wu41.Sifted 21000 11 a := by
      intro a ha
      have ha' : a = 231 := mem_singleton.mp ha
      subst a
      exact ⟨dvd_refl _, hs⟩
    unfold S
    rw [filter_eq_self.mpr he]
    exact card_singleton _

/-- The three sums subtracted in Delta one on page 37, followed by S4.
Every forced prime below the sifting level is excluded from the modulus.
Thus coordinate two excludes the first two primes and S4 excludes the first. -/
def tripleTerms (N : ℕ) : Fin 4 → ℝ :=
  let A := primeSequence N
  let y := fun k : ℝ => (N : ℝ) ^ k
  ![(∑ q ∈ primeTriples N (fun p q r => y kappa1 ≤ p ∧ p < q ∧ q < r ∧
      (r : ℝ) < y kappa2), S A (q.1 * q.2.1 * q.2.2) N q.1 : ℕ),
    (∑ q ∈ primeTriples N (fun p q r => y kappa1 ≤ p ∧ p < q ∧
      (q : ℝ) < y kappa2 ∧ y kappa2 ≤ r ∧
      (r : ℝ) < y (1 / 2 - 2 * kappa1) / q),
      S A (q.1 * q.2.1 * q.2.2) N q.1 : ℕ),
    (∑ q ∈ primeTriples N (fun p q r => y kappa2 ≤ p ∧ (p : ℝ) < y sigma2 ∧
      y sigma2 ≤ q ∧ q < r ∧ (r : ℝ) < y sigma1),
      S A (q.1 * q.2.1 * q.2.2) (N * q.1 * q.2.1) q.2.2 : ℕ),
    (∑ q ∈ primeTriples N (fun p q r => y kappa1 ≤ p ∧ p < q ∧ q < r ∧
      (r : ℝ) < y sigma1), S A (q.1 * q.2.1 * q.2.2) (N * q.1) q.2.1 : ℕ)]

/-- Delta one is the negative of the first three triple sums. -/
def deltaOne (N : ℕ) : ℝ := -tripleTerms N 0 - tripleTerms N 1 - tripleTerms N 2

/-- Every triple coefficient is a nonnegative count.
Source: page 37 definitions of Delta one and S4. -/
theorem tripleTerms_nonneg (N : ℕ) (i : Fin 4) : 0 ≤ tripleTerms N i := by
  fin_cases i <;> exact Nat.cast_nonneg _

/-- Delta one is nonpositive before the cancellation with S4.
Source: page 37 definition of Delta one. -/
theorem deltaOne_nonpos (N : ℕ) : deltaOne N ≤ 0 := by
  have h0 := tripleTerms_nonneg N 0
  have h1 := tripleTerms_nonneg N 1
  have h2 := tripleTerms_nonneg N 2
  dsimp only [deltaOne]
  linarith

/-- A nonempty instance of the prime triple indexing set.
Source: page 37 triple sum domains, with a constant domain predicate. -/
theorem primeTriples_instance : (3, 7, 11) ∈ primeTriples 1000 (fun _ _ _ => True) := by
  norm_num [primeTriples]

/-- LEAF. Wu 2004 page 37 equation 9.7.
The first half retains Delta one and discards only Upsilon 6, 11 and 12. -/
theorem first_half : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 page 37 equation 9.8.
The second half is Lemma 9.1 at kappa one and sigma one, retaining S4. -/
theorem second_half : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 2 - 2 * sieveTerms N 6 -
        sieveTerms N 8 + tripleTerms N 3 ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨Mc, hc⟩ := primeFactors_card_absorbed
  obtain ⟨Mt, ht⟩ := exceptional_triple_power
  refine ⟨11, by norm_num, max 4096 (max Mc Mt), ?_⟩
  intro N hEven hN
  have hN4096 : 4096 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  let K : ℝ := (N : ℝ) ^ kappa1
  let Sg : ℝ := (N : ℝ) ^ sigma1
  have hK : 1 < K := Real.one_lt_rpow hNgt (by norm_num [kappa1])
  have hKS : K ≤ Sg :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, sigma1])
  have hSN : Sg ≤ (N : ℝ) := by
    dsimp only [Sg]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show sigma1 ≤ 1 by norm_num [sigma1])
  have hChen := Wu08.lemma21_chen N hK hKS
  have hbase : (S (primeSequence N) 1 N K : ℝ) ≤
      (S (Wu08.Achen N) 1 N K : ℝ) + N.primeFactors.card := by
    exact_mod_cast primeSequence_sieve_transfer N 1 N K
  have hneg₁ : (Wu08.S₁ (Wu08.Achen N) N K Sg : ℝ) ≤ sieveTerms N 2 := by
    change ((∑ p ∈ Wu41.PS N K Sg, S (Wu08.Achen N) p N K : ℕ) : ℝ) ≤
      ((∑ p ∈ Wu41.PS N K Sg, S (primeSequence N) p N K : ℕ) : ℝ)
    exact_mod_cast (sum_le_sum (fun p (_ : p ∈ Wu41.PS N K Sg) => Achen_sieve_le N p N K))
  have hneg₂ : (Wu08.S₂ (Wu08.Achen N) N Sg : ℝ) ≤ sieveTerms N 6 := by
    change ((∑ q ∈ Wu08.pairs N Sg (N : ℝ) Sg,
      S (Wu08.Achen N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤
      ((∑ q ∈ Wu08Sum.P2 N (fun p q => Sg ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ)
    rw [pairs_eq_upper]
    exact_mod_cast (sum_le_sum (fun (q : ℕ × ℕ) (_ : q ∈ _) =>
      Achen_sieve_le N (q.1 * q.2) (N * q.1) q.2))
  have hneg₃ : (Wu08.S₃ (Wu08.Achen N) N K Sg : ℝ) ≤ sieveTerms N 8 := by
    change ((∑ q ∈ Wu08.pairs N K Sg Sg,
      S (Wu08.Achen N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤
      ((∑ q ∈ Wu08Sum.P2 N (fun p q => K ≤ p ∧ (p : ℝ) < Sg ∧ Sg ≤ q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ)
    rw [pairs_eq_cross]
    exact_mod_cast (sum_le_sum (fun (q : ℕ × ℕ) (_ : q ∈ _) =>
      Achen_sieve_le N (q.1 * q.2) (N * q.1) q.2))
  let C : ℕ → ℕ → ℕ → Prop := fun p q r => K ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < Sg
  let T : Finset ℕ → ℕ := fun A => ∑ q ∈ primeTriples N C,
    S A (q.1 * q.2.1 * q.2.2) (N * q.1) q.2.1
  have htransfer : (T (primeSequence N) : ℝ) ≤
      (T (Wu08.Achen N) : ℝ) + T (primeSequence N \ Wu08.Achen N) := by
    exact_mod_cast triple_sum_transfer (primeSequence N) (Wu08.Achen N) N C
      (fun q => N * q.1) (fun q => (q.2.1 : ℝ))
  have hbad : (T (primeSequence N \ Wu08.Achen N) : ℝ) ≤
      (N : ℝ) ^ (11 / 12 : ℝ) := by
    simpa only [T, Nat.cast_sum] using
      ht N hEven (by omega) C (fun q => N * q.1) (fun q => (q.2.1 : ℝ))
  have hcop : T (Wu08.Achen N) = Wu08.S₄ (Wu08.Achen N) N K Sg :=
    triple_sum_eq_S4 (Wu08.Achen N) N K Sg hSN
  have hS4 : tripleTerms N 3 ≤ (Wu08.S₄ (Wu08.Achen N) N K Sg : ℝ) +
      (N : ℝ) ^ (11 / 12 : ℝ) := by
    change (T (primeSequence N) : ℝ) ≤ _
    rw [← hcop]
    exact htransfer.trans (add_le_add le_rfl hbad)
  have hcard := hc N (by omega)
  have herr := lemma21_remainder_power N hN4096
  change 2 * (S (primeSequence N) 1 N K : ℝ) - sieveTerms N 2 -
    2 * sieveTerms N 6 - sieveTerms N 8 + tripleTerms N 3 ≤ _
  nlinarith only [hChen, hbase, hneg₁, hneg₂, hneg₃, hS4, hcard, herr]

/-- LEAF. Wu 2004 page 37 last display, after equation 9.9.
Buchstab cancellation bounds Delta two from below after discarding Upsilon 15. -/
theorem delta_cancellation : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      -sieveTerms N 10 - sieveTerms N 11 ≤ deltaOne N + tripleTerms N 3 +
        C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

/-- The exact weighted_sieve_power statement follows from three smaller leaves.
OPEN through first_half, second_half and delta_cancellation. -/
theorem weighted_sieve_power_supplied : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      weighted (sieveTerms N) ≤ 4 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C₁, hC₁, M₁, h₁⟩ := first_half
  obtain ⟨C₂, hC₂, M₂, h₂⟩ := second_half
  obtain ⟨C₃, hC₃, M₃, h₃⟩ := delta_cancellation
  refine ⟨C₁ + C₂ + C₃, by positivity, max M₁ (max M₂ M₃), ?_⟩
  intro N hEven hN
  have ha := h₁ N hEven (le_trans (le_max_left _ _) hN)
  have hb := h₂ N hEven (by omega)
  have hc := h₃ N hEven (by omega)
  dsimp only [weighted]
  nlinarith only [ha, hb, hc]

end LeanLab.ChenDoubleSieve.Task315
