/-
Split of compositeMean_model, MMS arXiv 1610.02017v2 page 11 bottom display.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp581a
import LeanLab.PNTSieve.MertensLower

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The admissible least prime factors of a composite x to the one quarter
rough number in the reference interval. MMS page 11 bottom display. -/
def s145c_lpfAdmissible (x : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x

/-- The normalized weighted bucket of n in the reference interval divisible by
the prime p with cofactor rough at p. MMS page 11 bottom display, one term of
the Buchstab identity compositeRough_buchstab. -/
noncomputable def s145c_bucketMean (x : ℝ) (p : ℕ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    if p ∣ n then Task379.referenceWeight x n * Task361.roughIndicator (n / p) p else 0) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The frozen Buchstab density of one bucket. MMS page 11 bottom display. -/
noncomputable def s145c_bucketModel (x : ℝ) (p : ℕ) : ℝ :=
  Real.log x * (Task571.buchstabModel (Real.log (x / p) / Real.log p) / (p * Real.log p))



/-- Composite numbers rough at x to the one quarter whose least prime factor
squared exceeds x, the boundary of the Buchstab buckets. MMS page 11. -/
noncomputable def s145c_boundaryRough (x : ℝ) (n : ℕ) : ℝ :=
  if ¬n.Prime ∧ x ^ (1 / 4 : ℝ) ≤ (n.minFac : ℝ) ∧ x < (n.minFac : ℝ) ^ 2 then 1 else 0

/-- Pointwise finite Buchstab identity removing the least prime factor, with
the boundary term. Derived, MMS page 11 bottom display. -/
theorem s145c_pointwise_buckets {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : x ≤ n) :
    compositeRough n (x ^ (1 / 4 : ℝ)) =
      (∑ p ∈ range (⌊x⌋₊ + 1), if s145c_lpfAdmissible x p then
        (if p ∣ n then Task361.roughIndicator (n / p) p else 0) else 0) +
      s145c_boundaryRough x n := by
  have hn2 : 2 ≤ n := by
    have : (1:ℝ) < n := by linarith
    exact_mod_cast this
  have hn1 : n ≠ 1 := by omega
  set q := n.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime hn1
  have hqn : q ∣ n := Nat.minFac_dvd n
  rw [sum_eq_single q]
  · rw [compositeRough_bucket hn1]
    unfold s145c_boundaryRough s145c_lpfAdmissible
    rw [← hq]
    generalize x ^ (1 / 4 : ℝ) = y
    by_cases hpr : n.Prime
    · have hqe : q = n := (Nat.Prime.minFac_eq hpr)
      have hbig : ¬ ((q : ℝ) ^ 2 ≤ x) := by
        rw [hqe]; push Not
        have : (n : ℝ) < (n : ℝ) ^ 2 := by
          have : (1 : ℝ) < n := by linarith
          nlinarith
        linarith
      simp [hpr, hbig]
    · by_cases hy : y ≤ (q : ℝ)
      · by_cases hsq : (q : ℝ) ^ 2 ≤ x
        · rw [hq, minFac_cofactor_rough, ← hq]
          simp [hpr, hy, hsq, hqp, hqn, not_lt.mpr hsq]
        · simp [hpr, hy, hsq, lt_of_not_ge hsq]
      · simp [hpr, hy]
  · intro p _ hpq
    split_ifs with hadm hdvd
    · have hpp : p.Prime := hadm.1
      have hle : q ≤ p := Nat.minFac_le_of_dvd hpp.two_le hdvd
      have hlt : q < p := lt_of_le_of_ne hle (fun h => hpq h.symm)
      unfold Task361.roughIndicator
      rw [if_neg]
      push Not
      have hnp : n = p * (n / p) := (Nat.mul_div_cancel' hdvd).symm
      have h2 : q ∣ p * (n / p) := hnp ▸ hqn
      rcases (Nat.Prime.dvd_mul hqp).mp h2 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp h) (ne_of_lt hlt)
      · exact ⟨q, hqp, by exact_mod_cast hlt, h⟩
    · rfl
    · rfl
  · intro hq'
    rw [if_neg]
    rintro ⟨_, _, hsq⟩
    apply hq'
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have : (1:ℝ) ≤ q := by exact_mod_cast hqp.one_lt.le
    nlinarith


/-- The normalized weighted boundary mass. MMS page 11 bottom display. -/
noncomputable def s145c_boundaryMean (x : ℝ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    Task379.referenceWeight x n * s145c_boundaryRough x n) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- compositeMean is the sum of the bucket means plus the boundary mean.
Derived, exact. MMS page 11 bottom display. -/
theorem s145c_compositeMean_eq {x : ℝ} (hx : 1 < x) :
    compositeMean x = (∑ p ∈ range (⌊x⌋₊ + 1),
        if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0) + s145c_boundaryMean x := by
  have key : (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * compositeRough n (x ^ (1 / 4 : ℝ))) =
      (∑ p ∈ range (⌊x⌋₊ + 1), ∑ n ∈ ints x (x + Task379.referenceLength x),
        if s145c_lpfAdmissible x p then (if p ∣ n then
          Task379.referenceWeight x n * Task361.roughIndicator (n / p) p else 0) else 0) +
      ∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * s145c_boundaryRough x n := by
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast (mem_Icc.mp hn).1)
    rw [s145c_pointwise_buckets hx hxn, mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have key2 : (∑ p ∈ range (⌊x⌋₊ + 1),
      if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0) =
      Real.log x * (∑ p ∈ range (⌊x⌋₊ + 1), ∑ n ∈ ints x (x + Task379.referenceLength x),
        if s145c_lpfAdmissible x p then (if p ∣ n then
          Task379.referenceWeight x n * Task361.roughIndicator (n / p) p else 0) else 0) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) := by
    unfold s145c_bucketMean
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun p _ => ?_
    by_cases h : s145c_lpfAdmissible x p <;> simp [h]
  rw [key2]
  unfold compositeMean s145c_boundaryMean
  rw [key]
  ring

/-- The flat exponential factor is at most one. Derived. -/
theorem s145c_expNegInvGlue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · norm_num
  · push Not at h
    exact Real.exp_le_one_iff.mpr (by have := inv_pos.mpr h; linarith)

/-- The reference weight is at most one. Derived. -/
theorem s145c_referenceWeight_le_one (x t : ℝ) : Task379.referenceWeight x t ≤ 1 := by
  unfold Task379.referenceWeight
  have h1 := s145c_expNegInvGlue_le_one ((t - x) / Task379.referenceLength x)
  have h2 := s145c_expNegInvGlue_le_one (1 - (t - x) / Task379.referenceLength x)
  have h3 := expNegInvGlue.nonneg ((t - x) / Task379.referenceLength x)
  have h4 := expNegInvGlue.nonneg (1 - (t - x) / Task379.referenceLength x)
  nlinarith

/-- Integers in a real interval. Derived. -/
theorem s145c_card_Icc_le {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ((Icc ⌈A⌉₊ ⌊B⌋₊).card : ℝ) ≤ B - A + 1 := by
  rw [Nat.card_Icc]
  by_cases h : ⌈A⌉₊ ≤ ⌊B⌋₊ + 1
  · rw [Nat.cast_sub h]
    push_cast
    have h1 := Nat.floor_le (hA.trans hAB)
    have h2 := Nat.le_ceil A
    linarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simp; linarith

/-- MMS page 11 bottom display, counting the boundary of the Buchstab buckets.
PROVED: n maps injectively to its least prime q and cofactor n over q, both
in intervals of length at most the reference length over the square root of x. -/
theorem s145c_boundary_count {x : ℝ} (hx : 1 < x) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * s145c_boundaryRough x n) ≤
      (Task379.referenceLength x / Real.sqrt x + 1) ^ 2 := by
  classical
  set L := Task379.referenceLength x with hLdef
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := by rw [hLdef]; unfold Task379.referenceLength; positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  set S := (ints x (x + L)).filter (fun n => s145c_boundaryRough x n = 1) with hSdef
  have hstep : (∑ n ∈ ints x (x + L), Task379.referenceWeight x n * s145c_boundaryRough x n)
      ≤ (S.card : ℝ) := by
    rw [hSdef, card_filter, Nat.cast_sum]
    refine sum_le_sum fun n _ => ?_
    unfold s145c_boundaryRough
    split_ifs <;> simp_all [s145c_referenceWeight_le_one]
  refine hstep.trans ?_
  set T := (Icc ⌈Real.sqrt x⌉₊ ⌊Real.sqrt (x + L)⌋₊) ×ˢ
    (Icc ⌈Real.sqrt x⌉₊ ⌊(x + L) / Real.sqrt x⌋₊) with hT
  have hcard : S.card ≤ T.card := by
    refine card_le_card_of_injOn (fun n => (n.minFac, n / n.minFac)) ?_ ?_
    · intro n hn
      have hn' := mem_filter.mp hn
      have hb := hn'.2
      unfold s145c_boundaryRough at hb
      split_ifs at hb with hc
      swap; · norm_num at hb
      obtain ⟨hnp, _, hq2⟩ := hc
      have hmem := mem_Icc.mp hn'.1
      have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hmem.1)
      have hnL : (n : ℝ) ≤ x + L := (Nat.le_floor_iff (by positivity)).mp hmem.2
      have hnpos : 0 < n := by
        have : (0:ℝ) < n := by linarith
        exact_mod_cast this
      have hsq := Nat.minFac_sq_le_self hnpos hnp
      have hsqR : ((n.minFac : ℝ)) ^ 2 ≤ n := by exact_mod_cast hsq
      have hq0 : (0 : ℝ) ≤ n.minFac := by positivity
      have hqlo : Real.sqrt x ≤ n.minFac := by
        rw [Real.sqrt_le_left]; · nlinarith
        exact hq0
      have hqhi : (n.minFac : ℝ) ≤ Real.sqrt (x + L) :=
        Real.le_sqrt_of_sq_le (by linarith)
      have hqpos : 0 < n.minFac := Nat.minFac_pos n
      have hqm : n.minFac ≤ n / n.minFac := by
        rw [Nat.le_div_iff_mul_le hqpos]; rw [sq] at hsq; exact hsq
      have hqmR : (n.minFac : ℝ) ≤ (n / n.minFac : ℕ) := by exact_mod_cast hqm
      have hmq : (n / n.minFac) * n.minFac ≤ n := Nat.div_mul_le_self n n.minFac
      have hmqR : ((n / n.minFac : ℕ) : ℝ) * n.minFac ≤ n := by exact_mod_cast hmq
      simp only [hT, coe_product, Set.mem_prod, mem_coe, mem_Icc]
      refine ⟨⟨Nat.ceil_le.mpr hqlo, Nat.le_floor hqhi⟩, ⟨Nat.ceil_le.mpr (hqlo.trans hqmR), ?_⟩⟩
      apply Nat.le_floor
      rw [le_div_iff₀ hsx]
      nlinarith
    · intro n₁ h₁ n₂ h₂ he
      simp only [Prod.mk.injEq] at he
      calc n₁ = n₁ / n₁.minFac * n₁.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd n₁)).symm
        _ = n₂ / n₂.minFac * n₂.minFac := by rw [he.2, he.1]
        _ = n₂ := Nat.div_mul_cancel (Nat.minFac_dvd n₂)
  have hT1 := s145c_card_Icc_le (A := Real.sqrt x) (B := Real.sqrt (x + L)) hsx.le
    (Real.sqrt_le_sqrt (by linarith))
  have hxs : Real.sqrt x ≤ (x + L) / Real.sqrt x := by
    rw [le_div_iff₀ hsx, Real.mul_self_sqrt hx0.le]; linarith
  have hT2 := s145c_card_Icc_le (A := Real.sqrt x) (B := (x + L) / Real.sqrt x) hsx.le hxs
  have hdiff1 : Real.sqrt (x + L) - Real.sqrt x ≤ L / Real.sqrt x := by
    rw [le_div_iff₀ hsx]
    have h1 : Real.sqrt x ≤ Real.sqrt (x + L) := Real.sqrt_le_sqrt (by linarith)
    have h2 := Real.mul_self_sqrt (show 0 ≤ x + L by linarith)
    have h3 := Real.mul_self_sqrt hx0.le
    nlinarith
  have hdiff2 : (x + L) / Real.sqrt x - Real.sqrt x = L / Real.sqrt x := by
    field_simp
    rw [Real.sq_sqrt hx0.le]; ring
  have hTc : (T.card : ℝ) ≤ (L / Real.sqrt x + 1) ^ 2 := by
    rw [hT, card_product, Nat.cast_mul, sq]
    apply mul_le_mul
    · linarith
    · linarith
    · positivity
    · positivity
  calc (S.card : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ ≤ _ := hTc

/-- MMS page 11, the boundary bound is small against the reference length.
PROVED: with s the square root of log x, exp s is at least s cubed over six. -/
theorem s145c_boundary_asymptotic :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Real.log x * (Task379.referenceLength x / Real.sqrt x + 1) ^ 2 ≤
        δ * Task379.referenceLength x := by
  intro δ hδ
  set K := max 2 (24 / δ) with hK
  refine ⟨Real.exp (K ^ 2), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : K ^ 2 ≤ Real.log x := by
    rw [← Real.log_exp (K ^ 2)]; exact Real.log_le_log (Real.exp_pos _) hx
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKd : 24 / δ ≤ K := le_max_right _ _
  set s := Real.sqrt (Real.log x) with hs
  have hlog0 : 0 ≤ Real.log x := by nlinarith
  have hs2 : s ^ 2 = Real.log x := Real.sq_sqrt hlog0
  have hsK : K ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le hlogx
  have hs0 : 0 < s := by linarith
  have hxe : x = Real.exp (s ^ 2) := by rw [hs2, Real.exp_log hx0]
  have hE : s ^ 3 / 6 ≤ Real.exp s := by
    have := Real.pow_div_factorial_le_exp (x := s) hs0.le 3
    simpa [Nat.factorial] using this
  have hsd : 24 / δ ≤ s := hKd.trans hsK
  have hsd' : 24 ≤ δ * s := by rwa [div_le_iff₀ hδ, mul_comm] at hsd
  -- first: 4 s^2 ≤ δ e^s
  have h1 : 4 * s ^ 2 ≤ δ * Real.exp s := by
    have : 4 * s ^ 2 ≤ δ * (s ^ 3 / 6) := by nlinarith
    nlinarith
  -- second: 4 s^2 e^s ≤ δ x
  have h2 : 4 * s ^ 2 * Real.exp s ≤ δ * x := by
    have hss : 2 * s ≤ s ^ 2 := by nlinarith
    have he : Real.exp s * Real.exp s ≤ x := by
      rw [← Real.exp_add, hxe]; exact Real.exp_le_exp.mpr (by linarith)
    have hep := Real.exp_pos s
    nlinarith
  set L := Task379.referenceLength x with hL
  have hLdef : L = x * Real.exp (-s) := rfl
  have hes : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  have hsq : (L / Real.sqrt x) ^ 2 = L ^ 2 / x := by
    rw [div_pow, Real.sq_sqrt hx0.le]
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hbound : (L / Real.sqrt x + 1) ^ 2 ≤ 2 * (L ^ 2 / x) + 2 := by
    nlinarith [sq_nonneg (L / Real.sqrt x - 1)]
  -- log x * (2 L^2/x + 2) ≤ δ L
  have hA : Real.log x * (2 * (L ^ 2 / x)) ≤ δ * L / 2 := by
    rw [← hs2]
    have : L ^ 2 / x = x * Real.exp (-s) * Real.exp (-s) := by
      rw [hLdef]; field_simp
    rw [this]
    have hem := Real.exp_pos (-s)
    -- s^2 * 2 * x e^{-2s} ≤ δ x e^{-s} / 2  ⇔ 4 s^2 e^{-s} ≤ δ
    have h1' : 4 * s ^ 2 * Real.exp (-s) ≤ δ := by
      have := mul_le_mul_of_nonneg_right h1 hem.le
      nlinarith
    rw [hLdef]
    have hxp := hx0.le
    nlinarith [mul_le_mul_of_nonneg_left h1' (mul_nonneg hxp hem.le)]
  have hB : Real.log x * 2 ≤ δ * L / 2 := by
    rw [← hs2, hLdef]
    have hem := Real.exp_pos (-s)
    have := mul_le_mul_of_nonneg_right h2 hem.le
    nlinarith
  calc Real.log x * (L / Real.sqrt x + 1) ^ 2
      ≤ Real.log x * (2 * (L ^ 2 / x) + 2) := mul_le_mul_of_nonneg_left hbound hlog0
    _ ≤ δ * L := by nlinarith

/-- The boundary of the Buchstab buckets has normalized mass tending to zero.
MMS page 11 bottom display. CONDITIONAL ON s145c_boundary_count and
s145c_boundary_asymptotic. -/
theorem s145c_boundaryMean_small :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |s145c_boundaryMean x| ≤ δ := by
  intro δ hδ
  obtain ⟨I, hI, hS⟩ := weightIntegral_scaling
  obtain ⟨X, hX⟩ := s145c_boundary_asymptotic (δ * I) (by positivity)
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have hL := referenceLength_pos_of_one_le hx1.le
  have hlx : 0 ≤ Real.log x := (Real.log_pos hx1).le
  have hS0 : 0 ≤ ∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * s145c_boundaryRough x n := by
    refine sum_nonneg fun n _ => mul_nonneg (Task379.referenceWeight_nonneg _ _) ?_
    unfold s145c_boundaryRough; split_ifs <;> norm_num
  have hc := s145c_boundary_count hx1
  have ha := hX x ((le_max_left _ _).trans hx)
  unfold s145c_boundaryMean
  rw [hS x hx1.le, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  calc Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * s145c_boundaryRough x n)
      ≤ Real.log x * (Task379.referenceLength x / Real.sqrt x + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hc hlx
    _ ≤ δ * I * Task379.referenceLength x := ha
    _ = δ * (I * Task379.referenceLength x) := by ring

/-- The finite Buchstab identity in mean form up to the boundary. Proved from
s145c_compositeMean_eq, CONDITIONAL ON s145c_boundaryMean_small. -/
theorem s145c_compositeMean_buckets :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - ∑ p ∈ range (⌊x⌋₊ + 1),
        if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0| ≤ δ := by
  intro δ hδ
  obtain ⟨X, hX⟩ := s145c_boundaryMean_small δ hδ
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  rw [s145c_compositeMean_eq hx1, add_sub_cancel_left]
  exact hX x ((le_max_left _ _).trans hx)

/-- LEAF: MMS page 11 bottom display, Buchstab recursion for the rough cofactor
n over p near x over p, rough at the least prime p, density buchstab of u over
log p with u frozen at log of x over p over log p, uniformly over the admissible
p and the subintervals from a to b of the reference interval. Class HARD.
CITED input: the short interval prime number theorem at scales x over d at
least x to the one tenth with d at most x to the nine tenths, exactly
shortIntervalPNT_scaled of Feed1122Decomp581b, Vinogradov Korobov or Huxley,
applied with d equal to p times the removed cofactor primes; the recursion has at
most three levels since u is at most three. This is
roughCount_of_shortIntervalPNT with the single prime p in place of the triple. -/
theorem s145c_bucketRoughCount :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p : ℕ, s145c_lpfAdmissible x p →
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            Task361.roughIndicator (n / p) p else 0) -
          (b - a) * s145c_bucketModel x p| ≤
        ε * Task379.referenceLength x / p := by
  sorry

section S145_s145c_bucketMean_transfer
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable

theorem s145x_layer_term_integrable (w M c : ℝ) (hw : 0 ≤ w) (hM : w ≤ M) :
    IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 M := by
  have h1 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 w := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hw]
    refine IntegrableOn.congr_fun_ae (f := fun _ => c) (integrableOn_const (by simp)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume w).filter_mono ae_restrict_le] with s hs hne
    simp [lt_of_le_of_ne hs.2 hne]
  have h2 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume w M := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr ?_
    rw [Set.uIoc_of_le hM]
    intro s hs
    simp [not_lt.mpr hs.1.le]
  exact h1.trans h2

/-- Pass 6 helper, MMS page 11 bottom display, layer cake for one term:
the integral over levels of one indicator recovers the weight. -/
theorem s145x_layer_term (w M c : ℝ) (hw : 0 ≤ w) (hM : w ≤ M) :
    ∫ s in (0:ℝ)..M, (if s < w then c else 0) = w * c := by
  have h2 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume w M := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr ?_
    rw [Set.uIoc_of_le hM]
    intro s hs
    simp [not_lt.mpr hs.1.le]
  have h1 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 w := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hw]
    refine IntegrableOn.congr_fun_ae (f := fun _ => c) (integrableOn_const (by simp)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume w).filter_mono ae_restrict_le] with s hs hne
    simp [lt_of_le_of_ne hs.2 hne]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ s in (0:ℝ)..w, (if s < w then c else 0) = ∫ s in (0:ℝ)..w, c := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hw]
    filter_upwards [Measure.ae_ne volume w] with s hne hs
    simp [lt_of_le_of_ne hs.2 hne]
  have e2 : ∫ s in w..M, (if s < w then c else 0) = ∫ s in w..M, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hM] at hs
    simp [not_lt.mpr hs.1]
  rw [e1, e2]; simp

/-- Pass 6, finite layer cake identity for the layer cake step of
cofactorMean_transfer, MMS page 11 bottom display: a weighted finite sum is
the integral over levels s of the sums over the superlevel sets. -/

theorem s145x_finite_layer_cake {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (M : ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hM : ∀ n ∈ S, w n ≤ M) :
    ∑ n ∈ S, w n * f n =
      ∫ s in (0:ℝ)..M, ∑ n ∈ S, (if s < w n then f n else 0) := by
  rw [intervalIntegral.integral_finsetSum
    (fun n hn => s145x_layer_term_integrable _ _ _ (hw n hn) (hM n hn))]
  exact Finset.sum_congr rfl (fun n hn => (s145x_layer_term _ _ _ (hw n hn) (hM n hn)).symm)

theorem s145x_numerator_layer_cake (x : ℝ) (p : ℕ) (M : ℝ)
    (hM : ∀ n : ℕ, Task379.referenceWeight x n ≤ M) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      if p ∣ n then
        Task379.referenceWeight x n * Task361.roughIndicator (n / p) p
      else 0) =
    ∫ s in (0:ℝ)..M, ∑ n ∈ ints x (x + Task379.referenceLength x),
      (if s < Task379.referenceWeight x n then
        (if p ∣ n then Task361.roughIndicator (n / p) p
          else 0) else 0) := by
  rw [← s145x_finite_layer_cake _ (fun n : ℕ => Task379.referenceWeight x n)
    (fun n : ℕ => if p ∣ n then
      Task361.roughIndicator (n / p) p else 0) M
    (fun n _ => Task379.referenceWeight_nonneg x n) (fun n _ => hM n)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp

theorem s145x_levelSum (x s a b : ℝ) (p : ℕ)
    (hlev : ∀ n : ℕ, s < Task379.referenceWeight x n ↔ a < (n : ℝ) ∧ (n : ℝ) < b) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      (if s < Task379.referenceWeight x n then
        (if p ∣ n then Task361.roughIndicator (n / p) p
          else 0) else 0)) =
    ∑ n ∈ ints x (x + Task379.referenceLength x),
      if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
        Task361.roughIndicator (n / p) p else 0 := by
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : s < Task379.referenceWeight x n <;>
    by_cases h2 : p ∣ n <;> simp_all

theorem s145x_profile_level (s : ℝ) (hs : 0 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ ∀ u : ℝ,
      s < expNegInvGlue u * expNegInvGlue (1 - u) ↔ |u - 1 / 2| < r := by
  rcases le_or_gt 1 s with h1 | h1
  · refine ⟨0, le_refl _, by norm_num, fun u => ?_⟩
    have a1 := s145c_expNegInvGlue_le_one u
    have a2 := s145c_expNegInvGlue_le_one (1 - u)
    have a3 := expNegInvGlue.nonneg u
    have a4 := expNegInvGlue.nonneg (1 - u)
    constructor
    · intro h; nlinarith
    · intro h; exact absurd h (not_lt.mpr (abs_nonneg _))
  have hlog : Real.log s < 0 := Real.log_neg hs h1
  set k : ℝ := (-Real.log s)⁻¹ with hk
  have hk0 : 0 < k := inv_pos.mpr (by linarith)
  refine ⟨Real.sqrt (max (1 / 4 - k) 0), Real.sqrt_nonneg _, ?_, fun u => ?_⟩
  · rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (max_le (by linarith) (by norm_num))
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
  by_cases hu : 0 < u ∧ u < 1
  · obtain ⟨hu0, hu1⟩ := hu
    have h1u : 0 < 1 - u := by linarith
    simp only [expNegInvGlue, not_le.mpr hu0, not_le.mpr h1u, ite_false, ← Real.exp_add]
    have e1 : -u⁻¹ + -(1 - u)⁻¹ = -(u * (1 - u))⁻¹ := by field_simp; ring
    rw [e1, ← Real.log_lt_iff_lt_exp hs]
    have hq : 0 < u * (1 - u) := mul_pos hu0 h1u
    have step : Real.log s < -(u * (1 - u))⁻¹ ↔ k < u * (1 - u) := by
      rw [hk, inv_lt_comm₀ (by linarith) hq]
      constructor <;> intro h <;> linarith
    rw [step]
    constructor
    · intro h
      calc (u - 1 / 2) ^ 2 = 1 / 4 - u * (1 - u) := by ring
        _ < 1 / 4 - k := by linarith
        _ ≤ max (1 / 4 - k) 0 := le_max_left _ _
    · intro h
      rcases le_total (1 / 4 - k) 0 with h2 | h2
      · rw [max_eq_right h2] at h; nlinarith [sq_nonneg (u - 1 / 2)]
      · rw [max_eq_left h2] at h; nlinarith
  · have hz : expNegInvGlue u * expNegInvGlue (1 - u) = 0 := by
      rcases le_or_gt u 0 with h0 | h0
      · rw [expNegInvGlue.zero_of_nonpos h0, zero_mul]
      · have : 1 ≤ u := by by_contra hc; exact hu ⟨h0, by linarith⟩
        rw [expNegInvGlue.zero_of_nonpos (by linarith : 1 - u ≤ 0), mul_zero]
    rw [hz]
    constructor
    · intro h; linarith
    · intro h
      exfalso
      have hb : (1 / 4 : ℝ) ≤ (u - 1 / 2) ^ 2 := by
        rcases le_or_gt u 0 with h0 | h0
        · nlinarith
        · have : 1 ≤ u := by by_contra hc; exact hu ⟨h0, by linarith⟩
          nlinarith
      have : max (1 / 4 - k) 0 ≤ 1 / 4 := max_le (by linarith) (by norm_num)
      linarith


theorem s145x_weight_level {x : ℝ} (hx : 0 < x) (s : ℝ) (hs : 0 < s) :
    ∃ a b : ℝ, x ≤ a ∧ a ≤ b ∧ b ≤ x + Task379.referenceLength x ∧
      ∀ t : ℝ, s < Task379.referenceWeight x t ↔ a < t ∧ t < b := by
  have hL := Task379.referenceLength_pos hx
  set L := Task379.referenceLength x with hLdef
  obtain ⟨r, hr0, hr1, hr⟩ := s145x_profile_level s hs
  refine ⟨x + L * (1 / 2 - r), x + L * (1 / 2 + r), ?_, ?_, ?_, fun t => ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  unfold Task379.referenceWeight
  rw [← hLdef, hr, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (1 / 2 - r) < (t - x) / L := by linarith
    have e2 : (t - x) / L < 1 / 2 + r := by linarith
    rw [lt_div_iff₀ hL] at e1
    rw [div_lt_iff₀ hL] at e2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have e1 : (1 / 2 - r) < (t - x) / L := by rw [lt_div_iff₀ hL]; nlinarith
    have e2 : (t - x) / L < 1 / 2 + r := by rw [div_lt_iff₀ hL]; nlinarith
    constructor <;> linarith

theorem s145x_profile_rescale_integral (x L : ℝ) (hL : 0 < L) :
    (∫ t in x..(x + L), expNegInvGlue ((t - x) / L) * expNegInvGlue (1 - (t - x) / L)) =
      L * ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := intervalIntegral.integral_comp_div_sub
    (fun s => expNegInvGlue s * expNegInvGlue (1 - s)) (c := L) (d := x / L) hL.ne'
    (a := x) (b := x + L)
  simp only [sub_div] at *
  rw [h]
  have e1 : x / L - x / L = 0 := sub_self _
  have e2 : (x + L) / L - x / L = 1 := by field_simp; ring
  rw [e1, e2, smul_eq_mul]

theorem s145x_profile_integral_pos :
    0 < ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have hc : Continuous (fun s : ℝ => expNegInvGlue s * expNegInvGlue (1 - s)) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ zero_lt_one
  intro s hs
  exact mul_pos (expNegInvGlue.pos_of_pos hs.1) (expNegInvGlue.pos_of_pos (by linarith [hs.2]))

/-- Layer cake for the weight integral over the reference interval. -/
theorem s145x_weight_layer {x : ℝ} (hx : 0 < x) :
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
      ∫ s in (0:ℝ)..1, ((volume.restrict (Set.Ioc x (x + Task379.referenceLength x))).real
        {t | s < Task379.referenceWeight x t}) := by
  have hL := Task379.referenceLength_pos hx
  set L := Task379.referenceLength x with hLdef
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le zero_le_one]
  have hint : Integrable (Task379.referenceWeight x) (volume.restrict (Set.Ioc x (x + L))) :=
    ((Task379.referenceWeight_contDiff x 0).continuous.integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  rw [hint.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall fun t => Task379.referenceWeight_nonneg x t)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self
  intro s hs
  have hs1 : 1 < s := by
    rcases hs with ⟨h1, h2⟩
    simp only [Set.mem_Ioi] at h1
    simp only [Set.mem_Ioc, not_and, not_le] at h2
    exact h2 h1
  have he : {t | s < Task379.referenceWeight x t} = ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    linarith [s145c_referenceWeight_le_one x t]
  rw [he, measureReal_empty]

theorem s145c_bucketMean_transfer_s145 :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ p : ℕ, s145c_lpfAdmissible x p → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
            if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
              Task361.roughIndicator (n / p) p else 0) -
            (b - a) * s145c_bucketModel x p| ≤
          ε * Task379.referenceLength x / p) →
      |s145c_bucketMean x p - s145c_bucketModel x p| ≤ C * ε / p := by
  set c0 := ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) with hc0
  have hc0p : 0 < c0 := s145x_profile_integral_pos
  refine ⟨1 / c0, by positivity, fun x hx p hp ε hε hyp => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL := Task379.referenceLength_pos hx0
  set L := Task379.referenceLength x with hLdef
  have hd : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  set d : ℝ := (p : ℝ) with hddef
  set μ := volume.restrict (Set.Ioc x (x + L)) with hμ
  set m : ℝ → ℝ := fun s => μ.real {t | s < Task379.referenceWeight x t} with hmdef
  set F : ℕ → ℝ := fun n => if p ∣ n then
    Task361.roughIndicator (n / p) p else 0 with hF
  set cnt : ℝ → ℝ := fun s => ∑ n ∈ ints x (x + L),
      (if s < Task379.referenceWeight x n then F n else 0) with hcnt
  set N := ∑ n ∈ ints x (x + L),
    if p ∣ n then
      Task379.referenceWeight x n * Task361.roughIndicator (n / p) p
    else 0 with hN
  set I := ∫ t in x..(x + L), Task379.referenceWeight x t with hIdef
  -- weight integral scaling
  have hIs : I = c0 * L := by
    rw [hIdef]
    unfold Task379.referenceWeight
    rw [← hLdef, s145x_profile_rescale_integral x L hL, mul_comm]
  have hIp : 0 < I := by rw [hIs]; positivity
  -- layer cakes
  have hNl : N = ∫ s in (0:ℝ)..1, cnt s :=
    s145x_numerator_layer_cake x p 1 (fun n => s145c_referenceWeight_le_one x n)
  have hIl : I = ∫ s in (0:ℝ)..1, m s := s145x_weight_layer hx0
  -- integrability
  have hcntI : IntervalIntegrable cnt volume 0 1 := by
    have := IntervalIntegrable.sum (μ := volume) (a := (0:ℝ)) (b := 1) (ints x (x + L))
      (f := fun n s => if s < Task379.referenceWeight x n then F n else 0)
      (fun n _ => s145x_layer_term_integrable _ _ _ (Task379.referenceWeight_nonneg x n)
        (s145c_referenceWeight_le_one x n))
    refine this.congr ?_
    intro s _
    simp [hcnt, Finset.sum_apply]
  have hmanti : Antitone m := by
    intro s1 s2 h12
    simp only [hmdef]
    apply measureReal_mono
    · intro t ht
      simp only [Set.mem_ofPred_eq] at ht ⊢
      linarith
    · apply ne_of_lt
      calc μ {t | s1 < Task379.referenceWeight x t} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = volume (Set.Ioc x (x + L)) := Measure.restrict_apply_univ _
        _ < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hmI : IntervalIntegrable m volume 0 1 := hmanti.intervalIntegrable
  -- pointwise bound
  have hpt : ∀ s ∈ Set.uIoc (0:ℝ) 1,
      ‖Real.log x * cnt s - m s * s145c_bucketModel x p‖ ≤ ε * L / d := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    obtain ⟨a, b, hxa, hab, hbL, hlev⟩ := s145x_weight_level hx0 s hs.1
    have hcs : cnt s = ∑ n ∈ ints x (x + L),
        if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          Task361.roughIndicator (n / p) p else 0 :=
      s145x_levelSum x s a b p (fun n => hlev n)
    have hms : m s = b - a := by
      simp only [hmdef]
      have hset : {t | s < Task379.referenceWeight x t} = Set.Ioo a b := by
        ext t; simp [hlev t]
      rw [hset, hμ, measureReal_restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr (show Set.Ioo a b ⊆ Set.Ioc x (x + L) from
          fun t ht => ⟨lt_of_le_of_lt hxa ht.1, (ht.2.trans_le hbL).le⟩),
        Real.volume_real_Ioo_of_le hab]
    rw [Real.norm_eq_abs, hcs, hms]
    exact hyp a b hxa hab hbL
  have hdiff : Real.log x * N - I * s145c_bucketModel x p =
      ∫ s in (0:ℝ)..1, (Real.log x * cnt s - m s * s145c_bucketModel x p) := by
    rw [intervalIntegral.integral_sub (hcntI.const_mul _) (hmI.mul_const _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, hNl, hIl]
  have hbound : |Real.log x * N - I * s145c_bucketModel x p| ≤ ε * L / d := by
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    simpa using this
  have hmean : s145c_bucketMean x p = Real.log x * N / I := rfl
  rw [hmean]
  have he : Real.log x * N / I - s145c_bucketModel x p =
      (Real.log x * N - I * s145c_bucketModel x p) / I := by field_simp
  rw [he, abs_div, abs_of_pos hIp, div_le_iff₀ hIp]
  calc _ ≤ ε * L / d := hbound
    _ = 1 / c0 * ε / d * I := by rw [hIs]; field_simp

end S145_s145c_bucketMean_transfer

/-- Proved by S145, formerly a LEAF: MMS page 11 bottom display, passage from interval rough cofactor
counts to the smooth weighted bucket mean. Class MEDIUM. Deterministic layer
cake step exactly as cofactorMean_transfer of Feed1122Decomp581b with the single
prime p in place of the triple product: the reference weight is unimodal and
vanishes at both ends, so each superlevel set is an open subinterval. -/
theorem s145c_bucketMean_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ p : ℕ, s145c_lpfAdmissible x p → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
            if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
              Task361.roughIndicator (n / p) p else 0) -
            (b - a) * s145c_bucketModel x p| ≤
          ε * Task379.referenceLength x / p) →
      |s145c_bucketMean x p - s145c_bucketModel x p| ≤ C * ε / p := by
  exact s145c_bucketMean_transfer_s145

/-- The bucket mean is uniformly close to its frozen Buchstab density.
MMS page 11 bottom display. CONDITIONAL ON s145c_bucketRoughCount and
s145c_bucketMean_transfer. -/
theorem s145c_bucketMean_uniform :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p : ℕ, s145c_lpfAdmissible x p →
      |s145c_bucketMean x p - s145c_bucketModel x p| ≤ δ / p := by
  intro δ hδ
  obtain ⟨C, hC, hT⟩ := s145c_bucketMean_transfer
  obtain ⟨X, hX⟩ := s145c_bucketRoughCount (δ / C) (by positivity)
  refine ⟨max X 2, fun x hx p hp => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have h := hT x hx1 p hp (δ / C) (by positivity) (hX x ((le_max_left _ _).trans hx) p hp)
  have he : C * (δ / C) / (p : ℝ) = δ / (p : ℝ) := by field_simp
  rwa [he] at h

/-- Proved in this file by S145 from Mertens.sum_inv_primes_block, formerly a LEAF: MMS page 11 bottom display, the reciprocal prime mass from x to the
one quarter up to the square root of x is bounded, by Mertens second theorem it
tends to log 2. Class MEDIUM. -/
theorem s145c_lpfMass_bounded :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∑ p ∈ range (⌊x⌋₊ + 1), (if s145c_lpfAdmissible x p then 1 / (p : ℝ) else 0) ≤ C := by
  refine ⟨18, by norm_num, 6561, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set t : ℝ := x ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht9 : 9 ≤ t := by
    have h : (6561 : ℝ) ^ (1 / 4 : ℝ) = 9 := by
      rw [show (6561 : ℝ) = 9 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h]; exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hsq : Real.sqrt x = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  set y : ℕ := ⌊t⌋₊ - 1 with hy
  set w : ℕ := ⌊Real.sqrt x⌋₊ with hw
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hfl' : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have h9 : 9 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht9)
  have hyR : (y : ℝ) = ⌊t⌋₊ - 1 := by rw [hy, Nat.cast_sub (by omega)]; simp
  have hy2 : 2 ≤ y := by omega
  have hyt : (y : ℝ) ≤ t := by rw [hyR]; linarith
  have hyt2 : t - 2 ≤ (y : ℝ) := by rw [hyR]; linarith
  have htw : t ≤ Real.sqrt x := by rw [hsq]; nlinarith
  have hyw : y ≤ w := Nat.le_floor (hyt.trans htw)
  have hsub : ∑ p ∈ range (⌊x⌋₊ + 1), (if s145c_lpfAdmissible x p then 1 / (p : ℝ) else 0)
      ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨-, hpr, htp, hpx⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
      · have : (y : ℝ) < p := by rw [hyR]; linarith
        exact_mod_cast this
      · apply Nat.le_floor
        rw [show (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt hpx
    · intro p _ _; positivity
  refine hsub.trans ((LeanLab.PNTSieve.Mertens.sum_inv_primes_block y w hy2 hyw).trans ?_)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hw0 : (w : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hwpos : (0 : ℝ) < w := by
    have : 1 ≤ w := le_trans (by omega) hyw
    exact_mod_cast this
  have hlw : Real.log w ≤ 2 * Real.log t := by
    calc Real.log w ≤ Real.log (t ^ 2) := Real.log_le_log hwpos (hsq ▸ hw0)
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hsqt : Real.sqrt t ≤ t - 2 := by
    calc Real.sqrt t ≤ Real.sqrt ((t - 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = t - 2 := Real.sqrt_sq (by linarith)
  have hst0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have hlyt : Real.log t / 2 ≤ Real.log y := by
    calc Real.log t / 2 = Real.log (Real.sqrt t) := by rw [Real.log_sqrt ht0]
      _ ≤ Real.log y := Real.log_le_log hst0 (hsqt.trans hyt2)
  have hlt : 2.07 ≤ Real.log t := by
    have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  rw [div_le_iff₀ hly]
  linarith

/-- The model sum is the sum of the bucket models. Derived. -/
theorem s145c_compositeModelSum_eq (x : ℝ) :
    compositeModelSum x = ∑ p ∈ range (⌊x⌋₊ + 1),
      if s145c_lpfAdmissible x p then s145c_bucketModel x p else 0 := by
  classical
  unfold compositeModelSum s145c_bucketModel s145c_lpfAdmissible
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- compositeMean_model from the three leaves above, uniform error accumulation.
CONDITIONAL ON s145c_compositeMean_buckets, s145c_bucketMean_uniform and
s145c_lpfMass_bounded. -/
theorem compositeMean_model_of_s145_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - compositeModelSum x| ≤ δ := by
  intro δ hδ
  obtain ⟨C, hC, X₀, hX₀⟩ := s145c_lpfMass_bounded
  obtain ⟨X₁, hX₁⟩ := s145c_compositeMean_buckets (δ / 2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := s145c_bucketMean_uniform (δ / (2 * C)) (by positivity)
  refine ⟨max X₀ (max X₁ X₂), fun x hx => ?_⟩
  have h0 := hX₀ x ((le_max_left _ _).trans hx)
  have h1 := hX₁ x (((le_max_left _ _).trans (le_max_right _ _)).trans hx)
  have h2 := hX₂ x (((le_max_right _ _).trans (le_max_right _ _)).trans hx)
  classical
  have hsum : |(∑ p ∈ range (⌊x⌋₊ + 1),
        if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0) -
      ∑ p ∈ range (⌊x⌋₊ + 1),
        if s145c_lpfAdmissible x p then s145c_bucketModel x p else 0| ≤ δ / 2 := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc (∑ p ∈ range (⌊x⌋₊ + 1),
          |(if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0) -
            (if s145c_lpfAdmissible x p then s145c_bucketModel x p else 0)|)
        ≤ ∑ p ∈ range (⌊x⌋₊ + 1),
          (δ / (2 * C)) * (if s145c_lpfAdmissible x p then 1 / (p : ℝ) else 0) := by
          refine sum_le_sum fun p _ => ?_
          split_ifs with hp
          · have := h2 p hp
            rw [mul_one_div]; exact this
          · simp
      _ = (δ / (2 * C)) * ∑ p ∈ range (⌊x⌋₊ + 1),
          (if s145c_lpfAdmissible x p then 1 / (p : ℝ) else 0) := by rw [mul_sum]
      _ ≤ (δ / (2 * C)) * C := by gcongr
      _ = δ / 2 := by field_simp
  rw [s145c_compositeModelSum_eq]
  have := abs_sub_le (compositeMean x)
    (∑ p ∈ range (⌊x⌋₊ + 1), if s145c_lpfAdmissible x p then s145c_bucketMean x p else 0)
    (∑ p ∈ range (⌊x⌋₊ + 1), if s145c_lpfAdmissible x p then s145c_bucketModel x p else 0)
  linarith

end LeanLab.Ternary.MMS.Task581

