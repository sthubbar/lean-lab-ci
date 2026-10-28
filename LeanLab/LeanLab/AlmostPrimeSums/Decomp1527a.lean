/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file a of three.

The linear sieve machinery behind Chen's theorem, part 1: the Buchstab identity and its
iteration on a finite set, and the linear sieve functions `F`, `f` of Jurkat-Richert, written
in closed form on the ranges `0 < s ≤ 5` for `F` and `0 < s ≤ 4` for `f`:
  `F(s) = 2e^γ/s` (0 < s ≤ 3),  `F(s) = (2e^γ/s)(1 + ∫_2^{s-1} log(t-1)/t dt)` (3 ≤ s ≤ 5),
  `f(s) = 0` (0 < s ≤ 2),       `f(s) = 2e^γ log(s-1)/s` (2 ≤ s ≤ 4),
Halberstam-Richert, Sieve Methods, ch. 8, (8.2.1) to (8.2.4) and Lemma 8.2 and 8.3;
Iwaniec-Kowalski, Analytic Number Theory, Section 6.4 and (11.62), (11.63).
The Lean definitions `Fsieve`, `fsieve` agree with these on the stated ranges; outside them they
are placeholders and nothing here claims the delay-differential equations there.

Numerical values (mpmath, 20 digits): f(3) = 0.82303, f(4) = 0.97835, F(3) = 1.18738,
F(4) = 1.02164, F(5) = 1.00174, ∫_2^3 log(t-1)/t dt = 0.147220677, γ = 0.5772156649.

AI-written Lean code, Claude, 2026-10-25.
AI wrote the proof completions in CODEX task146 with OpenAI Codex, 2026-10-28. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib
import LeanLab.ChenExplicit.GammaBounds

namespace LeanLab.AlmostPrimeSums.Decomp1527a
open Finset Real
attribute [local instance] Classical.propDecidable

/-! ### 1. The Buchstab identity on a finite set -/

/-- `S(A, z)`: the number of `n ∈ A` with no prime factor `p < z`. -/
noncomputable def siftCount (A : Finset ℕ) (z : ℝ) : ℕ :=
  #(A.filter fun n => ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n)

/-- The primes `p` with `w ≤ p < z`. -/
noncomputable def primesIco (w z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter fun p => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z

/-- `A_d`, the elements of `A` divisible by `d`. -/
def multiples (A : Finset ℕ) (d : ℕ) : Finset ℕ := A.filter (d ∣ ·)

/-- `S(A, z)` is antitone in `z`. -/
theorem siftCount_anti (A : Finset ℕ) {w z : ℝ} (hwz : w ≤ z) : siftCount A z ≤ siftCount A w := by
  unfold siftCount
  refine Finset.card_le_card fun n hn => ?_
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, fun p hp hpw => hn.2 p hp (lt_of_lt_of_le hpw hwz)⟩

/-- LEAF. Buchstab identity: for `w ≤ z`,
`S(A, w) = S(A, z) + Σ_{w ≤ p < z} S(A_p, p)`; each `n` counted on the left and not in `S(A,z)`
has a least prime factor `p ∈ [w, z)`. Halberstam-Richert ch. 1, (1.4.5) style, and
Iwaniec-Kowalski (6.4) with `P(w, z)`. Unit U-1527. -/
theorem buchstab_identity (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    siftCount A w = siftCount A z + ∑ p ∈ primesIco w z, siftCount (multiples A p) p := by
  classical
  let B : ℝ → Finset ℕ := fun t =>
    A.filter fun n => ∀ p : ℕ, p.Prime → (p : ℝ) < t → ¬ p ∣ n
  let C : ℕ → Finset ℕ := fun p =>
    (multiples A p).filter fun n => ∀ q : ℕ, q.Prime → (q : ℝ) < p → ¬ q ∣ n
  have hdisj : (primesIco w z : Set ℕ).PairwiseDisjoint C := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [C, multiples, Finset.mem_filter] at hn hm
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hqq := (Finset.mem_filter.mp hq).2.1
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact hm.2 p hpp (by exact_mod_cast hlt) hn.1.2
    · exact hn.2 q hqq (by exact_mod_cast hlt) hm.1.2
  have hdisj' : Disjoint (B z) ((primesIco w z).biUnion C) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨p, hp, hnp⟩ := Finset.mem_biUnion.mp hm
    have hp' := (Finset.mem_filter.mp hp).2
    exact (Finset.mem_filter.mp hn).2 p hp'.1 hp'.2.2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hnp).1).2
  have hpartition : B w = B z ∪ (primesIco w z).biUnion C := by
    ext n
    simp only [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro hn
      by_cases hz : n ∈ B z
      · exact Or.inl hz
      · right
        have hnA := (Finset.mem_filter.mp hn).1
        have hnw := (Finset.mem_filter.mp hn).2
        have hex : ∃ q : ℕ, q.Prime ∧ (q : ℝ) < z ∧ q ∣ n := by
          simp only [B, Finset.mem_filter, hnA, true_and, not_forall,
            not_imp, not_not] at hz
          obtain ⟨q, hq, hqz, hqn⟩ := hz
          exact ⟨q, hq, hqz, hqn⟩
        obtain ⟨q, hq, hqz, hqn⟩ := hex
        have hn1 : n ≠ 1 := by rintro rfl; exact hq.not_dvd_one hqn
        have hprime := Nat.minFac_prime hn1
        have hdvd := Nat.minFac_dvd n
        have hmin := Nat.minFac_le_of_dvd hq.two_le hqn
        have hz' : (n.minFac : ℝ) < z := lt_of_le_of_lt (by exact_mod_cast hmin) hqz
        have hw' : w ≤ (n.minFac : ℝ) := by
          by_contra h
          exact hnw _ hprime (lt_of_not_ge h) hdvd
        refine ⟨n.minFac, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hz'),
            hprime, hw', hz'⟩
        · simp only [C, multiples, Finset.mem_filter]
          refine ⟨⟨hnA, hdvd⟩, ?_⟩
          intro r hr hrlt hrd
          have := Nat.minFac_le_of_dvd hr.two_le hrd
          have : (n.minFac : ℝ) ≤ r := by exact_mod_cast this
          linarith
    · rintro (hn | ⟨p, hp, hn⟩)
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
          fun q hq hqw => (Finset.mem_filter.mp hn).2 q hq (hqw.trans_le hwz)⟩
      · have hwp := (Finset.mem_filter.mp hp).2.2.1
        have hn' := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn'.1).1,
          fun q hq hqw => hn'.2 q hq (hqw.trans_le hwp)⟩
  change #(B w) = #(B z) + ∑ p ∈ primesIco w z, #(C p)
  rw [hpartition, Finset.card_union_of_disjoint hdisj', Finset.card_biUnion hdisj]

/-- LEAF. Iterated Buchstab identity, two steps: for `w ≤ z`,
`S(A,z) = S(A,w) − Σ_{w≤p<z} S(A_p,w) + Σ_{w≤q<p<z} S(A_{pq},q)`, from `buchstab_identity`
applied to `A` and then to each `A_p` between `w` and `p`, with `(A_p)_q = A_{pq}` for primes
`q < p`. Iwaniec-Kowalski (6.5); Halberstam-Richert ch. 8, proof of Lemma 8.1. Unit U-1527. -/
theorem buchstab_iterated (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A z : ℤ) = siftCount A w - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      + ∑ p ∈ primesIco w z, ∑ q ∈ primesIco w p, (siftCount (multiples A (p * q)) q : ℤ) := by
  classical
  have h := buchstab_identity A w z hwz
  have hp : ∀ p ∈ primesIco w z,
      (siftCount (multiples A p) w : ℤ) = siftCount (multiples A p) p +
        ∑ q ∈ primesIco w p, (siftCount (multiples A (p * q)) q : ℤ) := by
    intro p hp
    have hwp := (Finset.mem_filter.mp hp).2.2.1
    have h' := buchstab_identity (multiples A p) w p hwp
    have hm : ∀ q ∈ primesIco w p, multiples (multiples A p) q = multiples A (p * q) := by
      intro q hq
      have hpp := (Finset.mem_filter.mp hp).2.1
      have hqq := (Finset.mem_filter.mp hq).2.1
      have hqp : q < p := by exact_mod_cast (Finset.mem_filter.mp hq).2.2.2
      have hcop := (Nat.coprime_primes hpp hqq).mpr (ne_of_gt hqp)
      ext n
      simp only [multiples, Finset.mem_filter]
      exact ⟨fun hn => ⟨hn.1.1, hcop.mul_dvd_of_dvd_of_dvd hn.1.2 hn.2⟩,
        fun hn => ⟨⟨hn.1, dvd_of_mul_right_dvd hn.2⟩, dvd_of_mul_left_dvd hn.2⟩⟩
    have h'' : (siftCount (multiples A p) w : ℤ) = siftCount (multiples A p) p +
        ∑ q ∈ primesIco w p, (siftCount (multiples (multiples A p) q) q : ℤ) := by
      exact_mod_cast h'
    rw [h'']
    congr 1
    exact Finset.sum_congr rfl fun q hq => by rw [hm q hq]
  have hs := Finset.sum_congr rfl hp
  rw [Finset.sum_add_distrib] at hs
  have h' : (siftCount A w : ℤ) = siftCount A z +
      ∑ p ∈ primesIco w z, (siftCount (multiples A p) p : ℤ) := by exact_mod_cast h
  linarith

/-- Buchstab lower inequality `S(A,z) ≥ S(A,w) − Σ_{w≤p<z} S(A_p,w)`, from the identity and
`S(A_p, p) ≤ S(A_p, w)`. Proved here from the leaf `buchstab_identity`. -/
theorem buchstab_lower (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A w : ℤ) - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      ≤ siftCount A z := by
  have h := buchstab_identity A w z hwz
  have hle : ∑ p ∈ primesIco w z, (siftCount (multiples A p) p : ℤ)
      ≤ ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hwp : w ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.2.1
    exact_mod_cast siftCount_anti _ hwp
  have h' : (siftCount A w : ℤ) = siftCount A z
      + ∑ p ∈ primesIco w z, (siftCount (multiples A p) p : ℤ) := by exact_mod_cast h
  linarith

/-- Buchstab upper inequality
`S(A,z) ≤ S(A,w) − Σ_{w≤p<z} S(A_p,w) + Σ_{w≤q<p<z} S(A_{pq},w)`, from the leaf
`buchstab_iterated` and monotonicity. -/
theorem buchstab_upper (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A z : ℤ) ≤ siftCount A w - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      + ∑ p ∈ primesIco w z, ∑ q ∈ primesIco w p, (siftCount (multiples A (p * q)) w : ℤ) := by
  rw [buchstab_iterated A w z hwz]
  gcongr with p hp q hq
  have hwq : w ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2.2.1
  exact_mod_cast siftCount_anti _ hwq

/-- Vacuity of the Buchstab setting: on `A = {1, …, 10}`, `primesIco 2 4 = {2, 3}`. -/
example : (2 : ℕ) ∈ primesIco 2 4 ∧ (3 : ℕ) ∈ primesIco 2 4 := by
  unfold primesIco
  refine ⟨?_, ?_⟩ <;> simp only [Finset.mem_filter, Finset.mem_range] <;>
    refine ⟨?_, by norm_num, by norm_num, by norm_num⟩ <;>
    · rw [show ⌈(4 : ℝ)⌉₊ = 4 by norm_num]; norm_num

/-! ### 2. The linear sieve functions `F` and `f` -/

/-- Jurkat-Richert's upper function `F(s)`, closed form valid for `0 < s ≤ 5`. -/
noncomputable def Fsieve (s : ℝ) : ℝ :=
  if s ≤ 3 then 2 * exp eulerMascheroniConstant / s
  else 2 * exp eulerMascheroniConstant / s * (1 + ∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t)

/-- Jurkat-Richert's lower function `f(s)`, closed form valid for `0 < s ≤ 4`. -/
noncomputable def fsieve (s : ℝ) : ℝ :=
  if s ≤ 2 then 0 else 2 * exp eulerMascheroniConstant * log (s - 1) / s

/-- `f(2) = 0`. -/
theorem fsieve_two : fsieve 2 = 0 := by simp [fsieve]

/-- `F(2) = e^γ`. -/
theorem Fsieve_two : Fsieve 2 = exp eulerMascheroniConstant := by
  rw [Fsieve, if_pos (by norm_num)]; ring

/-- `F(3) = 2e^γ/3`. -/
theorem Fsieve_three : Fsieve 3 = 2 * exp eulerMascheroniConstant / 3 := by
  rw [Fsieve, if_pos le_rfl]

/-- `f(3) = 2e^γ log 2 / 3`. -/
theorem fsieve_three : fsieve 3 = 2 * exp eulerMascheroniConstant * log 2 / 3 := by
  rw [fsieve, if_neg (by norm_num)]; norm_num

/-- `f(4) = e^γ log 3 / 2`. -/
theorem fsieve_four : fsieve 4 = exp eulerMascheroniConstant * log 3 / 2 := by
  rw [fsieve, if_neg (by norm_num)]; norm_num; ring

/-- `F(4) = (e^γ/2)(1 + ∫_2^3 log(t-1)/t dt)`. -/
theorem Fsieve_four : Fsieve 4 = exp eulerMascheroniConstant / 2 *
    (1 + ∫ t in (2 : ℝ)..3, log (t - 1) / t) := by
  rw [Fsieve, if_neg (by norm_num)]
  have : (4 : ℝ) - 1 = 3 := by norm_num
  rw [this]; ring

/-- LEAF. Delay-differential equation of `f`: `(s f(s))' = F(s-1)` for `2 < s < 4`; here
`s f(s) = 2e^γ log(s-1)` and `F(s-1) = 2e^γ/(s-1)`. Halberstam-Richert (8.2.4);
Iwaniec-Kowalski (11.63). Unit U-1527. -/
theorem fsieve_hasDerivAt (s : ℝ) (h2 : 2 < s) (h4 : s < 4) :
    HasDerivAt (fun t => t * fsieve t) (Fsieve (s - 1)) s := by
  have hs : s ≠ 0 := by linarith
  have hd := (((hasDerivAt_id s).sub_const 1).log (by linarith : s - 1 ≠ 0)).const_mul
    (2 * exp eulerMascheroniConstant)
  have heq : (fun t => t * fsieve t) =ᶠ[nhds s]
      (fun t => 2 * exp eulerMascheroniConstant * log (t - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds h2] with t ht
    change 2 < t at ht
    rw [fsieve, if_neg (not_le.mpr ht)]
    field_simp [show t ≠ 0 by linarith [ht]]
  have hd' := hd.congr_of_eventuallyEq heq
  convert hd' using 1
  rw [Fsieve, if_pos (by linarith)]
  simp only [id_eq]
  ring

/-- Calculus helper for the closed form in HR 8.2.3: the primitive has its expected derivative. -/
theorem sieve_primitive_hasDerivAt (s : ℝ) (hs : 2 ≤ s) :
    HasDerivAt (fun u => ∫ t in (2 : ℝ)..u, log (t - 1) / t)
      (log (s - 1) / s) s := by
  have hc : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.Ioi 1) := by
    intro t ht
    change 1 < t at ht
    exact (((continuousAt_id.sub continuousAt_const).log
      (by linarith [ht] : t - 1 ≠ 0)).div continuousAt_id
      (by linarith [ht] : t ≠ 0)).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume 2 s := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro t ht
    rw [Set.uIcc_of_le hs] at ht
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht.1
  have hcs := hc.continuousAt (isOpen_Ioi.mem_nhds (by linarith : (1 : ℝ) < s))
  have hm := hc.stronglyMeasurableAtFilter (μ := MeasureTheory.volume) isOpen_Ioi s (by linarith : (1 : ℝ) < s)
  exact intervalIntegral.integral_hasDerivAt_right hi hm hcs

/-- LEAF. Delay-differential equation of `F`: `(s F(s))' = f(s-1)` for `3 < s < 5`, by the
fundamental theorem of calculus for `∫_2^{s-1} log(t-1)/t dt`. Halberstam-Richert (8.2.3);
Iwaniec-Kowalski (11.62). Unit U-1527. -/
theorem Fsieve_hasDerivAt (s : ℝ) (h3 : 3 < s) (h5 : s < 5) :
    HasDerivAt (fun t => t * Fsieve t) (fsieve (s - 1)) s := by
  have hd := ((sieve_primitive_hasDerivAt (s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)).const_add 1
  have hd' := hd.const_mul (2 * exp eulerMascheroniConstant)
  have heq : (fun t => t * Fsieve t) =ᶠ[nhds s]
      (fun t => 2 * exp eulerMascheroniConstant *
        (1 + ∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds h3] with t ht
    change 3 < t at ht
    rw [Fsieve, if_neg (not_le.mpr ht)]
    field_simp [show t ≠ 0 by linarith [ht]]
  convert hd'.congr_of_eventuallyEq heq using 1
  rw [fsieve, if_neg (by linarith)]
  simp only [id_eq, mul_one]
  ring

/-- LEAF. `f` is continuous on `s > 0`; at `s = 2` both pieces vanish.
Halberstam-Richert ch. 8, Lemma 8.2. Unit U-1527. -/
theorem fsieve_continuousOn : ContinuousOn fsieve (Set.Ioi 0) := by
  unfold fsieve
  apply ContinuousOn.if
  · intro a ha
    have ha2 : a = 2 := by simpa only [frontier_Iic, Set.mem_singleton_iff] using
      (show a ∈ frontier (Set.Iic 2) from ha.2)
    subst a
    norm_num
  · exact continuousOn_const
  · intro x hx
    have hx2 : 2 ≤ x := by
      have hh : closure {a : ℝ | ¬a ≤ 2} ⊆ Set.Ici 2 :=
        closure_minimal (fun a ha => (not_le.mp ha).le) isClosed_Ici
      exact hh hx.2
    exact ((continuousAt_const.mul
      ((continuousAt_id.sub continuousAt_const).log (by linarith : x - 1 ≠ 0))).div
      continuousAt_id (by linarith : x ≠ 0)).continuousWithinAt

/-- LEAF. `F` is continuous on `s > 0`; at `s = 3` the integral `∫_2^{2}` vanishes.
Halberstam-Richert ch. 8, Lemma 8.2. Unit U-1527. -/
theorem Fsieve_continuousOn : ContinuousOn Fsieve (Set.Ioi 0) := by
  unfold Fsieve
  apply ContinuousOn.if
  · intro a ha
    have ha3 : a = 3 := by simpa only [frontier_Iic, Set.mem_singleton_iff] using
      (show a ∈ frontier (Set.Iic 3) from ha.2)
    subst a
    norm_num
  · intro x hx
    exact (continuousAt_const.div continuousAt_id (ne_of_gt hx.1)).continuousWithinAt
  · intro x hx
    have hx3 : 3 ≤ x := by
      have hh : closure {a : ℝ | ¬a ≤ 3} ⊆ Set.Ici 3 :=
        closure_minimal (fun a ha => (not_le.mp ha).le) isClosed_Ici
      exact hh hx.2
    have hsub : ContinuousAt (fun t : ℝ => t - 1) x :=
      continuousAt_id.sub continuousAt_const
    have hc : ContinuousAt (fun t : ℝ =>
        ∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) x :=
      (sieve_primitive_hasDerivAt (x - 1) (by linarith)).continuousAt.comp
        (f := fun t : ℝ => t - 1) hsub
    exact ((continuousAt_const.div continuousAt_id (ne_of_gt hx.1)).mul
      (continuousAt_const.add hc)).continuousWithinAt

/-- LEAF. `f` is strictly increasing on `[2, 4]`: `f(2) = 0 < f(s)` for `s > 2`, and
`d/ds (log(s-1)/s) > 0` there since `log(s-1) ≤ log 3 < 4/3 ≤ s/(s-1)`.
Halberstam-Richert ch. 8, Lemma 8.3. Unit U-1527. -/
theorem fsieve_strictMonoOn : StrictMonoOn fsieve (Set.Icc 2 4) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 2 4)
    (fsieve_continuousOn.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))
  intro s hs
  rw [interior_Icc] at hs
  have h2 : 2 < s := hs.1
  have h4 : s < 4 := hs.2
  have hs0 : s ≠ 0 := by linarith
  have hsm : 0 < s - 1 := by linarith
  have hd := ((((hasDerivAt_id s).sub_const 1).log (ne_of_gt hsm)).const_mul
    (2 * exp eulerMascheroniConstant)).div (hasDerivAt_id s) hs0
  simp only [id_eq] at hd
  have heq : fsieve =ᶠ[nhds s]
      (fun t => 2 * exp eulerMascheroniConstant * log (t - 1) / t) := by
    filter_upwards [isOpen_Ioi.mem_nhds h2] with t ht
    exact if_neg (not_le.mpr ht)
  rw [(hd.congr_of_eventuallyEq heq).deriv]
  apply div_pos _ (sq_pos_of_ne_zero hs0)
  have hl : log (s - 1) < 4 / 3 := by
    have hle := log_le_log hsm (show s - 1 ≤ 3 by linarith)
    linarith [log_three_lt_d9]
  have hmul := mul_lt_mul_of_pos_right hl hsm
  have hls : log (s - 1) < s / (s - 1) := by
    apply (lt_div_iff₀ hsm).mpr
    nlinarith
  have hk : 0 < 2 * exp eulerMascheroniConstant := by positivity
  have hh := mul_lt_mul_of_pos_left hls hk
  convert sub_pos.mpr hh using 1 <;> ring

/-- The 16 term logarithm polynomial used to check HR 8.2.3 numerically. -/
noncomputable def sieveLogApprox (t : ℝ) : ℝ :=
  log 2 - ∑ i ∈ range 16, ((3 - t) / 2) ^ (i + 1) / (i + 1)

/-- An explicit primitive of the logarithm polynomial divided by t. -/
noncomputable def sieveLogPrimitive (t : ℝ) : ℝ :=
  (log 2 + (-22320892047 / 149946368 : ℝ)) * log t +
  (42981185 / 65536 : ℝ) * t ^ 1 +
  (-186601327 / 262144 : ℝ) * t ^ 2 +
  (387354953 / 589824 : ℝ) * t ^ 3 +
  (-505465927 / 1048576 : ℝ) * t ^ 4 +
  (461756693 / 1638400 : ℝ) * t ^ 5 +
  (-312021403 / 2359296 : ℝ) * t ^ 6 +
  (160842989 / 3211264 : ℝ) * t ^ 7 +
  (-64330531 / 4194304 : ℝ) * t ^ 8 +
  (20109539 / 5308416 : ℝ) * t ^ 9 +
  (-4909741 / 6553600 : ℝ) * t ^ 10 +
  (928091 / 7929856 : ℝ) * t ^ 11 +
  (-133333 / 9437184 : ℝ) * t ^ 12 +
  (14087 / 11075584 : ℝ) * t ^ 13 +
  (-1033 / 12845056 : ℝ) * t ^ 14 +
  (47 / 14745600 : ℝ) * t ^ 15 +
  (-1 / 16777216 : ℝ) * t ^ 16

/-- The explicit primitive differentiates to the approximating integrand. -/
theorem sieveLogPrimitive_hasDerivAt (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt sieveLogPrimitive (sieveLogApprox t / t) t := by
  have hd := ((hasDerivAt_log ht).const_mul (log 2 + (-22320892047 / 149946368 : ℝ)))
    |>.add (((hasDerivAt_id t).pow 1).const_mul (42981185 / 65536 : ℝ))
    |>.add (((hasDerivAt_id t).pow 2).const_mul (-186601327 / 262144 : ℝ))
    |>.add (((hasDerivAt_id t).pow 3).const_mul (387354953 / 589824 : ℝ))
    |>.add (((hasDerivAt_id t).pow 4).const_mul (-505465927 / 1048576 : ℝ))
    |>.add (((hasDerivAt_id t).pow 5).const_mul (461756693 / 1638400 : ℝ))
    |>.add (((hasDerivAt_id t).pow 6).const_mul (-312021403 / 2359296 : ℝ))
    |>.add (((hasDerivAt_id t).pow 7).const_mul (160842989 / 3211264 : ℝ))
    |>.add (((hasDerivAt_id t).pow 8).const_mul (-64330531 / 4194304 : ℝ))
    |>.add (((hasDerivAt_id t).pow 9).const_mul (20109539 / 5308416 : ℝ))
    |>.add (((hasDerivAt_id t).pow 10).const_mul (-4909741 / 6553600 : ℝ))
    |>.add (((hasDerivAt_id t).pow 11).const_mul (928091 / 7929856 : ℝ))
    |>.add (((hasDerivAt_id t).pow 12).const_mul (-133333 / 9437184 : ℝ))
    |>.add (((hasDerivAt_id t).pow 13).const_mul (14087 / 11075584 : ℝ))
    |>.add (((hasDerivAt_id t).pow 14).const_mul (-1033 / 12845056 : ℝ))
    |>.add (((hasDerivAt_id t).pow 15).const_mul (47 / 14745600 : ℝ))
    |>.add (((hasDerivAt_id t).pow 16).const_mul (-1 / 16777216 : ℝ))
  convert hd using 1 <;> try rfl
  simp only [sieveLogApprox, id_eq, sum_range_succ, sum_range_zero, Nat.cast_add, Nat.cast_one]
  norm_num
  field_simp [ht]
  ring

/-- Uniform series error for the logarithm in the upper sieve closed form. -/
theorem sieveLogApprox_error (t : ℝ) (h2 : 2 ≤ t) (h4 : t ≤ 4) :
    |log (t - 1) - sieveLogApprox t| ≤ 1 / 65536 := by
  have hx : |(3 - t) / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hh := Real.abs_log_sub_add_sum_range_le
    (x := (3 - t) / 2) (by linarith) 16
  have he : log (1 - (3 - t) / 2) = log (t - 1) - log 2 := by
    rw [← log_div (by linarith) (by norm_num)]
    congr 1
    ring
  rw [he, add_comm] at hh
  have he' : log (t - 1) - sieveLogApprox t = log (t - 1) - log 2 +
      ∑ i ∈ range 16, ((3 - t) / 2) ^ (i + 1) / (i + 1) := by dsimp [sieveLogApprox]; ring
  rw [he']
  apply hh.trans
  calc |(3 - t) / 2| ^ (16 + 1) / (1 - |(3 - t) / 2|)
      ≤ (1 / 2 : ℝ) ^ (16 + 1) / (1 / 2) := by gcongr <;> linarith
    _ = 1 / 65536 := by norm_num

/-- An integral error bound for the explicit primitive on the full upper sieve range. -/
theorem sieve_integral_error (b : ℝ) (h2 : 2 ≤ b) (h4 : b ≤ 4) :
    |(∫ t in (2 : ℝ)..b, log (t - 1) / t) -
      (sieveLogPrimitive b - sieveLogPrimitive 2)| ≤ (b - 2) / 131072 := by
  have hc : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.Icc 2 b) := by
    intro t ht
    exact (((continuousAt_id.sub continuousAt_const).log
      (by linarith [ht.1] : t - 1 ≠ 0)).div continuousAt_id
      (by linarith [ht.1] : t ≠ 0)).continuousWithinAt
  have hp : ContinuousOn (fun t => sieveLogApprox t / t) (Set.Icc 2 b) := by
    have hP : Continuous sieveLogApprox := by unfold sieveLogApprox; fun_prop
    intro t ht
    exact (hP.continuousAt.div continuousAt_id
      (by linarith [ht.1] : t ≠ 0)).continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (2 : ℝ)) (b := b) (fun t ht => sieveLogPrimitive_hasDerivAt t (by
      rw [Set.uIcc_of_le h2] at ht; linarith [ht.1])) (hp.intervalIntegrable_of_Icc h2)
  have heint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (2 : ℝ)) (b := b)
    (f := fun t => log (t - 1) / t - sieveLogApprox t / t)
    (C := (1 / 131072 : ℝ)) (by
      intro t ht
      rw [Set.uIoc_of_le h2] at ht
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos (by linarith [ht.1] : 0 < t)]
      have he := sieveLogApprox_error t ht.1.le (ht.2.trans h4)
      calc |log (t - 1) - sieveLogApprox t| / t ≤ (1 / 65536 : ℝ) / 2 := by
            gcongr <;> linarith [ht.1]
        _ = 1 / 131072 := by norm_num)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc h2) (hp.intervalIntegrable_of_Icc h2),
    Real.norm_eq_abs, hi, abs_of_nonneg (sub_nonneg.mpr h2)] at heint
  convert heint using 1 <;> ring

/-- Elementary exponential bounds used in the closed form sieve values. -/
theorem sieve_exp_gamma_bounds :
    1.781 < exp eulerMascheroniConstant ∧ exp eulerMascheroniConstant < 1.7813 := by
  have hglo := LeanLab.ChenExplicit.Gamma.gamma_gt
  have hghi := LeanLab.ChenExplicit.Gamma.gamma_lt
  have hlo := Real.sum_le_exp_of_nonneg (x := (0.5772 : ℝ)) (by norm_num) 8
  have hhi := Real.exp_bound' (x := (0.5773 : ℝ))
    (by norm_num) (by norm_num) (n := 10) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hlo hhi
  norm_num at hlo hhi
  have hlow : exp (0.5772 : ℝ) < exp eulerMascheroniConstant := exp_lt_exp.mpr (by linarith)
  have hhigh : exp eulerMascheroniConstant < exp (0.5773 : ℝ) := exp_lt_exp.mpr (by linarith)
  constructor <;> linarith

/-- The lower closed form is below one at the right endpoint. -/
theorem fsieve_four_lt_one : fsieve 4 < 1 := by
  rw [fsieve_four]
  have he := sieve_exp_gamma_bounds.2
  have hl := log_three_lt_d9
  have hlog : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have h1 := mul_lt_mul_of_pos_right he hlog
  have h2 := mul_lt_mul_of_pos_left hl (by norm_num : (0 : ℝ) < 1.7813)
  linarith

/-- A rigorous lower bound for the integral at the endpoint used by F of 5. -/
theorem sieve_integral_four_lower :
    (0.4060 : ℝ) < ∫ t in (2 : ℝ)..4, log (t - 1) / t := by
  have he := sieve_integral_error 4 (by norm_num) (by norm_num)
  have h2lo := log_two_gt_d9
  have h2hi := log_two_lt_d9
  have hKneg : log 2 + (-22320892047 / 149946368 : ℝ) ≤ 0 := by linarith
  have hL : (0.6931471803 + (-22320892047 / 149946368 : ℝ)) * 0.6931471808 ≤ (log 2 + (-22320892047 / 149946368 : ℝ)) * log 2 := by
    calc _ ≤ (log 2 + (-22320892047 / 149946368 : ℝ)) * 0.6931471808 :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonpos_left h2hi.le hKneg
  norm_num [sieveLogPrimitive, log_four_eq] at he
  norm_num at hL
  rw [abs_le] at he
  nlinarith [he.1, he.2]

/-- The upper closed form is above one at its right endpoint. -/
theorem Fsieve_five_gt_one : 1 < Fsieve 5 := by
  have he := sieve_exp_gamma_bounds.1
  have hi := sieve_integral_four_lower
  have hp := mul_pos (sub_pos.mpr he)
    (show 0 < 1 + ∫ t in (2 : ℝ)..4, log (t - 1) / t by linarith)
  rw [Fsieve, if_neg (by norm_num)]
  norm_num
  nlinarith

/-- The integrated upper delay equation and monotonicity of the lower closed form. -/
theorem sieve_F_increment_le (a b : ℝ) (ha : 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    b * Fsieve b - a * Fsieve a ≤ (b - a) * fsieve 4 := by
  have hsub : ContinuousOn (fun t : ℝ => t - 1) (Set.Icc a b) :=
    continuousOn_id.sub continuousOn_const
  have hcf : ContinuousOn (fun t : ℝ => fsieve (t - 1)) (Set.Icc a b) :=
    fsieve_continuousOn.comp hsub (by
      intro t ht
      change 0 < t - 1
      linarith [ht.1])
  have hcF : ContinuousOn (fun t : ℝ => t * Fsieve t) (Set.Icc a b) :=
    continuousOn_id.mul (Fsieve_continuousOn.mono (by
      intro t ht
      change 0 < t
      linarith [ht.1]))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcF
    (fun t ht => Fsieve_hasDerivAt t (by linarith [ht.1]) (by linarith [ht.2]))
    (hcf.intervalIntegrable_of_Icc hab)
  rw [← hi]
  calc (∫ t in a..b, fsieve (t - 1)) ≤ ∫ t in a..b, fsieve 4 := by
        apply intervalIntegral.integral_mono_on hab
          (hcf.intervalIntegrable_of_Icc hab) intervalIntegrable_const
        intro t ht
        exact fsieve_strictMonoOn.monotoneOn
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
          ⟨by norm_num, le_rfl⟩ (by linarith [ht.2])
    _ = (b - a) * fsieve 4 := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- The upper closed form stays above one on its integral branch. -/
theorem Fsieve_gt_one_upper (s : ℝ) (h3 : 3 ≤ s) (h5 : s ≤ 5) : 1 < Fsieve s := by
  have hi := sieve_F_increment_le s 5 h3 h5 (by norm_num)
  have hsmall : (5 - s) * fsieve 4 ≤ 5 - s := by
    have hh := mul_le_mul_of_nonneg_left fsieve_four_lt_one.le (sub_nonneg.mpr h5)
    simpa using hh
  have hh : s * 1 < s * Fsieve s := by nlinarith [Fsieve_five_gt_one]
  exact (mul_lt_mul_iff_right₀ (by linarith : 0 < s)).mp hh

/-- LEAF. `F` is strictly decreasing on `(0, 5]`: `2e^γ/s` on `(0,3]`, and on `[3,5]`
`s F'(s) = f(s-1) − F(s) < 0` since `f(s-1) ≤ f(4) < 1 < F(5) ≤ F(s)`.
Halberstam-Richert ch. 8, Lemma 8.3. Unit U-1527. -/
theorem Fsieve_strictAntiOn : StrictAntiOn Fsieve (Set.Ioc 0 5) := by
  have hk : 0 < 2 * exp eulerMascheroniConstant := by positivity
  have hupper : StrictAntiOn Fsieve (Set.Icc 3 5) := by
    intro a ha b hb hab
    have hi := sieve_F_increment_le a b ha.1 hab.le hb.2
    have hpos := Fsieve_gt_one_upper a ha.1 ha.2
    have hsmall := mul_lt_mul_of_pos_left (fsieve_four_lt_one.trans hpos) (sub_pos.mpr hab)
    have hh : b * Fsieve b < b * Fsieve a := by nlinarith
    exact (mul_lt_mul_iff_right₀ (by linarith [hb.1] : 0 < b)).mp hh
  intro x hx y hy hxy
  by_cases hy3 : y ≤ 3
  · have hx3 : x ≤ 3 := hxy.le.trans hy3
    rw [Fsieve, if_pos hy3, Fsieve, if_pos hx3]
    exact div_lt_div_of_pos_left hk hx.1 hxy
  · by_cases hx3 : x ≤ 3
    · have hy' : Fsieve y < Fsieve 3 := hupper ⟨le_rfl, by norm_num⟩
        ⟨(not_le.mp hy3).le, hy.2⟩ (not_le.mp hy3)
      have hx' : Fsieve 3 ≤ Fsieve x := by
        rw [Fsieve_three, Fsieve, if_pos hx3]
        exact div_le_div_of_nonneg_left hk.le hx.1 hx3
      exact hy'.trans_le hx'
    · exact hupper ⟨(not_le.mp hx3).le, hx.2⟩ ⟨(not_le.mp hy3).le, hy.2⟩ hxy

/-- LEAF. `F(s) > 1` for `0 < s ≤ 5` (true value `F(5) = 1.00174`).
Halberstam-Richert ch. 8, Lemma 8.3, `F(s) > 1`. Unit U-1527. -/
theorem one_lt_Fsieve (s : ℝ) (h0 : 0 < s) (h5 : s ≤ 5) : 1 < Fsieve s := by
  have hle : Fsieve 5 ≤ Fsieve s := Fsieve_strictAntiOn.antitoneOn
    ⟨h0, h5⟩ ⟨by norm_num, le_rfl⟩ h5
  exact Fsieve_five_gt_one.trans_le hle

/-- LEAF. `f(s) < 1` for `0 < s ≤ 4` (true value `f(4) = 0.97835`), needs `e^γ < 2/log 3`.
Halberstam-Richert ch. 8, Lemma 8.3, `f(s) < 1`. Unit U-1527. -/
theorem fsieve_lt_one (s : ℝ) (h0 : 0 < s) (h4 : s ≤ 4) : fsieve s < 1 := by
  by_cases h2 : s ≤ 2
  · rw [fsieve, if_pos h2]
    norm_num
  · exact (fsieve_strictMonoOn.monotoneOn ⟨(not_le.mp h2).le, h4⟩
      ⟨by norm_num, le_rfl⟩ h4).trans_lt fsieve_four_lt_one

/-- LEAF. `0.5772 < γ < 0.5773` (`γ = 0.5772156649`), e.g. from
`eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` with an Euler-Maclaurin correction, or from
`eulerMascheroniConstant_eq_neg_integral_log`. numerics,
Mathlib `Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`. Unit U-1527. -/
theorem eulerMascheroni_bounds :
    0.5772 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.5773 := by
  constructor <;> linarith [LeanLab.ChenExplicit.Gamma.gamma_gt,
    LeanLab.ChenExplicit.Gamma.gamma_lt]

/-- LEAF. `0.1472 < ∫_2^3 log(t-1)/t dt < 0.1473` (value `0.1472206770`), the integral in
`F(4)`; substitute `u = t - 1` to get `∫_1^2 log u/(u+1) du`. Halberstam-Richert (8.2.3).
Unit U-1527. -/
theorem int_F4_bounds :
    0.1472 < ∫ t in (2 : ℝ)..3, log (t - 1) / t ∧ ∫ t in (2 : ℝ)..3, log (t - 1) / t < 0.1473 := by
  have heint := sieve_integral_error 3 (by norm_num) (by norm_num)
  norm_num at heint
  have h2lo := log_two_gt_d9
  have h2hi := log_two_lt_d9
  have h3lo := log_three_gt_d9
  have h3hi := log_three_lt_d9
  have hKneg : log 2 + (-22320892047 / 149946368 : ℝ) ≤ 0 := by linarith
  have hDlo : (1.0986122885 - 0.6931471808 : ℝ) ≤ log 3 - log 2 := by linarith
  have hDhi : log 3 - log 2 ≤ (1.0986122888 - 0.6931471803 : ℝ) := by linarith
  have hL : (0.6931471803 + (-22320892047 / 149946368 : ℝ)) *
      (1.0986122888 - 0.6931471803) ≤
      (log 2 + (-22320892047 / 149946368 : ℝ)) * (log 3 - log 2) := by
    calc _ ≤ (log 2 + (-22320892047 / 149946368 : ℝ)) *
          (1.0986122888 - 0.6931471803) :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonpos_left hDhi hKneg
  have hU : (log 2 + (-22320892047 / 149946368 : ℝ)) * (log 3 - log 2) ≤
      (0.6931471808 + (-22320892047 / 149946368 : ℝ)) *
        (1.0986122885 - 0.6931471808) := by
    calc _ ≤ (log 2 + (-22320892047 / 149946368 : ℝ)) *
          (1.0986122885 - 0.6931471808) := mul_le_mul_of_nonpos_left hDlo hKneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  norm_num [sieveLogPrimitive] at heint
  norm_num at hL hU
  rw [abs_le] at heint
  constructor <;> nlinarith [heint.1, heint.2]

/-- LEAF. Explicit values of the linear sieve functions at `s = 3, 4`:
`0.822 < f(3) < 0.824`, `0.978 < f(4) < 0.979`, `1.187 < F(3) < 1.188`, `1.021 < F(4) < 1.022`
(true values `0.82303, 0.97835, 1.18738, 1.02164`), from the closed forms
`fsieve_three`, `fsieve_four`, `Fsieve_three`, `Fsieve_four` and the two numeric leaves above.
Halberstam-Richert ch. 8, (8.2.1) to (8.2.4); Iwaniec-Kowalski (11.62), (11.63). Unit U-1527. -/
theorem sieve_values :
    (0.822 < fsieve 3 ∧ fsieve 3 < 0.824) ∧ (0.978 < fsieve 4 ∧ fsieve 4 < 0.979) ∧
    (1.187 < Fsieve 3 ∧ Fsieve 3 < 1.188) ∧ (1.021 < Fsieve 4 ∧ Fsieve 4 < 1.022) := by
  have helo := sieve_exp_gamma_bounds.1
  have hehi := sieve_exp_gamma_bounds.2
  have h2lo := log_two_gt_d9
  have h2hi := log_two_lt_d9
  have h3lo := log_three_gt_d9
  have h3hi := log_three_lt_d9
  have hIlo := int_F4_bounds.1
  have hIhi := int_F4_bounds.2
  have hlo2 : (1.781 : ℝ) * 0.6931471803 < exp eulerMascheroniConstant * log 2 :=
    (mul_lt_mul_of_pos_right helo (by norm_num)).trans
      (mul_lt_mul_of_pos_left h2lo (exp_pos _))
  have hhi2 : exp eulerMascheroniConstant * log 2 < (1.7813 : ℝ) * 0.6931471808 :=
    (mul_lt_mul_of_pos_left h2hi (exp_pos _)).trans
      (mul_lt_mul_of_pos_right hehi (by norm_num))
  have hlo3 : (1.781 : ℝ) * 1.0986122885 < exp eulerMascheroniConstant * log 3 :=
    (mul_lt_mul_of_pos_right helo (by norm_num)).trans
      (mul_lt_mul_of_pos_left h3lo (exp_pos _))
  have hhi3 : exp eulerMascheroniConstant * log 3 < (1.7813 : ℝ) * 1.0986122888 :=
    (mul_lt_mul_of_pos_left h3hi (exp_pos _)).trans
      (mul_lt_mul_of_pos_right hehi (by norm_num))
  have hloI : (1.781 : ℝ) * (1 + 0.1472) < exp eulerMascheroniConstant *
      (1 + ∫ t in (2 : ℝ)..3, log (t - 1) / t) :=
    (mul_lt_mul_of_pos_right helo (by norm_num)).trans
      (mul_lt_mul_of_pos_left (by linarith : 1 + (0.1472 : ℝ) <
        1 + ∫ t in (2 : ℝ)..3, log (t - 1) / t) (exp_pos _))
  have hhiI : exp eulerMascheroniConstant * (1 + ∫ t in (2 : ℝ)..3, log (t - 1) / t) <
      (1.7813 : ℝ) * (1 + 0.1473) :=
    (mul_lt_mul_of_pos_left (by linarith :
      1 + (∫ t in (2 : ℝ)..3, log (t - 1) / t) < 1 + (0.1473 : ℝ)) (exp_pos _)).trans
      (mul_lt_mul_of_pos_right hehi (by norm_num))
  simp only [fsieve_three, fsieve_four, Fsieve_three, Fsieve_four]
  constructor
  · constructor <;> nlinarith
  · constructor
    · constructor <;> nlinarith
    · constructor <;> constructor <;> nlinarith

/-! Concrete instances for the task146 statement twins. -/
example : siftCount {0, 1, 6} 1 = siftCount {0, 1, 6} 4 +
    ∑ p ∈ primesIco 1 4, siftCount (multiples {0, 1, 6} p) p :=
  buchstab_identity {0, 1, 6} 1 4 (by norm_num)

example : HasDerivAt (fun t => t * fsieve t) (exp eulerMascheroniConstant) 3 := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Fsieve_two] using
    fsieve_hasDerivAt 3 (by norm_num) (by norm_num)

example : HasDerivAt (fun t => t * Fsieve t) (fsieve 3) 4 := by
  simpa only [show (4 : ℝ) - 1 = 3 by norm_num] using
    Fsieve_hasDerivAt 4 (by norm_num) (by norm_num)

example : ContinuousAt fsieve 2 :=
  fsieve_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))

example : ContinuousAt Fsieve 3 :=
  Fsieve_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))

example : fsieve 2 < fsieve 4 :=
  fsieve_strictMonoOn ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)

example : Fsieve 5 < Fsieve 3 :=
  Fsieve_strictAntiOn ⟨by norm_num, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)

end LeanLab.AlmostPrimeSums.Decomp1527a
