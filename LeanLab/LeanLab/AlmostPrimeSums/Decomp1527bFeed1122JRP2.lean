/-
P0002 J.-R. Chen 1973, unit U-1527 file b, burst-20261122 session S117 split of the MEDIUM leaf
`Decomp1527bFeed1122JR.rosser_mainSum_buchstab`, the Buchstab decomposition of a Rosser sum,
Iwaniec-Kowalski (6.6)-(6.8) and Opera de Cribro Section 6.3, into its two faithful steps:
the regrouping of the failing divisors `d = e f` by their first failure `e`, and the Euler
product `Σ_{f ∣ P(p)} μ(f) g(f) = V(p)`. The parent is proved here as
`rosser_mainSum_buchstab_of_leaves` with exactly the statement of the parent.

AI-written Lean code, Claude, 2026-11-23. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527b

namespace LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JRP2
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
open LeanLab.AlmostPrimeSums.Decomp1527b
attribute [local instance] Classical.propDecidable

/-- `λ_1 = 1` for Rosser's weights. Helper for IK (6.6)-(6.7). -/
theorem rw_one (D : ℝ) (b : Bool) : rosserWeight D b 1 = 1 := by
  simp [rosserWeight, decPrimes]

/-- A nonzero Rosser weight equals `μ(d)`, IK (6.30). -/
theorem rw_eq_moebius_of_ne (D : ℝ) (b : Bool) {d : ℕ} (h : rosserWeight D b d ≠ 0) :
    rosserWeight D b d = (moebius d : ℝ) := by
  unfold rosserWeight at *
  split_ifs at * with h1
  · rfl
  · exact absurd rfl h

/-- Rosser's weights vanish off squarefree `d`, IK (6.30). -/
theorem rw_nonsq (D : ℝ) (b : Bool) {d : ℕ} (h : ¬ Squarefree d) : rosserWeight D b d = 0 := by
  unfold rosserWeight; simp [h]

/-- Removing the least prime of a squarefree `n ≠ 1`, the induction step behind IK (6.6)-(6.7). -/
theorem split_least {n : ℕ} (hn : Squarefree n) (h1 : n ≠ 1) :
    n = n / n.minFac * n.minFac ∧ n / n.minFac < n ∧ Squarefree (n / n.minFac) ∧
    ∀ q ∈ (n / n.minFac).primeFactors, n.minFac < q := by
  have hp : n.minFac.Prime := Nat.minFac_prime h1
  have hn0 : n ≠ 0 := hn.ne_zero
  have hed : n = n / n.minFac * n.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd n)).symm
  have hde : n / n.minFac ∣ n := Nat.div_dvd_of_dvd (Nat.minFac_dvd n)
  refine ⟨hed, Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp.one_lt, hn.squarefree_of_dvd hde, ?_⟩
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hle : n.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le (hqd.trans hde)
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have h2 : n.minFac * n.minFac ∣ n / n.minFac * n.minFac := Nat.mul_dvd_mul_right (h ▸ hqd) _
    rw [← hed] at h2
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hn _ h2))

/-- The divisors of `m p` prime to `p` are the divisors of `m`, when `p` is below every prime of `m`. -/
theorem divisors_filter_not_dvd {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hmin : ∀ q ∈ m.primeFactors, p < q) :
    (m * p).divisors.filter (fun d => ¬ p ∣ d) = m.divisors := by
  have hpm : ¬ p ∣ m := fun h =>
    lt_irrefl p (hmin p (Nat.mem_primeFactors.mpr ⟨hp, h, hm⟩))
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨((Nat.Coprime.dvd_mul_right ((hp.coprime_iff_not_dvd.mpr hpd).symm)).mp hd), hm⟩
  · rintro ⟨hd, -⟩
    exact ⟨⟨hd.mul_right p, mul_ne_zero hm hp.ne_zero⟩, fun h => hpm (h.trans hd)⟩

/-- `μ(d p) g(d p) = -g(p) μ(d) g(d)` for a prime `p ∤ d` and multiplicative `g`. -/
theorem mu_g_mul {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) {d p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d) :
    (moebius (d * p) : ℝ) * g (d * p) = -(g p * ((moebius d : ℝ) * g d)) := by
  have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp,
    hg.map_mul_of_coprime hcop]
  push_cast; ring

/-- Appending a new least prime `p` makes it the least prime factor. -/
theorem minFac_mul_smallest {d p : ℕ} (hd : d ≠ 0) (hp : p.Prime)
    (hmin : ∀ q ∈ d.primeFactors, p < q) : (d * p).minFac = p := by
  have h1 : d * p ≠ 1 := by
    intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h)
  have hq := Nat.minFac_prime h1
  refine le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_left p d)) ?_
  rcases (Nat.Prime.dvd_mul hq).mp (Nat.minFac_dvd (d * p)) with h | h
  · exact (hmin _ (Nat.mem_primeFactors.mpr ⟨hq, h, hd⟩)).le
  · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).ge

/-- One Euler factor of the inner sum `Σ_{f ∣ P(r)} μ(f) g(f)`, IK (6.8). -/
theorem inner_step {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) {m p : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hmin : ∀ q ∈ m.primeFactors, p < q) (r : ℕ) (hr : p < r) :
    ∑ f ∈ (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < r),
        (moebius f : ℝ) * g f =
      (1 - g p) * ∑ f ∈ m.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < r),
        (moebius f : ℝ) * g f := by
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_divisors_pair_of_squarefree_support (m * p) p (mul_ne_zero hm hp.ne_zero) hp
      (dvd_mul_left p m) _ (fun d hd => by simp [moebius_eq_zero_of_not_squarefree hd]),
    divisors_filter_not_dvd hm hp hmin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hfm := Nat.dvd_of_mem_divisors hf
  have hpf : ¬ p ∣ f := fun h => lt_irrefl p
    (hmin p (Nat.mem_primeFactors.mpr ⟨hp, h.trans hfm, hm⟩))
  have hf0 : f ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hf)
  have hpfac : (f * p).primeFactors = f.primeFactors ∪ {p} := by
    rw [Nat.primeFactors_mul hf0 hp.ne_zero, hp.primeFactors]
  have hiff : (∀ q ∈ (f * p).primeFactors, q < r) ↔ ∀ q ∈ f.primeFactors, q < r := by
    rw [hpfac]; simp [hr]
  rw [if_congr hiff rfl rfl, mu_g_mul hg hp hpf]
  split_ifs <;> ring

/-- Induction step for the regrouping identity IK (6.6)-(6.7): adjoining a new least prime `p`. -/
theorem regroup_step (D : ℝ) (b : Bool) {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    {m p : ℕ} (hm : Squarefree m) (hp : p.Prime) (hmin : ∀ q ∈ m.primeFactors, p < q)
    (ih : ∑ d ∈ m.divisors, ((moebius d : ℝ) - rosserWeight D b d) * g d =
      ∑ e ∈ m.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (moebius e : ℝ) * g e *
          ∑ f ∈ m.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < e.minFac),
            (moebius f : ℝ) * g f) :
    ∑ d ∈ (m * p).divisors, ((moebius d : ℝ) - rosserWeight D b d) * g d =
      ∑ e ∈ (m * p).divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (moebius e : ℝ) * g e *
          ∑ f ∈ (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < e.minFac),
            (moebius f : ℝ) * g f := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hn0 : m * p ≠ 0 := mul_ne_zero hm0 hp.ne_zero
  rw [Finset.sum_filter] at ih ⊢
  rw [sum_divisors_pair_of_squarefree_support (m * p) p hn0 hp (dvd_mul_left p m) _
      (fun d hd => by simp [moebius_eq_zero_of_not_squarefree hd, rw_nonsq D b hd]),
    sum_divisors_pair_of_squarefree_support (m * p) p hn0 hp (dvd_mul_left p m) _
      (fun d hd => by simp [moebius_eq_zero_of_not_squarefree hd]),
    divisors_filter_not_dvd hm0 hp hmin]
  let Y : ℕ → ℝ := fun d =>
    if ¬ ((b = true ↔ (decPrimes d).length % 2 = 0) → (d : ℝ) * (p : ℝ) ^ 3 < D)
    then -(g p * (rosserWeight D b d * g d)) else 0
  have hL : ∀ d ∈ m.divisors,
      ((moebius d : ℝ) - rosserWeight D b d) * g d +
        ((moebius (d * p) : ℝ) - rosserWeight D b (d * p)) * g (d * p) =
      (1 - g p) * (((moebius d : ℝ) - rosserWeight D b d) * g d) + Y d := by
    intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdsq : Squarefree d := hm.squarefree_of_dvd hdm
    have hdmin : ∀ q ∈ d.primeFactors, p < q := fun q hq =>
      hmin q (Nat.primeFactors_mono hdm hm0 hq)
    have hpd : ¬ p ∣ d := fun h => lt_irrefl p
      (hdmin p (Nat.mem_primeFactors.mpr ⟨hp, h, hd0⟩))
    have hmg := mu_g_mul hg hp hpd
    have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    simp only [sub_mul]
    rw [hmg, rosserWeight_mul_smallest D b hdsq hp hdmin, hg.map_mul_of_coprime hcop]
    have hwd : rosserWeight D b d ≠ 0 → rosserWeight D b d = (moebius d : ℝ) :=
      rw_eq_moebius_of_ne D b
    simp only [Y]
    split_ifs with hc
    · ring
    · by_cases h0 : rosserWeight D b d = 0
      · rw [h0]; ring
      · rw [hwd h0]; ring
  have hR : ∀ d ∈ m.divisors,
      ((if rosserWeight D b d = 0 ∧ rosserWeight D b (d / d.minFac) ≠ 0 then
        (moebius d : ℝ) * g d *
          ∑ f ∈ (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < d.minFac),
            (moebius f : ℝ) * g f else 0) +
      (if rosserWeight D b (d * p) = 0 ∧ rosserWeight D b (d * p / (d * p).minFac) ≠ 0 then
        (moebius (d * p) : ℝ) * g (d * p) *
          ∑ f ∈ (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < (d * p).minFac),
            (moebius f : ℝ) * g f else 0)) =
      (1 - g p) * (if rosserWeight D b d = 0 ∧ rosserWeight D b (d / d.minFac) ≠ 0 then
        (moebius d : ℝ) * g d *
          ∑ f ∈ m.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < d.minFac),
            (moebius f : ℝ) * g f else 0) + Y d := by
    intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdsq : Squarefree d := hm.squarefree_of_dvd hdm
    have hdmin : ∀ q ∈ d.primeFactors, p < q := fun q hq =>
      hmin q (Nat.primeFactors_mono hdm hm0 hq)
    have hpd : ¬ p ∣ d := fun h => lt_irrefl p
      (hdmin p (Nat.mem_primeFactors.mpr ⟨hp, h, hd0⟩))
    have hmf : (d * p).minFac = p := minFac_mul_smallest hd0 hp hdmin
    have hone : (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < p) = {1} := by
      ext f
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hf, -⟩, hq⟩
        by_contra hf1
        have hqp := Nat.minFac_prime hf1
        have hf0 : f ≠ 0 := by rintro rfl; exact hn0 (Nat.eq_zero_of_zero_dvd hf)
        have := hq _ (Nat.mem_primeFactors.mpr ⟨hqp, Nat.minFac_dvd f, hf0⟩)
        rcases (Nat.Prime.dvd_mul hqp).mp ((Nat.minFac_dvd f).trans hf) with h | h
        · exact lt_asymm this (hmin _ (Nat.mem_primeFactors.mpr ⟨hqp, h, hm0⟩))
        · exact lt_irrefl _ (((Nat.prime_dvd_prime_iff_eq hqp hp).mp h) ▸ this)
      · rintro rfl
        exact ⟨⟨one_dvd _, hn0⟩, by simp⟩
    rw [hmf, Nat.mul_div_cancel d hp.pos, hone, Finset.sum_singleton, mu_g_mul hg hp hpd]
    simp only [moebius_apply_one, Int.cast_one, hg.map_one, mul_one]
    have hfirst : (if rosserWeight D b d = 0 ∧ rosserWeight D b (d / d.minFac) ≠ 0 then
        (moebius d : ℝ) * g d *
          ∑ f ∈ (m * p).divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < d.minFac),
            (moebius f : ℝ) * g f else 0) =
      (1 - g p) * (if rosserWeight D b d = 0 ∧ rosserWeight D b (d / d.minFac) ≠ 0 then
        (moebius d : ℝ) * g d *
          ∑ f ∈ m.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < d.minFac),
            (moebius f : ℝ) * g f else 0) := by
      by_cases hd1 : d = 1
      · subst hd1; simp [rw_one]
      · have hlt : p < d.minFac := hdmin _
          (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hd1, Nat.minFac_dvd d, hd0⟩)
        rw [inner_step hg hm0 hp hmin _ hlt]
        split_ifs <;> ring
    rw [hfirst, rosserWeight_mul_smallest D b hdsq hp hdmin]
    have hwd : rosserWeight D b d ≠ 0 → rosserWeight D b d = (moebius d : ℝ) :=
      rw_eq_moebius_of_ne D b
    simp only [Y]
    congr 1
    split_ifs with h1 h2 h2 <;> simp_all
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ih]

/-- The regrouping identity IK (6.6)-(6.7) for any squarefree `n` and multiplicative `g`, by
induction removing the least prime. -/
theorem regroup_general (D : ℝ) (b : Bool) {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (n : ℕ) (hn : Squarefree n) :
    ∑ d ∈ n.divisors, ((moebius d : ℝ) - rosserWeight D b d) * g d =
      ∑ e ∈ n.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (moebius e : ℝ) * g e *
          ∑ f ∈ n.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < e.minFac),
            (moebius f : ℝ) * g f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      simp [rw_one, Finset.filter_singleton]
    · obtain ⟨hed, hlt, hmsq, hmin⟩ := split_least hn h1
      have := regroup_step D b hg hmsq (Nat.minFac_prime h1) hmin (ih _ hlt hmsq)
      rwa [← hed] at this

/-- LEAF: Iwaniec-Kowalski (6.6)-(6.7), Opera de Cribro Section 6.3, regrouping of the divisors
that fail the Rosser cut-off. Class MEDIUM, a finite combinatorial identity. Every `d ∣ P` with
`λ_d = 0` factors uniquely as `d = e f` with `e` its prefix of largest primes up to the first
failing prime, so `e ∈ B^b`, and `f ∣ P` having all prime factors below `p(e)`; conversely each
such `e f` fails. Hence `Σ_{d∣P} (μ(d) - λ^b_d) g(d) = Σ_{e ∈ B^b} μ(e) g(e) Σ_{f ∣ P(p(e))} μ(f) g(f)`. -/
theorem rosser_failure_regroup (s : BoundingSieve) (D : ℝ) (b : Bool) :
    ∑ d ∈ s.prodPrimes.divisors, ((ArithmeticFunction.moebius d : ℝ) - rosserWeight D b d) * s.nu d =
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (ArithmeticFunction.moebius e : ℝ) * s.nu e *
          ∑ f ∈ s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < e.minFac),
            (ArithmeticFunction.moebius f : ℝ) * s.nu f :=
  regroup_general D b s.nu_mult _ s.prodPrimes_squarefree

/-- LEAF: Iwaniec-Kowalski (6.8), the Euler product for the sifting function at `p`:
`Σ_{f ∣ P, all prime factors of f below p} μ(f) g(f) = ∏_{q ∣ P, q < p} (1 - g(q)) = V(p)`.
Class EASY, from multiplicativity of `g` and `Squarefree P`. -/
theorem sum_moebius_below_eq_prod (s : BoundingSieve) (p : ℕ) :
    ∑ f ∈ s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < p),
        (ArithmeticFunction.moebius f : ℝ) * s.nu f =
      ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q) := by
  set S := s.prodPrimes.primeFactors.filter (fun q => q < p) with hS
  have hSP : ∀ q ∈ S, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hnP : (∏ q ∈ S, q) ∣ s.prodPrimes := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hnsq : Squarefree (∏ q ∈ S, q) := s.prodPrimes_squarefree.squarefree_of_dvd hnP
  have hpf : (∏ q ∈ S, q).primeFactors = S := Nat.primeFactors_prod hSP
  have hdiv : (∏ q ∈ S, q).divisors =
      s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < p) := by
    ext f
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hf, hn0⟩
      refine ⟨⟨hf.trans hnP, hP0⟩, fun q hq => ?_⟩
      have : q ∈ (∏ q ∈ S, q).primeFactors := Nat.primeFactors_mono hf hn0 hq
      rw [hpf] at this
      exact (Finset.mem_filter.mp this).2
    · rintro ⟨⟨hfP, -⟩, hq⟩
      refine ⟨?_, hnsq.ne_zero⟩
      have hfsq : Squarefree f := s.prodPrimes_squarefree.squarefree_of_dvd hfP
      rw [← Nat.prod_primeFactors_of_squarefree hfsq]
      refine Finset.prod_dvd_prod_of_subset _ _ _ fun q hqf => ?_
      exact Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hfP hP0 hqf, hq q hqf⟩
  have key := s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hnsq
  rw [hpf] at key
  rw [← hdiv, key]

/-- **Parent `Decomp1527bFeed1122JR.rosser_mainSum_buchstab`, assembled from the leaves**
`rosser_failure_regroup` and `sum_moebius_below_eq_prod`, with the full Euler product
`Σ_{d∣P} μ(d) g(d) = V(P)` from Mathlib. Same statement as the parent. -/
theorem rosser_mainSum_buchstab_of_leaves (s : BoundingSieve) (D : ℝ) (b : Bool) :
    s.mainSum (rosserWeight D b) = (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) -
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (ArithmeticFunction.moebius e : ℝ) * s.nu e *
          ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q) := by
  have h1 := s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ s.prodPrimes_squarefree
  have h2 := rosser_failure_regroup s D b
  simp only [sum_moebius_below_eq_prod] at h2
  rw [h1, ← h2, ← Finset.sum_sub_distrib]
  unfold BoundingSieve.mainSum
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JRP2
