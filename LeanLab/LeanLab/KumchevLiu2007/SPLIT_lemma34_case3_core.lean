/-
Split of `leaf_case3_reduction_lemma33_core` of
`LeanLab.KumchevLiu2007.SPLIT_lemma34_large_right`, Case 3 of the proof of
Lemma 3.4 of Kumchev and Liu 2007, P0088 page 12, D ≥ y x^(-1/2) L^(-B).

The paper does two things in Case 3 before it applies Lemma 3.2.

* It factors d = p1 ... pr, pr < ... < p1 < z, picks the unique s with
  p1 ... ps ≤ V ≤ p1 ... ps+1, and writes the left side of (42) over
  p = ps, p' = ps+1, d1 = p1 ... ps-1, d2 = ps+2 ... pr. This is the PROVED
  identity `moebius_block_case3_factor`, with e = d1 p and f = p' d2, on top of
  `top_exists` and `top_unique`, the existence and uniqueness of s. The
  strictness is taken as e < V ≤ e p', which makes s unique.
* It removes the conditions p' < p, pp' d1 d2 ∼ D and d1 p p' ≥ V by Lemma 3.3,
  Kumchev Lemma 2.7, and groups u = k p' d2, v = p d1. This is the LEAF
  `leaf_case3_lemma33_removal`.

`case3_reduction_core_of_leaves` is the statement of the parent LEAF, proved
from the identity and the new LEAF, with V = H / (Y^(1/2) L^B) > 1 for large X.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import LeanLab.KumchevLiu2007.SPLIT_case3_removal_D

namespace LeanLab.KumchevLiu2007.Eq33RouteD.Case3Core1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, uniqueness of s, one
direction: for squarefree d, two divisors v, v' that are top segments of d,
that is every prime of d / v is below every prime of v, with v < V and with
V ≤ v' q for a prime q of d / v', the primes of v divide v'. -/
theorem top_dvd_of_dvd (d v v' : ℕ) (hd : Squarefree d) (hv : v ∣ d) (hv' : v' ∣ d) (V : ℝ)
    (htop : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ v → q ∣ d / v → q < p)
    (htop' : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ v' → q ∣ d / v' → q < p)
    (hvV : (v : ℝ) < V)
    (hq' : ∃ q : ℕ, q.Prime ∧ q ∣ d / v' ∧ V ≤ (v' : ℝ) * q) :
    ∀ p : ℕ, p.Prime → p ∣ v → p ∣ v' := by
  intro p hp hpv
  by_contra hpv'
  have hd0 : d ≠ 0 := hd.ne_zero
  have hdv : d = v * (d / v) := (Nat.mul_div_cancel' hv).symm
  have hdv' : d = v' * (d / v') := (Nat.mul_div_cancel' hv').symm
  have hv0 : v ≠ 0 := ne_zero_of_dvd_ne_zero hd0 hv
  have hv'0 : v' ≠ 0 := ne_zero_of_dvd_ne_zero hd0 hv'
  -- p divides d / v'
  have hpd : p ∣ d / v' := by
    have : p ∣ v' * (d / v') := hdv' ▸ (hpv.trans hv)
    exact (hp.dvd_mul.mp this).resolve_left hpv'
  -- squarefree: a prime cannot divide both v and d / v
  have hsep : ∀ x : ℕ, x ∣ d → ∀ r : ℕ, r.Prime → r ∣ x → r ∣ d / x → False := by
    intro x hx r hr h1 h2
    have : r * r ∣ d := by
      rw [← Nat.mul_div_cancel' hx]
      exact Nat.mul_dvd_mul h1 h2
    exact hr.one_lt.ne' (Nat.isUnit_iff.mp (hd r this))
  -- every prime of v' divides v
  have hsub : v'.primeFactors ⊆ v.primeFactors := by
    intro r hr
    obtain ⟨hrp, hrv', -⟩ := Nat.mem_primeFactors.mp hr
    refine Nat.mem_primeFactors.mpr ⟨hrp, ?_, hv0⟩
    by_contra hrv
    have hrd : r ∣ d / v := by
      have : r ∣ v * (d / v) := hdv ▸ (hrv'.trans hv')
      exact (hrp.dvd_mul.mp this).resolve_left hrv
    have h1 := htop p r hp hrp hpv hrd
    have h2 := htop' r p hrp hp hrv' hpd
    omega
  have hsq' : Squarefree v' := hd.squarefree_of_dvd hv'
  have hv'v : v' ∣ v := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq']
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd v)
  obtain ⟨q, hq, hqd, hVq⟩ := hq'
  have hqv' : ¬ q ∣ v' := fun h => hsep v' hv' q hq h hqd
  -- v' * x ∣ v gives v' * x ≤ v
  have hle : ∀ x : ℕ, x ∣ v → Nat.Coprime v' x → ((v' : ℝ) * x ≤ v) := by
    intro x hx hcop
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) (hcop.mul_dvd_of_dvd_of_dvd hv'v hx)
    exact_mod_cast this
  by_cases hqv : q ∣ v
  · have h1 := hle q hqv (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqv'))
    linarith
  · have hqd' : q ∣ d / v := by
      have hqd0 : q ∣ d := hqd.trans (Nat.div_dvd_of_dvd hv')
      have : q ∣ v * (d / v) := hdv ▸ hqd0
      exact (hq.dvd_mul.mp this).resolve_left hqv
    have hqp : q < p := htop p q hp hq hpv hqd'
    have h1 := hle p hpv (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpv'))
    have hqp' : (q : ℝ) ≤ p := by exact_mod_cast hqp.le
    have hv'pos : (0 : ℝ) ≤ v' := by positivity
    nlinarith

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4: the integer s with
p1 ... ps < V ≤ p1 ... ps+1 is unique. Written for the top segment
v = p1 ... ps of the squarefree d, with p' = ps+1 a prime of d / v. -/
theorem top_unique (d v v' : ℕ) (hd : Squarefree d) (hv : v ∣ d) (hv' : v' ∣ d) (V : ℝ)
    (htop : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ v → q ∣ d / v → q < p)
    (htop' : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ v' → q ∣ d / v' → q < p)
    (hvV : (v : ℝ) < V) (hv'V : (v' : ℝ) < V)
    (hq : ∃ q : ℕ, q.Prime ∧ q ∣ d / v ∧ V ≤ (v : ℝ) * q)
    (hq' : ∃ q : ℕ, q.Prime ∧ q ∣ d / v' ∧ V ≤ (v' : ℝ) * q) : v = v' := by
  have h1 := top_dvd_of_dvd d v v' hd hv hv' V htop htop' hvV hq'
  have h2 := top_dvd_of_dvd d v' v hd hv' hv V htop' htop hv'V hq
  exact (Nat.Squarefree.ext_iff (hd.squarefree_of_dvd hv) (hd.squarefree_of_dvd hv')).mpr
    fun p hp => ⟨h1 p hp, h2 p hp⟩

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4: each squarefree d ≥ V > 1
has a top segment v = p1 ... ps, the product of its largest primes, with
v < V ≤ v p' for the prime p' = ps+1 of d / v. -/
theorem top_exists (d : ℕ) (hd : Squarefree d) (V : ℝ) (hV : 1 < V) (hVd : V ≤ d) :
    ∃ v : ℕ, v ∣ d ∧ (∀ p q : ℕ, p.Prime → q.Prime → p ∣ v → q ∣ d / v → q < p) ∧
      (v : ℝ) < V ∧ ∃ q : ℕ, q.Prime ∧ q ∣ d / v ∧ V ≤ (v : ℝ) * q := by
  have hd0 : d ≠ 0 := hd.ne_zero
  set T := d.divisors.filter (fun v : ℕ =>
    (∀ p q : ℕ, p.Prime → q.Prime → p ∣ v → q ∣ d / v → q < p) ∧ (v : ℝ) < V) with hT
  have h1T : 1 ∈ T := by
    refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hd0, ?_, by simpa using hV⟩
    intro p q hp _ hp1 _
    exact absurd (Nat.le_of_dvd one_pos hp1) (by have := hp.two_le; omega)
  have hTne : T.Nonempty := ⟨1, h1T⟩
  set v := T.max' hTne with hvdef
  have hvT : v ∈ T := T.max'_mem hTne
  obtain ⟨hvd, htop, hvV⟩ := Finset.mem_filter.mp hvT
  have hvd' : v ∣ d := (Nat.mem_divisors.mp hvd).1
  have hv0 : v ≠ 0 := ne_zero_of_dvd_ne_zero hd0 hvd'
  have hdv : d = v * (d / v) := (Nat.mul_div_cancel' hvd').symm
  set w := d / v with hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdv
    exact hd0 hdv
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, mul_one] at hdv
    rw [← hdv] at hvV
    linarith
  have hwsq : Squarefree w := hd.squarefree_of_dvd (Nat.div_dvd_of_dvd hvd')
  have hpfne : w.primeFactors.Nonempty := by
    exact Nat.nonempty_primeFactors.mpr (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hw0, hw1⟩)
  set q := w.primeFactors.max' hpfne with hqdef
  have hqmem : q ∈ w.primeFactors := w.primeFactors.max'_mem hpfne
  obtain ⟨hqp, hqw, -⟩ := Nat.mem_primeFactors.mp hqmem
  refine ⟨v, hvd', htop, hvV, q, hqp, hqw, ?_⟩
  by_contra hlt
  push Not at hlt
  -- v * q is again a top segment below V, contradicting maximality
  have hvq : v * q ∣ d := by
    rw [hdv]
    exact Nat.mul_dvd_mul_left v hqw
  have hdvq : d / (v * q) = w / q := by
    rw [Nat.div_div_eq_div_mul]
  have hmem : v * q ∈ T := by
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hvq, hd0⟩, ?_, by exact_mod_cast hlt⟩
    intro p r hp hr hpvq hrd
    rw [hdvq] at hrd
    have hrw : r ∣ w := hrd.trans (Nat.div_dvd_of_dvd hqw)
    rcases hp.dvd_mul.mp hpvq with hpv | hpq
    · exact htop p r hp hr hpv hrw
    · have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
      rw [hpq']
      have hrle : r ≤ q := w.primeFactors.le_max' r (Nat.mem_primeFactors.mpr ⟨hr, hrw, hw0⟩)
      rcases lt_or_eq_of_le hrle with h | h
      · exact h
      · exfalso
        rw [h] at hrd
        have hsq : q * q ∣ w := by
          rw [← Nat.mul_div_cancel' hqw]
          exact Nat.mul_dvd_mul_left q hrd
        exact hqp.one_lt.ne' (Nat.isUnit_iff.mp (hwsq q hsq))
  have hle : v * q ≤ v := T.le_max' _ hmem
  have : v * 2 ≤ v * q := Nat.mul_le_mul_left v hqp.two_le
  omega

/-- The divisor sum over d | m and v | d equals the sum over v | m and
w | m / v, by d = v w. -/
theorem sum_divisors_swap (m : ℕ) (hm : m ≠ 0) (G : ℕ → ℕ → ℂ) :
    ∑ d ∈ m.divisors, ∑ e ∈ d.divisors, G e (d / e) =
      ∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors, G e f := by
  rw [Finset.sum_comm' (s' := fun e => m.divisors.filter (fun d => e ∣ d)) (t' := m.divisors)]
  · refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨hem, -⟩ := Nat.mem_divisors.mp he
    have he0 : 0 < e := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm hem)
    refine Finset.sum_nbij' (fun d => d / e) (fun f => e * f) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdm, hed⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdm', -⟩ := Nat.mem_divisors.mp hdm
      refine Nat.mem_divisors.mpr ⟨Nat.div_dvd_div hed hdm', ?_⟩
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hem) he0).ne'
    · intro f hf
      obtain ⟨hfm, -⟩ := Nat.mem_divisors.mp hf
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hm⟩, dvd_mul_right e f⟩
      rw [← Nat.mul_div_cancel' hem]
      exact Nat.mul_dvd_mul_left e hfm
    · intro d hd
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2
    · intro f _
      exact Nat.mul_div_cancel_left f he0
    · intro d _
      rfl
  · intro d e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdm, hm0⟩, hed, hd0⟩
      exact ⟨⟨⟨hdm, hm0⟩, hed⟩, hed.trans hdm, hm0⟩
    · rintro ⟨⟨⟨hdm, hm0⟩, hed⟩, -, -⟩
      exact ⟨⟨hdm, hm0⟩, hed, ne_zero_of_dvd_ne_zero hm0 hdm⟩

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, the display that writes
the left side of (42) over p, p', d1, d2: for 1 < V ≤ D, the Moebius block
over d ∼ D, d | Pi(z) equals the sum over the factorisations m = e f k with
e = d1 p, f = p' d2, where e and f are squarefree with all primes below z,
every prime of f is below every prime of e, that is p' < p, d2 | Pi(p') and
the primes of d1 above p, ef ∼ D and e < V ≤ e p'. The sign mu(d) is
mu(e) mu(f) since e and f are coprime. -/
theorem moebius_block_case3_factor (z V D : ℝ) (hV : 1 < V) (hVD : V ≤ D) (m : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
          ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
      if (Squarefree e ∧ Squarefree f ∧ (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
          (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
          D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧ (e : ℝ) < V ∧
          ∃ q : ℕ, q.Prime ∧ q ∣ f ∧ V ≤ (e : ℝ) * q)
      then ((ArithmeticFunction.moebius e : ℤ) : ℂ) * ((ArithmeticFunction.moebius f : ℤ) : ℂ)
      else 0 := by
  rw [← sum_divisors_swap m hm, Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm (Nat.mem_divisors.mp hd).1
  by_cases hS : (Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) ∧
      D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D
  · rw [if_pos hS]
    obtain ⟨⟨hsq, hz⟩, hD1, hD2⟩ := hS
    obtain ⟨v, hvd, htop, hvV, hq⟩ := top_exists d hsq V hV (hVD.trans hD1)
    have hdv : v * (d / v) = d := Nat.mul_div_cancel' hvd
    rw [Finset.sum_eq_single_of_mem v (Nat.mem_divisors.mpr ⟨hvd, hd0⟩)]
    · rw [if_pos ⟨hsq.squarefree_of_dvd hvd, hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hvd),
        by rw [hdv]; exact hz, htop, by rw [hdv]; exact hD1, by rw [hdv]; exact hD2, hvV, hq⟩]
      have hcop : Nat.Coprime v (d / v) := Nat.coprime_of_squarefree_mul (by rw [hdv]; exact hsq)
      rw [← Int.cast_mul, ← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        hdv]
    · intro e he hev
      rw [if_neg]
      rintro ⟨-, -, -, htop', -, -, heV, hq'⟩
      exact hev (top_unique d e v hsq (Nat.mem_divisors.mp he).1 hvd V htop' htop heV hvV hq' hq)
  · rw [if_neg hS]
    refine (Finset.sum_eq_zero fun e he => ?_).symm
    rw [if_neg]
    rintro ⟨hsqe, hsqf, hz, htop', hD1, hD2, -, -⟩
    have hdv : e * (d / e) = d := Nat.mul_div_cancel' (Nat.mem_divisors.mp he).1
    rw [hdv] at hz hD1 hD2
    apply hS
    refine ⟨⟨?_, hz⟩, hD1, hD2⟩
    rw [← hdv, Nat.squarefree_mul_iff]
    refine ⟨?_, hsqe, hsqf⟩
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.Coprime]
    refine Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpf hpe => ?_)
    exact lt_irrefl p (htop' p p hp hp hpe hpf)

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4, the use of Lemma 3.3,
Kumchev Lemma 2.7, to remove the conditions p' < p, pp' d1 d2 ∼ D and
d1 p p' ≥ V. The left side is display 42 over m = e f k as in
`moebius_block_case3_factor`, e = d1 p, f = p' d2, V = H / (Y^(1/2) L^B).
The right side is the bound before "Thus, (42) follows from Lemma 3.2", with
v = p d1 in [L^B, V], u = k p' d2, coefficients bounded by tau^c and not
depending on t, see Q3 in the notes. No longer a LEAF: proved in
`Case3RemovalD1123.case3_removal_of_core`, the range D ≥ Y^(1/2) directly and
the rest from the LEAF `Case3RemovalD1123.leaf_case3_lemma33_removal_core`.
CONDITIONAL ON leaf_case3_lemma33_removal_core. -/
theorem leaf_case3_lemma33_removal :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
              if (Squarefree e ∧ Squarefree f ∧
                  (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
                  (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
                  D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
                  (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
                  ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                    H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
              then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
                ((ArithmeticFunction.moebius f : ℤ) : ℂ)
              else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  exact Case3RemovalD1123.case3_removal_of_core

example : type_of% @leaf_case3_lemma33_removal := @Case3RemovalD1123.case3_removal_of_core

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, the display after the
factorisation, in the statement of `leaf_case3_reduction_lemma33_core`:
the factorisation identity `moebius_block_case3_factor`, with
V = H / (Y^(1/2) L^B) > 1 once L^B ≤ X^(7/72) / 2, turns the left side into
the left side of `leaf_case3_lemma33_removal`.
CONDITIONAL ON leaf_case3_lemma33_removal. -/
theorem case3_reduction_core_of_leaves :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
                  ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  obtain ⟨c, hleaf⟩ := leaf_case3_lemma33_removal
  refine ⟨c, fun B hB ε hε => ?_⟩
  obtain ⟨X1, hX1, k⟩ := hleaf B hB ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 7 / 72)).bound
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max X1 (max T 3), hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α z hz2 hz D hD1 hD3 hsmall
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXT : T ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX3 : 3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hLB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY0 : 0 < windowY X ε := by unfold windowY; exact Real.rpow_pos_of_pos hX0 _
  have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
  have hsq : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hlogB : Real.log X ^ B ≤ 1 / 2 * X ^ (7 / 72 : ℝ) := by
    have h0 := hT X hXT
    simpa only [Real.norm_eq_abs, abs_of_pos hLB,
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 72 : ℝ))] using h0
  have hprod : Real.sqrt (windowY X ε) * Real.log X ^ B < H := by
    have h1 : X ^ (7 / 24 + ε / 4 : ℝ) * X ^ (7 / 72 : ℝ) = X ^ (7 / 18 + ε / 4 : ℝ) := by
      rw [← Real.rpow_add hX0]
      congr 1
      ring
    have h2 : X ^ (7 / 18 + ε / 4 : ℝ) ≤ X ^ (7 / 18 + ε : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : 0 < X ^ (7 / 18 + ε / 4 : ℝ) := Real.rpow_pos_of_pos hX0 _
    have h4 : 0 < X ^ (7 / 24 + ε / 4 : ℝ) := Real.rpow_pos_of_pos hX0 _
    rw [hsq]
    calc X ^ (7 / 24 + ε / 4 : ℝ) * Real.log X ^ B
        ≤ X ^ (7 / 24 + ε / 4 : ℝ) * (1 / 2 * X ^ (7 / 72 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogB h4.le
      _ = 1 / 2 * X ^ (7 / 18 + ε / 4 : ℝ) := by rw [← h1]; ring
      _ < X ^ (7 / 18 + ε / 4 : ℝ) := by linarith
      _ ≤ H := h2.trans hH
  have hden : 0 < Real.sqrt (windowY X ε) * Real.log X ^ B := mul_pos hsq0 hLB
  have hV1 : 1 < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hVD : H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ D := by
    rw [div_le_iff₀ hden]
    linarith
  obtain ⟨w, v, hw, hv, hb⟩ := k X H hXa hH hHX α z hz2 hz D hD1 hD3 hsmall
  refine ⟨w, v, hw, hv, ?_⟩
  have hrw : ∀ t : ℝ,
      (∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ d ∈ (m.divisors.filter (fun d : ℕ => Squarefree d ∧
              ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
      ∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
          if (Squarefree e ∧ Squarefree f ∧
              (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
              (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
              D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
              (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
              ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
          then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            ((ArithmeticFunction.moebius f : ℤ) : ℂ)
          else 0) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro t
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨-, hm1, -⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm1
      linarith
    rw [moebius_block_case3_factor z _ D hV1 hVD m hm0]
  simp only [hrw]
  exact hb

end LeanLab.KumchevLiu2007.Eq33RouteD.Case3Core1122
