/-
Unit U-1525, run 20261025T2003Z-426, DECOMPOSE. P0066 R. C. Vaughan 1977, J. reine angew.
Math. 290, 93-108, read from copies/P0066.pdf, page images 97 to 101.

File b of three: the sieve upper bound, Lemma 8 p. 101, OPEN in the folder as the Prop
`Vaughan1977Lemma10.Lemma8 C` and used by Lemma 10, (5.5) and the 27 prime Theorem. This is
the explicit Selberg-type bound for the representation count in Schnirelmann's route:
R(h, x) < 16 C x/((α(x) + log x) log x) Π_{p | h, p > 2} (p-1)/(p-2).

Vaughan's proof, p. 101: R(h, x) ≤ #{n ≤ N : (n|h - n|, Q) = 1} + 2x^{1/2}; Corollary 1 of
Montgomery-Vaughan, The large sieve, Mathematika 20 (1973), bounds the sifted count by
x S_{|h|}(z, z^{-1})^{-1}; Lemma 7 (3.9) bounds S^{-1}. Lemma 7 rests on Lemma 4 (3.5),
Lemma 6, (3.10), (3.12), (3.13) and the constants of Decomp1525a.

PROVED here: `mv_cor1` (Corollary 1 from Montgomery-Vaughan Theorem 1 and Montgomery's
arithmetic lemma), `lemma7_of` and `lemma8_of`, the latter CONDITIONAL ON 0.6601 < C < 0.6602,
which the lab has PROVED for `twinC` (ChenExplicit, the same expression as `Cv`).
`lemma8_of`'s conclusion is the body of `Vaughan1977Lemma10.Lemma8 Cv` with the product written
over `primeFactors` in ℝ instead of `prodQ` in ℚ; the bridge is a separate small link.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Decomp1525a
import LeanLab.Helfgott2013.GammaFine
import LeanLab.PNTPort.LargeSieve.Montgomery
import LeanLab.RieselVaughan1983.Stieltjes1Enclosure

open Finset Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Decomp1525b
open LeanLab.SchnirelmannBounds.Decomp1525a

/-- `e(t) = exp(2πit)`. -/
def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- `R(h, x)`, Lemma 8: the primes `p ≤ x` with `|h - p|` prime; the same text as
`Vaughan1977Lemma10.Rc`. -/
def Rc (h : ℤ) (x : ℝ) : ℕ :=
  ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Nat.Prime (h - (p : ℤ)).natAbs)).card

/-- `α(x)`, (3.8), as `Vaughan1977Lemma10.alpha`. -/
def alpha (x : ℝ) : ℝ := if x < 10 ^ 44 then 1 else 1.6

/-- `z = (2x/3)^{1/2}`, Lemmas 7 and 8. -/
def zz (x : ℝ) : ℝ := Real.sqrt (2 * x / 3)

/-- The sifted set of p. 101: `n ≤ N = [x]` with `(n |h - n|, Q) = 1`, `Q = Π_{p ≤ z} p`. -/
def sifted (h : ℤ) (x : ℝ) : Finset ℕ :=
  (Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime (n * (h - (n : ℤ)).natAbs) (primorial ⌊zz x⌋₊))

/-- `S_n(z, y)` of (3.4): `Σ_{q ≤ z} μ(q)²/(1 + yq) Π_{p | q, p ∤ n} 2/(p-2) Π_{p | (q,n)} 1/(p-1)`. -/
def Sn (n : ℕ) (z y : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊z⌋₊, (if Squarefree q then (1 : ℝ) else 0) / (1 + y * q) *
    (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2)) *
    ∏ p ∈ q.primeFactors.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1)

/-- `τ₁(r)`, p. 97: the number of odd divisors of `r`. -/
def tau1 (r : ℕ) : ℕ := (r.divisors.filter Odd).card

/-- `Π_{p | n, p > 2} (p-1)/(p-2)`, the singular factor of Lemmas 7 and 8. -/
def singQ (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- Agreement of the two exponential conventions in the large sieve modules. -/
theorem ee_eq_largeSieve_e (t : ℝ) : ee t = LeanLab.PNTPort.LargeSieve.e t := by
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring


/-- Weighted finite duality for Montgomery and Vaughan 1973 Theorem 1.
The dual estimate is an explicit hypothesis. -/
theorem weighted_sampling_of_dual {ι κ : Type*} (R : Finset ι) (J : Finset κ)
    (c : ι → κ → ℂ) (w : ι → ℝ) (hw : ∀ r ∈ R, 0 < w r)
    (hdual : ∀ b : ι → ℂ,
      ∑ n ∈ J, ‖∑ r ∈ R, b r * c r n‖^2 ≤ ∑ r ∈ R, w r * ‖b r‖^2)
    (a : κ → ℂ) :
    ∑ r ∈ R, ‖∑ n ∈ J, a n*c r n‖^2/w r ≤ ∑ n ∈ J, ‖a n‖^2 := by
  let S : ι → ℂ := fun r => ∑ n ∈ J, a n*c r n
  let b : ι → ℂ := fun r => (starRingEnd ℂ) (S r)/(w r : ℂ)
  let X : ℝ := ∑ r ∈ R, ‖S r‖^2/w r
  let A : ℝ := ∑ n ∈ J, ‖a n‖^2
  let T : κ → ℂ := fun n => ∑ r ∈ R, b r*c r n
  have hX0 : 0 ≤ X := sum_nonneg (fun r hr => div_nonneg (sq_nonneg _) (hw r hr).le)
  have hA0 : 0 ≤ A := sum_nonneg (fun n hn => sq_nonneg _)
  have henergy : ∑ r ∈ R, w r*‖b r‖^2 = X := by
    apply sum_congr rfl
    intro r hr
    dsimp [b]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw r hr).le, div_pow]
    field_simp
  have hT : ∑ n ∈ J, ‖T n‖^2 ≤ X := by
    simpa only [T, henergy] using hdual b
  have hX : (X : ℂ) = ∑ n ∈ J, a n*T n := by
    dsimp only [X]
    rw [Complex.ofReal_sum]
    simp_rw [Complex.ofReal_div, Complex.ofReal_pow, ← Complex.mul_conj']
    dsimp only [T, b, S]
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro n hn
    ring
  have h1 : X ≤ ∑ n ∈ J, ‖a n‖*‖T n‖ := by
    have hh : X = ‖(X : ℂ)‖ := by simp [Real.norm_of_nonneg hX0]
    rw [hh, hX]
    simpa only [norm_mul] using norm_sum_le J (fun n => a n*T n)
  have h2 := sum_mul_sq_le_sq_mul_sq J (fun n => ‖a n‖) (fun n => ‖T n‖)
  have h3 : X^2 ≤ A*X := by
    calc
      X^2 ≤ (∑ n ∈ J, ‖a n‖*‖T n‖)^2 := pow_le_pow_left₀ hX0 h1 2
      _ ≤ A * ∑ n ∈ J, ‖T n‖^2 := h2
      _ ≤ A*X := mul_le_mul_of_nonneg_left hT hA0
  change X ≤ A
  rcases eq_or_lt_of_le hX0 with h0 | hp
  · rw [← h0]; exact hA0
  · exact le_of_mul_le_mul_left (by nlinarith : X*X ≤ X*A) hp


/-- The weighted Farey leaf follows from its exact dual estimate.
The dual estimate remains an explicit hypothesis. -/
theorem mv_large_sieve_of_dual (M N : ℕ) (Q : ℝ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hdual : ∀ b : (Σ _ : ℕ, ℕ) → ℂ,
      ∑ n ∈ Ioc M (M+N),
        ‖∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => r.Coprime q),
          b ⟨q,r⟩*ee ((r : ℝ)*n/q)‖^2 ≤
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => r.Coprime q),
        ((N : ℝ)+3/2*q*Q)*‖b ⟨q,r⟩‖^2)
    (a : ℕ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => r.Coprime q),
      ‖∑ n ∈ Ioc M (M+N), a n*ee ((r : ℝ)*n/q)‖^2/((N : ℝ)+3/2*q*Q) ≤
      ∑ n ∈ Ioc M (M+N), ‖a n‖^2 := by
  let R := (Icc 1 ⌊Q⌋₊).sigma (fun q => (Icc 1 q).filter (fun r => r.Coprime q))
  let c : (Σ _ : ℕ, ℕ) → ℕ → ℂ := fun r n => ee ((r.2 : ℝ)*n/r.1)
  let w : (Σ _ : ℕ, ℕ) → ℝ := fun r => (N : ℝ)+3/2*r.1*Q
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ0 : 0 < Q := by linarith
  have hh := weighted_sampling_of_dual R (Ioc M (M+N)) c w
    (fun r hr => by dsimp [w]; positivity)
    (fun b => by simpa only [R, c, w, Finset.sum_sigma'] using hdual b) a
  simpa only [R, c, w, Finset.sum_sigma'] using hh

/-- Diagonal and off diagonal energy for a finite complex sampling matrix.
This is the algebraic split behind Montgomery and Vaughan 1973 Theorem 1. -/
theorem sampling_energy_split {ι κ : Type*} [DecidableEq ι]
    (R : Finset ι) (J : Finset κ) (c : ι → κ → ℂ) (b : ι → ℂ) :
    (∑ n ∈ J, ‖∑ r ∈ R, b r*c r n‖^2) =
      (∑ r ∈ R, ‖b r‖^2 * ∑ n ∈ J, ‖c r n‖^2) +
        (∑ r ∈ R, ∑ t ∈ R.erase r,
          b r*(starRingEnd ℂ) (b t) * ∑ n ∈ J, c r n*(starRingEnd ℂ) (c t n)).re := by
  let K : ι → ι → ℂ := fun r t =>
    b r*(starRingEnd ℂ) (b t) * ∑ n ∈ J, c r n*(starRingEnd ℂ) (c t n)
  have hcomplex : ((∑ n ∈ J, ‖∑ r ∈ R, b r*c r n‖^2 : ℝ) : ℂ) =
      ∑ r ∈ R, ∑ t ∈ R, K r t := by
    rw [Complex.ofReal_sum]
    simp_rw [LeanLab.PNTPort.LargeSieve.ofReal_normSq_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    dsimp [K]
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  have hdiag (r : ι) : K r r = ((‖b r‖^2 * ∑ n ∈ J, ‖c r n‖^2 : ℝ) : ℂ) := by
    dsimp [K]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.ofReal_sum]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
  have hsplit : (∑ r ∈ R, ∑ t ∈ R, K r t) =
      (∑ r ∈ R, K r r) + ∑ r ∈ R, ∑ t ∈ R.erase r, K r t := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    exact (add_sum_erase R (K r) hr).symm
  rw [hsplit] at hcomplex
  have hh := congrArg Complex.re hcomplex
  simpa only [Complex.add_re, Complex.re_sum, hdiag, Complex.ofReal_re, K] using hh


/-- The weighted dual estimate follows from its off diagonal Gram bound.
The Gram bound remains an explicit analytic hypothesis. -/
theorem weighted_dual_of_gram {ι κ : Type*} [DecidableEq ι]
    (R : Finset ι) (J : Finset κ) (c : ι → κ → ℂ) (w : ι → ℝ)
    (hgram : ∀ b : ι → ℂ,
      (∑ r ∈ R, ∑ t ∈ R.erase r,
        b r*(starRingEnd ℂ) (b t) * ∑ n ∈ J, c r n*(starRingEnd ℂ) (c t n)).re ≤
      ∑ r ∈ R, (w r-∑ n ∈ J, ‖c r n‖^2)*‖b r‖^2)
    (b : ι → ℂ) :
    ∑ n ∈ J, ‖∑ r ∈ R, b r*c r n‖^2 ≤ ∑ r ∈ R, w r*‖b r‖^2 := by
  rw [sampling_energy_split]
  apply (add_le_add (le_refl (∑ r ∈ R, ‖b r‖^2 * ∑ n ∈ J, ‖c r n‖^2)) (hgram b)).trans_eq
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  ring



/-- The weighted Farey sieve follows from its off diagonal Hilbert estimate.
The Hilbert estimate remains an explicit analytic hypothesis. -/
theorem mv_large_sieve_of_hilbert (M N : ℕ) (Q : ℝ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (R : Finset (Σ _ : ℕ, ℕ))
    (hR : R = (Icc 1 ⌊Q⌋₊).sigma (fun q => (Icc 1 q).filter (fun r => r.Coprime q)))
    (hHilbert : ∀ b : (Σ _ : ℕ, ℕ) → ℂ,
      (∑ r ∈ R, ∑ t ∈ R.erase r, b r*(starRingEnd ℂ) (b t) *
        ∑ n ∈ Ioc M (M+N), ee ((r.2 : ℝ)*n/r.1)*(starRingEnd ℂ) (ee ((t.2 : ℝ)*n/t.1))).re ≤
      ∑ r ∈ R, (3/2*r.1*Q)*‖b r‖^2)
    (a : ℕ → ℂ) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => r.Coprime q),
      ‖∑ n ∈ Ioc M (M+N), a n*ee ((r : ℝ)*n/q)‖^2/((N : ℝ)+3/2*q*Q) ≤
      ∑ n ∈ Ioc M (M+N), ‖a n‖^2 := by
  apply mv_large_sieve_of_dual M N Q hN hQ
  intro b
  let c : (Σ _ : ℕ, ℕ) → ℕ → ℂ := fun r n => ee ((r.2 : ℝ)*n/r.1)
  let w : (Σ _ : ℕ, ℕ) → ℝ := fun r => (N : ℝ)+3/2*r.1*Q
  have hd (r : (Σ _ : ℕ, ℕ)) : ∑ n ∈ Ioc M (M+N), ‖c r n‖^2 = (N : ℝ) := by
    have he (t : ℝ) : ‖ee t‖ = 1 := by
      unfold ee
      rw [Complex.norm_exp]
      simp
    simp [c, he]
  have hh := weighted_dual_of_gram R (Ioc M (M+N)) c w (by
    intro v
    simpa only [c, w, hd, add_sub_cancel_left] using hHilbert v) b
  simpa only [hR, c, w, Finset.sum_sigma'] using hh


/-- The existing weak lab sieve ceiling exceeds the denominator needed on page 101.
This is a comparison of proof budgets. -/
theorem weak_large_sieve_ceiling (N q : ℕ) (Q : ℝ) (hQ : 0 < Q) (hq : (q : ℝ) ≤ Q) :
    (N : ℝ)+3/2*q*Q < N+2*Q^2 := by
  have hh := mul_le_mul_of_nonneg_right hq hQ.le
  nlinarith [sq_pos_of_pos hQ]

/-! ### Leaves: the large sieve -/

/-- LEAF. Montgomery-Vaughan's weighted large sieve at the Farey points `b/q`, `q ≤ Q`:
`Σ_{q ≤ Q} Σ_{(b,q)=1} |Σ_{M<n≤M+N} a_n e(bn/q)|² (N + (3/2) q Q)^{-1} ≤ Σ |a_n|²`, since the
Farey spacing at `b/q` is at least `1/(qQ)`. Montgomery-Vaughan, The large sieve, Mathematika
20 (1973), Theorem 1 with δ_r ≥ 1/(qQ); Vaughan 1977 p. 101 reference [6]. Unit U-1525. -/
theorem mv_large_sieve (M N : ℕ) (Q : ℝ) (a : ℕ → ℂ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ b ∈ (Icc 1 q).filter (fun b => b.Coprime q),
      ‖∑ n ∈ Ioc M (M + N), a n * ee ((b : ℝ) * n / q)‖ ^ 2 / ((N : ℝ) + 3 / 2 * q * Q)
      ≤ ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  sorry

/-- LEAF. Montgomery's arithmetic large sieve lemma: if `S` avoids `ω(p) < p` residue classes
modulo every prime `p | q`, `q` squarefree, then
`|S|² Π_{p|q} ω(p)/(p - ω(p)) ≤ Σ_{(b,q)=1} |Σ_{s ∈ S} e(bs/q)|²`. Montgomery, Topics in
multiplicative number theory, LNM 227, Lemma 4.2 (Iwaniec-Kowalski Lemma 7.15); the step from
Theorem 1 to Corollary 1 in Montgomery-Vaughan 1973. Unit U-1525. -/
theorem montgomery_sieve (S : Finset ℕ) (q : ℕ) (hq0 : 0 < q) (hq : Squarefree q)
    (Ω : ℕ → Finset ℕ)
    (hΩ : ∀ p ∈ q.primeFactors, (∀ w ∈ Ω p, w < p) ∧ (Ω p).card < p ∧ ∀ s ∈ S, s % p ∉ Ω p) :
    (S.card : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)
      ≤ ∑ b ∈ (Icc 1 q).filter (fun b => b.Coprime q), ‖∑ s ∈ S, ee ((b : ℝ) * s / q)‖ ^ 2 := by
  let I : Finset ℤ := S.image (fun s : ℕ => (s : ℤ))
  let B : ℕ → Finset ℕ := fun p => if p ∈ q.primeFactors then Ω p else ∅
  have hB : ∀ p, p.Prime → B p ⊆ range p ∧ (B p).card < p := by
    intro p hp
    by_cases h : p ∈ q.primeFactors
    · simp only [B, h, ite_true]
      exact ⟨fun w hw => mem_range.mpr ((hΩ p h).1 w hw), (hΩ p h).2.1⟩
    · simp only [B, if_neg h, card_empty]
      exact ⟨empty_subset _, hp.pos⟩
  have hav : ∀ p ∈ q.primeFactors, LeanLab.PNTPort.LargeSieve.Avoids I (fun _ => 1) p (B p) := by
    intro p hp n hn hb
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hn
    have hh : ((s : ℤ) % (p : ℤ)).toNat = s % p := by omega
    simp only [B, hp, ite_true, hh] at hb
    exact False.elim ((hΩ p hp).2.2 s hs hb)
  have h := LeanLab.PNTPort.LargeSieve.Pr_sqf_ge I (fun _ => 1) B hB q hq hav
  have hW : LeanLab.PNTPort.LargeSieve.hW B q =
      ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ)-(Ω p).card) := by
    unfold LeanLab.PNTPort.LargeSieve.hW
    apply prod_congr rfl
    intro p hp
    simp only [B, if_pos hp]
  have hS0 : LeanLab.PNTPort.LargeSieve.S I (fun _ => 1) 0 = (S.card : ℂ) := by
    simp [LeanLab.PNTPort.LargeSieve.S, LeanLab.PNTPort.LargeSieve.e_zero, I,
      Finset.card_image_of_injective _ Nat.cast_injective]
  have hsum (b : ℕ) : LeanLab.PNTPort.LargeSieve.S I (fun _ => 1) ((b : ℝ)/q) =
      ∑ s ∈ S, ee ((b : ℝ)*s/q) := by
    unfold LeanLab.PNTPort.LargeSieve.S
    rw [Finset.sum_image]
    · apply sum_congr rfl
      intro s hs
      simp only [one_mul, Int.cast_natCast, ee_eq_largeSieve_e]
      congr 1
      ring
    · exact Nat.cast_injective.injOn
  rw [hW, hS0] at h
  simp only [Complex.norm_natCast] at h
  rw [mul_comm] at h
  by_cases hq1 : q = 1
  · subst q
    have hee (s : ℕ) : ee (s : ℝ) = 1 := by
      rw [ee_eq_largeSieve_e]
      exact_mod_cast LeanLab.PNTPort.LargeSieve.e_int (s : ℤ)
    simp [hee]
  · have hU : LeanLab.PNTPort.LargeSieve.U q = (Icc 1 q).filter (fun b => b.Coprime q) := by
      ext b
      simp only [LeanLab.PNTPort.LargeSieve.U, mem_filter, mem_range, mem_Icc]
      constructor
      · rintro ⟨hb, hc⟩
        have hb0 : b ≠ 0 := by intro he; subst b; exact hq1 (by simpa using hc)
        exact ⟨⟨by omega, by omega⟩, hc.symm⟩
      · rintro ⟨⟨hb0, hb⟩, hc⟩
        have hbq : b ≠ q := by intro he; subst b; exact hq1 (by simpa using hc)
        exact ⟨by omega, hc.symm⟩
    simpa only [LeanLab.PNTPort.LargeSieve.Pr, hU, hsum] using h

/-- **Montgomery-Vaughan 1973 Corollary 1, PROVED from `mv_large_sieve` and
`montgomery_sieve`**: `|S| · Σ_{q ≤ Q} μ²(q) (N + (3/2)qQ)^{-1} Π_{p|q} ω(p)/(p - ω(p)) ≤ 1`
for `S ⊆ (M, M+N]` avoiding `ω(p)` classes modulo each prime `p ≤ Q`. -/
theorem mv_cor1 (M N : ℕ) (Q : ℝ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (S : Finset ℕ)
    (hS : S ⊆ Ioc M (M + N)) (Ω : ℕ → Finset ℕ)
    (hΩ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Q →
      (∀ w ∈ Ω p, w < p) ∧ (Ω p).card < p ∧ ∀ s ∈ S, s % p ∉ Ω p) :
    (S.card : ℝ) * ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter Squarefree,
      (∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) /
        ((N : ℝ) + 3 / 2 * q * Q) ≤ 1 := by
  set a : ℕ → ℂ := fun n => if n ∈ S then 1 else 0 with ha
  have hsumS : ∀ t : ℕ → ℂ, ∑ n ∈ Ioc M (M + N), a n * t n = ∑ s ∈ S, t s := by
    intro t
    simp only [ha, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext n; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hrhs : ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 = (S.card : ℝ) := by
    have : ∀ n, ‖a n‖ ^ 2 = if n ∈ S then (1 : ℝ) else 0 := by
      intro n; simp only [ha]; split_ifs <;> simp
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext n; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hLS := mv_large_sieve M N Q a hN hQ
  rw [hrhs] at hLS
  simp only [hsumS] at hLS
  have hD : ∀ q : ℕ, 0 < (N : ℝ) + 3 / 2 * q * Q := by
    intro q
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : 0 ≤ 3 / 2 * (q : ℝ) * Q := by positivity
    linarith
  -- termwise comparison on squarefree q
  have hterm : ∀ q ∈ (Icc 1 ⌊Q⌋₊).filter Squarefree,
      (S.card : ℝ) ^ 2 * ((∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) /
        ((N : ℝ) + 3 / 2 * q * Q)) ≤
      ∑ b ∈ (Icc 1 q).filter (fun b => b.Coprime q),
        ‖∑ s ∈ S, ee ((b : ℝ) * s / q)‖ ^ 2 / ((N : ℝ) + 3 / 2 * q * Q) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    have hq0 : 0 < q := by omega
    have hM := montgomery_sieve S q hq0 hq.2 Ω (by
      intro p hp
      apply hΩ p (Nat.prime_of_mem_primeFactors hp)
      have h1 : p ≤ q := Nat.le_of_mem_primeFactors hp
      have h2 : (q : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast hq.1.2
      have h3 : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
      have h4 : (p : ℝ) ≤ q := by exact_mod_cast h1
      linarith)
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hM (hD q).le
  have hsum1 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum1
  have hsub : ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter Squarefree,
      ∑ b ∈ (Icc 1 q).filter (fun b => b.Coprime q),
        ‖∑ s ∈ S, ee ((b : ℝ) * s / q)‖ ^ 2 / ((N : ℝ) + 3 / 2 * q * Q) ≤
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ b ∈ (Icc 1 q).filter (fun b => b.Coprime q),
        ‖∑ s ∈ S, ee ((b : ℝ) * s / q)‖ ^ 2 / ((N : ℝ) + 3 / 2 * q * Q) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q _ _
    exact Finset.sum_nonneg (fun b _ => div_nonneg (by positivity) (hD q).le)
  have hfin := le_trans hsum1 (le_trans hsub hLS)
  set W := ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter Squarefree,
      (∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) /
        ((N : ℝ) + 3 / 2 * q * Q) with hW
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]; simp
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hpos
    have : (S.card : ℝ) * ((S.card : ℝ) * W) ≤ (S.card : ℝ) * 1 := by nlinarith
    exact le_of_mul_le_mul_left this hc

/-! ### Leaves: from R(h, x) to the sifted count -/

/-- LEAF. The first display of the proof of Lemma 8: a prime `p ≤ x` with `|h - p|` prime is
counted by the sifted set unless `p ≤ z` or `|h - p| ≤ z`; each exception set has at most
`z ≤ x^{1/2}` elements (`p ↦ |h - p|` is injective when `h < 0` or `h > x`), so
`R(h, x) ≤ #{n ≤ [x] : (n|h - n|, Π_{p≤z} p) = 1} + 2x^{1/2}`. Vaughan 1977 p. 101, proof of
Lemma 8. Unit U-1525. -/
lemma filter_union_subset {α : Type*} [DecidableEq α] (s : Finset α) (p q r : α → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r]
  (H : ∀ a ∈ s, p a ∨ q a ∨ r a) : s ⊆ s.filter p ∪ s.filter q ∪ s.filter r := by
  intro a ha
  simp only [Finset.mem_union, Finset.mem_filter, ha, true_and]
  rcases H a ha with h1 | h2 | h3
  · left; left; exact h1
  · left; right; exact h2
  · right; exact h3

lemma coprime_primorial_of_prime {p n : ℕ} (hp : p.Prime) (hlt : n < p) : p.Coprime (primorial n) := by
  have : ∀ q ∈ (Finset.Icc 1 n).filter Nat.Prime, p.Coprime q := by
    intro q hq
    have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2
    have hq_le : q ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
    have : q < p := hq_le.trans_lt hlt
    exact Nat.coprime_primes hp hq_prime |>.mpr this.ne'
  have H : p.Coprime (∏ i ∈ (Finset.Icc 1 n).filter Nat.Prime, i) := Nat.coprime_prod_right_iff.mpr this
  have h_eq : (Finset.Icc 1 n).filter Nat.Prime = (Finset.range (n + 1)).filter Nat.Prime := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · intro ha
      exact ⟨by omega, ha.2⟩
    · intro ha
      have : a ≥ 2 := Nat.Prime.two_le ha.2
      exact ⟨⟨by omega, by omega⟩, ha.2⟩
  have h_primorial : primorial n = ∏ i ∈ (Finset.Icc 1 n).filter Nat.Prime, i := by
    unfold primorial
    rw [← h_eq]
  rw [h_primorial]
  exact H

theorem reduction (x : ℝ) (hx : 1 ≤ x) (h : ℤ) (hh : h < 0 ∨ x < h) :
    (Rc h x : ℝ) ≤ (sifted h x).card + 2 * Real.sqrt x := by
  let A := (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Nat.Prime (h - (p : ℤ)).natAbs)
  let A1 := A.filter (fun p : ℕ => zz x < p ∧ zz x < (h - (p : ℤ)).natAbs)
  let A2 := A.filter (fun p : ℕ => (p : ℝ) ≤ zz x)
  let A3 := A.filter (fun p : ℕ => ((h - (p : ℤ)).natAbs : ℝ) ≤ zz x)
  have Hsubset : A ⊆ A1 ∪ A2 ∪ A3 := by
    apply filter_union_subset
    intro a ha
    have Htri : zz x < (a : ℝ) ∧ zz x < ((h - (a : ℤ)).natAbs : ℝ) ∨ (a : ℝ) ≤ zz x ∨ ((h - (a : ℤ)).natAbs : ℝ) ≤ zz x := by
      by_cases h1 : (a : ℝ) ≤ zz x
      · right; left; exact h1
      · by_cases h2 : ((h - (a : ℤ)).natAbs : ℝ) ≤ zz x
        · right; right; exact h2
        · left; exact ⟨not_le.mp h1, not_le.mp h2⟩
    exact Htri
  have Hcard1 : (A.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) := by
    have hcard : A.card ≤ A1.card + A2.card + A3.card := by
      calc
        A.card ≤ (A1 ∪ A2 ∪ A3).card := Finset.card_mono Hsubset
        _ ≤ (A1 ∪ A2).card + A3.card := Finset.card_union_le _ _
        _ ≤ (A1.card + A2.card) + A3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    exact_mod_cast hcard
  have HA2 : (A2.card : ℝ) ≤ zz x := by
    have h1 : A2.card ≤ ⌊zz x⌋₊ := by
      calc
        A2.card ≤ ((Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ zz x)).card := by
          apply Finset.card_mono
          intro a ha
          have : a ∈ A ∧ (a : ℝ) ≤ zz x := by exact Finset.mem_filter.mp ha
          have hA : a ∈ A := this.1
          have : a ∈ Finset.Icc 1 ⌊x⌋₊ := by
            have : a ∈ Finset.Icc 1 ⌊x⌋₊ ∧ a.Prime ∧ Nat.Prime (h - (a : ℤ)).natAbs := Finset.mem_filter.mp hA
            exact this.1
          exact Finset.mem_filter.mpr ⟨this, Finset.mem_filter.mp ha |>.2⟩
        _ ≤ (Finset.Icc 1 ⌊zz x⌋₊).card := by
          apply Finset.card_mono
          intro a ha
          have : a ∈ Finset.Icc 1 ⌊x⌋₊ ∧ (a : ℝ) ≤ zz x := Finset.mem_filter.mp ha
          have h1 : 1 ≤ a := Finset.mem_Icc.mp this.1 |>.1
          have h2 : a ≤ ⌊zz x⌋₊ := Nat.le_floor this.2
          exact Finset.mem_Icc.mpr ⟨h1, h2⟩
        _ = ⌊zz x⌋₊ + 1 - 1 := Nat.card_Icc _ _
        _ = ⌊zz x⌋₊ := by omega
    have h2 : (⌊zz x⌋₊ : ℝ) ≤ zz x := Nat.floor_le (Real.sqrt_nonneg _)
    have h4 : (A2.card : ℝ) ≤ ⌊zz x⌋₊ := by exact_mod_cast h1
    exact h4.trans h2
  have HA3 : (A3.card : ℝ) ≤ zz x := by
    have h1 : A3.card ≤ ⌊zz x⌋₊ := by
      let s := A.filter (fun p : ℕ => ((h - (p : ℤ)).natAbs : ℝ) ≤ zz x)
      calc
        A3.card ≤ s.card := by
          exact le_rfl
        _ = (s.image (fun p : ℕ => (h - (p : ℤ)).natAbs)).card := by
          have hinj : ∀ x ∈ s, ∀ y ∈ s, (h - (x : ℤ)).natAbs = (h - (y : ℤ)).natAbs → x = y := by
            intro a ha b hb heq
            have hA : a ∈ Finset.Icc 1 ⌊x⌋₊ ∧ a.Prime ∧ Nat.Prime (h - (a : ℤ)).natAbs := Finset.mem_filter.mp (Finset.mem_filter.mp ha).1
            have hB : b ∈ Finset.Icc 1 ⌊x⌋₊ ∧ b.Prime ∧ Nat.Prime (h - (b : ℤ)).natAbs := Finset.mem_filter.mp (Finset.mem_filter.mp hb).1
            rcases hh with hh1 | hh2
            · have ha_pos : (1 : ℤ) ≤ a := by exact_mod_cast Finset.mem_Icc.mp hA.1 |>.1
              have hb_pos : (1 : ℤ) ≤ b := by exact_mod_cast Finset.mem_Icc.mp hB.1 |>.1
              have ha_lt : h - (a : ℤ) < 0 := by linarith
              have hb_lt : h - (b : ℤ) < 0 := by linarith
              have heqa : ((h - (a : ℤ)).natAbs : ℤ) = ((a : ℤ) - h) := by
                rw [← Int.natAbs_neg, neg_sub]
                exact Int.natAbs_of_nonneg (by linarith)
              have heqb : ((h - (b : ℤ)).natAbs : ℤ) = ((b : ℤ) - h) := by
                rw [← Int.natAbs_neg, neg_sub]
                exact Int.natAbs_of_nonneg (by linarith)
              have : ((a : ℤ) - h) = ((b : ℤ) - h) := by
                calc
                  ((a : ℤ) - h) = ((h - (a : ℤ)).natAbs : ℤ) := heqa.symm
                  _ = ((h - (b : ℤ)).natAbs : ℤ) := by rw [heq]
                  _ = ((b : ℤ) - h) := heqb
              have : (a : ℤ) = (b : ℤ) := by linarith
              exact_mod_cast this
            · have ha1 : (a : ℝ) ≤ x := by
                have : a ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hA.1 |>.2
                exact Nat.le_floor_iff (by linarith) |>.mp this
              have ha_pos : (a : ℤ) > 0 := by
                have : 1 ≤ a := Finset.mem_Icc.mp hA.1 |>.1
                exact_mod_cast this
              have hb1 : (b : ℝ) ≤ x := by
                have : b ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hB.1 |>.2
                exact Nat.le_floor_iff (by linarith) |>.mp this
              have hb_pos : (b : ℤ) > 0 := by
                have : 1 ≤ b := Finset.mem_Icc.mp hB.1 |>.1
                exact_mod_cast this
              have ha_gt : h - (a : ℤ) > 0 := by
                have : (a : ℝ) < h := by linarith
                have : (a : ℤ) < h := by exact_mod_cast this
                linarith
              have hb_gt : h - (b : ℤ) > 0 := by
                have : (b : ℝ) < h := by linarith
                have : (b : ℤ) < h := by exact_mod_cast this
                linarith
              have heqa : ((h - (a : ℤ)).natAbs : ℤ) = h - (a : ℤ) := Int.natAbs_of_nonneg ha_gt.le
              have heqb : ((h - (b : ℤ)).natAbs : ℤ) = h - (b : ℤ) := Int.natAbs_of_nonneg hb_gt.le
              have : h - (a : ℤ) = h - (b : ℤ) := by
                calc
                  h - (a : ℤ) = ((h - (a : ℤ)).natAbs : ℤ) := heqa.symm
                  _ = ((h - (b : ℤ)).natAbs : ℤ) := by rw [heq]
                  _ = h - (b : ℤ) := heqb
              have : (a : ℤ) = (b : ℤ) := by linarith
              exact_mod_cast this
          rw [Finset.card_image_of_injOn hinj]
        _ ≤ (Finset.Icc 1 ⌊zz x⌋₊).card := by
          apply Finset.card_mono
          intro a ha
          have ⟨p, hp1, hp2⟩ := Finset.mem_image.mp ha
          have h1 : p ∈ A ∧ ((h - (p : ℤ)).natAbs : ℝ) ≤ zz x := Finset.mem_filter.mp hp1
          have h2 : a ≤ ⌊zz x⌋₊ := by
            rw [← hp2]
            exact Nat.le_floor h1.2
          have h3 : 1 ≤ a := by
            rw [← hp2]
            have hprime : Nat.Prime (h - (p : ℤ)).natAbs := (Finset.mem_filter.mp h1.1).2.2
            exact (Nat.Prime.two_le hprime).trans' (by decide)
          exact Finset.mem_Icc.mpr ⟨h3, h2⟩
        _ = ⌊zz x⌋₊ + 1 - 1 := Nat.card_Icc _ _
        _ = ⌊zz x⌋₊ := by omega
    have h2 : (⌊zz x⌋₊ : ℝ) ≤ zz x := Nat.floor_le (Real.sqrt_nonneg _)
    have h4 : (A3.card : ℝ) ≤ ⌊zz x⌋₊ := by exact_mod_cast h1
    exact h4.trans h2
  have hA1_subset : A1 ⊆ sifted h x := by
    intro a ha
    have h_mem_filter : a ∈ A ∧ zz x < a ∧ zz x < (h - (a : ℤ)).natAbs := Finset.mem_filter.mp ha
    have h_mem_A : a ∈ A := h_mem_filter.1
    have h_mem_A_filter : a ∈ Finset.Icc 1 ⌊x⌋₊ ∧ a.Prime ∧ Nat.Prime (h - (a : ℤ)).natAbs := Finset.mem_filter.mp h_mem_A
    have h_Icc : a ∈ Finset.Icc 1 ⌊x⌋₊ := h_mem_A_filter.1
    have h_prime1 : a.Prime := h_mem_A_filter.2.1
    have h_prime2 : Nat.Prime (h - (a : ℤ)).natAbs := h_mem_A_filter.2.2
    have h_zz1 : zz x < a := h_mem_filter.2.1
    have h_zz2 : zz x < (h - (a : ℤ)).natAbs := h_mem_filter.2.2
    simp only [sifted, Finset.mem_filter]
    refine ⟨h_Icc, ?_⟩
    rw [Nat.coprime_mul_iff_left]
    constructor
    · apply coprime_primorial_of_prime h_prime1
      have ha_zz : ⌊zz x⌋₊ < a := by
        have H1 : (⌊zz x⌋₊ : ℝ) ≤ zz x := Nat.floor_le (Real.sqrt_nonneg _)
        have H2 : (⌊zz x⌋₊ : ℝ) < a := H1.trans_lt h_zz1
        exact_mod_cast H2
      exact ha_zz
    · apply coprime_primorial_of_prime h_prime2
      have hb_zz : ⌊zz x⌋₊ < (h - (a : ℤ)).natAbs := by
        have H1 : (⌊zz x⌋₊ : ℝ) ≤ zz x := Nat.floor_le (Real.sqrt_nonneg _)
        have H2 : (⌊zz x⌋₊ : ℝ) < (h - (a : ℤ)).natAbs := H1.trans_lt h_zz2
        exact_mod_cast H2
      exact hb_zz
  have hcardA1 : (A1.card : ℝ) ≤ (sifted h x).card := by
    have : A1.card ≤ (sifted h x).card := Finset.card_mono hA1_subset
    exact_mod_cast this
  calc
    (Rc h x : ℝ) = A.card := rfl
    _ ≤ A1.card + A2.card + A3.card := Hcard1
    _ = A1.card + (A2.card + A3.card) := by ring
    _ ≤ (sifted h x).card + (zz x + zz x) := by linarith
    _ ≤ (sifted h x).card + 2 * Real.sqrt x := by
      have h1 : zz x + zz x = 2 * zz x := by ring
      rw [h1]
      have h2 : 2 * zz x ≤ 2 * Real.sqrt x := by
        dsimp [zz]
        have h_pos : 0 ≤ x := by linarith
        have h3 : Real.sqrt (2 * x / 3) = Real.sqrt (2 / 3) * Real.sqrt x := by
          have : 2 * x / 3 = (2 / 3) * x := by ring
          rw [this]
          have h23_nonneg : (0 : ℝ) ≤ 2 / 3 := by norm_num
          have H : Real.sqrt (2 / 3 * x) = Real.sqrt (2 / 3) * Real.sqrt x := Real.sqrt_mul h23_nonneg x
          exact H
        rw [h3]
        have h4 : 2 * (Real.sqrt (2 / 3) * Real.sqrt x) = (2 * Real.sqrt (2 / 3)) * Real.sqrt x := by ring
        rw [h4]
        have hsq : 2 * Real.sqrt (2 / 3) ≤ 2 := by
          have : Real.sqrt (2 / 3) ≤ 1 := by
            have : (1 : ℝ) = Real.sqrt 1 := by norm_num
            rw [this]
            apply Real.sqrt_le_sqrt
            norm_num
          linarith
        have h5 : (2 * Real.sqrt (2 / 3)) * Real.sqrt x ≤ 2 * Real.sqrt x := by
          have h_pos : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
          apply mul_le_mul_of_nonneg_right hsq h_pos
        exact h5
      linarith

/-- LEAF. Corollary 1 of Montgomery-Vaughan applied as on p. 101: the sifted set avoids the
classes `0` and `h` modulo each `p ≤ z`, so `ω(p) = 1` for `p | h` and `ω(p) = 2` otherwise
(`ω(2) = 1` as `h` is even), and with `N = [x]`, `Q = z`, `(3/2) z² = x`,
`N + (3/2) q z ≤ x (1 + q/z)`, giving `#sifted · S_{|h|}(z, z^{-1}) ≤ x`. Proof: `mv_cor1`.
Vaughan 1977 p. 101, "by Corollary 1 of [6] and (3.4)". Unit U-1525. -/
theorem sifted_le (x : ℝ) (hx : 6 ≤ x) (h : ℤ) (he : Even h) :
    ((sifted h x).card : ℝ) * Sn h.natAbs (zz x) (zz x)⁻¹ ≤ x := by
  let Ω : ℕ → Finset ℕ := fun p => {0, (h % (p : ℤ)).toNat}
  have hz : 1 ≤ zz x := by
    unfold zz
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    linarith
  have hΩcard : ∀ p : ℕ, p.Prime →
      (Ω p).card = if p ∣ h.natAbs then 1 else 2 := by
    intro p hp
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hn : 0 ≤ h % (p : ℤ) := Int.emod_nonneg _ hp0
    have hziff : (h % (p : ℤ)).toNat = 0 ↔ p ∣ h.natAbs := by
      rw [Int.toNat_eq_zero]
      constructor
      · intro hh
        exact Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero (le_antisymm hh hn))
      · intro hh
        rw [Int.emod_eq_zero_of_dvd (Int.natCast_dvd.mpr hh)]
    by_cases hd : p ∣ h.natAbs
    · simp [Ω, hziff.mpr hd, hd]
    · have hh := mt hziff.mp hd
      simp [Ω, Ne.symm hh, hd]
  have hΩ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ zz x →
      (∀ w ∈ Ω p, w < p) ∧ (Ω p).card < p ∧ ∀ s ∈ sifted h x, s % p ∉ Ω p := by
    intro p hp hpx
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hrange : (h % (p : ℤ)).toNat < p := by
      have hlt := Int.emod_lt_of_pos h hpz
      have hn := Int.emod_nonneg h hp0
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simp only [Ω, mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hp.pos
      · exact hrange
    · rw [hΩcard p hp]
      by_cases hd : p ∣ h.natAbs
      · simp only [hd, ite_true]
        exact hp.one_lt
      · simp only [hd, ite_false]
        have h2 : p ≠ 2 := by
          intro hp2
          subst p
          exact hd (Int.natAbs_even.mpr he).two_dvd
        exact lt_of_le_of_ne hp.two_le (Ne.symm h2)
    · intro s hs hbad
      have hc := (mem_filter.mp hs).2
      have hpprim : p ∣ primorial ⌊zz x⌋₊ := hp.dvd_primorial_iff.mpr (Nat.le_floor hpx)
      have hcop : p.Coprime (s * (h - (s : ℤ)).natAbs) :=
        (hc.symm.of_dvd_left hpprim)
      have hnd : ¬ p ∣ s * (h - (s : ℤ)).natAbs := hp.coprime_iff_not_dvd.mp hcop
      simp only [Ω, mem_insert, mem_singleton] at hbad
      rcases hbad with hb | hb
      · exact hnd (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hb) _)
      · have heq : h % (p : ℤ) = (s : ℤ) % p := by
          have hh : ((h % (p : ℤ)).toNat : ℤ) = h % (p : ℤ) :=
            Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
          have hsmod := Int.natCast_mod s p
          omega
        have hd : (p : ℤ) ∣ h - (s : ℤ) := Int.dvd_of_emod_eq_zero
          (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq)
        exact hnd (dvd_mul_of_dvd_right (Int.natCast_dvd.mp hd) _)
  have hN : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hS : sifted h x ⊆ Ioc 0 (0 + ⌊x⌋₊) := by
    intro s hs
    have hh := (mem_filter.mp hs).1
    simp only [mem_Icc] at hh
    simp only [mem_Ioc, zero_add]
    omega
  have hmv := mv_cor1 0 ⌊x⌋₊ (zz x) hN hz (sifted h x) hS Ω hΩ
  let w : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors,
    ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)
  have hw : ∀ q, w q =
      (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ h.natAbs), 2 / ((p : ℝ) - 2)) *
      ∏ p ∈ q.primeFactors.filter (fun p => p ∣ h.natAbs), 1 / ((p : ℝ) - 1) := by
    intro q
    dsimp [w]
    calc
      _ = ∏ p ∈ q.primeFactors,
          if p ∣ h.natAbs then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2) := by
        apply prod_congr rfl
        intro p hp
        rw [hΩcard p (Nat.prime_of_mem_primeFactors hp)]
        split_ifs <;> norm_num
      _ = _ := by rw [prod_ite, mul_comm]
  have hw0 : ∀ q ∈ Icc 1 ⌊zz x⌋₊, 0 ≤ w q := by
    intro q hq
    apply prod_nonneg
    intro p hp
    have hple : (p : ℝ) ≤ zz x := by
      have hpq := Nat.le_of_mem_primeFactors hp
      have hqle := (mem_Icc.mp hq).2
      have hf := Nat.floor_le (by linarith : 0 ≤ zz x)
      exact le_trans (by exact_mod_cast hpq.trans hqle) hf
    have hcard := (hΩ p (Nat.prime_of_mem_primeFactors hp) hple).2.1
    have hcardR : ((Ω p).card : ℝ) < p := by exact_mod_cast hcard
    exact div_nonneg (by positivity) (by linarith)
  have hz0 : 0 < zz x := by linarith
  have hx0 : 0 < x := by linarith
  have hzsq : zz x ^ 2 = 2 * x / 3 := Real.sq_sqrt (by linarith)
  have hD : ∀ q : ℕ, 0 < (⌊x⌋₊ : ℝ) + 3 / 2 * q * zz x := by
    intro q
    have hNr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
    positivity
  have hDbound : ∀ q : ℕ,
      (⌊x⌋₊ : ℝ) + 3 / 2 * q * zz x ≤ x * (1 + (zz x)⁻¹ * q) := by
    intro q
    have hf := Nat.floor_le hx0.le
    have heq : 3 / 2 * (q : ℝ) * zz x = x * ((zz x)⁻¹ * q) := by
      apply (mul_right_cancel₀ hz0.ne')
      field_simp
      nlinarith [hzsq]
    rw [heq]
    nlinarith
  have hcompare : Sn h.natAbs (zz x) (zz x)⁻¹ / x ≤
      ∑ q ∈ (Icc 1 ⌊zz x⌋₊).filter Squarefree,
        w q / ((⌊x⌋₊ : ℝ) + 3 / 2 * q * zz x) := by
    unfold Sn
    rw [sum_div, sum_filter]
    apply sum_le_sum
    intro q hq
    by_cases hsq : Squarefree q
    · simp only [hsq, ite_true]
      rw [mul_assoc, ← hw q]
      have hd : 0 < 1 + (zz x)⁻¹ * (q : ℝ) := by positivity
      calc
        _ = w q / (x * (1 + (zz x)⁻¹ * q)) := by
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (hw0 q hq) (hD q) (hDbound q)
    · simp [hsq]
  have hc : (0 : ℝ) ≤ (sifted h x).card := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcompare hc
  have hfin : ((sifted h x).card : ℝ) * Sn h.natAbs (zz x) (zz x)⁻¹ / x ≤ 1 := by
    simpa only [mul_div_assoc] using hbound.trans hmv
  exact (div_le_one hx0).mp hfin

/-! ### Leaves: Lemmas 4, 5, 6 and the constants -/

/-- The local odd divisor count in the convolution on pages 97 and 98. -/
theorem tau1_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    tau1 (p^m) = if p = 2 then 1 else m+1 := by
  rw [tau1, Nat.divisors_prime_pow hp, Finset.filter_map, Finset.card_map]
  by_cases hp2 : p = 2
  · subst p
    have hodd (k : ℕ) : Odd (2^k) ↔ k = 0 := by
      by_cases hk : k = 0
      · simp [hk]
      · rw [Nat.odd_pow_iff hk]
        simp [hk]
    simp [hodd]
  · have hpo : Odd p := hp.odd_of_ne_two hp2
    simp [hp2, hpo.pow, Finset.filter_true_of_mem]


/-- The local odd divisor series used in Lemma 4 on pages 97 and 98. -/
theorem hasSum_tau1_prime_power {p : ℕ} (hp : p.Prime) :
    HasSum (fun m : ℕ => (tau1 (p^m) : ℝ)/(p : ℝ)^m)
      (if p = 2 then 2 else (p : ℝ)^2/((p : ℝ)-1)^2) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (1 : ℝ)/p := by positivity
  have hr1 : (1 : ℝ)/p < 1 := (div_lt_one (by linarith)).mpr hpR
  by_cases hp2 : p = 2
  · subst p
    have hh := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)
    convert hh using 1
    · funext m
      simp [tau1_prime_pow, hp, one_div_pow]
    · norm_num
  · have hh := hasSum_choose_mul_geometric_of_norm_lt_one 1
      (show ‖(1 : ℝ)/p‖ < 1 by rw [Real.norm_of_nonneg hr0]; exact hr1)
    convert hh using 1
    · funext m
      simp [tau1_prime_pow hp, hp2, one_div_pow, div_eq_mul_inv]
    · simp only [hp2, ite_false]
      norm_num only [Nat.reduceAdd]
      field_simp


/-- The local Euler mass of the divisor convolution on page 98. -/
theorem lemma4_local_factor {p : ℕ} (hp : p.Prime) :
    (∑' m : ℕ, (tau1 (p^m) : ℝ)/(p : ℝ)^m) * (∑' m : ℕ, g (p^m)) =
      if p = 2 then 2 else (p : ℝ)/((p : ℝ)-2) := by
  rw [(hasSum_tau1_prime_power hp).tsum_eq, (hasSum_g_prime_power hp).tsum_eq]
  by_cases hp2 : p = 2
  · subst p
    norm_num
  · have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hpR : (2 : ℝ) < p := by exact_mod_cast hpgt
    simp only [hp2, hpgt, ite_false, ite_true]
    field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ)-1 ≠ 0 by linarith,
      show (p : ℝ)-2 ≠ 0 by linarith]
    ring

/-- The prime factor redistribution in Vaughan 1977 pages 97 and 98.
A and B stand for a kernel value and the value after multiplication by p. -/
theorem lemma4_prime_reweight (p A B : ℝ) (hp : 2 < p) (hAB : B ≤ A) :
    A+2/(p-2)*B ≤ (p-1)/(p-2)*(A+1/(p-1)*B) := by
  have h1 : A+2/(p-2)*B = (A*(p-2)+2*B)/(p-2) := by
    field_simp [show p-2 ≠ 0 by linarith]
  have h2 : (p-1)/(p-2)*(A+1/(p-1)*B) = ((p-1)*A+B)/(p-2) := by
    field_simp [show p-1 ≠ 0 by linarith, show p-2 ≠ 0 by linarith]
  rw [h1,h2]
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ p-2)
  nlinarith

/-! ### The local factor of the pair sum -/

set_option maxHeartbeats 2000000 in
/-- `τ₁ 1 = 1`. -/
private theorem tau1_one : tau1 1 = 1 := by
  unfold tau1
  rw [Nat.divisors_one]
  decide

set_option maxHeartbeats 2000000 in
/-- The pair series is summable (product of two summable sequences). -/
private theorem summable_local_pair {p : ℕ} (hp : p.Prime) :
    Summable (fun z : ℕ × ℕ => g (p ^ z.1) * ((tau1 (p ^ z.2) : ℝ) / (p : ℝ) ^ z.2)) := by
  have hA := hasSum_g_prime_power hp
  have hB := hasSum_tau1_prime_power hp
  have hnorm : (fun x : ℕ => ‖g (p ^ x)‖) = fun x => g (p ^ x) := by
    funext m
    exact Real.norm_of_nonneg (g_nonneg _)
  have hnorm2 : (fun x : ℕ => ‖(tau1 (p ^ x) : ℝ) / (p : ℝ) ^ x‖) =
      fun x => (tau1 (p ^ x) : ℝ) / (p : ℝ) ^ x := by
    funext m
    exact Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))
  exact summable_mul_of_summable_norm (by rw [hnorm]; exact hA.summable)
    (by rw [hnorm2]; exact hB.summable)

set_option maxHeartbeats 2000000 in
/-- The two-variable local factor of pages 97-98: `Σ_{a,b} g(p^a) τ₁(p^b)/p^b` is `p/(p-2)`
for odd `p` and `2` for `p = 2` (there `τ₁(2^b) = 1`, so the divisor weight is geometric). -/
private theorem local_pair_factor {p : ℕ} (hp : p.Prime) :
    (∑' z : ℕ × ℕ, g (p ^ z.1) * ((tau1 (p ^ z.2) : ℝ) / (p : ℝ) ^ z.2)) =
      (if p = 2 then 2 else (p : ℝ) / ((p : ℝ) - 2)) := by
  have hA := hasSum_g_prime_power hp
  have hB := hasSum_tau1_prime_power hp
  have hnorm : (fun x : ℕ => ‖g (p ^ x)‖) = fun x => g (p ^ x) := by
    funext m
    exact Real.norm_of_nonneg (g_nonneg _)
  have hnorm2 : (fun x : ℕ => ‖(tau1 (p ^ x) : ℝ) / (p : ℝ) ^ x‖) =
      fun x => (tau1 (p ^ x) : ℝ) / (p : ℝ) ^ x := by
    funext m
    exact Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))
  have hmul := tsum_mul_tsum_of_summable_norm
    (f := fun m : ℕ => g (p ^ m)) (g := fun m : ℕ => (tau1 (p ^ m) : ℝ) / (p : ℝ) ^ m)
    (by rw [hnorm]; exact hA.summable) (by rw [hnorm2]; exact hB.summable)
  rw [← hmul, mul_comm]
  exact lemma4_local_factor hp

set_option maxHeartbeats 2000000 in
/-- The same sum with the trivial pair `(0,0)` removed: this is the coefficient attached to a
prime `p | q` when `Σ g d · τ₁ r / r` is grouped by the radical `q = sk (r*d)`. -/
private theorem local_pair_factor_sub {p : ℕ} (hp : p.Prime) :
    (∑' z : ℕ × ℕ,
        if z = (0, 0) then 0 else g (p ^ z.1) * ((tau1 (p ^ z.2) : ℝ) / (p : ℝ) ^ z.2)) =
      (if p = 2 then 2 else (p : ℝ) / ((p : ℝ) - 2)) - 1 := by
  have hsplit := (summable_local_pair hp).tsum_eq_add_tsum_ite ((0 : ℕ), (0 : ℕ))
  have hzero : g (p ^ (0 : ℕ)) * ((tau1 (p ^ (0 : ℕ)) : ℝ) / (p : ℝ) ^ (0 : ℕ)) = 1 := by
    rw [pow_zero, pow_zero, tau1_one, Nat.cast_one, div_one, g_one, mul_one]
  rw [local_pair_factor hp, hzero] at hsplit
  linarith

/-- The odd prime fibre contributes `2/(p-2)`, the coefficient of (3.4) and (3.5). -/
private theorem local_fibre_odd {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (∑' z : ℕ × ℕ,
        if z = (0, 0) then 0 else g (p ^ z.1) * ((tau1 (p ^ z.2) : ℝ) / (p : ℝ) ^ z.2)) =
      2 / ((p : ℝ) - 2) := by
  rw [local_pair_factor_sub hp, ite_eq_right (by omega : ¬ p = 2)]
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  have hne : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The `p = 2` fibre contributes `1`, the factor `1/(2-1)` of `Sn`. -/
private theorem local_fibre_two :
    (∑' z : ℕ × ℕ,
        if z = (0, 0) then 0 else
          g ((2 : ℕ) ^ z.1) * ((tau1 ((2 : ℕ) ^ z.2) : ℝ) / ((2 : ℕ) : ℝ) ^ z.2)) = 1 := by
  rw [local_pair_factor_sub Nat.prime_two, ite_eq_left (by norm_num : (2 : ℕ) = 2)]
  norm_num

/-! ### Multiplicativity of the divisor weight -/

/-- `τ₁` is multiplicative on coprime arguments: a divisor of `a*b` with `(a,b) = 1` splits
as `gcd d a * gcd d b`, and both parts are odd iff `d` is odd. -/
private theorem tau1_mul {a b : ℕ} (hab : a.Coprime b) : tau1 (a * b) = tau1 a * tau1 b := by
  have hg : ∀ x : ℕ, x ∣ a * b → x.gcd a * x.gcd b = x := fun x hx =>
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hab).mpr hx
  rw [tau1, tau1, tau1, ← Finset.card_product]
  refine Finset.card_bij (fun d _ => (d.gcd a, d.gcd b)) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, hab0⟩, hodd⟩ := hd
    have ha0 : a ≠ 0 := fun h => hab0 (by rw [h, Nat.zero_mul])
    have hb0 : b ≠ 0 := fun h => hab0 (by rw [h, Nat.mul_zero])
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, ha0⟩,
          Odd.of_dvd_nat hodd (Nat.gcd_dvd_left _ _)⟩
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hb0⟩,
          Odd.of_dvd_nat hodd (Nat.gcd_dvd_left _ _)⟩
  · intro d₁ h₁ d₂ h₂ heq
    rw [Finset.mem_filter, Nat.mem_divisors] at h₁ h₂
    have e1 := hg d₁ h₁.1.1
    have e2 := hg d₂ h₂.1.1
    have h1' : d₁.gcd a = d₂.gcd a := congrArg Prod.fst heq
    have h2' : d₁.gcd b = d₂.gcd b := congrArg Prod.snd heq
    rw [← e1, ← e2, h1', h2']
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hp1d, hp1odd⟩, hp2d, hp2odd⟩ := hp
    rw [Nat.mem_divisors] at hp1d hp2d
    obtain ⟨hp1dvd, ha0⟩ := hp1d
    obtain ⟨hp2dvd, hb0⟩ := hp2d
    have hca : a.Coprime p.2 := hab.coprime_dvd_right hp2dvd
    have hcb : b.Coprime p.1 := hab.symm.coprime_dvd_right hp1dvd
    refine ⟨p.1 * p.2, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul hp1dvd hp2dvd, mul_ne_zero ha0 hb0⟩,
        Odd.mul hp1odd hp2odd⟩
    · refine Prod.ext ?_ ?_
      · show (p.1 * p.2).gcd a = p.1
        refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right _ _) hp1dvd)
        have hc : ((p.1 * p.2).gcd a).Coprime p.2 :=
          hca.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        exact hc.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
      · show (p.1 * p.2).gcd b = p.2
        rw [Nat.mul_comm p.1 p.2]
        refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right _ _) hp2dvd)
        have hc : ((p.2 * p.1).gcd b).Coprime p.1 :=
          hcb.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        exact hc.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)

/-- `τ₁ p^m = m + 1` for odd `p`, already in the lab file, restated multiplicatively. -/
private theorem tau1_pow_mul {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (m : ℕ) :
    (tau1 (p ^ m) : ℝ) = (m : ℝ) + 1 := by
  rw [tau1_prime_pow hp, if_neg (by omega : ¬ p = 2)]
  push_cast
  ring

/-- The local weight at a prime power, `1` at exponent `0`, so that it is the local factor of the
multiplicative function `g` of (3.3). -/
private noncomputable def glocw (p m : ℕ) : ℝ := if m = 0 then 1 else gloc p m

/-- The local weight is `g` at the prime power. -/
private theorem glocw_eq_g {p : ℕ} (hp : p.Prime) (m : ℕ) : glocw p m = g (p ^ m) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [pow_zero, g_one, glocw, ite_eq_left rfl]
  · rw [glocw, ite_eq_right h.ne', g_prime_pow hp h]

/-- `g` is multiplicative over a product of distinct prime powers. -/
private theorem g_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℕ) :
    g (∏ p ∈ s, p ^ (a p)) = ∏ p ∈ s, g (p ^ (a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g_one]
  | insert p s' hpnot hrec =>
    rw [Finset.prod_insert hpnot, Finset.prod_insert hpnot]
    have hs' : ∀ q ∈ s', q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s')
    have hcop : (p ^ (a p)).Coprime (∏ q ∈ s', q ^ (a q)) := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      have hqp : q.Prime := hs' q hq
      have hne : p ≠ q := by rintro rfl; exact hpnot hq
      exact Nat.coprime_pow_primes (a p) (a q) hpp hqp hne
    rw [g_mul hcop, hrec hs']

/-- `τ₁` is multiplicative over a product of distinct prime powers. -/
private theorem tau1_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℕ) :
    tau1 (∏ p ∈ s, p ^ (a p)) = ∏ p ∈ s, tau1 (p ^ (a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tau1_one
  | insert p s' hpnot hrec =>
    rw [Finset.prod_insert hpnot, Finset.prod_insert hpnot]
    have hs' : ∀ q ∈ s', q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s')
    have hcop : (p ^ (a p)).Coprime (∏ q ∈ s', q ^ (a q)) := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      have hqp : q.Prime := hs' q hq
      have hne : p ≠ q := by rintro rfl; exact hpnot hq
      exact Nat.coprime_pow_primes (a p) (a q) hpp hqp hne
    rw [tau1_mul hcop, hrec hs']

/-- A number is the product of its prime powers. -/
private theorem prod_factorization_primeFactors {r : ℕ} (hr : r ≠ 0) :
    ∏ p ∈ r.primeFactors, p ^ (r.factorization p) = r :=
  Nat.support_factorization r ▸ Nat.prod_factorization_pow_eq_self hr

/-- The same product extended over a larger set of primes (the extra exponents are `0`). -/
private theorem prod_factorization_of_subset {q r : ℕ} (hr : r ≠ 0)
    (hsub : r.primeFactors ⊆ q.primeFactors) :
    ∏ p ∈ q.primeFactors, p ^ (r.factorization p) = r := by
  have h1 : ∏ p ∈ q.primeFactors, p ^ (r.factorization p)
      = ∏ p ∈ r.primeFactors, p ^ (r.factorization p) := by
    refine (Finset.prod_subset (s₁ := r.primeFactors) (s₂ := q.primeFactors)
      (f := fun p : ℕ => p ^ (r.factorization p)) hsub ?_).symm
    intro p hp hpr
    have hz : r.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact hpr (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hdvd, hr⟩)
    rw [hz]
    exact pow_zero p
  rw [h1, prod_factorization_primeFactors hr]

/-- The radical has the same prime factors as the number itself. -/
private theorem primeFactors_sk (m : ℕ) : (sk m).primeFactors = m.primeFactors := by
  rw [sk]
  exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- `sk 0 = 1`, so a pair with a zero entry never lies in a fibre with `q > 1`. -/
private theorem sk_zero : sk 0 = 1 := by
  simp [sk]

/-- Both entries of a pair with `sk (r*d) = q` are `q`-smooth (the support lemma for the fibre
decomposition of the pair sum). -/
private theorem primeFactors_subset_of_sk {q r d : ℕ} (hr : r ≠ 0) (hd : d ≠ 0) (h : sk (r * d) = q) :
    r.primeFactors ⊆ q.primeFactors ∧ d.primeFactors ⊆ q.primeFactors := by
  have hq : q.primeFactors = (r * d).primeFactors := by rw [← h, primeFactors_sk]
  have hrd : r * d ≠ 0 := mul_ne_zero hr hd
  constructor
  · rw [hq]
    exact Nat.primeFactors_mono (Nat.dvd_mul_right r d) hrd
  · rw [hq]
    exact Nat.primeFactors_mono (Nat.dvd_mul_left d r) hrd

/-- A product of prime powers with positive exponents has exactly those primes. -/
private theorem primeFactors_prod_prime_pow {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {c : ℕ → ℕ}
    (hc : ∀ p ∈ s, 1 ≤ c p) : (∏ p ∈ s, p ^ c p).primeFactors = s := by
  have hne : (∏ p ∈ s, p ^ c p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hdvd, -⟩
    obtain ⟨t, ht, hqt⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun p => p ^ c p)).mp hdvd
    have ht' : t.Prime := hs t ht
    have hqt' : q ∣ t := hq.prime.dvd_of_dvd_pow hqt
    rcases (Nat.dvd_prime ht').mp hqt' with h1 | h1
    · exact absurd h1 hq.ne_one
    · exact h1 ▸ ht
  · intro hq
    have hq' : q.Prime := hs q hq
    refine ⟨hq', ?_, hne⟩
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun p => p ^ c p) hq)
    simpa using pow_dvd_pow q (hc q hq)

/-- The radical of a product of prime powers with positive exponents, the converse direction of
`primeFactors_subset_of_sk`: this is how a pair is rebuilt from its exponent family. -/
private theorem sk_prod_prime_pow {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {c : ℕ → ℕ}
    (hc : ∀ p ∈ s, 1 ≤ c p) : sk (∏ p ∈ s, p ^ c p) = ∏ p ∈ s, p := by
  rw [sk, primeFactors_prod_prime_pow hs hc]

/-- **The weight of a pair, factorized over the primes of `q`.**  For a squarefree `q` and
`r, d ≠ 0` supported on the primes of `q`, the weight `g d · τ₁ r / r` of the pair sum is the
product of the two-variable local weights over `q.primeFactors`.  This is the pointwise half of
`fibre_sum`: the map `(r,d) ↦ (p ↦ (v_p d, v_p r))` turns the weight into a product. -/
private theorem weight_factor {q r d : ℕ} (hr : r ≠ 0) (hd : d ≠ 0)
    (hsub : r.primeFactors ⊆ q.primeFactors ∧ d.primeFactors ⊆ q.primeFactors) :
    g d * (tau1 r : ℝ) / (r : ℝ)
      = ∏ p ∈ q.primeFactors,
          (glocw p (d.factorization p) *
            ((tau1 (p ^ r.factorization p) : ℝ) / (p : ℝ) ^ r.factorization p)) := by
  have hs : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hrprod : r = ∏ p ∈ q.primeFactors, p ^ r.factorization p :=
    (prod_factorization_of_subset hr hsub.1).symm
  have hdprod : d = ∏ p ∈ q.primeFactors, p ^ d.factorization p :=
    (prod_factorization_of_subset hd hsub.2).symm
  have hgd : g d = ∏ p ∈ q.primeFactors, glocw p (d.factorization p) := by
    nth_rewrite 1 [hdprod]
    rw [g_prod hs]
    exact Finset.prod_congr rfl (fun p hp => (glocw_eq_g (hs p hp) _).symm)
  have htr : tau1 r = ∏ p ∈ q.primeFactors, tau1 (p ^ r.factorization p) := by
    nth_rewrite 1 [hrprod]
    exact tau1_prod hs _
  have hrcast : (r : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) ^ r.factorization p := by
    nth_rewrite 1 [hrprod]
    push_cast
    rfl
  rw [hgd, hrcast, htr]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
  ring

/-- For a squarefree number the radical is the number itself. -/
private theorem sk_self {q : ℕ} (hq : Squarefree q) : sk q = q := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hfac : ∀ p, q.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hq0).mp hq
  have h2 : ∏ p ∈ q.primeFactors, p ^ q.factorization p = ∏ p ∈ q.primeFactors, p := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hne : q.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    have h3 : q.factorization p = 1 := by
      have := hfac p
      omega
    rw [h3, pow_one]
  rw [sk]
  exact h2.symm.trans (prod_factorization_primeFactors hq0)

/-- A prime of the radical divides the number: the divisibility side of the support
characterization. -/
private theorem dvd_of_mem_primeFactors_sk {q r d p : ℕ} (hp : p ∈ q.primeFactors)
    (h : sk (r * d) = q) : p ∣ r * d := by
  have h1 : p ∈ (sk (r * d)).primeFactors := by rw [h]; exact hp
  rw [primeFactors_sk] at h1
  exact (Nat.mem_primeFactors.mp h1).2.1

/-- Rebuilding from an exponent family gives back the radical: the surjectivity half of the
support bijection, in the `Finset` form used by the fibre decomposition. -/
private theorem sk_rebuild {q : ℕ} (hq : Squarefree q) (c : ℕ → ℕ)
    (hc : ∀ p ∈ q.primeFactors, 1 ≤ c p) :
    sk (∏ p ∈ q.primeFactors, p ^ c p) = q := by
  rw [sk_prod_prime_pow (fun p hp => Nat.prime_of_mem_primeFactors hp) hc]
  simpa [sk] using sk_self hq

/-- Exponent recovery: the exponent of `q` in a product of prime powers over a set of primes is
the exponent attached to `q`.  This is the roundtrip half of the fibre correspondence. -/
private theorem factorization_prod_prime_pow {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℕ)
    {q : ℕ} (hq : q ∈ s) : (∏ p ∈ s, p ^ c p).factorization q = c q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hq
  | insert p s' hpnot hrec =>
    have hp' : p.Prime := hs p (Finset.mem_insert_self p s')
    have hs' : ∀ x ∈ s', x.Prime := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hne2 : (∏ x ∈ s', x ^ c x) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (hs' x hx).ne_zero)
    rw [Finset.prod_insert hpnot, Nat.factorization_mul (pow_ne_zero _ hp'.ne_zero) hne2,
      Finsupp.add_apply]
    rcases Finset.mem_insert.mp hq with hqp | hq'
    · rw [hqp]
      have hz : (∏ x ∈ s', x ^ c x).factorization p = 0 := by
        have hnp : ¬ p ∣ ∏ x ∈ s', x ^ c x := by
          intro hdvd
          obtain ⟨x, hx, hpx⟩ := (Prime.dvd_finsetProd_iff hp'.prime (fun x => x ^ c x)).mp hdvd
          have hx' : x.Prime := hs' x hx
          have h1 : p ∣ x := hp'.prime.dvd_of_dvd_pow hpx
          rcases (Nat.dvd_prime hx').mp h1 with h | h
          · exact hp'.ne_one h
          · exact hpnot (h ▸ hx)
        exact Nat.factorization_eq_zero_of_not_dvd hnp
      rw [Nat.factorization_pow_self hp', hz, add_zero]
    · have hz : (p ^ c p).factorization q = 0 := by
        have hnp : ¬ q ∣ p ^ c p := by
          intro hdvd
          have hq'p : q.Prime := hs q (Finset.mem_insert_of_mem hq')
          have h1 : q ∣ p := hq'p.prime.dvd_of_dvd_pow hdvd
          rcases (Nat.dvd_prime hp').mp h1 with h | h
          · exact hq'p.ne_one h
          · exact hpnot (h ▸ hq')
        exact Nat.factorization_eq_zero_of_not_dvd hnp
      rw [hz, zero_add, hrec hs' hq']

/-- The exponent family of a pair: the forward map of the fibre correspondence, sending `(r,d)`
to `p ↦ (v_p d, v_p r)`. -/
private noncomputable def famOfPair {q : ℕ} (z : ℕ × ℕ) : Π _ : q.primeFactors, ℕ × ℕ :=
  fun p => (z.2.factorization (p : ℕ), z.1.factorization (p : ℕ))

/-- Inside the fibre `sk (z.1*z.2) = q`, every coordinate of the exponent family is nonzero
(each `p ∣ q` divides `r·d`, so it divides `r` or `d`). -/
private theorem famOfPair_ne_zero {q : ℕ} {z : ℕ × ℕ} (hz1 : z.1 ≠ 0) (hz2 : z.2 ≠ 0)
    (h : sk (z.1 * z.2) = q) (p : q.primeFactors) : famOfPair (q := q) z p ≠ (0, 0) := by
  have hp : (p : ℕ) ∈ q.primeFactors := p.2
  have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors hp
  have hdvd : (p : ℕ) ∣ z.1 * z.2 := dvd_of_mem_primeFactors_sk hp h
  intro h0
  have h2 : z.1.factorization (p : ℕ) = 0 := by
    simpa [famOfPair] using congrArg Prod.snd h0
  have h1 : z.2.factorization (p : ℕ) = 0 := by
    simpa [famOfPair] using congrArg Prod.fst h0
  rcases (Prime.dvd_mul hpp.prime).mp hdvd with hd | hd
  · exact (Nat.Prime.factorization_pos_of_dvd hpp hz1 hd).ne' h2
  · exact (Nat.Prime.factorization_pos_of_dvd hpp hz2 hd).ne' h1

/-- The pair rebuilt from an `ℕ`-indexed exponent family: the backward map of the fibre
correspondence, indexed on `ℕ` so that every product below is a plain `Finset` product over
`q.primeFactors` (the first component of a family entry is the `d`-exponent, the second the
`r`-exponent, matching `famOfPair`). -/
private noncomputable def zOfFam {q : ℕ} (g : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  (∏ y ∈ q.primeFactors, y ^ (g y).2, ∏ y ∈ q.primeFactors, y ^ (g y).1)

/-- Exponent recovery for the `d`-component of a rebuilt pair. -/
private theorem factorization_zOfFam_fst {q : ℕ} (g : ℕ → ℕ × ℕ) {p : ℕ}
    (hp : p ∈ q.primeFactors) :
    (∏ y ∈ q.primeFactors, y ^ (g y).1).factorization p = (g p).1 :=
  factorization_prod_prime_pow (fun y hy => Nat.prime_of_mem_primeFactors hy)
    (fun y => (g y).1) hp

/-- Exponent recovery for the `r`-component of a rebuilt pair. -/
private theorem factorization_zOfFam_snd {q : ℕ} (g : ℕ → ℕ × ℕ) {p : ℕ}
    (hp : p ∈ q.primeFactors) :
    (∏ y ∈ q.primeFactors, y ^ (g y).2).factorization p = (g p).2 :=
  factorization_prod_prime_pow (fun y hy => Nat.prime_of_mem_primeFactors hy)
    (fun y => (g y).2) hp

/-- The rebuilt pair lies in the fibre: surjectivity of the correspondence, in `Finset` form. -/
private theorem sk_zOfFam {q : ℕ} (hq : Squarefree q) (g : ℕ → ℕ × ℕ)
    (hg : ∀ y ∈ q.primeFactors, 1 ≤ (g y).1 + (g y).2) :
    sk ((zOfFam (q := q) g).1 * (zOfFam (q := q) g).2) = q := by
  have hprod : (zOfFam (q := q) g).1 * (zOfFam (q := q) g).2
      = ∏ y ∈ q.primeFactors, y ^ ((g y).1 + (g y).2) := by
    rw [zOfFam, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun y _ => ?_)
    rw [← pow_add, add_comm]
  rw [hprod]
  exact sk_rebuild hq (fun y => (g y).1 + (g y).2) hg

/-- Roundtrip: rebuilding a pair of the fibre from its exponent family gives the pair back. -/
private theorem zOfFam_famOfPair {q : ℕ} {z : ℕ × ℕ} (hz1 : z.1 ≠ 0) (hz2 : z.2 ≠ 0)
    (h : sk (z.1 * z.2) = q) :
    zOfFam (q := q) (fun y => (z.2.factorization y, z.1.factorization y)) = z := by
  have hsub := primeFactors_subset_of_sk hz1 hz2 h
  have h1 : (∏ y ∈ q.primeFactors, y ^ (z.1.factorization y)) = z.1 :=
    prod_factorization_of_subset hz1 hsub.1
  have h2 : (∏ y ∈ q.primeFactors, y ^ (z.2.factorization y)) = z.2 :=
    prod_factorization_of_subset hz2 hsub.2
  rw [zOfFam, h2, h1]

/-- Roundtrip in the other direction: the exponent family of a rebuilt pair is the family itself
(the family is only read on `q.primeFactors`). -/
private theorem famOfPair_zOfFam {q : ℕ} (g : ℕ → ℕ × ℕ) (y : q.primeFactors) :
    famOfPair (q := q) (zOfFam (q := q) g) y = g (y : ℕ) := by
  simp only [famOfPair, zOfFam]
  rw [factorization_zOfFam_fst g y.2, factorization_zOfFam_snd g y.2]

/-- A rebuilt pair has nonzero components. -/
private theorem zOfFam_ne_zero {q : ℕ} (φ : ℕ → ℕ × ℕ) :
    (zOfFam (q := q) φ).1 ≠ 0 ∧ (zOfFam (q := q) φ).2 ≠ 0 := by
  have hf : ∀ y ∈ q.primeFactors, y ≠ 0 := fun y hy => (Nat.pos_of_mem_primeFactors hy).ne'
  constructor
  · rw [zOfFam]
    exact Finset.prod_ne_zero_iff.mpr (fun y hy => pow_ne_zero _ (hf y hy))
  · rw [zOfFam]
    exact Finset.prod_ne_zero_iff.mpr (fun y hy => pow_ne_zero _ (hf y hy))

/-- A rebuilt pair is supported on the primes of `q`. -/
private theorem primeFactors_zOfFam {q : ℕ} (φ : ℕ → ℕ × ℕ) :
    (zOfFam (q := q) φ).1.primeFactors ⊆ q.primeFactors ∧
      (zOfFam (q := q) φ).2.primeFactors ⊆ q.primeFactors := by
  have hmain : ∀ (c : ℕ → ℕ), (∏ y ∈ q.primeFactors, y ^ c y).primeFactors ⊆ q.primeFactors := by
    intro c p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hne : (∏ y ∈ q.primeFactors, y ^ c y) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr
        (fun y hy => pow_ne_zero _ (Nat.pos_of_mem_primeFactors hy).ne')
    have hdvd : p ∣ ∏ y ∈ q.primeFactors, y ^ c y := (Nat.mem_primeFactors.mp hp).2.1
    obtain ⟨y, hy, hpy⟩ := (Prime.dvd_finsetProd_iff hpp.prime (fun y => y ^ c y)).mp hdvd
    have h1 : p ∣ y := hpp.prime.dvd_of_dvd_pow hpy
    rcases (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hy)).mp h1 with h | h
    · exact absurd h hpp.ne_one
    · exact h ▸ hy
  exact ⟨hmain _, hmain _⟩

/-- The weight of a rebuilt pair in the family form used by the Euler product: the pair weight is
the product over `q.primeFactors` of the local weights of the family entries. -/
private theorem weight_zOfFam {q : ℕ} (φ : ℕ → ℕ × ℕ) :
    g (zOfFam (q := q) φ).2 * (tau1 (zOfFam (q := q) φ).1 : ℝ)
        / ((zOfFam (q := q) φ).1 : ℝ)
      = ∏ p ∈ q.primeFactors,
          (glocw p (φ p).1 * ((tau1 (p ^ (φ p).2) : ℝ) / (p : ℝ) ^ (φ p).2)) := by
  rw [weight_factor (q := q) (r := (zOfFam (q := q) φ).1) (d := (zOfFam (q := q) φ).2)
    (zOfFam_ne_zero φ).1 (zOfFam_ne_zero φ).2 (primeFactors_zOfFam φ)]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  simp only [zOfFam]
  rw [factorization_zOfFam_fst φ hp, factorization_zOfFam_snd φ hp]

/-- Splitting off the value at an inserted point, for a constant fibre: the branches of the `if`
have the same type, so (unlike Mathlib's `Finset.prodPiInsert`) no `cast` is inserted and the
evaluation lemmas hold by `dif_pos`/`dif_neg`. -/
private def famSplitEquiv {s : Finset ℕ} {a : ℕ} (ha : a ∉ s) :
    ((ℕ × ℕ) × ((i : ℕ) → i ∈ s → ℕ × ℕ)) ≃ ((i : ℕ) → i ∈ insert a s → ℕ × ℕ) where
  toFun x := fun i hi => if h : i = a then x.1 else x.2 i (Finset.mem_of_mem_insert_of_ne hi h)
  invFun φ := (φ a (Finset.mem_insert_self a s), fun i hi => φ i (Finset.mem_insert_of_mem hi))
  left_inv := by
    rintro ⟨v, ψ⟩
    simp only [Prod.mk.injEq]
    refine ⟨dif_pos trivial, ?_⟩
    funext i hi
    rw [dif_neg (show (i : ℕ) ≠ a from fun h => ha (h ▸ hi))]
  right_inv := by
    intro φ
    funext i hi
    by_cases h : i = a
    · subst h
      simp
    · simp [h]

/-- Splitting a `Finset` product at an inserted element, for a function on the subtype of the
insertion (the `dite`-extension is unavoidable when the function is only defined on the subtype).
This is the step the Euler-product induction needs; Mathlib has no such lemma. -/
private theorem prod_insert_ite {s : Finset ℕ} {a : ℕ} (ha : a ∉ s) (F : ↥(insert a s) → ℝ) :
    (∏ x ∈ insert a s, (if h : x ∈ insert a s then F ⟨x, h⟩ else 1))
      = F ⟨a, Finset.mem_insert_self a s⟩
        * ∏ x ∈ s, (if h : x ∈ s then F ⟨x, Finset.mem_insert_of_mem h⟩ else 1) := by
  rw [Finset.prod_insert ha, dif_pos (Finset.mem_insert_self a s)]
  congr 1
  refine Finset.prod_congr rfl (fun x hx => ?_)
  rw [dif_pos (Finset.mem_insert_of_mem hx), dif_pos hx]

/-- The prime-indexed Euler product: summing a product of local weights over all exponent
families factorizes into the product of the local sums. -/
private theorem euler_prod_pi {s : Finset ℕ} (W : ℕ → ℕ × ℕ → ℝ)
    (hWnn : ∀ p ∈ s, ∀ ab : ℕ × ℕ, 0 ≤ W p ab)
    (hW : ∀ p ∈ s, Summable fun ab : ℕ × ℕ => W p ab) :
    Summable (fun φ : (i : ℕ) → i ∈ s → ℕ × ℕ =>
        ∏ x ∈ s, (if h : x ∈ s then W x (φ x h) else 1)) ∧
      (∑' φ : (i : ℕ) → i ∈ s → ℕ × ℕ,
          ∏ x ∈ s, (if h : x ∈ s then W x (φ x h) else 1))
        = ∏ p ∈ s, ∑' ab : ℕ × ℕ, W p ab := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hsub : Subsingleton ((i : ℕ) → i ∈ (∅ : Finset ℕ) → ℕ × ℕ) := by
      constructor
      intro f g
      funext p hp
      exact absurd hp (by simp)
    have hzero : ((i : ℕ) → i ∈ (∅ : Finset ℕ) → ℕ × ℕ) := fun p hp => absurd hp (by simp)
    constructor
    · have hb : ∀ t : Finset ((i : ℕ) → i ∈ (∅ : Finset ℕ) → ℕ × ℕ),
          ∑ _x ∈ t, (1 : ℝ) ≤ 1 := by
        intro t
        have h1 : t.card ≤ 1 := Finset.card_le_one.mpr (fun x _ y _ => hsub.elim x y)
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast h1
      exact summable_of_sum_le (fun _ => zero_le_one) hb
    · rw [tsum_eq_single hzero (fun b hb => absurd (hsub.elim b hzero) hb)]
      simp
  | insert a s' ha ih =>
    have hmem : ∀ p ∈ s', p ∈ insert a s' := fun p hp => Finset.mem_insert_of_mem hp
    obtain ⟨ihSum, ihVal⟩ := ih (fun p hp => hWnn p (hmem p hp)) (fun p hp => hW p (hmem p hp))
    set G : ((i : ℕ) → i ∈ s' → ℕ × ℕ) → ℝ :=
      fun ψ => ∏ x ∈ s', (if h : x ∈ s' then W x (ψ x h) else 1) with hG
    have hGnn : ∀ ψ, 0 ≤ G ψ := by
      intro ψ
      rw [hG]
      refine Finset.prod_nonneg (fun x hx => ?_)
      by_cases h : x ∈ s'
      · rw [dif_pos h]
        exact hWnn x (hmem x hx) _
      · rw [dif_neg h]
        exact zero_le_one
    have hWa : Summable (fun v : ℕ × ℕ => W a v) := hW a (Finset.mem_insert_self a s')
    have hWanorm : Summable (fun v : ℕ × ℕ => ‖W a v‖) := by
      refine hWa.congr (fun v => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnn a (Finset.mem_insert_self a s') v)]
    have hGnorm : Summable (fun ψ => ‖G ψ‖) := by
      refine ihSum.congr (fun ψ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnn ψ)]
    let e := famSplitEquiv (s := s') (a := a) ha
    have hstep : ∀ (v : ℕ × ℕ) (ψ : (i : ℕ) → i ∈ s' → ℕ × ℕ),
        (∏ x ∈ insert a s', (if h : x ∈ insert a s' then W x ((e (v, ψ)) x h) else 1))
          = W a v * G ψ := by
      intro v ψ
      rw [prod_insert_ite ha (F := fun y : ↥(insert a s') => W (y : ℕ) ((e (v, ψ)) (y : ℕ) y.2))]
      have h1 : (e (v, ψ)) a (Finset.mem_insert_self a s') = v := by
        simp only [e, famSplitEquiv, Equiv.coe_fn_mk]
        rw [dif_pos trivial]
      have h2 : ∀ (x : ℕ) (hx : x ∈ s'),
          (e (v, ψ)) x (Finset.mem_insert_of_mem hx) = ψ x hx := by
        intro x hx
        simp only [e, famSplitEquiv, Equiv.coe_fn_mk]
        rw [dif_neg (show x ≠ a from fun h => ha (h ▸ hx))]
      rw [h1, hG]
      congr 1
      refine Finset.prod_congr rfl (fun x hx => ?_)
      rw [dif_pos hx, dif_pos hx]
      simp only [Subtype.coe_mk]
      rw [h2 x hx]
    constructor
    · have h1 : Summable (fun z : (ℕ × ℕ) × ((i : ℕ) → i ∈ s' → ℕ × ℕ) => W a z.1 * G z.2) :=
        summable_mul_of_summable_norm hWanorm hGnorm
      have h2 : Summable (fun z : (ℕ × ℕ) × ((i : ℕ) → i ∈ s' → ℕ × ℕ) =>
          ∏ x ∈ insert a s', (if h : x ∈ insert a s' then W x ((e z) x h) else 1)) := by
        refine h1.congr (fun z => ?_)
        exact (hstep z.1 z.2).symm
      exact (Equiv.summable_iff (e := e)).mp h2
    · rw [← e.tsum_eq (fun φ : (i : ℕ) → i ∈ insert a s' → ℕ × ℕ =>
        ∏ x ∈ insert a s', (if h : x ∈ insert a s' then W x (φ x h) else 1))]
      have hz : ∀ z : (ℕ × ℕ) × ((i : ℕ) → i ∈ s' → ℕ × ℕ), (∏ x ∈ insert a s',
          (if h : x ∈ insert a s' then W x ((e z) x h) else 1)) = W a z.1 * G z.2 :=
        fun z => hstep z.1 z.2
      simp only [hz]
      rw [← tsum_mul_tsum_of_summable_norm hWanorm hGnorm, ihVal, Finset.prod_insert ha]

/-- The local weight of the fibre sum at a prime, in the form consumed by `euler_prod_pi`. -/
private noncomputable def lw (p : ℕ) (ab : ℕ × ℕ) : ℝ :=
  if ab = (0, 0) then 0 else g (p ^ ab.1) * ((tau1 (p ^ ab.2) : ℝ) / (p : ℝ) ^ ab.2)

/-- The local weight is nonnegative. -/
private theorem lw_nonneg (p : ℕ) (ab : ℕ × ℕ) : 0 ≤ lw p ab := by
  simp only [lw]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (g_nonneg _) (div_nonneg (Nat.cast_nonneg _) (by positivity))

/-- The local weight is summable (it is the pair sum of the local factors). -/
private theorem lw_summable {p : ℕ} (hp : p.Prime) : Summable (lw p) := by
  refine Summable.of_nonneg_of_le (fun ab => lw_nonneg p ab) (fun ab => ?_)
    (summable_local_pair hp)
  simp only [lw]
  split_ifs with h0
  · rw [h0]
    simp [g_one, tau1_one]
  · exact le_rfl

/-- The value of the local sum: `2/(p-2)` for odd `p`, `1` for `p = 2`. -/
private theorem lw_tsum {p : ℕ} (hp : p.Prime) :
    (∑' ab : ℕ × ℕ, lw p ab) = if p = 2 then 1 else 2 / ((p : ℝ) - 2) := by
  simp only [lw]
  rcases eq_or_ne p 2 with rfl | h2
  · rw [show (∑' ab : ℕ × ℕ, if ab = (0, 0) then (0 : ℝ)
        else g ((2 : ℕ) ^ ab.1) * ((tau1 ((2 : ℕ) ^ ab.2) : ℝ) / ((2 : ℕ) : ℝ) ^ ab.2))
        = 1 from local_fibre_two, if_pos rfl]
  · rw [if_neg h2]
    have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    exact local_fibre_odd hp hp2

/-- **The weight of a pair as the product of local weights.**  In the `Finset`-indexed form used
by `euler_prod_pi`: for a pair in the fibre `sk (r*d) = q`, the pair weight is the product over
`q.primeFactors` of the local weight `lw` evaluated at the exponent pair `(v_x d, v_x r)`.  The
hypothesis `sk (r*d) = q` is what makes every such exponent pair nonzero. -/
private theorem weight_famOfPair {q r d : ℕ} (hr : r ≠ 0) (hd : d ≠ 0) (hsk : sk (r * d) = q) :
    g d * (tau1 r : ℝ) / (r : ℝ)
      = ∏ x ∈ q.primeFactors,
          (if h : x ∈ q.primeFactors then lw x (d.factorization x, r.factorization x) else 1) := by
  rw [weight_factor hr hd (primeFactors_subset_of_sk hr hd hsk)]
  refine Finset.prod_congr rfl (fun x hx => ?_)
  have hne : (d.factorization x, r.factorization x) ≠ (0, 0) := by
    intro h0
    have h1 : d.factorization x = 0 := by simpa using congrArg Prod.fst h0
    have h2 : r.factorization x = 0 := by simpa using congrArg Prod.snd h0
    have hpp : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
    have hdvd : x ∣ r * d := dvd_of_mem_primeFactors_sk hx hsk
    rcases (Prime.dvd_mul hpp.prime).mp hdvd with hd' | hd'
    · exact (Nat.Prime.factorization_pos_of_dvd hpp hr hd').ne' h2
    · exact (Nat.Prime.factorization_pos_of_dvd hpp hd hd').ne' h1
  rw [dif_pos hx, lw, if_neg hne, glocw_eq_g (Nat.prime_of_mem_primeFactors hx)]

/-- The pair-to-family map in the `Finset`-indexed form of `euler_prod_pi`. -/
private def toFam {q : ℕ} (z : ℕ × ℕ) : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ :=
  fun i _ => (z.2.factorization i, z.1.factorization i)

/-- The family-to-pair map: rebuild the pair from the exponents of the family. -/
private noncomputable def ofFam {q : ℕ} (φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ) : ℕ × ℕ :=
  ((∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then (φ x h).2 else 0)),
   (∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then (φ x h).1 else 0)))

/-- A pair in a fibre with `q > 1` has nonzero components. -/
private theorem fibre_fst_ne {q : ℕ} (hq1 : 1 < q) {z : ℕ × ℕ} (h : sk (z.1 * z.2) = q) : z.1 ≠ 0 := by
  intro h0
  rw [h0, Nat.zero_mul, sk_zero] at h
  omega

private theorem fibre_snd_ne {q : ℕ} (hq1 : 1 < q) {z : ℕ × ℕ} (h : sk (z.1 * z.2) = q) : z.2 ≠ 0 := by
  intro h0
  rw [h0, Nat.mul_zero, sk_zero] at h
  omega

/-- Roundtrip: rebuilding a fibre pair from its exponent family gives the pair back. -/
private theorem ofFam_toFam {q : ℕ} (hq1 : 1 < q) {z : ℕ × ℕ} (h : sk (z.1 * z.2) = q) :
    ofFam (q := q) (toFam (q := q) z) = z := by
  have hz1 := fibre_fst_ne hq1 h
  have hz2 := fibre_snd_ne hq1 h
  have hsub := primeFactors_subset_of_sk hz1 hz2 h
  refine Prod.ext ?_ ?_
  · -- first component: `∏ x, x ^ v_x z.1 = z.1`
    show (∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then z.1.factorization x else 0))
      = z.1
    rw [show (∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then z.1.factorization x else 0))
        = ∏ x ∈ q.primeFactors, x ^ z.1.factorization x from
        Finset.prod_congr rfl (fun x hx => by rw [dif_pos hx])]
    exact prod_factorization_of_subset hz1 hsub.1
  · show (∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then z.2.factorization x else 0))
      = z.2
    rw [show (∏ x ∈ q.primeFactors, x ^ (if h : x ∈ q.primeFactors then z.2.factorization x else 0))
        = ∏ x ∈ q.primeFactors, x ^ z.2.factorization x from
        Finset.prod_congr rfl (fun x hx => by rw [dif_pos hx])]
    exact prod_factorization_of_subset hz2 hsub.2

/-- Roundtrip: the exponent family of a rebuilt pair is the family itself. -/
private theorem toFam_ofFam {q : ℕ} (hq : Squarefree q)
    (φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ) (x : ℕ) (hx : x ∈ q.primeFactors) :
    toFam (q := q) (ofFam (q := q) φ) x hx = φ x hx := by
  have hs : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h1 : (∏ y ∈ q.primeFactors,
      y ^ (if h : y ∈ q.primeFactors then (φ y h).2 else 0)).factorization x = (φ x hx).2 := by
    rw [factorization_prod_prime_pow hs
      (fun y => if h : y ∈ q.primeFactors then (φ y h).2 else 0) hx, dif_pos hx]
  have h2 : (∏ y ∈ q.primeFactors,
      y ^ (if h : y ∈ q.primeFactors then (φ y h).1 else 0)).factorization x = (φ x hx).1 := by
    rw [factorization_prod_prime_pow hs
      (fun y => if h : y ∈ q.primeFactors then (φ y h).1 else 0) hx, dif_pos hx]
  show ((ofFam (q := q) φ).2.factorization x, (ofFam (q := q) φ).1.factorization x) = φ x hx
  simp only [ofFam, h1, h2]

/-- A rebuilt pair from a *supported* family lies in the fibre. -/
private theorem sk_ofFam {q : ℕ} (hq : Squarefree q)
    (φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ)
    (hφ : ∀ (x : ℕ) (hx : x ∈ q.primeFactors), φ x hx ≠ (0, 0)) :
    sk ((ofFam (q := q) φ).1 * (ofFam (q := q) φ).2) = q := by
  have hs : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod : (ofFam (q := q) φ).1 * (ofFam (q := q) φ).2
      = ∏ x ∈ q.primeFactors,
          x ^ ((if h : x ∈ q.primeFactors then (φ x h).2 else 0)
            + (if h : x ∈ q.primeFactors then (φ x h).1 else 0)) := by
    simp only [ofFam, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun x hx => ?_)
    rw [← pow_add]
  have hpos : ∀ x ∈ q.primeFactors, 1 ≤ (if h : x ∈ q.primeFactors then (φ x h).2 else 0)
      + (if h : x ∈ q.primeFactors then (φ x h).1 else 0) := by
    intro x hx
    rw [dif_pos hx, dif_pos hx]
    have hne := hφ x hx
    rcases hp : φ x hx with ⟨a, b⟩
    have hne' : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨h1, h2⟩
      exact hne (by rw [hp, h1, h2])
    simp only
    omega
  rw [hprod, sk_prod_prime_pow hs hpos]
  simpa [sk] using sk_self hq

/-- The exponents of a rebuilt pair are nonnegative automatically; the `lw` product vanishes off
the supported families, so the family sum may be restricted to them. -/
private theorem prod_lw_eq_zero_of_not_supported {q : ℕ}
    (φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ)
    (hφ : ¬ ∀ (x : ℕ) (hx : x ∈ q.primeFactors), φ x hx ≠ (0, 0)) :
    (∏ x ∈ q.primeFactors, (if h : x ∈ q.primeFactors then lw x (φ x h) else 1)) = 0 := by
  push_neg at hφ
  obtain ⟨x, hx, h0⟩ := hφ
  refine Finset.prod_eq_zero hx ?_
  rw [dif_pos hx, h0, lw]
  simp

/-- The fibre correspondence as an equivalence of subtypes. -/
private noncomputable def fibreEquiv {q : ℕ} (hq : Squarefree q) (hq1 : 1 < q) :
    {z : ℕ × ℕ // sk (z.1 * z.2) = q} ≃
      {φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ //
        ∀ (x : ℕ) (hx : x ∈ q.primeFactors), φ x hx ≠ (0, 0)} where
  toFun z := ⟨toFam (q := q) z.1, by
    intro x hx
    have hsk := z.2
    have hdvd : x ∣ z.1.1 * z.1.2 := dvd_of_mem_primeFactors_sk hx hsk
    have hpp : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
    have h1 := fibre_fst_ne hq1 hsk
    have h2 := fibre_snd_ne hq1 hsk
    intro h0
    have hz1 : z.1.1.factorization x = 0 := by simpa only [toFam] using congrArg Prod.snd h0
    have hz2 : z.1.2.factorization x = 0 := by simpa only [toFam] using congrArg Prod.fst h0
    rcases (Prime.dvd_mul hpp.prime).mp hdvd with hd | hd
    · exact (Nat.Prime.factorization_pos_of_dvd hpp h1 hd).ne' hz1
    · exact (Nat.Prime.factorization_pos_of_dvd hpp h2 hd).ne' hz2⟩
  invFun φ := ⟨ofFam (q := q) φ.1, sk_ofFam hq φ.1 φ.2⟩
  left_inv z := by
    refine Subtype.ext ?_
    exact ofFam_toFam hq1 z.2
  right_inv φ := by
    refine Subtype.ext ?_
    funext x hx
    exact toFam_ofFam hq φ.1 x hx

/-- **`fibre_sum`, from `q > 1`.**  The fibre sum grouped by the radical equals the product of the
local sums. -/
private theorem fibre_sum_gt_one {q : ℕ} (hq : Squarefree q) (hq1 : 1 < q) :
    (∑' z : ℕ × ℕ, if sk (z.1 * z.2) = q then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0)
      = ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) := by
  classical
  set S := {z : ℕ × ℕ | sk (z.1 * z.2) = q} with hS
  set T := {φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ |
      ∀ (x : ℕ) (hx : x ∈ q.primeFactors), φ x hx ≠ (0, 0)} with hT
  set F : ℕ × ℕ → ℝ := fun z => if sk (z.1 * z.2) = q then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0
    with hF
  set G : ((i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ) → ℝ :=
    fun φ => ∏ x ∈ q.primeFactors, (if h : x ∈ q.primeFactors then lw x (φ x h) else 1) with hG
  -- pair side: restrict to the fibre subtype
  have hsupp : Function.support F ⊆ S := by
    intro z hz
    by_contra hcon
    have hc : ¬ (sk (z.1 * z.2) = q) := by simpa [hS] using hcon
    exact hz (by simp [hF, hc])
  have hpair : (∑' z : ℕ × ℕ, F z) = ∑' z : S, F z.1 :=
    (tsum_subtype_eq_of_support_subset (s := S) (f := F) hsupp).symm
  -- the pointwise identity on the fibre
  have hpt : ∀ z : S, F z.1 = G (toFam (q := q) z.1) := by
    intro z
    have hsk : sk ((↑z : ℕ × ℕ).1 * (↑z : ℕ × ℕ).2) = q := z.2
    show (if sk ((↑z : ℕ × ℕ).1 * (↑z : ℕ × ℕ).2) = q then
        g (↑z : ℕ × ℕ).2 * (tau1 (↑z : ℕ × ℕ).1 : ℝ) / ((↑z : ℕ × ℕ).1 : ℝ) else 0)
      = G (toFam (q := q) (↑z : ℕ × ℕ))
    rw [if_pos hsk]
    exact weight_famOfPair (fibre_fst_ne hq1 hsk) (fibre_snd_ne hq1 hsk) hsk
  -- family side: restrict to the supported families
  have hsuppT : Function.support G ⊆ T := by
    intro φ hφ
    by_contra hcon
    exact hφ (prod_lw_eq_zero_of_not_supported φ (by simpa [hT] using hcon))
  have hfam : (∑' φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ, G φ) = ∑' φ : T, G φ.1 :=
    (tsum_subtype_eq_of_support_subset (s := T) (f := G) hsuppT).symm
  calc (∑' z : ℕ × ℕ, if sk (z.1 * z.2) = q then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0)
      = ∑' z : ℕ × ℕ, F z := rfl
    _ = ∑' z : S, F z.1 := hpair
    _ = ∑' z : S, G (toFam (q := q) z.1) := tsum_congr hpt
    _ = ∑' φ : T, G φ.1 := (fibreEquiv hq hq1).tsum_eq (fun φ : T => G φ.1)
    _ = ∑' φ : (i : ℕ) → i ∈ q.primeFactors → ℕ × ℕ, G φ := hfam.symm
    _ = ∏ p ∈ q.primeFactors, (∑' ab : ℕ × ℕ, lw p ab) :=
        (euler_prod_pi (s := q.primeFactors) (fun p ab => lw p ab)
          (fun p _ => lw_nonneg p)
          (fun p hp => lw_summable (Nat.prime_of_mem_primeFactors hp))).2
    _ = ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) := by
        rw [← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => 2 < p)
          (fun p => ∑' ab : ℕ × ℕ, lw p ab)]
        have h2 : (∏ p ∈ q.primeFactors.filter (fun p => ¬ 2 < p), (∑' ab : ℕ × ℕ, lw p ab)) = 1 := by
          rw [Finset.prod_eq_one]
          intro p hp
          rw [Finset.mem_filter] at hp
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
          have hp2 : p = 2 := by have := hpp.two_le; omega
          rw [lw_tsum hpp, if_pos hp2]
        rw [h2, mul_one]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        rw [Finset.mem_filter] at hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
        rw [lw_tsum hpp, if_neg (by omega)]

/-! ### Cuts: what is still missing for `lemma4`

`fibre_sum` is the Euler product over `q.primeFactors` of the local factors above; with it,
`lemma4` reduces to the squarefree majorisation.  Both are stated here only, as targets for a
later session; neither is proved, and the lab file is untouched. -/

/-- The squarefree kernel is `1` exactly at `0` and `1` (where `sk 0 = 1` because `0` has no
prime factors). -/
private theorem sk_eq_one_iff {m : ℕ} : sk m = 1 ↔ m = 0 ∨ m = 1 := by
  constructor
  · intro h
    by_contra hne
    have hempty : m.primeFactors ≠ ∅ := fun he => hne ((Nat.primeFactors_eq_empty).mp he)
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ sk m := Finset.dvd_prod_of_mem id hp
    rw [h] at hdvd
    exact hpp.not_dvd_one hdvd
  · rintro (rfl | rfl) <;> simp [sk]

/-- **The fibre of the pair sum over the radical `q`, `q` squarefree**: the Euler product of
`local_fibre_odd` / `local_fibre_two` over the primes of `q`. -/
private theorem fibre_sum (q : ℕ) (hq : Squarefree q) (hq0 : 0 < q) :
    (∑' z : ℕ × ℕ, if sk (z.1 * z.2) = q then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0) =
      ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) := by
  classical
  rcases Nat.lt_or_ge 1 q with hq1 | hq1
  · exact fibre_sum_gt_one hq hq1
  · -- `q = 1`: the only contributing pair is `(1, 1)`, with weight `1`
    have hqeq : q = 1 := by omega
    subst hqeq
    have hsk1 : sk (1 * 1) = 1 := by simp [sk]
    have hval : (if sk (1 * 1) = 1 then g 1 * (tau1 1 : ℝ) / (1 : ℕ) else 0) = 1 := by
      rw [if_pos hsk1, g_one, tau1_one]
      norm_num
    rw [tsum_eq_single (1, 1) ?_, hval]
    · simp
    · intro z hz
      show (if sk (z.1 * z.2) = 1 then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0) = 0
      by_cases hsk : sk (z.1 * z.2) = 1
      · rw [if_pos hsk]
        rcases sk_eq_one_iff.mp hsk with h0 | h1
        · rcases Nat.mul_eq_zero.mp h0 with h0 | h0
          · rw [h0, Nat.cast_zero, div_zero]
          · rw [h0]
            simp [g]
        · exfalso
          have hz1 : z.1 = 1 := Nat.dvd_one.mp ⟨z.2, h1.symm⟩
          have hz2 : z.2 = 1 := Nat.dvd_one.mp ⟨z.1, by rw [Nat.mul_comm]; exact h1.symm⟩
          exact hz (Prod.ext hz1 hz2)
      · rw [if_neg hsk]

/-! ### The Chebyshev-type rearrangement for the squarefree majorisation

`sqfree_majorisation` compares two sums over squarefree `q ≤ z`: the `α`-weighted sum with the
local factors `2/(p-2)`, and `Sₙ`.  Splitting each `q` into its part supported on the odd primes
of `n` and the rest turns the comparison, for each fixed rest, into a comparison of two product
measures on the subsets of the odd prime set `N₁ = {p | n, p > 2}`:

* left:  `∏_{p∈S} 2/(p-1) · ∏_{p∈N₁∖S} (p-2)/(p-1)`  (total mass `∏(1+1/(p-1))`),
* right: `∏_{p∈S} 1/(p-1)`                            (total mass `∏(1+1/(p-1))`).

The left measure is biased towards the larger subsets, and the weight `1/(1+yq)` is decreasing, so
the left sum is at most the right one.  `cheb_powerset` is that statement, proved by induction on
the prime set; it is the mathematical content of the majorisation. -/

/-- Splitting a product carrying an `if` on a subset. -/
private theorem prod_ite_split {s S : Finset ℕ} (hS : S ⊆ s) (f g : ℕ → ℝ) :
    (∏ x ∈ s, (if x ∈ S then f x else g x)) = (∏ x ∈ S, f x) * (∏ x ∈ s \ S, g x) := by
  rw [← Finset.prod_sdiff hS]
  have h1 : ∏ x ∈ s \ S, (if x ∈ S then f x else g x) = ∏ x ∈ s \ S, g x :=
    Finset.prod_congr rfl (fun x hx => if_neg (Finset.mem_sdiff.mp hx).2)
  have h2 : ∏ x ∈ S, (if x ∈ S then f x else g x) = ∏ x ∈ S, f x :=
    Finset.prod_congr rfl (fun x hx => if_pos hx)
  rw [h1, h2, mul_comm]

/-- The `α`-weighted local factor on a subset of the odd prime set. -/
private noncomputable def VL (s S : Finset ℕ) : ℝ :=
  ∏ x ∈ s, (if x ∈ S then 2 / ((x : ℝ) - 1) else ((x : ℝ) - 2) / ((x : ℝ) - 1))

/-- The `Sₙ` local factor on a subset of the odd prime set. -/
private noncomputable def VR (s S : Finset ℕ) : ℝ :=
  ∏ x ∈ s, (if x ∈ S then 1 / ((x : ℝ) - 1) else 1)

private theorem VL_nonneg {s S : Finset ℕ} (hs : ∀ p ∈ s, (2 : ℝ) < (p : ℝ)) : 0 ≤ VL s S := by
  unfold VL
  refine Finset.prod_nonneg (fun x hx => ?_)
  have hx2 := hs x hx
  by_cases h : x ∈ S
  · rw [if_pos h]
    exact div_nonneg (by norm_num) (by linarith)
  · rw [if_neg h]
    exact div_nonneg (by linarith) (by linarith)

private theorem VR_nonneg {s S : Finset ℕ} (hs : ∀ p ∈ s, (2 : ℝ) < (p : ℝ)) : 0 ≤ VR s S := by
  unfold VR
  refine Finset.prod_nonneg (fun x hx => ?_)
  have hx2 := hs x hx
  by_cases h : x ∈ S
  · rw [if_pos h]
    exact div_nonneg (by norm_num) (by linarith)
  · rw [if_neg h]; exact zero_le_one

/-- **Chebyshev rearrangement.**  For a nonnegative decreasing function on subsets of `s` (all
primes `> 2`), the sum against the left weights `VL` is at most the sum against `VR`. -/
private theorem cheb_powerset : ∀ (s : Finset ℕ), (∀ p ∈ s, (2 : ℝ) < (p : ℝ)) → ∀ (h : Finset ℕ → ℝ),
    (∀ S T, S ⊆ T → T ⊆ s → h T ≤ h S) → (∀ S, 0 ≤ h S) →
    (∑ S ∈ s.powerset, VL s S * h S) ≤ (∑ S ∈ s.powerset, VR s S * h S) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs h hdec hnn
    simp [VL, VR]
  | insert p s' hp ih =>
    intro hs h hdec hnn
    have hp2 : (2 : ℝ) < (p : ℝ) := hs p (Finset.mem_insert_self p s')
    have hs' : ∀ x ∈ s', (2 : ℝ) < (x : ℝ) := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hsub : ∀ x ∈ s', x ∈ insert p s' := fun x hx => Finset.mem_insert_of_mem hx
    have hA : (∑ S ∈ s'.powerset, VL s' S * h S) ≤ (∑ S ∈ s'.powerset, VR s' S * h S) :=
      ih hs' h (fun S T hST hTs => hdec S T hST (fun x hx => hsub x (hTs hx))) hnn
    have hB : (∑ S ∈ s'.powerset, VL s' S * h (insert p S))
        ≤ (∑ S ∈ s'.powerset, VR s' S * h (insert p S)) := by
      refine ih hs' (fun S => h (insert p S)) (fun S T hST hTs => ?_) (fun S => hnn _)
      refine hdec (insert p S) (insert p T) (Finset.insert_subset_insert p hST) (fun x hx => ?_)
      rcases Finset.mem_insert.mp hx with h1 | h2
      · rw [h1]; exact Finset.mem_insert_self p s'
      · exact Finset.mem_insert_of_mem (hTs h2)
    have hBA : (∑ S ∈ s'.powerset, VL s' S * h (insert p S))
        ≤ (∑ S ∈ s'.powerset, VL s' S * h S) := by
      refine Finset.sum_le_sum (fun S hS => ?_)
      have hSs : S ⊆ s' := Finset.mem_powerset.mp hS
      refine mul_le_mul_of_nonneg_left ?_ (VL_nonneg hs')
      refine hdec S (insert p S) (fun x hx => Finset.mem_insert_of_mem hx) (fun x hx => ?_)
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact Finset.mem_insert_self p s'
      · exact Finset.mem_insert_of_mem (hSs h)
    have hterm : ∀ S ∈ s'.powerset,
        (VL (insert p s') S * h S + VL (insert p s') (insert p S) * h (insert p S))
          = ((p : ℝ) - 2) / ((p : ℝ) - 1) * (VL s' S * h S)
            + 2 / ((p : ℝ) - 1) * (VL s' S * h (insert p S)) := by
      intro S hS
      have hSs : S ⊆ s' := Finset.mem_powerset.mp hS
      have hpS : p ∉ S := fun hcon => hp (hSs hcon)
      have hxne : ∀ x ∈ s', x ≠ p := fun x hx hcon => hp (hcon ▸ hx)
      have h1 : VL (insert p s') S = ((p : ℝ) - 2) / ((p : ℝ) - 1) * VL s' S := by
        unfold VL
        rw [Finset.prod_insert hp, if_neg hpS, mul_comm]
      have h2 : VL (insert p s') (insert p S) = 2 / ((p : ℝ) - 1) * VL s' S := by
        unfold VL
        rw [Finset.prod_insert hp,
          if_pos (Finset.mem_insert_self p S : p ∈ insert p S)]
        congr 1
        refine Finset.prod_congr rfl (fun x hx => ?_)
        have hxp : x ≠ p := hxne x hx
        by_cases hc : x ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hc), if_pos hc]
        · rw [if_neg (show ¬ (x ∈ insert p S) from by simp [hc, hxp]), if_neg hc]
      rw [h1, h2]; ring
    have htermR : ∀ S ∈ s'.powerset,
        (VR (insert p s') S * h S + VR (insert p s') (insert p S) * h (insert p S))
          = (VR s' S * h S) + 1 / ((p : ℝ) - 1) * (VR s' S * h (insert p S)) := by
      intro S hS
      have hSs : S ⊆ s' := Finset.mem_powerset.mp hS
      have hpS : p ∉ S := fun hcon => hp (hSs hcon)
      have hxne : ∀ x ∈ s', x ≠ p := fun x hx hcon => hp (hcon ▸ hx)
      have h1 : VR (insert p s') S = VR s' S := by
        unfold VR
        rw [Finset.prod_insert hp, if_neg hpS, one_mul]
      have h2 : VR (insert p s') (insert p S) = 1 / ((p : ℝ) - 1) * VR s' S := by
        unfold VR
        rw [Finset.prod_insert hp,
          if_pos (Finset.mem_insert_self p S : p ∈ insert p S)]
        congr 1
        refine Finset.prod_congr rfl (fun x hx => ?_)
        have hxp : x ≠ p := hxne x hx
        by_cases hc : x ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hc), if_pos hc]
        · rw [if_neg (show ¬ (x ∈ insert p S) from by simp [hc, hxp]), if_neg hc]
      rw [h1, h2]; ring
    set A := ∑ S ∈ s'.powerset, VL s' S * h S with hAdef
    set B := ∑ S ∈ s'.powerset, VL s' S * h (insert p S) with hBdef
    set C := ∑ S ∈ s'.powerset, VR s' S * h S with hCdef
    set E := ∑ S ∈ s'.powerset, VR s' S * h (insert p S) with hEdef
    have hA' : A ≤ C := by rw [hAdef, hCdef]; exact hA
    have hB' : B ≤ E := by rw [hBdef, hEdef]; exact hB
    have hBA' : B ≤ A := by rw [hAdef, hBdef]; exact hBA
    rw [Finset.sum_powerset_insert hp, Finset.sum_powerset_insert hp,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl htermR, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    have e1 : (∑ x ∈ s'.powerset, ((p : ℝ) - 2) / ((p : ℝ) - 1) * (VL s' x * h x))
        = ((p : ℝ) - 2) / ((p : ℝ) - 1) * A := by
      rw [hAdef, Finset.mul_sum]
    have e2 : (∑ x ∈ s'.powerset, 2 / ((p : ℝ) - 1) * (VL s' x * h (insert p x)))
        = 2 / ((p : ℝ) - 1) * B := by
      rw [hBdef, Finset.mul_sum]
    have e4 : (∑ x ∈ s'.powerset, 1 / ((p : ℝ) - 1) * (VR s' x * h (insert p x)))
        = 1 / ((p : ℝ) - 1) * E := by
      rw [hEdef, Finset.mul_sum]
    rw [e1, e2, e4, ← hCdef]
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left (by
      have h1 : ((p : ℝ) - 1) * (((p : ℝ) - 2) / ((p : ℝ) - 1) * A
            + 2 / ((p : ℝ) - 1) * B) = ((p : ℝ) - 2) * A + 2 * B := by
        field_simp
      have h2 : ((p : ℝ) - 1) * (C + 1 / ((p : ℝ) - 1) * E) = ((p : ℝ) - 1) * C + E := by
        field_simp
      rw [h1, h2]
      nlinarith [hA', hB', hBA']) hp1

/-- The odd primes of `n`, the set `N₁` of the majorisation. -/
private def Nodd (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private theorem Nodd_subset (n : ℕ) : Nodd n ⊆ n.primeFactors :=
  Finset.filter_subset _ _

private theorem two_lt_of_mem_Nodd {n p : ℕ} (hp : p ∈ Nodd n) : 2 < p :=
  (Finset.mem_filter.mp hp).2

/-- **The `α`-weighted local factor.**  For `S` among the odd primes of `n`, the factor `α` times
the local product `∏_{p∈S} 2/(p-2)` is the "left" weight `VL`. -/
private theorem alpha_mul_prod_eq_VL (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Nodd n) :
    (∏ p ∈ Nodd n, ((p : ℝ) - 2) / ((p : ℝ) - 1)) * (∏ p ∈ S, 2 / ((p : ℝ) - 2))
      = VL (Nodd n) S := by
  have hsplit : (∏ p ∈ Nodd n, ((p : ℝ) - 2) / ((p : ℝ) - 1))
      = (∏ p ∈ S, ((p : ℝ) - 2) / ((p : ℝ) - 1))
        * (∏ p ∈ Nodd n \ S, ((p : ℝ) - 2) / ((p : ℝ) - 1)) := by
    rw [mul_comm (∏ p ∈ S, ((p : ℝ) - 2) / ((p : ℝ) - 1))
      (∏ p ∈ Nodd n \ S, ((p : ℝ) - 2) / ((p : ℝ) - 1))]
    exact (Finset.prod_sdiff hS).symm
  have hp : ∀ p ∈ S, ((p : ℝ) - 2) / ((p : ℝ) - 1) * (2 / ((p : ℝ) - 2))
      = 2 / ((p : ℝ) - 1) := by
    intro p hpS
    have h2p : (2 : ℝ) < (p : ℝ) := by
      exact_mod_cast two_lt_of_mem_Nodd (hS hpS)
    field_simp
  calc (∏ p ∈ Nodd n, ((p : ℝ) - 2) / ((p : ℝ) - 1)) * (∏ p ∈ S, 2 / ((p : ℝ) - 2))
      = ((∏ p ∈ S, ((p : ℝ) - 2) / ((p : ℝ) - 1)) * (∏ p ∈ S, 2 / ((p : ℝ) - 2)))
          * (∏ p ∈ Nodd n \ S, ((p : ℝ) - 2) / ((p : ℝ) - 1)) := by
        rw [hsplit]; ring
    _ = (∏ p ∈ S, 2 / ((p : ℝ) - 1))
          * (∏ p ∈ Nodd n \ S, ((p : ℝ) - 2) / ((p : ℝ) - 1)) := by
        rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hp]
    _ = VL (Nodd n) S := (prod_ite_split hS (fun p => 2 / ((p : ℝ) - 1))
          (fun p => ((p : ℝ) - 2) / ((p : ℝ) - 1))).symm

/-- **The `Sₙ` local factor.**  For `S` among the odd primes of `n`, the `Sₙ` local product is the
"right" weight `VR`. -/
private theorem prod_one_div_eq_VR (s S : Finset ℕ) (hS : S ⊆ s) :
    (∏ p ∈ S, 1 / ((p : ℝ) - 1)) = VR s S := by
  rw [VR, prod_ite_split hS (fun p => 1 / ((p : ℝ) - 1)) (fun _ => 1)]
  simp

/-- The weight `1/(1+yq)` is decreasing in `q`, for `y ≥ 0`. -/
private theorem weight_anti {y : ℝ} (hy : 0 ≤ y) {q q' : ℕ} (h : q ≤ q') :
    1 / (1 + y * (q' : ℝ)) ≤ 1 / (1 + y * (q : ℝ)) := by
  have hq : (q : ℝ) ≤ (q' : ℝ) := by exact_mod_cast h
  have h1 : (0 : ℝ) < 1 + y * (q : ℝ) := by
    have h0 : (0:ℝ) ≤ y * (q:ℝ) := mul_nonneg hy (Nat.cast_nonneg _)
    linarith
  have h2 : (0 : ℝ) < 1 + y * (q' : ℝ) := by
    have h0 : (0:ℝ) ≤ y * (q':ℝ) := mul_nonneg hy (Nat.cast_nonneg _)
    linarith
  exact one_div_le_one_div_of_le h1 (by nlinarith)

/-! ### The majorisation by pairing `q` with `q/p`

`Bw s q` is the `Sₙ`-type local weight of `q` at a set `s` of odd primes: an odd prime `p | q`
contributes `1/(p-1)` if `p ∈ s` and `2/(p-2)` otherwise.  Thus `Bw ∅ q` is the local factor of the
pair sum (`fibre_sum`) and `Bw (Nodd n) q` the local factor of `Sₙ`.

The comparison `α · Σ_q A(q)/(1+yq) ≤ Σ_q B(q)/(1+yq)` is an induction adjoining one prime at a
time.  Adjoining `p` rescales the summand at `p | q` by `(p-2)/(2(p-1))` and leaves the others
alone, so after factoring out `α_{s}` one has to compare `((p-2)/2)·Σ_{p|q}` with `Σ_{p∤q}`.  That
is a pairing: each squarefree `q` with `p | q` is matched with `q/p`, which is smaller (so its weight
`1/(1+y·)` is larger) and whose local factor at `p` is `2/(p-2)` rather than `1/(p-1)`. -/

/-- The index set of the squarefree majorisation: `q` with `1 ≤ q ≤ ⌊z⌋` and `q` squarefree. -/
private noncomputable def Fsq (z : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q)

/-- The `Sₙ`-type local weight of `q` at a set `s` of odd primes. -/
private noncomputable def Bw (s : Finset ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors.filter (2 < ·),
    (if p ∈ s then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2))

private theorem Bw_nonneg (s : Finset ℕ) (q : ℕ) : 0 ≤ Bw s q := by
  unfold Bw
  refine Finset.prod_nonneg (fun p hp => ?_)
  have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
  by_cases h : p ∈ s
  · rw [if_pos h]; exact div_nonneg (by norm_num) (by linarith)
  · rw [if_neg h]; exact div_nonneg (by norm_num) (by linarith)

private theorem Bw_empty (q : ℕ) :
    Bw ∅ q = ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) := by
  simp [Bw]

/-- A squarefree number divided by a prime factor is squarefree. -/
private theorem squarefree_div {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (h : p ∣ q) :
    Squarefree (q / p) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (Nat.squarefree_iff_prime_squarefree.mp hq) 2 Nat.prime_two (by norm_num)
  have hpq' : p * (q / p) = q := Nat.mul_div_cancel' h
  have hcop : p.Coprime (q / p) := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd
    have h2 : p * p ∣ q := by rw [← hpq']; exact mul_dvd_mul_left p hpd
    exact (Nat.squarefree_iff_prime_squarefree.mp hq) p hp h2
  rw [← hpq'] at hq
  exact ((Nat.squarefree_mul hcop).mp hq).2

/-- The prime factors of `p * q` for a prime `p` not dividing `q`: `p` adjoined to those of `q`. -/
private theorem filter_primeFactors_mul_prime {p q : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hq : q ≠ 0)
    (h : ¬ p ∣ q) :
    (p * q).primeFactors.filter (2 < ·) = insert p (q.primeFactors.filter (2 < ·)) := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq
  have hnot : p ∉ q.primeFactors.filter (2 < ·) := fun hmem =>
    h (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hmem).1).2.1
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hxP, hxdvd, -⟩, h2x⟩
    rcases (Nat.Prime.dvd_mul hxP).mp hxdvd with hd | hd
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hxP hp).mp hd)
    · exact Or.inr ⟨⟨hxP, hd, hq⟩, h2x⟩
  · intro hxmem
    rcases hxmem with hxp | ⟨⟨hxP, hxd, -⟩, h2x⟩
    · rw [hxp]
      exact ⟨⟨hp, dvd_mul_right p q, hpq0⟩, hp2⟩
    · exact ⟨⟨hxP, dvd_mul_of_dvd_right hxd p, hpq0⟩, h2x⟩

/-- Pulling a prime factor `p ∉ s` out of the local weight, for `p ∤ q`. -/
private theorem Bw_mul_prime {s : Finset ℕ} {p q : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpq : ¬ p ∣ q)
    (hq : q ≠ 0) :
    Bw s (p * q) = (if p ∈ s then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) * Bw s q := by
  unfold Bw
  rw [filter_primeFactors_mul_prime hp hp2 hq hpq,
    Finset.prod_insert (fun hmem => hpq (Nat.mem_primeFactors.mp
      (Finset.mem_filter.mp hmem).1).2.1)]

/-- Adjoining an odd prime `p ∉ s` rescales the local weight of `q` at `p`. -/
private theorem Bw_insert {s : Finset ℕ} {p q : ℕ} (hp : p ∉ s) (hp2 : 2 < p) (hpq : p.Prime)
    (hq : q ≠ 0) :
    Bw (insert p s) q
      = Bw s q * (if p ∣ q then ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) else 1) := by
  classical
  have hpT : (p ∈ q.primeFactors.filter (2 < ·)) ↔ p ∣ q := by
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨fun h => h.1.2.1, fun h => ⟨⟨hpq, h, hq⟩, hp2⟩⟩
  set T := q.primeFactors.filter (2 < ·) with hT
  set f : ℕ → ℝ := fun r => if r ∈ s then 1 / ((r : ℝ) - 1) else 2 / ((r : ℝ) - 2) with hfdef
  have hfs : ∀ r, r ≠ p →
      (if r ∈ insert p s then (1 : ℝ) / ((r : ℝ) - 1) else 2 / ((r : ℝ) - 2)) = f r := by
    intro r hr
    simp only [hfdef]
    by_cases h : r ∈ s
    · rw [if_pos (Finset.mem_insert_of_mem h), if_pos h]
    · rw [if_neg (by simp [h, hr]), if_neg h]
  by_cases hpq' : p ∣ q
  · rw [if_pos hpq']
    have hmem : p ∈ T := hpT.mpr hpq'
    have e1 : Bw (insert p s) q = (1 / ((p : ℝ) - 1)) * ∏ r ∈ T.erase p, f r := by
      rw [show Bw (insert p s) q = ∏ r ∈ T,
        (if r ∈ insert p s then (1 : ℝ) / ((r : ℝ) - 1) else 2 / ((r : ℝ) - 2)) from rfl,
        ← Finset.mul_prod_erase T
          (fun r => if r ∈ insert p s then (1 : ℝ) / ((r : ℝ) - 1) else 2 / ((r : ℝ) - 2)) hmem,
        if_pos (Finset.mem_insert_self p s)]
      congr 1
      exact Finset.prod_congr rfl (fun r hr => hfs r (by
        intro hcon
        rw [hcon] at hr
        exact absurd hr (Finset.notMem_erase p T)))
    have e2 : Bw s q = (2 / ((p : ℝ) - 2)) * ∏ r ∈ T.erase p, f r := by
      rw [show Bw s q = ∏ r ∈ T, f r from rfl,
        ← Finset.mul_prod_erase T f hmem]
      congr 1
      simp only [hfdef]
      rw [if_neg hp]
    rw [e1, e2]
    have hp2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp2' : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    field_simp
  · rw [if_neg hpq', mul_one]
    have hmem : p ∉ T := fun h => hpq' (hpT.mp h)
    rw [show Bw (insert p s) q = ∏ r ∈ T,
        (if r ∈ insert p s then (1 : ℝ) / ((r : ℝ) - 1) else 2 / ((r : ℝ) - 2)) from rfl,
      show Bw s q = ∏ r ∈ T, f r from rfl]
    exact Finset.prod_congr rfl (fun r hr => hfs r (fun hcon => hmem (hcon ▸ hr)))

/-- **The pairing step.**  All primes below are odd.  Each squarefree `q` with `p ∣ q` is matched
with `q / p`, which is smaller — so its weight `1/(1+y·)` is larger — and whose local factor at `p`
is `2/(p-2)` rather than `1/(p-1)`.  Hence the `p`-divisible part of the weighted sum, scaled by
`(p-2)/2`, is dominated by the `p`-free part. -/
private theorem pairing {z y : ℝ} (hy : 0 ≤ y) {s : Finset ℕ} {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hps : p ∉ s) :
    ((p : ℝ) - 2) / 2 * (∑ q ∈ (Fsq z).filter (fun q => p ∣ q),
        Bw s q * (1 / (1 + y * (q : ℝ))))
      ≤ ∑ q ∈ (Fsq z).filter (fun q => ¬ p ∣ q), Bw s q * (1 / (1 + y * (q : ℝ))) := by
  classical
  set F := Fsq z with hF
  set A' := F.filter (fun q => ¬ p ∣ q ∧ p * q ≤ ⌊z⌋₊) with hA'
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hmemA' : ∀ q ∈ A', q ≠ 0 ∧ Squarefree q ∧ ¬ p ∣ q ∧ p * q ≤ ⌊z⌋₊ := by
    intro q hq
    rw [hA', hF, Fsq, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨h1, h2⟩, hsq⟩, hnp, hle⟩ := hq
    exact ⟨by omega, hsq, hnp, hle⟩
  have hinj : Set.InjOn (fun q => p * q) ↑A' := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel hp.pos hab
  have himage : A'.image (fun q => p * q) = F.filter (fun q => p ∣ q) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨hq0, hsq, hnp, hle⟩ := hmemA' q hq
      rw [hF, Fsq, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hq0), hle⟩, ?_⟩,
        ⟨q, rfl⟩⟩
      exact (Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr hnp)).mpr ⟨hp.squarefree, hsq⟩
    · intro hx
      rw [hF, Fsq, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨⟨⟨h1, h2⟩, hsq⟩, hpdvd⟩ := hx
      have hpx : p * (x / p) = x := Nat.mul_div_cancel' hpdvd
      have hsqdiv : Squarefree (x / p) := squarefree_div hsq hp hpdvd
      have hcop : p.Coprime (x / p) := by
        rw [hp.coprime_iff_not_dvd]
        intro hpd
        have h2' : p * p ∣ x := by rw [← hpx]; exact mul_dvd_mul_left p hpd
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp h2'
      have hnp : ¬ p ∣ x / p := hp.coprime_iff_not_dvd.mp hcop
      rw [Finset.mem_image]
      refine ⟨x / p, ?_, hpx⟩
      rw [hA', hF, Fsq, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
      have hxdvd1 : 1 ≤ x / p := by
        have hpx2 : p ≤ x := Nat.le_of_dvd (by omega) hpdvd
        have := Nat.div_pos hpx2 hp.pos
        omega
      refine ⟨⟨⟨hxdvd1, le_trans (Nat.div_le_self x p) h2⟩, hsqdiv⟩, hnp, by rw [hpx]; exact h2⟩
  have hstep1 : (∑ q ∈ F.filter (fun q => p ∣ q), Bw s q * (1 / (1 + y * (q : ℝ))))
      = ∑ q ∈ A', Bw s (p * q) * (1 / (1 + y * ((p * q : ℕ) : ℝ))) := by
    rw [← himage]
    exact Finset.sum_image hinj
  have hstep2 : (∑ q ∈ A', Bw s (p * q) * (1 / (1 + y * ((p * q : ℕ) : ℝ))))
      = (2 / ((p : ℝ) - 2)) * ∑ q ∈ A', Bw s q * (1 / (1 + y * ((p * q : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    obtain ⟨hq0, -, hnp, -⟩ := hmemA' q hq
    rw [Bw_mul_prime hp hp2 hnp hq0, if_neg hps]
    ring
  have hstep3 : (∑ q ∈ A', Bw s q * (1 / (1 + y * ((p * q : ℕ) : ℝ))))
      ≤ ∑ q ∈ A', Bw s q * (1 / (1 + y * (q : ℝ))) := by
    refine Finset.sum_le_sum (fun q hq => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Bw_nonneg s q)
    refine one_div_le_one_div_of_le ?_ ?_
    · have h0 : (0 : ℝ) ≤ y * (q : ℝ) := mul_nonneg hy (Nat.cast_nonneg q)
      linarith
    · have h1 : (q : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) q]
      have h0 : (0 : ℝ) ≤ y * (q : ℝ) := mul_nonneg hy (Nat.cast_nonneg q)
      have h0' : (0 : ℝ) ≤ y * ((p * q : ℕ) : ℝ) :=
        mul_nonneg hy (Nat.cast_nonneg _)
      nlinarith
  have hstep4 : (∑ q ∈ A', Bw s q * (1 / (1 + y * (q : ℝ))))
      ≤ ∑ q ∈ F.filter (fun q => ¬ p ∣ q), Bw s q * (1 / (1 + y * (q : ℝ))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ =>
      mul_nonneg (Bw_nonneg s i) (by positivity))
    intro q hq
    rw [hA', Finset.mem_filter] at hq
    rw [Finset.mem_filter]
    exact ⟨hq.1, hq.2.1⟩
  have hfac : ((p : ℝ) - 2) / 2 * (2 / ((p : ℝ) - 2)) = 1 := by
    field_simp
  calc ((p : ℝ) - 2) / 2 * (∑ q ∈ F.filter (fun q => p ∣ q),
        Bw s q * (1 / (1 + y * (q : ℝ))))
      = ((p : ℝ) - 2) / 2 * (∑ q ∈ A', Bw s (p * q)
          * (1 / (1 + y * ((p * q : ℕ) : ℝ)))) := by rw [hstep1]
    _ = ((p : ℝ) - 2) / 2 * ((2 / ((p : ℝ) - 2))
          * ∑ q ∈ A', Bw s q * (1 / (1 + y * ((p * q : ℕ) : ℝ)))) := by rw [hstep2]
    _ = ∑ q ∈ A', Bw s q * (1 / (1 + y * ((p * q : ℕ) : ℝ))) := by
        rw [← mul_assoc, hfac, one_mul]
    _ ≤ ∑ q ∈ A', Bw s q * (1 / (1 + y * (q : ℝ))) := hstep3
    _ ≤ ∑ q ∈ F.filter (fun q => ¬ p ∣ q), Bw s q * (1 / (1 + y * (q : ℝ))) := hstep4

/-- **The squarefree majorisation in `Bw` form**, by adjoining the primes of `s` one at a time. -/
private theorem sqfree_major_aux : ∀ (s : Finset ℕ), (∀ p ∈ s, 2 < p) → (∀ p ∈ s, p.Prime) →
    ∀ (z y : ℝ), 0 ≤ y →
    (∏ p ∈ s, ((p : ℝ) - 2) / ((p : ℝ) - 1))
        * (∑ q ∈ Fsq z, Bw ∅ q * (1 / (1 + y * (q : ℝ))))
      ≤ ∑ q ∈ Fsq z, Bw s q * (1 / (1 + y * (q : ℝ))) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ z y _
    simp
  | insert p s' hp ih =>
    intro hs hpr z y hy
    have hp2 : 2 < p := hs p (Finset.mem_insert_self p s')
    have hpp : p.Prime := hpr p (Finset.mem_insert_self p s')
    have hp2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
    have hp1R : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hs' : ∀ x ∈ s', 2 < x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hpr' : ∀ x ∈ s', x.Prime := fun x hx => hpr x (Finset.mem_insert_of_mem hx)
    have hIH := ih hs' hpr' z y hy
    set w : ℕ → ℝ := fun q => 1 / (1 + y * (q : ℝ)) with hw
    set U := ∑ q ∈ (Fsq z).filter (fun q => ¬ p ∣ q), Bw s' q * w q with hU
    set Z := ∑ q ∈ (Fsq z).filter (fun q => p ∣ q), Bw s' q * w q with hZ
    have hpair : ((p : ℝ) - 2) / 2 * Z ≤ U := by
      rw [hZ, hU]
      exact pairing (z := z) (y := y) hy hpp hp2 (s := s') hp
    have hB : (∑ q ∈ Fsq z, Bw s' q * w q) = U + Z := by
      rw [hU, hZ,
        ← Finset.sum_filter_add_sum_filter_not (Fsq z) (fun q => p ∣ q)
          (fun q => Bw s' q * w q),
        add_comm]
    have hsum : (∑ q ∈ Fsq z, Bw (insert p s') q * w q)
        = U + ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) * Z := by
      have hpt : ∀ q ∈ Fsq z, Bw (insert p s') q * w q
          = (if p ∣ q then ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) else 1) * (Bw s' q * w q) := by
        intro q hq
        have hq0 : q ≠ 0 := by
          rw [Fsq, Finset.mem_filter, Finset.mem_Icc] at hq
          have := hq.1.1
          omega
        rw [Bw_insert hp hp2 hpp hq0]
        ring
      rw [Finset.sum_congr rfl hpt,
        ← Finset.sum_filter_add_sum_filter_not (Fsq z) (fun q => p ∣ q)
          (fun q => (if p ∣ q then ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) else 1)
            * (Bw s' q * w q))]
      conv_lhs => rw [add_comm]
      rw [hU, hZ]
      congr 1
      · refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mem_filter] at hq
        rw [if_neg hq.2, one_mul]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mem_filter] at hq
        rw [if_pos hq.2]
    have step1 : ((p : ℝ) - 2) / ((p : ℝ) - 1)
        * ((∏ x ∈ s', ((x : ℝ) - 2) / ((x : ℝ) - 1)) * (∑ q ∈ Fsq z, Bw ∅ q * w q))
        ≤ ((p : ℝ) - 2) / ((p : ℝ) - 1) * (U + Z) := by
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) (by linarith))
      rw [← hB]
      exact hIH
    have step2 : ((p : ℝ) - 2) / ((p : ℝ) - 1) * (U + Z)
        ≤ U + ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) * Z := by
      have hdiff : U + ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) * Z
            - ((p : ℝ) - 2) / ((p : ℝ) - 1) * (U + Z)
          = (1 / ((p : ℝ) - 1)) * (U - ((p : ℝ) - 2) / 2 * Z) := by
        field_simp
        ring
      have hnonneg : 0 ≤ U - ((p : ℝ) - 2) / 2 * Z := sub_nonneg.mpr hpair
      rw [← sub_nonneg, hdiff]
      exact mul_nonneg (le_of_lt (one_div_pos.mpr hp1R)) hnonneg
    rw [Finset.prod_insert hp, hsum]
    calc ((p : ℝ) - 2) / ((p : ℝ) - 1) * (∏ x ∈ s', ((x : ℝ) - 2) / ((x : ℝ) - 1))
          * (∑ q ∈ Fsq z, Bw ∅ q * w q)
        = ((p : ℝ) - 2) / ((p : ℝ) - 1)
            * ((∏ x ∈ s', ((x : ℝ) - 2) / ((x : ℝ) - 1)) * (∑ q ∈ Fsq z, Bw ∅ q * w q)) := by
          ring
      _ ≤ ((p : ℝ) - 2) / ((p : ℝ) - 1) * (U + Z) := step1
      _ ≤ U + ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1)) * Z := step2

/-- The local factors of `Sₙ` recombine into `Bw (Nodd n)`: the `p = 2` factor of `Sₙ` is `1`,
because `n` is even. -/
private theorem prod_Sn_factors (n q : ℕ) (hn : Even n) (hn0 : 0 < n) :
    (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2))
        * (∏ p ∈ q.primeFactors.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1))
      = Bw (Nodd n) q := by
  classical
  have h2n : 2 ∣ n := by
    rcases hn with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  set T := q.primeFactors with hT
  have h1 : (∏ p ∈ T.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2))
      * (∏ p ∈ T.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1))
      = ∏ p ∈ T, (if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not T (fun p => p ∣ n)
      (fun p => if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2))
    have hA : (∏ p ∈ T.filter (fun p => p ∣ n),
        (if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)))
        = ∏ p ∈ T.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1) :=
      Finset.prod_congr rfl (fun p hp => if_pos (Finset.mem_filter.mp hp).2)
    have hB : (∏ p ∈ T.filter (fun p => ¬ p ∣ n),
        (if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)))
        = ∏ p ∈ T.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2) :=
      Finset.prod_congr rfl (fun p hp => if_neg (Finset.mem_filter.mp hp).2)
    rw [hA, hB] at hsplit
    rw [← hsplit, mul_comm]
  have h2 : (∏ p ∈ T, (if p ∣ n then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)))
      = ∏ p ∈ T.filter (2 < ·), (if p ∣ n then 1 / ((p : ℝ) - 1)
          else 2 / ((p : ℝ) - 2)) := by
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun x hx hxf => ?_)).symm
    have hx2 : ¬ (2 < x) := fun hcon => hxf (Finset.mem_filter.mpr ⟨hx, hcon⟩)
    have hxP : x.Prime := (Nat.mem_primeFactors.mp hx).1
    have hxeq : x = 2 := le_antisymm (by omega) hxP.two_le
    rw [hxeq, if_pos h2n]
    norm_num
  have h3 : (∏ p ∈ T.filter (2 < ·), (if p ∣ n then 1 / ((p : ℝ) - 1)
        else 2 / ((p : ℝ) - 2))) = Bw (Nodd n) q := by
    rw [Bw, hT]
    refine Finset.prod_congr rfl (fun x hx => ?_)
    obtain ⟨hxT, hx2⟩ := Finset.mem_filter.mp hx
    have hxP : x.Prime := (Nat.mem_primeFactors.mp hxT).1
    have hmem : (x ∈ Nodd n) ↔ x ∣ n := by
      rw [Nodd, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨fun h => h.1.2.1, fun h => ⟨⟨hxP, h, hn0.ne'⟩, hx2⟩⟩
    by_cases h : x ∣ n
    · rw [if_pos h, if_pos (hmem.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hmem.mp hc))]
  rw [h1, h2]
  exact h3

/-- `Sₙ` as a sum of the `Bw (Nodd n)` weights over the squarefree range. -/
private theorem Sn_eq (n : ℕ) (hn : Even n) (hn0 : 0 < n) (z y : ℝ) :
    Sn n z y = ∑ q ∈ Fsq z, Bw (Nodd n) q * (1 / (1 + y * (q : ℝ))) := by
  classical
  rw [Sn, Fsq]
  have hpt : ∀ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then (1 : ℝ) else 0) / (1 + y * (q : ℝ))
          * (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2))
          * (∏ p ∈ q.primeFactors.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1))
        = if Squarefree q then ((1 / (1 + y * (q : ℝ)))
            * (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), 2 / ((p : ℝ) - 2))
            * (∏ p ∈ q.primeFactors.filter (fun p => p ∣ n), 1 / ((p : ℝ) - 1))) else 0 := by
    intro q _
    by_cases h : Squarefree q <;> simp [h]
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [mul_assoc, prod_Sn_factors n q hn hn0]
  ring

/-- CUT (not proved).  The squarefree majorisation: `Sn n z y` dominates the `α`-weighted sum
of `Π_{p|q,p>2} 2/(p-2)/(1+yq)` over squarefree `q ≤ z`.  Together with `fibre_sum` and the
monotonicity of `q ↦ 1/(1+yq)` this gives `lemma4`. -/
private theorem sqfree_majorisation (n : ℕ) (hn : Even n) (hn0 : 0 < n) (z y : ℝ) (hz : 1 ≤ z)
    (hy : 0 ≤ y) :
    (∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
        (∑ q ∈ (Icc 1 ⌊z⌋₊).filter Squarefree,
          (∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2)) / (1 + y * q))
      ≤ Sn n z y := by
  classical
  rw [Sn_eq n hn hn0 z y]
  have h1 : (∑ q ∈ (Icc 1 ⌊z⌋₊).filter Squarefree,
        (∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2)) / (1 + y * q))
      = ∑ q ∈ Fsq z, Bw ∅ q * (1 / (1 + y * (q : ℝ))) := by
    rw [Fsq]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Bw_empty, div_eq_mul_one_div]
  rw [h1]
  have hs : ∀ p ∈ Nodd n, 2 < p := fun p hp => two_lt_of_mem_Nodd hp
  have hpr : ∀ p ∈ Nodd n, p.Prime := fun p hp =>
    (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have h := sqfree_major_aux (Nodd n) hs hpr z y hy
  rw [Nodd] at h
  exact h

/-- `sk m ≥ 1`. -/
private theorem sk_pos (m : ℕ) : 1 ≤ sk m := by
  rw [sk]
  exact Finset.one_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)

/-- `sk m` is squarefree: it is the product of the distinct primes of `m`. -/
private theorem squarefree_sk (m : ℕ) : Squarefree (sk m) := by
  have hsk0 : sk m ≠ 0 := by have h := sk_pos m; omega
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hdvd
  have hxdvd : x ∣ sk m := dvd_trans (dvd_mul_right x x) hdvd
  have hxmem : x ∈ m.primeFactors := by
    have h := Nat.mem_primeFactors.mpr ⟨hx, hxdvd, hsk0⟩
    rwa [primeFactors_sk] at h
  have hfac : (sk m).factorization x = 1 := by
    rw [sk, show (∏ q ∈ m.primeFactors, q) = ∏ q ∈ m.primeFactors, q ^ (1 : ℕ) from by simp,
      factorization_prod_prime_pow (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun _ => 1) hxmem]
  have h2 : 2 ≤ (sk m).factorization x := by
    have hx2 : x ^ 2 ∣ sk m := by rw [pow_two]; exact hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hx hsk0).mp hx2
  omega

/-- LEAF. Lemma 4, (3.5), in truncated form: for `y ≥ 0`, `z ≥ 1`, `n` even and every finite
set `T` of pairs `(r, d)` with `s(rd) ≤ z`,
`Π_{p|n,p>2} (p-2)/(p-1) · Σ_{(r,d) ∈ T} g(d) τ₁(r)/(r + r y s(rd)) ≤ S_n(z, y)`. The terms are
nonnegative, so this is (3.5). Vaughan 1977 p. 97 and 98, Lemma 4. Unit U-1525. -/
theorem lemma4 (n : ℕ) (hn : Even n) (hn0 : 0 < n) (z y : ℝ) (hz : 1 ≤ z) (hy : 0 ≤ y)
    (T : Finset (ℕ × ℕ))
    (hT : ∀ rd ∈ T, 1 ≤ rd.1 ∧ 1 ≤ rd.2 ∧ (sk (rd.1 * rd.2) : ℝ) ≤ z) :
    (∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
      ∑ rd ∈ T, g rd.2 * (tau1 rd.1 : ℝ) / (rd.1 + rd.1 * y * sk (rd.1 * rd.2))
      ≤ Sn n z y := by

  classical
  set al := ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 2) / ((p : ℝ) - 1) with hal
  set Wt := fun q : ℕ => 1 / (1 + y * (q : ℝ)) with hWt
  set Yw := fun q : ℕ => ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) with hYw
  -- (0) the summand as a product of the fibre weight and the radical weight
  have hterm : ∀ rd ∈ T, g rd.2 * (tau1 rd.1 : ℝ) / (rd.1 + rd.1 * y * sk (rd.1 * rd.2))
      = (g rd.2 * (tau1 rd.1 : ℝ) / rd.1) * Wt (sk (rd.1 * rd.2)) := by
    intro rd hrd
    obtain ⟨h1, -, -⟩ := hT rd hrd
    have hr : (rd.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hs1 : (1 + y * (sk (rd.1 * rd.2) : ℝ)) ≠ 0 := by
      have h0 : (0 : ℝ) ≤ y * (sk (rd.1 * rd.2) : ℝ) := mul_nonneg hy (Nat.cast_nonneg _)
      have : (0 : ℝ) ≤ (sk (rd.1 * rd.2) : ℝ) := Nat.cast_nonneg _
      linarith
    have hfac : (rd.1 : ℝ) + (rd.1 : ℝ) * y * (sk (rd.1 * rd.2) : ℝ)
        = (rd.1 : ℝ) * (1 + y * (sk (rd.1 * rd.2) : ℝ)) := by ring
    rw [hfac, hWt]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  -- (1) split the finite sum by the value of the radical
  set Q := T.image (fun rd => sk (rd.1 * rd.2)) with hQ
  have hmaps : ∀ rd ∈ T, sk (rd.1 * rd.2) ∈ Q := fun rd hrd => Finset.mem_image_of_mem _ hrd
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun rd => (g rd.2 * (tau1 rd.1 : ℝ) / rd.1) * Wt (sk (rd.1 * rd.2)))]
  -- (2) on each fibre the radical weight is constant
  have hstep : ∀ q ∈ Q, (∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
        (g rd.2 * (tau1 rd.1 : ℝ) / rd.1) * Wt (sk (rd.1 * rd.2)))
      = (∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
          g rd.2 * (tau1 rd.1 : ℝ) / rd.1) * Wt q := by
    intro q hq
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun rd hrd => by
      have h := (Finset.mem_filter.mp hrd).2
      rw [h])
  rw [Finset.sum_congr rfl hstep]
  -- (3) each fibre sum is bounded by `Yw q`
  have hbnd : ∀ q ∈ Q, (∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
        g rd.2 * (tau1 rd.1 : ℝ) / rd.1) ≤ Yw q := by
    intro q hq
    obtain ⟨rd0, hrd0T, hrd0q⟩ := Finset.mem_image.mp hq
    have hqs : Squarefree q := by
      rw [← hrd0q]; exact squarefree_sk (rd0.1 * rd0.2)
    have hqpos : 0 < q := by
      rw [← hrd0q]; exact sk_pos _
    have htsum := fibre_sum q hqs hqpos
    have hsumm : Summable (fun z : ℕ × ℕ =>
        if sk (z.1 * z.2) = q then g z.2 * (tau1 z.1 : ℝ) / z.1 else 0) := by
      by_contra hcon
      have hz := tsum_eq_zero_of_not_summable hcon
      rw [htsum] at hz
      have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2) :=
        Finset.prod_pos (fun p hp => by
          have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
          exact div_pos (by norm_num) (by linarith))
      linarith
    have h1 : (∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
          g rd.2 * (tau1 rd.1 : ℝ) / rd.1)
        = ∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
            (if sk (rd.1 * rd.2) = q then g rd.2 * (tau1 rd.1 : ℝ) / rd.1 else 0) :=
      Finset.sum_congr rfl (fun rd hrd => by rw [if_pos (Finset.mem_filter.mp hrd).2])
    rw [h1]
    refine le_trans (hsumm.sum_le_tsum _ ?_) ?_
    · intro i _
      by_cases h : sk (i.1 * i.2) = q
      · rw [if_pos h]
        exact div_nonneg (mul_nonneg (g_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      · rw [if_neg h]
    · rw [htsum, hYw]
  -- (4) `Q` lies in the squarefree range
  have hQsub : Q ⊆ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q) := by
    intro q hq
    obtain ⟨rd, hrdT, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨-, -, h3⟩ := hT rd hrdT
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨sk_pos _, Nat.le_floor h3⟩, squarefree_sk _⟩
  -- (5) the two monotone comparisons and the majorisation
  have hYnn : ∀ q : ℕ, 0 ≤ Yw q := fun q => by
    rw [hYw]
    exact Finset.prod_nonneg (fun p hp => by
      have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (by norm_num) (by linarith))
  have hWnn : ∀ q : ℕ, 0 ≤ Wt q := fun q => by
    rw [hWt]
    have h0 : (0 : ℝ) ≤ y * (q : ℝ) := mul_nonneg hy (Nat.cast_nonneg _)
    exact div_nonneg (by norm_num) (by linarith)
  have halpos : 0 ≤ al := by
    rw [hal]
    exact Finset.prod_nonneg (fun p hp => by
      have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (by linarith) (by linarith))
  have step1 : al * (∑ q ∈ Q, (∑ rd ∈ T.filter (fun rd => sk (rd.1 * rd.2) = q),
        g rd.2 * (tau1 rd.1 : ℝ) / rd.1) * Wt q)
      ≤ al * (∑ q ∈ Q, Yw q * Wt q) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q hq => ?_)) halpos
    exact mul_le_mul_of_nonneg_right (hbnd q hq) (hWnn q)
  have step2 : al * (∑ q ∈ Q, Yw q * Wt q)
      ≤ al * (∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q), Yw q * Wt q) := by
    refine mul_le_mul_of_nonneg_left ?_ halpos
    exact Finset.sum_le_sum_of_subset_of_nonneg hQsub
      (fun i _ _ => mul_nonneg (hYnn i) (hWnn i))
  have step3 : al * (∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q), Yw q * Wt q)
      ≤ Sn n z y := by
    have hmaj := sqfree_majorisation n hn hn0 z y hz hy
    have hconv : (∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q),
          (∏ p ∈ q.primeFactors.filter (2 < ·), 2 / ((p : ℝ) - 2)) / (1 + y * q))
        = ∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Squarefree q), Yw q * Wt q := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [hYw, hWt, div_eq_mul_one_div]
    rw [hconv] at hmaj
    rw [hal]
    exact hmaj
  exact le_trans step1 (le_trans step2 step3)

/-- LEAF. (2.2), first half: `0.57721 < γ < 0.57722`. Vaughan 1977 p. 94, (2.2), by
Euler-Maclaurin; Mathlib's `Real.eulerMascheroniSeq` and `eulerMascheroniSeq'` bracket γ.
Unit U-1525. -/
theorem gamma_bounds :
    0.57721 < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57722 := by
  constructor
  · have h := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
    linarith
  · have h := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
    linarith

open LeanLab.RieselVaughan1983 in
/-- The sharper hyperbola remainder used to close Lemma 5 above 121.
This extracts the intermediate bound in Riesel and Vaughan 1983 page 49. -/
theorem lemma5_divisor_error (x : ℝ) (hx : 16 ≤ x) :
    |lem1E stieltjes1 x| < 2*(1/(⌊Real.sqrt x⌋₊ : ℝ)) := by
  let g1 := stieltjes1
  have hL := stieltjes1_hL
  have hx0 : 0 < x := by linarith
  obtain ⟨z, hzdef⟩ : ∃ z, z = Real.sqrt x := ⟨_, rfl⟩
  have hzz : z * z = x := by rw [hzdef]; exact Real.mul_self_sqrt hx0.le
  have hz4 : 4 ≤ z := by
    rw [hzdef, show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  obtain ⟨N, hNdef⟩ : ∃ N, N = ⌊z⌋₊ := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hzdef, ← hNdef]
  have hN4 : 4 ≤ N := by rw [hNdef]; exact Nat.le_floor (by exact_mod_cast hz4)
  have hNz : (N : ℝ) ≤ z := by rw [hNdef]; exact Nat.floor_le (by linarith)
  have hzN : z < N + 1 := by rw [hNdef]; exact Nat.lt_floor_add_one z
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hXx : (X : ℝ) ≤ x := by rw [hXdef]; exact Nat.floor_le hx0.le
  have hNNx : (N : ℝ) * N ≤ x := by nlinarith
  have hxNN : x < ((N : ℝ) + 1) * (N + 1) := by nlinarith
  have hN1 : N * N ≤ X := by
    rw [hXdef]; apply Nat.le_floor; push_cast; exact hNNx
  have hN2 : X < (N + 1) * (N + 1) := by
    have : (X : ℝ) < ((N + 1) * (N + 1) : ℕ) := by push_cast; linarith
    exact_mod_cast this
  unfold lem1E
  rw [← hXdef, divsum_eq, hyperbola X N hN1 hN2]
  have hsplit : ∑ a ∈ Icc 1 N, (harmonic (X / a) : ℝ) / a
      = (Real.log x + eulerMascheroniConstant) * (harmonic N : ℝ) - Lsum N
        + ∑ a ∈ Icc 1 N,
          ((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a := by
    rw [sum_Icc_inv N, Finset.mul_sum, Lsum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    rw [Nat.floor_div_natCast, ← hXdef, Real.log_div hx0.ne' ha0.ne']
    field_simp; ring
  have hSr : |∑ a ∈ Icc 1 N,
      ((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a|
        ≤ 1 / (N : ℝ) / 2 + (1 / (N : ℝ)) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ a ∈ Icc 1 N,
        |((harmonic ⌊x / a⌋₊ : ℝ) - Real.log (x / a) - eulerMascheroniConstant) / a|
          ≤ 1 / (2 * x) + N / x ^ 2 := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
      have haN : (a : ℝ) ≤ N := by exact_mod_cast ha.2
      have hy4 : 4 ≤ x / a := by
        rw [le_div_iff₀ ha0]; nlinarith
      have hR := R_bound (x / a) hy4
      rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
      have e : (1 / (2 * (x / a)) + 1 / (x / a) ^ 2) = (1 / (2 * x) + a / x ^ 2) * a := by
        field_simp
      rw [e] at hR
      have : (1 / (2 * x) + a / x ^ 2) * a ≤ (1 / (2 * x) + N / x ^ 2) * a := by
        apply mul_le_mul_of_nonneg_right _ ha0.le
        have : (a : ℝ) / x ^ 2 ≤ N / x ^ 2 := div_le_div_of_nonneg_right haN (by positivity)
        linarith
      linarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have h1 : (N : ℝ) * (1 / (2 * x)) ≤ 1 / (N : ℝ) / 2 := by
      rw [show (N : ℝ) * (1 / (2 * x)) = N / (2 * x) by ring,
        show 1 / (N : ℝ) / 2 = 1 / (2 * N) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (N : ℝ) * (N / x ^ 2) ≤ (1 / (N : ℝ)) ^ 2 := by
      rw [show (N : ℝ) * (N / x ^ 2) = (N * N) / x ^ 2 by ring, div_pow, one_pow,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : ((N : ℝ) * N) * ((N : ℝ) * N) ≤ x * x := mul_le_mul hNNx hNNx (by positivity) hx0.le
      nlinarith
    nlinarith
  rw [hsplit]
  obtain ⟨hHl, hHu⟩ := harm_bounds N (by omega)
  have hσ := sigma_bound g1 hL N (by omega)
  have hlam0 : 0 ≤ Real.log z - Real.log N := by
    have := Real.log_le_log hN0 hNz; linarith
  have hlam1 : Real.log z - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by linarith) hN0.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < z / N by positivity)
    have h2 : z / N - 1 ≤ 1 / N := by
      rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  have hlogx : Real.log x = 2 * (Real.log N + (Real.log z - Real.log N)) := by
    rw [← hzz, Real.log_mul (by linarith) (by linarith)]; ring
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlN := log_le_div_e N hN0
  have hlNu : Real.log N * (1 / N) ≤ 10 / 27 := by
    rw [mul_one_div, div_le_iff₀ hN0]; linarith
  refine (final_alg (Real.log N) (Real.log z - Real.log N)
    ((harmonic N : ℝ) - Real.log N - 1 / N / 2 - eulerMascheroniConstant) (cseq N - g1) _ (1 / N)
    eulerMascheroniConstant g1 _ _ _ (by ring) hlogx (by unfold cseq; ring) (by positivity)
    (by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith) ?_ ?_ hlam0 hlam1
    (by rw [show (1 : ℝ) / N / 10 = 1 / (10 * N) by ring]; exact hσ) hSr hlN0 hlNu)
  · rw [div_pow, one_pow]
    have : 1 / (8 * (N : ℝ) ^ 2) = 1 / N ^ 2 / 8 := by ring
    have h1 : 1 / (2 * (N : ℝ)) = 1 / N / 2 := by ring
    rw [this, h1] at hHl; linarith
  · have h1 : 1 / (2 * (N : ℝ)) = 1 / N / 2 := by ring
    rw [h1] at hHu; linarith



set_option maxHeartbeats 1000000 in
/-- The finite range below 42 in the proof of Lemma 5, Vaughan 1977 page 99.
The 41 rational endpoint certificates are checked by the Lean kernel. -/
theorem lemma5_below_42 (z : ℝ) (hz : 1 ≤ z) (hz42 : z < 42) :
    1 / 4 * Real.log z ^ 2 + (Real.eulerMascheroniConstant + 1 / 2 * Real.log 2) * Real.log z
      + 0.1833 < ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ) / r := by
  let U : ℕ → ℚ := fun n =>
    (([69315, 109862, 138630, 160944, 179176, 194592, 207945, 219723, 230259,
       239790, 248491, 256495, 263906, 270806, 277259, 283322, 289038, 294444,
       299574, 304453, 309105, 313550, 317806, 321888, 325810, 329584, 333221,
       336730, 340120, 343399, 346574, 349651, 352637, 355535, 358352, 361092,
       363759, 366357, 368888, 371358, 373767] : List ℚ).getD (n-1) 0) / 100000
  have cert : ∀ n ∈ Icc 1 41,
      0 ≤ U n ∧ (n+1 : ℚ) < ∑ k ∈ range 20, (U n)^k / (k.factorial : ℚ) ∧
        1/4*(U n)^2+(57722/100000+693148/2000000)*(U n)+1833/10000 <
          ∑ r ∈ Icc 1 n, (tau1 r : ℚ)/r := by
    decide +kernel
  have hn1 : 1 ≤ ⌊z⌋₊ := Nat.floor_pos.mpr hz
  have hn42 : ⌊z⌋₊ ≤ 41 := by
    have hh := Nat.floor_le (by linarith : 0 ≤ z)
    have hh2 : (⌊z⌋₊ : ℝ) < 42 := hh.trans_lt hz42
    have hh3 : ⌊z⌋₊ < 42 := by exact_mod_cast hh2
    omega
  obtain ⟨hu, he, hs⟩ := cert ⌊z⌋₊ (mem_Icc.mpr ⟨hn1, hn42⟩)
  have huR : 0 ≤ (U ⌊z⌋₊ : ℝ) := by exact_mod_cast hu
  have heR : (⌊z⌋₊ : ℝ)+1 < ∑ k ∈ range 20, (U ⌊z⌋₊ : ℝ)^k / (k.factorial : ℝ) := by
    exact_mod_cast he
  have hlog : Real.log z ≤ (U ⌊z⌋₊ : ℝ) := by
    rw [Real.log_le_iff_le_exp (by linarith : 0 < z)]
    exact (Nat.lt_floor_add_one z).le.trans
      (heR.le.trans (Real.sum_le_exp_of_nonneg huR 20))
  have hsR : (1:ℝ)/4*(U ⌊z⌋₊ : ℝ)^2+
      (57722/100000+693148/2000000)*(U ⌊z⌋₊ : ℝ)+1833/10000 <
      ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hs
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have hg := gamma_bounds.2
  have hl := Real.log_two_lt_d9
  have hlog0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hsq := pow_le_pow_left₀ hlog0 hlog 2
  have hcoef : Real.eulerMascheroniConstant+1/2*Real.log 2 ≤ 57722/100000+693148/2000000 := by linarith
  have hm := mul_le_mul hcoef hlog hlog0 (by norm_num : (0:ℝ) ≤ 57722/100000+693148/2000000)
  linarith

/-- Odd and even divisors split the divisor count in Vaughan 1977 equation 3.6. -/
theorem tau1_add_even_divisors (r : ℕ) :
    tau1 r + (r.divisors.filter Even).card = r.divisors.card := by
  have hh := Finset.card_filter_add_card_filter_not (s := r.divisors) Odd
  simpa [tau1, Nat.not_odd_iff_even] using hh

/-- The even divisors of a positive multiple of two are twice the divisors of its half. -/
theorem even_divisors_image (m : ℕ) :
    ((2*m).divisors.filter Even) = m.divisors.image (2*·) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_image]
  constructor
  · rintro ⟨⟨hd, hm0⟩, he⟩
    obtain ⟨k, rfl⟩ := he.two_dvd
    refine ⟨k, ⟨?_, by omega⟩, rfl⟩
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  · rintro ⟨k, ⟨hk, hm0⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left 2 hk, by omega⟩, even_two_mul k⟩

/-- Equation 3.6 on page 98 expressed as finite real sums. -/
theorem lemma5_divisor_identity (z : ℝ) (hz : 1 ≤ z) :
    (∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r) =
      (∑ r ∈ Icc 1 ⌊z⌋₊, (r.divisors.card : ℝ)/r) -
        1/2 * ∑ m ∈ Icc 1 ⌊z/2⌋₊, (m.divisors.card : ℝ)/m := by
  let E := (Icc 1 ⌊z⌋₊).filter Even
  have hE : E = (Icc 1 ⌊z/2⌋₊).image (2*·) := by
    ext r
    simp only [E, mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hr1, hrz⟩, he⟩
      obtain ⟨m, rfl⟩ := he.two_dvd
      refine ⟨m, ⟨by omega, ?_⟩, rfl⟩
      apply Nat.le_floor
      have hrR := (Nat.le_floor_iff (by linarith : 0 ≤ z)).mp hrz
      push_cast at hrR
      linarith
    · rintro ⟨m, ⟨hm1, hmz⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, even_two_mul m⟩
      apply Nat.le_floor
      have hmR := (Nat.le_floor_iff (by linarith : 0 ≤ z/2)).mp hmz
      push_cast
      linarith
  have hzero (r : ℕ) (hr : ¬ Even r) : (r.divisors.filter Even).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro d hd he
    exact hr (even_iff_two_dvd.mpr (dvd_trans he.two_dvd (Nat.dvd_of_mem_divisors hd)))
  have hsum : (∑ r ∈ Icc 1 ⌊z⌋₊, ((r.divisors.filter Even).card : ℝ)/r) =
      1/2 * ∑ m ∈ Icc 1 ⌊z/2⌋₊, (m.divisors.card : ℝ)/m := by
    calc
      _ = ∑ r ∈ E, ((r.divisors.filter Even).card : ℝ)/r := by
        symm
        apply sum_subset (filter_subset _ _)
        intro r hr hnot
        have he : ¬ Even r := by simpa [E, hr] using hnot
        simp [hzero r he]
      _ = _ := by
        rw [hE, sum_image]
        · rw [mul_sum]
          apply sum_congr rfl
          intro m hm
          rw [even_divisors_image, card_image_of_injective _ (fun a b h => by omega)]
          push_cast
          ring
        · intro a ha b hb he
          change 2*a = 2*b at he
          omega
  have hcount (r : ℕ) : (tau1 r : ℝ)+(r.divisors.filter Even).card = r.divisors.card := by
    exact_mod_cast tau1_add_even_divisors r
  have hsum' : (∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r) +
      (∑ r ∈ Icc 1 ⌊z⌋₊, ((r.divisors.filter Even).card : ℝ)/r) =
      ∑ r ∈ Icc 1 ⌊z⌋₊, (r.divisors.card : ℝ)/r := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    rw [← add_div, hcount]
  linarith

set_option maxHeartbeats 1000000 in
/-- The finite range below 121 in the alternate proof of Vaughan Lemma 5, page 99.
The 79 new endpoint certificates close the range from 42 to 121. -/
theorem lemma5_below_121 (z : ℝ) (hz : 1 ≤ z) (hz42 : z < 121) :
    1 / 4 * Real.log z ^ 2 + (Real.eulerMascheroniConstant + 1 / 2 * Real.log 2) * Real.log z
      + 0.1833 < ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ) / r := by
  by_cases hsmall : z < 42
  · exact lemma5_below_42 z hz hsmall
  have hzlarge : 42 ≤ z := le_of_not_gt hsmall
  let U : ℕ → ℚ := fun n =>
    (([376121, 378419, 380667, 382865, 385015, 387121, 389183, 391203, 393183, 395125, 397030, 398899, 400734, 402536, 404306, 406045, 407754, 409435, 411088, 412714, 414314, 415889, 417439, 418966, 420470, 421951, 423411, 424850, 426268, 427667, 429046, 430407, 431749, 433074, 434381, 435671, 436945, 438203, 439445, 440672, 441885, 443082, 444266, 445435, 446591, 447734, 448864, 449981, 451086, 452179, 453260, 454330, 455388, 456435, 457472, 458497, 459512, 460518, 461513, 462498, 463473, 464440, 465397, 466344, 467283, 468214, 469135, 470049, 470954, 471850, 472739, 473620, 474494, 475360, 476218, 477069, 477913, 478750, 479580] : List ℚ).getD (n-42) 0) / 100000
  have cert : ∀ n ∈ Icc 42 120,
      0 ≤ U n ∧ (n+1 : ℚ) < ∑ k ∈ range 20, (U n)^k / (k.factorial : ℚ) ∧
        1/4*(U n)^2+(57722/100000+693148/2000000)*(U n)+1833/10000 <
          ∑ r ∈ Icc 1 n, (tau1 r : ℚ)/r := by
    decide +kernel
  have hn1 : 1 ≤ ⌊z⌋₊ := Nat.floor_pos.mpr hz
  have hnlo : 42 ≤ ⌊z⌋₊ := Nat.le_floor hzlarge
  have hn42 : ⌊z⌋₊ ≤ 120 := by
    have hh := Nat.floor_le (by linarith : 0 ≤ z)
    have hh2 : (⌊z⌋₊ : ℝ) < 121 := hh.trans_lt hz42
    have hh3 : ⌊z⌋₊ < 121 := by exact_mod_cast hh2
    omega
  obtain ⟨hu, he, hs⟩ := cert ⌊z⌋₊ (mem_Icc.mpr ⟨hnlo, hn42⟩)
  have huR : 0 ≤ (U ⌊z⌋₊ : ℝ) := by exact_mod_cast hu
  have heR : (⌊z⌋₊ : ℝ)+1 < ∑ k ∈ range 20, (U ⌊z⌋₊ : ℝ)^k / (k.factorial : ℝ) := by
    exact_mod_cast he
  have hlog : Real.log z ≤ (U ⌊z⌋₊ : ℝ) := by
    rw [Real.log_le_iff_le_exp (by linarith : 0 < z)]
    exact (Nat.lt_floor_add_one z).le.trans
      (heR.le.trans (Real.sum_le_exp_of_nonneg huR 20))
  have hsR : (1:ℝ)/4*(U ⌊z⌋₊ : ℝ)^2+
      (57722/100000+693148/2000000)*(U ⌊z⌋₊ : ℝ)+1833/10000 <
      ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hs
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have hg := gamma_bounds.2
  have hl := Real.log_two_lt_d9
  have hlog0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hsq := pow_le_pow_left₀ hlog0 hlog 2
  have hcoef : Real.eulerMascheroniConstant+1/2*Real.log 2 ≤ 57722/100000+693148/2000000 := by linarith
  have hm := mul_le_mul hcoef hlog hlog0 (by norm_num : (0:ℝ) ≤ 57722/100000+693148/2000000)
  linarith


open LeanLab.RieselVaughan1983 in
/-- The analytic range of Vaughan 1977 Lemma 5, using the existing hyperbola remainder. -/
theorem lemma5_above_121 (z : ℝ) (hz : 121 ≤ z) :
    1/4*Real.log z^2+(Real.eulerMascheroniConstant+1/2*Real.log 2)*Real.log z+0.1833 <
      ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r := by
  have hz0 : 0 < z := by linarith
  have hN1 : (11 : ℝ) ≤ ⌊Real.sqrt z⌋₊ := by
    exact_mod_cast (Nat.le_floor (show (11 : ℝ) ≤ Real.sqrt z by
      rw [Real.le_sqrt (by norm_num) hz0.le]
      norm_num
      exact hz) : 11 ≤ ⌊Real.sqrt z⌋₊)
  have hN2 : (7 : ℝ) ≤ ⌊Real.sqrt (z/2)⌋₊ := by
    exact_mod_cast (Nat.le_floor (show (7 : ℝ) ≤ Real.sqrt (z/2) by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
      linarith) : 7 ≤ ⌊Real.sqrt (z/2)⌋₊)
  have hE1 := lemma5_divisor_error z (by linarith)
  have hE2 := lemma5_divisor_error (z/2) (by linarith)
  have hb1 : 2*(1/(⌊Real.sqrt z⌋₊ : ℝ)) ≤ 2/11 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11) hN1
    linarith
  have hb2 : 2*(1/(⌊Real.sqrt (z/2)⌋₊ : ℝ)) ≤ 2/7 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7) hN2
    linarith
  have he1 := abs_lt.mp (hE1.trans_le hb1)
  have he2 := abs_lt.mp (hE2.trans_le hb2)
  have hloghalf : Real.log (z/2) = Real.log z-Real.log 2 :=
    Real.log_div hz0.ne' (by norm_num)
  have hg := gamma_bounds
  have hloglo : (0.693147 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hloghi : Real.log 2 ≤ (0.693148 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hprod : (0.57721 : ℝ)*0.693147 ≤ Real.eulerMascheroniConstant*Real.log 2 :=
    mul_le_mul hg.1.le hloglo (by norm_num) (by linarith)
  have hsqlo : (0.57721 : ℝ)^2 ≤ Real.eulerMascheroniConstant^2 :=
    pow_le_pow_left₀ (by norm_num) hg.1.le 2
  have hsqhi : Real.log 2^2 ≤ (0.693148 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) hloghi 2
  have hst := LeanLab.RieselVaughan1983.StieltjesCert.stieltjes1_bounds.2
  have hc : (0.1833 : ℝ) < Real.eulerMascheroniConstant*Real.log 2-Real.log 2^2/4+
      Real.eulerMascheroniConstant^2/2-stieltjes1-2/11-1/7 := by
    linarith
  rw [lemma5_divisor_identity z (by linarith)]
  unfold lem1E at he1 he2
  rw [hloghalf] at he2
  nlinarith only [he1.1, he2.2, hc]

/-- LEAF. Lemma 5: for `z ≥ 1`,
`Σ_{r ≤ z} τ₁(r)/r > (1/4) log² z + (γ + (1/2) log 2) log z + 0.1833`. Vaughan 1977 p. 98 and
99, Lemma 5, via (3.6), (3.7) and Euler-Maclaurin for `z ≥ 42`, direct check below 42; the
margin is small, about `10^{-4}`, near some integers. Unit U-1525. -/
theorem lemma5 (z : ℝ) (hz : 1 ≤ z) :
    1 / 4 * Real.log z ^ 2 + (Real.eulerMascheroniConstant + 1 / 2 * Real.log 2) * Real.log z
      + 0.1833 < ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ) / r := by
  by_cases hsmall : z < 121
  · exact lemma5_below_121 z hz hsmall
  · exact lemma5_above_121 z (le_of_not_gt hsmall)

/-- The nonnegative remainder at the end of Lemma 6, Vaughan 1977 page 99.
Mathlib's rational lower bound for the logarithm gives the claim directly. -/
theorem lemma6_remainder_nonneg (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ 0.9238 * Real.log (1 + 1/z) - 0.1833/(z+1) - 1/(2*z) := by
  have hz0 : 0 < z := by linarith
  have hlog := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1/z by positivity)
  have heq : 2*(1/z)/(1/z+2) = 2/(2*z+1) := by field_simp; ring
  rw [heq] at hlog
  have hpoly : 0 ≤ 0.9238 * (2/(2*z+1)) - 0.1833/(z+1) - 1/(2*z) := by
    apply (nonneg_of_mul_nonneg_left _ (show 0 < 2*z*(z+1)*(2*z+1) by positivity))
    field_simp
    nlinarith [sq_nonneg (z-1)]
  linarith

/-- Abel summation for the weighted sum in Lemma 6, Vaughan 1977 page 99. -/
theorem tau1_partial_summation (z : ℝ) (hz : 1 ≤ z) :
    (∑ r ∈ Icc 1 ⌊z⌋₊, z / (z+r) * ((tau1 r : ℝ)/r)) =
      1/2 * (∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ)/r) +
        ∫ t in Set.Ioc 1 z, z/(z+t)^2 * ∑ r ∈ Icc 1 ⌊t⌋₊, (tau1 r : ℝ)/r := by
  have hz0 : 0 < z := by linarith
  let c : ℕ → ℝ := fun r => (tau1 r : ℝ)/r
  have hsum (N : ℕ) (f : ℕ → ℝ) (hf : f 0 = 0) :
      ∑ r ∈ Icc 0 N, f r = ∑ r ∈ Icc 1 N, f r := by
    symm
    apply sum_subset
    · intro a ha
      simp only [mem_Icc] at *
      omega
    · intro a ha hnot
      have ha0 : a = 0 := by
        simp only [mem_Icc] at *
        omega
      simpa [ha0] using hf
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 z) :
      HasDerivAt (fun t : ℝ => z/(z+t)) (-z/(z+t)^2) t := by
    convert (hasDerivAt_const t z).div ((hasDerivAt_const t z).add (hasDerivAt_id t))
      (by linarith [ht.1] : z+t ≠ 0) using 1
    · rfl
    · simp only [Pi.add_apply, id_eq]
      ring
  have hcont : ContinuousOn (fun t : ℝ => -z/(z+t)^2) (Set.Icc 1 z) := by
    apply ContinuousOn.div continuousOn_const ((continuousOn_const.add continuousOn_id).pow 2)
    intro t ht
    have hh : 0 < z+t := by linarith [ht.1]
    exact pow_ne_zero 2 hh.ne'
  have hi : IntegrableOn (deriv (fun t : ℝ => z/(z+t))) (Set.Icc 1 z) := by
    apply hcont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have hab := sum_mul_eq_sub_integral_mul₀ c (by simp [c]) z
    (fun t ht => (hd t ht).differentiableAt) hi
  rw [hsum ⌊z⌋₊ (fun r => z/(z+r)*c r) (by simp [c]), hsum ⌊z⌋₊ c (by simp [c])] at hab
  have hf : z/(z+z) = (1/2 : ℝ) := by field_simp; ring
  rw [hf] at hab
  have hint : (∫ t in Set.Ioc 1 z, deriv (fun t : ℝ => z/(z+t)) t * ∑ r ∈ Icc 0 ⌊t⌋₊, c r) =
      -(∫ t in Set.Ioc 1 z, z/(z+t)^2 * ∑ r ∈ Icc 1 ⌊t⌋₊, c r) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, hsum ⌊t⌋₊ c (by simp [c])]
    ring
  rw [hint, sub_neg_eq_add] at hab
  exact hab

/-- The lower Abel integral from Lemma 5 in the proof of Lemma 6, page 99.
This theorem is conditional on the still cited Lemma 5. -/
theorem lemma6_abel_lower (z : ℝ) (hz : 1 ≤ z) :
    1/2 * (1/4*Real.log z^2+(Real.eulerMascheroniConstant+1/2*Real.log 2)*Real.log z+0.1833) +
      (∫ t in Set.Ioc 1 z, z/(z+t)^2 *
        (1/4*Real.log t^2+(Real.eulerMascheroniConstant+1/2*Real.log 2)*Real.log t+0.1833)) <
      ∑ r ∈ Icc 1 ⌊z⌋₊, z/(z+r)*((tau1 r : ℝ)/r) := by
  have hz0 : 0 < z := by linarith
  have hcont : ContinuousOn (fun t : ℝ => z/(z+t)^2) (Set.Icc 1 z) := by
    apply ContinuousOn.div continuousOn_const ((continuousOn_const.add continuousOn_id).pow 2)
    intro t ht
    exact pow_ne_zero 2 (by change z+t ≠ 0; linarith [ht.1])
  have hlog : ContinuousOn Real.log (Set.Icc 1 z) :=
    continuousOn_id.log (by intro t ht; change t ≠ 0; linarith [ht.1])
  have hB : ContinuousOn (fun t : ℝ =>
      1/4*Real.log t^2+(Real.eulerMascheroniConstant+1/2*Real.log 2)*Real.log t+0.1833) (Set.Icc 1 z) := by
    exact ((continuousOn_const.mul (hlog.pow 2)).add (continuousOn_const.mul hlog)).add continuousOn_const
  have hi1 := ((hcont.mul hB).integrableOn_Icc (μ := volume)).mono_set Set.Ioc_subset_Icc_self
  have hi2 := (integrableOn_mul_sum_Icc (fun r : ℕ => (tau1 r : ℝ)/r)
    (show (0 : ℝ) ≤ 1 by norm_num) hcont.integrableOn_Icc (m := 1)).mono_set Set.Ioc_subset_Icc_self
  have hint := setIntegral_mono_on hi1 hi2 measurableSet_Ioc (fun t ht =>
    mul_le_mul_of_nonneg_left (lemma5 t ht.1.le).le (show 0 ≤ z/(z+t)^2 by positivity))
  have hhalf := mul_lt_mul_of_pos_left (lemma5 z hz) (show (0 : ℝ) < 1/2 by norm_num)
  exact (add_lt_add_of_lt_of_le hhalf hint).trans_eq (tau1_partial_summation z hz).symm
/-- The alternating reciprocal square sum used in Lemma 6, Vaughan 1977 page 99. -/
theorem lemma6_alternating_sum : HasSum (fun n : ℕ => (-1 : ℝ)^n / ((n : ℝ)+1)^2) (Real.pi^2/12) := by
  have hh := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide) (x := (1/2 : ℝ)) (by norm_num)
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_zero, bernoulli_one,
    bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two] at hh
  have hs : HasSum (fun n : ℕ => (-1 : ℝ)^(n+1)/(n : ℝ)^2) (Real.pi^2/12) := by
    convert hh.neg using 1
    · funext n
      rw [show 2*Real.pi*(n : ℝ)*(1/2) = (n : ℝ)*Real.pi by ring, Real.cos_nat_mul_pi, pow_succ]
      ring
    · ring
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  simpa [Nat.cast_add, Nat.cast_one, pow_succ, Finset.sum_range_one, div_eq_mul_inv] using hs'



/-- The logarithmic integral corresponding to the alternating sum on page 99. -/
theorem lemma6_dilog_integral : (∫ t in Set.Ioo (0 : ℝ) 1, Real.log (1+t)/t) = Real.pi^2/12 := by
  let F : ℕ → ℝ → ℝ := fun n t => (-t)^n/((n : ℝ)+1)
  have hFint (n : ℕ) : Integrable (F n) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    exact (((continuous_neg.pow n).div_const ((n : ℝ)+1)).integrableOn_Icc (μ := volume)).mono_set Set.Ioo_subset_Icc_self
  have hbase (n : ℕ) : (∫ t in Set.Ioo (0 : ℝ) 1, t^n/((n : ℝ)+1)) = 1/((n : ℝ)+1)^2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_div, integral_pow]
    simp
    field_simp
  have hnorm (n : ℕ) : (∫ t in Set.Ioo (0 : ℝ) 1, ‖F n t‖) = 1/((n : ℝ)+1)^2 := by
    calc
      _ = ∫ t in Set.Ioo (0 : ℝ) 1, t^n/((n : ℝ)+1) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only [F]
        rw [norm_div, Real.norm_eq_abs, abs_pow, abs_neg, abs_of_pos ht.1,
          Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)+1)]
      _ = _ := hbase n
  have hsummable : Summable (fun n : ℕ => ∫ t in Set.Ioo (0 : ℝ) 1, ‖F n t‖) := by
    simp_rw [hnorm]
    have hh := (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hsum := hasSum_integral_of_summable_integral_norm hFint hsummable
  have hterm (n : ℕ) : (∫ t in Set.Ioo (0 : ℝ) 1, F n t) = (-1 : ℝ)^n/((n : ℝ)+1)^2 := by
    calc
      _ = ∫ t in Set.Ioo (0 : ℝ) 1, (-1 : ℝ)^n * (t^n/((n : ℝ)+1)) := by
        congr 1
        funext t
        dsimp only [F]
        rw [neg_pow]
        ring
      _ = _ := by rw [MeasureTheory.integral_const_mul, hbase]; ring
  simp_rw [hterm] at hsum
  have heq : (∫ t in Set.Ioo (0 : ℝ) 1, ∑' n, F n t) = Real.pi^2/12 := hsum.unique lemma6_alternating_sum
  rw [← heq]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hh := (Real.hasSum_pow_div_log_of_abs_lt_one (x := -t)
    (by rw [abs_neg, abs_of_pos ht.1]; exact ht.2)).div_const (-t)
  have he : HasSum (fun n => F n t) (Real.log (1+t)/t) := by
    convert hh using 1
    · funext n
      dsimp only [F]
      rw [pow_succ]
      field_simp [ht.1.ne']
    · simp only [sub_neg_eq_add, neg_div_neg_eq]
  exact he.tsum_eq.symm

/-- The cutoff bound for the logarithmic integral in Lemma 6, page 99. -/
theorem lemma6_integral_lower (z : ℝ) (hz : 1 ≤ z) :
    Real.pi^2/12-1/z ≤ ∫ t in (1 : ℝ)..z, Real.log (1+t/z)/t := by
  let f : ℝ → ℝ := fun t => Real.log (1+t)/t
  have hz0 : 0 < z := by linarith
  have hw0 : 0 ≤ 1/z := by positivity
  have hw1 : 1/z ≤ 1 := by rw [div_le_one hz0]; exact hz
  have hfbound (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖f t‖ ≤ 1 := by
    by_cases ht0 : t = 0
    · simp [f, ht0]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hlog0 : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith)
      have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+t)
      dsimp [f]
      rw [abs_of_nonneg (div_nonneg hlog0 htpos.le), div_le_one htpos]
      linarith
  have hfcont : ContinuousOn f (Set.Ioc 0 1) := by
    apply ContinuousOn.div
    · apply (continuousOn_const.add continuousOn_id).log
      intro t ht
      change 1+t ≠ 0
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      linarith [ht.1]
  have hfi : IntegrableOn f (Set.Ioc 0 1) := by
    apply (integrable_const (1 : ℝ)).mono' (hfcont.aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hfbound t ⟨ht.1.le, ht.2⟩
  have hi0 : IntervalIntegrable f volume 0 (1/z) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hw0]
    exact hfi.mono_set (Set.Ioc_subset_Ioc_right hw1)
  have hi1 : IntervalIntegrable f volume (1/z) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hw1]
    exact hfi.mono_set (Set.Ioc_subset_Ioc_left hw0)
  have hsmall : (∫ t in (0 : ℝ)..(1/z), f t) ≤ 1/z := by
    have hh := intervalIntegral.integral_mono_on hw0 hi0 (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t ht => (le_abs_self (f t)).trans (by simpa only [Real.norm_eq_abs] using hfbound t ⟨ht.1, ht.2.trans hw1⟩))
    simpa using hh
  have hfull : (∫ t in (0 : ℝ)..1, f t) = Real.pi^2/12 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    exact lemma6_dilog_integral
  have hcut := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  rw [hfull] at hcut
  have hscaled : (∫ t in (1 : ℝ)..z, Real.log (1+t/z)/t) = ∫ t in (1/z)..1, f t := by
    have hh := intervalIntegral.integral_comp_div f hz0.ne' (a := (1 : ℝ)) (b := z)
    rw [div_self hz0.ne'] at hh
    have heq : (fun t : ℝ => f (t/z)) = fun t => z*(Real.log (1+t/z)/t) := by
      funext t
      dsimp [f]
      rw [div_div_eq_mul_div]
      ring
    rw [heq, intervalIntegral.integral_const_mul] at hh
    exact (mul_left_cancel₀ hz0.ne' hh)
  rw [hscaled]
  linarith

set_option maxHeartbeats 1000000 in
/-- Evaluation of the Abel polynomial integral in Lemma 6, page 99.
The paper uses beta equal to gamma plus one half log 2 and delta equal to 0.1833. -/
theorem lemma6_abel_evaluation (β δ z : ℝ) (hz : 1 ≤ z) :
    1/2*(1/4*Real.log z^2+β*Real.log z+δ) +
      (∫ t in (1 : ℝ)..z, z/(z+t)^2*(1/4*Real.log t^2+β*Real.log t+δ)) =
    1/4*Real.log z^2+(β-1/2*Real.log 2)*Real.log z+δ*z/(z+1)-β*Real.log 2+
      β*Real.log (1+1/z)+1/2*(∫ t in (1 : ℝ)..z, Real.log (1+t/z)/t) := by
  have hz0 : 0 < z := by linarith
  let B : ℝ → ℝ := fun t => 1/4*Real.log t^2+β*Real.log t+δ
  let H : ℝ → ℝ := fun t => z/(z+t)*B t-1/4*Real.log t^2-β*Real.log t+
    1/2*Real.log t*Real.log (1+t/z)+β*Real.log (z+t)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 1 z) :
      HasDerivAt H (1/2*(Real.log (1+t/z)/t)-z/(z+t)^2*B t) t := by
    rw [Set.uIcc_of_le hz] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hzt0 : 0 < z+t := by positivity
    have hk0 : 0 < 1+t/z := by positivity
    have hL := Real.hasDerivAt_log ht0.ne'
    have hK : HasDerivAt (fun t : ℝ => Real.log (1+t/z)) (1/(z+t)) t := by
      have hh := (((hasDerivAt_id t).div_const z).const_add 1).log hk0.ne'
      convert hh using 1
      · rfl
      · change 1/(z+t) = 1/z/(1+t/z)
        field_simp
    have hZ : HasDerivAt (fun t : ℝ => Real.log (z+t)) (1/(z+t)) t := by
      convert ((hasDerivAt_id t).const_add z).log hzt0.ne' using 1 <;> simp
    have hG : HasDerivAt (fun t : ℝ => z/(z+t)) (-z/(z+t)^2) t := by
      convert (hasDerivAt_const t z).div ((hasDerivAt_const t z).add (hasDerivAt_id t)) hzt0.ne' using 1
      · rfl
      · simp only [Pi.add_apply, id_eq]
        ring
    have hB := (((hL.pow 2).const_mul (1/4)).add (hL.const_mul β)).add_const δ
    have hh := (((hG.mul hB).sub ((hL.pow 2).const_mul (1/4))).sub (hL.const_mul β)).add
      (((hL.mul hK).const_mul (1/2))) |>.add (hZ.const_mul β)
    convert hh using 1
    · funext u
      dsimp [H, B]
      ring
    · dsimp [B]
      norm_num
      field_simp [ht0.ne', hz0.ne', hzt0.ne']; ring
  have hL : ContinuousOn Real.log (Set.uIcc 1 z) := by
    apply continuousOn_id.log
    intro t ht
    rw [Set.uIcc_of_le hz] at ht
    change t ≠ 0
    linarith [ht.1]
  have hK : ContinuousOn (fun t : ℝ => Real.log (1+t/z)) (Set.uIcc 1 z) := by
    apply (continuousOn_const.add (continuousOn_id.div_const z)).log
    intro t ht
    rw [Set.uIcc_of_le hz] at ht
    change 1+t/z ≠ 0
    have ht0 : 0 < t := by linarith [ht.1]
    positivity
  have hiK : IntervalIntegrable (fun t : ℝ => Real.log (1+t/z)/t) volume 1 z := by
    apply ContinuousOn.intervalIntegrable
    exact hK.div continuousOn_id (by intro t ht; rw [Set.uIcc_of_le hz] at ht; change t ≠ 0; linarith [ht.1])
  have hiB : IntervalIntegrable (fun t : ℝ => z/(z+t)^2*B t) volume 1 z := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const ((continuousOn_const.add continuousOn_id).pow 2)
      intro t ht
      rw [Set.uIcc_of_le hz] at ht
      exact pow_ne_zero 2 (by change z+t ≠ 0; linarith [ht.1])
    · exact ((continuousOn_const.mul (hL.pow 2)).add (continuousOn_const.mul hL)).add continuousOn_const
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hiK.const_mul (1/2)).sub hiB)
  rw [intervalIntegral.integral_sub (hiK.const_mul (1/2)) hiB, intervalIntegral.integral_const_mul] at heq
  have hf : z/(z+z) = (1/2 : ℝ) := by field_simp; ring
  have hlog2z : Real.log (z+z) = Real.log 2+Real.log z := by
    rw [show z+z=2*z by ring, Real.log_mul (by norm_num) hz0.ne']
  have hlogz1 : Real.log (z+1) = Real.log z+Real.log (1+1/z) := by
    rw [← Real.log_mul hz0.ne' (by positivity : 1+1/z ≠ 0)]
    congr 1
    field_simp
  dsimp [H, B] at heq
  rw [hf, Real.log_one, show 1+z/z=(2 : ℝ) by field_simp; ring, hlog2z, hlogz1] at heq
  linear_combination -heq


/-- LEAF. Lemma 6: for `z ≥ 1`,
`Σ_{r ≤ z} z/(z + r) · τ₁(r)/r > (1/4) log² z + γ log z - 0.0458`. Vaughan 1977 p. 99,
Lemma 6, partial summation from Lemma 5. Unit U-1525. -/
theorem lemma6 (z : ℝ) (hz : 1 ≤ z) :
    1 / 4 * Real.log z ^ 2 + Real.eulerMascheroniConstant * Real.log z - 0.0458 <
      ∑ r ∈ Icc 1 ⌊z⌋₊, z / (z + r) * ((tau1 r : ℝ) / r) := by
  have hz0 : 0 < z := by linarith
  let β : ℝ := Real.eulerMascheroniConstant+1/2*Real.log 2
  have habel := lemma6_abel_lower z hz
  rw [← intervalIntegral.integral_of_le hz] at habel
  have heval := lemma6_abel_evaluation β 0.1833 z hz
  change 1/2*(1/4*Real.log z^2+β*Real.log z+0.1833) + _ < _ at habel
  rw [heval] at habel
  have hcut := lemma6_integral_lower z hz
  have hβlo : 0.9237 ≤ β := by
    dsimp [β]
    linarith [gamma_bounds.1, Real.log_two_gt_d9]
  have hβhi : β ≤ 0.9238 := by
    dsimp [β]
    linarith [gamma_bounds.2, Real.log_two_lt_d9]
  have hlog0 : 0 ≤ Real.log (1+1/z) := by
    apply Real.log_nonneg
    have hh : 0 ≤ 1/z := by positivity
    linarith
  have hprod : β*Real.log 2 ≤ 0.9238*0.6931471808 :=
    mul_le_mul hβhi Real.log_two_lt_d9.le (by positivity) (by norm_num)
  have hconst : -0.0458 ≤ 0.1833-β*Real.log 2+Real.pi^2/24 := by
    nlinarith [Real.pi_gt_d6]
  have hF : 0 ≤ 0.9237*Real.log (1+1/z)-0.1833/(z+1)-1/(2*z) := by
    have hh := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1/z by positivity)
    have heq : 2*(1/z)/(1/z+2) = 2/(2*z+1) := by field_simp; ring
    rw [heq] at hh
    have hpoly : 0 ≤ 0.9237*(2/(2*z+1))-0.1833/(z+1)-1/(2*z) := by
      apply (nonneg_of_mul_nonneg_left _ (show 0 < 2*z*(z+1)*(2*z+1) by positivity))
      field_simp
      nlinarith [sq_nonneg (z-1)]
    linarith
  have hβprod := mul_le_mul_of_nonneg_right hβlo hlog0
  have hδ : (0.1833 : ℝ)*z/(z+1) = 0.1833-0.1833/(z+1) := by
    field_simp
    ring
  rw [hδ] at habel
  have hrecip : (1 : ℝ)/(2*z) = 1/2*(1/z) := by ring
  rw [hrecip] at hF
  dsimp [β] at *
  nlinarith

/-! ### Leaves: (3.10), (3.13) and the closing numerics of Lemma 7 -/

/-- The squarefree kernel comparison used before equation 3.10, page 100. -/
theorem sk_mul_le (r d : ℕ) (hr : 1 ≤ r) : sk (r*d) ≤ r*sk d := by
  by_cases hd : d = 0
  · subst d
    simpa [sk] using hr
  have hr0 : r ≠ 0 := by omega
  have hsk0 : sk d ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hdiv : sk (r*d) ∣ r*sk d := by
    apply (Nat.prod_primeFactors_dvd_iff (mul_ne_zero hr0 hsk0)).mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdiv := Nat.dvd_of_mem_primeFactors hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hprime, ?_, mul_ne_zero hr0 hsk0⟩
    rcases hprime.dvd_mul.mp hpdiv with hpr | hpd
    · exact dvd_mul_of_dvd_left hpr _
    · apply dvd_mul_of_dvd_right
      exact Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hprime, hpd, hd⟩)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hr0 hsk0)) hdiv

set_option maxHeartbeats 1000000 in
/-- The finite rectangular truncation of Lemma 4 used on page 100 before equation 3.10.
This theorem is conditional on the still cited Lemma 4. -/
theorem lemma4_rectangular (n : ℕ) (hn : Even n) (hn0 : 0 < n) (z : ℝ) (hz : 1 ≤ z) (D : Finset ℕ) :
    (∑ d ∈ D, if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
      ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0) ≤
      Sn n z z⁻¹ * singQ n := by
  have hz0 : 0 < z := by linarith
  have hsk (d : ℕ) : 0 < (sk d : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  let R := Icc 1 ⌊z⌋₊
  let T := (R.product D).filter (fun rd => 1 ≤ rd.2 ∧ (sk rd.2 : ℝ) ≤ z ∧ rd.1 ≤ ⌊z/(sk rd.2 : ℝ)⌋₊)
  have hT : ∀ rd ∈ T, 1 ≤ rd.1 ∧ 1 ≤ rd.2 ∧ (sk (rd.1*rd.2) : ℝ) ≤ z := by
    intro rd hrd
    have hh := mem_filter.mp hrd
    have hr1 := (mem_Icc.mp (mem_product.mp hh.1).1).1
    refine ⟨hr1, hh.2.1, ?_⟩
    have hrl : (rd.1 : ℝ) ≤ z/(sk rd.2 : ℝ) :=
      (Nat.le_floor_iff (by positivity : 0 ≤ z/(sk rd.2 : ℝ))).mp hh.2.2.2
    have hbound := (le_div_iff₀ (hsk rd.2)).mp hrl
    have hhsk : (sk (rd.1*rd.2) : ℝ) ≤ rd.1*(sk rd.2 : ℝ) := by exact_mod_cast sk_mul_le rd.1 rd.2 hr1
    exact hhsk.trans hbound
  have h4 := lemma4 n hn hn0 z z⁻¹ hz (by positivity) T hT
  have hQP : 0 < singQ n := by
    unfold singQ
    apply prod_pos
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact div_pos (by linarith) (by linarith)
  have hprod : singQ n * (∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ)-2)/((p : ℝ)-1)) = 1 := by
    unfold singQ
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    field_simp [show (p : ℝ)-1 ≠ 0 by linarith, show (p : ℝ)-2 ≠ 0 by linarith]
  have hbound := mul_le_mul_of_nonneg_left h4 hQP.le
  rw [← mul_assoc, hprod, one_mul, mul_comm (singQ n)] at hbound
  apply le_trans _ hbound
  rw [sum_filter]
  have hexpand := Finset.sum_product_right R D (fun a : ℕ × ℕ =>
    if 1 ≤ a.2 ∧ (sk a.2 : ℝ) ≤ z ∧ a.1 ≤ ⌊z/(sk a.2 : ℝ)⌋₊ then
      g a.2*(tau1 a.1 : ℝ)/(a.1+a.1*z⁻¹*sk (a.1*a.2)) else 0)
  apply le_trans ?_ (le_of_eq hexpand.symm)
  apply sum_le_sum
  intro d hd
  by_cases hdz : 1 ≤ d ∧ (sk d : ℝ) ≤ z
  · simp only [hdz.1, hdz.2, true_and, ite_true]
    have hsub : Icc 1 ⌊z/(sk d : ℝ)⌋₊ ⊆ R := by
      intro r hr
      refine mem_Icc.mpr ⟨(mem_Icc.mp hr).1, ?_⟩
      apply (mem_Icc.mp hr).2.trans
      apply Nat.floor_le_floor
      apply div_le_self hz0.le
      have h1 := hsk d
      have hn : 1 ≤ sk d := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h1.ne')
      exact_mod_cast hn
    calc
      _ = ∑ r ∈ R, if r ≤ ⌊z/(sk d : ℝ)⌋₊ then z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0 := by
        rw [← sum_filter]
        apply sum_congr
        · ext r
          simp only [mem_filter]
          constructor
          · intro hr
            exact ⟨hsub hr, (mem_Icc.mp hr).2⟩
          · rintro ⟨hr, hr'⟩
            exact mem_Icc.mpr ⟨(mem_Icc.mp hr).1, hr'⟩
        · intro r hr
          rfl
      _ ≤ _ := by
        apply sum_le_sum
        intro r hr
        by_cases hrl : r ≤ ⌊z/(sk d : ℝ)⌋₊
        · simp only [hrl, ite_true]
          have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
          have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
          have hden : (r : ℝ)+r*z⁻¹*sk (r*d) ≤ r+r*z⁻¹*(r*(sk d : ℝ)) := by
            have hle : (sk (r*d) : ℝ) ≤ r*(sk d : ℝ) := by exact_mod_cast sk_mul_le r d hr1
            linarith [mul_le_mul_of_nonneg_left hle (show 0 ≤ (r : ℝ)*z⁻¹ by positivity)]
          have hh := div_le_div_of_nonneg_left (mul_nonneg (g_nonneg d) (Nat.cast_nonneg (tau1 r)))
            (show 0 < (r : ℝ)+r*z⁻¹*sk (r*d) by positivity) hden
          calc
            _ = g d*(tau1 r : ℝ)/(r+r*z⁻¹*(r*(sk d : ℝ))) := by field_simp
            _ ≤ _ := hh
        · simp [hrl]
  · have hh : ¬ (1 ≤ d ∧ (sk d : ℝ) ≤ z) := hdz
    simp only [hdz, ite_false]
    have hzero : ∀ r, ¬ (1 ≤ d ∧ (sk d : ℝ) ≤ z ∧ r ≤ ⌊z/(sk d : ℝ)⌋₊) := fun r h => hh ⟨h.1,h.2.1⟩
    simp [hzero]

/-- Summability and the infinite rectangular bound before equation 3.10, page 100.
This theorem is conditional on the still cited Lemma 4. -/

theorem lemma4_rectangular_tsum (n : ℕ) (hn : Even n) (hn0 : 0 < n) (z : ℝ) (hz : 1 ≤ z) :
    Summable (fun d : ℕ => if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
      ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0) ∧
    (∑' d : ℕ, if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
      ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0) ≤
      Sn n z z⁻¹ * singQ n := by
  have hnneg : 0 ≤ (fun d : ℕ => if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
      ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0) := by
    intro d
    dsimp only
    split_ifs
    · apply sum_nonneg
      intro r hr
      exact mul_nonneg (div_nonneg (by linarith) (by positivity))
        (div_nonneg (mul_nonneg (g_nonneg d) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    · exact le_rfl
  exact ⟨summable_of_sum_le hnneg (lemma4_rectangular n hn hn0 z hz),
    Real.tsum_le_of_sum_le hnneg (lemma4_rectangular n hn hn0 z hz)⟩


/-- The radical cutoff bounds its logarithm on page 100. -/
theorem eq310_log_cutoff (d : ℕ) (z : ℝ) (hdz : (sk d : ℝ) ≤ z) :
    0 ≤ Real.log (sk d) ∧ Real.log (sk d) ≤ Real.log z := by
  have hs : 0 < (sk d : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  exact ⟨Real.log_natCast_nonneg _, Real.log_le_log hs hdz⟩

/-- The square logarithm moment restricted by the radical is summable. -/
theorem eq310_log_sq_summable (z : ℝ) (hz : 1 ≤ z) :
    Summable (fun d => if (sk d : ℝ) ≤ z then g d * Real.log (sk d)^2 else 0) := by
  apply Summable.of_nonneg_of_le _ _ (hasSum_g.summable.mul_right (Real.log z^2))
  · intro d
    split_ifs
    · exact mul_nonneg (g_nonneg d) (sq_nonneg _)
    · exact le_rfl
  · intro d
    split_ifs with hd
    · have hh := eq310_log_cutoff d z hd
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1 hh.2 2) (g_nonneg d)
    · exact mul_nonneg (g_nonneg d) (sq_nonneg _)

/-- Termwise application of Lemma 6 in the proof of equation 3.10.
Lemma 6 supplies the comparison. -/
theorem eq310_term (d : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (if (sk d : ℝ) ≤ z then
      g d*(1/4*Real.log (z/(sk d : ℝ))^2 + Real.eulerMascheroniConstant*Real.log (z/(sk d : ℝ))-0.0458)
      else 0) ≤
    (if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
      ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0) := by
  by_cases hd0 : d = 0
  · subst d
    simp [g]
  by_cases hd : (sk d : ℝ) ≤ z
  · simp only [hd, Nat.one_le_iff_ne_zero.mpr hd0, and_self, ite_true]
    have hs : 0 < (sk d : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have ht : 1 ≤ z/(sk d : ℝ) := (le_div_iff₀ hs).mpr (by simpa using hd)
    have hh := mul_le_mul_of_nonneg_left (lemma6 (z/(sk d : ℝ)) ht).le (g_nonneg d)
    rw [Finset.mul_sum] at hh
    apply hh.trans_eq
    apply sum_congr rfl
    intro r hr
    have hz0 : z ≠ 0 := by linarith
    field_simp
  · simp [hd]

set_option maxHeartbeats 1000000 in
/-- The truncated logarithmic polynomial sum on page 100. -/
theorem eq310_polynomial_sum (z : ℝ) (hz : 1 ≤ z) :
    HasSum (fun d => if (sk d : ℝ) ≤ z then
      g d*(1/4*Real.log (z/(sk d : ℝ))^2 + Real.eulerMascheroniConstant*Real.log (z/(sk d : ℝ))-0.0458)
      else 0)
      ((Real.log z^2/4+Real.eulerMascheroniConstant*Real.log z-0.0458)*
          (∑' d, if (sk d : ℝ) ≤ z then g d else 0)
       -(Real.log z/2+Real.eulerMascheroniConstant)*
          (∑' d, if (sk d : ℝ) ≤ z then g d*Real.log (sk d) else 0)
       +(∑' d, if (sk d : ℝ) ≤ z then g d*Real.log (sk d)^2 else 0)/4) := by
  have hs : Summable (fun d => if (sk d : ℝ) ≤ z then g d else 0) := by
    apply Summable.of_nonneg_of_le _ _ hasSum_g.summable
    · intro d; split_ifs
      · exact g_nonneg d
      · exact le_rfl
    · intro d; split_ifs <;> simp_all [g_nonneg]
  have ht : Summable (fun d => if (sk d : ℝ) ≤ z then g d*Real.log (sk d) else 0) := by
    apply Summable.of_nonneg_of_le _ _ hasSum_g_log.summable
    · intro d; split_ifs
      · exact mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg _)
      · exact le_rfl
    · intro d; split_ifs <;> simp_all [mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg (sk d))]
  have hu := eq310_log_sq_summable z hz
  have hh := ((hs.hasSum.mul_left (Real.log z^2/4+Real.eulerMascheroniConstant*Real.log z-0.0458)).sub
    (ht.hasSum.mul_left (Real.log z/2+Real.eulerMascheroniConstant))).add (hu.hasSum.div_const 4)
  apply hh.congr_fun
  intro d
  by_cases hd : (sk d : ℝ) ≤ z
  · simp only [hd, ite_true]
    have hs0 : (sk d : ℝ) ≠ 0 := by
      exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    rw [Real.log_div (by linarith : z ≠ 0) hs0]
    ring
  · simp [hd]

/-- LEAF. (3.10): with `z = (2x/3)^{1/2}`, `L = log x`, `ℓ = log(3/2)`,
`Σ₁ = Σ_{s(d) ≤ z} g(d)`, `Σ₂ = Σ_d g(d) log s(d)`, `Σ₃ = Σ_{s(d) ≤ z} g(d) log² s(d)`,
`Σ₄ = Σ_d g(d)`:
`S_n(z, z^{-1}) Π_{p|n,p>2} (p-1)/(p-2) > (1/16) Σ₁ L² + ((γ/2 - ℓ/8) Σ₁ - Σ₂/4) L + Σ₃/4
 - (γ - ℓ/4) Σ₂ - (γℓ/2 + 0.0458 - ℓ²/16) Σ₄`.
Proof: Lemma 4 at `y = z^{-1}`, restrict to `r ≤ z/s(d)`, use `z + s(rd) ≤ z + r s(d)` and
Lemma 6 at `z/s(d)`, expand `log(z/s(d)) = (L - ℓ)/2 - log s(d)`. Vaughan 1977 p. 100, proof of
Lemma 7, (3.10), (3.11). Unit U-1525. -/
theorem eq310 (x : ℝ) (hx : 10 ^ 9 ≤ x) (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    1 / 16 * (∑' d, if (sk d : ℝ) ≤ zz x then g d else 0) * Real.log x ^ 2
      + ((Real.eulerMascheroniConstant / 2 - Real.log (3 / 2) / 8) *
          (∑' d, if (sk d : ℝ) ≤ zz x then g d else 0)
        - (∑' d, g d * Real.log (sk d)) / 4) * Real.log x
      + (∑' d, if (sk d : ℝ) ≤ zz x then g d * Real.log (sk d) ^ 2 else 0) / 4
      - (Real.eulerMascheroniConstant - Real.log (3 / 2) / 4) * (∑' d, g d * Real.log (sk d))
      - (Real.eulerMascheroniConstant * Real.log (3 / 2) / 2 + 0.0458
          - Real.log (3 / 2) ^ 2 / 16) * (∑' d, g d)
      < Sn n (zz x) (zz x)⁻¹ * singQ n := by
  let z := zz x
  have hz : 1 ≤ z := by
    dsimp [z, zz]
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    linarith
  have hz0 : 0 < z := by linarith
  have hx0 : 0 < x := by positivity
  have hlog : Real.log z = (Real.log x-Real.log (3/2))/2 := by
    dsimp [z, zz]
    rw [Real.log_sqrt (by linarith), Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) hx0.ne', Real.log_div (by norm_num) (by norm_num)]
    ring
  let F : ℕ → ℝ := fun d => if (sk d : ℝ) ≤ z then
    g d*(1/4*Real.log (z/(sk d : ℝ))^2+Real.eulerMascheroniConstant*Real.log (z/(sk d : ℝ))-0.0458) else 0
  let B : ℕ → ℝ := fun d => if 1 ≤ d ∧ (sk d : ℝ) ≤ z then
    ∑ r ∈ Icc 1 ⌊z/(sk d : ℝ)⌋₊, z/(z+r*(sk d : ℝ))*((g d*(tau1 r : ℝ))/r) else 0
  have hsF := eq310_polynomial_sum z hz
  have hsB := lemma4_rectangular_tsum n hn hn0 z hz
  have hstrict : F 1 < B 1 := by
    simpa [F, B, sk, g_one, hz] using lemma6 z hz
  have hlt : (∑' d, F d) < ∑' d, B d :=
    Summable.tsum_lt_tsum (fun d => eq310_term d z hz) hstrict hsF.summable hsB.1
  have hs : Summable (fun d => if (sk d : ℝ) ≤ z then g d else 0) := by
    apply Summable.of_nonneg_of_le _ _ hasSum_g.summable
    · intro d; split_ifs
      · exact g_nonneg d
      · exact le_rfl
    · intro d; split_ifs <;> simp_all [g_nonneg]
  have ht : Summable (fun d => if (sk d : ℝ) ≤ z then g d*Real.log (sk d) else 0) := by
    apply Summable.of_nonneg_of_le _ _ hasSum_g_log.summable
    · intro d; split_ifs
      · exact mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg _)
      · exact le_rfl
    · intro d; split_ifs <;> simp_all [mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg (sk d))]
  have hmass : (∑' d, if (sk d : ℝ) ≤ z then g d else 0) ≤ ∑' d, g d := by
    exact Summable.tsum_le_tsum (fun d => by split_ifs <;> simp_all [g_nonneg]) hs hasSum_g.summable
  have hmoment : (∑' d, if (sk d : ℝ) ≤ z then g d*Real.log (sk d) else 0) ≤ ∑' d, g d*Real.log (sk d) := by
    exact Summable.tsum_le_tsum (fun d => by split_ifs <;> simp_all [mul_nonneg (g_nonneg d) (Real.log_natCast_nonneg (sk d))]) ht hasSum_g_log.summable
  have hg : 0 < Real.eulerMascheroniConstant := by linarith [gamma_bounds.1]
  have hl : 0 ≤ Real.log z := Real.log_nonneg hz
  have hb : 0 ≤ Real.log z/2+Real.eulerMascheroniConstant := by positivity
  have hell : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hellhi : Real.log (3/2) < 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3/2)
    linarith
  have hc : 0 ≤ Real.eulerMascheroniConstant*Real.log (3/2)/2+0.0458-Real.log (3/2)^2/16 := by
    have hg1 := gamma_bounds.1
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hmass hc
  have ht' := mul_le_mul_of_nonneg_left hmoment hb
  have heq := hsF.tsum_eq
  change (∑' d, F d) = _ at heq
  have hfin := hlt.trans_le hsB.2
  dsimp [z] at hlog heq hm ht' hfin
  rw [hlog] at heq ht'
  nlinarith [heq, hm, ht', hfin]


/-- LEAF. (3.13) with the tail bound: `S_n(z, z^{-1}) Π_{p|n,p>2} (p-1)/(p-2) >
(16C)^{-1}(L² + 1.666 L - 6.52) - 2.61 x^{-1/4} (L²/16 + 0.238 L)`. Proof: `eq310` with
`Σ₄ = C^{-1}` (`hasSum_g`), `Σ₂ = Γ/C` (`hasSum_g_log`), `Σ₃ ≥ 0`, `Σ₁ = C^{-1} - Σ_{s(d)>z} g(d)`
(`split_sum`), `Γ < 0.535` (`gam_lt`), `gamma_bounds`, then `tail_le` with `C₀ < 2.35`
(`C0v_lt`) and `2.35 z^{-1/2} < 2.61 x^{-1/4}`. Vaughan 1977 p. 100 and 101, (3.13) and the
first display of p. 101. Unit U-1525. -/
theorem eq313 (x : ℝ) (hx : 10 ^ 9 ≤ x) (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    1 / (16 * Cv) * (Real.log x ^ 2 + 1.666 * Real.log x - 6.52)
      - 2.61 / x ^ (1 / 4 : ℝ) * (Real.log x ^ 2 / 16 + 0.238 * Real.log x)
      < Sn n (zz x) (zz x)⁻¹ * singQ n := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hℓ1 : (0.4054 : ℝ) ≤ Real.log (3/2) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  have hℓ2 : Real.log (3/2) ≤ (0.4055 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  obtain ⟨hγ1, hγ2⟩ := gamma_bounds
  have hG0 : 0 ≤ Gam := by
    apply tsum_nonneg
    intro p
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.1))) (sq_nonneg _)
  have hG1 := gam_lt
  have hCinv : 0 < 1 / Cv := by
    have hh := hasSum_g.summable.le_tsum 1 (fun _ _ => g_nonneg _)
    rw [hasSum_g.tsum_eq, g_one] at hh
    linarith
  have hC : 0 < Cv := (one_div_pos).mp hCinv
  have hnum : (Real.log x ^ 2 + 1.666 * Real.log x - 6.52) / 16 ≤
      Real.log x ^ 2 / 16 +
        (Real.eulerMascheroniConstant / 2 - Real.log (3/2) / 8 - Gam / 4) * Real.log x -
        (Real.eulerMascheroniConstant - Real.log (3/2) / 4) * Gam -
        (Real.eulerMascheroniConstant * Real.log (3/2) / 2 + 0.0458 - Real.log (3/2) ^ 2 / 16) := by
    have hcoef : 1.666 / 16 ≤ Real.eulerMascheroniConstant / 2 - Real.log (3/2) / 8 - Gam / 4 := by linarith
    have hγℓ : Real.eulerMascheroniConstant * Real.log (3/2) ≤ 0.57722 * 0.4055 :=
      mul_le_mul hγ2.le hℓ2 (by linarith) (by norm_num)
    have hγG : (Real.eulerMascheroniConstant - Real.log (3/2) / 4) * Gam ≤ (0.57722 - 0.4054 / 4) * 0.535 :=
      mul_le_mul (by linarith) hG1.le hG0 (by norm_num)
    have hℓsq : 0.4054 ^ 2 ≤ Real.log (3/2) ^ 2 := by nlinarith
    have hconst : (Real.eulerMascheroniConstant - Real.log (3/2) / 4) * Gam +
        Real.eulerMascheroniConstant * Real.log (3/2) / 2 + 0.0458 - Real.log (3/2) ^ 2 / 16 ≤ 6.52 / 16 := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hL]
  let t : ℝ := ∑' d, if zz x < (sk d : ℝ) then g d else 0
  have ht0 : 0 ≤ t := tsum_nonneg (fun d => by split_ifs; exact g_nonneg d; exact le_rfl)
  have ht : t ≤ 2.61 / x ^ (1/4 : ℝ) := by
    have hz0 : 0 < zz x := Real.sqrt_pos.mpr (by linarith)
    calc
      t ≤ C0v / Real.sqrt (zz x) := tail_le hz0
      _ ≤ 2.35 / Real.sqrt (zz x) := div_le_div_of_nonneg_right C0v_lt.le (Real.sqrt_nonneg _)
      _ ≤ 2.61 / x ^ (1/4 : ℝ) := by
        have h1 : 0.816 ≤ Real.sqrt (2/3) := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3), Real.sqrt_nonneg (2/3)]
        have h2 : 0.903 ≤ Real.sqrt (Real.sqrt (2/3)) := by
          nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (2/3)), Real.sqrt_nonneg (Real.sqrt (2/3))]
        have heq : Real.sqrt (Real.sqrt (2*x/3)) = Real.sqrt (Real.sqrt (2/3)) * x ^ (1/4 : ℝ) := by
          rw [show 2*x/3 = (2/3)*x by ring, Real.sqrt_mul (by norm_num),
            Real.sqrt_mul (Real.sqrt_nonneg _)]
          simp_rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul hx0.le]
          norm_num
        change 2.35 / Real.sqrt (Real.sqrt (2*x/3)) ≤ _
        rw [heq]
        have hp : 0 < x ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hx0 _
        rw [div_le_div_iff₀ (mul_pos (by linarith) hp) hp]
        nlinarith
  have hcoef : Real.eulerMascheroniConstant / 2 - Real.log (3/2) / 8 ≤ 0.238 := by linarith
  have hcoef0 : 0 ≤ Real.log x ^ 2 / 16 + 0.238 * Real.log x := by positivity
  have hsplit := split_sum (zz x)
  have hsum2 := hasSum_g_log.tsum_eq
  have hsum4 := hasSum_g.tsum_eq
  have hsum3 : 0 ≤ ∑' d, if (sk d : ℝ) ≤ zz x then g d * Real.log (sk d) ^ 2 else 0 := by
    apply tsum_nonneg
    intro d
    split_ifs
    · exact mul_nonneg (g_nonneg d) (sq_nonneg _)
    · exact le_rfl
  have heq := eq310 x hx n hn hn0
  rw [hsum2, hsum4] at heq
  have hmain := mul_le_mul_of_nonneg_left hnum hCinv.le
  have htail1 := mul_le_mul_of_nonneg_right hcoef hL
  have htail2 := mul_le_mul_of_nonneg_left htail1 ht0
  have htail3 := mul_le_mul_of_nonneg_right ht hcoef0
  have hA : (∑' d, if (sk d : ℝ) ≤ zz x then g d else 0) = 1/Cv - t := by
    linarith [hsplit]
  rw [hA] at heq
  have hidentity :
      1 / Cv * (Real.log x ^ 2 / 16 + (Real.eulerMascheroniConstant / 2 - Real.log (3/2) / 8 - Gam / 4) * Real.log x -
        (Real.eulerMascheroniConstant - Real.log (3/2) / 4) * Gam -
        (Real.eulerMascheroniConstant * Real.log (3/2) / 2 + 0.0458 - Real.log (3/2) ^ 2 / 16)) =
      1 / 16 * (1/Cv) * Real.log x ^ 2 +
        ((Real.eulerMascheroniConstant / 2 - Real.log (3/2) / 8) * (1/Cv) - (Gam/Cv)/4) * Real.log x -
        (Real.eulerMascheroniConstant - Real.log (3/2) / 4) * (Gam/Cv) -
        (Real.eulerMascheroniConstant * Real.log (3/2) / 2 + 0.0458 - Real.log (3/2)^2/16) * (1/Cv) := by ring
  rw [hidentity] at hmain
  have hiden2 : 1/Cv * ((Real.log x ^ 2 + 1.666 * Real.log x - 6.52)/16) =
      1/(16*Cv)*(Real.log x ^ 2 + 1.666 * Real.log x - 6.52) := by ring
  rw [hiden2] at hmain
  nlinarith

set_option maxHeartbeats 1000000 in
/-- LEAF. The closing numerics of Lemma 7, p. 101: for `x ≥ 10^9`, `0.6601 < c < 0.6602`,
`L = log x`, `K = 16c/((α(x) + L)L)`: `K > 2x^{-1/2}` and
`(K - 2x^{-1/2})^{-1} ≤ (16c)^{-1}(L² + 1.666L - 6.52) - 2.61 x^{-1/4}(L²/16 + 0.238L)`.
The paper's two ranges: `(0.033 - 0.02x^{-1/2}L³ - 0.2x^{-1/4}L)L > 0` for `x < 10^44`,
`(0.00015 - ...)L > 0` for `x ≥ 10^44`. Vaughan 1977 p. 101, proof of Lemma 7.
Unit U-1525. -/
theorem lemma7_numeric (x : ℝ) (hx : 10 ^ 9 ≤ x) (c : ℝ) (hc1 : 0.6601 < c) (hc2 : c < 0.6602) :
    0 < 16 * c / ((alpha x + Real.log x) * Real.log x) - 2 / Real.sqrt x ∧
    1 / (16 * c / ((alpha x + Real.log x) * Real.log x) - 2 / Real.sqrt x) ≤
      1 / (16 * c) * (Real.log x ^ 2 + 1.666 * Real.log x - 6.52)
        - 2.61 / x ^ (1 / 4 : ℝ) * (Real.log x ^ 2 / 16 + 0.238 * Real.log x) := by
  have algebra (L a c s t m : ℝ) (hL : 20.7 ≤ L) (hc1 : 0.6601 < c) (hc2 : c < 0.6602)
    (ha0 : 0 < a) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hA : L^2 + a*L ≤ 1.05*L^2)
    (hu : s*L^3 ≤ 0.282)
    (hm : 16*c*m*L ≤ (1.666-a)*L-6.52)
    (hmargin : 0 < m-0.02*(s*L^3)-0.2*(t*L)) :
    0 < 16*c/((a+L)*L)-2*s ∧
    1/(16*c/((a+L)*L)-2*s) ≤
      1/(16*c)*(L^2+1.666*L-6.52)-2.61*t*(L^2/16+0.238*L) := by
    let A := L^2+a*L
    have hL0 : 0 < L := by linarith
    have hc0 : 0 < c := by linarith
    have hA0 : 0 < A := by dsimp [A]; positivity
    have hsA : s*A ≤ 0.015 := by
      have h1 := mul_le_mul_of_nonneg_left hA hs0
      have h2 : s*L^2 ≤ 0.282/20.7 := by
        have h3 := mul_le_mul_of_nonneg_left hL (mul_nonneg hs0 (sq_nonneg L))
        nlinarith
      dsimp [A]
      nlinarith
    let D := 16*c-2*s*A
    have hD : 10.5 ≤ D := by dsimp [D]; linarith
    have hD0 : 0 < D := by linarith
    have heq : 16*c/((a+L)*L)-2*s = D/A := by
      dsimp [D, A]
      field_simp
      ring
    rw [heq]
    refine ⟨div_pos hD0 hA0, ?_⟩
    have hden : 2 * 1.05^2 ≤ 0.02*(16*c*D) := by
      nlinarith [mul_le_mul_of_nonneg_left hD (show 0 ≤ 16*c by positivity)]
    have hASq : A^2 ≤ 1.05^2*L^4 := by
      have hh := pow_le_pow_left₀ hA0.le hA 2
      dsimp [A] at *
      nlinarith [hh]
    have hpen : 2*s*A^2/(16*c*D) ≤ 0.02*s*L^4 := by
      rw [div_le_iff₀ (by positivity : 0 < 16*c*D)]
      have h1 := mul_le_mul_of_nonneg_left hASq (show 0 ≤ 2*s by positivity)
      have h2 := mul_le_mul_of_nonneg_right hden (show 0 ≤ s*L^4 by positivity)
      nlinarith
    have htail : 2.61*t*(L^2/16+0.238*L) ≤ 0.2*t*L^2 := by
      have h1 : 2.61*(L^2/16+0.238*L) ≤ 0.2*L^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 ht0]
    have hinv : 1/(D/A) = A/(16*c)+2*s*A^2/(16*c*D) := by
      field_simp [hD0.ne', hA0.ne', hc0.ne']
      dsimp [D]
      ring
    have hmain : A/(16*c)+m*L ≤ 1/(16*c)*(L^2+1.666*L-6.52) := by
      calc
        _ = (A+16*c*m*L)/(16*c) := by field_simp
        _ ≤ (L^2+1.666*L-6.52)/(16*c) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          dsimp [A]
          nlinarith
        _ = _ := by ring
    rw [hinv]
    have hmL := mul_pos hmargin hL0
    nlinarith
  have small_decay (x : ℝ) (hx : (10 : ℝ)^9 ≤ x) :
    (1 / Real.sqrt x) * Real.log x ^ 3 ≤ 0.282 ∧
    (1 / x^(1/4 : ℝ))*Real.log x ≤ 0.117 := by
    have hx0 : 0 < x := by linarith
    have hloglo : (2.30258 : ℝ) < Real.log 10 := by
      rw [Real.log_ten_eq]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hloghi : Real.log 10 < (2.30259 : ℝ) := by
      rw [Real.log_ten_eq]
      linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    have ha6 : Real.exp ((1/6 : ℝ)⁻¹) ≤ (10 : ℝ)^9 := by
      rw [← Real.le_log_iff_exp_le (by positivity)]
      rw [Real.log_pow]
      norm_num
      linarith
    have ha4 : Real.exp ((1/4 : ℝ)⁻¹) ≤ (10 : ℝ)^9 := by
      rw [← Real.le_log_iff_exp_le (by positivity)]
      rw [Real.log_pow]
      norm_num
      linarith
    have hm6 := Real.log_div_self_rpow_antitoneOn (a := (1/6 : ℝ)) (by norm_num)
      ha6 (ha6.trans hx) hx
    have hm4 := Real.log_div_self_rpow_antitoneOn (a := (1/4 : ℝ)) (by norm_num)
      ha4 (ha4.trans hx) hx
    have hr6 : (31.62 : ℝ) ≤ ((10 : ℝ)^9)^(1/6 : ℝ) := by
      rw [show (1/6 : ℝ) = (6 : ℝ)⁻¹ by norm_num,
        Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
      norm_num
    have hr4 : (177.8 : ℝ) ≤ ((10 : ℝ)^9)^(1/4 : ℝ) := by
      rw [show (1/4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
      norm_num
    have h6 : Real.log x / x^(1/6 : ℝ) ≤ 0.6555 := by
      apply hm6.trans
      rw [div_le_iff₀ (by positivity : 0 < ((10 : ℝ)^9)^(1/6 : ℝ)), Real.log_pow]
      nlinarith
    have h4 : Real.log x / x^(1/4 : ℝ) ≤ 0.117 := by
      apply hm4.trans
      rw [div_le_iff₀ (by positivity : 0 < ((10 : ℝ)^9)^(1/4 : ℝ)), Real.log_pow]
      nlinarith
    refine ⟨?_, by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h4⟩
    have h6pow := pow_le_pow_left₀ (show 0 ≤ Real.log x / x^(1/6 : ℝ) by apply div_nonneg; exact Real.log_nonneg (by linarith); positivity) h6 3
    have heq : (x^(1/6 : ℝ))^3 = Real.sqrt x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
      norm_num
    rw [div_pow, heq] at h6pow
    nlinarith [show (1/Real.sqrt x)*Real.log x^3 = Real.log x^3/Real.sqrt x by ring]
  have large_decay (x : ℝ) (hx : (10 : ℝ)^24 ≤ x) :
    (1 / Real.sqrt x) * Real.log x ^ 3 ≤ 0.001 ∧
    (1 / x^(1/4 : ℝ))*Real.log x ≤ 0.0001 := by
    have hx0 : 0 < x := by linarith
    have hloglo : (2.30258 : ℝ) < Real.log 10 := by
      rw [Real.log_ten_eq]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hloghi : Real.log 10 < (2.30259 : ℝ) := by
      rw [Real.log_ten_eq]
      linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    have ha6 : Real.exp ((1/6 : ℝ)⁻¹) ≤ (10 : ℝ)^24 := by
      rw [← Real.le_log_iff_exp_le (by positivity)]
      rw [Real.log_pow]
      norm_num
      linarith
    have ha4 : Real.exp ((1/4 : ℝ)⁻¹) ≤ (10 : ℝ)^24 := by
      rw [← Real.le_log_iff_exp_le (by positivity)]
      rw [Real.log_pow]
      norm_num
      linarith
    have hm6 := Real.log_div_self_rpow_antitoneOn (a := (1/6 : ℝ)) (by norm_num)
      ha6 (ha6.trans hx) hx
    have hm4 := Real.log_div_self_rpow_antitoneOn (a := (1/4 : ℝ)) (by norm_num)
      ha4 (ha4.trans hx) hx
    have hr6 : (1000 : ℝ) ≤ ((10 : ℝ)^24)^(1/6 : ℝ) := by
      rw [show (1/6 : ℝ) = (6 : ℝ)⁻¹ by norm_num,
        Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
      norm_num
    have hr4 : (1000000 : ℝ) ≤ ((10 : ℝ)^24)^(1/4 : ℝ) := by
      rw [show (1/4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
      norm_num
    have h6 : Real.log x / x^(1/6 : ℝ) ≤ 0.1 := by
      apply hm6.trans
      rw [div_le_iff₀ (by positivity : 0 < ((10 : ℝ)^24)^(1/6 : ℝ)), Real.log_pow]
      nlinarith
    have h4 : Real.log x / x^(1/4 : ℝ) ≤ 0.0001 := by
      apply hm4.trans
      rw [div_le_iff₀ (by positivity : 0 < ((10 : ℝ)^24)^(1/4 : ℝ)), Real.log_pow]
      nlinarith
    refine ⟨?_, by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h4⟩
    have h6pow := pow_le_pow_left₀ (show 0 ≤ Real.log x / x^(1/6 : ℝ) by apply div_nonneg; exact Real.log_nonneg (by linarith); positivity) h6 3
    have heq : (x^(1/6 : ℝ))^3 = Real.sqrt x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
      norm_num
    rw [div_pow, heq] at h6pow
    nlinarith [show (1/Real.sqrt x)*Real.log x^3 = Real.log x^3/Real.sqrt x by ring]
  have hloglo : (2.30258 : ℝ) < Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hL : 20.7 ≤ Real.log x := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 10^9) hx
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨hu, hv⟩ := small_decay x hx
  by_cases hxx : x < 10^44
  · have hm : 16*c*0.033*Real.log x ≤ (1.666-1)*Real.log x-6.52 := by
      nlinarith [mul_lt_mul_of_pos_right hc2 hL0]
    have hh := algebra (Real.log x) 1 c (1/Real.sqrt x) (1/x^(1/4 : ℝ)) 0.033
      hL hc1 hc2 (by norm_num) (by positivity) (by positivity)
      (by nlinarith) hu hm (by nlinarith)
    simp only [alpha, hxx, ite_true]
    convert hh using 1 <;> ring
  · have hx44 : (10 : ℝ)^44 ≤ x := le_of_not_gt hxx
    have hL44 : 101.3 ≤ Real.log x := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 10^44) hx44
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith
    obtain ⟨hu44, hv44⟩ := large_decay x (by nlinarith : (10 : ℝ)^24 ≤ x)
    have hm : 16*c*0.00015*Real.log x ≤ (1.666-1.6)*Real.log x-6.52 := by
      nlinarith [mul_lt_mul_of_pos_right hc2 hL0]
    have hh := algebra (Real.log x) 1.6 c (1/Real.sqrt x) (1/x^(1/4 : ℝ)) 0.00015
      hL hc1 hc2 (by norm_num) (by positivity) (by positivity)
      (by nlinarith) hu hm (by nlinarith)
    simp only [alpha, hxx, ite_false]
    convert hh using 1 <;> ring


/-! ### Assemblies: Lemma 7 and Lemma 8 -/

theorem singQ_ge_one (n : ℕ) : 1 ≤ singQ n := by
  unfold singQ
  apply Finset.one_le_prod₀
  intro p hp
  rw [Finset.mem_filter] at hp
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
  rw [one_le_div (by linarith)]; linarith

/-- **Lemma 7, (3.9), PROVED from `eq313` and `lemma7_numeric`, CONDITIONAL ON
0.6601 < C < 0.6602**: `S_n(z, z^{-1})^{-1} < 16C/((α(x) + log x) log x) Π_{p|n,p>2} (p-1)/(p-2)
- 2x^{-1/2}`. Vaughan 1977 p. 100, Lemma 7. -/
theorem lemma7_of (hC : 0.6601 < Cv ∧ Cv < 0.6602) (x : ℝ) (hx : 10 ^ 9 ≤ x) (n : ℕ)
    (hn : Even n) (hn0 : 0 < n) :
    0 < Sn n (zz x) (zz x)⁻¹ ∧
    (Sn n (zz x) (zz x)⁻¹)⁻¹ <
      16 * Cv / ((alpha x + Real.log x) * Real.log x) * singQ n - 2 / Real.sqrt x := by
  obtain ⟨hK, hV⟩ := lemma7_numeric x hx Cv hC.1 hC.2
  have h13 := eq313 x hx n hn hn0
  set K := 16 * Cv / ((alpha x + Real.log x) * Real.log x) with hKdef
  set e := 2 / Real.sqrt x with he
  set S := Sn n (zz x) (zz x)⁻¹
  set P := singQ n
  have hP : 1 ≤ P := singQ_ge_one n
  have he0 : 0 ≤ e := by positivity
  have hpos : 0 < 1 / (K - e) := by positivity
  have hSP : 1 / (K - e) < S * P := by linarith
  have hSP0 : 0 < S * P := lt_trans hpos hSP
  have hS : 0 < S := by
    by_contra hneg
    have hneg : S ≤ 0 := le_of_not_gt hneg
    have : S * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    linarith
  refine ⟨hS, ?_⟩
  -- 1/(SP) < K - e
  have h1 : 1 / (S * P) < K - e := by
    rw [div_lt_iff₀ hSP0]
    rw [div_lt_iff₀ hK] at hSP
    nlinarith
  have h2 : S⁻¹ = P * (1 / (S * P)) := by field_simp
  rw [h2]
  have : P * (1 / (S * P)) < P * (K - e) := mul_lt_mul_of_pos_left h1 (by linarith)
  nlinarith

/-- **Lemma 8, PROVED from `reduction`, `sifted_le` and `lemma7_of`, CONDITIONAL ON
0.6601 < C < 0.6602** (PROVED in the lab for `twinC`, the same expression as `Cv`): for
`x ≥ 10^9`, `h` even with `h < 0` or `h > x`,
`R(h, x) < 16 C x/((α(x) + log x) log x) Π_{p | h, p > 2} (p-1)/(p-2)`. Vaughan 1977 p. 101,
Lemma 8. -/
theorem lemma8_of (hC : 0.6601 < Cv ∧ Cv < 0.6602) (x : ℝ) (hx : 10 ^ 9 ≤ x) (h : ℤ)
    (he : Even h) (hh : h < 0 ∨ x < h) :
    (Rc h x : ℝ) < 16 * Cv * x / ((alpha x + Real.log x) * Real.log x) * singQ h.natAbs := by
  have hx0 : 0 < x := by linarith
  have hh0 : h ≠ 0 := by
    rintro rfl
    rcases hh with h1 | h1
    · exact lt_irrefl _ h1
    · have : (0 : ℝ) < x := hx0
      push_cast at h1; linarith
  have hn : Even h.natAbs := Int.natAbs_even.mpr he
  have hn0 : 0 < h.natAbs := Int.natAbs_pos.mpr hh0
  obtain ⟨hS, h7⟩ := lemma7_of hC x hx h.natAbs hn hn0
  have hred := reduction x (by linarith) h hh
  have hsf := sifted_le x (by linarith) h he
  set S := Sn h.natAbs (zz x) (zz x)⁻¹
  set c := ((sifted h x).card : ℝ)
  set K := 16 * Cv / ((alpha x + Real.log x) * Real.log x)
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsq2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  -- c ≤ x / S < x (K P - 2/√x)
  have hc : c ≤ x * S⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hS]; exact hsf
  have hc2 : x * S⁻¹ < x * (K * singQ h.natAbs - 2 / Real.sqrt x) :=
    mul_lt_mul_of_pos_left h7 hx0
  have hxe : x * (2 / Real.sqrt x) = 2 * Real.sqrt x := by
    field_simp; nlinarith
  have : 16 * Cv * x / ((alpha x + Real.log x) * Real.log x) * singQ h.natAbs
      = x * (K * singQ h.natAbs) := by simp only [K]; ring
  rw [this]
  have : x * (K * singQ h.natAbs - 2 / Real.sqrt x) = x * (K * singQ h.natAbs) - 2 * Real.sqrt x := by
    rw [mul_sub, hxe]
  linarith

/-! ### Vacuity -/

/-- Vacuity for `mv_cor1`: its hypotheses hold for `S = {1}`, `M = 0`, `N = 1`, `Q = 1`, no
excluded classes. -/
example : ∃ (S : Finset ℕ) (Ω : ℕ → Finset ℕ), S ⊆ Ioc 0 (0 + 1) ∧ S.Nonempty ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1 → (∀ w ∈ Ω p, w < p) ∧ (Ω p).card < p ∧
      ∀ s ∈ S, s % p ∉ Ω p :=
  ⟨{1}, fun _ => ∅, by decide, ⟨1, by simp⟩, fun p hp _ => ⟨by simp, by simp [hp.pos], by simp⟩⟩

/-- Vacuity for `lemma8_of`: `x = 10^9`, `h = -2` meet its hypotheses on `x` and `h`. -/
example : (10 : ℝ) ^ 9 ≤ 10 ^ 9 ∧ Even (-2 : ℤ) ∧ ((-2 : ℤ) < 0 ∨ (10 : ℝ) ^ 9 < ((-2 : ℤ) : ℝ)) :=
  ⟨le_rfl, ⟨-1, by norm_num⟩, Or.inl (by norm_num)⟩

/-- Concrete hypotheses for the finite range and the Abel helpers. -/
example : 1 ≤ (1 : ℝ) ∧ (1 : ℝ) < 42 := by norm_num

/-- Concrete hypotheses for the two numeric ranges. -/
example : (10 : ℝ)^9 ≤ 10^9 ∧ (0.6601 : ℝ) < 0.66015 ∧ (0.66015 : ℝ) < 0.6602 := by norm_num

end LeanLab.SchnirelmannBounds.Decomp1525b
