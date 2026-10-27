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
  sorry

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
  sorry

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

/-- LEAF. Lemma 5: for `z ≥ 1`,
`Σ_{r ≤ z} τ₁(r)/r > (1/4) log² z + (γ + (1/2) log 2) log z + 0.1833`. Vaughan 1977 p. 98 and
99, Lemma 5, via (3.6), (3.7) and Euler-Maclaurin for `z ≥ 42`, direct check below 42; the
margin is small, about `10^{-4}`, near some integers. Unit U-1525. -/
theorem lemma5 (z : ℝ) (hz : 1 ≤ z) :
    1 / 4 * Real.log z ^ 2 + (Real.eulerMascheroniConstant + 1 / 2 * Real.log 2) * Real.log z
      + 0.1833 < ∑ r ∈ Icc 1 ⌊z⌋₊, (tau1 r : ℝ) / r := by
  sorry

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
  sorry

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
