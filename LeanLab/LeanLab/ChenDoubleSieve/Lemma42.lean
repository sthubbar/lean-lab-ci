import LeanLab.ChenDoubleSieve.Lemma41
import LeanLab.ChenDoubleSieve.Lemma42Comb
import LeanLab.ChenDoubleSieve.Lemma42Arith

/-!
# Wu 2004 Lemma 4.2, the 21 term weighted inequality, exact pointwise form

P0036 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114, 2004, arXiv 0705.1652, Section 4, Lemma 4.2.
Unit U-5402, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

Thresholds `w ≤ k₁ ≤ k₂ ≤ k₃ ≤ z` stand for Wu's `d̲^{1/s'} ≤ d̲^{1/κ₁} ≤ d̲^{1/κ₂} ≤ d̲^{1/κ₃}
≤ d̲^{1/s}`. Each `Γᵢ`, `i ≥ 2`, is a sum over `p₁ < ⋯ < p_k` of primes of `[w, z)` coprime to `N`
with `lo j ≤ p_j < hi j`, exactly Wu's ranges, of `S(A_{d p₁⋯p_k}; P(d p₁⋯p_k N), y)`.

READING. Wu prints `P(dN)` in every `Γᵢ`. With his definition of `S` in Section 2,
`S(A; P, z) = #{a ∈ A : (a, P(z)) = 1}`, a term `S(A_{dp₁p₂p₃}; P(dN), p₂)` with `p₁ < p₂`
is `0` unless `p₁ ∣ d`, since then `p₁ ∈ P(dN)` divides every element of `A_{dp₁p₂p₃}`; Lemma 4.1 writes
`P(dp₁N)` for the same reason. We read `P(dN)` as `P(d p₁⋯p_k N)`, which changes nothing for
`Γ₁` to `Γ₈`, whose sifting level is at most `p₁`. `literal_zero` proves the degenerate reading
vanishes; the Python check `wu42.py` finds the literal reading fails pointwise on 532 of the
patterns of at most 10 primes, the intended one on none.

`lemma42_exact`: for every finite `A`, `d`, `N` and `w ≤ k₁ ≤ k₂ ≤ k₃ ≤ z`,
`5 S(A_d; P(dN), z) + Γ₂ + Γ₃ + Γ₄ ≤ Γ₁ + Γ₅ + ⋯ + Γ₂₁ + 3E`, `E` the `p ∣ d` terms of
Lemma 4.1, with no `O(N^{1-η})`. Numerically, not proved in Lean, the inequality is tight and
none of `Γ₅` to `Γ₂₁` can be dropped, `numerics/wu42n.py`.
Binary Goldbach is OPEN; this is one combinatorial step of Wu's upper bound sieve.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu42

open Wu41 (Sifted S PS mem_PS S_eq_sum sifted_mono coprime_of_prime_not_dvd Err)

/-- Tuples `p₁ < ⋯ < p_k` of primes of `[w, z)` coprime to `N`, with `lo j ≤ p_j < hi j`. -/
def tuples (N k : ℕ) (w z : ℝ) (lo hi : Fin k → ℝ) : Finset (Fin k → ℕ) :=
  {p ∈ Fintype.piFinset (fun _ : Fin k => PS N w z) |
    StrictMono p ∧ ∀ j, lo j ≤ ((p j : ℕ) : ℝ) ∧ ((p j : ℕ) : ℝ) < hi j}

/-- `Σ_{p₁ < ⋯ < p_k} S(A_{d p₁⋯p_k}; P(d p₁⋯p_k N), y(p))`. -/
def G (A : Finset ℕ) (d N k : ℕ) (w z : ℝ) (lo hi : Fin k → ℝ) (y : (Fin k → ℕ) → ℝ) : ℕ :=
  ∑ p ∈ tuples N k w z lo hi, S A (d * ∏ j, p j) (d * (∏ j, p j) * N) (y p)

/-- Sifting level `p_m` for a tuple `p₁ < ⋯ < p_{m+1}`, the second largest prime. -/
def yPrev (m : ℕ) (p : Fin (m + 1) → ℕ) : ℝ := ((p ⟨m - 1, by omega⟩ : ℕ) : ℝ)

section Gammas
variable (A : Finset ℕ) (d N : ℕ) (w k₁ k₂ k₃ z : ℝ)

/-- `Γ₁ = 4 S(A_d; P(dN), d̲^{1/s'}) + S(A_d; P(dN), d̲^{1/κ₁})`. -/
def Γ₁ : ℕ := 4 * S A d (d * N) w + S A d (d * N) k₁
/-- `Γ₂ = Σ_{w ≤ p < z} S(A_{dp}; P(dN), w)`. -/
def Γ₂ : ℕ := G A d N 1 w z ![w] ![z] fun _ => w
/-- `Γ₃ = Σ_{w ≤ p < k₂} S(A_{dp}; P(dN), w)`. -/
def Γ₃ : ℕ := G A d N 1 w z ![w] ![k₂] fun _ => w
/-- `Γ₄ = Σ_{w ≤ p < k₃} S(A_{dp}; P(dN), w)`. -/
def Γ₄ : ℕ := G A d N 1 w z ![w] ![k₃] fun _ => w
/-- `Γ₅ = Σ_{w ≤ p₁ < p₂ < k₂} S(A_{dp₁p₂}; P(dN), w)`. -/
def Γ₅ : ℕ := G A d N 2 w z ![w, w] ![k₂, k₂] fun _ => w
/-- `Γ₆ = Σ_{w ≤ p₁ < k₁, k₂ ≤ p₂ < k₃} S(A_{dp₁p₂}; P(dN), w)`. -/
def Γ₆ : ℕ := G A d N 2 w z ![w, k₂] ![k₁, k₃] fun _ => w
/-- `Γ₇ = Σ_{w ≤ p₁ < p₂ < k₁} S(A_{dp₁p₂}; P(dN), p₁)`. -/
def Γ₇ : ℕ := G A d N 2 w z ![w, w] ![k₁, k₁] (yPrev 1)
/-- `Γ₈ = Σ_{w ≤ p₁ < k₁ ≤ p₂ < k₂} S(A_{dp₁p₂}; P(dN), p₁)`. -/
def Γ₈ : ℕ := G A d N 2 w z ![w, k₁] ![k₁, k₂] (yPrev 1)
/-- `Γ₉ = Σ_{k₁ ≤ p₁ < p₂ < p₃ < k₃} S(A_{dp₁p₂p₃}; P(dp₁N), p₂)`. -/
def Γ₉ : ℕ := G A d N 3 w z ![k₁, k₁, k₁] ![k₃, k₃, k₃] (yPrev 2)
/-- `Γ₁₀ = Σ_{k₁ ≤ p₁ < p₂ < k₂ ≤ p₃ < z}`, level `p₂`. -/
def Γ₁₀ : ℕ := G A d N 3 w z ![k₁, k₁, k₂] ![k₂, k₂, z] (yPrev 2)
/-- `Γ₁₁ = Σ_{k₁ ≤ p₁ < k₂ ≤ p₂ < p₃ < k₃}`, level `p₂`. -/
def Γ₁₁ : ℕ := G A d N 3 w z ![k₁, k₂, k₂] ![k₂, k₃, k₃] (yPrev 2)
/-- `Γ₁₂ = Σ_{w ≤ p₁ < p₂ < k₁, k₃ ≤ p₃ < z}`, level `p₂`. -/
def Γ₁₂ : ℕ := G A d N 3 w z ![w, w, k₃] ![k₁, k₁, z] (yPrev 2)
/-- `Γ₁₃ = Σ_{w ≤ p₁ < k₁ ≤ p₂ < k₂ ≤ p₃ < z}`, level `p₂`. -/
def Γ₁₃ : ℕ := G A d N 3 w z ![w, k₁, k₂] ![k₁, k₂, z] (yPrev 2)
/-- `Γ₁₄ = Σ_{w ≤ p₁ < k₁, k₂ ≤ p₂ < p₃ < z}`, level `p₂`. -/
def Γ₁₄ : ℕ := G A d N 3 w z ![w, k₂, k₂] ![k₁, z, z] (yPrev 2)
/-- `Γ₁₅ = Σ_{k₁ ≤ p₁ < k₂ ≤ p₂ < k₃ ≤ p₃ < z}`, level `p₂`. -/
def Γ₁₅ : ℕ := G A d N 3 w z ![k₁, k₂, k₃] ![k₂, k₃, z] (yPrev 2)
/-- `Γ₁₆ = Σ_{k₂ ≤ p₁ < ⋯ < p₄ < k₃}`, level `p₃`. -/
def Γ₁₆ : ℕ := G A d N 4 w z ![k₂, k₂, k₂, k₂] ![k₃, k₃, k₃, k₃] (yPrev 3)
/-- `Γ₁₇ = Σ_{k₂ ≤ p₁ < p₂ < p₃ < k₃ ≤ p₄ < z}`, level `p₃`. -/
def Γ₁₇ : ℕ := G A d N 4 w z ![k₂, k₂, k₂, k₃] ![k₃, k₃, k₃, z] (yPrev 3)
/-- `Γ₁₈ = Σ_{k₂ ≤ p₁ < p₂ < k₃ ≤ p₃ < p₄ < z}`, level `p₃`. -/
def Γ₁₈ : ℕ := G A d N 4 w z ![k₂, k₂, k₃, k₃] ![k₃, k₃, z, z] (yPrev 3)
/-- `Γ₁₉ = Σ_{k₁ ≤ p₁ < k₂, k₃ ≤ p₂ < p₃ < p₄ < z}`, level `p₃`. -/
def Γ₁₉ : ℕ := G A d N 4 w z ![k₁, k₃, k₃, k₃] ![k₂, z, z, z] (yPrev 3)
/-- `Γ₂₀ = Σ_{k₂ ≤ p₁ < k₃ ≤ p₂ < ⋯ < p₅ < z}`, level `p₄`. -/
def Γ₂₀ : ℕ := G A d N 5 w z ![k₂, k₃, k₃, k₃, k₃] ![k₃, z, z, z, z] (yPrev 4)
/-- `Γ₂₁ = Σ_{k₃ ≤ p₁ < ⋯ < p₆ < z}`, level `p₅`. -/
def Γ₂₁ : ℕ := G A d N 6 w z (fun _ => k₃) (fun _ => z) (yPrev 5)

end Gammas

/-! ## The literal reading is degenerate -/

/-- With `P(dN)` as printed, a term sifted at `p₂` over `A_{d p₁ p₂ ⋯}`, `p₁ < p₂`, `p₁ ∤ dN`,
is `0`: every element of `A_{d p₁ ⋯}` has the prime factor `p₁ < p₂` from `P(dN)`. -/
theorem literal_zero (A : Finset ℕ) (d N m : ℕ) {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (h12 : p₁ < p₂)
    (hp₁dN : ¬ p₁ ∣ d * N) (hm : p₁ ∣ m) : S A (d * m) (d * N) p₂ = 0 := by
  unfold S
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro a - ⟨hda, hs⟩
  exact hs p₁ hp₁ (by exact_mod_cast h12) hp₁dN (dvd_trans (dvd_trans hm (dvd_mul_left m d)) hda)

/-! ## From sieve terms to counting -/

/-- The pointwise count of a tuple sum. -/
def cnt (d N : ℕ) (w z : ℝ) (a k : ℕ) (lo hi : Fin k → ℝ) (y : (Fin k → ℕ) → ℝ) : ℕ :=
  #{p ∈ tuples N k w z lo hi | d * ∏ j, p j ∣ a ∧ Sifted (d * (∏ j, p j) * N) (y p) a}

lemma G_eq (A : Finset ℕ) (d N k : ℕ) (w z : ℝ) (lo hi : Fin k → ℝ) (y : (Fin k → ℕ) → ℝ) :
    G A d N k w z lo hi y = ∑ a ∈ A, cnt d N w z a k lo hi y := by
  unfold G cnt
  simp only [S_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [card_filter]

/-- `R(a)`: the primes of `[w, z)` coprime to `dN` dividing `a`. -/
def Rset (d N : ℕ) (w z : ℝ) (a : ℕ) : Finset ℕ := {q ∈ PS N w z | ¬ q ∣ d ∧ q ∣ a}

lemma mem_Rset {d N : ℕ} {w z : ℝ} {a q : ℕ} :
    q ∈ Rset d N w z a ↔ q ∈ PS N w z ∧ ¬ q ∣ d ∧ q ∣ a := by
  unfold Rset; rw [mem_filter]

/-- A tuple of distinct primes of `R(a)` containing every prime of `R(a)` below the level
gives a counted term. -/
lemma valid_of {d N a : ℕ} {w z : ℝ} (hd : d ∣ a) (hw : Sifted (d * N) w a) {k : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hR : ∀ j, p j ∈ Rset d N w z a) {y : ℝ}
    (hyz : y ≤ z) (hs : ∀ q ∈ Rset d N w z a, (q : ℝ) < y → ∃ j, p j = q) :
    d * ∏ j, p j ∣ a ∧ Sifted (d * (∏ j, p j) * N) y a := by
  have hpr : ∀ j, (p j).Prime := fun j => (mem_PS.1 (mem_Rset.1 (hR j)).1).1
  refine ⟨?_, ?_⟩
  · have himg : ∏ j, p j = ∏ q ∈ univ.image p, q := by
      rw [prod_image (fun x _ y _ h => hp h)]
    have hdvd : ∏ j, p j ∣ a := by
      rw [himg]
      refine Finset.prod_primes_dvd a (fun q hq => ?_) (fun q hq => ?_)
      · obtain ⟨j, -, rfl⟩ := mem_image.1 hq; exact (hpr j).prime
      · obtain ⟨j, -, rfl⟩ := mem_image.1 hq; exact (mem_Rset.1 (hR j)).2.2
    have hcop : d.Coprime (∏ j, p j) :=
      Nat.Coprime.prod_right fun j _ => coprime_of_prime_not_dvd (hpr j) (mem_Rset.1 (hR j)).2.1
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hd hdvd
  · intro q hq hqy hqD hqa
    have hqdN : ¬ q ∣ d * N := fun h => hqD (dvd_trans h (mul_dvd_mul_right (dvd_mul_right _ _) N))
    by_cases hqw : (q : ℝ) < w
    · exact hw q hq hqw hqdN hqa
    · push Not at hqw
      have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2
        (fun h => hqdN (dvd_mul_of_dvd_right h d))
      have hqd : ¬ q ∣ d := fun h => hqdN (dvd_mul_of_dvd_left h N)
      have hqR : q ∈ Rset d N w z a :=
        mem_Rset.2 ⟨mem_PS.2 ⟨hq, hqw, lt_of_lt_of_le hqy hyz, hqN⟩, hqd, hqa⟩
      obtain ⟨j, rfl⟩ := hs q hqR hqy
      exact hqD (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_prod_of_mem p (mem_univ j)) d) N)

lemma Rset_ge {d N : ℕ} {w z : ℝ} {a q : ℕ} (h : q ∈ Rset d N w z a) : w ≤ (q : ℝ) :=
  (mem_PS.1 (mem_Rset.1 h).1).2.1

lemma Rset_lt {d N : ℕ} {w z : ℝ} {a q : ℕ} (h : q ∈ Rset d N w z a) : (q : ℝ) < z :=
  (mem_PS.1 (mem_Rset.1 h).1).2.2.1

lemma Nc_w (d N : ℕ) (w z : ℝ) (a : ℕ) : Nc (Rset d N w z a) w = 0 := by
  unfold Nc; rw [card_eq_zero, filter_eq_empty_iff]
  intro q hq h; exact absurd (Rset_ge hq) (not_le.2 h)

lemma Nc_z (d N : ℕ) (w z : ℝ) (a : ℕ) : Nc (Rset d N w z a) z = #(Rset d N w z a) := by
  unfold Nc; rw [filter_true_of_mem fun q hq => Rset_lt hq]

/-! ## The smallest-prefix lower bound, for `Γ₇` to `Γ₂₁` -/

/-- If the `m` smallest primes of `R(a)` satisfy the first `m` range conditions, the tuples
made of them and one more prime of `R(a)` in the last range are all counted. -/
theorem prefix_bound {d N a : ℕ} {w z : ℝ} (hd : d ∣ a) (hw : Sifted (d * N) w a)
    (m : ℕ) (hm : 1 ≤ m) (lo hi : Fin (m + 1) → ℝ)
    (hpre : ∀ j : Fin m, Nc (Rset d N w z a) (lo j.castSucc) ≤ j ∧
      (j : ℕ) < Nc (Rset d N w z a) (hi j.castSucc)) :
    Nc (Rset d N w z a) (hi (Fin.last m)) - max m (Nc (Rset d N w z a) (lo (Fin.last m))) ≤
      cnt d N w z a (m + 1) lo hi (yPrev m) := by
  set R := Rset d N w z a with hRdef
  have hmR : m ≤ #R := by
    have h1 := (hpre ⟨m - 1, by omega⟩).2
    have h2 := Nc_le_card R (hi (Fin.castSucc ⟨m - 1, by omega⟩))
    have : m - 1 < #R := lt_of_lt_of_le h1 h2
    omega
  set e := ord R
  let f : ℕ → Fin (m + 1) → ℕ := fun x j =>
    if h : (j : ℕ) < m then e ⟨j, by omega⟩ else x
  have hf_last : ∀ x, f x (Fin.last m) = x := by intro x; simp [f]
  have hf_lt : ∀ x (j : Fin (m + 1)) (h : (j : ℕ) < m), f x j = e ⟨j, by omega⟩ := by
    intro x j h; simp [f, h]
  have hpre' : ∀ (j : Fin (m + 1)) (h : (j : ℕ) < m),
      lo j ≤ ((e ⟨j, by omega⟩ : ℕ) : ℝ) ∧ ((e ⟨j, by omega⟩ : ℕ) : ℝ) < hi j := by
    intro j h
    have hj : Fin.castSucc (⟨j, h⟩ : Fin m) = j := Fin.ext rfl
    obtain ⟨h1, h2⟩ := hpre ⟨j, h⟩
    rw [hj] at h1 h2
    exact ⟨(le_ord_iff R ⟨j, by omega⟩ _).2 h1, (ord_lt_iff R ⟨j, by omega⟩ _).2 h2⟩
  have hjlast : ∀ j : Fin (m + 1), ¬ (j : ℕ) < m → j = Fin.last m := by
    intro j h; exact Fin.ext (by rw [Fin.val_last]; omega)
  set tail := ({x ∈ R | e ⟨m - 1, by omega⟩ < x ∧ lo (Fin.last m) ≤ ((x : ℕ) : ℝ) ∧
    ((x : ℕ) : ℝ) < hi (Fin.last m)} : Finset ℕ)
  have hsub : tail.image f ⊆
      {p ∈ tuples N (m + 1) w z lo hi | d * ∏ j, p j ∣ a ∧
        Sifted (d * (∏ j, p j) * N) (yPrev m p) a} := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
    obtain ⟨hxR, hxe, hxlo, hxhi⟩ := mem_filter.1 hx
    have hval : ∀ j, f x j ∈ R := by
      intro j
      by_cases h : (j : ℕ) < m
      · rw [hf_lt x j h]; exact R.orderEmbOfFin_mem rfl _
      · rw [hjlast j h, hf_last]; exact hxR
    have hmono : StrictMono (f x) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      by_cases hj : (j : ℕ) < m
      · rw [hf_lt x i (by omega), hf_lt x j hj]
        exact e.strictMono (Fin.mk_lt_mk.2 (by omega))
      · rw [hjlast j hj, hf_last]
        have hi' : (i : ℕ) < m := by have := j.2; omega
        rw [hf_lt x i hi']
        exact lt_of_le_of_lt (e.monotone (Fin.mk_le_mk.2 (by omega))) hxe
    have hyv : yPrev m (f x) = ((e ⟨m - 1, by omega⟩ : ℕ) : ℝ) := by
      unfold yPrev; rw [hf_lt x _ (by show m - 1 < m; omega)]
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · unfold tuples
      rw [mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => (mem_Rset.1 (hval j)).1, hmono, fun j => ?_⟩
      by_cases h : (j : ℕ) < m
      · rw [hf_lt x j h]; exact hpre' j h
      · rw [hjlast j h, hf_last]; exact ⟨hxlo, hxhi⟩
    · rw [hyv]
      refine valid_of hd hw (f x) hmono.injective hval
        (Rset_lt (R.orderEmbOfFin_mem rfl _)).le ?_
      intro q hq hqy
      obtain ⟨i, rfl⟩ := (mem_iff_exists R q).1 hq
      have hi : (i : ℕ) < m - 1 :=
        Fin.lt_iff_val_lt_val.1 ((e.lt_iff_lt).1 (by exact_mod_cast hqy : e i < e ⟨m - 1, by omega⟩))
      exact ⟨⟨i, by omega⟩, by rw [hf_lt x _ (by show (i : ℕ) < m; omega)]⟩
  have hinj : Set.InjOn f tail := by
    intro x _ y _ h
    have := congrFun h (Fin.last m)
    rwa [hf_last, hf_last] at this
  have := card_le_card hsub
  rw [card_image_of_injOn hinj] at this
  exact (tail_count R m hm hmR _ _).trans this

/-! ## `Γ₅`, `Γ₆` and the single-prime terms -/

lemma pair_mem {N : ℕ} {w z : ℝ} {lo hi : Fin 2 → ℝ} {x y : ℕ} (hx : x ∈ PS N w z)
    (hy : y ∈ PS N w z) (hxy : x < y) (hlo0 : lo 0 ≤ x) (hhi0 : (x : ℝ) < hi 0)
    (hlo1 : lo 1 ≤ y) (hhi1 : (y : ℝ) < hi 1) : ![x, y] ∈ tuples N 2 w z lo hi := by
  unfold tuples
  rw [mem_filter, Fintype.mem_piFinset]
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · fin_cases j <;> simpa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  · fin_cases j <;> simp_all

lemma pair_inj : Set.InjOn (fun q : ℕ × ℕ => ![q.1, q.2]) Set.univ := by
  intro q _ q' _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  exact Prod.ext h0 h1

lemma pair_valid {d N a : ℕ} {w z : ℝ} (hd : d ∣ a) (hw : Sifted (d * N) w a) (hwz : w ≤ z)
    {x y : ℕ} (hx : x ∈ Rset d N w z a) (hy : y ∈ Rset d N w z a) (hxy : x < y) :
    d * ∏ j, (![x, y] : Fin 2 → ℕ) j ∣ a ∧
      Sifted (d * (∏ j, (![x, y] : Fin 2 → ℕ) j) * N) w a := by
  refine valid_of hd hw _ ?_ (fun j => by fin_cases j <;> simpa) hwz ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · intro q hq hqw; exact absurd (Rset_ge hq) (not_le.2 hqw)

/-- `2 · #{x < y in s} = #s² - #s`. -/
lemma two_mul_card_lt_pairs (s : Finset ℕ) :
    2 * #{q ∈ s ×ˢ s | q.1 < q.2} + #s = #s * #s := by
  have hsplit : #{q ∈ s ×ˢ s | q.1 < q.2} + #{q ∈ s ×ˢ s | q.2 < q.1} +
      #{q ∈ s ×ˢ s | q.1 = q.2} = #s * #s := by
    rw [← card_product]
    have h1 := card_filter_add_card_filter_not (s := s ×ˢ s) (fun q : ℕ × ℕ => q.1 < q.2)
    have h2 := card_filter_add_card_filter_not (s := {q ∈ s ×ˢ s | ¬ q.1 < q.2})
      (fun q : ℕ × ℕ => q.2 < q.1)
    rw [filter_filter, filter_filter] at h2
    have e1 : {q ∈ s ×ˢ s | ¬ q.1 < q.2 ∧ q.2 < q.1} = {q ∈ s ×ˢ s | q.2 < q.1} := by
      apply filter_congr; intro q _; constructor
      · exact fun h => h.2
      · intro h; exact ⟨not_lt.2 h.le, h⟩
    have e2 : {q ∈ s ×ˢ s | ¬ q.1 < q.2 ∧ ¬ q.2 < q.1} = {q ∈ s ×ˢ s | q.1 = q.2} := by
      apply filter_congr; intro q _; omega
    rw [e1, e2] at h2
    omega
  have hswap : #{q ∈ s ×ˢ s | q.2 < q.1} = #{q ∈ s ×ˢ s | q.1 < q.2} := by
    apply card_nbij' Prod.swap Prod.swap <;> intro q <;> simp +contextual [and_comm]
  have hdiag : #{q ∈ s ×ˢ s | q.1 = q.2} = #s := by
    have : {q ∈ s ×ˢ s | q.1 = q.2} = s.diag := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, mem_diag]
      constructor
      · rintro ⟨⟨hx, -⟩, h⟩; exact ⟨hx, h⟩
      · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, hx⟩, rfl⟩
    rw [this, diag_card]
  omega

lemma between_card (R : Finset ℕ) {θ θ' : ℝ} (h : θ ≤ θ') :
    #{x ∈ R | θ ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) < θ'} = Nc R θ' - Nc R θ := by
  unfold Nc
  have := card_filter_add_card_filter_not (s := {x ∈ R | ((x : ℕ) : ℝ) < θ'})
    (fun x : ℕ => ((x : ℕ) : ℝ) < θ)
  rw [filter_filter, filter_filter] at this
  have e1 : {x ∈ R | ((x : ℕ) : ℝ) < θ' ∧ ((x : ℕ) : ℝ) < θ} = {x ∈ R | ((x : ℕ) : ℝ) < θ} := by
    apply filter_congr; intro x _; constructor
    · exact fun h => h.2
    · intro h'; exact ⟨lt_of_lt_of_le h' h, h'⟩
  have e2 : {x ∈ R | ((x : ℕ) : ℝ) < θ' ∧ ¬ ((x : ℕ) : ℝ) < θ} =
      {x ∈ R | θ ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) < θ'} := by
    apply filter_congr; intro x _; rw [not_lt]; tauto
  rw [e1, e2] at this
  omega

theorem gamma5_bound {d N a : ℕ} {w k₂ z : ℝ} (hd : d ∣ a) (hw : Sifted (d * N) w a)
    (hwz : w ≤ z) :
    2 * Nc (Rset d N w z a) k₂ ≤ cnt d N w z a 2 ![w, w] ![k₂, k₂] (fun _ => w) + 3 := by
  set R := Rset d N w z a
  set s := ({x ∈ R | ((x : ℕ) : ℝ) < k₂} : Finset ℕ)
  have hs : #s = Nc R k₂ := rfl
  have hsub : ({q ∈ s ×ˢ s | q.1 < q.2}).image (fun q : ℕ × ℕ => ![q.1, q.2]) ⊆
      {p ∈ tuples N 2 w z ![w, w] ![k₂, k₂] | d * ∏ j, p j ∣ a ∧
        Sifted (d * (∏ j, p j) * N) ((fun _ => w) p) a} := by
    intro p hp
    obtain ⟨⟨x, y⟩, hq, rfl⟩ := mem_image.1 hp
    simp only [mem_filter, mem_product, s] at hq
    obtain ⟨⟨⟨hxR, hxk⟩, hyR, hyk⟩, hxy⟩ := hq
    rw [mem_filter]
    exact ⟨pair_mem (mem_Rset.1 hxR).1 (mem_Rset.1 hyR).1 hxy (by simpa using Rset_ge hxR)
      (by simpa using hxk) (by simpa using Rset_ge hyR) (by simpa using hyk),
      pair_valid hd hw hwz hxR hyR hxy⟩
  have h1 := card_le_card hsub
  rw [card_image_of_injOn (fun q _ q' _ h => pair_inj (Set.mem_univ q) (Set.mem_univ q') h)]
    at h1
  have h2 := two_mul_card_lt_pairs s
  have key : 2 * #s ≤ #{q ∈ s ×ˢ s | q.1 < q.2} + 3 := by
    generalize #{q ∈ s ×ˢ s | q.1 < q.2} = c at h2 ⊢
    generalize #s = n at h2 ⊢
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> omega
    · nlinarith
  unfold cnt
  rw [← hs]
  exact key.trans (Nat.add_le_add_right h1 3)

theorem gamma6_bound {d N a : ℕ} {w k₁ k₂ k₃ z : ℝ} (hd : d ∣ a) (hw : Sifted (d * N) w a)
    (hwz : w ≤ z) (h12 : k₁ ≤ k₂) (h23 : k₂ ≤ k₃) :
    Nc (Rset d N w z a) k₁ * (Nc (Rset d N w z a) k₃ - Nc (Rset d N w z a) k₂) ≤
      cnt d N w z a 2 ![w, k₂] ![k₁, k₃] (fun _ => w) := by
  set R := Rset d N w z a
  set s := ({x ∈ R | ((x : ℕ) : ℝ) < k₁} : Finset ℕ)
  set t := ({x ∈ R | k₂ ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) < k₃} : Finset ℕ)
  have hsub : (s ×ˢ t).image (fun q : ℕ × ℕ => ![q.1, q.2]) ⊆
      {p ∈ tuples N 2 w z ![w, k₂] ![k₁, k₃] | d * ∏ j, p j ∣ a ∧
        Sifted (d * (∏ j, p j) * N) ((fun _ => w) p) a} := by
    intro p hp
    obtain ⟨⟨x, y⟩, hq, rfl⟩ := mem_image.1 hp
    simp only [mem_product, mem_filter, s, t] at hq
    obtain ⟨⟨hxR, hxk⟩, hyR, hyk2, hyk3⟩ := hq
    have hxy : x < y := by
      have : (x : ℝ) < y := by linarith
      exact_mod_cast this
    rw [mem_filter]
    exact ⟨pair_mem (mem_Rset.1 hxR).1 (mem_Rset.1 hyR).1 hxy (by simpa using Rset_ge hxR)
      (by simpa using hxk) (by simpa using hyk2) (by simpa using hyk3),
      pair_valid hd hw hwz hxR hyR hxy⟩
  have h1 := card_le_card hsub
  rw [card_image_of_injOn (fun q _ q' _ h => pair_inj (Set.mem_univ q) (Set.mem_univ q') h),
    card_product] at h1
  have ht : #t = Nc R k₃ - Nc R k₂ := between_card R h23
  unfold cnt
  rw [← ht]
  exact h1

/-- The terms with `p ∣ d`, pointwise. -/
def eCnt (d N : ℕ) (w z : ℝ) (a : ℕ) : ℕ :=
  #{p ∈ {p ∈ PS N w z | p ∣ d} | d * p ∣ a ∧ Sifted (d * N) w a}

theorem single_bound {d N a : ℕ} {w z θ : ℝ} :
    cnt d N w z a 1 ![w] ![θ] (fun _ => w) ≤ Nc (Rset d N w z a) θ + eCnt d N w z a := by
  set R := Rset d N w z a
  unfold cnt eCnt Nc
  have hsub : ({p ∈ tuples N 1 w z ![w] ![θ] | d * ∏ j, p j ∣ a ∧
      Sifted (d * (∏ j, p j) * N) ((fun _ => w) p) a}).image (fun p => p 0) ⊆
      {x ∈ R | ((x : ℕ) : ℝ) < θ} ∪ {p ∈ {p ∈ PS N w z | p ∣ d} | d * p ∣ a ∧
        Sifted (d * N) w a} := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
    simp only [mem_filter, tuples, Fintype.mem_piFinset, Fin.prod_univ_one] at hp
    obtain ⟨⟨hPS, -, hb⟩, hdvd, hs⟩ := hp
    have hP0 := hPS 0
    have hpr := (mem_PS.1 hP0).1
    have hsw : Sifted (d * N) w a := by
      intro q hq hqw hqdN hqa
      refine hs q hq hqw (fun h => ?_) hqa
      rw [mul_right_comm] at h
      rcases (Nat.Prime.dvd_mul hq).1 h with h' | h'
      · exact hqdN h'
      · have := (Nat.prime_dvd_prime_iff_eq hq hpr).1 h'
        have hge := (mem_PS.1 hP0).2.1
        rw [← this] at hge
        exact absurd hqw (not_lt.2 hge)
    rw [mem_union]
    by_cases hpd : p 0 ∣ d
    · right
      rw [mem_filter, mem_filter]
      exact ⟨⟨hP0, hpd⟩, hdvd, hsw⟩
    · left
      rw [mem_filter, mem_Rset]
      exact ⟨⟨hP0, hpd, dvd_trans (dvd_mul_left _ d) hdvd⟩, by simpa using (hb 0).2⟩
  have := card_le_card hsub
  rw [card_image_of_injOn (fun p _ q _ h => by
    funext j; rw [Fin.fin_one_eq_zero j]; exact h)] at this
  exact this.trans (card_union_le _ _)

/-! ## The pointwise inequality and Lemma 4.2 -/

/-- Lemma 4.2 for one `a`. -/
theorem pointwise (d N : ℕ) {w k₁ k₂ k₃ z : ℝ} (h01 : w ≤ k₁) (h12 : k₁ ≤ k₂) (h23 : k₂ ≤ k₃)
    (h34 : k₃ ≤ z) (a : ℕ) :
    5 * (if d ∣ a ∧ Sifted (d * N) z a then 1 else 0)
      + cnt d N w z a 1 ![w] ![z] (fun _ => w)
      + cnt d N w z a 1 ![w] ![k₂] (fun _ => w)
      + cnt d N w z a 1 ![w] ![k₃] (fun _ => w)
    ≤ 4 * (if d ∣ a ∧ Sifted (d * N) w a then 1 else 0)
      + (if d ∣ a ∧ Sifted (d * N) k₁ a then 1 else 0)
      + cnt d N w z a 2 ![w, w] ![k₂, k₂] (fun _ => w)
      + cnt d N w z a 2 ![w, k₂] ![k₁, k₃] (fun _ => w)
      + cnt d N w z a 2 ![w, w] ![k₁, k₁] (yPrev 1)
      + cnt d N w z a 2 ![w, k₁] ![k₁, k₂] (yPrev 1)
      + cnt d N w z a 3 ![k₁, k₁, k₁] ![k₃, k₃, k₃] (yPrev 2)
      + cnt d N w z a 3 ![k₁, k₁, k₂] ![k₂, k₂, z] (yPrev 2)
      + cnt d N w z a 3 ![k₁, k₂, k₂] ![k₂, k₃, k₃] (yPrev 2)
      + cnt d N w z a 3 ![w, w, k₃] ![k₁, k₁, z] (yPrev 2)
      + cnt d N w z a 3 ![w, k₁, k₂] ![k₁, k₂, z] (yPrev 2)
      + cnt d N w z a 3 ![w, k₂, k₂] ![k₁, z, z] (yPrev 2)
      + cnt d N w z a 3 ![k₁, k₂, k₃] ![k₂, k₃, z] (yPrev 2)
      + cnt d N w z a 4 ![k₂, k₂, k₂, k₂] ![k₃, k₃, k₃, k₃] (yPrev 3)
      + cnt d N w z a 4 ![k₂, k₂, k₂, k₃] ![k₃, k₃, k₃, z] (yPrev 3)
      + cnt d N w z a 4 ![k₂, k₂, k₃, k₃] ![k₃, k₃, z, z] (yPrev 3)
      + cnt d N w z a 4 ![k₁, k₃, k₃, k₃] ![k₂, z, z, z] (yPrev 3)
      + cnt d N w z a 5 ![k₂, k₃, k₃, k₃, k₃] ![k₃, z, z, z, z] (yPrev 4)
      + cnt d N w z a 6 (fun _ => k₃) (fun _ => z) (yPrev 5)
      + 3 * eCnt d N w z a := by
  have hwz : w ≤ z := by linarith
  by_cases hda : d ∣ a ∧ Sifted (d * N) w a
  swap
  · -- nothing survives: the single-prime counts vanish
    have hz : ¬ (d ∣ a ∧ Sifted (d * N) z a) := fun h => hda ⟨h.1, sifted_mono hwz h.2⟩
    have h0 : ∀ θ : ℝ, cnt d N w z a 1 ![w] ![θ] (fun _ => w) = 0 := by
      intro θ
      unfold cnt
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro p hp ⟨hdvd, hs⟩
      simp only [tuples, mem_filter, Fintype.mem_piFinset, Fin.prod_univ_one] at hp hdvd hs
      have hP0 := hp.1 0
      have hpr := (mem_PS.1 hP0).1
      refine hda ⟨dvd_trans (dvd_mul_right d _) hdvd, fun q hq hqw hqdN hqa => ?_⟩
      refine hs q hq hqw (fun h => ?_) hqa
      rw [mul_right_comm] at h
      rcases (Nat.Prime.dvd_mul hq).1 h with h' | h'
      · exact hqdN h'
      · have := (Nat.prime_dvd_prime_iff_eq hq hpr).1 h'
        have hge := (mem_PS.1 hP0).2.1
        rw [← this] at hge
        exact absurd hqw (not_lt.2 hge)
    rw [if_neg hz, h0, h0, h0]
    omega
  obtain ⟨hd, hw⟩ := hda
  rw [if_pos (show d ∣ a ∧ Sifted (d * N) w a from ⟨hd, hw⟩)]
  set R := Rset d N w z a with hRdef
  have hN0 : Nc R w = 0 := Nc_w d N w z a
  have hNz : Nc R z = #R := Nc_z d N w z a
  have m1 := Nc_mono R h12
  have m2 := Nc_mono R h23
  have m3 : Nc R k₃ ≤ #R := Nc_le_card R k₃
  -- the left indicator
  have hL0 : 1 ≤ #R → (5 * (if d ∣ a ∧ Sifted (d * N) z a then 1 else 0)) = 0 := by
    intro hR
    obtain ⟨q, hq⟩ := card_pos.1 (by omega : 0 < #R)
    obtain ⟨hqP, hqd, hqa⟩ := mem_Rset.1 hq
    obtain ⟨hqpr, -, hqz, hqN⟩ := mem_PS.1 hqP
    rw [if_neg]
    rintro ⟨-, hs⟩
    refine hs q hqpr hqz (fun h => ?_) hqa
    rcases (Nat.Prime.dvd_mul hqpr).1 h with h' | h'
    · exact hqd h'
    · exact (Nat.Prime.coprime_iff_not_dvd hqpr).1 hqN h'
  have hL5 : 5 * (if d ∣ a ∧ Sifted (d * N) z a then 1 else 0) ≤ 5 := by split_ifs <;> omega
  -- the `Γ₁` indicator at `k₁`
  have hg : Nc R k₁ = 0 → 1 ≤ (if d ∣ a ∧ Sifted (d * N) k₁ a then 1 else 0) := by
    intro h0
    rw [if_pos]
    refine ⟨hd, fun q hq hqk hqdN hqa => ?_⟩
    by_cases hqw : (q : ℝ) < w
    · exact hw q hq hqw hqdN hqa
    · push Not at hqw
      have hqR : q ∈ R := mem_Rset.2 ⟨mem_PS.2 ⟨hq, hqw, by linarith,
        (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqdN (dvd_mul_of_dvd_right h d))⟩,
        fun h => hqdN (dvd_mul_of_dvd_left h N), hqa⟩
      unfold Nc at h0
      rw [card_eq_zero, filter_eq_empty_iff] at h0
      exact h0 hqR hqk
  -- the bounds
  have b2 : cnt d N w z a 1 ![w] ![z] (fun _ => w) ≤ #R + eCnt d N w z a := by
    have := @single_bound d N a w z z; rw [Nc_z] at this; exact this
  have b3 : cnt d N w z a 1 ![w] ![k₂] (fun _ => w) ≤ Nc R k₂ + eCnt d N w z a :=
    single_bound
  have b4 : cnt d N w z a 1 ![w] ![k₃] (fun _ => w) ≤ Nc R k₃ + eCnt d N w z a :=
    single_bound
  have b5 : 2 * Nc R k₂ ≤ cnt d N w z a 2 ![w, w] ![k₂, k₂] (fun _ => w) + 3 :=
    gamma5_bound hd hw hwz
  have b6 : Nc R k₁ * (Nc R k₃ - Nc R k₂) ≤ cnt d N w z a 2 ![w, k₂] ![k₁, k₃] (fun _ => w) :=
    gamma6_bound hd hw hwz h12 h23
  have b6a : Nc R k₁ = 1 → Nc R k₃ - Nc R k₂ ≤ cnt d N w z a 2 ![w, k₂] ![k₁, k₃] (fun _ => w) :=
    fun h => by rw [h, one_mul] at b6; exact b6
  have b6b : 2 ≤ Nc R k₁ → 2 * (Nc R k₃ - Nc R k₂) ≤
      cnt d N w z a 2 ![w, k₂] ![k₁, k₃] (fun _ => w) :=
    fun h => le_trans (Nat.mul_le_mul_right _ h) b6
  have P : ∀ (m : ℕ) (hm : 1 ≤ m) (lo hi : Fin (m + 1) → ℝ),
      (∀ j : Fin m, Nc R (lo j.castSucc) ≤ j ∧ (j : ℕ) < Nc R (hi j.castSucc)) →
      Nc R (hi (Fin.last m)) - max m (Nc R (lo (Fin.last m))) ≤
        cnt d N w z a (m + 1) lo hi (yPrev m) :=
    fun m hm lo hi hpre => prefix_bound hd hw m hm lo hi hpre
  have b7 : 0 < Nc R k₁ → Nc R k₁ - max 1 0 ≤ cnt d N w z a 2 ![w, w] ![k₁, k₁] (yPrev 1) := by
    intro h; have := P 1 le_rfl ![w, w] ![k₁, k₁] (by intro j; fin_cases j; simp [hN0]; omega)
    simpa [hN0] using this
  have b8 : 0 < Nc R k₁ → Nc R k₂ - max 1 (Nc R k₁) ≤
      cnt d N w z a 2 ![w, k₁] ![k₁, k₂] (yPrev 1) := by
    intro h; exact P 1 le_rfl ![w, k₁] ![k₁, k₂] (by intro j; fin_cases j; simp [hN0]; omega)
  have b9 : Nc R k₁ ≤ 0 ∧ 0 < Nc R k₃ ∧ Nc R k₁ ≤ 1 ∧ 1 < Nc R k₃ →
      Nc R k₃ - max 2 (Nc R k₁) ≤ cnt d N w z a 3 ![k₁, k₁, k₁] ![k₃, k₃, k₃] (yPrev 2) := by
    intro h; exact P 2 (by norm_num) ![k₁, k₁, k₁] ![k₃, k₃, k₃]
      (by intro j; fin_cases j <;> simp <;> omega)
  have b10 : Nc R k₁ ≤ 0 ∧ 0 < Nc R k₂ ∧ Nc R k₁ ≤ 1 ∧ 1 < Nc R k₂ →
      #R - max 2 (Nc R k₂) ≤ cnt d N w z a 3 ![k₁, k₁, k₂] ![k₂, k₂, z] (yPrev 2) := by
    intro h; have := P 2 (by norm_num) ![k₁, k₁, k₂] ![k₂, k₂, z]
      (by intro j; fin_cases j <;> simp <;> omega)
    simpa [hNz] using this
  have b11 : Nc R k₁ ≤ 0 ∧ 0 < Nc R k₂ ∧ Nc R k₂ ≤ 1 ∧ 1 < Nc R k₃ →
      Nc R k₃ - max 2 (Nc R k₂) ≤ cnt d N w z a 3 ![k₁, k₂, k₂] ![k₂, k₃, k₃] (yPrev 2) := by
    intro h; exact P 2 (by norm_num) ![k₁, k₂, k₂] ![k₂, k₃, k₃]
      (by intro j; fin_cases j <;> simp <;> omega)
  have b12 : 0 < Nc R k₁ ∧ 1 < Nc R k₁ →
      #R - max 2 (Nc R k₃) ≤ cnt d N w z a 3 ![w, w, k₃] ![k₁, k₁, z] (yPrev 2) := by
    intro h; have := P 2 (by norm_num) ![w, w, k₃] ![k₁, k₁, z]
      (by intro j; fin_cases j <;> simp [hN0] <;> omega)
    simpa [hNz] using this
  have b13 : 0 < Nc R k₁ ∧ Nc R k₁ ≤ 1 ∧ 1 < Nc R k₂ →
      #R - max 2 (Nc R k₂) ≤ cnt d N w z a 3 ![w, k₁, k₂] ![k₁, k₂, z] (yPrev 2) := by
    intro h; have := P 2 (by norm_num) ![w, k₁, k₂] ![k₁, k₂, z]
      (by intro j; fin_cases j <;> simp [hN0] <;> omega)
    simpa [hNz] using this
  have b14 : 0 < Nc R k₁ ∧ Nc R k₂ ≤ 1 ∧ 1 < #R →
      #R - max 2 (Nc R k₂) ≤ cnt d N w z a 3 ![w, k₂, k₂] ![k₁, z, z] (yPrev 2) := by
    intro h; have := P 2 (by norm_num) ![w, k₂, k₂] ![k₁, z, z]
      (by intro j; fin_cases j <;> simp [hN0, hNz] <;> omega)
    simpa [hNz] using this
  have b15 : Nc R k₁ ≤ 0 ∧ 0 < Nc R k₂ ∧ Nc R k₂ ≤ 1 ∧ 1 < Nc R k₃ →
      #R - max 2 (Nc R k₃) ≤ cnt d N w z a 3 ![k₁, k₂, k₃] ![k₂, k₃, z] (yPrev 2) := by
    intro h; have := P 2 (by norm_num) ![k₁, k₂, k₃] ![k₂, k₃, z]
      (by intro j; fin_cases j <;> simp <;> omega)
    simpa [hNz] using this
  have b16 : Nc R k₂ ≤ 0 ∧ 0 < Nc R k₃ ∧ Nc R k₂ ≤ 1 ∧ 1 < Nc R k₃ ∧ Nc R k₂ ≤ 2 ∧
      2 < Nc R k₃ → Nc R k₃ - max 3 (Nc R k₂) ≤
        cnt d N w z a 4 ![k₂, k₂, k₂, k₂] ![k₃, k₃, k₃, k₃] (yPrev 3) := by
    intro h; exact P 3 (by norm_num) ![k₂, k₂, k₂, k₂] ![k₃, k₃, k₃, k₃]
      (by intro j; fin_cases j <;> simp <;> omega)
  have b17 : Nc R k₂ ≤ 0 ∧ 0 < Nc R k₃ ∧ Nc R k₂ ≤ 1 ∧ 1 < Nc R k₃ ∧ Nc R k₂ ≤ 2 ∧
      2 < Nc R k₃ → #R - max 3 (Nc R k₃) ≤
        cnt d N w z a 4 ![k₂, k₂, k₂, k₃] ![k₃, k₃, k₃, z] (yPrev 3) := by
    intro h; have := P 3 (by norm_num) ![k₂, k₂, k₂, k₃] ![k₃, k₃, k₃, z]
      (by intro j; fin_cases j <;> simp <;> omega)
    simpa [hNz] using this
  have b18 : Nc R k₂ ≤ 0 ∧ 0 < Nc R k₃ ∧ Nc R k₂ ≤ 1 ∧ 1 < Nc R k₃ ∧ Nc R k₃ ≤ 2 ∧
      2 < #R → #R - max 3 (Nc R k₃) ≤
        cnt d N w z a 4 ![k₂, k₂, k₃, k₃] ![k₃, k₃, z, z] (yPrev 3) := by
    intro h; have := P 3 (by norm_num) ![k₂, k₂, k₃, k₃] ![k₃, k₃, z, z]
      (by intro j; fin_cases j <;> simp [hNz] <;> omega)
    simpa [hNz] using this
  have b19 : Nc R k₁ ≤ 0 ∧ 0 < Nc R k₂ ∧ Nc R k₃ ≤ 1 ∧ 1 < #R ∧ Nc R k₃ ≤ 2 ∧ 2 < #R →
      #R - max 3 (Nc R k₃) ≤ cnt d N w z a 4 ![k₁, k₃, k₃, k₃] ![k₂, z, z, z] (yPrev 3) := by
    intro h; have := P 3 (by norm_num) ![k₁, k₃, k₃, k₃] ![k₂, z, z, z]
      (by intro j; fin_cases j <;> simp [hNz] <;> omega)
    simpa [hNz] using this
  have b20 : Nc R k₂ ≤ 0 ∧ 0 < Nc R k₃ ∧ Nc R k₃ ≤ 1 ∧ 1 < #R ∧ Nc R k₃ ≤ 2 ∧ 2 < #R ∧
      Nc R k₃ ≤ 3 ∧ 3 < #R → #R - max 4 (Nc R k₃) ≤
        cnt d N w z a 5 ![k₂, k₃, k₃, k₃, k₃] ![k₃, z, z, z, z] (yPrev 4) := by
    intro h; have := P 4 (by norm_num) ![k₂, k₃, k₃, k₃, k₃] ![k₃, z, z, z, z]
      (by intro j; fin_cases j <;> simp [hNz] <;> omega)
    simpa [hNz] using this
  have b21 : Nc R k₃ ≤ 0 ∧ 0 < #R ∧ Nc R k₃ ≤ 1 ∧ 1 < #R ∧ Nc R k₃ ≤ 2 ∧ 2 < #R ∧
      Nc R k₃ ≤ 3 ∧ 3 < #R ∧ Nc R k₃ ≤ 4 ∧ 4 < #R → #R - max 5 (Nc R k₃) ≤
        cnt d N w z a 6 (fun _ => k₃) (fun _ => z) (yPrev 5) := by
    intro h; have := P 5 (by norm_num) (fun _ => k₃) (fun _ => z)
      (by intro j; simp only [hNz]; have := j.2; omega)
    simpa [hNz] using this
  have := lemma42_arith (Nc R k₁) (Nc R k₂) (Nc R k₃) (#R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ (eCnt d N w z a) m1 m2 m3 hL5 hL0 hg b2 b3 b4 b5 b6a b6b b7 b8 b9
    b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
  omega

/-- **Wu 2004 Lemma 4.2, exact form, in `ℕ`**, the printed `P(dN)` read as `P(d p₁⋯p_k N)`:
`5 S(A_d; P(dN), z) + Γ₂ + Γ₃ + Γ₄ ≤ Γ₁ + Γ₅ + ⋯ + Γ₂₁ + 3E`. -/
theorem lemma42_nat (A : Finset ℕ) (d N : ℕ) {w k₁ k₂ k₃ z : ℝ} (h01 : w ≤ k₁) (h12 : k₁ ≤ k₂)
    (h23 : k₂ ≤ k₃) (h34 : k₃ ≤ z) :
    5 * S A d (d * N) z + Γ₂ A d N w z + Γ₃ A d N w k₂ z + Γ₄ A d N w k₃ z ≤
      Γ₁ A d N w k₁ + Γ₅ A d N w k₂ z + Γ₆ A d N w k₁ k₂ k₃ z + Γ₇ A d N w k₁ z
      + Γ₈ A d N w k₁ k₂ z + Γ₉ A d N w k₁ k₃ z + Γ₁₀ A d N w k₁ k₂ z + Γ₁₁ A d N w k₁ k₂ k₃ z
      + Γ₁₂ A d N w k₁ k₃ z + Γ₁₃ A d N w k₁ k₂ z + Γ₁₄ A d N w k₁ k₂ z
      + Γ₁₅ A d N w k₁ k₂ k₃ z + Γ₁₆ A d N w k₂ k₃ z + Γ₁₇ A d N w k₂ k₃ z
      + Γ₁₈ A d N w k₂ k₃ z + Γ₁₉ A d N w k₁ k₂ k₃ z + Γ₂₀ A d N w k₂ k₃ z
      + Γ₂₁ A d N w k₃ z + 3 * Err A d N w z := by
  have hErr : Err A d N w z = ∑ a ∈ A, eCnt d N w z a := by
    unfold Err eCnt
    simp only [S_eq_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [card_filter]
  unfold Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Γ₁₈ Γ₁₉ Γ₂₀ Γ₂₁
  simp only [G_eq, hErr, S_eq_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun a _ => pointwise d N h01 h12 h23 h34 a

/-- Vacuity: tuple sets are not empty; `2 < 3` is a pair of `Γ₅`'s shape with `N = 1`,
`w = 2`, `z = 4`. -/
theorem tuples_ex : ![2, 3] ∈ tuples 1 2 (2 : ℝ) 4 ![2, 2] ![4, 4] :=
  pair_mem (by rw [Wu41.PS_ex]; simp) (by rw [Wu41.PS_ex]; simp) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end LeanLab.ChenDoubleSieve.Wu42
