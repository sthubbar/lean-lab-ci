/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1103Z-29422, unit U-1414.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1, read on arxiv.org/html/2608.09488 this run, Section 2, definition of
`R₄(𝒜, D) = Σ_{d ∣ P(z), d < D} τ₄(d) |r_d|`, Section 3, eq (3.1) to (3.3), and Section 4,
Lemma 4.3: for `z ≥ z₁ = 10^8`, `R₄(𝒜, z^{14.66}) < 0.563 z^{14.66} log⁸ z`.

Objects, all as in the paper. `𝒜 = (aₙ)_{n ∈ I₃}`, `I₃ = {1 ≤ n ≤ N - 1 : 3 ∤ aₙ}`, `X = |I₃|`,
`𝒫` the primes other than 3, `P(z) = ∏_{p < z, p ∈ 𝒫} p`, `r_d = |𝒜_d| - X g(d)`. A squarefree
`d ∣ P(z)` is a set `s ⊆ primesBelow z` and `τ₄(d) = 4^{|s|}`. `R4paper N` is `R₄(𝒜, z^{14.66})`
at `z = N^{1/16.5}`; it is a concrete function, so `Thm21Case3 R4paper` is Theorem 2.1 for the
paper's own remainder, no longer a statement about a free `R4`.

Route, close to the paper with two changes.
* `r_d = ρ_d - ρ_{3d} + g(d) ρ_3`, eq (3.3), PROVED here from the counts; `|ρ_d| ≤ 2^{ω(d)}` is
  `DDNathanson.nathansonRd`, PROVED, the same sequence `aₙ`. With `g(d) ≤ 1`, `|ρ₃| ≤ 2`:
  `|r_d| ≤ 5 · 2^{ω(d)}`, cruder than the paper's `19/6`.
* Rankin with `δ = 1 - α/log z`, `α = 0.6`, and the convexity bound
  `e^{α t} ≤ 1 + t (e^α - 1)` on `[0, 1]` in place of the paper's `1 + α t e^α`; the paper's
  `α = 0.3246` is optimal for its own bound, `α = 0.6` near `log(14.66/8)` for this one.
* `Σ_{p ∈ 𝒫, p < z} 1/p` is not taken from Rosser-Schoenfeld (3.18). Instead
  `e^{1/p}(1 - 1/p) ≤ 1` gives `exp Σ_{5 ≤ p < z} 1/p ≤ 1/∏_{5 ≤ p < z}(1 - 1/p)`, and that product
  is bounded below from **Rosser-Schoenfeld eq (3.25)**, the input `RS325` Lemma 4.2 already uses.
  `Σ_{p < z} log p / p < log z` is `RSLogSum.sum_log_div_lt_log_real`, PROVED.
Constant: `5 e^{8 e^{0.6} - 12.796} / (3^8 E0^4 (1 - 1/(2 · 18.4192²))^8) < 0.563`, Python value
0.46592, the exact-γ value 0.46348.

PROVED, no cited input: `rA_eq` (eq (3.3)), `rA_bound`, `rankin14`, `exp_recip_le`,
`lemma43_const`, `rA_example`, `R4paper_nonneg`.
CONDITIONAL ON `RS325`: `lemma43_general`, `lemma43_of_RS325`, the lab's `Lemma43 R4paper`.
CONDITIONAL ON `Thm21Case3 R4paper` and `RS325`: `case3Sieve_of_RS43`.
CONDITIONAL ON `GapTable`, `Case2Sieve`, `Case2Table`, `Thm21Case3 R4paper`, `RS325`:
`theorem1_2_of_inputs_RS43`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellLemma42
import LeanLab.AlmostPrimes.DDNathanson

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellLemma43
open LeanLab.AlmostPrimes Campbell2026 CampbellCase3 CampbellCase2 CampbellCase2X CampbellCase3X
  CampbellLemma42

/-! ### The paper's objects -/

/-- `|𝒜_d|`: the `1 ≤ n ≤ N - 1` with `3 ∤ aₙ` and `d ∣ aₙ`. -/
def Ad3 (N d : ℕ) : ℕ := #{n ∈ Icc 1 (N - 1) | ¬ 3 ∣ aSeq N n ∧ d ∣ aSeq N n}

/-- `g(d) = ∏_{p ∈ s} g(p)` for `d = ∏ s`, Campbell's `g`. -/
def gS (N : ℕ) (s : Finset ℕ) : ℝ := ∏ p ∈ s, CampbellCase2.g N p

/-- `r_d = |𝒜_d| - X g(d)` for `d = ∏ s`, eq (3.3). -/
def rA (N : ℕ) (s : Finset ℕ) : ℝ := (Ad3 N (∏ p ∈ s, p) : ℝ) - (Xcount N : ℝ) * gS N s

/-- `R₄(𝒜, D) = Σ_{d ∣ P(z), d < D} τ₄(d) |r_d|`, with `τ₄(d) = 4^{ω(d)}` for squarefree `d`. -/
def R4A (N : ℕ) (z D : ℝ) : ℝ :=
  ∑ s ∈ (primesBelow z).powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D),
    (4 : ℝ) ^ s.card * |rA N s|

/-- The paper's `R₄(𝒜, z^{14.66})` at `z = N^{1/16.5}`. -/
def R4paper (N : ℕ) : ℝ := R4A N (zOf N) (zOf N ^ (14.66 : ℝ))

theorem R4paper_nonneg (N : ℕ) : 0 ≤ R4paper N := by
  unfold R4paper R4A
  exact sum_nonneg fun s _ => by positivity

/-! ### Eq (3.3): `r_d = ρ_d - ρ_{3d} + g(d) ρ₃` -/

lemma g_eq (N p : ℕ) : CampbellCase2.g N p = DDLemma21.g N p := rfl

lemma gS_eq (N : ℕ) (s : Finset ℕ) : gS N s = DDMain.gd N s := rfl

lemma g_bounds (N : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ CampbellCase2.g N p ∧ CampbellCase2.g N p ≤ 1 := by
  unfold CampbellCase2.g
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs
  · norm_num
  · constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith
  · constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith

lemma gS_bounds (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : 0 ≤ gS N s ∧ gS N s ≤ 1 :=
  ⟨prod_nonneg fun p hp => (g_bounds N (hs p hp)).1,
   prod_le_one₀ (fun p hp => (g_bounds N (hs p hp)).1) (fun p hp => (g_bounds N (hs p hp)).2)⟩

/-- `|𝒜_d| = |ℬ_d| - |ℬ_{3d}|` for `3 ∉ s`. -/
lemma Ad3_eq (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (h3 : 3 ∉ s) :
    (Ad3 N (∏ p ∈ s, p) : ℝ) =
      (DDMain.Ad N (∏ p ∈ s, p) : ℝ) - (DDMain.Ad N (∏ p ∈ insert 3 s, p) : ℝ) := by
  have hs' : ∀ p ∈ insert 3 s, p.Prime := by
    intro p hp; rw [mem_insert] at hp
    rcases hp with rfl | hp
    · exact Nat.prime_three
    · exact hs p hp
  set S := (Icc 1 (N - 1)).filter (fun n => (∏ p ∈ s, p) ∣ aSeq N n) with hS
  have hsplit := card_filter_add_card_filter_not (s := S) (fun n => 3 ∣ aSeq N n)
  have e1 : DDMain.Ad N (∏ p ∈ insert 3 s, p) = #(S.filter (fun n => 3 ∣ aSeq N n)) := by
    unfold DDMain.Ad
    rw [hS, filter_filter]
    congr 1
    apply filter_congr
    intro n _
    rw [DDNathanson.prod_dvd_iff hs', DDNathanson.prod_dvd_iff hs, forall_mem_insert]
    exact and_comm
  have e2 : Ad3 N (∏ p ∈ s, p) = #(S.filter (fun n => ¬ 3 ∣ aSeq N n)) := by
    unfold Ad3
    rw [hS, filter_filter]
    congr 1
    apply filter_congr
    intro n _
    exact and_comm
  have e3 : DDMain.Ad N (∏ p ∈ s, p) = #S := rfl
  rw [e1, e2, e3]
  have : (#(S.filter (fun n => 3 ∣ aSeq N n)) : ℝ) + #(S.filter (fun n => ¬ 3 ∣ aSeq N n)) = #S := by
    exact_mod_cast hsplit
  linarith

/-- `X = Y - |ℬ₃|`. -/
lemma Xcount_eq (N : ℕ) :
    (Xcount N : ℝ) = DDMain.Xc N - (DDMain.Ad N (∏ p ∈ ({3} : Finset ℕ), p) : ℝ) := by
  have hsplit := card_filter_add_card_filter_not (s := Icc 1 (N - 1))
    (fun n => 3 ∣ aSeq N n)
  have hc : #(Icc 1 (N - 1)) = N - 1 := by simp
  rw [prod_singleton]
  unfold Xcount DDMain.Xc DDMain.Ad
  rw [hc] at hsplit
  have : (#((Icc 1 (N - 1)).filter (fun n => 3 ∣ aSeq N n)) : ℝ) +
      #((Icc 1 (N - 1)).filter (fun n => ¬ 3 ∣ aSeq N n)) = ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- **Eq (3.3), PROVED**: `r_d = ρ_d - ρ_{3d} + g(d) ρ₃`, `ρ` the remainders of `ℬ`. -/
theorem rA_eq (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (h3 : 3 ∉ s) :
    rA N s = DDMain.rd N s - DDMain.rd N (insert 3 s) + gS N s * DDMain.rd N {3} := by
  unfold rA DDMain.rd
  rw [Ad3_eq N hs h3, Xcount_eq N, gS_eq]
  have hg : DDMain.gd N (insert 3 s) = DDLemma21.g N 3 * DDMain.gd N s := by
    unfold DDMain.gd; rw [prod_insert h3]
  have hg3 : DDMain.gd N {3} = DDLemma21.g N 3 := by unfold DDMain.gd; rw [prod_singleton]
  rw [hg, hg3]
  ring

/-- **`|r_d| ≤ 5 · 2^{ω(d)}`, PROVED** for `d ∣ P(z)`. -/
theorem rA_bound (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (h3 : 3 ∉ s) :
    |rA N s| ≤ 5 * (2 : ℝ) ^ s.card := by
  have hs' : ∀ p ∈ insert 3 s, p.Prime := by
    intro p hp; rw [mem_insert] at hp
    rcases hp with rfl | hp
    · exact Nat.prime_three
    · exact hs p hp
  have h1 := DDNathanson.nathansonRd N s hs
  have h2 := DDNathanson.nathansonRd N (insert 3 s) hs'
  have h3' := DDNathanson.nathansonRd N {3} (by simp [Nat.prime_three])
  rw [card_insert_of_notMem h3] at h2
  rw [card_singleton] at h3'
  obtain ⟨g0, g1⟩ := gS_bounds N hs
  rw [rA_eq N hs h3]
  have hk : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
  have ha : |gS N s * DDMain.rd N {3}| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg g0]
    calc gS N s * |DDMain.rd N {3}| ≤ 1 * 2 := mul_le_mul g1 (by simpa using h3') (abs_nonneg _)
          (by norm_num)
      _ = 2 := by norm_num
  calc |DDMain.rd N s - DDMain.rd N (insert 3 s) + gS N s * DDMain.rd N {3}|
      ≤ |DDMain.rd N s| + |DDMain.rd N (insert 3 s)| + |gS N s * DDMain.rd N {3}| := by
        have := abs_add_le (DDMain.rd N s - DDMain.rd N (insert 3 s)) (gS N s * DDMain.rd N {3})
        have := abs_sub (DDMain.rd N s) (DDMain.rd N (insert 3 s))
        linarith
    _ ≤ 2 ^ s.card + 2 ^ (s.card + 1) + 2 := by linarith
    _ ≤ 5 * 2 ^ s.card := by rw [pow_succ]; linarith

/-! ### Rankin's trick at `D = z^{14.66}`, `α = 0.6` -/

/-- `e^{x} ≤ 1 + (x/α)(e^α - 1)` for `0 ≤ x ≤ α`, convexity of `exp`. -/
lemma exp_le_chord {x α : ℝ} (hx : 0 ≤ x) (hxα : x ≤ α) (hα : 0 < α) :
    exp x ≤ 1 + x / α * (exp α - 1) := by
  set t := x / α
  have ht0 : 0 ≤ t := div_nonneg hx hα.le
  have ht1 : t ≤ 1 := (div_le_one hα).2 hxα
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ α)
    (show (0 : ℝ) ≤ 1 - t by linarith) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  have e : t * α = x := by simp only [t]; field_simp
  rw [e] at h
  linarith

lemma mem_P {z : ℝ} {p : ℕ} (hp : p ∈ primesBelow z) : p.Prime ∧ (p : ℝ) < z ∧ p ≠ 3 := by
  rw [mem_primesBelow] at hp; exact ⟨hp.1, hp.2.2, hp.2.1⟩

/-- **Rankin, PROVED**: `Σ_{d ∣ P(z), d < z^{14.66}} 8^{ω(d)} ≤
z^{14.66} e^{-14.66 · 0.6} exp(8 Σ_{p} 1/p + 8 (e^{0.6} - 1))`, for `z ≥ 1000`. -/
theorem rankin14 (z : ℝ) (hz : 1000 ≤ z) :
    ∑ s ∈ (primesBelow z).powerset.filter
        (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < z ^ (14.66 : ℝ)), (8 : ℝ) ^ s.card ≤
      z ^ (14.66 : ℝ) * exp (-(14.66 * 0.6)) *
        exp (8 * ∑ p ∈ primesBelow z, (1 : ℝ) / p + 8 * (exp 0.6 - 1)) := by
  set P := primesBelow z with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z := fun p hp => ⟨(mem_P hp).1, (mem_P hp).2.1⟩
  have hz0 : 0 < z := by linarith
  set L := log z with hLdef
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hz0]
    have : exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hL0 : 0 < L := by linarith
  set α : ℝ := 0.6 with hα
  have hα0 : 0 < α := by rw [hα]; norm_num
  set η := α / L with hη
  set δ := 1 - η with hδ
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η < 1 := by rw [hη, div_lt_one hL0]; rw [hα]; linarith
  have hδ0 : 0 ≤ δ := by linarith
  set D := z ^ (14.66 : ℝ) with hD
  have hD0 : 0 < D := by positivity
  have hp0 : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).1.pos
  have hp1 : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hP p hp).1.one_lt.le
  set w : ℕ → ℝ := fun p => 8 * (p : ℝ) ^ (-δ) with hw
  have step1 : ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D),
      (8 : ℝ) ^ s.card ≤ ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p := by
    calc _ ≤ ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D),
            D ^ δ * ∏ p ∈ s, w p := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_filter, Finset.mem_powerset] at hs
          have hpos : 0 < ∏ p ∈ s, (p : ℝ) := Finset.prod_pos fun p hp => hp0 p (hs.1 hp)
          have e : D ^ δ * ∏ p ∈ s, w p = (8 : ℝ) ^ s.card * (D / ∏ p ∈ s, (p : ℝ)) ^ δ := by
            rw [hw, Finset.prod_mul_distrib, Finset.prod_const,
              Real.div_rpow hD0.le hpos.le,
              Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs.1 hp)).le)]
            rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity),
              ← Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs.1 hp)).le)]
            ring
          rw [e]
          have : 1 ≤ (D / ∏ p ∈ s, (p : ℝ)) ^ δ :=
            Real.one_le_rpow (by rw [le_div_iff₀ hpos]; linarith [hs.2]) hδ0
          have h8 : (0 : ℝ) ≤ 8 ^ s.card := by positivity
          nlinarith
      _ ≤ ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro s hs _
          rw [Finset.mem_powerset] at hs
          apply mul_nonneg (by positivity)
          apply Finset.prod_nonneg
          intro p hp; rw [hw]; have := hp0 p (hs hp); positivity
  have step2 : ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p ≤ D ^ δ * exp (∑ p ∈ P, w p) := by
    rw [← Finset.mul_sum, ← Finset.prod_one_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun p hp => by rw [hw]; have := hp0 p hp; positivity)
      (fun p _ => by have := Real.add_one_le_exp (w p); linarith)
  have step3 : ∑ p ∈ P, w p ≤
      8 * ∑ p ∈ P, (1 : ℝ) / p + 8 * (η / α) * (exp α - 1) * ∑ p ∈ P, log p / p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := hp0 p hp
    have hlp : 0 ≤ log p := Real.log_nonneg (hp1 p hp)
    have hlpz : log p ≤ L := by rw [hLdef]; exact Real.log_le_log hp' (hP p hp).2.le
    have e1 : (p : ℝ) ^ (-δ) = exp (η * log p) / p := by
      rw [Real.rpow_def_of_pos hp', hδ, show log p * -(1 - η) = η * log p - log p by ring,
        Real.exp_sub, Real.exp_log hp']
    have hx : η * log p ≤ α := by
      calc η * log p ≤ η * L := mul_le_mul_of_nonneg_left hlpz hη0.le
        _ = α := by rw [hη]; field_simp
    have e2 := exp_le_chord (mul_nonneg hη0.le hlp) hx hα0
    rw [hw]; simp only
    rw [e1]
    have : exp (η * log p) / p ≤ (1 + η * log p / α * (exp α - 1)) / p :=
      div_le_div_of_nonneg_right e2 hp'.le
    have e3 : 8 * ((1 + η * log p / α * (exp α - 1)) / p) =
        8 * (1 / p) + 8 * (η / α) * (exp α - 1) * (log p / p) := by
      field_simp
    nlinarith
  have hexp : ∑ p ∈ P, w p ≤ 8 * ∑ p ∈ P, (1 : ℝ) / p + 8 * (exp α - 1) := by
    have hRS2 := RSLogSum.sum_log_div_lt_log_real z hz P hP
    have hηL : η / α * L = 1 := by rw [hη]; field_simp
    have hea : 0 ≤ exp α - 1 := by have := Real.add_one_le_exp α; linarith
    have : 8 * (η / α) * (exp α - 1) * ∑ p ∈ P, log p / p ≤ 8 * (η / α) * (exp α - 1) * L :=
      mul_le_mul_of_nonneg_left hRS2.le (by positivity)
    have e : 8 * (η / α) * (exp α - 1) * L = 8 * (exp α - 1) := by
      rw [show 8 * (η / α) * (exp α - 1) * L = 8 * (exp α - 1) * (η / α * L) by ring, hηL, mul_one]
    linarith
  have hDδ : D ^ δ = D * exp (-(14.66 * α)) := by
    rw [hD, ← Real.rpow_mul hz0.le, Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0,
      ← Real.exp_add, ← hLdef, hδ, hη]
    congr 1
    field_simp
    ring
  calc _ ≤ D ^ δ * exp (∑ p ∈ P, w p) := step1.trans step2
    _ ≤ D ^ δ * exp (8 * ∑ p ∈ P, (1 : ℝ) / p + 8 * (exp α - 1)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [hDδ]

/-! ### The prime reciprocal sum from eq (3.25) -/

lemma primesBelow_eq {z : ℝ} (hz : 2 < z) : primesBelow z = insert 2 (primes5Below z) := by
  unfold primes5Below
  rw [filter_ne', insert_erase]
  rw [mem_primesBelow]
  exact ⟨Nat.prime_two, by norm_num, by exact_mod_cast hz⟩

/-- **`exp(Σ_{5 ≤ p < z} 1/p) · ∏_{5 ≤ p < z} (1 - 1/p) ≤ 1`, PROVED.** -/
theorem exp_recip_le (z : ℝ) :
    exp (∑ p ∈ primes5Below z, (1 : ℝ) / p) * ∏ p ∈ primes5Below z, f2 p ≤ 1 := by
  rw [Real.exp_sum, ← prod_mul_distrib]
  apply prod_le_one₀
  · intro p hp
    have := (f2_bounds (mem_A hp).1.one_lt.le).1
    positivity
  · intro p _
    have h := Real.add_one_le_exp (-(1 / (p : ℝ)))
    unfold f2
    have e : exp (1 / (p : ℝ)) * exp (-(1 / (p : ℝ))) = 1 := by rw [← exp_add]; simp
    have hp := exp_pos (1 / (p : ℝ))
    nlinarith

/-! ### The constant -/

lemma exp06_le : exp (0.6 : ℝ) ≤ 1.8222 := by
  have h := Real.exp_bound' (x := (0.6 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

lemma exp08908_le : exp (0.8908 : ℝ) ≤ 2.43716 := by
  have h := Real.exp_bound' (x := (0.8908 : ℝ)) (by norm_num) (by norm_num) (n := 16) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

/-- `c₁ = 1 - 1/(2 · 18.4192²)`. -/
def c1 : ℝ := 1 - 1 / (2 * 18.4192 ^ 2)

/-- **Lemma 4.3's constant for this route, PROVED**: Python value 0.46592 against 0.563. -/
theorem lemma43_const :
    5 * (exp (-(14.66 * 0.6)) * exp 4 * exp (8 * (exp 0.6 - 1))) / (3 ^ 8 * E0 ^ 4 * c1 ^ 8)
      < (0.563 : ℝ) := by
  have h1 : exp (-(14.66 * 0.6)) * exp 4 * exp (8 * (exp 0.6 - 1)) ≤ 5.94 := by
    rw [← exp_add, ← exp_add]
    have he := exp06_le
    have h2 : exp (-(14.66 * 0.6) + 4 + 8 * (exp 0.6 - 1)) ≤ exp (2 * 0.8908) :=
      exp_le_exp.2 (by nlinarith)
    have h3 : exp (2 * (0.8908 : ℝ)) = exp 0.8908 ^ 2 := by rw [← exp_nat_mul]; norm_num
    have h4 := exp08908_le
    have h5 : exp (0.8908 : ℝ) ^ 2 ≤ 2.43716 ^ 2 := pow_le_pow_left₀ (exp_pos _).le h4 2
    have : (2.43716 : ℝ) ^ 2 ≤ 5.94 := by norm_num
    linarith
  have hden : (0 : ℝ) < 3 ^ 8 * E0 ^ 4 * c1 ^ 8 := by unfold E0 c1; norm_num
  rw [div_lt_iff₀ hden]
  have : 5 * (5.94 : ℝ) < 0.563 * (3 ^ 8 * E0 ^ 4 * c1 ^ 8) := by unfold E0 c1; norm_num
  linarith

/-! ### Lemma 4.3 -/

/-- **Lemma 4.3, CONDITIONAL ON `RS325`**: for every `N` and `z ≥ 10^8`,
`R₄(𝒜, z^{14.66}) < 0.563 z^{14.66} log⁸ z`. -/
theorem lemma43_general (h325 : RS325) (N : ℕ) {z : ℝ} (hz : (10 : ℝ) ^ 8 ≤ z) :
    R4A N z (z ^ (14.66 : ℝ)) < 0.563 * z ^ (14.66 : ℝ) * log z ^ 8 := by
  have hz0 : 0 < z := by linarith [show (0 : ℝ) < 10 ^ 8 by norm_num]
  have hz1000 : (1000 : ℝ) ≤ z := le_trans (by norm_num) hz
  set L := log z with hLdef
  have hL := log_ge hz
  have hL0 : 0 < L := by linarith
  set D := z ^ (14.66 : ℝ) with hD
  have hD0 : 0 < D := by positivity
  -- step A: R₄ ≤ 5 Σ 8^{ω(d)}
  have hA : R4A N z D ≤ 5 * ∑ s ∈ (primesBelow z).powerset.filter
      (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), (8 : ℝ) ^ s.card := by
    unfold R4A
    rw [mul_sum]
    apply sum_le_sum
    intro s hs
    have hsub : s ⊆ primesBelow z := mem_powerset.mp (mem_filter.mp hs).1
    have hb := rA_bound N (fun p hp => (mem_P (hsub hp)).1) (fun h => (mem_P (hsub h)).2.2 rfl)
    calc (4 : ℝ) ^ s.card * |rA N s| ≤ 4 ^ s.card * (5 * 2 ^ s.card) := by gcongr
      _ = 5 * 8 ^ s.card := by rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]; ring
  -- step B: Rankin
  have hB := rankin14 z hz1000
  -- step C: the reciprocal sum
  have h2z : (2 : ℝ) < z := by linarith
  have hsum : ∑ p ∈ primesBelow z, (1 : ℝ) / p = 1 / 2 + ∑ p ∈ primes5Below z, (1 : ℝ) / p := by
    rw [primesBelow_eq h2z, sum_insert (fun h => (mem_A h).2.2.2 rfl)]
    norm_num
  set Sg := ∑ p ∈ primes5Below z, (1 : ℝ) / p
  set Q := ∏ p ∈ primes5Below z, f2 p
  set q0 := 3 * (exp (-eulerMascheroniConstant) / L * (1 - 1 / (2 * L ^ 2)))
  have hQ : q0 ≤ Q := Q_bound_of h325 (by linarith)
  have hε : c1 ≤ 1 - 1 / (2 * L ^ 2) := by
    unfold c1
    have : 1 / (2 * L ^ 2) ≤ 1 / (2 * 18.4192 ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  have hc1 : 0 < c1 := by unfold c1; norm_num
  set e := exp (-eulerMascheroniConstant) with he
  have he0 : 0 < e := exp_pos _
  have hq0 : 0 < q0 := by
    have : 0 < 1 - 1 / (2 * L ^ 2) := by linarith
    positivity
  have hESg : exp Sg ≤ 1 / q0 := by
    have h := exp_recip_le z
    rw [le_div_iff₀ hq0]
    calc exp Sg * q0 ≤ exp Sg * Q := mul_le_mul_of_nonneg_left hQ (exp_pos _).le
      _ ≤ 1 := h
  -- exp(8 Σ_P 1/p + 8(e^α - 1)) ≤ e^4 e^{8(e^α-1)} / q0^8
  have hE : exp (8 * ∑ p ∈ primesBelow z, (1 : ℝ) / p + 8 * (exp 0.6 - 1)) ≤
      exp 4 * exp (8 * (exp 0.6 - 1)) * (1 / q0) ^ 8 := by
    rw [hsum, show 8 * (1 / 2 + Sg) + 8 * (exp 0.6 - 1) = 4 + 8 * (exp 0.6 - 1) + 8 * Sg by ring,
      exp_add, exp_add]
    have : exp (8 * Sg) = exp Sg ^ 8 := by
      rw [← exp_nat_mul]; norm_num
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (exp_pos _).le hESg 8
  -- 1/q0^8 ≤ L^8 / (3^8 E0^4 c1^8)
  have hq8 : (1 / q0) ^ 8 ≤ L ^ 8 / (3 ^ 8 * E0 ^ 4 * c1 ^ 8) := by
    have hg := gamma_sq_bound
    have hE0 : 0 < E0 := by unfold E0; norm_num
    have he8 : E0 ^ 4 ≤ e ^ 8 := by
      have : (E0) ^ 4 ≤ (e ^ 2) ^ 4 := pow_le_pow_left₀ hE0.le hg 4
      rw [← pow_mul] at this; exact this
    have hlow : 3 ^ 8 * E0 ^ 4 * c1 ^ 8 / L ^ 8 ≤ q0 ^ 8 := by
      have e1 : q0 ^ 8 = 3 ^ 8 * e ^ 8 * (1 - 1 / (2 * L ^ 2)) ^ 8 / L ^ 8 := by
        simp only [q0]; field_simp; rw [he]; ring
      rw [e1]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc8 : c1 ^ 8 ≤ (1 - 1 / (2 * L ^ 2)) ^ 8 := pow_le_pow_left₀ hc1.le hε 8
      have : E0 ^ 4 * c1 ^ 8 ≤ e ^ 8 * (1 - 1 / (2 * L ^ 2)) ^ 8 :=
        mul_le_mul he8 hc8 (by positivity) (by positivity)
      nlinarith
    have hpos : 0 < 3 ^ 8 * E0 ^ 4 * c1 ^ 8 / L ^ 8 := by positivity
    rw [one_div_pow]
    calc 1 / q0 ^ 8 ≤ 1 / (3 ^ 8 * E0 ^ 4 * c1 ^ 8 / L ^ 8) :=
          one_div_le_one_div_of_le hpos hlow
      _ = L ^ 8 / (3 ^ 8 * E0 ^ 4 * c1 ^ 8) := by rw [one_div_div]
  have hK := lemma43_const
  set K := 5 * (exp (-(14.66 * 0.6)) * exp 4 * exp (8 * (exp 0.6 - 1))) /
    (3 ^ 8 * E0 ^ 4 * c1 ^ 8)
  have hfinal : R4A N z D ≤ K * (D * L ^ 8) := by
    calc R4A N z D ≤ 5 * (D * exp (-(14.66 * 0.6)) *
          exp (8 * ∑ p ∈ primesBelow z, (1 : ℝ) / p + 8 * (exp 0.6 - 1))) :=
          hA.trans (mul_le_mul_of_nonneg_left hB (by norm_num))
      _ ≤ 5 * (D * exp (-(14.66 * 0.6)) *
          (exp 4 * exp (8 * (exp 0.6 - 1)) * (L ^ 8 / (3 ^ 8 * E0 ^ 4 * c1 ^ 8)))) := by
          gcongr
          exact hE.trans (mul_le_mul_of_nonneg_left hq8 (by positivity))
      _ = K * (D * L ^ 8) := by simp only [K]; ring
  have hDL : 0 < D * L ^ 8 := by positivity
  have := mul_lt_mul_of_pos_right hK hDL
  linarith

/-- **`Lemma43 R4paper`, CONDITIONAL ON `RS325`**: Lemma 4.3 for the paper's `R₄`. -/
theorem lemma43_of_RS325 (h325 : RS325) : Lemma43 R4paper := by
  intro N hN
  exact (lemma43_general h325 N (z_ge_1e8 hN)).le

/-! ### Wiring -/

/-- **`Case3Sieve`, CONDITIONAL ON `Thm21Case3 R4paper` and `RS325` only.** -/
theorem case3Sieve_of_RS43 (h21 : Thm21Case3 R4paper) (h325 : RS325) : Case3Sieve :=
  case3Sieve_of_RS R4paper h21 h325 (lemma43_of_RS325 h325)

/-- **Theorem 1.2, `Ω(ab) ≤ 33` for every `N ≥ 2`, CONDITIONAL ON `GapTable`, `Case2Sieve`,
`Case2Table`, `Thm21Case3 R4paper` and `RS325`.** -/
theorem theorem1_2_of_inputs_RS43 (hG : GapTable) (hs : Case2Sieve) (ht : Case2Table)
    (h21 : Thm21Case3 R4paper) (h325 : RS325) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N :=
  theorem1_2_of_inputs_RS hG hs ht R4paper h21 h325 (lemma43_of_RS325 h325)

/-! ### Vacuity check -/

/-- At `N = 7`, `aₙ = n(7 - n)/2 = 3, 5, 6, 6, 5, 3`, `I₃ = {2, 5}`, `X = 2`, `𝒜₂ = ∅`, so
`r₂ = 0 - 2 · ½ = -1`: `r_d` is not identically zero. -/
theorem rA_example : rA 7 {2} = -1 := by
  unfold rA gS Xcount Ad3 CampbellCase2.g
  have h1 : ((Icc 1 (7 - 1)).filter (fun n => ¬ 3 ∣ aSeq 7 n ∧
      (∏ p ∈ ({2} : Finset ℕ), p) ∣ aSeq 7 n)).card = 0 := by decide
  have h2 : ((Icc 1 (7 - 1)).filter (fun n => ¬ 3 ∣ aSeq 7 n)).card = 2 := by decide
  rw [h1, h2]
  norm_num

end LeanLab.AlmostPrimes.CampbellLemma43
