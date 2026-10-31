import LeanLab.RieselVaughan1983.Lemma1Large

/-!
# The Stieltjes constant `γ₁` as a Lean constant, and Lemma 1 for `x ≥ 16` without `hL`

Unit U-1397, PC run 20261021T1103Z-29422, paper P0032 Riesel-Vaughan 1983, track T1.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
KNOWN mathematics.

`cseq_step` of Lemma1Large gives `|c_{k+1} − c_k| ≤ 1/(10k) − 1/(10(k+1))` for `k ≥ 2`, so
`u_j = c_{j+2} − 1/(10(j+2))` increases and is bounded above by `c_2 + 1/20`. We define
`stieltjes1` as its supremum and prove that `∑_{m≤n} log m / m − ½ log² n` tends to it, which is
the definition (2.1) of P0032 p. 46 at `k = 1`.

PROVED, no cited input:
* `gamma1Seq_mono`, `gamma1Seq_le`, `cseq_tendsto_stieltjes1`.
* `stieltjes1_hL`: the hypothesis `hL` of Lemma1Large at `g1 = stieltjes1`.
* `lemma1_ge16_stieltjes1`: Lemma 1 for all `x ≥ 16` at `g1 = stieltjes1`.
* `sigma_bound_stieltjes1`: `|c_n − γ₁| ≤ 1/(10n)` for `n ≥ 2`.
CONDITIONAL, counted apart:
* `lemma1_stieltjes1`: `Lemma1P stieltjes1`, CONDITIONAL ON the CITED range
  `−0.0729 < γ₁ < −0.07` only; `hL` is discharged.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset Filter Topology

/-- `u_j = c_{j+2} − 1/(10(j+2))`. -/
noncomputable def gamma1Seq (j : ℕ) : ℝ := cseq (j + 2) - 1 / (10 * ((j : ℝ) + 2))

/-- The Stieltjes constant `γ₁`, as the supremum of the increasing bounded sequence `u_j`. -/
noncomputable def stieltjes1 : ℝ := ⨆ j : ℕ, gamma1Seq j

lemma gamma1Seq_mono : Monotone gamma1Seq := by
  refine monotone_nat_of_le_succ (fun j => ?_)
  have h := cseq_step (j + 2) (by omega)
  rw [abs_le] at h
  unfold gamma1Seq
  push_cast at h ⊢
  have e : ((j : ℝ) + 1 + 2) = (j + 2) + 1 := by ring
  rw [e]; linarith [h.1]

lemma gamma1Upper_anti :
    Antitone (fun j : ℕ => cseq (j + 2) + 1 / (10 * ((j : ℝ) + 2))) := by
  refine antitone_nat_of_succ_le (fun j => ?_)
  have h := cseq_step (j + 2) (by omega)
  rw [abs_le] at h
  push_cast at h ⊢
  have e : ((j : ℝ) + 1 + 2) = (j + 2) + 1 := by ring
  rw [e]; linarith [h.2]

/-- `u_j ≤ c_2 + 1/20` for every `j`. -/
lemma gamma1Seq_le (j : ℕ) : gamma1Seq j ≤ cseq 2 + 1 / 20 := by
  have h : cseq (j + 2) + 1 / (10 * ((j : ℝ) + 2)) ≤ cseq (0 + 2) + 1 / (10 * (((0 : ℕ) : ℝ) + 2)) :=
    gamma1Upper_anti (Nat.zero_le j)
  have e : (1 : ℝ) / (10 * (((0 : ℕ) : ℝ) + 2)) = 1 / 20 := by norm_num
  rw [e] at h
  unfold gamma1Seq
  have : (0 : ℝ) ≤ 1 / (10 * ((j : ℝ) + 2)) := by positivity
  linarith

lemma gamma1Seq_bdd : BddAbove (Set.range gamma1Seq) :=
  ⟨cseq 2 + 1 / 20, by rintro _ ⟨j, rfl⟩; exact gamma1Seq_le j⟩

lemma gamma1Seq_tendsto : Tendsto gamma1Seq atTop (𝓝 stieltjes1) :=
  tendsto_atTop_ciSup gamma1Seq_mono gamma1Seq_bdd

/-- `c_n → γ₁`. -/
lemma cseq_tendsto_stieltjes1 : Tendsto cseq atTop (𝓝 stieltjes1) := by
  have h := gamma1Seq_tendsto.add (tendsto_inv_ten 2)
  rw [add_zero] at h
  have h2 : Tendsto (fun j : ℕ => cseq (j + 2)) atTop (𝓝 stieltjes1) :=
    h.congr (fun j => by unfold gamma1Seq; ring)
  exact (tendsto_add_atTop_iff_nat 2).mp h2

/-- **`hL` at `g1 = stieltjes1`, PROVED.** `∑_{m≤n} log m / m − ½ log² n → γ₁`. -/
theorem stieltjes1_hL :
    Tendsto (fun n : ℕ => Lsum n - Real.log n ^ 2 / 2) atTop (𝓝 stieltjes1) := by
  have h0 : Tendsto (fun n : ℕ => Real.log n / (2 * n)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun n => ?_)
    simp
  have := cseq_tendsto_stieltjes1.add h0
  rw [add_zero] at this
  exact this.congr (fun n => by unfold cseq; ring)

/-- `|c_n − γ₁| ≤ 1/(10n)` for `n ≥ 2`, PROVED. -/
theorem sigma_bound_stieltjes1 (n : ℕ) (hn : 2 ≤ n) :
    |cseq n - stieltjes1| ≤ 1 / (10 * (n : ℝ)) :=
  sigma_bound stieltjes1 stieltjes1_hL n hn

/-- **P0032 Lemma 1 for `x ≥ 16` at `γ₁ = stieltjes1`, PROVED, no cited input.** -/
theorem lemma1_ge16_stieltjes1 (x : ℝ) (hx : 16 ≤ x) :
    |lem1E stieltjes1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) :=
  lemma1_ge16 stieltjes1 stieltjes1_hL x hx

/-- **P0032 Lemma 1, `Lemma1P stieltjes1`**, CONDITIONAL ON the CITED range
`−0.0729 < γ₁ < −0.07` only. -/
theorem lemma1_stieltjes1 (hg1 : -729 / 10000 < stieltjes1) (hg1' : stieltjes1 < -7 / 100) :
    Lemma1P stieltjes1 :=
  lemma1_full stieltjes1 hg1 hg1' stieltjes1_hL

end LeanLab.RieselVaughan1983
