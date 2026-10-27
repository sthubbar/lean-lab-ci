/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The elementary singular series lower bound used on page 357.
The singular series is the existing absolutely convergent ternary series.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.EulerLower
import LeanLab.HardyLittlewood1923.U1438Sing
import LeanLab.Zinoviev1997.ArcInputs

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology
open LeanLab.PNTPort.Vinogradov
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.CircleOrth
open scoped ArithmeticFunction.Moebius

/-- The series sigma written on page 352, with residues from zero through q minus one. -/
noncomputable def paperSigma (N : ℕ) : ℂ :=
  ∑' q : ℕ, (μ q : ℂ) / (Nat.totient q : ℂ) ^ 3 *
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ee ((N : ℝ) * a / q)

/-- The paper's exponential series agrees with the existing real singular series. -/
theorem paperSigma_eq (N : ℕ) : paperSigma N = (sing3 N : ℂ) := by
  rw [sing3_eq_tsum_fS, Complex.ofReal_tsum]
  unfold paperSigma
  apply tsum_congr
  intro q
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst q
    simp
  · have he : ∀ x : ℝ, ee x = LeanLab.PNTPort.LargeSieve.e x := by
      intro x
      unfold ee LeanLab.PNTPort.LargeSieve.e
      congr 1
      push_cast
      ring
    simp_rw [he]
    rw [ramanujan_sum hq N, fS_apply hq N]
    push_cast
    ring

/-- Each worst factor lies in the unit interval at positive indices. -/
theorem worstFactor_mem (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ worstFactor k ∧ worstFactor k ≤ 1 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (1 : ℝ) ≤ (2 * (k : ℝ)) ^ 2 := by nlinarith
  have hh : 1 / (2 * (k : ℝ)) ^ 2 ≤ 1 :=
    (div_le_one (by positivity)).mpr hd
  have hl : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) ^ 2 := by positivity
  constructor <;> unfold worstFactor <;> linarith

/-- The finite Euler product is uniformly at least 39/32 for odd N. -/
theorem singular_euler_lower {N : ℕ} (hN : Odd N) {P : ℕ} (hP : 2 ≤ P) :
    (39 : ℝ) / 32 ≤ ∏ p ∈ Nat.primesLE P, (1 + fS N p) := by
  have h2 : 2 ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨hP, Nat.prime_two⟩
  let T := (Nat.primesLE P).erase 2
  let U := T.image (fun p => p / 2)
  have hpodd : ∀ p ∈ T, Odd p := by
    intro p hp
    have hh := (Finset.mem_erase.mp hp)
    have hprime := (Nat.mem_primesLE.mp hh.2).2
    exact hprime.odd_of_ne_two hh.1
  have hpdecomp : ∀ p ∈ T, 2 * (p / 2) + 1 = p := by
    intro p hp
    obtain ⟨k, hk⟩ := hpodd p hp
    omega
  have hU : U ⊆ Finset.Icc 1 P := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hh := Nat.mem_primesLE.mp (Finset.mem_erase.mp hp).2
    have hd := hpdecomp p hp
    have hp2 := hh.2.two_le
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have heq : ∏ k ∈ U, worstFactor k = ∏ p ∈ T, worstFactor (p / 2) := by
    change (∏ k ∈ T.image (fun p => p / 2), worstFactor k) = _
    rw [Finset.prod_image]
    intro a ha b hb hab
    change a / 2 = b / 2 at hab
    have hda := hpdecomp a ha
    have hdb := hpdecomp b hb
    omega
  have hA : ∏ k ∈ Finset.Icc 1 P, worstFactor k ≤ ∏ k ∈ U, worstFactor k :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hU
      (fun k hk => (worstFactor_mem k (Finset.mem_Icc.mp hk).1).1)
      (fun k hk _ => (worstFactor_mem k (Finset.mem_Icc.mp hk).1).2)
  have hB : ∏ k ∈ U, worstFactor k ≤ ∏ p ∈ T, (1 + fS N p) := by
    rw [heq]
    apply Finset.prod_le_prod₀
    · intro p hp
      have : 1 ≤ p / 2 := by
        have := hpdecomp p hp
        have := (Nat.mem_primesLE.mp (Finset.mem_erase.mp hp).2).2.two_le
        omega
      exact (worstFactor_mem _ this).1
    · intro p hp
      have hprime := (Nat.mem_primesLE.mp (Finset.mem_erase.mp hp).2).2
      have hd : (p : ℝ) - 1 = 2 * ((p / 2 : ℕ) : ℝ) := by
        have hh := congrArg (fun n : ℕ => (n : ℝ)) (hpdecomp p hp)
        push_cast at hh
        linarith
      simpa only [worstFactor, hd] using one_add_fS_ge hprime N
  have hbase := worstFactor_product P (by omega)
  rw [← Finset.insert_erase h2, Finset.prod_insert (Finset.notMem_erase 2 _), fS_two_odd hN]
  change (39 : ℝ) / 32 ≤ (1 + 1) * ∏ p ∈ T, (1 + fS N p)
  linarith

/-- The actual convergent ternary singular series has the same uniform lower bound. -/
theorem singular_series_lower {N : ℕ} (hN : Odd N) :
    (39 : ℝ) / 32 ≤ sing3 N := by
  have hbound : ∀ Q : ℕ, 2 ≤ Q →
      (39 : ℝ) / 32 - 2 * (Real.exp 8 / Real.sqrt Q) ≤ sing3 N := by
    intro Q hQ
    have hprod := singular_euler_lower hN hQ
    have he := LeanLab.VanDerCorput1939.abs_sum_fS_sub_euler N (by omega : 1 ≤ Q)
    have hs := abs_partial_sub_sing3 N (by omega : 1 ≤ Q)
    simp only [singTerm_eq_fS] at hs
    have h1 := (abs_le.mp he).1
    have h2 := (abs_le.mp hs).2
    linarith
  have hlim : Tendsto (fun Q : ℕ => (39 : ℝ) / 32 -
      2 * (Real.exp 8 / Real.sqrt Q)) atTop (𝓝 ((39 : ℝ) / 32)) := by
    simpa using tendsto_const_nhds.sub (tendsto_exp8_div_sqrt.const_mul 2)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  exact hbound Q hQ

/-- The lower bound on page 357 follows without a cited numerical hypothesis. -/
theorem singular_series_gt {N : ℕ} (hN : Odd N) : SingularSeriesLower (sing3 N) := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hnum : 12 / Real.pi ^ 2 < (39 : ℝ) / 32 := by
    rw [div_lt_iff₀ (by positivity : 0 < Real.pi ^ 2)]
    nlinarith [Real.pi_pos]
  exact hnum.trans_le (singular_series_lower hN)

/-- Theorem 3.4, CONDITIONAL ON only the two cited arc estimates. -/
theorem zinoviev_of_two_lemmas (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (hodd : Odd N)
    (h21 : Lemma21Input N) (h32 : Lemma32Input N (sing3 N)) : IsTernarySum N :=
  zinoviev_of_lemmas N hN (sing3 N) h21 h32 (singular_series_gt hodd)

end LeanLab.Zinoviev1997
