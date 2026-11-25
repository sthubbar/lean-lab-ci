import Mathlib
import LeanLab.AlmostPrimes.Decomp1528b

/-!
Shared core for the prime pair and prime quadruple Riemann sum limits of
Wu 2004 arXiv 0705.1652, page 39 equation 10.5 and page 41 equations 10.9 to 10.12.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
The measure putting mass 1/p at the point log p / log N converges on compact
subintervals of (0,1] to dt/t, by Mertens' second theorem. This file holds that
one dimensional limit, proved from the lab's explicit Mertens theorem, the sandwich reduction that passes from a set
squeezed between an open and a closed region to the closed region, proved, and a
coordinate lemma. AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.PrimeRiemannCore

/-- Wu 2004 page 39, the one dimensional reciprocal prime mass of the primes p at most N
with log p / log N in the closed interval a to b; Mertens' second theorem gives its limit
log b minus log a, Wu page 39 line before equation 10.5. -/
def prcMertens (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter
      (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc a b),
    1 / (p : ℝ)

/-- Coordinate lemma: N to the sigma at most p iff sigma at most log p / log N. -/
theorem prc_rpow_le_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (N : ℝ) ^ σ ≤ p ↔ σ ≤ log (p : ℝ) / log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hL, rpow_def_of_pos hN0, ← le_log_iff_exp_le hp0, mul_comm]

/-- Coordinate lemma: p at most N to the sigma iff log p / log N at most sigma. -/
theorem prc_le_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) ≤ (N : ℝ) ^ σ ↔ log (p : ℝ) / log N ≤ σ := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hL, ← log_le_log_iff hp0 (rpow_pos_of_pos hN0 σ), log_rpow hN0]

/-- Wu 2004 page 39, Mertens' second theorem in the scale t equal log p / log N:
for 0 less than a at most b at most 1 the reciprocal prime mass of the primes with
log p / log N in the interval a to b tends to log b minus log a, the mass of dt/t.
Proved from the lab's explicit Mertens `LeanLab.AlmostPrimes.Decomp1528b.mertens2_block`
with y equal N to the a and x equal N to the b, error 4 / log y, plus the single possible
endpoint prime p equal N to the a. -/
theorem prc_mertens_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Tendsto (fun N : ℕ => prcMertens a b N) atTop (𝓝 (log b - log a)) := by
  have hLt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 5 / (a * log (N : ℝ))) atTop (𝓝 0) := by
    have := ((hLt.const_mul_atTop ha).inv_tendsto_atTop).const_mul 5
    simpa [div_eq_mul_inv] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hLt.eventually_ge_atTop (log 2 / a), eventually_ge_atTop 2] with N hNl hN
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hly : log ((N : ℝ) ^ a) = a * log N := log_rpow hN0 a
  have hlx : log ((N : ℝ) ^ b) = b * log N := log_rpow hN0 b
  have hy2 : 2 ≤ (N : ℝ) ^ a := by
    have h1 : log 2 ≤ a * log N := by rw [div_le_iff₀ ha] at hNl; linarith
    rw [← hly] at h1
    exact (log_le_log_iff (by norm_num) (rpow_pos_of_pos hN0 a)).mp h1
  have hyx : (N : ℝ) ^ a ≤ (N : ℝ) ^ b := rpow_le_rpow_of_exponent_le hN1 hab
  have hxN : (N : ℝ) ^ b ≤ N := by
    calc (N : ℝ) ^ b ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hN1 hb1
      _ = N := rpow_one _
  have hMB := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy2 hyx
  have hlogdiff : log (log ((N : ℝ) ^ b)) - log (log ((N : ℝ) ^ a)) = log b - log a := by
    rw [hlx, hly, log_mul (ha.trans_le hab).ne' hL.ne', log_mul ha.ne' hL.ne']; ring
  rw [hlogdiff, hly] at hMB
  set y : ℝ := (N : ℝ) ^ a with hy
  set x : ℝ := (N : ℝ) ^ b with hx
  set G := (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime with hG
  set F := (Finset.range (N + 1)).filter
      (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc a b) with hF
  have hGF : G ⊆ F := by
    intro p hp
    simp only [G, F, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, Set.mem_Icc] at hp ⊢
    obtain ⟨⟨h1, h2⟩, hpp⟩ := hp
    have hp1 : y < p := (Nat.floor_lt (by linarith)).mp h1
    have hp2 : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp h2
    have hpN : (p : ℝ) ≤ N := hp2.trans hxN
    have hpN' : p ≤ N := by exact_mod_cast hpN
    exact ⟨Nat.lt_succ_of_le hpN', hpp, (prc_rpow_le_iff hN hpp.pos a).mp hp1.le,
      (prc_le_rpow_iff hN hpp.pos b).mp hp2⟩
  have hFG : F \ G ⊆ {⌈y⌉₊} := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpF, hpG⟩ := hp
    simp only [G, F, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range,
      Set.mem_Icc] at hpF hpG
    obtain ⟨-, hpp, h1, h2⟩ := hpF
    have hp1 : y ≤ p := (prc_rpow_le_iff hN hpp.pos a).mpr h1
    have hp2 : (p : ℝ) ≤ x := (prc_le_rpow_iff hN hpp.pos b).mpr h2
    have h2' : p ≤ ⌊x⌋₊ := Nat.le_floor hp2
    have h3 : ¬ ⌊y⌋₊ < p := fun h => hpG ⟨⟨h, h2'⟩, hpp⟩
    have h4 : (p : ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).mp (not_lt.mp h3)
    have hpy : (p : ℝ) = y := le_antisymm h4 hp1
    rw [Finset.mem_singleton, ← hpy, Nat.ceil_natCast]
  have hsum : prcMertens a b N = ∑ p ∈ G, 1 / (p : ℝ) + ∑ p ∈ F \ G, 1 / (p : ℝ) := by
    rw [add_comm, Finset.sum_sdiff hGF]; rfl
  have hE0 : 0 ≤ ∑ p ∈ F \ G, 1 / (p : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hE1 : ∑ p ∈ F \ G, 1 / (p : ℝ) ≤ 1 / y := by
    calc ∑ p ∈ F \ G, 1 / (p : ℝ) ≤ ∑ p ∈ ({⌈y⌉₊} : Finset ℕ), 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => by positivity)
      _ = 1 / (⌈y⌉₊ : ℝ) := Finset.sum_singleton _ _
      _ ≤ 1 / y := one_div_le_one_div_of_le (by linarith) (Nat.le_ceil y)
  have hy1 : 1 / y ≤ 1 / (a * log N) := by
    rw [← hly]
    exact one_div_le_one_div_of_le (log_pos (by linarith))
      ((log_le_sub_one_of_pos (by linarith)).trans (by linarith))
  have h5 : 5 / (a * log N) = 4 / (a * log N) + 1 / (a * log N) := by ring
  rw [Real.norm_eq_abs, hsum, h5]
  rw [abs_le] at hMB ⊢
  constructor <;> linarith [hMB.1, hMB.2]

/-- Wu 2004 page 39 equation 10.5, the comparison step: a sum over sets S N squeezed
between an open region set O N and a closed region set C N has the limit of the sum
over C N, once the absolute mass of C N minus O N tends to zero. -/
theorem prc_sandwich {α : Type*} [DecidableEq α] (C O S : ℕ → Finset α) (F : ℕ → α → ℝ)
    {I : ℝ} (hsub : ∀ᶠ N in atTop, S N ⊆ C N) (hsup : ∀ᶠ N in atTop, O N ⊆ S N)
    (hC : Tendsto (fun N => ∑ q ∈ C N, F N q) atTop (𝓝 I))
    (hB : Tendsto (fun N => ∑ q ∈ C N \ O N, |F N q|) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ q ∈ S N, F N q) atTop (𝓝 I) := by
  have hE : Tendsto (fun N => ∑ q ∈ C N, F N q - ∑ q ∈ S N, F N q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [hsub, hsup] with N h1 h2
    rw [← Finset.sum_sdiff h1, add_sub_cancel_right, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset_sdiff le_rfl h2)
      (fun _ _ _ => abs_nonneg _)
  have h := hC.sub hE
  simp only [sub_sub_cancel, sub_zero] at h
  exact h

/-- Coordinate lemma: for N at least 2 and p positive, log p / log N at most 1 forces
p at most N. -/
theorem prc_lt_succ_of_le_one {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    (h : log (p : ℝ) / log N ≤ 1) : p < N + 1 := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [div_le_one hL, log_le_log_iff hp0 hN0] at h
  have : p ≤ N := by exact_mod_cast h
  omega

end LeanLab.ChenDoubleSieve.PrimeRiemannCore
