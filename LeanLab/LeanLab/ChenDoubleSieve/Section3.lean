import LeanLab.ChenDoubleSieve.Lemma41Uk
import LeanLab.ChenDoubleSieve.Statements

/-!
# Wu 2004 Section 3: the double sieve functions

Source: https://arxiv.org/pdf/0705.1652, pages 9 and 10, equations 3.1 to 3.4.
Weights are represented by prime tuples. Repeated products retain their multiplicity.
The two sieve functions F and f are parameters. Their analytic properties are not asserted.
Extended real suprema retain the paper's possible value minus infinity.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04

/-- Wu's level of distribution. -/
def Q (δ : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 2 - δ)

/-- Wu's lower endpoint for the prime intervals. -/
def W (δ : ℝ) (k N : ℕ) : ℝ := (N : ℝ) ^ (δ ^ (k + 1))

/-- An admissible tuple presentation of a member of U_k. -/
structure UkData (δ : ℝ) (k N i : ℕ) (V : Fin i → ℝ) (Δ : ℝ) : Prop where
  count : i ≤ k
  delta_lower : 1 + (Real.log N)⁻¹ ^ 4 ≤ Δ
  delta_upper : Δ < 1 + 2 * (Real.log N)⁻¹ ^ 4
  order : Antitone V
  lower : ∀ j, W δ k N ≤ V j
  level : ∀ j, (∏ l ∈ univ.filter (· < j), V l) * V j ^ 2 ≤ Q δ N

/-- The exact prime difference sequence, including p = N when N is prime. -/
def A (N : ℕ) : Finset ℕ :=
  ((range (N + 1)).filter Nat.Prime).image (fun p => N - p)

/-- The product attached to one prime tuple. -/
def modulus {i : ℕ} (t : Fin i → ℕ) : ℕ := ∏ j, t j

/-- Phi, with the convolution sum expanded as a sum over tuples. -/
def Phi (δ : ℝ) (N i : ℕ) (V : Fin i → ℝ) (Δ s : ℝ) : ℝ :=
  ∑ t ∈ Wu41.Tset N i V Δ,
    (Wu41.S (A N) (modulus t) (modulus t * N) ((Q δ N / modulus t) ^ (1 / s)) : ℝ)

/-- The logarithmic integral with lower endpoint 2. -/
def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- The weighted normalizer Theta in Section 3. -/
def Theta (δ : ℝ) (N i : ℕ) (V : Fin i → ℝ) (Δ : ℝ) : ℝ :=
  4 * li N * ∑ t ∈ Wu41.Tset N i V Δ,
    CN (modulus t * N) / ((Nat.totient (modulus t) : ℝ) * Real.log (Q δ N / modulus t))

/-- A and a from equation 3.2. -/
def normalized (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * F s / (2 * Real.exp Real.eulerMascheroniConstant)

/-- A real candidate for the upper double sieve correction. -/
def UpperCandidate (F : ℝ → ℝ) (δ : ℝ) (k N₀ : ℕ) (s c : ℝ) : Prop :=
  ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → Even N → ∀ i V Δ, UkData δ k N i V Δ →
    Phi δ N i V Δ s ≤ (normalized F s - c) * Theta δ N i V Δ

/-- A real candidate for the lower double sieve correction. -/
def LowerCandidate (f : ℝ → ℝ) (δ : ℝ) (k N₀ : ℕ) (s c : ℝ) : Prop :=
  ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → Even N → ∀ i V Δ, UkData δ k N i V Δ →
    (normalized f s + c) * Theta δ N i V Δ ≤ Phi δ N i V Δ s

/-- The paper's H_{k,N0}, with minus infinity for an empty candidate set. -/
def Hkn (F : ℝ → ℝ) (δ : ℝ) (k N₀ : ℕ) (s : ℝ) : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | UpperCandidate F δ k N₀ s c})

/-- The paper's h_{k,N0}. -/
def hkn (f : ℝ → ℝ) (δ : ℝ) (k N₀ : ℕ) (s : ℝ) : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | LowerCandidate f δ k N₀ s c})

/-- The increasing threshold limits. Finiteness requires the analytic sieve inputs. -/
def Hk (F : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) : EReal := ⨆ N₀ : ℕ, Hkn F δ k N₀ s

def hk (f : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) : EReal := ⨆ N₀ : ℕ, hkn f δ k N₀ s

/-- The final correction H, with positive k encoded by k + 1. -/
def H (F : ℝ → ℝ) (δ s : ℝ) : EReal := ⨅ k : ℕ, Hk F δ (k + 1) s

/-- The final correction h. -/
def h (f : ℝ → ℝ) (δ s : ℝ) : EReal := ⨅ k : ℕ, hk f δ (k + 1) s

/-- Raising the threshold only removes constraints. -/
theorem upperCandidate_threshold {F : ℝ → ℝ} {δ s c : ℝ} {k N₀ N₁ : ℕ}
    (hN : N₀ ≤ N₁) (hc : UpperCandidate F δ k N₀ s c) :
    UpperCandidate F δ k N₁ s c := by
  intro N hNN h2 hEven i V Δ hU
  exact hc N (hN.trans hNN) h2 hEven i V Δ hU

/-- The corresponding lower bound statement. -/
theorem lowerCandidate_threshold {f : ℝ → ℝ} {δ s c : ℝ} {k N₀ N₁ : ℕ}
    (hN : N₀ ≤ N₁) (hc : LowerCandidate f δ k N₀ s c) :
    LowerCandidate f δ k N₁ s c := by
  intro N hNN h2 hEven i V Δ hU
  exact hc N (hN.trans hNN) h2 hEven i V Δ hU

/-- H_{k,N0} is increasing in N0 under its defining supremum. -/
theorem Hkn_mono_threshold (F : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) :
    Monotone (fun N₀ => Hkn F δ k N₀ s) := by
  intro N₀ N₁ hN
  apply sSup_le_sSup
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, upperCandidate_threshold hN hc, rfl⟩

/-- h_{k,N0} is increasing in N0 under its defining supremum. -/
theorem hkn_mono_threshold (f : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) :
    Monotone (fun N₀ => hkn f δ k N₀ s) := by
  intro N₀ N₁ hN
  apply sSup_le_sSup
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, lowerCandidate_threshold hN hc, rfl⟩

/-- The empty tuple is admissible whenever Delta is in the stated interval. -/
theorem empty_UkData (δ : ℝ) (k N : ℕ) {Δ : ℝ}
    (hlo : 1 + (Real.log N)⁻¹ ^ 4 ≤ Δ)
    (hhi : Δ < 1 + 2 * (Real.log N)⁻¹ ^ 4) :
    UkData δ k N 0 Fin.elim0 Δ := by
  refine ⟨Nat.zero_le _, hlo, hhi, ?_, ?_, ?_⟩
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j

/-- Concrete nonempty presentation family at even N = 16. -/
theorem empty_UkData_instance (δ : ℝ) (k : ℕ) :
    UkData δ k 16 0 Fin.elim0 (1 + 3 / 2 * (Real.log 16)⁻¹ ^ 4) := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (Real.log (16 : ℝ))⁻¹ ^ 4 := by positivity
  apply empty_UkData <;> norm_num only [Nat.cast_ofNat] <;> linarith

/-- The lattice supremum Hk is the threshold limit printed on page 10. -/
theorem Hkn_tendsto (F : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) :
    Filter.Tendsto (fun N₀ => Hkn F δ k N₀ s) Filter.atTop (nhds (Hk F δ k s)) :=
  tendsto_atTop_iSup (Hkn_mono_threshold F δ k s)

/-- The analogous threshold limit for hk. -/
theorem hkn_tendsto (f : ℝ → ℝ) (δ : ℝ) (k : ℕ) (s : ℝ) :
    Filter.Tendsto (fun N₀ => hkn f δ k N₀ s) Filter.atTop (nhds (hk f δ k s)) :=
  tendsto_atTop_iSup (hkn_mono_threshold f δ k s)

/-- Lemma 3.1's inclusion for tuple presentations. -/
theorem UkData_succ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {k N i : ℕ} {V : Fin i → ℝ} {Δ : ℝ} (hN : 2 ≤ N) (hU : UkData δ k N i V Δ) :
    UkData δ (k + 1) N i V Δ := by
  refine ⟨hU.count.trans (Nat.le_succ k), hU.delta_lower, hU.delta_upper, hU.order, ?_, hU.level⟩
  intro j
  apply le_trans ?_ (hU.lower j)
  unfold W
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.trans' (by omega : 1 ≤ 2))
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg hδ0 _) hδ1

/-- More tuple presentations impose more upper constraints. -/
theorem Hkn_antitone_k (F : ℝ → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (N₀ : ℕ) (s : ℝ) : Antitone (fun k => Hkn F δ k N₀ s) := by
  apply antitone_nat_of_succ_le
  intro k
  apply sSup_le_sSup
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  intro N hNN h2 hEven i V Δ hU
  exact hc N hNN h2 hEven i V Δ (UkData_succ hδ0 hδ1 h2 hU)

/-- More tuple presentations impose more lower constraints. -/
theorem hkn_antitone_k (f : ℝ → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (N₀ : ℕ) (s : ℝ) : Antitone (fun k => hkn f δ k N₀ s) := by
  apply antitone_nat_of_succ_le
  intro k
  apply sSup_le_sSup
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  intro N hNN h2 hEven i V Δ hU
  exact hc N hNN h2 hEven i V Δ (UkData_succ hδ0 hδ1 h2 hU)

/-- The decreasing k limit defining H exists in the extended reals. -/
theorem Hk_tendsto (F : ℝ → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (s : ℝ) :
    Filter.Tendsto (fun k => Hk F δ (k + 1) s) Filter.atTop (nhds (H F δ s)) := by
  apply tendsto_atTop_iInf
  intro k l hkl
  exact iSup_mono fun N₀ => Hkn_antitone_k F hδ0 hδ1 N₀ s (Nat.add_le_add_right hkl 1)

/-- The decreasing k limit defining h exists in the extended reals. -/
theorem hk_tendsto (f : ℝ → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (s : ℝ) :
    Filter.Tendsto (fun k => hk f δ (k + 1) s) Filter.atTop (nhds (h f δ s)) := by
  apply tendsto_atTop_iInf
  intro k l hkl
  exact iSup_mono fun N₀ => hkn_antitone_k f hδ0 hδ1 N₀ s (Nat.add_le_add_right hkl 1)

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.upperCandidate_threshold
#print axioms LeanLab.ChenDoubleSieve.Wu04.lowerCandidate_threshold
#print axioms LeanLab.ChenDoubleSieve.Wu04.Hkn_mono_threshold
#print axioms LeanLab.ChenDoubleSieve.Wu04.hkn_mono_threshold
#print axioms LeanLab.ChenDoubleSieve.Wu04.empty_UkData

#print axioms LeanLab.ChenDoubleSieve.Wu04.empty_UkData_instance

#print axioms LeanLab.ChenDoubleSieve.Wu04.Hkn_tendsto

#print axioms LeanLab.ChenDoubleSieve.Wu04.hkn_tendsto

#print axioms LeanLab.ChenDoubleSieve.Wu04.UkData_succ

#print axioms LeanLab.ChenDoubleSieve.Wu04.Hkn_antitone_k

#print axioms LeanLab.ChenDoubleSieve.Wu04.hkn_antitone_k

#print axioms LeanLab.ChenDoubleSieve.Wu04.Hk_tendsto

#print axioms LeanLab.ChenDoubleSieve.Wu04.hk_tendsto
