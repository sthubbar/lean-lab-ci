import LeanLab.PerelliPintz1992.Decomp97
import Mathlib

namespace LeanLab.PerelliPintz1992.DecompJ288
open Real ArithmeticFunction MeasureTheory Set Filter Topology Decomp97

/-! ## 1. `Q N ≥ 1` for `N ≥ 4` -/

private lemma farey_sqrt_four : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [← Real.sqrt_eq_rpow]
  norm_num

private lemma farey_one_le_Q {N : ℕ} (hN : 4 ≤ N) : 1 ≤ Q N := by
  have hN' : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmono : (4 : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hN' (by norm_num)
  rw [farey_sqrt_four] at hmono
  unfold Q
  linarith

/-! ## 2. Dirichlet: a reduced Farey fraction of denominator `≤ ⌊Q⌋₊` close to `x ∈ (1/Q, 1]` -/

private lemma farey_exists_arc {x QQ : ℝ} (hQ1 : 1 ≤ QQ) (hx0 : 1 / QQ < x) (hx1 : x ≤ 1) :
    ∃ a q : ℕ, 1 ≤ q ∧ q ≤ ⌊QQ⌋₊ ∧ a ≤ q ∧ a.Coprime q ∧
      |x - (a : ℝ) / q| < 1 / ((q : ℝ) * QQ) := by
  have hn : 0 < ⌊QQ⌋₊ := Nat.le_floor (by simpa using hQ1)
  obtain ⟨t, ht, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hn
  have hQQpos : (0 : ℝ) < QQ := lt_of_lt_of_le zero_lt_one hQ1
  have hdenpos : (0 : ℝ) < (t.den : ℝ) := by exact_mod_cast t.pos
  have hden1 : (1 : ℝ) ≤ (t.den : ℝ) := by exact_mod_cast t.pos
  have hQQlt : QQ < ((⌊QQ⌋₊ : ℕ) : ℝ) + 1 := by simpa using Nat.lt_succ_floor QQ
  have hstrict : |x - (t : ℝ)| < 1 / ((t.den : ℝ) * QQ) := by
    refine lt_of_le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using ht) ?_
    rw [one_div, one_div, inv_lt_inv₀ (by positivity) (mul_pos hdenpos hQQpos)]
    have := mul_lt_mul_of_pos_right hQQlt hdenpos
    linarith
  have htcast : (t : ℝ) = (t.num : ℝ) / (t.den : ℝ) := Rat.cast_def t
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have h1 : x - 1 / ((t.den : ℝ) * QQ) < (t : ℝ) := by
      have := (abs_lt.mp hstrict).2
      linarith
    have h2 : 1 / QQ - 1 / ((t.den : ℝ) * QQ) = ((t.den : ℝ) - 1) / ((t.den : ℝ) * QQ) := by
      field_simp
    have h3 : (0 : ℝ) ≤ ((t.den : ℝ) - 1) / ((t.den : ℝ) * QQ) := by
      apply div_nonneg _ (le_of_lt (mul_pos hdenpos hQQpos))
      linarith
    linarith
  have hnum0 : 0 ≤ t.num := by
    have hmul : (t.num : ℝ) = (t : ℝ) * (t.den : ℝ) := by
      rw [htcast]
      field_simp
    have h : (0 : ℝ) < (t.num : ℝ) := by
      rw [hmul]
      positivity
    exact_mod_cast h.le
  have hnumle : t.num ≤ (t.den : ℤ) := by
    rw [← not_lt]
    intro hge
    have hge' : ((t.den : ℤ) + 1 : ℤ) ≤ t.num := by omega
    have hcast : ((t.den : ℝ) + 1) ≤ (t.num : ℝ) := by
      have hcc : (((t.den : ℤ) + 1 : ℤ) : ℝ) ≤ (t.num : ℝ) := by exact_mod_cast hge'
      push_cast at hcc
      linarith
    have htge : 1 + 1 / (t.den : ℝ) ≤ (t : ℝ) := by
      have heq : 1 + 1 / (t.den : ℝ) = ((t.den : ℝ) + 1) / (t.den : ℝ) := by
        field_simp
      rw [heq, htcast, div_le_div_iff_of_pos_right hdenpos]
      linarith
    have hsmall : 1 / ((t.den : ℝ) * QQ) ≤ 1 / (t.den : ℝ) := by
      rw [one_div, one_div, inv_le_inv₀ (mul_pos hdenpos hQQpos) hdenpos]
      exact le_mul_of_one_le_right hdenpos.le hQ1
    have hxgt : 1 < x := by
      have h2 : (t : ℝ) - 1 / ((t.den : ℝ) * QQ) < x := by
        have := (abs_lt.mp hstrict).1
        linarith
      linarith
    linarith
  refine ⟨t.num.toNat, t.den, by exact_mod_cast t.pos, hden, ?_, ?_, ?_⟩
  · omega
  · have hred := t.reduced
    have hrep : t.num = ((t.num.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hnum0).symm
    rwa [hrep, Int.natAbs_natCast] at hred
  · have hval : ((t.num.toNat : ℕ) : ℝ) = (t.num : ℝ) := by
      rw [show ((t.num.toNat : ℕ) : ℝ) = ((t.num.toNat : ℤ) : ℝ) by push_cast; ring]
      exact congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnum0)
    rw [hval, ← htcast]
    exact hstrict

/-- LEAF. Page 364, the Farey sequence partition of the minor arcs. DECISION U-1614: `4 ≤ N` added,
for `N < 4` the Farey range `q ≤ ⌊Q⌋` is empty, `Audit1614.old_farey_cover_false`. -/
theorem farey_cover (N : ℕ) (ε A : ℝ) (_hN : 4 ≤ N) :
    minorArcs N A ⊆ ⋃ q ∈ Finset.Icc 1 ⌊Q N⌋₊, ⋃ (a : ℕ) (_ : a ≤ q ∧ a.Coprime q),
      Ioo ((a : ℝ) / q - 1 / (q * Q N)) ((a : ℝ) / q + 1 / (q * Q N)) := by
  intro x hx
  have hQval : Q N = (N : ℝ) ^ (1 / 2 : ℝ) / 2 := rfl
  obtain ⟨⟨hx1, hx2⟩, -⟩ := hx
  rw [← hQval] at hx1 hx2
  have hQ1 : 1 ≤ Q N := farey_one_le_Q _hN
  have hQpos : (0 : ℝ) < Q N := lt_of_lt_of_le zero_lt_one hQ1
  have hfloor : 1 ≤ ⌊Q N⌋₊ := Nat.le_floor (by simpa using hQ1)
  rcases le_total x 1 with hxle | hxge
  · obtain ⟨a, q, hq1, hqq, haq, hcop, hlt⟩ := farey_exists_arc hQ1 hx1 hxle
    refine mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨?_, mem_iUnion.mpr
      ⟨a, mem_iUnion.mpr ⟨⟨haq, hcop⟩, ?_⟩⟩⟩⟩
    · rw [Finset.mem_Icc]; exact ⟨hq1, hqq⟩
    · rw [mem_Ioo]
      have hh := abs_lt.mp hlt
      constructor <;> linarith [hh.1, hh.2]
  · refine mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨?_, mem_iUnion.mpr
      ⟨1, mem_iUnion.mpr ⟨⟨le_rfl, Nat.coprime_one_left 1⟩, ?_⟩⟩⟩⟩
    · rw [Finset.mem_Icc]; exact ⟨le_rfl, hfloor⟩
    · rw [mem_Ioo]
      have homeg : (0 : ℝ) < 1 / Q N := by positivity
      simp only [Nat.cast_one, one_div_one, one_mul]
      constructor <;> linarith

/-- REFUTED, `Audit1614.old_gallagher_comparison_false`: one modulus block `M` cannot bound the whole
integral, the paper sums over dyadic `M` and loses a power of `L`. Do not prove this. The correct form
is `Decomp97.reduction27`, display 27 on p. 364. Unused by the assembly. Kept as text of record.
LEAF. Page 364, the Gallagher lemma application comparing discrete and continuous mean squares. -/
theorem gallagher_comparison (N : ℕ) (ε ξ A : ℝ) (M : ℕ) (hM1 : 1 ≤ M) (hM2 : (M : ℝ) ≤ Q N) :
    (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A, ‖S N α‖ ^ 2)
      ≤ 2 * (energy N ε ξ M) := by
  sorry

/-- Assembly theorem for reduction27 from the Farey cover and Gallagher comparison.
CONDITIONAL ON farey_cover and gallagher_comparison. -/
theorem reduction27_assembly :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27
  exact ⟨ε₁, hε₁, hred⟩

end LeanLab.PerelliPintz1992.DecompJ288
