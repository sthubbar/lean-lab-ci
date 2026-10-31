/-
P0086 Basak, Bhat, Dong, Zaharescu 2024: Theorem 1.1 from Lemma 3.1 and ternary Goldbach.
Our own gluing, not the paper's display 3.7, which VERIFY U-0175 found loose though the theorem
survives. Blocks u_j = (5/4)^j: the windows [4u_j, 5u_j] tile [4, ∞). Lemma 3.1 thresholds
t_A are made monotone as T_A = 3 + Σ_{i ≤ A} |t_i|; block j uses the largest A ≤ j with
T_A ≤ u_j, so A grows without bound along the blocks. Odd m up to 5T_1 are covered by all
primes up to that bound and ternary Goldbach. Sparseness: for each B, all but finitely many
blocks have A ≥ B + 2, and Σ_{u_j ≤ Y} u_j ≤ 5Y.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Statements

open Finset Filter Topology
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Gluing

/-! ### The block sizes -/

/-- `u_j = (5/4)^j`. -/
def u (j : ℕ) : ℝ := (5 / 4 : ℝ) ^ j

theorem u_pos (j : ℕ) : 0 < u j := by unfold u; positivity

theorem one_le_u (j : ℕ) : 1 ≤ u j := by unfold u; exact one_le_pow₀ (by norm_num)

theorem u_mono : Monotone u := fun a b h => pow_le_pow_right₀ (by norm_num) h

theorem u_succ (j : ℕ) : u (j + 1) = 5 / 4 * u j := by unfold u; ring

theorem u_ge_lin (j : ℕ) : 1 + (j : ℝ) / 4 ≤ u j := by
  unfold u
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 4 by norm_num) j
  have h : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  rw [h] at this; linarith

theorem sum_u (n : ℕ) : ∑ j ∈ range n, u j = 4 * (u n - 1) := by
  induction n with
  | zero => simp [u]
  | succ n ih => rw [sum_range_succ, ih, u_succ]; ring

/-- `Σ_{j : u_j ≤ Y} u_j ≤ 5Y`, any finite range of indices. -/
theorem sum_u_le (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ j ∈ (range N).filter (fun j => u j ≤ Y), u j ≤ 5 * Y := by
  by_cases hne : ((range N).filter (fun j => u j ≤ Y)).Nonempty
  · set J := ((range N).filter (fun j => u j ≤ Y)).max' hne
    have hJ : J ∈ (range N).filter (fun j => u j ≤ Y) := max'_mem _ _
    have hsub : (range N).filter (fun j => u j ≤ Y) ⊆ range (J + 1) := by
      intro j hj
      have := le_max' _ j hj
      rw [mem_range]; omega
    calc ∑ j ∈ (range N).filter (fun j => u j ≤ Y), u j ≤ ∑ j ∈ range (J + 1), u j :=
          sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (u_pos j).le)
      _ = 4 * (u (J + 1) - 1) := sum_u _
      _ ≤ 5 * u J := by rw [u_succ]; linarith
      _ ≤ 5 * Y := by have := (mem_filter.mp hJ).2; linarith
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]; linarith

/-- Every `m ≥ 4` lies in some window `[4u_j, 5u_j)`. -/
theorem exists_window (m : ℝ) (hm : 4 ≤ m) : ∃ j : ℕ, 4 * u j ≤ m ∧ m < 5 * u j := by
  have hex : ∃ j : ℕ, m < 5 * u j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt m (show (1 : ℝ) < 5 / 4 by norm_num)
    exact ⟨j, by unfold u; have := (u_pos j); unfold u at this; linarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | k
  · simp [u]; linarith
  · have := Nat.find_min hex (show k < Nat.find hex by omega)
    push_neg at this
    rw [u_succ]; linarith

/-! ### The gluing, from Lemma 3.1 for every `A` -/

section Glue

variable (hL : ∀ A : ℕ, Lemma31 A)

/-- The threshold of Lemma 3.1 for `A`. -/
def t (A : ℕ) : ℝ := Classical.choose (hL A)

/-- A monotone threshold above `t A` and above `3`. -/
def T (A : ℕ) : ℝ := 3 + ∑ i ∈ range (A + 1), |t hL i|

theorem t_le_T (A : ℕ) : t hL A ≤ T hL A := by
  unfold T
  have h1 : |t hL A| ≤ ∑ i ∈ range (A + 1), |t hL i| :=
    single_le_sum (f := fun i => |t hL i|) (fun i _ => abs_nonneg _) (self_mem_range_succ A)
  linarith [le_abs_self (t hL A)]

theorem three_le_T (A : ℕ) : 3 ≤ T hL A := by
  unfold T; linarith [sum_nonneg (fun i (_ : i ∈ range (A + 1)) => abs_nonneg (t hL i))]

theorem T_mono : Monotone (T hL) := by
  intro a b hab
  unfold T
  have := sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.succ_le_succ hab))
    (fun i (_ : i ∈ range (b + 1)) _ => abs_nonneg (t hL i))
  linarith

/-- The Lemma 3.1 set for `A` at `u`, empty if `u` is below the threshold. -/
def pick (A : ℕ) (v : ℝ) : Finset ℕ :=
  if h : t hL A ≤ v then Classical.choose ((Classical.choose_spec (hL A)).2 v h) else ∅

theorem pick_spec (A : ℕ) (v : ℝ) (h : t hL A ≤ v) :
    (∀ p ∈ pick hL A v, p.Prime ∧ v ≤ p ∧ (p : ℝ) ≤ 2 * v) ∧
    ((pick hL A v).card : ℝ) ≤ v / Real.log v ^ A ∧
    ∀ m : ℕ, Odd m → 4 * v ≤ m → (m : ℝ) ≤ 5 * v → IsSum3In (↑(pick hL A v) : Set ℕ) m := by
  unfold pick; rw [dif_pos h]
  exact Classical.choose_spec ((Classical.choose_spec (hL A)).2 v h)

/-- The admissible exponents for block `j`. -/
def S (j : ℕ) : Finset ℕ := (Icc 1 j).filter (fun A => T hL A ≤ u j)

/-- The exponent used in block `j`. -/
def Aj (j : ℕ) : ℕ := (S hL j).sup id

/-- The primes of block `j`. -/
def Pj (j : ℕ) : Finset ℕ := if T hL (Aj hL j) ≤ u j then pick hL (Aj hL j) (u j) else ∅

theorem mem_S_of {j A : ℕ} (h1 : 1 ≤ A) (h2 : A ≤ j) (h3 : T hL A ≤ u j) : A ∈ S hL j := by
  unfold S; simp [h1, h2, h3]

theorem le_Aj {j A : ℕ} (h : A ∈ S hL j) : A ≤ Aj hL j := by
  unfold Aj; exact le_sup (f := id) h

theorem Aj_mem {j : ℕ} (h : (S hL j).Nonempty) : Aj hL j ∈ S hL j := by
  unfold Aj
  obtain ⟨a, ha, he⟩ := exists_mem_eq_sup (S hL j) h id
  rw [he]; exact ha

theorem Pj_spec {j : ℕ} (h : T hL (Aj hL j) ≤ u j) :
    (∀ p ∈ Pj hL j, p.Prime ∧ u j ≤ p ∧ (p : ℝ) ≤ 2 * u j) ∧
    ((Pj hL j).card : ℝ) ≤ u j / Real.log (u j) ^ (Aj hL j) ∧
    ∀ m : ℕ, Odd m → 4 * u j ≤ m → (m : ℝ) ≤ 5 * u j → IsSum3In (↑(Pj hL j) : Set ℕ) m := by
  unfold Pj; rw [if_pos h]
  exact pick_spec hL _ _ ((t_le_T hL _).trans h)

theorem Pj_mem {j p : ℕ} (hp : p ∈ Pj hL j) :
    p.Prime ∧ u j ≤ p ∧ (p : ℝ) ≤ 2 * u j ∧ T hL (Aj hL j) ≤ u j := by
  by_cases h : T hL (Aj hL j) ≤ u j
  · obtain ⟨h1, -, -⟩ := Pj_spec hL h
    exact ⟨(h1 p hp).1, (h1 p hp).2.1, (h1 p hp).2.2, h⟩
  · unfold Pj at hp; rw [if_neg h] at hp; simp at hp

theorem one_le_log_u {j : ℕ} (h : T hL (Aj hL j) ≤ u j) : 1 ≤ Real.log (u j) := by
  have h3 := (three_le_T hL (Aj hL j)).trans h
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- The card bound on block `j` for any exponent `E ≤ A_j`. -/
theorem card_Pj_le {j E : ℕ} (hE : E ≤ Aj hL j) :
    ((Pj hL j).card : ℝ) ≤ u j / Real.log (u j) ^ E := by
  by_cases h : T hL (Aj hL j) ≤ u j
  · obtain ⟨-, h2, -⟩ := Pj_spec hL h
    have hl := one_le_log_u hL h
    have hp : Real.log (u j) ^ E ≤ Real.log (u j) ^ (Aj hL j) := pow_le_pow_right₀ hl hE
    have hpos : 0 < Real.log (u j) ^ E := by positivity
    exact h2.trans (div_le_div_of_nonneg_left (u_pos j).le hpos hp)
  · unfold Pj; rw [if_neg h]; simp only [card_empty, Nat.cast_zero]
    exact div_nonneg (u_pos j).le (pow_nonneg (Real.log_nonneg (one_le_u j)) _)

/-- The glued set of primes. -/
def Pset : Set ℕ :=
  {p | p.Prime ∧ p ≤ ⌊5 * T hL 1⌋₊} ∪ ⋃ j, (↑(Pj hL j) : Set ℕ)

theorem Pset_prime : ∀ p ∈ Pset hL, p.Prime := by
  intro p hp
  rcases hp with h | h
  · exact h.1
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact (Pj_mem hL hj).1

/-- Condition (b): every odd `m ≥ 7` is a sum of three primes of the set. -/
theorem Pset_basis (hT : TernaryGoldbach) :
    ∀ m : ℕ, Odd m → 7 ≤ m → IsSum3In (Pset hL) m := by
  intro m ho h7
  by_cases hsmall : m ≤ ⌊5 * T hL 1⌋₊
  · obtain ⟨a, b, c, ha, hb, hc, e⟩ := hT m ho h7
    refine ⟨a, b, c, Or.inl ⟨ha, by omega⟩, Or.inl ⟨hb, by omega⟩, Or.inl ⟨hc, by omega⟩, e⟩
  · push_neg at hsmall
    have hm5 : 5 * T hL 1 < m := by
      have := Nat.lt_floor_add_one (5 * T hL 1)
      have : ((⌊5 * T hL 1⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hsmall
      push_cast at this; linarith
    obtain ⟨j, hj1, hj2⟩ := exists_window (m : ℝ) (by have : (7 : ℝ) ≤ m := by exact_mod_cast h7
                                                      linarith)
    have huj : T hL 1 ≤ u j := by linarith
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; have := three_le_T hL 1; simp [u] at huj; linarith
      · exact h0
    have hmem : 1 ∈ S hL j := mem_S_of hL le_rfl hj huj
    have hA := Aj_mem hL ⟨1, hmem⟩
    have hTA : T hL (Aj hL j) ≤ u j := (mem_filter.mp hA).2
    obtain ⟨-, -, h3⟩ := Pj_spec hL hTA
    have hsub : (↑(Pj hL j) : Set ℕ) ⊆ Pset hL := fun p hp =>
      Or.inr (Set.mem_iUnion.mpr ⟨j, hp⟩)
    exact isSum3In_mono hsub (h3 m ho hj1 hj2.le)

/-- For every `E`, all late blocks have exponent at least `E`. -/
theorem eventually_Aj_ge (E : ℕ) : ∃ j0 : ℕ, ∀ j, j0 ≤ j → E ≤ Aj hL j := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (T hL (E + 1)) (show (1 : ℝ) < 5 / 4 by norm_num)
  refine ⟨k + E + 1, fun j hj => ?_⟩
  have h1 : T hL (E + 1) ≤ u j := by
    have := u_mono (show k ≤ j by omega); unfold u at this ⊢; linarith
  have := le_Aj hL (mem_S_of hL (by omega) (by omega) h1)
  omega

/-- The count up to `X` is covered by the small primes, the first `j0` blocks, and the late
blocks with `u_j ≤ X`. -/
theorem count_le (X : ℝ) (hX : 1 ≤ X) (j0 : ℕ) :
    (countLe (Pset hL) X : ℝ) ≤ ((⌊5 * T hL 1⌋₊ + 1 : ℕ) : ℝ) +
      ∑ j ∈ range j0, ((Pj hL j).card : ℝ) +
      ∑ j ∈ ((range (4 * ⌊X⌋₊ + 5)).filter (fun j => u j ≤ X)).filter (fun j => j0 ≤ j),
        ((Pj hL j).card : ℝ) := by
  set N0 := ⌊5 * T hL 1⌋₊
  set F := ((range (4 * ⌊X⌋₊ + 5)).filter (fun j => u j ≤ X)).filter (fun j => j0 ≤ j)
  have hsub : (range (⌊X⌋₊ + 1)).filter (fun p => p ∈ Pset hL) ⊆
      range (N0 + 1) ∪ ((range j0).biUnion (Pj hL) ∪ F.biUnion (Pj hL)) := by
    intro p hp
    obtain ⟨hpr, hpP⟩ := mem_filter.mp hp
    have hpX : (p : ℝ) ≤ X := by
      have : p ≤ ⌊X⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hpr)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
    rcases hpP with h | h
    · exact mem_union_left _ (mem_range.mpr (Nat.lt_succ_of_le h.2))
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      have hj' : p ∈ Pj hL j := hj
      apply mem_union_right
      by_cases hj0 : j < j0
      · exact mem_union_left _ (mem_biUnion.mpr ⟨j, mem_range.mpr hj0, hj'⟩)
      · apply mem_union_right
        refine mem_biUnion.mpr ⟨j, ?_, hj'⟩
        obtain ⟨-, hu, -, -⟩ := Pj_mem hL hj'
        have huX : u j ≤ X := hu.trans hpX
        have hlin := u_ge_lin j
        have hfl : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
        have hjlt : j < 4 * ⌊X⌋₊ + 5 := by
          have : (j : ℝ) < 4 * ⌊X⌋₊ + 5 := by linarith
          exact_mod_cast this
        simp only [F, mem_filter, mem_range]
        exact ⟨⟨hjlt, huX⟩, by omega⟩
  unfold countLe
  have h1 := card_le_card hsub
  have h2 := card_union_le (range (N0 + 1)) ((range j0).biUnion (Pj hL) ∪ F.biUnion (Pj hL))
  have h3 := card_union_le ((range j0).biUnion (Pj hL)) (F.biUnion (Pj hL))
  have h4 := card_biUnion_le (s := range j0) (t := Pj hL)
  have h5 := card_biUnion_le (s := F) (t := Pj hL)
  rw [card_range] at h2
  have : #((range (⌊X⌋₊ + 1)).filter (fun p => p ∈ Pset hL)) ≤
      (N0 + 1) + ∑ j ∈ range j0, (Pj hL j).card + ∑ j ∈ F, (Pj hL j).card := by omega
  have := (Nat.cast_le (α := ℝ)).mpr this
  push_cast at this ⊢
  exact this

/-- The late blocks: `Σ ≤ 5√X + 5 · 2^E X / (log X)^E` once every block has exponent `≥ E`. -/
theorem late_le (X : ℝ) (hX : 3 ≤ X) (E j0 : ℕ) (hj0 : ∀ j, j0 ≤ j → E ≤ Aj hL j) :
    ∑ j ∈ ((range (4 * ⌊X⌋₊ + 5)).filter (fun j => u j ≤ X)).filter (fun j => j0 ≤ j),
        ((Pj hL j).card : ℝ) ≤
      5 * Real.sqrt X + 5 * 2 ^ E * X / Real.log X ^ E := by
  set N := 4 * ⌊X⌋₊ + 5
  set F := ((range N).filter (fun j => u j ≤ X)).filter (fun j => j0 ≤ j)
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  rw [← sum_filter_add_sum_filter_not F (fun j => u j ≤ Real.sqrt X)]
  have hA : ∑ j ∈ F.filter (fun j => u j ≤ Real.sqrt X), ((Pj hL j).card : ℝ) ≤ 5 * Real.sqrt X := by
    calc ∑ j ∈ F.filter (fun j => u j ≤ Real.sqrt X), ((Pj hL j).card : ℝ)
        ≤ ∑ j ∈ F.filter (fun j => u j ≤ Real.sqrt X), u j := by
          apply sum_le_sum; intro j _
          have := card_Pj_le hL (j := j) (E := 0) (Nat.zero_le _)
          simpa using this
      _ ≤ ∑ j ∈ (range N).filter (fun j => u j ≤ Real.sqrt X), u j := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => (u_pos j).le)
          intro j hj
          simp only [F, mem_filter] at hj ⊢
          exact ⟨hj.1.1.1, hj.2⟩
      _ ≤ 5 * Real.sqrt X := sum_u_le N _ hsq0
  have hB : ∑ j ∈ F.filter (fun j => ¬ u j ≤ Real.sqrt X), ((Pj hL j).card : ℝ) ≤
      5 * 2 ^ E * X / Real.log X ^ E := by
    have hlogsq : Real.log (Real.sqrt X) = Real.log X / 2 := by
      rw [Real.log_sqrt hX0.le]
    calc ∑ j ∈ F.filter (fun j => ¬ u j ≤ Real.sqrt X), ((Pj hL j).card : ℝ)
        ≤ ∑ j ∈ F.filter (fun j => ¬ u j ≤ Real.sqrt X), u j * (2 / Real.log X) ^ E := by
          apply sum_le_sum; intro j hj
          simp only [F, mem_filter] at hj
          have hc := card_Pj_le hL (hj0 j hj.1.2)
          have hlt : Real.sqrt X < u j := lt_of_not_ge hj.2
          have hsqpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
          have hl : Real.log X / 2 ≤ Real.log (u j) := by
            rw [← hlogsq]; exact Real.log_le_log hsqpos hlt.le
          have hl0 : 0 < Real.log X / 2 := by linarith
          have hp : (Real.log X / 2) ^ E ≤ Real.log (u j) ^ E :=
            pow_le_pow_left₀ hl0.le hl E
          have hp0 : 0 < (Real.log X / 2) ^ E := by positivity
          calc ((Pj hL j).card : ℝ) ≤ u j / Real.log (u j) ^ E := hc
            _ ≤ u j / (Real.log X / 2) ^ E :=
                div_le_div_of_nonneg_left (u_pos j).le hp0 hp
            _ = u j * (2 / Real.log X) ^ E := by
                rw [div_pow, div_pow, div_eq_mul_inv, inv_div]
      _ = (∑ j ∈ F.filter (fun j => ¬ u j ≤ Real.sqrt X), u j) * (2 / Real.log X) ^ E := by
          rw [sum_mul]
      _ ≤ (5 * X) * (2 / Real.log X) ^ E := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc ∑ j ∈ F.filter (fun j => ¬ u j ≤ Real.sqrt X), u j
              ≤ ∑ j ∈ (range N).filter (fun j => u j ≤ X), u j := by
                apply sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => (u_pos j).le)
                intro j hj
                simp only [F, mem_filter] at hj ⊢
                exact hj.1.1
            _ ≤ 5 * X := sum_u_le N X hX0.le
      _ = 5 * 2 ^ E * X / Real.log X ^ E := by rw [div_pow]; ring
  linarith

/-- Condition (a) for every `B`. -/
theorem Pset_sparse (B : ℕ) : SparseB (Pset hL) B := by
  obtain ⟨j0, hj0⟩ := eventually_Aj_ge hL (B + 2)
  set C0 : ℝ := ((⌊5 * T hL 1⌋₊ + 1 : ℕ) : ℝ) + ∑ j ∈ range j0, ((Pj hL j).card : ℝ)
  have hC0 : 0 ≤ C0 := by positivity
  -- the three limits
  have L1 : Tendsto (fun X : ℝ => Real.log X ^ B / X) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 B one_ne_zero
    simpa using this
  have L2 : Tendsto (fun X : ℝ => Real.log (Real.sqrt X) ^ B / Real.sqrt X) atTop (𝓝 0) :=
    L1.comp Real.tendsto_sqrt_atTop
  have L3 : Tendsto (fun X : ℝ => (Real.log X ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp Real.tendsto_log_atTop)
  have Lsum : Tendsto (fun X : ℝ => C0 * (Real.log X ^ B / X) +
      5 * 2 ^ B * (Real.log (Real.sqrt X) ^ B / Real.sqrt X) +
      5 * 2 ^ (B + 2) * (Real.log X ^ 2)⁻¹) atTop (𝓝 0) := by
    have := ((L1.const_mul C0).add (L2.const_mul (5 * 2 ^ B))).add (L3.const_mul (5 * 2 ^ (B + 2)))
    simpa using this
  unfold SparseB
  refine squeeze_zero' ?_ ?_ Lsum
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
    have hX0 : 0 < X := by linarith
    have hlX : 0 < Real.log X := Real.log_pos (by linarith)
    have hc := count_le hL X (by linarith) j0
    have hl := late_le hL X hX (B + 2) j0 hj0
    have hcount : (countLe (Pset hL) X : ℝ) ≤
        C0 + 5 * Real.sqrt X + 5 * 2 ^ (B + 2) * X / Real.log X ^ (B + 2) := by
      simp only [C0]; linarith
    have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have hsqpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
    have hlogsq : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
    have hLB : 0 ≤ Real.log X ^ B := by positivity
    calc Real.log X ^ B * (countLe (Pset hL) X : ℝ) / X
        ≤ Real.log X ^ B * (C0 + 5 * Real.sqrt X + 5 * 2 ^ (B + 2) * X / Real.log X ^ (B + 2)) / X := by
          apply div_le_div_of_nonneg_right _ hX0.le
          exact mul_le_mul_of_nonneg_left hcount hLB
      _ = C0 * (Real.log X ^ B / X) +
          5 * 2 ^ B * (Real.log (Real.sqrt X) ^ B / Real.sqrt X) +
          5 * 2 ^ (B + 2) * (Real.log X ^ 2)⁻¹ := by
          rw [hlogsq, div_pow]
          set L := Real.log X with hLdef
          have hL0 : L ≠ 0 := hlX.ne'
          set s := Real.sqrt X with hsdef
          have hs0 : s ≠ 0 := hsqpos.ne'
          rw [← hsq]
          field_simp
          ring
      _ ≤ _ := le_rfl

/-- **Basak-Bhat-Dong-Zaharescu 2024, Theorem 1.1, from Lemma 3.1 for every `A` and the
ternary Goldbach theorem**, zero sorry. -/
theorem theorem11_of (hL : ∀ A : ℕ, Lemma31 A) (hT : TernaryGoldbach) : Theorem11 :=
  ⟨Pset hL, Pset_prime hL, fun B _ => Pset_sparse hL B, Pset_basis hL hT⟩

end Glue

/-- The same with Lemma 3.1 only for positive `A`, as the paper states it. -/
theorem theorem11_of_lemma31 (hL : ∀ A : ℕ, 0 < A → Lemma31 A) (hT : TernaryGoldbach) :
    Theorem11 := by
  have hL' : ∀ A : ℕ, Lemma31 A := fun A =>
    lemma31_mono (show A ≤ A + 1 by omega) (hL (A + 1) (by omega))
  exact theorem11_of hL' hT

end LeanLab.SparseTernary.Gluing
