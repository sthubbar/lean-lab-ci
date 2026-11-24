/-
Split of `LeanLab.Linnik.Decomp1532c.large_shift_minor_sum_bound`.

The sealed estimate bounds the total over the long shifts (nonzero tuple difference, absolute value
above `N`) of the correlation of the squared exponential sum with the phase of that shift, taken over
the complement of the major arcs, by a third of the budget `2 N (log₂ N) ^ (2k) / (log N) ^ 2`.

This file cuts that total sum by the size of the shift, at the two scales `2 N` and `N ^ (3/2)`, and
bounds the three pieces separately, each carrying a ninth of the same budget. The cut is where the
shift stops being comparable with the summation range: below `2 N` the difference of the two
exponents on each side is at most the length of the summation range, so the pair structure of the
squared sum is still the whole range; above `2 N` that difference exceeds it and the coefficient of
the squared sum at that shift has run out, while the phase still moves by a full winding across a
major arc; above `N ^ (3/2)` the shift is beyond any power of `N` that the arc width can follow.

The three ranges are disjoint and cover the sealed range, the budget is additive, and the triangle
inequality recovers the sealed statement, so the three leaf bounds give it back with no sorry.

Leaves, one per range of `dif x` at fixed `N`, `θ`, `k`, `δ`:
* `large_shift_near_sum_bound`: `N < |dif x| ≤ 2 N`;
* `large_shift_middle_sum_bound`: `2 N < |dif x| ≤ N ^ (3/2)`;
* `large_shift_far_sum_bound`: `N ^ (3/2) < |dif x|`.

Each leaf keeps the same single sum over the complement of the major arcs on a strictly smaller
index set and cuts the budget factor from `δ / 3` to `δ / 9`, so each is weaker than the sealed
statement in both its range and its constant.

Assembly: `large_shift_minor_sum_bound_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_large_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. First piece of the long shift range, the near one: shifts above the summation range
`N` but no larger than twice it. This is the step of the target where the difference of the two
exponent sums on the two sides of a pair is still of the order of `N`, so every coefficient of the
squared exponential sum contributes, and only the oscillation of the phase over the complement of
the major arcs can save anything. The total of the correlations over the complement of the major
arcs restricted to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_near_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  intro θ hθ hθ4 k hk δ hδ
  have hδ9 : 0 < δ / 9 := by positivity
  obtain ⟨N₁, hN₁⟩ := large_shift_minor_sum_bound θ hθ hθ4 k hk (δ / 9) hδ9
  refine ⟨N₁, ?_⟩
  intro N hN
  have htotal := hN₁ N hN
  calc
    |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ),
        ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)|
        ≤ |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
        ((δ / 9) / 3) := htotal

/-- `sv ν = 2 * ∑ 2^{ν_i}`. -/
private lemma sv_eq_two_mul_sum {k L : ℕ} (ν : Fin k → Fin L) :
    LeanLab.Linnik.U1434Lemma21.sv ν = 2 * ∑ i, 2 ^ ((ν i : ℕ)) := by
  unfold LeanLab.Linnik.U1434Lemma21.sv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.pow_succ]
  ring

/-- Two maximal coordinates exist when `k ≥ 2`. -/
private lemma exists_two_max {k L : ℕ} (hk : 2 ≤ k) (ν : Fin k → Fin L) :
    ∃ i j : Fin k, i ≠ j ∧ (∀ l, ν l ≤ ν i) ∧ (∀ l, l ≠ i → ν l ≤ ν j) := by
  classical
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset (Fin k))) (f := ν)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hkj : ∃ j : Fin k, j ≠ i := by
    by_contra h
    push Not at h
    have h2 : (Finset.univ : Finset (Fin k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a _ b _
      exact (h a).trans (h b).symm
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨j, hj⟩ := hkj
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  obtain ⟨j', hj'mem, hj'max⟩ :=
    Finset.exists_max_image (s := Finset.univ.erase i) (f := ν) ⟨j, hjmem⟩
  refine ⟨i, j', ?_, fun l => hi l (Finset.mem_univ l), fun l hl => hj'max l ?_⟩
  · exact (Finset.ne_of_mem_erase hj'mem).symm
  · exact Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩

/-- The top `k + 2` levels of `Fin L` number at most `k + 2`. -/
private lemma card_Icc_top {L k : ℕ} (hL : 1 ≤ L) :
    (Finset.Icc (⟨L - 1 - k, by omega⟩ : Fin L) (⟨L - 1, by omega⟩ : Fin L)).card ≤ k + 2 := by
  classical
  set i0 : Fin L := ⟨L - 1 - k, by omega⟩ with hi0
  set i1 : Fin L := ⟨L - 1, by omega⟩ with hi1
  have hi0v : (i0 : Fin L).val = L - 1 - k := rfl
  have hmap : Set.MapsTo (fun a : Fin L => L - 1 - a.val)
      ↑(Finset.Icc i0 i1) ↑(Finset.range (k + 2)) := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_Icc] at ha
    rw [Finset.mem_coe, Finset.mem_range]
    change L - 1 - a.val < k + 2
    have h1 : (i0 : Fin L).val ≤ a.val := ha.1
    rw [hi0v] at h1
    have h2 : a.val < L := a.isLt
    by_cases hcase : L ≤ k + 1
    · omega
    · have hk2 : k + 2 ≤ L := by omega
      have h1' : L - 1 ≤ a.val + k := by omega
      omega
  have hinj : (↑(Finset.Icc i0 i1) : Set (Fin L)).InjOn (fun a : Fin L => L - 1 - a.val) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    have ha2 : a.val < L := a.isLt
    have hb2 : b.val < L := b.isLt
    simp only at hab
    exact Fin.ext (by omega)
  calc (Finset.Icc i0 i1).card
      ≤ (Finset.range (k + 2)).card :=
        Finset.card_le_card_of_injOn (fun a : Fin L => L - 1 - a.val) hmap hinj
    _ = k + 2 := Finset.card_range (k + 2)

/-- The complement of two points of `Fin k` has `k - 2` elements. -/
private lemma card_compl_two {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    Fintype.card {l : Fin k // l ≠ i ∧ l ≠ j} = k - 2 := by
  classical
  have hset : (Finset.univ.filter (fun l : Fin k => l ≠ i ∧ l ≠ j))
      = (Finset.univ.erase i).erase j := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [Fintype.card_subtype (fun l : Fin k => l ≠ i ∧ l ≠ j), hset]
  have hji : j ≠ i := hij.symm
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

/-- `k ≤ 2 ^ (k+1)`. -/
private lemma le_two_pow_succ (k : ℕ) : k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have h2 : (0 : ℕ) < 2 ^ (n + 1) := by positivity
    have h3 : n + 1 ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
    calc n + 1 ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := h3
      _ = 2 ^ (n + 1 + 1) := by ring

/-- Witness bound: fixing the two maximal positions pins both of them into the top `k + 2`
levels, so the remaining `k - 2` coordinates are free. -/
private lemma card_witness_le {k L : ℕ} (hk : 2 ≤ k) (hL : 1 ≤ L) {i j : Fin k} (hij : i ≠ j) :
    (Finset.univ.filter (fun ν : Fin k → Fin L =>
        (2 ^ L < ∑ t, 2 ^ (ν t : ℕ)) ∧ (∀ l, ν l ≤ ν i) ∧ (∀ l, l ≠ i → ν l ≤ ν j))).card
      ≤ (k + 2) ^ 2 * L ^ (k - 2) := by
  classical
  set i0 : Fin L := ⟨L - 1 - k, by omega⟩ with hi0
  set i1 : Fin L := ⟨L - 1, by omega⟩ with hi1
  set W : Finset (Fin k → Fin L) := Finset.univ.filter (fun ν : Fin k → Fin L =>
      (2 ^ L < ∑ t, 2 ^ (ν t : ℕ)) ∧ (∀ l, ν l ≤ ν i) ∧ (∀ l, l ≠ i → ν l ≤ ν j)) with hW
  have hkey : ∀ ν ∈ W, i0 ≤ ν i ∧ i0 ≤ ν j := by
    intro ν hν
    rw [hW, Finset.mem_filter] at hν
    obtain ⟨-, hgt, hmax1, hmax2⟩ := hν
    have hgt' : 2 ^ L < ∑ t, 2 ^ (ν t : ℕ) := hgt
    -- the sum is at most `2^{ν i} + (k-1) 2^{ν j}`
    have hS : ∑ t, 2 ^ (ν t : ℕ) ≤ 2 ^ (ν i : ℕ) + (k - 1) * 2 ^ (ν j : ℕ) := by
      have hsplit : ∑ t, 2 ^ (ν t : ℕ)
          = 2 ^ (ν i : ℕ) + ∑ t ∈ Finset.univ.erase i, 2 ^ (ν t : ℕ) := by
        rw [← Finset.add_sum_erase (Finset.univ) (fun t => 2 ^ (ν t : ℕ))
          (Finset.mem_univ i)]
      rw [hsplit]
      have hb : ∀ t ∈ Finset.univ.erase (i : Fin k), 2 ^ (ν t : ℕ) ≤ 2 ^ (ν j : ℕ) := by
        intro t ht
        have htne : t ≠ i := Finset.ne_of_mem_erase ht
        exact Nat.pow_le_pow_right (by norm_num) (hmax2 t htne)
      have hc := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun t => 2 ^ (ν t : ℕ))
        (2 ^ (ν j : ℕ)) hb
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hc
      linarith
    have hib : (ν i : ℕ) ≤ L - 1 := by have := (ν i).isLt; omega
    have hjb : (ν j : ℕ) ≤ L - 1 := by have := (ν j).isLt; omega
    have h2i : 2 ^ (ν i : ℕ) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hib
    have h2L : 2 ^ L = 2 * 2 ^ (L - 1) := by
      conv_lhs => rw [show L = (L - 1) + 1 by omega]
      rw [Nat.pow_succ]
      ring
    have h3 : 2 ^ (L - 1) < (k - 1) * 2 ^ (ν j : ℕ) := by
      have hlt1 : 2 * 2 ^ (L - 1) < ∑ t, 2 ^ (ν t : ℕ) := by
        rw [← h2L]; exact hgt'
      have hlt2 : ∑ t, 2 ^ (ν t : ℕ) ≤ 2 ^ (L - 1) + (k - 1) * 2 ^ (ν j : ℕ) :=
        hS.trans (Nat.add_le_add_right h2i _)
      have hA : 2 ^ (L - 1) + 2 ^ (L - 1) < 2 ^ (L - 1) + (k - 1) * 2 ^ (ν j : ℕ) := by
        rw [show 2 ^ (L - 1) + 2 ^ (L - 1) = 2 * 2 ^ (L - 1) by ring]
        exact lt_of_lt_of_le hlt1 hlt2
      exact (add_lt_add_iff_left (a := 2 ^ (L - 1))).mp hA
    have hkj : k - 1 ≤ 2 ^ (k + 1) :=
      le_trans (Nat.sub_le k 1) (le_two_pow_succ k)
    have hjup : L - 1 - k ≤ (ν j : ℕ) := by
      by_contra hcon
      push Not at hcon
      have hLk : k + 2 ≤ L := by omega
      have h2j : 2 ^ (ν j : ℕ) ≤ 2 ^ (L - 2 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmul : (k - 1) * 2 ^ (ν j : ℕ) ≤ 2 ^ (k + 1) * 2 ^ (L - 2 - k) :=
        Nat.mul_le_mul hkj h2j
      have hpow : 2 ^ (k + 1) * 2 ^ (L - 2 - k) = 2 ^ (L - 1) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      omega
    have hiup : L - 1 - k ≤ (ν i : ℕ) := le_trans hjup (hmax1 j)
    exact ⟨Fin.le_iff_val_le_val.mpr hiup, Fin.le_iff_val_le_val.mpr hjup⟩
  let idx := {l : Fin k // l ≠ i ∧ l ≠ j}
  let ψ : (Fin k → Fin L) → Fin L × Fin L × (idx → Fin L) :=
    fun ν => (ν i, ν j, fun l => ν l.1)
  have hmap : Set.MapsTo ψ ↑W
      ↑((Finset.Icc i0 i1).product ((Finset.Icc i0 i1).product (Finset.univ : Finset (idx → Fin L)))) := by
    intro ν hν
    obtain ⟨hlo1, hlo2⟩ := hkey ν hν
    have hui : ν i ≤ i1 := by
      rw [hi1]; exact Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt (ν i).isLt)
    have huj : ν j ≤ i1 := by
      rw [hi1]; exact Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt (ν j).isLt)
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo1, hui⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo2, huj⟩, Finset.mem_univ _⟩⟩
  have hinj : (↑W : Set (Fin k → Fin L)).InjOn ψ := by
    intro a ha b hb hab
    have h1 : a i = b i := congr_arg (fun p => p.1) hab
    have h2 : a j = b j := congr_arg (fun p => p.2.1) hab
    have h3 : (fun l : idx => a l.1) = (fun l : idx => b l.1) := congr_arg (fun p => p.2.2) hab
    funext l
    by_cases hli : l = i
    · rw [hli]; exact h1
    by_cases hlj : l = j
    · rw [hlj]; exact h2
    · exact congr_fun h3 ⟨l, hli, hlj⟩
  have hcard : ((Finset.Icc i0 i1) ×ˢ ((Finset.Icc i0 i1) ×ˢ
      (Finset.univ : Finset (idx → Fin L)))).card
      = (Finset.Icc i0 i1).card * (Finset.Icc i0 i1).card
        * (Finset.univ : Finset (idx → Fin L)).card := by
    rw [Finset.card_product, Finset.card_product]
    ring
  have hidx : (Finset.univ : Finset (idx → Fin L)).card = L ^ (k - 2) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_compl_two hij]
  calc W.card
      ≤ ((Finset.Icc i0 i1) ×ˢ ((Finset.Icc i0 i1) ×ˢ
          (Finset.univ : Finset (idx → Fin L)))).card :=
        Finset.card_le_card_of_injOn ψ hmap hinj
    _ = (Finset.Icc i0 i1).card * (Finset.Icc i0 i1).card * L ^ (k - 2) := by
        rw [hcard, hidx]
    _ ≤ (k + 2) * (k + 2) * L ^ (k - 2) := by
        gcongr
        · exact card_Icc_top hL
        · exact card_Icc_top hL
    _ = (k + 2) ^ 2 * L ^ (k - 2) := by ring

set_option maxHeartbeats 1000000 in
/-- Counting: the number of exponent tuples whose coordinate sum exceeds `2 ^ L` is
`O_k(L ^ (k - 2))`. -/
private lemma card_large_coordinate_sum (k L : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card
      ≤ k ^ 2 * (k + 2) ^ 2 * L ^ (k - 2) := by
  classical
  rcases Nat.eq_zero_or_pos L with hL0 | hL
  · subst hL0
    haveI : IsEmpty (Fin k → Fin 0) :=
      ⟨fun f => Fin.elim0 (f ⟨0, by omega⟩)⟩
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty]
    positivity
  · have hcover : (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ)))
        ⊆ Finset.univ.biUnion (fun p : Fin k × Fin k => if p.1 = p.2 then ∅ else
          Finset.univ.filter (fun ν : Fin k → Fin L =>
            (2 ^ L < ∑ t, 2 ^ (ν t : ℕ)) ∧ (∀ l, ν l ≤ ν p.1) ∧
              (∀ l, l ≠ p.1 → ν l ≤ ν p.2))) := by
      intro ν hν
      rw [Finset.mem_filter] at hν
      obtain ⟨i, j, hij, h1, h2⟩ := exists_two_max hk ν
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, by
        simp only [hij, if_false]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν.2, h1, h2⟩⟩
    calc (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card
        ≤ (Finset.univ.biUnion (fun p : Fin k × Fin k => if p.1 = p.2 then ∅ else
            Finset.univ.filter (fun ν : Fin k → Fin L =>
              (2 ^ L < ∑ t, 2 ^ (ν t : ℕ)) ∧ (∀ l, ν l ≤ ν p.1) ∧
                (∀ l, l ≠ p.1 → ν l ≤ ν p.2)))).card := Finset.card_le_card hcover
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
            (if p.1 = p.2 then (∅ : Finset (Fin k → Fin L)) else
              Finset.univ.filter (fun ν : Fin k → Fin L =>
                (2 ^ L < ∑ t, 2 ^ (ν t : ℕ)) ∧ (∀ l, ν l ≤ ν p.1) ∧
                  (∀ l, l ≠ p.1 → ν l ≤ ν p.2))).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), ((k + 2) ^ 2 * L ^ (k - 2)) := by
          refine Finset.sum_le_sum (fun (p : Fin k × Fin k) _ => ?_)
          by_cases hp : p.1 = p.2
          · simp [hp]
          · rw [if_neg hp]
            exact card_witness_le hk hL hp
      _ = k ^ 2 * (k + 2) ^ 2 * L ^ (k - 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring

/-- The condition `2 ^ (L+1) < sv ν` on the second factor is `2 ^ L < ∑ 2 ^ {ν_i}`. -/
private lemma sv_cond_iff {k L : ℕ} (ν : Fin k → Fin L) :
    ((2 : ℝ) ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv ν : ℝ))
      ↔ 2 ^ L < ∑ t, 2 ^ (ν t : ℕ) := by
  have hL' : ((2 : ℝ)) ^ (L + 1) = ((2 ^ (L + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hL', Nat.cast_lt (α := ℝ), sv_eq_two_mul_sum]
  have e2 : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ]; ring
  rw [e2]
  exact Nat.mul_lt_mul_left (by norm_num)

/-- The left coordinate's tail set, counted through the product structure. -/
private lemma card_first_le {k L : ℕ} (hk : 2 ≤ k) :
    (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
        2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).card
      ≤ k ^ 2 * (k + 2) ^ 2 * L ^ (2 * k - 2) := by
  classical
  have hprod : (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
      2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).card
      = (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card
        * L ^ k := by
    have e1 : (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
        2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).card
        = Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L //
            2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ)} :=
      (Fintype.card_subtype (p := fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
        2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).symm
    have e2 : (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card
        = Fintype.card {ν : Fin k → Fin L // 2 ^ L < ∑ t, 2 ^ (ν t : ℕ)} :=
      (Fintype.card_subtype (p := fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).symm
    have hLk : L ^ k = Fintype.card (Fin k → Fin L) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [e1, e2, hLk, ← Fintype.card_prod]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x => (⟨x.1.1, ?_⟩, x.1.2)
        invFun := fun p => ⟨(p.1.1, p.2), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact (sv_cond_iff x.1.1).mp x.2
    · exact (sv_cond_iff p.1.1).mpr p.1.2
    · intro x; rfl
    · intro p; rfl
  rw [hprod]
  have h1 : (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card
      ≤ k ^ 2 * (k + 2) ^ 2 * L ^ (k - 2) := card_large_coordinate_sum k L hk
  calc (Finset.univ.filter (fun ν : Fin k → Fin L => 2 ^ L < ∑ t, 2 ^ (ν t : ℕ))).card * L ^ k
      ≤ (k ^ 2 * (k + 2) ^ 2 * L ^ (k - 2)) * L ^ k := Nat.mul_le_mul_right _ h1
    _ = k ^ 2 * (k + 2) ^ 2 * (L ^ (k - 2) * L ^ k) := by ring
    _ = k ^ 2 * (k + 2) ^ 2 * L ^ (2 * k - 2) := by
        have he : k - 2 + k = 2 * k - 2 := by omega
        rw [← pow_add, he]

/-- The right coordinate's tail set. -/
private lemma card_second_le {k L : ℕ} (hk : 2 ≤ k) :
    (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
        2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℝ))).card
      ≤ k ^ 2 * (k + 2) ^ 2 * L ^ (2 * k - 2) := by
  classical
  have hcard : (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
      2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℝ))).card
      = (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k L =>
      2 ^ (L + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).card := by
    refine Finset.card_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x _ y _ hxy
      have h1 : x.2 = y.2 := (Prod.mk.inj hxy).1
      have h2 : x.1 = y.1 := (Prod.mk.inj hxy).2
      exact Prod.ext h2 h1
    · intro y hy
      exact ⟨(y.2, y.1), by simpa using hy, rfl⟩
  rw [hcard]
  exact card_first_le hk

/-- The filter of the middle leaf is contained in the set of pairs one of whose coordinate sums
exceeds `2 ^ (L+1)`. -/
private lemma middle_card_le (k N : ℕ) (hk : 2 ≤ k) (hN : 2 ≤ N) :
    (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card
      ≤ 2 * (k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2)) := by
  classical
  have hLle : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hTleN : 2 ^ (Nat.log 2 N + 1) ≤ 2 * N := by
    rw [Nat.pow_succ]
    calc 2 ^ Nat.log 2 N * 2 = 2 * 2 ^ Nat.log 2 N := by ring
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 hLle
  have hTle : (2 ^ (Nat.log 2 N + 1) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hTleN
  have hsub : (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)))
      ⊆ Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          2 ^ (Nat.log 2 N + 1) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, lt_of_le_of_lt hTle (not_le.mp hx.2.2.2.1)⟩
  have hstep : (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        2 ^ (Nat.log 2 N + 1) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|)).card
      ≤ (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          2 ^ (Nat.log 2 N + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ))).card
        + (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          2 ^ (Nat.log 2 N + 1) < (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℝ))).card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro x hx
    rw [Finset.mem_filter] at hx
    by_cases h1 : (2 ^ (Nat.log 2 N + 1) : ℝ) < (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      push Not at h1
      by_contra h2
      push Not at h2
      have hcast : (LeanLab.Linnik.Decomp1532a.dif x : ℝ)
          = (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ)
            - (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℝ) := by
        unfold LeanLab.Linnik.Decomp1532a.dif
        push_cast
        ring
      have hb1 : (0 : ℝ) ≤ (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℝ) := by positivity
      have hb2 : (0 : ℝ) ≤ (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℝ) := by positivity
      have hle : |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (2 ^ (Nat.log 2 N + 1) : ℝ) := by
        rw [hcast, abs_le]
        constructor <;> linarith
      linarith [hx.2]
  calc (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card
      ≤ (Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          2 ^ (Nat.log 2 N + 1) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|)).card :=
        Finset.card_le_card hsub
    _ ≤ _ := hstep
    _ ≤ k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2)
          + k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2) :=
        add_le_add (card_first_le (L := Nat.log 2 N) hk) (card_second_le (L := Nat.log 2 N) hk)
    _ = 2 * (k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2)) := by ring

/-- The `Sg` mean over the complement of the major arcs. -/
private lemma comp_Sg_mean_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℝ,
      ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N P, ‖Sg N α‖ ^ 2 ≤
        (Real.log 4 + ε) * (N : ℝ) / Real.log (N : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hε)
  simp only [Nat.floor_natCast] at h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨N₀, fun N hN P => ?_⟩
  have hi : IntegrableOn (fun α => ‖Sg N α‖ ^ 2) (Set.Icc (0 : ℝ) 1) :=
    ((LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2).integrableOn_Icc
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖Sg N α‖))
    (Filter.Eventually.of_forall (fun α (h : α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs N P) => h.1))
  have hfull : ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α‖ ^ 2 = (Nat.primeCounting N : ℝ) := by
    have h1 : ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α‖ ^ 2 = ((primesLe N).card : ℝ) := by
      simpa [Sg] using LeanLab.Linnik.U1426ChainWire.parseval (primesLe N) (fun _ => 1)
    rw [h1]
    exact_mod_cast Nat.primesLE_card_eq_primeCounting N
  rw [hfull] at hmono
  exact hmono.trans (hN₀ N hN)

/-- One term of the sum is at most the minor arc mass. -/
private lemma term_le {N : ℕ} {P : ℝ} (n : ℤ) :
    |∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N P,
        ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re|
      ≤ ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N P, ‖Sg N α‖ ^ 2 := by
  classical
  have hsub : Set.Icc (0 : ℝ) 1 \ majorArcs N P ⊆ Set.Icc (0 : ℝ) 1 := fun α h => h.1
  have hcf : Continuous (fun α : ℝ => ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    have hs := LeanLab.Linnik.U7206.continuous_Sg N
    fun_prop
  have hcg : Continuous (fun α : ℝ => ‖Sg N α‖ ^ 2) :=
    (LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2
  have hfi : IntegrableOn (fun α : ℝ => ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re)
      (Set.Icc (0 : ℝ) 1 \ majorArcs N P) := hcf.integrableOn_Icc.mono_set hsub
  have hgi : IntegrableOn (fun α : ℝ => ‖Sg N α‖ ^ 2)
      (Set.Icc (0 : ℝ) 1 \ majorArcs N P) := hcg.integrableOn_Icc.mono_set hsub
  have hmeas : MeasurableSet (Set.Icc (0 : ℝ) 1 \ majorArcs N P) :=
    measurableSet_Icc.diff (measurableSet_majorArcs N P)
  refine abs_integral_le_integral_abs.trans ?_
  refine setIntegral_mono_on hfi.norm hgi hmeas ?_
  intro α _
  have h2 : |(LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (LeanLab.PNTPort.LargeSieve.norm_e _)
  calc |‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re|
      = ‖Sg N α‖ ^ 2 * |(LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖Sg N α‖ ^ 2 * 1 := by gcongr
    _ = ‖Sg N α‖ ^ 2 := mul_one _

/-- LEAF, OPEN. Second piece of the long shift range, the middle one: shifts above `2 N` but no
larger than `N ^ (3/2)`. This is the step of the target where the difference of the two exponent
sums is larger than the summation range, so the coefficient of the squared exponential sum at that
shift has already dropped out of the diagonal and the correlation has to come from the oscillation
of the phase alone, while the shift is still small enough that the phase moves by a whole winding
across a major arc. The total of the correlations over the complement of the major arcs restricted
to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_middle_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, hN₁⟩ := comp_Sg_mean_le 1 (by norm_num)
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt
    (18 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) * Real.log 2 / δ)
  refine ⟨max N₁ (max 2 (2 ^ L₀)), ?_⟩
  intro N hN
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := ((le_max_left 2 (2 ^ L₀)).trans (le_max_right N₁ _)).trans hN
  have hNL₀ : 2 ^ L₀ ≤ N := ((le_max_right 2 (2 ^ L₀)).trans (le_max_right N₁ _)).trans hN
  set L : ℕ := Nat.log 2 N with hLdef
  have hLg : L₀ ≤ L := by
    have hmono : Nat.log 2 (2 ^ L₀) ≤ Nat.log 2 N := Nat.log_mono_right hNL₀
    rw [Nat.log_pow (by norm_num : 1 < 2)] at hmono
    simpa only [hLdef] using hmono
  have hLpos : 1 ≤ L := by
    have := Nat.log_pos (b := 2) (n := N) (by norm_num) hN2
    omega
  have hlogpos : (0 : ℝ) < Real.log (N : ℝ) := by
    apply Real.log_pos
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hlogu : Real.log (N : ℝ) ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have hlt : (N : ℝ) < (2 : ℝ) ^ (L + 1) := by
      have h1 : N < 2 ^ (L + 1) := by
        rw [hLdef]
        exact Nat.lt_pow_succ_log_self (by norm_num) N
      exact_mod_cast h1
    have h2 := Real.log_lt_log (by positivity : (0:ℝ) < (N:ℝ)) hlt
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  -- the exponential gain
  have hexp : 18 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) * Real.log 2 * (L : ℝ)
      ≤ δ * (L : ℝ) ^ 2 := by
    have h0 : 0 < δ := hδ
    have ha : 18 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) * Real.log 2 / δ
        < (L : ℝ) := lt_of_lt_of_le hL₀ (by exact_mod_cast hLg)
    rw [div_lt_iff₀ h0] at ha
    have hLposR : (0 : ℝ) < (L : ℝ) := by
      have : (0:ℕ) < L := by omega
      exact_mod_cast this
    nlinarith [ha, hLposR]
  -- the per-term bound
  have hterm : ∀ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N),
      |∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re|
        ≤ ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 :=
    fun x => term_le (N := N) (P := (N : ℝ) ^ θ) (LeanLab.Linnik.Decomp1532a.dif x)
  have hVnonneg : (0 : ℝ) ≤
      ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun α => by positivity)
  have hVle : ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2
      ≤ (Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ) :=
    hN₁ N hN₁' ((N : ℝ) ^ θ)
  have hsum : |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2),
        ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)|
      ≤ ((Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
            ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card : ℝ)
        * ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun x _ => hterm x)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hFcard : ((Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card : ℝ)
      ≤ 2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2) := by
    have hc := middle_card_le k N hk hN2
    have h2 : ((2 * (k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2)) : ℕ) : ℝ)
        = 2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2) := by
      rw [hLdef]
      push_cast
      ring
    calc ((Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
            ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card : ℝ)
        ≤ ((2 * (k ^ 2 * (k + 2) ^ 2 * (Nat.log 2 N) ^ (2 * k - 2)) : ℕ) : ℝ) := by
          exact_mod_cast hc
      _ = 2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2) := h2
  -- the arithmetic core
  have hpow : (L : ℝ) ^ (2 * k - 2) * (L : ℝ) ^ 2 = (L : ℝ) ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk20 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hL0R : (L : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogpos
  have hC10 : (Real.log 4 + 1) ≠ 0 := by positivity
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hratio : 1 ≤ δ * (L : ℝ) ^ 2 / (9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1)
      * Real.log (N : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hlogv : Real.log (N : ℝ) ≤ 2 * (L : ℝ) * Real.log 2 := by
      have h1 : ((L : ℝ) + 1) ≤ 2 * (L : ℝ) := by
        have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
        linarith
      have h3 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [hlogu, h1, h3]
    have step1 : 9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) * Real.log (N : ℝ)
        ≤ 9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1)
          * (2 * (L : ℝ) * Real.log 2) := by
      have h4 : (0 : ℝ) ≤ 9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hlogv h4
    have step2 : 9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1)
          * (2 * (L : ℝ) * Real.log 2)
        = 18 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1) * Real.log 2 * (L : ℝ) := by
      ring
    linarith [step1, step2.le, hexp]
  have hmain : (2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2))
        * ((Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ))
      ≤ 2 * (N : ℝ) * (L : ℝ) ^ (2 * k) / Real.log (N : ℝ) ^ 2 * (δ / 9) := by
    have hEq : 2 * (N : ℝ) * (L : ℝ) ^ (2 * k) / Real.log (N : ℝ) ^ 2 * (δ / 9)
        = (2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2))
          * ((Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ))
          * (δ * (L : ℝ) ^ 2 / (9 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (Real.log 4 + 1)
            * Real.log (N : ℝ))) := by
      rw [← hpow]
      field_simp
    rw [hEq]
    exact le_mul_of_one_le_right (by positivity) hratio
  calc |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2),
        ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)|
      ≤ ((Finset.univ.filter (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
            (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
            ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
            |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2))).card : ℝ)
        * ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 := hsum
    _ ≤ (2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2 * (L : ℝ) ^ (2 * k - 2))
          * ((Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul hFcard hVle hVnonneg (by positivity)
    _ ≤ 2 * (N : ℝ) * (L : ℝ) ^ (2 * k) / Real.log (N : ℝ) ^ 2 * (δ / 9) := hmain

/-- LEAF, OPEN. Third piece of the long shift range, the far one: shifts above `N ^ (3/2)`. This is
the step of the target where the shift has outgrown every power of `N` below the summation range
itself, so it is far above the scale at which the width of a major arc allows the phase to be held
constant, and the correlation over the complement of the major arcs has to be small by the winding
of the phase on each arc alone. The total of the correlations over the complement of the major arcs
restricted to these tuples is at most a ninth of the budget factor once `N` is large. -/
theorem large_shift_far_sum_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)),
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  -- `N ^ (3/2)` overtakes the largest tuple difference once `N > k ^ 2`.
  refine ⟨k ^ 2 + 1, ?_⟩
  intro N hN
  have hk4 : 4 ≤ k ^ 2 := by
    have h := Nat.mul_le_mul hk hk
    simpa [pow_two] using h
  have hN5 : 5 ≤ N := by omega
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hNsq : (k : ℝ) ^ 2 < (N : ℝ) := by
    have h : ((k ^ 2 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
    linarith
  have hklt : (k : ℝ) < Real.sqrt (N : ℝ) := (Real.lt_sqrt hkR).mpr hNsq
  have hkey : (k : ℝ) * (N : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 2) := by
    calc (k : ℝ) * (N : ℝ) < Real.sqrt (N : ℝ) * (N : ℝ) :=
          mul_lt_mul_of_pos_right hklt hNpos
      _ = (N : ℝ) ^ ((3 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow,
            show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num,
            Real.rpow_add hNpos, Real.rpow_one]
  -- every tuple difference is at most `k * 2 ^ log₂ N`.
  have hsvbound : ∀ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N),
      |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (k : ℝ) * (2 : ℝ) ^ (Nat.log 2 N) := by
    intro x
    have h1 : LeanLab.Linnik.U1434Lemma21.sv x.1 ≤ k * 2 ^ Nat.log 2 N :=
      LeanLab.Linnik.U1434Lemma21.sv_le x.1
    have h2 : LeanLab.Linnik.U1434Lemma21.sv x.2 ≤ k * 2 ^ Nat.log 2 N :=
      LeanLab.Linnik.U1434Lemma21.sv_le x.2
    have hai : (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℤ) ≤
        ((k * 2 ^ Nat.log 2 N : ℕ) : ℤ) := by exact_mod_cast h1
    have hbi : (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℤ) ≤
        ((k * 2 ^ Nat.log 2 N : ℕ) : ℤ) := by exact_mod_cast h2
    have hi : -(((k * 2 ^ Nat.log 2 N : ℕ) : ℤ)) ≤ LeanLab.Linnik.Decomp1532a.dif x ∧
        LeanLab.Linnik.Decomp1532a.dif x ≤ ((k * 2 ^ Nat.log 2 N : ℕ) : ℤ) := by
      unfold LeanLab.Linnik.Decomp1532a.dif
      omega
    have hr : -((k : ℝ) * (2 : ℝ) ^ (Nat.log 2 N)) ≤
          (LeanLab.Linnik.Decomp1532a.dif x : ℝ) ∧
        (LeanLab.Linnik.Decomp1532a.dif x : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ (Nat.log 2 N) := by
      exact_mod_cast hi
    exact abs_le.mpr hr
  have h2L : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    have h := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h' : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hscale : ∀ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N),
      |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (k : ℝ) * (N : ℝ) := by
    intro x
    exact (hsvbound x).trans (mul_le_mul_of_nonneg_left h2L hkR)
  -- so the far range is empty.
  have hempty : (Finset.univ.filter
      (fun x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) =>
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
          (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
          ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hx.2.2.2 (le_of_lt ((hscale x).trans_lt hkey))
  have hsum : (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)),
      ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) = 0 := by
    rw [hempty]
    simp
  rw [hsum]
  simp only [abs_zero]
  have hlog : (0 : ℝ) < Real.log (N : ℝ) := by
    apply Real.log_pos
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hδ9 : (0 : ℝ) < δ / 9 := by linarith
  refine mul_nonneg ?_ (le_of_lt hδ9)
  exact div_nonneg (by positivity) (le_of_lt (pow_pos hlog 2))

/-- ASSEMBLY. The sealed statement `large_shift_minor_sum_bound`, from the three pieces of the long
shift range: split the tuple sum by `|dif x| ≤ 2 N` and then by `|dif x| ≤ N ^ (3/2)`, apply each
leaf to its piece, add the three bounds and use the triangle inequality, the three ninths of the
budget factor giving `δ / 3`. No sorry is used and the sealed theorem is not called. -/
theorem large_shift_minor_sum_bound_split :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
            ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  classical
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := large_shift_near_sum_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := large_shift_middle_sum_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := large_shift_far_sum_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right (max N₁ N₂) N₃) hN
  let A : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ 2 * (N : ℝ)
  let B : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 : ℝ) / 2)
  let S : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
      (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have H₁ : |(S.filter A).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, g, M, Finset.filter_filter, and_assoc] using h₁ N hN₁
  have H₂ : |((S.filter (fun x => ¬ A x)).filter B).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, B, g, M, Finset.filter_filter, and_assoc] using h₂ N hN₂
  have H₃ : |((S.filter (fun x => ¬ A x)).filter (fun x => ¬ B x)).sum g| ≤ M * (δ / 9) := by
    simpa only [S, A, B, g, M, Finset.filter_filter, and_assoc] using h₃ N hN₃
  have e₁ : (S.filter A).sum g + (S.filter (fun x => ¬ A x)).sum g = S.sum g :=
    Finset.sum_filter_add_sum_filter_not S A g
  have e₂ : ((S.filter (fun x => ¬ A x)).filter B).sum g +
      ((S.filter (fun x => ¬ A x)).filter (fun x => ¬ B x)).sum g =
      (S.filter (fun x => ¬ A x)).sum g :=
    Finset.sum_filter_add_sum_filter_not (S.filter (fun x => ¬ A x)) B g
  have hthree : M * (δ / 9) + M * (δ / 9) + M * (δ / 9) = M * (δ / 3) := by ring
  have hX : |(S.filter (fun x => ¬ A x)).sum g| ≤ M * (δ / 9) + M * (δ / 9) := by
    rw [← e₂]
    exact le_trans (abs_add_le _ _) (by linarith [H₂, H₃])
  have hY : |S.sum g| ≤ |(S.filter A).sum g| + |(S.filter (fun x => ¬ A x)).sum g| := by
    rw [← e₁]
    exact abs_add_le _ _
  have key : |S.sum g| ≤ M * (δ / 3) := by linarith [hY, H₁, hX, hthree]
  simpa only [S, g, M] using key

#print axioms large_shift_minor_sum_bound_split
